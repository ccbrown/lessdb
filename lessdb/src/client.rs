use super::{
    node::{AppendCondition, FilterPredicate, Node, SetCondition},
    partition::{IncorrectHashLengthError, Scalar, Value},
    protos::{
        client as proto,
        client_grpc::{create_service, Service},
    },
};
use anyhow::{Context, Error, Result};
use futures::{FutureExt, TryFutureExt};
use grpcio::{ChannelBuilder, EnvBuilder, ResourceQuota, Server, ServerBuilder};
use std::{
    convert::{TryFrom, TryInto},
    net::ToSocketAddrs,
    ops::Bound,
    sync::Arc,
};

#[derive(Debug, thiserror::Error)]
enum UserFacingError {
    #[error("bad request: {0}")]
    BadRequest(String),
    #[error("internal error")]
    InternalError(Error),
}

trait BadRequestError: std::error::Error {}

// these errors and their messages can be converted directly into bad request errors
impl BadRequestError for ScalarError {}
impl BadRequestError for ValueError {}
impl BadRequestError for IncorrectHashLengthError {}

impl<E: BadRequestError> From<E> for UserFacingError {
    fn from(e: E) -> Self {
        Self::BadRequest(e.to_string())
    }
}

#[derive(Clone, Copy, Debug, thiserror::Error)]
pub enum ScalarError {
    #[error("missing required scalar")]
    MissingRequiredScalar,
}

impl TryFrom<proto::Scalar> for Scalar {
    type Error = ScalarError;

    fn try_from(value: proto::Scalar) -> Result<Self, Self::Error> {
        match value.value {
            Some(value) => Ok(match value {
                proto::Scalar_oneof_value::bytes(bytes) => Scalar::Bytes(bytes.into()),
                proto::Scalar_oneof_value::int(n) => Scalar::Int(n),
            }),
            None => Err(ScalarError::MissingRequiredScalar),
        }
    }
}

impl TryFrom<Option<proto::Scalar>> for Scalar {
    type Error = ScalarError;

    fn try_from(value: Option<proto::Scalar>) -> Result<Self, Self::Error> {
        match value {
            Some(value) => value.try_into(),
            None => Err(ScalarError::MissingRequiredScalar),
        }
    }
}

#[derive(Clone, Copy, Debug, thiserror::Error)]
pub enum ValueError {
    #[error(transparent)]
    ScalarError(#[from] ScalarError),
    #[error("missing required value")]
    MissingRequiredValue,
}

impl TryFrom<proto::Value> for Value {
    type Error = ValueError;

    fn try_from(value: proto::Value) -> Result<Self, Self::Error> {
        match value.value {
            Some(value) => Ok(match value {
                proto::Value_oneof_value::bytes(bytes) => Value::Bytes(bytes.into()),
                proto::Value_oneof_value::int(n) => Value::Int(n),
                proto::Value_oneof_value::array(mut a) => Value::Array(
                    a.take_values()
                        .into_iter()
                        .map(|v| v.try_into())
                        .collect::<Result<_, _>>()?,
                ),
            }),
            None => Err(ValueError::MissingRequiredValue),
        }
    }
}

impl TryFrom<Option<proto::Value>> for Value {
    type Error = ValueError;

    fn try_from(value: Option<proto::Value>) -> Result<Self, Self::Error> {
        match value {
            Some(value) => value.try_into(),
            None => Err(ValueError::MissingRequiredValue),
        }
    }
}

impl Into<proto::Scalar> for Scalar {
    fn into(self) -> proto::Scalar {
        let mut scalar = proto::Scalar::new();
        scalar.value = Some(match self {
            Self::Bytes(bytes) => proto::Scalar_oneof_value::bytes(bytes),
            Self::Int(n) => proto::Scalar_oneof_value::int(n),
        });
        scalar
    }
}

impl Into<proto::Value> for Value {
    fn into(self) -> proto::Value {
        let mut value = proto::Value::new();
        value.value = Some(match self {
            Self::Bytes(bytes) => proto::Value_oneof_value::bytes(bytes),
            Self::Int(n) => proto::Value_oneof_value::int(n),
            Self::Array(values) => {
                let mut a = proto::ValueArray::new();
                a.set_values(values.into_iter().map(|v| v.into()).collect());
                proto::Value_oneof_value::array(a)
            }
        });
        value
    }
}

fn convert_bound(bound: Option<proto::Bound>) -> Result<Bound<Scalar>, ValueError> {
    Ok(match bound.and_then(|bound| bound.value) {
        None => Bound::Unbounded,
        Some(proto::Bound_oneof_value::included(scalar)) => Bound::Included(scalar.try_into()?),
        Some(proto::Bound_oneof_value::excluded(scalar)) => Bound::Excluded(scalar.try_into()?),
    })
}

pub struct API {
    _server: Server,
}

impl API {
    pub fn new<A: ToSocketAddrs>(logger: slog::Logger, node: Arc<Node>, addr: A) -> Result<Self> {
        let env = Arc::new(EnvBuilder::new().build());

        let service = create_service(ServiceImpl {
            node,
            logger: logger.clone(),
        });

        let quota = ResourceQuota::new(Some("ClientServiceQuota")).resize_memory(1024 * 1024);
        let ch_builder = ChannelBuilder::new(env.clone()).set_resource_quota(quota);

        let mut server = ServerBuilder::new(env).register_service(service);

        for addr in addr
            .to_socket_addrs()
            .with_context(|| "invalid socket address")?
        {
            server = server.bind(addr.ip().to_string(), addr.port());
        }

        let mut server = server
            .channel_args(ch_builder.build_args())
            .build()
            .with_context(|| "unable to build server")?;

        server.start();
        for (host, port) in server.bind_addrs() {
            info!(logger, "listening at {}:{}", host, port);
        }

        Ok(Self { _server: server })
    }
}

#[derive(Clone)]
struct ServiceImpl {
    node: Arc<Node>,
    logger: slog::Logger,
}

impl ServiceImpl {
    fn handle_grpc_request<
        Response: Default,
        Output,
        F: FnOnce(&Node) -> Result<Output, UserFacingError>,
        SetBody: FnOnce(&mut Response, Result<Output, proto::Error>),
    >(
        &mut self,
        ctx: ::grpcio::RpcContext,
        sink: ::grpcio::UnarySink<Response>,
        f: F,
        set_body: SetBody,
    ) {
        // TODO: maybe we should do our work on a thread pool?
        // See: https://github.com/tikv/grpc-rs/issues/179
        // And: https://github.com/tikv/grpc-rs/issues/297
        let mut resp = Response::default();
        set_body(
            &mut resp,
            f(&self.node).map_err(|e| {
                let mut err = proto::Error::new();
                err.message = e.to_string();
                match e {
                    UserFacingError::BadRequest(_) => {
                        err.set_code(proto::Error_Code::BAD_REQUEST);
                    }
                    UserFacingError::InternalError(e) => {
                        error!(self.logger, "request error: {}", e);
                        err.set_code(proto::Error_Code::INTERNAL);
                    }
                }
                err
            }),
        );
        let logger = self.logger.clone();
        let f = sink
            .success(resp)
            .map_err(move |e| error!(logger, "failed to set response: {}", e))
            .map(|_| ());
        ctx.spawn(f)
    }
}

impl Service for ServiceImpl {
    fn clear_partitions(
        &mut self,
        ctx: ::grpcio::RpcContext,
        _req: proto::ClearPartitionsRequest,
        sink: ::grpcio::UnarySink<proto::ClearPartitionsResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                node.clear_partitions()
                    .map(|_| proto::ClearPartitionsResult::new())
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::ClearPartitionsResponse_oneof_body::result(r),
                    Err(e) => proto::ClearPartitionsResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn get(
        &mut self,
        ctx: ::grpcio::RpcContext,
        req: proto::GetRequest,
        sink: ::grpcio::UnarySink<proto::GetResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                node.get(&key)
                    .map(|value| {
                        let mut result = proto::GetResult::new();
                        if let Some(value) = value {
                            result.set_value(value.into());
                        }
                        result
                    })
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::GetResponse_oneof_body::result(r),
                    Err(e) => proto::GetResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn set(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::SetRequest,
        sink: ::grpcio::UnarySink<proto::SetResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                let value = req.value.take().try_into()?;
                let condition = req
                    .condition
                    .take()
                    .and_then(|cond| cond.condition)
                    .map(|cond| -> Result<_, ValueError> {
                        Ok(match cond {
                            proto::SetRequest_Condition_oneof_condition::exists(exists) => {
                                SetCondition::Exists(exists)
                            }
                            proto::SetRequest_Condition_oneof_condition::equals(value) => {
                                SetCondition::Equals(value.try_into()?)
                            }
                        })
                    })
                    .transpose()?;
                node.set(key, value, condition)
                    .map(|did_set| {
                        let mut result = proto::SetResult::new();
                        result.set_did_set(did_set);
                        result
                    })
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::SetResponse_oneof_body::result(r),
                    Err(e) => proto::SetResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn delete(
        &mut self,
        ctx: ::grpcio::RpcContext,
        req: proto::DeleteRequest,
        sink: ::grpcio::UnarySink<proto::DeleteResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                node.delete(&key)
                    .map(|did_delete| {
                        let mut result = proto::DeleteResult::new();
                        result.set_did_delete(did_delete);
                        result
                    })
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::DeleteResponse_oneof_body::result(r),
                    Err(e) => proto::DeleteResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn append(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::AppendRequest,
        sink: ::grpcio::UnarySink<proto::AppendResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                let values: Vec<Value> = req
                    .values
                    .into_iter()
                    .map(|s| s.try_into())
                    .collect::<Result<_, _>>()?;
                let condition = req
                    .condition
                    .take()
                    .and_then(|cond| cond.condition)
                    .map(|cond| -> Result<_, ValueError> {
                        Ok(match cond {
                            proto::AppendRequest_Condition_oneof_condition::contains_value(
                                contains,
                            ) => AppendCondition::ContainsValue(contains),
                        })
                    })
                    .transpose()?;
                node.append(key, values, condition)
                    .map(|_| proto::AppendResult::new())
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::AppendResponse_oneof_body::result(r),
                    Err(e) => proto::AppendResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn filter(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::FilterRequest,
        sink: ::grpcio::UnarySink<proto::FilterResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                let predicate = req
                    .predicate
                    .take()
                    .and_then(|p| p.predicate)
                    .map(|p| -> Result<_, ValueError> {
                        Ok(match p {
                            proto::FilterRequest_Predicate_oneof_predicate::not_in(values) => {
                                FilterPredicate::NotIn(
                                    values
                                        .values
                                        .into_iter()
                                        .map(|s| s.try_into())
                                        .collect::<Result<_, _>>()?,
                                )
                            }
                        })
                    })
                    .transpose()?
                    .unwrap();
                node.filter(key, predicate)
                    .map(|_| proto::FilterResult::new())
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::FilterResponse_oneof_body::result(r),
                    Err(e) => proto::FilterResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn map_set(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::MapSetRequest,
        sink: ::grpcio::UnarySink<proto::MapSetResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                let field = req.field.take().try_into()?;
                let value = req.value.take().try_into()?;
                let order = req.order.take().try_into()?;
                node.map_set(key, field, value, order)
                    .map(|_| proto::MapSetResult::new())
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::MapSetResponse_oneof_body::result(r),
                    Err(e) => proto::MapSetResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn map_delete(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::MapDeleteRequest,
        sink: ::grpcio::UnarySink<proto::MapDeleteResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                let field = req.field.take().try_into()?;
                node.map_delete(key, field)
                    .map(|did_delete| {
                        let mut result = proto::MapDeleteResult::new();
                        result.set_did_delete(did_delete);
                        result
                    })
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::MapDeleteResponse_oneof_body::result(r),
                    Err(e) => proto::MapDeleteResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn map_get_range(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::MapGetRangeRequest,
        sink: ::grpcio::UnarySink<proto::MapGetRangeResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                let start: Bound<Scalar> = convert_bound(req.start.take())?;
                let end: Bound<Scalar> = convert_bound(req.end.take())?;
                node.map_get_range(
                    key,
                    (start, end),
                    if req.limit > 0 {
                        Some(req.limit as usize)
                    } else {
                        None
                    },
                    req.reverse,
                )
                .map(|values| {
                    let mut result = proto::MapGetRangeResult::new();
                    result.set_values(values.into_iter().map(|v| v.into()).collect());
                    result
                })
                .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::MapGetRangeResponse_oneof_body::result(r),
                    Err(e) => proto::MapGetRangeResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn map_get_range_by_field(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::MapGetRangeByFieldRequest,
        sink: ::grpcio::UnarySink<proto::MapGetRangeByFieldResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                let start: Bound<Scalar> = convert_bound(req.start.take())?;
                let end: Bound<Scalar> = convert_bound(req.end.take())?;
                node.map_get_range_by_field(
                    key,
                    (start, end),
                    if req.limit > 0 {
                        Some(req.limit as usize)
                    } else {
                        None
                    },
                    req.reverse,
                )
                .map(|values| {
                    let mut result = proto::MapGetRangeByFieldResult::new();
                    result.set_values(values.into_iter().map(|v| v.into()).collect());
                    result
                })
                .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::MapGetRangeByFieldResponse_oneof_body::result(r),
                    Err(e) => proto::MapGetRangeByFieldResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn map_count_range(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::MapCountRangeRequest,
        sink: ::grpcio::UnarySink<proto::MapCountRangeResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                let start: Bound<Scalar> = convert_bound(req.start.take())?;
                let end: Bound<Scalar> = convert_bound(req.end.take())?;
                node.map_count_range(key, (start, end))
                    .map(|count| {
                        let mut result = proto::MapCountRangeResult::new();
                        result.count = count;
                        result
                    })
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::MapCountRangeResponse_oneof_body::result(r),
                    Err(e) => proto::MapCountRangeResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn map_count_range_by_field(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::MapCountRangeByFieldRequest,
        sink: ::grpcio::UnarySink<proto::MapCountRangeByFieldResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let key = req.key.try_into()?;
                let start: Bound<Scalar> = convert_bound(req.start.take())?;
                let end: Bound<Scalar> = convert_bound(req.end.take())?;
                node.map_count_range_by_field(key, (start, end))
                    .map(|count| {
                        let mut result = proto::MapCountRangeByFieldResult::new();
                        result.count = count;
                        result
                    })
                    .map_err(UserFacingError::InternalError)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::MapCountRangeByFieldResponse_oneof_body::result(r),
                    Err(e) => proto::MapCountRangeByFieldResponse_oneof_body::error(e),
                })
            },
        )
    }
}
