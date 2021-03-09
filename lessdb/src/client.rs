use super::{
    node::{
        Node, ReadExpression, ReadTransaction, TransactionError, WriteExpression,
        WriteExpressionSetCondition, WriteTransaction,
    },
    protos::{
        client as proto,
        client_grpc::{create_service, Service},
    },
    storage::Value,
};
use anyhow::{Context, Error, Result};
use futures::{FutureExt, TryFutureExt};
use grpcio::{ChannelBuilder, EnvBuilder, ResourceQuota, Server, ServerBuilder};
use std::{
    convert::{TryFrom, TryInto},
    net::ToSocketAddrs,
    sync::Arc,
};

#[derive(Debug, thiserror::Error)]
pub enum UserFacingError {
    #[error("bad request: {0}")]
    BadRequest(String),
    #[error("internal error")]
    InternalError(Error),
}

impl From<TransactionError> for UserFacingError {
    fn from(e: TransactionError) -> Self {
        match e {
            TransactionError::ExpressionError(_) => Self::BadRequest(e.to_string()),
            TransactionError::Other(_) => Self::InternalError(e.into()),
        }
    }
}

impl TryFrom<proto::ReadExpression> for ReadExpression {
    type Error = UserFacingError;

    fn try_from(expr: proto::ReadExpression) -> Result<Self, Self::Error> {
        match expr.expr {
            Some(value) => Ok(match value {
                proto::ReadExpression_oneof_expr::get(expr) => ReadExpression::Get {
                    key: expr.key as _,
                    dest: expr.dest as _,
                },
                proto::ReadExpression_oneof_expr::sequence(mut expr) => ReadExpression::Sequence {
                    exprs: expr
                        .take_exprs()
                        .into_iter()
                        .map(|e| e.try_into())
                        .collect::<Result<_, _>>()?,
                },
            }),
            None => Err(UserFacingError::BadRequest(
                "missing expression".to_string(),
            )),
        }
    }
}

impl TryFrom<proto::ReadTransaction> for ReadTransaction {
    type Error = UserFacingError;

    fn try_from(mut tx: proto::ReadTransaction) -> Result<Self, Self::Error> {
        Ok(Self {
            inputs: tx
                .take_inputs()
                .into_iter()
                .map(|v| v.try_into())
                .collect::<Result<_, _>>()?,
            outputs: tx.take_outputs().into_iter().map(|v| v as _).collect(),
            expr: match tx.expr.take() {
                Some(expr) => expr.try_into()?,
                None => {
                    return Err(UserFacingError::BadRequest(
                        "missing expression".to_string(),
                    ))
                }
            },
        })
    }
}

impl TryFrom<proto::WriteExpression> for WriteExpression {
    type Error = UserFacingError;

    fn try_from(expr: proto::WriteExpression) -> Result<Self, Self::Error> {
        match expr.expr {
            Some(value) => {
                Ok(match value {
                    proto::WriteExpression_oneof_expr::clear(_) => WriteExpression::Clear {},
                    proto::WriteExpression_oneof_expr::delete(expr) => {
                        WriteExpression::Delete { key: expr.key as _ }
                    }
                    proto::WriteExpression_oneof_expr::set(mut expr) => WriteExpression::Set {
                        key: expr.key as _,
                        value: expr.value as _,
                        condition: expr.condition.take().and_then(|cond| cond.condition).map(
                            |cond| match cond {
                                proto::WriteExpressionSet_Condition_oneof_condition::exists(
                                    exists,
                                ) => WriteExpressionSetCondition::Exists(exists),
                                proto::WriteExpressionSet_Condition_oneof_condition::equals(
                                    value,
                                ) => WriteExpressionSetCondition::Equals(value as _),
                            },
                        ),
                    },
                    proto::WriteExpression_oneof_expr::read(expr) => WriteExpression::Read {
                        expr: expr.try_into()?,
                    },
                    proto::WriteExpression_oneof_expr::sequence(mut expr) => {
                        WriteExpression::Sequence {
                            exprs: expr
                                .take_exprs()
                                .into_iter()
                                .map(|e| e.try_into())
                                .collect::<Result<_, _>>()?,
                        }
                    }
                })
            }
            None => Err(UserFacingError::BadRequest(
                "missing expression".to_string(),
            )),
        }
    }
}

impl TryFrom<proto::WriteTransaction> for WriteTransaction {
    type Error = UserFacingError;

    fn try_from(mut tx: proto::WriteTransaction) -> Result<Self, Self::Error> {
        Ok(Self {
            inputs: tx
                .take_inputs()
                .into_iter()
                .map(|v| v.try_into())
                .collect::<Result<_, _>>()?,
            outputs: tx.take_outputs().into_iter().map(|v| v as _).collect(),
            expr: match tx.expr.take() {
                Some(expr) => expr.try_into()?,
                None => {
                    return Err(UserFacingError::BadRequest(
                        "missing expression".to_string(),
                    ))
                }
            },
        })
    }
}

impl TryFrom<proto::Value> for Value {
    type Error = UserFacingError;

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
            None => Err(UserFacingError::BadRequest(
                "missing required value".to_string(),
            )),
        }
    }
}

impl TryFrom<Option<proto::Value>> for Value {
    type Error = UserFacingError;

    fn try_from(value: Option<proto::Value>) -> Result<Self, Self::Error> {
        match value {
            Some(value) => value.try_into(),
            None => Err(UserFacingError::BadRequest(
                "missing required value".to_string(),
            )),
        }
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
    fn read(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::ReadRequest,
        sink: ::grpcio::UnarySink<proto::ReadResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let tx = req.take_tx().try_into()?;
                let mut result = proto::ReadResult::default();
                result.outputs = node
                    .read(tx)?
                    .into_iter()
                    .map(|v| {
                        let mut output = proto::ReadOutput::default();
                        output.value = v.map(|v| v.into()).into();
                        output
                    })
                    .collect();
                Ok(result)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::ReadResponse_oneof_body::result(r),
                    Err(e) => proto::ReadResponse_oneof_body::error(e),
                })
            },
        )
    }

    fn write(
        &mut self,
        ctx: ::grpcio::RpcContext,
        mut req: proto::WriteRequest,
        sink: ::grpcio::UnarySink<proto::WriteResponse>,
    ) {
        self.handle_grpc_request(
            ctx,
            sink,
            |node| {
                let tx = req.take_tx().try_into()?;
                let mut result = proto::WriteResult::default();
                result.outputs = node
                    .write(tx)?
                    .into_iter()
                    .map(|v| {
                        let mut output = proto::WriteOutput::default();
                        output.value = v.map(|v| v.into()).into();
                        output
                    })
                    .collect();
                Ok(result)
            },
            |resp, r| {
                resp.body = Some(match r {
                    Ok(r) => proto::WriteResponse_oneof_body::result(r),
                    Err(e) => proto::WriteResponse_oneof_body::error(e),
                })
            },
        )
    }
}
