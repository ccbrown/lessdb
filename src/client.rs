use super::{
    node::{Node, SetCondition},
    partition::{Scalar, Value},
    protos::client as proto,
};
use anyhow::{Context, Result};
use protobuf::Message;
use std::{
    convert::{TryFrom, TryInto},
    net::{TcpListener, TcpStream, ToSocketAddrs},
    ops::Bound,
    sync::Arc,
};

#[error("missing value")]
#[derive(Clone, Copy, Debug, thiserror::Error)]
pub struct MissingValueError;

impl TryFrom<proto::Scalar> for Scalar {
    type Error = MissingValueError;

    fn try_from(value: proto::Scalar) -> Result<Self, Self::Error> {
        match value.value {
            Some(value) => Ok(match value {
                proto::Scalar_oneof_value::bytes(bytes) => Scalar::Bytes(bytes.into()),
                proto::Scalar_oneof_value::int(n) => Scalar::Int(n),
            }),
            None => Err(MissingValueError),
        }
    }
}

impl TryFrom<Option<proto::Scalar>> for Scalar {
    type Error = MissingValueError;

    fn try_from(value: Option<proto::Scalar>) -> Result<Self, Self::Error> {
        match value {
            Some(value) => value.try_into(),
            None => Err(MissingValueError),
        }
    }
}

impl TryFrom<proto::Value> for Value {
    type Error = MissingValueError;

    fn try_from(value: proto::Value) -> Result<Self, Self::Error> {
        match value.value {
            Some(value) => Ok(match value {
                proto::Value_oneof_value::bytes(bytes) => Value::Bytes(bytes.into()),
                proto::Value_oneof_value::int(n) => Value::Int(n),
                proto::Value_oneof_value::set(mut a) => Value::Set(
                    a.take_scalars()
                        .into_iter()
                        .map(|v| v.try_into())
                        .collect::<Result<_, _>>()?,
                ),
            }),
            None => Err(MissingValueError),
        }
    }
}

impl TryFrom<Option<proto::Value>> for Value {
    type Error = MissingValueError;

    fn try_from(value: Option<proto::Value>) -> Result<Self, Self::Error> {
        match value {
            Some(value) => value.try_into(),
            None => Err(MissingValueError),
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
            Self::Set(values) => {
                let mut a = proto::ScalarArray::new();
                a.set_scalars(values.into_iter().map(|v| v.into()).collect());
                proto::Value_oneof_value::set(a)
            }
        });
        value
    }
}

fn convert_bound(bound: Option<proto::Bound>) -> Result<Bound<Scalar>, MissingValueError> {
    Ok(match bound.and_then(|bound| bound.value) {
        None => Bound::Unbounded,
        Some(proto::Bound_oneof_value::included(scalar)) => Bound::Included(scalar.try_into()?),
        Some(proto::Bound_oneof_value::excluded(scalar)) => Bound::Excluded(scalar.try_into()?),
    })
}

pub struct API {
    node: Arc<Node>,
    logger: slog::Logger,
}

impl API {
    pub fn new(node: Arc<Node>, logger: slog::Logger) -> Self {
        Self { node, logger }
    }

    pub fn listen<A: ToSocketAddrs>(&self, addr: A) -> Result<()> {
        let listener = TcpListener::bind(addr).with_context(|| "unable to bind listener")?;
        info!(
            self.logger,
            "listening for client connections at {}",
            listener
                .local_addr()
                .with_context(|| "unable to get local address")?
        );
        for stream in listener.incoming() {
            let stream = stream?;
            let node = self.node.clone();
            let logger = self.logger.clone();
            std::thread::spawn(move || {
                if let Err(e) = Self::serve_tcp_stream(node, &logger, stream) {
                    error!(logger, "client connection error: {}", e);
                }
            });
        }
        Ok(())
    }

    /// Parses request from the TCP stream and serves them sequentially. Any error parsing requests
    /// will cause the function to return with the error. Errors that occur during request
    /// execution will be logged and cause an error response, but will not cause the function to
    /// return.
    fn serve_tcp_stream(
        node: Arc<Node>,
        logger: &slog::Logger,
        mut stream: TcpStream,
    ) -> Result<()> {
        loop {
            let request = proto::Request::parse_from_reader(&mut stream)
                .with_context(|| "unable to parse request")?;

            let body = match request.body {
                Some(body) => body,
                None => continue,
            };

            let response_body = match body {
                proto::Request_oneof_body::get(op) => {
                    let key = op.key.try_into()?;
                    node.get(&key).map(|value| {
                        let mut result = proto::GetResult::new();
                        if let Some(value) = value {
                            result.set_value(value.into());
                        }
                        proto::Response_oneof_body::get(result)
                    })
                }
                proto::Request_oneof_body::set(mut op) => {
                    let key = op.key.try_into()?;
                    let value = op.value.take().try_into()?;
                    let condition = op
                        .condition
                        .take()
                        .and_then(|cond| cond.value)
                        .map(|cond| -> Result<_> {
                            Ok(match cond {
                                proto::SetOperation_Condition_oneof_value::exists(exists) => {
                                    SetCondition::Exists(exists)
                                }
                                proto::SetOperation_Condition_oneof_value::equals(value) => {
                                    SetCondition::Equals(value.try_into()?)
                                }
                            })
                        })
                        .transpose()?;
                    node.set(key, value, condition).map(|did_set| {
                        let mut result = proto::SetResult::new();
                        result.set_did_set(did_set);
                        proto::Response_oneof_body::set(result)
                    })
                }
                proto::Request_oneof_body::delete(op) => {
                    let key = op.key.try_into()?;
                    node.delete(&key).map(|did_delete| {
                        let mut result = proto::DeleteResult::new();
                        result.set_did_delete(did_delete);
                        proto::Response_oneof_body::delete(result)
                    })
                }
                proto::Request_oneof_body::set_add(op) => {
                    let key = op.key.try_into()?;
                    let members: Vec<Scalar> = op
                        .members
                        .into_iter()
                        .map(|s| s.try_into())
                        .collect::<Result<_, _>>()?;
                    node.set_add(key, members)
                        .map(|_| proto::Response_oneof_body::set_add(proto::SetAddResult::new()))
                }
                proto::Request_oneof_body::set_remove(op) => {
                    let key = op.key.try_into()?;
                    let members: Vec<Scalar> = op
                        .members
                        .into_iter()
                        .map(|s| s.try_into())
                        .collect::<Result<_, _>>()?;
                    node.set_remove(key, members).map(|_| {
                        proto::Response_oneof_body::set_remove(proto::SetRemoveResult::new())
                    })
                }
                proto::Request_oneof_body::map_set(mut op) => {
                    let key = op.key.try_into()?;
                    let field = op.field.take().try_into()?;
                    let value = op.value.take().try_into()?;
                    let order = op.order.take().try_into()?;
                    node.map_set(key, field, value, order)
                        .map(|_| proto::Response_oneof_body::map_set(proto::MapSetResult::new()))
                }
                proto::Request_oneof_body::map_delete(mut op) => {
                    let key = op.key.try_into()?;
                    let field = op.field.take().try_into()?;
                    node.map_delete(key, field).map(|did_delete| {
                        let mut result = proto::MapDeleteResult::new();
                        result.set_did_delete(did_delete);
                        proto::Response_oneof_body::map_delete(result)
                    })
                }
                proto::Request_oneof_body::get_map_range(mut op) => {
                    let key = op.key.try_into()?;
                    let start: Bound<Scalar> = convert_bound(op.start.take())?;
                    let end: Bound<Scalar> = convert_bound(op.end.take())?;
                    node.get_map_range(
                        key,
                        (start, end),
                        if op.limit > 0 {
                            Some(op.limit as usize)
                        } else {
                            None
                        },
                        op.reverse,
                    )
                    .map(|values| {
                        let mut result = proto::GetMapRangeResult::new();
                        result.set_values(values.into_iter().map(|v| v.into()).collect());
                        proto::Response_oneof_body::get_map_range(result)
                    })
                }
                proto::Request_oneof_body::get_map_range_by_field(mut op) => {
                    let key = op.key.try_into()?;
                    let start: Bound<Scalar> = convert_bound(op.start.take())?;
                    let end: Bound<Scalar> = convert_bound(op.end.take())?;
                    node.get_map_range_by_field(
                        key,
                        (start, end),
                        if op.limit > 0 {
                            Some(op.limit as usize)
                        } else {
                            None
                        },
                        op.reverse,
                    )
                    .map(|values| {
                        let mut result = proto::GetMapRangeByFieldResult::new();
                        result.set_values(values.into_iter().map(|v| v.into()).collect());
                        proto::Response_oneof_body::get_map_range_by_field(result)
                    })
                }
            }
            .unwrap_or_else(|e| {
                error!(logger, "request error: {}", e);
                let mut result = proto::Error::new();
                result.set_code(proto::Error_Code::INTERNAL);
                proto::Response_oneof_body::error(result)
            });

            let mut response = proto::Response::new();
            response.body = Some(response_body);
            response
                .write_to_writer(&mut stream)
                .with_context(|| "unable to write response")?;
        }
    }
}
