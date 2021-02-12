use super::{
    node::{Node, SetCondition},
    partition::Value,
    protos::client as proto,
};
use anyhow::{Context, Result};
use protobuf::Message;
use std::{
    convert::{TryFrom, TryInto},
    net::{TcpListener, TcpStream, ToSocketAddrs},
    sync::Arc,
};

#[derive(Clone, Copy, Debug, thiserror::Error)]
pub enum TryValueFromProtoValueError {
    #[error("missing value")]
    MissingValue,
}

impl TryFrom<proto::Value> for Value {
    type Error = TryValueFromProtoValueError;

    fn try_from(value: proto::Value) -> Result<Self, Self::Error> {
        match value.value {
            Some(value) => Ok(match value {
                proto::Value_oneof_value::bytes(bytes) => Value::Bytes(bytes.into()),
                proto::Value_oneof_value::int(n) => Value::Int(n),
            }),
            None => Err(TryValueFromProtoValueError::MissingValue),
        }
    }
}

impl TryFrom<Option<proto::Value>> for Value {
    type Error = TryValueFromProtoValueError;

    fn try_from(value: Option<proto::Value>) -> Result<Self, Self::Error> {
        match value {
            Some(value) => value.try_into(),
            None => Err(TryValueFromProtoValueError::MissingValue),
        }
    }
}

impl Into<proto::Value> for Value {
    fn into(self) -> proto::Value {
        let mut value = proto::Value::new();
        value.value = Some(match self {
            Self::Bytes(bytes) => proto::Value_oneof_value::bytes(bytes),
            Self::Int(n) => proto::Value_oneof_value::int(n),
        });
        value
    }
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
            if let Some(body) = request.body {
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
                    proto::Request_oneof_body::increment(op) => {
                        let key = op.key.try_into()?;
                        node.increment(key, op.amount).map(|new_value| {
                            let mut result = proto::IncrementResult::new();
                            result.set_new_value(new_value);
                            proto::Response_oneof_body::increment(result)
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
}
