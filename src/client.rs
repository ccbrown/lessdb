use super::{
    node::Node,
    partition::{Bytes, Hash},
};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::{
    net::{TcpListener, TcpStream, ToSocketAddrs},
    sync::Arc,
};

#[derive(Deserialize)]
pub struct Request {
    pub body: RequestBody,
}

#[derive(Deserialize)]
pub enum RequestBody {
    Get { key: Hash },
    Set { key: Hash, value: Bytes },
    Delete { key: Hash },
}

#[derive(Serialize)]
pub struct Response {
    pub body: ResponseBody,
}

#[derive(Serialize)]
pub enum ErrorCode {
    InternalError,
}

#[derive(Serialize)]
pub enum ResponseBody {
    Error { code: ErrorCode },
    GetResult { value: Option<Bytes> },
    SetResult {},
    DeleteResult {},
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

    pub fn serve_tcp_stream(
        node: Arc<Node>,
        logger: &slog::Logger,
        stream: TcpStream,
    ) -> Result<()> {
        loop {
            let request: Request =
                rmp_serde::from_read(&stream).with_context(|| "unable to deserialize request")?;
            let response_body = match request.body {
                RequestBody::Get { key } => node
                    .get(&key)
                    .map(|value| ResponseBody::GetResult { value }),
                RequestBody::Set { key, value } => {
                    node.set(key, value).map(|_| ResponseBody::SetResult {})
                }
                RequestBody::Delete { key } => {
                    node.delete(&key).map(|_| ResponseBody::DeleteResult {})
                }
            }
            .unwrap_or_else(|e| {
                error!(logger, "request error: {}", e);
                ResponseBody::Error {
                    code: ErrorCode::InternalError,
                }
            });
            let response = Response {
                body: response_body,
            };
            response
                .serialize(&mut rmp_serde::Serializer::new(&stream))
                .with_context(|| "unable to serialize response")?;
        }
    }
}
