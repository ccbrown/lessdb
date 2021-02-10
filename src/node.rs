use super::partition::Partition;
use anyhow::{Context, Result};
use std::{net::SocketAddr, path::Path};

const PARTITION_COUNT: usize = 1 << 16;

pub struct Node {
    partitions: Vec<Partition>,
}

pub struct Config<P> {
    pub data_path: P,
    pub client_listen_addr: SocketAddr,
}

impl Node {
    pub fn new<P: AsRef<Path>>(config: Config<P>) -> Result<Self> {
        Ok(Self {
            partitions: (0..PARTITION_COUNT)
                .map(|i| {
                    Partition::open(
                        config
                            .data_path
                            .as_ref()
                            .join(format!("partition-{:08}", i)),
                    )
                    .with_context(|| format!("unable to create partition {}", i))
                })
                .collect::<Result<_>>()?,
        })
    }
}
