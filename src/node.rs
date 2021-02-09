use super::cluster::Cluster;
use std::{
    net::{SocketAddr, ToSocketAddrs},
    path::Path,
};

pub struct Node {
    cluster: Cluster,
}

pub struct Config<A, P> {
    pub data_path: P,
    pub client_listen_addr: SocketAddr,
    pub peer_listen_addr: SocketAddr,
    pub seed_peers: A,
}

impl Node {
    pub fn new<A: ToSocketAddrs, P: AsRef<Path>>(config: Config<A, P>) -> Self {
        Self {
            cluster: Cluster::join(config.peer_listen_addr, config.seed_peers),
        }
    }
}
