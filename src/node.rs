use super::cluster::Cluster;
use std::net::{SocketAddr, ToSocketAddrs};

pub struct Node {
    cluster: Cluster,
}

impl Node {
    pub fn new<A: ToSocketAddrs>(
        client_listen_addr: SocketAddr,
        peer_listen_addr: SocketAddr,
        seed_peers: A,
    ) -> Self {
        Self {
            cluster: Cluster::join(peer_listen_addr, seed_peers),
        }
    }
}
