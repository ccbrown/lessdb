use std::net::{SocketAddr, ToSocketAddrs};

/// This maintains connections to all nodes in the cluster.
pub struct Cluster;

impl Cluster {
    pub fn join<A: ToSocketAddrs>(addr: SocketAddr, seed_peers: A) -> Self {
        Self
    }
}
