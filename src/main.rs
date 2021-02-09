use clap::{App, Arg};
use std::{error::Error, net::SocketAddr};

mod cluster;
mod node;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn main() -> Result<()> {
    let matches = App::new("ElastiKV")
        .version("0.0")
        .arg(
            Arg::with_name("client-listen-addr")
                .long("client-listen-addr")
                .value_name("ADDR")
                .help("the address to listen on and advertise for clients")
                .required(true)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("peer-listen-addr")
                .long("peer-listen-addr")
                .value_name("ADDR")
                .help("the address to listen on and advertise for peers")
                .required(true)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("seed-peer")
                .long("seed-peer")
                .value_name("ADDR")
                .help("a seed peer to connect to")
                .multiple(true)
                .takes_value(true),
        )
        .get_matches();

    let client_listen_addr: SocketAddr = matches.value_of("client-listen-addr").unwrap().parse()?;
    let peer_listen_addr: SocketAddr = matches.value_of("peer-listen-addr").unwrap().parse()?;

    let seed_peers: Vec<SocketAddr> = matches
        .values_of("seed-peer")
        .into_iter()
        .flatten()
        .map(|s| Ok(s.parse()?))
        .collect::<Result<_>>()?;

    let _node = node::Node::new(client_listen_addr, peer_listen_addr, seed_peers.as_slice());
    loop {
        std::thread::park();
    }
}
