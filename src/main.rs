use clap::{App, Arg};
use std::error::Error;

mod client;
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
        .arg(
            Arg::with_name("data")
                .long("data")
                .short("d")
                .value_name("PATH")
                .help("the directory to store data in")
                .required(true)
                .takes_value(true),
        )
        .get_matches();

    let _node = node::Node::new(node::Config {
        data_path: matches.value_of("data").expect("this argument is required"),
        client_listen_addr: matches
            .value_of("client-listen-addr")
            .expect("this argument is required")
            .parse()?,
        peer_listen_addr: matches
            .value_of("peer-listen-addr")
            .expect("this argument is required")
            .parse()?,
        seed_peers: matches
            .values_of("seed-peer")
            .into_iter()
            .flatten()
            .map(|s| Ok(s.parse()?))
            .collect::<Result<Vec<_>>>()?
            .as_slice(),
    });
    loop {
        std::thread::park();
    }
}
