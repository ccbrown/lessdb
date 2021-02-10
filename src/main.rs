use anyhow::Result;
use clap::{App, Arg};

mod append_only_file;
mod b_tree;
mod client;
mod node;
mod partition;

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
    });
    loop {
        std::thread::park();
    }
}
