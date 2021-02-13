#![cfg_attr(feature = "benchmarks", feature(test))]
#[cfg(feature = "benchmarks")]
extern crate test;
#[macro_use]
extern crate slog;

use anyhow::Result;
use clap::{App, Arg};
use slog::Drain;
use std::os::unix::io::AsRawFd;
use std::sync::Arc;

mod append_only_file;
mod b_tree;
mod b_tree_2d;
mod cache;
mod client;
mod node;
mod partition;
mod protos;

use node::Node;

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

    let stderr = std::io::stderr();
    let drain: Box<dyn Drain<Ok = (), Err = std::io::Error> + Send> =
        match termios::Termios::from_fd(stderr.as_raw_fd() as _) {
            Ok(_) => {
                let decorator = slog_term::TermDecorator::new().build();
                Box::new(slog_term::FullFormat::new(decorator).build())
            }
            Err(_) => Box::new(slog_json::Json::default(stderr)),
        };

    let drain = slog_async::Async::new(drain.fuse())
        .build()
        .filter_level(if matches.is_present("verbose") {
            slog::Level::Debug
        } else {
            slog::Level::Info
        })
        .fuse();

    let logger = slog::Logger::root(drain, o!());

    let node = Arc::new(Node::new(
        matches.value_of("data").expect("this argument is required"),
    )?);

    let client_listen_addr = matches
        .value_of("client-listen-addr")
        .expect("this argument is required");
    let _client_api = client::API::new(logger, node, client_listen_addr);

    loop {
        std::thread::park();
    }
}
