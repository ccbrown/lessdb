# lessdb

LessDB is a key-value store meant to be similar to DynamoDB in scale and
robustness, but with significantly higher performance at the expense of
horizontal scalability.

It's nearly feature complete for single node setups, but not really suitable
for production as high availability features are not yet implemented.

## Goals

* Redundant Storage: All data is replicated at least 3 times across distinct data centers.
* Large Capacity: The store can grow to tens of terabytes in size without significant slowdown.
* Transactions: Writes to multiple keys can be done with strong consistency and all-or-nothing conditionals.
* Low Latency: Speeds are typically closer to Redis than to DynamoDB.
* High Availability: An availability zone outage will cause no disruption to service.
* Simple: The code is minimal enough to be quickly reviewed and understood by anyone with Rust familiarity.

## Client API

Clients interact with the database via gRPC. See the protos directory for the
proto definitions.

## Development

This a Rust program. Once you have the prerequisites installed you can...

* `cargo run` to run it.
* `cargo test` to run tests.
* `(cd lessdb && cargo +nightly bench --features benchmarks)` to run benchmarks.
