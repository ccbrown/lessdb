# lessdb

LessDB is a key-value store meant to be similar to DynamoDB in scale and robustness, but with significantly higher performance.

## Goals

* Redundant Storage: All data is replicated at least 3 times across distinct data centers.
* Large Capacity: The store can grow to petabytes in size without significant slowdown.
* Transactions: Writes to multiple keys can be done with strong consistency and all-or-nothing conditionals.
* Low Latency: Speeds are typically closer to Redis than to DynamoDB.
* High Availability: An availability zone outage will cause no disruption to service.
* Simple: The code is minimal enough to be quickly reviewed and understood by anyone with Rust familiarity.

## Design

### Items

All underlying items have a unique combination of binary hash key binary sort
key. The hash key is used to assign the items to partitions and the sort key is
used to sort and iterate through multiple items sharing a hash key.
Additionally items can have a second sort key for an additional sort dimension.
The equivalent DynamoDB schema looks like this:

```yaml
DynamoDBTable:
  Type: AWS::DynamoDB::Table
  Properties:
    AttributeDefinitions:
      - AttributeName: hk
        AttributeType: B
      - AttributeName: rk
        AttributeType: B
      - AttributeName: rk2
        AttributeType: B
    KeySchema:
      - AttributeName: hk
        KeyType: HASH
      - AttributeName: rk
        KeyType: RANGE
    LocalSecondaryIndexes:
      - IndexName: rk2
        KeySchema:
          - AttributeName: hk
            KeyType: HASH
          - AttributeName: rk2
            KeyType: RANGE
        Projection:
          ProjectionType: ALL
```

The hash key is an actual 32-byte hash. It is computed by clients, so the
server is agnostic to the hashing mechanism itself, but SHA-256 is a reasonable
choice.

Items can contain one of the following values:

* A binary blob.
* An integer.
* A set of values.

To clients most of these details are completely abstracted away into a higher
level Redis-like API.

### Partitions

Each item is assigned to one of 4096 partitions based on the first two bytes of
its hash key. Each partition is replicated to at least 3 nodes in the cluster.
As nodes join and leave the cluster, nodes may be moved around to balance the
load. Note that this design is subject to hot partitions in a way similar to
DynamoDB, though the thresholds at which this happens can be made be much
higher.

For example, a 1PB store with uniformly distributed hash keys will have
partitions that are about 244GB in size. If this store uses 200 nodes, each
will own about 61 partitions and require about 15TB of storage. At this scale,
bringing new nodes into the cluster would take considerable time, but requests
should remain nearly as fast as any other scale cluster.

Partitions consist of an append-only "2D" B+tree where each modification
appends a new root node to the partition. The "2D" B+tree is actually just two
B+trees combined into one data structure. Items that have a secondary sort key
are inserted into the secondary B+tree so they can be accessed based on this
second dimension.

### Client API

The client API is a simple MessagePack TCP API: Clients open a connection, send
a request, then get a response. A single connection can be used for multiple
requests, but requests will be served sequentially.
