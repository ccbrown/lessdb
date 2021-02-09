# elastikv

ElastiKV is a key-value store meant to be similar to DynamoDB in scale and robustness, but with significantly higher performance.

## Features

* Redundant Storage: All data is replicated at least 3 times across distinct data centers.
* Large Capacity: The store can grow to petabytes in size without significant slowdown.
* Transactions: Writes to multiple keys can be done with strong consistency and all-or-nothing conditionals.
* Low Latency: Speeds are typically closer to Redis than to DynamoDB.
* High Availability: An availability zone outage will cause no disruption to service.
* Simple: The code is minimal enough to be quickly reviewed and understood by anyone with Rust familiarity.

## Design

### Items

All items have a unique combination of binary hash key binary range key. The
hash key is used to assign the items to partitions and the range key is used to
sort and iterate through multiple items sharing a hash key. Additionally items
can have a second range key for an additional sort dimension. The equivalent
DynamoDB schema looks like this:

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

### Partitions

Each item is assigned to one of 65536 partitions based on its hash key. Each
partition is replicated to at least 3 nodes in the cluster. As nodes join and
leave the cluster, nodes may be moved around to balance the load. Note that
this design is subject to hot partitions in a way similar to DynamoDB, though
the thresholds at which this happens can be made be much higher.

For example, a 1PB store with uniformly distributed hash keys will have
partitions that are about 15GB in size. If this store uses 200 nodes, each
will own about 1000 partitions and require about 15TB of storage. At this scale,
bringing new nodes into the cluster would take considerable time, but requests
should remain nearly as fast as any other scale cluster.

### Partition Table

Each node in the cluster is capable of receiving requests. In order to know
where to route those requests, the nodes maintain a copy of the partition
table. This table is used to look up the addresses of the nodes that contain
the partitions required to fulfil the request.
