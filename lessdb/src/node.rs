use super::{
    cache::Cache,
    partition::{Hash, Key, Partition, PrimaryKey, Scalar, SecondaryKey, Sort, Value},
};
use anyhow::{Context, Result};
use std::{
    collections::HashSet,
    convert::TryInto,
    ops::{Bound, RangeBounds},
    path::Path,
    sync::{Arc, RwLock},
};

const PARTITION_COUNT: usize = 1 << 12;

pub fn partition_number(hash: &Hash) -> usize {
    (u16::from_be_bytes(
        hash.as_ref()[..2]
            .try_into()
            .expect("hashes always have at least 2 bytes"),
    ) & 0xfff) as _
}

pub struct Node {
    partitions: Vec<RwLock<Partition>>,
}

pub enum AppendCondition {
    ContainsValue(bool),
}

impl AppendCondition {
    pub fn evaluate(&self, existing: &HashSet<&Value>, to_append: &Value) -> bool {
        match *self {
            Self::ContainsValue(contains) => contains == existing.contains(to_append),
        }
    }
}

pub enum FilterPredicate {
    NotIn(Vec<Value>),
}

impl FilterPredicate {
    pub fn evaluate(&self, values: Vec<Value>) -> Vec<Value> {
        match self {
            Self::NotIn(to_remove) => {
                let to_remove: HashSet<&Value> = to_remove.into_iter().collect();
                values
                    .into_iter()
                    .filter(|v| !to_remove.contains(v))
                    .collect()
            }
        }
    }
}

pub enum SetCondition {
    Exists(bool),
    Equals(Value),
}

impl SetCondition {
    pub fn evaluate(&self, value: Option<&Value>) -> bool {
        match self {
            Self::Exists(exists) => *exists == value.is_some(),
            Self::Equals(other) => value == Some(other),
        }
    }
}

impl Node {
    pub fn new<P: AsRef<Path>>(data_path: P) -> Result<Self> {
        let cache = Arc::new(Cache::new());
        Ok(Self {
            partitions: (0..PARTITION_COUNT)
                .map(|i| {
                    Ok(RwLock::new(
                        Partition::open(
                            data_path.as_ref().join(format!("partition-{:08}", i)),
                            i as _,
                            cache.clone(),
                        )
                        .with_context(|| format!("unable to open partition {}", i))?,
                    ))
                })
                .collect::<Result<_>>()?,
        })
    }

    /// Individually clears each partition. This is equivalent to deleting everything one-by-one,
    /// but is faster and is atomic within each partition. This is intended for development
    /// purposes and there's probably no good reason to use it production.
    pub fn clear_partitions(&self) -> Result<()> {
        for partition in &self.partitions {
            let mut partition = partition.write().expect("the lock shouldn't be poisoned");
            partition.commit(|tree| Ok(tree.clear()?))?;
        }
        Ok(())
    }

    pub fn get(&self, key: &Hash) -> Result<Option<Value>> {
        let partition = &self.partitions[partition_number(key)];
        let partition = partition.read().expect("the lock shouldn't be poisoned");

        let value = partition.tree().get(&PrimaryKey {
            hash: key.clone(),
            sort: Sort::Min,
        })?;
        Ok(value)
    }

    pub fn set(&self, key: Hash, value: Value, condition: Option<SetCondition>) -> Result<bool> {
        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.write().expect("the lock shouldn't be poisoned");

        let mut did_set = false;
        partition.commit(|tree| {
            Ok(tree.insert(
                Key {
                    primary: PrimaryKey {
                        hash: key.clone(),
                        sort: Sort::Min,
                    },
                    secondary_sort: None,
                },
                |prev| {
                    if condition.map(|cond| cond.evaluate(prev)).unwrap_or(true) {
                        did_set = true;
                        Some(value)
                    } else {
                        None
                    }
                },
            )?)
        })?;
        Ok(did_set)
    }

    pub fn delete(&self, key: &Hash) -> Result<bool> {
        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.write().expect("the lock shouldn't be poisoned");

        let mut did_delete = false;
        partition.commit(|tree| {
            let (tree, prev) = tree.delete(&PrimaryKey {
                hash: key.clone(),
                sort: Sort::Min,
            })?;
            did_delete = prev.is_some();
            Ok(tree)
        })?;
        Ok(did_delete)
    }

    /// Appends one or more members to an array. The array is created if you add a value to an
    /// array that doesn't exist.
    pub fn append<I: IntoIterator<Item = Value>>(
        &self,
        key: Hash,
        values: I,
        condition: Option<AppendCondition>,
    ) -> Result<()> {
        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.write().expect("the lock shouldn't be poisoned");

        partition.commit(|tree| {
            Ok(tree.insert(
                Key {
                    primary: PrimaryKey {
                        hash: key,
                        sort: Sort::Min,
                    },
                    secondary_sort: None,
                },
                |prev| match prev {
                    Some(Value::Array(existing)) => {
                        let existing_set: HashSet<&Value> = existing.into_iter().collect();

                        let to_add: Vec<_> = values
                            .into_iter()
                            .filter(|v| {
                                condition
                                    .as_ref()
                                    .map(|c| c.evaluate(&existing_set, v))
                                    .unwrap_or(true)
                            })
                            .collect();

                        if !to_add.is_empty() {
                            let mut new_values = existing.clone();
                            for m in to_add {
                                new_values.push(m);
                            }
                            Some(Value::Array(new_values))
                        } else {
                            None
                        }
                    }
                    _ => {
                        let to_add: Vec<_> = values
                            .into_iter()
                            .filter(|v| {
                                condition
                                    .as_ref()
                                    .map(|c| c.evaluate(&HashSet::new(), v))
                                    .unwrap_or(true)
                            })
                            .collect();
                        if !to_add.is_empty() {
                            Some(Value::Array(to_add))
                        } else {
                            None
                        }
                    }
                },
            )?)
        })?;
        Ok(())
    }

    /// Filters the array with the given key if it exists.
    pub fn filter(&self, key: Hash, predicate: FilterPredicate) -> Result<()> {
        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.write().expect("the lock shouldn't be poisoned");

        partition.commit(|tree| {
            Ok(tree.insert(
                Key {
                    primary: PrimaryKey {
                        hash: key,
                        sort: Sort::Min,
                    },
                    secondary_sort: None,
                },
                |prev| match prev {
                    Some(Value::Array(values)) => {
                        let new_values = predicate.evaluate(values.clone());
                        if new_values.len() < values.len() {
                            Some(Value::Array(new_values))
                        } else {
                            None
                        }
                    }
                    _ => None,
                },
            )?)
        })?;
        Ok(())
    }

    /// Adds or updates a field in a map.
    pub fn map_set(&self, key: Hash, field: Scalar, value: Value, order: Scalar) -> Result<()> {
        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.write().expect("the lock shouldn't be poisoned");

        partition.commit(|tree| {
            Ok(tree.insert(
                Key {
                    primary: PrimaryKey {
                        hash: key,
                        sort: field.into(),
                    },
                    secondary_sort: Some(order.into()),
                },
                |_| Some(value),
            )?)
        })?;
        Ok(())
    }

    /// Removes a field from a map.
    pub fn map_delete(&self, key: Hash, field: Scalar) -> Result<bool> {
        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.write().expect("the lock shouldn't be poisoned");

        let mut did_delete = false;
        partition.commit(|tree| {
            let (tree, prev) = tree.delete(&PrimaryKey {
                hash: key,
                sort: field.into(),
            })?;
            did_delete = prev.is_some();
            Ok(tree)
        })?;
        Ok(did_delete)
    }

    fn map_range_bounds<B: RangeBounds<Scalar>>(
        key: Hash,
        bounds: B,
    ) -> (Bound<SecondaryKey>, Bound<SecondaryKey>) {
        let start = match bounds.start_bound() {
            Bound::Unbounded => Bound::Included(SecondaryKey {
                hash: key.clone(),
                secondary_sort: Sort::Min,
                primary_sort: Sort::Min,
            }),
            Bound::Included(sort) => Bound::Included(SecondaryKey {
                hash: key.clone(),
                secondary_sort: Sort::Scalar(sort.clone()),
                primary_sort: Sort::Min,
            }),
            Bound::Excluded(sort) => Bound::Excluded(SecondaryKey {
                hash: key.clone(),
                secondary_sort: Sort::Scalar(sort.clone()),
                primary_sort: Sort::Min,
            }),
        };

        let end = match bounds.end_bound() {
            Bound::Unbounded => Bound::Included(SecondaryKey {
                hash: key,
                secondary_sort: Sort::Max,
                primary_sort: Sort::Max,
            }),
            Bound::Included(sort) => Bound::Included(SecondaryKey {
                hash: key,
                secondary_sort: Sort::Scalar(sort.clone()),
                primary_sort: Sort::Max,
            }),
            Bound::Excluded(sort) => Bound::Excluded(SecondaryKey {
                hash: key,
                secondary_sort: Sort::Scalar(sort.clone()),
                primary_sort: Sort::Max,
            }),
        };

        (start, end)
    }

    /// Gets entries in a map sorted by their prescribed order.
    pub fn map_get_range<B: RangeBounds<Scalar>>(
        &self,
        key: Hash,
        bounds: B,
        limit: Option<usize>,
        reverse: bool,
    ) -> Result<Vec<Value>> {
        let partition = &self.partitions[partition_number(&key)];
        let (start, end) = Self::map_range_bounds(key, bounds);

        let partition = partition.read().expect("the lock shouldn't be poisoned");

        let tree = partition.tree();
        let range = tree.get_range_by_secondary_key((start, end));

        match (limit, reverse) {
            (Some(limit), true) => range.rev().take(limit).collect(),
            (Some(limit), false) => range.take(limit).collect(),
            (None, true) => range.rev().collect(),
            (None, false) => range.collect(),
        }
    }

    /// Counts entries in a map sorted by their prescribed order.
    pub fn map_count_range<B: RangeBounds<Scalar>>(&self, key: Hash, bounds: B) -> Result<u64> {
        let partition = &self.partitions[partition_number(&key)];
        let (start, end) = Self::map_range_bounds(key, bounds);

        let partition = partition.read().expect("the lock shouldn't be poisoned");
        partition.tree().count_range_by_secondary_key((start, end))
    }

    fn map_range_by_field_bounds<B: RangeBounds<Scalar>>(
        key: Hash,
        bounds: B,
    ) -> (Bound<PrimaryKey>, Bound<PrimaryKey>) {
        let start = match bounds.start_bound() {
            Bound::Unbounded => Bound::Included(PrimaryKey {
                hash: key.clone(),
                sort: Sort::Min,
            }),
            Bound::Included(sort) => Bound::Included(PrimaryKey {
                hash: key.clone(),
                sort: Sort::Scalar(sort.clone()),
            }),
            Bound::Excluded(sort) => Bound::Excluded(PrimaryKey {
                hash: key.clone(),
                sort: Sort::Scalar(sort.clone()),
            }),
        };

        let end = match bounds.end_bound() {
            Bound::Unbounded => Bound::Included(PrimaryKey {
                hash: key,
                sort: Sort::Max,
            }),
            Bound::Included(sort) => Bound::Included(PrimaryKey {
                hash: key,
                sort: Sort::Scalar(sort.clone()),
            }),
            Bound::Excluded(sort) => Bound::Excluded(PrimaryKey {
                hash: key,
                sort: Sort::Scalar(sort.clone()),
            }),
        };

        (start, end)
    }

    /// Gets entries in a map sorted by their fields.
    pub fn map_get_range_by_field<B: RangeBounds<Scalar>>(
        &self,
        key: Hash,
        bounds: B,
        limit: Option<usize>,
        reverse: bool,
    ) -> Result<Vec<Value>> {
        let partition = &self.partitions[partition_number(&key)];
        let (start, end) = Self::map_range_by_field_bounds(key, bounds);

        let partition = partition.read().expect("the lock shouldn't be poisoned");

        let tree = partition.tree();
        let range = tree.get_range_by_primary_key((start, end));

        match (limit, reverse) {
            (Some(limit), true) => range.rev().take(limit).collect(),
            (Some(limit), false) => range.take(limit).collect(),
            (None, true) => range.rev().collect(),
            (None, false) => range.collect(),
        }
    }

    /// Counts entries in a map sorted by their fields.
    pub fn map_count_range_by_field<B: RangeBounds<Scalar>>(
        &self,
        key: Hash,
        bounds: B,
    ) -> Result<u64> {
        let partition = &self.partitions[partition_number(&key)];
        let (start, end) = Self::map_range_by_field_bounds(key, bounds);

        let partition = partition.read().expect("the lock shouldn't be poisoned");
        partition.tree().count_range_by_primary_key((start, end))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempdir::TempDir;

    struct Test {
        node: Node,
        _dir: TempDir,
    }

    impl Test {
        pub fn new() -> Self {
            let dir = TempDir::new("partition-test").unwrap();
            Self {
                node: Node::new(dir.path()).unwrap(),
                _dir: dir,
            }
        }
    }

    #[test]
    fn test_node() {
        let t = Test::new();

        assert_eq!(t.node.get(&"foo".into()).unwrap(), None);
        assert_eq!(t.node.map_count_range("foo".into(), ..).unwrap(), 0);
    }

    #[cfg(feature = "benchmarks")]
    #[bench]
    fn bench_map_set(b: &mut test::Bencher) {
        use bytes::BytesMut;

        let t = Test::new();

        let mut hash = BytesMut::new();
        hash.resize(32, 0x00);
        let hash: Hash = hash.freeze().try_into().unwrap();

        let mut value = BytesMut::new();
        value.resize(1000, 0x20);
        let value: Value = value.freeze().into();

        let mut i = 0;
        b.iter(|| {
            t.node
                .map_set(hash.clone(), Scalar::Int(i), value.clone(), Scalar::Int(0))
                .unwrap();
            i += 1;
        });
    }
}
