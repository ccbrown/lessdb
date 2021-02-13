use super::partition::{Hash, Key, Partition, PrimaryKey, Scalar, SecondaryKey, Sort, Value};
use anyhow::{Context, Result};
use std::{
    collections::HashSet,
    convert::TryInto,
    ops::{Bound, RangeBounds},
    path::Path,
    sync::Mutex,
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
    partitions: Vec<Mutex<Partition>>,
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
        Ok(Self {
            partitions: (0..PARTITION_COUNT)
                .map(|i| {
                    Ok(Mutex::new(
                        Partition::open(data_path.as_ref().join(format!("partition-{:08}", i)))
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
            let mut partition = partition.lock().expect("the lock shouldn't be poisoned");
            partition.commit(|tree| Ok(tree.clear()?))?;
        }
        Ok(())
    }

    pub fn get(&self, key: &Hash) -> Result<Option<Value>> {
        let partition = &self.partitions[partition_number(key)];
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

        let value = partition.tree().get(&PrimaryKey {
            hash: key.clone(),
            sort: Sort::Min,
        })?;
        Ok(value)
    }

    pub fn set(&self, key: Hash, value: Value, condition: Option<SetCondition>) -> Result<bool> {
        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

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
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

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

    /// Adds one or more members to the set with the given key or creates it if it doesn't exist.
    pub fn set_add<I: IntoIterator<Item = Scalar>>(&self, key: Hash, members: I) -> Result<()> {
        let to_add: HashSet<Scalar> = members.into_iter().collect();

        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

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
                    Some(Value::Set(members)) => {
                        let mut did_add = false;
                        let mut members: HashSet<&Scalar> = members.into_iter().collect();
                        for m in &to_add {
                            if members.insert(m) {
                                did_add = true;
                            }
                        }
                        if did_add {
                            Some(Value::Set(members.into_iter().cloned().collect()))
                        } else {
                            None
                        }
                    }
                    _ => Some(Value::Set(to_add.into_iter().collect())),
                },
            )?)
        })?;
        Ok(())
    }

    /// Removes one or more members from the set with the given key if it exists.
    pub fn set_remove<I: IntoIterator<Item = Scalar>>(&self, key: Hash, members: I) -> Result<()> {
        let to_remove: HashSet<Scalar> = members.into_iter().collect();

        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

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
                    Some(Value::Set(members)) => {
                        let original_len = members.len();
                        let new_members: Vec<_> = members
                            .into_iter()
                            .filter(|m| !to_remove.contains(m))
                            .cloned()
                            .collect();
                        if new_members.len() < original_len {
                            Some(Value::Set(new_members))
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
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

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
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

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

        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

        let mut tree = partition.tree();
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

        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");
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

        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

        let mut tree = partition.tree();
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

        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");
        partition.tree().count_range_by_primary_key((start, end))
    }
}
