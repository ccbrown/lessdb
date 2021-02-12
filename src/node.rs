use super::partition::{Hash, Key, Partition, PrimaryKey, Scalar, Value};
use anyhow::{Context, Result};
use bytes::Bytes;
use std::{collections::HashSet, convert::TryInto, path::Path, sync::Mutex};

const PARTITION_COUNT: usize = 1 << 16;

pub fn partition_number(hash: &Hash) -> usize {
    u16::from_be_bytes(
        hash.as_ref()[..2]
            .try_into()
            .expect("hashes always have at least 2 bytes"),
    ) as _
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
                            .with_context(|| format!("unable to create partition {}", i))?,
                    ))
                })
                .collect::<Result<_>>()?,
        })
    }

    pub fn get(&self, key: &Hash) -> Result<Option<Value>> {
        let partition = &self.partitions[partition_number(key)];
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

        let value = partition.tree().get(&PrimaryKey {
            hash: key.clone(),
            sort: Bytes::new(),
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
                        sort: Bytes::new(),
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
                sort: Bytes::new(),
            })?;
            did_delete = prev.is_some();
            Ok(tree)
        })?;
        Ok(did_delete)
    }

    pub fn increment(&self, key: Hash, amount: i64) -> Result<i64> {
        let partition = &self.partitions[partition_number(&key)];
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");

        let mut new_value = 0;
        partition.commit(|tree| {
            Ok(tree.insert(
                Key {
                    primary: PrimaryKey {
                        hash: key,
                        sort: Bytes::new(),
                    },
                    secondary_sort: None,
                },
                |prev| {
                    new_value = match prev {
                        Some(Value::Int(prev)) => prev + amount,
                        _ => amount,
                    };
                    Some(Value::Int(new_value))
                },
            )?)
        })?;
        Ok(new_value)
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
                        sort: Bytes::new(),
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
                        sort: Bytes::new(),
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
}
