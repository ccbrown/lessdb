use super::partition::{Bytes, Hash, Key, Partition, PrimaryKey};
use anyhow::{Context, Result};
use std::{convert::TryInto, path::Path, sync::Mutex};

const PARTITION_COUNT: usize = 1 << 16;

pub struct Node {
    partitions: Vec<Mutex<Partition>>,
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

    pub fn partition_number(hash: &Hash) -> usize {
        u16::from_be_bytes(
            hash.as_ref()[..2]
                .try_into()
                .expect("hashes always have at least 2 bytes"),
        ) as _
    }

    pub fn get(&self, key: &Hash) -> Result<Option<Bytes>> {
        let partition = &self.partitions[Self::partition_number(key)];
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");
        let value = partition.tree().get(&PrimaryKey {
            hash: key.clone(),
            sort: Bytes::new(),
        })?;
        Ok(value)
    }

    pub fn set(&self, key: Hash, value: Bytes) -> Result<()> {
        let partition = &self.partitions[Self::partition_number(&key)];
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");
        partition.commit(|tree| {
            tree.insert(
                Key {
                    primary: PrimaryKey {
                        hash: key.clone(),
                        sort: Bytes::new(),
                    },
                    secondary_sort: None,
                },
                value,
            )
        })?;
        Ok(())
    }

    pub fn delete(&self, key: &Hash) -> Result<()> {
        let partition = &self.partitions[Self::partition_number(&key)];
        let mut partition = partition.lock().expect("the lock shouldn't be poisoned");
        partition.commit(|tree| {
            tree.delete(&PrimaryKey {
                hash: key.clone(),
                sort: Bytes::new(),
            })
        })?;
        Ok(())
    }
}
