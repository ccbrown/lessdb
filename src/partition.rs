use super::{
    append_only_file::{self, AppendOnlyFile},
    b_tree::{self, Tree as BTree},
    b_tree_2d::{self, Range},
    cache::{self, Cache},
};
use anyhow::{Context, Error, Result};
use bytes::Bytes;
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    convert::{TryFrom, TryInto},
    io::{Read, Seek, SeekFrom},
    ops::RangeBounds,
    path::Path,
    sync::{Arc, Mutex},
};

pub const HASH_LENGTH: usize = 32;

#[derive(Clone, Debug, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hash(Bytes);

#[derive(Clone, Copy, Debug, thiserror::Error)]
#[error("incorrect hash length")]
pub struct IncorrectHashLengthError;

impl TryFrom<Bytes> for Hash {
    type Error = IncorrectHashLengthError;

    fn try_from(bytes: Bytes) -> Result<Self, Self::Error> {
        if bytes.len() != HASH_LENGTH {
            Err(IncorrectHashLengthError)
        } else {
            Ok(Self(bytes))
        }
    }
}

impl AsRef<[u8]> for Hash {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

#[cfg(test)]
impl From<&str> for Hash {
    fn from(s: &str) -> Hash {
        use digest::Digest;
        let mut hasher = sha2::Sha256::new();
        hasher.update(s.as_bytes());
        Hash(hasher.finalize().to_vec().into())
    }
}

#[derive(Clone, Debug, Ord, Hash, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub enum Scalar {
    Bytes(Bytes),
    Int(i64),
}

impl From<Bytes> for Scalar {
    fn from(b: Bytes) -> Self {
        Self::Bytes(b)
    }
}

#[cfg(test)]
impl From<&str> for Scalar {
    fn from(s: &str) -> Scalar {
        Scalar::Bytes(s.as_bytes().to_vec().into())
    }
}

#[derive(Clone, Debug, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub enum Value {
    Bytes(Bytes),
    Int(i64),
    Set(Vec<Scalar>),
}

impl From<Bytes> for Value {
    fn from(b: Bytes) -> Self {
        Self::Bytes(b)
    }
}

impl From<Scalar> for Value {
    fn from(s: Scalar) -> Self {
        match s {
            Scalar::Bytes(b) => Self::Bytes(b),
            Scalar::Int(n) => Self::Int(n),
        }
    }
}

#[derive(Clone, Debug, Ord, Hash, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub enum Sort {
    Min,
    Scalar(Scalar),
    Max,
}

impl Into<Sort> for Scalar {
    fn into(self) -> Sort {
        Sort::Scalar(self)
    }
}

#[cfg(test)]
impl From<&str> for Sort {
    fn from(s: &str) -> Sort {
        Sort::Scalar(s.into())
    }
}

type BTree2D = b_tree_2d::Tree<Hash, Sort, Value>;
type BTree2DValue = b_tree_2d::Value<Sort, Value>;

pub type Key = b_tree_2d::Key<Hash, Sort>;
pub type PrimaryKey = b_tree_2d::PrimaryKey<Hash, Sort>;
pub type SecondaryKey = b_tree_2d::SecondaryKey<Hash, Sort>;

pub struct Partition {
    f: Arc<Mutex<AppendOnlyFile>>,
    tree: BTree2D,
    loader: Loader,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Child {
    len: u64,
    offset: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Node<K: Clone + Serialize> {
    Internal { index: Vec<K>, children: Vec<Child> },
    Leaf { keys: Vec<K>, values: Vec<u64> },
}

impl<K: Clone + Serialize, V: Clone> Into<b_tree::Node<K, V>> for Node<K> {
    fn into(self) -> b_tree::Node<K, V> {
        match self {
            Self::Internal { index, children } => b_tree::Node::Internal {
                index,
                children: children
                    .into_iter()
                    .map(|child| b_tree::Child {
                        len: child.len,
                        tree: b_tree::Tree::Persisted { id: child.offset },
                    })
                    .collect(),
            },
            Self::Leaf { keys, values } => b_tree::Node::Leaf {
                keys,
                values: values
                    .into_iter()
                    .map(|id| b_tree::Value::Persisted { id })
                    .collect(),
            },
        }
    }
}

pub struct Tree {
    loader: Loader,
    inner: BTree2D,
}

impl Tree {
    fn into_inner(self) -> BTree2D {
        self.inner
    }

    pub fn clear(self) -> Result<Self> {
        Ok(if self.inner.is_empty(&self.loader)? {
            self
        } else {
            Self {
                inner: BTree2D::new(),
                loader: self.loader,
            }
        })
    }

    pub fn get(&self, key: &PrimaryKey) -> Result<Option<Value>> {
        Ok(self.inner.get(&self.loader, key)?)
    }

    pub fn get_range_by_primary_key<B: RangeBounds<PrimaryKey>>(
        &self,
        bounds: B,
    ) -> Range<PrimaryKey, Sort, Value, Loader, B> {
        self.inner.get_range_by_primary_key(&self.loader, bounds)
    }

    pub fn count_range_by_primary_key<B: RangeBounds<PrimaryKey>>(&self, bounds: B) -> Result<u64> {
        self.inner.count_range_by_primary_key(&self.loader, bounds)
    }

    pub fn get_range_by_secondary_key<B: RangeBounds<SecondaryKey>>(
        &self,
        bounds: B,
    ) -> Range<SecondaryKey, Sort, Value, Loader, B> {
        self.inner.get_range_by_secondary_key(&self.loader, bounds)
    }

    pub fn count_range_by_secondary_key<B: RangeBounds<SecondaryKey>>(
        &self,
        bounds: B,
    ) -> Result<u64> {
        self.inner
            .count_range_by_secondary_key(&self.loader, bounds)
    }

    pub fn insert<F: FnOnce(Option<&Value>) -> Option<Value>>(
        self,
        key: Key,
        value: F,
    ) -> Result<Self> {
        let mut loader = self.loader;
        Ok(Self {
            inner: self.inner.insert(&mut loader, key, value)?,
            loader,
        })
    }

    pub fn delete(self, key: &PrimaryKey) -> Result<(Self, Option<Value>)> {
        let mut loader = self.loader;
        let (inner, prev) = self.inner.delete(&mut loader, key)?;
        Ok((Self { inner, loader }, prev))
    }
}

#[derive(Clone)]
pub struct Loader {
    f: Arc<Mutex<AppendOnlyFile>>,
    partition: u32,
    cache: Arc<Cache>,
}

impl<'a> b_tree_2d::Loader<Hash, Sort, Value> for Loader {
    type Error = Error;

    fn load_primary_node(
        &self,
        id: u64,
    ) -> Result<b_tree_2d::PrimaryNode<Hash, Sort, Value>, Self::Error> {
        self.cache.get_primary_node(
            cache::Key {
                partition: self.partition,
                offset: id,
            },
            || {
                let mut f = self.f.lock().expect("the lock should not be poisoned");
                f.seek(SeekFrom::Start(id))
                    .with_context(|| "unable to seek to primary node")?;
                let node: Node<_> = rmp_serde::from_read(&mut *f).with_context(|| {
                    format!("unable to deserialize primary node at offset {}", id)
                })?;
                Ok(node.into())
            },
        )
    }

    fn load_secondary_node(
        &self,
        id: u64,
    ) -> Result<b_tree_2d::SecondaryNode<Hash, Sort, Value>, Self::Error> {
        self.cache.get_secondary_node(
            cache::Key {
                partition: self.partition,
                offset: id,
            },
            || {
                let mut f = self.f.lock().expect("the lock should not be poisoned");
                f.seek(SeekFrom::Start(id))
                    .with_context(|| "unable to seek to secondary node")?;
                let node: Node<_> = rmp_serde::from_read(&mut *f).with_context(|| {
                    format!("unable to deserialize secondary node at offset {}", id)
                })?;
                Ok(node.into())
            },
        )
    }

    fn load_value(&self, id: u64) -> Result<BTree2DValue, Self::Error> {
        self.cache.get_value(
            cache::Key {
                partition: self.partition,
                offset: id,
            },
            || {
                let mut f = self.f.lock().expect("the lock should not be poisoned");
                f.seek(SeekFrom::Start(id))
                    .with_context(|| "unable to seek to value")?;
                Ok(rmp_serde::from_read(&mut *f)
                    .with_context(|| format!("unable to deserialize value at offset {}", id))?)
            },
        )
    }
}

struct SerializedTree {
    tree: BTree2D,
    data: Vec<u8>,
    cache_items: Vec<(u64, cache::Item)>,
}

enum SerializedNodeOrValue<K: Clone> {
    Node(u64, b_tree::Node<K, BTree2DValue>),
    Value(u64, BTree2DValue),
}

impl Partition {
    pub fn open<P: AsRef<Path>>(path: P, number: u32, cache: Arc<Cache>) -> Result<Self> {
        let mut f =
            AppendOnlyFile::open(path).with_context(|| "unable to open append-only file")?;
        let tree = match f.last_entry_offset() {
            Some(offset) => {
                (&mut f)
                    .seek(SeekFrom::Start(
                        offset + append_only_file::ENTRY_PREFIX_LENGTH as u64,
                    ))
                    .with_context(|| "unable to seek to latest entry")?;
                Self::deserialize_tree(&mut f).with_context(|| "unable to deserialize tree")?
            }
            None => BTree2D::new(),
        };
        let f = Arc::new(Mutex::new(f));
        Ok(Self {
            loader: Loader {
                f: f.clone(),
                partition: number,
                cache,
            },
            f,
            tree,
        })
    }

    fn deserialize_tree<R: Read>(mut r: R) -> Result<BTree2D> {
        let mut buf = [0u8; 16];
        r.read_exact(&mut buf)
            .with_context(|| "error reading tree bytes")?;
        Ok(BTree2D {
            primary_tree: BTree::Persisted {
                id: u64::from_be_bytes((&buf[..8]).try_into().expect("we know this is 8 bytes")),
            },
            secondary_tree: BTree::Persisted {
                id: u64::from_be_bytes((&buf[8..]).try_into().expect("we know this is 8 bytes")),
            },
        })
    }

    fn serialize_tree(tree: BTree2D, offset: u64) -> Result<SerializedTree> {
        let mut buf = vec![0; 16];
        let mut value_ids = HashMap::new();
        let mut primary_cache_items = Vec::new();
        let primary_offset = Self::serialize_b_tree(
            tree.primary_tree,
            offset,
            &mut buf,
            &mut value_ids,
            &mut primary_cache_items,
        )?;
        buf[..8].copy_from_slice(&primary_offset.to_be_bytes());
        let mut secondary_cache_items = Vec::new();
        let secondary_offset = Self::serialize_b_tree(
            tree.secondary_tree,
            offset,
            &mut buf,
            &mut value_ids,
            &mut secondary_cache_items,
        )?;
        buf[8..16].copy_from_slice(&secondary_offset.to_be_bytes());
        Ok(SerializedTree {
            tree: BTree2D {
                primary_tree: BTree::Persisted { id: primary_offset },
                secondary_tree: BTree::Persisted {
                    id: secondary_offset,
                },
            },
            data: buf,
            cache_items: primary_cache_items
                .into_iter()
                .map(|item| match item {
                    SerializedNodeOrValue::Node(offset, node) => {
                        (offset, cache::Item::PrimaryNode(node))
                    }
                    SerializedNodeOrValue::Value(offset, v) => (offset, cache::Item::Value(v)),
                })
                .chain(secondary_cache_items.into_iter().map(|item| match item {
                    SerializedNodeOrValue::Node(offset, node) => {
                        (offset, cache::Item::SecondaryNode(node))
                    }
                    SerializedNodeOrValue::Value(offset, v) => (offset, cache::Item::Value(v)),
                }))
                .collect(),
        })
    }

    fn serialize_b_tree<K: Clone + Serialize>(
        tree: BTree<K, BTree2DValue>,
        dest_offset: u64,
        dest: &mut Vec<u8>,
        mut value_ids: &mut HashMap<BTree2DValue, u64>,
        mut cache_items: &mut Vec<SerializedNodeOrValue<K>>,
    ) -> Result<u64> {
        Ok(match tree {
            BTree::Persisted { id } => id,
            BTree::Volatile { node } => {
                let node_out = match node.clone() {
                    b_tree::Node::Internal { index, children } => {
                        let children = children
                            .into_iter()
                            .map(|child| {
                                Ok(Child {
                                    len: child.len,
                                    offset: Self::serialize_b_tree(
                                        child.tree,
                                        dest_offset,
                                        dest,
                                        &mut value_ids,
                                        cache_items,
                                    )?,
                                })
                            })
                            .collect::<Result<Vec<_>>>()?;
                        Node::Internal { index, children }
                    }
                    b_tree::Node::Leaf { keys, values } => {
                        let values = values
                            .into_iter()
                            .map(|value| {
                                Self::serialize_b_tree_value(
                                    value,
                                    dest_offset,
                                    dest,
                                    &mut value_ids,
                                    &mut cache_items,
                                )
                            })
                            .collect::<Result<Vec<_>>>()?;
                        Node::Leaf { keys, values }
                    }
                };
                let id = dest_offset + dest.len() as u64;
                cache_items.push(SerializedNodeOrValue::Node(id, node));
                node_out.serialize(&mut rmp_serde::Serializer::new(dest))?;
                id
            }
        })
    }

    fn serialize_b_tree_value<K: Clone>(
        value: b_tree::Value<BTree2DValue>,
        dest_offset: u64,
        dest: &mut Vec<u8>,
        value_ids: &mut HashMap<BTree2DValue, u64>,
        cache_items: &mut Vec<SerializedNodeOrValue<K>>,
    ) -> Result<u64> {
        Ok(match value {
            b_tree::Value::Persisted { id } => id,
            b_tree::Value::Volatile { value } => match value_ids.get(&value) {
                Some(id) => *id,
                None => {
                    let id = dest_offset + dest.len() as u64;
                    value_ids.insert(value.clone(), id);
                    value.serialize(&mut rmp_serde::Serializer::new(dest))?;
                    cache_items.push(SerializedNodeOrValue::Value(id, value));
                    id
                }
            },
        })
    }

    /// Gets a snapshot of the tree, which can be used for reads.
    pub fn tree(&self) -> Tree {
        Tree {
            loader: self.loader.clone(),
            inner: self.tree.clone(),
        }
    }

    /// Makes a modification to the tree and commits it to disk.
    pub fn commit<F: FnOnce(Tree) -> Result<Tree>>(&mut self, f: F) -> Result<()> {
        let tree = f(Tree {
            loader: self.loader.clone(),
            inner: self.tree.clone(),
        })?;
        let tree = tree.into_inner();
        if !tree.is_persisted() {
            let mut f = self.f.lock().expect("the lock should not be poisoned");
            // TODO: we should serialize before locking the file
            let tree = Self::serialize_tree(
                tree,
                f.size() + append_only_file::ENTRY_PREFIX_LENGTH as u64,
            )
            .with_context(|| "unable to serialize tree")?;
            f.append(&tree.data)
                .with_context(|| "unable to append tree to append-only file")?;
            self.tree = tree.tree;
            for (offset, item) in tree.cache_items.into_iter() {
                self.loader.cache.insert(
                    cache::Key {
                        partition: self.loader.partition,
                        offset,
                    },
                    item,
                )
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempdir::TempDir;

    fn primary_key(hash: &'static str, sort: &'static str) -> PrimaryKey {
        PrimaryKey {
            hash: hash.into(),
            sort: sort.into(),
        }
    }

    fn key(hash: &'static str, sort: &'static str, sort2: Option<&'static str>) -> Key {
        Key {
            primary: primary_key(hash, sort),
            secondary_sort: sort2.map(|sort| sort.into()),
        }
    }

    #[test]
    fn test_partition() {
        let dir = TempDir::new("partition-test").unwrap();
        let path = dir.path().join("partition");

        // write to the partition
        {
            let mut partition = Partition::open(&path, 0, Arc::new(Cache::new())).unwrap();

            partition
                .commit(|tree| {
                    tree.insert(key("foo", "a", None), |_| Some(Value::Bytes("bar".into())))
                })
                .unwrap();

            assert_eq!(
                partition.tree().get(&primary_key("foo", "a")).unwrap(),
                Some(Value::Bytes("bar".into()))
            );
        }

        // make sure the data is still there
        {
            let partition = Partition::open(&path, 0, Arc::new(Cache::new())).unwrap();

            assert_eq!(
                partition.tree().get(&primary_key("foo", "a")).unwrap(),
                Some(Value::Bytes("bar".into()))
            );
        }
    }

    // When we insert a value with a secondary sort key, it gets inserted into both trees. Let's
    // make sure we're not actually writing that value to the file twice though.
    #[test]
    fn test_partition_value_deduplication() {
        let dir = TempDir::new("partition-test").unwrap();
        let path = dir.path().join("partition");

        {
            let mut partition = Partition::open(&path, 0, Arc::new(Cache::new())).unwrap();
            partition
                .commit(|tree| {
                    tree.insert(key("foo", "1", Some("2")), |_| {
                        Some(Value::Bytes("dedupme".into()))
                    })
                })
                .unwrap();
        }

        let mut f = std::fs::File::open(path).unwrap();
        let mut buf = Vec::new();
        f.read_to_end(&mut buf).unwrap();

        assert_eq!(
            buf.windows(7)
                .filter(|b| *b == "dedupme".as_bytes())
                .count(),
            1
        );
    }
}
