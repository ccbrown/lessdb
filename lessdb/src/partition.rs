use super::{
    append_only_file::{self, AppendOnlyFile},
    cache::{self, Cache},
};
use algorithms::{
    b_tree::{self, Tree as BTree},
    indexed_b_tree::{
        self, Key as NormalizedKey, PrimaryKey as NormalizedPrimaryKey, Range,
        SecondaryKey as NormalizedSecondaryKey,
    },
};
use anyhow::{Context, Error, Result};
use bytes::{BufMut, Bytes, BytesMut};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    convert::{TryFrom, TryInto},
    io::{Read, Seek, SeekFrom},
    ops::{Bound, RangeBounds},
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
    Array(Vec<Value>),
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

impl Sort {
    fn normalize(&self) -> Bytes {
        match self {
            Self::Min => vec![0].into(),
            Self::Scalar(Scalar::Bytes(b)) => {
                let mut buf = BytesMut::with_capacity(1 + b.len());
                buf.put_u8(1);
                buf.extend_from_slice(&b);
                buf.freeze()
            }
            Self::Scalar(Scalar::Int(n)) => {
                let mut buf = BytesMut::with_capacity(1 + 8);
                buf.put_u8(2);
                buf.extend_from_slice(&u64::to_be_bytes((*n as u64) ^ 0x8000000000000000));
                buf.freeze()
            }
            Self::Max => vec![255].into(),
        }
    }
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

type IBTree = indexed_b_tree::Tree<Value>;
type IBTreeValue = indexed_b_tree::Value<Value>;

#[derive(Clone, Serialize, Deserialize)]
pub struct Key {
    pub primary: PrimaryKey,
    pub secondary_sort: Option<Sort>,
}

impl Key {
    fn normalize(&self) -> NormalizedKey {
        NormalizedKey {
            primary: self.primary.normalize(),
            secondary_sort: self.secondary_sort.as_ref().map(|s| s.normalize()),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PrimaryKey {
    pub hash: Hash,
    pub sort: Sort,
}

impl PrimaryKey {
    fn normalize(&self) -> NormalizedPrimaryKey {
        NormalizedPrimaryKey {
            hash: self.hash.0.clone(),
            sort: self.sort.normalize(),
        }
    }

    fn normalize_bound(b: Bound<&Self>) -> Bound<NormalizedPrimaryKey> {
        match b {
            Bound::Unbounded => Bound::Unbounded,
            Bound::Included(k) => Bound::Included(k.normalize()),
            Bound::Excluded(k) => Bound::Excluded(k.normalize()),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SecondaryKey {
    pub hash: Hash,
    pub secondary_sort: Sort,
    pub primary_sort: Sort,
}

impl SecondaryKey {
    fn normalize(&self) -> NormalizedSecondaryKey {
        NormalizedSecondaryKey {
            hash: self.hash.0.clone(),
            secondary_sort: self.secondary_sort.normalize(),
            primary_sort: self.primary_sort.normalize(),
        }
    }

    fn normalize_bound(b: Bound<&Self>) -> Bound<NormalizedSecondaryKey> {
        match b {
            Bound::Unbounded => Bound::Unbounded,
            Bound::Included(k) => Bound::Included(k.normalize()),
            Bound::Excluded(k) => Bound::Excluded(k.normalize()),
        }
    }
}

pub struct Partition {
    f: Arc<Mutex<AppendOnlyFile>>,
    tree: IBTree,
    loader: Loader,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Child {
    len: u64,
    offset: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Node {
    prefix: Bytes,
    body: NodeBody,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum NodeBody {
    Internal {
        index: Vec<Bytes>,
        children: Vec<Child>,
    },
    Leaf {
        keys: Vec<Bytes>,
        values: Vec<u64>,
    },
}

type BTreeNode = b_tree::Node<Bytes, IBTreeValue>;

impl Into<BTreeNode> for Node {
    fn into(self) -> BTreeNode {
        let prefix = self.prefix;
        match self.body {
            NodeBody::Internal { index, children } => b_tree::Node::Internal {
                index: index
                    .into_iter()
                    .map(|b| {
                        let mut buf = BytesMut::with_capacity(prefix.len() + b.len());
                        buf.extend_from_slice(&prefix);
                        buf.extend_from_slice(&b);
                        buf.freeze()
                    })
                    .collect(),
                children: children
                    .into_iter()
                    .map(|child| b_tree::Child {
                        len: child.len,
                        tree: b_tree::Tree::Persisted { id: child.offset },
                    })
                    .collect(),
            },
            NodeBody::Leaf { keys, values } => b_tree::Node::Leaf {
                keys: keys
                    .into_iter()
                    .map(|b| {
                        let mut buf = BytesMut::with_capacity(prefix.len() + b.len());
                        buf.extend_from_slice(&prefix);
                        buf.extend_from_slice(&b);
                        buf.freeze()
                    })
                    .collect(),
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
    inner: IBTree,
}

impl Tree {
    fn into_inner(self) -> IBTree {
        self.inner
    }

    pub fn clear(self) -> Result<Self> {
        Ok(if self.inner.is_empty(&self.loader)? {
            self
        } else {
            Self {
                inner: IBTree::new(),
                loader: self.loader,
            }
        })
    }

    pub fn get(&self, key: &PrimaryKey) -> Result<Option<Value>> {
        Ok(self.inner.get(&self.loader, &key.normalize())?)
    }

    pub fn get_range_by_primary_key<B: RangeBounds<PrimaryKey>>(
        &self,
        bounds: B,
    ) -> Range<Value, Loader, (Bound<Bytes>, Bound<Bytes>)> {
        self.inner.get_range_by_primary_key(
            &self.loader,
            (
                PrimaryKey::normalize_bound(bounds.start_bound()),
                PrimaryKey::normalize_bound(bounds.end_bound()),
            ),
        )
    }

    pub fn count_range_by_primary_key<B: RangeBounds<PrimaryKey>>(&self, bounds: B) -> Result<u64> {
        self.inner.count_range_by_primary_key(
            &self.loader,
            (
                PrimaryKey::normalize_bound(bounds.start_bound()),
                PrimaryKey::normalize_bound(bounds.end_bound()),
            ),
        )
    }

    pub fn get_range_by_secondary_key<B: RangeBounds<SecondaryKey>>(
        &self,
        bounds: B,
    ) -> Range<Value, Loader, (Bound<Bytes>, Bound<Bytes>)> {
        self.inner.get_range_by_secondary_key(
            &self.loader,
            (
                SecondaryKey::normalize_bound(bounds.start_bound()),
                SecondaryKey::normalize_bound(bounds.end_bound()),
            ),
        )
    }

    pub fn count_range_by_secondary_key<B: RangeBounds<SecondaryKey>>(
        &self,
        bounds: B,
    ) -> Result<u64> {
        self.inner.count_range_by_secondary_key(
            &self.loader,
            (
                SecondaryKey::normalize_bound(bounds.start_bound()),
                SecondaryKey::normalize_bound(bounds.end_bound()),
            ),
        )
    }

    pub fn insert<F: FnOnce(Option<&Value>) -> Option<Value>>(
        self,
        key: Key,
        value: F,
    ) -> Result<Self> {
        let mut loader = self.loader;
        Ok(Self {
            inner: self.inner.insert(&mut loader, key.normalize(), value)?,
            loader,
        })
    }

    pub fn delete(self, key: &PrimaryKey) -> Result<(Self, Option<Value>)> {
        let mut loader = self.loader;
        let (inner, prev) = self.inner.delete(&mut loader, &key.normalize())?;
        Ok((Self { inner, loader }, prev))
    }
}

#[derive(Clone)]
pub struct Loader {
    f: Arc<Mutex<AppendOnlyFile>>,
    partition: u32,
    cache: Arc<Cache>,
}

impl<'a> b_tree::Loader<Bytes, IBTreeValue> for Loader {
    type Error = Error;

    fn load_node(&self, id: u64) -> Result<b_tree::Node<Bytes, IBTreeValue>, Self::Error> {
        self.cache.get_node(
            cache::Key {
                partition: self.partition,
                offset: id,
            },
            || {
                let mut f = self.f.lock().expect("the lock should not be poisoned");
                f.seek(SeekFrom::Start(id))
                    .with_context(|| "unable to seek to primary node")?;
                let node: Node = rmp_serde::from_read(&mut *f).with_context(|| {
                    format!("unable to deserialize primary node at offset {}", id)
                })?;
                Ok(node.into())
            },
        )
    }

    fn load_value(&self, id: u64) -> Result<IBTreeValue, Self::Error> {
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
    tree: IBTree,
    data: Vec<u8>,
    cache_items: Vec<(u64, cache::Item)>,
}

enum SerializedNodeOrValue {
    Node(u64, BTreeNode),
    Value(u64, IBTreeValue),
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
            None => IBTree::new(),
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

    fn deserialize_tree<R: Read>(mut r: R) -> Result<IBTree> {
        let mut buf = [0u8; 16];
        r.read_exact(&mut buf)
            .with_context(|| "error reading tree bytes")?;
        Ok(IBTree {
            primary_tree: BTree::Persisted {
                id: u64::from_be_bytes((&buf[..8]).try_into().expect("we know this is 8 bytes")),
            },
            secondary_tree: BTree::Persisted {
                id: u64::from_be_bytes((&buf[8..]).try_into().expect("we know this is 8 bytes")),
            },
        })
    }

    fn serialize_tree(tree: IBTree, offset: u64) -> Result<SerializedTree> {
        let mut buf = vec![0; 16];
        let mut value_ids = HashMap::new();
        let mut cache_items = Vec::new();
        let primary_offset = Self::serialize_b_tree(
            tree.primary_tree,
            offset,
            &mut buf,
            &mut value_ids,
            &mut cache_items,
            0,
        )?;
        buf[..8].copy_from_slice(&primary_offset.to_be_bytes());
        let secondary_offset = Self::serialize_b_tree(
            tree.secondary_tree,
            offset,
            &mut buf,
            &mut value_ids,
            &mut cache_items,
            0,
        )?;
        buf[8..16].copy_from_slice(&secondary_offset.to_be_bytes());
        Ok(SerializedTree {
            tree: IBTree {
                primary_tree: BTree::Persisted { id: primary_offset },
                secondary_tree: BTree::Persisted {
                    id: secondary_offset,
                },
            },
            data: buf,
            cache_items: cache_items
                .into_iter()
                .map(|item| match item {
                    SerializedNodeOrValue::Node(offset, node) => (offset, cache::Item::Node(node)),
                    SerializedNodeOrValue::Value(offset, v) => (offset, cache::Item::Value(v)),
                })
                .collect(),
        })
    }

    fn node_prefix(node: &BTreeNode) -> Bytes {
        if node.len() == 0 {
            Bytes::new()
        } else {
            let (l, r) = match &node {
                b_tree::Node::Internal { index, .. } => (&index[0], &index[index.len() - 1]),
                b_tree::Node::Leaf { keys, .. } => (&keys[0], &keys[keys.len() - 1]),
            };

            let a = l.as_ref();
            let b = r.as_ref();
            let mut i = 0;
            while i < a.len() && i < b.len() && a[i] == b[i] {
                i += 1;
            }
            l.slice(0..i)
        }
    }

    fn serialize_b_tree(
        tree: BTree<Bytes, IBTreeValue>,
        dest_offset: u64,
        dest: &mut Vec<u8>,
        mut value_ids: &mut HashMap<IBTreeValue, u64>,
        mut cache_items: &mut Vec<SerializedNodeOrValue>,
        depth: u64,
    ) -> Result<u64> {
        Ok(match tree {
            BTree::Persisted { id } => id,
            BTree::Volatile { node } => {
                let shallow_node = match node {
                    b_tree::Node::Internal { index, children } => {
                        let children = children
                            .into_iter()
                            .map(|child| {
                                Ok(b_tree::Child {
                                    len: child.len,
                                    tree: b_tree::Tree::Persisted {
                                        id: Self::serialize_b_tree(
                                            child.tree,
                                            dest_offset,
                                            dest,
                                            &mut value_ids,
                                            cache_items,
                                            depth + 1,
                                        )?,
                                    },
                                })
                            })
                            .collect::<Result<Vec<_>>>()?;
                        b_tree::Node::Internal { index, children }
                    }
                    b_tree::Node::Leaf { keys, values } => {
                        let values = values
                            .into_iter()
                            .map(|value| {
                                Ok(b_tree::Value::Persisted {
                                    id: Self::serialize_b_tree_value(
                                        value,
                                        dest_offset,
                                        dest,
                                        &mut value_ids,
                                        &mut cache_items,
                                    )?,
                                })
                            })
                            .collect::<Result<Vec<_>>>()?;
                        b_tree::Node::Leaf { keys, values }
                    }
                };

                let node_out = {
                    let node = shallow_node.clone();
                    let prefix = Self::node_prefix(&node);
                    Node {
                        body: match node {
                            b_tree::Node::Internal { index, children } => {
                                let children = children
                                    .into_iter()
                                    .map(|child| {
                                        Ok(Child {
                                            len: child.len,
                                            offset: match child.tree {
                                                b_tree::Tree::Persisted { id } => id,
                                                _ => panic!(
                                                    "we should have already persisted the child"
                                                ),
                                            },
                                        })
                                    })
                                    .collect::<Result<Vec<_>>>()?;
                                NodeBody::Internal {
                                    index: index
                                        .into_iter()
                                        .map(|b| b.slice(prefix.len()..))
                                        .collect(),
                                    children,
                                }
                            }
                            b_tree::Node::Leaf { keys, values } => NodeBody::Leaf {
                                keys: keys.into_iter().map(|b| b.slice(prefix.len()..)).collect(),
                                values: values
                                    .into_iter()
                                    .map(|value| match value {
                                        b_tree::Value::Persisted { id } => id,
                                        _ => panic!("we should have already persisted the value"),
                                    })
                                    .collect(),
                            },
                        },
                        prefix: prefix,
                    }
                };

                let id = dest_offset + dest.len() as u64;
                cache_items.push(SerializedNodeOrValue::Node(id, shallow_node));
                node_out.serialize(&mut rmp_serde::Serializer::new(dest))?;
                id
            }
        })
    }

    fn serialize_b_tree_value(
        value: b_tree::Value<IBTreeValue>,
        dest_offset: u64,
        dest: &mut Vec<u8>,
        value_ids: &mut HashMap<IBTreeValue, u64>,
        cache_items: &mut Vec<SerializedNodeOrValue>,
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
    use bytes::BytesMut;
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

    // Let's make sure the partition is a reasonable size after our writes.
    #[test]
    fn test_partition_size() {
        let dir = TempDir::new("partition-test").unwrap();
        let path = dir.path().join("partition");

        {
            let mut partition = Partition::open(&path, 0, Arc::new(Cache::new())).unwrap();

            let mut hash = BytesMut::new();
            hash.resize(32, 0x11);
            let hash: Hash = hash.freeze().try_into().unwrap();

            let mut value = BytesMut::new();
            value.resize(128, 0x22);
            let value: Value = value.freeze().try_into().unwrap();

            for i in 0u32..200 {
                let i_bytes = i.to_be_bytes();

                let mut sort = BytesMut::new();
                sort.resize(32, 0x33);
                sort.extend_from_slice(&i_bytes);
                let sort: Scalar = sort.freeze().try_into().unwrap();

                let mut secondary_sort = BytesMut::new();
                secondary_sort.resize(32, 0x44);
                secondary_sort.extend_from_slice(&i_bytes);
                let secondary_sort: Scalar = secondary_sort.freeze().try_into().unwrap();

                partition
                    .commit(|tree| {
                        tree.insert(
                            Key {
                                primary: PrimaryKey {
                                    hash: hash.clone(),
                                    sort: Sort::Scalar(sort),
                                },
                                secondary_sort: Some(Sort::Scalar(secondary_sort)),
                            },
                            |_| Some(value.clone()),
                        )
                    })
                    .unwrap();
            }
        }

        let f = AppendOnlyFile::open(path).unwrap();
        assert_eq!(
            f.size(),
            268872,
            "last entry size = {}",
            f.size() - f.last_entry_offset().unwrap()
        );
    }
}
