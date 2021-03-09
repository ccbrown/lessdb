use super::{
    append_only_file::{self, AppendOnlyFile},
    cache::{self, Cache},
};
use algorithms::b_tree::{self};
use anyhow::{Context, Error, Result};
use bytes::{Bytes, BytesMut};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    convert::TryInto,
    io::{Read, Seek, SeekFrom},
    path::Path,
    sync::{Arc, Mutex},
};

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

type BTree = b_tree::Tree<Bytes, Value>;
type BTreeNode = b_tree::Node<Bytes, Value>;

pub struct Storage {
    f: Arc<Mutex<AppendOnlyFile>>,
    tree: BTree,
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
    inner: BTree,
}

impl Tree {
    fn into_inner(self) -> BTree {
        self.inner
    }

    pub fn clear(self) -> Result<Self> {
        Ok(if self.inner.is_empty(&self.loader)? {
            self
        } else {
            Self {
                inner: BTree::new(),
                loader: self.loader,
            }
        })
    }

    pub fn get(&self, key: &Bytes) -> Result<Option<Value>> {
        Ok(self.inner.get(&self.loader, key)?)
    }

    pub fn insert<F: FnOnce(Option<&Value>) -> Option<Value>>(
        mut self,
        key: Bytes,
        value: F,
    ) -> Result<Self> {
        let (inner, _) =
            match self
                .inner
                .insert_conditionally(&mut self.loader, key, |loader, prev| {
                    let prev_value = match prev {
                        Some(prev) => Some(prev.clone().load(loader)?),
                        None => None,
                    };
                    Ok(value(prev_value.as_ref()))
                })? {
                Some(result) => result,
                None => return Ok(self),
            };
        Ok(Self {
            inner,
            loader: self.loader,
        })
    }

    pub fn delete(self, key: &Bytes) -> Result<(Self, Option<Value>)> {
        let mut loader = self.loader;
        let (inner, prev) = self.inner.delete(&mut loader, key)?;
        let prev = prev.map(|prev| prev.load(&loader)).transpose()?;
        Ok((Self { inner, loader }, prev))
    }
}

#[derive(Clone)]
pub struct Loader {
    f: Arc<Mutex<AppendOnlyFile>>,
    cache: Arc<Cache>,
}

impl<'a> b_tree::Loader<Bytes, Value> for Loader {
    type Error = Error;

    fn load_node(&self, id: u64) -> Result<BTreeNode, Self::Error> {
        self.cache.get_node(cache::Key { offset: id }, || {
            let mut f = self.f.lock().expect("the lock should not be poisoned");
            f.seek(SeekFrom::Start(id))
                .with_context(|| "unable to seek to primary node")?;
            let node: Node = rmp_serde::from_read(&mut *f)
                .with_context(|| format!("unable to deserialize primary node at offset {}", id))?;
            Ok(node.into())
        })
    }

    fn load_value(&self, id: u64) -> Result<Value, Self::Error> {
        self.cache.get_value(cache::Key { offset: id }, || {
            let mut f = self.f.lock().expect("the lock should not be poisoned");
            f.seek(SeekFrom::Start(id))
                .with_context(|| "unable to seek to value")?;
            Ok(rmp_serde::from_read(&mut *f)
                .with_context(|| format!("unable to deserialize value at offset {}", id))?)
        })
    }
}

struct SerializedTree {
    tree: BTree,
    data: Vec<u8>,
    cache_items: Vec<(u64, cache::Item)>,
}

enum SerializedNodeOrValue {
    Node(u64, BTreeNode),
    Value(u64, Value),
}

impl Storage {
    pub fn open<P: AsRef<Path>>(path: P) -> Result<Self> {
        let cache = Arc::new(Cache::new());
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
            None => BTree::new(),
        };
        let f = Arc::new(Mutex::new(f));
        Ok(Self {
            loader: Loader {
                f: f.clone(),
                cache,
            },
            f,
            tree,
        })
    }

    fn deserialize_tree<R: Read>(mut r: R) -> Result<BTree> {
        let mut buf = [0u8; 8];
        r.read_exact(&mut buf)
            .with_context(|| "error reading tree bytes")?;
        Ok(BTree::Persisted {
            id: u64::from_be_bytes((buf.as_ref()).try_into().expect("we know this is 8 bytes")),
        })
    }

    fn serialize_tree(tree: BTree, offset: u64) -> Result<SerializedTree> {
        let mut buf = vec![0; 8];
        let mut value_ids = HashMap::new();
        let mut cache_items = Vec::new();
        let offset =
            Self::serialize_b_tree(tree, offset, &mut buf, &mut value_ids, &mut cache_items, 0)?;
        buf[..8].copy_from_slice(&offset.to_be_bytes());
        Ok(SerializedTree {
            tree: BTree::Persisted { id: offset },
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
        tree: BTree,
        dest_offset: u64,
        dest: &mut Vec<u8>,
        mut value_ids: &mut HashMap<Value, u64>,
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
        value: b_tree::Value<Value>,
        dest_offset: u64,
        dest: &mut Vec<u8>,
        value_ids: &mut HashMap<Value, u64>,
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
    pub fn commit<F: FnOnce(Tree) -> Result<Option<Tree>>>(&mut self, f: F) -> Result<()> {
        let tree = match f(Tree {
            loader: self.loader.clone(),
            inner: self.tree.clone(),
        })? {
            Some(tree) => tree,
            None => return Ok(()),
        };
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
                self.loader.cache.insert(cache::Key { offset }, item)
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

    fn key(s: &'static str) -> Bytes {
        s.as_bytes().into()
    }

    #[test]
    fn test_storage() {
        let dir = TempDir::new("storage-test").unwrap();
        let path = dir.path().join("storage");

        // write to the storage
        {
            let mut storage = Storage::open(&path).unwrap();

            storage
                .commit(|tree| {
                    Some(tree.insert(key("foo"), |_| Some(Value::Bytes("bar".into())))).transpose()
                })
                .unwrap();

            assert_eq!(
                storage.tree().get(&key("foo")).unwrap(),
                Some(Value::Bytes("bar".into()))
            );
        }

        // make sure the data is still there
        {
            let storage = Storage::open(&path).unwrap();

            assert_eq!(
                storage.tree().get(&key("foo")).unwrap(),
                Some(Value::Bytes("bar".into()))
            );
        }
    }

    // Let's make sure the storage is a reasonable size after our writes.
    #[test]
    fn test_storage_size() {
        let dir = TempDir::new("storage-test").unwrap();
        let path = dir.path().join("storage");

        {
            let mut storage = Storage::open(&path).unwrap();

            let mut value = BytesMut::new();
            value.resize(128, 0x22);
            let value: Value = value.freeze().try_into().unwrap();

            for i in 0u32..200 {
                let i_bytes = i.to_be_bytes();

                let mut key = BytesMut::new();
                key.resize(32, 0x33);
                key.extend_from_slice(&i_bytes);
                let key = key.freeze();

                storage
                    .commit(|tree| Some(tree.insert(key, |_| Some(value.clone()))).transpose())
                    .unwrap();
            }
        }

        let f = AppendOnlyFile::open(path).unwrap();
        assert_eq!(
            f.size(),
            90109,
            "last entry size = {}",
            f.size() - f.last_entry_offset().unwrap()
        );
    }
}
