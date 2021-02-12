use super::{
    append_only_file::{self, AppendOnlyFile},
    b_tree::{self, Tree as BTree},
    b_tree_2d,
};
use anyhow::{Context, Error, Result};
use bytes::Bytes;
use serde::{Deserialize, Serialize};
use std::{
    convert::{TryFrom, TryInto},
    io::{Read, Seek, SeekFrom},
    path::Path,
};

pub const HASH_LENGTH: usize = 32;

#[derive(Clone, Debug, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hash(Bytes);

#[derive(Clone, Copy, Debug, thiserror::Error)]
#[error("incorrect hash length")]
pub struct IncorrectHashLength;

impl TryFrom<Bytes> for Hash {
    type Error = IncorrectHashLength;

    fn try_from(bytes: Bytes) -> Result<Self, Self::Error> {
        if bytes.len() != HASH_LENGTH {
            Err(IncorrectHashLength)
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

#[derive(Clone, Debug, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub enum Value {
    Bytes(Bytes),
    Int(i64),
    Set(Vec<Scalar>),
}

type BTree2D = b_tree_2d::Tree<Hash, Bytes, Value>;

pub type Key = b_tree_2d::Key<Hash, Bytes>;
pub type PrimaryKey = b_tree_2d::PrimaryKey<Hash, Bytes>;

pub struct Partition {
    f: AppendOnlyFile,
    tree: BTree2D,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum Node<K: Clone + Serialize> {
    Internal { index: Vec<K>, children: Vec<u64> },
    Leaf { keys: Vec<K>, values: Vec<u64> },
}

impl<K: Clone + Serialize, V: Clone> Into<b_tree::Node<K, V>> for Node<K> {
    fn into(self) -> b_tree::Node<K, V> {
        match self {
            Self::Internal { index, children } => b_tree::Node::Internal {
                index,
                children: children
                    .into_iter()
                    .map(|id| b_tree::Tree::Persisted { id })
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

pub struct Tree<'a> {
    loader: Loader<'a>,
    inner: BTree2D,
}

impl<'a> Tree<'a> {
    fn into_inner(self) -> BTree2D {
        self.inner
    }

    pub fn get(&mut self, key: &PrimaryKey) -> Result<Option<Value>> {
        Ok(self.inner.get(&mut self.loader, key)?)
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

struct Loader<'a>(&'a mut AppendOnlyFile);

impl<'a> b_tree_2d::Loader<Hash, Bytes, Value> for Loader<'a> {
    type Error = Error;

    fn load_primary_node(
        &mut self,
        id: u64,
    ) -> Result<b_tree_2d::PrimaryNode<Hash, Bytes, Value>, Self::Error> {
        self.0
            .seek(SeekFrom::Start(id))
            .with_context(|| "unable to seek to primary node")?;
        let node: Node<_> = rmp_serde::from_read(&mut self.0)
            .with_context(|| format!("unable to deserialize primary node at offset {}", id))?;
        Ok(node.into())
    }

    fn load_secondary_node(
        &mut self,
        id: u64,
    ) -> Result<b_tree_2d::SecondaryNode<Hash, Bytes, Value>, Self::Error> {
        self.0
            .seek(SeekFrom::Start(id))
            .with_context(|| "unable to seek to secondary node")?;
        let node: Node<_> = rmp_serde::from_read(&mut self.0)
            .with_context(|| format!("unable to deserialize secondary node at offset {}", id))?;
        Ok(node.into())
    }

    fn load_value(&mut self, id: u64) -> Result<b_tree_2d::Value<Bytes, Value>, Self::Error> {
        self.0
            .seek(SeekFrom::Start(id))
            .with_context(|| "unable to seek to value")?;
        Ok(rmp_serde::from_read(&mut self.0)
            .with_context(|| format!("unable to deserialize value at offset {}", id))?)
    }
}

impl Partition {
    pub fn open<P: AsRef<Path>>(path: P) -> Result<Self> {
        let mut f =
            AppendOnlyFile::open(path).with_context(|| "unable to create append-only file")?;
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
        Ok(Self { f, tree })
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

    fn serialize_tree(tree: BTree2D, offset: u64) -> Result<(BTree2D, Vec<u8>)> {
        // TODO: currently values may be serialized into both trees. we should deduplicate that.
        let mut buf = vec![0; 16];
        let primary_offset = Self::serialize_b_tree(tree.primary_tree, offset, &mut buf)?;
        buf[..8].copy_from_slice(&primary_offset.to_be_bytes());
        let secondary_offset = Self::serialize_b_tree(tree.secondary_tree, offset, &mut buf)?;
        buf[8..16].copy_from_slice(&secondary_offset.to_be_bytes());
        Ok((
            BTree2D {
                primary_tree: BTree::Persisted { id: primary_offset },
                secondary_tree: BTree::Persisted {
                    id: secondary_offset,
                },
            },
            buf,
        ))
    }

    fn serialize_b_tree<K: Clone + Serialize, V: Clone + Serialize>(
        tree: BTree<K, V>,
        dest_offset: u64,
        dest: &mut Vec<u8>,
    ) -> Result<u64> {
        Ok(match tree {
            BTree::Persisted { id } => id,
            BTree::Volatile { node } => {
                let node = match node {
                    b_tree::Node::Internal { index, children } => {
                        let children = children
                            .into_iter()
                            .map(|tree| Self::serialize_b_tree(tree, dest_offset, dest))
                            .collect::<Result<Vec<_>>>()?;
                        Node::Internal { index, children }
                    }
                    b_tree::Node::Leaf { keys, values } => {
                        let values = values
                            .into_iter()
                            .map(|value| Self::serialize_b_tree_value(value, dest_offset, dest))
                            .collect::<Result<Vec<_>>>()?;
                        Node::Leaf { keys, values }
                    }
                };
                let id = dest_offset + dest.len() as u64;
                node.serialize(&mut rmp_serde::Serializer::new(dest))?;
                id
            }
        })
    }

    fn serialize_b_tree_value<V: Clone + Serialize>(
        value: b_tree::Value<V>,
        dest_offset: u64,
        dest: &mut Vec<u8>,
    ) -> Result<u64> {
        Ok(match value {
            b_tree::Value::Persisted { id } => id,
            b_tree::Value::Volatile { value } => {
                let id = dest_offset + dest.len() as u64;
                value.serialize(&mut rmp_serde::Serializer::new(dest))?;
                id
            }
        })
    }

    /// Gets a snapshot of the tree, which can be used for reads.
    pub fn tree(&mut self) -> Tree {
        Tree {
            loader: Loader(&mut self.f),
            inner: self.tree.clone(),
        }
    }

    /// Makes a modification to the tree and commits it to disk.
    pub fn commit<F: FnOnce(Tree) -> Result<Tree>>(&mut self, f: F) -> Result<()> {
        let tree = f(Tree {
            loader: Loader(&mut self.f),
            inner: self.tree.clone(),
        })?;
        let tree = tree.into_inner();
        if !tree.is_persisted() {
            let (tree, buf) = Self::serialize_tree(
                tree,
                self.f.size() + append_only_file::ENTRY_PREFIX_LENGTH as u64,
            )
            .with_context(|| "unable to serialize tree")?;
            self.f
                .append(&buf)
                .with_context(|| "unable to append tree to append-only file")?;
            self.tree = tree;
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
            let mut partition = Partition::open(&path).unwrap();

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
            let mut partition = Partition::open(&path).unwrap();

            assert_eq!(
                partition.tree().get(&primary_key("foo", "a")).unwrap(),
                Some(Value::Bytes("bar".into()))
            );
        }
    }
}
