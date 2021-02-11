use super::{
    append_only_file::{self, AppendOnlyFile},
    b_tree::{self, Tree as BTree},
    b_tree_2d,
};
use anyhow::{Context, Error, Result};
use serde::{Deserialize, Serialize};
use std::{
    convert::TryInto,
    io::{Read, Seek, SeekFrom},
    path::Path,
    sync::Arc,
};

pub const HASH_LENGTH: usize = 32;

#[derive(Clone, Debug, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hash(Arc<[u8; HASH_LENGTH]>);

impl AsRef<[u8; HASH_LENGTH]> for Hash {
    fn as_ref(&self) -> &[u8; HASH_LENGTH] {
        &self.0
    }
}

#[cfg(test)]
impl From<&str> for Hash {
    fn from(s: &str) -> Hash {
        use digest::Digest;
        let mut hasher = sha2::Sha256::new();
        hasher.update(s.as_bytes());
        let mut buf = [0u8; 32];
        buf.copy_from_slice(&hasher.finalize());
        Hash(Arc::new(buf))
    }
}

#[derive(Clone, Debug, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct Bytes(Arc<Vec<u8>>);

impl Bytes {
    pub fn new() -> Self {
        Self(Arc::new(Vec::new()))
    }
}

#[cfg(test)]
impl From<&str> for Bytes {
    fn from(s: &str) -> Bytes {
        Bytes(Arc::new(s.as_bytes().to_vec()))
    }
}

type BTree2D = b_tree_2d::Tree<Hash, Bytes, Bytes>;

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

    pub fn get(&mut self, key: &PrimaryKey) -> Result<Option<Bytes>> {
        Ok(self.inner.get(&mut self.loader, key)?)
    }

    pub fn insert(self, key: Key, value: Bytes) -> Result<Self> {
        let mut loader = self.loader;
        Ok(Self {
            inner: self.inner.insert(&mut loader, key, value)?,
            loader,
        })
    }

    pub fn delete(self, key: &PrimaryKey) -> Result<Self> {
        let mut loader = self.loader;
        Ok(Self {
            inner: self.inner.delete(&mut loader, key)?,
            loader,
        })
    }
}

struct Loader<'a>(&'a mut AppendOnlyFile);

impl<'a> b_tree_2d::Loader<Hash, Bytes, Bytes> for Loader<'a> {
    type Error = Error;

    fn load_primary_node(
        &mut self,
        id: u64,
    ) -> Result<b_tree_2d::PrimaryNode<Hash, Bytes, Bytes>, Self::Error> {
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
    ) -> Result<b_tree_2d::SecondaryNode<Hash, Bytes, Bytes>, Self::Error> {
        self.0
            .seek(SeekFrom::Start(id))
            .with_context(|| "unable to seek to secondary node")?;
        let node: Node<_> = rmp_serde::from_read(&mut self.0)
            .with_context(|| format!("unable to deserialize secondary node at offset {}", id))?;
        Ok(node.into())
    }

    fn load_value(&mut self, id: u64) -> Result<b_tree_2d::Value<Bytes, Bytes>, Self::Error> {
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
        })?
        .into_inner();
        let (tree, buf) = Self::serialize_tree(
            tree,
            self.f.size() + append_only_file::ENTRY_PREFIX_LENGTH as u64,
        )
        .with_context(|| "unable to serialize tree")?;
        self.f
            .append(&buf)
            .with_context(|| "unable to append tree to append-only file")?;
        self.tree = tree;
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
                .commit(|tree| tree.insert(key("foo", "a", None), "bar".into()))
                .unwrap();

            assert_eq!(
                partition.tree().get(&primary_key("foo", "a")).unwrap(),
                Some("bar".into())
            );
        }

        // make sure the data is still there
        {
            let mut partition = Partition::open(&path).unwrap();

            assert_eq!(
                partition.tree().get(&primary_key("foo", "a")).unwrap(),
                Some("bar".into())
            );
        }
    }
}
