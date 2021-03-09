use super::storage::{self};
use algorithms::{b_tree, cache::Cache as InnerCache};
use bytes::Bytes;

#[derive(Debug, Hash, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct Key {
    pub offset: u64,
}

type Node = b_tree::Node<Bytes, storage::Value>;
type Value = storage::Value;

pub enum Item {
    Node(Node),
    Value(Value),
}

/// Keeps recently used items in memory so we don't have to hit the disk for everything. For
/// example, items are placed in the cache right after they're written to disk as we're almost 100%
/// sure to need at least the new root node again.
pub struct Cache {
    node_cache: InnerCache<Key, Node>,
    value_cache: InnerCache<Key, Value>,
}

impl Cache {
    pub fn new() -> Self {
        Self {
            // TODO: these parameters should probably be tunable
            node_cache: InnerCache::new(5000),
            value_cache: InnerCache::new(5000),
        }
    }

    pub fn get_node<E, F: FnOnce() -> Result<Node, E>>(
        &self,
        key: Key,
        recompute: F,
    ) -> Result<Node, E> {
        match self.node_cache.get(&key) {
            Some(hit) => Ok(hit),
            None => {
                let node = recompute()?;
                self.node_cache.set(key, node.clone());
                Ok(node)
            }
        }
    }

    pub fn get_value<E, F: FnOnce() -> Result<Value, E>>(
        &self,
        key: Key,
        recompute: F,
    ) -> Result<Value, E> {
        match self.value_cache.get(&key) {
            Some(hit) => Ok(hit),
            None => {
                let v = recompute()?;
                self.value_cache.set(key, v.clone());
                Ok(v)
            }
        }
    }

    pub fn insert(&self, key: Key, item: Item) {
        match item {
            Item::Node(node) => {
                self.node_cache.set(key, node);
            }
            Item::Value(v) => {
                self.value_cache.set(key, v);
            }
        }
    }
}
