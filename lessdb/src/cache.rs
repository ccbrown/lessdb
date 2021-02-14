use super::partition::{self, Hash, Sort};
use algorithms::{b_tree_2d, cache::Cache as InnerCache};

#[derive(Debug, Hash, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct Key {
    pub partition: u32,
    pub offset: u64,
}

type PrimaryNode = b_tree_2d::PrimaryNode<Hash, Sort, partition::Value>;
type SecondaryNode = b_tree_2d::SecondaryNode<Hash, Sort, partition::Value>;
type Value = b_tree_2d::Value<Sort, partition::Value>;

pub enum Item {
    PrimaryNode(PrimaryNode),
    SecondaryNode(SecondaryNode),
    Value(Value),
}

/// Keeps recently used items in memory so we don't have to hit the disk for everything. For
/// example, items are placed in the cache right after they're written to disk as we're almost 100%
/// sure to need at least the new root node again.
pub struct Cache {
    primary_node_cache: InnerCache<Key, PrimaryNode>,
    secondary_node_cache: InnerCache<Key, SecondaryNode>,
    value_cache: InnerCache<Key, Value>,
}

impl Cache {
    pub fn new() -> Self {
        Self {
            // TODO: these parameters should probably be tunable
            primary_node_cache: InnerCache::new(5000),
            secondary_node_cache: InnerCache::new(5000),
            value_cache: InnerCache::new(5000),
        }
    }

    pub fn get_primary_node<E, F: FnOnce() -> Result<PrimaryNode, E>>(
        &self,
        key: Key,
        recompute: F,
    ) -> Result<PrimaryNode, E> {
        match self.primary_node_cache.get(&key) {
            Some(hit) => Ok(hit),
            None => {
                let node = recompute()?;
                self.primary_node_cache.set(key, node.clone());
                Ok(node)
            }
        }
    }

    pub fn get_secondary_node<E, F: FnOnce() -> Result<SecondaryNode, E>>(
        &self,
        key: Key,
        recompute: F,
    ) -> Result<SecondaryNode, E> {
        match self.secondary_node_cache.get(&key) {
            Some(hit) => Ok(hit),
            None => {
                let node = recompute()?;
                self.secondary_node_cache.set(key, node.clone());
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
            Item::PrimaryNode(node) => {
                self.primary_node_cache.set(key, node);
            }
            Item::SecondaryNode(node) => {
                self.secondary_node_cache.set(key, node);
            }
            Item::Value(v) => {
                self.value_cache.set(key, v);
            }
        }
    }
}