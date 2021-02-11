use super::b_tree::{Loader as BTreeLoader, Node as BTreeNode, Tree as BTree};
use std::sync::Arc;

pub struct Key<H, S> {
    pub hash: H,
    pub primary_sort: S,
    pub secondary_sort: Option<S>,
}

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord)]
pub struct PrimaryKey<H, S> {
    pub hash: H,
    pub sort: S,
}

pub type PrimaryNode<H, S, V> = BTreeNode<PrimaryKey<H, S>, BTreeValue<S, V>>;

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord)]
pub struct SecondaryKey<H, S> {
    pub hash: H,
    pub secondary_sort: S,
    pub primary_sort: S,
}

pub type SecondaryNode<H, S, V> = BTreeNode<SecondaryKey<H, S>, BTreeValue<S, V>>;

pub struct BTreeValue<S, V> {
    pub secondary_sort: Option<S>,
    pub value: Arc<V>,
}

pub struct Tree<H: Clone, S: Clone, V> {
    primary_tree: BTree<PrimaryKey<H, S>, BTreeValue<S, V>>,
    secondary_tree: BTree<SecondaryKey<H, S>, BTreeValue<S, V>>,
}

pub trait Loader<H: Clone, S: Clone, V> {
    type Error;

    fn load_primary_node(&self, id: u64) -> Result<Arc<PrimaryNode<H, S, V>>, Self::Error>;
    fn load_secondary_node(&self, id: u64) -> Result<Arc<SecondaryNode<H, S, V>>, Self::Error>;
    fn load_value(&self, id: u64) -> Result<Arc<BTreeValue<S, V>>, Self::Error>;
}

impl<H: Clone, S: Clone, V, E, L: Loader<H, S, V, Error = E>>
    BTreeLoader<PrimaryKey<H, S>, BTreeValue<S, V>> for L
{
    type Error = E;

    fn load_node(&self, id: u64) -> Result<Arc<PrimaryNode<H, S, V>>, Self::Error> {
        self.load_primary_node(id)
    }

    fn load_value(&self, id: u64) -> Result<Arc<BTreeValue<S, V>>, Self::Error> {
        self.load_value(id)
    }
}

impl<H: Clone, S: Clone, V, E, L: Loader<H, S, V, Error = E>>
    BTreeLoader<SecondaryKey<H, S>, BTreeValue<S, V>> for L
{
    type Error = E;

    fn load_node(&self, id: u64) -> Result<Arc<SecondaryNode<H, S, V>>, Self::Error> {
        self.load_secondary_node(id)
    }

    fn load_value(&self, id: u64) -> Result<Arc<BTreeValue<S, V>>, Self::Error> {
        self.load_value(id)
    }
}

impl<H: Ord + Clone, S: Ord + Clone, V> Tree<H, S, V> {
    /// Creates a new, empty B-tree.
    pub fn new() -> Self {
        Self {
            primary_tree: BTree::new(),
            secondary_tree: BTree::new(),
        }
    }

    /// Gets an item from the B-tree, if it exists.
    pub fn get<E, L: Loader<H, S, V, Error = E>>(
        &self,
        loader: &L,
        key: &PrimaryKey<H, S>,
    ) -> Result<Option<Arc<V>>, E> {
        Ok(self.primary_tree.get(loader, key)?.map(|v| v.value.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Storage;

    impl Loader<i32, i32, String> for Storage {
        type Error = anyhow::Error;

        fn load_primary_node(
            &self,
            id: u64,
        ) -> Result<Arc<PrimaryNode<i32, i32, String>>, Self::Error> {
            panic!("the tests don't persist nodes")
        }

        fn load_secondary_node(
            &self,
            id: u64,
        ) -> Result<Arc<SecondaryNode<i32, i32, String>>, Self::Error> {
            panic!("the tests don't persist nodes")
        }

        fn load_value(&self, id: u64) -> Result<Arc<BTreeValue<i32, String>>, Self::Error> {
            panic!("the tests don't persist values")
        }
    }

    #[test]
    fn test_tree() {
        let storage = Storage;

        let mut root = Tree::<i32, i32, String>::new();
        assert_eq!(
            root.get(&storage, &PrimaryKey { hash: 1, sort: 1 })
                .unwrap(),
            None
        );
    }
}
