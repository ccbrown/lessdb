use super::b_tree::{Loader as BTreeLoader, Node as BTreeNode, Tree as BTree};
use serde::{Deserialize, Serialize};

#[derive(Clone, Serialize, Deserialize)]
pub struct Key<H, S> {
    pub primary: PrimaryKey<H, S>,
    pub secondary_sort: Option<S>,
}

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PrimaryKey<H, S> {
    pub hash: H,
    pub sort: S,
}

pub type PrimaryNode<H, S, V> = BTreeNode<PrimaryKey<H, S>, Value<S, V>>;

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SecondaryKey<H, S> {
    pub hash: H,
    pub secondary_sort: S,
    pub primary_sort: S,
}

pub type SecondaryNode<H, S, V> = BTreeNode<SecondaryKey<H, S>, Value<S, V>>;

#[derive(Clone, Serialize, Deserialize)]
pub struct Value<S, V> {
    pub secondary_sort: Option<S>,
    pub value: V,
}

/// Implements a "2D" B+tree which combines two B+trees to allow for indexing by up to 2
/// dimensions.
#[derive(Clone)]
pub struct Tree<H: Clone, S: Clone, V: Clone> {
    pub primary_tree: BTree<PrimaryKey<H, S>, Value<S, V>>,
    pub secondary_tree: BTree<SecondaryKey<H, S>, Value<S, V>>,
}

pub trait Loader<H: Clone, S: Clone, V: Clone> {
    type Error;

    fn load_primary_node(&mut self, id: u64) -> Result<PrimaryNode<H, S, V>, Self::Error>;
    fn load_secondary_node(&mut self, id: u64) -> Result<SecondaryNode<H, S, V>, Self::Error>;
    fn load_value(&mut self, id: u64) -> Result<Value<S, V>, Self::Error>;
}

impl<H: Clone, S: Clone, V: Clone, E, L: Loader<H, S, V, Error = E>>
    BTreeLoader<PrimaryKey<H, S>, Value<S, V>> for L
{
    type Error = E;

    fn load_node(&mut self, id: u64) -> Result<PrimaryNode<H, S, V>, Self::Error> {
        self.load_primary_node(id)
    }

    fn load_value(&mut self, id: u64) -> Result<Value<S, V>, Self::Error> {
        self.load_value(id)
    }
}

impl<H: Clone, S: Clone, V: Clone, E, L: Loader<H, S, V, Error = E>>
    BTreeLoader<SecondaryKey<H, S>, Value<S, V>> for L
{
    type Error = E;

    fn load_node(&mut self, id: u64) -> Result<SecondaryNode<H, S, V>, Self::Error> {
        self.load_secondary_node(id)
    }

    fn load_value(&mut self, id: u64) -> Result<Value<S, V>, Self::Error> {
        self.load_value(id)
    }
}

impl<H: Ord + Clone, S: Ord + Clone, V: Clone> Tree<H, S, V> {
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
        loader: &mut L,
        key: &PrimaryKey<H, S>,
    ) -> Result<Option<V>, E> {
        Ok(self.primary_tree.get(loader, key)?.map(|v| v.value.clone()))
    }

    /// Inserts a new item into the B-tree or updates an existing one.
    pub fn insert<E, L: Loader<H, S, V, Error = E>>(
        &self,
        loader: &mut L,
        key: Key<H, S>,
        value: V,
    ) -> Result<Self, E> {
        let value = Value {
            secondary_sort: key.secondary_sort.clone(),
            value: value.clone(),
        };

        let (primary_tree, prev) =
            self.primary_tree
                .insert(loader, key.primary.clone(), value.clone())?;

        let mut secondary_tree = match prev
            .map(|prev| -> Result<_, _> {
                Ok(prev
                    .load::<_, SecondaryKey<H, S>, _>(loader)?
                    .secondary_sort)
            })
            .transpose()?
            .flatten()
        {
            Some(prev_secondary_sort) => {
                let (tree, _) = self.secondary_tree.delete(
                    loader,
                    &SecondaryKey {
                        hash: key.primary.hash.clone(),
                        secondary_sort: prev_secondary_sort,
                        primary_sort: key.primary.sort.clone(),
                    },
                )?;
                tree
            }
            None => self.secondary_tree.clone(),
        };

        if let Some(secondary_sort) = key.secondary_sort {
            let (tree, _) = secondary_tree.insert(
                loader,
                SecondaryKey {
                    hash: key.primary.hash,
                    secondary_sort: secondary_sort,
                    primary_sort: key.primary.sort,
                },
                value,
            )?;
            secondary_tree = tree
        }

        Ok(Self {
            primary_tree,
            secondary_tree,
        })
    }

    /// Deletes a new item from the B-tree.
    pub fn delete<E, L: Loader<H, S, V, Error = E>>(
        &self,
        loader: &mut L,
        key: &PrimaryKey<H, S>,
    ) -> Result<Self, E> {
        let (primary_tree, prev) = self.primary_tree.delete(loader, &key)?;

        let secondary_tree = match prev
            .map(|prev| -> Result<_, _> {
                Ok(prev
                    .load::<_, SecondaryKey<H, S>, _>(loader)?
                    .secondary_sort)
            })
            .transpose()?
            .flatten()
        {
            Some(prev_secondary_sort) => {
                let (tree, _) = self.secondary_tree.delete(
                    loader,
                    &SecondaryKey {
                        hash: key.hash.clone(),
                        secondary_sort: prev_secondary_sort,
                        primary_sort: key.sort.clone(),
                    },
                )?;
                tree
            }
            None => self.secondary_tree.clone(),
        };

        Ok(Self {
            primary_tree,
            secondary_tree,
        })
    }

    #[cfg(test)]
    pub fn assert_invariants<E: std::fmt::Debug, L: Loader<H, S, V, Error = E>>(
        &self,
        loader: &mut L,
    ) {
        self.primary_tree.assert_invariants(loader);
        self.secondary_tree.assert_invariants(loader);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Storage;

    impl Loader<i32, i32, String> for Storage {
        type Error = anyhow::Error;

        fn load_primary_node(
            &mut self,
            id: u64,
        ) -> Result<PrimaryNode<i32, i32, String>, Self::Error> {
            panic!("the tests don't persist nodes")
        }

        fn load_secondary_node(
            &mut self,
            id: u64,
        ) -> Result<SecondaryNode<i32, i32, String>, Self::Error> {
            panic!("the tests don't persist nodes")
        }

        fn load_value(&mut self, id: u64) -> Result<Value<i32, String>, Self::Error> {
            panic!("the tests don't persist values")
        }
    }

    #[test]
    fn test_tree() {
        let mut storage = Storage;

        let mut root = Tree::<i32, i32, String>::new();
        assert_eq!(
            root.get(&mut storage, &PrimaryKey { hash: 1, sort: 1 })
                .unwrap(),
            None
        );

        let primary_key = |i| PrimaryKey { hash: i, sort: i };

        let key = |i| Key {
            primary: primary_key(i),
            secondary_sort: Some(i),
        };

        // insert some arbitrary values
        for i in (100..900).step_by(10) {
            root = root.insert(&mut storage, key(i), i.to_string()).unwrap();
            root.assert_invariants(&mut storage);
        }

        for i in (0..1000).step_by(9) {
            // test inserting the value
            root = root.insert(&mut storage, key(i), "-1".to_string()).unwrap();
            root.assert_invariants(&mut storage);
            assert_eq!(
                root.get(&mut storage, &primary_key(i)).unwrap(),
                Some("-1".to_string())
            );

            // test updating the value
            root = root.insert(&mut storage, key(i), i.to_string()).unwrap();
            root.assert_invariants(&mut storage);
            assert_eq!(
                root.get(&mut storage, &primary_key(i)).unwrap(),
                Some(i.to_string())
            );
        }

        // test deleting values
        for i in (0..1000).step_by(3) {
            let root = root.delete(&mut storage, &primary_key(i)).unwrap();
            root.assert_invariants(&mut storage);
            assert_eq!(root.get(&mut storage, &primary_key(i)).unwrap(), None);
        }
    }
}
