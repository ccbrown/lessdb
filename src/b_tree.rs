use std::sync::Arc;

const MAX_NODE_CHILDREN: usize = 6;

#[derive(Debug)]
pub enum Tree<K: Clone, V> {
    Persisted { id: u64 },
    Volatile { node: Arc<Node<K, V>> },
}

impl<K: Clone, V> Tree<K, V> {
    fn load_node<E, L: Loader<K, V, Error = E>>(&self, loader: &L) -> Result<Arc<Node<K, V>>, E> {
        match self {
            Self::Persisted { id } => loader.load_node(*id),
            Self::Volatile { node, .. } => Ok(node.clone()),
        }
    }
}

impl<K: Clone, V> Clone for Tree<K, V> {
    fn clone(&self) -> Self {
        match self {
            Self::Persisted { id } => Self::Persisted { id: *id },
            Self::Volatile { node } => Self::Volatile { node: node.clone() },
        }
    }
}

#[derive(Debug)]
pub enum Value<V> {
    Persisted { id: u64 },
    Volatile { value: Arc<V> },
}

impl<V> Value<V> {
    fn load<E, K: Clone, L: Loader<K, V, Error = E>>(&self, loader: &L) -> Result<Arc<V>, E> {
        match self {
            Self::Persisted { id } => loader.load_value(*id),
            Self::Volatile { value, .. } => Ok(value.clone()),
        }
    }
}

impl<V> Clone for Value<V> {
    fn clone(&self) -> Self {
        match self {
            Self::Persisted { id } => Self::Persisted { id: *id },
            Self::Volatile { value } => Self::Volatile {
                value: value.clone(),
            },
        }
    }
}

#[derive(Debug)]
pub enum Node<K: Clone, V> {
    Internal {
        index: Vec<K>,
        children: Vec<Tree<K, V>>,
    },
    Leaf {
        keys: Vec<K>,
        values: Vec<Value<V>>,
    },
}

impl<K: Clone, V> Node<K, V> {
    fn split_if_overflow(self) -> (Self, Option<(K, Self)>) {
        match self {
            Node::Internal {
                mut index,
                mut children,
            } => {
                if children.len() <= MAX_NODE_CHILDREN {
                    return (Node::Internal { index, children }, None);
                }
                let right_children = children.split_off(children.len() / 2);
                let right_index = index.split_off(children.len());
                let right_first_key = index.pop().expect("index should not be empty");
                (
                    Node::Internal { index, children },
                    Some((
                        right_first_key,
                        Node::Internal {
                            index: right_index,
                            children: right_children,
                        },
                    )),
                )
            }
            Node::Leaf {
                mut keys,
                mut values,
            } => {
                if values.len() <= MAX_NODE_CHILDREN {
                    return (Node::Leaf { keys, values }, None);
                }
                let right_values = values.split_off(values.len() / 2);
                let right_keys = keys.split_off(values.len());
                (
                    Node::Leaf { keys, values },
                    Some((
                        right_keys[0].clone(),
                        Node::Leaf {
                            keys: right_keys,
                            values: right_values,
                        },
                    )),
                )
            }
        }
    }
}

pub trait Loader<K: Clone, V> {
    type Error;

    fn load_node(&self, id: u64) -> Result<Arc<Node<K, V>>, Self::Error>;
    fn load_value(&self, id: u64) -> Result<Arc<V>, Self::Error>;
}

impl<K: Ord + Clone, V> Tree<K, V> {
    /// Creates a new, empty B-tree.
    pub fn new() -> Self {
        Self::Volatile {
            node: Arc::new(Node::Leaf {
                keys: Vec::new(),
                values: Vec::new(),
            }),
        }
    }

    /// Gets an item from the B-tree, if it exists.
    pub fn get<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &L,
        key: &K,
    ) -> Result<Option<Arc<V>>, E> {
        match &*self.load_node(loader)? {
            Node::Internal { index, children } => match index.binary_search(&key) {
                Ok(i) => children[i + 1].get(loader, key),
                Err(i) => children[i].get(loader, key),
            },
            Node::Leaf { keys, values } => Ok(match keys.binary_search(&key) {
                Ok(i) => Some(values[i].load(loader)?),
                Err(_) => None,
            }),
        }
    }

    /// Inserts a new item into the B-tree or updates an existing one.
    pub fn insert<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &L,
        key: K,
        value: V,
    ) -> Result<Self, E> {
        Ok(
            match self.insert_impl(loader, key, value)?.split_if_overflow() {
                (a, None) => Tree::Volatile { node: Arc::new(a) },
                (a, Some((b_key, b))) => Tree::Volatile {
                    node: Arc::new(Node::Internal {
                        index: vec![b_key],
                        children: vec![
                            Tree::Volatile { node: Arc::new(a) },
                            Tree::Volatile { node: Arc::new(b) },
                        ],
                    }),
                },
            },
        )
    }

    fn insert_impl<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &L,
        key: K,
        value: V,
    ) -> Result<Node<K, V>, E> {
        Ok(match &*self.load_node(loader)? {
            Node::Internal { index, children } => {
                let i = match index.binary_search(&key) {
                    Ok(i) => i + 1,
                    Err(i) => i,
                };
                let mut new_children = Vec::with_capacity(children.len() + 1);
                new_children.extend_from_slice(&children[..i]);
                let new_index = match children[i]
                    .insert_impl(loader, key, value)?
                    .split_if_overflow()
                {
                    (a, None) => {
                        new_children.push(Tree::Volatile { node: Arc::new(a) });
                        index.clone()
                    }
                    (a, Some((b_key, b))) => {
                        let mut new_index = Vec::with_capacity(index.len() + 1);
                        new_index.extend_from_slice(&index[..i]);
                        new_index.push(b_key);
                        new_index.extend_from_slice(&index[i..]);
                        new_children.push(Tree::Volatile { node: Arc::new(a) });
                        new_children.push(Tree::Volatile { node: Arc::new(b) });
                        new_index
                    }
                };
                new_children.extend_from_slice(&children[i + 1..]);
                Node::Internal {
                    index: new_index,
                    children: new_children,
                }
            }
            Node::Leaf { keys, values } => match keys.binary_search(&key) {
                Ok(i) => {
                    let mut values = values.clone();
                    values[i] = Value::Volatile {
                        value: Arc::new(value),
                    };
                    Node::Leaf {
                        keys: keys.clone(),
                        values,
                    }
                }
                Err(dest) => {
                    let mut keys = keys.clone();
                    keys.insert(dest, key);
                    let mut values = values.clone();
                    values.insert(
                        dest,
                        Value::Volatile {
                            value: Arc::new(value),
                        },
                    );
                    Node::Leaf { keys, values }
                }
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Storage;

    impl Loader<i32, String> for Storage {
        type Error = anyhow::Error;

        fn load_node(&self, id: u64) -> Result<Arc<Node<i32, String>>, Self::Error> {
            panic!("the tests don't persist nodes")
        }

        fn load_value(&self, id: u64) -> Result<Arc<String>, Self::Error> {
            panic!("the tests don't persist values")
        }
    }

    #[test]
    fn test_tree() {
        let storage = Storage;

        let mut root = Tree::<i32, String>::new();
        assert_eq!(root.get(&storage, &1).unwrap(), None);

        for i in 0..20 {
            // test inserting the value
            root = root.insert(&storage, i, (-1).to_string()).unwrap();
            for j in 0..=i {
                assert_eq!(
                    root.get(&storage, &j).unwrap(),
                    Some(Arc::new((if i == j { -1 } else { j }).to_string()))
                );
            }

            // test updating the value
            root = root.insert(&storage, i, i.to_string()).unwrap();
            for j in 0..=i {
                assert_eq!(
                    root.get(&storage, &j).unwrap(),
                    Some(Arc::new(j.to_string()))
                );
            }
        }
    }
}
