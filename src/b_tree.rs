const MAX_NODE_CHILDREN: usize = 6;
const MIN_NODE_CHILDREN: usize = MAX_NODE_CHILDREN / 2;

#[derive(Clone, Debug)]
pub enum Tree<K: Clone, V: Clone> {
    Persisted { id: u64 },
    Volatile { node: Node<K, V> },
}

impl<K: Clone, V: Clone> Tree<K, V> {
    fn load_node<E, L: Loader<K, V, Error = E>>(&self, loader: &L) -> Result<Node<K, V>, E> {
        match self {
            Self::Persisted { id } => loader.load_node(*id),
            Self::Volatile { node, .. } => Ok(node.clone()),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value<V> {
    Persisted { id: u64 },
    Volatile { value: V },
}

impl<V: Clone> Value<V> {
    pub fn load<E, K: Clone, L: Loader<K, V, Error = E>>(self, loader: &L) -> Result<V, E> {
        match self {
            Self::Persisted { id } => loader.load_value(id),
            Self::Volatile { value, .. } => Ok(value),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Node<K: Clone, V: Clone> {
    Internal {
        index: Vec<K>,
        children: Vec<Tree<K, V>>,
    },
    Leaf {
        keys: Vec<K>,
        values: Vec<Value<V>>,
    },
}

impl<K: Clone, V: Clone> Node<K, V> {
    fn children(&self) -> usize {
        match self {
            Node::Internal { children, .. } => children.len(),
            Node::Leaf { keys, .. } => keys.len(),
        }
    }

    fn merge(self, other: Self, other_left_key: K) -> Self {
        match (self, other) {
            (
                Self::Internal { index, children },
                Self::Internal {
                    index: other_index,
                    children: other_children,
                },
            ) => Self::Internal {
                index: [index.as_slice(), &[other_left_key], other_index.as_slice()].concat(),
                children: [children.as_slice(), other_children.as_slice()].concat(),
            },
            (
                Self::Leaf { keys, values },
                Self::Leaf {
                    keys: other_keys,
                    values: other_values,
                },
            ) => Self::Leaf {
                keys: [keys.as_slice(), other_keys.as_slice()].concat(),
                values: [values.as_slice(), other_values.as_slice()].concat(),
            },
            _ => panic!("cannot merge internal and leaf nodes"),
        }
    }

    fn split_if_overflow(self) -> (Self, Option<(K, Self)>) {
        if self.children() <= MAX_NODE_CHILDREN {
            return (self, None);
        }

        match self {
            Node::Internal {
                mut index,
                mut children,
            } => {
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

pub trait Loader<K: Clone, V: Clone> {
    type Error;

    fn load_node(&self, id: u64) -> Result<Node<K, V>, Self::Error>;
    fn load_value(&self, id: u64) -> Result<V, Self::Error>;
}

struct Deletion<K: Clone, V: Clone> {
    left_key_if_changed: Option<K>,
    new_node: Node<K, V>,
    previous_value: Value<V>,
}

impl<K: Ord + Clone, V: Clone> Tree<K, V> {
    /// Creates a new, empty B-tree.
    pub fn new() -> Self {
        Self::Volatile {
            node: Node::Leaf {
                keys: Vec::new(),
                values: Vec::new(),
            },
        }
    }

    /// Gets an item from the B-tree, if it exists.
    pub fn get<E, L: Loader<K, V, Error = E>>(&self, loader: &L, key: &K) -> Result<Option<V>, E> {
        match self.load_node(loader)? {
            Node::Internal { index, children } => match index.binary_search(&key) {
                Ok(i) => children[i + 1].get(loader, key),
                Err(i) => children[i].get(loader, key),
            },
            Node::Leaf { keys, values } => Ok(match keys.binary_search(&key) {
                Ok(i) => Some(values[i].clone().load(loader)?),
                Err(_) => None,
            }),
        }
    }

    /// Inserts a new item into the B-tree or updates an existing one. If the item existed, its previous value is returned.
    pub fn insert<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &L,
        key: K,
        value: V,
    ) -> Result<(Self, Option<Value<V>>), E> {
        let (node, prev) = self.insert_impl(loader, key, value)?;
        Ok((
            match node.split_if_overflow() {
                (a, None) => Tree::Volatile { node: a },
                (a, Some((b_key, b))) => Tree::Volatile {
                    node: Node::Internal {
                        index: vec![b_key],
                        children: vec![Tree::Volatile { node: a }, Tree::Volatile { node: b }],
                    },
                },
            },
            prev,
        ))
    }

    fn insert_impl<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &L,
        key: K,
        value: V,
    ) -> Result<(Node<K, V>, Option<Value<V>>), E> {
        Ok(match self.load_node(loader)? {
            Node::Internal { index, children } => {
                let i = match index.binary_search(&key) {
                    Ok(i) => i + 1,
                    Err(i) => i,
                };
                let mut new_children = Vec::with_capacity(children.len() + 1);
                new_children.extend_from_slice(&children[..i]);
                let (new_child, prev_value) = children[i].insert_impl(loader, key, value)?;
                let new_index = match new_child.split_if_overflow() {
                    (a, None) => {
                        new_children.push(Tree::Volatile { node: a });
                        index
                    }
                    (a, Some((b_key, b))) => {
                        let mut new_index = Vec::with_capacity(index.len() + 1);
                        new_index.extend_from_slice(&index[..i]);
                        new_index.push(b_key);
                        new_index.extend_from_slice(&index[i..]);
                        new_children.push(Tree::Volatile { node: a });
                        new_children.push(Tree::Volatile { node: b });
                        new_index
                    }
                };
                new_children.extend_from_slice(&children[i + 1..]);
                (
                    Node::Internal {
                        index: new_index,
                        children: new_children,
                    },
                    prev_value,
                )
            }
            Node::Leaf {
                mut keys,
                mut values,
            } => match keys.binary_search(&key) {
                Ok(i) => {
                    let prev = std::mem::replace(&mut values[i], Value::Volatile { value });
                    (Node::Leaf { keys, values }, Some(prev))
                }
                Err(dest) => {
                    keys.insert(dest, key);
                    values.insert(dest, Value::Volatile { value });
                    (Node::Leaf { keys, values }, None)
                }
            },
        })
    }

    /// Deletes an item from the B-tree. If the item existed, its previous value is returned.
    pub fn delete<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &L,
        key: &K,
    ) -> Result<(Self, Option<Value<V>>), E> {
        Ok(match self.delete_impl(loader, key)? {
            Some(deletion) => (
                match deletion.new_node {
                    Node::Internal { mut children, .. } if children.len() == 1 => {
                        children.remove(0)
                    }
                    _ => Tree::Volatile {
                        node: deletion.new_node,
                    },
                },
                Some(deletion.previous_value),
            ),
            None => (self.clone(), None),
        })
    }

    fn delete_impl<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &L,
        key: &K,
    ) -> Result<Option<Deletion<K, V>>, E> {
        Ok(match self.load_node(loader)? {
            Node::Internal {
                mut index,
                mut children,
            } => {
                let i = match index.binary_search(&key) {
                    Ok(i) => i + 1,
                    Err(i) => i,
                };
                match children[i].delete_impl(loader, key)? {
                    Some(deletion) => Some({
                        let mut left_key_if_changed = None;
                        if deletion.new_node.children() >= MIN_NODE_CHILDREN {
                            children[i] = Tree::Volatile {
                                node: deletion.new_node,
                            };
                            if i == 0 {
                                left_key_if_changed = deletion.left_key_if_changed;
                            } else if let Some(key) = deletion.left_key_if_changed {
                                index[i - 1] = key;
                            }
                        } else {
                            let (
                                left_node,
                                left_node_idx,
                                left_left_key_if_changed,
                                right_node,
                                right_left_key,
                            ) = if i == 0 {
                                (
                                    deletion.new_node,
                                    i,
                                    deletion.left_key_if_changed,
                                    children[1].load_node(loader)?,
                                    index.remove(0),
                                )
                            } else {
                                (
                                    children[i - 1].load_node(loader)?,
                                    i - 1,
                                    None,
                                    deletion.new_node,
                                    deletion.left_key_if_changed.unwrap_or(index.remove(i - 1)),
                                )
                            };
                            match left_node
                                .merge(right_node, right_left_key)
                                .split_if_overflow()
                            {
                                (a, None) => {
                                    children.remove(left_node_idx);
                                    children[left_node_idx] = Tree::Volatile { node: a };
                                }
                                (a, Some((b_key, b))) => {
                                    children[left_node_idx] = Tree::Volatile { node: a };
                                    children[left_node_idx + 1] = Tree::Volatile { node: b };
                                    index.insert(left_node_idx, b_key);
                                }
                            }
                            if left_node_idx == 0 {
                                left_key_if_changed = left_left_key_if_changed;
                            } else if let Some(key) = left_left_key_if_changed {
                                index[left_node_idx - 1] = key;
                            }
                        }
                        Deletion {
                            left_key_if_changed,
                            new_node: Node::Internal { index, children },
                            previous_value: deletion.previous_value,
                        }
                    }),
                    None => None,
                }
            }
            Node::Leaf {
                mut keys,
                mut values,
            } => match keys.binary_search(&key) {
                Ok(i) => {
                    keys.remove(i);
                    let previous_value = values.remove(i);
                    Some(Deletion {
                        left_key_if_changed: if i == 0 { keys.first().cloned() } else { None },
                        new_node: Node::Leaf { keys, values },
                        previous_value,
                    })
                }
                Err(_) => None,
            },
        })
    }

    #[cfg(test)]
    pub fn assert_invariants<E: std::fmt::Debug, L: Loader<K, V, Error = E>>(&self, loader: &L) {
        self.assert_invariants_impl(loader, true)
    }

    #[cfg(test)]
    pub fn assert_invariants_impl<E: std::fmt::Debug, L: Loader<K, V, Error = E>>(
        &self,
        loader: &L,
        is_root: bool,
    ) {
        match self.load_node(loader).unwrap() {
            Node::Internal { index, children } => {
                assert_eq!(index.is_empty(), false);
                if is_root {
                    assert_eq!(children.len() > 1, true);
                } else {
                    assert_eq!(children.len() >= MIN_NODE_CHILDREN, true);
                }
                assert_eq!(children.len() <= MAX_NODE_CHILDREN, true);
                assert_eq!(index.len() + 1, children.len());
                for child in children {
                    child.assert_invariants_impl(loader, false);
                }
            }
            Node::Leaf { keys, values } => {
                assert_eq!(keys.len(), values.len());
                if !is_root {
                    assert_eq!(keys.len() >= MIN_NODE_CHILDREN, true);
                }
                assert_eq!(keys.len() <= MAX_NODE_CHILDREN, true);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Storage;

    impl Loader<i32, String> for Storage {
        type Error = anyhow::Error;

        fn load_node(&self, id: u64) -> Result<Node<i32, String>, Self::Error> {
            panic!("the tests don't persist nodes")
        }

        fn load_value(&self, id: u64) -> Result<String, Self::Error> {
            panic!("the tests don't persist values")
        }
    }

    #[test]
    fn test_tree() {
        let storage = Storage;

        let mut root = Tree::<i32, String>::new();
        assert_eq!(root.get(&storage, &1).unwrap(), None);

        // insert some arbitrary values
        for i in (100..900).step_by(10) {
            let (new_root, prev) = root.insert(&storage, i, i.to_string()).unwrap();
            root = new_root;
            assert_eq!(prev.is_none(), true);
            root.assert_invariants(&storage);
        }

        for i in (0..1000).step_by(9) {
            // test inserting the value
            let (new_root, _) = root.insert(&storage, i, "-1".to_string()).unwrap();
            root = new_root;
            root.assert_invariants(&storage);
            assert_eq!(root.get(&storage, &i).unwrap(), Some("-1".to_string()));

            // test updating the value
            let (new_root, prev) = root.insert(&storage, i, i.to_string()).unwrap();
            root = new_root;
            root.assert_invariants(&storage);
            assert_eq!(
                prev,
                Some(Value::Volatile {
                    value: "-1".to_string()
                })
            );
            assert_eq!(root.get(&storage, &i).unwrap(), Some(i.to_string()));
        }

        // test deleting values
        for i in (0..1000).step_by(3) {
            let (root, prev) = root.delete(&storage, &i).unwrap();
            if i % 9 == 0 {
                assert_eq!(prev.is_some(), true);
            }
            root.assert_invariants(&storage);
            assert_eq!(root.get(&storage, &i).unwrap(), None);
        }
    }
}
