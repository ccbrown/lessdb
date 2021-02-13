use std::collections::VecDeque;
use std::ops::{Bound, RangeBounds};

const MAX_NODE_CHILDREN: usize = 6;
const MIN_NODE_CHILDREN: usize = MAX_NODE_CHILDREN / 2;

#[derive(Clone, Debug)]
pub enum Tree<K: Clone, V: Clone> {
    Persisted { id: u64 },
    Volatile { node: Node<K, V> },
}

impl<K: Clone, V: Clone> Tree<K, V> {
    fn load_node<E, L: Loader<K, V, Error = E>>(&self, loader: &mut L) -> Result<Node<K, V>, E> {
        match self {
            Self::Persisted { id } => loader.load_node(*id),
            Self::Volatile { node, .. } => Ok(node.clone()),
        }
    }

    pub fn is_persisted(&self) -> bool {
        match self {
            Self::Persisted { .. } => true,
            Self::Volatile { .. } => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value<V> {
    Persisted { id: u64 },
    Volatile { value: V },
}

impl<V: Clone> Value<V> {
    pub fn load<E, K: Clone, L: Loader<K, V, Error = E>>(self, loader: &mut L) -> Result<V, E> {
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

    fn load_node(&mut self, id: u64) -> Result<Node<K, V>, Self::Error>;
    fn load_value(&mut self, id: u64) -> Result<V, Self::Error>;
}

struct Deletion<K: Clone, V: Clone> {
    left_key_if_changed: Option<K>,
    new_node: Node<K, V>,
    previous_value: Value<V>,
}

pub struct Range<'a, K: Clone, V: Clone, L, B> {
    tree: &'a Tree<K, V>,
    loader: &'a mut L,
    bounds: B,
    forward: Option<IteratorState<K, V>>,
    backward: Option<IteratorState<K, V>>,
}

struct IteratorState<K: Clone, V: Clone> {
    to_visit: Vec<VecDeque<Tree<K, V>>>,
    keys: VecDeque<K>,
    values: VecDeque<Value<V>>,
}

impl<'a, K: Clone + Ord, V: Clone, E, L: Loader<K, V, Error = E>, B: RangeBounds<K>>
    Range<'a, K, V, L, B>
{
    fn new(tree: &'a Tree<K, V>, loader: &'a mut L, bounds: B) -> Self {
        Self {
            tree,
            loader,
            bounds,
            forward: None,
            backward: None,
        }
    }

    /// Initializes the range state by finding the first leaf node that might be within the range.
    /// Any values encountered by advancing through the returned state are guaranteed to not come
    /// before the range.
    fn init_forward_state(&mut self) -> Result<IteratorState<K, V>, E> {
        let mut to_visit = vec![];
        let mut node = self.tree.load_node(self.loader)?;
        loop {
            match node {
                Node::Internal {
                    index,
                    mut children,
                } => {
                    let min_child_idx = match self.bounds.start_bound() {
                        Bound::Unbounded => 0,
                        Bound::Included(key) => match index.binary_search(&key) {
                            Ok(i) => i + 1,
                            Err(i) => i,
                        },
                        Bound::Excluded(key) => match index.binary_search(&key) {
                            Ok(i) => i + 1,
                            Err(i) => i,
                        },
                    };
                    to_visit.push(children.split_off(min_child_idx + 1).into());
                    node = children[min_child_idx].load_node(self.loader)?;
                }
                Node::Leaf {
                    mut keys,
                    mut values,
                } => {
                    let idx = match self.bounds.start_bound() {
                        Bound::Unbounded => 0,
                        Bound::Included(key) => match keys.binary_search(&key) {
                            Ok(i) => i,
                            Err(i) => i,
                        },
                        Bound::Excluded(key) => match keys.binary_search(&key) {
                            Ok(i) => i + 1,
                            Err(i) => i,
                        },
                    };
                    return Ok(IteratorState {
                        to_visit,
                        keys: keys.split_off(idx).into(),
                        values: values.split_off(idx).into(),
                    });
                }
            }
        }
    }

    /// Gets the next value within the range by advancing through the forward state.
    fn get_next(&mut self) -> Result<Option<V>, E> {
        if self.forward.is_none() {
            self.forward = Some(self.init_forward_state()?);
        }
        let state = self.forward.as_mut().expect("we just set this");

        if state.keys.is_empty() {
            'outer: while let Some(next) = state.to_visit.last_mut() {
                if let Some(mut tree) = next.pop_front() {
                    loop {
                        match tree.load_node(self.loader)? {
                            Node::Internal { mut children, .. } => {
                                state.to_visit.push(children.split_off(1).into());
                                tree = children.remove(0);
                            }
                            Node::Leaf { keys, values } => {
                                state.keys = keys.into();
                                state.values = values.into();
                                break 'outer;
                            }
                        }
                    }
                } else {
                    state.to_visit.pop();
                }
            }
        }

        if let Some(key) = state.keys.pop_front() {
            if self.bounds.contains(&key) {
                let ret = state
                    .values
                    .pop_front()
                    .expect("there should be the same number of keys and values")
                    .load(self.loader)?;
                return Ok(Some(ret));
            } else {
                return Ok(None);
            }
        }

        Ok(None)
    }

    /// Initializes the range state by finding the last leaf node that might be within the range.
    /// Any values encountered by advancing backward through the returned state are guaranteed to
    /// not come after the range.
    fn init_backward_state(&mut self) -> Result<IteratorState<K, V>, E> {
        let mut to_visit = vec![];
        let mut node = self.tree.load_node(self.loader)?;
        loop {
            match node {
                Node::Internal {
                    index,
                    mut children,
                } => {
                    let max_child_idx = match self.bounds.end_bound() {
                        Bound::Unbounded => index.len(),
                        Bound::Included(key) => match index.binary_search(&key) {
                            Ok(i) => i + 1,
                            Err(i) => i,
                        },
                        Bound::Excluded(key) => match index.binary_search(&key) {
                            Ok(i) => i,
                            Err(i) => i,
                        },
                    };
                    let _ = children.split_off(max_child_idx + 1);
                    node = children.remove(max_child_idx).load_node(self.loader)?;
                    to_visit.push(children.into());
                }
                Node::Leaf {
                    mut keys,
                    mut values,
                } => {
                    let end = match self.bounds.end_bound() {
                        Bound::Unbounded => keys.len(),
                        Bound::Included(key) => match keys.binary_search(&key) {
                            Ok(i) => i + 1,
                            Err(i) => i,
                        },
                        Bound::Excluded(key) => match keys.binary_search(&key) {
                            Ok(i) => i,
                            Err(i) => i,
                        },
                    };
                    let _ = keys.split_off(end);
                    let _ = values.split_off(end);
                    return Ok(IteratorState {
                        to_visit,
                        keys: keys.into(),
                        values: values.into(),
                    });
                }
            }
        }
    }

    /// Gets the next value within the range by advancing backward through the backward state.
    fn get_next_back(&mut self) -> Result<Option<V>, E> {
        if self.backward.is_none() {
            self.backward = Some(self.init_backward_state()?);
        }
        let state = self.backward.as_mut().expect("we just set this");

        if state.keys.is_empty() {
            'outer: while let Some(next) = state.to_visit.last_mut() {
                if let Some(mut tree) = next.pop_back() {
                    loop {
                        match tree.load_node(self.loader)? {
                            Node::Internal { mut children, .. } => {
                                tree = children.remove(children.len() - 1);
                                state.to_visit.push(children.into());
                            }
                            Node::Leaf { keys, values } => {
                                state.keys = keys.into();
                                state.values = values.into();
                                break 'outer;
                            }
                        }
                    }
                } else {
                    state.to_visit.pop();
                }
            }
        }

        if let Some(key) = state.keys.pop_back() {
            if self.bounds.contains(&key) {
                let ret = state
                    .values
                    .pop_back()
                    .expect("there should be the same number of keys and values")
                    .load(self.loader)?;
                return Ok(Some(ret));
            } else {
                return Ok(None);
            }
        }

        Ok(None)
    }
}

impl<'a, K: Clone + Ord, V: Clone, E, L: Loader<K, V, Error = E>, B: RangeBounds<K>> Iterator
    for Range<'a, K, V, L, B>
{
    type Item = Result<V, E>;

    fn next(&mut self) -> Option<Self::Item> {
        self.get_next().transpose()
    }
}

impl<'a, K: Clone + Ord, V: Clone, E, L: Loader<K, V, Error = E>, B: RangeBounds<K>>
    DoubleEndedIterator for Range<'a, K, V, L, B>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.get_next_back().transpose()
    }
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

    pub fn is_empty<E, L: Loader<K, V, Error = E>>(&self, loader: &mut L) -> Result<bool, E> {
        Ok(match self.load_node(loader)? {
            Node::Internal { index, children } => false,
            Node::Leaf { keys, values } => values.is_empty(),
        })
    }

    /// Gets an item from the B-tree, if it exists.
    pub fn get<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &mut L,
        key: &K,
    ) -> Result<Option<V>, E> {
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

    /// Gets a range of items from the B-tree.
    pub fn get_range<'a, E, L: Loader<K, V, Error = E>, B: RangeBounds<K>>(
        &'a self,
        loader: &'a mut L,
        bounds: B,
    ) -> Range<'a, K, V, L, B> {
        Range::new(self, loader, bounds)
    }

    /// Inserts a new item into the B-tree or updates an existing one. `value` is a function that
    /// is invoked with the existing value for the key. If it returns `None`, no change is made.
    /// Otherwise the item is updated and its previous value is returned.
    pub fn insert<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &mut L,
        key: K,
        value: V,
    ) -> Result<(Self, Option<Value<V>>), E> {
        Ok(self
            .insert_conditionally(loader, key, |_, _| Ok(Some(value)))?
            .expect("this is unconditional"))
    }

    /// Inserts a new item into the B-tree or updates an existing one. `value` is a function that
    /// is invoked with the existing value for the key. If it returns `None`, no change is made.
    /// Otherwise the item is updated and its previous value is returned.
    pub fn insert_conditionally<
        E,
        L: Loader<K, V, Error = E>,
        F: FnOnce(&mut L, Option<&Value<V>>) -> Result<Option<V>, E>,
    >(
        &self,
        loader: &mut L,
        key: K,
        value: F,
    ) -> Result<Option<(Self, Option<Value<V>>)>, E> {
        Ok(self.insert_impl(loader, key, value)?.map(|(node, prev)| {
            (
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
            )
        }))
    }

    fn insert_impl<
        E,
        L: Loader<K, V, Error = E>,
        F: FnOnce(&mut L, Option<&Value<V>>) -> Result<Option<V>, E>,
    >(
        &self,
        loader: &mut L,
        key: K,
        value: F,
    ) -> Result<Option<(Node<K, V>, Option<Value<V>>)>, E> {
        Ok(match self.load_node(loader)? {
            Node::Internal { index, children } => {
                let i = match index.binary_search(&key) {
                    Ok(i) => i + 1,
                    Err(i) => i,
                };
                let mut new_children = Vec::with_capacity(children.len() + 1);
                new_children.extend_from_slice(&children[..i]);
                children[i]
                    .insert_impl(loader, key, value)?
                    .map(|(new_child, prev_value)| {
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
                    })
            }
            Node::Leaf {
                mut keys,
                mut values,
            } => match keys.binary_search(&key) {
                Ok(i) => value(loader, Some(&values[i]))?.map(|value| {
                    let prev = std::mem::replace(&mut values[i], Value::Volatile { value });
                    (Node::Leaf { keys, values }, Some(prev))
                }),
                Err(dest) => value(loader, None)?.map(|value| {
                    keys.insert(dest, key);
                    values.insert(dest, Value::Volatile { value });
                    (Node::Leaf { keys, values }, None)
                }),
            },
        })
    }

    /// Deletes an item from the B-tree. If the item existed, its previous value is returned.
    pub fn delete<E, L: Loader<K, V, Error = E>>(
        &self,
        loader: &mut L,
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
        loader: &mut L,
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
    pub fn assert_invariants<E: std::fmt::Debug, L: Loader<K, V, Error = E>>(
        &self,
        loader: &mut L,
    ) {
        self.assert_invariants_impl(loader, true)
    }

    #[cfg(test)]
    pub fn assert_invariants_impl<E: std::fmt::Debug, L: Loader<K, V, Error = E>>(
        &self,
        loader: &mut L,
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

        fn load_node(&mut self, _id: u64) -> Result<Node<i32, String>, Self::Error> {
            panic!("the tests don't persist nodes")
        }

        fn load_value(&mut self, _id: u64) -> Result<String, Self::Error> {
            panic!("the tests don't persist values")
        }
    }

    #[test]
    fn test_tree() {
        let mut storage = Storage;

        let mut root = Tree::<i32, String>::new();
        assert_eq!(root.get(&mut storage, &1).unwrap(), None);

        // insert some arbitrary values
        for i in (100..900).step_by(10) {
            let (new_root, prev) = root.insert(&mut storage, i, i.to_string()).unwrap();
            root = new_root;
            assert_eq!(prev.is_none(), true);
            root.assert_invariants(&mut storage);
        }

        for i in (0..1000).step_by(9) {
            // test inserting the value
            let (new_root, _) = root.insert(&mut storage, i, "-1".to_string()).unwrap();
            root = new_root;
            root.assert_invariants(&mut storage);
            assert_eq!(root.get(&mut storage, &i).unwrap(), Some("-1".to_string()));

            // test updating the value
            let (new_root, prev) = root.insert(&mut storage, i, i.to_string()).unwrap();
            root = new_root;
            root.assert_invariants(&mut storage);
            assert_eq!(
                prev,
                Some(Value::Volatile {
                    value: "-1".to_string()
                })
            );
            assert_eq!(root.get(&mut storage, &i).unwrap(), Some(i.to_string()));
        }

        // test deleting values
        for i in (0..1000).step_by(3) {
            let (root, prev) = root.delete(&mut storage, &i).unwrap();
            if i % 9 == 0 {
                assert_eq!(prev.is_some(), true);
            }
            root.assert_invariants(&mut storage);
            assert_eq!(root.get(&mut storage, &i).unwrap(), None);
        }
    }

    #[test]
    fn test_tree_range() {
        let mut storage = Storage;

        let mut root = Tree::<i32, String>::new();

        // insert some arbitrary values
        for i in 0..100 {
            let (new_root, _) = root.insert(&mut storage, i, i.to_string()).unwrap();
            root = new_root;
            root.assert_invariants(&mut storage);
        }

        // get some forward ranges
        for i in 0..100 {
            assert_eq!(
                root.get_range(&mut storage, i..)
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap(),
                (i..100).map(|n| n.to_string()).collect::<Vec<_>>()
            );

            assert_eq!(
                root.get_range(&mut storage, i..(i + 10))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap(),
                (i..i + 10)
                    .filter_map(|n| if n < 100 { Some(n.to_string()) } else { None })
                    .collect::<Vec<_>>()
            );

            assert_eq!(
                root.get_range(&mut storage, i..=(i + 10))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap(),
                (i..=i + 10)
                    .filter_map(|n| if n < 100 { Some(n.to_string()) } else { None })
                    .collect::<Vec<_>>()
            );
        }

        // get some backward ranges
        for i in 0..100 {
            assert_eq!(
                root.get_range(&mut storage, i..)
                    .rev()
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap(),
                (i..100).rev().map(|n| n.to_string()).collect::<Vec<_>>()
            );

            assert_eq!(
                root.get_range(&mut storage, i..(i + 10))
                    .rev()
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap(),
                (i..i + 10)
                    .rev()
                    .filter_map(|n| if n < 100 { Some(n.to_string()) } else { None })
                    .collect::<Vec<_>>()
            );

            assert_eq!(
                root.get_range(&mut storage, i..=(i + 10))
                    .rev()
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap(),
                (i..=i + 10)
                    .rev()
                    .filter_map(|n| if n < 100 { Some(n.to_string()) } else { None })
                    .collect::<Vec<_>>()
            );
        }
    }
}
