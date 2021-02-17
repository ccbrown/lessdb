use super::b_tree::{Loader, Node as BTreeNode, Range as BTreeRange, Tree as BTree};
use bytes::{BufMut, Bytes, BytesMut};
use serde::{Deserialize, Serialize};
use std::ops::{Bound, RangeBounds};

#[derive(Clone, Serialize, Deserialize)]
pub struct Key {
    pub primary: PrimaryKey,
    pub secondary_sort: Option<Bytes>,
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PrimaryKey {
    pub hash: Bytes,
    pub sort: Bytes,
}

const ESCAPE_BYTE: u8 = 1;

impl PrimaryKey {
    fn normalize(&self) -> Bytes {
        if self.sort.is_empty() {
            self.hash.clone()
        } else {
            let mut ret = BytesMut::with_capacity(self.hash.len() + self.sort.len());
            ret.extend_from_slice(&self.hash);
            ret.extend_from_slice(&self.sort);
            ret.freeze()
        }
    }

    fn normalize_bound(b: Bound<&Self>) -> Bound<Bytes> {
        match b {
            Bound::Unbounded => Bound::Unbounded,
            Bound::Included(k) => Bound::Included(k.normalize()),
            Bound::Excluded(k) => Bound::Excluded(k.normalize()),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SecondaryKey {
    pub hash: Bytes,
    pub secondary_sort: Bytes,
    pub primary_sort: Bytes,
}

impl SecondaryKey {
    fn normalize(&self) -> Bytes {
        if self.primary_sort.is_empty() && self.secondary_sort.is_empty() {
            self.hash.clone()
        } else {
            let mut ret = BytesMut::with_capacity(
                self.hash.len() + (self.secondary_sort.len() + self.primary_sort.len()) * 2,
            );
            ret.extend_from_slice(&self.hash);

            for &b in &self.secondary_sort {
                if b == 0 || b == ESCAPE_BYTE {
                    ret.put_u8(ESCAPE_BYTE);
                }
                ret.put_u8(b);
            }
            ret.put_u8(0);

            ret.extend_from_slice(&self.primary_sort);

            ret.freeze()
        }
    }

    fn normalize_bound(b: Bound<&Self>) -> Bound<Bytes> {
        match b {
            Bound::Unbounded => Bound::Unbounded,
            Bound::Included(k) => Bound::Included(k.normalize()),
            Bound::Excluded(k) => Bound::Excluded(k.normalize()),
        }
    }
}

pub type NormalizedNode<V> = BTreeNode<Bytes, Value<V>>;

#[derive(Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct Value<V> {
    pub secondary_sort: Option<Bytes>,
    pub value: V,
}

#[derive(Clone, Debug)]
pub struct Tree<V: Clone> {
    pub primary_tree: BTree<Bytes, Value<V>>,
    pub secondary_tree: BTree<Bytes, Value<V>>,
}

pub struct Range<'a, V: Clone, L, B>(BTreeRange<'a, Bytes, Value<V>, L, B>);

impl<'a, V: Clone, E, L: Loader<Bytes, Value<V>, Error = E>, B: RangeBounds<Bytes>> Iterator
    for Range<'a, V, L, B>
{
    type Item = Result<V, E>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|v| v.map(|v| v.value))
    }
}

impl<'a, V: Clone, E, L: Loader<Bytes, Value<V>, Error = E>, B: RangeBounds<Bytes>>
    DoubleEndedIterator for Range<'a, V, L, B>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|v| v.map(|v| v.value))
    }
}

impl<V: Clone> Tree<V> {
    /// Creates a new, empty B-tree.
    pub fn new() -> Self {
        Self {
            primary_tree: BTree::new(),
            secondary_tree: BTree::new(),
        }
    }

    pub fn is_empty<E, L: Loader<Bytes, Value<V>, Error = E>>(
        &self,
        loader: &L,
    ) -> Result<bool, E> {
        self.primary_tree.is_empty(loader)
    }

    pub fn is_persisted(&self) -> bool {
        self.primary_tree.is_persisted() && self.secondary_tree.is_persisted()
    }

    /// Gets an item from the B-tree, if it exists.
    pub fn get<E, L: Loader<Bytes, Value<V>, Error = E>>(
        &self,
        loader: &L,
        key: &PrimaryKey,
    ) -> Result<Option<V>, E> {
        Ok(self
            .primary_tree
            .get(loader, &key.normalize())?
            .map(|v| v.value.clone()))
    }

    /// Gets a range of items based on their primary key.
    pub fn get_range_by_primary_key<
        'a,
        E,
        L: Loader<Bytes, Value<V>, Error = E>,
        B: RangeBounds<PrimaryKey>,
    >(
        &'a self,
        loader: &'a L,
        bounds: B,
    ) -> Range<'a, V, L, (Bound<Bytes>, Bound<Bytes>)> {
        Range(self.primary_tree.get_range(
            loader,
            (
                PrimaryKey::normalize_bound(bounds.start_bound()),
                PrimaryKey::normalize_bound(bounds.end_bound()),
            ),
        ))
    }

    /// Counts a range of items based on their primary key.
    pub fn count_range_by_primary_key<
        'a,
        E,
        L: Loader<Bytes, Value<V>, Error = E>,
        B: RangeBounds<PrimaryKey>,
    >(
        &'a self,
        loader: &'a L,
        bounds: B,
    ) -> Result<u64, E> {
        self.primary_tree.count(
            loader,
            (
                PrimaryKey::normalize_bound(bounds.start_bound()),
                PrimaryKey::normalize_bound(bounds.end_bound()),
            ),
        )
    }

    /// Gets a range of items based on their secondary key.
    pub fn get_range_by_secondary_key<
        'a,
        E,
        L: Loader<Bytes, Value<V>, Error = E>,
        B: RangeBounds<SecondaryKey>,
    >(
        &'a self,
        loader: &'a L,
        bounds: B,
    ) -> Range<'a, V, L, (Bound<Bytes>, Bound<Bytes>)> {
        Range(self.secondary_tree.get_range(
            loader,
            (
                SecondaryKey::normalize_bound(bounds.start_bound()),
                SecondaryKey::normalize_bound(bounds.end_bound()),
            ),
        ))
    }

    /// Counts a range of items based on their secondary key.
    pub fn count_range_by_secondary_key<
        'a,
        E,
        L: Loader<Bytes, Value<V>, Error = E>,
        B: RangeBounds<SecondaryKey>,
    >(
        &'a self,
        loader: &'a L,
        bounds: B,
    ) -> Result<u64, E> {
        self.secondary_tree.count(
            loader,
            (
                SecondaryKey::normalize_bound(bounds.start_bound()),
                SecondaryKey::normalize_bound(bounds.end_bound()),
            ),
        )
    }

    /// Inserts a new item into the B-tree or updates an existing one.
    pub fn insert<E, L: Loader<Bytes, Value<V>, Error = E>, F: FnOnce(Option<&V>) -> Option<V>>(
        &self,
        loader: &L,
        key: Key,
        value: F,
    ) -> Result<Self, E> {
        let mut new_value = None;
        let mut prev_value = None;

        let primary_key = key.primary.normalize();

        let (primary_tree, _) = match self.primary_tree.insert_conditionally(
            loader,
            primary_key.clone(),
            |loader, prev| {
                prev_value = match prev {
                    Some(prev) => Some(prev.clone().load(loader)?),
                    None => None,
                };
                Ok(
                    value(prev_value.as_ref().map(|prev| &prev.value)).map(|value| {
                        let value = Value {
                            secondary_sort: key.secondary_sort.clone(),
                            value: value,
                        };
                        new_value = Some(value.clone());
                        value
                    }),
                )
            },
        )? {
            Some(result) => result,
            None => return Ok(self.clone()),
        };

        let mut secondary_tree = match prev_value.and_then(|prev| prev.secondary_sort) {
            Some(prev_secondary_sort) => {
                let (tree, _) = self.secondary_tree.delete(
                    loader,
                    &SecondaryKey {
                        hash: key.primary.hash.clone(),
                        secondary_sort: prev_secondary_sort,
                        primary_sort: key.primary.sort.clone(),
                    }
                    .normalize(),
                )?;
                tree
            }
            None => self.secondary_tree.clone(),
        };

        if let (Some(new_value), Some(secondary_sort)) = (new_value, key.secondary_sort) {
            let (tree, _) = secondary_tree.insert(
                loader,
                SecondaryKey {
                    hash: key.primary.hash,
                    secondary_sort: secondary_sort,
                    primary_sort: key.primary.sort,
                }
                .normalize(),
                new_value,
            )?;
            secondary_tree = tree;
        }

        Ok(Self {
            primary_tree,
            secondary_tree,
        })
    }

    /// Deletes a new item from the B-tree. Returns the previous value if the item existed.
    pub fn delete<E, L: Loader<Bytes, Value<V>, Error = E>>(
        &self,
        loader: &L,
        key: &PrimaryKey,
    ) -> Result<(Self, Option<V>), E> {
        let (primary_tree, prev) = self.primary_tree.delete(loader, &key.normalize())?;
        let prev = prev
            .map(|prev| -> Result<_, _> { Ok(prev.load(loader)?) })
            .transpose()?;

        let secondary_tree = match prev.as_ref().and_then(|prev| prev.secondary_sort.clone()) {
            Some(prev_secondary_sort) => {
                let (tree, _) = self.secondary_tree.delete(
                    loader,
                    &SecondaryKey {
                        hash: key.hash.clone(),
                        secondary_sort: prev_secondary_sort,
                        primary_sort: key.sort.clone(),
                    }
                    .normalize(),
                )?;
                tree
            }
            None => self.secondary_tree.clone(),
        };

        Ok((
            Self {
                primary_tree,
                secondary_tree,
            },
            prev.map(|prev| prev.value),
        ))
    }

    #[cfg(test)]
    pub fn assert_invariants<E: std::fmt::Debug, L: Loader<Bytes, Value<V>, Error = E>>(
        &self,
        loader: &L,
    ) {
        self.primary_tree.assert_invariants(loader);
        self.secondary_tree.assert_invariants(loader);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::b_tree::Node;

    struct Storage;

    impl Loader<Bytes, Value<String>> for Storage {
        type Error = ();

        fn load_node(&self, _id: u64) -> Result<Node<Bytes, Value<String>>, Self::Error> {
            panic!("the tests don't persist nodes")
        }

        fn load_value(&self, _id: u64) -> Result<Value<String>, Self::Error> {
            panic!("the tests don't persist values")
        }
    }

    fn bytes(n: i32) -> Bytes {
        i32::to_be_bytes(n).to_vec().into()
    }

    #[test]
    fn test_tree() {
        let storage = Storage;

        let mut root = Tree::<String>::new();
        assert_eq!(
            root.get(
                &storage,
                &PrimaryKey {
                    hash: bytes(1),
                    sort: bytes(1)
                }
            )
            .unwrap(),
            None
        );

        let primary_key = |i| PrimaryKey {
            hash: bytes(i),
            sort: bytes(i),
        };

        let key = |i| Key {
            primary: primary_key(i),
            secondary_sort: Some(bytes(i)),
        };

        // insert some arbitrary values
        for i in (100..900).step_by(10) {
            root = root
                .insert(&storage, key(i), |_| Some(i.to_string()))
                .unwrap();
            root.assert_invariants(&storage);
        }

        for i in (0..1000).step_by(9) {
            // test inserting the value
            root = root
                .insert(&storage, key(i), |_| Some("-1".to_string()))
                .unwrap();
            root.assert_invariants(&storage);
            assert_eq!(
                root.get(&storage, &primary_key(i)).unwrap(),
                Some("-1".to_string())
            );

            // test updating the value
            root = root
                .insert(&storage, key(i), |_| Some(i.to_string()))
                .unwrap();
            root.assert_invariants(&storage);
            assert_eq!(
                root.get(&storage, &primary_key(i)).unwrap(),
                Some(i.to_string())
            );
        }

        // test deleting values
        for i in (0..1000).step_by(3) {
            let (root, _) = root.delete(&storage, &primary_key(i)).unwrap();
            root.assert_invariants(&storage);
            assert_eq!(root.get(&storage, &primary_key(i)).unwrap(), None);
        }
    }
}
