use cached::{stores::SizedCache, Cached};
use std::{hash::Hash, sync::Mutex};

/// Cache is a simple cache, safe for multiple threads, for arbitrary data.
// TODO: we can almost certainly do better than using a mutex
pub struct Cache<K, V>(Mutex<SizedCache<K, V>>);

impl<K: Hash + Eq + Clone, V: Clone> Cache<K, V> {
    pub fn new(size: usize) -> Self {
        Self(Mutex::new(SizedCache::with_size(size)))
    }

    pub fn get(&self, key: &K) -> Option<V> {
        self.0.lock().expect("no poison").cache_get(key).cloned()
    }

    pub fn set(&self, key: K, value: V) {
        self.0.lock().expect("no poison").cache_set(key, value);
    }
}
