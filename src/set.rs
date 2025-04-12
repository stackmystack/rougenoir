use std::borrow::Borrow;

use crate::{Noop, Set, Tree, TreeCallbacks};

impl<T> Set<T, Noop<T, ()>> {
    pub fn new() -> Self {
        Self { tree: Tree::new() }
    }
}

impl<T, C: TreeCallbacks<Key = T, Value = ()> + Default> Default for Set<T, C> {
    fn default() -> Self {
        Self::with_callbacks(C::default())
    }
}

impl<T, C: TreeCallbacks<Key = T, Value = ()>> Set<T, C> {
    pub fn with_callbacks(augmented: C) -> Self {
        Self {
            tree: Tree::with_callbacks(augmented),
        }
    }
}

impl<T, C: TreeCallbacks<Key = T, Value = ()> + Default> Set<T, C> {
    fn clear(&mut self) {
        self.tree.clear();
    }
}

impl<T, C: TreeCallbacks<Key = T, Value = ()>> Set<T, C> {
    pub fn insert(&mut self, key: T) -> bool
    where
        T: Ord,
    {
        self.tree.insert(key, ()).is_none()
    }

    pub fn pop_first(&mut self) -> Option<T> {
        self.tree.pop_first().map(|kv| kv.0)
    }

    pub fn pop_last(&mut self) -> Option<T> {
        self.tree.pop_last().map(|kv| kv.0)
    }

    pub fn remove<Q>(&mut self, key: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.tree.remove(key).is_some()
    }
}

impl<T, C> Set<T, C> {
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.tree.contains_key(key)
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&T>
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.tree.get_key_value(key).map(|(k, _)| k)
    }

    pub fn first(&self) -> Option<&T> {
        self.tree.first_key_value().map(|(k, _)| k)
    }

    pub fn last(&self) -> Option<&T> {
        self.tree.last_key_value().map(|(k, _)| k)
    }

    pub const fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    pub const fn len(&self) -> usize {
        self.tree.len()
    }
}
