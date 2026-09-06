use std::borrow::Borrow;

use crate::{
    Noop, Set, Tree, TreeCallbacks,
    alloc::{Allocator, Global},
};

impl<T> Set<T, Noop<T, ()>> {
    pub fn new() -> Self {
        Self { tree: Tree::new() }
    }
}

impl<T, A: Allocator> Set<T, Noop<T, ()>, A> {
    /// Creates an empty `Set` whose nodes are allocated from `alloc`.
    pub fn new_in(alloc: A) -> Self {
        Self {
            tree: Tree::new_in(alloc),
        }
    }
}

impl<T, C: TreeCallbacks<Key = T, Value = ()> + Default, A: Allocator + Default> Default
    for Set<T, C, A>
{
    fn default() -> Self {
        Self::with_callbacks_in(C::default(), A::default())
    }
}

impl<T, C: TreeCallbacks<Key = T, Value = ()>> Set<T, C, Global> {
    pub fn with_callbacks(augmented: C) -> Self {
        Self {
            tree: Tree::with_callbacks(augmented),
        }
    }
}

impl<T, C: TreeCallbacks<Key = T, Value = ()>, A: Allocator> Set<T, C, A> {
    /// Creates an empty `Set` with the given augmentation callbacks, whose
    /// nodes are allocated from `alloc`.
    pub fn with_callbacks_in(augmented: C, alloc: A) -> Self {
        Self {
            tree: Tree::with_callbacks_in(augmented, alloc),
        }
    }
}

// impl<T, C: TreeCallbacks<Key = T, Value = ()> + Default> Set<T, C> {
//     fn clear(&mut self) {
//         self.tree.clear();
//     }
// }

impl<T, C: TreeCallbacks<Key = T, Value = ()>, A: Allocator> Set<T, C, A> {
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

impl<T, C, A: Allocator> Set<T, C, A> {
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
