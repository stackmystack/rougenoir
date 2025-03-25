use std::marker::PhantomData;

use crate::{Augmenter, DummyAugmenter, Node, Root, RootCached, RootOps};

#[derive(Debug)]
pub struct Tree<R: RootOps> {
    root: R,
}

impl<R: RootOps + Default> Tree<R> {
    fn new() -> Self {
        Tree { root: R::default() }
    }
}

pub type RBTree<K, V> = Tree<Root<K, V, DummyAugmenter<K, V>>>;
pub type RBTreeCached<K, V> = Tree<RootCached<K, V, DummyAugmenter<K, V>>>;
pub type RBTreeAugmented<K, V, A> = Tree<Root<K, V, A>>;
pub type RBTreeCachedAugmented<K, V, A> = Tree<RootCached<K, V, A>>;

pub trait TreeOps {
    type Key;
    type Value;

    // fn delete(&mut self, key: Self::Key, value: Self::Value);
    fn first(&self) -> Option<&Self::Value>;
    // fn get(&self, key: Self::Key) -> Option<&Self::Value>;
    // fn insert(&mut self, key: Self::Key, value: Self::Value);
    // fn last(&self) -> Option<&Self::Value>;
    // fn update(&mut self, key: &Self::Key, value: Self::Value);
}

impl<R: RootOps> TreeOps for Tree<R> {
    type Key = R::Key;
    type Value = R::Value;

    fn first(&self) -> Option<&Self::Value> {
        self.root.first().map(|e| &unsafe { e.as_ref() }.value)
    }
}

#[cfg(test)]
mod test {
    use crate::DummyAugmenter;

    use super::*;

    #[test]
    fn tree_ctor_works() {
        let tree = Tree::<Root<String, String, DummyAugmenter<String, String>>>::new();
        assert_eq!(tree.first(), None)
    }

    #[test]
    fn rbtree_ctor_works() {
        let tree = RBTree::<String, String>::new();
        assert_eq!(tree.first(), None)
    }
}
