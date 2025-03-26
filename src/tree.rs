use std::{cmp::Ordering::*, ptr::NonNull};

use crate::{Color, DummyAugmenter, Node, NodePtrExt, Root, RootCached, RootOps};

#[derive(Debug)]
pub struct Tree<R: RootOps> {
    len: usize,
    root: R,
}

impl<R: RootOps + Default> Tree<R> {
    fn new() -> Self {
        Tree {
            len: 0,
            root: R::default(),
        }
    }
}

pub type RBTree<K, V> = Tree<Root<K, V, DummyAugmenter<K, V>>>;
pub type RBTreeCached<K, V> = Tree<RootCached<K, V, DummyAugmenter<K, V>>>;
pub type RBTreeAugmented<K, V, A> = Tree<Root<K, V, A>>;
pub type RBTreeCachedAugmented<K, V, A> = Tree<RootCached<K, V, A>>;

pub trait TreeOps {
    type Key;
    type Value;

    fn contains_key(&self, key: &Self::Key) -> bool;
    fn first(&self) -> Option<&Self::Value>;
    fn first_key_value(&self) -> Option<(&Self::Key, &Self::Value)>;
    fn get(&self, key: &Self::Key) -> Option<&Self::Value>;
    fn get_key_value(&self, key: &Self::Key) -> Option<(&Self::Key, &Self::Value)>;
    fn insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value>;
    // fn keys(&self) -> Keys<'a, K, V>;
    fn last(&self) -> Option<&Self::Value>;
    fn last_key_value(&self) -> Option<(&Self::Key, &Self::Value)>;
    fn len(&self) -> usize;
    // fn pop_first(&mut self) -> Option<(&Self::Key, &Self::Value)>;
    // fn pop_last(&mut self) -> Option<(&Self::Key, &Self::Value)>;
    // fn remove(&mut self, key: Self::Key, value: Self::Value);
    // fn retain<F>(&mut self, f: F)
    // where
    //     F: FnMut(&Self::Key, &mut Self::Value) -> bool;
    // fn update(&mut self, key: &Self::Key, value: Self::Value);
    // fn values(&self) -> Values<'a, self::key, self::value>;
    // fn values_mut(&mut self) -> ValuesMut<'a, self::key, self::value>;
}

impl<R: RootOps> Drop for Tree<R> {
    fn drop(&mut self) {
        enum Direction {
            Left,
            Right,
            None,
        }
        let mut parent = self.root.root();
        let mut direction = Direction::None;
        while let Some(current) = parent {
            let current_ref = unsafe { current.as_ref() };
            if current_ref.left.is_some() {
                parent = current_ref.left;
                direction = Direction::Left;
                continue;
            }
            if current_ref.right.is_some() {
                parent = current_ref.right;
                direction = Direction::Right;
                continue;
            }
            parent = current_ref.parent();
            // drop; don't call rbtree erase => needless overhead.
            if parent.is_some() {
                match &direction {
                    Direction::Left => unsafe { parent.unwrap().as_mut() }.left = None,
                    Direction::Right => unsafe { parent.unwrap().as_mut() }.right = None,
                    _ => {}
                }
            }
            let _ = unsafe { Box::from_raw(current.as_ptr()) };
        }
    }
}

impl<R: RootOps> TreeOps for Tree<R> {
    type Key = R::Key;
    type Value = R::Value;

    fn contains_key(&self, key: &Self::Key) -> bool {
        self.get_key_value(key).is_some()
    }

    fn first(&self) -> Option<&Self::Value> {
        self.root.first().map(|e| &unsafe { e.as_ref() }.value)
    }

    fn first_key_value(&self) -> Option<(&Self::Key, &Self::Value)> {
        self.root.first().map(|e| {
            let e = unsafe { e.as_ref() };
            (&e.key, &e.value)
        })
    }

    fn get(&self, key: &Self::Key) -> Option<&Self::Value> {
        self.get_key_value(key).map(|(_, v)| v)
    }

    fn get_key_value(&self, key: &Self::Key) -> Option<(&Self::Key, &Self::Value)> {
        let mut node = self.root.root();
        while let Some(candidate) = node {
            let candidate = unsafe { candidate.as_ref() };
            match key.cmp(&candidate.key) {
                Equal => break,
                Greater => node = candidate.right,
                Less => node = candidate.left,
            }
        }
        node.map(|e| {
            let e = unsafe { e.as_ref() };
            (&e.key, &e.value)
        })
    }

    fn insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value> {
        let mut link = &mut self.root.root();
        if link.is_none() {
            let mut node = NonNull::new(Box::into_raw(Box::new(Node::new(key, value))));
            node.set_parent_color(Color::Black as usize);
            self.root.set_root(node);
            self.len += 1;
            return None;
        }

        let mut parent = link.unwrap().as_ptr();
        while let Some(mut candidate) = link.clone() {
            parent = link.unwrap().as_ptr();
            let candidate = unsafe { candidate.as_mut() };
            match key.cmp(&candidate.key) {
                Equal => {
                    return Some(std::mem::replace(&mut candidate.value, value));
                }
                Greater => link = &mut candidate.right,
                Less => link = &mut candidate.left,
            }
        }

        let mut node = Box::new(Node::new(key, value));
        node.link(NonNull::new(parent).unwrap(), &mut link);
        let node = NonNull::new(Box::into_raw(node));
        self.root.insert(node.expect("cannot be null"));
        self.len += 1;
        None
    }

    fn last(&self) -> Option<&Self::Value> {
        self.root.last().map(|e| &unsafe { e.as_ref() }.value)
    }

    fn last_key_value(&self) -> Option<(&Self::Key, &Self::Value)> {
        self.root.last().map(|e| {
            let e = unsafe { e.as_ref() };
            (&e.key, &e.value)
        })
    }

    fn len(&self) -> usize {
        self.len
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::DummyAugmenter;

    use pretty_assertions::assert_eq;

    #[test]
    fn tree_ctor_works() {
        let tree = Tree::<Root<usize, String, DummyAugmenter<usize, String>>>::new();
        assert_eq!(tree.first(), None);
        assert_eq!(false, tree.contains_key(&42));
    }

    #[test]
    fn rbtree_ctor_works() {
        let tree = RBTree::<usize, String>::new();
        assert_eq!(tree.first(), None);
        assert_eq!(false, tree.contains_key(&42));
    }

    #[test]
    fn contains_many() {
        let forty_two = "forty two".to_string();
        let mut tree = RBTree::<usize, String>::new();
        let mut res = tree.insert(42, forty_two);
        assert_eq!(None, res);
        assert_eq!(1, tree.len());

        let zero = "zero".to_string();
        let hando = "hundo".to_string();
        res = tree.insert(0, zero);
        assert_eq!(None, res);
        assert_eq!(2, tree.len());
        res = tree.insert(100, hando);
        assert_eq!(None, res);
        assert_eq!(3, tree.len());

        assert_eq!(true, tree.contains_key(&42));
        assert_eq!(true, tree.contains_key(&0));
        assert_eq!(true, tree.contains_key(&100));
        assert_eq!(false, tree.contains_key(&1));
        assert_eq!(false, tree.contains_key(&1000));
    }

    #[test]
    fn first_and_last() {
        let mut tree = RBTree::<usize, String>::new();
        assert_eq!(None, tree.first());
        assert_eq!(None, tree.last());

        let forty_two = "forty two".to_string();
        tree.insert(42, forty_two.clone());
        assert_eq!(Some(&forty_two), tree.first());
        assert_eq!(Some((&42, &forty_two)), tree.first_key_value());
        assert_eq!(Some((&42, &forty_two)), tree.last_key_value());

        let zero = "zero".to_string();
        let hundo = "hundo".to_string();
        tree.insert(0, zero.clone());
        tree.insert(100, hundo.clone());

        assert_eq!(Some(&zero), tree.first());
        assert_eq!(Some((&0, &zero)), tree.first_key_value());
        assert_eq!(Some(&hundo), tree.last());
        assert_eq!(Some((&100, &hundo)), tree.last_key_value());
    }

    #[test]
    fn insert_same_key() {
        let mut tree = RBTree::<usize, String>::new();
        let forty_two = "forty two".to_string();
        let mut res = tree.insert(42, forty_two.clone());
        assert_eq!(None, res);
        assert_eq!(1, tree.len());
        res = tree.insert(42, "42".to_string());
        assert_eq!(Some(forty_two), res);
        assert_eq!(1, tree.len());
    }
}
