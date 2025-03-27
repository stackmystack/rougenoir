use std::{cmp::Ordering::*, ptr::NonNull};

use crate::{Color, Node, NodePtrExt, RootOps, Tree, TreeOps};

impl<R: RootOps> Drop for Tree<R> {
    fn drop(&mut self) {
        enum Direction {
            Left,
            Right,
        }
        let mut parent = self.root.root();
        // TODO: allocate once using the tree's depth.
        let mut direction = Vec::new();
        while let Some(current) = parent {
            let current_ref = unsafe { current.as_ref() };
            if current_ref.left.is_some() {
                parent = current_ref.left;
                direction.push(Direction::Left);
                continue;
            }
            if current_ref.right.is_some() {
                parent = current_ref.right;
                direction.push(Direction::Right);
                continue;
            }
            parent = current_ref.parent();
            // drop; don't call rbtree erase => needless overhead.
            if parent.is_some() {
                match direction.pop() {
                    Some(Direction::Left) => unsafe { parent.unwrap().as_mut() }.left = None,
                    Some(Direction::Right) => unsafe { parent.unwrap().as_mut() }.right = None,
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

    fn pop_first(&mut self) -> Option<(Self::Key, Self::Value)> {
        let first_node = self.root.first()?;
        self.root.erase(first_node);
        let first_node = unsafe { Box::from_raw(first_node.as_ptr()) };
        self.len -= 1;
        Some((first_node.key, first_node.value))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{DummyAugmenter, RBTree, Root};

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
    fn insert_multiple_values() {
        let data: Vec<(usize, String)> = (0..100).map(|i| (i, format!("{i}"))).collect();
        let mut tree = RBTree::<usize, String>::new();
        for (k, v) in data.iter() {
            tree.insert(k.clone(), v.to_string());
        }

        assert_eq!(data.len(), tree.len());
        for (k, v) in data.iter() {
            assert_eq!(true, tree.contains_key(k));
            assert_eq!(Some((k, v)), tree.get_key_value(k));
        }
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

    #[test]
    fn pop_first() {
        let mut tree = RBTree::<usize, String>::new();

        let mut res = tree.pop_first();
        assert_eq!(None, res);

        let forty_two = "forty two".to_string();
        tree.insert(42, forty_two.clone());
        res = tree.pop_first();
        assert_eq!(Some((42, forty_two.clone())), res);
        assert_eq!(0, tree.len());
        assert_eq!(false, tree.contains_key(&42));

        let zero = "zero".to_string();
        let hundo = "hundo".to_string();
        tree.insert(42, forty_two.clone());
        tree.insert(0, zero.clone());
        tree.insert(100, hundo.clone());

        res = tree.pop_first();
        assert_eq!(Some((0, zero.clone())), res);
        assert_eq!(2, tree.len());
        assert_eq!(false, tree.contains_key(&0));
        assert_eq!(true, tree.contains_key(&42));
        assert_eq!(true, tree.contains_key(&100));

        res = tree.pop_first();
        assert_eq!(Some((42, forty_two.clone())), res);
        assert_eq!(1, tree.len());
        assert_eq!(false, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(true, tree.contains_key(&100));

        res = tree.pop_first();
        assert_eq!(Some((100, hundo.clone())), res);
        assert_eq!(0, tree.len());
        assert_eq!(false, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(false, tree.contains_key(&100));
    }
}
