use std::{cmp::Ordering::*, ptr::NonNull};

use crate::{Callbacks, Color, Node, NodePtr, NodePtrExt, Tree};

impl<K, V, C: Callbacks<Key = K, Value = V>> Drop for Tree<K, V, C> {
    fn drop(&mut self) {
        enum Direction {
            Left,
            Right,
        }
        let mut parent = self.root.root;
        let mut direction = Vec::new();
        // max depth = 2 × log₂(n+1)
        let log_val = (self.len + 1).checked_ilog2().unwrap_or(0) as usize;
        direction.reserve(log_val.checked_mul(2).unwrap_or(usize::MAX).max(4096));
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

impl<K, V, C: Callbacks<Key = K, Value = V>> Tree<K, V, C> {
    pub fn contains_key(&self, key: &K) -> bool
    where
        K: Ord,
    {
        self.find_node(key).is_some()
    }

    fn find_node(&self, key: &K) -> NodePtr<K, V>
    where
        K: Ord,
    {
        let mut node = self.root.root;
        while let Some(candidate) = node {
            let candidate = unsafe { candidate.as_ref() };
            match key.cmp(&candidate.key) {
                Equal => break,
                Greater => node = candidate.right,
                Less => node = candidate.left,
            }
        }
        node
    }

    pub fn first(&self) -> Option<&V> {
        self.root.first().map(|e| &unsafe { e.as_ref() }.value)
    }

    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        self.root.first().map(|n| {
            let n = unsafe { n.as_ref() };
            (&n.key, &n.value)
        })
    }

    pub fn get(&self, key: &K) -> Option<&V>
    where
        K: Ord,
    {
        self.find_node(key).map(|n| &unsafe { n.as_ref() }.value)
    }

    pub fn get_key_value(&self, key: &K) -> Option<(&K, &V)>
    where
        K: Ord,
    {
        self.find_node(key).map(|n| {
            let n = unsafe { n.as_ref() };
            (&n.key, &n.value)
        })
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        let mut link = &mut self.root.root;
        if link.is_none() {
            let mut node = NonNull::new(Box::into_raw(Box::new(Node::new(key, value))));
            node.set_parent_color(Color::Black as usize);
            self.root.root = node;
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

    // TODO
    // fn keys(&self) -> Keys<'a, K, V>;

    pub fn last(&self) -> Option<&V> {
        self.root.last().map(|n| &unsafe { n.as_ref() }.value)
    }

    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        self.root.last().map(|n| {
            let n = unsafe { n.as_ref() };
            (&n.key, &n.value)
        })
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn pop_first(&mut self) -> Option<(K, V)> {
        Some(self.pop_node(self.root.first()?))
    }

    pub fn pop_last(&mut self) -> Option<(K, V)> {
        Some(self.pop_node(self.root.last()?))
    }

    fn pop_node(&mut self, node: NonNull<Node<K, V>>) -> (K, V) {
        self.root.erase(node);
        let first_node = unsafe { Box::from_raw(node.as_ptr()) };
        self.len -= 1;
        (first_node.key, first_node.value)
    }

    pub fn remove(&mut self, key: &K) -> Option<V>
    where
        K: Ord,
    {
        Some(self.pop_node(self.find_node(key)?).1)
    }

    // TODO
    // fn retain<F>(&mut self, f: F)
    // where
    //     F: FnMut(&Self::Key, &mut Self::Value) -> bool;
    // fn values(&self) -> Values<'a, self::key, self::value>;
    // fn values_mut(&mut self) -> ValuesMut<'a, self::key, self::value>;
}

#[cfg(test)]
mod test {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn tree_ctor_works() {
        let tree = Tree::<usize, String>::new();
        assert_eq!(tree.first(), None);
        assert_eq!(false, tree.contains_key(&42));
    }

    #[test]
    fn contains_many() {
        let forty_two = "forty two".to_string();
        let mut tree = Tree::<usize, String>::new();
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
        let mut tree = Tree::<usize, String>::new();
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
        let mut tree = Tree::<usize, String>::new();
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
        let mut tree = Tree::<usize, String>::new();
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
        let mut tree = Tree::<usize, String>::new();

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

    #[test]
    fn pop_last() {
        let mut tree = Tree::<usize, String>::new();

        let mut res = tree.pop_last();
        assert_eq!(None, res);

        let forty_two = "forty two".to_string();
        tree.insert(42, forty_two.clone());
        res = tree.pop_last();
        assert_eq!(Some((42, forty_two.clone())), res);
        assert_eq!(0, tree.len());
        assert_eq!(false, tree.contains_key(&42));

        let zero = "zero".to_string();
        let hundo = "hundo".to_string();
        tree.insert(42, forty_two.clone());
        tree.insert(0, zero.clone());
        tree.insert(100, hundo.clone());

        res = tree.pop_last();
        assert_eq!(Some((100, hundo.clone())), res);
        assert_eq!(2, tree.len());
        assert_eq!(true, tree.contains_key(&0));
        assert_eq!(true, tree.contains_key(&42));
        assert_eq!(false, tree.contains_key(&100));

        res = tree.pop_last();
        assert_eq!(Some((42, forty_two.clone())), res);
        assert_eq!(1, tree.len());
        assert_eq!(true, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(false, tree.contains_key(&100));

        res = tree.pop_last();
        assert_eq!(Some((0, zero.clone())), res);
        assert_eq!(0, tree.len());
        assert_eq!(false, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(false, tree.contains_key(&100));
    }

    #[test]
    fn remove() {
        let mut tree = Tree::<usize, String>::new();

        let mut res = tree.remove(&42);
        assert_eq!(None, res);

        let forty_two = "forty two".to_string();
        tree.insert(42, forty_two.clone());
        res = tree.remove(&42);
        assert_eq!(Some(forty_two.clone()), res);
        assert_eq!(0, tree.len());
        assert_eq!(false, tree.contains_key(&42));

        let zero = "zero".to_string();
        let hundo = "hundo".to_string();
        tree.insert(42, forty_two.clone());
        tree.insert(0, zero.clone());
        tree.insert(100, hundo.clone());

        res = tree.remove(&42);
        assert_eq!(Some(forty_two.clone()), res);
        assert_eq!(2, tree.len());
        assert_eq!(true, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(true, tree.contains_key(&100));

        res = tree.remove(&0);
        assert_eq!(Some(zero.clone()), res);
        assert_eq!(1, tree.len());
        assert_eq!(false, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(true, tree.contains_key(&100));

        res = tree.remove(&100);
        assert_eq!(Some(hundo.clone()), res);
        assert_eq!(0, tree.len());
        assert_eq!(false, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(false, tree.contains_key(&100));
    }
}
