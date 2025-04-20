use std::{
    borrow::Borrow,
    cmp::Ordering::{self, *},
    mem,
    ops::Index,
};

use crate::{
    CachedTree, Direction, Node, NodePtr, NodePtrExt, Noop, Root, TreeCallbacks, alloc_node,
    dealloc_root,
};

impl<K, V> CachedTree<K, V, Noop<K, V>> {
    pub fn new() -> Self {
        CachedTree {
            leftmost: None,
            len: 0,
            root: Root::new(Noop::new()),
        }
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V> + Default> Default for CachedTree<K, V, C> {
    fn default() -> Self {
        Self::with_callbacks(C::default())
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> CachedTree<K, V, C> {
    pub fn with_callbacks(augmented: C) -> Self {
        CachedTree {
            leftmost: None,
            len: 0,
            root: Root::new(augmented),
        }
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V> + Default> CachedTree<K, V, C> {
    pub fn clear(&mut self) {
        drop(CachedTree {
            leftmost: None,
            len: mem::replace(&mut self.len, 0),
            root: Root {
                callbacks: mem::take(&mut self.root.callbacks),
                node: mem::take(&mut self.root.node),
            },
        });
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> CachedTree<K, V, C> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        match self.root.node {
            None => {
                self.root.node = unsafe { alloc_node(key, value) };
                self.len += 1;
                self.leftmost = self.root.node;
                None
            }
            Some(_) => {
                let mut current_node = self.root.node.ptr();
                let mut parent = current_node;
                let mut direction = Direction::None;
                while !current_node.is_null() {
                    parent = current_node;
                    match key.cmp(&unsafe { current_node.as_ref().unwrap() }.key) {
                        Equal => {
                            let res = std::mem::replace(
                                &mut unsafe { current_node.as_mut().unwrap() }.value,
                                value,
                            );
                            return Some(res);
                        }
                        Greater => {
                            direction = Direction::Right;
                            current_node = unsafe { current_node.as_ref().unwrap() }.right.ptr();
                        }
                        Less => {
                            direction = Direction::Left;
                            current_node = unsafe { current_node.as_ref().unwrap() }.left.ptr();
                        }
                    };
                }

                let mut node = unsafe { alloc_node(key, value) };
                node.link(parent, direction);
                self.root.insert(node.expect("can never be None"));
                self.len += 1;
                if matches!(direction, Direction::Left) {
                    self.leftmost = node;
                }
                None
            }
        }
    }

    pub fn pop_first(&mut self) -> Option<(K, V)> {
        Some(self.pop_node(self.root.first()?.as_ptr()))
    }

    pub fn pop_last(&mut self) -> Option<(K, V)> {
        Some(self.pop_node(self.root.last()?.as_ptr()))
    }

    pub(crate) fn pop_node(&mut self, node: *mut Node<K, V>) -> (K, V) {
        // TODO: we have a second place to dealloc. Should we use dealloc_node?
        let node = unsafe { Box::from_raw(node) };
        let victim = node.as_ref();
        self.root.erase(victim.into());
        self.len -= 1;
        if self.leftmost == victim.into() {
            self.leftmost = node.next();
        }
        (node.key, node.value)
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        Some(self.pop_node(self.find_node(key)?.as_ptr()))
    }
}

impl<K, V, C> CachedTree<K, V, C> {
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.find_node(key).is_some()
    }

    fn find_node<Q>(&self, key: &Q) -> NodePtr<K, V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        if self
            .leftmost
            .is_some_and(|l| unsafe { l.as_ref() }.key.borrow() == key)
        {
            return self.leftmost;
        }

        let mut node = self.root.node;
        while let Some(candidate) = node {
            let candidate = unsafe { candidate.as_ref() };
            match key.cmp(candidate.key.borrow()) {
                Equal => break,
                Greater => node = candidate.right,
                Less => node = candidate.left,
            }
        }
        node
    }

    pub fn first(&self) -> Option<&V> {
        self.leftmost.map(|e| &unsafe { e.as_ref() }.value)
    }

    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        self.leftmost.map(|n| {
            let n = unsafe { n.as_ref() };
            (&n.key, &n.value)
        })
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.find_node(key).map(|n| &unsafe { n.as_ref() }.value)
    }

    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        self.find_node(key).map(|n| {
            let n = unsafe { n.as_ref() };
            (&n.key, &n.value)
        })
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

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
}

impl<K, Q: ?Sized, V, C: TreeCallbacks<Key = K, Value = V>> Index<&Q> for CachedTree<K, V, C>
where
    K: Borrow<Q> + Ord,
    Q: Ord,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `Tree`.
    #[inline]
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<K, V, C> Drop for CachedTree<K, V, C> {
    fn drop(&mut self) {
        unsafe {
            dealloc_root(&mut self.root, self.len);
        }
    }
}

#[cfg(debug_assertions)]
impl<K, V, C> CachedTree<K, V, C>
where
    K: std::fmt::Debug,
{
    #[allow(dead_code)]
    fn validate(&self) -> bool {
        self.root.validate()
    }
}

impl<K, V, C> std::fmt::Debug for CachedTree<K, V, C>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
    C: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: PartialEq, V: PartialEq, C: PartialEq> PartialEq for CachedTree<K, V, C> {
    fn eq(&self, other: &CachedTree<K, V, C>) -> bool {
        self.len() == other.len()
            && self.root.callbacks == other.root.callbacks
            && self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl<K, V, C> Clone for CachedTree<K, V, C>
where
    K: Clone + Ord,
    V: Clone,
    C: Clone + TreeCallbacks<Key = K, Value = V>,
{
    fn clone(&self) -> Self {
        if self.is_empty() {
            CachedTree {
                leftmost: None,
                len: 0,
                root: self.root.clone(),
            }
        } else {
            let mut tree = CachedTree {
                leftmost: None,
                len: 0,
                root: Root {
                    callbacks: self.root.callbacks.clone(),
                    node: None,
                },
            };
            for (k, v) in self.iter() {
                tree.insert(k.clone(), v.clone());
            }
            tree
        }
    }
}

impl<K: PartialOrd, V: PartialOrd, C: PartialOrd> PartialOrd for CachedTree<K, V, C> {
    #[inline]
    fn partial_cmp(&self, other: &CachedTree<K, V, C>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K: Eq, V: Eq, C: Eq> Eq for CachedTree<K, V, C> {}

impl<K: Ord, V: Ord, C: Ord> Ord for CachedTree<K, V, C> {
    #[inline]
    fn cmp(&self, other: &CachedTree<K, V, C>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

unsafe impl<K, V, C> Send for CachedTree<K, V, C>
where
    K: Send,
    V: Send,
    C: Send,
{
}

unsafe impl<K, V, C> Sync for CachedTree<K, V, C>
where
    K: Sync,
    V: Sync,
    C: Sync,
{
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Noop;
    use pretty_assertions::{assert_eq, assert_ne};
    use quickcheck_macros::quickcheck;
    use rand::SeedableRng;
    use rand::seq::SliceRandom;
    use rand_chacha::ChaCha8Rng;

    #[test]
    fn clear() {
        let mut tree = CachedTree::new();
        tree.clear();
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(true, tree.is_empty());

        let forty_two = "forty two".to_string();
        tree.insert(42, forty_two.clone());
        assert_eq!(true, tree.contains_key(&42));
        assert_eq!(false, tree.is_empty());
        assert_eq!(1, tree.len());

        tree.clear();
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(0, tree.len());

        let zero = "zero".to_string();
        let hundo = "hundo".to_string();
        tree.insert(0, zero);
        tree.insert(42, forty_two.clone());
        tree.insert(100, hundo);
        assert_eq!(true, tree.contains_key(&0));
        assert_eq!(true, tree.contains_key(&42));
        assert_eq!(true, tree.contains_key(&100));
        assert_eq!(false, tree.is_empty());

        tree.clear();
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(0, tree.len());
        assert_eq!(true, tree.is_empty());
    }

    #[test]
    fn clone_and_eq_for_unit() {
        let mut t1 = CachedTree::new();
        let mut t2 = t1.clone();
        assert_eq!(t1, t2);

        t1.insert(0, ());
        t1.insert(1, ());
        t1.insert(2, ());

        assert_ne!(t1, t2);
        assert_eq!(3, t1.len());
        assert_eq!(0, t2.len());
        assert_eq!(true, t1.contains_key(&0));
        assert_eq!(true, t1.contains_key(&1));
        assert_eq!(true, t1.contains_key(&2));
        assert_eq!(false, t2.contains_key(&0));
        assert_eq!(false, t2.contains_key(&1));
        assert_eq!(false, t2.contains_key(&2));

        t2.insert(0, ());
        t2.insert(1, ());
        t2.insert(2, ());
        assert_eq!(t1, t2);
        assert_eq!(3, t1.len());
        assert_eq!(3, t2.len());
        assert_eq!(true, t1.contains_key(&0));
        assert_eq!(true, t1.contains_key(&1));
        assert_eq!(true, t1.contains_key(&2));
        assert_eq!(true, t2.contains_key(&0));
        assert_eq!(true, t2.contains_key(&1));
        assert_eq!(true, t2.contains_key(&2));
    }

    #[test]
    fn clone_and_eq_for_string() {
        let mut t1 = CachedTree::new();
        let mut t2 = t1.clone();
        assert_eq!(t1, t2);

        t1.insert(0, "zero".to_string());
        t1.insert(1, "one".to_string());
        t1.insert(2, "two".to_string());

        assert_ne!(t1, t2);
        assert_eq!(true, t1.contains_key(&0));
        assert_eq!(true, t1.contains_key(&1));
        assert_eq!(true, t1.contains_key(&2));
        assert_eq!(false, t2.contains_key(&0));
        assert_eq!(false, t2.contains_key(&1));
        assert_eq!(false, t2.contains_key(&2));

        t2.insert(0, "zero".to_string());
        t2.insert(1, "one".to_string());
        t2.insert(2, "two".to_string());
        assert_eq!(t1, t2);
        assert_eq!(3, t1.len());
        assert_eq!(3, t2.len());
        assert_eq!(true, t1.contains_key(&0));
        assert_eq!(true, t1.contains_key(&1));
        assert_eq!(true, t1.contains_key(&2));
        assert_eq!(true, t2.contains_key(&0));
        assert_eq!(true, t2.contains_key(&1));
        assert_eq!(true, t2.contains_key(&2));
    }

    #[test]
    fn clone_and_eq_for_str() {
        let mut t1 = CachedTree::new();
        let mut t2 = t1.clone();
        assert_eq!(t1, t2);

        let zero_0 = "zero";
        let one_0 = "one";
        let two_0 = "two";

        t1.insert(0, zero_0);
        t1.insert(1, one_0);
        t1.insert(2, two_0);

        assert_ne!(t1, t2);
        assert_eq!(true, t1.contains_key(&0));
        assert_eq!(true, t1.contains_key(&1));
        assert_eq!(true, t1.contains_key(&2));
        assert_eq!(false, t2.contains_key(&0));
        assert_eq!(false, t2.contains_key(&1));
        assert_eq!(false, t2.contains_key(&2));

        t2.insert(0, zero_0);
        t2.insert(1, one_0);
        t2.insert(2, two_0);
        assert_eq!(t1, t2);
        assert_eq!(3, t1.len());
        assert_eq!(3, t2.len());
        assert_eq!(true, t1.contains_key(&0));
        assert_eq!(true, t1.contains_key(&1));
        assert_eq!(true, t1.contains_key(&2));
        assert_eq!(true, t2.contains_key(&0));
        assert_eq!(true, t2.contains_key(&1));
        assert_eq!(true, t2.contains_key(&2));

        t2.clear();
        let zero_1 = "zero";
        let one_1 = "one";
        let two_1 = "two";
        t2.insert(0, zero_1);
        t2.insert(1, one_1);
        t2.insert(2, two_1);
        assert_eq!(t1, t2);
    }

    #[test]
    fn contains_many() {
        let forty_two = "forty two".to_string();
        let mut tree = CachedTree::new();
        let mut res = tree.insert(42, forty_two);
        assert_eq!(None, res);
        assert_eq!(1, tree.len());

        let zero = "zero".to_string();
        let hundo = "hundo".to_string();
        res = tree.insert(0, zero);
        assert_eq!(None, res);
        assert_eq!(2, tree.len());
        res = tree.insert(100, hundo);
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
        let mut tree = CachedTree::new();
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
    fn index_passes() {
        let mut tree = CachedTree::new();
        let forty_two_str = "forty two";
        let forty_two = forty_two_str.to_string();
        tree.insert(forty_two.clone(), forty_two.clone());
        assert_eq!(forty_two, tree[forty_two_str]);
        assert_eq!(forty_two, tree[&forty_two]);
    }

    #[test]
    #[should_panic]
    fn index_panics() {
        let tree: CachedTree<usize, (), Noop<usize, ()>> = CachedTree::new();
        assert_eq!((), tree[&42]);
    }

    #[test]
    fn insert_multiple_values() {
        let data: Vec<(usize, String)> = (0..100).map(|i| (i, format!("{i}"))).collect();
        let mut tree = CachedTree::new();
        for (k, v) in data.iter() {
            tree.insert(*k, v.to_string());
        }

        assert_eq!(data.len(), tree.len());
        for (k, v) in data.iter() {
            assert_eq!(true, tree.contains_key(k));
            assert_eq!(Some((k, v)), tree.get_key_value(k));
        }
    }

    #[test]
    fn insert_same_key() {
        let mut tree = CachedTree::new();
        let forty_two = "forty two".to_string();
        let mut res = tree.insert(42, forty_two.clone());
        assert_eq!(None, res);
        assert_eq!(1, tree.len());
        res = tree.insert(42, "42".to_string());
        assert_eq!(Some(forty_two), res);
        assert_eq!(1, tree.len());
    }

    #[test]
    fn odd_even() {
        let mut tree = CachedTree::new();
        for i in 0..10 {
            tree.insert(i, i);
        }
        for i in (0..10).filter(|i| i % 2 == 0) {
            tree.remove(&i);
        }
        assert_eq!(5, tree.len());
        assert_eq!(vec![1, 3, 5, 7, 9], tree.into_keys().collect::<Vec<_>>());
    }

    #[test]
    fn partial_ord() {
        let mut t1 = CachedTree::new();
        let mut t2 = CachedTree::new();
        let one = "one";
        let two = "two";
        let three = "three";

        assert!(t1 <= t2);
        assert!(t1 >= t2);
        assert!(t1 == t2);

        t1.insert(1, one);
        t2.insert(1, one);
        assert!(t1 <= t2);
        assert!(t1 >= t2);
        assert!(t1 == t2);

        t2.insert(2, two);
        assert!(t1 <= t2);
        assert!(t1 < t2);

        t1.insert(3, three);
        assert!(t1 >= t2);
        assert!(t1 > t2);
    }

    #[test]
    fn pop_first() {
        let mut tree = CachedTree::new();

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
        let mut tree = CachedTree::new();

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
        let mut tree = CachedTree::new();

        let mut res = tree.remove(&42);
        assert_eq!(None, res);

        let forty_two = "forty two".to_string();
        tree.insert(42, forty_two.clone());
        res = tree.remove(&42);
        assert_eq!(Some((42, forty_two.clone())), res);
        assert_eq!(0, tree.len());
        assert_eq!(false, tree.contains_key(&42));

        let zero = "zero".to_string();
        let hundo = "hundo".to_string();
        tree.insert(42, forty_two.clone());
        tree.insert(0, zero.clone());
        tree.insert(100, hundo.clone());

        res = tree.remove(&42);
        assert_eq!(Some((42, forty_two.clone())), res);
        assert_eq!(2, tree.len());
        assert_eq!(true, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(true, tree.contains_key(&100));

        res = tree.remove(&0);
        assert_eq!(Some((0, zero.clone())), res);
        assert_eq!(1, tree.len());
        assert_eq!(false, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(true, tree.contains_key(&100));

        res = tree.remove(&100);
        assert_eq!(Some((100, hundo.clone())), res);
        assert_eq!(0, tree.len());
        assert_eq!(false, tree.contains_key(&0));
        assert_eq!(false, tree.contains_key(&42));
        assert_eq!(false, tree.contains_key(&100));
    }

    #[quickcheck]
    fn insertion_order_is_irrelevant(xs: Vec<(isize, ())>) -> bool {
        let t1 = CachedTree::<isize, (), Noop<isize, ()>>::from_iter(xs.clone().into_iter());
        let t2 = CachedTree::<isize, (), Noop<isize, ()>>::from_iter(xs.into_iter().rev());
        t1 == t2
    }

    const TEST_SEED: u64 = 42;

    fn rand_slice<I, T>(items: I, ratio: f64) -> Vec<T>
    where
        I: IntoIterator<Item = T> + ExactSizeIterator,
    {
        assert!(ratio > 0.0 && ratio <= 1.0);
        let mut rng = ChaCha8Rng::seed_from_u64(TEST_SEED);
        let len = items.len() as f64;
        let mut selected = items.into_iter().collect::<Vec<_>>();
        selected.shuffle(&mut rng);
        selected.truncate((len * ratio).round().clamp(0.0, usize::MAX as f64) as usize);
        selected
    }

    #[quickcheck]
    fn remove_arbitrary(xs: Vec<(u8, ())>) -> bool {
        let remove = rand_slice(xs.iter().map(|(k, _)| *k), 0.5);
        let mut tree = CachedTree::<u8, (), Noop<u8, ()>>::from_iter(xs.into_iter());
        for k in &remove {
            tree.remove(k);
        }
        for k in remove {
            assert_eq!(false, tree.contains_key(&k));
        }
        true
    }
}
