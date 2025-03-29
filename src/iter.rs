use std::marker::PhantomData;

use crate::{Callbacks, NodePtr, Tree};

pub struct IntoIter<K, V, C: Callbacks<Key = K, Value = V>>(Tree<K, V, C>);

impl<K, V, C: Callbacks<Key = K, Value = V>> IntoIterator for Tree<K, V, C> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, C>;

    /// Gets an owning iterator over the entries of the map, sorted by key.
    fn into_iter(self) -> IntoIter<K, V, C> {
        IntoIter(self)
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> Iterator for IntoIter<K, V, C> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_first()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.len, Some(self.0.len))
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> DoubleEndedIterator for IntoIter<K, V, C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_last()
    }
}

pub struct Iter<'a, K, V> {
    next: NodePtr<K, V>,
    len: usize,
    _phantom_k: PhantomData<&'a K>,
    _phantom_v: PhantomData<&'a V>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|n| {
            let n = unsafe { n.as_ref() };
            self.len -= 1;
            self.next = n.next();
            (&n.key, &n.value)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

pub struct IterMut<'a, K, V> {
    next: NodePtr<K, V>,
    len: usize,
    _phantom_k: PhantomData<&'a K>,
    _phantom_v: PhantomData<&'a mut V>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|mut n| {
            let n = unsafe { n.as_mut() };
            self.len -= 1;
            self.next = n.next();
            &mut n.value
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> Tree<K, V, C> {
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            next: self.root.first(),
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            next: self.root.first(),
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }
}

/// Iter and IntoIter are covariant.
//
///```
/// use rougenoir::{Noop, Tree, iter::{IntoIter, Iter}};
///
/// fn into_iter_covariant<'a, K, V>(x: IntoIter<&'static K, &'static V, Noop<&'static K, &'static V>>) -> IntoIter<&'a K, &'a V, Noop<&'a K, &'a V>> { x }
/// fn iter_covariant<'i, 'a, K, V>(x: Iter<'i, &'static K, &'static V>) -> Iter<'i, &'a K, &'a V> { x }
/// ```
#[allow(dead_code)]
fn test_covariance() {}

/// IterMut should be invariant like &'a mut T.
///
/// ```compile_fail
/// use rougenoir::{Tree, iter::IterMut};
///
/// fn iter_mut_covariant<'i, 'a, K, V>(x: IterMut<'i, &'static K, &'static V>) -> IterMut<'i, &'a K, &'a V> { x }
/// ```
#[allow(dead_code)]
fn test_invariance() {}

#[cfg(test)]
mod test {
    use crate::Tree;
    use pretty_assertions::assert_eq;

    #[test]
    fn into_iter_empty() {
        let tree = Tree::<usize, ()>::new();
        let vec = tree.into_iter().collect::<Vec<_>>();
        assert_eq!(0, vec.len());
    }

    #[test]
    fn into_iter() {
        let mut tree = Tree::new();
        let zero = "zero".to_string();
        let forty_two = "forty_two".to_string();
        let hundo = "hundo".to_string();

        tree.insert(100, hundo.clone());
        tree.insert(0, zero.clone());
        tree.insert(42, forty_two.clone());

        let vec = tree.into_iter().collect::<Vec<_>>();
        assert_eq!(3, vec.len());
        assert_eq!((0, zero), vec[0]);
        assert_eq!((42, forty_two), vec[1]);
        assert_eq!((100, hundo), vec[2]);
    }

    #[test]
    fn iter_empty() {
        let tree = Tree::<usize, ()>::new();
        assert_eq!(None, tree.iter().next());
    }

    #[test]
    fn iter() {
        let mut tree = Tree::new();
        let zero = "zero".to_string();
        let forty_two = "forty_two".to_string();
        let hundo = "hundo".to_string();

        tree.insert(100, hundo.clone());
        tree.insert(0, zero.clone());
        tree.insert(42, forty_two.clone());

        let mut iter = tree.iter();

        assert_eq!(Some((&0, &zero)), iter.next());
        assert_eq!(Some((&42, &forty_two)), iter.next());
        assert_eq!(Some((&100, &hundo)), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next());

        let mut tree = Tree::new();
        // TODO: when I do (0..128).rev(), i = 1 disappears from the tree
        for i in 0..128 {
            tree.insert(i, ());
        }
        let mut iter = tree.iter();
        for i in 0..128 {
            assert_eq!(Some((&i, &())), iter.next());
        }
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn iter_rev_insert() {
        let mut tree = Tree::new();
        for i in (0..128).rev() {
            tree.insert(i, ());
        }
        let mut iter = tree.iter();
        for i in 0..128 {
            assert_eq!(Some((&i, &())), iter.next());
        }
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn iter_mut_empty() {
        let mut tree = Tree::<usize, ()>::new();
        assert_eq!(None, tree.iter_mut().next());
    }

    #[test]
    fn iter_mut() {
        let mut tree = Tree::new();
        let zero = "zero".to_string();
        let forty_two = "forty_two".to_string();
        let hundo = "hundo".to_string();
        let stomp = "stomp";

        tree.insert(100, hundo.clone());
        tree.insert(0, zero.clone());
        tree.insert(42, forty_two.clone());

        let mut iter = tree.iter_mut();
        let res = iter.next();
        assert_eq!(Some(&zero), res.as_deref());
        let res = res.unwrap();
        res.push_str(stomp);
        assert_eq!(&format!("{zero}{stomp}"), res);
    }
}
