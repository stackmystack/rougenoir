use std::{borrow::Borrow, marker::PhantomData, ops::Index};

use crate::{Callbacks, NodePtr, NodePtrExt, Tree};

impl<K, Q: ?Sized, V, C: Callbacks<Key = K, Value = V>> Index<&Q> for Tree<K, V, C>
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

pub struct Iter<'a, K, V, C: Callbacks<Key = K, Value = V>> {
    next: NodePtr<K, V>,
    len: usize,
    _phantom_k: PhantomData<&'a K>,
    _phantom_v: PhantomData<&'a V>,
    _phantom_c: PhantomData<C>,
}

impl<'a, K, V, C: Callbacks<Key = K, Value = V>> Iterator for Iter<'a, K, V, C> {
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

pub struct IterMut<'a, K, V, C: Callbacks<Key = K, Value = V>>(Iter<'a, K, V, C>);

impl<'a, K, V, C: Callbacks<Key = K, Value = V>> Iterator for IterMut<'a, K, V, C> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next.map(|mut n| {
            let n = unsafe { n.as_mut() };
            self.0.len -= 1;
            self.0.next = n.next();
            &mut n.value
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.len, Some(self.0.len))
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V> + Default> Tree<K, V, C> {
    pub fn iter(&self) -> Iter<K, V, C> {
        Iter {
            next: self.root.first(),
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
            _phantom_c: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<K, V, C> {
        IterMut(Iter {
            next: self.root.first(),
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
            _phantom_c: PhantomData,
        })
    }
}

#[cfg(test)]
mod test {
    use crate::Tree;
    use pretty_assertions::assert_eq;

    #[test]
    fn index_passes() {
        let mut tree = Tree::new();
        let forty_two_str = "forty two";
        let forty_two = forty_two_str.to_string();
        tree.insert(forty_two.clone(), forty_two.clone());
        assert_eq!(forty_two, tree[forty_two_str]);
        assert_eq!(forty_two, tree[&forty_two]);
    }

    #[test]
    #[should_panic]
    fn index_panics() {
        let tree: Tree<usize, ()> = Tree::new();
        assert_eq!((), tree[&42]);
    }

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
