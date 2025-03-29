use std::{iter::FusedIterator, marker::PhantomData};

use crate::{Callbacks, NodePtr, Tree};

impl<K, V, C> Tree<K, V, C> {
    /// Gets an iterator over the keys of the map, in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut a = Tree::new();
    /// a.insert(2, "b");
    /// a.insert(1, "a");
    ///
    /// let keys: Vec<_> = a.keys().cloned().collect();
    /// assert_eq!(keys, [1, 2]);
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            first: self.root.first(),
            last: self.root.last(),
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            first: self.root.first(),
            last: self.root.first(),
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }

    /// Gets an iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut a = Tree::new();
    /// a.insert(1, "hello");
    /// a.insert(2, "goodbye");
    ///
    /// let values: Vec<&str> = a.values().cloned().collect();
    /// assert_eq!(values, ["hello", "goodbye"]);
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }

    /// Gets a mutable iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut a = Tree::new();
    /// a.insert(1, String::from("hello"));
    /// a.insert(2, String::from("goodbye"));
    ///
    /// for value in a.values_mut() {
    ///     value.push_str("!");
    /// }
    ///
    /// let values: Vec<String> = a.values().cloned().collect();
    /// assert_eq!(values, [String::from("hello!"),
    ///                     String::from("goodbye!")]);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> Tree<K, V, C> {
    /// Creates a consuming iterator visiting all the keys, in sorted order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut a = Tree::new();
    /// a.insert(2, "b");
    /// a.insert(1, "a");
    ///
    /// let keys: Vec<i32> = a.into_keys().collect();
    /// assert_eq!(keys, [1, 2]);
    /// ```
    #[inline]
    pub fn into_keys(self) -> IntoKeys<K, V, C> {
        IntoKeys {
            inner: self.into_iter(),
        }
    }

    /// Creates a consuming iterator visiting all the values, in order by key.
    /// The map cannot be used after calling this.
    /// The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut a = Tree::new();
    /// a.insert(1, "hello");
    /// a.insert(2, "goodbye");
    ///
    /// let values: Vec<&str> = a.into_values().collect();
    /// assert_eq!(values, ["hello", "goodbye"]);
    /// ```
    #[inline]
    pub fn into_values(self) -> IntoValues<K, V, C> {
        IntoValues {
            inner: self.into_iter(),
        }
    }
}

pub struct IntoIter<K, V, C>(Tree<K, V, C>);

impl<K, V, C> IntoIter<K, V, C> {
    /// Returns an iterator of references over the remaining items.
    #[inline]
    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            first: self.0.root.first(),
            last: self.0.root.last(),
            len: self.0.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }
}

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

    fn next(&mut self) -> Option<(K, V)> {
        self.0.pop_first()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.len, Some(self.0.len))
    }

    fn last(mut self) -> Option<(K, V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(K, V)>
    where
        (K, V): Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<(K, V)>
    where
        (K, V): Ord,
    {
        self.next_back()
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> DoubleEndedIterator for IntoIter<K, V, C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_last()
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> ExactSizeIterator for IntoIter<K, V, C> {
    fn len(&self) -> usize {
        self.0.len
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> FusedIterator for IntoIter<K, V, C> {}

pub struct Iter<'a, K, V> {
    first: NodePtr<K, V>,
    last: NodePtr<K, V>,
    len: usize,
    _phantom_k: PhantomData<&'a K>,
    _phantom_v: PhantomData<&'a V>,
}

impl<'a, K, V, C: Callbacks<Key = K, Value = V>> IntoIterator for &'a Tree<K, V, C> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.first.map(|n| {
            let n = unsafe { n.as_ref() };
            self.len -= 1;
            self.first = n.next();
            (&n.key, &n.value)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn last(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a V)>
    where
        (&'a K, &'a V): Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a V)>
    where
        (&'a K, &'a V): Ord,
    {
        self.next_back()
    }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        self.first.map(|n| {
            let n = unsafe { n.as_ref() };
            self.len -= 1;
            self.last = n.prev();
            (&n.key, &n.value)
        })
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Iter {
            first: self.first.clone(),
            last: self.last.clone(),
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }
}

pub struct IterMut<'a, K, V> {
    first: NodePtr<K, V>,
    last: NodePtr<K, V>,
    len: usize,
    _phantom_k: PhantomData<&'a K>,
    _phantom_v: PhantomData<&'a mut V>,
}

impl<'a, K, V, C> IntoIterator for &'a mut Tree<K, V, C> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.first.map(|mut n| {
            let n = unsafe { n.as_mut() };
            self.len -= 1;
            self.first = n.next();
            (&n.key, &mut n.value)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn last(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a mut V)>
    where
        (&'a K, &'a mut V): Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a mut V)>
    where
        (&'a K, &'a mut V): Ord,
    {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.first.map(|mut n| {
            let n = unsafe { n.as_mut() };
            self.len -= 1;
            self.last = n.prev();
            (&n.key, &mut n.value)
        })
    }
}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<K, V> FusedIterator for IterMut<'_, K, V> {}

impl<K, V> Clone for IterMut<'_, K, V> {
    fn clone(&self) -> Self {
        IterMut {
            first: self.first.clone(),
            last: self.last.clone(),
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }
}

impl<K: Ord, V, C: Callbacks<Key = K, Value = V>> Extend<(K, V)> for Tree<K, V, C> {
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(move |(k, v)| {
            self.insert(k, v);
        });
    }
}

impl<'a, K: Ord + Copy, V: Copy, C: Callbacks<Key = K, Value = V>> Extend<(&'a K, &'a V)>
    for Tree<K, V, C>
{
    fn extend<I: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: I) {
        self.extend(iter.into_iter().map(|(&key, &value)| (key, value)));
    }
}

/// An iterator over the keys of a `Tree`.
///
/// This `struct` is created by the [`keys`] method on [`Tree`]. See its
/// documentation for more.
///
/// [`keys`]: Tree::keys
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

/// An iterator over the values of a `Tree`.
///
/// This `struct` is created by the [`values`] method on [`Tree`]. See its
/// documentation for more.
///
/// [`values`]: Tree::values
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}

/// A mutable iterator over the values of a `Tree`.
///
/// This `struct` is created by the [`values_mut`] method on [`Tree`]. See its
/// documentation for more.
///
/// [`values_mut`]: Tree::values_mut
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ValuesMut<'a, K, V> {
    inner: IterMut<'a, K, V>,
}

/// An owning iterator over the keys of a `Tree`.
///
/// This `struct` is created by the [`into_keys`] method on [`Tree`].
/// See its documentation for more.
///
/// [`into_keys`]: Tree::into_keys
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IntoKeys<K, V, C: Callbacks<Key = K, Value = V>> {
    inner: IntoIter<K, V, C>,
}

/// An owning iterator over the values of a `Tree`.
///
/// This `struct` is created by the [`into_values`] method on [`Tree`].
/// See its documentation for more.
///
/// [`into_values`]: Tree::into_keys
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IntoValues<K, V, C: Callbacks<Key = K, Value = V>> {
    inner: IntoIter<K, V, C>,
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<&'a K> {
        self.next_back()
    }

    fn min(mut self) -> Option<&'a K>
    where
        &'a K: Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<&'a K>
    where
        &'a K: Ord,
    {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a K> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<K, V> ExactSizeIterator for Keys<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for Keys<'_, K, V> {}

impl<K, V> Clone for Keys<'_, K, V> {
    fn clone(&self) -> Self {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<&'a V> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a V> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

impl<K, V> ExactSizeIterator for Values<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for Values<'_, K, V> {}

impl<K, V> Clone for Values<'_, K, V> {
    fn clone(&self) -> Self {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<&'a mut V> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<&'a mut V> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for ValuesMut<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a mut V> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

impl<K, V, C: Callbacks<Key = K, Value = V>> Iterator for IntoKeys<K, V, C> {
    type Item = K;

    fn next(&mut self) -> Option<K> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<K> {
        self.next_back()
    }

    fn min(mut self) -> Option<K>
    where
        K: Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<K>
    where
        K: Ord,
    {
        self.next_back()
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> DoubleEndedIterator for IntoKeys<K, V, C> {
    fn next_back(&mut self) -> Option<K> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> ExactSizeIterator for IntoKeys<K, V, C> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> FusedIterator for IntoKeys<K, V, C> {}

impl<K, V, C: Callbacks<Key = K, Value = V>> Iterator for IntoValues<K, V, C> {
    type Item = V;

    fn next(&mut self) -> Option<V> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<V> {
        self.next_back()
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> DoubleEndedIterator for IntoValues<K, V, C> {
    fn next_back(&mut self) -> Option<V> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> ExactSizeIterator for IntoValues<K, V, C> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> FusedIterator for IntoValues<K, V, C> {}

#[cfg(test)]
mod test {
    use crate::{Noop, Tree};
    use pretty_assertions::assert_eq;

    #[test]
    fn extend() {
        let mut tree = Tree::new();
        let zero = "zero".to_string();
        let one = "one".to_string();
        let forty_two = "forty_two".to_string();
        let hundo = "hundo".to_string();

        tree.insert(100, hundo.clone());
        tree.insert(0, zero.clone());
        tree.insert(42, forty_two.clone());
        tree.extend(vec![(1, one.clone())]);

        assert_eq!(4, tree.len());
        let mut iter = tree.iter();
        assert_eq!(Some((&0, &zero)), iter.next());
        assert_eq!(Some((&1, &one)), iter.next());
        assert_eq!(Some((&42, &forty_two)), iter.next());
        assert_eq!(Some((&100, &hundo)), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn for_loop() {
        let mut tree = Tree::new();
        let zero = "zero".to_string();
        let forty_two = "forty_two".to_string();
        let hundo = "hundo".to_string();

        tree.insert(100, hundo.clone());
        tree.insert(0, zero.clone());
        tree.insert(42, forty_two.clone());

        for (_k, _v) in &tree {
            assert!(true);
        }

        for (_k, _v) in tree {
            assert!(true);
        }
    }

    #[test]
    fn into_iter_empty() {
        let tree = Tree::<usize, (), Noop<usize, ()>>::new();
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
        let tree = Tree::<usize, (), Noop<usize, ()>>::new();
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
        let mut tree = Tree::<usize, (), Noop<usize, ()>>::new();
        assert_eq!(None, tree.iter_mut().next());
    }

    #[test]
    fn iter_mut() {
        let mut tree = Tree::new();
        let mut zero = "zero".to_string();
        let forty_two = "forty_two".to_string();
        let hundo = "hundo".to_string();
        let stomp = "stomp";

        tree.insert(100, hundo.clone());
        tree.insert(0, zero.clone());
        tree.insert(42, forty_two.clone());

        let mut iter = tree.iter_mut();
        let res = iter.next();
        assert_eq!(Some((&0, &mut zero)), res);
        let res = res.unwrap();
        res.1.push_str(stomp);
        assert_eq!(&format!("{zero}{stomp}"), res.1);
    }
}
