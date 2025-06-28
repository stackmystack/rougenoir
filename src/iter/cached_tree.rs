use std::{iter::FusedIterator, marker::PhantomData, ptr};

use crate::{CachedTree, Node, NodePtr, TreeCallbacks};

impl<K, V, C> CachedTree<K, V, C> {
    /// Gets an iterator over the keys of the map, in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::CachedTree;
    ///
    /// let mut a = CachedTree::new();
    /// a.insert(2, "b");
    /// a.insert(1, "a");
    ///
    /// let keys: Vec<_> = a.keys().cloned().collect();
    /// assert_eq!(keys, [1, 2]);
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            first: self.root.first(),
            last: self.root.last(),
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
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
    /// use rougenoir::CachedTree;
    ///
    /// let mut a = CachedTree::new();
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
    /// use rougenoir::CachedTree;
    ///
    /// let mut a = CachedTree::new();
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

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> CachedTree<K, V, C> {
    /// Creates an iterator that visits all elements (key-value pairs) in
    /// ascending key order and uses a closure to determine if an element should
    /// be removed. If the closure returns `true`, the element is removed from
    /// the map and yielded. If the closure returns `false`, or panics, the
    /// element remains in the map and will not be yielded.
    ///
    /// The iterator also lets you mutate the value of each element in the
    /// closure, regardless of whether you choose to keep or remove it.
    ///
    /// If the returned `ExtractIf` is not exhausted, e.g. because it is dropped without iterating
    /// or the iteration short-circuits, then the remaining elements will be retained.
    /// Use [`retain`] with a negated predicate if you do not need the returned iterator.
    ///
    /// [`retain`]: CachedTree::retain
    ///
    /// # Examples
    ///
    /// Splitting a map into even and odd keys, reusing the original map:
    ///
    /// ```
    /// use rougenoir::{CachedTree, Noop};
    ///
    /// let mut map: CachedTree<i32, i32, Noop<i32, i32>> = (0..8).map(|x| (x, x)).collect();
    /// let evens: CachedTree<i32, i32, Noop<i32, i32>> = map.extract_if(|k, _v| k % 2 == 0).collect();
    /// let odds = map;
    /// assert_eq!(evens.keys().copied().collect::<Vec<_>>(), [0, 2, 4, 6]);
    /// assert_eq!(odds.keys().copied().collect::<Vec<_>>(), [1, 3, 5, 7]);
    /// ```
    pub fn extract_if<F>(&mut self, pred: F) -> ExtractIf<'_, K, V, C, F>
    where
        K: Ord,
        F: FnMut(&K, &V) -> bool,
    {
        ExtractIf {
            pred,
            next: self.root.first().map_or(ptr::null(), |n| n.as_ptr()),
            tree: self,
        }
    }

    /// Creates a consuming iterator visiting all the keys, in sorted order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::CachedTree;
    ///
    /// let mut a = CachedTree::new();
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
    /// use rougenoir::CachedTree;
    ///
    /// let mut a = CachedTree::new();
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

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`.
    /// The elements are visited in ascending key order.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::{CachedTree, Noop};
    ///
    /// let mut map: CachedTree<i32, i32, Noop<i32, i32>> = (0..8).map(|x| (x, x*10)).collect();
    /// // Keep only the elements with even-numbered keys.
    /// map.retain(|&k, _| k % 2 == 0);
    /// assert!(map.into_iter().eq(vec![(0, 0), (2, 20), (4, 40), (6, 60)]));
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        K: Ord,
        F: FnMut(&K, &V) -> bool,
    {
        self.extract_if(|k, v| !f(k, v)).for_each(drop);
    }
}

pub struct IntoIter<K, V, C>(CachedTree<K, V, C>);

impl<K, V, C> IntoIter<K, V, C> {
    /// Returns an iterator of references over the remaining items.
    #[inline]
    #[allow(dead_code)]
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

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> IntoIterator for CachedTree<K, V, C> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, C>;

    /// Gets an owning iterator over the entries of the map, sorted by key.
    fn into_iter(self) -> IntoIter<K, V, C> {
        IntoIter(self)
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> Iterator for IntoIter<K, V, C> {
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

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> DoubleEndedIterator for IntoIter<K, V, C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_last()
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> ExactSizeIterator for IntoIter<K, V, C> {
    fn len(&self) -> usize {
        self.0.len
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> FusedIterator for IntoIter<K, V, C> {}

pub struct Iter<'a, K, V> {
    first: NodePtr<K, V>,
    last: NodePtr<K, V>,
    len: usize,
    _phantom_k: PhantomData<&'a K>,
    _phantom_v: PhantomData<&'a V>,
}

impl<'a, K, V, C: TreeCallbacks<Key = K, Value = V>> IntoIterator for &'a CachedTree<K, V, C> {
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
            first: self.first,
            last: self.last,
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

impl<'a, K, V, C> IntoIterator for &'a mut CachedTree<K, V, C> {
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
            first: self.first,
            last: self.last,
            len: self.len,
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }
}

impl<K: Ord, V, C: TreeCallbacks<Key = K, Value = V>> Extend<(K, V)> for CachedTree<K, V, C> {
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(move |(k, v)| {
            self.insert(k, v);
        });
    }
}

impl<'a, K: Ord + Copy, V: Copy, C: TreeCallbacks<Key = K, Value = V>> Extend<(&'a K, &'a V)>
    for CachedTree<K, V, C>
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
/// [`keys`]: CachedTree::keys
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

/// An iterator over the values of a `Tree`.
///
/// This `struct` is created by the [`values`] method on [`Tree`]. See its
/// documentation for more.
///
/// [`values`]: CachedTree::values
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}

/// A mutable iterator over the values of a `Tree`.
///
/// This `struct` is created by the [`values_mut`] method on [`Tree`]. See its
/// documentation for more.
///
/// [`values_mut`]: CachedTree::values_mut
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ValuesMut<'a, K, V> {
    inner: IterMut<'a, K, V>,
}

/// An owning iterator over the keys of a `Tree`.
///
/// This `struct` is created by the [`into_keys`] method on [`Tree`].
/// See its documentation for more.
///
/// [`into_keys`]: CachedTree::into_keys
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IntoKeys<K, V, C: TreeCallbacks<Key = K, Value = V>> {
    inner: IntoIter<K, V, C>,
}

/// An owning iterator over the values of a `Tree`.
///
/// This `struct` is created by the [`into_values`] method on [`Tree`].
/// See its documentation for more.
///
/// [`into_values`]: CachedTree::into_keys
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IntoValues<K, V, C: TreeCallbacks<Key = K, Value = V>> {
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

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> Iterator for IntoKeys<K, V, C> {
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

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> DoubleEndedIterator for IntoKeys<K, V, C> {
    fn next_back(&mut self) -> Option<K> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> ExactSizeIterator for IntoKeys<K, V, C> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> FusedIterator for IntoKeys<K, V, C> {}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> Iterator for IntoValues<K, V, C> {
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

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> DoubleEndedIterator for IntoValues<K, V, C> {
    fn next_back(&mut self) -> Option<V> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> ExactSizeIterator for IntoValues<K, V, C> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> FusedIterator for IntoValues<K, V, C> {}

impl<K: Ord, V, C: TreeCallbacks<Key = K, Value = V> + Default> FromIterator<(K, V)>
    for CachedTree<K, V, C>
{
    /// Constructs a `CachedTree<K, V>` from an iterator of key-value pairs.
    ///
    /// If the iterator produces any pairs with equal keys,
    /// all but one of the corresponding values will be dropped.
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> CachedTree<K, V, C> {
        let inputs: Vec<_> = iter.into_iter().collect();
        if inputs.is_empty() {
            return CachedTree::with_callbacks(Default::default());
        }
        let mut res = CachedTree::with_callbacks(Default::default());
        for (k, v) in inputs {
            res.insert(k, v);
        }
        res
    }
}

pub struct ExtractIf<'a, K, V, C, F>
where
    C: TreeCallbacks<Key = K, Value = V>,
    F: 'a + FnMut(&K, &V) -> bool,
{
    pred: F,
    tree: &'a mut CachedTree<K, V, C>,
    next: *const Node<K, V>,
}

impl<'a, K, V, C, F> Iterator for ExtractIf<'a, K, V, C, F>
where
    K: Ord,
    C: TreeCallbacks<Key = K, Value = V>,
    F: 'a + FnMut(&K, &V) -> bool,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        // [1] look for the first match: [2] bump self.next until [3] the key
        // matches and finally [4] pop the node.
        let mut victim = self.next;
        while !victim.is_null() {
            // Call unsafe once to get the next node for the [2] bump, and the
            // references for [3] key matching.
            let (next, key, value) = {
                // SAFETY: guaranteed not null by the while guard.
                let victim_ref = unsafe { victim.as_ref() }.unwrap();
                (
                    victim_ref.next().map_or(ptr::null(), |n| n.as_ptr()),
                    &victim_ref.key,
                    &victim_ref.value,
                )
            };

            // [2] bump self.next
            self.next = next;
            if (self.pred)(key, value) {
                // [3] key matches. victim points to the correct location.
                break;
            }
            // ![3] key didn't match, it must be the next, right?
            victim = self.next;
        }

        if victim.is_null() {
            // ![4] nothing found.
            None
        } else {
            // [4] pop the node.
            // SAFETY: guaranteed not null by the if guard, which follows from
            // the [1..3] construction, and nobody is mutating it after this
            // point.
            Some(unsafe { self.tree.pop_node(victim.cast_mut()) })
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{CachedTree, Noop};
    use pretty_assertions::assert_eq;

    #[test]
    fn extend() {
        let mut tree = CachedTree::new();
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
    fn extract_if() {
        let mut map: CachedTree<i32, i32, Noop<i32, i32>> = (0..8).map(|x| (x, x)).collect();
        let evens: CachedTree<i32, i32, Noop<i32, i32>> =
            map.extract_if(|k, _v| k % 2 == 0).collect();
        let odds = map;
        assert_eq!(evens.keys().copied().collect::<Vec<_>>(), [0, 2, 4, 6]);
        assert_eq!(odds.keys().copied().collect::<Vec<_>>(), [1, 3, 5, 7]);
    }

    #[test]
    fn for_loop() {
        let mut tree = CachedTree::new();
        let zero = "zero".to_string();
        let forty_two = "forty_two".to_string();
        let hundo = "hundo".to_string();

        tree.insert(100, hundo.clone());
        tree.insert(0, zero.clone());
        tree.insert(42, forty_two.clone());

        for (k, _v) in &tree {
            // This is a test for compilation.
            let _ = k;
        }

        for (_k, v) in tree {
            // This is a test for compilation.
            let _ = v;
        }
    }

    #[test]
    fn into_iter_empty() {
        let tree = CachedTree::<usize, (), Noop<usize, ()>>::new();
        let vec = tree.into_iter().collect::<Vec<_>>();
        assert_eq!(0, vec.len());
    }

    #[test]
    fn into_iter() {
        let mut tree = CachedTree::new();
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
        let tree = CachedTree::<usize, (), Noop<usize, ()>>::new();
        assert_eq!(None, tree.iter().next());
    }

    #[test]
    fn iter() {
        let mut tree = CachedTree::new();
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

        let mut tree = CachedTree::new();
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
        let mut tree = CachedTree::new();
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
        let mut tree = CachedTree::<usize, (), Noop<usize, ()>>::new();
        assert_eq!(None, tree.iter_mut().next());
    }

    #[test]
    fn iter_mut() {
        let mut tree = CachedTree::new();
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

    #[test]
    fn retain() {
        let mut map: CachedTree<i32, i32, Noop<i32, i32>> = (0..8).map(|x| (x, x * 10)).collect();
        // Keep only the elements with even-numbered keys.
        map.retain(|&k, _| k % 2 == 0);
        assert!(map.into_iter().eq(vec![(0, 0), (2, 20), (4, 40), (6, 60)]));
    }
}
