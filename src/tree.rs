use std::{
    borrow::Borrow,
    cmp::Ordering::{self, *},
    mem,
    ops::Index,
};

use crate::{ComingFrom, Node, NodePtr, NodePtrExt, Noop, Root, Tree, TreeCallbacks};

impl<K, V> Tree<K, V, Noop<K, V>> {
    pub fn new() -> Self {
        Tree {
            len: 0,
            root: Root::new(Noop::new()),
        }
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V> + Default> Default for Tree<K, V, C> {
    fn default() -> Self {
        Self::with_callbacks(C::default())
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> Tree<K, V, C> {
    pub fn with_callbacks(augmented: C) -> Self {
        Tree {
            len: 0,
            root: Root::new(augmented),
        }
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V> + Default> Tree<K, V, C> {
    /// Removes all key-value pairs from the tree, leaving it empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(1, "one");
    /// tree.insert(2, "two");
    /// assert_eq!(tree.len(), 2);
    ///
    /// tree.clear();
    /// assert_eq!(tree.len(), 0);
    /// assert!(tree.is_empty());
    /// ```
    pub fn clear(&mut self) {
        drop(Tree {
            len: mem::replace(&mut self.len, 0),
            root: Root {
                callbacks: mem::take(&mut self.root.callbacks),
                node: mem::take(&mut self.root.node),
            },
        });
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> Tree<K, V, C> {
    /// Inserts a key-value pair into the tree.
    ///
    /// If the tree did not have this key present, `None` is returned.
    ///
    /// If the tree did have this key present, the value is updated, and the old
    /// value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// assert_eq!(tree.insert(37, "a"), None);
    /// assert_eq!(tree.is_empty(), false);
    ///
    /// tree.insert(37, "b");
    /// assert_eq!(tree.insert(37, "c"), Some("b"));
    /// assert_eq!(tree[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        match self.root.node {
            None => {
                // SAFETY: root doesn't exist, so we create a new one.
                self.root.node = unsafe { Node::<K, V>::leak(key, value) };
                self.len += 1;
                None
            }
            Some(_) => {
                // [1] replace an existing value or ([2] prepare for linking and [3] link).
                let mut current_node = self.root.node.ptr();
                let mut parent = current_node;
                let mut direction = ComingFrom::Left; // We don't really care, but rust does.
                while !current_node.is_null() {
                    parent = current_node; // [4] parent is never null by construction.
                    #[allow(unused_variables)]
                    let parent = parent; // [4] by sealing, parent is never null hereafter.

                    // SAFETY: guaranteed not null by the while guard.
                    let current_ref = unsafe { current_node.as_mut().unwrap() };
                    match key.cmp(&current_ref.key) {
                        Equal => {
                            // [1] replace an existing value.
                            return Some(std::mem::replace(&mut current_ref.value, value));
                        }
                        Greater => {
                            // [2] prepare for linking on the right of parent.
                            direction = ComingFrom::Right;
                            current_node = current_ref.right.ptr();
                        }
                        Less => {
                            // [2] prepare for linking on the left of parent.
                            direction = ComingFrom::Left;
                            current_node = current_ref.left.ptr();
                        }
                    };
                }
                #[allow(unused_variables)]
                let current_node = current_node;
                let direction = direction;
                let parent = parent; // [4] by sealing, parent is never null hereafter.

                // [3] link.

                // SAFETY: we're owning (k,v)
                let mut node = unsafe { Node::<K, V>::leak(key, value) };
                // SAFETY: [4] parent is never null by construction.
                unsafe { node.link(parent, direction) };
                // SAFETY: node is definitely non null at this stage.
                self.root.insert(unsafe { node.unwrap_unchecked() });
                self.len += 1;
                None
            }
        }
    }

    /// Removes and returns the element with the smallest key from the tree.
    ///
    /// # Returns
    ///
    /// `None` if the tree is empty, else `Some((key, value))`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(3, "three");
    /// tree.insert(1, "one");
    /// tree.insert(2, "two");
    ///
    /// assert_eq!(tree.pop_first(), Some((1, "one")));
    /// assert_eq!(tree.pop_first(), Some((2, "two")));
    /// assert_eq!(tree.pop_first(), Some((3, "three")));
    /// assert_eq!(tree.pop_first(), None);
    /// ```
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        let node = self.root.first()?.as_ptr();
        // SAFETY: by if guard, via op ?, node is not null.
        Some(unsafe { self.pop_node(node) })
    }

    /// Removes and returns the element with the largest key from the tree.
    ///
    /// # Returns
    ///
    /// `None` if the tree is empty, else `Some((key, value))`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(3, "three");
    /// tree.insert(1, "one");
    /// tree.insert(2, "two");
    ///
    /// assert_eq!(tree.pop_last(), Some((3, "three")));
    /// assert_eq!(tree.pop_last(), Some((2, "two")));
    /// assert_eq!(tree.pop_last(), Some((1, "one")));
    /// assert_eq!(tree.pop_last(), None);
    /// ```
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        let node = self.root.last()?.as_ptr();
        // SAFETY: by if guard, via op ?, node is not null.
        Some(unsafe { self.pop_node(node) })
    }

    /// Removes a node from the tree and returns its key-value pair.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `node` is a valid, non-null pointer to a node that
    /// belongs to this tree.
    ///
    /// This is an internal method used by other removal operations.
    pub(crate) unsafe fn pop_node(&mut self, node: *mut Node<K, V>) -> (K, V) {
        // SAFETY: pop_node delegates the safety to the caller; he needs to guarantee a non null ptr.
        let mut node = unsafe { Node::<K, V>::unleak(node) };
        self.root.erase(node.as_mut());
        self.len -= 1;
        (node.key, node.value)
    }

    /// Removes the entry with the given key from the tree and returns the stored
    /// key-value pair.
    ///
    /// # Returns
    ///
    /// `Some((key, value))` if the key is in the tree, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(1, "a");
    ///
    /// assert_eq!(tree.remove(&1), Some((1, "a")));
    /// assert_eq!(tree.remove(&1), None);
    /// assert_eq!(tree.len(), 0);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let node = self.find_node(key)?.as_ptr();
        // SAFETY: by if guard, via op ?, node is not null.
        Some(unsafe { self.pop_node(node) })
    }
}

impl<K, V, C> Tree<K, V, C> {
    /// Returns `true` if the key is in the tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(1, "a");
    /// assert_eq!(tree.contains_key(&1), true);
    /// assert_eq!(tree.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.find_node(key).is_some()
    }

    /// Returns a reference to a node containing the given key in the tree.
    ///
    /// # Returns
    ///
    /// `Some(node)` if the key is in the tree, else `None`.
    fn find_node<Q>(&self, key: &Q) -> NodePtr<K, V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let mut node = self.root.node;
        while let Some(candidate) = node {
            // SAFETY: by while guard, candidate is valid.
            let candidate = unsafe { candidate.as_ref() };
            match key.cmp(candidate.key.borrow()) {
                Equal => break,
                Greater => node = candidate.right,
                Less => node = candidate.left,
            }
        }
        node
    }

    /// Finds the node and the direction from which it was reached.
    ///
    /// # Returns
    ///
    /// A tuple containing the node pointer and an optional `ComingFrom` enum indicating
    /// the direction from which the node was reached.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::{ComingFrom::{Left, Right}, Tree};
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(1, "one");
    /// tree.insert(2, "two");
    /// tree.insert(3, "three");
    ///
    /// let (node, direction) = tree.find_node_and_branch(&2);
    ///
    /// assert!(node.is_some());
    /// assert_eq!(direction, None);
    ///
    /// let (node, direction) = tree.find_node_and_branch(&1);
    /// assert!(node.is_some());
    /// assert_eq!(direction, Some(Left));
    ///
    /// let (node, direction) = tree.find_node_and_branch(&3);
    /// assert!(node.is_some());
    /// assert_eq!(direction, Some(Right));
    ///
    /// let (node, direction) = tree.find_node_and_branch(&42);
    /// assert!(node.is_none());
    /// assert_eq!(direction, Some(Right));
    /// ```
    #[allow(dead_code)]
    pub fn find_node_and_branch<Q>(&self, key: &Q) -> (NodePtr<K, V>, Option<ComingFrom>)
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let mut direction = None;
        let mut node = self.root.node;
        while let Some(candidate) = node {
            // SAFETY: by while guard, candidate is valid.
            let candidate = unsafe { candidate.as_ref() };
            match key.cmp(candidate.key.borrow()) {
                Equal => break,
                Greater => {
                    direction = Some(ComingFrom::Right);
                    node = candidate.right;
                }
                Less => {
                    direction = Some(ComingFrom::Left);
                    node = candidate.left;
                }
            }
        }
        (node, direction)
    }

    /// Returns a reference to the value with the smallest key in the tree.
    ///
    /// # Returns
    ///
    /// `None` if the tree is empty, else `Some(&value)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// assert_eq!(tree.first(), None);
    ///
    /// tree.insert(3, "three");
    /// tree.insert(2, "two");
    /// tree.insert(1, "one");
    ///
    /// assert_eq!(tree.first(), Some(&"one"));
    /// ```
    pub fn first(&self) -> Option<&V> {
        // SAFETY: by construction, n is valid.
        self.root.first().map(|e| &unsafe { e.as_ref() }.value)
    }

    /// Returns the key-value pair with the smallest key in the tree.
    ///
    /// # Returns
    ///
    /// `None` if the tree is empty, else `Some((&key, &value))`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// assert_eq!(tree.first_key_value(), None);
    ///
    /// tree.insert(3, "three");
    /// tree.insert(2, "two");
    /// tree.insert(1, "one");
    ///
    /// assert_eq!(tree.first_key_value(), Some((&1, &"one")));
    /// ```
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        self.root.first().map(|n| {
            // SAFETY: by if guard, via map, n is valid.
            let n = unsafe { n.as_ref() };
            (&n.key, &n.value)
        })
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Returns
    ///
    /// `Some(&value)` if the key is in the tree, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(1, "a");
    /// assert_eq!(tree.get(&1), Some(&"a"));
    /// assert_eq!(tree.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        // SAFETY: by if guard, via map, n is valid.
        self.find_node(key).map(|n| &unsafe { n.as_ref() }.value)
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// # Returns
    ///
    /// `Some((&key, &value))` if the key is in the tree, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(1, "a");
    /// assert_eq!(tree.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(tree.get_key_value(&2), None);
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.find_node(key).map(|n| {
            // SAFETY: by if guard, via map, n is valid.
            let n = unsafe { n.as_ref() };
            (&n.key, &n.value)
        })
    }

    /// Returns `true` if the tree contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// assert!(tree.is_empty());
    ///
    /// tree.insert(1, "one");
    /// assert!(!tree.is_empty());
    ///
    /// tree.remove(&1);
    /// assert!(tree.is_empty());
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns a reference to the value with the largest key in the tree.
    ///
    /// # Returns
    ///
    /// `None` if the tree is empty, else `Some(&value)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// assert_eq!(tree.last(), None);
    ///
    /// tree.insert(2, "two");
    /// tree.insert(3, "three");
    /// tree.insert(1, "one");
    ///
    /// assert_eq!(tree.last(), Some(&"three"));
    /// ```
    pub fn last(&self) -> Option<&V> {
        // SAFETY: by if guard, via map, n is valid.
        self.root.last().map(|n| &unsafe { n.as_ref() }.value)
    }

    /// Returns the key-value pair with the largest key in the tree.
    ///
    /// # Returns
    ///
    /// `None` if the tree is empty, else `Some((&key, &value))`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// assert_eq!(tree.last_key_value(), None);
    ///
    /// tree.insert(1, "one");
    /// tree.insert(2, "two");
    /// tree.insert(3, "three");
    ///
    /// assert_eq!(tree.last_key_value(), Some((&3, &"three")));
    /// ```
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        self.root.last().map(|n| {
            // SAFETY: by if guard, via map, n is valid.
            let n = unsafe { n.as_ref() };
            (&n.key, &n.value)
        })
    }

    /// Returns the number of elements in the tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use rougenoir::Tree;
    ///
    /// let mut tree = Tree::new();
    /// assert_eq!(tree.len(), 0);
    ///
    /// tree.insert(1, "a");
    /// assert_eq!(tree.len(), 1);
    ///
    /// tree.insert(2, "b");
    /// assert_eq!(tree.len(), 2);
    ///
    /// tree.remove(&1);
    /// assert_eq!(tree.len(), 1);
    /// ```
    pub const fn len(&self) -> usize {
        self.len
    }
}

impl<K, Q: ?Sized, V, C: TreeCallbacks<Key = K, Value = V>> Index<&Q> for Tree<K, V, C>
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

impl<K, V, C> Drop for Tree<K, V, C> {
    fn drop(&mut self) {
        // SAFETY: we're literally in drop.
        unsafe {
            Root::dealloc(&mut self.root, self.len);
        }
    }
}

#[cfg(debug_assertions)]
impl<K, V, C> Tree<K, V, C>
where
    K: std::fmt::Debug,
{
    #[allow(dead_code)]
    fn validate(&self) -> bool {
        self.root.validate()
    }
}

impl<K, V, C> std::fmt::Debug for Tree<K, V, C>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
    C: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: PartialEq, V: PartialEq, C: PartialEq> PartialEq for Tree<K, V, C> {
    fn eq(&self, other: &Tree<K, V, C>) -> bool {
        self.len() == other.len()
            && self.root.callbacks == other.root.callbacks
            && self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl<K, V, C> Clone for Tree<K, V, C>
where
    K: Clone + Ord,
    V: Clone,
    C: Clone + TreeCallbacks<Key = K, Value = V>,
{
    fn clone(&self) -> Self {
        if self.is_empty() {
            Tree {
                len: 0,
                root: self.root.clone(),
            }
        } else {
            let mut tree = Tree {
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

impl<K: PartialOrd, V: PartialOrd, C: PartialOrd> PartialOrd for Tree<K, V, C> {
    #[inline]
    fn partial_cmp(&self, other: &Tree<K, V, C>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K: Eq, V: Eq, C: Eq> Eq for Tree<K, V, C> {}

impl<K: Ord, V: Ord, C: Ord> Ord for Tree<K, V, C> {
    #[inline]
    fn cmp(&self, other: &Tree<K, V, C>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

unsafe impl<K, V, C> Send for Tree<K, V, C>
where
    K: Send,
    V: Send,
    C: Send,
{
}

unsafe impl<K, V, C> Sync for Tree<K, V, C>
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
        let mut tree = Tree::new();
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
        let mut t1 = Tree::new();
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
        let mut t1 = Tree::new();
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
        let mut t1 = Tree::new();
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
        let mut tree = Tree::new();
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
        let mut tree = Tree::new();
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
        let tree: Tree<usize, (), Noop<usize, ()>> = Tree::new();
        assert_eq!((), tree[&42]);
    }

    #[test]
    fn insert_multiple_values() {
        let data: Vec<(usize, String)> = (0..100).map(|i| (i, format!("{i}"))).collect();
        let mut tree = Tree::new();
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
        let mut tree = Tree::new();
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
        let mut tree = Tree::new();
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
        let mut t1 = Tree::new();
        let mut t2 = Tree::new();
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
        let mut tree = Tree::new();

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
        let mut tree = Tree::new();

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
        let mut tree = Tree::new();

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
        let t1 = Tree::<isize, (), Noop<isize, ()>>::from_iter(xs.clone().into_iter());
        let t2 = Tree::<isize, (), Noop<isize, ()>>::from_iter(xs.into_iter().rev());
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
        let mut tree = Tree::<u8, (), Noop<u8, ()>>::from_iter(xs.into_iter());
        for k in &remove {
            tree.remove(k);
        }
        for k in remove {
            assert_eq!(false, tree.contains_key(&k));
        }
        true
    }
}
