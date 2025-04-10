use std::{borrow::Borrow, cmp::Ordering::*, mem, ptr::NonNull};

use crate::{CachedTree, Callbacks, Node, NodePtr, NodePtrExt, Root, alloc_node};

impl<K, V, C: Callbacks<Key = K, Value = V> + Default> CachedTree<K, V, C> {
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

impl<K, V, C: Callbacks<Key = K, Value = V>> CachedTree<K, V, C> {
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
                let mut leftmost = true;
                let mut current_node = &mut self.root.node;
                let mut parent = current_node.unwrap();
                while let Some(mut current_ptr) = *current_node {
                    parent = current_ptr;
                    let current = unsafe { current_ptr.as_mut() };
                    match key.cmp(&current.key) {
                        Equal => {
                            return Some(std::mem::replace(&mut current.value, value));
                        }
                        Greater => {
                            leftmost = false;
                            current_node = &mut current.right
                        }
                        Less => current_node = &mut current.left,
                    }
                }

                let mut node = unsafe { alloc_node(key, value) };
                node.link(parent, current_node);
                self.root.insert(node.expect("can never be None"));
                self.len += 1;
                if leftmost {
                    self.leftmost = node;
                }
                None
            }
        }
    }

    pub fn pop_first(&mut self) -> Option<(K, V)>
    where
        K: PartialEq,
    {
        Some(self.pop_node(self.root.first()?))
    }

    pub fn pop_last(&mut self) -> Option<(K, V)> {
        Some(self.pop_node(self.root.last()?))
    }

    fn pop_node(&mut self, node: NonNull<Node<K, V>>) -> (K, V) {
        self.root.erase(node);
        if self.leftmost.is_some_and(|l| l == node) {
            self.leftmost = unsafe { node.as_ref() }.next();
        }
        let first_node = unsafe { Box::from_raw(node.as_ptr()) };
        self.len -= 1;
        (first_node.key, first_node.value)
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        Some(self.pop_node(self.find_node(key)?))
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

    // pub fn get<Q>(&self, key: &Q) -> Option<&V>
    // where
    //     K: Borrow<Q> + Ord,
    //     Q: Ord + ?Sized,
    // {
    //     self.find_node(key).map(|n| &unsafe { n.as_ref() }.value)
    // }

    // pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    // where
    //     K: Borrow<Q> + Ord,
    //     Q: Ord,
    // {
    //     self.find_node(key).map(|n| {
    //         let n = unsafe { n.as_ref() };
    //         (&n.key, &n.value)
    //     })
    // }

    // pub fn is_empty(&self) -> bool {
    //     self.len == 0
    // }

    // pub fn last(&self) -> Option<&V> {
    //     self.root.last().map(|n| &unsafe { n.as_ref() }.value)
    // }

    // pub fn last_key_value(&self) -> Option<(&K, &V)> {
    //     self.root.last().map(|n| {
    //         let n = unsafe { n.as_ref() };
    //         (&n.key, &n.value)
    //     })
    // }

    // pub fn len(&self) -> usize {
    //     self.len
    // }

    // TODO
    // fn retain<F>(&mut self, f: F)
    // where
    //     F: FnMut(&Self::Key, &mut Self::Value) -> bool;
}
