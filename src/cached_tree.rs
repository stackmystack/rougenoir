use std::{cmp::Ordering::*, mem};

use crate::{CachedTree, Callbacks, NodePtrExt, Root, alloc_node};

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
}

// impl<K: PartialEq + Ord, V, A: Augmenter<Key = K, Value = V>> RootOps for RootCached<K, V, A> {
//     type Key = K;
//     type Value = V;

//     fn root(&self) -> NodePtr<Self::Key, Self::Value> {
//         self.root.root
//     }

//     fn set_root(&mut self, new: NodePtr<Self::Key, Self::Value>) {
//         self.root.root = new;
//     }

//     fn first(&self) -> NodePtr<Self::Key, Self::Value> {
//         self.leftmost
//     }

//     fn last(&self) -> NodePtr<Self::Key, Self::Value> {
//         self.root.last()
//     }

//     fn first_postorder(&self) -> NodePtr<Self::Key, Self::Value> {
//         self.root.first_postorder()
//     }

//     fn replace_node(
//         &mut self,
//         victim: NonNull<Node<Self::Key, Self::Value>>,
//         new: NonNull<Node<Self::Key, Self::Value>>,
//     ) {
//         if self.leftmost == victim.into() {
//             self.leftmost = new.into();
//         }
//         self.root.replace_node(victim, new);
//     }

//     fn insert(&mut self, node: NonNull<Node<Self::Key, Self::Value>>) {
//         self.leftmost = node.into();
//         self.root.insert(node);
//     }

//     fn erase(&mut self, node: NonNull<Node<Self::Key, Self::Value>>) {
//         if self.leftmost == node.into() {
//             self.leftmost = unsafe { node.as_ref() }.next();
//         }
//         self.root.erase(node);
//     }
// }
