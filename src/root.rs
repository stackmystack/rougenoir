use std::{marker::PhantomData, ptr::NonNull};

use crate::intrusive;

use super::{Node, NodeAdapter, NodePtr, Root, TreeCallbacks};

/// Bridges [`TreeCallbacks`] (which hands out `&mut Node<K, V>`) to
/// [`intrusive::TreeCallbacks`] (which hands out `NonNull<Value>`), so
/// [`Root<K, V, C>`] can delegate its rebalancing to
/// [`crate::intrusive::Root`] instead of keeping its own copy of the
/// algorithm.
struct CallbackBridge<'a, K, V, C>(&'a C, PhantomData<(K, V)>);

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> intrusive::TreeCallbacks
    for CallbackBridge<'_, K, V, C>
{
    type Value = Node<K, V>;

    fn propagate(&self, node: Option<NonNull<Node<K, V>>>, stop: Option<NonNull<Node<K, V>>>) {
        // SAFETY: any Some(_) here points at a live Node<K, V> that nothing
        // else holds a reference to for the duration of this call.
        self.0.propagate(
            node.map(|mut n| unsafe { n.as_mut() }),
            stop.map(|mut s| unsafe { s.as_mut() }),
        );
    }

    fn copy(&self, mut old: NonNull<Node<K, V>>, mut new: NonNull<Node<K, V>>) {
        // SAFETY: see `propagate`.
        self.0
            .copy(unsafe { old.as_mut() }, unsafe { new.as_mut() });
    }

    fn rotate(&self, mut old: NonNull<Node<K, V>>, mut new: NonNull<Node<K, V>>) {
        // SAFETY: see `propagate`.
        self.0
            .rotate(unsafe { old.as_mut() }, unsafe { new.as_mut() });
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V> + Default> Default for Root<K, V, C> {
    fn default() -> Self {
        Root::new(C::default())
    }
}

// Public
impl<K, V, C: TreeCallbacks<Key = K, Value = V>> Root<K, V, C> {
    pub fn new(augmented: C) -> Self {
        Root {
            node: None,
            callbacks: augmented,
        }
    }

    pub fn erase(&mut self, node: &mut Node<K, V>) {
        let mut inner = intrusive::Root::<NodeAdapter<K, V>, _>::new(CallbackBridge(
            &self.callbacks,
            PhantomData,
        ));
        inner.node = self.node.map(Node::link_ptr);
        inner.erase(Node::link_ptr(NonNull::from(node)));
        self.node = inner.node.map(Node::from_link);
    }

    pub fn insert(&mut self, node: NonNull<Node<K, V>>) {
        let mut inner = intrusive::Root::<NodeAdapter<K, V>, _>::new(CallbackBridge(
            &self.callbacks,
            PhantomData,
        ));
        inner.node = self.node.map(Node::link_ptr);
        inner.insert(Node::link_ptr(node));
        self.node = inner.node.map(Node::from_link);
    }
}

#[cfg(debug_assertions)]
impl<K, V, C> Root<K, V, C>
where
    K: std::fmt::Debug,
{
    pub fn validate(&self) -> bool {
        intrusive::validate_of(self.node.map(Node::link_ptr))
    }
}

impl<K, V, C> Root<K, V, C> {
    pub fn first(&self) -> NodePtr<Node<K, V>> {
        intrusive::first_of(self.node.map(Node::link_ptr)).map(Node::from_link)
    }

    pub fn first_postorder(&self) -> NodePtr<Node<K, V>> {
        let n = self.node?;
        // SAFETY: by construction, n is always valid.
        Some(unsafe { n.as_ref() }.left_deepest_node())
    }

    pub fn last(&self) -> NodePtr<Node<K, V>> {
        intrusive::last_of(self.node.map(Node::link_ptr)).map(Node::from_link)
    }
}
