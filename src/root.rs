use std::{cmp::Ordering, marker::PhantomData, ptr::NonNull};

use crate::{ComingFrom, alloc::Global, intrusive};

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

impl<K, V, C: TreeCallbacks<Key = K, Value = V> + Default, A: Default> Default
    for Root<K, V, C, A>
{
    fn default() -> Self {
        Root::new_in(C::default(), A::default())
    }
}

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> Root<K, V, C, Global> {
    pub fn new(augmented: C) -> Self {
        Root::new_in(augmented, Global)
    }
}

// Public
impl<K, V, C: TreeCallbacks<Key = K, Value = V>, A> Root<K, V, C, A> {
    pub fn new_in(augmented: C, alloc: A) -> Self {
        Root {
            node: None,
            callbacks: augmented,
            alloc,
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

    /// Finds where a node comparing via `cmp` belongs (descending as
    /// [`intrusive::find_insert_position`] does), without linking anything.
    /// This is the shared implementation behind
    /// `Tree::insert`/`CachedTree::insert`.
    ///
    /// `cmp` must not read through the node you're about to insert. It doesn't
    /// exist as far as this tree is concerned yet, and combining "compare
    /// against the new node's own key" with linking it in the same step is
    /// exactly the unsound pattern documented on
    /// [`intrusive::find_insert_position`]. Compare against the key you're
    /// about to move into that node instead, then pass what this returns to
    /// [`Root::link_vacant`].
    ///
    /// # Safety
    ///
    /// Every link reachable from `self.node` must point at a live
    /// `Node<K, V>`.
    pub unsafe fn find_insert_position(
        &self,
        cmp: impl FnMut(&Node<K, V>) -> Ordering,
    ) -> intrusive::InsertPosition<Node<K, V>> {
        // SAFETY: delegated to the caller.
        unsafe {
            intrusive::find_insert_position::<NodeAdapter<K, V>>(self.node.map(Node::link_ptr), cmp)
        }
    }

    /// Links `node` at the `Vacant` position [`Root::find_insert_position`]
    /// reported, and rebalances.
    ///
    /// # Safety
    ///
    /// `node` must point at a live, currently unlinked `Node<K, V>` (fresh
    /// from [`Node::leak`], not already part of any tree). `parent`, if
    /// any, must be a live `Node<K, V>` already in this tree — i.e. exactly
    /// what `find_insert_position` just returned.
    pub unsafe fn link_vacant(
        &mut self,
        node: NonNull<Node<K, V>>,
        parent: Option<NonNull<Node<K, V>>>,
        direction: ComingFrom,
    ) {
        let mut inner = intrusive::Root::<NodeAdapter<K, V>, _>::new(CallbackBridge(
            &self.callbacks,
            PhantomData,
        ));
        inner.node = self.node.map(Node::link_ptr);
        // SAFETY: delegated to the caller.
        unsafe { intrusive::link_at(&mut inner, node, parent, direction) };
        self.node = inner.node.map(Node::from_link);
    }
}

#[cfg(debug_assertions)]
impl<K, V, C, A> Root<K, V, C, A>
where
    K: std::fmt::Debug,
{
    pub fn validate(&self) -> bool {
        intrusive::validate_of(self.node.map(Node::link_ptr))
    }
}

impl<K, V, C, A> Root<K, V, C, A> {
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
