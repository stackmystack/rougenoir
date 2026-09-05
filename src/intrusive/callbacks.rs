use std::{marker::PhantomData, ptr::NonNull};

/// Augmentation hooks for an intrusive tree, invoked at the same points the
/// Linux kernel's `rb_augment_callbacks` invokes `propagate`/`copy`/`rotate`.
///
/// Unlike [`crate::TreeCallbacks`] (used by [`crate::Tree`]/[`crate::Node`]),
/// these callbacks receive a pointer to the caller's own `Value` type, not a
/// `Node<K, V>`. The tree has no idea what `Value` looks like beyond where
/// its [`crate::intrusive::Link`] lives.
pub trait TreeCallbacks {
    type Value;

    fn propagate(&self, node: Option<NonNull<Self::Value>>, stop: Option<NonNull<Self::Value>>);
    fn copy(&self, old: NonNull<Self::Value>, new: NonNull<Self::Value>);
    fn rotate(&self, old: NonNull<Self::Value>, new: NonNull<Self::Value>);
}

/// A [`TreeCallbacks`] that does nothing. The default for a tree with no
/// augmentation.
#[derive(Debug)]
pub struct Noop<V> {
    _marker: PhantomData<fn() -> V>,
}

impl<V> Noop<V> {
    pub fn new() -> Self {
        Noop {
            _marker: PhantomData,
        }
    }
}

impl<V> Default for Noop<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V> Clone for Noop<V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<V> Copy for Noop<V> {}

impl<V> TreeCallbacks for Noop<V> {
    type Value = V;

    fn propagate(&self, _node: Option<NonNull<V>>, _stop: Option<NonNull<V>>) {}
    fn copy(&self, _old: NonNull<V>, _new: NonNull<V>) {}
    fn rotate(&self, _old: NonNull<V>, _new: NonNull<V>) {}
}
