//! A red-black (rouge-noir) tree translated from the linux kernel's implementation of red-black trees.
#![cfg_attr(feature = "nightly", feature(allocator_api))]

pub mod alloc;
mod cached_tree;
pub mod intrusive;
mod iter;
mod node;
mod root;
mod set;
mod tree;

use std::{
    marker::PhantomData,
    ptr::{self, NonNull},
};

use alloc::Allocator;
use intrusive::{Adapter, Link};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Color {
    Red = 0,
    Black = 1,
}

impl From<Color> for usize {
    fn from(color: Color) -> usize {
        color as usize
    }
}

impl From<usize> for Color {
    fn from(color: usize) -> Color {
        match color {
            0 => Color::Red,
            _ => Color::Black,
        }
    }
}

/// Encodes a parent pointer with color information in the lowest bit.
///
/// The color is stored in the lowest bit of the pointer address:
/// - Bit 0 = 0: Red
/// - Bit 0 = 1: Black
#[derive(Debug, PartialEq)]
pub(crate) struct ParentColor<N>(*mut N);

impl<N> Clone for ParentColor<N> {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<N> Copy for ParentColor<N> {}

impl<N> ParentColor<N> {
    /// Create a null parent color (no parent)
    #[inline(always)]
    pub fn null() -> Self {
        ParentColor(ptr::null_mut())
    }

    /// Create a new ParentColor from a parent pointer and color
    #[inline(always)]
    pub fn new(parent: *mut N, color: Color) -> Self {
        ParentColor(parent.map_addr(|p| p + color as usize))
    }

    /// Extract the parent pointer (clears color bit)
    #[inline(always)]
    pub fn parent(&self) -> *mut N {
        self.0.map_addr(|p| p & !1)
    }

    /// Extract the color from the lowest bit
    #[inline(always)]
    pub fn color(&self) -> Color {
        Color::from(self.0.addr() & 1)
    }

    /// Set parent while preserving color
    #[inline(always)]
    pub fn set_parent(&mut self, parent: *mut N) {
        let color = self.color();
        *self = ParentColor::new(parent, color);
    }

    /// Set color while preserving parent
    #[inline(always)]
    pub fn set_color(&mut self, color: Color) {
        let parent = self.parent();
        *self = ParentColor::new(parent, color);
    }

    /// Get the raw encoded pointer (parent with color bits)
    #[inline(always)]
    pub fn raw(&self) -> *mut N {
        self.0
    }

    /// Create from raw encoded pointer
    #[allow(dead_code)]
    #[inline(always)]
    pub fn from_raw(raw: *mut N) -> Self {
        ParentColor(raw)
    }

    /// Get parent as NonNull pointer (clears color bit)
    #[inline(always)]
    pub fn non_null(&self) -> NodePtr<N> {
        NonNull::new(self.parent())
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ComingFrom {
    Left,
    Right,
}

pub type NodePtr<N> = Option<NonNull<N>>;

impl<K, V> From<&Node<K, V>> for NodePtr<Node<K, V>> {
    fn from(node: &Node<K, V>) -> Self {
        Some(NonNull::from(node))
    }
}

impl<K, V> From<&mut Node<K, V>> for NodePtr<Node<K, V>> {
    fn from(node: &mut Node<K, V>) -> Self {
        Some(NonNull::from(node))
    }
}

#[repr(C)]
pub struct Node<K, V> {
    /// The link into the tree structure (parent/left/right/color).
    pub(crate) link: Link,
    /// Key
    pub key: K,
    /// Value
    pub value: V,
}

// Bridges a `Node<K, V>`'s embedded `Link` back to the whole `Node`. This
// is what lets `Root<K, V, C>` reuse the exact same pointer-chasing
// primitives (`Link`'s raw-pointer-based associated functions)
intrusive_adapter!(NodeAdapter<K, V> = Node<K, V> : link);

impl<K, V> Node<K, V> {
    /// Converts a pointer to a whole `Node<K, V>` into a pointer to its
    /// embedded [`Link`].
    #[inline(always)]
    fn link_ptr(this: NonNull<Node<K, V>>) -> NonNull<Link> {
        // SAFETY: `this` points at a live `Node<K, V>`, which genuinely
        // embeds a `Link` at `NodeAdapter::link_offset()`.
        unsafe { NodeAdapter::<K, V>::get_link(this) }
    }

    /// Converts a pointer to a [`Link`] embedded in some `Node<K, V>` back
    /// to a pointer to that whole `Node<K, V>`.
    #[inline(always)]
    fn from_link(link: NonNull<Link>) -> NonNull<Node<K, V>> {
        // SAFETY: every `Link` reachable from a `Node<K, V>` tree was
        // produced by `link_ptr` from a live `Node<K, V>`.
        unsafe { NodeAdapter::<K, V>::get_value(link) }
    }

    /// Like [`Node::link_ptr`], but tolerates (and preserves) a null
    /// pointer, mirroring how a null `*mut Node<K, V>` means "no parent".
    #[inline(always)]
    fn raw_link_ptr(this: *mut Node<K, V>) -> *mut Link {
        NonNull::new(this).map_or(ptr::null_mut(), |n| Node::link_ptr(n).as_ptr())
    }
}

pub trait TreeCallbacks {
    type Key;
    type Value;

    fn propagate(
        &self,
        node: Option<&mut Node<Self::Key, Self::Value>>,
        stop: Option<&mut Node<Self::Key, Self::Value>>,
    );
    fn copy(&self, old: &mut Node<Self::Key, Self::Value>, new: &mut Node<Self::Key, Self::Value>);
    fn rotate(
        &self,
        old: &mut Node<Self::Key, Self::Value>,
        new: &mut Node<Self::Key, Self::Value>,
    );
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd)]
pub struct Noop<K, V> {
    phantom: PhantomData<(K, V)>,
}

impl<K, V> Default for Noop<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Noop<K, V> {
    pub fn new() -> Self {
        Noop {
            phantom: PhantomData,
        }
    }
}

impl<K, V> TreeCallbacks for Noop<K, V> {
    type Key = K;
    type Value = V;

    fn propagate(
        &self,
        _node: Option<&mut Node<Self::Key, Self::Value>>,
        _stop: Option<&mut Node<Self::Key, Self::Value>>,
    ) {
    }
    fn copy(
        &self,
        _old: &mut Node<Self::Key, Self::Value>,
        _new: &mut Node<Self::Key, Self::Value>,
    ) {
    }
    fn rotate(
        &self,
        _old: &mut Node<Self::Key, Self::Value>,
        _new: &mut Node<Self::Key, Self::Value>,
    ) {
    }
}

/// A red-black tree root.
/// T is the type of the data stored in the tree.
/// A is the Augmented Callback type.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Root<K, V, C, A = crate::alloc::Global> {
    pub callbacks: C,
    pub node: NodePtr<Node<K, V>>,
    pub alloc: A,
}

pub struct Tree<K, V, C, A = crate::alloc::Global>
where
    A: Allocator,
{
    len: usize,
    root: Root<K, V, C, A>,
}

pub struct CachedTree<K, V, C, A = crate::alloc::Global>
where
    A: Allocator,
{
    leftmost: NodePtr<Node<K, V>>,
    len: usize,
    root: Root<K, V, C, A>,
}

pub struct Set<T, C, A = crate::alloc::Global>
where
    A: Allocator,
{
    tree: Tree<T, (), C, A>,
}

impl<K, V> Node<K, V> {
    /// # Safety
    ///
    /// It leaks; use with dealloc_node.
    pub unsafe fn leak(key: K, value: V) -> Option<NonNull<Node<K, V>>>
    where
        K: Ord,
    {
        alloc::alloc_node(&alloc::Global, key, value)
    }

    /// # Safety
    ///
    /// It drops; use after alloc_node.
    pub unsafe fn unleak(current: *mut Node<K, V>) -> Box<Node<K, V>> {
        // SAFETY: delegated to the caller. A `Global` node is a plain
        // `std::alloc` allocation, so `Box::from_raw` owns it correctly.
        unsafe { Box::from_raw(current) }
    }
}

impl<K, V, C, A> Root<K, V, C, A> {
    /// # SAFETY
    ///
    /// It drops all nodes from the root.
    /// Pass len = 0 if you're unsure of the length of the # of elements in
    /// your tree.
    pub unsafe fn dealloc(root: &mut Root<K, V, C, A>, len: usize)
    where
        A: Allocator,
    {
        let mut parent = root.node;
        let mut direction = Vec::new();
        // max depth = 2 × log₂(n+1)
        let log_val = (len + 1).checked_ilog2().unwrap_or(0) as usize;
        direction.reserve(log_val.saturating_mul(2).max(4096));
        while let Some(current) = parent {
            let current_ref = unsafe { current.as_ref() };
            if current_ref.left().is_some() {
                parent = current_ref.left();
                direction.push(ComingFrom::Left);
                continue;
            }
            if current_ref.right().is_some() {
                parent = current_ref.right();
                direction.push(ComingFrom::Right);
                continue;
            }
            parent = current_ref.parent();
            // drop; don't call rbtree erase => needless overhead.
            if let Some(mut parent) = parent {
                match direction.pop() {
                    Some(ComingFrom::Left) => unsafe { parent.as_mut() }.set_left(None),
                    Some(ComingFrom::Right) => unsafe { parent.as_mut() }.set_right(None),
                    _ => {}
                }
            }
            // SAFETY: `current` is a live node of this tree, now unlinked
            // from its parent, and nothing else references it.
            unsafe { alloc::drop_node(&root.alloc, current) };
        }
    }
}
