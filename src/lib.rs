//! A red-black (rouge-noir) tree translated from the linux kernel's implementation of red-black trees.
mod alloc;
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

pub trait NodePtrExt {
    type Node;

    fn maybe_ref(&self) -> Option<&Self::Node>;
    fn maybe_mut_ref(&mut self) -> Option<&mut Self::Node>;
    fn is_black(&self) -> bool;
    fn is_red(&self) -> bool;
    fn left(&self) -> NodePtr<Self::Node>;
    /// # Safety
    ///
    /// This should not be called on null ptrs.
    unsafe fn link(&mut self, parent: *mut Self::Node, direction: ComingFrom);
    #[allow(dead_code)]
    fn next_node(&self) -> NodePtr<Self::Node>;
    fn parent(&self) -> NodePtr<Self::Node>;
    #[allow(dead_code)]
    fn prev_node(&self) -> NodePtr<Self::Node>;
    fn ptr(&self) -> *mut Self::Node;
    fn right(&self) -> NodePtr<Self::Node>;
}

pub(crate) trait NodePtrImplExt {
    type Node;

    fn red_parent(&self) -> NodePtr<Self::Node>;
    fn set_color(&mut self, color: Color);
    fn set_left(&mut self, left: NodePtr<Self::Node>);
    fn set_parent(&mut self, parent: *mut Self::Node);
    fn set_parent_and_color(&mut self, parent: *mut Self::Node, color: Color);
    fn set_parent_color(&mut self, parent_color: ParentColor<Self::Node>);
    fn set_right(&mut self, right: NodePtr<Self::Node>);
}

// Every accessor below bridges through `Node::link_ptr`/`Node::from_link`
// (i.e. through `Link`'s own raw-pointer-based associated functions)
// instead of touching a stored sibling pointer's target directly. This
// mirrors `crate::intrusive::node_ptr`'s impls for `NodePtr<Link>`: a
// pointer read back out of a sibling's `left`/`right` is a `NonNull<Link>`
// pointing at that sibling's *embedded* `Link`, and widening it back out to
// the sibling's whole `Node<K, V>` is exactly the `container_of()`-style
// operation that requires staying in raw-pointer land end to end.
impl<K, V> NodePtrExt for NodePtr<Node<K, V>> {
    type Node = Node<K, V>;

    #[inline(always)]
    fn maybe_ref(&self) -> Option<&Self::Node> {
        self.map(|n| unsafe { n.as_ref() })
    }

    #[inline(always)]
    fn maybe_mut_ref(&mut self) -> Option<&mut Self::Node> {
        self.map(|mut n| unsafe { n.as_mut() })
    }

    #[inline(always)]
    fn is_black(&self) -> bool {
        !self.is_red()
    }

    #[inline(always)]
    fn is_red(&self) -> bool {
        // SAFETY: any Some(v) here points at a live Node<K, V>.
        self.is_some_and(|v| unsafe { Link::is_red(Node::link_ptr(v)) })
    }

    #[inline(always)]
    unsafe fn link(&mut self, parent: *mut Self::Node, direction: ComingFrom) {
        // SAFETY: delegated to the caller.
        self.map(|v| unsafe { Node::link(v.as_ptr(), parent, direction) });
    }

    #[inline(always)]
    fn next_node(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(v) here points at a live Node<K, V>.
        self.and_then(|v| unsafe { Link::next(Node::link_ptr(v)) })
            .map(Node::from_link)
    }

    #[inline(always)]
    fn parent(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(v) here points at a live Node<K, V>.
        self.and_then(|v| unsafe { Link::parent(Node::link_ptr(v)) })
            .map(Node::from_link)
    }

    #[inline(always)]
    fn prev_node(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(v) here points at a live Node<K, V>.
        self.and_then(|v| unsafe { Link::prev(Node::link_ptr(v)) })
            .map(Node::from_link)
    }

    #[inline(always)]
    fn ptr(&self) -> *mut Self::Node {
        self.map_or(ptr::null_mut(), |p| p.as_ptr())
    }

    #[inline(always)]
    fn left(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(v) here points at a live Node<K, V>.
        self.and_then(|v| unsafe { Link::left(Node::link_ptr(v)) })
            .map(Node::from_link)
    }

    #[inline(always)]
    fn right(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(v) here points at a live Node<K, V>.
        self.and_then(|v| unsafe { Link::right(Node::link_ptr(v)) })
            .map(Node::from_link)
    }
}

impl<K, V> NodePtrImplExt for NodePtr<Node<K, V>> {
    type Node = Node<K, V>;

    #[inline(always)]
    fn red_parent(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(v) here points at a live Node<K, V>.
        self.and_then(|v| unsafe { Link::red_parent(Node::link_ptr(v)) })
            .map(Node::from_link)
    }

    #[inline(always)]
    fn set_color(&mut self, color: Color) {
        if let Some(node) = self {
            // SAFETY: node points at a live Node<K, V>.
            unsafe { Link::set_color(Node::link_ptr(*node), color) };
        }
    }

    #[inline(always)]
    fn set_parent(&mut self, parent: *mut Self::Node) {
        if let Some(node) = self {
            // SAFETY: node points at a live Node<K, V>.
            unsafe { Link::set_parent(Node::link_ptr(*node), Node::raw_link_ptr(parent)) };
        }
    }

    #[inline(always)]
    fn set_parent_and_color(&mut self, parent: *mut Self::Node, color: Color) {
        if let Some(node) = self {
            // SAFETY: node points at a live Node<K, V>.
            unsafe {
                Link::set_parent_and_color(Node::link_ptr(*node), Node::raw_link_ptr(parent), color)
            };
        }
    }

    #[inline(always)]
    fn set_parent_color(&mut self, parent_color: ParentColor<Node<K, V>>) {
        if let Some(node) = self {
            let link_pc = ParentColor::new(
                Node::raw_link_ptr(parent_color.parent()),
                parent_color.color(),
            );
            // SAFETY: node points at a live Node<K, V>.
            unsafe { Link::set_parent_color(Node::link_ptr(*node), link_pc) };
        }
    }

    #[inline(always)]
    fn set_left(&mut self, left: NodePtr<Self::Node>) {
        if let Some(node) = self {
            // SAFETY: node points at a live Node<K, V>.
            unsafe { Link::set_left(Node::link_ptr(*node), left.map(Node::link_ptr)) };
        }
    }

    #[inline(always)]
    fn set_right(&mut self, right: NodePtr<Self::Node>) {
        if let Some(node) = self {
            // SAFETY: node points at a live Node<K, V>.
            unsafe { Link::set_right(Node::link_ptr(*node), right.map(Node::link_ptr)) };
        }
    }
}

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

/// Bridges a [`Node<K, V>`]'s embedded [`Link`] back to the whole `Node`.
///
/// This is what lets [`Root<K, V, C>`] reuse the exact same pointer-chasing
/// primitives ([`Link`]'s raw-pointer-based associated functions) as the
/// public [`intrusive`] API, instead of duplicating them.
struct NodeAdapter<K, V>(PhantomData<(K, V)>);

// SAFETY: `link` is genuinely a field of type `Link` on `Node<K, V>`, so
// `offset_of!` gives its exact byte offset.
unsafe impl<K, V> Adapter for NodeAdapter<K, V> {
    type Value = Node<K, V>;

    fn link_offset() -> usize {
        std::mem::offset_of!(Node<K, V>, link)
    }
}

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
pub struct Root<K, V, C> {
    pub callbacks: C,
    pub node: NodePtr<Node<K, V>>,
}

pub struct Tree<K, V, C> {
    len: usize,
    root: Root<K, V, C>,
}

pub struct CachedTree<K, V, C> {
    leftmost: NodePtr<Node<K, V>>,
    len: usize,
    root: Root<K, V, C>,
}

pub struct Set<T, C> {
    tree: Tree<T, (), C>,
}

impl<K, V> Node<K, V> {
    /// # Safety
    ///
    /// It leaks; use with dealloc_node.
    pub unsafe fn leak(key: K, value: V) -> Option<NonNull<Node<K, V>>>
    where
        K: Ord,
    {
        unsafe { alloc::leak_alloc_node(key, value) }
    }

    /// # Safety
    ///
    /// It drops; use after alloc_node.
    pub unsafe fn unleak(current: *mut Node<K, V>) -> Box<Node<K, V>> {
        unsafe { alloc::own_back(current) }
    }
}

impl<K, V, C> Root<K, V, C> {
    /// # SAFETY
    ///
    /// It drops all nodes from the root.
    /// Pass len = 0 if you're unsure of the length of the # of elements in
    /// your tree.
    pub unsafe fn dealloc(root: &mut Root<K, V, C>, len: usize) {
        let mut parent = root.node;
        let mut direction = Vec::new();
        // max depth = 2 × log₂(n+1)
        let log_val = (len + 1).checked_ilog2().unwrap_or(0) as usize;
        direction.reserve(log_val.saturating_mul(2).max(4096));
        while let Some(mut current) = parent {
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
            // SAFETY: Now it's safe to drop
            unsafe { Node::<K, V>::unleak(current.as_mut()) };
        }
    }
}
