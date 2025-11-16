//! A red-black (rouge-noir) tree translated from the linux kernel's implementation of red-black trees.
mod alloc;
mod cached_tree;
mod iter;
mod node;
mod root;
mod set;
mod tree;

use std::{
    marker::PhantomData,
    ptr::{self, NonNull},
};

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
///
/// This is a simple wrapper around a raw pointer with no type constraints,
/// making it Copy and safe to pass around.
#[derive(Debug, PartialEq)]
pub(crate) struct ParentColor<K, V>(*mut Node<K, V>);

impl<K, V> Clone for ParentColor<K, V> {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V> Copy for ParentColor<K, V> {}

impl<K, V> ParentColor<K, V> {
    /// Create a null parent color (no parent)
    #[inline(always)]
    pub fn null() -> Self {
        ParentColor(ptr::null_mut())
    }

    /// Create a new ParentColor from a parent pointer and color
    #[inline(always)]
    pub fn new(parent: *mut Node<K, V>, color: Color) -> Self {
        ParentColor(parent.map_addr(|p| p + color as usize))
    }

    /// Extract the parent pointer (clears color bit)
    #[inline(always)]
    pub fn parent(&self) -> *mut Node<K, V> {
        self.0.map_addr(|p| p & !1)
    }

    /// Extract the color from the lowest bit
    #[inline(always)]
    pub fn color(&self) -> Color {
        Color::from(self.0.addr() & 1)
    }

    /// Set parent while preserving color
    #[inline(always)]
    pub fn set_parent(&mut self, parent: *mut Node<K, V>) {
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
    pub fn raw(&self) -> *mut Node<K, V> {
        self.0
    }

    /// Create from raw encoded pointer
    #[inline(always)]
    pub fn from_raw(raw: *mut Node<K, V>) -> Self {
        ParentColor(raw)
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ComingFrom {
    Left,
    Right,
}

pub type NodePtr<K, V> = Option<NonNull<Node<K, V>>>;

pub trait NodePtrExt {
    type Key;
    type Value;

    fn maybe_ref(&self) -> Option<&Node<Self::Key, Self::Value>>;
    fn maybe_mut_ref(&mut self) -> Option<&mut Node<Self::Key, Self::Value>>;
    /// # Safety
    ///
    /// This is an internal API. Don't use directly, and most importantly, don't drop manually.
    unsafe fn mut_ref(&mut self) -> &mut Node<Self::Key, Self::Value>;
    fn is_black(&self) -> bool;
    fn is_red(&self) -> bool;
    fn left(&self) -> NodePtr<Self::Key, Self::Value>;
    /// # Safety
    ///
    /// This should not be called on null ptrs.
    unsafe fn link(&mut self, parent: *mut Node<Self::Key, Self::Value>, direction: ComingFrom);
    #[allow(dead_code)]
    fn next_node(&self) -> NodePtr<Self::Key, Self::Value>;
    fn parent(&self) -> NodePtr<Self::Key, Self::Value>;
    #[allow(dead_code)]
    fn prev_node(&self) -> NodePtr<Self::Key, Self::Value>;
    fn ptr(&self) -> *mut Node<Self::Key, Self::Value>;
    fn red_parent(&self) -> NodePtr<Self::Key, Self::Value>;
    fn right(&self) -> NodePtr<Self::Key, Self::Value>;
    fn set_color(&mut self, color: Color);
    fn set_left(&mut self, left: NodePtr<Self::Key, Self::Value>);
    fn set_parent(&mut self, parent: *mut Node<Self::Key, Self::Value>);
    fn set_parent_and_color(&mut self, parent: *mut Node<Self::Key, Self::Value>, color: Color);
    fn set_parent_color(&mut self, parent_color: *mut Node<Self::Key, Self::Value>);
    fn set_right(&mut self, right: NodePtr<Self::Key, Self::Value>);
}

impl<K, V> NodePtrExt for NodePtr<K, V> {
    type Key = K;
    type Value = V;

    #[inline(always)]
    fn maybe_ref(&self) -> Option<&Node<Self::Key, Self::Value>> {
        self.map(|n| unsafe { n.as_ref() })
    }

    #[inline(always)]
    fn maybe_mut_ref(&mut self) -> Option<&mut Node<Self::Key, Self::Value>> {
        self.map(|mut n| unsafe { n.as_mut() })
    }

    #[inline(always)]
    unsafe fn mut_ref(&mut self) -> &mut Node<Self::Key, Self::Value> {
        self.map(|mut v| unsafe { v.as_mut() }).unwrap()
    }

    #[inline(always)]
    fn is_black(&self) -> bool {
        !self.is_red()
    }

    #[inline(always)]
    fn is_red(&self) -> bool {
        self.is_some_and(|v| unsafe { v.as_ref() }.is_red())
    }

    #[inline(always)]
    unsafe fn link(&mut self, parent: *mut Node<Self::Key, Self::Value>, direction: ComingFrom) {
        self.map(|mut v| unsafe { Node::link(v.as_mut(), parent, direction) });
    }

    #[inline(always)]
    fn next_node(&self) -> NodePtr<Self::Key, Self::Value> {
        self.map(|v| unsafe { v.as_ref() }.next()).flatten()
    }

    #[inline(always)]
    fn parent(&self) -> NodePtr<Self::Key, Self::Value> {
        self.map_or(None, |v| unsafe { v.as_ref() }.parent())
    }

    #[inline(always)]
    fn prev_node(&self) -> NodePtr<Self::Key, Self::Value> {
        self.map(|v| unsafe { v.as_ref() }.prev()).flatten()
    }

    #[inline(always)]
    fn ptr(&self) -> *mut Node<Self::Key, Self::Value> {
        self.map_or(ptr::null_mut(), |p| p.as_ptr())
    }

    #[inline(always)]
    fn red_parent(&self) -> NodePtr<Self::Key, Self::Value> {
        self.map_or(None, |v| unsafe { v.as_ref().red_parent() })
    }

    #[inline(always)]
    fn set_color(&mut self, color: Color) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.set_color(color);
        }
    }

    #[inline(always)]
    fn set_parent(&mut self, parent: *mut Node<Self::Key, Self::Value>) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.set_parent(parent);
        }
    }

    #[inline(always)]
    fn set_parent_and_color(&mut self, parent: *mut Node<Self::Key, Self::Value>, color: Color) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.set_parent_and_color(parent, color);
        }
    }

    #[inline(always)]
    fn set_parent_color(&mut self, parent_color: *mut Node<K, V>) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.parent_color = ParentColor::from_raw(parent_color);
        }
    }

    #[inline(always)]
    fn left(&self) -> NodePtr<Self::Key, Self::Value> {
        self.map_or(None, |v| unsafe { v.as_ref() }.left)
    }

    #[inline(always)]
    fn right(&self) -> NodePtr<Self::Key, Self::Value> {
        self.map_or(None, |v| unsafe { v.as_ref() }.right)
    }

    #[inline(always)]
    fn set_left(&mut self, left: NodePtr<Self::Key, Self::Value>) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.left = left;
        }
    }

    #[inline(always)]
    fn set_right(&mut self, right: NodePtr<Self::Key, Self::Value>) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.right = right;
        }
    }
}

impl<K, V> From<&Node<K, V>> for NodePtr<K, V> {
    fn from(node: &Node<K, V>) -> Self {
        Some(NonNull::from(node))
    }
}

impl<K, V> From<&mut Node<K, V>> for NodePtr<K, V> {
    fn from(node: &mut Node<K, V>) -> Self {
        Some(NonNull::from(node))
    }
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq)]
pub struct Node<K, V> {
    /// The parent pointer with color information in the lowest bit
    pub(crate) parent_color: ParentColor<K, V>,
    /// Right Child
    pub right: NodePtr<K, V>,
    /// Left Child
    pub left: NodePtr<K, V>,
    /// Key
    pub key: K,
    /// Value
    pub value: V,
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
    pub node: NodePtr<K, V>,
}

pub struct Tree<K, V, C> {
    len: usize,
    root: Root<K, V, C>,
}

pub struct CachedTree<K, V, C> {
    leftmost: NodePtr<K, V>,
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
        direction.reserve(log_val.checked_mul(2).unwrap_or(usize::MAX).max(4096));
        while let Some(mut current) = parent {
            let current_ref = unsafe { current.as_ref() };
            if current_ref.left.is_some() {
                parent = current_ref.left;
                direction.push(ComingFrom::Left);
                continue;
            }
            if current_ref.right.is_some() {
                parent = current_ref.right;
                direction.push(ComingFrom::Right);
                continue;
            }
            parent = current_ref.parent();
            // drop; don't call rbtree erase => needless overhead.
            if let Some(mut parent) = parent {
                match direction.pop() {
                    Some(ComingFrom::Left) => unsafe { parent.as_mut() }.left = None,
                    Some(ComingFrom::Right) => unsafe { parent.as_mut() }.right = None,
                    _ => {}
                }
            }
            // SAFETY: Now it's safe to drop
            unsafe { Node::<K, V>::unleak(current.as_mut()) };
        }
    }
}
