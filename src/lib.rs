//! A red-black (rouge-noir) tree translated from the linux kernel's implementation of red-black trees.
mod cached_tree;
mod iter;
mod node;
mod root;
mod set;
mod tree;

use std::{marker::PhantomData, ptr::NonNull};

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

pub type NodePtr<K, V> = Option<NonNull<Node<K, V>>>;

pub trait NodePtrExt {
    type Key;
    type Value;

    fn is_black(&self) -> bool;
    fn is_red(&self) -> bool;
    fn left(&self) -> NodePtr<Self::Key, Self::Value>;
    fn link(
        &mut self,
        parent: NonNull<Node<Self::Key, Self::Value>>,
        link: &mut NodePtr<Self::Key, Self::Value>,
    ) -> usize;
    #[allow(dead_code)]
    fn next_node(&self) -> NodePtr<Self::Key, Self::Value>;
    fn parent(&self) -> NodePtr<Self::Key, Self::Value>;
    #[allow(dead_code)]
    fn prev_node(&self) -> NodePtr<Self::Key, Self::Value>;
    fn ptr_value(&self) -> usize;
    fn red_parent(&self) -> NodePtr<Self::Key, Self::Value>;
    fn right(&self) -> NodePtr<Self::Key, Self::Value>;
    fn set_color(&mut self, color: Color);
    fn set_left(&mut self, left: NodePtr<Self::Key, Self::Value>);
    fn set_parent(&mut self, parent: NodePtr<Self::Key, Self::Value>);
    fn set_parent_and_color(&mut self, parent: NodePtr<Self::Key, Self::Value>, color: Color);
    fn set_parent_color(&mut self, parent_color: usize);
    fn set_right(&mut self, right: NodePtr<Self::Key, Self::Value>);
}

impl<K, V> NodePtrExt for NodePtr<K, V> {
    type Key = K;
    type Value = V;

    #[inline(always)]
    fn is_black(&self) -> bool {
        self.is_none_or(|v| unsafe { v.as_ref() }.is_black())
    }

    #[inline(always)]
    fn is_red(&self) -> bool {
        self.is_some_and(|v| unsafe { v.as_ref() }.is_red())
    }

    #[inline(always)]
    fn link(
        &mut self,
        parent: NonNull<Node<Self::Key, Self::Value>>,
        link: &mut NodePtr<Self::Key, Self::Value>,
    ) -> usize {
        self.map_or(0, |mut v| unsafe { v.as_mut() }.link(parent, link))
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
    fn set_parent(&mut self, parent: NodePtr<Self::Key, Self::Value>) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.set_parent(parent);
        }
    }

    #[inline(always)]
    fn set_parent_and_color(&mut self, parent: NodePtr<Self::Key, Self::Value>, color: Color) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.set_parent_and_color(parent, color);
        }
    }

    #[inline(always)]
    fn set_parent_color(&mut self, parent_color: usize) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.parent_color = parent_color;
        }
    }

    #[inline(always)]
    fn left(&self) -> NodePtr<Self::Key, Self::Value> {
        self.map_or(None, |v| unsafe { v.as_ref() }.left)
    }

    #[inline(always)]
    fn ptr_value(&self) -> usize {
        self.map_or(0, |v| v.as_ptr() as usize)
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
        NonNull::new(node as *const _ as *mut _)
    }
}

impl<K, V> From<&mut Node<K, V>> for NodePtr<K, V> {
    fn from(node: &mut Node<K, V>) -> Self {
        NonNull::new(node as *mut _)
    }
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq)]
pub struct Node<K, V> {
    /// The parent pointer with color information in the lowest bit
    pub(crate) parent_color: usize,
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
        node: NodePtr<Self::Key, Self::Value>,
        stop: NodePtr<Self::Key, Self::Value>,
    );
    fn copy(&self, old: NodePtr<Self::Key, Self::Value>, new: NodePtr<Self::Key, Self::Value>);
    fn rotate(&self, old: NodePtr<Self::Key, Self::Value>, new: NodePtr<Self::Key, Self::Value>);
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd)]
pub struct Noop<K, V> {
    _phantom_k: PhantomData<K>,
    _phantom_v: PhantomData<V>,
}

impl<K, V> Default for Noop<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Noop<K, V> {
    pub fn new() -> Self {
        Noop {
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }
}

impl<K, V> TreeCallbacks for Noop<K, V> {
    type Key = K;
    type Value = V;

    fn propagate(
        &self,
        _node: NodePtr<Self::Key, Self::Value>,
        _stop: NodePtr<Self::Key, Self::Value>,
    ) {
    }
    fn copy(&self, _old: NodePtr<Self::Key, Self::Value>, _new: NodePtr<Self::Key, Self::Value>) {}
    fn rotate(&self, _old: NodePtr<Self::Key, Self::Value>, _new: NodePtr<Self::Key, Self::Value>) {
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

/// SAFETY: it leaks; use with dealloc_node.
pub unsafe fn alloc_node<K, V>(key: K, value: V) -> Option<NonNull<Node<K, V>>>
where
    K: Ord,
{
    let mut root_node = NonNull::new(Box::into_raw(Box::new(Node::new(key, value))));
    root_node.set_parent_color(Color::Black as usize);
    root_node
}

/// SAFETY: it drops; use after alloc_node.
pub unsafe fn dealloc_node<K, V>(current: *mut Node<K, V>) {
    let _ = unsafe { Box::from_raw(current) };
}

/// SAFETY: it drops all nodes from the root.
/// Pass len = 0 if you're unsure of the length of the # of elements in
/// your tree.
pub unsafe fn dealloc_root<K, V, C>(root: &mut Root<K, V, C>, len: usize) {
    enum ComingFrom {
        Left,
        Right,
    }
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
        if parent.is_some() {
            match direction.pop() {
                Some(ComingFrom::Left) => unsafe { parent.unwrap().as_mut() }.left = None,
                Some(ComingFrom::Right) => unsafe { parent.unwrap().as_mut() }.right = None,
                _ => {}
            }
        }
        // SAFETY: Now it's safe to drop
        unsafe { dealloc_node(current.as_mut()) };
    }
}
