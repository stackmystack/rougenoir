/// Translated from the linux kernel's implementation of red-black trees.
mod iter;
mod node;
mod root;
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

pub(crate) trait NodePtrExt {
    type Key;
    type Value;

    fn is_black(&self) -> bool;
    fn is_red(&self) -> bool;
    fn left(&self) -> NodePtr<Self::Key, Self::Value>;
    #[allow(dead_code)]
    fn next_node(&self) -> NodePtr<Self::Key, Self::Value>;
    fn parent(&self) -> NodePtr<Self::Key, Self::Value>;
    #[allow(dead_code)]
    fn prev_node(&self) -> NodePtr<Self::Key, Self::Value>;
    fn ptr_value(&self) -> usize;
    fn red_parent(&self) -> NodePtr<Self::Key, Self::Value>;
    fn right(&self) -> NodePtr<Self::Key, Self::Value>;
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
        self.map_or(true, |v| unsafe { v.as_ref() }.is_black())
    }

    #[inline(always)]
    fn is_red(&self) -> bool {
        self.map_or(false, |v| unsafe { v.as_ref() }.is_red())
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
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Node<K, V> {
    // The parent pointer with color information in the lowest bit
    pub(crate) parent_color: usize,
    // Child pointers
    pub(crate) right: NodePtr<K, V>,
    pub(crate) left: NodePtr<K, V>,
    key: K,
    value: V,
}

pub trait Callbacks {
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

#[derive(Debug, Copy, Clone)]
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

impl<K, V> Callbacks for Noop<K, V> {
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
pub struct Root<K, V, C: Callbacks<Key = K, Value = V> = Noop<K, V>> {
    pub(crate) callbacks: C,
    pub(crate) root: NodePtr<K, V>,
}

#[derive(Debug)]
pub struct Tree<K, V, C: Callbacks<Key = K, Value = V> = Noop<K, V>> {
    len: usize,
    root: Root<K, V, C>,
}

impl<K, V, C: Callbacks<Key = K, Value = V>> Tree<K, V, C> {
    pub fn with_callbacks(augmented: C) -> Self {
        Tree {
            len: 0,
            root: Root::new(augmented),
        }
    }
}

impl<K, V> Tree<K, V, Noop<K, V>> {
    pub fn new() -> Self {
        Tree {
            len: 0,
            root: Root::new(Noop::new()),
        }
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V> + Default> Default for Tree<K, V, C> {
    fn default() -> Self {
        Self::with_callbacks(C::default())
    }
}

// TODO:

// 1. Send + Sync impl
// 1. TreeCached
// pub type RBTreeCached<K, V> = Tree<RootCached<K, V, DummyAugmenter<K, V>>>;
// pub type RBTreeCachedAugmented<K, V, A> = Tree<RootCached<K, V, A>>;
