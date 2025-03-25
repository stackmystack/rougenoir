/// Translated from the linux kernel's implementation of red-black trees.
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
    fn parent(&self) -> NodePtr<Self::Key, Self::Value>;
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
    fn parent(&self) -> NodePtr<Self::Key, Self::Value> {
        self.map_or(None, |v| unsafe { v.as_ref() }.parent())
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

pub trait Augmenter {
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

pub struct DummyAugmenter<K, V> {
    _phantom_k: PhantomData<K>,
    _phantom_v: PhantomData<V>,
}

impl<K, V> Default for DummyAugmenter<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> DummyAugmenter<K, V> {
    pub fn new() -> Self {
        DummyAugmenter {
            _phantom_k: PhantomData::default(),
            _phantom_v: PhantomData::default(),
        }
    }
}

impl<K, V> Augmenter for DummyAugmenter<K, V> {
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

pub trait RootOps {
    type Key;
    type Value;

    fn first(&self) -> NodePtr<Self::Key, Self::Value>;
    fn last(&self) -> NodePtr<Self::Key, Self::Value>;
    fn first_postorder(&self) -> NodePtr<Self::Key, Self::Value>;
    fn replace_node(
        &mut self,
        victim: NonNull<Node<Self::Key, Self::Value>>,
        new: NonNull<Node<Self::Key, Self::Value>>,
    );
    fn insert(&mut self, node: NonNull<Node<Self::Key, Self::Value>>);
    fn erase(&mut self, node: NonNull<Node<Self::Key, Self::Value>>);
}

pub trait RootOpsCmp {
    type Key;
    type Value;

    fn add(
        &mut self,
        node: NodePtr<Self::Key, Self::Value>,
        cmp: fn(&Node<Self::Key, Self::Value>, &Node<Self::Key, Self::Value>) -> bool,
    );
}

/// A red-black tree root.
/// T is the type of the data stored in the tree.
/// A is the Augmented Callback type.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Root<K, V, A: Augmenter> {
    root: NodePtr<K, V>,
    augmented: A,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RootCached<K, V, A: Augmenter> {
    root: Root<K, V, A>,
    leftmost: NodePtr<K, V>,
}
