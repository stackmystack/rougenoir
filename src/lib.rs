/// Translated from the linux kernel's implementation of red-black trees.
mod node;
mod root;

use std::ptr::NonNull;

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

pub type NodePtr = Option<NonNull<Node>>;

pub(crate) trait NodePtrExt {
    fn is_black(&self) -> bool;
    fn is_red(&self) -> bool;
    fn left(&self) -> NodePtr;
    fn parent(&self) -> NodePtr;
    fn ptr_value(&self) -> usize;
    fn red_parent(&self) -> NodePtr;
    fn right(&self) -> NodePtr;
    fn set_left(&mut self, left: NodePtr);
    fn set_parent(&mut self, parent: NodePtr);
    fn set_parent_and_color(&mut self, parent: NodePtr, color: Color);
    fn set_parent_color(&mut self, parent_color: usize);
    fn set_right(&mut self, right: NodePtr);
}

impl NodePtrExt for NodePtr {
    #[inline(always)]
    fn is_black(&self) -> bool {
        self.map_or(true, |v| unsafe { v.as_ref() }.is_black())
    }

    #[inline(always)]
    fn is_red(&self) -> bool {
        self.map_or(false, |v| unsafe { v.as_ref() }.is_red())
    }

    #[inline(always)]
    fn parent(&self) -> NodePtr {
        self.map_or(None, |v| unsafe { v.as_ref() }.parent())
    }

    #[inline(always)]
    fn red_parent(&self) -> NodePtr {
        self.map_or(None, |v| unsafe { v.as_ref().red_parent() })
    }

    #[inline(always)]
    fn set_parent(&mut self, parent: NodePtr) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.set_parent(parent);
        }
    }

    #[inline(always)]
    fn set_parent_and_color(&mut self, parent: NodePtr, color: Color) {
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
    fn left(&self) -> NodePtr {
        self.map_or(None, |v| unsafe { v.as_ref() }.left)
    }

    #[inline(always)]
    fn ptr_value(&self) -> usize {
        self.map_or(0, |v| v.as_ptr() as usize)
    }

    #[inline(always)]
    fn right(&self) -> NodePtr {
        self.map_or(None, |v| unsafe { v.as_ref() }.right)
    }

    #[inline(always)]
    fn set_left(&mut self, left: NodePtr) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.left = left;
        }
    }

    #[inline(always)]
    fn set_right(&mut self, right: NodePtr) {
        if let Some(node) = self {
            unsafe { node.as_mut() }.right = right;
        }
    }
}

impl From<&Node> for NodePtr {
    fn from(node: &Node) -> Self {
        NonNull::new(node as *const _ as *mut _)
    }
}

impl From<&mut Node> for NodePtr {
    fn from(node: &mut Node) -> Self {
        NonNull::new(node as *mut _)
    }
}

// #[cfg_attr(target_pointer_width = "64", repr(align(8)))]
// #[cfg_attr(target_pointer_width = "32", repr(align(4)))]
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Node {
    // The parent pointer with color information in the lowest bit
    pub(crate) parent_color: usize,
    // Child pointers
    pub(crate) right: NodePtr,
    pub(crate) left: NodePtr,
}

pub trait Augmenter {
    fn propagate(&self, node: NodePtr, stop: NodePtr);
    fn copy(&self, old: NodePtr, new: NodePtr);
    fn rotate(&self, old: NodePtr, new: NodePtr);
}

pub struct DummyAugmenter {}

impl Default for DummyAugmenter {
    fn default() -> Self {
        Self::new()
    }
}

impl DummyAugmenter {
    pub fn new() -> Self {
        DummyAugmenter {}
    }
}

impl Augmenter for DummyAugmenter {
    fn propagate(&self, _node: NodePtr, _stop: NodePtr) {}
    fn copy(&self, _old: NodePtr, _new: NodePtr) {}
    fn rotate(&self, _old: NodePtr, _new: NodePtr) {}
}

pub trait RootOps {
    fn first(&self) -> NodePtr;
    fn last(&self) -> NodePtr;
    fn first_postorder(&self) -> NodePtr;
    fn replace_node(&mut self, victim: NonNull<Node>, new: NonNull<Node>);
    fn insert(&mut self, node: NonNull<Node>);
    fn erase(&mut self, node: NonNull<Node>);
}

pub trait RootOpsCmp {
    fn add(&mut self, node: NodePtr, cmp: fn(&Node, &Node) -> bool);
}

/// A red-black tree root.
/// T is the type of the data stored in the tree.
/// A is the Augmented Callback type.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Root<A: Augmenter> {
    root: NodePtr,
    augmented: A,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RootCached<A: Augmenter> {
    root: Root<A>,
    leftmost: NodePtr,
}

pub type RBTree = Root<DummyAugmenter>;
pub type RBTreeCached = RootCached<DummyAugmenter>;
pub type RBTreeAugmented<A> = Root<A>;
pub type RBTreeCachedAugmented<A> = RootCached<A>;
