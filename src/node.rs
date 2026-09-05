use std::{fmt::Debug, ptr::NonNull};

use crate::{ComingFrom, intrusive::Link};

use super::{Color, Node, NodePtr, ParentColor};

// Public API.
impl<K, V> Node<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Node {
            link: Link::new(),
            key,
            value,
        }
    }

    #[inline(always)]
    pub fn is_black(&self) -> bool {
        self.link.parent_color.color() == Color::Black
    }

    #[inline(always)]
    pub fn is_red(&self) -> bool {
        self.link.parent_color.color() == Color::Red
    }

    #[inline(always)]
    pub fn color(&self) -> Color {
        if self.is_black() {
            Color::Black
        } else {
            Color::Red
        }
    }

    #[inline(always)]
    pub fn left_deepest_node(&self) -> NonNull<Node<K, V>> {
        let mut node = self;
        while let Some(next) = node.left().or(node.right()) {
            // SAFETY: by if guard, next is never null.
            node = unsafe { next.as_ref() };
        }
        self.into()
    }

    /// # Safety
    ///
    /// This should not be called on null ptrs.
    #[inline(always)]
    pub unsafe fn link(node: *mut Self, parent: *mut Node<K, V>, direction: ComingFrom) {
        // SAFETY: link delegates the safety of this call to the caller.
        // `node`/`parent` are guaranteed not null by the caller.
        unsafe {
            let node = NonNull::new(node).expect("node pointer should be valid");
            let parent = NonNull::new(parent).expect("parent pointer should be valid");
            Link::link(Node::link_ptr(node), Node::link_ptr(parent), direction);
        }
    }

    #[inline(always)]
    pub fn next(&self) -> NodePtr<Node<K, V>> {
        // SAFETY: self is a live Node<K, V>.
        unsafe { Link::next(Node::link_ptr(NonNull::from(self))) }.map(Node::from_link)
    }

    #[inline(always)]
    pub fn parent(&self) -> NodePtr<Node<K, V>> {
        // SAFETY: self is a live Node<K, V>.
        unsafe { Link::parent(Node::link_ptr(NonNull::from(self))) }.map(Node::from_link)
    }

    #[inline(always)]
    pub fn prev(&self) -> NodePtr<Node<K, V>> {
        // SAFETY: self is a live Node<K, V>.
        unsafe { Link::prev(Node::link_ptr(NonNull::from(self))) }.map(Node::from_link)
    }

    /// This is technically [`Self::parent()`] but doesn't reset the color bit.
    #[inline(always)]
    pub fn red_parent(&self) -> NodePtr<Node<K, V>> {
        // SAFETY: self is a live Node<K, V>.
        unsafe { Link::red_parent(Node::link_ptr(NonNull::from(self))) }.map(Node::from_link)
    }

    /// The node's left child.
    #[inline(always)]
    pub fn left(&self) -> NodePtr<Node<K, V>> {
        // SAFETY: self is a live Node<K, V>.
        unsafe { Link::left(Node::link_ptr(NonNull::from(self))) }.map(Node::from_link)
    }

    /// The node's right child.
    #[inline(always)]
    pub fn right(&self) -> NodePtr<Node<K, V>> {
        // SAFETY: self is a live Node<K, V>.
        unsafe { Link::right(Node::link_ptr(NonNull::from(self))) }.map(Node::from_link)
    }

    #[inline(always)]
    pub(crate) fn set_parent(&mut self, parent: *mut Node<K, V>) {
        // SAFETY: self is a live Node<K, V>.
        unsafe {
            Link::set_parent(
                Node::link_ptr(NonNull::from(&mut *self)),
                Node::raw_link_ptr(parent),
            )
        };
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn set_parent_and_color(&mut self, parent: *mut Node<K, V>, color: Color) {
        // SAFETY: self is a live Node<K, V>.
        unsafe {
            Link::set_parent_and_color(
                Node::link_ptr(NonNull::from(&mut *self)),
                Node::raw_link_ptr(parent),
                color,
            )
        };
    }

    #[inline(always)]
    pub(crate) fn set_color(&mut self, color: Color) {
        // SAFETY: self is a live Node<K, V>.
        unsafe { Link::set_color(Node::link_ptr(NonNull::from(&mut *self)), color) };
    }

    #[inline(always)]
    pub(crate) fn set_parent_color(&mut self, parent_color: ParentColor<Node<K, V>>) {
        let link_pc = ParentColor::new(
            Node::raw_link_ptr(parent_color.parent()),
            parent_color.color(),
        );
        // SAFETY: self is a live Node<K, V>.
        unsafe { Link::set_parent_color(Node::link_ptr(NonNull::from(&mut *self)), link_pc) };
    }

    #[inline(always)]
    pub(crate) fn set_left(&mut self, left: NodePtr<Node<K, V>>) {
        // SAFETY: self is a live Node<K, V>.
        unsafe {
            Link::set_left(
                Node::link_ptr(NonNull::from(&mut *self)),
                left.map(Node::link_ptr),
            )
        };
    }

    #[inline(always)]
    pub(crate) fn set_right(&mut self, right: NodePtr<Node<K, V>>) {
        // SAFETY: self is a live Node<K, V>.
        unsafe {
            Link::set_right(
                Node::link_ptr(NonNull::from(&mut *self)),
                right.map(Node::link_ptr),
            )
        };
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub fn next_postorder(&self) -> NodePtr<Node<K, V>> {
        // SAFETY: by if guard, via op ?, parent is never None.
        let parent = unsafe { self.parent()?.as_ref() };
        if let (Some(left), Some(right)) = (parent.left(), parent.right()) {
            // If we're sitting on node, we've already seen our children
            // SAFETY: by if guard, both left and right are valid.
            unsafe {
                if std::ptr::eq(self, left.as_ref()) {
                    // If we are the parent's left node, go to the parent's right
                    // node then all the way down to the left
                    return Some(right.as_ref().left_deepest_node());
                }
            }
        }
        self.into()
    }
}

impl<K, V> Debug for Node<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{:?}::({:?},{:?})",
            self.color(),
            self.key,
            self.value
        ))
    }
}
