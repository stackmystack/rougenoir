use std::ptr::NonNull;

use super::{Color, Node, NodePtr, NodePtrExt};

// Public API.
impl<K, V> Node<K, V> {
    pub(crate) fn new(key: K, value: V) -> Self {
        Node {
            parent_color: 0,
            right: None,
            left: None,
            key,
            value,
        }
    }

    #[inline(always)]
    pub(crate) fn is_black(&self) -> bool {
        Self::parent_color(self.parent_color) == Color::Black
    }

    /// 'empty' nodes are nodes that are known not to be inserted in an rbtree
    #[inline(always)]
    pub(crate) fn is_empty(&self) -> bool {
        self.parent_color == self as *const _ as usize
    }

    #[inline(always)]
    pub(crate) fn is_red(&self) -> bool {
        Self::parent_color(self.parent_color) == Color::Red
    }

    #[inline(always)]
    pub(crate) fn color(&self) -> Color {
        if self.is_black() {
            Color::Black
        } else {
            Color::Red
        }
    }

    pub(crate) fn left_deepest_node(&self) -> NodePtr<K, V> {
        let mut node = self;
        while let Some(next) = node.left.or(node.right) {
            node = unsafe { next.as_ref() };
        }
        Some(node.into())
    }

    pub(crate) fn next(&self) -> NodePtr<K, V> {
        /*
         * If we have a right-hand child, go down and then left as far
         * as we can.
         */
        if let Some(mut current) = self.right {
            while let Some(left) = unsafe { current.as_ref() }.left {
                current = left;
            }
            return Some(current);
        }
        /*
         * No right-hand children. Everything down and left is smaller than us,
         * so any 'next' node must be in the general direction of our parent.
         * Go up the tree; any time the ancestor is a right-hand child of its
         * parent, keep going up. First time it's a left-hand child of its
         * parent, said parent is our 'next' node.
         */
        let mut current = self;
        while let Some(parent) = current.parent() {
            if unsafe { parent.as_ref() }.right.is_some() {
                return Some(parent);
            }
            current = unsafe { parent.as_ref() };
        }
        None
    }

    #[inline(always)]
    pub(crate) fn parent(&self) -> NodePtr<K, V> {
        NonNull::new((self.parent_color & !3) as *mut Node<K, V>)
    }

    #[inline(always)]
    pub(crate) fn from_color(parent_color: usize) -> NodePtr<K, V> {
        NonNull::new((parent_color & !3) as *mut Node<K, V>)
    }

    #[inline(always)]
    pub(crate) fn parent_color(parent_color: usize) -> Color {
        Color::from(parent_color & 1)
    }

    pub(crate) fn prev(&self) -> NodePtr<K, V> {
        /*
         * If we have a left-hand child, go down and then right as far
         * as we can.
         */
        if let Some(mut current) = self.left {
            while let Some(right) = unsafe { current.as_ref() }.right {
                current = right;
            }
            return Some(current);
        }

        /*
         * No left-hand children. Go up till we find an ancestor which
         * is a right-hand child of its parent.
         */
        let mut current = self;
        while let Some(parent) = current.parent() {
            if unsafe { parent.as_ref() }.left.is_some() {
                return Some(parent);
            }
            current = unsafe { parent.as_ref() };
        }
        None
    }

    /// This is technically [`Self::parent()`] but doesn't reset the color bit.
    #[inline(always)]
    pub(crate) fn red_parent(&self) -> NodePtr<K, V> {
        NonNull::new(self.parent_color as *mut Node<K, V>)
    }

    #[inline(always)]
    pub(crate) fn set_parent(&mut self, parent: NodePtr<K, V>) {
        self.parent_color = self.color() as usize + parent.ptr_value();
    }

    #[inline(always)]
    pub(crate) fn set_parent_and_color(&mut self, parent: NodePtr<K, V>, color: Color) {
        self.parent_color = color as usize + parent.ptr_value();
    }
}

// Internal API.
impl<K, V> Node<K, V> {
    #[inline(always)]
    fn clean(&mut self) {
        self.parent_color = self as *const _ as usize;
        self.right = None;
        self.left = None;
    }

    #[inline(always)]
    fn set_black(&mut self) {
        self.parent_color += Color::Black as usize;
    }

    fn next_postorder(&self) -> NodePtr<K, V> {
        let parent = unsafe { self.parent()?.as_ref() };
        if let (Some(left), Some(right)) = (parent.left, parent.right) {
            /* If we're sitting on node, we've already seen our children */
            if std::ptr::eq(self, unsafe { left.as_ref() }) {
                /* If we are the parent's left node, go to the parent's right
                 * node then all the way down to the left */
                return unsafe { right.as_ref() }.left_deepest_node();
            }
        }
        Some(parent.into())
    }
}
