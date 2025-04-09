use std::{fmt::Debug, ptr::NonNull};

use super::{Color, Node, NodePtr, NodePtrExt};

// Public API.
impl<K, V> Node<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Node {
            parent_color: 0,
            right: None,
            left: None,
            key,
            value,
        }
    }

    #[inline(always)]
    pub fn is_black(&self) -> bool {
        Self::parent_color(self.parent_color) == Color::Black
    }

    #[inline(always)]
    pub fn is_red(&self) -> bool {
        Self::parent_color(self.parent_color) == Color::Red
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
    pub fn left_deepest_node(&self) -> NodePtr<K, V> {
        let mut node = self;
        while let Some(next) = node.left.or(node.right) {
            node = unsafe { next.as_ref() };
        }
        Some(node.into())
    }

    #[inline(always)]
    pub fn link(&mut self, parent: NonNull<Node<K, V>>, link: &mut NodePtr<K, V>) -> usize {
        self.parent_color = parent.as_ptr() as usize;
        self.left = None;
        self.right = None;
        *link = Some(self.into());
        self.parent_color
    }

    #[inline(always)]
    pub fn next(&self) -> NodePtr<K, V> {
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
        let mut node_ref = self;
        let mut parent;
        loop {
            parent = node_ref.parent();
            if parent.is_none() {
                break;
            }
            if parent
                .right()
                .map(|p| node_ref as *const Node<K, V> != p.as_ptr())
                .unwrap_or(true)
            {
                break;
            }
            node_ref = unsafe { parent.unwrap().as_ref() };
        }
        parent
    }

    #[inline(always)]
    pub fn parent(&self) -> NodePtr<K, V> {
        NonNull::new((self.parent_color & !3) as *mut Node<K, V>)
    }

    #[inline(always)]
    pub fn from_parent_color(parent_color: usize) -> NodePtr<K, V> {
        NonNull::new((parent_color & !3) as *mut Node<K, V>)
    }

    #[inline(always)]
    pub fn parent_color(parent_color: usize) -> Color {
        Color::from(parent_color & 1)
    }

    #[inline(always)]
    pub fn prev(&self) -> NodePtr<K, V> {
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
        let mut node_ref = self;
        let mut parent;
        loop {
            parent = node_ref.parent();
            if parent.is_none() {
                break;
            }
            if parent
                .left()
                .map(|p| node_ref as *const Node<K, V> != p.as_ptr())
                .unwrap_or(true)
            {
                break;
            }
            node_ref = unsafe { parent.unwrap().as_ref() };
        }
        parent
    }

    /// This is technically [`Self::parent()`] but doesn't reset the color bit.
    #[inline(always)]
    pub fn red_parent(&self) -> NodePtr<K, V> {
        NonNull::new(self.parent_color as *mut Node<K, V>)
    }

    #[inline(always)]
    pub fn set_parent(&mut self, parent: NodePtr<K, V>) {
        self.parent_color = self.color() as usize + parent.ptr_value();
    }

    #[inline(always)]
    pub fn set_parent_and_color(&mut self, parent: NodePtr<K, V>, color: Color) {
        self.parent_color = color as usize + parent.ptr_value();
    }

    #[inline(always)]
    pub fn set_color(&mut self, color: Color) {
        self.parent_color = color as usize + self.parent().ptr_value();
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub fn clean(&mut self) {
        self.parent_color = self as *const _ as usize;
        self.right = None;
        self.left = None;
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub fn next_postorder(&self) -> NodePtr<K, V> {
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
