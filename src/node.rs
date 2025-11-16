use std::{fmt::Debug, ptr::NonNull};

use crate::ComingFrom;

use super::{Color, Node, NodePtr, NodePtrExt, ParentColor};

// Public API.
impl<K, V> Node<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Node {
            parent_color: ParentColor::null(),
            right: None,
            left: None,
            key,
            value,
        }
    }

    #[inline(always)]
    pub fn is_black(&self) -> bool {
        self.parent_color.color() == Color::Black
    }

    #[inline(always)]
    pub fn is_red(&self) -> bool {
        self.parent_color.color() == Color::Red
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
        while let Some(next) = node.left.or(node.right) {
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
        // SAFETY: node is guaranteed not null by the caller, but we still can't
        // [1] get a &mut to parent until we finish from [2] assigning
        // parent_color. Thanks miri.
        let node = unsafe { node.as_mut().expect("node pointer should be valid") };
        node.parent_color = ParentColor::new(parent, Color::Red); // [2] assigning parent_color
        node.left = None;
        node.right = None;
        // [1] get a &mut parent
        let parent = unsafe { parent.as_mut().expect("parent pointer should be valid") };
        match direction {
            ComingFrom::Left => parent.left = node.into(),
            ComingFrom::Right => parent.right = node.into(),
        };
    }

    #[inline(always)]
    pub fn next(&self) -> NodePtr<K, V> {
        // If we have a right-hand child, go down and then left as far as we
        // can.
        if let Some(mut current) = self.right {
            // SAFETY: by if guard, current is valid.
            // SAFETY: current.as_ref is no longer in use.
            while let Some(left) = unsafe { current.as_ref() }.left {
                current = left;
            }
            return Some(current);
        }
        // No right-hand children. Everything down and left is smaller than us,
        // so any 'next' node must be in the general direction of our parent.
        //
        // [1] Go up the tree
        //     [2] any time the ancestor is a right-hand child of its parent,
        //         keep going up.
        //     [3] First time it's a left-hand child of its parent, [4] said
        //         parent is our 'next' node.
        let mut node_ref = self;
        let mut parent;
        loop {
            parent = node_ref.parent();
            if parent.is_none() {
                break; // [5] parent can never be null;
            }

            if parent // [3] first time it's a left-hand child of its parent.
                .right()
                .map(|p| !std::ptr::eq(node_ref, p.as_ptr()))
                .unwrap_or(true)
            {
                break; // [4] said parent is our 'next' node.
            }

            // [2] ancestor is a right-hand child of its parent, keep going up.
            // SAFETY: by construction, [5] parent can never be null.
            node_ref = unsafe { parent.unwrap().as_ref() };
        }
        parent
    }

    #[inline(always)]
    pub fn parent(&self) -> NodePtr<K, V> {
        NonNull::new(self.parent_color.parent())
    }

    #[inline(always)]
    pub fn prev(&self) -> NodePtr<K, V> {
        // If we have a left-hand child, go down and then right as far as we
        // can.
        if let Some(mut current) = self.left {
            // SAFETY: by construction, current is valid.
            while let Some(right) = unsafe { current.as_ref() }.right {
                current = right;
            }
            return Some(current);
        }

        // No left-hand children. Everything down and left is smaller than us,
        // so any 'next' node must be in the general direction of our parent.
        //
        // [1] Go up the tree
        //     [2] any time the ancestor is a left-hand child of its parent,
        //         keep going up.
        //     [3] First time it's a right-hand child of its parent, [4] said
        //         parent is our 'next' node.
        let mut node_ref = self;
        let mut parent;
        loop {
            parent = node_ref.parent();
            if parent.is_none() {
                break; // [5] when parent is none, we just [6] return.
            }

            if parent // [3] first time it's a left-hand child of its parent.
                .left()
                .map(|p| !std::ptr::eq(node_ref, p.as_ptr()))
                .unwrap_or(true)
            {
                break; // [4] said parent is our 'next' node, [6] return.
            }

            // [2] ancestor is a right-hand child of its parent, keep going up.
            // SAFETY: by construction, [5] parent can never be None.
            node_ref = unsafe { parent.unwrap().as_ref() };
        }
        parent // [6] return
    }

    /// This is technically [`Self::parent()`] but doesn't reset the color bit.
    #[inline(always)]
    pub fn red_parent(&self) -> NodePtr<K, V> {
        NonNull::new(self.parent_color.raw())
    }

    #[inline(always)]
    pub(crate) fn set_parent(&mut self, parent: *mut Node<K, V>) {
        self.parent_color.set_parent(parent);
    }

    #[inline(always)]
    pub(crate) fn set_parent_and_color(&mut self, parent: *mut Node<K, V>, color: Color) {
        self.parent_color = ParentColor::new(parent, color);
    }

    #[inline(always)]
    pub(crate) fn set_color(&mut self, color: Color) {
        self.parent_color.set_color(color);
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub fn next_postorder(&self) -> NodePtr<K, V> {
        // SAFETY: by if guard, via op ?, parent is never None.
        let parent = unsafe { self.parent()?.as_ref() };
        if let (Some(left), Some(right)) = (parent.left, parent.right) {
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
