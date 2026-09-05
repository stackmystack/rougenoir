use std::ptr::{self, NonNull};

use crate::{Color, ComingFrom, NodePtr, NodePtrExt, NodePtrImplExt, ParentColor};

use super::Link;

// Every accessor below goes through `Link`'s raw-pointer-based associated
// functions rather than `NonNull::as_ref`/`as_mut`. See the note on `Link`
// for why: a reference derived from a `NonNull<Link>` is only ever valid for
// `size_of::<Link>()` bytes, and these pointers get widened back out to
// their containing struct by `Adapter::get_value`. Narrowing them through
// an intermediate reference first is unsound (and is exactly what Miri catches).
impl NodePtrExt for NodePtr<Link> {
    type Node = Link;

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
        // SAFETY: any Some(link) here points at a live Link.
        self.is_some_and(|v| unsafe { Link::is_red(v) })
    }

    #[inline(always)]
    unsafe fn link(&mut self, parent: *mut Self::Node, direction: ComingFrom) {
        // SAFETY: delegated to the caller.
        self.map(|v| unsafe {
            Link::link(
                v,
                NonNull::new(parent).expect("parent pointer should be valid"),
                direction,
            )
        });
    }

    #[inline(always)]
    fn next_node(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(link) here points at a live Link.
        self.and_then(|v| unsafe { Link::next(v) })
    }

    #[inline(always)]
    fn parent(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(link) here points at a live Link.
        self.and_then(|v| unsafe { Link::parent(v) })
    }

    #[inline(always)]
    fn prev_node(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(link) here points at a live Link.
        self.and_then(|v| unsafe { Link::prev(v) })
    }

    #[inline(always)]
    fn ptr(&self) -> *mut Self::Node {
        self.map_or(ptr::null_mut(), |p| p.as_ptr())
    }

    #[inline(always)]
    fn left(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(link) here points at a live Link.
        self.and_then(|v| unsafe { Link::left(v) })
    }

    #[inline(always)]
    fn right(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(link) here points at a live Link.
        self.and_then(|v| unsafe { Link::right(v) })
    }
}

impl NodePtrImplExt for NodePtr<Link> {
    type Node = Link;

    #[inline(always)]
    unsafe fn mut_ref(&mut self) -> &mut Self::Node {
        self.map(|mut v| unsafe { v.as_mut() }).unwrap()
    }

    #[inline(always)]
    fn red_parent(&self) -> NodePtr<Self::Node> {
        // SAFETY: any Some(link) here points at a live Link.
        self.and_then(|v| unsafe { Link::red_parent(v) })
    }

    #[inline(always)]
    fn set_color(&mut self, color: Color) {
        if let Some(node) = self {
            // SAFETY: node points at a live Link.
            unsafe { Link::set_color(*node, color) };
        }
    }

    #[inline(always)]
    fn set_parent(&mut self, parent: *mut Self::Node) {
        if let Some(node) = self {
            // SAFETY: node points at a live Link.
            unsafe { Link::set_parent(*node, parent) };
        }
    }

    #[inline(always)]
    fn set_parent_and_color(&mut self, parent: *mut Self::Node, color: Color) {
        if let Some(node) = self {
            // SAFETY: node points at a live Link.
            unsafe { Link::set_parent_and_color(*node, parent, color) };
        }
    }

    #[inline(always)]
    fn set_parent_color(&mut self, parent_color: ParentColor<Link>) {
        if let Some(node) = self {
            // SAFETY: node points at a live Link.
            unsafe { Link::set_parent_color(*node, parent_color) };
        }
    }

    #[inline(always)]
    fn set_left(&mut self, left: NodePtr<Self::Node>) {
        if let Some(node) = self {
            // SAFETY: node points at a live Link.
            unsafe { Link::set_left(*node, left) };
        }
    }

    #[inline(always)]
    fn set_right(&mut self, right: NodePtr<Self::Node>) {
        if let Some(node) = self {
            // SAFETY: node points at a live Link.
            unsafe { Link::set_right(*node, right) };
        }
    }
}
