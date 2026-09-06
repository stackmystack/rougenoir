use std::ptr;

use crate::{Color, NodePtr, ParentColor};

use super::Link;

/// `None`-propagating navigation on a bare `NodePtr<Link>` (`Option<NonNull<Link>>`).
///
/// This exists for [`super::Root`]'s Case 1–4 rebalancing algorithm, which is a
/// direct port of the kernel's `rbtree.c` and is written throughout in terms of
/// `struct rb_node *`-shaped locals that may be null at any point (`tmp`,
/// `parent`, `successor`, ...). The kernel leans on C's implicit null-pointer
/// handling for exactly this, and this trait is what lets the port read the
/// same way instead of wrapping every one of those call sites in `if let
/// Some(x) = ...`.
///
/// This is deliberately **not** the public API for navigating a `Link`: a
/// caller that already has a live `NonNull<Link>` (as every consumer does; see
/// `RawIter`) should call [`Link::left`]/[`Link::right`]/etc. directly, the
/// same way [`super::Adapter`]'s methods do. Consolidating those with this
/// trait would mean either giving the engine's internals a public, safe-looking
/// surface with the same live-pointer precondition `Adapter` correctly marks
/// `unsafe fn` for (the original problem), or making `Adapter` itself deal in
/// bare, possibly-null `Option`s it has no reason to know about.
pub(crate) trait LinkPtrExt {
    fn is_black(&self) -> bool;
    fn is_red(&self) -> bool;
    fn left_node(&self) -> NodePtr<Link>;
    fn right_node(&self) -> NodePtr<Link>;
    fn parent_node(&self) -> NodePtr<Link>;
    fn ptr(&self) -> *mut Link;
}

/// The mutating counterpart to [`LinkPtrExt`], same rationale: crate-internal
/// vocabulary for the rebalancing engine, not a public API. Calling these on an
/// already-linked node directly (instead of through
/// [`super::Root::insert`]/[`super::Root::erase`]) bypasses rebalancing
/// entirely and silently corrupts the tree's red-black invariants — there is no
/// sanctioned external use for them.
pub(crate) trait LinkPtrMut {
    fn red_parent(&self) -> NodePtr<Link>;
    fn set_color(&mut self, color: Color);
    fn set_left(&mut self, left: NodePtr<Link>);
    fn set_parent(&mut self, parent: *mut Link);
    fn set_parent_and_color(&mut self, parent: *mut Link, color: Color);
    fn set_parent_color(&mut self, parent_color: ParentColor<Link>);
    fn set_right(&mut self, right: NodePtr<Link>);
}

// Every accessor below goes through `Link`'s raw-pointer-based associated
// functions rather than `NonNull::as_ref`/`as_mut`. See the note on `Link` for
// why: a reference derived from a `NonNull<Link>` is only ever valid for
// `size_of::<Link>()` bytes, and these pointers get widened back out to their
// containing struct by `Adapter::get_value`. Narrowing them through an
// intermediate reference first is unsound (and is exactly what Miri catches).
impl LinkPtrExt for NodePtr<Link> {
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
    fn parent_node(&self) -> NodePtr<Link> {
        // SAFETY: any Some(link) here points at a live Link.
        self.and_then(|v| unsafe { Link::parent(v) })
    }

    #[inline(always)]
    fn ptr(&self) -> *mut Link {
        self.map_or(ptr::null_mut(), |p| p.as_ptr())
    }

    #[inline(always)]
    fn left_node(&self) -> NodePtr<Link> {
        // SAFETY: any Some(link) here points at a live Link.
        self.and_then(|v| unsafe { Link::left(v) })
    }

    #[inline(always)]
    fn right_node(&self) -> NodePtr<Link> {
        // SAFETY: any Some(link) here points at a live Link.
        self.and_then(|v| unsafe { Link::right(v) })
    }
}

impl LinkPtrMut for NodePtr<Link> {
    #[inline(always)]
    fn red_parent(&self) -> NodePtr<Link> {
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
    fn set_parent(&mut self, parent: *mut Link) {
        if let Some(node) = self {
            // SAFETY: node points at a live Link.
            unsafe { Link::set_parent(*node, parent) };
        }
    }

    #[inline(always)]
    fn set_parent_and_color(&mut self, parent: *mut Link, color: Color) {
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
    fn set_left(&mut self, left: NodePtr<Link>) {
        if let Some(node) = self {
            // SAFETY: node points at a live Link.
            unsafe { Link::set_left(*node, left) };
        }
    }

    #[inline(always)]
    fn set_right(&mut self, right: NodePtr<Link>) {
        if let Some(node) = self {
            // SAFETY: node points at a live Link.
            unsafe { Link::set_right(*node, right) };
        }
    }
}
