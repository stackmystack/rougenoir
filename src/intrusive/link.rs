use std::ptr::{self, NonNull};

use crate::{Color, ComingFrom, NodePtr, ParentColor};

/// An embeddable red-black tree link.
///
/// Unlike [`crate::Node`], a `Link` carries no data of its own. It is meant
/// to be embedded as a plain field (at any position, even more than once)
/// inside an arbitrary caller-defined struct, mirroring the Linux kernel's
/// `struct rb_node`. Pair it with an [`Adapter`](super::Adapter) (see
/// [`crate::intrusive_adapter!`]) to let a tree navigate from a `Link` back
/// to the struct that embeds it.
///
/// # A note on the unsafe associated functions below
///
/// Every structural operation here takes `NonNull<Link>` rather than
/// `&self`/`&mut self`, and reads/writes fields via [`ptr::addr_of!`]/
/// [`ptr::addr_of_mut!`] instead of going through a reference. This is
/// deliberate: a `Link` is always narrower than the struct that embeds it,
/// and [`Adapter::get_value`](super::Adapter::get_value) later widens a
/// `Link` pointer back out to that whole struct. Under Stacked Borrows, a
/// pointer derived from a `&Link`/`&mut Link` reference is only ever valid
/// for `size_of::<Link>()` bytes, so storing such a pointer (e.g. into a
/// sibling's `left`/`right`) and later widening it via `get_value` is
/// undefined behavior, caught by Miri. Staying in raw-pointer land end to
/// end (no reference ever gets created, so provenance never narrows) avoids
/// this.
#[repr(C)]
pub struct Link {
    pub(crate) parent_color: ParentColor<Link>,
    pub(crate) left: NodePtr<Link>,
    pub(crate) right: NodePtr<Link>,
}

impl Link {
    /// Creates a new, unlinked `Link`.
    pub fn new() -> Self {
        Link {
            parent_color: ParentColor::null(),
            left: None,
            right: None,
        }
    }

    /// Returns `true` if this link's local state shows no trace of tree
    /// membership.
    ///
    /// This is a best-effort, local check: a lone root node also has no
    /// parent and no children, so this can't distinguish "never linked"
    /// from "linked, but as the sole node of its tree". It reliably reports
    /// `true` right after [`Link::new`], and `false` once a link has ever
    /// gained a parent or a child.
    pub fn is_unlinked(&self) -> bool {
        self.parent_color.parent().is_null() && self.left.is_none() && self.right.is_none()
    }

    /// # Safety
    /// `link` must be valid for reads.
    #[inline(always)]
    unsafe fn read_parent_color(link: NonNull<Link>) -> ParentColor<Link> {
        // SAFETY: delegated to the caller; `addr_of!` projects a field
        // pointer without requiring (or creating) a reference to the whole
        // `Link`, so this doesn't narrow the provenance of `link`.
        unsafe { ptr::read(ptr::addr_of!((*link.as_ptr()).parent_color)) }
    }

    /// # Safety
    /// `link` must be valid for writes.
    #[inline(always)]
    unsafe fn write_parent_color(link: NonNull<Link>, value: ParentColor<Link>) {
        // SAFETY: see `read_parent_color`.
        unsafe { ptr::write(ptr::addr_of_mut!((*link.as_ptr()).parent_color), value) }
    }

    /// # Safety
    /// `link` must be valid for reads.
    #[inline(always)]
    unsafe fn read_left(link: NonNull<Link>) -> NodePtr<Link> {
        // SAFETY: see `read_parent_color`.
        unsafe { ptr::read(ptr::addr_of!((*link.as_ptr()).left)) }
    }

    /// # Safety
    /// `link` must be valid for writes.
    #[inline(always)]
    unsafe fn write_left(link: NonNull<Link>, value: NodePtr<Link>) {
        // SAFETY: see `read_parent_color`.
        unsafe { ptr::write(ptr::addr_of_mut!((*link.as_ptr()).left), value) }
    }

    /// # Safety
    /// `link` must be valid for reads.
    #[inline(always)]
    unsafe fn read_right(link: NonNull<Link>) -> NodePtr<Link> {
        // SAFETY: see `read_parent_color`.
        unsafe { ptr::read(ptr::addr_of!((*link.as_ptr()).right)) }
    }

    /// # Safety
    /// `link` must be valid for writes.
    #[inline(always)]
    unsafe fn write_right(link: NonNull<Link>, value: NodePtr<Link>) {
        // SAFETY: see `read_parent_color`.
        unsafe { ptr::write(ptr::addr_of_mut!((*link.as_ptr()).right), value) }
    }

    // --- Structural operations, all raw-pointer based. ---

    /// # Safety
    /// `link` must be valid for reads.
    #[inline(always)]
    pub unsafe fn is_red(link: NonNull<Link>) -> bool {
        // SAFETY: delegated to the caller.
        unsafe { Self::read_parent_color(link) }.color() == Color::Red
    }

    /// Links `node` as a child of `parent`, in the direction `direction`.
    ///
    /// This is the BST-insertion half of a red-black insert: it does not
    /// rebalance. Follow it with [`crate::intrusive::Root::insert`].
    ///
    /// # Safety
    ///
    /// `node` and `parent` must point at live, distinct `Link`s.
    #[inline(always)]
    pub unsafe fn link(node: NonNull<Link>, parent: NonNull<Link>, direction: ComingFrom) {
        // SAFETY: delegated to the caller.
        unsafe {
            Self::write_parent_color(node, ParentColor::new(parent.as_ptr(), Color::Red));
            match direction {
                ComingFrom::Left => {
                    Self::write_left(parent, Some(node));
                    Self::write_right(node, None);
                }
                ComingFrom::Right => {
                    Self::write_left(node, None);
                    Self::write_right(parent, Some(node));
                }
            }
        }
    }

    /// # Safety
    /// `link` must be valid for reads, as must every link reachable from it.
    #[inline(always)]
    pub unsafe fn next(link: NonNull<Link>) -> NodePtr<Link> {
        // SAFETY: delegated to the caller for the whole traversal below.
        unsafe {
            // If we have a right-hand child, go down and then left as far as
            // we can.
            if let Some(mut current) = Self::read_right(link) {
                while let Some(left) = Self::read_left(current) {
                    current = left;
                }
                return Some(current);
            }
            // No right-hand children. Everything down and left is smaller
            // than us, so any 'next' node must be in the general direction
            // of our parent.
            //
            // [1] Go up the tree
            //     [2] any time the ancestor is a right-hand child of its
            //         parent, keep going up.
            //     [3] First time it's a left-hand child of its parent, [4]
            //         said parent is our 'next' node.
            let mut node = link;
            let mut parent;
            loop {
                parent = Self::parent(node);
                let Some(p) = parent else {
                    break; // [5] parent can never be null;
                };
                if Self::read_right(p).map(|r| r != node).unwrap_or(true) {
                    break; // [4] said parent is our 'next' node.
                }
                // [2] ancestor is a right-hand child of its parent, keep
                // going up.
                node = p;
            }
            parent
        }
    }

    /// # Safety
    /// `link` must be valid for reads.
    #[inline(always)]
    pub unsafe fn parent(link: NonNull<Link>) -> NodePtr<Link> {
        // SAFETY: delegated to the caller.
        NonNull::new(unsafe { Self::read_parent_color(link) }.parent())
    }

    /// # Safety
    /// `link` must be valid for reads, as must every link reachable from it.
    #[inline(always)]
    pub unsafe fn prev(link: NonNull<Link>) -> NodePtr<Link> {
        // SAFETY: delegated to the caller for the whole traversal below.
        unsafe {
            // If we have a left-hand child, go down and then right as far as
            // we can.
            if let Some(mut current) = Self::read_left(link) {
                while let Some(right) = Self::read_right(current) {
                    current = right;
                }
                return Some(current);
            }

            let mut node = link;
            let mut parent;
            loop {
                parent = Self::parent(node);
                let Some(p) = parent else {
                    break; // [5] when parent is none, we just [6] return.
                };
                if Self::read_left(p).map(|l| l != node).unwrap_or(true) {
                    break; // [4] said parent is our 'next' node, [6] return.
                }
                node = p;
            }
            parent // [6] return
        }
    }

    /// This is technically [`Self::parent`] but doesn't reset the color bit.
    ///
    /// # Safety
    /// `link` must be valid for reads.
    #[inline(always)]
    pub(crate) unsafe fn red_parent(link: NonNull<Link>) -> NodePtr<Link> {
        // SAFETY: delegated to the caller.
        NonNull::new(unsafe { Self::read_parent_color(link) }.raw())
    }

    /// # Safety
    /// `link` must be valid for writes.
    #[inline(always)]
    pub(crate) unsafe fn set_parent(link: NonNull<Link>, parent: *mut Link) {
        // SAFETY: delegated to the caller.
        unsafe {
            let mut pc = Self::read_parent_color(link);
            pc.set_parent(parent);
            Self::write_parent_color(link, pc);
        }
    }

    /// # Safety
    /// `link` must be valid for writes.
    #[inline(always)]
    pub(crate) unsafe fn set_parent_and_color(
        link: NonNull<Link>,
        parent: *mut Link,
        color: Color,
    ) {
        // SAFETY: delegated to the caller.
        unsafe { Self::write_parent_color(link, ParentColor::new(parent, color)) }
    }

    /// # Safety
    /// `link` must be valid for writes.
    #[inline(always)]
    pub(crate) unsafe fn set_color(link: NonNull<Link>, color: Color) {
        // SAFETY: delegated to the caller.
        unsafe {
            let mut pc = Self::read_parent_color(link);
            pc.set_color(color);
            Self::write_parent_color(link, pc);
        }
    }

    /// # Safety
    /// `link` must be valid for reads.
    #[inline(always)]
    pub unsafe fn left(link: NonNull<Link>) -> NodePtr<Link> {
        // SAFETY: delegated to the caller.
        unsafe { Self::read_left(link) }
    }

    /// # Safety
    /// `link` must be valid for writes.
    #[inline(always)]
    pub(crate) unsafe fn set_left(link: NonNull<Link>, left: NodePtr<Link>) {
        // SAFETY: delegated to the caller.
        unsafe { Self::write_left(link, left) }
    }

    /// # Safety
    /// `link` must be valid for reads.
    #[inline(always)]
    pub unsafe fn right(link: NonNull<Link>) -> NodePtr<Link> {
        // SAFETY: delegated to the caller.
        unsafe { Self::read_right(link) }
    }

    /// # Safety
    /// `link` must be valid for writes.
    #[inline(always)]
    pub(crate) unsafe fn set_right(link: NonNull<Link>, right: NodePtr<Link>) {
        // SAFETY: delegated to the caller.
        unsafe { Self::write_right(link, right) }
    }

    /// # Safety
    /// `link` must be valid for writes.
    #[inline(always)]
    pub(crate) unsafe fn set_parent_color(link: NonNull<Link>, parent_color: ParentColor<Link>) {
        // SAFETY: delegated to the caller.
        unsafe { Self::write_parent_color(link, parent_color) }
    }

    /// # Safety
    /// `link` must be valid for reads.
    #[inline(always)]
    pub(crate) unsafe fn parent_color(link: NonNull<Link>) -> ParentColor<Link> {
        // SAFETY: delegated to the caller.
        unsafe { Self::read_parent_color(link) }
    }
}

impl Default for Link {
    fn default() -> Self {
        Self::new()
    }
}
