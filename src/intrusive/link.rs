use crate::{NodePtr, ParentColor};

/// An embeddable red-black tree link.
///
/// Unlike [`crate::Node`], a `Link` carries no data of its own. It is meant
/// to be embedded as a plain field (at any position, even more than once)
/// inside an arbitrary caller-defined struct, mirroring the Linux kernel's
/// `struct rb_node`. Pair it with an [`Adapter`](super::Adapter) (see
/// [`crate::intrusive_adapter!`]) to let a tree navigate from a `Link` back
/// to the struct that embeds it.
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
}

impl Default for Link {
    fn default() -> Self {
        Self::new()
    }
}
