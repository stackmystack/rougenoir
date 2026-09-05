use std::{
    marker::PhantomData,
    ptr::{self, NonNull},
};

use crate::{Color, NodePtr, NodePtrExt, NodePtrImplExt};

use super::{Adapter, Link, TreeCallbacks};

/// The root of an intrusive red-black tree of `A::Value`s.
///
/// This is the [`crate::Root`] of the low-level [`crate::intrusive`] API: it
/// carries no allocation of its own (it never owns the `A::Value`s inserted
/// into it, mirroring the Linux kernel's `struct rb_root`) and has no
/// built-in notion of ordering.
///
/// As with [`crate::Root`], the caller walks the tree themselves
/// (via [`NodePtrExt`]/[`Link`]'s methods) to find where a new node belongs,
/// links it in with [`Link::link`], and then calls [`Root::insert`] to rebalance.
pub struct Root<A: Adapter, C> {
    pub callbacks: C,
    pub node: NodePtr<Link>,
    _adapter: PhantomData<A>,
}

impl<A: Adapter, C: TreeCallbacks<Value = A::Value> + Default> Default for Root<A, C> {
    fn default() -> Self {
        Root::new(C::default())
    }
}

// Public
impl<A: Adapter, C: TreeCallbacks<Value = A::Value>> Root<A, C> {
    pub fn new(callbacks: C) -> Self {
        Root {
            callbacks,
            node: None,
            _adapter: PhantomData,
        }
    }

    pub fn erase(&mut self, node: NonNull<Link>) {
        let rebalance = self.erase_augmented(node);
        if rebalance.is_some() {
            self.erase_color(rebalance);
        }
    }

    pub fn insert(&mut self, node: NonNull<Link>) {
        let mut node: NodePtr<Link> = node.into();
        let mut parent = node.red_parent();
        let mut gparent;
        let mut tmp;

        loop {
            // Loop invariant: node is red.
            //
            // TODO: unlikely hint, but it's nightly only.
            if parent.is_none() {
                // The inserted node is root. Either this is the first node, or
                // we recursed at Case 1 below and are no longer violating 4).
                node.set_parent_and_color(ptr::null_mut(), Color::Black);
                break;
            }

            // If there is a black parent, we are done. Otherwise, take some
            // corrective action as, per 4), we don't want a red root or two
            // consecutive red nodes.
            if parent.is_black() {
                break;
            }

            gparent = parent.red_parent();
            tmp = gparent.right();

            if parent != tmp {
                // parent == gparent->rb_left
                if tmp.is_red() {
                    // Case 1 - node's uncle is red (color flips).
                    //
                    //       G            g
                    //      / \          / \
                    //     p   u  -->   P   U
                    //    /            /
                    //   n            n
                    //
                    // However, since g's parent might be red, and 4) does not
                    // allow this, we need to recurse at g.
                    tmp.set_parent_and_color(gparent.ptr(), Color::Black);
                    parent.set_parent_and_color(gparent.ptr(), Color::Black);
                    node = gparent;
                    parent = node.parent();
                    node.set_parent_and_color(parent.ptr(), Color::Red);
                    continue;
                }

                tmp = parent.right();
                if node == tmp {
                    // Case 2 - node's uncle is black and node is the parent's
                    // right child (left rotate at parent).
                    //
                    //      G             G
                    //     / \           / \
                    //    p   U  -->    n   U
                    //     \           /
                    //      n         p
                    //
                    // This still leaves us in violation of 4), the continuation
                    // into Case 3 will fix that.
                    tmp = node.left();
                    parent.set_right(tmp);
                    node.set_left(parent);
                    if tmp.is_some() {
                        tmp.set_parent_and_color(parent.ptr(), Color::Black);
                    }
                    parent.set_parent_and_color(node.ptr(), Color::Red);
                    self.callbacks
                        .rotate(Self::value(parent), Self::value(node));
                    parent = node;
                    tmp = node.right();
                }

                // Case 3 - node's uncle is black and node is
                // the parent's left child (right rotate at gparent).
                //
                //        G           P
                //       / \         / \
                //      p   U  -->  n   g
                //     /                 \
                //    n                   U
                gparent.set_left(tmp); /* == parent->rb_right */
                parent.set_right(gparent);
                if tmp.is_some() {
                    tmp.set_parent_and_color(gparent.ptr(), Color::Black);
                }
                self.rotate_set_parents(gparent, parent, Color::Red);
                self.callbacks
                    .rotate(Self::value(gparent), Self::value(parent));
                break;
            } else {
                tmp = gparent.left();
                if tmp.is_red() {
                    // Case 1 - color flips
                    tmp.set_parent_and_color(gparent.ptr(), Color::Black);
                    parent.set_parent_and_color(gparent.ptr(), Color::Black);
                    node = gparent;
                    parent = node.parent();
                    node.set_parent_and_color(parent.ptr(), Color::Red);
                    continue;
                }

                tmp = parent.left();
                if node == tmp {
                    // Case 2 - right rotate at parent
                    tmp = node.right();
                    parent.set_left(tmp);
                    node.set_right(parent);
                    if tmp.is_some() {
                        tmp.set_parent_and_color(parent.ptr(), Color::Black);
                    }
                    parent.set_parent_and_color(node.ptr(), Color::Red);
                    self.callbacks
                        .rotate(Self::value(parent), Self::value(node));
                    parent = node;
                    tmp = node.left();
                }

                // Case 3 - left rotate at gparent
                gparent.set_right(tmp); // == parent->rb_left
                parent.set_left(gparent);
                if tmp.is_some() {
                    tmp.set_parent_and_color(gparent.ptr(), Color::Black);
                }
                self.rotate_set_parents(gparent, parent, Color::Red);
                self.callbacks
                    .rotate(Self::value(gparent), Self::value(parent));
                break;
            }
        }
    }
}

/// Returns the leftmost (in-order first) link reachable from `node`.
///
/// Free function (rather than a `Root` method) so [`crate::Root`] can reuse
/// this exact traversal without needing to construct a whole intrusive
/// [`Root`] (which would require a [`TreeCallbacks`] value it has no use
/// for here).
pub(crate) fn first_of(node: NodePtr<Link>) -> NodePtr<Link> {
    let mut n = node?;
    // n can never be null here, by construction.
    while let Some(left) = Some(n).left() {
        n = left;
    }
    Some(n)
}

/// Returns the rightmost (in-order last) link reachable from `node`. See
/// [`first_of`].
pub(crate) fn last_of(node: NodePtr<Link>) -> NodePtr<Link> {
    let mut n = node?;
    // n is never null here, via the `?` above.
    while let Some(right) = Some(n).right() {
        n = right;
    }
    Some(n)
}

/// Checks the structural red-black invariant (every child's `parent()`
/// points back at its actual parent) starting from `node`. See
/// [`first_of`].
#[cfg(debug_assertions)]
#[allow(useless_ptr_null_checks)]
pub(crate) fn validate_of(node: NodePtr<Link>) -> bool {
    let mut current = first_of(node);
    let mut res = true;
    while let Some(c) = current {
        if c.as_ptr().is_null() {
            res = false;
            break;
        }
        let left = Some(c).left();
        let right = Some(c).right();
        if left.is_some() && left.parent() != current {
            res = false;
        }
        if right.is_some() && right.parent() != current {
            res = false;
        }
        if !res {
            return false;
        }
        current = Some(c).next_node();
    }

    res
}

#[cfg(debug_assertions)]
impl<A: Adapter, C> Root<A, C> {
    pub fn validate(&self) -> bool {
        validate_of(self.node)
    }
}

impl<A: Adapter, C> Root<A, C> {
    pub fn first(&self) -> NodePtr<Link> {
        first_of(self.node)
    }

    pub fn last(&self) -> NodePtr<Link> {
        last_of(self.node)
    }
}

// Private
impl<A: Adapter, C: TreeCallbacks<Value = A::Value>> Root<A, C> {
    /// Converts a link known (by the algorithm's own invariants) to be
    /// non-null into a pointer to the value that embeds it.
    #[inline(always)]
    fn value(link: NodePtr<Link>) -> NonNull<A::Value> {
        // SAFETY: every link ever stored in this tree was produced by
        // `A::get_link` from a live `A::Value`; callers only reach here
        // where the algorithm has already established `link` is Some.
        unsafe { A::get_value(link.expect("link pointer should be valid")) }
    }

    #[inline(always)]
    fn value_opt(link: NodePtr<Link>) -> Option<NonNull<A::Value>> {
        // SAFETY: see `value`.
        link.map(|l| unsafe { A::get_value(l) })
    }

    #[inline]
    fn erase_augmented(&mut self, node: NonNull<Link>) -> NodePtr<Link> {
        let mut child = Some(node).right();
        let mut tmp = Some(node).left();
        let mut parent;
        let rebalance;
        let pc;

        if tmp.is_none() {
            // Case 1: node to erase has no more than 1 child (easy!)
            //
            // Note that if there is one child it must be red due to 5) and node
            // must be black due to 4). We adjust colors locally so as to bypass
            // __rb_erase_color() later on.
            // SAFETY: node points at a live Link that is part of this tree.
            pc = unsafe { Link::parent_color(node) };
            parent = pc.non_null();
            self.change_child(node, child, parent);
            rebalance = if child.is_some() {
                child.set_parent_color(pc);
                None
            } else if pc.color() == Color::Black {
                parent
            } else {
                None
            };
            tmp = parent;
        } else if child.is_none() {
            // Still case 1, but this time the child is node->rb_left
            // SAFETY: node points at a live Link that is part of this tree.
            pc = unsafe { Link::parent_color(node) };
            tmp.set_parent_color(pc);
            parent = pc.non_null();
            self.change_child(node, tmp, parent);
            rebalance = None;
            tmp = parent;
        } else {
            let mut successor = child;
            let mut child2;

            tmp = child.left();
            if tmp.is_none() {
                // Case 2: node's successor is its right child
                //
                //    (n)          (s)
                //    / \          / \
                //  (x) (s)  ->  (x) (c)
                //        \
                //        (c)
                parent = successor;
                child2 = successor.right();
                self.callbacks
                    .copy(Self::value(Some(node)), Self::value(successor));
            } else {
                // Case 3: node's successor is leftmost under
                // node's right child subtree
                //
                //    (n)          (s)
                //    / \          / \
                //  (x) (y)  ->  (x) (y)
                //      /            /
                //    (p)          (p)
                //    /            /
                //  (s)          (c)
                //    \
                //    (c)
                loop {
                    parent = successor;
                    successor = tmp;
                    tmp = tmp.left();
                    if tmp.is_none() {
                        break;
                    }
                }
                child2 = successor.right();
                parent.set_left(child2);
                successor.set_right(child);
                child.set_parent(successor.ptr());

                self.callbacks
                    .copy(Self::value(Some(node)), Self::value(successor));
                self.callbacks
                    .propagate(Self::value_opt(parent), Self::value_opt(successor));
            }

            tmp = Some(node).left();
            successor.set_left(tmp);
            tmp.set_parent(successor.ptr());

            // SAFETY: node points at a live Link that is part of this tree.
            pc = unsafe { Link::parent_color(node) };
            tmp = pc.non_null();
            self.change_child(node, successor, tmp);
            rebalance = if child2.is_some() {
                child2.set_parent_and_color(parent.ptr(), Color::Black);
                None
            } else if successor.is_black() {
                parent
            } else {
                None
            };
            successor.set_parent_color(pc);
            tmp = successor;
        }

        self.callbacks.propagate(Self::value_opt(tmp), None);
        rebalance
    }

    /// Inline version for erase() use - we want to be able to inline
    /// and eliminate the [`super::callbacks::Noop::rotate`] callback there
    #[inline]
    fn erase_color(&mut self, mut parent: NodePtr<Link>) {
        let mut node = None;
        let mut sibling;
        let mut tmp1;
        let mut tmp2;

        loop {
            // Loop invariants:
            // - node is black (or NULL on first iteration)
            // - node is not the root (parent is not NULL)
            // - All leaf paths going through parent and node have a
            //   black node count that is 1 lower than other leaf paths.
            sibling = parent.right();
            if node != sibling {
                if sibling.is_red() {
                    // Case 1 - left rotate at parent
                    //
                    //     P               S
                    //    / \             / \
                    //   N   s    -->    p   Sr
                    //      / \         / \
                    //     Sl  Sr      N   Sl
                    tmp1 = sibling.left();
                    parent.set_right(tmp1);
                    sibling.set_left(parent);
                    tmp1.set_parent_and_color(parent.ptr(), Color::Black);
                    self.rotate_set_parents(parent, sibling, Color::Red);
                    self.callbacks
                        .rotate(Self::value(parent), Self::value(sibling));
                    sibling = tmp1;
                }
                tmp1 = sibling.right();
                if tmp1.is_black() {
                    tmp2 = sibling.left();
                    if tmp2.is_black() {
                        // Case 2 - sibling color flip
                        // (p could be either color here)
                        //
                        //    (p)           (p)
                        //    / \           / \
                        //   N   S    -->  N   s
                        //      / \           / \
                        //     Sl  Sr        Sl  Sr
                        //
                        // This leaves us violating 5) which can be fixed by
                        // flipping p to black if it was red, or by recursing at
                        // p. p is red when coming from Case 1.
                        sibling.set_parent_and_color(parent.ptr(), Color::Red);
                        if parent.is_red() {
                            parent.set_color(Color::Black);
                        } else {
                            node = parent;
                            parent = parent.parent();
                            if parent.is_some() {
                                continue;
                            }
                        }
                        break;
                    }
                    // Case 3 - right rotate at sibling
                    // (p could be either color here)
                    //
                    //   (p)           (p)
                    //   / \           / \
                    //  N   S    -->  N   sl
                    //     / \             \
                    //    sl  sr            S
                    //                       \
                    //                        sr
                    //
                    // Note: p might be red, and then both p and sl are red
                    // after rotation(which breaks property 4). This is fixed in
                    //
                    // Case 4 (in rotate_set_parents() which sets sl the
                    // color of p and sets p Black)
                    //
                    //   (p)            (sl)
                    //   / \            /  \
                    //  N   sl   -->   P    S
                    //       \        /      \
                    //        S      N        sr
                    //         \
                    //          sr
                    tmp1 = tmp2.right();
                    sibling.set_left(tmp1);
                    tmp2.set_right(sibling);
                    parent.set_right(tmp2);
                    if tmp1.is_some() {
                        tmp1.set_parent_and_color(sibling.ptr(), Color::Black);
                    }
                    self.callbacks
                        .rotate(Self::value(sibling), Self::value(tmp2));
                    tmp1 = sibling;
                    sibling = tmp2;
                }
                // Case 4 - left rotate at parent + color flips
                // (p and sl could be either color here. After rotation, p
                // becomes black, s acquires p's color, and sl keeps its color)
                //
                //      (p)             (s)
                //      / \             / \
                //     N   S     -->   P   Sr
                //        / \         / \
                //      (sl) sr      N  (sl)
                tmp2 = sibling.left();
                parent.set_right(tmp2);
                sibling.set_left(parent);
                tmp1.set_parent_and_color(sibling.ptr(), Color::Black);
                if tmp2.is_some() {
                    tmp2.set_parent(parent.ptr());
                }
                self.rotate_set_parents(parent, sibling, Color::Black);
                self.callbacks
                    .rotate(Self::value(parent), Self::value(sibling));
                break;
            } else {
                sibling = parent.left();
                if sibling.is_red() {
                    // Case 1 - right rotate at parent
                    tmp1 = sibling.right();
                    parent.set_left(tmp1);
                    sibling.set_right(parent);
                    tmp1.set_parent_and_color(parent.ptr(), Color::Black);
                    self.rotate_set_parents(parent, sibling, Color::Red);
                    self.callbacks
                        .rotate(Self::value(parent), Self::value(sibling));
                    sibling = tmp1;
                }
                tmp1 = sibling.left();
                if tmp1.is_black() {
                    tmp2 = sibling.right();
                    if tmp2.is_black() {
                        // Case 2 - sibling color flip
                        sibling.set_parent_and_color(parent.ptr(), Color::Red);
                        if parent.is_red() {
                            parent.set_color(Color::Black);
                        } else {
                            node = parent;
                            parent = node.parent();
                            if parent.is_some() {
                                continue;
                            }
                        }
                        break;
                    }
                    // Case 3 - left rotate at sibling
                    tmp1 = tmp2.left();
                    sibling.set_right(tmp1);
                    tmp2.set_left(sibling);
                    parent.set_left(tmp2);
                    if tmp1.is_some() {
                        tmp1.set_parent_and_color(sibling.ptr(), Color::Black);
                    }
                    self.callbacks
                        .rotate(Self::value(sibling), Self::value(tmp2));
                    tmp1 = sibling;
                    sibling = tmp2;
                }
                // Case 4 - right rotate at parent + color flips
                tmp2 = sibling.right();
                parent.set_left(tmp2);
                sibling.set_right(parent);
                tmp1.set_parent_and_color(sibling.ptr(), Color::Black);
                if tmp2.is_some() {
                    tmp2.set_parent(parent.ptr());
                }
                self.rotate_set_parents(parent, sibling, Color::Black);
                self.callbacks
                    .rotate(Self::value(parent), Self::value(sibling));
                break;
            }
        }
    }
}

impl<A: Adapter, C> Root<A, C> {
    fn change_child(&mut self, old: NonNull<Link>, new: NodePtr<Link>, parent: NodePtr<Link>) {
        if parent.is_some() {
            // parent is never null here, by the if guard.
            let mut parent = parent;
            if parent.left() == Some(old) {
                parent.set_left(new);
            } else {
                parent.set_right(new);
            }
        } else {
            self.node = new;
        }
    }

    /// Helper function for rotations:
    /// - old's parent and color get assigned to new
    /// - old gets assigned new as a parent and 'color' as a color.
    #[inline]
    fn rotate_set_parents(&mut self, mut old: NodePtr<Link>, new: NodePtr<Link>, color: Color) {
        if let Some(old_ptr) = old {
            let parent = old.parent();
            // SAFETY: old_ptr points at a live Link that is part of this tree.
            let old_parent_color = unsafe { Link::parent_color(old_ptr) };
            let new_ptr = new.expect("new pointer should be valid");
            // SAFETY: new_ptr points at a live Link that is part of this tree.
            unsafe { Link::set_parent_color(new_ptr, old_parent_color) };
            old.set_parent_and_color(new.ptr(), color);
            self.change_child(old_ptr, new, parent);
        }
    }
}

#[cfg(test)]
mod test {
    use quickcheck_macros::quickcheck;

    use super::*;
    use crate::{ComingFrom, intrusive::Noop, intrusive_adapter};

    struct IntEntry {
        link: Link,
        key: i16,
    }

    intrusive_adapter!(IntEntryAdapter = IntEntry: link);

    type IntRoot = Root<IntEntryAdapter, Noop<IntEntry>>;

    fn leak(key: i16) -> NonNull<IntEntry> {
        NonNull::from(Box::leak(Box::new(IntEntry {
            link: Link::new(),
            key,
        })))
    }

    /// # Safety
    /// `entry` must have been produced by [`leak`] and not already freed.
    unsafe fn unleak(entry: NonNull<IntEntry>) -> Box<IntEntry> {
        // SAFETY: delegated to the caller.
        unsafe { Box::from_raw(entry.as_ptr()) }
    }

    /// Descends the tree by key, links the new entry in, and rebalances —
    /// the same "caller does the BST walk, engine only rebalances" split
    /// `examples/interval_tree.rs` uses for `crate::Root`.
    fn insert(root: &mut IntRoot, key: i16) -> NonNull<IntEntry> {
        let entry = leak(key);
        // SAFETY: entry was just leaked; it is live and unaliased.
        let link = unsafe { IntEntryAdapter::get_link(entry) };
        match root.node {
            None => {
                // SAFETY: link is live and not yet part of any tree.
                unsafe { Link::set_color(link, Color::Black) };
                root.node = Some(link);
            }
            Some(mut current) => {
                let parent;
                let direction;
                loop {
                    let candidate_parent = current;
                    // SAFETY: current is a live link belonging to this tree.
                    let current_value = unsafe { IntEntryAdapter::get_value(current) };
                    // SAFETY: current_value points at a live IntEntry.
                    let candidate_direction = if key < unsafe { current_value.as_ref() }.key {
                        ComingFrom::Left
                    } else {
                        ComingFrom::Right
                    };
                    let next = match candidate_direction {
                        ComingFrom::Left => Some(current).left(),
                        ComingFrom::Right => Some(current).right(),
                    };
                    match next {
                        Some(n) => current = n,
                        None => {
                            parent = candidate_parent;
                            direction = candidate_direction;
                            break;
                        }
                    }
                }
                // SAFETY: link is freshly leaked and unlinked; parent is a
                // live link belonging to this tree.
                unsafe { Link::link(link, parent, direction) };
                root.insert(link);
            }
        }
        entry
    }

    fn in_order_keys(root: &IntRoot) -> Vec<i16> {
        let mut keys = Vec::new();
        let mut current = root.first();
        while let Some(link) = current {
            // SAFETY: link belongs to this tree, hence to a live IntEntry.
            let value = unsafe { IntEntryAdapter::get_value(link) };
            // SAFETY: value points at a live IntEntry.
            keys.push(unsafe { value.as_ref() }.key);
            current = Some(link).next_node();
        }
        keys
    }

    #[test]
    fn insert_then_iterate_in_order() {
        let mut root = IntRoot::new(Noop::new());
        let entries: Vec<_> = [5, 1, 9, 3, 7, 1, 0, -4]
            .into_iter()
            .map(|k| insert(&mut root, k))
            .collect();

        assert!(root.validate());
        assert_eq!(in_order_keys(&root), vec![-4, 0, 1, 1, 3, 5, 7, 9]);

        for entry in entries {
            let link = unsafe { IntEntryAdapter::get_link(entry) };
            root.erase(link);
            // SAFETY: entry was leaked by `insert` and hasn't been freed yet.
            drop(unsafe { unleak(entry) });
        }
        assert!(root.node.is_none());
    }

    #[quickcheck]
    fn insertion_order_is_irrelevant(xs: Vec<i16>) -> bool {
        let mut forward = IntRoot::new(Noop::new());
        let forward_entries: Vec<_> = xs.iter().map(|&k| insert(&mut forward, k)).collect();

        let mut backward = IntRoot::new(Noop::new());
        let backward_entries: Vec<_> = xs.iter().rev().map(|&k| insert(&mut backward, k)).collect();

        let mut expected = xs;
        expected.sort();

        let ok = forward.validate()
            && backward.validate()
            && in_order_keys(&forward) == expected
            && in_order_keys(&backward) == expected;

        for entry in forward_entries {
            // SAFETY: entry was leaked by `insert` and hasn't been freed yet.
            drop(unsafe { unleak(entry) });
        }
        for entry in backward_entries {
            // SAFETY: entry was leaked by `insert` and hasn't been freed yet.
            drop(unsafe { unleak(entry) });
        }

        ok
    }

    #[quickcheck]
    fn remove_arbitrary(xs: Vec<i16>) -> bool {
        let mut root = IntRoot::new(Noop::new());
        let entries: Vec<_> = xs.iter().map(|&k| insert(&mut root, k)).collect();

        let (removed, kept): (Vec<_>, Vec<_>) = entries
            .into_iter()
            .enumerate()
            .partition(|(i, _)| i % 2 == 0);

        for (_, entry) in &removed {
            let link = unsafe { IntEntryAdapter::get_link(*entry) };
            root.erase(link);
        }

        let mut expected: Vec<i16> = kept
            .iter()
            .map(|(_, entry)| unsafe { entry.as_ref() }.key)
            .collect();
        expected.sort();

        let ok = root.validate() && in_order_keys(&root) == expected;

        for (_, entry) in removed {
            // SAFETY: entry was leaked by `insert` and hasn't been freed yet.
            drop(unsafe { unleak(entry) });
        }
        for (_, entry) in kept {
            let link = unsafe { IntEntryAdapter::get_link(entry) };
            root.erase(link);
            // SAFETY: entry was leaked by `insert` and hasn't been freed yet.
            drop(unsafe { unleak(entry) });
        }

        ok
    }
}
