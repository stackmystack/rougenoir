//! Optional convenience helpers for common chores: a tree ordered by a
//! plain key comparison with no per-node work needed during descent
//! ([`insert_by`]/[`find_by`]), and walking every value to tear a tree down
//! ([`for_each_postorder`]).
//!
//! Everything here is built entirely on the public primitives
//! ([`Adapter::left`]/[`Adapter::right`], [`Link::link`], [`Root::insert`],
//! [`Root::node`]) and is purely additive: nothing here replaces or hides
//! them. Reach for [`insert_by`]/[`find_by`] when your comparison is a
//! simple `Ordering`, and fall back to walking the tree by hand (as
//! `examples/interval_tree.rs` does, which needs to update an augmented
//! field on every ancestor *during* descent — something a read-only
//! comparator can't express) whenever you need more control.

use std::{cmp::Ordering, ptr::NonNull};

use crate::{Color, ComingFrom, NodePtr};

use super::{Adapter, Link, Root, TreeCallbacks};

/// Where a key comparison landed while descending a tree: either an
/// existing node compared equal, or the empty slot where a new node
/// comparing this way belongs.
pub enum InsertPosition<V> {
    /// An existing node compares equal to the key.
    Occupied(NonNull<V>),
    /// No existing node compares equal. Linking a new node as `direction`
    /// of `parent` (or as the tree's root, if `parent` is `None`) would
    /// insert it in the right place.
    Vacant {
        parent: Option<NonNull<V>>,
        direction: ComingFrom,
    },
}

/// Descends from `root` (a tree root pointer, e.g. `some_root.node`),
/// calling `cmp` at each node to decide which way to go, and reports where
/// a key comparing this way belongs.
///
/// `cmp(candidate)` should compare *the key being searched for* against
/// `candidate`, the same convention `Ord::cmp` uses on `self` — i.e.
/// `Ordering::Less` means "my key is less than `candidate`'s", and descends
/// left.
///
/// # Safety
///
/// Every link reachable from `root` must point at a live `A::Value`.
pub unsafe fn find_insert_position<A: Adapter>(
    root: NodePtr<Link>,
    mut cmp: impl FnMut(&A::Value) -> Ordering,
) -> InsertPosition<A::Value> {
    let Some(root_link) = root else {
        return InsertPosition::Vacant {
            parent: None,
            // Arbitrary: there is no parent for this to be a child of.
            direction: ComingFrom::Left,
        };
    };

    // SAFETY: delegated to the caller.
    let mut current = Some(unsafe { A::get_value(root_link) });
    let mut parent = current.expect("just constructed as Some above");
    let mut direction = ComingFrom::Left;

    while let Some(candidate) = current {
        parent = candidate;
        // SAFETY: candidate points at a live A::Value, per the caller's
        // contract.
        let candidate_ref = unsafe { candidate.as_ref() };
        direction = match cmp(candidate_ref) {
            Ordering::Equal => return InsertPosition::Occupied(candidate),
            Ordering::Less => ComingFrom::Left,
            Ordering::Greater => ComingFrom::Right,
        };
        current = match direction {
            // SAFETY: candidate points at a live A::Value in this tree.
            ComingFrom::Left => unsafe { A::left(candidate) },
            ComingFrom::Right => unsafe { A::right(candidate) },
        };
    }

    InsertPosition::Vacant {
        parent: Some(parent),
        direction,
    }
}

/// Links `value` into `root` at the position `cmp` dictates (see
/// [`find_insert_position`]), and rebalances.
///
/// If an existing node compares equal, `value` is *not* linked in — the
/// caller decides whether to replace, merge into, or reject it — and that
/// existing node is returned instead.
///
/// # Safety
///
/// `value` must point at a live, currently unlinked `A::Value` (fresh from
/// construction, not already part of any tree through this `Adapter`).
/// Every link reachable from `root.node` must point at a live `A::Value`.
pub unsafe fn insert_by<A: Adapter, C: TreeCallbacks<Value = A::Value>>(
    root: &mut Root<A, C>,
    value: NonNull<A::Value>,
    cmp: impl FnMut(&A::Value) -> Ordering,
) -> Option<NonNull<A::Value>> {
    // SAFETY: delegated to the caller.
    match unsafe { find_insert_position::<A>(root.node, cmp) } {
        InsertPosition::Occupied(existing) => Some(existing),
        InsertPosition::Vacant {
            parent: None,
            direction: _,
        } => {
            // SAFETY: value is freshly unlinked, per the caller's contract;
            // a lone root must be black.
            unsafe { A::set_color(value, Color::Black) };
            // SAFETY: value embeds a live Link.
            root.node = Some(unsafe { A::get_link(value) });
            None
        }
        InsertPosition::Vacant {
            parent: Some(parent),
            direction,
        } => {
            // SAFETY: value is freshly unlinked, per the caller's contract;
            // parent is a live A::Value belonging to this tree.
            unsafe {
                Link::link(A::get_link(value), A::get_link(parent), direction);
                root.insert(A::get_link(value));
            }
            None
        }
    }
}

/// Looks up the node comparing equal via `cmp` (see
/// [`find_insert_position`]), if any.
///
/// # Safety
///
/// Every link reachable from `root` must point at a live `A::Value`.
pub unsafe fn find_by<A: Adapter>(
    root: NodePtr<Link>,
    cmp: impl FnMut(&A::Value) -> Ordering,
) -> Option<NonNull<A::Value>> {
    // SAFETY: delegated to the caller.
    match unsafe { find_insert_position::<A>(root, cmp) } {
        InsertPosition::Occupied(v) => Some(v),
        InsertPosition::Vacant { .. } => None,
    }
}

/// Calls `f` once for every value reachable from `link`, children before
/// parent (post-order), so `f` can free each value's allocation without
/// disturbing subtrees not yet visited; the same job `Root::dealloc` does
/// for `Tree`/`CachedTree`, since the intrusive API never owns allocation
/// and so has no automatic teardown of its own.
///
/// # Safety
///
/// Every link reachable from `link` must point at a live `A::Value`, and
/// `f` must not touch a value again after it (or a later call to `f`) frees
/// it.
pub unsafe fn for_each_postorder<A: Adapter>(
    link: NodePtr<Link>,
    f: &mut impl FnMut(NonNull<A::Value>),
) {
    let Some(link) = link else {
        return;
    };
    // SAFETY: delegated to the caller.
    let value = unsafe { A::get_value(link) };
    // Capture the children before calling `f` which may free `value`, but
    // that doesn't touch the separate allocations `left`/`right` point to.
    // SAFETY: value points at a live A::Value, per the caller's contract.
    let left = unsafe { A::left(value) };
    // SAFETY: see above.
    let right = unsafe { A::right(value) };
    // SAFETY: left/right, if any, point at live A::Values reachable from
    // `link`, per the caller's contract (transitively, for these subtrees).
    unsafe {
        for_each_postorder::<A>(left.map(|l| A::get_link(l)), f);
        for_each_postorder::<A>(right.map(|r| A::get_link(r)), f);
    }
    f(value);
}

#[cfg(test)]
mod test {
    use quickcheck_macros::quickcheck;

    use super::*;
    use crate::NodePtrExt;
    use crate::intrusive::{Noop, first_of, validate_of};
    use crate::intrusive_adapter;

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

    unsafe fn unleak(entry: NonNull<IntEntry>) -> Box<IntEntry> {
        // SAFETY: delegated to the caller.
        unsafe { Box::from_raw(entry.as_ptr()) }
    }

    fn in_order_keys(root: &IntRoot) -> Vec<i16> {
        let mut keys = Vec::new();
        let mut current = first_of(root.node);
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
    fn insert_by_finds_the_right_spot_and_find_by_locates_it() {
        let mut root = IntRoot::new(Noop::new());
        let entries: Vec<_> = [5, 1, 9, 3, 7]
            .into_iter()
            .map(|key| {
                let entry = leak(key);
                // SAFETY: entry is freshly leaked and unlinked; root's
                // links all point at live IntEntries (there are none yet,
                // or they were all inserted the same way).
                unsafe { insert_by::<IntEntryAdapter, _>(&mut root, entry, |c| key.cmp(&c.key)) };
                entry
            })
            .collect();

        assert!(validate_of(root.node));
        assert_eq!(in_order_keys(&root), vec![1, 3, 5, 7, 9]);

        for key in [1, 3, 5, 7, 9] {
            // SAFETY: root's links all point at live IntEntries.
            let found = unsafe { find_by::<IntEntryAdapter>(root.node, |c| key.cmp(&c.key)) };
            assert_eq!(found.map(|f| unsafe { f.as_ref() }.key), Some(key));
        }
        // SAFETY: see above.
        assert!(unsafe { find_by::<IntEntryAdapter>(root.node, |c| 42.cmp(&c.key)) }.is_none());

        for entry in entries {
            // SAFETY: entry was leaked above and hasn't been freed yet.
            drop(unsafe { unleak(entry) });
        }
    }

    #[test]
    fn insert_by_reports_an_existing_node_instead_of_double_inserting() {
        let mut root = IntRoot::new(Noop::new());
        let first = leak(1);
        // SAFETY: first is freshly leaked and unlinked.
        let inserted =
            unsafe { insert_by::<IntEntryAdapter, _>(&mut root, first, |c| 1.cmp(&c.key)) };
        assert!(inserted.is_none());

        let second = leak(1);
        // SAFETY: second is freshly leaked and unlinked; root's links all
        // point at live IntEntries.
        let collision =
            unsafe { insert_by::<IntEntryAdapter, _>(&mut root, second, |c| 1.cmp(&c.key)) };
        assert_eq!(collision, Some(first));

        // `second` was never linked in, so it must be freed directly
        // instead of via a tree walk.
        // SAFETY: first is the only node in the tree; second was never linked.
        drop(unsafe { unleak(second) });
        unsafe {
            root.erase(IntEntryAdapter::get_link(first));
        }
        // SAFETY: first was leaked above and just erased from the tree.
        drop(unsafe { unleak(first) });
    }

    #[quickcheck]
    fn insertion_order_is_irrelevant(xs: Vec<i16>) -> bool {
        let mut forward = IntRoot::new(Noop::new());
        let forward_entries: Vec<_> = xs
            .iter()
            .filter_map(|&key| {
                let entry = leak(key);
                // SAFETY: entry is freshly leaked and unlinked.
                let existing = unsafe {
                    insert_by::<IntEntryAdapter, _>(&mut forward, entry, |c| key.cmp(&c.key))
                };
                if existing.is_some() {
                    // SAFETY: entry was never linked in.
                    drop(unsafe { unleak(entry) });
                    None
                } else {
                    Some(entry)
                }
            })
            .collect();

        let mut expected: Vec<i16> = xs;
        expected.sort();
        expected.dedup();

        let ok = validate_of(forward.node) && in_order_keys(&forward) == expected;

        for entry in forward_entries {
            // SAFETY: entry was leaked above and successfully linked in,
            // and hasn't been freed yet.
            drop(unsafe { unleak(entry) });
        }

        ok
    }

    #[test]
    fn for_each_postorder_visits_every_node_exactly_once() {
        let mut root = IntRoot::new(Noop::new());
        let keys = [5, 1, 9, 3, 7, 0, -2];
        let entries: Vec<_> = keys
            .iter()
            .map(|&key| {
                let entry = leak(key);
                // SAFETY: entry is freshly leaked and unlinked; root's
                // links all point at live IntEntries.
                unsafe { insert_by::<IntEntryAdapter, _>(&mut root, entry, |c| key.cmp(&c.key)) };
                entry
            })
            .collect();

        let mut visited = Vec::new();
        // SAFETY: root's links all point at live IntEntries; the closure
        // only reads each value, and every value is still alive throughout
        // (nothing is freed here).
        unsafe {
            for_each_postorder::<IntEntryAdapter>(root.node, &mut |n| visited.push(n.as_ref().key));
        }
        visited.sort();
        let mut expected = keys.to_vec();
        expected.sort();
        assert_eq!(visited, expected);

        for entry in entries {
            // SAFETY: entry was leaked above and hasn't been freed yet.
            drop(unsafe { unleak(entry) });
        }
    }

    #[test]
    fn for_each_postorder_can_free_every_node() {
        let mut root = IntRoot::new(Noop::new());
        for key in 0..50i16 {
            let entry = leak(key);
            // SAFETY: entry is freshly leaked and unlinked; root's links
            // all point at live IntEntries.
            unsafe { insert_by::<IntEntryAdapter, _>(&mut root, entry, |c| key.cmp(&c.key)) };
        }

        // SAFETY: root's links all point at live IntEntries, each
        // originally produced by Box::leak (via `leak`); the closure frees
        // each one exactly once and never touches it again afterward.
        unsafe {
            for_each_postorder::<IntEntryAdapter>(root.node, &mut |n| drop(unleak(n)));
        }
        // Nothing left to assert on directly (it's all freed). A double
        // free or a dangling access here is exactly what Miri is for.
    }
}
