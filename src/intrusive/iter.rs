//! A generic, double-ended cursor over any [`Adapter`]-navigable intrusive
//! tree — the shared traversal core behind `Tree`/`CachedTree`'s `Iter`/
//! `IterMut` (see `src/iter/tree.rs`/`src/iter/cached_tree.rs`), and directly
//! usable by custom intrusive trees built on this module (see
//! `examples/interval_tree.rs`, `examples/multi_index.rs`).

use std::{iter::FusedIterator, marker::PhantomData, ptr::NonNull};

use crate::NodePtr;

use super::{Adapter, Link, first_of, last_of};

/// Walks every value reachable from a tree root, front-to-back or
/// back-to-front, yielding `NonNull<A::Value>`.
///
/// This carries no borrow of `A::Value` itself (it's built entirely on raw
/// pointers), so wrap it to produce `&`/`&mut` references or owned values,
/// the way `src/iter/tree.rs`'s `Iter`/`IterMut` do around their own
/// (previously hand-rolled, now `RawIter`-backed) traversal.
pub struct RawIter<A: Adapter> {
    first: NodePtr<Link>,
    last: NodePtr<Link>,
    len: usize,
    _adapter: PhantomData<A>,
}

impl<A: Adapter> RawIter<A> {
    /// Builds a cursor over every value reachable from `root` (a tree root
    /// pointer, e.g. `some_root.node`), which must contain exactly `len`
    /// values.
    ///
    /// # Safety
    ///
    /// Every link reachable from `root` must point at a live `A::Value`, and
    /// `root`'s tree must contain exactly `len` of them.
    #[inline]
    pub unsafe fn new(root: NodePtr<Link>, len: usize) -> Self {
        RawIter {
            first: first_of(root),
            last: last_of(root),
            len,
            _adapter: PhantomData,
        }
    }
}

impl<A: Adapter> Iterator for RawIter<A> {
    type Item = NonNull<A::Value>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        let link = self.first.expect("len > 0 implies first is Some");
        self.len -= 1;
        // SAFETY: link points at a live Link, per `RawIter::new`'s contract.
        self.first = unsafe { Link::next(link) };
        // SAFETY: link points at a live A::Value, per `RawIter::new`'s
        // contract.
        Some(unsafe { A::get_value(link) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

// `len` (not `first == last`) is the authoritative stop condition: once both
// ends have been pulled from, `first` may have walked past `last` (e.g. a
// forward pull following a backward one on the same node) without either
// hitting its own natural `None`. Relying on `first`/`last` converging
// instead of on `len` is exactly the bug this type's tests were written to
// catch in `Tree`/`CachedTree`'s own (independently implemented) `next_back`.
impl<A: Adapter> DoubleEndedIterator for RawIter<A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        let link = self.last.expect("len > 0 implies last is Some");
        self.len -= 1;
        // SAFETY: link points at a live Link, per `RawIter::new`'s contract.
        self.last = unsafe { Link::prev(link) };
        // SAFETY: link points at a live A::Value, per `RawIter::new`'s
        // contract.
        Some(unsafe { A::get_value(link) })
    }
}

impl<A: Adapter> ExactSizeIterator for RawIter<A> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<A: Adapter> FusedIterator for RawIter<A> {}

impl<A: Adapter> Clone for RawIter<A> {
    fn clone(&self) -> Self {
        RawIter {
            first: self.first,
            last: self.last,
            len: self.len,
            _adapter: PhantomData,
        }
    }
}

#[cfg(test)]
mod test {
    use quickcheck_macros::quickcheck;

    use super::*;
    use crate::{intrusive::Noop, intrusive::Root, intrusive::insert_by, intrusive_adapter};

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

    /// Inserts `key`, assumed distinct from every key already in `root`.
    fn insert(root: &mut IntRoot, key: i16) -> NonNull<IntEntry> {
        let entry = leak(key);
        // SAFETY: entry is freshly leaked and unlinked; root's links all
        // point at live IntEntries.
        let existing = unsafe { insert_by::<IntEntryAdapter, _>(root, entry, |c| key.cmp(&c.key)) };
        assert!(existing.is_none(), "test helper only inserts distinct keys");
        entry
    }

    fn free_all(entries: Vec<NonNull<IntEntry>>) {
        for entry in entries {
            // SAFETY: every entry was leaked above and hasn't been freed yet.
            drop(unsafe { unleak(entry) });
        }
    }

    #[test]
    fn empty_tree_yields_nothing() {
        let root = IntRoot::new(Noop::new());
        // SAFETY: root is empty, so vacuously every (zero) reachable link
        // points at a live IntEntry.
        let mut iter = unsafe { RawIter::<IntEntryAdapter>::new(root.node, 0) };
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn walks_forward_in_order() {
        let mut root = IntRoot::new(Noop::new());
        let keys = [5, 1, 9, 3, 7];
        let entries: Vec<_> = keys.iter().map(|&k| insert(&mut root, k)).collect();

        // SAFETY: root's links all point at the live IntEntries just
        // inserted, and there are exactly `keys.len()` of them.
        let iter = unsafe { RawIter::<IntEntryAdapter>::new(root.node, keys.len()) };
        // SAFETY: every yielded pointer points at a live IntEntry, read-only,
        // for the duration of this collect.
        let seen: Vec<_> = iter.map(|n| unsafe { n.as_ref() }.key).collect();
        assert_eq!(seen, vec![1, 3, 5, 7, 9]);

        free_all(entries);
    }

    #[test]
    fn walks_backward_in_reverse_order() {
        let mut root = IntRoot::new(Noop::new());
        let keys = [5, 1, 9, 3, 7];
        let entries: Vec<_> = keys.iter().map(|&k| insert(&mut root, k)).collect();

        // SAFETY: see `walks_forward_in_order`.
        let iter = unsafe { RawIter::<IntEntryAdapter>::new(root.node, keys.len()) };
        // SAFETY: see `walks_forward_in_order`.
        let seen: Vec<_> = iter.rev().map(|n| unsafe { n.as_ref() }.key).collect();
        assert_eq!(seen, vec![9, 7, 5, 3, 1]);

        free_all(entries);
    }

    #[test]
    fn next_and_next_back_meet_in_the_middle_without_overrunning() {
        let mut root = IntRoot::new(Noop::new());
        let keys: Vec<i16> = (0..10).collect();
        let entries: Vec<_> = keys.iter().map(|&k| insert(&mut root, k)).collect();

        // SAFETY: see `walks_forward_in_order`.
        let mut iter = unsafe { RawIter::<IntEntryAdapter>::new(root.node, keys.len()) };
        for i in 0..5i16 {
            // SAFETY: yielded pointers point at live IntEntries.
            assert_eq!(unsafe { iter.next().unwrap().as_ref() }.key, i);
            // SAFETY: see above.
            assert_eq!(unsafe { iter.next_back().unwrap().as_ref() }.key, 9 - i);
        }
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        free_all(entries);
    }

    #[quickcheck]
    fn matches_forward_and_backward_reference_order(xs: Vec<i16>) -> bool {
        let mut root = IntRoot::new(Noop::new());
        // `xs` may contain duplicate keys; insert_by rejects (and doesn't
        // link) a key that already compares equal, so free those instead of
        // treating them as newly-linked entries.
        let entries: Vec<_> = xs
            .iter()
            .filter_map(|&key| {
                let entry = leak(key);
                // SAFETY: entry is freshly leaked and unlinked; root's links
                // all point at live IntEntries.
                let existing = unsafe {
                    insert_by::<IntEntryAdapter, _>(&mut root, entry, |c| key.cmp(&c.key))
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

        let mut expected = xs;
        expected.sort();
        expected.dedup();

        // SAFETY: root's links all point at the live IntEntries just
        // inserted, and there are exactly `entries.len()` of them.
        let forward: Vec<_> = unsafe { RawIter::<IntEntryAdapter>::new(root.node, entries.len()) }
            // SAFETY: every yielded pointer points at a live IntEntry.
            .map(|n| unsafe { n.as_ref() }.key)
            .collect();
        // SAFETY: see above.
        let backward: Vec<_> = unsafe { RawIter::<IntEntryAdapter>::new(root.node, entries.len()) }
            .rev()
            // SAFETY: see above.
            .map(|n| unsafe { n.as_ref() }.key)
            .collect();

        let mut expected_rev = expected.clone();
        expected_rev.reverse();

        let ok = forward == expected && backward == expected_rev;

        free_all(entries);
        ok
    }
}
