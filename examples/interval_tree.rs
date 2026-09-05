// From the Linux Kernel's core API docs:
// https://github.com/torvalds/linux/blob/master/Documentation/core-api/rbtree.rst
//
// Unlike the kernel's own interval tree recipe, this builds on rougenoir's
// *intrusive* API (`rougenoir::intrusive`): `IntervalNode` embeds a `Link`
// directly, owns its own allocation (leaked via `Box`, freed by hand in
// `Drop`), and the tree never sees a `Node<K, V>` wrapper at all.
use std::{marker::PhantomData, ptr::NonNull};

use rougenoir::{
    Color, ComingFrom,
    intrusive::{Adapter, Link, RawIter, Root, TreeCallbacks, for_each_postorder},
    intrusive_adapter,
};

/// The interval `[from, to]` a caller inserts. `IntervalNode` below is the
/// struct actually embedded in the tree; this is just a convenient input
/// type for [`IntervalTree::insert`].
#[derive(Debug, Clone, Copy)]
struct Interval<T> {
    from: T,
    to: T,
}

impl<T> From<(T, T)> for Interval<T> {
    fn from(value: (T, T)) -> Self {
        Self {
            from: value.0,
            to: value.1,
        }
    }
}

/// A node of the interval tree: an embedded [`Link`], the interval itself,
/// the augmented `subtree_to` (the maximum `to` in this node's subtree,
/// including itself), and the caller's value.
struct IntervalNode<K, V> {
    link: Link,
    from: K,
    to: K,
    subtree_to: K,
    value: V,
}

intrusive_adapter!(IntervalNodeAdapter<K, V> = IntervalNode<K, V> : link);

struct IntervalTreeCallbacks<K, V> {
    phantom: PhantomData<(K, V)>,
}

impl<K, V> IntervalTreeCallbacks<K, V>
where
    K: Ord + Copy,
{
    /// The augmented value for `node`: the largest `to` reachable from it,
    /// i.e. `max(node.to, left.subtree_to, right.subtree_to)`.
    fn compute_subtree_max(node: NonNull<IntervalNode<K, V>>) -> K {
        // SAFETY: node points at a live IntervalNode.
        let mut max = unsafe { node.as_ref() }.to;
        // SAFETY: node points at a live IntervalNode belonging to a tree
        // built through IntervalNodeAdapter.
        if let Some(left) = unsafe { IntervalNodeAdapter::<K, V>::left(node) } {
            // SAFETY: see above.
            let subtree_to = unsafe { left.as_ref() }.subtree_to;
            if max < subtree_to {
                max = subtree_to;
            }
        }
        // SAFETY: see above.
        if let Some(right) = unsafe { IntervalNodeAdapter::<K, V>::right(node) } {
            // SAFETY: see above.
            let subtree_to = unsafe { right.as_ref() }.subtree_to;
            if max < subtree_to {
                max = subtree_to;
            }
        }
        max
    }
}

impl<K, V> TreeCallbacks for IntervalTreeCallbacks<K, V>
where
    K: Ord + Copy,
{
    type Value = IntervalNode<K, V>;

    fn copy(&self, old: NonNull<Self::Value>, mut new: NonNull<Self::Value>) {
        // SAFETY: old/new point at live IntervalNodes.
        unsafe { new.as_mut() }.subtree_to = unsafe { old.as_ref() }.subtree_to;
    }

    fn propagate(&self, node: Option<NonNull<Self::Value>>, stop: Option<NonNull<Self::Value>>) {
        let mut current = node;
        while current != stop {
            let Some(mut current_ptr) = current else {
                break;
            };
            let subtree_to = Self::compute_subtree_max(current_ptr);
            // SAFETY: current_ptr points at a live IntervalNode that
            // nothing else touches for the duration of this call.
            let current_ref = unsafe { current_ptr.as_mut() };
            if current_ref.subtree_to == subtree_to {
                break;
            }
            current_ref.subtree_to = subtree_to;
            // SAFETY: current_ptr points at a live IntervalNode belonging
            // to a tree built through IntervalNodeAdapter.
            current = unsafe { IntervalNodeAdapter::<K, V>::parent(current_ptr) };
        }
    }

    fn rotate(&self, mut old: NonNull<Self::Value>, mut new: NonNull<Self::Value>) {
        // SAFETY: old/new point at live IntervalNodes.
        unsafe {
            new.as_mut().subtree_to = old.as_ref().subtree_to;
            old.as_mut().subtree_to = Self::compute_subtree_max(old);
        }
    }
}

struct IntervalTree<K, V>
where
    K: Ord,
{
    root: Root<IntervalNodeAdapter<K, V>, IntervalTreeCallbacks<K, V>>,
    len: usize,
}

impl<K, V> IntervalTree<K, V>
where
    K: Ord + Copy,
{
    pub fn new() -> Self {
        IntervalTree {
            root: Root::new(IntervalTreeCallbacks {
                phantom: PhantomData,
            }),
            len: 0,
        }
    }

    pub fn insert<Q>(&mut self, key: Q, value: V) -> Option<V>
    where
        Q: Into<Interval<K>>,
    {
        let interval: Interval<K> = key.into();
        let to = interval.to;

        match self.root.node {
            None => {
                // SAFETY: root doesn't exist, so we create a new one.
                let node_ptr = NonNull::from(Box::leak(Box::new(IntervalNode {
                    link: Link::new(),
                    from: interval.from,
                    to: interval.to,
                    subtree_to: to,
                    value,
                })));
                // SAFETY: node_ptr is freshly leaked and not yet part of
                // any tree; a lone root must be black.
                unsafe { IntervalNodeAdapter::<K, V>::set_color(node_ptr, Color::Black) };
                // SAFETY: node_ptr embeds a live Link.
                self.root.node = Some(unsafe { IntervalNodeAdapter::<K, V>::get_link(node_ptr) });
                self.len += 1;
                None
            }
            Some(root_link) => {
                // [1] replace an existing value or ([2] prepare for linking and [3] link).
                // SAFETY: root_link embeds a live IntervalNode.
                let mut current =
                    Some(unsafe { IntervalNodeAdapter::<K, V>::get_value(root_link) });
                let mut parent = current.expect("tree is non-empty by the match guard above");
                let mut direction = ComingFrom::Left; // We don't really care, but rust does.

                while let Some(mut candidate) = current {
                    parent = candidate; // [4] parent is never null by construction.
                    #[allow(unused_variables)]
                    let parent = parent; // [4] by sealing, parent is never null hereafter.

                    // SAFETY: candidate points at a live IntervalNode.
                    let candidate_ref = unsafe { candidate.as_mut() };
                    if candidate_ref.subtree_to < to {
                        candidate_ref.subtree_to = to;
                    }

                    current = match interval
                        .from
                        .cmp(&candidate_ref.from)
                        .then_with(|| interval.to.cmp(&candidate_ref.to))
                    {
                        std::cmp::Ordering::Equal => {
                            // [1] replace an existing value.
                            return Some(std::mem::replace(&mut candidate_ref.value, value));
                        }
                        std::cmp::Ordering::Greater => {
                            // [2] prepare for linking on the right of parent.
                            direction = ComingFrom::Right;
                            // SAFETY: candidate points at a live IntervalNode.
                            unsafe { IntervalNodeAdapter::<K, V>::right(candidate) }
                        }
                        std::cmp::Ordering::Less => {
                            // [2] prepare for linking on the left of parent.
                            direction = ComingFrom::Left;
                            // SAFETY: candidate points at a live IntervalNode.
                            unsafe { IntervalNodeAdapter::<K, V>::left(candidate) }
                        }
                    };
                }
                #[allow(unused_variables)]
                let direction = direction;
                let parent = parent; // [4] by sealing, parent is never null hereafter.

                // [3] link.

                // SAFETY: we're owning (k,v)
                let node_ptr = NonNull::from(Box::leak(Box::new(IntervalNode {
                    link: Link::new(),
                    from: interval.from,
                    to: interval.to,
                    subtree_to: to,
                    value,
                })));
                // SAFETY: node_ptr is freshly leaked and unlinked; parent
                // is a live IntervalNode belonging to this tree.
                unsafe {
                    Link::link(
                        IntervalNodeAdapter::<K, V>::get_link(node_ptr),
                        IntervalNodeAdapter::<K, V>::get_link(parent),
                        direction,
                    );
                    self.root
                        .insert(IntervalNodeAdapter::<K, V>::get_link(node_ptr));
                }
                self.len += 1;
                None
            }
        }
    }

    /// Iterates over every interval in ascending order, yielding `(from, to, &value)`.
    pub fn iter(&self) -> impl Iterator<Item = (K, K, &V)> {
        // SAFETY: every link reachable from self.root.node points at a live
        // IntervalNode<K, V> borrowed for the lifetime of &self, and this
        // tree contains exactly self.len of them.
        unsafe { RawIter::<IntervalNodeAdapter<K, V>>::new(self.root.node, self.len) }.map(|n| {
            // SAFETY: n points at a live IntervalNode borrowed above.
            let n = unsafe { n.as_ref() };
            (n.from, n.to, &n.value)
        })
    }
}

impl<K, V> Drop for IntervalTree<K, V>
where
    K: Ord,
{
    fn drop(&mut self) {
        // The intrusive API never owns allocation (mirroring the kernel's
        // `struct rb_node`), so unlike `Tree`/`CachedTree` there is no
        // built-in teardown to call.
        //
        // `for_each_postorder` is the additive convenience that replaces
        // hand-writing that walk.
        //
        // SAFETY: every node in this tree was leaked via Box::leak in
        // `insert`, and this tree owns them exclusively; the closure frees
        // each one exactly once and never touches it again afterward.
        unsafe {
            for_each_postorder::<IntervalNodeAdapter<K, V>>(self.root.node, &mut |n| {
                drop(Box::from_raw(n.as_ptr()))
            });
        }
    }
}

fn main() {
    let mut tree = IntervalTree::new();
    tree.insert((0, 1), 12);
    tree.insert((0, 2), 12);
    tree.insert((0, 3), 12);

    let intervals: Vec<_> = tree.iter().map(|(from, to, _)| (from, to)).collect();
    assert_eq!(intervals, vec![(0, 1), (0, 2), (0, 3)]);
}

#[cfg(test)]
mod test {
    use crate::IntervalTree;

    #[test]
    fn insert_single_interval() {
        let mut tree = IntervalTree::new();
        let result = tree.insert((0, 5), "first");
        assert_eq!(result, None);
        assert_eq!(tree.len, 1);
    }

    #[test]
    fn insert_duplicate_interval_replaces_value() {
        let mut tree = IntervalTree::new();
        tree.insert((0, 5), "first");
        let result = tree.insert((0, 5), "second");
        assert_eq!(result, Some("first"));
        assert_eq!(tree.len, 1);
    }

    #[test]
    fn insert_multiple_non_overlapping_intervals() {
        let mut tree = IntervalTree::new();
        tree.insert((0, 5), "a");
        tree.insert((10, 15), "b");
        tree.insert((20, 25), "c");
        assert_eq!(tree.len, 3);
    }

    #[test]
    fn insert_overlapping_intervals() {
        let mut tree = IntervalTree::new();
        tree.insert((0, 10), "a");
        tree.insert((5, 15), "b");
        tree.insert((12, 20), "c");
        assert_eq!(tree.len, 3);
    }

    #[test]
    fn insert_nested_intervals() {
        let mut tree = IntervalTree::new();
        tree.insert((0, 20), "outer");
        tree.insert((5, 10), "inner1");
        tree.insert((12, 15), "inner2");
        assert_eq!(tree.len, 3);
    }

    #[test]
    fn insert_maintains_ordering() {
        let mut tree = IntervalTree::new();
        // Insert in non-sorted order
        tree.insert((10, 15), "b");
        tree.insert((0, 5), "a");
        tree.insert((20, 25), "c");
        tree.insert((5, 10), "d");
        assert_eq!(tree.len, 4);
    }

    #[test]
    fn insert_identical_start_different_end() {
        let mut tree = IntervalTree::new();
        tree.insert((0, 5), "short");
        tree.insert((0, 10), "medium");
        tree.insert((0, 15), "long");
        assert_eq!(tree.len, 3);
    }

    #[test]
    fn insert_point_intervals() {
        let mut tree = IntervalTree::new();
        tree.insert((5, 5), "point1");
        tree.insert((10, 10), "point2");
        tree.insert((15, 15), "point3");
        assert_eq!(tree.len, 3);
    }

    #[test]
    fn insert_updates_subtree_max() {
        let mut tree = IntervalTree::new();
        tree.insert((0, 5), "a");
        tree.insert((10, 20), "b");
        tree.insert((2, 15), "c"); // This should update subtree_to values
        assert_eq!(tree.len, 3);
    }

    #[test]
    fn insert_large_range_intervals() {
        let mut tree = IntervalTree::new();
        tree.insert((0, 1000), "big");
        tree.insert((500, 1500), "bigger");
        tree.insert((100, 200), "small");
        assert_eq!(tree.len, 3);
    }

    #[test]
    fn insert_negative_intervals() {
        let mut tree = IntervalTree::new();
        tree.insert((-10, -5), "neg1");
        tree.insert((-20, -15), "neg2");
        tree.insert((-5, 5), "crossing");
        assert_eq!(tree.len, 3);
    }

    #[test]
    fn iter_visits_every_interval_in_ascending_order() {
        let mut tree = IntervalTree::new();
        tree.insert((10, 15), "b");
        tree.insert((0, 5), "a");
        tree.insert((20, 25), "c");
        tree.insert((5, 10), "d");

        let seen: Vec<_> = tree.iter().map(|(from, to, v)| (from, to, *v)).collect();
        assert_eq!(
            seen,
            vec![(0, 5, "a"), (5, 10, "d"), (10, 15, "b"), (20, 25, "c"),]
        );
    }

    #[test]
    fn iter_empty_tree_yields_nothing() {
        let tree: IntervalTree<i32, &str> = IntervalTree::new();
        assert_eq!(tree.iter().count(), 0);
    }

    #[test]
    fn insert_many_intervals() {
        let mut tree = IntervalTree::new();
        for i in 0..100 {
            tree.insert((i * 2, i * 2 + 1), format!("interval_{}", i));
        }
        assert_eq!(tree.len, 100);
    }
}
