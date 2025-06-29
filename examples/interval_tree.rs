// From the Linux Kernel's core API docs:
// https://github.com/torvalds/linux/blob/master/Documentation/core-api/rbtree.rst
use std::{cmp::Ordering::*, marker::PhantomData};

use rougenoir::{ComingFrom, Node, NodePtrExt, Root, TreeCallbacks};

#[derive(Debug, Clone, Copy)]
struct Interval<T>
where
    T: Ord,
{
    from: T,
    to: T,
    subtree_to: T,
}

impl<T> Eq for Interval<T> where T: Ord + Eq {}
impl<T> Ord for Interval<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.from
            .cmp(&other.from)
            .then_with(|| self.to.cmp(&other.to))
    }
}

impl<T> PartialOrd for Interval<T>
where
    T: Ord + PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> PartialEq for Interval<T>
where
    T: Ord + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.from == other.from && self.to == other.to
    }
}

struct IntervalTreeCallbacks<K, V> {
    phantom: PhantomData<(K, V)>,
}

impl<K, V> IntervalTreeCallbacks<K, V>
where
    K: Ord + Copy,
{
    fn compute_rubtree_last(node: &Node<Interval<K>, V>) -> K {
        let mut max = node.key.to;
        let mut subtree_to;
        if node.left.is_some() {
            subtree_to = node.key.subtree_to;
            if max < subtree_to {
                max = subtree_to;
            }
        }
        if node.right.is_some() {
            subtree_to = node.key.subtree_to;
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
    type Key = Interval<K>;
    type Value = V;

    fn copy(&self, old: &mut Node<Self::Key, Self::Value>, new: &mut Node<Self::Key, Self::Value>) {
        new.key.subtree_to = old.key.subtree_to;
    }

    fn propagate(
        &self,
        node: Option<&mut Node<Self::Key, Self::Value>>,
        stop: Option<&mut Node<Self::Key, Self::Value>>,
    ) {
        if let Some(start_node) = node {
            let mut current: *mut Node<Self::Key, Self::Value> = start_node;
            let stop_ptr = stop.map_or(std::ptr::null(), |s| s as *const _);

            while !std::ptr::eq(current, stop_ptr) {
                let current_ref = unsafe { &*current };
                let current_mut = unsafe { &mut *current };

                let subtree_to = IntervalTreeCallbacks::compute_rubtree_last(current_ref);

                if current_ref.key.subtree_to == subtree_to {
                    break;
                }

                current_mut.key.subtree_to = subtree_to;

                // Move to parent
                let parent_opt = current_ref.parent();
                if let Some(parent_ptr) = parent_opt {
                    current = parent_ptr.as_ptr();
                } else {
                    break;
                }
            }
        }
    }

    fn rotate(
        &self,
        old: &mut Node<Self::Key, Self::Value>,
        new: &mut Node<Self::Key, Self::Value>,
    ) {
        new.key.subtree_to = old.key.subtree_to;
        old.key.subtree_to = IntervalTreeCallbacks::compute_rubtree_last(old);
    }
}

struct IntervalTree<K, V>
where
    K: Ord,
{
    root: Root<Interval<K>, V, IntervalTreeCallbacks<K, V>>,
    len: usize,
}

impl<K, V> IntervalTree<K, V>
where
    K: Ord + Copy,
{
    pub fn new() -> Self {
        IntervalTree {
            root: Root {
                callbacks: IntervalTreeCallbacks {
                    phantom: PhantomData,
                },
                node: None,
            },
            len: 0,
        }
    }

    // ⚠️ marks a comment on the difference with the implementation of insert in Tree.
    pub fn insert<Q>(&mut self, key: Q, value: V) -> Option<V>
    where
        K: Ord + Copy,
        Q: Into<Interval<K>>,
    {
        match self.root.node {
            None => {
                // SAFETY: root doesn't exist, so we create a new one.
                self.root.node = unsafe { Node::<Interval<K>, V>::leak(key.into(), value) }; // ⚠️ coerce type
                self.len += 1;
                None
            }
            Some(_) => {
                let to = unsafe { self.root.node.unwrap().as_ref() }.key.to;

                // [1] replace an existing value or ([2] prepare for linking and [3] link).
                let mut current_node = self.root.node.ptr();
                let mut parent = current_node;
                let mut direction = ComingFrom::Left; // We don't really care, but rust does.

                let key: Interval<K> = key.into(); // ⚠️ add
                while !current_node.is_null() {
                    parent = current_node; // [4] parent is never null by construction.
                    #[allow(unused_variables)]
                    let parent = parent; // [4] by sealing, parent is never null hereafter.

                    // SAFETY: guaranteed not null by the while guard.
                    let current_ref = unsafe { current_node.as_mut().unwrap() };
                    // ⚠️ begin::add
                    if current_ref.key.subtree_to < to {
                        current_ref.key.subtree_to = to;
                    }
                    // ⚠️ end::add

                    match key.cmp(&current_ref.key) {
                        Equal => {
                            // [1] replace an existing value.
                            return Some(std::mem::replace(&mut current_ref.value, value));
                        }
                        Greater => {
                            // [2] prepare for linking on the right of parent.
                            direction = ComingFrom::Right;
                            current_node = current_ref.right.ptr();
                        }
                        Less => {
                            // [2] prepare for linking on the left of parent.
                            direction = ComingFrom::Left;
                            current_node = current_ref.left.ptr();
                        }
                    };
                }
                #[allow(unused_variables)]
                let current_node = current_node;
                let direction = direction;
                let parent = parent; // [4] by sealing, parent is never null hereafter.

                // [3] link.

                // SAFETY: we're owning (k,v)
                let mut node = unsafe { Node::<Interval<K>, V>::leak(key, value) }; // ⚠️ coerce type
                unsafe { node.unwrap_unchecked().as_mut() }.key.subtree_to = to; // ⚠️ add
                // SAFETY: [4] parent is never null by construction.
                unsafe { node.link(parent, direction) };
                // SAFETY: node is definitely non null at this stage.
                self.root.insert(unsafe { node.unwrap_unchecked() });
                self.len += 1;
                None
            }
        }
    }
}

impl<K, V> Drop for IntervalTree<K, V>
where
    K: Ord,
{
    fn drop(&mut self) {
        // SAFETY: we're literally in drop.
        unsafe {
            Root::dealloc(&mut self.root, self.len);
        }
    }
}

impl<T> From<(T, T)> for Interval<T>
where
    T: Ord + Clone,
{
    fn from(value: (T, T)) -> Self {
        Self {
            from: value.0.clone(),
            to: value.1,
            subtree_to: value.0,
        }
    }
}

fn main() {
    let mut tree = IntervalTree::new();
    tree.insert((0, 1), 12);
    tree.insert((0, 2), 12);
    tree.insert((0, 3), 12);
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
    fn insert_many_intervals() {
        let mut tree = IntervalTree::new();
        for i in 0..100 {
            tree.insert((i * 2, i * 2 + 1), format!("interval_{}", i));
        }
        assert_eq!(tree.len, 100);
    }
}
