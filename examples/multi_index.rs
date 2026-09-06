// The actual point of rougenoir's full kernel-style, offset-based `Adapter`
// (over the simpler single-membership alternative considered for it): a
// single struct can embed more than one `Link` and belong to more than one
// independent intrusive tree at once, with no extra allocation or
// indirection per tree — exactly like a Linux kernel object that's linked
// into both a lookup rbtree and a scheduling rbtree through two separate
// `struct rb_node` fields.
//
// Here, one `Employee` allocation is a member of two trees at once: one
// ordered by `id`, one ordered by `name`.
use std::ptr::NonNull;

use rougenoir::intrusive::{
    Adapter, InsertPosition, Link, Noop, RawIter, Root, find_by, find_insert_position,
    for_each_postorder, insert_by, link_at,
};
use rougenoir::intrusive_adapter;

struct Employee {
    by_id: Link,
    by_name: Link,
    id: u32,
    name: String,
}

// `Employee` isn't generic, so (unlike `IntervalNode<K, V>` in
// `examples/interval_tree.rs`) `intrusive_adapter!` can generate both
// adapters directly.
intrusive_adapter!(ByIdAdapter = Employee: by_id);
intrusive_adapter!(ByNameAdapter = Employee: by_name);

type IdRoot = Root<ByIdAdapter, Noop<Employee>>;
type NameRoot = Root<ByNameAdapter, Noop<Employee>>;

struct EmployeeStore {
    by_id: IdRoot,
    by_name: NameRoot,
    len: usize,
}

impl EmployeeStore {
    fn new() -> Self {
        EmployeeStore {
            by_id: Root::new(Noop::new()),
            by_name: Root::new(Noop::new()),
            len: 0,
        }
    }

    /// Inserts a new employee, linking the same allocation into both trees.
    ///
    /// Both indices are simple key comparisons with no per-node work
    /// needed during descent, so `intrusive`'s convenience layer covers
    /// this completely: no manual descent loop, no first-node special case.
    ///
    /// `by_id`'s comparator can use `insert_by` directly: `id` is a plain
    /// `u32`, independent of `node`'s memory. `by_name`'s comparator needs
    /// `name`, which *is* about to live inside `node` — comparing against a
    /// reference borrowed from `node` itself (`&node.as_ref().name`) would
    /// be unsound (see the safety note on `find_insert_position`): once
    /// linked, `node` can be rotated by either tree's rebalancing while
    /// that borrow is still considered live. So `by_name` finds its
    /// position first, using the owned `name` before it's moved into
    /// `node`, then links separately via `link_at`.
    ///
    /// See `examples/interval_tree.rs` for a tree that instead walks by
    /// hand, because it needs more than a read-only comparison.
    fn insert(&mut self, id: u32, name: impl Into<String>) {
        let name = name.into();

        // SAFETY: every link reachable from by_name points at a live
        // Employee.
        let name_position = unsafe {
            find_insert_position::<ByNameAdapter>(self.by_name.node, |c| name.cmp(&c.name))
        };

        let node = NonNull::from(Box::leak(Box::new(Employee {
            by_id: Link::new(),
            by_name: Link::new(),
            id,
            name,
        })));

        // SAFETY: node is freshly leaked and unlinked in either tree; every
        // link reachable from by_id/by_name points at a live Employee;
        // name_position was computed against this tree before node existed.
        unsafe {
            insert_by::<ByIdAdapter, _>(&mut self.by_id, node, |c| id.cmp(&c.id));
            if let InsertPosition::Vacant { parent, direction } = name_position {
                link_at(&mut self.by_name, node, parent, direction);
            }
        }
        self.len += 1;
    }

    fn get_by_id(&self, id: u32) -> Option<&Employee> {
        // SAFETY: every link reachable from by_id points at a live Employee.
        let found = unsafe { find_by::<ByIdAdapter>(self.by_id.node, |c| id.cmp(&c.id)) };
        // SAFETY: found, if any, points at a live Employee.
        found.map(|n| unsafe { n.as_ref() })
    }

    fn get_by_name(&self, name: &str) -> Option<&Employee> {
        // SAFETY: every link reachable from by_name points at a live Employee.
        let found =
            unsafe { find_by::<ByNameAdapter>(self.by_name.node, |c| name.cmp(c.name.as_str())) };
        // SAFETY: found, if any, points at a live Employee.
        found.map(|n| unsafe { n.as_ref() })
    }

    /// Removes the employee with the given `id` from both trees and frees
    /// it, returning `true` if one was found.
    fn remove(&mut self, id: u32) -> bool {
        // SAFETY: every link reachable from by_id points at a live Employee.
        let Some(node) = (unsafe { find_by::<ByIdAdapter>(self.by_id.node, |c| id.cmp(&c.id)) })
        else {
            return false;
        };
        // SAFETY: node embeds live Links in both trees; erasing it from one
        // tree doesn't touch the other tree's structure (each Link is a
        // separate, independent field), and node isn't used again after
        // Box::from_raw below.
        unsafe {
            self.by_id.erase(ByIdAdapter::get_link(node));
            self.by_name.erase(ByNameAdapter::get_link(node));
            drop(Box::from_raw(node.as_ptr()));
        }
        self.len -= 1;
        true
    }

    /// Employees in ascending `id` order — the same `RawIter` core `by_id`
    /// and `by_name` share, aimed at whichever `Link` field is relevant.
    fn iter_by_id(&self) -> impl Iterator<Item = &Employee> {
        // SAFETY: every link reachable from self.by_id.node points at a live
        // Employee borrowed for the lifetime of &self, and this tree
        // contains exactly self.len of them.
        unsafe { RawIter::<ByIdAdapter>::new(self.by_id.node, self.len) }
            // SAFETY: n points at a live Employee borrowed above.
            .map(|n| unsafe { n.as_ref() })
    }

    /// Employees in ascending `name` order.
    fn iter_by_name(&self) -> impl Iterator<Item = &Employee> {
        // SAFETY: see `iter_by_id`, for the `by_name` tree instead.
        unsafe { RawIter::<ByNameAdapter>::new(self.by_name.node, self.len) }
            // SAFETY: n points at a live Employee borrowed above.
            .map(|n| unsafe { n.as_ref() })
    }
}

impl Drop for EmployeeStore {
    fn drop(&mut self) {
        // Walking the by-id tree visits every employee exactly once.
        // Freeing a node here doesn't touch `by_name`'s structure (its
        // Link is a separate, independent field on the same allocation),
        // so this one traversal safely frees the whole shared allocation
        // without needing to walk `by_name` too.
        //
        // SAFETY: every node in by_id was leaked via Box::leak in `insert`,
        // and this store owns them exclusively; the closure frees each one
        // exactly once and never touches it again afterward.
        unsafe {
            for_each_postorder::<ByIdAdapter>(self.by_id.node, &mut |n| {
                drop(Box::from_raw(n.as_ptr()))
            });
        }
    }
}

fn main() {
    let mut store = EmployeeStore::new();
    store.insert(3, "carol");
    store.insert(1, "alice");
    store.insert(2, "bob");

    assert_eq!(store.get_by_id(1).map(|e| e.name.as_str()), Some("alice"));
    assert_eq!(store.get_by_name("carol").map(|e| e.id), Some(3));

    let ids: Vec<_> = store.iter_by_id().map(|e| e.id).collect();
    assert_eq!(ids, vec![1, 2, 3]);
    let names: Vec<_> = store.iter_by_name().map(|e| e.name.as_str()).collect();
    assert_eq!(names, vec!["alice", "bob", "carol"]);

    store.remove(2);
    assert!(store.get_by_id(2).is_none());
    assert!(store.get_by_name("bob").is_none());
}

#[cfg(test)]
mod test {
    use crate::EmployeeStore;

    #[test]
    fn insert_and_look_up_by_either_index() {
        let mut store = EmployeeStore::new();
        store.insert(1, "alice");
        store.insert(2, "bob");
        store.insert(3, "carol");
        assert_eq!(store.len, 3);

        assert_eq!(store.get_by_id(2).map(|e| e.name.as_str()), Some("bob"));
        assert_eq!(store.get_by_name("carol").map(|e| e.id), Some(3));
        assert!(store.get_by_id(42).is_none());
        assert!(store.get_by_name("dave").is_none());
    }

    #[test]
    fn both_indices_stay_consistent_after_arbitrary_insertion_order() {
        let mut store = EmployeeStore::new();
        let names = ["mallory", "alice", "eve", "carol", "bob", "trent"];
        for (id, name) in names.iter().enumerate() {
            store.insert(id as u32, *name);
        }

        assert!(store.by_id.validate());
        assert!(store.by_name.validate());

        for (id, name) in names.iter().enumerate() {
            assert_eq!(
                store.get_by_id(id as u32).map(|e| e.name.as_str()),
                Some(*name)
            );
            assert_eq!(store.get_by_name(name).map(|e| e.id), Some(id as u32));
        }
    }

    #[test]
    fn remove_updates_both_indices_and_frees_the_node() {
        let mut store = EmployeeStore::new();
        store.insert(1, "alice");
        store.insert(2, "bob");
        store.insert(3, "carol");

        assert!(store.remove(2));
        assert_eq!(store.len, 2);
        assert!(store.get_by_id(2).is_none());
        assert!(store.get_by_name("bob").is_none());

        // The other two are still reachable through both indices.
        assert_eq!(store.get_by_id(1).map(|e| e.name.as_str()), Some("alice"));
        assert_eq!(store.get_by_name("carol").map(|e| e.id), Some(3));

        assert!(!store.remove(99));
    }

    #[test]
    fn iter_by_id_and_iter_by_name_each_walk_their_own_order() {
        let mut store = EmployeeStore::new();
        let names = ["mallory", "alice", "eve", "carol", "bob", "trent"];
        for (id, name) in names.iter().enumerate() {
            store.insert(id as u32, *name);
        }

        let by_id: Vec<_> = store.iter_by_id().map(|e| e.id).collect();
        assert_eq!(by_id, (0..names.len() as u32).collect::<Vec<_>>());

        let by_name: Vec<_> = store.iter_by_name().map(|e| e.name.as_str()).collect();
        let mut expected_names = names.to_vec();
        expected_names.sort_unstable();
        assert_eq!(by_name, expected_names);
    }

    #[test]
    fn remove_all_leaves_both_trees_empty() {
        let mut store = EmployeeStore::new();
        for id in 0..20u32 {
            store.insert(id, format!("employee_{id}"));
        }
        for id in 0..20u32 {
            assert!(store.remove(id));
        }
        assert_eq!(store.len, 0);
        assert!(store.by_id.node.is_none());
        assert!(store.by_name.node.is_none());
    }
}
