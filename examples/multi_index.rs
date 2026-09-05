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

use rougenoir::{
    Color, ComingFrom, NodePtr,
    intrusive::{Adapter, Link, Noop, Root},
    intrusive_adapter,
};

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
    fn insert(&mut self, id: u32, name: impl Into<String>) {
        let node = NonNull::from(Box::leak(Box::new(Employee {
            by_id: Link::new(),
            by_name: Link::new(),
            id,
            name: name.into(),
        })));

        link_by_id(&mut self.by_id, node);
        link_by_name(&mut self.by_name, node);
        self.len += 1;
    }

    fn get_by_id(&self, id: u32) -> Option<&Employee> {
        // SAFETY: by_id.node, if any, embeds a live Employee.
        let mut current = self
            .by_id
            .node
            .map(|l| unsafe { ByIdAdapter::get_value(l) });
        while let Some(candidate) = current {
            // SAFETY: candidate points at a live Employee.
            let candidate_ref = unsafe { candidate.as_ref() };
            current = match id.cmp(&candidate_ref.id) {
                std::cmp::Ordering::Equal => return Some(candidate_ref),
                // SAFETY: candidate points at a live Employee in this tree.
                std::cmp::Ordering::Less => unsafe { ByIdAdapter::left(candidate) },
                std::cmp::Ordering::Greater => unsafe { ByIdAdapter::right(candidate) },
            };
        }
        None
    }

    fn get_by_name(&self, name: &str) -> Option<&Employee> {
        // SAFETY: by_name.node, if any, embeds a live Employee.
        let mut current = self
            .by_name
            .node
            .map(|l| unsafe { ByNameAdapter::get_value(l) });
        while let Some(candidate) = current {
            // SAFETY: candidate points at a live Employee.
            let candidate_ref = unsafe { candidate.as_ref() };
            current = match name.cmp(candidate_ref.name.as_str()) {
                std::cmp::Ordering::Equal => return Some(candidate_ref),
                // SAFETY: candidate points at a live Employee in this tree.
                std::cmp::Ordering::Less => unsafe { ByNameAdapter::left(candidate) },
                std::cmp::Ordering::Greater => unsafe { ByNameAdapter::right(candidate) },
            };
        }
        None
    }

    /// Removes the employee with the given `id` from both trees and frees
    /// it, returning `true` if one was found.
    fn remove(&mut self, id: u32) -> bool {
        let Some(node) = self.find_node_by_id(id) else {
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

    fn find_node_by_id(&self, id: u32) -> Option<NonNull<Employee>> {
        // SAFETY: by_id.node, if any, embeds a live Employee.
        let mut current = self
            .by_id
            .node
            .map(|l| unsafe { ByIdAdapter::get_value(l) });
        while let Some(candidate) = current {
            // SAFETY: candidate points at a live Employee.
            let candidate_id = unsafe { candidate.as_ref() }.id;
            current = match id.cmp(&candidate_id) {
                std::cmp::Ordering::Equal => return Some(candidate),
                // SAFETY: candidate points at a live Employee in this tree.
                std::cmp::Ordering::Less => unsafe { ByIdAdapter::left(candidate) },
                std::cmp::Ordering::Greater => unsafe { ByIdAdapter::right(candidate) },
            };
        }
        None
    }
}

/// Descends `root` by `id`, links the new node in, and rebalances — the
/// same "caller does the BST walk, the engine only rebalances" split
/// `examples/interval_tree.rs` and `crate::Tree::insert` both use.
fn link_by_id(root: &mut IdRoot, node: NonNull<Employee>) {
    match root.node {
        None => {
            // SAFETY: node is freshly leaked and not yet part of any tree;
            // a lone root must be black.
            unsafe { ByIdAdapter::set_color(node, Color::Black) };
            // SAFETY: node embeds a live Link.
            root.node = Some(unsafe { ByIdAdapter::get_link(node) });
        }
        Some(root_link) => {
            // SAFETY: root_link embeds a live Employee.
            let mut current = Some(unsafe { ByIdAdapter::get_value(root_link) });
            let mut parent = current.expect("tree is non-empty by the match guard above");
            let mut direction = ComingFrom::Left;
            // SAFETY: node is live (freshly leaked above).
            let id = unsafe { node.as_ref() }.id;

            while let Some(candidate) = current {
                parent = candidate;
                // SAFETY: candidate points at a live Employee.
                let candidate_id = unsafe { candidate.as_ref() }.id;
                direction = if id < candidate_id {
                    ComingFrom::Left
                } else {
                    ComingFrom::Right
                };
                current = match direction {
                    // SAFETY: candidate points at a live Employee in this tree.
                    ComingFrom::Left => unsafe { ByIdAdapter::left(candidate) },
                    ComingFrom::Right => unsafe { ByIdAdapter::right(candidate) },
                };
            }

            // SAFETY: node is freshly leaked and unlinked; parent is a
            // live Employee belonging to this tree.
            unsafe {
                Link::link(
                    ByIdAdapter::get_link(node),
                    ByIdAdapter::get_link(parent),
                    direction,
                );
                root.insert(ByIdAdapter::get_link(node));
            }
        }
    }
}

/// Descends `root` by `name`. See [`link_by_id`].
fn link_by_name(root: &mut NameRoot, node: NonNull<Employee>) {
    match root.node {
        None => {
            // SAFETY: node is freshly leaked and not yet part of any tree;
            // a lone root must be black.
            unsafe { ByNameAdapter::set_color(node, Color::Black) };
            // SAFETY: node embeds a live Link.
            root.node = Some(unsafe { ByNameAdapter::get_link(node) });
        }
        Some(root_link) => {
            // SAFETY: root_link embeds a live Employee.
            let mut current = Some(unsafe { ByNameAdapter::get_value(root_link) });
            let mut parent = current.expect("tree is non-empty by the match guard above");
            let mut direction = ComingFrom::Left;

            while let Some(candidate) = current {
                parent = candidate;
                // SAFETY: node/candidate point at live Employees.
                let (name, candidate_name) =
                    unsafe { (&node.as_ref().name, &candidate.as_ref().name) };
                direction = if name < candidate_name {
                    ComingFrom::Left
                } else {
                    ComingFrom::Right
                };
                current = match direction {
                    // SAFETY: candidate points at a live Employee in this tree.
                    ComingFrom::Left => unsafe { ByNameAdapter::left(candidate) },
                    ComingFrom::Right => unsafe { ByNameAdapter::right(candidate) },
                };
            }

            // SAFETY: node is freshly leaked and unlinked; parent is a
            // live Employee belonging to this tree.
            unsafe {
                Link::link(
                    ByNameAdapter::get_link(node),
                    ByNameAdapter::get_link(parent),
                    direction,
                );
                root.insert(ByNameAdapter::get_link(node));
            }
        }
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
        // and this store owns them exclusively.
        unsafe { free_subtree(self.by_id.node) };
    }
}

/// Frees every node reachable from `link` (by-id links, but any embedded
/// `Link` field addresses the same allocations).
///
/// # Safety
///
/// Every link reachable from `link` must point at a live `Employee`
/// originally produced by `Box::leak`, and none of them may be touched
/// again after this call.
unsafe fn free_subtree(link: NodePtr<Link>) {
    let Some(link) = link else {
        return;
    };
    // SAFETY: delegated to the caller.
    let node = unsafe { ByIdAdapter::get_value(link) };
    // SAFETY: node points at a live Employee belonging to this tree.
    let left = unsafe { ByIdAdapter::left(node) };
    // SAFETY: see above.
    let right = unsafe { ByIdAdapter::right(node) };
    // SAFETY: node was produced by Box::leak in `insert`, and this is the
    // only remaining reference to it.
    drop(unsafe { Box::from_raw(node.as_ptr()) });

    // SAFETY: left/right, if any, point at live Employees.
    let left_link = left.map(|l| unsafe { ByIdAdapter::get_link(l) });
    // SAFETY: see above.
    let right_link = right.map(|r| unsafe { ByIdAdapter::get_link(r) });
    // SAFETY: delegated to the caller (transitively, for these subtrees).
    unsafe {
        free_subtree(left_link);
        free_subtree(right_link);
    }
}

fn main() {
    let mut store = EmployeeStore::new();
    store.insert(3, "carol");
    store.insert(1, "alice");
    store.insert(2, "bob");

    assert_eq!(store.get_by_id(1).map(|e| e.name.as_str()), Some("alice"));
    assert_eq!(store.get_by_name("carol").map(|e| e.id), Some(3));

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
