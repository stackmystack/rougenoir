//! Adapter for [`bumpalo::Bump`] as a node backing store (`feature = "bumpalo"`).
//!
//! Pass `&bump` to [`Tree::new_in`](crate::Tree::new_in) &co. Allocation is a
//! pointer bump; there is **no per-node reclamation** — `remove`/`pop_*` still
//! run the entry's `Drop`, but the slot is only reclaimed when the `Bump` is
//! reset or dropped. A `Bump`-backed tree therefore does not implement
//! `Clone`/`Default`/`clear` (there is no fresh allocator to build into);
//! rebuild with `iter().collect()` into a new arena instead.

use std::{alloc::Layout, ptr::NonNull};

use super::Allocator;

// SAFETY:
// - `bumpalo::Bump` never moves a live allocation (it is a linked list of
//   chunks, never reallocated), so the raw pointers the tree stores stay
//   valid until the arena is reset or dropped.
// - `try_alloc_layout` returns a block matching `layout`.
// - `deallocate` is a no-op: bump allocators reclaim en masse. The tree's
//   `Drop` still runs each entry's `key`/`value` destructor before this
//   no-op; the memory itself is freed with the `Bump`.
unsafe impl Allocator for &bumpalo::Bump {
    #[inline]
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        self.try_alloc_layout(layout).ok()
    }

    #[inline]
    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

#[cfg(test)]
mod test {
    use crate::{Noop, Tree};
    use bumpalo::Bump;

    #[test]
    fn matches_global() {
        let bump = Bump::new();
        let mut bumped: Tree<i32, i32, Noop<i32, i32>, &Bump> = Tree::new_in(&bump);
        let mut global: Tree<i32, i32, Noop<i32, i32>> = Tree::new();

        for k in [5, 1, 9, 3, 7, 2, 8, 0, 6, 4] {
            bumped.insert(k, k * 10);
            global.insert(k, k * 10);
        }
        // remove still works; the slot just isn't reclaimed until `bump` drops.
        for k in [3, 7, 0] {
            assert_eq!(bumped.remove(&k), global.remove(&k));
        }

        assert!(bumped.iter().eq(global.iter()));
        assert_eq!(bumped.len(), global.len());
    }

    #[test]
    fn runs_value_destructors_on_drop() {
        use std::rc::Rc;

        let bump = Bump::new();
        let witness = Rc::new(());
        {
            let mut tree: Tree<i32, Rc<()>, Noop<i32, Rc<()>>, &Bump> = Tree::new_in(&bump);
            for k in 0..16 {
                tree.insert(k, Rc::clone(&witness));
            }
            assert_eq!(Rc::strong_count(&witness), 17);
        }
        // Tree dropped: every `Rc` value must have been dropped even though the
        // bump slots are still held.
        assert_eq!(Rc::strong_count(&witness), 1);
    }
}
