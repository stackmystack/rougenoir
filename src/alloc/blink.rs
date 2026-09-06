//! Adapter for [`blink_alloc::BlinkAlloc`] as a node backing store
//! (`feature = "blink-alloc"`).
//!
//! Same shape and caveats as the [`bumpalo`](super) adapter: pass `&blink` to
//! [`Tree::new_in`](crate::Tree::new_in) &co., allocation is a pointer bump,
//! and there is **no per-node reclamation** — `remove`/`pop_*` run the entry's
//! `Drop` but the slot is reclaimed only on `reset`/drop of the `BlinkAlloc`.
//! A blink-backed tree therefore does not implement `Clone`/`Default`/`clear`.

use std::{alloc::Layout, ptr::NonNull};

use super::Allocator;

// SAFETY:
// - `BlinkAlloc` never moves a live allocation (chunk list, never realloc'd),
//   so the raw pointers the tree stores stay valid until reset/drop.
// - the inherent `allocate` returns a slice covering `layout`; we hand back a
//   pointer to its start.
// - `deallocate` is a no-op; the tree's `Drop` still runs each entry's
//   `key`/`value` destructor first, and the memory is freed with the arena.
unsafe impl Allocator for &blink_alloc::BlinkAlloc {
    #[inline]
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        blink_alloc::BlinkAlloc::allocate(self, layout)
            .ok()
            .map(NonNull::cast)
    }

    #[inline]
    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

#[cfg(test)]
mod test {
    use crate::{Noop, Tree};
    use blink_alloc::BlinkAlloc;

    #[test]
    fn matches_global() {
        let blink = BlinkAlloc::new();
        let mut blinked: Tree<i32, i32, Noop<i32, i32>, &BlinkAlloc> = Tree::new_in(&blink);
        let mut global: Tree<i32, i32, Noop<i32, i32>> = Tree::new();

        for k in [5, 1, 9, 3, 7, 2, 8, 0, 6, 4] {
            blinked.insert(k, k * 10);
            global.insert(k, k * 10);
        }
        for k in [3, 7, 0] {
            assert_eq!(blinked.remove(&k), global.remove(&k));
        }

        assert!(blinked.iter().eq(global.iter()));
        assert_eq!(blinked.len(), global.len());
    }

    #[test]
    fn runs_value_destructors_on_drop() {
        use std::rc::Rc;

        let blink = BlinkAlloc::new();
        let witness = Rc::new(());
        {
            let mut tree: Tree<i32, Rc<()>, Noop<i32, Rc<()>>, &BlinkAlloc> = Tree::new_in(&blink);
            for k in 0..16 {
                tree.insert(k, Rc::clone(&witness));
            }
            assert_eq!(Rc::strong_count(&witness), 17);
        }
        assert_eq!(Rc::strong_count(&witness), 1);
    }
}
