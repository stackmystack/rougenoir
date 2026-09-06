//! Bridge from `core::alloc::Allocator` to [`Allocator`] (`feature = "nightly"`).
//!
//! `core::alloc::Allocator` is nightly-only, so this whole module — and the
//! `#![feature(allocator_api)]` it needs — is gated on the `nightly` feature.
//! Wrap any std or custom allocator in [`Std`] and hand it to
//! [`Tree::new_in`](crate::Tree::new_in) &co.:
//!
//! ```ignore
//! use rougenoir::{Tree, alloc::Std};
//! let tree: Tree<u64, u64, _, Std<std::alloc::System>> =
//!     Tree::new_in(Std(std::alloc::System));
//! ```

use std::{alloc::Layout, ptr::NonNull};

use super::Allocator;

/// Adapts any [`core::alloc::Allocator`] to rougenoir's [`Allocator`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct Std<A>(pub A);

// SAFETY:
// - `core::alloc::Allocator` guarantees an allocated block stays valid at a
//   fixed address until it is deallocated (only `grow`/`shrink`, which we
//   never call, may relocate) — that is exactly rougenoir's stable-address
//   requirement.
// - `allocate` yields a slice covering `layout`; we return a pointer to its
//   start. `deallocate` forwards unchanged under the same `ptr`/`layout`
//   contract.
unsafe impl<A: core::alloc::Allocator> Allocator for Std<A> {
    #[inline]
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        core::alloc::Allocator::allocate(&self.0, layout)
            .ok()
            .map(NonNull::cast)
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        // SAFETY: forwarded per the trait contract — `ptr`/`layout` name a
        // live block from `self.0`, freed once.
        unsafe { core::alloc::Allocator::deallocate(&self.0, ptr, layout) }
    }
}

#[cfg(test)]
mod test {
    use super::Std;
    use crate::{Noop, Tree};
    use std::alloc::System;

    #[test]
    fn matches_global() {
        let mut sys: Tree<i32, i32, Noop<i32, i32>, Std<System>> = Tree::new_in(Std(System));
        let mut global: Tree<i32, i32, Noop<i32, i32>> = Tree::new();

        for k in [5, 1, 9, 3, 7, 2, 8, 0, 6, 4] {
            sys.insert(k, k * 10);
            global.insert(k, k * 10);
        }
        for k in [3, 7, 0] {
            assert_eq!(sys.remove(&k), global.remove(&k));
        }
        assert!(sys.iter().eq(global.iter()));
    }

    #[test]
    fn clone_uses_a_fresh_allocator() {
        // `Std<System>: Default`, so a `Std`-backed tree is still `Clone`.
        let mut tree: Tree<i32, i32, Noop<i32, i32>, Std<System>> = Tree::new_in(Std(System));
        for k in 0..32 {
            tree.insert(k, k);
        }
        let clone = tree.clone();
        assert_eq!(tree, clone);
        drop(tree);
        assert_eq!(clone.len(), 32);
    }
}
