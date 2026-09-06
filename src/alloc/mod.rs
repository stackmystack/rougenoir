//! The node backing store for the collection layer.
//!
//! [`Tree`](crate::Tree)/[`CachedTree`](crate::CachedTree)/[`Set`](crate::Set)
//! allocate one `Node<K, V>` per entry. Which allocator they draw those nodes
//! from is a compile-time choice: the `A` type parameter, defaulting to
//! [`Global`] (a leaked `Box`, honouring any `#[global_allocator]`).
//!
//! Optional backends live behind cargo features — `slab` (a local
//! slab-of-chunks pool), `bumpalo`, `blink-alloc`, and `nightly` (a bridge
//! for any `core::alloc::Allocator`).

use std::{
    alloc::Layout,
    ptr::{self, NonNull},
};

use crate::{Color, Node};

#[cfg(feature = "blink-alloc")]
mod blink;
#[cfg(feature = "bumpalo")]
mod bumpalo;
#[cfg(feature = "nightly")]
mod nightly;
#[cfg(feature = "slab")]
mod slab;

#[cfg(feature = "nightly")]
pub use nightly::Std;
#[cfg(feature = "slab")]
pub use slab::Slab;

/// Backing store for a red-black tree's nodes.
///
/// This is a strict subset of the (nightly) `core::alloc::Allocator` trait —
/// there is no `grow`/`shrink`, because tree nodes are fixed size. With the
/// `nightly` feature, any `core::alloc::Allocator` adapts via `alloc::Std`.
///
/// # Safety
///
/// An implementor must uphold:
///
/// - `allocate(layout)` returns either `None` or a non-null block of at least
///   `layout.size()` bytes aligned to at least `layout.align()`.
/// - A block returned by `allocate` keeps its address until it is passed to
///   `deallocate` — the allocator must **never relocate a live allocation**.
///   The tree stores raw `NonNull` pointers into these blocks, so a
///   `Vec`-backed arena that reallocates on growth is unsound here.
/// - `deallocate(ptr, layout)` is only ever called with a `ptr` previously
///   returned from this same allocator's `allocate` under an equal `layout`,
///   and at most once for that `ptr`.
pub unsafe trait Allocator {
    /// Allocate an uninitialised block fitting `layout`, or `None` on failure.
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>>;

    /// Return a block to the allocator.
    ///
    /// # Safety
    ///
    /// See the trait-level contract: `ptr`/`layout` must match a live
    /// allocation from this allocator, freed at most once.
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
}

/// The default node store: `std::alloc::{alloc, dealloc}`, which honours any
/// `#[global_allocator]`. Equivalent to the leaked `Box` rougenoir used
/// before the allocator abstraction existed.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct Global;

// SAFETY: the global allocator never relocates a live allocation, and
// `alloc`/`dealloc` uphold the size/alignment contract for non-zero layouts;
// the zero-size branch returns a well-aligned dangling pointer, as
// `core::alloc::Allocator` does.
unsafe impl Allocator for Global {
    #[inline]
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        if layout.size() == 0 {
            return NonNull::new(ptr::without_provenance_mut(layout.align()));
        }
        // SAFETY: `layout.size()` is non-zero per the branch above.
        NonNull::new(unsafe { std::alloc::alloc(layout) })
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() == 0 {
            return;
        }
        // SAFETY: delegated to the caller by the trait contract.
        unsafe { std::alloc::dealloc(ptr.as_ptr(), layout) }
    }
}

/// Allocate and initialise a `Node<K, V>` for `(key, value)` from `alloc`.
///
/// The node starts black and unlinked, exactly as the old `leak_alloc_node`
/// did. Returns `None` only when `alloc` is out of memory.
pub(crate) fn alloc_node<K, V, A: Allocator>(
    alloc: &A,
    key: K,
    value: V,
) -> Option<NonNull<Node<K, V>>> {
    let ptr = alloc
        .allocate(Layout::new::<Node<K, V>>())?
        .cast::<Node<K, V>>();
    let mut node = Node::new(key, value);
    node.set_color(Color::Black);
    // SAFETY: `ptr` is a fresh, uninitialised, suitably aligned block for a
    // `Node<K, V>` (the `Allocator` contract) that nothing else references.
    unsafe { ptr.as_ptr().write(node) };
    Some(ptr)
}

/// Drop an already-unlinked node's `key`/`value` in place, then return its
/// storage to `alloc`.
///
/// # Safety
///
/// `node` points at a live `Node<K, V>` obtained from `alloc`, no longer
/// linked into any tree, with no other live references to it.
pub(crate) unsafe fn drop_node<K, V, A: Allocator>(alloc: &A, node: NonNull<Node<K, V>>) {
    // SAFETY: the caller guarantees `node` is live and solely owned; `Link`
    // has no `Drop`, so this runs only `key`/`value` destructors.
    unsafe { ptr::drop_in_place(node.as_ptr()) };
    // SAFETY: `node` came from `alloc.allocate` under this exact layout and
    // is freed exactly once here.
    unsafe { alloc.deallocate(node.cast::<u8>(), Layout::new::<Node<K, V>>()) };
}

/// Move `(key, value)` out of an already-unlinked node and return its storage
/// to `alloc`.
///
/// # Safety
///
/// As [`drop_node`].
pub(crate) unsafe fn take_node<K, V, A: Allocator>(alloc: &A, node: NonNull<Node<K, V>>) -> (K, V) {
    // SAFETY: the caller guarantees `node` is live and solely owned; the
    // block is read exactly once and not touched again before it is freed.
    let n = unsafe { ptr::read(node.as_ptr()) };
    // SAFETY: `node` came from `alloc.allocate` under this exact layout and
    // is freed exactly once here; `n` now owns `key`/`value`.
    unsafe { alloc.deallocate(node.cast::<u8>(), Layout::new::<Node<K, V>>()) };
    (n.key, n.value)
}
