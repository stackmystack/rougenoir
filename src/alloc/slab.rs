//! A local slab-of-chunks pool allocator (`feature = "slab"`).
//!
//! One [`Slab`] backs one tree. Nodes are handed out from cache-line-aligned
//! chunks that are never relocated (so the raw `NonNull` pointers the tree
//! holds stay valid), and freed slots are recycled through an intrusive
//! free list threaded through the dead slots themselves — no per-node
//! `malloc`/`free` round trip, and teardown frees a handful of chunks
//! instead of `n` individual nodes.

use std::{
    alloc::Layout,
    cell::RefCell,
    mem,
    ptr::{self, NonNull},
};

use super::Allocator;

/// How many slots the first chunk holds. Each subsequent chunk doubles this,
/// up to [`MAX_SLOTS_PER_CHUNK`], so a large tree ends up in a handful of
/// chunks while a tiny one wastes almost nothing.
const INITIAL_SLOTS_PER_CHUNK: usize = 32;
const MAX_SLOTS_PER_CHUNK: usize = 8192;
/// Chunk bases are aligned to a cache line so slots pack predictably.
const CHUNK_ALIGN: usize = 64;

struct State {
    /// The padded layout of a single slot, learned from the first
    /// `allocate` call. Every later call must match it (a tree only ever
    /// allocates one node type).
    slot: Option<Layout>,
    /// `(base, layout)` for every chunk, in allocation order. Freed on drop.
    chunks: Vec<(NonNull<u8>, Layout)>,
    /// Head of the intrusive free list; each free slot's first word points
    /// at the next free slot (or is null).
    free: *mut u8,
    /// Slots in the last chunk that have never been handed out yet:
    /// `[bump_next, bump_end)` as byte offsets from the last chunk's base.
    bump_next: usize,
    bump_end: usize,
    /// Slot count for the *next* chunk to allocate.
    next_chunk_slots: usize,
}

/// A slab-of-chunks node pool. See the module docs.
///
/// Backs exactly one tree / one node type. Not `Sync` — a slab shared
/// between threads without external synchronisation would be unsound.
pub struct Slab {
    state: RefCell<State>,
}

impl Slab {
    /// Creates an empty pool. The first chunk is allocated lazily, on the
    /// first insertion.
    pub fn new() -> Self {
        Self::with_capacity(INITIAL_SLOTS_PER_CHUNK)
    }

    /// Creates an empty pool whose first chunk will hold at least `nodes`
    /// slots.
    pub fn with_capacity(nodes: usize) -> Self {
        Slab {
            state: RefCell::new(State {
                slot: None,
                chunks: Vec::new(),
                free: ptr::null_mut(),
                bump_next: 0,
                bump_end: 0,
                next_chunk_slots: nodes.clamp(1, MAX_SLOTS_PER_CHUNK),
            }),
        }
    }
}

impl Default for Slab {
    fn default() -> Self {
        Self::new()
    }
}

/// The slot layout for `layout`: wide and aligned enough to also hold the
/// free-list link, and padded so `size()` is the slot stride.
fn slot_layout_for(layout: Layout) -> Layout {
    let align = layout.align().max(mem::align_of::<*mut u8>());
    let size = layout.size().max(mem::size_of::<*mut u8>());
    Layout::from_size_align(size, align)
        .expect("slot layout")
        .pad_to_align()
}

fn chunk_layout_for(slot: Layout, slots: usize) -> Option<Layout> {
    let size = slot.size().checked_mul(slots)?;
    Layout::from_size_align(size, slot.align().max(CHUNK_ALIGN)).ok()
}

impl State {
    /// Allocate one fresh chunk and make it the bump region.
    fn grow(&mut self, slot: Layout) -> Option<()> {
        let slots = self.next_chunk_slots;
        let layout = chunk_layout_for(slot, slots)?;
        // SAFETY: `layout` has non-zero size (slot.size() >= word size,
        // slots >= 1).
        let base = NonNull::new(unsafe { std::alloc::alloc(layout) })?;
        self.chunks.push((base, layout));
        self.bump_next = 0;
        self.bump_end = slot.size() * slots;
        self.next_chunk_slots = (slots * 2).min(MAX_SLOTS_PER_CHUNK);
        Some(())
    }
}

// SAFETY:
// - Chunks are individually `alloc`ated and never reallocated or moved, so
//   every slot address stays fixed until `deallocate` (and only becomes
//   reusable, never invalid, after it).
// - `allocate` returns a `slot.size()`-byte, `slot.align()`-aligned block,
//   which covers the requested `layout` (slot is derived to be at least as
//   large and aligned).
// - `deallocate` only ever pushes a slot onto the free list; the caller
//   contract guarantees the slot came from this pool.
unsafe impl Allocator for Slab {
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        let mut st = self.state.borrow_mut();

        let slot = match st.slot {
            Some(s) => {
                debug_assert!(
                    layout.size() <= s.size() && layout.align() <= s.align(),
                    "Slab handed a second, larger node layout",
                );
                s
            }
            None => {
                let s = slot_layout_for(layout);
                st.slot = Some(s);
                s
            }
        };

        // 1. Recycle a freed slot.
        if !st.free.is_null() {
            let p = st.free;
            // SAFETY: `p` is a slot we previously freed; its first word holds
            // the next free-list link.
            st.free = unsafe { ptr::read(p as *const *mut u8) };
            return NonNull::new(p);
        }

        // 2. Bump within the current chunk.
        if st.bump_next >= st.bump_end {
            st.grow(slot)?;
        }
        let (base, _) = *st.chunks.last().expect("chunk just ensured");
        // SAFETY: `bump_next < bump_end` and the chunk is `bump_end` bytes.
        let p = unsafe { base.as_ptr().add(st.bump_next) };
        st.bump_next += slot.size();
        NonNull::new(p)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let mut st = self.state.borrow_mut();
        debug_assert_eq!(
            st.slot.map(|s| (s.size(), s.align())),
            Some((
                slot_layout_for(layout).size(),
                slot_layout_for(layout).align()
            )),
        );
        // Push onto the free list: stash the current head in this slot's
        // first word.
        // SAFETY: `ptr` is a live slot from this pool, at least word-sized
        // and word-aligned, and nothing else references it now.
        unsafe { ptr::write(ptr.as_ptr() as *mut *mut u8, st.free) };
        st.free = ptr.as_ptr();
    }
}

impl Drop for Slab {
    fn drop(&mut self) {
        let st = self.state.get_mut();
        for (base, layout) in st.chunks.drain(..) {
            // SAFETY: each `(base, layout)` pair came from `std::alloc::alloc`
            // in `State::grow` and is freed exactly once here.
            unsafe { std::alloc::dealloc(base.as_ptr(), layout) };
        }
    }
}

// SAFETY: `Slab` owns plain heap allocations and no thread-affine state, so
// it may move between threads. It is deliberately **not** `Sync`: `allocate`
// mutates through `&self`.
unsafe impl Send for Slab {}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{Noop, Tree};
    use quickcheck_macros::quickcheck;

    #[test]
    fn recycles_freed_slots() {
        let slab = Slab::new();
        let layout = Layout::from_size_align(32, 8).unwrap();

        let a = slab.allocate(layout).unwrap();
        let b = slab.allocate(layout).unwrap();
        assert_ne!(a, b);

        // SAFETY: `a`/`b` are live slots from `slab` under `layout`.
        unsafe {
            slab.deallocate(a, layout);
            slab.deallocate(b, layout);
        }

        // LIFO free list: last freed comes back first.
        let c = slab.allocate(layout).unwrap();
        let d = slab.allocate(layout).unwrap();
        assert_eq!(c, b);
        assert_eq!(d, a);

        // SAFETY: clean up.
        unsafe {
            slab.deallocate(c, layout);
            slab.deallocate(d, layout);
        }
    }

    #[test]
    fn spans_multiple_chunks() {
        let slab = Slab::with_capacity(4);
        let layout = Layout::from_size_align(24, 8).unwrap();
        let mut ptrs = Vec::new();
        for _ in 0..100 {
            ptrs.push(slab.allocate(layout).unwrap());
        }
        ptrs.sort();
        ptrs.dedup();
        assert_eq!(ptrs.len(), 100, "every slot is distinct");
        assert!(slab.state.borrow().chunks.len() >= 2);
        // SAFETY: every ptr is a live, distinct slot from `slab`.
        for p in ptrs {
            unsafe { slab.deallocate(p, layout) };
        }
    }

    #[quickcheck]
    fn slab_tree_matches_global(ops: Vec<(u16, bool)>) -> bool {
        let mut slab: Tree<u16, u32, Noop<u16, u32>, Slab> = Tree::new_in(Slab::new());
        let mut global: Tree<u16, u32, Noop<u16, u32>> = Tree::new();

        for (i, (k, remove)) in ops.into_iter().enumerate() {
            if remove {
                if slab.remove(&k) != global.remove(&k) {
                    return false;
                }
            } else {
                let v = i as u32;
                if slab.insert(k, v) != global.insert(k, v) {
                    return false;
                }
            }
        }

        slab.len() == global.len() && slab.iter().eq(global.iter())
    }

    #[quickcheck]
    fn slab_tree_drains_in_order(mut keys: Vec<i32>) -> bool {
        let mut tree: Tree<i32, (), Noop<i32, ()>, Slab> = Tree::new_in(Slab::new());
        for &k in &keys {
            tree.insert(k, ());
        }
        keys.sort_unstable();
        keys.dedup();

        let mut drained = Vec::new();
        while let Some((k, ())) = tree.pop_first() {
            drained.push(k);
        }
        drained == keys
    }
}
