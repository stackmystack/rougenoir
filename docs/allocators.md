# Allocators

`Tree`, `CachedTree` and `Set` allocate one `Node<K, V>` per entry. Where
those nodes come from is a compile-time choice — the `A` type parameter:

```rust
pub struct Tree<K, V, C = Noop<K, V>, A = rougenoir::alloc::Global> where A: rougenoir::alloc::Allocator { .. }
```

The default, `Global`, routes to `std::alloc::{alloc, dealloc}` (so it
honours any `#[global_allocator]`) and is exactly the leaked-`Box` behaviour
rougenoir has always had. Everything below is opt-in.

## The `Allocator` trait

```rust
pub unsafe trait Allocator {
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>>;
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
}
```

It is a deliberate subset of the nightly `core::alloc::Allocator` (no
`grow`/`shrink` — tree nodes are fixed size). The **safety contract** an
implementor must uphold:

- `allocate` returns `None`, or a block of at least `layout.size()` bytes
  aligned to at least `layout.align()`.
- **A live allocation is never relocated.** The tree stores raw `NonNull`
  pointers into these blocks, so a `Vec`-backed arena that reallocates on
  growth is unsound. Chunked arenas (a linked list of fixed blocks) are fine.
- `deallocate` is called at most once per block, with the `Layout` the block
  was allocated under.

## Backends

Enable one cargo feature and use the matching `*_in` constructor
(`Tree::new_in`, `Tree::with_callbacks_in`, and the same on `CachedTree` /
`Set`).

### `Global` — default, no feature

`std::alloc`. One allocation per node, freed individually. Nothing to enable.

### `slab` → `alloc::Slab`

```toml
rougenoir = { version = "0.1", features = ["slab"] }
```

```rust
use rougenoir::{Tree, alloc::Slab};

let mut tree: Tree<u64, String, _, Slab> = Tree::new_in(Slab::new());
```

A local **slab-of-chunks pool**: cache-line-aligned chunks (geometric
growth), an intrusive free list threaded through freed slots. No per-node
`malloc`/`free`, and teardown frees a handful of chunks instead of `n`
nodes. Freed slots *are* recycled, so `remove`-heavy workloads are fine —
though after heavy churn the in-memory order drifts from key order (a future
`compact()` would address that).

- `Slab::new()` — first chunk allocated lazily on the first insert.
- `Slab::with_capacity(n)` — size the first chunk for `n` nodes.
- One `Slab` backs one tree / one node type. `Slab: Send + !Sync + Default`.
- Because `Slab: Default`, a `Slab`-backed tree is still `Clone` / `Default` /
  `FromIterator` — the clone builds into a *fresh* `Slab` (a compacting copy).

### `bumpalo` → `&bumpalo::Bump`, `blink-alloc` → `&blink_alloc::BlinkAlloc`

```rust
let bump = bumpalo::Bump::new();
let mut tree = rougenoir::Tree::new_in(&bump);
```

Pointer-bump arenas. Allocation is a bump; **`deallocate` is a no-op** —
slots are reclaimed only when the arena is `reset()` or dropped.

- `remove` / `pop_*` still run the entry's `Drop`; only the raw slot lingers.
- Tree `Drop` runs every entry's `Drop` (cheaply), then the arena frees the
  memory when *it* drops.
- `&Bump` / `&BlinkAlloc` are not `Default`, so these trees have **no
  `Clone` / `Default` / `clear`**. Rebuild with `old.iter().collect()` into a
  tree over a fresh arena.
- Best for build-mostly / drain / drop lifecycles, or `Set` used as a dedup
  pass.

### `nightly` → `alloc::Std<A>`

```toml
rougenoir = { version = "0.1", features = ["nightly"] }
```

```rust
use rougenoir::{Tree, alloc::Std};
use std::alloc::System;

let mut tree: Tree<u64, u64, _, Std<System>> = Tree::new_in(Std(System));
```

`Std<A>` wraps any `core::alloc::Allocator`. Because that trait is
nightly-only, this feature turns on `#![feature(allocator_api)]` and the
whole crate then **requires `cargo +nightly`**. `Std<A>` is `Clone`/`Copy`/
`Default` when `A` is, so a `Std`-backed tree keeps `Clone` etc. as long as
`A: Default`.

## Testing an allocator layer change

```sh
just test-features      # all stable backends
just test-nightly       # + the nightly bridge  (needs nightly)
just miri-features      # Miri, stable backends
just miri-nightly       # Miri, + nightly bridge
```

CI runs all of these. Any new `Allocator` impl needs an equivalence property
test against `Global` (same insert/remove/iter results) and a Miri pass.
