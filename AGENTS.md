# rougenoir

This file provides guidance on working with code in this repository.

## What this is

`rougenoir` is a Rust port of the Linux kernel's red-black tree (`rbtree.c`/`rbtree_augmented.h`). It has two layers:

- A genuinely intrusive engine (`src/intrusive/`, public as `rougenoir::intrusive`): a `Link` type meant to be embedded — even more than once, for membership in more than one tree at once — in an arbitrary caller struct, navigated via an `Adapter` (the `container_of()` equivalent), and rebalanced by `intrusive::Root`. This is where the kernel's `rbtree.c` Case 1–4 logic actually lives — the *only* copy of it in the crate.
- Safe-ish collection types (`Tree`, `CachedTree`, `Set`) plus a `Node`/`Root` low-level API, both built on top of that same engine: `Node<K, V>` embeds a `Link` and owns `K`/`V` directly, and `Root<K, V, C>` is a thin wrapper that converts to/from `intrusive::Root` at its public boundary instead of keeping its own copy of the rebalancing algorithm.

## Commands

All common tasks are wired through `just` (see `justfile`); the underlying `cargo`/`cargo-nextest` commands are shown too.

- Build: `just build` (`cargo build`)
- Test: `just test` (`cargo nextest run --tests --examples` + `cargo test --doc` — doctests don't run under nextest, so both are required)
- Test the `examples/` folder specifically (compiles, unit-tests, and runs every example's `main`): `just test-examples`
- Run a single test: `cargo nextest run <test_name>` (or `cargo nextest run -E 'test(<pattern>)'`)
- Lint (must pass, matches CI): `just lint` = `clippy` + `clippy-features` + `fmt-check` + `typos`
  - `just clippy` → `cargo clippy --all --all-targets -- --deny warnings`
  - `just clippy-features` → same, for `--no-default-features` and `--features slab,bumpalo,blink-alloc`
  - `just clippy-fix` — autofix if working dir is clean; `just clippy-fix-now` — autofix even if dirty
  - `just fmt` / `just fmt-check`
- Typo check: `just typos` / `just typos-fix`
- Miri (memory-safety check, required before considering unsafe changes done): `just miri` = `cargo +nightly miri nextest run --tests --examples` + `cargo +nightly miri test --doc`
- Benchmarks (criterion): `just bench` (quick smoke run of rougenoir's own suite), `just bench-full` (whole matrix incl. the 1M out-of-cache size), `just bench-compare` (vs `std::collections::BTreeMap` and the `rbtree` crate). Regression workflow: `just bench-baseline <name>` before a change, `just bench-cmp <name>` after. See [docs/contributing.md](docs/contributing.md#benchmarking) for the full story — run modes, input shapes, and how to get stable numbers. Bare `cargo bench` (no `--bench`) currently fails to compile because the crate's unit-test target uses `debug_assertions`-gated helpers that vanish in release; the `just` targets sidestep it with explicit `--bench`.
- Docs: `just doc` (`cargo doc --no-deps --open`)
- One-time setup: `just setup` (installs `cargo-nextest`, `typos-cli`, the `nightly` toolchain, and `miri`)

### Allocator features

The collection layer (`Tree`/`CachedTree`/`Set`) picks its node backing store
at compile time. The default (nothing enabled) is the historical leaked-`Box`
behaviour (`alloc::Global`). Optional backends:

- `slab` — `alloc::Slab`, a local slab-of-chunks pool (rougenoir's own code,
  **not** the `slab` crate).
- `bumpalo` / `blink-alloc` — adapters for `&bumpalo::Bump` / `&blink_alloc::BlinkAlloc`.
- `nightly` — `alloc::Std<A>`, bridging any `core::alloc::Allocator`. Enables
  `#![feature(allocator_api)]`, so it **requires `cargo +nightly`**.

Targets that exercise them: `just test-features` (all stable backends),
`just test-nightly` (+ the nightly bridge), `just miri-features`,
`just miri-nightly`, `just clippy-features` (folded into `just lint`).

CI (`just lint && just test-examples && just miri`) is the bar for any change — always run all three before considering work done, especially anything touching `unsafe` code or `examples/`. When a change touches the allocator layer, also run `just test-features` / `just test-nightly` and the matching `miri-*` targets.

## Architecture

- **`src/intrusive/link.rs`** — `Link`: the actual embeddable rb-tree node (`parent_color`/`left`/`right`), non-generic. Every structural operation is a `NonNull<Link>`-taking associated function (never `&self`/`&mut self`) that reads/writes fields via `ptr::addr_of!`/`addr_of_mut!` instead of ever materializing a `&Link`/`&mut Link` reference. This is load-bearing, not stylistic — see the invariant below.
- **`src/intrusive/adapter.rs`** — `Adapter`: `get_link`/`get_value` do the `container_of()`-style pointer arithmetic (offset from `core::mem::offset_of!`) between a `Value` and its embedded `Link`; default methods (`left`, `right`, `parent`, `next`, `prev`, `set_color`) give `Value`-level navigation without exposing `Link`'s own primitives outside the crate. `intrusive_adapter!` generates an `Adapter` impl for one named `Link` field of a **non-generic** value type — a generic value type (`Node<K, V>`, or `examples/interval_tree.rs`'s `IntervalNode<K, V>`) needs its `Adapter` written by hand instead (see `NodeAdapter<K, V>` in `src/lib.rs`).
- **`src/intrusive/node_ptr.rs`** — `LinkPtrExt`/`LinkPtrMut`, both `pub(crate)`: fluent, `None`-propagating navigation/mutation on a bare `NodePtr<Link>`, delegating to `Link`'s own functions. This is crate-internal vocabulary for `intrusive::Root`'s Case 1–4 algorithm (which is written throughout in terms of possibly-null `NodePtr<Link>` locals, mirroring the kernel's implicit-null-pointer C style) — not a public API. A caller with an already-live `NonNull<Link>` (as every consumer has, e.g. `RawIter`) uses `Link::left`/`right`/`parent`/`next`/`prev` (now `pub`) directly instead.
- **`src/intrusive/root.rs`** — `intrusive::Root<A: Adapter, C>`: `insert` (rebalancing after insertion), `erase_augmented`/`erase_color` (deletion + rebalancing), rotations — **the only copy of the kernel's Case 1–4 logic in the crate**. `first_of`/`last_of`/`validate_of` are free functions (not methods) specifically so `crate::Root<K, V, C>` can reuse them without constructing a whole `intrusive::Root` (which would force an unwanted `TreeCallbacks` bound on callers that don't need one).
- **`src/intrusive/callbacks.rs`** — `intrusive::TreeCallbacks` (the augmentation trait, `NonNull<Value>`-based — distinct from `crate::TreeCallbacks`, which is `&mut Node<K, V>`-based) and `intrusive::Noop`.
- **`src/node.rs`** — `Node<K, V>`'s methods (`new`, `left`/`right`/`parent`/`next`/`prev`, `set_*`). `Node<K, V>` is never itself embedded in anything, so these stay ordinary `&self`/`&mut self` methods; each converts to/from the embedded `Link` via `Node::link_ptr`/`Node::from_link` (in `src/lib.rs`) and delegates to the matching `Link::*` function.
- **`src/lib.rs`** — core shared types: `Color`, `ParentColor<N>`, `Node<K, V>` (now `{ link: Link, key: K, value: V }`), `NodePtr<N> = Option<NonNull<N>>`, `NodeAdapter<K, V>` (`Node<K, V>`'s hand-written `Adapter`), `crate::TreeCallbacks`/`crate::Noop` (the `Tree`/`CachedTree`/`Set`-facing augmentation trait), `Root<K, V, C>`'s struct definition, and `Root::dealloc`. Tier 2 navigation (`Node<K, V>`'s own `left`/`right`/`parent`/`next`/`prev`) lives in `src/node.rs` as ordinary safe `&self` methods, not through any extension trait.
- **`src/root.rs`** — `Root<K, V, C>`'s `insert`/`erase`/`first`/`last`/`validate`: thin delegation to `intrusive::Root`, converting `NodePtr<Node<K, V>>` ↔ `NodePtr<Link>` at the boundary via a `CallbackBridge` that adapts `crate::TreeCallbacks` to `intrusive::TreeCallbacks`. Holds no rebalancing logic of its own.
- **`src/tree.rs`** — `Tree<K, V, C>`: the ordered-map-like API (`insert`, `remove`, `get`, `first`/`last`, `Index`, `Clone`, `Drop`, etc.) built on `Root`. `C` is the `TreeCallbacks` implementation (defaults to `Noop` via `Tree::new()`; use `Tree::with_callbacks(...)` for augmentation).
- **`src/cached_tree.rs`** — `CachedTree<K, V, C>`: like `Tree` but caches the leftmost (minimum) node pointer for O(1) `first()`.
- **`src/set.rs`** — `Set<T, C>`: a thin wrapper around `Tree<T, (), C>`.
- **`src/iter/`** — iterator implementations (`Iter`, `Keys`, `Values`, in-order/postorder cursors) split per collection: `iter/tree.rs`, `iter/cached_tree.rs`, `iter/set.rs`, `iter/node.rs` (shared traversal primitives).
- **`src/alloc/`** — the node backing store for `Tree`/`CachedTree`/`Set`.
  - **`mod.rs`** — the `Allocator` trait (a type-erased subset of `core::alloc::Allocator`: `allocate(Layout)`/`deallocate`, `&self`, stable-address contract), `Global` (the default — `std::alloc::{alloc,dealloc}`, ≡ the old leaked `Box`), and the `pub(crate)` node helpers `alloc_node`/`drop_node`/`take_node` (the only place `Layout`/`cast`/`ptr::write` boilerplate lives). `crate::Root<K, V, C, A = Global>` carries the `alloc` and `Root::dealloc` frees through it; `intrusive::` never allocates and is untouched.
  - **`slab.rs`** (`feature = "slab"`) — `Slab`, a local slab-of-chunks pool: cache-line-aligned chunks that never move, an intrusive free list through dead slots, geometric chunk growth. The recommended non-default backend.
  - **`bumpalo.rs`** / **`blink.rs`** (`feature = "bumpalo"` / `"blink-alloc"`) — `unsafe impl Allocator for &Bump` / `&BlinkAlloc` via each crate's inherent `Layout` allocation; `deallocate` is a no-op (bump semantics — `remove` runs `Drop` but doesn't reclaim the slot; no `Clone`/`Default`/`clear`).
  - **`nightly.rs`** (`feature = "nightly"`) — `Std<A>`, a wrapper bridging any `core::alloc::Allocator`. Enables `#![feature(allocator_api)]`, hence `cargo +nightly`.
- **`examples/interval_tree.rs`** — a custom augmented interval tree built directly on `rougenoir::intrusive` (not `Tree`/`Node`): `IntervalNode<K, V>` embeds a `Link` and owns its own allocation/deallocation by hand, since the intrusive API never owns memory. Its `Adapter` is hand-written since `IntervalNode<K, V>` is generic.
- **`examples/multi_index.rs`** — one `Employee` allocation embedding *two* `Link` fields, each in its own independent tree (`by_id`, `by_name`) via its own `intrusive_adapter!`-generated `Adapter` — the actual point of the offset-based `Adapter` design (one object, more than one intrusive tree membership, no extra allocation) over a simpler single-membership alternative that was considered and rejected for this crate.
- **`benches/harness/mod.rs`** — shared benchmark scaffolding: the `Shape` enum (six insertion orders — ascending, descending, shuffled, random, adversarial/bit-reversal, duplicates), deterministic `ChaCha8`-seeded key generators (`keys(shape, n)` — every implementation under test sees the *identical* sequence), the geometric size ladder (`sizes()` — one point per cache regime, not a dense list of L2-resident sizes), and `configure()` (per-group throughput + sample counts scaled to size). Run mode comes from the environment: `BENCH_QUICK` / (none) / `BENCH_FULL`, plus `BENCH_SIZES=a,b,c` for a one-off. It's a *directory* module (`benches/harness/mod.rs`, `mod harness;`) because Cargo auto-discovers `benches/*.rs` as bench targets but not subdirectory files (and `autobenches = false` in `Cargo.toml` makes the `[[bench]]` list explicit).
- **`benches/rougenoir.rs`** — the regression suite: rougenoir's own types only. Groups isolate one thing each — `insert` (build from empty, per shape), `get` (hits + misses), `remove` (delete-rebalance over a fresh `Clone` each iter), `iter` (both directions), `pop_first` (`Tree` vs `CachedTree` — the cache's whole reason to exist), `augmented` (`Noop` vs an order-statistics callback, pricing `propagate`), `churn` (steady-state mixed op stream), `bulk` (`clone`/`drop`), `costly_key` (`String` keys). Mutation benches use `iter_batched*` so setup/teardown isn't timed; reads run against a prebuilt tree.
- **`benches/compare.rs`** — rougenoir vs `std::collections::BTreeMap` vs the `rbtree` crate, `insert`/`get`/`remove`/`iter`, two shapes. Separate target because it ~triples measurement time and answers an occasional question, not a per-commit one.
- **`benches/allocators.rs`** — rougenoir's own tree across node backing stores (`Global`/`Slab`/`&bumpalo::Bump`/`&blink_alloc::BlinkAlloc`), `insert`/`get`/`iter`/`drop`/`churn`. `required-features = ["slab", "bumpalo", "blink-alloc"]`; run via `just bench-allocators`. Uses bench-local `OwnedBump`/`OwnedBlink` newtypes so a routine can return the tree (drop untimed) as the `Global`/`Slab` cases do — the allocation path is identical to the public `&Bump` adapter. Separate target for the same reason as `compare.rs`: you pick a backend once.

### Key invariants / conventions to preserve

- Parent+color packing (`ParentColor<N>`) is load-bearing for memory layout — don't split it into separate fields without understanding why the kernel (and this port) avoid that.
- **`Link`'s structural fields must never be touched through a `&Link`/`&mut Link` reference** — every operation on it takes `NonNull<Link>` and uses `ptr::addr_of!`/`addr_of_mut!`. A `Link` is always narrower than the struct embedding it, and a pointer derived from a `&Link` reference is only valid (under Stacked Borrows) for `size_of::<Link>()` bytes; widening it back out to the full struct via `Adapter::get_value` is real, Miri-catchable UB. Match this discipline for any new `Link`-level code.
- Public safe API surface is `Tree`/`CachedTree`/`Set`. `Node`/`Root`/`TreeCallbacks` (the original, `Node<K, V>`-owning low-level API) and `rougenoir::intrusive::{Link, Adapter, Root, TreeCallbacks}` (the genuinely intrusive low-level API) are both intentionally exposed for building custom augmented structures — reach for `Node`/`Root` when the crate should own `K`/`V` and allocation, `intrusive` when you want to embed the tree link in your own struct and own allocation yourself.
- A navigation/mutation primitive is public only if there's a real external consumer for it, and it's `unsafe fn` if its precondition ("points at a live `Link`/`Value`") isn't already enforced by the type system. `Link`'s read-navigation (`left`/`right`/`parent`/`next`/`prev`/`is_red`) and `Adapter`'s default methods meet that bar and are `pub`. `Link`'s mutating primitives (`set_left`, `set_right`, `set_parent`, ...) and the fluent, `None`-propagating `LinkPtrExt`/`LinkPtrMut` traits in `src/intrusive/node_ptr.rs` don't — using them directly instead of `Root::insert`/`erase` silently corrupts the tree — so they stay `pub(crate)`, engine-internal only.
- Any `unsafe` block should carry a `// SAFETY:` comment justifying it (existing code follows this convention throughout the crate); match that style for new unsafe code.
- The allocator parameter `A` is threaded as `Tree<K, V, C, A = Global>` (likewise `CachedTree`/`Set`/`crate::Root`). `Tree`/`CachedTree`/`Set` carry a `where A: Allocator` **bound on the struct itself** (required — their `Drop` calls `Allocator` methods; matches `std::collections::BTreeMap`), so every impl repeats `A: Allocator`. `Clone`/`Default`/`FromIterator`/`clear` additionally need `A: Default` (they build into a *fresh* `A::default()`, so a `&Bump`-backed tree has none of them). New `Allocator` impls must honour the stable-address contract (never relocate a live allocation) and be Miri-clean; add a per-backend equivalence test against `Global`.
- Changes to rebalancing must be made in **`src/intrusive/root.rs` only** — it's the sole copy of the kernel's Case 1–4 logic; `src/root.rs` delegates to it rather than reimplementing it. Validate any change with both the `validate()`/`validate_of()` invariant checker (used in property tests) and `just miri` — this is where most memory-safety risk in the crate concentrates.
- Benchmark inputs are deterministic and shared: never introduce `thread_rng` or an unseeded RNG into `benches/`, and never generate a fresh key sequence per implementation inside a comparison — both defeat the point (comparing implementations on the same work, reproducibly). New shapes/ops go in `benches/harness/mod.rs` so both bench targets get them. Keep the size ladder geometric and regime-spanning, not dense.

## Contribution/commit conventions

JJ is used to maintain this repository, but **NEVER** Never commit anything!
