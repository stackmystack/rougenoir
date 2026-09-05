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
- Lint (must pass, matches CI): `just lint` = `clippy` + `fmt-check` + `typos`
  - `just clippy` → `cargo clippy --all --all-targets -- --deny warnings`
  - `just clippy-fix` — autofix if working dir is clean; `just clippy-fix-now` — autofix even if dirty
  - `just fmt` / `just fmt-check`
- Typo check: `just typos` / `just typos-fix`
- Miri (memory-safety check, required before considering unsafe changes done): `just miri` = `cargo +nightly miri nextest run --tests --examples` + `cargo +nightly miri test --doc`
- Benchmarks: `just bench` (`cargo bench`, criterion, compares against `std::collections::BTreeMap`)
- Docs: `just doc` (`cargo doc --no-deps --open`)
- One-time setup: `just setup` (installs `cargo-nextest`, `typos-cli`, and `miri`)

CI (`just lint && just test-examples && just miri`) is the bar for any change — always run all three before considering work done, especially anything touching `unsafe` code or `examples/`.

## Architecture

- **`src/intrusive/link.rs`** — `Link`: the actual embeddable rb-tree node (`parent_color`/`left`/`right`), non-generic. Every structural operation is a `NonNull<Link>`-taking associated function (never `&self`/`&mut self`) that reads/writes fields via `ptr::addr_of!`/`addr_of_mut!` instead of ever materializing a `&Link`/`&mut Link` reference. This is load-bearing, not stylistic — see the invariant below.
- **`src/intrusive/adapter.rs`** — `Adapter`: `get_link`/`get_value` do the `container_of()`-style pointer arithmetic (offset from `core::mem::offset_of!`) between a `Value` and its embedded `Link`; default methods (`left`, `right`, `parent`, `next`, `prev`, `set_color`) give `Value`-level navigation without exposing `Link`'s own primitives outside the crate. `intrusive_adapter!` generates an `Adapter` impl for one named `Link` field of a **non-generic** value type — a generic value type (`Node<K, V>`, or `examples/interval_tree.rs`'s `IntervalNode<K, V>`) needs its `Adapter` written by hand instead (see `NodeAdapter<K, V>` in `src/lib.rs`).
- **`src/intrusive/node_ptr.rs`** — `NodePtrExt`/`NodePtrImplExt` for `NodePtr<Link>`, delegating to `Link`'s own functions.
- **`src/intrusive/root.rs`** — `intrusive::Root<A: Adapter, C>`: `insert` (rebalancing after insertion), `erase_augmented`/`erase_color` (deletion + rebalancing), rotations — **the only copy of the kernel's Case 1–4 logic in the crate**. `first_of`/`last_of`/`validate_of` are free functions (not methods) specifically so `crate::Root<K, V, C>` can reuse them without constructing a whole `intrusive::Root` (which would force an unwanted `TreeCallbacks` bound on callers that don't need one).
- **`src/intrusive/callbacks.rs`** — `intrusive::TreeCallbacks` (the augmentation trait, `NonNull<Value>`-based — distinct from `crate::TreeCallbacks`, which is `&mut Node<K, V>`-based) and `intrusive::Noop`.
- **`src/node.rs`** — `Node<K, V>`'s methods (`new`, `left`/`right`/`parent`/`next`/`prev`, `set_*`). `Node<K, V>` is never itself embedded in anything, so these stay ordinary `&self`/`&mut self` methods; each converts to/from the embedded `Link` via `Node::link_ptr`/`Node::from_link` (in `src/lib.rs`) and delegates to the matching `Link::*` function.
- **`src/lib.rs`** — core shared types: `Color`, `ParentColor<N>`, `Node<K, V>` (now `{ link: Link, key: K, value: V }`), `NodePtr<N> = Option<NonNull<N>>`, `NodeAdapter<K, V>` (`Node<K, V>`'s hand-written `Adapter`), `NodePtrExt`/`NodePtrImplExt` for `NodePtr<Node<K, V>>` (bridging to `Link` via `NodeAdapter`), `crate::TreeCallbacks`/`crate::Noop` (the `Tree`/`CachedTree`/`Set`-facing augmentation trait), `Root<K, V, C>`'s struct definition, and `Root::dealloc`.
- **`src/root.rs`** — `Root<K, V, C>`'s `insert`/`erase`/`first`/`last`/`validate`: thin delegation to `intrusive::Root`, converting `NodePtr<Node<K, V>>` ↔ `NodePtr<Link>` at the boundary via a `CallbackBridge` that adapts `crate::TreeCallbacks` to `intrusive::TreeCallbacks`. Holds no rebalancing logic of its own.
- **`src/tree.rs`** — `Tree<K, V, C>`: the ordered-map-like API (`insert`, `remove`, `get`, `first`/`last`, `Index`, `Clone`, `Drop`, etc.) built on `Root`. `C` is the `TreeCallbacks` implementation (defaults to `Noop` via `Tree::new()`; use `Tree::with_callbacks(...)` for augmentation).
- **`src/cached_tree.rs`** — `CachedTree<K, V, C>`: like `Tree` but caches the leftmost (minimum) node pointer for O(1) `first()`.
- **`src/set.rs`** — `Set<T, C>`: a thin wrapper around `Tree<T, (), C>`.
- **`src/iter/`** — iterator implementations (`Iter`, `Keys`, `Values`, in-order/postorder cursors) split per collection: `iter/tree.rs`, `iter/cached_tree.rs`, `iter/set.rs`, `iter/node.rs` (shared traversal primitives).
- **`src/alloc.rs`** — node allocation/deallocation (`leak_alloc_node`, `own_back`); nodes are boxed and leaked into raw pointers, owned back explicitly on drop/removal. There is currently no custom allocator (see "Nice to Have" in README) — this is the main place a future allocator API would plug in.
- **`examples/interval_tree.rs`** — a custom augmented interval tree built directly on `rougenoir::intrusive` (not `Tree`/`Node`): `IntervalNode<K, V>` embeds a `Link` and owns its own allocation/deallocation by hand, since the intrusive API never owns memory. Its `Adapter` is hand-written since `IntervalNode<K, V>` is generic.
- **`examples/multi_index.rs`** — one `Employee` allocation embedding *two* `Link` fields, each in its own independent tree (`by_id`, `by_name`) via its own `intrusive_adapter!`-generated `Adapter` — the actual point of the offset-based `Adapter` design (one object, more than one intrusive tree membership, no extra allocation) over a simpler single-membership alternative that was considered and rejected for this crate.

### Key invariants / conventions to preserve

- Parent+color packing (`ParentColor<N>`) is load-bearing for memory layout — don't split it into separate fields without understanding why the kernel (and this port) avoid that.
- **`Link`'s structural fields must never be touched through a `&Link`/`&mut Link` reference** — every operation on it takes `NonNull<Link>` and uses `ptr::addr_of!`/`addr_of_mut!`. A `Link` is always narrower than the struct embedding it, and a pointer derived from a `&Link` reference is only valid (under Stacked Borrows) for `size_of::<Link>()` bytes; widening it back out to the full struct via `Adapter::get_value` is real, Miri-catchable UB. Match this discipline for any new `Link`-level code.
- Public safe API surface is `Tree`/`CachedTree`/`Set`. `Node`/`Root`/`TreeCallbacks` (the original, `Node<K, V>`-owning low-level API) and `rougenoir::intrusive::{Link, Adapter, Root, TreeCallbacks}` (the genuinely intrusive low-level API) are both intentionally exposed for building custom augmented structures — reach for `Node`/`Root` when the crate should own `K`/`V` and allocation, `intrusive` when you want to embed the tree link in your own struct and own allocation yourself.
- Any `unsafe` block should carry a `// SAFETY:` comment justifying it (existing code follows this convention throughout the crate); match that style for new unsafe code.
- Changes to rebalancing must be made in **`src/intrusive/root.rs` only** — it's the sole copy of the kernel's Case 1–4 logic; `src/root.rs` delegates to it rather than reimplementing it. Validate any change with both the `validate()`/`validate_of()` invariant checker (used in property tests) and `just miri` — this is where most memory-safety risk in the crate concentrates.

## Contribution/commit conventions

JJ is used to maintain this repository, but **NEVER** Never commit anything!
