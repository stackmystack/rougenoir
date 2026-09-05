# rougenoir

This file provides guidance on working with code in this repository.

## What this is

`rougenoir` is a Rust port of the Linux kernel's red-black tree (`rbtree.c`/`rbtree_augmented.h`), exposed as safe-ish collection types (`Tree`, `CachedTree`, `Set`) plus a low-level `unsafe` API for building custom augmented trees. It is not an intrusive data structure like the kernel's — nodes own `K`/`V` directly.

## Commands

All common tasks are wired through `just` (see `justfile`); the underlying `cargo`/`cargo-nextest` commands are shown too.

- Build: `just build` (`cargo build`)
- Test: `just test` (`cargo nextest run --tests --examples` + `cargo test --doc` — doctests don't run under nextest, so both are required)
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

CI (`just lint && just miri`) is the bar for any change — always run both before considering work done, especially anything touching `unsafe` code.

## Architecture

The crate is organized as one red-black tree engine (`Root`/`Node`) with three collection wrappers built on top of it.

- **`src/node.rs`** — `Node<K, V>` layout and pointer-chasing primitives: `next()`/`prev()` (in-order successor/predecessor), `left_deepest_node()`, `next_postorder()`. Colors are *not* stored as a separate field: `parent_color` (defined in `src/lib.rs`) packs the parent pointer and the red/black bit into the low bit of the pointer address (mirrors the kernel's trick). All pointer/color mutation on nodes goes through `ParentColor`.
- **`src/lib.rs`** — core types shared across the crate: `Color`, `ParentColor`, `Node<K, V>`, `NodePtr<K, V>` (= `Option<NonNull<Node<K, V>>>`), and two extension traits on `NodePtr`:
  - `NodePtrExt` — safe-ish public helpers (`left`, `right`, `parent`, `is_red`, `next_node`, …).
  - `NodePtrImplExt` (`pub(crate)`) — internal mutation helpers (`set_left`, `set_parent_and_color`, `red_parent`, …) used by the rebalancing algorithms.
  Also defines `TreeCallbacks` (the augmentation trait: `propagate`, `copy`, `rotate`) and `Noop`, the default no-op callback implementation.
- **`src/root.rs`** — the actual red-black tree algorithms: `insert` (rebalancing after insertion), `erase` (deletion + rebalancing), rotations, and `validate` (checks RB invariants, used in tests). This is where the kernel's `rbtree.c` logic lives, translated to Rust. `TreeCallbacks` hooks (`propagate`/`rotate`/`copy`) are invoked here at the points the kernel calls `rb_augment_*`, which is what lets augmented trees (e.g. interval trees) keep derived per-subtree data up to date across rotations.
- **`src/tree.rs`** — `Tree<K, V, C>`: the ordered-map-like API (`insert`, `remove`, `get`, `first`/`last`, `Index`, `Clone`, `Drop`, etc.) built on `Root`. `C` is the `TreeCallbacks` implementation (defaults to `Noop` via `Tree::new()`; use `Tree::with_callbacks(...)` for augmentation).
- **`src/cached_tree.rs`** — `CachedTree<K, V, C>`: like `Tree` but caches the leftmost (minimum) node pointer for O(1) `first()`.
- **`src/set.rs`** — `Set<T, C>`: a thin wrapper around `Tree<T, (), C>`.
- **`src/iter/`** — iterator implementations (`Iter`, `Keys`, `Values`, in-order/postorder cursors) split per collection: `iter/tree.rs`, `iter/cached_tree.rs`, `iter/set.rs`, `iter/node.rs` (shared traversal primitives).
- **`src/alloc.rs`** — node allocation/deallocation (`leak_alloc_node`, `own_back`); nodes are boxed and leaked into raw pointers, owned back explicitly on drop/removal. There is currently no custom allocator (see "Nice to Have" in README) — this is the main place a future allocator API would plug in.
- **`examples/interval_tree.rs`** — the canonical example of using the low-level `Root`/`TreeCallbacks` API directly (not `Tree`) to build an augmented interval tree, following the kernel docs' interval tree recipe.

### Key invariants / conventions to preserve

- Parent+color packing (`ParentColor`) is load-bearing for memory layout — don't split it into separate fields without understanding why the kernel (and this port) avoid that.
- Public safe API surface is `Tree`/`CachedTree`/`Set`; `Node`, `Root`, and the `unsafe` leak/link/dealloc functions are the intentionally-exposed low-level API for custom augmented structures (see `NodePtrImplExt` staying `pub(crate)` while `NodePtrExt` is public — that boundary is deliberate).
- Any `unsafe` block should carry a `// SAFETY:` comment justifying it (existing code follows this convention throughout `node.rs`/`root.rs`/`lib.rs`); match that style for new unsafe code.
- Changes to rebalancing (`root.rs`) must be validated with both the `validate()` invariant checker (used in property tests) and `just miri` — this is where most memory-safety risk in the crate concentrates.

## Contribution/commit conventions

JJ is used to maintain this repository, but **NEVER** Never commit anything!
