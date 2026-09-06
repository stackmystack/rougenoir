# Allocation & cache-locality: landscape review

Status: the pluggable-allocator plan that came out of this review has
**landed** — see [`allocators.md`](allocators.md). Shipped: the type-erased
`alloc::Allocator` seam with `Global` as default (§3a/§2), the `slab`
feature's `Slab` pool (§3c / Family A), the `bumpalo` and `blink-alloc`
adapters (§3b), and the `nightly` `Std<A>` bridge to `core::alloc::Allocator`
(§6). Deferred: Family B (index-based nodes / `FlatTree`), Family C
(`compact()` / traversal-order rebuild), and any benchmarking of the above.

The rest of this document is the original landscape review that motivated
that work.

## 1. Where the time actually goes

Every node is `Box::into_raw(Box::new(Node { link, key, value }))`
(`src/alloc.rs`), i.e. one global-allocator call per node, leaked, owned

## 1. Where the time actually goes

Every node is `Box::into_raw(Box::new(Node { link, key, value }))`
(`src/alloc.rs`), i.e. one global-allocator call per node, leaked, owned
back individually on `remove`/`drop`.

`Node<K, V>` layout (`#[repr(C)]`, `src/lib.rs`):

| field  | type                        | size (64-bit) |
| ------ | --------------------------- | ------------- |
| `link` | `Link { parent_color, left, right }` | 24 B  |
| `key`  | `K`                         | e.g. 8 B      |
| `value`| `V`                         | e.g. 8 B      |

So a `Tree<u64, u64>` node is 40 B. `Link` alone — the part every
tree-structural operation touches — is 24 B, three words.

The README's own numbers (i7-7700HQ, 64 Ki, random keys):

| op     | `BTreeMap` | rougenoir | ratio |
| ------ | ---------: | --------: | ----- |
| insert |        137 |       279 | 2.0×  |
| lookup |        124 |       255 | 2.1×  |
| remove |        133 |       272 | 2.0×  |
| iterate|        1.7 |        35 | 20×   |

Two distinct costs are bundled here:

1. **`malloc`/`free` call overhead** — one per node on the write path.
   Removable with any pooled/bump strategy.
2. **Pointer chasing with no spatial locality** — a root-to-leaf descent
   touches ~`log2(n)` nodes (RB height ≤ `2·log2(n+1)`; ~18–22 at 64 Ki)
   that sit at addresses unrelated to key order, so each level is a
   probable cache miss. `BTreeMap` packs 11 keys/node, is ~5 levels deep at
   64 Ki, and touches 1–2 lines per level. This is the dominant gap on
   random-access and the *iteration* blowout (following `next()` links out
   of cache vs scanning an array).

Allocation strategy alone fixes (1) and part of (2). The rest of (2) needs
the node layout and/or the in-memory *order* of nodes to change.

## 2. The constraint that shapes every option

The engine (`src/intrusive/`) is written end-to-end in terms of
`NonNull<Link>` / `NodePtr<Link> = Option<NonNull<Link>>`, and
`ParentColor<Link>` packs a real `*mut Link` with the colour in bit 0. The
rebalancing algorithm — the kernel Case 1–4 logic in
`src/intrusive/root.rs`, the *only* copy in the crate — never materialises a
`&Link`; it only chases raw pointers (this is a load-bearing soundness
invariant, see `CLAUDE.md`).

`src/root.rs` deliberately makes `Tree`/`CachedTree`/`Set` reuse that exact
pointer-based engine rather than keep their own copy (recent commits
the "retrofit insert / narrow NodePtrExt" commits). Any option that stops the collection
layer being expressible as raw `Link` pointers *un-does that
consolidation*.

This splits the solution space cleanly:

- **Family A — keep raw pointers, control the backing store.** Needs an
  allocator that hands out **stable addresses** (never relocates a live
  allocation). Slots into the `src/alloc.rs` seam with near-zero engine
  change. The `intrusive::` core is untouched and still shared.
- **Family B — indices instead of pointers.** `left`/`right`/`parent`
  become `u32` into a single backing `Vec<Node>`. Smaller nodes, one
  contiguous allocation, relocatable storage. But it is a real rewrite of
  `link.rs` / `node_ptr.rs` / `root.rs` / the adapter / iterators, it kills
  the `ParentColor` pointer-tag trick, and — crucially — the genuinely
  intrusive public API (`intrusive::Link` embedded in a user's own struct,
  user owns allocation) is inherently pointer-based and gets no benefit, so
  the collection layer would fork away from the shared engine again.
- **Family C — locality rebuilding.** Orthogonal: lay nodes out in
  traversal order at bulk-build / `clone` / an explicit `compact()`. This is
  the only thing that attacks the *random insertion order ≠ key order*
  penalty directly. Best combined with A.

## 3. Family A — stable-address backing store

### 3a. Drop-in global allocator (zero code)

`#[global_allocator]` with `mimalloc`, `jemallocator` /
`tikv-jemalloc-allocator`, or `snmalloc`. Costs nothing, is a legitimate
data point, typically buys 10–25 % on alloc-heavy paths and a little
locality (better size-class packing → freed slots reused nearby). Does
**not** fix key-order locality. Worth measuring first purely to know the
floor.

### 3b. Bump arena (`bumpalo`, `typed-arena`, `blink-alloc`)

Chunked, never relocates, so raw `Link` pointers stay valid. Allocation is
a pointer bump. `bumpalo` with the `allocator-api2` feature gives
`Box::new_in(&bump, node)` on stable.

- **Wins:** removes `malloc` overhead; nodes land in *insertion-temporal*
  order (= address order within a chunk); `drop`/`clear` becomes "drop the
  chunks" instead of `n` frees + a traversal; `Clone` becomes a fast
  bulk copy.
- **Loses:** no per-node free. `remove` / `pop_*` can't return memory —
  they'd leak the slot until the whole tree drops. Fine for
  build-once/iterate/drop and for `Set` used as a dedup pass; not fine for a
  long-lived churning map without a compaction step.
- **Note:** insertion-temporal order only equals key order for
  `Ascending`/`Descending` shapes. On `Random` the layout is still
  key-scrambled — see Family C.

### 3c. Custom slab-of-chunks + intrusive freelist (Family A, full)

`Vec<Box<[MaybeUninit<Node>; CHUNK]>>` (chunk base cache-line aligned) plus
a freelist threaded through dead slots — reuse `Link.left` as the freelist
`next`, so no extra space. This is the kernel `kmem_cache` / `hashbrown`
model the README gestures at.

- **Wins:** everything 3b gives, **plus** O(1) per-node free and slot
  reuse, so `remove` works normally. Chunks never move → raw pointers safe.
  ~150–250 LOC, lives entirely behind `leak_alloc_node` / `own_back`.
- **Loses:** after churn, a freed slot from anywhere gets reused by the next
  insert, so locality slowly degrades back toward random — `compact()`
  (Family C) stays valuable for long-lived trees.
- This is the best effort-to-reward option that **keeps the architecture
  intact**: the `intrusive::` engine, the soundness invariants, and Miri
  coverage are all unchanged; `Tree` just gains an `A` type parameter.

### 3d. `slab` / `slotmap` / `thunderdome` / `generational-arena` / `id-arena`

All `Vec`-backed → **relocate on grow** → break raw `Link` pointers. Only
usable if you also move to indices (Family B). `slotmap`/`thunderdome` add
generational keys (ABA-safe handles) which the tree doesn't need
internally. Listed here so they're explicitly ruled out for Family A.

## 4. Family B — index-based nodes

`left/right/parent: Option<NonZeroU32>` (or a `u32::MAX` sentinel) into one
`Vec<Slot<Node>>`; colour packed in a high bit of the parent index or a
spare byte; freelist through the `Vec` for `remove`.

- **Wins:** `Link` drops from 24 B → 12 B (or 13 with a colour byte); a
  `Tree<u64,u64>` node 40 B → ~28 B → more nodes per line. Whole tree is one
  allocation, `realloc`-able freely (nothing holds node pointers),
  trivially `memcpy`-`Clone`d, serialisable. Cache-friendlier by default
  even before any layout work. Enables **SoA** cleanly (see §5).
- **Loses:** real rewrite of the engine; `ParentColor` pointer-tag trick
  gone; `intrusive::Link`-in-your-own-struct API gets nothing from it, so
  the collection layer forks from the shared engine (reverses the recent
  engine-consolidation work). Bounds the tree at `u32::MAX` nodes (probably
  fine; document it).
- **Still doesn't** fix random-insertion locality on its own — same
  temporal-vs-key-order problem, just with smaller nodes in one arena.
- Prior art: the `rbtree-arena` crate ("cache friendly red black tree where
  nodes live on sequential memory", Aug 2026) — index-based, `Vec` arena.
  Undocumented and unbenchmarked but worth reading the source.

If Family B is ever pursued, do it as a **separate type** (`FlatTree`?),
not a conversion of `Tree`, precisely because it can't share the
pointer-based engine.

## 5. Cache-locality techniques (orthogonal to the allocator)

- **Shrink the node.** `u32` indices (Family B), or arena-relative `u32`
  offsets even in Family A. Colour is already packed via `ParentColor`.
- **SoA / hot-cold split.** Store `(key, links)` contiguously and `value`
  in a parallel array. A search touches only keys+links and fetches the one
  `value` at the end. Large win when `V` is big; natural once nodes are
  index-addressed.
- **Traversal-order layout.** After a bulk build, place nodes **in-order**
  → `iter()` becomes a near-linear scan (closes the 20× iteration gap) and
  `next()`/`prev()` mostly stay on one line. Or **van Emde Boas / BFS**
  order → optimises root-to-leaf search instead. Can't optimise both; pick
  per use case or expose both.
- **`compact()` / arena-aware bulk build.** `CachedTree::clone` already
  does a bottom-up O(n) build from a sorted vector
  (`build_from_sorted_impl`) — that is exactly the hook: have it allocate
  into a fresh contiguous arena in in-order. Add `Tree::compact(&mut self)`
  for long-lived trees to re-pack after churn.
- **B-tree-ifying** (multiple keys per node) is the real route to
  `BTreeMap` parity, but that's a different data structure, not an
  rb-tree port — name it as the ceiling, out of scope.
- **Prefetch** the far child during descent (`core::arch` `_mm_prefetch`):
  marginal, low priority.
- **Don't over-align** individual nodes; do align chunk bases to 64 B so
  nodes don't needlessly straddle lines.

## 6. Crate landscape

| Crate / approach | Model | Stable addrs | Per-item free | Family | Notes |
| --- | --- | --- | --- | --- | --- |
| `mimalloc` / `jemallocator` / `snmalloc` as `#[global_allocator]` | general | yes | yes | A (free) | 0 code; alloc throughput + minor locality; no key-order fix |
| `bumpalo` | bump, chunked | yes | no (reset only) | A (3b) | `allocator-api2` feature → `Box::new_in` on stable |
| `typed-arena` | chunked, typed | yes | no | A (3b) | runs `Drop`; minimal API |
| `blink-alloc` | bump | yes | no | A (3b) | fast reset, `allocator-api2` |
| custom slab-of-chunks + freelist | `Vec<Box<[T; N]>>` | yes | yes | A (3c) | **the recommended engine** for `Tree`; ~150–250 LOC |
| `slab` | `Vec<Entry<T>>` | no | yes | B | `usize` keys; moves on grow |
| `slotmap` / `thunderdome` | `Vec` + generations | no | yes | B | ABA-safe handles the tree doesn't need internally |
| `generational-arena` / `id-arena` | `Vec` | no | some | B | |
| `hashbrown` `RawTable` | single `realloc`'d alloc | no | n/a | B-ish | README's idea; really an open-addressing/index model |
| `allocator-api2` | trait shim | — | — | plumbing | mirrors nightly `Allocator` on stable; dep of `hashbrown`, `bumpalo`; ~250M downloads |
| `rbtree-arena` | index arena rb-tree | — | — | B | prior art; undocumented, unbenchmarked |

**`Allocator` trait status (2026):** still unstable on nightly after ~a
decade; `allocator-api2` is the de-facto stable bridge and is widely
depended on. Blockers are zero-sized-layout handling, missing context
param, ZST `AllocError`, and the allocate/deallocate split — none of which
block *our* use. Practical takeaway: a `Tree<K, V, C, A = Global>` type
parameter over `allocator_api2::Allocator` is the idiomatic shape and
composes with `#[global_allocator]` and with `&Bump`.

## 7. Ginger Bill's arena series — how it maps

- His growing arena is a **linked list of blocks, never a `realloc`** —
  that *is* the stable-address requirement (§2, Family A).
- "Arenas make freeing free" — the `drop`/`clear` win in 3b/3c.
- His "free list within the arena" post = the §3c custom slab
  recommendation almost exactly.
- His temp/scratch scoped arenas map onto `Set`-as-a-dedup-pass and onto
  per-operation scratch (e.g. the `Vec<ComingFrom>` in `Root::dealloc`).

## 8. Suggested phasing (for the later design pass)

1. **Measure the floor.** Add an alloc-isolating bench (insert with the
   node store pre-reserved vs cold) and a cache-cold traversal bench to the
   harness. Try `#[global_allocator] = mimalloc` as a no-risk data point.
2. **Family A §3c custom slab** behind the `src/alloc.rs` seam, as
   `Tree<K, V, C, A = Global>`. Keeps the shared `intrusive::` engine and
   every soundness invariant. Expect: `malloc` overhead gone, insertion-
   temporal locality, much faster `drop`/`clone`.
3. **`compact()` + arena-aware bulk build** (Family C), piggybacking on
   `CachedTree`'s existing bottom-up builder. This is what beats the
   random-insertion penalty and narrows the iteration gap.
4. **Only if 2–3 leave a gap that matters:** prototype the index + SoA
   representation as a *separate* `FlatTree`, benchmark honestly against
   `BTreeMap`, decide whether it earns its maintenance cost.

## 9. Open questions for the design pass

- Allocator as a monomorphised `A: Allocator` type param (via
  `allocator-api2`) vs a bespoke `NodeAlloc` trait vs a hard-wired slab.
- Does the `intrusive` public API get any allocator story, or stay strictly
  "you own memory"? (Likely stays.)
- Freelist threading through `Link.left` in dead slots — confirm it's sound
  under the "never form `&Link`" invariant and Miri.
- `Send`/`Sync`: arena per-tree (keeps current `unsafe impl` reasoning) vs
  shared.
- `Clone` as chunk-`memcpy` + pointer fixup; `Drop` running `K`/`V`
  destructors by walking the live set vs a tracked count.
- Bump-only (§3b) as an opt-in `A` for build-once workloads, with
  `compact()`/`shrink_to_fit` to reclaim leaked slots.
- `u32` node-count cap if Family B is ever taken — document or feature-gate.

## Sources

- [bumpalo](https://github.com/fitzgen/bumpalo) ·
  [typed-arena](https://github.com/thomcc/rust-typed-arena) ·
  [allocator-api2](https://github.com/zakarumych/allocator-api2)
- [The State of Allocators in 2026](https://cetra3.github.io/blog/state-of-allocators-2026/)
- [Arenas in Rust — Manish Goregaokar](https://manishearth.github.io/blog/2021/03/15/arenas-in-rust/)
- [Guide to using arenas in Rust — LogRocket](https://blog.logrocket.com/guide-using-arenas-rust/)
- [rbtree-arena](https://crates.io/crates/rbtree-arena)
- [Linux rbtree docs](https://docs.kernel.org/core-api/rbtree.html)
- [Cache-sensitive Memory Layout for Binary Trees (van Emde Boas)](https://link.springer.com/content/pdf/10.1007/978-0-387-09680-3_17.pdf)
