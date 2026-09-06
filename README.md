# rougenoir

[![Crates.io](https://img.shields.io/crates/v/rougenoir.svg)](https://crates.io/crates/rougenoir)
[![Documentation](https://docs.rs/rougenoir/badge.svg)](https://docs.rs/rougenoir)
[![CI](https://github.com/stackmystack/rougenoir/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/stackmystack/rougenoir/actions/workflows/ci.yml)
[![License: GPL v2](https://img.shields.io/badge/License-GPL_v2-blue.svg)](https://www.gnu.org/licenses/old-licenses/gpl-2.0.en.html)

A Rust clone of linux' red-black trees.

The name of this library is French for redblack.

## Motivation

I wanted a red-black tree with callbacks and I couldn't find any I could hack to
my needs. I eventually stumbled upon the linux kernel's implementation and I
thought it would be an opportunity to play with `unsafe` rust … and so I did.

## Features

- Collections with an API close to that of [`std::collections`](https://doc.rust-lang.org/std/collections).
  - [`CachedTree`](https://docs.rs/rougenoir/latest/rougenoir/struct.CachedTree.html), a `Tree` where the leftmost entry is cached.
  - [`Set`](https://docs.rs/rougenoir/latest/rougenoir/struct.Set.html).
  - [`Tree`](https://docs.rs/rougenoir/latest/rougenoir/struct.Tree.html).
- A genuinely intrusive low-level API (`rougenoir::intrusive`), in the style of the Linux kernel's `struct rb_node` + `container_of()`: embed a `Link` directly in your own struct — even more than once, to belong to more than one tree at once — and rougenoir never allocates on your behalf.
  - See the [`interval_tree` example](examples/interval_tree.rs) (one embedded `Link`, augmented) and the [`multi_index` example](examples/multi_index.rs) (two `Link`s on the same struct, two independent trees).
- A second, simpler low-level API (`Node`/`Root`), where rougenoir owns `K`/`V` and allocation directly — what `Tree`/`CachedTree`/`Set` themselves are built on.
  - Notification on tree modification, aka [Augmentation](#augmentation).
- Checked with [`miri`](https://github.com/rust-lang/miri).

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
rougenoir = "0.1.0"
```

### Example

```rust
use rougenoir::Tree;

fn main() {
    let mut tree = Tree::new();

    tree.insert(1, "one".to_string());
    tree.insert(2, "two".to_string());
    tree.insert(3, "three".to_string());

    if let Some(value) = tree.get(&2) {
        println!("Found: {}", value);
    }

    for (key, value) in tree.iter() {
        println!("{}: {}", key, value);
    }

    tree.remove(&1);
}
```

## Augmentation

`rougenoir` supports tree augmentation, allowing you to maintain additional information about subtrees.

```rust
struct SizeAugmentation<K, V> {
    _phantom: std::marker::PhantomData<(K, V)>,
}

impl<K, V> TreeCallbacks for SizeAugmentation<K, V> {
    type Key = K;
    type Value = V;

    fn propagate(&self, node: Option<&mut Node<K, V>>, stop: Option<&mut Node<K, V>>) {
        // Listen to a propagation event.
    }

    fn copy(&self, old: &mut Node<K, V>, new: &mut Node<K, V>) {
        // Listen to a copy event.
    }

    fn rotate(&self, old: &mut Node<K, V>, new: &mut Node<K, V>) {
        // Listen to a rotate event.
    }
}
```

## Intrusive API

For full kernel-style intrusion, embed `rougenoir::intrusive::Link` directly:

```rust
struct Employee {
    by_id: Link,
    by_name: Link,
    id: u32,
    name: String,
}

intrusive_adapter!(ByIdAdapter = Employee: by_id);
intrusive_adapter!(ByNameAdapter = Employee: by_name);

type IdRoot = Root<ByIdAdapter, Noop<Employee>>;
type NameRoot = Root<ByNameAdapter, Noop<Employee>>;

struct EmployeeStore {
    by_id: IdRoot,
    by_name: NameRoot,
    len: usize,
}
```

See the [multi-index example](examples/multi_index.rs).

## Benchmarks

A criterion suite lives in [`benches/`](benches/): `just bench` for a quick
smoke run, `just bench-full` for the whole matrix, `just bench-compare` to
race the alternatives, `just bench-allocators` to race the node backing
stores. Method, input shapes and run modes are documented in
[docs/contributing.md](docs/contributing.md#benchmarking).

### The machine

|           |                                                                                     |
| --------- | ----------------------------------------------------------------------------------------- |
| CPU       | Intel Core i7-7700HQ — Kaby Lake, 4C/8T, 2.8 GHz base / 3.8 GHz turbo (**turbo on**)      |
| Cache     | L1d 32 KiB/core · L2 256 KiB/core · L3 6 MiB shared                                       |
| Memory    | 16 GiB DDR4                                                                              |
| OS        | Arch Linux, kernel 7.1.9, x86-64                                                         |
| Toolchain | rustc 1.92.0 / LLVM 21 · `--release` + `lto = "thin"` + `codegen-units = 1`              |
| criterion | 0.6 — 20 samples, 3 s + 0.75 s warm-up per point (`BENCH_PRECISE=1`)                      |
| Isolation | `taskset -c 2` · `powersave` governor                                                    |

It's a laptop, not a bench rig — turbo is on and the governor is
`powersave`. **The 4 Ki and 64 Ki rows are the trustworthy ones**; at
n = 256 the per-key cost is tens of nanoseconds and criterion-loop overhead
plus turbo drift swamp real differences, so read that row as an order of
magnitude, not a measurement. Even at scale, treat < 10 % as noise.

### Method

Every implementation is fed the **identical** key sequence from a fixed
`ChaCha8` seed. Figures are criterion's median as **nanoseconds per
element** — for `insert`, the per-key cost of building the whole tree from
empty; for `iterate`, per element walked. `n` is the tree size.

### vs `std::collections::BTreeMap` and the [`rbtree`](https://crates.io/crates/rbtree) crate

**insert** — build from empty (ns/key)

| n     | order     | `BTreeMap` | `rbtree` | rougenoir `Tree` | `CachedTree` |
| ----- | --------- | ---------: | -------: | ---------------: | -----------: |
| 256   | ascending |         31 |       67 |               53 |           50 |
| 256   | random    |         20 |       66 |               56 |           60 |
| 4 Ki  | ascending |         50 |       96 |               54 |           55 |
| 4 Ki  | random    |         74 |      102 |              130 |          133 |
| 64 Ki | ascending |         85 |      240 |              130 |          134 |
| 64 Ki | random    |        137 |      284 |              279 |          299 |

**lookup** — `get`, every key present (ns/key)

| n     | `BTreeMap` | `rbtree` | rougenoir |
| ----- | ---------: | -------: | --------: |
| 256   |         19 |        8 |         9 |
| 4 Ki  |         65 |       84 |        87 |
| 64 Ki |        124 |      264 |       255 |

**remove** — delete every key, random order (ns/key)

| n     | `BTreeMap` | `rbtree` | rougenoir |
| ----- | ---------: | -------: | --------: |
| 256   |         25 |       66 |        47 |
| 4 Ki  |         80 |      146 |       121 |
| 64 Ki |        133 |      339 |       272 |

**iterate** — in-order walk (ns/element)

| n     | `BTreeMap` | `rbtree` | rougenoir |
| ----- | ---------: | -------: | --------: |
| 256   |        1.3 |      2.6 |       3.1 |
| 4 Ki  |        1.4 |      8.7 |       7.3 |
| 64 Ki |        1.7 |       47 |        35 |

**Reading it**

- On **sorted** inserts rougenoir matches `BTreeMap` up to L2 (54 vs 50
  ns/key) and trails it ~1.5× out of cache; on **random** inserts `BTreeMap`
  is ~1.8–2× ahead from 4 Ki up. Same cause both times — `BTreeMap` packs
  many keys per cache line, rougenoir chases one `Box`-ed node per tree
  level. rougenoir is ~2× faster than `rbtree` on sorted inserts; on random
  inserts `rbtree` edges it in L2 and they converge out of cache.
- **Lookup**: `BTreeMap`'s cache density wins once the tree leaves L1 — 1.3×
  ahead at 4 Ki, 2× at 64 Ki. rougenoir tracks `rbtree` throughout.
- **Remove**: rougenoir is consistently ~1.3× faster than `rbtree` and
  ~1.5–2× slower than `BTreeMap`.
- **Iteration** is `BTreeMap`'s runaway — it scans an array while a pointer
  tree follows `next()` links out of cache. rougenoir still beats `rbtree`
  at scale.

### rougenoir across insertion orders (`Tree`, ns/key)

| order        | 4 Ki | 64 Ki | |
| ------------ | ---: | ----: | --- |
| ascending    |   56 |   140 | best case — every insert on the right spine |
| descending   |   67 |   134 | mirror image; the left spine |
| duplicates   |   58 |   103 | keys from a domain of `n/16` — ~15⁄16 of inserts take the update path, no alloc, no rebalance |
| adversarial  |  100 |   125 | a bit-reversal permutation — the textbook *unbalanced*-BST adversary; **benign** for a self-balancing tree |
| random       |  121 |   280 | realistic — no locality between successive keys |
| shuffled     |  147 |   284 | the *same keys* as `ascending`, so the ~2.5× gap is purely insertion *order* |

### What `CachedTree` buys

Draining the tree with `pop_first` until empty (ns/element):

| n     | `Tree` | `CachedTree` |
| ----- | -----: | -----------: |
| 256   |     30 |           27 |
| 4 Ki  |     56 |           32 |
| 64 Ki |     78 |           51 |

The cached leftmost pointer turns each pop's O(log n) descent into O(1).
The write-path tax is small — sorted insert is unchanged (55 vs 54 ns/key
at 4 Ki, 134 vs 130 at 64 Ki), random insert pays ~7 % out of cache.

### Augmentation is nearly free

`Noop` vs an order-statistics callback (every node caches its subtree size;
`propagate` runs to the root on each insert), ns/key:

| n     | `Noop` | order-stat | overhead |
| ----- | -----: | ---------: | -------: |
| 256   |     72 |         65 | ~0 (noise) |
| 4 Ki  |    166 |        172 |     +3 % |
| 64 Ki |    343 |        355 |     +3 % |

The propagate path is already cache-hot from the insertion descent, so the
extra work barely shows against the per-node allocation. (These use a
12-byte value, so the absolute numbers run above the `u64`-value insert
table.)

### Node backing store

By default every rougenoir node is its own leaked `Box`; the backing store
is a compile-time choice (see [Allocators](#allocators)). Numbers below are
`just bench-allocators` at `BENCH_PRECISE`, same machine as above.

**insert** — build from empty (ns/key)

| n     | order     | `Global` | `Slab` | `bumpalo` | `blink-alloc` |
| ----- | --------- | -------: | -----: | --------: | ------------: |
| 4 Ki  | ascending |       57 |     40 |        38 |            37 |
| 4 Ki  | random    |      123 |     98 |        94 |            93 |
| 64 Ki | ascending |      118 |     69 |        77 |            57 |
| 64 Ki | random    |      206 |    176 |       173 |           172 |

**drop** — tear the whole tree down (ns/element)

| n     | `Global` | `Slab` | `bumpalo` | `blink-alloc` |
| ----- | -------: | -----: | --------: | ------------: |
| 4 Ki  |       37 |     11 |        11 |            11 |
| 64 Ki |       45 |     20 |        19 |            19 |

`Global` pays a `malloc` per insert and a `free` per node at teardown; a
pool or bump arena drops both to near zero (the ~19 ns floor on `drop` is
the tree walk itself). Insert is **1.2–2× faster**, drop **~2.3× faster**.

**get / iter / churn** move far less — ~5 % on reads, ~15 % on a
`pop_first`+`insert` churn loop at 64 Ki. A pool gives *temporal* locality
(nodes sit in insertion order), and for a tree built from a shuffled stream
that is not key order, so a key-ordered walk or a random lookup still hops.
Closing that needs a compacting rebuild — see the
[research notes](docs/allocation-research.md) (Family C), not yet built.

> `bumpalo`/`blink-alloc` never reclaim a slot mid-life, so a long-running
> churn workload grows the arena unboundedly; `Slab` recycles through a free
> list. Pick the arena for build-then-drop, `Slab` for a long-lived map.

## Allocators

`Tree`/`CachedTree`/`Set` take an allocator type parameter,
`Tree<K, V, C, A = Global>`. The default `Global` is the historical
leaked-`Box` behaviour (and honours any `#[global_allocator]`). Opt into a
different backing store with a cargo feature and `*_in` constructor:

| feature | type | reclaims on `remove`? | notes |
| --- | --- | --- | --- |
| *(default)* | `alloc::Global` | yes | `std::alloc`; unchanged behaviour |
| `slab` | `alloc::Slab` | yes | local slab-of-chunks pool + free list; cache-line-aligned chunks that never move |
| `bumpalo` | `&bumpalo::Bump` | no (freed on arena reset/drop) | pointer-bump; no `Clone`/`Default`/`clear` |
| `blink-alloc` | `&blink_alloc::BlinkAlloc` | no (freed on arena reset/drop) | as `bumpalo` |
| `nightly` | `alloc::Std<A>` | per `A` | bridges any `core::alloc::Allocator`; needs `cargo +nightly` |

```rust
use rougenoir::{Tree, alloc::Slab};

let mut tree: Tree<u64, u64, _, Slab> = Tree::new_in(Slab::new());
tree.insert(1, 10);
```

```rust
let bump = bumpalo::Bump::new();
let mut tree = rougenoir::Tree::new_in(&bump);
tree.insert(1, "one");
// nodes live in `bump`; `remove` runs the entry's `Drop` but the slot
// is only reclaimed when `bump` is reset or dropped.
```

Every backend must (and does) keep node addresses stable for the life of the
node — `remove` never invalidates other nodes' pointers. A non-reclaiming
backend still runs each entry's `Drop` on removal and on tree drop; only the
raw slot lingers until the arena is reset.

## Nice to Have

- Concurrency.
  - AFAICT the kernel's implementation allows for lock-free concurrency.
  - I'm not a linux expert, so I might be wrong.
  - If it's the case, then adding barriers here might do it?
- Generic support in `intrusive_adapter!`.
  - The macro only generates an `Adapter` for non-generic value types today; a
    generic one (like `Node<K, V>`, or `examples/interval_tree.rs`'s
    `IntervalNode<K, V>`) needs its `Adapter` written by hand instead.

See [TODO.md](docs/TODO.md).

## Contributing

See [docs/Contributing.md](docs/contributing.md).
