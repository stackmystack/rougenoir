//! rougenoir's own regression suite.
//!
//! Groups, and what each one actually isolates:
//!
//! * `insert` — build a tree from empty, per shape. The core event.
//! * `get` — lookups into a warm tree: present keys, and misses.
//! * `remove` — delete-and-rebalance (the crate's most intricate path) over
//!   a fresh clone each iteration.
//! * `iter` — in-order `next()`/`prev()` pointer walks, both ways.
//! * `pop_first` — the reason `CachedTree` exists: `Tree` vs `CachedTree`
//!   for repeated min-extraction and for a bare `first()`.
//! * `augmented` — `Noop` vs a real order-statistics callback, to price the
//!   up-the-spine `propagate` on every insert.
//! * `churn` — a steady-state tree under interleaved insert/remove/get.
//! * `bulk` — `clone` and `drop` of a whole tree.
//! * `costly_key` — one size, `String` keys, to show comparison-cost
//!   sensitivity that `u64` keys hide.
//!
//! Run modes and knobs live in `benches/harness/mod.rs`.

mod harness;

use std::hint::black_box;
use std::ptr::NonNull;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use harness::{Key, batch, configure, configure_ops, is_quick, keys, shapes, shuffle, sizes};
use rougenoir::{CachedTree, Node, NodePtr, Noop, Tree, TreeCallbacks};

type Plain = Tree<Key, Key, Noop<Key, Key>>;
type PlainCached = CachedTree<Key, Key, Noop<Key, Key>>;

fn tree_from(ks: &[Key]) -> Plain {
    let mut t = Tree::new();
    for &k in ks {
        t.insert(k, k);
    }
    t
}

fn cached_from(ks: &[Key]) -> PlainCached {
    let mut t = CachedTree::new();
    for &k in ks {
        t.insert(k, k);
    }
    t
}

// ---------------------------------------------------------------------------
// insert
// ---------------------------------------------------------------------------

fn bench_insert(c: &mut Criterion) {
    let mut g = c.benchmark_group("insert");
    for &n in &sizes() {
        configure(&mut g, n);
        for &shape in shapes() {
            let ks = keys(shape, n);
            g.bench_with_input(
                BenchmarkId::new(format!("tree/{}", shape.name()), n),
                &ks,
                |b, ks| {
                    b.iter_batched(
                        || (),
                        |()| {
                            let mut t: Plain = Tree::new();
                            for &k in black_box(ks) {
                                black_box(t.insert(k, k));
                            }
                            t
                        },
                        batch(n),
                    );
                },
            );
            // CachedTree only for the realistic shape in Quick mode; all
            // shapes otherwise. The interesting question is how much the
            // leftmost-pointer maintenance costs on the write path.
            if !is_quick() || shape.name() == "random" {
                g.bench_with_input(
                    BenchmarkId::new(format!("cached_tree/{}", shape.name()), n),
                    &ks,
                    |b, ks| {
                        b.iter_batched(
                            || (),
                            |()| {
                                let mut t: PlainCached = CachedTree::new();
                                for &k in black_box(ks) {
                                    black_box(t.insert(k, k));
                                }
                                t
                            },
                            batch(n),
                        );
                    },
                );
            }
        }
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// get
// ---------------------------------------------------------------------------

fn bench_get(c: &mut Criterion) {
    let mut g = c.benchmark_group("get");
    for &n in &sizes() {
        // Tree of keys 0..n (a shuffled build), so every present-key
        // lookup hits and every key in n..2n misses.
        let tree = tree_from(&keys(harness::Shape::Shuffled, n));

        let mut hit_order: Vec<Key> = (0..n as Key).collect();
        shuffle(&mut hit_order, 0x6E7);
        let miss_order: Vec<Key> = (n as Key..2 * n as Key).collect();

        configure(&mut g, n);
        g.bench_with_input(BenchmarkId::new("hit", n), &hit_order, |b, order| {
            b.iter(|| {
                let mut acc = 0u64;
                for &k in order {
                    if let Some(v) = black_box(tree.get(&k)) {
                        acc = acc.wrapping_add(*v);
                    }
                }
                black_box(acc)
            });
        });
        g.bench_with_input(BenchmarkId::new("miss", n), &miss_order, |b, order| {
            b.iter(|| {
                let mut acc = 0u64;
                for &k in order {
                    acc += black_box(tree.contains_key(&k)) as u64;
                }
                black_box(acc)
            });
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// remove
// ---------------------------------------------------------------------------

fn bench_remove(c: &mut Criterion) {
    let mut g = c.benchmark_group("remove");
    for &n in &sizes() {
        let present = keys(harness::Shape::Shuffled, n);
        let template = tree_from(&present);

        let mut order = present.clone();
        shuffle(&mut order, 0xDE1E7E);

        configure(&mut g, n);
        g.bench_with_input(BenchmarkId::new("random_order", n), &order, |b, order| {
            b.iter_batched_ref(
                || template.clone(),
                |t| {
                    for k in order {
                        black_box(t.remove(k));
                    }
                },
                batch(n),
            );
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// iter
// ---------------------------------------------------------------------------

fn bench_iter(c: &mut Criterion) {
    let mut g = c.benchmark_group("iter");
    for &n in &sizes() {
        let tree = tree_from(&keys(harness::Shape::Shuffled, n));
        configure(&mut g, n);

        g.bench_with_input(BenchmarkId::new("forward", n), &n, |b, _| {
            b.iter(|| {
                let mut acc = 0u64;
                for (k, v) in tree.iter() {
                    acc = acc.wrapping_add(*k ^ *v);
                }
                black_box(acc)
            });
        });
        g.bench_with_input(BenchmarkId::new("backward", n), &n, |b, _| {
            b.iter(|| {
                let mut acc = 0u64;
                for (k, v) in tree.iter().rev() {
                    acc = acc.wrapping_add(*k ^ *v);
                }
                black_box(acc)
            });
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// pop_first / first  — CachedTree's whole point
// ---------------------------------------------------------------------------

fn bench_pop_first(c: &mut Criterion) {
    let mut g = c.benchmark_group("pop_first");
    for &n in &sizes() {
        let ks = keys(harness::Shape::Shuffled, n);
        let plain = tree_from(&ks);
        let cached = cached_from(&ks);

        configure(&mut g, n);

        g.bench_with_input(BenchmarkId::new("drain/tree", n), &n, |b, _| {
            b.iter_batched_ref(
                || plain.clone(),
                |t| {
                    while let Some(kv) = t.pop_first() {
                        black_box(kv);
                    }
                },
                batch(n),
            );
        });
        g.bench_with_input(BenchmarkId::new("drain/cached_tree", n), &n, |b, _| {
            b.iter_batched_ref(
                || cached.clone(),
                |t| {
                    while let Some(kv) = t.pop_first() {
                        black_box(kv);
                    }
                },
                batch(n),
            );
        });

        // Pure read: no structural change, so this is exactly the O(log n)
        // leftmost descent vs the O(1) cached pointer. `black_box` the tree
        // reference *before* the call, not just the result — otherwise the
        // optimiser hoists the (pure, unchanging) `first()` out of the loop
        // and measures nothing.
        g.bench_with_input(BenchmarkId::new("peek/tree", n), &n, |b, _| {
            b.iter(|| black_box(black_box(&plain).first()));
        });
        g.bench_with_input(BenchmarkId::new("peek/cached_tree", n), &n, |b, _| {
            b.iter(|| black_box(black_box(&cached).first()));
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// augmented  — price of a real callback on the write path
// ---------------------------------------------------------------------------

/// Order-statistics augmentation: each node caches the size of its own
/// subtree in `value.0`. Inserting always changes every size on the path
/// to the root, so `propagate` walks the full height every time — the
/// heavy end of what augmentation costs, which is the honest thing to show
/// someone deciding whether to pay for it.
#[derive(Clone, Copy, Default, PartialEq)]
struct OrderStat;

type OsVal = (u32, Key);
type OsNode = Node<Key, OsVal>;

fn subtree_size(child: NodePtr<OsNode>) -> u32 {
    // SAFETY: a child pointer handed out during a callback points at a
    // live node in the tree currently being rebalanced.
    child.map_or(0, |p| unsafe { p.as_ref() }.value.0)
}

fn recompute(node: &OsNode) -> u32 {
    1 + subtree_size(node.left()) + subtree_size(node.right())
}

impl TreeCallbacks for OrderStat {
    type Key = Key;
    type Value = OsVal;

    fn propagate(&self, node: Option<&mut OsNode>, stop: Option<&mut OsNode>) {
        let stop_ptr = stop.map(|s| s as *const OsNode);
        let mut cur: NodePtr<OsNode> = node.map(NonNull::from);
        while cur.map(|p| p.as_ptr() as *const OsNode) != stop_ptr {
            let Some(mut p) = cur else { break };
            // SAFETY: `p` points at a live node on the path being fixed up;
            // nothing else aliases it for the duration of this call.
            let n = unsafe { p.as_mut() };
            let size = recompute(n);
            if n.value.0 == size {
                break;
            }
            n.value.0 = size;
            cur = n.parent();
        }
    }

    fn copy(&self, old: &mut OsNode, new: &mut OsNode) {
        new.value.0 = old.value.0;
    }

    fn rotate(&self, old: &mut OsNode, new: &mut OsNode) {
        new.value.0 = old.value.0;
        old.value.0 = recompute(old);
    }
}

fn bench_augmented(c: &mut Criterion) {
    let mut g = c.benchmark_group("augmented");
    for &n in &sizes() {
        let ks = keys(harness::Shape::Random, n);
        configure(&mut g, n);

        g.bench_with_input(BenchmarkId::new("noop/insert", n), &ks, |b, ks| {
            b.iter_batched(
                || (),
                |()| {
                    let mut t: Tree<Key, OsVal, Noop<Key, OsVal>> = Tree::new();
                    for &k in black_box(ks) {
                        black_box(t.insert(k, (0, k)));
                    }
                    t
                },
                batch(n),
            );
        });
        g.bench_with_input(BenchmarkId::new("order_stat/insert", n), &ks, |b, ks| {
            b.iter_batched(
                || (),
                |()| {
                    let mut t: Tree<Key, OsVal, OrderStat> = Tree::with_callbacks(OrderStat);
                    for &k in black_box(ks) {
                        black_box(t.insert(k, (0, k)));
                    }
                    t
                },
                batch(n),
            );
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// churn  — steady-state tree under a mixed op stream
// ---------------------------------------------------------------------------

enum Op {
    Insert(Key),
    Remove(Key),
    Get(Key),
}

/// ~`min(n, 4096)` operations against a tree that starts (and stays) near
/// size `n`: 25% insert of a fresh key, 25% remove of a live key, 50%
/// lookup. The realistic workload, and the one where allocator behaviour
/// (free-list reuse) actually shows.
fn churn_script(n: usize, mut live: Vec<Key>) -> Vec<Op> {
    use rand::Rng;
    use rand::SeedableRng;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(harness::SEED ^ 0xC0FFEE ^ n as u64);
    shuffle(&mut live, 0xC0FFEE);

    let count = n.min(4096);
    let mut next_fresh = n as Key; // keys >= n are guaranteed absent
    let mut ops = Vec::with_capacity(count);
    for _ in 0..count {
        match rng.random_range(0u8..4) {
            0 => {
                ops.push(Op::Insert(next_fresh));
                live.push(next_fresh);
                next_fresh += 1;
            }
            1 if !live.is_empty() => {
                let idx = rng.random_range(0..live.len());
                ops.push(Op::Remove(live.swap_remove(idx)));
            }
            _ => {
                let k = if live.is_empty() {
                    0
                } else {
                    live[rng.random_range(0..live.len())]
                };
                ops.push(Op::Get(k));
            }
        }
    }
    ops
}

fn bench_churn(c: &mut Criterion) {
    let mut g = c.benchmark_group("churn");
    for &n in &sizes() {
        let present = keys(harness::Shape::Shuffled, n);
        let template = tree_from(&present);
        let ops = churn_script(n, present);

        configure_ops(&mut g, n, ops.len());
        g.bench_with_input(BenchmarkId::new("mixed", n), &ops, |b, ops| {
            b.iter_batched_ref(
                || template.clone(),
                |t| {
                    let mut acc = 0u64;
                    for op in ops {
                        match op {
                            Op::Insert(k) => {
                                black_box(t.insert(*k, *k));
                            }
                            Op::Remove(k) => {
                                black_box(t.remove(k));
                            }
                            Op::Get(k) => {
                                if let Some(v) = t.get(k) {
                                    acc = acc.wrapping_add(*v);
                                }
                            }
                        }
                    }
                    black_box(acc);
                },
                batch(n),
            );
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// bulk  — clone / drop of a whole tree
// ---------------------------------------------------------------------------

fn bench_bulk(c: &mut Criterion) {
    let mut g = c.benchmark_group("bulk");
    for &n in &sizes() {
        let tree = tree_from(&keys(harness::Shape::Shuffled, n));
        configure(&mut g, n);

        // `iter_batched` (not `iter_with_large_drop`, which accumulates every
        // clone until the batch ends): here the clone is timed and its drop
        // is not.
        g.bench_with_input(BenchmarkId::new("clone", n), &n, |b, _| {
            b.iter_batched(|| (), |()| tree.clone(), batch(n));
        });
        // Mirror image: the clone is the (untimed) setup, the drop is timed.
        g.bench_with_input(BenchmarkId::new("drop", n), &n, |b, _| {
            b.iter_batched(|| tree.clone(), drop, batch(n));
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// costly_key  — comparison cost that u64 keys hide
// ---------------------------------------------------------------------------

fn bench_costly_key(c: &mut Criterion) {
    let mut g = c.benchmark_group("costly_key");
    // One mid-ladder size is enough to make the point.
    let n = if is_quick() { 1 << 10 } else { 1 << 14 };

    let mut raw: Vec<Key> = (0..n as Key).collect();
    shuffle(&mut raw, 0x5731_4E59);
    let ks: Vec<String> = raw
        .iter()
        .map(|k| format!("key-{k:016x}-payload"))
        .collect();

    configure(&mut g, n);
    g.bench_with_input(BenchmarkId::new("string/insert", n), &ks, |b, ks| {
        b.iter_batched(
            || (),
            |()| {
                let mut t: Tree<String, u32, Noop<String, u32>> = Tree::new();
                for (i, k) in black_box(ks).iter().enumerate() {
                    black_box(t.insert(k.clone(), i as u32));
                }
                t
            },
            batch(n),
        );
    });

    let tree: Tree<String, u32, Noop<String, u32>> = {
        let mut t = Tree::new();
        for (i, k) in ks.iter().enumerate() {
            t.insert(k.clone(), i as u32);
        }
        t
    };
    let mut lookup = ks.clone();
    shuffle_strings(&mut lookup);
    g.bench_with_input(BenchmarkId::new("string/get", n), &lookup, |b, lookup| {
        b.iter(|| {
            let mut acc = 0u64;
            for k in lookup {
                if let Some(v) = black_box(tree.get(k.as_str())) {
                    acc = acc.wrapping_add(*v as u64);
                }
            }
            black_box(acc)
        });
    });
    g.finish();
}

fn shuffle_strings(v: &mut [String]) {
    use rand::SeedableRng;
    use rand::seq::SliceRandom;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(harness::SEED ^ 0x5715);
    v.shuffle(&mut rng);
}

criterion_group!(
    benches,
    bench_insert,
    bench_get,
    bench_remove,
    bench_iter,
    bench_pop_first,
    bench_augmented,
    bench_churn,
    bench_bulk,
    bench_costly_key
);
criterion_main!(benches);
