//! rougenoir against the alternatives:
//!
//! * `std::collections::BTreeMap` — the real bar. A B-tree, not a
//!   red-black tree, so it wins on cache density (few, wide nodes) and
//!   loses the per-operation worst-case latency that a balanced binary
//!   tree with pointer-stable nodes gives you.
//! * `rbtree` 0.2 — another Rust red-black tree; a same-family sanity peer.
//!
//! Kept separate from the `rougenoir` suite because it roughly triples the
//! measurement cost and answers a question you ask occasionally, not every
//! commit. Three shapes only, three operations.

mod harness;

use std::collections::BTreeMap;
use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use harness::{Key, Shape, batch, configure, keys, shuffle, sizes};
use rougenoir::{CachedTree, Noop, Tree};

type RnTree = Tree<Key, Key, Noop<Key, Key>>;
type RnCached = CachedTree<Key, Key, Noop<Key, Key>>;

/// Insertion shapes worth comparing across implementations: the best case
/// (where `BTreeMap`'s bulk-friendly access shines) and the realistic one.
fn compare_shapes() -> &'static [Shape] {
    &[Shape::Ascending, Shape::Random]
}

// ---------------------------------------------------------------------------
// insert
// ---------------------------------------------------------------------------

fn bench_insert(c: &mut Criterion) {
    let mut g = c.benchmark_group("compare/insert");
    for &n in &sizes() {
        configure(&mut g, n);
        for &shape in compare_shapes() {
            let ks = keys(shape, n);
            let s = shape.name();

            g.bench_with_input(
                BenchmarkId::new(format!("btreemap/{s}"), n),
                &ks,
                |b, ks| {
                    b.iter_batched(
                        || (),
                        |()| {
                            let mut m = BTreeMap::new();
                            for &k in black_box(ks) {
                                black_box(m.insert(k, k));
                            }
                            m
                        },
                        batch(n),
                    );
                },
            );
            g.bench_with_input(BenchmarkId::new(format!("rbtree/{s}"), n), &ks, |b, ks| {
                b.iter_batched(
                    || (),
                    |()| {
                        let mut t = rbtree::RBTree::new();
                        for &k in black_box(ks) {
                            t.insert(k, k);
                        }
                        t
                    },
                    batch(n),
                );
            });
            g.bench_with_input(
                BenchmarkId::new(format!("rougenoir/{s}"), n),
                &ks,
                |b, ks| {
                    b.iter_batched(
                        || (),
                        |()| {
                            let mut t: RnTree = Tree::new();
                            for &k in black_box(ks) {
                                black_box(t.insert(k, k));
                            }
                            t
                        },
                        batch(n),
                    );
                },
            );
            g.bench_with_input(
                BenchmarkId::new(format!("rougenoir_cached/{s}"), n),
                &ks,
                |b, ks| {
                    b.iter_batched(
                        || (),
                        |()| {
                            let mut t: RnCached = CachedTree::new();
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
    g.finish();
}

// ---------------------------------------------------------------------------
// get (present keys)
// ---------------------------------------------------------------------------

fn bench_get(c: &mut Criterion) {
    let mut g = c.benchmark_group("compare/get");
    for &n in &sizes() {
        let ks = keys(Shape::Shuffled, n);
        let mut order: Vec<Key> = (0..n as Key).collect();
        shuffle(&mut order, 0x63E7);

        let btree: BTreeMap<Key, Key> = ks.iter().map(|&k| (k, k)).collect();
        let mut rb = rbtree::RBTree::new();
        for &k in &ks {
            rb.insert(k, k);
        }
        let mut rn: RnTree = Tree::new();
        for &k in &ks {
            rn.insert(k, k);
        }

        configure(&mut g, n);
        g.bench_with_input(BenchmarkId::new("btreemap", n), &order, |b, order| {
            b.iter(|| {
                let mut acc = 0u64;
                for &k in order {
                    if let Some(v) = black_box(btree.get(&k)) {
                        acc = acc.wrapping_add(*v);
                    }
                }
                black_box(acc)
            });
        });
        g.bench_with_input(BenchmarkId::new("rbtree", n), &order, |b, order| {
            b.iter(|| {
                let mut acc = 0u64;
                for &k in order {
                    if let Some(v) = black_box(rb.get(&k)) {
                        acc = acc.wrapping_add(*v);
                    }
                }
                black_box(acc)
            });
        });
        g.bench_with_input(BenchmarkId::new("rougenoir", n), &order, |b, order| {
            b.iter(|| {
                let mut acc = 0u64;
                for &k in order {
                    if let Some(v) = black_box(rn.get(&k)) {
                        acc = acc.wrapping_add(*v);
                    }
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
    let mut g = c.benchmark_group("compare/remove");
    for &n in &sizes() {
        let ks = keys(Shape::Shuffled, n);
        let mut order: Vec<Key> = (0..n as Key).collect();
        shuffle(&mut order, 0x63DE);

        let btree: BTreeMap<Key, Key> = ks.iter().map(|&k| (k, k)).collect();
        let mut rb_template = rbtree::RBTree::new();
        for &k in &ks {
            rb_template.insert(k, k);
        }
        let mut rn_template: RnTree = Tree::new();
        for &k in &ks {
            rn_template.insert(k, k);
        }

        configure(&mut g, n);
        g.bench_with_input(BenchmarkId::new("btreemap", n), &order, |b, order| {
            b.iter_batched_ref(
                || btree.clone(),
                |m| {
                    for k in order {
                        black_box(m.remove(k));
                    }
                },
                batch(n),
            );
        });
        g.bench_with_input(BenchmarkId::new("rbtree", n), &order, |b, order| {
            b.iter_batched_ref(
                || rb_template.clone(),
                |t| {
                    for k in order {
                        black_box(t.remove(k));
                    }
                },
                batch(n),
            );
        });
        g.bench_with_input(BenchmarkId::new("rougenoir", n), &order, |b, order| {
            b.iter_batched_ref(
                || rn_template.clone(),
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
    let mut g = c.benchmark_group("compare/iter");
    for &n in &sizes() {
        let ks = keys(Shape::Shuffled, n);
        let btree: BTreeMap<Key, Key> = ks.iter().map(|&k| (k, k)).collect();
        let mut rb = rbtree::RBTree::new();
        for &k in &ks {
            rb.insert(k, k);
        }
        let mut rn: RnTree = Tree::new();
        for &k in &ks {
            rn.insert(k, k);
        }

        configure(&mut g, n);
        g.bench_with_input(BenchmarkId::new("btreemap", n), &n, |b, _| {
            b.iter(|| {
                let mut acc = 0u64;
                for (k, v) in &btree {
                    acc = acc.wrapping_add(*k ^ *v);
                }
                black_box(acc)
            });
        });
        g.bench_with_input(BenchmarkId::new("rbtree", n), &n, |b, _| {
            b.iter(|| {
                let mut acc = 0u64;
                for (k, v) in rb.iter() {
                    acc = acc.wrapping_add(*k ^ *v);
                }
                black_box(acc)
            });
        });
        g.bench_with_input(BenchmarkId::new("rougenoir", n), &n, |b, _| {
            b.iter(|| {
                let mut acc = 0u64;
                for (k, v) in rn.iter() {
                    acc = acc.wrapping_add(*k ^ *v);
                }
                black_box(acc)
            });
        });
    }
    g.finish();
}

criterion_group!(benches, bench_insert, bench_get, bench_remove, bench_iter);
criterion_main!(benches);
