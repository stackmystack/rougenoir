//! rougenoir's own tree across node backing stores: `Global` (the default,
//! one leaked `Box` per node) vs `Slab` (the local slab-of-chunks pool) vs
//! `bumpalo` / `blink-alloc` (pointer-bump arenas).
//!
//! What each group isolates:
//!
//! * `insert` — build from empty. Prices the per-node allocation call and
//!   how insertion-order locality lands.
//! * `get` / `iter` — reads against a warm tree of *identical shape*; the
//!   only thing that differs between backends is where the nodes sit in
//!   memory.
//! * `drop` — teardown: `Global` frees `n` nodes, `Slab` frees a handful of
//!   chunks, a bump arena frees its chunks.
//! * `churn` — steady state: `pop_first` + `insert` in a tight loop, size
//!   held constant. The free-list (`Slab`) vs no-reclaim (bump — grows
//!   unboundedly) contrast.
//!
//! Requires `--features slab,bumpalo,blink-alloc`; run it with
//! `just bench-allocators`. Separate target because you pick a backend once,
//! not every commit — same rationale as `compare.rs`.

mod harness;

use std::alloc::Layout;
use std::hint::black_box;
use std::ptr::NonNull;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use harness::{Key, Shape, batch, configure, configure_ops, keys, shuffle, sizes};
use rougenoir::alloc::{Allocator, Global, Slab};
use rougenoir::{Noop, Tree};

// The `bumpalo`/`blink-alloc` public adapters are `impl Allocator for &Bump`
// — the arena outlives the tree. For the bench it is tidier to let the tree
// *own* its arena, so a routine can return the tree and have its drop fall
// outside the timed region, exactly as the `Global`/`Slab` cases do. The
// allocation path is identical either way.
struct OwnedBump(bumpalo::Bump);

// SAFETY: `bumpalo::Bump` never relocates a live allocation; `deallocate` is
// a no-op (bump arenas reclaim en masse on drop).
unsafe impl Allocator for OwnedBump {
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        self.0.try_alloc_layout(layout).ok()
    }
    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

struct OwnedBlink(blink_alloc::BlinkAlloc);

// SAFETY: as `OwnedBump`.
unsafe impl Allocator for OwnedBlink {
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        blink_alloc::BlinkAlloc::allocate(&self.0, layout)
            .ok()
            .map(NonNull::cast)
    }
    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

type PlainTree<A> = Tree<Key, Key, Noop<Key, Key>, A>;

fn build<A: Allocator>(alloc: A, ks: &[Key]) -> PlainTree<A> {
    let mut t = Tree::new_in(alloc);
    for &k in ks {
        black_box(t.insert(k, k));
    }
    t
}

/// Expands `$body` once per backend, with `$mk` bound to a fresh-allocator
/// constructor and `$lbl` to the backend's name.
macro_rules! per_backend {
    ($mk:ident, $lbl:ident => $body:block) => {{
        {
            let $lbl = "global";
            let $mk = || Global;
            $body
        }
        {
            let $lbl = "slab";
            let $mk = || Slab::new();
            $body
        }
        {
            let $lbl = "bumpalo";
            let $mk = || OwnedBump(bumpalo::Bump::new());
            $body
        }
        {
            let $lbl = "blink";
            let $mk = || OwnedBlink(blink_alloc::BlinkAlloc::new());
            $body
        }
    }};
}

/// Best case (right spine, predicted branches — pure allocation cost) and the
/// realistic, cache-hostile case.
fn alloc_shapes() -> &'static [Shape] {
    &[Shape::Ascending, Shape::Random]
}

// ---------------------------------------------------------------------------
// insert
// ---------------------------------------------------------------------------

fn bench_insert(c: &mut Criterion) {
    let mut g = c.benchmark_group("insert");
    for &n in &sizes() {
        configure(&mut g, n);
        for &shape in alloc_shapes() {
            let ks = keys(shape, n);
            per_backend!(mk, lbl => {
                g.bench_with_input(
                    BenchmarkId::new(format!("{lbl}/{}", shape.name()), n),
                    &ks,
                    |b, ks| b.iter_batched(|| (), |()| build(mk(), ks), batch(n)),
                );
            });
        }
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// get / iter  — identical tree shape, different node addresses
// ---------------------------------------------------------------------------

fn bench_get(c: &mut Criterion) {
    let mut g = c.benchmark_group("get");
    for &n in &sizes() {
        let ks = keys(Shape::Shuffled, n);
        let mut order: Vec<Key> = (0..n as Key).collect();
        shuffle(&mut order, 0x611E7);
        configure(&mut g, n);

        per_backend!(mk, lbl => {
            let t = build(mk(), &ks);
            g.bench_with_input(BenchmarkId::new(lbl, n), &order, |b, order| {
                b.iter(|| {
                    let mut acc = 0u64;
                    for &k in order {
                        if let Some(v) = black_box(t.get(&k)) {
                            acc = acc.wrapping_add(*v);
                        }
                    }
                    black_box(acc)
                });
            });
        });
    }
    g.finish();
}

fn bench_iter(c: &mut Criterion) {
    let mut g = c.benchmark_group("iter");
    for &n in &sizes() {
        let ks = keys(Shape::Shuffled, n);
        configure(&mut g, n);

        per_backend!(mk, lbl => {
            let t = build(mk(), &ks);
            g.bench_with_input(BenchmarkId::new(lbl, n), &n, |b, _| {
                b.iter(|| {
                    let mut acc = 0u64;
                    for (k, v) in t.iter() {
                        acc = acc.wrapping_add(*k ^ *v);
                    }
                    black_box(acc)
                });
            });
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// drop  — teardown cost
// ---------------------------------------------------------------------------

fn bench_drop(c: &mut Criterion) {
    let mut g = c.benchmark_group("drop");
    for &n in &sizes() {
        let ks = keys(Shape::Shuffled, n);
        configure(&mut g, n);

        per_backend!(mk, lbl => {
            g.bench_with_input(BenchmarkId::new(lbl, n), &ks, |b, ks| {
                b.iter_batched(|| build(mk(), ks), drop, batch(n));
            });
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// churn  — steady-state allocate/free
// ---------------------------------------------------------------------------

fn bench_churn(c: &mut Criterion) {
    let mut g = c.benchmark_group("churn");
    for &n in &sizes() {
        let ks = keys(Shape::Shuffled, n);
        let ops = n.min(4096);
        configure_ops(&mut g, n, ops);

        per_backend!(mk, lbl => {
            g.bench_with_input(BenchmarkId::new(lbl, n), &ks, |b, ks| {
                b.iter_batched(
                    || build(mk(), ks),
                    |mut t| {
                        // Hold size constant: drop the min, add a fresh max.
                        let base = n as Key;
                        for next in base..base + ops as Key {
                            black_box(t.pop_first());
                            black_box(t.insert(next, next));
                        }
                        t
                    },
                    batch(n),
                );
            });
        });
    }
    g.finish();
}

criterion_group!(
    benches,
    bench_insert,
    bench_get,
    bench_iter,
    bench_drop,
    bench_churn
);
criterion_main!(benches);
