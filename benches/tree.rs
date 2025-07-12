extern crate rougenoir;

use std::hint::black_box;
use std::{collections::BTreeMap, ops::Range};

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use rougenoir::Noop;

fn insert_btree(range: Range<usize>, tree: &mut BTreeMap<usize, ()>) {
    for k in range {
        tree.insert(k, ());
    }
}

fn insert_rbtree(range: Range<usize>, tree: &mut rbtree::RBTree<usize, ()>) {
    for k in range {
        tree.insert(k, ());
    }
}

fn insert_rougenoir(range: Range<usize>, tree: &mut rougenoir::Tree<usize, (), Noop<usize, ()>>) {
    for k in range {
        tree.insert(k, ());
    }
}

fn insert_rougenoir_cached(
    range: Range<usize>,
    tree: &mut rougenoir::CachedTree<usize, (), Noop<usize, ()>>,
) {
    for k in range {
        tree.insert(k, ());
    }
}

fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");

    for size in [1, 10, 32, 64, 128, 512, 1024, 2048, 4096] {
        group.bench_with_input(BenchmarkId::new("btree", size), &size, |b, &size| {
            let mut tree = BTreeMap::<usize, ()>::new();
            b.iter(|| insert_btree(black_box(0..size), black_box(&mut tree)));
        });
        group.bench_with_input(BenchmarkId::new("rbtree", size), &size, |b, &size| {
            let mut tree = rbtree::RBTree::<usize, ()>::new();
            b.iter(|| insert_rbtree(black_box(0..size), black_box(&mut tree)));
        });
        group.bench_with_input(BenchmarkId::new("rougenoir", size), &size, |b, &size| {
            let mut tree = rougenoir::Tree::<usize, (), Noop<usize, ()>>::new();
            b.iter(|| insert_rougenoir(black_box(0..size), black_box(&mut tree)));
        });
        group.bench_with_input(
            BenchmarkId::new("rougenoir::cached_tree", size),
            &size,
            |b, &size| {
                let mut tree = rougenoir::CachedTree::<usize, (), Noop<usize, ()>>::new();
                b.iter(|| insert_rougenoir_cached(black_box(0..size), black_box(&mut tree)));
            },
        );
    }
    group.finish();
}

criterion_group!(benches, bench_insert);
criterion_main!(benches);
