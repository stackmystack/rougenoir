extern crate rougenoir;

use std::{collections::BTreeMap, ops::Range};

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};

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

fn insert_rougenoir(range: Range<usize>, tree: &mut rougenoir::Tree<usize, ()>) {
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
            let mut tree = rougenoir::Tree::<usize, ()>::new();
            b.iter(|| insert_rougenoir(black_box(0..size), black_box(&mut tree)));
        });
    }
    group.finish();
}

criterion_group!(benches, bench_insert);
criterion_main!(benches);
