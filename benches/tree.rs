extern crate rougenoir;

use criterion::{Criterion, criterion_group, criterion_main};
use rougenoir::TreeOps;

fn insert(c: &mut Criterion) {
    let mut tree = rougenoir::RBTree::<usize, ()>::new();
    c.bench_function("rougenoir_insert", |b| {
        b.iter(|| {
            for k in 0..100 {
                tree.insert(k.clone(), ());
            }
        })
    });
    let mut tree = rbtree::RBTree::<usize, ()>::new();
    c.bench_function("rbtree_insert", |b| {
        b.iter(|| {
            for k in 0..100 {
                tree.insert(k.clone(), ());
            }
        })
    });
}

criterion_group!(benches, insert);
criterion_main!(benches);
