extern crate criterion;
extern crate rand;
extern crate rand_chacha;
extern crate rougenoir;

use criterion::*;
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;
use std::time::Duration;

const DURATION_SECS: u64 = 10;
const SAMPLE_SIZE: usize = 256;
const SIZES: [usize; 6] = [128, 256, 512, 1024, 2048, 4096];

trait TreeBehavior<K, V> {
    fn new() -> Self;
    fn insert(&mut self, key: K, value: V);
    fn remove(&mut self, key: &K);
    fn name() -> &'static str;
}

impl<K: Ord + Copy, V: Clone> TreeBehavior<K, V> for rougenoir::RBTree<K, V> {
    fn new() -> Self {
        Self::new()
    }
    fn insert(&mut self, key: K, value: V) {
        self.insert(key, value);
    }
    fn remove(&mut self, key: &K) {
        self.remove(key);
    }
    fn name() -> &'static str {
        "rougenoir::Tree"
    }
}

impl<K: Ord + Copy, V: Clone> TreeBehavior<K, V> for rbtree::RBTree<K, V> {
    fn new() -> Self {
        Self::new()
    }
    fn insert(&mut self, key: K, value: V) {
        self.insert(key, value);
    }
    fn remove(&mut self, key: &K) {
        self.remove(key);
    }
    fn name() -> &'static str {
        "rbtree::RBTree"
    }
}

enum OrderStrategy {
    Ascending,
    Descending,
    Random,
}

impl OrderStrategy {
    fn name(&self) -> &'static str {
        match self {
            OrderStrategy::Ascending => "ascending",
            OrderStrategy::Descending => "descending",
            OrderStrategy::Random => "random",
        }
    }

    fn prepare_data(&self, size: usize) -> Vec<u32> {
        let mut data: Vec<u32> = (0..size as u32).collect();

        match self {
            OrderStrategy::Ascending => {
                // Already in ascending order
            }
            OrderStrategy::Descending => {
                data.reverse();
            }
            OrderStrategy::Random => {
                let mut rng = ChaCha8Rng::seed_from_u64(42); // Use a fixed seed for reproducibility
                data.shuffle(&mut rng);
            }
        }

        data
    }
}

fn bench_insert<T: TreeBehavior<u32, ()> + 'static>(
    c: &mut Criterion,
    size: usize,
    order: OrderStrategy,
) {
    let data = order.prepare_data(size);
    let id = format!("{}_insert_{}_{}", T::name(), order.name(), size);

    let mut group = c.benchmark_group("insert");
    group.measurement_time(Duration::from_secs(DURATION_SECS));
    group.sample_size(SAMPLE_SIZE);

    group.bench_function(&id, |b| {
        b.iter(|| {
            let mut tree = T::new();
            for &v in &data {
                tree.insert(v, ());
            }
        })
    });

    group.finish();
}

fn bench_remove<T: TreeBehavior<u32, ()> + 'static>(
    c: &mut Criterion,
    size: usize,
    order: OrderStrategy,
) {
    let mut data = order.prepare_data(size);
    let mut tree = T::new();
    for &v in &data {
        tree.insert(v, ());
    }
    data.reverse();
    let id = format!("{}_remove_{}_{}", T::name(), order.name(), size);

    let mut group = c.benchmark_group("remove");
    group.measurement_time(Duration::from_secs(DURATION_SECS));
    group.sample_size(SAMPLE_SIZE);

    group.bench_function(&id, |b| {
        b.iter(|| {
            for &v in &data {
                tree.remove(&v);
            }
        })
    });

    group.finish();
}

fn generate_benchmarks(c: &mut Criterion) {
    for size in SIZES.iter() {
        bench_insert::<rougenoir::RBTree<u32, ()>>(c, *size, OrderStrategy::Ascending);
        // bench_insert::<rougenoir::RBTree<u32, ()>>(c, *size, OrderStrategy::Descending);
        // bench_insert::<rougenoir::RBTree<u32, ()>>(c, *size, OrderStrategy::Random);
        // bench_insert::<rbtree::RBTree<u32, ()>>(c, *size, OrderStrategy::Random);
        // bench_remove::<rougenoir::RBTree<u32, ()>>(c, *size, OrderStrategy::Random);
    }
}

criterion_group!(
    name = benches;
    config = Criterion::default()
        .measurement_time(Duration::from_secs(DURATION_SECS))
        .sample_size(SAMPLE_SIZE)
        .with_plots();
    targets = generate_benchmarks
);
criterion_main!(benches);
