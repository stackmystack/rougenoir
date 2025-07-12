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
- Low-level API to build your own trees.
  - All the algorithms and data structures implemented exactly like the linux' version, but it's not an intrusive data-structure.
  - Notification on tree modification, aka [Augmentation](#augmentation).
  - See the [`IntervalTree` example](examples/interval_tree.rs).
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

## Benchmarks

You can run the benchmarks with `just bench` or `cargo bench` and check on your local machine.

I ran them on an old Intel(R) Core(TM) i7-7700HQ CPU @ 2.80GHz and on an M1 Max,
and in both cases I noticed that rougenoir can outperform
[`std::collections::BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html)
for small trees (~ < 4k), but it's a microbenchmark so take it with a kilo of
salt.

I think that this can be significantly and reliably improved once a custom
allocator can be used.

## Nice to Have

- Custom allocator.
  - Currently it's leaking boxes.
  - I'm thinking of [`hashbrown`](https://github.com/rust-lang/hashbrown).
  - And of course benchmarks would make more sense.
- Concurrency.
  - AFAICT the kernel's implementation allows for lock-free concurrency.
  - I'm not a linux expert, so I might be wrong.
  - If it's the case, then adding barriers here might do it?
- Intrusive rewrite.
  - I don't want to dismiss the idea, and patches are welcome, but it's not my priority. I'm already satisfied with this implementation.

See [TODO.md](docs/TODO.md).

## Contributing

See [docs/Contributing.md](docs/contributing.md).
