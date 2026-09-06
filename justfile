#!/usr/bin/env just --justfile

alias b := build
alias c := clean
alias l := lint
alias t := test

default:
  @just --choose

clean:
  cargo clean

clippy:
  cargo clippy --all --all-targets -- --deny warnings

clippy-fix *args:
  cargo clippy --fix {{args}}

clippy-fix-now:
  @just clippy-fix --allow-dirty --allow-staged

# Benchmark targets. We always pass `--bench` explicitly: a bare
# `cargo bench` also builds the crate's unit-test target, which currently
# fails to compile in release (debug-assertion-gated test helpers) — an
# orthogonal, pre-existing issue.

# Quick smoke run: 2 sizes, 3 shapes, few samples. Seconds.
bench *args:
  BENCH_QUICK=1 cargo bench --bench rougenoir {{args}}

# Default run: rougenoir's own suite, 3 sizes up to 64k.
bench-rougenoir *args:
  cargo bench --bench rougenoir {{args}}

# Full matrix, including the 1M out-of-cache size. Tens of minutes.
bench-full *args:
  BENCH_FULL=1 cargo bench --bench rougenoir {{args}}

# rougenoir vs BTreeMap vs the rbtree crate.
bench-compare *args:
  cargo bench --bench compare {{args}}

# Record the current numbers under a name (run before a change).
bench-baseline name:
  BENCH_FULL=1 cargo bench --bench rougenoir -- --save-baseline {{name}}

# Compare the working tree against a recorded baseline (run after).
bench-cmp name:
  BENCH_FULL=1 cargo bench --bench rougenoir -- --baseline {{name}}

build *args:
  cargo build {{args}}

doc:
  cargo doc --no-deps --open

fmt:
  cargo fmt --all

fmt-check:
  cargo fmt --all -- --check

lint: clippy fmt-check typos

miri *args:
  cargo +nightly miri nextest run {{args}} --tests --examples
  cargo +nightly miri test --doc

release:
  @just build --release

setup:
  cargo install cargo-nextest typos-cli
  cargo +nightly install miri

test *args:
  cargo nextest run {{args}} --tests --examples
  cargo test --doc

# Compile, unit-test, and run every example's `main`.
test-examples:
  #!/usr/bin/env bash
  set -euo pipefail
  cargo nextest run --examples
  for f in examples/*.rs; do
    name=$(basename "$f" .rs)
    echo "==> cargo run --example $name"
    cargo run --quiet --example "$name"
  done

typos:
  typos --sort

typos-fix:
  typos --write-changes
