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

bench:
  cargo bench

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
