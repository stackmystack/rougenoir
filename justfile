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
  cargo +nightly miri nextest run {{args}}

release:
  @just build --release

setup:
  cargo install cargo-nextest git-cliff typos-cli

test *args:
  cargo nextest run {{args}} --tests --examples

typos:
  typos --sort

typos-fix:
  typos --write-changes
