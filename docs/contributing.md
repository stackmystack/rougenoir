# Contributing

1. Be nice.
1. Please contact me before:
  1. you start a big re-write, or
  1. you want to tackle something from [TODO.md](TODO.md).

## Dependencies

1. [`just`](https://just.systems/man/en/), to run common tasks.
1. [`rust nightly`](https://rust-lang.github.io/rustup/concepts/channels.html), to run `miri`.
1. [`cargo-nextest`](https://nexte.st/), to run the tests.
1. [`typos-cli`](https://github.com/crate-ci/typos), for spell checking.
1. [`miri`](https://github.com/rust-lang/miri), for memory safety analysis.

### Installation Procedure

All you need to install manually is `just` and `rust nightly`.
Check their docs and pick what suits your setup best.
If you're feeling especially lazy today, you can always install them with `cargo` and `rustup`:

```sh
cargo install just
rustup toolchain install nightly
```

Once done, you can setup the project and you're ready to go:
```sh
just setup # Pulls cargo-nextest, typos-cli, and miri
```

## Rules

The CI should pass the pipeline:

```sh
just lint && just miri # miri will download automatically.
```

## Helpers

Automatically fix with clippy if the working dir is _clean_:

```sh
just clippy-fix
```

Automatically fix with clippy if the working dir is _dirty_:
```sh
just clippy-fix-now
```
