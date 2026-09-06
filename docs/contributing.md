# Contributing

1. Be nice.
1. Please contact me before:

- you start a big re-write, or
- you want to tackle something from [TODO.md](TODO.md).

1. Please pay attention to the commit message format because the changelog is automatically generated:

- **Don't use** [conventional commits](https://www.conventionalcommits.org/en/v1.0.0/).
- The format is close enough:

  ```
  <type>: [optional scope]: <description>

  [optional body]
  ```

- `fix: tree: change rotation API`.
- Examples and descriptions are highly encouraged in the commit body.

## Dependencies

1. [`cargo-nextest`](https://nexte.st/), to run the tests.
1. [`just`](https://just.systems/man/en/), to run common tasks.
1. [`miri`](https://github.com/rust-lang/miri), for memory safety analysis.
1. [`rust nightly`](https://rust-lang.github.io/rustup/concepts/channels.html), to run `miri` and to build the `nightly` allocator feature (`cargo +nightly … --features nightly`).
1. [`typos-cli`](https://github.com/crate-ci/typos), for spell checking.

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

## Benchmarking

The suite lives in `benches/` and runs on [criterion](https://bheisler.github.io/criterion.rs/book/).

```
benches/
├── harness/mod.rs   shared: input shapes, key generators, size ladder, criterion config
├── rougenoir.rs     the regression suite — rougenoir's own types only
└── compare.rs       rougenoir vs std::collections::BTreeMap vs the rbtree crate
```

### Running

| Command | What it does | Roughly |
| --- | --- | --- |
| `just bench` | Quick smoke run: 2 sizes, 3 shapes, few samples. `BENCH_QUICK=1`. | seconds |
| `just bench-rougenoir` | Default: 3 sizes up to 64k, all 6 shapes. | a few minutes |
| `just bench-full` | Whole matrix incl. the 1M out-of-cache size. `BENCH_FULL=1`. | tens of minutes |
| `just bench-compare` | rougenoir vs `BTreeMap` vs `rbtree`. | a few minutes |
| `just bench-baseline <name>` | Full run, saved under `<name>` (do this *before* a change). | |
| `just bench-cmp <name>` | Full run, diffed against `<name>` (do this *after*). | |

One-offs: `BENCH_SIZES=1000,50000 cargo bench --bench rougenoir` overrides the ladder,
`BENCH_PRECISE=1` bumps every size to 20 samples / 3 s (for numbers you'll publish),
and criterion's own filter still works — `cargo bench --bench rougenoir -- insert/random`.

> **Note:** a bare `cargo bench` (no `--bench`) currently fails to compile — it also
> builds the crate's unit-test target, which uses `debug_assertions`-gated helpers
> (`validate`, `validate_of`) that don't exist in release. Always name a target.

### How it's built to be fair and fast

- **Deterministic, shared inputs.** Every key sequence comes from `harness::keys(shape, n)`,
  which is seeded from a single fixed `ChaCha8` seed. Two runs a month apart are comparable,
  and in `compare.rs` every implementation gets the *identical* sequence for a given
  `(shape, size)` — nobody wins on a luckier distribution. **Never** add `thread_rng` or an
  unseeded RNG here.
- **Six insertion shapes**, because insertion *order* dominates the cost of building a
  balanced tree even though it barely changes the result:
  `ascending` (best case, right-spine, predicted branches), `descending`, `shuffled` (a
  permutation of `0..n` — isolates order from key distribution), `random` (realistic,
  cache-hostile), `adversarial` (bit-reversal — maximises rotation/recolour work), and
  `duplicates` (a small key domain — most inserts hit the update path, not a real insertion).
- **A geometric size ladder**, one point per cache regime (256 → L1, 4k → L2, 64k → L3,
  1M → DRAM), not a dense list of sizes that all live in L2. With `Throughput::Elements`
  set, criterion reports ns/element, so three or four points show the asymptote.
- **Setup isn't timed.** Mutation benches (`insert`, `remove`, `pop_first`, `churn`, `drop`)
  use `iter_batched*`: the fixture (a fresh `Tree`, or a `Clone` of a template — an O(n)
  structural copy, cheaper than rebuilding) is created outside the measured region, and the
  result is dropped outside it too. Read benches (`get`, `iter`, `peek`) run against one
  prebuilt tree.
- **Sample counts scale with size** (`harness::configure`) so a full run stays in the tens of
  minutes. Fewer samples widen criterion's confidence interval but barely move the estimate.

### Getting stable numbers

Criterion's variance is only as good as the machine under it. Before a run you care about:

```sh
# pin to one core, away from CPU 0
taskset -c 2 just bench-full

# if you can (root): a fixed frequency beats turbo's jitter
sudo cpupower frequency-set -g performance
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo   # Intel
```

Close other work, run on AC power, and for a before/after use `bench-baseline` /
`bench-cmp` rather than eyeballing two logs. HTML reports land in
`target/criterion/`.

### Adding to the suite

New shapes, ops, or sizes go in `benches/harness/mod.rs` so **both** targets pick them up.
Keep the size ladder geometric and regime-spanning. If you add an operation, add it to
`rougenoir.rs` first; only mirror it into `compare.rs` if the cross-implementation
comparison is genuinely interesting.
