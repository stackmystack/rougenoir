//! Shared benchmark scaffolding: deterministic key generators, the size
//! ladder, and per-group criterion configuration.
//!
//! Every bench in this crate pulls its inputs from here so that:
//!
//! * every implementation under test sees the *identical* key sequence for
//!   a given `(shape, size)` — no implementation gets a luckier
//!   distribution than another;
//! * runs are reproducible bit-for-bit (a fixed `ChaCha8` seed, never
//!   `thread_rng`);
//! * the run's cost is tunable from the environment without editing code
//!   (`BENCH_QUICK`, `BENCH_FULL`, `BENCH_SIZES`).
//!
//! It is a directory module (`benches/harness/mod.rs`, `mod harness;`)
//! rather than `benches/harness.rs` on purpose: Cargo auto-discovers
//! `benches/*.rs` as benchmark targets, but not subdirectory files.
#![allow(dead_code)]

use std::time::Duration;

use criterion::measurement::Measurement;
use criterion::{BatchSize, BenchmarkGroup, Throughput};
use rand::SeedableRng;
use rand::seq::SliceRandom;
use rand_chacha::ChaCha8Rng;

/// The one seed. Change it and every "random" number in the suite moves;
/// leave it and two runs a month apart are comparable.
pub const SEED: u64 = 0x5EED_C0DE_1234_5678;

/// Benchmarks key on `u64` throughout. `usize` would make the numbers
/// platform-dependent for no insight; a wider or `Ord`-expensive key is a
/// deliberately separate concern (see `bench_costly_key`).
pub type Key = u64;

// ---------------------------------------------------------------------------
// Run mode
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// `BENCH_QUICK=1` — a smoke test: two sizes, three shapes, few
    /// samples. Seconds, not minutes. This is what `just bench` runs.
    Quick,
    /// No env var — a useful default: three sizes up to 64k.
    Default,
    /// `BENCH_FULL=1` — the whole matrix, including the 1M out-of-cache
    /// size. This is what `just bench-full` and baselines run.
    Full,
}

pub fn mode() -> Mode {
    if env_flag("BENCH_FULL") {
        Mode::Full
    } else if env_flag("BENCH_QUICK") {
        Mode::Quick
    } else {
        Mode::Default
    }
}

pub fn is_quick() -> bool {
    mode() == Mode::Quick
}

fn env_flag(name: &str) -> bool {
    matches!(
        std::env::var(name).ok().as_deref(),
        Some("1" | "true" | "yes" | "on")
    )
}

// ---------------------------------------------------------------------------
// Size ladder
// ---------------------------------------------------------------------------

/// A geometric ladder, one point per cache regime, instead of a dense list
/// of tiny sizes that all live in L2. With `Throughput::Elements` set (see
/// [`configure`]) criterion reports ns/element, so three or four points
/// are enough to read the asymptote.
///
/// * 256 — comfortably in L1; measures the algorithm, not the memory system.
/// * 4096 — L2.
/// * 65536 — spills L2 into L3; ~3 MB of nodes.
/// * 1048576 — out of cache; every pointer chase is a probable DRAM miss.
///   This is where a B-tree pulls ahead of a pointer-based RB tree, and
///   where the `Full` runs earn their keep.
///
/// Override with `BENCH_SIZES=1000,50000` for a one-off.
pub fn sizes() -> Vec<usize> {
    if let Ok(raw) = std::env::var("BENCH_SIZES") {
        let parsed: Vec<usize> = raw
            .split(',')
            .filter_map(|s| s.trim().parse().ok())
            .filter(|&n| n > 0)
            .collect();
        if !parsed.is_empty() {
            return parsed;
        }
    }
    match mode() {
        Mode::Quick => vec![1 << 10, 1 << 16],
        Mode::Default => vec![1 << 8, 1 << 12, 1 << 16],
        Mode::Full => vec![1 << 8, 1 << 12, 1 << 16, 1 << 20],
    }
}

// ---------------------------------------------------------------------------
// Input shapes
// ---------------------------------------------------------------------------

/// The order keys are inserted in. For a balanced tree this barely touches
/// the *shape* of the result, but it dominates the *cost* of building it:
/// rotation counts, branch predictability, and which cache lines are hot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// `0, 1, 2, …` — the best case and the least representative one:
    /// every insert lands on the right spine, the comparisons are
    /// perfectly predicted, and the working set is a single hot path.
    /// `BTreeMap` also gets its friendliest pattern here.
    Ascending,
    /// `n-1, …, 1, 0` — the mirror image; left spine.
    Descending,
    /// a uniform-random permutation of `0..n`. Same key *set* as
    /// `Ascending`, so the delta between the two is purely the cost of
    /// insertion *order*.
    Shuffled,
    /// `n` independent uniform-random `u64`. The realistic, cache-hostile
    /// case: no spatial locality between successive keys.
    Random,
    /// the bit-reversal permutation of `0..n` (van der Corput). Successive
    /// keys are maximally far apart in tree order, which maximises the
    /// rotation and recolour work per insert — the adversarial input for
    /// the rebalancing code.
    Adversarial,
    /// keys drawn from a domain of only `n/16` distinct values, shuffled.
    /// ~15 of every 16 inserts therefore hit the *update* path
    /// (`mem::replace` on the value, no allocation, no rebalance) rather
    /// than a real insertion. The old bench measured *only* this path by
    /// accident; here it is one shape among six.
    Duplicates,
}

impl Shape {
    pub fn name(self) -> &'static str {
        match self {
            Shape::Ascending => "ascending",
            Shape::Descending => "descending",
            Shape::Shuffled => "shuffled",
            Shape::Random => "random",
            Shape::Adversarial => "adversarial",
            Shape::Duplicates => "duplicates",
        }
    }
}

/// Which shapes to sweep. `Quick` keeps the three that tell you the most
/// (best case, order effect, realistic); `Default`/`Full` sweep all six.
pub fn shapes() -> &'static [Shape] {
    if is_quick() {
        &[Shape::Ascending, Shape::Shuffled, Shape::Random]
    } else {
        &[
            Shape::Ascending,
            Shape::Descending,
            Shape::Shuffled,
            Shape::Random,
            Shape::Adversarial,
            Shape::Duplicates,
        ]
    }
}

fn rng_for(shape: Shape, n: usize) -> ChaCha8Rng {
    // Distinct-but-deterministic stream per (shape, size) so that, say,
    // `Random @ 4096` is the same sequence on every run and every machine,
    // but not a prefix of `Random @ 65536`.
    let salt = (shape as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (n as u64).rotate_left(29);
    ChaCha8Rng::seed_from_u64(SEED ^ salt)
}

/// The `n` keys to insert, in insertion order, for the given shape.
pub fn keys(shape: Shape, n: usize) -> Vec<Key> {
    let mut rng = rng_for(shape, n);
    match shape {
        Shape::Ascending => (0..n as Key).collect(),
        Shape::Descending => (0..n as Key).rev().collect(),
        Shape::Shuffled => {
            let mut v: Vec<Key> = (0..n as Key).collect();
            v.shuffle(&mut rng);
            v
        }
        Shape::Random => {
            use rand::Rng;
            (0..n).map(|_| rng.random::<Key>()).collect()
        }
        Shape::Adversarial => bit_reversal(n),
        Shape::Duplicates => {
            let domain = ((n / 16).max(1)) as Key;
            let mut v: Vec<Key> = (0..n as Key).map(|i| i % domain).collect();
            v.shuffle(&mut rng);
            v
        }
    }
}

/// The bit-reversal permutation of `0..n`: reverse the low `ceil(log2 n)`
/// bits of each index, keep the results that land in range.
fn bit_reversal(n: usize) -> Vec<Key> {
    if n <= 1 {
        return (0..n as Key).collect();
    }
    let bits = n.next_power_of_two().trailing_zeros();
    let mut out = Vec::with_capacity(n);
    let mut i: u64 = 0;
    while out.len() < n {
        let r = i.reverse_bits() >> (64 - bits);
        if (r as usize) < n {
            out.push(r);
        }
        i += 1;
    }
    out
}

/// Shuffle in place with a named, reproducible stream — used to pick a
/// lookup / deletion order that is independent of insertion order.
pub fn shuffle(v: &mut [Key], tag: u64) {
    let mut rng = ChaCha8Rng::seed_from_u64(SEED ^ tag.wrapping_mul(0xD1B5_4A32_D192_ED03));
    v.shuffle(&mut rng);
}

// ---------------------------------------------------------------------------
// criterion wiring
// ---------------------------------------------------------------------------

/// Per-group configuration: throughput (so results read as ns/element),
/// plus sample counts and timings scaled to the size so a `Full` run of
/// the whole matrix stays in the tens of minutes rather than hours.
///
/// Fewer samples widen criterion's confidence interval but barely move the
/// point estimate; for a project bench that is the right trade.
pub fn configure<M: Measurement>(group: &mut BenchmarkGroup<'_, M>, n: usize) {
    group.throughput(Throughput::Elements(n as u64));

    // These benches do `n` operations per iteration, not one — they are
    // throughput measurements, and criterion still runs each many times.
    // Chasing sub-1% precision here would cost minutes per benchmark for
    // no decision-relevant gain, so keep samples and windows modest. 10 is
    // criterion's floor.
    //
    // `BENCH_PRECISE=1` overrides that for a run whose numbers you intend to
    // publish: more samples and a longer window, at every size, so the
    // large-`n` rows (few iterations per sample otherwise) settle down.
    let (samples, secs, warmup_ms) = if env_flag("BENCH_PRECISE") {
        (20usize, 3.0, 750u64)
    } else {
        match mode() {
            Mode::Quick => (10, 1.0, 200),
            _ if n >= (1 << 16) => (10, 1.5, 250),
            _ => (12, 1.5, 300),
        }
    };
    group.sample_size(samples);
    group.measurement_time(Duration::from_secs_f64(secs));
    group.warm_up_time(Duration::from_millis(warmup_ms));
}

/// Like [`configure`] but for benches whose unit of work is a fixed script
/// of `ops` operations rather than `n` elements (e.g. churn).
pub fn configure_ops<M: Measurement>(group: &mut BenchmarkGroup<'_, M>, n: usize, ops: usize) {
    configure(group, n);
    group.throughput(Throughput::Elements(ops as u64));
}

/// Batch strategy for `iter_batched*`. Always [`BatchSize::PerIteration`].
///
/// The other modes size the batch assuming a *cheap* input, then keep the
/// whole batch live: every setup runs before the timed region and every
/// output drops after it. Our fixtures and outputs are whole trees, so a
/// batch is thousands of them at once — hundreds of MB to GB that thrashes
/// and swamps the measurement. `PerIteration` builds and drops exactly one
/// tree per iteration. Its overhead is two extra `Instant::now()` calls
/// (tens of ns) against a routine that does thousands of operations —
/// unmeasurable.
///
/// `n` is taken for symmetry with the rest of the harness and in case a
/// future size wants a different rule.
pub fn batch(_n: usize) -> BatchSize {
    BatchSize::PerIteration
}
