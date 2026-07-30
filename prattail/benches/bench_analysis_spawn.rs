//! Work item #164 — what does an unwanted analysis thread actually cost?
//!
//! # The question this benchmark exists to answer
//!
//! [`mettail_prattail::pipeline::run_math_analyses_parallel`] considers 32
//! mathematical analyses per grammar expansion. Sixteen of them are gated on
//! [`mettail_prattail::predicate_dispatch::GrammarDispatchPlan::requires`], and
//! before #164 all sixteen asked that question *inside* the spawned closure: an
//! analysis the plan did not want was still created as an OS thread, scheduled,
//! entered, and joined, in order to return the `None` the caller could have had
//! for free.
//!
//! Hoisting the gate to the spawn site is obviously *better shaped*. Whether it
//! is measurably **faster** is a separate question, and the owner's rule is to
//! answer it with data rather than with intuition. So this benchmark measures
//! three things, in increasing order of realism:
//!
//! 1. `spawn_mechanism/*` — the cost of `std::thread::scope` with `n` closures
//!    that return immediately, for the `n` that matter: **32** (every analysis
//!    considered, the pre-#164 behaviour), **18** (the post-#164 floor: 16
//!    ungated analyses plus `Symbolic` and `Mso`, which
//!    `PredicateSignature::BASE` makes mandatory for every grammar) and **26**
//!    (a mid-range grammar). The 32-vs-18 difference is the **upper bound** on
//!    what #164 can save, because a real elided analysis costs *at least* a
//!    thread and this measures exactly a thread and nothing else.
//! 2. `analysis_spawn_share/*` — that upper bound as a fraction of one whole
//!    `generate_parser` call, which is the unit a `language!` expansion actually
//!    pays. `small` and `complex` are the two standard bench specs with ≥3
//!    categories, which is the eligibility condition for the parallel analysis
//!    path (`< 3` categories takes the sequential path and spawns nothing).
//! 3. `generate_parser/*` — full parser generation per spec, so the saving can
//!    be quoted as a share of something a caller cares about.
//!
//! # Running it
//!
//! ```text
//! taskset -c 24-31 cargo bench -p prattail --bench bench_analysis_spawn
//! ```
//!
//! ⚠ CPU affinity is not optional: the analysis path is multi-threaded, so an
//! unpinned run on a loaded machine measures the scheduler. Record the load
//! average alongside any number taken from this benchmark — a wall-time figure
//! from a contended host is not reproducible without it.
//!
//! # Reading the ledger line it prints
//!
//! Before the timing loops, the bench prints one
//! [`mettail_prattail::pipeline::AnalysisSpawnLedger`] line per spec. That is the
//! **load-independent** half of the measurement: an exact count of threads
//! created and elided, which no amount of contention can perturb.

mod bench_specs;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::time::Duration;

use mettail_prattail::generate_parser;
use mettail_prattail::pipeline::analysis_spawn_ledger;

use bench_specs::{complex_spec, medium_spec, minimal_spec, small_spec};

/// Analyses considered per grammar before #164 — every one became a thread.
const CONSIDERED_ANALYSES: usize = 32;
/// Post-#164 floor: 16 ungated analyses + `Symbolic` + `Mso`, the two modules
/// `PredicateSignature::BASE` requires of every grammar.
const SPAWN_FLOOR: usize = 18;
/// A representative middle: a grammar with brackets, recursion and binders
/// leaves roughly this many gates satisfied.
const SPAWN_TYPICAL: usize = 26;

// ══════════════════════════════════════════════════════════════════════════════
// Group 1: the spawn mechanism in isolation — the upper bound on the saving
// ══════════════════════════════════════════════════════════════════════════════

/// `std::thread::scope` with `n` closures that do nothing but return.
///
/// This is deliberately the *emptiest possible* analysis: creation, scheduling,
/// entry, exit and join, with no work in between. A real elided analysis cost at
/// least this much, so the 32-vs-18 delta is a hard upper bound on what hoisting
/// the dispatch gate can recover.
fn empty_scope(spawn_count: usize) -> usize {
    std::thread::scope(|scope| {
        let handles: Vec<std::thread::ScopedJoinHandle<'_, usize>> = (0..spawn_count)
            .map(|index| scope.spawn(move || index))
            .collect();
        handles
            .into_iter()
            .map(|handle| {
                handle
                    .join()
                    .expect("empty scoped analysis thread cannot panic")
            })
            .sum()
    })
}

fn spawn_mechanism(c: &mut Criterion) {
    let mut group = c.benchmark_group("spawn_mechanism");
    group.warm_up_time(Duration::from_secs(2));
    group.measurement_time(Duration::from_secs(6));
    group.sample_size(200);

    for spawn_count in [SPAWN_FLOOR, SPAWN_TYPICAL, CONSIDERED_ANALYSES] {
        group.bench_with_input(
            BenchmarkId::from_parameter(spawn_count),
            &spawn_count,
            |b, &spawn_count| b.iter(|| empty_scope(spawn_count)),
        );
    }

    group.finish();
}

// ══════════════════════════════════════════════════════════════════════════════
// Group 2: the same cost as a share of one whole `generate_parser`
// ══════════════════════════════════════════════════════════════════════════════

/// Full parser generation for the four standard specs.
///
/// `minimal` (1 category) and `medium` (2 categories) fall below the parallel
/// path's `>= 3` eligibility threshold and so spawn **nothing**; they are here as
/// the control that isolates the analysis phase from the rest of the pipeline.
fn generate_parser_per_spec(c: &mut Criterion) {
    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    let mut group = c.benchmark_group("generate_parser");
    group.warm_up_time(Duration::from_secs(2));
    group.measurement_time(Duration::from_secs(8));
    group.sample_size(60);

    for (name, spec) in &specs {
        group.bench_with_input(BenchmarkId::from_parameter(name), spec, |b, spec| {
            b.iter(|| generate_parser(spec).expect("bench spec must be generable"))
        });
    }

    group.finish();
}

// ══════════════════════════════════════════════════════════════════════════════
// The load-independent half: exact spawn counts, printed once
// ══════════════════════════════════════════════════════════════════════════════

/// Print the spawn ledger for each spec before any timing runs.
///
/// Criterion has no hook for "report a non-timing fact", so this runs as its own
/// `criterion_group` member and simply generates each parser once, reading the
/// thread-local ledger afterwards. Counts are exact and unaffected by machine
/// load, which is why they — not the wall times below — are the headline number
/// for #164.
fn report_spawn_counts(_c: &mut Criterion) {
    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    println!("#164 spawn ledger (exact, load-independent):");
    for (name, spec) in &specs {
        let _ = generate_parser(spec).expect("bench spec must be generable");
        let ledger = analysis_spawn_ledger();
        println!(
            "  spec={name:<8} considered={:<3} spawned={:<3} elided={:<3} gated_sites={}",
            ledger.considered(),
            ledger.spawned,
            ledger.elided,
            ledger.gated_sites(),
        );
    }
}

criterion_group!(benches, report_spawn_counts, spawn_mechanism, generate_parser_per_spec);
criterion_main!(benches);
