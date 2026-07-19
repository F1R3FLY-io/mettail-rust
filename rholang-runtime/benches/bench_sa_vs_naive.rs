//! Track B — B6: the criterion WALL-CLOCK bench for the naive-vs-optimized
//! matcher head-to-head (`bench-naive-baseline` + the three demo-language
//! features; see the `[[bench]]` registration in `Cargo.toml`).
//!
//! # Group structure and WHAT EACH GROUP TIMES
//!
//! Groups are `warm/<workload>/<matcher>` and `cold/<workload>/<matcher>`,
//! with the size parameter `n` as the benchmark id — e.g.
//! `warm/lambda_chain/sa/8`. Timing is `iter_custom` (manual `Instant`
//! spans), so the measured region is EXACT:
//!
//! * **warm** — the B3 hoist applies: `compile_workload` (reconstruct → lower
//!   → plan → `compile_in_rho_matching_ruleset` → installed σ-receiver
//!   program) runs ONCE, OUTSIDE the measured region, as does the tokio
//!   current-thread runtime construction. Measured per iteration:
//!   `emission` (the per-call driver emitters + composition against the
//!   hoisted installed program) `+ build + inj + readback` (the
//!   `bench_inj_and_read` phase timers: pre-inj soft-checkpoint/budget/seed
//!   prep, the reduction to quiescence, and the OUT `get_data` readback).
//!   NOT measured: per-injection counting-runtime bring-up
//!   (`bench_runtime_with_counters` — a fresh runtime per injection, per the
//!   rep discipline), and the observed-vs-expected verification/decode.
//! * **cold** — the same drive with the compilation INSIDE the measured
//!   region. Measured per iteration: the `compile_workload` span `+ bringup`
//!   (counting-runtime construction) `+ emission + build + inj + readback`.
//!   Verification/decode remains unmeasured.
//!
//! The multi-step `lambda_chain` rep sums its per-step spans (each step on a
//! fresh runtime, fed by the previous step's OBSERVED reduct — the B2 per-step
//! root-drive discipline); every other workload is a single injection.
//!
//! Every iteration VERIFIES the observed multiset against the workload's
//! ground truth (a mismatch panics — a benchmark that stops matching is not a
//! benchmark), so the wall numbers are always numbers for CORRECT runs.
//!
//! # Configuration
//!
//! Bench-top defaults: 10 samples, 3 s warm-up (the full pinned protocol
//! overrides via the criterion CLI, e.g. `-- --sample-size 30
//! --warm-up-time 5`). The naive columns run the `pattern-guard` encoding by
//! default; set `BENCH_SA_VS_NAIVE_ENCODING=consume-test` to bench the
//! paper-literal encoding on the cells that admit it (single-candidate
//! subjects only — non-admitted cells are SKIPPED with a note, not silently
//! rebound). Matcher columns per workload come from the shared registry
//! (`nested_spine` benches `naive` vs `replay`; the rest bench `sa` vs
//! `naive`).

#[path = "support/workloads.rs"]
mod workloads;

use std::time::{Duration, Instant};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use workloads::{
    cell_width_probe, compile_workload, consume_test_admitted, node_count,
    run_compiled_workload, GuardEncodingKind, MatcherKind, WorkloadKind, ALL_ENCODINGS,
    ALL_MATCHERS, ALL_WORKLOADS,
};

/// Whether a `(workload, matcher, encoding, n)` cell must be SKIPPED, with the
/// printed reason: the consume-test single-candidate restriction, or the
/// pre-existing f1r3node `split_byte(i8)` panic zone (the driver records the
/// same cells as fail-closed `"dnf"` lines; criterion cannot represent a dnf,
/// so the cell is skipped LOUDLY — the ladder itself stays pinned).
fn cell_skip_reason(
    kind: WorkloadKind,
    matcher: MatcherKind,
    encoding: GuardEncodingKind,
    n: u64,
) -> Option<String> {
    if matcher == MatcherKind::Naive
        && encoding == GuardEncodingKind::ConsumeTest
        && !consume_test_admitted(kind, n)
    {
        return Some("consume-test is single-candidate only".to_string());
    }
    let compiled = compile_workload(kind, n)
        .unwrap_or_else(|error| panic!("compile_workload({}, {n}) failed: {error}", kind.name()));
    match cell_width_probe(&compiled, matcher, encoding) {
        Ok(probe) => probe.hazard_width.map(|width| {
            format!(
                "an injection's parallel eval width ({width}) lies in the pre-existing f1r3node \
                 split_byte(i8) panic zone [129, 256] (reduce.rs:227) — fails closed, see the \
                 driver's dnf lines"
            )
        }),
        Err(failure) => Some(format!("emitter fails closed offline: {}", failure.reason)),
    }
}

/// Registry sanity gate, run once before any measurement: every workload's
/// matcher columns come from the shared registry and every full-ladder size is
/// admitted — a drifted registry fails the bench loudly instead of producing a
/// half-populated matrix.
fn assert_registry_consistent() {
    for kind in ALL_WORKLOADS {
        for matcher in kind.matchers() {
            assert!(
                ALL_MATCHERS.contains(matcher),
                "workload {} lists a matcher outside the registry",
                kind.name(),
            );
        }
        for &n in kind.full_sizes() {
            kind.admitted_size(n).unwrap_or_else(|error| {
                panic!("full-ladder size {n} of {} is not admitted: {error}", kind.name())
            });
        }
    }
}

/// Resolve the naive-column guard encoding from `BENCH_SA_VS_NAIVE_ENCODING`
/// (default `pattern-guard`), against the shared registry.
fn naive_encoding_from_env() -> GuardEncodingKind {
    match std::env::var("BENCH_SA_VS_NAIVE_ENCODING") {
        Ok(token) => ALL_ENCODINGS
            .iter()
            .copied()
            .find(|encoding| encoding.name() == token)
            .unwrap_or_else(|| {
                panic!(
                    "BENCH_SA_VS_NAIVE_ENCODING must be one of {:?}, got `{token}`",
                    ALL_ENCODINGS.iter().map(|e| e.name()).collect::<Vec<_>>(),
                )
            }),
        Err(_) => GuardEncodingKind::PatternGuard,
    }
}

/// The encoding a cell runs: the env-selected one on the naive column,
/// `pattern-guard` (ignored downstream, recorded `"-"`) elsewhere.
fn cell_encoding(matcher: MatcherKind, naive_encoding: GuardEncodingKind) -> GuardEncodingKind {
    match matcher {
        MatcherKind::Naive => naive_encoding,
        MatcherKind::Sa | MatcherKind::Replay => GuardEncodingKind::PatternGuard,
    }
}

fn bench_matrix(c: &mut Criterion) {
    // Demo-language reconstruction shares the process-global var-name cache;
    // clear it once up front (the same discipline as every B2 drive).
    mettail_runtime::clear_var_cache();
    assert_registry_consistent();
    let naive_encoding = naive_encoding_from_env();

    for kind in ALL_WORKLOADS {
        for &matcher in kind.matchers() {
            let encoding = cell_encoding(matcher, naive_encoding);

            // ── warm/<workload>/<matcher> ───────────────────────────────────
            let mut warm = c.benchmark_group(format!("warm/{}/{}", kind.name(), matcher.name()));
            for &n in kind.full_sizes() {
                if let Some(reason) = cell_skip_reason(kind, matcher, encoding, n) {
                    eprintln!(
                        "skipping warm/{}/{}/{n}: {reason}",
                        kind.name(),
                        matcher.name(),
                    );
                    continue;
                }
                // The B3 hoist: compile ONCE, outside the measured region.
                let compiled = compile_workload(kind, n).unwrap_or_else(|error| {
                    panic!("compile_workload({}, {n}) failed: {error}", kind.name())
                });
                eprintln!(
                    "warm/{}/{}/{n}: subject nodes {}, expected firings {}",
                    kind.name(),
                    matcher.name(),
                    node_count(&compiled.subject),
                    kind.expected_firings(n),
                );
                let runtime = tokio::runtime::Builder::new_current_thread()
                    .enable_all()
                    .build()
                    .expect("build the current-thread tokio runtime");
                warm.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, _| {
                    b.iter_custom(|iters| {
                        let mut measured = Duration::ZERO;
                        for _ in 0..iters {
                            let outcome = runtime
                                .block_on(run_compiled_workload(&compiled, matcher, encoding, 0))
                                .unwrap_or_else(|failure| {
                                    panic!(
                                        "warm {}/{}/{n}: {}",
                                        kind.name(),
                                        matcher.name(),
                                        failure.reason,
                                    )
                                });
                            // emission + build + inj + readback; bring-up and
                            // verification stay outside (module rustdoc).
                            measured += outcome.emission
                                + outcome.result.build
                                + outcome.result.inj
                                + outcome.result.readback;
                        }
                        measured
                    })
                });
            }
            warm.finish();

            // ── cold/<workload>/<matcher> ───────────────────────────────────
            let mut cold = c.benchmark_group(format!("cold/{}/{}", kind.name(), matcher.name()));
            for &n in kind.full_sizes() {
                if let Some(reason) = cell_skip_reason(kind, matcher, encoding, n) {
                    eprintln!(
                        "skipping cold/{}/{}/{n}: {reason}",
                        kind.name(),
                        matcher.name(),
                    );
                    continue;
                }
                let runtime = tokio::runtime::Builder::new_current_thread()
                    .enable_all()
                    .build()
                    .expect("build the current-thread tokio runtime");
                cold.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, _| {
                    b.iter_custom(|iters| {
                        let mut measured = Duration::ZERO;
                        for _ in 0..iters {
                            // Compilation INSIDE the measured region (cold).
                            let compile_started = Instant::now();
                            let compiled = compile_workload(kind, n).unwrap_or_else(|error| {
                                panic!(
                                    "compile_workload({}, {n}) failed: {error}",
                                    kind.name(),
                                )
                            });
                            let compile_span = compile_started.elapsed();
                            let outcome = runtime
                                .block_on(run_compiled_workload(&compiled, matcher, encoding, 0))
                                .unwrap_or_else(|failure| {
                                    panic!(
                                        "cold {}/{}/{n}: {}",
                                        kind.name(),
                                        matcher.name(),
                                        failure.reason,
                                    )
                                });
                            // compile + bringup + emission + build + inj +
                            // readback; verification stays outside.
                            measured += compile_span
                                + outcome.bringup
                                + outcome.emission
                                + outcome.result.build
                                + outcome.result.inj
                                + outcome.result.readback;
                        }
                        measured
                    })
                });
            }
            cold.finish();
        }
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(10)
        .warm_up_time(Duration::from_secs(3));
    targets = bench_matrix
}
criterion_main!(benches);
