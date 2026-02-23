//! Criterion A/B benchmark: static vs weighted dispatch strategies.
//!
//! Three benchmark groups:
//! 1. `dispatch/a_b` — Static vs Weighted for each standard spec (4 specs)
//! 2. `dispatch/scaling` — Static vs Weighted at N = 5, 10, 20, 50, 100 rules
//! 3. `dispatch/grammar_gen` — Expression generation overhead per spec
//!
//! Run static-only (no wfst feature):
//!   cargo bench -p mettail-prattail --bench bench_dispatch --features grammar-gen
//!
//! Run full A/B (with wfst):
//!   cargo bench -p mettail-prattail --bench bench_dispatch --features grammar-gen,wfst

mod bench_specs;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use mettail_prattail::{generate_parser, DispatchStrategy, LanguageSpec};
use mettail_prattail::grammar_gen::generate_bench_inputs;

use bench_specs::{
    minimal_spec, small_spec, medium_spec, complex_spec, synthetic_spec,
};

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Clone a spec with a different dispatch strategy.
fn with_dispatch(spec: &LanguageSpec, strategy: DispatchStrategy) -> LanguageSpec {
    let mut s = spec.clone();
    s.dispatch_strategy = strategy;
    s
}

// ══════════════════════════════════════════════════════════════════════════════
// Group 1: A/B comparison for each standard spec
// ══════════════════════════════════════════════════════════════════════════════

fn dispatch_ab(c: &mut Criterion) {
    let specs: Vec<(&str, LanguageSpec)> = vec![
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    let mut group = c.benchmark_group("dispatch/a_b");

    for (name, spec) in &specs {
        // Static dispatch
        let static_spec = with_dispatch(spec, DispatchStrategy::Static);
        group.bench_with_input(
            BenchmarkId::new("static", name),
            &static_spec,
            |b, s| b.iter(|| generate_parser(s)),
        );

        // Weighted dispatch (only available with wfst feature)
        #[cfg(feature = "wfst")]
        {
            let weighted_spec = with_dispatch(spec, DispatchStrategy::Weighted);
            group.bench_with_input(
                BenchmarkId::new("weighted", name),
                &weighted_spec,
                |b, s| b.iter(|| generate_parser(s)),
            );
        }
    }

    group.finish();
}

// ══════════════════════════════════════════════════════════════════════════════
// Group 2: Scaling — synthetic specs at various rule counts
// ══════════════════════════════════════════════════════════════════════════════

fn dispatch_scaling(c: &mut Criterion) {
    let rule_counts = [5, 10, 20, 50, 100];

    let mut group = c.benchmark_group("dispatch/scaling");

    for &n in &rule_counts {
        let spec = synthetic_spec(n);

        // Static
        let static_spec = with_dispatch(&spec, DispatchStrategy::Static);
        group.bench_with_input(
            BenchmarkId::new("static", n),
            &static_spec,
            |b, s| b.iter(|| generate_parser(s)),
        );

        // Weighted (wfst feature)
        #[cfg(feature = "wfst")]
        {
            let weighted_spec = with_dispatch(&spec, DispatchStrategy::Weighted);
            group.bench_with_input(
                BenchmarkId::new("weighted", n),
                &weighted_spec,
                |b, s| b.iter(|| generate_parser(s)),
            );
        }
    }

    group.finish();
}

// ══════════════════════════════════════════════════════════════════════════════
// Group 3: Grammar-aware expression generation benchmark
// ══════════════════════════════════════════════════════════════════════════════

fn dispatch_grammar_gen(c: &mut Criterion) {
    let specs: Vec<(&str, LanguageSpec, &str)> = vec![
        ("minimal", minimal_spec(), "Term"),
        ("small", small_spec(), "Int"),
        ("medium", medium_spec(), "Proc"),
        ("complex", complex_spec(), "Proc"),
    ];

    let mut group = c.benchmark_group("dispatch/grammar_gen");

    for (name, spec, category) in &specs {
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &(spec, *category),
            |b, (s, cat)| {
                b.iter(|| generate_bench_inputs(s, cat, 5, 50))
            },
        );
    }

    group.finish();
}

// ══════════════════════════════════════════════════════════════════════════════
// Criterion main
// ══════════════════════════════════════════════════════════════════════════════

criterion_group!(benches, dispatch_ab, dispatch_scaling, dispatch_grammar_gen);
criterion_main!(benches);
