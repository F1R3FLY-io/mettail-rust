//! Criterion benchmark: parser generation dispatch performance.
//!
//! Three benchmark groups:
//! 1. `dispatch/pipeline` — Pipeline cost for each standard spec (4 specs)
//! 2. `dispatch/scaling` — Pipeline cost at N = 5, 10, 20, 50, 100 rules
//! 3. `dispatch/grammar_gen` — Expression generation overhead per spec
//!
//! Run:
//!   cargo bench -p mettail-prattail --bench bench_dispatch --features grammar-gen

mod bench_specs;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use mettail_prattail::grammar_gen::generate_bench_inputs;
use mettail_prattail::generate_parser;

use bench_specs::{complex_spec, medium_spec, minimal_spec, small_spec, synthetic_spec};

// ══════════════════════════════════════════════════════════════════════════════
// Group 1: Pipeline cost for each standard spec
// ══════════════════════════════════════════════════════════════════════════════

fn dispatch_pipeline(c: &mut Criterion) {
    let specs = vec![
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    let mut group = c.benchmark_group("dispatch/pipeline");

    for (name, spec) in &specs {
        group.bench_with_input(BenchmarkId::from_parameter(name), spec, |b, s| {
            b.iter(|| generate_parser(s))
        });
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

        group.bench_with_input(BenchmarkId::from_parameter(n), &spec, |b, s| {
            b.iter(|| generate_parser(s))
        });
    }

    group.finish();
}

// ══════════════════════════════════════════════════════════════════════════════
// Group 3: Grammar-aware expression generation benchmark
// ══════════════════════════════════════════════════════════════════════════════

fn dispatch_grammar_gen(c: &mut Criterion) {
    let specs = vec![
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
            |b, (s, cat)| b.iter(|| generate_bench_inputs(s, cat, 5, 50)),
        );
    }

    group.finish();
}

// ══════════════════════════════════════════════════════════════════════════════
// Criterion main
// ══════════════════════════════════════════════════════════════════════════════

criterion_group!(benches, dispatch_pipeline, dispatch_scaling, dispatch_grammar_gen);
criterion_main!(benches);
