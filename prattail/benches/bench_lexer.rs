//! Lexer pipeline sub-phase benchmarks.
//!
//! Benchmarks each stage of the automata pipeline independently:
//! 1. Terminal extraction
//! 2. Full lexer pipeline (NFA -> DFA -> minimize -> codegen)
//! 3. NFA construction (Thompson's construction)
//! 4. Alphabet partitioning (equivalence classes)
//! 5. Subset construction (NFA -> DFA)
//! 6. DFA minimization (Hopcroft's algorithm)
//! 7. Code generation (DFA -> Rust source)
//! 8. Scaling with synthetic specs

mod bench_specs;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::time::Duration;

use mettail_prattail::automata::codegen::generate_lexer_code;
use mettail_prattail::automata::minimize::minimize_dfa;
use mettail_prattail::automata::nfa::build_nfa_default;
use mettail_prattail::automata::partition::compute_equivalence_classes;
use mettail_prattail::automata::subset::subset_construction;
use mettail_prattail::lexer::{extract_terminals, generate_lexer};

use bench_specs::{complex_spec, medium_spec, minimal_spec, prepare, small_spec, synthetic_spec};

fn bench_extract_terminals(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer/extract_terminals");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(BenchmarkId::from_parameter(name), &prepared, |b, prepared| {
            b.iter(|| extract_terminals(&prepared.grammar_rules, &prepared.type_infos, false, &[]));
        });
    }

    group.finish();
}

fn bench_full_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer/full_pipeline");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(BenchmarkId::from_parameter(name), &prepared, |b, prepared| {
            b.iter(|| generate_lexer(&prepared.lexer_input));
        });
    }

    group.finish();
}

fn bench_build_nfa(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer/build_nfa");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(BenchmarkId::from_parameter(name), &prepared, |b, prepared| {
            b.iter(|| {
                build_nfa_default(&prepared.lexer_input.terminals, &prepared.lexer_input.needs)
            });
        });
    }

    group.finish();
}

fn bench_partition(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer/partition");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(BenchmarkId::from_parameter(name), &prepared, |b, prepared| {
            b.iter(|| compute_equivalence_classes(&prepared.nfa));
        });
    }

    group.finish();
}

fn bench_subset_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer/subset_construction");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(BenchmarkId::from_parameter(name), &prepared, |b, prepared| {
            b.iter(|| subset_construction(&prepared.nfa, &prepared.partition));
        });
    }

    group.finish();
}

fn bench_minimize(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer/minimize");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(BenchmarkId::from_parameter(name), &prepared, |b, prepared| {
            b.iter(|| minimize_dfa(&prepared.dfa));
        });
    }

    group.finish();
}

fn bench_codegen(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer/codegen");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(BenchmarkId::from_parameter(name), &prepared, |b, prepared| {
            b.iter(|| {
                generate_lexer_code(
                    &prepared.min_dfa,
                    &prepared.partition,
                    &prepared.token_kinds,
                    &prepared.spec.name,
                )
            });
        });
    }

    group.finish();
}

fn bench_lexer_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer/scaling");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    for n in [5, 10, 20, 50, 100] {
        let spec = synthetic_spec(n);
        let prepared = prepare(&spec);
        let n_terminals = prepared.lexer_input.terminals.len() as u64;
        group.throughput(Throughput::Elements(n_terminals));
        group.bench_with_input(BenchmarkId::from_parameter(n), &prepared, |b, prepared| {
            b.iter(|| generate_lexer(&prepared.lexer_input));
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_extract_terminals,
    bench_full_pipeline,
    bench_build_nfa,
    bench_partition,
    bench_subset_construction,
    bench_minimize,
    bench_codegen,
    bench_lexer_scaling
);
criterion_main!(benches);
