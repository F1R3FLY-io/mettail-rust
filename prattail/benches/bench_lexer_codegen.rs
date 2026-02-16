//! Lexer codegen sub-function benchmarks.
//!
//! Benchmarks each code generation sub-function independently to identify
//! optimization targets within the codegen phase (53.2% of pipeline time).
//!
//! Groups:
//! 1. `lexer_codegen/token_enum` — Token enum generation
//! 2. `lexer_codegen/span_def` — Span struct generation (constant)
//! 3. `lexer_codegen/class_table` — Equivalence class lookup table
//! 4. `lexer_codegen/accept_arms` — Accept match arms
//! 5. `lexer_codegen/transition_arms` — DFA transition match arms
//! 6. `lexer_codegen/direct_coded` — Complete direct-coded lexer
//! 7. `lexer_codegen/table_driven` — Complete table-driven lexer
//! 8. `lexer_codegen/full` — Full lexer code generation
//! 9. `lexer_codegen/scaling` — Scaling with synthetic specs

mod bench_specs;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::time::Duration;

use mettail_prattail::automata::codegen::{
    generate_accept_match_arms, generate_class_table, generate_direct_coded_lexer,
    generate_lexer_code, generate_span_def, generate_table_driven_lexer, generate_token_enum,
    generate_transition_match_arms,
};

use bench_specs::{complex_spec, medium_spec, minimal_spec, prepare, small_spec, synthetic_spec};

fn bench_token_enum(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/token_enum");
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
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &prepared,
            |b, prepared| {
                b.iter(|| generate_token_enum(&prepared.token_kinds));
            },
        );
    }

    group.finish();
}

fn bench_span_def(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/span_def");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    group.bench_function("generate_span_def", |b| {
        b.iter(|| generate_span_def());
    });

    group.finish();
}

fn bench_class_table(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/class_table");
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
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &prepared,
            |b, prepared| {
                b.iter(|| generate_class_table(&prepared.partition));
            },
        );
    }

    group.finish();
}

fn bench_accept_arms(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/accept_arms");
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
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &prepared,
            |b, prepared| {
                b.iter(|| generate_accept_match_arms(&prepared.min_dfa));
            },
        );
    }

    group.finish();
}

fn bench_transition_arms(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/transition_arms");
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
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &prepared,
            |b, prepared| {
                b.iter(|| generate_transition_match_arms(&prepared.min_dfa, &prepared.partition));
            },
        );
    }

    group.finish();
}

fn bench_direct_coded(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/direct_coded");
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
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &prepared,
            |b, prepared| {
                b.iter(|| {
                    generate_direct_coded_lexer(
                        &prepared.min_dfa,
                        &prepared.partition,
                        &prepared.token_kinds,
                    )
                });
            },
        );
    }

    group.finish();
}

fn bench_table_driven(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/table_driven");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    // Table-driven is for larger DFAs, but we benchmark it on all specs for comparison
    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &prepared,
            |b, prepared| {
                b.iter(|| {
                    generate_table_driven_lexer(
                        &prepared.min_dfa,
                        &prepared.partition,
                        &prepared.token_kinds,
                    )
                });
            },
        );
    }

    group.finish();
}

fn bench_full_codegen(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/full");
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
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &prepared,
            |b, prepared| {
                b.iter(|| {
                    generate_lexer_code(
                        &prepared.min_dfa,
                        &prepared.partition,
                        &prepared.token_kinds,
                        &prepared.spec.name,
                    )
                });
            },
        );
    }

    group.finish();
}

fn bench_codegen_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/scaling");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    for n in [5, 10, 20, 50, 100] {
        let spec = synthetic_spec(n);
        let prepared = prepare(&spec);
        let n_terminals = prepared.lexer_input.terminals.len() as u64;
        group.throughput(Throughput::Elements(n_terminals));
        group.bench_with_input(
            BenchmarkId::from_parameter(n),
            &prepared,
            |b, prepared| {
                b.iter(|| {
                    generate_lexer_code(
                        &prepared.min_dfa,
                        &prepared.partition,
                        &prepared.token_kinds,
                        &prepared.spec.name,
                    )
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_token_enum,
    bench_span_def,
    bench_class_table,
    bench_accept_arms,
    bench_transition_arms,
    bench_direct_coded,
    bench_table_driven,
    bench_full_codegen,
    bench_codegen_scaling,
);
criterion_main!(benches);
