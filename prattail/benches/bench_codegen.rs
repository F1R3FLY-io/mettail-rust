//! Code generation phase benchmarks.
//!
//! Benchmarks current parser generation entry points:
//! 1. Full parser generation
//! 2. Parser generation with retained pipeline analysis
//! 3. WFST preparation used by prediction/recovery codegen

mod bench_specs;

use std::time::Duration;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

use mettail_prattail::{generate_parser, generate_parser_with_analysis};

use bench_specs::{complex_spec, medium_spec, minimal_spec, prepare, prepare_wfst, small_spec};

fn bench_full_parser_generation(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen/full_parser");
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
        group.bench_with_input(BenchmarkId::from_parameter(name), spec, |b, spec| {
            b.iter(|| generate_parser(spec).expect("bench spec must be generable"));
        });
    }

    group.finish();
}

fn bench_parser_with_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen/parser_with_analysis");
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
        group.bench_with_input(BenchmarkId::from_parameter(name), spec, |b, spec| {
            b.iter(|| generate_parser_with_analysis(spec).expect("bench spec must be generable"));
        });
    }

    group.finish();
}

fn bench_analysis_preparation(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen/analysis_preparation");
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
        group.bench_with_input(BenchmarkId::from_parameter(name), spec, |b, spec| {
            b.iter(|| prepare(spec));
        });
    }

    group.finish();
}

fn bench_wfst_preparation(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen/wfst_preparation");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    let specs = [("small", small_spec()), ("complex", complex_spec())];

    for (name, spec) in &specs {
        group.bench_with_input(BenchmarkId::from_parameter(name), spec, |b, spec| {
            b.iter(|| prepare_wfst(spec));
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_full_parser_generation,
    bench_parser_with_analysis,
    bench_analysis_preparation,
    bench_wfst_preparation,
);
criterion_main!(benches);
