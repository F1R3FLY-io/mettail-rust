//! End-to-end benchmarks for the full `generate_parser()` pipeline.
//!
//! Measures total time for:
//! 1. Four realistic language specs of increasing complexity
//! 2. Scaling behavior with synthetic specs (5, 10, 20, 50, 100 infix operators)
//! 3. Output size (generated TokenStream byte count)

mod bench_specs;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::time::Duration;

use mettail_prattail::generate_parser;

use bench_specs::{complex_spec, medium_spec, minimal_spec, small_spec, synthetic_spec};

fn bench_end_to_end(c: &mut Criterion) {
    let mut group = c.benchmark_group("generator/end_to_end");
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
            b.iter(|| generate_parser(spec));
        });
    }

    group.finish();
}

fn bench_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("generator/scaling");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    for n in [5, 10, 20, 50, 100] {
        let spec = synthetic_spec(n);
        let n_rules = spec.rules.len() as u64;
        group.throughput(Throughput::Elements(n_rules));
        group.bench_with_input(BenchmarkId::from_parameter(n), &spec, |b, spec| {
            b.iter(|| generate_parser(spec));
        });
    }

    group.finish();
}

fn bench_output_size(c: &mut Criterion) {
    let mut group = c.benchmark_group("generator/output_size");
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
        group.throughput(Throughput::Bytes(1)); // will be updated per-iteration
        group.bench_with_input(BenchmarkId::from_parameter(name), spec, |b, spec| {
            b.iter(|| {
                let output = generate_parser(spec);
                let size = output.to_string().len();
                size
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_end_to_end, bench_scaling, bench_output_size);
criterion_main!(benches);
