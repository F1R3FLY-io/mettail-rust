//! Analysis phase benchmarks.
//!
//! Benchmarks the analysis phases of the parser generator:
//! 1. Binding power analysis
//! 2. FIRST set computation (fixed-point iteration)
//! 3. Dispatch table construction
//! 4. Cross-category overlap analysis

mod bench_specs;

use criterion::{
    criterion_group, criterion_main, BenchmarkId, Criterion, Throughput,
};
use std::time::Duration;

use mettail_prattail::binding_power::analyze_binding_powers;
use mettail_prattail::prediction::{
    analyze_cross_category_overlaps, build_dispatch_tables, compute_first_sets,
};

use bench_specs::{
    complex_spec, medium_spec, minimal_spec, prepare, small_spec, synthetic_spec,
};

fn bench_binding_powers(c: &mut Criterion) {
    let mut group = c.benchmark_group("analysis/binding_powers");
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
                b.iter(|| analyze_binding_powers(&prepared.infix_rules));
            },
        );
    }

    group.finish();
}

fn bench_first_sets(c: &mut Criterion) {
    let mut group = c.benchmark_group("analysis/first_sets");
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
                b.iter(|| compute_first_sets(&prepared.rule_infos, &prepared.categories));
            },
        );
    }

    group.finish();
}

fn bench_dispatch_tables(c: &mut Criterion) {
    let mut group = c.benchmark_group("analysis/dispatch_tables");
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
                    build_dispatch_tables(
                        &prepared.rule_infos,
                        &prepared.categories,
                        &prepared.first_sets,
                    )
                });
            },
        );
    }

    group.finish();
}

fn bench_overlaps(c: &mut Criterion) {
    let mut group = c.benchmark_group("analysis/overlaps");
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
                    analyze_cross_category_overlaps(&prepared.categories, &prepared.first_sets)
                });
            },
        );
    }

    group.finish();
}

fn bench_first_sets_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("analysis/first_sets_scaling");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    for n in [5, 10, 20, 50, 100] {
        let spec = synthetic_spec(n);
        let prepared = prepare(&spec);
        let n_rules = prepared.rule_infos.len() as u64;
        group.throughput(Throughput::Elements(n_rules));
        group.bench_with_input(
            BenchmarkId::from_parameter(n),
            &prepared,
            |b, prepared| {
                b.iter(|| compute_first_sets(&prepared.rule_infos, &prepared.categories));
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_binding_powers,
    bench_first_sets,
    bench_dispatch_tables,
    bench_overlaps,
    bench_first_sets_scaling,
);
criterion_main!(benches);
