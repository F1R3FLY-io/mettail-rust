//! Code generation phase benchmarks.
//!
//! Benchmarks the code generation phases:
//! 1. RD handler generation (per-spec, summed over all RD rules)
//! 2. Pratt parser generation (per-spec, summed over all categories)
//! 3. Cross-category dispatch generation
//! 4. Helper function generation (static, no spec variation)

mod bench_specs;

use std::time::Duration;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

use mettail_prattail::dispatch::write_category_dispatch;
use mettail_prattail::pratt::{write_parser_helpers, write_pratt_parser};
use mettail_prattail::recursive::write_rd_handler;

use bench_specs::{complex_spec, medium_spec, minimal_spec, prepare, small_spec};

fn bench_rd_handlers(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen/rd_handlers");
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
                let mut buf = String::with_capacity(4096);
                for rd_rule in &prepared.rd_rules {
                    let _ = write_rd_handler(&mut buf, rd_rule);
                }
            });
        });
    }

    group.finish();
}

fn bench_pratt_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen/pratt_parser");
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
                let mut buf = String::with_capacity(4096);
                for ppc in &prepared.pratt_configs {
                    write_pratt_parser(&mut buf, &ppc.config, &prepared.bp_table, &ppc.handlers);
                }
            });
        });
    }

    group.finish();
}

fn bench_dispatch(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen/dispatch");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    // Only specs with cross-category rules produce dispatch code
    let specs = [("small", small_spec()), ("complex", complex_spec())];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(BenchmarkId::from_parameter(name), &prepared, |b, prepared| {
            b.iter(|| {
                let mut buf = String::with_capacity(4096);
                for cat in &prepared.categories {
                    let cat_cross: Vec<_> = prepared
                        .cross_rules
                        .iter()
                        .filter(|r| r.result_category == *cat)
                        .cloned()
                        .collect();
                    if !cat_cross.is_empty() {
                        write_category_dispatch(
                            &mut buf,
                            cat,
                            &cat_cross,
                            &[],
                            &prepared.overlaps,
                            &prepared.first_sets,
                        );
                    }
                }
            });
        });
    }

    group.finish();
}

fn bench_helpers(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen/helpers");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    group.bench_function("write_parser_helpers", |b| {
        b.iter(|| {
            let mut buf = String::with_capacity(2048);
            write_parser_helpers(&mut buf);
        });
    });

    group.finish();
}

criterion_group!(benches, bench_rd_handlers, bench_pratt_parser, bench_dispatch, bench_helpers,);
criterion_main!(benches);
