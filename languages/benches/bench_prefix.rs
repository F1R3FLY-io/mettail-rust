//! Unary prefix operator benchmarks: chained negation, keyword prefix, mixed contexts.
//!
//! Language: Calculator (Int for Neg, Bool for Not)
//! Features exercised: prefix handler dispatch, tight binding power,
//! shared operator tokens (e.g., `-` for both Neg and Sub).
//!
//! Run with: cargo bench -p mettail-languages --bench bench_prefix

mod bench_common;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::time::Duration;
use mettail_languages::calculator::*;

use bench_common::{gen_chained_negation, gen_not_chain, gen_prefix_infix, DEPTH_SIZES, SIZES};

fn bench_chained_neg(c: &mut Criterion) {
    let mut group = c.benchmark_group("prefix/chained_neg");
    for &n in DEPTH_SIZES {
        let input = gen_chained_negation(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Int::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_neg_plus_infix(c: &mut Criterion) {
    let mut group = c.benchmark_group("prefix/neg_plus_infix");
    for &n in SIZES {
        let input = gen_prefix_infix(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Int::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_not_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("prefix/not_chain");
    for &n in DEPTH_SIZES {
        let input = gen_not_chain(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Bool::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(5))
        .sample_size(100);
    targets = bench_chained_neg,
        bench_neg_plus_infix,
        bench_not_chain
}
criterion_main!(benches);
