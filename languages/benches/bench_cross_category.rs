//! Cross-category dispatch benchmarks: FIRST set dispatch, cast rules.
//!
//! Languages: Calculator (cross-cat `==`), RhoCalc (cast `Int -> Proc`)
//! Features exercised: FIRST set dispatch, unambiguous cross-category rules,
//! cast rules (prefix handler), backtracking (save/restore for ambiguous tokens).
//!
//! Run with: cargo bench -p mettail-languages --bench bench_cross_category

mod bench_common;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::time::Duration;
use mettail_languages::calculator;
use mettail_languages::rhocalc;

use bench_common::{gen_cast_chain, gen_cross_cat_eq, SIZES};

fn bench_simple_eq(c: &mut Criterion) {
    let mut group = c.benchmark_group("cross_cat/simple_eq");
    let input = "1 == 2";
    group.bench_function("baseline", |b| {
        b.iter(|| {
            mettail_runtime::clear_var_cache();
            calculator::Bool::parse(black_box(input)).expect("parse failed")
        })
    });
    group.finish();
}

fn bench_eq_complex(c: &mut Criterion) {
    let mut group = c.benchmark_group("cross_cat/eq_complex");
    for &n in SIZES {
        let input = gen_cross_cat_eq(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                calculator::Bool::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_cast_int(c: &mut Criterion) {
    let mut group = c.benchmark_group("cross_cat/cast_int");
    let input = "42";
    group.bench_function("baseline", |b| {
        b.iter(|| {
            mettail_runtime::clear_var_cache();
            rhocalc::Proc::parse(black_box(input)).expect("parse failed")
        })
    });
    group.finish();
}

fn bench_cast_in_parallel(c: &mut Criterion) {
    let mut group = c.benchmark_group("cross_cat/cast_in_parallel");
    for &n in SIZES {
        let input = gen_cast_chain(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                rhocalc::Proc::parse(black_box(input)).expect("parse failed")
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
    targets = bench_simple_eq,
        bench_eq_complex,
        bench_cast_int,
        bench_cast_in_parallel
}
criterion_main!(benches);
