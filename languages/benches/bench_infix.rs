//! Pratt infix loop benchmarks: chains, precedence, associativity.
//!
//! Language: Calculator (Int)
//! Features exercised: binding power lookup, precedence climbing,
//! left/right associativity, make_infix construction, token consumption.
//!
//! Run with: cargo bench -p mettail-languages --bench bench_infix

mod bench_common;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::time::Duration;
use mettail_languages::calculator::*;

use bench_common::{
    gen_alternating_add_sub, gen_infix_chain, gen_mixed_precedence, gen_right_assoc_chain, SIZES,
};

fn bench_left_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("infix/left_chain");
    for &n in SIZES {
        let input = gen_infix_chain(n, "+");
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

fn bench_right_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("infix/right_chain");
    for &n in SIZES {
        let input = gen_right_assoc_chain(n);
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

fn bench_mixed_prec(c: &mut Criterion) {
    let mut group = c.benchmark_group("infix/mixed_prec");
    for &n in SIZES {
        let input = gen_mixed_precedence(n);
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

fn bench_mixed_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("infix/mixed_ops");
    for &n in SIZES {
        let input = gen_alternating_add_sub(n);
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

criterion_group! {
    name = benches;
    config = Criterion::default()
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(5))
        .sample_size(100);
    targets = bench_left_chain,
        bench_right_chain,
        bench_mixed_prec,
        bench_mixed_ops
}
criterion_main!(benches);
