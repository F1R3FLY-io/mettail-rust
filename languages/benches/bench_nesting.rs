//! Recursive descent depth benchmarks: lambdas, applications, parentheses.
//!
//! Languages: Lambda (Term), Calculator (Int)
//! Features exercised: RD handler recursion, terminal matching,
//! nonterminal parsing, binder creation, parenthesized grouping.
//!
//! Run with: cargo bench -p mettail-languages --bench bench_nesting

mod bench_common;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use mettail_languages::calculator::*;
use mettail_languages::lambda::*;
use std::time::Duration;

use bench_common::{
    gen_lambda_app_mix, gen_nested_application, gen_nested_lambda, gen_nested_parens, DEPTH_SIZES,
};

fn bench_lambda_depth(c: &mut Criterion) {
    let mut group = c.benchmark_group("nesting/lambda_depth");
    for &d in DEPTH_SIZES {
        let input = gen_nested_lambda(d);
        group.throughput(Throughput::Elements(d as u64));
        group.bench_with_input(BenchmarkId::from_parameter(d), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Term::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_application_depth(c: &mut Criterion) {
    let mut group = c.benchmark_group("nesting/application_depth");
    for &d in DEPTH_SIZES {
        let input = gen_nested_application(d);
        group.throughput(Throughput::Elements(d as u64));
        group.bench_with_input(BenchmarkId::from_parameter(d), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Term::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_paren_depth(c: &mut Criterion) {
    let mut group = c.benchmark_group("nesting/paren_depth");
    for &d in DEPTH_SIZES {
        let input = gen_nested_parens(d);
        group.throughput(Throughput::Elements(d as u64));
        group.bench_with_input(BenchmarkId::from_parameter(d), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Int::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_lambda_app_mix(c: &mut Criterion) {
    let mut group = c.benchmark_group("nesting/lambda_app_mix");
    for &d in DEPTH_SIZES {
        let input = gen_lambda_app_mix(d);
        group.throughput(Throughput::Elements(d as u64));
        group.bench_with_input(BenchmarkId::from_parameter(d), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Term::parse(black_box(input)).expect("parse failed")
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
    targets = bench_lambda_depth,
        bench_application_depth,
        bench_paren_depth,
        bench_lambda_app_mix
}
criterion_main!(benches);
