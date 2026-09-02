//! Runtime comparison gate for the generated tagged typed-assembly kernel.
//!
//! Parsing is outside every timed loop. The normalization group exercises
//! ordinary application assembly, beta assembly, and binder traversal. The
//! Dovetail group exercises the independently produced inverse-assembly path
//! that shares the same checked typed constructor kernel.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use mettail_languages::lambda::LambdaLanguage;
use mettail_runtime::{Language, Term};
use std::time::Duration;

const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 100_000;

fn parse(source: &str) -> Box<dyn Term> {
    LambdaLanguage
        .parse_term(source)
        .expect("benchmark Lambda term parses")
}

fn bench_generated_normalization(c: &mut Criterion) {
    let nested_binders = mettail_languages::bench_common::gen_nested_lambda(100);
    let nested_applications = mettail_languages::bench_common::gen_nested_application(100);
    let cases = [
        ("beta", parse("(lam x. (x,x), y)")),
        ("nested_binders_100", parse(&nested_binders)),
        ("nested_applications_100", parse(&nested_applications)),
    ];

    let mut group = c.benchmark_group("tagged_assembly/normalize");
    for (name, term) in &cases {
        group.bench_with_input(BenchmarkId::from_parameter(name), term.as_ref(), |b, term| {
            b.iter(|| black_box(LambdaLanguage.normalize_term(black_box(term))))
        });
    }
    group.finish();
}

fn bench_dovetail_inverse_assembly(c: &mut Criterion) {
    let nested_binders = mettail_languages::bench_common::gen_nested_lambda(25);
    let cases = [
        ("identity_beta", parse("(lam x. x, y)")),
        ("duplicating_beta", parse("(lam x. (x,x), y)")),
        ("nested_binders_25", parse(&nested_binders)),
    ];

    let mut group = c.benchmark_group("tagged_assembly/dovetail");
    for (name, term) in &cases {
        group.bench_with_input(BenchmarkId::from_parameter(name), term.as_ref(), |b, term| {
            b.iter(|| {
                black_box(LambdaLanguage::dovetail_report_for(
                    black_box(term),
                    MAX_ITERS,
                    MAX_NODES,
                ))
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
    targets = bench_generated_normalization, bench_dovetail_inverse_assembly
}
criterion_main!(benches);
