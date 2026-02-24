//! Parse-only benchmarks for PraTTaIL parser performance.
//!
//! Run with: cargo bench -p mettail-languages --bench parse_bench

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use mettail_languages::ambient::*;
use mettail_languages::calculator::*;
use mettail_languages::lambda::*;
use mettail_languages::rhocalc::*;
use std::time::Duration;

// =============================================================================
// Ambient Calculus inputs
// =============================================================================

fn ambient_inputs() -> Vec<(&'static str, &'static str)> {
    vec![
        ("zero", "{}"),
        ("variable", "x"),
        ("simple_amb", "n[p]"),
        ("capability_in", "in(n,p)"),
        ("parallel", "{p | q}"),
        ("nested", "n[{in(m,p)}]"),
        ("complex", "{n[{in(m,p)}] | m[r]}"),
        ("new", "new(x,p)"),
        ("deep_nested", "{n[{in(m,p) | inner[data]}] | m[{r | local}]}"),
        ("multi_parallel", "{a[{in(parent,x)}] | b[{in(parent,y)}] | parent[z]}"),
    ]
}

// =============================================================================
// Calculator inputs
// =============================================================================

fn calculator_inputs() -> Vec<(&'static str, &'static str)> {
    vec![
        ("integer", "42"),
        ("variable", "x"),
        ("addition", "1 + 2"),
        ("chain_add", "1 + 2 + 3"),
        ("mixed_ops", "1 + 2 - 3"),
        ("power", "2 ^ 3"),
        ("bool_true", "true"),
        ("bool_false", "false"),
        ("string_lit", "\"hello\""),
        ("string_concat", "\"a\" ++ \"b\""),
        ("complex_expr", "1 + 2 + 3 + 4 + 5"),
    ]
}

// =============================================================================
// Lambda Calculus inputs
// =============================================================================

fn lambda_inputs() -> Vec<(&'static str, &'static str)> {
    vec![
        ("variable", "x"),
        ("abstraction", "lam x.x"),
        ("application", "(x,y)"),
        ("nested_lam", "lam x.lam y.x"),
        ("complex", "lam f.(lam x.(f,(x,x)),lam x.(f,(x,x)))"),
    ]
}

// =============================================================================
// RhoCalc inputs
// =============================================================================

fn rhocalc_inputs() -> Vec<(&'static str, &'static str)> {
    vec![
        ("zero", "{}"),
        ("variable", "x"),
        ("integer", "42"),
        ("error", "error"),
        ("drop", "*(n)"),
        ("quote", "@(p)"),
        ("output", "x!(p)"),
        ("addition", "1 + 2"),
        ("parallel", "{p | q}"),
        ("drop_quote", "*(@(p))"),
        ("nested_output", "{x!(p) | y!(q)}"),
        ("multi_input", "(x?a, y?b).{*(a)}"),
        ("complex", "{c!(0) | (c?x).{*(x)} | d!(1) | (d?y).{*(y)}}"),
    ]
}

// =============================================================================
// Benchmarks
// =============================================================================

fn bench_ambient_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse/ambient");
    for (name, input) in ambient_inputs() {
        group.bench_with_input(BenchmarkId::new("parse", name), input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                AmbientLanguage::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_calculator_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse/calculator");
    for (name, input) in calculator_inputs() {
        group.bench_with_input(BenchmarkId::new("parse", name), input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                CalculatorLanguage::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_lambda_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse/lambda");
    for (name, input) in lambda_inputs() {
        group.bench_with_input(BenchmarkId::new("parse", name), input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                LambdaLanguage::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_rhocalc_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse/rhocalc");
    for (name, input) in rhocalc_inputs() {
        group.bench_with_input(BenchmarkId::new("parse", name), input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                RhoCalcLanguage::parse(black_box(input)).expect("parse failed")
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
        .sample_size(200);
    targets = bench_ambient_parse,
        bench_calculator_parse,
        bench_lambda_parse,
        bench_rhocalc_parse
}
criterion_main!(benches);
