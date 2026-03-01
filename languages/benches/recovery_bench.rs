//! Recovery benchmarks for PraTTaIL error recovery performance.
//!
//! Measures:
//! - Happy-path overhead of `parse_recovering()` vs `parse()`
//! - Single-error recovery latency
//! - Cascade recovery (multiple errors)
//! - Deeply nested expressions with errors
//! - Multi-step Viterbi recovery
//!
//! Run with: cargo bench -p mettail-languages --bench recovery_bench

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use mettail_languages::calculator::Int;
use std::time::Duration;

/// Benchmark: valid input via parse() (baseline).
fn bench_parse_valid(c: &mut Criterion) {
    let mut group = c.benchmark_group("recovery/valid_baseline");
    group.measurement_time(Duration::from_secs(5));

    let inputs: Vec<(&str, &str)> = vec![
        ("literal", "42"),
        ("addition", "1 + 2"),
        ("chain", "1 + 2 + 3 + 4 + 5"),
        ("parens", "((1 + 2) + 3)"),
        ("complex", "(1 + 2) * 3 - 4 / 2"),
    ];

    for (name, input) in &inputs {
        group.bench_with_input(BenchmarkId::new("parse", name), input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                let _ = black_box(Int::parse(input));
            })
        });
    }
    group.finish();
}

/// Benchmark: valid input via parse_recovering() (measures happy-path overhead).
fn bench_parse_recovering_valid(c: &mut Criterion) {
    let mut group = c.benchmark_group("recovery/valid_recovering");
    group.measurement_time(Duration::from_secs(5));

    let inputs: Vec<(&str, &str)> = vec![
        ("literal", "42"),
        ("addition", "1 + 2"),
        ("chain", "1 + 2 + 3 + 4 + 5"),
        ("parens", "((1 + 2) + 3)"),
        ("complex", "(1 + 2) * 3 - 4 / 2"),
    ];

    for (name, input) in &inputs {
        group.bench_with_input(
            BenchmarkId::new("parse_recovering", name),
            input,
            |b, input| {
                b.iter(|| {
                    mettail_runtime::clear_var_cache();
                    let _ = black_box(Int::parse_recovering(input));
                })
            },
        );
    }
    group.finish();
}

/// Benchmark: single-error recovery.
fn bench_recovery_single_error(c: &mut Criterion) {
    let mut group = c.benchmark_group("recovery/single_error");
    group.measurement_time(Duration::from_secs(5));

    let inputs: Vec<(&str, &str)> = vec![
        ("extra_op", "1 + + 2"),
        ("trailing_int", "1 2"),
        ("trailing_op", "1 +"),
        ("empty_input", ""),
        ("unclosed_paren", "(1 + 2"),
    ];

    for (name, input) in &inputs {
        group.bench_with_input(BenchmarkId::new("recover", name), input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                let _ = black_box(Int::parse_recovering(input));
            })
        });
    }
    group.finish();
}

/// Benchmark: cascading errors (multiple error sites).
fn bench_recovery_cascade(c: &mut Criterion) {
    let mut group = c.benchmark_group("recovery/cascade");
    group.measurement_time(Duration::from_secs(5));

    let inputs: Vec<(&str, String)> = vec![
        ("2_errors", "1 + + + 2".to_string()),
        ("4_errors", "1 + + + + + 2".to_string()),
        ("8_errors", "1 + + + + + + + + + 2".to_string()),
    ];

    for (name, input) in &inputs {
        group.bench_with_input(BenchmarkId::new("cascade", name), input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                let _ = black_box(Int::parse_recovering(input));
            })
        });
    }
    group.finish();
}

/// Benchmark: deeply nested expressions with errors.
fn bench_recovery_deeply_nested(c: &mut Criterion) {
    let mut group = c.benchmark_group("recovery/nested");
    group.measurement_time(Duration::from_secs(5));

    for depth in [5, 10, 20, 50] {
        let open: String = "(".repeat(depth);
        let close: String = ")".repeat(depth);
        // Valid nested
        let valid_input = format!("{}1 + 2{}", open, close);
        group.bench_with_input(
            BenchmarkId::new("valid", depth),
            &valid_input,
            |b, input| {
                b.iter(|| {
                    mettail_runtime::clear_var_cache();
                    let _ = black_box(Int::parse_recovering(input));
                })
            },
        );
        // Nested with error
        let error_input = format!("{}1 + + 2{}", open, close);
        group.bench_with_input(
            BenchmarkId::new("error", depth),
            &error_input,
            |b, input| {
                b.iter(|| {
                    mettail_runtime::clear_var_cache();
                    let _ = black_box(Int::parse_recovering(input));
                })
            },
        );
    }
    group.finish();
}

/// Benchmark: multi-step recovery (requires Viterbi).
fn bench_recovery_multistep(c: &mut Criterion) {
    let mut group = c.benchmark_group("recovery/multistep");
    group.measurement_time(Duration::from_secs(5));

    let inputs: Vec<(&str, &str)> = vec![
        ("juxtaposed_3", "1 2 3"),
        ("juxtaposed_5", "1 2 3 4 5"),
        ("mixed_junk", "1 + * / 2"),
    ];

    for (name, input) in &inputs {
        group.bench_with_input(BenchmarkId::new("multistep", name), input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                let _ = black_box(Int::parse_recovering(input));
            })
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_parse_valid,
    bench_parse_recovering_valid,
    bench_recovery_single_error,
    bench_recovery_cascade,
    bench_recovery_deeply_nested,
    bench_recovery_multistep,
);
criterion_main!(benches);
