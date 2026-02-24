//! Full-language scaling benchmarks using composite deterministic inputs.
//!
//! Languages: All 4 (Calculator, Lambda, Ambient, RhoCalc)
//! Features exercised: ALL features simultaneously via composite inputs
//! built from deterministic generators. This shows overall O(n) scaling.
//!
//! Each benchmark group builds increasingly large inputs that exercise
//! multiple parser features simultaneously (infix + prefix + nesting, etc.)
//!
//! Run with: cargo bench -p mettail-languages --bench bench_scaling

mod bench_common;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use mettail_languages::ambient;
use mettail_languages::calculator;
use mettail_languages::lambda;
use mettail_languages::rhocalc;
use std::time::Duration;

use bench_common::{
    gen_chained_negation, gen_infix_chain, gen_mixed_precedence, gen_nested_application,
    gen_nested_lambda, gen_nested_output, gen_nested_parallel, gen_parallel, gen_parallel_amb,
    gen_right_assoc_chain, SIZES,
};

// =============================================================================
// Calculator composite scaling
// =============================================================================

/// Build a composite Calculator expression at scale N:
/// "- (1 + 2 + ... + N) + (2 ^ 2 ^ ... ^ 2) + (1 + 2 ^ 3 + 4 ^ ...)"
/// This exercises: infix left-assoc, infix right-assoc, mixed precedence,
/// unary prefix, and parenthesized grouping.
fn gen_calculator_composite(n: usize) -> String {
    let left = gen_infix_chain(n, "+");
    let right = gen_right_assoc_chain(n.min(20)); // cap ^ depth to avoid stack issues
    let mixed = gen_mixed_precedence(n);
    let neg = gen_chained_negation(n.min(50)); // cap negation depth
    format!("{} + ({}) + ({})", neg, left, right) + &format!(" + ({})", mixed)
}

fn bench_calculator_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling/calculator");
    for &n in SIZES {
        let input = gen_calculator_composite(n);
        let len = input.len();
        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(BenchmarkId::new("composite", n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                calculator::Int::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

// =============================================================================
// Lambda composite scaling
// =============================================================================

/// Build a composite Lambda expression at scale N:
/// "lam x0.lam x1. ... lam xN.(((x0,x1),x2), ...)"
/// This exercises: lambda abstraction depth, application nesting,
/// binder creation, terminal matching, and grouping.
fn gen_lambda_composite(n: usize) -> String {
    let lam_depth = n.min(100); // cap lambda nesting
    let app_depth = n.min(100);
    let lam = gen_nested_lambda(lam_depth);
    let app = gen_nested_application(app_depth);
    // Replace the body of the lambda chain with a nested application
    // gen_nested_lambda produces "lam x0.lam x1....x0", replace trailing "x0" with app
    if lam_depth > 0 {
        let prefix = &lam[..lam.len() - 2]; // strip trailing "x0"
        format!("{}{}", prefix, app)
    } else {
        app
    }
}

fn bench_lambda_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling/lambda");
    // Use DEPTH_SIZES for lambda since it's recursion-heavy
    let sizes: &[usize] = &[1, 5, 10, 25, 50, 100];
    for &n in sizes {
        let input = gen_lambda_composite(n);
        let len = input.len();
        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(BenchmarkId::new("composite", n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                lambda::Term::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

// =============================================================================
// Ambient composite scaling
// =============================================================================

/// Build a composite Ambient expression at scale N:
/// "new(x0, new(x1, ... {n0[0] | n1[0] | ... | {0 | {0 | ...}}}))"
/// This exercises: binder chains, parallel composition, named ambients,
/// nested parallel, and structural delimiters.
fn gen_ambient_composite(n: usize) -> String {
    let binder_depth = n.min(50);
    let par_width = n;
    let nested_depth = n.min(50);
    // Build the body: parallel amb + nested parallel
    let par = gen_parallel_amb(par_width);
    let nested = gen_nested_parallel(nested_depth);
    let body = if par_width > 0 && nested_depth > 0 {
        // Merge: add nested_parallel as another element in the outer parallel
        let inner = &par[1..par.len() - 1]; // strip outer {}
        format!("{{{} | {}}}", inner, nested)
    } else if par_width > 0 {
        par
    } else {
        nested
    };
    // Wrap in binder chain
    let mut result = body;
    for i in (0..binder_depth).rev() {
        result = format!("new(x{},{})", i, result);
    }
    result
}

fn bench_ambient_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling/ambient");
    for &n in SIZES {
        let input = gen_ambient_composite(n);
        let len = input.len();
        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(BenchmarkId::new("composite", n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                ambient::Proc::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

// =============================================================================
// RhoCalc composite scaling
// =============================================================================

/// Build a composite RhoCalc expression at scale N:
/// "{c0!(0) | c1!(0) | ... | 1 | 2 | ... | N}"
/// This exercises: channel output, cast rules (int -> Proc),
/// parallel composition, and structural delimiters.
fn gen_rhocalc_composite(n: usize) -> String {
    // Output terms
    let outputs = gen_nested_output(n);
    // Cast chain (ints in parallel)
    let casts: Vec<String> = (1..=n.min(50)).map(|i| i.to_string()).collect();
    if n == 0 {
        return "{}".to_string();
    }
    // Combine outputs and casts in one parallel composition
    let output_inner = &outputs[1..outputs.len() - 1]; // strip {}
    if casts.is_empty() {
        outputs
    } else {
        format!("{{{} | {}}}", output_inner, casts.join(" | "))
    }
}

fn bench_rhocalc_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling/rhocalc");
    for &n in SIZES {
        let input = gen_rhocalc_composite(n);
        let len = input.len();
        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(BenchmarkId::new("composite", n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                rhocalc::Proc::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

// =============================================================================
// Width x Depth matrix for Ambient and RhoCalc
// =============================================================================

/// Ambient width x depth: flat parallel of varying widths at varying nesting depths.
fn bench_ambient_matrix(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling/ambient_matrix");
    for depth in [1, 3, 5, 10, 20] {
        for width in [2, 5, 10, 50] {
            // Build a nested parallel of `depth` levels, each with `width` elements
            let leaf = gen_parallel(width, "0");
            let mut result = leaf;
            for _ in 1..depth {
                let inner_terms: Vec<String> = (0..width - 1).map(|_| "0".to_string()).collect();
                result = format!("{{{} | {}}}", inner_terms.join(" | "), result);
            }
            let input = result;
            let len = input.len();
            group.throughput(Throughput::Bytes(len as u64));
            group.bench_with_input(
                BenchmarkId::new(format!("d{}_w{}", depth, width), len),
                &input,
                |b, input| {
                    b.iter(|| {
                        mettail_runtime::clear_var_cache();
                        ambient::Proc::parse(black_box(input)).expect("parse failed")
                    })
                },
            );
        }
    }
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(5))
        .sample_size(100);
    targets = bench_calculator_scaling,
        bench_lambda_scaling,
        bench_ambient_scaling,
        bench_rhocalc_scaling,
        bench_ambient_matrix
}
criterion_main!(benches);
