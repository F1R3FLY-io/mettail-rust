//! Binder and ZipMapSep benchmarks: single binder, multi-binder, channel output.
//!
//! Languages: Ambient (single binder via `new`), RhoCalc (multi-input ZipMapSep)
//! Features exercised: single binder (Scope creation, ident capture),
//! multi-binder, ZipMapSep (parallel dual-vec parsing with closing delimiter guard).
//!
//! Run with: cargo bench -p mettail-languages --bench bench_binders

mod bench_common;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::time::Duration;
use mettail_languages::ambient;
use mettail_languages::rhocalc;

use bench_common::{gen_chained_new, gen_multi_input, gen_nested_output, DEPTH_SIZES, SIZES};

/// ZipMapSep sizes: smaller range since each element involves two parallel vectors.
const ZIPMAPSEP_SIZES: &[usize] = &[1, 2, 4, 8, 16, 32];

fn bench_single_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("binders/single_chain");
    for &d in DEPTH_SIZES {
        let input = gen_chained_new(d);
        group.throughput(Throughput::Elements(d as u64));
        group.bench_with_input(BenchmarkId::from_parameter(d), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                ambient::Proc::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_zipmapsep_width(c: &mut Criterion) {
    let mut group = c.benchmark_group("binders/zipmapsep_width");
    for &n in ZIPMAPSEP_SIZES {
        let input = gen_multi_input(n);
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

fn bench_output_width(c: &mut Criterion) {
    let mut group = c.benchmark_group("binders/output_width");
    for &n in SIZES {
        let input = gen_nested_output(n);
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
    targets = bench_single_chain,
        bench_zipmapsep_width,
        bench_output_width
}
criterion_main!(benches);
