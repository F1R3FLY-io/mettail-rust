//! Collection parsing benchmarks: HashBag parallel composition.
//!
//! Language: Ambient (Proc with PPar, HashBag with `|` sep and `{}` delimiters)
//! Features exercised: collection loop (init, parse, insert/push, separator check),
//! HashBag construction, structural delimiters `{}`, element parsing recursion.
//!
//! Run with: cargo bench -p mettail-languages --bench bench_collections

mod bench_common;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use mettail_languages::ambient::*;
use std::time::Duration;

use bench_common::{gen_nested_parallel, gen_parallel, gen_parallel_amb, DEPTH_SIZES, SIZES};

fn bench_flat_parallel(c: &mut Criterion) {
    let mut group = c.benchmark_group("collections/flat_parallel");
    for &n in SIZES {
        let input = gen_parallel(n, "0");
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Proc::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_amb_parallel(c: &mut Criterion) {
    let mut group = c.benchmark_group("collections/amb_parallel");
    for &n in SIZES {
        let input = gen_parallel_amb(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Proc::parse(black_box(input)).expect("parse failed")
            })
        });
    }
    group.finish();
}

fn bench_nested_parallel(c: &mut Criterion) {
    let mut group = c.benchmark_group("collections/nested_parallel");
    for &d in DEPTH_SIZES {
        let input = gen_nested_parallel(d);
        group.throughput(Throughput::Elements(d as u64));
        group.bench_with_input(BenchmarkId::from_parameter(d), &input, |b, input| {
            b.iter(|| {
                mettail_runtime::clear_var_cache();
                Proc::parse(black_box(input)).expect("parse failed")
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
    targets = bench_flat_parallel,
        bench_amb_parallel,
        bench_nested_parallel
}
criterion_main!(benches);
