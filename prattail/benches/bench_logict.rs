//! LogicT fair backtracking search benchmarks.
//!
//! Measures:
//! - Interleave throughput (1K/10K/100K branches)
//! - fair_conjoin depth scaling
//! - Search with bounded labeling
//! - Iterator collect performance
//! - once/gnot/ifte throughput

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use mettail_prattail::logict::{LogicStream, multiset_partitions, multiset_select};

fn bench_interleave_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("logict/interleave");

    for size in [100, 1_000, 10_000] {
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &size,
            |b, &size| {
                b.iter(|| {
                    let left = LogicStream::from_iter(0..size);
                    let right = LogicStream::from_iter(size..2 * size);
                    let merged = left.interleave(right);
                    let results = merged.collect_all();
                    black_box(results.len());
                });
            },
        );
    }

    group.finish();
}

fn bench_mplus(c: &mut Criterion) {
    let mut group = c.benchmark_group("logict/mplus");

    for size in [100, 1_000, 10_000] {
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &size,
            |b, &size| {
                b.iter(|| {
                    let left = LogicStream::from_iter(0..size);
                    let right = LogicStream::from_iter(size..2 * size);
                    let merged = left.mplus(right);
                    let results = merged.collect_all();
                    black_box(results.len());
                });
            },
        );
    }

    group.finish();
}

fn bench_fair_conjoin(c: &mut Criterion) {
    let mut group = c.benchmark_group("logict/fair_conjoin");

    // fair_conjoin depth 1: 100 elements x identity function
    group.bench_function("depth_1_100", |b| {
        b.iter(|| {
            let stream = LogicStream::from_iter(0..100_i32);
            let result = stream.fair_conjoin(|x| LogicStream::unit(x * 2));
            let results = result.collect_all();
            black_box(results.len());
        });
    });

    // fair_conjoin depth 2: 10 x 10 Cartesian product
    group.bench_function("depth_2_10x10", |b| {
        b.iter(|| {
            let stream = LogicStream::from_iter(0..10_i32);
            let result = stream.fair_conjoin(|x| {
                LogicStream::from_iter((0..10).map(move |y| (x, y)))
            });
            let results = result.collect_all();
            black_box(results.len());
        });
    });

    // fair_conjoin depth 2: 100 x 10
    group.bench_function("depth_2_100x10", |b| {
        b.iter(|| {
            let stream = LogicStream::from_iter(0..100_i32);
            let result = stream.fair_conjoin(|x| {
                LogicStream::from_iter((0..10).map(move |y| (x, y)))
            });
            let results = result.collect_all();
            black_box(results.len());
        });
    });

    group.finish();
}

fn bench_once(c: &mut Criterion) {
    let mut group = c.benchmark_group("logict/once");

    for size in [100, 1_000, 10_000] {
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &size,
            |b, &size| {
                b.iter(|| {
                    let stream = LogicStream::from_iter(0..size);
                    let result = stream.once();
                    let results = result.collect_all();
                    black_box(results.len());
                });
            },
        );
    }

    group.finish();
}

fn bench_collect_bounded(c: &mut Criterion) {
    let mut group = c.benchmark_group("logict/collect_bounded");

    // Collect first 10 from a 10K stream
    group.bench_function("10_from_10K", |b| {
        b.iter(|| {
            let stream = LogicStream::from_iter(0..10_000_i32);
            let results = stream.collect_bounded(10);
            black_box(results.len());
        });
    });

    // Collect first 100 from a 10K stream
    group.bench_function("100_from_10K", |b| {
        b.iter(|| {
            let stream = LogicStream::from_iter(0..10_000_i32);
            let results = stream.collect_bounded(100);
            black_box(results.len());
        });
    });

    group.finish();
}

fn bench_ifte(c: &mut Criterion) {
    let mut group = c.benchmark_group("logict/ifte");

    // ifte with success -> then branch
    group.bench_function("success", |b| {
        b.iter(|| {
            let test = LogicStream::unit(42_i32);
            let result = test.ifte(
                |x| LogicStream::unit(x * 2),
                LogicStream::unit(-1),
            );
            let results = result.collect_all();
            black_box(results);
        });
    });

    // ifte with failure -> else branch
    group.bench_function("failure", |b| {
        b.iter(|| {
            let test: LogicStream<i32> = LogicStream::empty();
            let result = test.ifte(
                |x| LogicStream::unit(x * 2),
                LogicStream::unit(-1),
            );
            let results = result.collect_all();
            black_box(results);
        });
    });

    group.finish();
}

fn bench_gnot(c: &mut Criterion) {
    let mut group = c.benchmark_group("logict/gnot");

    // gnot of empty stream -> unit (success)
    group.bench_function("empty_stream", |b| {
        b.iter(|| {
            let stream: LogicStream<i32> = LogicStream::empty();
            let result = stream.gnot();
            let results = result.collect_all();
            black_box(results);
        });
    });

    // gnot of non-empty stream -> empty (failure)
    group.bench_function("non_empty_stream", |b| {
        b.iter(|| {
            let stream = LogicStream::unit(42_i32);
            let result = stream.gnot();
            let results = result.collect_all();
            black_box(results);
        });
    });

    group.finish();
}

fn bench_ac_match(c: &mut Criterion) {
    let mut group = c.benchmark_group("logict/ac_match");

    // 5 distinct elements, K=2 → C(5,2) = 10 partitions
    group.bench_function("partition_5_k2", |b| {
        let items: Vec<(u32, usize)> = (0..5).map(|i| (i, 1)).collect();
        b.iter(|| {
            let results = multiset_partitions(black_box(&items), 2).collect_all();
            black_box(results.len());
        });
    });

    // 10 distinct elements, K=3 → C(10,3) = 120 partitions
    group.bench_function("partition_10_k3", |b| {
        let items: Vec<(u32, usize)> = (0..10).map(|i| (i, 1)).collect();
        b.iter(|| {
            let results = multiset_partitions(black_box(&items), 3).collect_all();
            black_box(results.len());
        });
    });

    // 20 distinct elements, K=3 → C(20,3) = 1140 partitions
    group.bench_function("partition_20_k3", |b| {
        let items: Vec<(u32, usize)> = (0..20).map(|i| (i, 1)).collect();
        b.iter(|| {
            let results = multiset_partitions(black_box(&items), 3).collect_all();
            black_box(results.len());
        });
    });

    // 20 distinct elements, K=3, bounded to 10 results
    group.bench_function("partition_bounded_20_k3", |b| {
        let items: Vec<(u32, usize)> = (0..20).map(|i| (i, 1)).collect();
        b.iter(|| {
            let results = multiset_select(black_box(&items), 3, 10);
            black_box(results.len());
        });
    });

    // Elements with multiplicity: {A:5, B:3, C:2}, K=4
    group.bench_function("partition_with_multiplicity", |b| {
        let items = vec![(0u32, 5), (1, 3), (2, 2)];
        b.iter(|| {
            let results = multiset_partitions(black_box(&items), 4).collect_all();
            black_box(results.len());
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_interleave_throughput,
    bench_mplus,
    bench_fair_conjoin,
    bench_once,
    bench_collect_bounded,
    bench_ifte,
    bench_gnot,
    bench_ac_match,
);
criterion_main!(benches);
