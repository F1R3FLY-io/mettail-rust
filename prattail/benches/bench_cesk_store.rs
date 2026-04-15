//! Benchmarks for the CESK store infrastructure.
//!
//! Measures throughput of store operations, two-stage lookup overhead,
//! persistent store fork cost, GC overhead, and abstract allocation strategies.

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::collections::HashMap;

use mettail_prattail::cesk_store::*;
use mettail_prattail::gc::*;

// ── LocalCeskStore benchmarks ───────────────────────────────────────────

fn bench_local_alloc(c: &mut Criterion) {
    c.bench_function("cesk/local_store/alloc_with", |b| {
        b.iter(|| {
            let mut store = LocalCeskStore::new();
            for i in 0..1000 {
                black_box(store.alloc_with(StoreValue::Simple(format!("v{}", i))));
            }
        });
    });
}

fn bench_local_get(c: &mut Criterion) {
    let mut store = LocalCeskStore::new();
    let addrs: Vec<u64> = (0..1000)
        .map(|i| store.alloc_with(StoreValue::Simple(format!("v{}", i))))
        .collect();

    c.bench_function("cesk/local_store/get", |b| {
        b.iter(|| {
            for &addr in &addrs {
                black_box(store.get(addr));
            }
        });
    });
}

fn bench_local_set(c: &mut Criterion) {
    let mut store = LocalCeskStore::new();
    let addrs: Vec<u64> = (0..1000)
        .map(|i| store.alloc_with(StoreValue::Simple(format!("v{}", i))))
        .collect();

    c.bench_function("cesk/local_store/set", |b| {
        b.iter(|| {
            for &addr in &addrs {
                store.set(addr, StoreValue::Simple("updated".to_string()));
            }
        });
    });
}

// ── Two-stage lookup overhead ───────────────────────────────────────────

fn bench_two_stage_lookup(c: &mut Criterion) {
    let mut store = LocalCeskStore::new();
    let mut env: HashMap<String, StoreAddr> = HashMap::new();

    for i in 0..1000 {
        let id = store.alloc_with(StoreValue::Simple(format!("v{}", i)));
        env.insert(format!("var_{}", i), StoreAddr::Local(id));
    }

    c.bench_function("cesk/two_stage_lookup", |b| {
        b.iter(|| {
            for (_, addr) in &env {
                black_box(store.get(addr.id()));
            }
        });
    });
}

fn bench_direct_hashmap_lookup(c: &mut Criterion) {
    let mut direct_env: HashMap<String, String> = HashMap::new();
    for i in 0..1000 {
        direct_env.insert(format!("var_{}", i), format!("v{}", i));
    }

    c.bench_function("cesk/direct_hashmap_lookup", |b| {
        b.iter(|| {
            for (_, v) in &direct_env {
                black_box(v);
            }
        });
    });
}

// ── RefCountGc benchmarks ───────────────────────────────────────────────

fn bench_refcount_inc_dec(c: &mut Criterion) {
    c.bench_function("cesk/refcount/inc_dec_cycle", |b| {
        b.iter(|| {
            let mut gc = RefCountGc::new();
            for i in 0u64..1000 {
                gc.inc_ref(i);
            }
            for i in 0u64..1000 {
                black_box(gc.dec_ref(i));
            }
        });
    });
}

fn bench_refcount_pending_drain(c: &mut Criterion) {
    c.bench_function("cesk/refcount/pending_drain", |b| {
        b.iter(|| {
            let mut gc = RefCountGc::new();
            for i in 0u64..1000 {
                gc.inc_ref(i);
                gc.dec_ref(i);
            }
            black_box(gc.take_pending_removals());
        });
    });
}

// ── AllocStrategy benchmarks ────────────────────────────────────────────

fn bench_alloc_strategies(c: &mut Criterion) {
    let config = CeskConfig {
        control: "f(x)".to_string(),
        env_size: 10,
        store_size: 100,
        stack_depth: 5,
    };

    let mut group = c.benchmark_group("cesk/alloc_strategy");

    group.bench_function("monotonic", |b| {
        let alloc = MonotonicAlloc::new();
        b.iter(|| {
            for i in 0..1000 {
                black_box(alloc.alloc(&format!("v{}", i), &config));
            }
        });
    });

    group.bench_function("0cfa", |b| {
        let alloc = ZeroCfaAlloc;
        b.iter(|| {
            for i in 0..1000 {
                black_box(alloc.alloc(&format!("v{}", i), &config));
            }
        });
    });

    group.bench_function("1cfa", |b| {
        let alloc = OneCfaAlloc;
        b.iter(|| {
            for i in 0..1000 {
                black_box(alloc.alloc(&format!("v{}", i), &config));
            }
        });
    });

    group.finish();
}

// ── Criterion setup ─────────────────────────────────────────────────────

criterion_group!(
    benches,
    bench_local_alloc,
    bench_local_get,
    bench_local_set,
    bench_two_stage_lookup,
    bench_direct_hashmap_lookup,
    bench_refcount_inc_dec,
    bench_refcount_pending_drain,
    bench_alloc_strategies,
);
criterion_main!(benches);
