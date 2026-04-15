//! Benchmarks for green thread infrastructure.
//!
//! Requires `--features green-threads`.

use std::sync::Arc;

use criterion::{criterion_group, criterion_main, Criterion};

use mettail_prattail::channel::{Channel, ChannelId, ChannelMap};
use mettail_prattail::green_thread::{GreenThreadId, GreenThreadRegistry};
use mettail_prattail::scheduler::{Scheduler, SchedulerAutomaton};

/// Benchmark channel send/recv throughput.
fn bench_channel_send_recv(c: &mut Criterion) {
    c.bench_function("channel_send_recv_10k", |b| {
        b.iter(|| {
            let ch: Channel<u64> = Channel::unbounded(ChannelId(0), "bench");
            for i in 0..10_000u64 {
                ch.send(i).expect("send should succeed");
            }
            for _ in 0..10_000 {
                let _ = ch.try_recv().expect("should have data");
            }
        });
    });
}

/// Benchmark forking 1000 green threads.
fn bench_fork_1000_threads(c: &mut Criterion) {
    c.bench_function("fork_1000_threads", |b| {
        b.iter(|| {
            let registry = GreenThreadRegistry::new();
            let parent = registry.spawn("root".to_string());
            for _ in 0..1_000 {
                registry.spawn_child(parent, "child".to_string());
            }
        });
    });
}

/// Benchmark scheduler dispatch of 100 threads.
fn bench_scheduler_dispatch_100(c: &mut Criterion) {
    c.bench_function("scheduler_dispatch_100", |b| {
        b.iter(|| {
            let registry = Arc::new(GreenThreadRegistry::new());
            let channels = Arc::new(ChannelMap::new());
            let mut scheduler = Scheduler::new(Arc::clone(&registry), Arc::clone(&channels));

            for _ in 0..100 {
                let tid = registry.spawn("Expr".to_string());
                scheduler.enqueue(tid, 1);
            }
        });
    });
}

/// Benchmark automaton dispatch with 8 channels.
fn bench_automaton_dispatch_8_channels(c: &mut Criterion) {
    c.bench_function("automaton_dispatch_8ch", |b| {
        let channels: Vec<String> = (0..8).map(|i| format!("ch{}", i)).collect();
        let join_patterns: Vec<(String, Vec<String>)> = vec![
            ("jp1".to_string(), vec!["ch0".to_string(), "ch1".to_string()]),
            ("jp2".to_string(), vec!["ch2".to_string(), "ch3".to_string()]),
            ("jp3".to_string(), vec!["ch4".to_string(), "ch5".to_string(), "ch6".to_string()]),
        ];
        let automaton = SchedulerAutomaton::from_spec(&channels, &join_patterns);

        b.iter(|| {
            // All channels non-empty → all patterns fire
            let result = automaton.dispatch(0xFF);
            assert!(!result.ready_patterns.is_empty());
        });
    });
}

criterion_group!(
    benches,
    bench_channel_send_recv,
    bench_fork_1000_threads,
    bench_scheduler_dispatch_100,
    bench_automaton_dispatch_8_channels,
);
criterion_main!(benches);
