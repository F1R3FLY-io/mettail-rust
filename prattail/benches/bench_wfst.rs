//! WFST benchmark suite: measures time and space for WFST-augmented pipeline
//! components vs the non-WFST baseline.
//!
//! # Feature gates
//!
//! - **`wfst`**: Groups A-D and F (construction, prediction, recovery, lattice, space)
//! - **`wfst-log`**: Group E (log-semiring algorithms: forward-backward, log-push, N-best)
//!
//! # Running
//!
//! ```sh
//! # Groups A-D, F only:
//! cargo bench -p mettail-prattail --bench bench_wfst --features wfst
//!
//! # All groups A-F:
//! cargo bench -p mettail-prattail --bench bench_wfst --features wfst-log
//! ```

mod bench_specs;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, BenchmarkId, Criterion,
};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use mettail_prattail::automata::semiring::TropicalWeight;
use mettail_prattail::lattice::{viterbi_best_path, viterbi_best_path_beam};
use mettail_prattail::prediction::DispatchAction;
use mettail_prattail::recovery::{viterbi_recovery_beam, RecoveryContext, RecoveryWfst};
use mettail_prattail::token_id::TokenIdMap;
use mettail_prattail::wfst::{PredictionWfst, PredictionWfstBuilder};

#[cfg(feature = "wfst-log")]
use mettail_prattail::automata::semiring::LogWeight;
#[cfg(feature = "wfst-log")]
use mettail_prattail::forward_backward::{backward_scores, forward_scores};
#[cfg(feature = "wfst-log")]
use mettail_prattail::lattice::n_best_paths;
#[cfg(feature = "wfst-log")]
use mettail_prattail::log_push::log_push_weights;

use bench_specs::{
    build_sample_token_ids, build_synthetic_lattice, complex_spec, medium_spec, minimal_spec,
    prepare_wfst, small_spec,
};

#[cfg(feature = "wfst-log")]
use bench_specs::{build_synthetic_dag, log_weight_fn, tropical_weight_fn};

use mettail_prattail::generate_parser;

// ══════════════════════════════════════════════════════════════════════════════
// Counting allocator for space measurement
// ══════════════════════════════════════════════════════════════════════════════

struct CountingAllocator;

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            let current = ALLOCATED.fetch_add(layout.size(), Ordering::Relaxed) + layout.size();
            PEAK.fetch_max(current, Ordering::Relaxed);
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        ALLOCATED.fetch_sub(layout.size(), Ordering::Relaxed);
        unsafe { System.dealloc(ptr, layout) };
    }
}

#[global_allocator]
static GLOBAL: CountingAllocator = CountingAllocator;

fn reset_peak() {
    PEAK.store(ALLOCATED.load(Ordering::Relaxed), Ordering::Relaxed);
}

fn peak_bytes() -> usize {
    PEAK.load(Ordering::Relaxed)
}

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

fn configure_group(group: &mut BenchmarkGroup<WallTime>) {
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);
}

/// Named specs for parameterized benchmarks.
fn named_specs() -> Vec<(&'static str, mettail_prattail::LanguageSpec)> {
    vec![
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ]
}

// ══════════════════════════════════════════════════════════════════════════════
// Group A: WFST Construction
// ══════════════════════════════════════════════════════════════════════════════

fn bench_construction(c: &mut Criterion) {
    let specs = named_specs();

    // A1: TokenIdMap construction
    {
        let mut group = c.benchmark_group("wfst/construction/token_id_map");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);
            // Collect token names to reconstruct
            let token_names: Vec<String> = prepared.token_id_map.iter().map(|(n, _)| n.to_string()).collect();

            group.bench_with_input(BenchmarkId::from_parameter(name), &token_names, |b, names| {
                b.iter(|| TokenIdMap::from_names(names.iter().cloned()));
            });
        }
        group.finish();
    }

    // A2: PredictionWfst construction
    {
        let mut group = c.benchmark_group("wfst/construction/prediction_wfst");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);

            // For each category, benchmark building the WFST
            // Use the first (primary) category for consistent comparison
            let primary_cat = &prepared.base.categories[0];
            let dt = match prepared.base.dispatch_tables.get(primary_cat) {
                Some(dt) => dt,
                None => continue,
            };
            let token_id_map = prepared.token_id_map.clone();
            let entries: Vec<(String, DispatchAction, TropicalWeight)> = dt
                .entries
                .iter()
                .enumerate()
                .map(|(i, (tok, action))| {
                    (tok.clone(), action.clone(), TropicalWeight::from_priority(i as u8))
                })
                .collect();
            let default = dt.default_action.clone();
            let default_weight = TropicalWeight::from_priority(entries.len() as u8);
            let cat = primary_cat.clone();

            group.bench_with_input(
                BenchmarkId::from_parameter(name),
                &(cat.clone(), entries.clone(), default.clone()),
                |b, (cat, entries, default)| {
                    b.iter(|| {
                        let mut builder = PredictionWfstBuilder::new(cat, token_id_map.clone());
                        for (tok, action, weight) in entries {
                            builder.add_action(tok, action.clone(), *weight);
                        }
                        if let Some(ref default_action) = default {
                            builder.add_action("Ident", default_action.clone(), default_weight);
                        }
                        builder.build()
                    });
                },
            );
        }
        group.finish();
    }

    // A3: RecoveryWfst construction
    {
        let mut group = c.benchmark_group("wfst/construction/recovery_wfst");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);
            let primary_cat = prepared.base.categories[0].clone();
            let token_id_map = prepared.token_id_map.clone();

            // Collect sync token names
            let sync_names: Vec<String> = prepared
                .sample_token_names
                .iter()
                .chain(std::iter::once(&"Eof".to_string()))
                .cloned()
                .collect();

            group.bench_with_input(
                BenchmarkId::from_parameter(name),
                &(primary_cat.clone(), sync_names.clone()),
                |b, (cat, sync)| {
                    b.iter(|| RecoveryWfst::new(cat.clone(), sync, &token_id_map));
                },
            );
        }
        group.finish();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Group B: Prediction
// ══════════════════════════════════════════════════════════════════════════════

fn bench_prediction(c: &mut Criterion) {
    let specs = named_specs();

    // B1: predict() — unpruned
    {
        let mut group = c.benchmark_group("wfst/prediction/predict");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);
            let primary_cat = &prepared.base.categories[0];
            let wfst: &PredictionWfst = match prepared.prediction_wfsts.get(primary_cat) {
                Some(w) => w,
                None => continue,
            };
            let sample_tokens = prepared.sample_token_names.clone();
            let wfst_owned = wfst.clone();

            group.bench_with_input(
                BenchmarkId::from_parameter(name),
                &(wfst_owned, sample_tokens),
                |b, (wfst, tokens)| {
                    b.iter(|| {
                        for token_name in tokens {
                            let _ = wfst.predict(token_name);
                        }
                    });
                },
            );
        }
        group.finish();
    }

    // B2: predict_pruned() — with beam width
    {
        let mut group = c.benchmark_group("wfst/prediction/predict_pruned");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);
            let primary_cat = &prepared.base.categories[0];
            let wfst: PredictionWfst = match prepared.prediction_wfsts.get(primary_cat) {
                Some(w) => w.clone(),
                None => continue,
            };
            let mut wfst_beam = wfst;
            wfst_beam.set_beam_width(Some(TropicalWeight::new(1.5)));
            let sample_tokens = prepared.sample_token_names.clone();

            group.bench_with_input(
                BenchmarkId::from_parameter(name),
                &(wfst_beam, sample_tokens),
                |b, (wfst, tokens)| {
                    b.iter(|| {
                        for token_name in tokens {
                            let _ = wfst.predict_pruned(token_name);
                        }
                    });
                },
            );
        }
        group.finish();
    }

    // B3: Prediction scaling — varying token vocabulary sizes
    {
        let mut group = c.benchmark_group("wfst/prediction/predict_scaling");
        configure_group(&mut group);

        for n_ops in [5, 10, 20, 50, 100] {
            let spec = bench_specs::synthetic_spec(n_ops);
            let prepared = prepare_wfst(&spec);
            let primary_cat = &prepared.base.categories[0];
            let wfst: &PredictionWfst = match prepared.prediction_wfsts.get(primary_cat) {
                Some(w) => w,
                None => continue,
            };
            let sample_tokens = prepared.sample_token_names.clone();
            let wfst_owned = wfst.clone();

            group.bench_with_input(
                BenchmarkId::from_parameter(n_ops),
                &(wfst_owned, sample_tokens),
                |b, (wfst, tokens)| {
                    b.iter(|| {
                        for token_name in tokens {
                            let _ = wfst.predict(token_name);
                        }
                    });
                },
            );
        }
        group.finish();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Group C: Recovery
// ══════════════════════════════════════════════════════════════════════════════

fn bench_recovery(c: &mut Criterion) {
    let specs = named_specs();

    // C1: find_best_recovery
    {
        let mut group = c.benchmark_group("wfst/recovery/find_recovery");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);
            if prepared.recovery_wfsts.is_empty() {
                continue;
            }
            let recovery = &prepared.recovery_wfsts[0];
            let token_ids = build_sample_token_ids(&prepared.token_id_map, 20);

            group.bench_with_input(
                BenchmarkId::from_parameter(name),
                &(recovery.clone(), token_ids.clone()),
                |b, (rec, ids)| {
                    b.iter(|| {
                        let _ = rec.find_best_recovery(ids, 3);
                    });
                },
            );
        }
        group.finish();
    }

    // C2: find_best_recovery_contextual
    {
        let mut group = c.benchmark_group("wfst/recovery/find_recovery_contextual");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);
            if prepared.recovery_wfsts.is_empty() {
                continue;
            }
            let recovery = &prepared.recovery_wfsts[0];
            let token_ids = build_sample_token_ids(&prepared.token_id_map, 20);
            let ctx = RecoveryContext::default();
            let cat = prepared.base.categories[0].clone();

            group.bench_with_input(
                BenchmarkId::from_parameter(name),
                &(recovery.clone(), token_ids.clone()),
                |b, (rec, ids)| {
                    b.iter(|| {
                        let _ = rec.find_best_recovery_contextual(ids, 3, &ctx, None, &cat);
                    });
                },
            );
        }
        group.finish();
    }

    // C3: viterbi_recovery_beam (standalone, not on RecoveryWfst)
    {
        let mut group = c.benchmark_group("wfst/recovery/recovery_beam");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);
            if prepared.recovery_wfsts.is_empty() {
                continue;
            }
            let sync_tokens = prepared.recovery_wfsts[0].sync_tokens().clone();
            let token_ids = build_sample_token_ids(&prepared.token_id_map, 20);
            let beam = Some(TropicalWeight::new(2.0));

            group.bench_with_input(
                BenchmarkId::from_parameter(name),
                &token_ids,
                |b, ids| {
                    b.iter(|| {
                        let _ = viterbi_recovery_beam(ids, 3, &sync_tokens, beam);
                    });
                },
            );
        }
        group.finish();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Group D: Lattice
// ══════════════════════════════════════════════════════════════════════════════

fn bench_lattice(c: &mut Criterion) {
    let lattice_sizes = [10, 50, 100, 500];
    let edges_per_node = 3;

    // D1: Viterbi best path
    {
        let mut group = c.benchmark_group("wfst/lattice/viterbi");
        configure_group(&mut group);

        for &n_nodes in &lattice_sizes {
            let (lattice, final_node) = build_synthetic_lattice(n_nodes, edges_per_node);

            group.bench_with_input(
                BenchmarkId::from_parameter(n_nodes),
                &(lattice, final_node),
                |b, (lat, fin)| {
                    b.iter(|| viterbi_best_path(lat, *fin));
                },
            );
        }
        group.finish();
    }

    // D2: Viterbi best path with beam
    {
        let mut group = c.benchmark_group("wfst/lattice/viterbi_beam");
        configure_group(&mut group);

        for &n_nodes in &lattice_sizes {
            let (lattice, final_node) = build_synthetic_lattice(n_nodes, edges_per_node);
            let beam = Some(TropicalWeight::new(2.0));

            group.bench_with_input(
                BenchmarkId::from_parameter(n_nodes),
                &(lattice, final_node),
                |b, (lat, fin)| {
                    b.iter(|| viterbi_best_path_beam(lat, *fin, beam));
                },
            );
        }
        group.finish();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Group E: Log-Semiring Algorithms (wfst-log only)
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "wfst-log")]
fn bench_log_semiring(c: &mut Criterion) {
    let dag_sizes = [10, 50, 100, 500];
    let edges_per_node = 3;

    // E1: forward_scores with LogWeight
    {
        let mut group = c.benchmark_group("wfst/log_semiring/forward_scores");
        configure_group(&mut group);

        for &n in &dag_sizes {
            let dag = build_synthetic_dag(n, edges_per_node, log_weight_fn);

            group.bench_with_input(BenchmarkId::from_parameter(n), &dag, |b, dag| {
                b.iter(|| forward_scores::<LogWeight>(dag, n));
            });
        }
        group.finish();
    }

    // E2: backward_scores with LogWeight
    {
        let mut group = c.benchmark_group("wfst/log_semiring/backward_scores");
        configure_group(&mut group);

        for &n in &dag_sizes {
            let dag = build_synthetic_dag(n, edges_per_node, log_weight_fn);
            let final_node = n - 1;

            group.bench_with_input(BenchmarkId::from_parameter(n), &dag, |b, dag| {
                b.iter(|| backward_scores::<LogWeight>(dag, n, final_node));
            });
        }
        group.finish();
    }

    // E3: log_push_weights
    {
        let mut group = c.benchmark_group("wfst/log_semiring/log_push");
        configure_group(&mut group);

        for &n in &dag_sizes {
            let dag = build_synthetic_dag(n, edges_per_node, log_weight_fn);
            let final_node = n - 1;

            group.bench_with_input(BenchmarkId::from_parameter(n), &dag, |b, dag_orig| {
                b.iter(|| {
                    let mut dag = dag_orig.clone();
                    log_push_weights(&mut dag, n, final_node);
                });
            });
        }
        group.finish();
    }

    // E4: n_best_paths
    {
        let mut group = c.benchmark_group("wfst/log_semiring/n_best");
        configure_group(&mut group);

        for &n_nodes in &dag_sizes {
            let (lattice, final_node) = build_synthetic_lattice(n_nodes, edges_per_node);

            group.bench_with_input(
                BenchmarkId::from_parameter(n_nodes),
                &(lattice, final_node),
                |b, (lat, fin)| {
                    b.iter(|| n_best_paths(lat, *fin, 5));
                },
            );
        }
        group.finish();
    }

    // E5: Forward with Tropical vs Log comparison
    {
        let mut group = c.benchmark_group("wfst/log_semiring/forward_tropical_vs_log");
        configure_group(&mut group);

        for &n in &[50usize, 100, 500] {
            // Tropical
            let dag_trop = build_synthetic_dag(n, edges_per_node, tropical_weight_fn);
            group.bench_with_input(
                BenchmarkId::new("tropical", n),
                &dag_trop,
                |b, dag| {
                    b.iter(|| forward_scores::<TropicalWeight>(dag, n));
                },
            );

            // Log
            let dag_log = build_synthetic_dag(n, edges_per_node, log_weight_fn);
            group.bench_with_input(
                BenchmarkId::new("log", n),
                &dag_log,
                |b, dag| {
                    b.iter(|| forward_scores::<LogWeight>(dag, n));
                },
            );
        }
        group.finish();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Group F: Space Measurement
// ══════════════════════════════════════════════════════════════════════════════

fn bench_space(c: &mut Criterion) {
    let specs = named_specs();

    // F1: PredictionWfst heap size
    {
        let mut group = c.benchmark_group("wfst/space/prediction_wfst");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);
            let primary_cat = &prepared.base.categories[0];
            let dt = match prepared.base.dispatch_tables.get(primary_cat) {
                Some(dt) => dt,
                None => continue,
            };
            let token_id_map = prepared.token_id_map.clone();
            let entries: Vec<(String, DispatchAction, TropicalWeight)> = dt
                .entries
                .iter()
                .enumerate()
                .map(|(i, (tok, action))| {
                    (tok.clone(), action.clone(), TropicalWeight::from_priority(i as u8))
                })
                .collect();
            let default = dt.default_action.clone();
            let default_weight = TropicalWeight::from_priority(entries.len() as u8);
            let cat = primary_cat.clone();

            group.bench_function(BenchmarkId::from_parameter(name), |b| {
                b.iter_custom(|iters| {
                    let mut total_bytes = 0u64;
                    for _ in 0..iters {
                        reset_peak();
                        let mut builder = PredictionWfstBuilder::new(&cat, token_id_map.clone());
                        for (tok, action, weight) in &entries {
                            builder.add_action(tok, action.clone(), *weight);
                        }
                        if let Some(ref default_action) = default {
                            builder.add_action("Ident", default_action.clone(), default_weight);
                        }
                        let _wfst = builder.build();
                        total_bytes += peak_bytes() as u64;
                    }
                    // Return as Duration — criterion will divide by iters
                    // We use nanos = bytes to encode the measurement
                    Duration::from_nanos(total_bytes / iters)
                });
            });
        }
        group.finish();
    }

    // F2: RecoveryWfst heap size
    {
        let mut group = c.benchmark_group("wfst/space/recovery_wfst");
        configure_group(&mut group);

        for (name, spec) in &specs {
            let prepared = prepare_wfst(spec);
            let primary_cat = prepared.base.categories[0].clone();
            let token_id_map = prepared.token_id_map.clone();
            let sync_names: Vec<String> = prepared
                .sample_token_names
                .iter()
                .chain(std::iter::once(&"Eof".to_string()))
                .cloned()
                .collect();

            group.bench_function(BenchmarkId::from_parameter(name), |b| {
                b.iter_custom(|iters| {
                    let mut total_bytes = 0u64;
                    for _ in 0..iters {
                        reset_peak();
                        let _rec = RecoveryWfst::new(primary_cat.clone(), &sync_names, &token_id_map);
                        total_bytes += peak_bytes() as u64;
                    }
                    Duration::from_nanos(total_bytes / iters)
                });
            });
        }
        group.finish();
    }

    // F3: TokenLattice heap size (scaling)
    {
        let mut group = c.benchmark_group("wfst/space/lattice");
        configure_group(&mut group);

        for &n_nodes in &[10usize, 50, 100, 500] {
            group.bench_function(BenchmarkId::from_parameter(n_nodes), |b| {
                b.iter_custom(|iters| {
                    let mut total_bytes = 0u64;
                    for _ in 0..iters {
                        reset_peak();
                        let (_lattice, _final_node) = build_synthetic_lattice(n_nodes, 3);
                        total_bytes += peak_bytes() as u64;
                    }
                    Duration::from_nanos(total_bytes / iters)
                });
            });
        }
        group.finish();
    }

    // F4: Baseline pipeline heap size (non-WFST generate_parser)
    {
        let mut group = c.benchmark_group("wfst/space/baseline_pipeline");
        configure_group(&mut group);

        for (name, spec) in &specs {
            group.bench_function(BenchmarkId::from_parameter(name), |b| {
                b.iter_custom(|iters| {
                    let mut total_bytes = 0u64;
                    for _ in 0..iters {
                        reset_peak();
                        let _output = generate_parser(spec);
                        total_bytes += peak_bytes() as u64;
                    }
                    Duration::from_nanos(total_bytes / iters)
                });
            });
        }
        group.finish();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Criterion entry point
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(not(feature = "wfst-log"))]
criterion_group!(
    benches,
    bench_construction,
    bench_prediction,
    bench_recovery,
    bench_lattice,
    bench_space,
);

#[cfg(feature = "wfst-log")]
criterion_group!(
    benches,
    bench_construction,
    bench_prediction,
    bench_recovery,
    bench_lattice,
    bench_log_semiring,
    bench_space,
);

criterion_main!(benches);
