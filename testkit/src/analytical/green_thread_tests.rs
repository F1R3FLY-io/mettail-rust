//! Green thread scheduling analysis for generated language tests.
//!
//! Wraps `mettail_prattail::green_thread` and provides a higher-level
//! interface that works with `LanguageMetadata`. Exercises the green thread
//! infrastructure by spawning threads for each term constructor category,
//! verifying scheduling determinism (same inputs produce same scheduling
//! order), and checking fork/join patterns.
//!
//! The green thread system models Rholang's concurrent process evaluation
//! where parallel compositions `P | Q` create independent green threads
//! sharing the parent environment via structural sharing.

use mettail_prattail::channel::GreenThreadId;
use mettail_prattail::green_thread::{GreenThreadRegistry, QuantumResult};
use mettail_runtime::LanguageMetadata;

/// Result of green thread scheduling analysis on a language.
#[derive(Debug)]
pub struct GreenThreadResult {
    /// Whether scheduling is deterministic (same inputs produce same order).
    pub is_deterministic: bool,
    /// Number of threads spawned during analysis.
    pub threads_spawned: usize,
    /// Number of threads that completed successfully.
    pub threads_completed: usize,
    /// Number of threads that yielded (quantum exhausted).
    pub threads_yielded: usize,
    /// Number of fork events observed.
    pub fork_count: usize,
    /// Maximum concurrent thread count observed.
    pub max_concurrent: usize,
    /// Human-readable summary.
    pub summary: String,
}

/// Check green thread scheduling properties for a language.
///
/// Exercises the green thread infrastructure by:
/// 1. Spawning a thread for each category (type) in the language.
/// 2. Running each thread for a small quantum to observe scheduling behavior.
/// 3. Repeating the exercise to verify determinism.
/// 4. For types with multiple constructors, testing fork/join by spawning
///    child threads.
///
/// # Arguments
/// * `metadata` -- static language metadata providing type and term definitions
///
/// # Returns
/// A `GreenThreadResult` summarizing scheduling behavior.
pub fn check_green_thread_scheduling(metadata: &dyn LanguageMetadata) -> GreenThreadResult {
    let types = metadata.types();
    let terms = metadata.terms();

    if types.is_empty() {
        return GreenThreadResult {
            is_deterministic: true,
            threads_spawned: 0,
            threads_completed: 0,
            threads_yielded: 0,
            fork_count: 0,
            max_concurrent: 0,
            summary: format!(
                "{}: no types defined, green thread analysis trivially empty",
                metadata.name()
            ),
        };
    }

    // Run the scheduling exercise twice to check determinism.
    let run1 = run_scheduling_exercise(metadata, types, terms);
    let run2 = run_scheduling_exercise(metadata, types, terms);

    // Determinism: both runs should produce the same completion order.
    let is_deterministic = run1.completion_order == run2.completion_order;

    GreenThreadResult {
        is_deterministic,
        threads_spawned: run1.threads_spawned,
        threads_completed: run1.threads_completed,
        threads_yielded: run1.threads_yielded,
        fork_count: run1.fork_count,
        max_concurrent: run1.max_concurrent,
        summary: format!(
            "{}: green threads (spawned: {}, completed: {}, yielded: {}, forks: {}, \
             max_concurrent: {}, deterministic: {})",
            metadata.name(),
            run1.threads_spawned,
            run1.threads_completed,
            run1.threads_yielded,
            run1.fork_count,
            run1.max_concurrent,
            is_deterministic,
        ),
    }
}

/// Internal tracking for a single scheduling exercise run.
struct SchedulingRun {
    threads_spawned: usize,
    threads_completed: usize,
    threads_yielded: usize,
    fork_count: usize,
    max_concurrent: usize,
    completion_order: Vec<String>,
}

/// Run one scheduling exercise: spawn threads, run quanta, collect results.
fn run_scheduling_exercise(
    _metadata: &dyn LanguageMetadata,
    types: &[mettail_runtime::TypeDef],
    terms: &[mettail_runtime::TermDef],
) -> SchedulingRun {
    let registry = GreenThreadRegistry::new();

    let mut threads_spawned = 0;
    let mut threads_completed = 0;
    let mut threads_yielded = 0;
    let mut fork_count = 0;
    let mut completion_order = Vec::new();

    // Spawn one thread per category (type).
    let mut thread_ids: Vec<GreenThreadId> = Vec::with_capacity(types.len());
    for ty in types {
        let id = registry.spawn(ty.name.to_string());
        thread_ids.push(id);
        threads_spawned += 1;
    }

    let max_concurrent = thread_ids.len();

    // For each type with multiple constructors, test fork/join by spawning
    // child threads from the parent.
    for ty in types {
        let constructors: Vec<&mettail_runtime::TermDef> =
            terms.iter().filter(|t| t.type_name == ty.name).collect();

        if constructors.len() >= 2 {
            // Find the parent thread for this type.
            if let Some(&parent_id) = thread_ids.iter().find(|id| {
                registry
                    .get(**id)
                    .map(|t| t.category == ty.name)
                    .unwrap_or(false)
            }) {
                // Fork child threads for each constructor.
                for ctor in &constructors[1..] {
                    if let Some(child_id) = registry.spawn_child(parent_id, ctor.name.to_string()) {
                        thread_ids.push(child_id);
                        threads_spawned += 1;
                        fork_count += 1;
                    }
                }
            }
        }
    }

    // Run each thread for a small quantum (10 steps).
    // Since these threads have no CEK control term, they will
    // either complete immediately or yield.
    for &id in &thread_ids {
        let mut thread_ref = match registry.get_mut(id) {
            Some(r) => r,
            None => continue,
        };

        // Transition to Running state before running quantum.
        if thread_ref.is_runnable() {
            thread_ref.state = mettail_prattail::green_thread::CekThreadState::Running;

            let result = thread_ref.run_quantum(10);
            match result {
                QuantumResult::Completed { result } => {
                    threads_completed += 1;
                    completion_order.push(format!("{}:{}", id, result));
                },
                QuantumResult::Yielded => {
                    threads_yielded += 1;
                },
                QuantumResult::Suspended { .. } => {
                    // Thread is blocked, count as yielded for analysis.
                    threads_yielded += 1;
                },
                QuantumResult::Forked { children } => {
                    fork_count += children.len();
                    threads_completed += 1;
                    completion_order.push(format!("{}:forked({})", id, children.len()));
                },
                QuantumResult::Failed { error } => {
                    threads_completed += 1;
                    completion_order.push(format!("{}:failed({})", id, error));
                },
            }
        }
    }

    SchedulingRun {
        threads_spawned,
        threads_completed,
        threads_yielded,
        fork_count,
        max_concurrent,
        completion_order,
    }
}
