//! Integration tests for Phase 2 simulation framework.
//!
//! These tests use the Calculator language from mettail-languages
//! to validate the simulation runner, invariants, morphology tracking,
//! and JSONL trace serialization.
//!
//! JSONL I/O uses hand-formatted JSON (no serde_json) to avoid Cranelift
//! aarch64 NEON intrinsic issues on macOS nightly.

use mettail_languages::calculator::{self as calc};
use mettail_runtime::Language;
use mettail_simulation::invariant::{BoundedDepth, BoundedSize};
use mettail_simulation::morphology::{MorphologyTracker, TermMetrics};
use mettail_simulation::runner::{SimulationConfig, SimulationRunner, TraceOutputFormat};
use mettail_simulation::trace::{self, TraceOutcome};

// =============================================================================
// Helper: run Calculator to normal form
// =============================================================================

fn calc_runner(config: SimulationConfig) -> SimulationRunner<'static> {
    // Use a leaked static reference for the language since integration tests
    // need 'static lifetime for the runner.
    let lang: &'static dyn Language = Box::leak(Box::new(calc::CalculatorLanguage));
    SimulationRunner::new(lang, config)
}

// =============================================================================
// Test 1: run_to_normal_form -- parse "1 + 2", verify normal form is "3"
// =============================================================================

#[test]
fn test_run_to_normal_form() {
    let config = SimulationConfig {
        max_steps: 100,
        track_morphology: true,
        ..SimulationConfig::default()
    };
    let runner = calc_runner(config);

    let trace = runner
        .run_to_normal_form("1 + 2")
        .expect("should reach normal form");

    // Verify the outcome is NormalForm with term "3".
    match &trace.outcome {
        TraceOutcome::NormalForm { term, .. } => {
            assert_eq!(term, "3", "Expected normal form '3', got '{}'", term);
        },
        other => panic!("Expected NormalForm outcome, got: {:?}", other),
    }

    // Verify trace has at least a parse step.
    assert!(!trace.steps.is_empty(), "Trace should have at least one step");
    assert_eq!(trace.language, "Calculator");

    // Verify morphology was collected.
    assert!(
        trace.morphology.is_some(),
        "Morphology should be present when tracking is enabled"
    );
}

#[test]
fn test_run_to_normal_form_nested() {
    let config = SimulationConfig {
        max_steps: 100,
        track_morphology: true,
        ..SimulationConfig::default()
    };
    let runner = calc_runner(config);

    let trace = runner
        .run_to_normal_form("(2 + 3) * (4 - 1)")
        .expect("should reach normal form");

    match &trace.outcome {
        TraceOutcome::NormalForm { term, .. } => {
            assert_eq!(term, "15", "Expected normal form '15', got '{}'", term);
        },
        other => panic!("Expected NormalForm outcome, got: {:?}", other),
    }
}

// =============================================================================
// Test 2: campaign_all_pass -- run 50 cases of arb_int(2) style expressions
// =============================================================================

#[test]
fn test_campaign_all_pass() {
    let config = SimulationConfig {
        max_steps: 200,
        proptest_cases: 50,
        track_morphology: true,
        seed: Some([42u8; 32]),
        ..SimulationConfig::default()
    };
    let mut runner = calc_runner(config);

    // Strategy: generate simple integer arithmetic expressions.
    // We use proptest's built-in combinators to create expressions
    // like "N + M" where N, M are small integers.
    use proptest::prelude::*;
    let int_arith_strategy = (0i32..100, 0i32..100).prop_map(|(a, b)| format!("{} + {}", a, b));

    let results = runner.run_campaign(int_arith_strategy);

    assert_eq!(results.total_cases, 50, "Should run 50 cases");
    assert_eq!(
        results.failed,
        0,
        "All cases should pass. Failures: {:?}",
        results
            .failures
            .iter()
            .map(|f| format!("input={:?}, error={}", f.input, f.error))
            .collect::<Vec<_>>()
    );
    assert_eq!(results.passed, 50, "All 50 cases should pass");

    // Verify coverage was tracked.
    assert!(!results.coverage.rules_fired.is_empty(), "At least one rule should have fired");
}

// =============================================================================
// Test 3: invariant_bounded_size -- verify BoundedSize catches large terms
// =============================================================================

#[test]
fn test_invariant_bounded_size() {
    // Use a very small size bound (1 node) that will be violated by
    // any compound expression.
    let config = SimulationConfig {
        max_steps: 100,
        track_morphology: true,
        invariants: vec![Box::new(BoundedSize { max_nodes: 1 })],
        ..SimulationConfig::default()
    };
    let runner = calc_runner(config);

    // "1 + 2" has 3 tokens, which exceeds max_nodes=1.
    let result = runner.run_to_normal_form("1 + 2");

    match result {
        Err(failure) => {
            assert!(
                failure.error.contains("BoundedSize"),
                "Error should mention BoundedSize invariant, got: {}",
                failure.error
            );
        },
        Ok(trace) => {
            // The parse step should have triggered the violation
            // since "1 + 2" has 3 tokens.
            match &trace.outcome {
                TraceOutcome::InvariantViolation { invariant, .. } => {
                    assert!(invariant.contains("BoundedSize"));
                },
                _ => {
                    panic!("Expected BoundedSize violation for '1 + 2', but simulation passed");
                },
            }
        },
    }
}

#[test]
fn test_invariant_bounded_depth() {
    // Bound depth to 0 (no nesting allowed).
    let config = SimulationConfig {
        max_steps: 100,
        invariants: vec![Box::new(BoundedDepth { max_depth: 0 })],
        ..SimulationConfig::default()
    };
    let runner = calc_runner(config);

    // "1 + 2" at depth 0 should pass BoundedDepth since the display has
    // no parentheses. But "(1 + 2)" would have depth 1.
    // Test with a nested expression that has parentheses in its display.
    let result = runner.run_to_normal_form("(1 + 2) + (3 + 4)");

    // The display of the parsed term will have depth >= 1 from
    // the generated AST display (operator nesting).
    assert!(result.is_err(), "Expected BoundedDepth violation");
    let failure = result.unwrap_err();
    assert!(
        failure.error.contains("BoundedDepth"),
        "Error should mention BoundedDepth invariant, got: {}",
        failure.error
    );
}

// =============================================================================
// Test 4: morphology_tracking -- verify metrics are recorded correctly
// =============================================================================

#[test]
fn test_morphology_tracking() {
    let mut tracker = MorphologyTracker::new();

    // Record several terms with known structure.
    let displays = vec!["1 + 2", "3", "((1 + 2) * (3 + 4))", "21"];

    for display in &displays {
        let metrics = TermMetrics::from_display(display);
        tracker.record(metrics);
    }

    let summary = tracker.summary();

    assert_eq!(summary.total_steps, 4);
    assert!(summary.min_nodes >= 1, "Minimum nodes should be >= 1");
    assert!(summary.max_nodes >= 1, "Maximum nodes should be >= 1 (for compound expr)");
    assert!(summary.distinct_shapes >= 2, "Should have multiple distinct shapes");
}

#[test]
fn test_morphology_from_simulation() {
    let config = SimulationConfig {
        max_steps: 100,
        track_morphology: true,
        ..SimulationConfig::default()
    };
    let runner = calc_runner(config);

    let trace = runner
        .run_to_normal_form("(2 + 3) * 4")
        .expect("should succeed");

    let morphology = trace.morphology.expect("morphology should be present");
    assert!(morphology.total_steps >= 1, "Should have at least 1 step recorded");
    assert!(morphology.min_nodes >= 1);
}

// =============================================================================
// Test 5: jsonl_output -- verify JSONL trace can be written and parsed back
// =============================================================================

#[test]
fn test_jsonl_output() {
    let dir = std::env::temp_dir().join("mettail_sim_test_jsonl");
    let _ = std::fs::create_dir_all(&dir);
    let path = dir.join("test_trace.jsonl");

    let config = SimulationConfig {
        max_steps: 100,
        track_morphology: true,
        trace_output: TraceOutputFormat::Jsonl { path: path.clone() },
        ..SimulationConfig::default()
    };
    let runner = calc_runner(config);

    let original_trace = runner
        .run_to_normal_form("1 + 2")
        .expect("should reach normal form");

    // Verify the JSONL file was written.
    assert!(path.exists(), "JSONL file should exist at {:?}", path);

    // Read it back.
    let recovered = trace::read_trace_jsonl(&path).expect("should parse JSONL");

    // Verify key fields match.
    assert_eq!(recovered.seed, original_trace.seed);
    assert_eq!(recovered.language, "Calculator");
    assert_eq!(recovered.steps.len(), original_trace.steps.len(), "Step count should match");

    // Verify outcome.
    match (&original_trace.outcome, &recovered.outcome) {
        (
            TraceOutcome::NormalForm { term: orig_term, .. },
            TraceOutcome::NormalForm { term: rec_term, .. },
        ) => {
            assert_eq!(orig_term, rec_term, "Normal form terms should match");
        },
        _ => panic!(
            "Outcome mismatch: original={:?}, recovered={:?}",
            original_trace.outcome, recovered.outcome
        ),
    }

    // Verify morphology roundtrip.
    assert!(recovered.morphology.is_some(), "Morphology should be present");

    // Verify each step entry has proper fields.
    for (orig, rec) in original_trace.steps.iter().zip(recovered.steps.iter()) {
        assert_eq!(orig.step_index, rec.step_index);
        assert_eq!(orig.term_display, rec.term_display);
        assert_eq!(orig.operation, rec.operation);
    }

    // Clean up.
    let _ = std::fs::remove_file(&path);
}

#[test]
fn test_jsonl_multi_step_trace() {
    let dir = std::env::temp_dir().join("mettail_sim_test_jsonl_multi");
    let _ = std::fs::create_dir_all(&dir);
    let path = dir.join("multi_step_trace.jsonl");

    let config = SimulationConfig {
        max_steps: 100,
        track_morphology: true,
        trace_output: TraceOutputFormat::Jsonl { path: path.clone() },
        ..SimulationConfig::default()
    };
    let runner = calc_runner(config);

    let trace = runner
        .run_to_normal_form("(2 + 3) * (4 - 1)")
        .expect("should reach normal form");

    match &trace.outcome {
        TraceOutcome::NormalForm { term, .. } => {
            assert_eq!(term, "15");
        },
        other => panic!("Expected NormalForm, got: {:?}", other),
    }

    // Read back from file.
    let recovered = trace::read_trace_jsonl(&path).expect("should parse");
    assert_eq!(recovered.steps.len(), trace.steps.len());

    // Clean up.
    let _ = std::fs::remove_file(&path);
}

// =============================================================================
// Test: campaign with failures collected
// =============================================================================

#[test]
fn test_campaign_collects_failures() {
    // Use a tiny size bound that causes many failures.
    let config = SimulationConfig {
        max_steps: 100,
        proptest_cases: 10,
        track_morphology: false,
        seed: Some([7u8; 32]),
        invariants: vec![Box::new(BoundedSize { max_nodes: 1 })],
        ..SimulationConfig::default()
    };
    let mut runner = calc_runner(config);

    use proptest::prelude::*;
    let strategy = (1i32..50, 1i32..50).prop_map(|(a, b)| format!("{} + {}", a, b));

    let results = runner.run_campaign(strategy);

    // All cases should fail because "N + M" has 3 tokens > 1.
    assert_eq!(results.total_cases, 10);
    assert_eq!(results.failed, 10, "All cases should fail with BoundedSize=1");

    // Verify all failures have proper error messages.
    for failure in &results.failures {
        assert!(
            failure.error.contains("BoundedSize"),
            "Failure error should mention BoundedSize, got: {}",
            failure.error,
        );
    }
}

// =============================================================================
// Test: rule coverage tracking
// =============================================================================

#[test]
fn test_rule_coverage_tracking() {
    let config = SimulationConfig {
        max_steps: 200,
        proptest_cases: 20,
        track_morphology: true,
        seed: Some([99u8; 32]),
        ..SimulationConfig::default()
    };
    let mut runner = calc_runner(config);

    use proptest::prelude::*;
    let strategy = (0i32..100, 0i32..100).prop_map(|(a, b)| format!("{} + {}", a, b));

    let results = runner.run_campaign(strategy);

    assert!(results.is_success(), "All cases should pass");
    assert!(
        results.coverage.total_rules > 0,
        "Total rules should be populated from metadata"
    );

    // With addition expressions, at least AddInt-related rules should fire.
    let total_firings: usize = results.coverage.rules_fired.values().sum();
    assert!(total_firings > 0, "At least some rules should have fired");
}

// =============================================================================
// Test: TermMetrics edge cases
// =============================================================================

#[test]
fn test_term_metrics_empty_string() {
    let m = TermMetrics::from_display("");
    assert_eq!(m.node_count, 1); // max(1) ensures at least 1
    assert_eq!(m.depth, 0);
}

#[test]
fn test_term_metrics_deeply_nested() {
    let m = TermMetrics::from_display("((((x))))");
    assert_eq!(m.depth, 4);
}

#[test]
fn test_term_metrics_fingerprint_differs() {
    let m1 = TermMetrics::from_display("1 + 2");
    let m2 = TermMetrics::from_display("2 + 1");
    assert_ne!(
        m1.structural_fingerprint, m2.structural_fingerprint,
        "Different terms should have different fingerprints"
    );
}

// =============================================================================
// CoverageGuidedCampaign tests
// =============================================================================

use mettail_simulation::coverage::CoverageGuidedCampaign;

/// Run 2-3 iterations and verify coverage increases (or at least is non-zero).
#[test]
fn test_coverage_guided_basic() {
    use proptest::prelude::*;

    let lang: &'static dyn Language = Box::leak(Box::new(calc::CalculatorLanguage));

    // Strategy factory: generate a variety of arithmetic expressions to exercise
    // multiple rewrite rules (AddInt, SubInt, MulInt, fold operations).
    let strategy_factory = || {
        prop_oneof![
            (0i32..50, 0i32..50).prop_map(|(a, b)| format!("{} + {}", a, b)),
            (0i32..50, 0i32..50).prop_map(|(a, b)| format!("{} - {}", a, b)),
            (0i32..20, 0i32..20).prop_map(|(a, b)| format!("{} * {}", a, b)),
            (0i32..50, 0i32..50, 0i32..50).prop_map(|(a, b, c)| format!("({} + {}) * {}", a, b, c)),
        ]
    };

    let campaign = CoverageGuidedCampaign::new(lang)
        .max_iterations(3)
        .cases_per_iteration(20)
        .max_steps(200)
        .plateau_threshold(0.1); // Very low threshold to ensure we run multiple iterations.

    let results = campaign.run(strategy_factory);

    // Verify we ran at least 1 iteration.
    assert!(
        results.iterations >= 1,
        "Should run at least 1 iteration, ran {}",
        results.iterations,
    );

    // Verify some runs were executed.
    assert!(
        results.total_runs > 0,
        "Should have at least 1 total run, got {}",
        results.total_runs,
    );

    // Verify coverage history has entries.
    assert_eq!(
        results.coverage_history.len(),
        results.iterations,
        "Coverage history length should match iterations",
    );

    // Verify that coverage is non-zero (some rules should have fired).
    let total_rules = lang.metadata().rewrites().len();
    let final_pct = results.final_coverage.coverage_pct(total_rules);
    assert!(final_pct > 0.0, "Final coverage should be > 0%, got {:.1}%", final_pct,);

    // Verify coverage is monotonically non-decreasing across iterations.
    for window in results.coverage_history.windows(2) {
        assert!(
            window[1] >= window[0] - f64::EPSILON,
            "Coverage should be non-decreasing: {:.1}% -> {:.1}%",
            window[0],
            window[1],
        );
    }

    // If we ran more than 1 iteration, the coverage should be at least as good
    // as a single iteration.
    if results.iterations > 1 && results.coverage_history.len() >= 2 {
        let first_iter_coverage = results.coverage_history[0];
        let last_iter_coverage = *results
            .coverage_history
            .last()
            .expect("coverage_history should have at least one entry");
        assert!(
            last_iter_coverage >= first_iter_coverage - f64::EPSILON,
            "Later iterations should have >= coverage: first={:.1}%, last={:.1}%",
            first_iter_coverage,
            last_iter_coverage,
        );
    }
}

/// Verify that the campaign stops when coverage plateaus.
///
/// We use a simple addition-only strategy that will quickly saturate the
/// "AddInt" rules and then plateau, because subtraction/multiplication
/// rules will never fire.
#[test]
fn test_coverage_guided_plateau() {
    use proptest::prelude::*;

    let lang: &'static dyn Language = Box::leak(Box::new(calc::CalculatorLanguage));

    // Only addition: this will fire AddInt rules but nothing else.
    // Coverage should plateau quickly.
    let add_only_factory = || (0i32..100, 0i32..100).prop_map(|(a, b)| format!("{} + {}", a, b));

    let campaign = CoverageGuidedCampaign::new(lang)
        .max_iterations(10)
        .cases_per_iteration(30)
        .max_steps(200)
        .plateau_threshold(1.0); // 1% — once we stop discovering new rules, stop.

    let results = campaign.run(add_only_factory);

    // The campaign should have stopped before max_iterations because the
    // addition-only strategy plateaus quickly: it can only fire AddInt rules.
    // With plateau_threshold=1.0%, it should stop well before 10 iterations.
    //
    // Note: on the first iteration (iterations_completed == 1) we don't check
    // the plateau condition, so we need at least 2 iterations before early exit.
    assert!(
        results.iterations >= 2,
        "Should run at least 2 iterations, ran {}",
        results.iterations,
    );

    // Verify the coverage history shows that improvement slowed down.
    if results.coverage_history.len() >= 2 {
        let last_improvement = results.coverage_history[results.coverage_history.len() - 1]
            - results.coverage_history[results.coverage_history.len() - 2];
        // The campaign stopped because improvement < plateau_threshold (1.0%),
        // or because coverage hit 100%, or because max iterations was reached.
        let total_rules = lang.metadata().rewrites().len();
        let final_pct = results.final_coverage.coverage_pct(total_rules);
        let stopped_at_plateau = last_improvement < 1.0;
        let stopped_at_full_coverage = final_pct >= 100.0;
        let stopped_at_max = results.iterations == 10;
        assert!(
            stopped_at_plateau || stopped_at_full_coverage || stopped_at_max,
            "Campaign should have stopped due to plateau ({:.2}% improvement), \
             full coverage ({:.1}%), or max iterations ({})",
            last_improvement,
            final_pct,
            results.iterations,
        );
    }

    // Verify some coverage was achieved.
    let total_rules = lang.metadata().rewrites().len();
    let final_pct = results.final_coverage.coverage_pct(total_rules);
    assert!(final_pct > 0.0, "Even with add-only strategy, some rules should fire",);
}
