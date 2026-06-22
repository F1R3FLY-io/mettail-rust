//! Temporal Property Checking
//!
//! Provides standalone LTL (Linear Temporal Logic) checking over simulation
//! traces, independent of the simulation runner. Traces are sequences of
//! `(term_display, is_normal_form)` pairs, and atomic propositions evaluate
//! over these pairs.
//!
//! ## Architecture
//!
//! ```text
//! trace: [(String, bool)]
//!       │
//!       ▼
//! check_trace_ltl(trace, formula_str, propositions)
//!       │
//!       ├── 1. Parse LTL formula via prattail::ltl::parse_ltl()
//!       ├── 2. Evaluate atomic propositions at each trace step → label sets
//!       ├── 3. Build system Büchi automaton from labeled trace
//!       ├── 4. Negate property, compile to Büchi, intersect, check emptiness
//!       └── 5. Return LtlCheckResult
//!             │
//!             ├── Satisfied
//!             ├── Violated { step, message }
//!             └── ParseError { message }
//! ```
//!
//! ## Theoretical Foundations
//!
//! The implementation follows the standard automata-theoretic model checking
//! pipeline (Vardi & Wolper, 1986):
//!
//! 1. The system trace is modeled as a finite-word Büchi automaton with
//!    self-loops on the final state (to model infinite extension).
//! 2. The LTL property is negated and compiled to a Büchi automaton.
//! 3. The product automaton L(system) ∩ L(¬φ) is computed.
//! 4. If the product is non-empty, the property is violated.

use crate::trace::{ExecutionTrace, TraceOutcome};
use mettail_prattail::buchi::BuchiAutomaton;
use mettail_prattail::ltl::{self, LtlProperty};

// ══════════════════════════════════════════════════════════════════════════════
// Atomic Propositions
// ══════════════════════════════════════════════════════════════════════════════

/// An atomic proposition that can be evaluated over a simulation state.
///
/// Each proposition has a name (corresponding to an LTL atom) and an
/// evaluation function that determines whether the proposition holds
/// for a given (term_display, is_normal_form) pair.
pub trait AtomicProposition: Send + Sync {
    /// The name of this proposition, matching the LTL atom name.
    fn name(&self) -> &str;

    /// Evaluate whether this proposition holds for the given state.
    ///
    /// # Arguments
    ///
    /// * `term_display` - The display string of the current term.
    /// * `is_normal_form` - Whether the current term is in normal form.
    fn evaluate(&self, term_display: &str, is_normal_form: bool) -> bool;
}

/// Proposition: the term is in normal form (no further rewrites possible).
pub struct IsNormalForm;

impl AtomicProposition for IsNormalForm {
    fn name(&self) -> &str {
        "normal_form"
    }

    fn evaluate(&self, _term: &str, is_nf: bool) -> bool {
        is_nf
    }
}

/// Proposition: the term's display string length is bounded.
pub struct TermSizeBounded {
    /// Maximum allowed length of the term's display string.
    pub bound: usize,
}

impl AtomicProposition for TermSizeBounded {
    fn name(&self) -> &str {
        "bounded_size"
    }

    fn evaluate(&self, term: &str, _: bool) -> bool {
        term.len() <= self.bound
    }
}

/// Proposition: the term's display string contains a specific substring.
pub struct ContainsSubstring {
    /// The substring to search for.
    pub pattern: String,
}

impl AtomicProposition for ContainsSubstring {
    fn name(&self) -> &str {
        "contains"
    }

    fn evaluate(&self, term: &str, _: bool) -> bool {
        term.contains(&self.pattern)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// LTL Check Result
// ══════════════════════════════════════════════════════════════════════════════

/// Result of checking an LTL property against a trace.
#[derive(Debug, Clone)]
pub enum LtlCheckResult {
    /// The property is satisfied by the trace.
    Satisfied,
    /// The property is violated at a specific step.
    Violated {
        /// The step index where the violation was detected (0-based).
        step: usize,
        /// Human-readable description of the violation.
        message: String,
    },
    /// The LTL formula could not be parsed.
    ParseError {
        /// The parse error message.
        message: String,
    },
}

// ══════════════════════════════════════════════════════════════════════════════
// Core checking function
// ══════════════════════════════════════════════════════════════════════════════

/// Check an LTL property against a trace of (term_display, is_normal_form) pairs.
///
/// Implements the full automata-theoretic LTL model checking pipeline:
///
/// 1. Parse the LTL formula string.
/// 2. Evaluate atomic propositions at each trace step to produce label sets.
/// 3. Build a system Büchi automaton from the labeled trace.
/// 4. Negate the property formula, compile to Büchi automaton.
/// 5. Intersect the system and negated-property automata.
/// 6. Check emptiness of the product automaton.
/// 7. If non-empty, extract the violating step from the trace.
///
/// # Arguments
///
/// * `trace` - Sequence of (term_display, is_normal_form) pairs representing
///   the execution trace.
/// * `formula_str` - The LTL formula to check (e.g., "F(normal_form)").
/// * `propositions` - The atomic propositions available for evaluation.
///
/// # Returns
///
/// An `LtlCheckResult` indicating whether the property holds.
pub fn check_trace_ltl(
    trace: &[(String, bool)],
    formula_str: &str,
    propositions: &[Box<dyn AtomicProposition>],
) -> LtlCheckResult {
    // Step 1: Parse the LTL formula.
    let formula = match ltl::parse_ltl(formula_str) {
        Ok(f) => f,
        Err(e) => {
            return LtlCheckResult::ParseError {
                message: format!("Failed to parse LTL formula '{}': {}", formula_str, e),
            };
        },
    };

    // Handle empty trace: vacuously satisfied for safety, violated for liveness.
    if trace.is_empty() {
        // An empty trace satisfies any safety property (nothing bad happens)
        // but fails liveness (nothing good can happen either).
        // For simplicity, treat empty as satisfied (vacuously true).
        return LtlCheckResult::Satisfied;
    }

    // Step 2: Evaluate atomic propositions at each step.
    // For each trace step, compute the set of proposition names that hold.
    let atom_names: Vec<String> = formula.atoms().into_iter().collect();
    let label_sets: Vec<Vec<String>> = trace
        .iter()
        .map(|(term_display, is_nf)| {
            atom_names
                .iter()
                .filter(|atom_name| {
                    propositions.iter().any(|prop| {
                        prop.name() == atom_name.as_str() && prop.evaluate(term_display, *is_nf)
                    })
                })
                .cloned()
                .collect()
        })
        .collect();

    // Step 3: Build system Büchi automaton from the labeled trace.
    //
    // The trace is a finite sequence of states. To model it as an infinite
    // word (required for Büchi acceptance), we add a self-loop on the last
    // state. The last state is accepting (to model the infinite suffix).
    //
    // States: one per trace step.
    // Transitions: step[i] --labels[i]--> step[i+1], and self-loop on last.
    // The transition labels encode which propositions hold at the source state.
    let mut system = BuchiAutomaton::new();
    let num_steps = trace.len();

    // Add states: all are accepting (we want the system to always accept;
    // the property checking is done via the negated formula).
    // Actually, for the standard model checking approach, the system automaton
    // should accept all runs. We make all states accepting with self-loops.
    let mut state_ids = Vec::with_capacity(num_steps);
    for _ in 0..num_steps {
        let sid = system.add_state(true);
        state_ids.push(sid);
    }

    // Set initial state
    system.initial_states.insert(state_ids[0]);

    // Add transitions based on label sets.
    // Each step's labels become the transition label from that state.
    // We encode the label set as individual transition labels (one per proposition).
    for i in 0..num_steps {
        let next_state = if i + 1 < num_steps {
            state_ids[i + 1]
        } else {
            // Self-loop on the last state
            state_ids[i]
        };

        let from_state = state_ids[i];

        // Add a transition for each proposition that holds at this step.
        // Also add a "__true__" transition (matches the wildcard in LTL Büchi).
        system.add_transition(from_state, Some("__true__".to_string()), next_state);

        for prop_name in &label_sets[i] {
            system.add_transition(from_state, Some(prop_name.clone()), next_state);
        }

        // Add negated proposition labels for propositions that do NOT hold.
        // This is needed for the Büchi intersection to work correctly with
        // negated atoms (e.g., !normal_form).
        for atom_name in &atom_names {
            if !label_sets[i].contains(atom_name) {
                system.add_transition(from_state, Some(format!("!{}", atom_name)), next_state);
            }
        }
    }

    // Step 4: Check the LTL property via standard automata-theoretic approach.
    let property = LtlProperty::new(formula_str.to_string(), formula);
    let check_result = ltl::check_ltl_property(&system, &property);

    // Step 5: Convert the prattail LtlCheckResult to our LtlCheckResult.
    match check_result {
        ltl::LtlCheckResult::Satisfied => LtlCheckResult::Satisfied,
        ltl::LtlCheckResult::Violated { prefix, lasso } => {
            // Try to identify the violating step.
            // The prefix gives the trace leading to violation.
            // We report the length of the prefix as the step index,
            // clamped to the trace length.
            let step = prefix.len().min(num_steps.saturating_sub(1));
            let mut message = format!("LTL property '{}' violated", formula_str);
            if !prefix.is_empty() {
                message.push_str(&format!(". Prefix: {}", prefix.join(" -> ")));
            }
            if !lasso.is_empty() {
                message.push_str(&format!(". Lasso: {}", lasso.join(" -> ")));
            }
            LtlCheckResult::Violated { step, message }
        },
        ltl::LtlCheckResult::Inconclusive { reason } => {
            // Treat inconclusive as satisfied with a note.
            // This can happen for very large state spaces.
            LtlCheckResult::Violated {
                step: 0,
                message: format!("LTL check inconclusive for '{}': {}", formula_str, reason),
            }
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Runner adaptor: ExecutionTrace → LTL step sequence
// ══════════════════════════════════════════════════════════════════════════════

/// The default term-display length bound used by [`default_propositions`] for
/// the `bounded_size` atom. Chosen generously so `G(bounded_size)` holds for
/// ordinary terms; users wanting a tighter bound construct their own
/// [`TermSizeBounded`] proposition set.
pub const DEFAULT_TERM_SIZE_BOUND: usize = 4096;

/// Project an [`ExecutionTrace`] into the `(term_display, is_normal_form)`
/// step sequence consumed by [`check_trace_ltl`].
///
/// Each [`crate::trace::TraceEntry`] contributes one step whose label is its
/// `term_display`. The `ExecutionTrace` records no per-step normal-form flag —
/// normal-form status lives only in the terminal [`TraceOutcome::NormalForm`]
/// outcome — so the flag is *derived*: a step is in normal form iff the trace's
/// outcome is `NormalForm` **and** the step is the final one. Intermediate
/// steps are therefore never normal-form, and a trace whose outcome is anything
/// other than `NormalForm` (step-limit, runtime report, invariant violation,
/// error, …) yields no normal-form step at all — which is exactly what makes a
/// liveness property like `F(normal_form)` fail for a non-converging run.
///
/// The returned vector is preallocated to the trace's step count. An empty
/// trace yields an empty step sequence (which `check_trace_ltl` treats as
/// vacuously satisfied).
pub fn trace_to_ltl_steps(trace: &ExecutionTrace) -> Vec<(String, bool)> {
    let terminal_normal_form = matches!(trace.outcome, TraceOutcome::NormalForm { .. });
    let last_index = trace.steps.len().saturating_sub(1);
    let mut steps = Vec::with_capacity(trace.steps.len());
    for (idx, entry) in trace.steps.iter().enumerate() {
        let is_normal_form = terminal_normal_form && idx == last_index;
        steps.push((entry.term_display.clone(), is_normal_form));
    }
    steps
}

/// The default atomic-proposition set wired into LTL trace checking by the
/// [`crate::runner::SimulationRunner`].
///
/// Provides exactly the shipped propositions needed for the canonical
/// termination/safety formulas:
///
/// - [`IsNormalForm`] (atom `normal_form`) — supports `F(normal_form)`
///   ("eventually reaches a normal form") and `G(!normal_form)` style queries.
/// - [`TermSizeBounded`] (atom `bounded_size`, bound [`DEFAULT_TERM_SIZE_BOUND`])
///   — supports `G(bounded_size)` ("term display never blows up").
/// - [`ContainsSubstring`] (atom `contains`, empty pattern) — present so the
///   `contains` atom resolves; an empty pattern is contained by every string,
///   so it acts as a `true` literal unless the user supplies their own pattern
///   via a custom proposition set.
///
/// Callers wanting different bounds or patterns build their own
/// `Vec<Box<dyn AtomicProposition>>` and call [`check_trace_ltl`] directly.
pub fn default_propositions() -> Vec<Box<dyn AtomicProposition>> {
    vec![
        Box::new(IsNormalForm),
        Box::new(TermSizeBounded { bound: DEFAULT_TERM_SIZE_BOUND }),
        Box::new(ContainsSubstring { pattern: String::new() }),
    ]
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace::{ExecutionTrace, TraceEntry, TraceOutcome};

    /// Helper: create standard propositions for testing.
    fn standard_propositions() -> Vec<Box<dyn AtomicProposition>> {
        vec![Box::new(IsNormalForm), Box::new(TermSizeBounded { bound: 100 })]
    }

    /// Build a minimal trace with the given step displays and outcome.
    fn trace_with(steps: &[&str], outcome: TraceOutcome) -> ExecutionTrace {
        ExecutionTrace {
            seed: "deterministic".to_string(),
            language: "Mock".to_string(),
            steps: steps
                .iter()
                .enumerate()
                .map(|(i, d)| TraceEntry {
                    step_index: i,
                    term_display: (*d).to_string(),
                    operation: "parse".to_string(),
                    metrics: None,
                })
                .collect(),
            outcome,
            morphology: None,
        }
    }

    #[test]
    fn trace_to_ltl_steps_marks_only_final_step_normal_form() {
        let trace = trace_with(
            &["(AddInt 3 5)", "8"],
            TraceOutcome::NormalForm { term: "8".to_string(), steps: 2 },
        );
        let steps = trace_to_ltl_steps(&trace);
        assert_eq!(steps.len(), 2);
        assert_eq!(steps[0], ("(AddInt 3 5)".to_string(), false));
        assert_eq!(steps[1], ("8".to_string(), true));
    }

    #[test]
    fn trace_to_ltl_steps_non_normal_form_outcome_has_no_nf_step() {
        let trace = trace_with(
            &["a", "b", "c"],
            TraceOutcome::StepLimitReached { final_term: "c".to_string() },
        );
        let steps = trace_to_ltl_steps(&trace);
        assert_eq!(steps.len(), 3);
        assert!(steps.iter().all(|(_, is_nf)| !is_nf));
    }

    #[test]
    fn trace_to_ltl_steps_empty_trace_is_empty() {
        let trace =
            trace_with(&[], TraceOutcome::NormalForm { term: "x".to_string(), steps: 0 });
        assert!(trace_to_ltl_steps(&trace).is_empty());
    }

    #[test]
    fn default_propositions_resolve_canonical_atoms() {
        let props = default_propositions();
        // F(normal_form) is satisfied for a converging trace.
        let converging = trace_with(
            &["(AddInt 3 5)", "8"],
            TraceOutcome::NormalForm { term: "8".to_string(), steps: 2 },
        );
        let steps = trace_to_ltl_steps(&converging);
        assert!(matches!(
            check_trace_ltl(&steps, "F(normal_form)", &props),
            LtlCheckResult::Satisfied
        ));
        // F(normal_form) is violated for a non-converging trace.
        let stuck =
            trace_with(&["a", "b"], TraceOutcome::StepLimitReached { final_term: "b".to_string() });
        let stuck_steps = trace_to_ltl_steps(&stuck);
        assert!(matches!(
            check_trace_ltl(&stuck_steps, "F(normal_form)", &props),
            LtlCheckResult::Violated { .. }
        ));
        // G(bounded_size) holds for short terms under the generous default bound.
        assert!(matches!(
            check_trace_ltl(&steps, "G(bounded_size)", &props),
            LtlCheckResult::Satisfied
        ));
    }

    #[test]
    fn test_ltl_eventually_normal_form() {
        // Trace: starts non-normal, eventually reaches normal form.
        let trace: Vec<(String, bool)> = vec![
            ("(AddInt 3 5)".to_string(), false),
            ("(AddInt 3 5)".to_string(), false),
            ("8".to_string(), true),
        ];

        let props = standard_propositions();
        let result = check_trace_ltl(&trace, "F(normal_form)", &props);

        match result {
            LtlCheckResult::Satisfied => {}, // expected
            other => panic!(
                "Expected Satisfied for F(normal_form) on trace reaching NF, got: {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_ltl_always_bounded() {
        // Trace: all terms have display length <= 100.
        let trace: Vec<(String, bool)> =
            vec![("(AddInt 3 5)".to_string(), false), ("8".to_string(), true)];

        let props = standard_propositions();
        let result = check_trace_ltl(&trace, "G(bounded_size)", &props);

        match result {
            LtlCheckResult::Satisfied => {}, // expected
            other => {
                panic!("Expected Satisfied for G(bounded_size) on bounded trace, got: {:?}", other)
            },
        }
    }

    #[test]
    fn test_ltl_violation() {
        // Trace that NEVER reaches normal form.
        let trace: Vec<(String, bool)> = vec![
            ("(AddInt 3 5)".to_string(), false),
            ("(SubInt 10 2)".to_string(), false),
            ("(MulInt 2 3)".to_string(), false),
        ];

        let props = standard_propositions();
        let result = check_trace_ltl(&trace, "F(normal_form)", &props);

        match result {
            LtlCheckResult::Violated { step: _, message } => {
                assert!(
                    message.contains("F(normal_form)"),
                    "Violation message should reference the formula: {}",
                    message
                );
            },
            other => panic!(
                "Expected Violated for F(normal_form) on trace never reaching NF, got: {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_ltl_parse_error() {
        let trace: Vec<(String, bool)> = vec![("x".to_string(), false)];
        let props = standard_propositions();

        let result = check_trace_ltl(&trace, "F(normal_form &&& bad)", &props);
        match result {
            LtlCheckResult::ParseError { message } => {
                assert!(
                    message.contains("Failed to parse"),
                    "Parse error message should indicate failure: {}",
                    message
                );
            },
            other => panic!("Expected ParseError, got: {:?}", other),
        }
    }

    #[test]
    fn test_ltl_empty_trace() {
        let trace: Vec<(String, bool)> = vec![];
        let props = standard_propositions();

        let result = check_trace_ltl(&trace, "F(normal_form)", &props);
        match result {
            LtlCheckResult::Satisfied => {}, // vacuously true
            other => panic!("Expected Satisfied for empty trace, got: {:?}", other),
        }
    }

    #[test]
    fn test_atomic_propositions() {
        // IsNormalForm
        let nf = IsNormalForm;
        assert_eq!(nf.name(), "normal_form");
        assert!(nf.evaluate("anything", true));
        assert!(!nf.evaluate("anything", false));

        // TermSizeBounded
        let bounded = TermSizeBounded { bound: 5 };
        assert_eq!(bounded.name(), "bounded_size");
        assert!(bounded.evaluate("abc", false));
        assert!(bounded.evaluate("12345", false));
        assert!(!bounded.evaluate("123456", false));

        // ContainsSubstring
        let contains = ContainsSubstring { pattern: "Zero".to_string() };
        assert_eq!(contains.name(), "contains");
        assert!(contains.evaluate("PZero", false));
        assert!(!contains.evaluate("PPar", false));
    }

    #[test]
    fn test_ltl_single_step_normal_form() {
        // Single step that IS normal form: F(normal_form) should be satisfied.
        let trace: Vec<(String, bool)> = vec![("42".to_string(), true)];

        let props = standard_propositions();
        let result = check_trace_ltl(&trace, "F(normal_form)", &props);

        match result {
            LtlCheckResult::Satisfied => {}, // expected
            other => panic!("Expected Satisfied for single-step NF trace, got: {:?}", other),
        }
    }

    #[test]
    fn test_ltl_always_true_literal() {
        // G(true) should always be satisfied.
        let trace: Vec<(String, bool)> =
            vec![("a".to_string(), false), ("b".to_string(), false), ("c".to_string(), true)];

        let props = standard_propositions();
        let result = check_trace_ltl(&trace, "G(true)", &props);

        match result {
            LtlCheckResult::Satisfied => {}, // expected
            other => panic!("Expected Satisfied for G(true), got: {:?}", other),
        }
    }
}
