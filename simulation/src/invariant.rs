//! Invariant checking for simulation runs.
//!
//! Invariants are predicates checked at each step of a simulation. If an
//! invariant fails, the simulation records the failure but continues
//! (fail-slow). Built-in invariants cover common safety properties:
//! bounded size, bounded depth, parseability, and normal-form reachability.

use mettail_runtime::Language;

/// State passed to invariant checks at each simulation step.
pub struct InvariantState<'a> {
    /// Display string of the current term.
    pub current_term_display: &'a str,
    /// Zero-based step index.
    pub step_index: usize,
    /// Approximate number of AST nodes (from TermMetrics).
    pub term_size: usize,
    /// Approximate nesting depth (from TermMetrics).
    pub term_depth: usize,
    /// The language being simulated.
    pub language: &'a dyn Language,
}

/// Trait for simulation invariants.
///
/// Invariants are checked after each rewrite step. They return `Ok(())`
/// if the invariant holds, or `Err(message)` if it is violated.
pub trait Invariant: Send + Sync {
    /// Human-readable name of this invariant.
    fn name(&self) -> &str;

    /// Check the invariant against the current state.
    ///
    /// Returns `Ok(())` if the invariant holds, or `Err(message)` with
    /// a description of the violation.
    fn check(&self, state: &InvariantState) -> Result<(), String>;
}

// =============================================================================
// Built-in invariants
// =============================================================================

/// Invariant: term size (approximate node count) must not exceed `max_nodes`.
pub struct BoundedSize {
    /// Maximum allowed node count.
    pub max_nodes: usize,
}

impl Invariant for BoundedSize {
    fn name(&self) -> &str {
        "BoundedSize"
    }

    fn check(&self, state: &InvariantState) -> Result<(), String> {
        if state.term_size > self.max_nodes {
            Err(format!(
                "Term size {} exceeds bound {} at step {}",
                state.term_size, self.max_nodes, state.step_index,
            ))
        } else {
            Ok(())
        }
    }
}

/// Invariant: term depth (max nesting) must not exceed `max_depth`.
pub struct BoundedDepth {
    /// Maximum allowed nesting depth.
    pub max_depth: usize,
}

impl Invariant for BoundedDepth {
    fn name(&self) -> &str {
        "BoundedDepth"
    }

    fn check(&self, state: &InvariantState) -> Result<(), String> {
        if state.term_depth > self.max_depth {
            Err(format!(
                "Term depth {} exceeds bound {} at step {}",
                state.term_depth, self.max_depth, state.step_index,
            ))
        } else {
            Ok(())
        }
    }
}

/// Invariant: the term's display string must always be parseable.
///
/// This checks that the language's pretty-printer produces output that
/// can be re-parsed, which is a basic soundness property.
pub struct AlwaysParseable;

impl Invariant for AlwaysParseable {
    fn name(&self) -> &str {
        "AlwaysParseable"
    }

    fn check(&self, state: &InvariantState) -> Result<(), String> {
        mettail_runtime::clear_var_cache();
        match state.language.parse_term(state.current_term_display) {
            Ok(_) => Ok(()),
            Err(e) => Err(format!(
                "Term display {:?} is not parseable at step {}: {}",
                state.current_term_display, state.step_index, e,
            )),
        }
    }
}

/// Invariant: a normal form must be reachable within `max_steps`.
///
/// This is checked once at the end of a simulation run, not at each step.
/// It verifies that the rewriting process terminates.
pub struct NormalFormReachable {
    /// Maximum number of steps allowed before declaring non-termination.
    pub max_steps: usize,
}

impl Invariant for NormalFormReachable {
    fn name(&self) -> &str {
        "NormalFormReachable"
    }

    fn check(&self, state: &InvariantState) -> Result<(), String> {
        // This invariant is intentionally a no-op per step.
        // It is checked by the runner at the end of the simulation,
        // which inspects the total step count and final outcome.
        // Including it here allows it to be included in the invariant list
        // and reported consistently.
        let _ = state;
        Ok(())
    }
}

impl NormalFormReachable {
    /// Check at simulation completion whether normal form was reached.
    pub fn check_completion(&self, total_steps: usize, reached_normal_form: bool) -> Result<(), String> {
        if !reached_normal_form && total_steps >= self.max_steps {
            Err(format!(
                "Normal form not reached after {} steps (limit: {})",
                total_steps, self.max_steps,
            ))
        } else {
            Ok(())
        }
    }
}

// ═════════════════════════════════════════════════════════════════════════
// Sim-D: Guard-aware invariants
// ═════════════════════════════════════════════════════════════════════════

/// Invariant that asserts guarded rewrites fire only when their declared
/// guard predicates hold.
///
/// **What it is.** The `GuardSatisfaction` invariant takes a set of
/// rewrite-rule names that were declared with `BehavioralGuard`
/// premises in the language's `rewrites { }` block. Whenever the
/// simulator fires one of these rules, the invariant expects the
/// `language!`-macro-generated guard evaluation code to already have
/// returned `true` — firing a guarded rule whose guard returns
/// `false` is a soundness bug.
///
/// **Current scope (contract surface, not full evaluation).** The
/// invariant is a *contract surface*: it records which rules are
/// guarded and provides the hook for the simulator to report
/// violations. Full runtime evaluation of `BehavioralPred` against
/// arbitrary terms requires either:
///
/// 1. Reusing the language's macro-generated guard evaluation
///    functions (available in the generated parser but not yet
///    exposed through the `Language` trait), or
/// 2. Building a mini-evaluator over `QuantifiedFormula` from the
///    runtime trait methods.
///
/// The current `SimulationRunner::step` API does not pass the firing
/// rule name to the invariant `check` method, so the invariant cannot
/// yet identify which guarded rule fired on a given step. This is
/// documented as future work. The invariant is included in the
/// invariant list so users can opt in and track when they start
/// exercising guarded rules, and so the contract surface is stable
/// across future runner changes.
///
/// **Construction.** Users typically build this invariant from a
/// [`LanguageStateMachine`](crate::model::LanguageStateMachine)'s
/// `guarded_rewrites()` iterator:
///
/// ```ignore
/// use mettail_simulation::{model::LanguageStateMachine, invariant::GuardSatisfaction};
/// let state = LanguageStateMachine::from_metadata(language.metadata());
/// let invariant = GuardSatisfaction::from_state_machine(&state);
/// ```
pub struct GuardSatisfaction {
    /// Names of rewrite rules whose guards must be satisfied at every
    /// step that fires them. Sourced from
    /// `LanguageStateMachine::guarded_rewrites()`.
    pub guarded_rule_names: std::collections::HashSet<String>,
}

impl GuardSatisfaction {
    /// Construct a `GuardSatisfaction` invariant from a
    /// [`LanguageStateMachine`](crate::model::LanguageStateMachine),
    /// copying the names of all guarded rewrite rules.
    pub fn from_state_machine(state: &crate::model::LanguageStateMachine) -> Self {
        let guarded_rule_names = state
            .guarded_rewrites()
            .filter_map(|r| r.name.clone())
            .collect();
        GuardSatisfaction { guarded_rule_names }
    }

    /// Whether the given rule name is in this invariant's guarded set.
    pub fn is_guarded(&self, rule_name: &str) -> bool {
        self.guarded_rule_names.contains(rule_name)
    }

    /// Number of rules tracked by this invariant.
    pub fn guarded_rule_count(&self) -> usize {
        self.guarded_rule_names.len()
    }
}

impl Invariant for GuardSatisfaction {
    fn name(&self) -> &str {
        "GuardSatisfaction"
    }

    fn check(&self, _state: &InvariantState) -> Result<(), String> {
        // Sim-D scope note: the current SimulationRunner step API does
        // not pass the firing rule name to invariant check methods. When
        // it does (future work), this check should verify that any
        // guarded rule in `self.guarded_rule_names` fired only when its
        // guard evaluated to true. For now the invariant is a
        // contract-surface no-op so users can opt in and track which
        // rules are guarded.
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A mock language for invariant testing that always parses successfully.
    struct MockLanguage;

    impl Language for MockLanguage {
        fn name(&self) -> &'static str {
            "Mock"
        }
        fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
            &MockMetadata
        }
        fn parse_term(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, String> {
            Ok(Box::new(MockTerm(input.to_string())))
        }
        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, String> {
            self.parse_term(input)
        }
        fn run_ascent(&self, _term: &dyn mettail_runtime::Term) -> Result<mettail_runtime::AscentResults, String> {
            Ok(mettail_runtime::AscentResults::empty())
        }
        fn create_env(&self) -> Box<dyn std::any::Any + Send + Sync> {
            Box::new(())
        }
        fn add_to_env(&self, _env: &mut dyn std::any::Any, _name: &str, _term: &dyn mettail_runtime::Term) -> Result<(), String> {
            Ok(())
        }
        fn remove_from_env(&self, _env: &mut dyn std::any::Any, _name: &str) -> Result<bool, String> {
            Ok(false)
        }
        fn clear_env(&self, _env: &mut dyn std::any::Any) {}
        fn substitute_env(&self, term: &dyn mettail_runtime::Term, _env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, String> {
            Ok(term.clone_box())
        }
        fn list_env(&self, _env: &dyn std::any::Any) -> Vec<(String, String, Option<String>)> {
            vec![]
        }
        fn set_env_comment(&self, _env: &mut dyn std::any::Any, _name: &str, _comment: String) -> Result<(), String> {
            Ok(())
        }
        fn is_env_empty(&self, _env: &dyn std::any::Any) -> bool {
            true
        }
        fn infer_term_type(&self, _term: &dyn mettail_runtime::Term) -> mettail_runtime::TermType {
            mettail_runtime::TermType::Unknown
        }
        fn infer_var_types(&self, _term: &dyn mettail_runtime::Term) -> Vec<mettail_runtime::VarTypeInfo> {
            vec![]
        }
        fn infer_var_type(&self, _term: &dyn mettail_runtime::Term, _var_name: &str) -> Option<mettail_runtime::TermType> {
            None
        }
    }

    struct MockMetadata;

    impl mettail_runtime::LanguageMetadata for MockMetadata {
        fn name(&self) -> &'static str { "Mock" }
        fn types(&self) -> &'static [mettail_runtime::TypeDef] { &[] }
        fn terms(&self) -> &'static [mettail_runtime::TermDef] { &[] }
        fn equations(&self) -> &'static [mettail_runtime::EquationDef] { &[] }
        fn rewrites(&self) -> &'static [mettail_runtime::RewriteDef] { &[] }
    }

    #[derive(Debug, Clone)]
    struct MockTerm(String);

    impl std::fmt::Display for MockTerm {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl mettail_runtime::Term for MockTerm {
        fn clone_box(&self) -> Box<dyn mettail_runtime::Term> {
            Box::new(self.clone())
        }
        fn term_id(&self) -> u64 {
            0
        }
        fn term_eq(&self, other: &dyn mettail_runtime::Term) -> bool {
            if let Some(other) = other.as_any().downcast_ref::<MockTerm>() {
                self.0 == other.0
            } else {
                false
            }
        }
        fn as_any(&self) -> &dyn std::any::Any {
            self
        }
    }

    #[test]
    fn test_bounded_size_ok() {
        let inv = BoundedSize { max_nodes: 10 };
        let lang = MockLanguage;
        let state = InvariantState {
            current_term_display: "hello",
            step_index: 0,
            term_size: 5,
            term_depth: 1,
            language: &lang,
        };
        assert!(inv.check(&state).is_ok());
    }

    #[test]
    fn test_bounded_size_violation() {
        let inv = BoundedSize { max_nodes: 3 };
        let lang = MockLanguage;
        let state = InvariantState {
            current_term_display: "hello",
            step_index: 0,
            term_size: 5,
            term_depth: 1,
            language: &lang,
        };
        assert!(inv.check(&state).is_err());
    }

    #[test]
    fn test_bounded_depth_ok() {
        let inv = BoundedDepth { max_depth: 10 };
        let lang = MockLanguage;
        let state = InvariantState {
            current_term_display: "hello",
            step_index: 0,
            term_size: 5,
            term_depth: 3,
            language: &lang,
        };
        assert!(inv.check(&state).is_ok());
    }

    #[test]
    fn test_bounded_depth_violation() {
        let inv = BoundedDepth { max_depth: 2 };
        let lang = MockLanguage;
        let state = InvariantState {
            current_term_display: "hello",
            step_index: 0,
            term_size: 5,
            term_depth: 3,
            language: &lang,
        };
        assert!(inv.check(&state).is_err());
    }

    #[test]
    fn test_always_parseable_ok() {
        let inv = AlwaysParseable;
        let lang = MockLanguage;
        let state = InvariantState {
            current_term_display: "anything",
            step_index: 0,
            term_size: 1,
            term_depth: 0,
            language: &lang,
        };
        assert!(inv.check(&state).is_ok());
    }

    #[test]
    fn test_normal_form_reachable_completion() {
        let inv = NormalFormReachable { max_steps: 100 };
        assert!(inv.check_completion(50, true).is_ok());
        assert!(inv.check_completion(100, false).is_err());
        assert!(inv.check_completion(100, true).is_ok());
    }

    // ═════════════════════════════════════════════════════════════════════
    // Sim-D: GuardSatisfaction invariant tests
    // ═════════════════════════════════════════════════════════════════════

    use crate::model::{
        LanguageStateMachine, ModelBuiltinPredicate, ModelChannel, ModelConnective,
        ModelEquation, ModelJoinPattern, ModelRewriteRule, ModelTheory,
    };

    fn state_machine_with_guarded_rules(rules: Vec<(&str, bool)>) -> LanguageStateMachine {
        LanguageStateMachine {
            categories: vec!["Proc".to_string()],
            rewrite_rules: rules
                .into_iter()
                .map(|(name, is_guarded)| ModelRewriteRule {
                    name: Some(name.to_string()),
                    lhs_display: "lhs".to_string(),
                    rhs_display: "rhs".to_string(),
                    is_congruence: false,
                    is_guarded,
                })
                .collect(),
            equations: Vec::<ModelEquation>::new(),
            builtin_predicates: Vec::<ModelBuiltinPredicate>::new(),
            theories: Vec::<ModelTheory>::new(),
            channels: Vec::<ModelChannel>::new(),
            join_patterns: Vec::<ModelJoinPattern>::new(),
            connectives: Vec::<ModelConnective>::new(),
        }
    }

    #[test]
    fn sim_d_guard_satisfaction_collects_guarded_names() {
        let state = state_machine_with_guarded_rules(vec![
            ("GuardedComm", true),
            ("PlainCong", false),
            ("GuardedExec", true),
        ]);
        let inv = GuardSatisfaction::from_state_machine(&state);
        assert_eq!(inv.guarded_rule_count(), 2);
        assert!(inv.is_guarded("GuardedComm"));
        assert!(inv.is_guarded("GuardedExec"));
        assert!(!inv.is_guarded("PlainCong"));
        assert!(!inv.is_guarded("UnknownRule"));
    }

    #[test]
    fn sim_d_guard_satisfaction_empty_when_no_guarded_rules() {
        let state = state_machine_with_guarded_rules(vec![
            ("Rule1", false),
            ("Rule2", false),
        ]);
        let inv = GuardSatisfaction::from_state_machine(&state);
        assert_eq!(inv.guarded_rule_count(), 0);
    }

    #[test]
    fn sim_d_guard_satisfaction_check_is_noop() {
        // Current scope: the check method is a no-op contract surface.
        // This test locks in that behavior so a future semantic change
        // is explicit (the test will need updating then).
        let state = state_machine_with_guarded_rules(vec![("G", true)]);
        let inv = GuardSatisfaction::from_state_machine(&state);
        assert_eq!(inv.name(), "GuardSatisfaction");
        let lang = MockLanguage;
        let state = InvariantState {
            current_term_display: "",
            step_index: 0,
            term_size: 0,
            term_depth: 0,
            language: &lang,
        };
        assert!(inv.check(&state).is_ok());
    }
}
