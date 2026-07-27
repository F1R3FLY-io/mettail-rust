//! Safety and liveness verification via WPDS reachability.
//!
//! Provides the core verification API that uses existing WPDS infrastructure
//! (poststar/prestar) to check properties of programs written in `language!`-defined
//! languages. Properties are expressed as sets of "bad" configurations (safety) or
//! temporal patterns (liveness, when `ltl` feature is enabled).
//!
//! ## Verification Strategy
//!
//! Safety properties are checked via **prestar**: given a set of bad configurations
//! (encoded as a P-automaton), prestar computes all configurations from which a bad
//! configuration is reachable. If the initial configuration is NOT in this set, the
//! property holds.
//!
//! Quantitative properties use different semirings:
//! - `BooleanWeight`: yes/no reachability (safety)
//! - `TropicalWeight`: minimum cost to reach bad state (resource bounds)
//! - `CountingWeight`: number of distinct paths to bad state
//!
//! ## References
//!
//! - Reps, Lal & Kidd (2007), *Program Analysis Using Weighted Pushdown Systems*
//! - Schwoon (2002), *Model-Checking Pushdown Systems*

use crate::automata::semiring::Semiring;
use crate::repair::{RepairAction, RepairKind, RepairSet, RepairSuggestion};
use crate::wpds::{PAutomaton, StackSymbol, Wpds};

/// Result of a safety verification check.
#[derive(Debug, Clone)]
pub struct SafetyResult<W: Semiring> {
    /// Whether the property holds (no bad state is reachable).
    pub safe: bool,
    /// Weight of the initial configuration in the prestar result.
    /// For `BooleanWeight`: true = reachable (unsafe), false = unreachable (safe).
    /// For `TropicalWeight`: minimum cost to reach bad state.
    pub initial_weight: W,
    /// Witness trace: stack symbols along the path to the bad state (if unsafe).
    /// Empty if the property holds.
    pub witness_trace: Vec<StackSymbol>,
}

/// Check whether any "bad" configuration is reachable from the initial configuration.
///
/// The `bad_states` P-automaton encodes the set of configurations that violate the
/// safety property. Returns `SafetyResult` with `safe = true` if none are reachable.
///
/// # How the verdict is read
///
/// The initial configuration is the one-symbol stack `⟨p, γ₀⟩`, so membership in
/// `pre*(bad)` is the acceptance of the stack word `γ₀` by the prestar automaton:
/// a path from `p` reading `γ₀` that **ends in a final state** (Reps et al. 2007,
/// Definition 3). [`PAutomaton::symbol_weight`](crate::wpds::PAutomaton::symbol_weight)
/// asks exactly that, and `cegar::abstract_check` asks it independently via
/// `accepts_initial_config`.
///
/// The target check is load-bearing. Saturation adds transitions that lead nowhere
/// accepting — prestar's Pop phase seeds the self-loop `(p, γ, p)` for every Pop rule,
/// and the Replace pass propagates it onto other symbols — so a weight that summed
/// every out-transition regardless of target reported `safe = false`, with a witness,
/// for a WPDS with rules checked against a bad set containing NO configurations at
/// all. `verify::tests::test_empty_bad_states_is_safe` pins the repaired behaviour on
/// a WPDS carrying all three rule kinds, and
/// `verify::tests::test_reachable_bad_state_is_reported_unsafe` pins the converse so
/// the verdict cannot degenerate into a blanket "safe".
///
/// # Example (Boolean reachability)
///
/// The label `"BadState"` matches no stack symbol of this grammar, so `bad` encodes
/// the EMPTY set of configurations — and nothing is reachable from a WPDS into a set
/// with no members, however many rules the WPDS has.
///
/// ```
/// # use std::collections::HashMap;
/// # use mettail_prattail::automata::semiring::BooleanWeight;
/// # use mettail_prattail::binding_power::Associativity;
/// # use mettail_prattail::verify::{build_bad_state_automaton, check_safety};
/// # use mettail_prattail::wpds::build_wpds;
/// # use mettail_prattail::{CategorySpec, LanguageSpec, RuleSpecInput};
/// # let spec = LanguageSpec::new(
/// #     "Calc".to_string(),
/// #     vec![CategorySpec {
/// #         name: "Expr".to_string(),
/// #         native_type: Some("i64".to_string()),
/// #         is_primary: true,
/// #         has_var: true,
/// #     }],
/// #     vec![RuleSpecInput {
/// #         label: "NumLit".to_string(),
/// #         category: "Expr".to_string(),
/// #         syntax: Vec::new(),
/// #         associativity: Associativity::Left,
/// #         prefix_precedence: None,
/// #         has_rust_code: false,
/// #         rust_code: None,
/// #         eval_mode: None,
/// #         source_location: None,
/// #         is_auto_injected: false,
/// #     }],
/// # );
/// # let wfsts = HashMap::new();
/// let wpds = build_wpds::<BooleanWeight>(&spec, &wfsts, |_| BooleanWeight::new(true));
/// // The grammar really does generate rules — the verdict below is not vacuous.
/// assert!(!wpds.rules.is_empty());
///
/// let bad = build_bad_state_automaton(&wpds, &["BadState"]);
/// assert!(bad.transitions.is_empty(), "no stack symbol is labelled `BadState`");
///
/// let result = check_safety(&wpds, &bad);
/// assert!(result.safe, "nothing is reachable into the empty set of configurations");
/// // Verdict and witness always agree: a safe verdict carries no trace,
/// // an unsafe one names the symbols along the path to the bad state.
/// assert!(result.witness_trace.is_empty());
/// assert_eq!(result.safe, result.witness_trace.is_empty());
/// ```
pub fn check_safety<W: Semiring>(wpds: &Wpds<W>, bad_states: &PAutomaton<W>) -> SafetyResult<W> {
    let prestar_result = crate::wpds::prestar(wpds, bad_states);

    // Check if the initial configuration is in the prestar result.
    let initial_weight = prestar_result.symbol_weight(&wpds.initial_symbol);
    let safe = initial_weight.is_zero();

    let witness_trace = if !safe {
        extract_witness_trace(&prestar_result, &wpds.initial_symbol)
    } else {
        Vec::new()
    };

    SafetyResult { safe, initial_weight, witness_trace }
}

/// Build a P-automaton representing a set of "bad" configurations.
///
/// Each label in `bad_labels` is treated as a category entry that should not be
/// reachable. The resulting P-automaton accepts any configuration containing
/// one of these stack symbols.
pub fn build_bad_state_automaton<W: Semiring>(
    wpds: &Wpds<W>,
    bad_labels: &[&str],
) -> PAutomaton<W> {
    let initial_state = 0;
    let mut automaton = PAutomaton::new(initial_state);
    let final_state = automaton.add_state();
    automaton.mark_final(final_state);

    for label in bad_labels {
        // Find all stack symbols matching this label.
        for sym in &wpds.stack_symbols {
            if sym.rule_label == *label || sym.category == *label {
                automaton.add_transition(initial_state, sym.clone(), final_state, W::one());
                automaton.symbol_to_state.insert(sym.clone(), final_state);
            }
        }
    }

    automaton
}

/// Extract a witness trace from a prestar result showing how the initial
/// configuration reaches a bad state.
fn extract_witness_trace<W: Semiring>(
    prestar_result: &PAutomaton<W>,
    initial_symbol: &StackSymbol,
) -> Vec<StackSymbol> {
    let mut trace = Vec::new();
    let mut current_state = prestar_result.initial_state;

    // Follow transitions from the initial state, collecting stack symbols.
    if let Some(trans_indices) = prestar_result.transitions_by_source.get(&current_state) {
        for &idx in trans_indices {
            let t = &prestar_result.transitions[idx];
            if t.symbol == *initial_symbol && !t.weight.is_zero() {
                trace.push(t.symbol.clone());
                current_state = t.to;
                break;
            }
        }
    }

    // Continue following non-zero transitions to build the trace.
    let mut visited = std::collections::HashSet::new();
    visited.insert(current_state);
    loop {
        let mut found = false;
        if let Some(trans_indices) = prestar_result.transitions_by_source.get(&current_state) {
            for &idx in trans_indices {
                let t = &prestar_result.transitions[idx];
                if !t.weight.is_zero() && !visited.contains(&t.to) {
                    trace.push(t.symbol.clone());
                    visited.insert(t.to);
                    current_state = t.to;
                    found = true;
                    break;
                }
            }
        }
        if !found || prestar_result.final_states.contains(&current_state) {
            break;
        }
    }

    trace
}

/// Verdict from a verification analysis. Always included regardless of feature flags.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Property holds — no counterexample exists.
    Verified,
    /// Property violated — counterexample/witness available.
    Violated,
    /// Analysis could not determine (e.g., timeout, undecidable).
    Unknown,
}

impl std::fmt::Display for Verdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Verdict::Verified => write!(f, "VERIFIED"),
            Verdict::Violated => write!(f, "VIOLATED"),
            Verdict::Unknown => write!(f, "UNKNOWN"),
        }
    }
}

/// A verification result with verdict and optional witness.
#[derive(Debug, Clone)]
pub struct VerificationResult<W: Semiring> {
    /// The verdict: verified, violated, or unknown.
    pub verdict: Verdict,
    /// Property description (human-readable).
    pub property: String,
    /// The analysis weight (semiring-dependent interpretation).
    pub weight: W,
    /// Witness trace (stack symbols) if violated; empty if verified.
    pub witness: Vec<StackSymbol>,
}

/// Generate repair suggestions from a failed safety check.
///
/// If the safety result indicates the property holds (`safe == true`), returns an
/// empty `RepairSet`. Otherwise, analyzes the witness trace to produce actionable
/// repair suggestions:
///
/// 1. **Per-step guards**: For each step in the witness trace, suggests adding a
///    guard at that position. Edit cost increases with trace position (earlier
///    positions are cheaper to fix), and the number of alternatives equals the
///    trace length (each step is an independent fix site).
///
/// 2. **Restrict initial configuration**: Suggests restricting the initial
///    configuration so that the unsafe path is never entered. This is always
///    suggested when a witness exists, with confidence 0.5 and edit cost 3
///    (moderately expensive since it may change program semantics).
///
/// Confidence is derived from trace length: shorter traces yield higher confidence
/// because the causal chain is more direct and easier to reason about.
///
/// # Arguments
///
/// * `result` — The `SafetyResult` from `check_safety`.
/// * `wpds` — The WPDS used in the analysis (provides grammar context for
///   descriptive messages).
pub fn suggest_safety_repairs<W: Semiring>(result: &SafetyResult<W>, wpds: &Wpds<W>) -> RepairSet {
    let mut repairs = RepairSet::new();

    if result.safe {
        return repairs;
    }

    let trace = &result.witness_trace;

    // Confidence inversely proportional to trace length: shorter traces are
    // more actionable. Clamp to [0.1, 1.0].
    let base_confidence = if trace.is_empty() {
        0.5
    } else {
        (1.0 / trace.len() as f64).clamp(0.1, 1.0)
    };

    // Suggest adding a guard at each step of the witness trace.
    for (step_idx, sym) in trace.iter().enumerate() {
        let description = if sym.rule_label.is_empty() {
            format!(
                "Add guard at category entry {} (trace step {}) in grammar '{}'",
                sym.category, step_idx, wpds.grammar_name,
            )
        } else {
            format!(
                "Add guard at {}.{}@{} (trace step {}) in grammar '{}'",
                sym.category, sym.rule_label, sym.position, step_idx, wpds.grammar_name,
            )
        };

        // Earlier steps in the trace are cheaper to fix (prevent the path sooner).
        let edit_cost = (step_idx as u32).saturating_add(1);

        let suggestion = RepairSuggestion::new(
            RepairKind::FixTermination,
            description,
            RepairAction::Description(format!(
                "Insert a guard predicate before stack symbol {} to block the unsafe path",
                sym,
            )),
        )
        .with_confidence(base_confidence)
        .with_edit_cost(edit_cost)
        .with_alternatives(trace.len() as u64);

        repairs.add(suggestion);
    }

    // Suggest restricting the initial configuration.
    let restrict_description = format!(
        "Restrict initial configuration at {} to exclude unsafe paths in grammar '{}'",
        wpds.initial_symbol, wpds.grammar_name,
    );

    let restrict_suggestion = RepairSuggestion::new(
        RepairKind::Custom("RestrictInitialConfig".to_string()),
        restrict_description,
        RepairAction::Description(format!(
            "Narrow the entry point {} so that the initial configuration \
             cannot reach the bad state via the identified witness trace",
            wpds.initial_symbol,
        )),
    )
    .with_confidence(0.5)
    .with_edit_cost(3)
    .with_alternatives(1);

    repairs.add(restrict_suggestion);

    repairs
}

/// Generate repair suggestions when a verification result is `Violated`.
///
/// Produces two complementary suggestions for strengthening verification:
///
/// 1. **Strengthen precondition** (`RepairKind::StrengthenPrecondition`):
///    Suggests making the precondition more restrictive so that the violating
///    input is excluded. Confidence is 0.7 (precondition strengthening is a
///    well-understood technique but may over-restrict).
///
/// 2. **Weaken postcondition** (`RepairKind::WeakenPostcondition`):
///    Suggests relaxing the postcondition to accommodate the observed behavior.
///    Confidence is 0.6 (weakening may hide real bugs, so slightly less confident).
///
/// Both suggestions include the witness trace for context. If the verdict is
/// `Verified` or `Unknown`, returns an empty `RepairSet`.
///
/// # Arguments
///
/// * `result` — The `VerificationResult` to analyze.
pub fn suggest_invariant_strengthening<W: Semiring>(result: &VerificationResult<W>) -> RepairSet {
    let mut repairs = RepairSet::new();

    if result.verdict != Verdict::Violated {
        return repairs;
    }

    // Format witness context for repair descriptions.
    let witness_context = if result.witness.is_empty() {
        "no witness trace available".to_string()
    } else {
        let symbols: Vec<String> = result.witness.iter().map(|s| s.to_string()).collect();
        format!("witness trace: {}", symbols.join(" -> "))
    };

    // Suggestion 1: Strengthen the precondition.
    let pre_description = format!(
        "Strengthen precondition for property '{}' to exclude violating inputs ({})",
        result.property, witness_context,
    );

    let pre_suggestion = RepairSuggestion::new(
        RepairKind::StrengthenPrecondition,
        pre_description,
        RepairAction::Description(format!(
            "Add additional constraints to the precondition of '{}' \
             that exclude the configuration(s) leading to the violation. \
             The witness trace identifies the specific path to guard against.",
            result.property,
        )),
    )
    .with_confidence(0.7)
    .with_edit_cost(2)
    .with_alternatives(2);

    repairs.add(pre_suggestion);

    // Suggestion 2: Weaken the postcondition.
    let post_description = format!(
        "Weaken postcondition for property '{}' to accommodate observed behavior ({})",
        result.property, witness_context,
    );

    let post_suggestion = RepairSuggestion::new(
        RepairKind::WeakenPostcondition,
        post_description,
        RepairAction::Description(format!(
            "Relax the postcondition of '{}' so that the observed behavior \
             at the witness trace is within the acceptable range. \
             Verify that this relaxation does not mask genuine bugs.",
            result.property,
        )),
    )
    .with_confidence(0.6)
    .with_edit_cost(2)
    .with_alternatives(2);

    repairs.add(post_suggestion);

    repairs
}

/// Pipeline bridge: run safety verification against WPDS-dead rules.
///
/// Builds a bad-state automaton from WPDS-unreachable rules, then checks
/// whether any bad states are reachable via `check_safety`.
///
/// Returns `None` when there are no unreachable rules (nothing to verify).
/// Otherwise returns `Some(SafetyResult<BooleanWeight>)` indicating whether
/// the unreachable rules are truly unreachable (safe) or whether the initial
/// configuration can reach one of them (unsafe).
pub fn verify_from_bundle(
    wpds_analysis: &crate::wpds::WpdsAnalysis,
    _categories: &[crate::pipeline::CategoryInfo],
    _all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Option<SafetyResult<crate::automata::semiring::BooleanWeight>> {
    use crate::automata::semiring::BooleanWeight;

    if wpds_analysis.unreachable_rules.is_empty() {
        return None;
    }

    // Build a minimal WPDS containing stack symbols for all unreachable rules.
    // Each unreachable rule becomes a category-entry stack symbol so
    // `build_bad_state_automaton` can match on its category.
    let mut stack_symbols = Vec::new();
    let mut symbol_index = std::collections::HashMap::new();

    // Always include a root symbol derived from the grammar name.
    let root_sym = StackSymbol::category_entry(&wpds_analysis.grammar_name);
    symbol_index.insert(root_sym.clone(), 0);
    stack_symbols.push(root_sym.clone());

    for ur in &wpds_analysis.unreachable_rules {
        let sym = StackSymbol::rule_position(&ur.category, &ur.rule_label, 0);
        if !symbol_index.contains_key(&sym) {
            let idx = stack_symbols.len();
            symbol_index.insert(sym.clone(), idx);
            stack_symbols.push(sym);
        }
    }

    let wpds = Wpds::<BooleanWeight> {
        stack_symbols,
        symbol_index,
        rules: Vec::new(),
        rules_by_source: std::collections::HashMap::new(),
        initial_symbol: root_sym,
        grammar_name: wpds_analysis.grammar_name.clone(),
    };

    // Collect unreachable rule labels for the bad-state automaton.
    let bad_labels: Vec<&str> = wpds_analysis
        .unreachable_rules
        .iter()
        .map(|r| r.rule_label.as_str())
        .collect();

    let bad_automaton = build_bad_state_automaton(&wpds, &bad_labels);
    Some(check_safety(&wpds, &bad_automaton))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::BooleanWeight;

    #[test]
    fn test_verdict_display() {
        assert_eq!(Verdict::Verified.to_string(), "VERIFIED");
        assert_eq!(Verdict::Violated.to_string(), "VIOLATED");
        assert_eq!(Verdict::Unknown.to_string(), "UNKNOWN");
    }

    /// A WPDS whose rules are the three kinds a real grammar produces.
    ///
    /// Shape — the smallest grammar that dispatches, recurses, and returns:
    ///
    /// ```text
    ///   ⟨p, Expr⟩     ↪ ⟨p, NumLit@0⟩        Replace  (dispatch to the leaf rule)
    ///   ⟨p, NumLit@0⟩ ↪ ⟨p, ε⟩               Pop      (leaf consumes its token, returns)
    ///   ⟨p, Expr⟩     ↪ ⟨p, Add@0⟩           Replace  (dispatch to the binary rule)
    ///   ⟨p, Add@0⟩    ↪ ⟨p, Add@1 Expr⟩      Push     (call Expr; Add@1 is the return site)
    ///   ⟨p, Add@1⟩    ↪ ⟨p, ε⟩               Pop      (binary rule returns)
    /// ```
    ///
    /// Every rule kind matters to the invariant below. `Pop` is what makes prestar's
    /// Phase 1 seed `(p, γ, p)` — a transition BACK to the non-accepting initial
    /// state — and `Replace` is what propagates that self-loop onto the initial
    /// symbol. A WPDS with `rules: Vec::new()` has neither, which is exactly why the
    /// previous form of `test_empty_bad_states_is_safe` could not fail: it was
    /// quantified over the one case in which the defect cannot arise.
    fn wpds_with_rules_of_every_kind() -> Wpds<BooleanWeight> {
        use crate::wpds::WpdsRule;

        let expr = StackSymbol::category_entry("Expr");
        let numlit = StackSymbol::rule_position("Expr", "NumLit", 0);
        let add0 = StackSymbol::rule_position("Expr", "Add", 0);
        let add1 = StackSymbol::rule_position("Expr", "Add", 1);

        let mut wpds: Wpds<BooleanWeight> = Wpds {
            stack_symbols: Vec::new(),
            symbol_index: std::collections::HashMap::new(),
            rules: Vec::new(),
            rules_by_source: std::collections::HashMap::new(),
            initial_symbol: expr.clone(),
            grammar_name: "empty_bad_set_invariant".to_string(),
        };
        for sym in [&expr, &numlit, &add0, &add1] {
            wpds.ensure_symbol(sym.clone());
        }

        wpds.add_rule(WpdsRule::Replace {
            from_gamma: expr.clone(),
            to_gamma: numlit.clone(),
            weight: BooleanWeight::one(),
        });
        wpds.add_rule(WpdsRule::Pop {
            from_gamma: numlit,
            weight: BooleanWeight::one(),
        });
        wpds.add_rule(WpdsRule::Replace {
            from_gamma: expr.clone(),
            to_gamma: add0.clone(),
            weight: BooleanWeight::one(),
        });
        wpds.add_rule(WpdsRule::Push {
            from_gamma: add0,
            to_gamma_bottom: add1.clone(),
            to_gamma_top: expr,
            weight: BooleanWeight::one(),
        });
        wpds.add_rule(WpdsRule::Pop {
            from_gamma: add1,
            weight: BooleanWeight::one(),
        });

        wpds
    }

    /// `pre*(∅) = ∅`, so a WPDS **with rules** is safe against an empty bad set.
    ///
    /// The verdict is a set-membership question: is the initial configuration in the
    /// set of configurations from which a bad one is reachable? When the bad set is
    /// empty that set is empty too, whatever the rules do — no saturation step can
    /// place a configuration in the pre-image of nothing.
    #[test]
    fn test_empty_bad_states_is_safe() {
        let wpds = wpds_with_rules_of_every_kind();

        // The precondition the previous form of this test lacked. Without rules there
        // is no saturation, so no over-counted transition can exist to be miscounted.
        assert_eq!(wpds.rules.len(), 5, "the invariant is only non-trivial for a WPDS WITH rules");

        let bad = build_bad_state_automaton(&wpds, &[]);
        assert!(
            bad.transitions.is_empty(),
            "an empty label list must encode the EMPTY configuration set"
        );

        let result = check_safety(&wpds, &bad);
        assert!(
            result.safe,
            "pre*(∅) is empty, so no initial configuration can be in it; got unsafe with \
             witness {:?}",
            result.witness_trace
        );
        assert!(result.witness_trace.is_empty());
    }

    /// ★ The **executed reddening leg** for `test_empty_bad_states_is_safe`.
    ///
    /// The test above pins the repaired verdict, but on its own it cannot distinguish
    /// the repaired `symbol_weight` from the defective one *by execution* — it only
    /// records, in prose, that the defective one used to answer differently. That is
    /// the shape of an un-failable guard: swap the two accessors inside `check_safety`
    /// and the prose stays true while the code goes wrong.
    ///
    /// It does not have to stay that way here, because **the pre-fix expression is
    /// still public**. `symbol_weight`'s body before `8fc3f7a1` summed every
    /// out-transition regardless of target; that is verbatim what
    /// [`PAutomaton::stack_top_weight`](crate::wpds::PAutomaton::stack_top_weight)
    /// computes today, kept for the five liveness callers that genuinely want the
    /// over-approximation. So the DEFECTIVE decision procedure can simply be RUN, on
    /// the exact datum that produced the defect, and shown to return the wrong answer
    /// — no reimplementation, no mutation of production code, no mock.
    ///
    /// | leg     | bad set          | `stack_top_weight` (pre-fix) | `symbol_weight` (post-fix) |
    /// |---------|------------------|------------------------------|----------------------------|
    /// | risky   | `∅`              | non-zero ⇒ UNSAFE ✗          | zero ⇒ safe ✓              |
    /// | control | `{Add@0, Add@1}` | non-zero ⇒ unsafe ✓          | non-zero ⇒ unsafe ✓        |
    ///
    /// Divergence on the risky shape **and** agreement on the control together pin
    /// WHICH clause does the rejecting — the `final_states.contains(&t.to)` conjunct,
    /// and nothing else:
    ///
    /// - drop that conjunct (i.e. read `stack_top_weight` where `symbol_weight`
    ///   belongs) and the risky leg's post-fix assertion fails;
    /// - make it reject unconditionally (`symbol_weight ≡ zero`) and the control leg's
    ///   post-fix assertion fails.
    ///
    /// Neither accessor can absorb the other while both legs are green, which is
    /// exactly the claim `test_empty_bad_states_is_safe` needs and cannot make alone.
    #[test]
    fn the_empty_bad_set_guard_can_go_red() {
        let wpds = wpds_with_rules_of_every_kind();
        let gamma0 = wpds.initial_symbol.clone();

        // ── Risky leg: the empty bad set, the datum that produced the defect. ──
        let empty_bad = build_bad_state_automaton(&wpds, &[]);
        assert!(empty_bad.transitions.is_empty(), "the risky leg's bad set must be empty");
        let risky = crate::wpds::prestar(&wpds, &empty_bad);

        // Saturation really did fire — otherwise there is nothing to over-count and
        // the two accessors would agree for an uninteresting reason (N2: the
        // observation came from the real saturation, not from an empty automaton).
        let out_edges: Vec<_> = risky
            .transitions_by_source
            .get(&risky.initial_state)
            .map(|idx| idx.iter().map(|&i| &risky.transitions[i]).collect())
            .unwrap_or_default();
        let gamma0_edges: Vec<_> = out_edges.iter().filter(|t| t.symbol == gamma0).collect();
        assert!(
            !gamma0_edges.is_empty(),
            "prestar must have saturated at least one transition on ⟨p, {gamma0:?}⟩ for the \
             two accessors to be able to disagree; got out-edges {out_edges:?}"
        );

        // The clause under test, read directly off the datum: every transition on γ₀
        // targets a NON-final state. `stack_top_weight` counts them, `symbol_weight`
        // discards them, and that is the entire difference between the two.
        assert!(
            gamma0_edges
                .iter()
                .all(|t| !risky.final_states.contains(&t.to)),
            "the defect is that saturation seeds ⟨p, γ₀⟩-transitions to non-accepting \
             targets; if any target here were final the legs below would agree for the \
             wrong reason. Edges: {gamma0_edges:?}, final states: {:?}",
            risky.final_states
        );

        assert!(
            !risky.stack_top_weight(&gamma0).is_zero(),
            "PRE-FIX: summing every out-transition regardless of target must still \
             report ⟨p, γ₀⟩ as reachable — this is the wrong answer that shipped, and \
             if it ever became zero this leg would stop testing anything"
        );
        assert!(
            risky.symbol_weight(&gamma0).is_zero(),
            "POST-FIX: requiring an accepting target must report ⟨p, γ₀⟩ as NOT in \
             pre*(∅). Non-zero here means the final-state conjunct was lost."
        );

        // ── Control leg: a bad set that really is reachable. ──
        // Both accessors must now agree, so the divergence above is attributable to
        // the empty-bad-set shape and not to `symbol_weight` rejecting everything.
        let real_bad = build_bad_state_automaton(&wpds, &["Add"]);
        assert!(!real_bad.transitions.is_empty(), "the control leg's bad set must be non-empty");
        let control = crate::wpds::prestar(&wpds, &real_bad);

        assert!(
            !control.stack_top_weight(&gamma0).is_zero(),
            "PRE-FIX on the control: ⟨p, Expr⟩ ↪ ⟨p, Add@0⟩ is one step from the bad set"
        );
        assert!(
            !control.symbol_weight(&gamma0).is_zero(),
            "POST-FIX on the control: the repaired accessor must AGREE with the \
             pre-fix one whenever an accepting target exists. Zero here means the fix \
             degenerated into a blanket `safe`."
        );

        // And the reason it agrees: on the control there IS an accepting target, so
        // the conjunct that rejected the risky leg is satisfiable rather than dead.
        let control_edges: Vec<_> = control
            .transitions_by_source
            .get(&control.initial_state)
            .map(|idx| {
                idx.iter()
                    .map(|&i| &control.transitions[i])
                    .filter(|t| t.symbol == gamma0)
                    .collect()
            })
            .unwrap_or_default();
        assert!(
            control_edges
                .iter()
                .any(|t| control.final_states.contains(&t.to)),
            "the control leg must exercise the accepting branch of the very conjunct \
             that rejected the risky leg; edges {control_edges:?}, final states {:?}",
            control.final_states
        );
    }

    /// The converse, so the fix above cannot be a blanket "always safe".
    ///
    /// `⟨p, Expr⟩ ↪ ⟨p, Add@0⟩` puts a bad configuration one step from the initial one,
    /// so the verdict must be UNSAFE and must carry a witness. A `symbol_weight` that
    /// returned zero unconditionally would satisfy the empty-bad-set test and fail this.
    #[test]
    fn test_reachable_bad_state_is_reported_unsafe() {
        let wpds = wpds_with_rules_of_every_kind();

        let bad = build_bad_state_automaton(&wpds, &["Add"]);
        assert!(
            !bad.transitions.is_empty(),
            "the label `Add` matches the Add@0/Add@1 rule positions"
        );

        let result = check_safety(&wpds, &bad);
        assert!(!result.safe, "⟨p, Expr⟩ ↪ ⟨p, Add@0⟩ reaches the bad set in one step");
        assert!(
            !result.witness_trace.is_empty(),
            "an unsafe verdict must name the path it found"
        );
    }

    #[test]
    fn test_safety_result_fields() {
        let result: SafetyResult<BooleanWeight> = SafetyResult {
            safe: true,
            initial_weight: BooleanWeight(false),
            witness_trace: Vec::new(),
        };
        assert!(result.safe);
        assert!(result.initial_weight.is_zero());
    }

    #[test]
    fn test_bad_state_automaton_construction() {
        let wpds: Wpds<BooleanWeight> = Wpds {
            stack_symbols: vec![
                StackSymbol::category_entry("Expr"),
                StackSymbol::rule_position("Expr", "BadRule", 0),
            ],
            symbol_index: {
                let mut m = std::collections::HashMap::new();
                m.insert(StackSymbol::category_entry("Expr"), 0);
                m.insert(StackSymbol::rule_position("Expr", "BadRule", 0), 1);
                m
            },
            rules: Vec::new(),
            rules_by_source: std::collections::HashMap::new(),
            initial_symbol: StackSymbol::category_entry("Expr"),
            grammar_name: "test".to_string(),
        };

        let bad = build_bad_state_automaton(&wpds, &["BadRule"]);
        // Should have a transition for the BadRule stack symbol.
        assert!(!bad.transitions.is_empty());
        assert!(bad.final_states.len() == 1);
    }

    // ──────────────────────────────────────────────────────────────────────
    // Tests for suggest_safety_repairs
    // ──────────────────────────────────────────────────────────────────────

    #[test]
    fn test_suggest_safety_repairs_safe_result_returns_empty() {
        let wpds: Wpds<BooleanWeight> = Wpds {
            stack_symbols: vec![StackSymbol::category_entry("Expr")],
            symbol_index: {
                let mut m = std::collections::HashMap::new();
                m.insert(StackSymbol::category_entry("Expr"), 0);
                m
            },
            rules: Vec::new(),
            rules_by_source: std::collections::HashMap::new(),
            initial_symbol: StackSymbol::category_entry("Expr"),
            grammar_name: "test_safe".to_string(),
        };

        let safe_result = SafetyResult {
            safe: true,
            initial_weight: BooleanWeight(false),
            witness_trace: Vec::new(),
        };

        let repairs = suggest_safety_repairs(&safe_result, &wpds);
        assert!(
            repairs.suggestions.is_empty(),
            "safe result should produce no repair suggestions"
        );
    }

    #[test]
    fn test_suggest_safety_repairs_unsafe_with_witness_trace() {
        let wpds: Wpds<BooleanWeight> = Wpds {
            stack_symbols: vec![
                StackSymbol::category_entry("Expr"),
                StackSymbol::rule_position("Expr", "Add", 0),
                StackSymbol::rule_position("Expr", "Add", 1),
            ],
            symbol_index: {
                let mut m = std::collections::HashMap::new();
                m.insert(StackSymbol::category_entry("Expr"), 0);
                m.insert(StackSymbol::rule_position("Expr", "Add", 0), 1);
                m.insert(StackSymbol::rule_position("Expr", "Add", 1), 2);
                m
            },
            rules: Vec::new(),
            rules_by_source: std::collections::HashMap::new(),
            initial_symbol: StackSymbol::category_entry("Expr"),
            grammar_name: "test_unsafe".to_string(),
        };

        let unsafe_result = SafetyResult {
            safe: false,
            initial_weight: BooleanWeight(true),
            witness_trace: vec![
                StackSymbol::category_entry("Expr"),
                StackSymbol::rule_position("Expr", "Add", 0),
                StackSymbol::rule_position("Expr", "Add", 1),
            ],
        };

        let repairs = suggest_safety_repairs(&unsafe_result, &wpds);

        // 3 per-step guard suggestions + 1 restrict-initial-config = 4 total.
        assert_eq!(
            repairs.suggestions.len(),
            4,
            "expected 3 guard suggestions + 1 restrict suggestion"
        );

        // Verify per-step guard suggestions have increasing edit cost.
        for (i, suggestion) in repairs.suggestions[..3].iter().enumerate() {
            assert_eq!(
                suggestion.kind,
                RepairKind::FixTermination,
                "step {} should be FixTermination",
                i
            );
            assert_eq!(
                suggestion.edit_cost,
                (i as u32) + 1,
                "edit cost should increase with trace position"
            );
            assert_eq!(suggestion.alternative_count, 3, "alternatives should equal trace length");
            assert!(
                suggestion.description.contains("test_unsafe"),
                "description should include grammar name"
            );
        }

        // Verify restrict-initial-config suggestion.
        let restrict = &repairs.suggestions[3];
        assert_eq!(restrict.kind, RepairKind::Custom("RestrictInitialConfig".to_string()),);
        assert_eq!(restrict.edit_cost, 3);
        assert!((restrict.confidence - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_suggest_safety_repairs_confidence_scales_with_trace_length() {
        let wpds: Wpds<BooleanWeight> = Wpds {
            stack_symbols: vec![StackSymbol::category_entry("X")],
            symbol_index: {
                let mut m = std::collections::HashMap::new();
                m.insert(StackSymbol::category_entry("X"), 0);
                m
            },
            rules: Vec::new(),
            rules_by_source: std::collections::HashMap::new(),
            initial_symbol: StackSymbol::category_entry("X"),
            grammar_name: "conf_test".to_string(),
        };

        // Single-step trace → confidence = 1.0 (clamped).
        let short_result = SafetyResult {
            safe: false,
            initial_weight: BooleanWeight(true),
            witness_trace: vec![StackSymbol::category_entry("X")],
        };
        let short_repairs = suggest_safety_repairs(&short_result, &wpds);
        assert!(
            (short_repairs.suggestions[0].confidence - 1.0).abs() < f64::EPSILON,
            "single-step trace should have confidence 1.0"
        );

        // 10-step trace → confidence = 0.1 (clamped lower bound).
        let long_trace: Vec<StackSymbol> = (0..10)
            .map(|i| StackSymbol::rule_position("X", "R", i))
            .collect();
        let long_result = SafetyResult {
            safe: false,
            initial_weight: BooleanWeight(true),
            witness_trace: long_trace,
        };
        let long_repairs = suggest_safety_repairs(&long_result, &wpds);
        assert!(
            (long_repairs.suggestions[0].confidence - 0.1).abs() < f64::EPSILON,
            "10-step trace should have confidence 0.1"
        );
    }

    // ──────────────────────────────────────────────────────────────────────
    // Tests for suggest_invariant_strengthening
    // ──────────────────────────────────────────────────────────────────────

    #[test]
    fn test_suggest_invariant_strengthening_verified_returns_empty() {
        let verified_result: VerificationResult<BooleanWeight> = VerificationResult {
            verdict: Verdict::Verified,
            property: "no-deadlock".to_string(),
            weight: BooleanWeight(false),
            witness: Vec::new(),
        };

        let repairs = suggest_invariant_strengthening(&verified_result);
        assert!(
            repairs.suggestions.is_empty(),
            "verified result should produce no repair suggestions"
        );

        // Also check Unknown verdict.
        let unknown_result: VerificationResult<BooleanWeight> = VerificationResult {
            verdict: Verdict::Unknown,
            property: "may-terminate".to_string(),
            weight: BooleanWeight(false),
            witness: Vec::new(),
        };
        let unknown_repairs = suggest_invariant_strengthening(&unknown_result);
        assert!(
            unknown_repairs.suggestions.is_empty(),
            "unknown result should produce no repair suggestions"
        );
    }

    #[test]
    fn test_suggest_invariant_strengthening_violated_produces_two_suggestions() {
        let violated_result: VerificationResult<BooleanWeight> = VerificationResult {
            verdict: Verdict::Violated,
            property: "safety-invariant".to_string(),
            weight: BooleanWeight(true),
            witness: vec![
                StackSymbol::category_entry("Expr"),
                StackSymbol::rule_position("Expr", "BadOp", 0),
            ],
        };

        let repairs = suggest_invariant_strengthening(&violated_result);
        assert_eq!(
            repairs.suggestions.len(),
            2,
            "violated result should produce exactly 2 suggestions"
        );

        // First: StrengthenPrecondition.
        let pre = &repairs.suggestions[0];
        assert_eq!(pre.kind, RepairKind::StrengthenPrecondition);
        assert!((pre.confidence - 0.7).abs() < f64::EPSILON);
        assert_eq!(pre.edit_cost, 2);
        assert!(
            pre.description.contains("safety-invariant"),
            "description should include property name"
        );
        assert!(
            pre.description.contains("witness trace"),
            "description should reference the witness trace"
        );

        // Second: WeakenPostcondition.
        let post = &repairs.suggestions[1];
        assert_eq!(post.kind, RepairKind::WeakenPostcondition);
        assert!((post.confidence - 0.6).abs() < f64::EPSILON);
        assert_eq!(post.edit_cost, 2);
        assert!(
            post.description.contains("safety-invariant"),
            "description should include property name"
        );
    }

    fn make_empty_wpds_analysis() -> crate::wpds::WpdsAnalysis {
        use std::collections::{HashMap, HashSet};
        crate::wpds::WpdsAnalysis {
            grammar_name: "test".to_string(),
            num_symbols: 0,
            num_rules: 0,
            reachable_categories: HashSet::new(),
            unreachable_rules: Vec::new(),
            category_weights: HashMap::new(),
            call_graph: crate::wpds::WpdsCallGraph {
                edges: Vec::new(),
                fan_out: HashMap::new(),
                fan_in: HashMap::new(),
                sccs: Vec::new(),
                categories: HashSet::new(),
            },
            depth_bounds: HashMap::new(),
            cycles: Vec::new(),
            calling_contexts: HashMap::new(),
            context_rule_tables: HashMap::new(),
            cross_category_bp: HashMap::new(),
            context_unambiguous: HashMap::new(),
            cek_bijection: crate::wpds::CekWpdsBijection::default(),
            pautomaton: crate::wpds::PAutomaton::new(0),
        }
    }

    #[test]
    fn test_verify_from_bundle_with_unreachable() {
        let mut wpds_analysis = make_empty_wpds_analysis();
        wpds_analysis
            .unreachable_rules
            .push(crate::wpds::WpdsUnreachableRule {
                rule_label: "DeadRule".to_string(),
                category: "Expr".to_string(),
                missing_contexts: vec!["Main".to_string()],
                witness_trace: vec!["Main".to_string(), "Expr".to_string()],
            });
        let cats = vec![crate::pipeline::CategoryInfo {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
            has_var: true,
        }];
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "DeadRule".to_string(),
            "Expr".to_string(),
            vec![crate::SyntaxItemSpec::Terminal("+".to_string())],
        )];
        let result = verify_from_bundle(&wpds_analysis, &cats, &syntax);
        assert!(
            result.is_some(),
            "should return Some(SafetyResult) when unreachable rules exist"
        );
    }

    #[test]
    fn test_verify_from_bundle_no_unreachable() {
        let wpds_analysis = make_empty_wpds_analysis();
        let cats = vec![crate::pipeline::CategoryInfo {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
            has_var: true,
        }];
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];
        let result = verify_from_bundle(&wpds_analysis, &cats, &syntax);
        assert!(result.is_none(), "should return None when no unreachable rules");
    }
}
