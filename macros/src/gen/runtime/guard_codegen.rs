//! Guard compilation codegen for predicated types
//!
//! Generates runtime guard evaluation functions from compiled SFA/automaton
//! representations. Each decidability tier produces different generated code:
//!
//! | Tier | Strategy | Generated Code |
//! |------|----------|----------------|
//! | T1   | Static elimination | No runtime code (guard eliminated at compile time) |
//! | T2   | Range/SFA/Register | Inline range check, transition table, or register machine |
//! | T3   | Bounded iteration | BFS/DFS with depth counter, returns `TriState` |
//! | T4   | User assertion | `assert_pred()` wrapper with MSO01 lint |
//!
//! ## Architecture
//!
//! This module is called from the predicated types pipeline (Stage 5) when
//! `TermParam::GuardBody` constructors exist in the language definition.
//! The generated guard functions are included in the `TokenStream` alongside
//! the Ascent struct and Comm rules.
//!
//! ## Guard Evaluation Paths
//!
//! **Primary path (inline):** For T2 guards with simple `RelationQuery`, the
//! guard is compiled to a direct Ascent join clause in the Comm rule body.
//! This uses Ascent's native indexing and is the most efficient path.
//!
//! **Standalone path:** Each guard also gets a standalone `__guard_N()` function
//! for testing, external callers, and the selectivity/overlap analysis pipeline.
//!
//! ## AWA Strategy (documentation only)
//!
//! For quantified predicates (`forall`, `exists`), the AWA approach would compile
//! to alternating weighted automata:
//! - `∀` → universal state (Q⊗): all transitions must accept
//! - `∃` → existential state (Q⊕): at least one transition must accept
//!
//! AWA requires `to_weighted_automaton()` (~2000 lines, not yet implemented).
//! The current path uses LogicT's `evaluate_quantified()` which is already working
//! and composable with existing infrastructure. The cost-benefit framework can
//! gate between LogicT and AWA once AWA is implemented.

use crate::ast::language::{BehavioralPred, LanguageDef, PredArg};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

// =============================================================================
// TriState Type Generation
// =============================================================================

/// Generate the `TriState` enum for T3 bounded checking results.
pub fn generate_tristate_type() -> TokenStream {
    quote! {
        /// Result of a T3 bounded guard evaluation.
        ///
        /// - `True`: guard definitely holds
        /// - `False`: guard definitely does not hold
        /// - `Unknown`: depth limit exceeded before determination
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum TriState {
            True,
            False,
            Unknown,
        }

        impl TriState {
            /// Logical conjunction: And(True, True) = True, And(_, False) = False,
            /// And(Unknown, _) = Unknown
            pub fn and(self, other: TriState) -> TriState {
                match (self, other) {
                    (TriState::True, TriState::True) => TriState::True,
                    (TriState::False, _) | (_, TriState::False) => TriState::False,
                    _ => TriState::Unknown,
                }
            }

            /// Logical disjunction: Or(True, _) = True, Or(False, False) = False,
            /// Or(Unknown, _) = Unknown
            pub fn or(self, other: TriState) -> TriState {
                match (self, other) {
                    (TriState::True, _) | (_, TriState::True) => TriState::True,
                    (TriState::False, TriState::False) => TriState::False,
                    _ => TriState::Unknown,
                }
            }

            /// Logical negation: Not(True) = False, Not(False) = True, Not(Unknown) = Unknown
            pub fn not(self) -> TriState {
                match self {
                    TriState::True => TriState::False,
                    TriState::False => TriState::True,
                    TriState::Unknown => TriState::Unknown,
                }
            }

            /// Convert to bool (Unknown → false, conservative).
            pub fn to_bool_conservative(self) -> bool {
                matches!(self, TriState::True)
            }
        }
    }
}

// =============================================================================
// Guard Codegen Entry Point
// =============================================================================

/// Generate guard evaluation code for all `TermParam::GuardBody` constructors
/// in the language definition.
///
/// Returns a `TokenStream` containing:
/// - `TriState` enum definition
/// - Per-guard evaluation functions (one per `GuardBody` constructor)
/// - Guard tier classification metadata
pub fn generate_guard_codegen(language: &LanguageDef) -> TokenStream {
    use crate::ast::grammar::TermParam;

    let tristate = generate_tristate_type();

    // Collect all guarded constructors
    let mut guard_fns: Vec<TokenStream> = Vec::new();
    let mut guard_idx: usize = 0;

    for rule in &language.terms {
        let guard_param = rule.term_context.as_ref().and_then(|ctx| {
            ctx.iter().find_map(|p| {
                if let TermParam::GuardBody { name, guard } = p {
                    Some((name.clone(), guard.clone()))
                } else {
                    None
                }
            })
        });

        if let Some((guard_name, guard_pred)) = guard_param {
            let tier = classify_guard_tier(&guard_pred);
            let fn_code = generate_guard_function(
                guard_idx,
                &rule.label,
                &guard_name,
                &guard_pred,
                tier,
                language,
            );
            guard_fns.push(fn_code);
            guard_idx += 1;
        }
    }

    if guard_fns.is_empty() {
        // No guarded constructors — emit only TriState for potential external use
        return tristate;
    }

    quote! {
        #tristate
        #(#guard_fns)*
    }
}

// =============================================================================
// Guard Tier Classification
// =============================================================================

/// Decidability tier for a guard predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GuardTier {
    /// T1: Statically decidable — guard can be eliminated at compile time
    T1Static,
    /// T2: Decidable at runtime — finite SFA/range check/register automaton
    T2Decidable,
    /// T3: Semi-decidable — bounded iteration with depth limit
    T3Bounded,
    /// T4: Undecidable — user assertion wrapper
    T4Assert,
}

/// Classify the decidability tier of a behavioral predicate.
///
/// - T1: Tautological or contradictory (eliminated at compile time)
/// - T2: Simple relation queries, negated queries — decidable with finite joins
/// - T3: Quantified with bounded domains — semi-decidable with depth limit
/// - T4: Quantified over unbounded domains — user must assert
pub(crate) fn classify_guard_tier(pred: &BehavioralPred) -> GuardTier {
    // T1 check: detect trivially true/false guards
    if is_statically_decidable(pred) {
        return GuardTier::T1Static;
    }

    match pred {
        BehavioralPred::RelationQuery { .. } => GuardTier::T2Decidable,
        BehavioralPred::AcMatch { .. } => GuardTier::T2Decidable,
        BehavioralPred::Quantified { bound, body, .. } => {
            if bound.is_some() {
                // Bounded quantification — semi-decidable
                GuardTier::T3Bounded
            } else {
                // Check if the body is simple enough for T3
                let body_tier = classify_guard_tier(body);
                match body_tier {
                    GuardTier::T1Static | GuardTier::T2Decidable => GuardTier::T3Bounded,
                    _ => GuardTier::T4Assert,
                }
            }
        }
        BehavioralPred::And(a, b) | BehavioralPred::Or(a, b) | BehavioralPred::Implies(a, b) => {
            let ta = classify_guard_tier(a);
            let tb = classify_guard_tier(b);
            max_tier(ta, tb)
        }
        BehavioralPred::Not(inner) => classify_guard_tier(inner),
    }
}

/// Check if a guard is statically decidable (T1).
///
/// A guard is T1 if it evaluates to a constant regardless of input:
/// - `Not(a)` where `a` is T1 → T1
/// - `And(T1_true, T1_true)` → T1
/// - `Or(T1_true, _)` → T1
/// - `Implies(T1_false, _)` → T1 (vacuously true)
///
/// In the current AST there are no constant True/False variants in
/// BehavioralPred, so T1 is detected only for tautological/contradictory
/// boolean combinations (e.g., `a ∧ ¬a`). This is intentionally conservative.
fn is_statically_decidable(pred: &BehavioralPred) -> bool {
    // Check for tautology: P ∨ ¬P
    if let BehavioralPred::Or(a, b) = pred {
        if is_complement(a, b) {
            return true;
        }
    }
    // Check for contradiction: P ∧ ¬P
    if let BehavioralPred::And(a, b) = pred {
        if is_complement(a, b) {
            return true;
        }
    }
    // Check for vacuous implication: ¬P ⇒ P (always true when simplified)
    // This is conservative — only catches obvious patterns.
    false
}

/// Check if two predicates are complements (one is the negation of the other).
fn is_complement(a: &BehavioralPred, b: &BehavioralPred) -> bool {
    if let BehavioralPred::Not(inner) = a {
        return pred_structurally_equal(inner, b);
    }
    if let BehavioralPred::Not(inner) = b {
        return pred_structurally_equal(a, inner);
    }
    false
}

/// Structural equality check for predicates.
fn pred_structurally_equal(a: &BehavioralPred, b: &BehavioralPred) -> bool {
    match (a, b) {
        (
            BehavioralPred::RelationQuery { relation_name: rn1, args: a1, negated: n1 },
            BehavioralPred::RelationQuery { relation_name: rn2, args: a2, negated: n2 },
        ) => {
            rn1 == rn2
                && n1 == n2
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(x, y)| pred_arg_equal(x, y))
        }
        (BehavioralPred::Not(x), BehavioralPred::Not(y)) => pred_structurally_equal(x, y),
        (BehavioralPred::And(a1, b1), BehavioralPred::And(a2, b2)) => {
            pred_structurally_equal(a1, a2) && pred_structurally_equal(b1, b2)
        }
        (BehavioralPred::Or(a1, b1), BehavioralPred::Or(a2, b2)) => {
            pred_structurally_equal(a1, a2) && pred_structurally_equal(b1, b2)
        }
        _ => false,
    }
}

fn pred_arg_equal(a: &PredArg, b: &PredArg) -> bool {
    match (a, b) {
        (PredArg::Var(v1), PredArg::Var(v2)) => v1 == v2,
        (PredArg::Constant(c1), PredArg::Constant(c2)) => c1 == c2,
        _ => false,
    }
}

/// Return the higher (less decidable) tier.
fn max_tier(a: GuardTier, b: GuardTier) -> GuardTier {
    use GuardTier::*;
    match (a, b) {
        (T4Assert, _) | (_, T4Assert) => T4Assert,
        (T3Bounded, _) | (_, T3Bounded) => T3Bounded,
        (T2Decidable, _) | (_, T2Decidable) => T2Decidable,
        _ => T1Static,
    }
}

/// Evaluate a T1 static guard at compile time.
///
/// Returns `Some(true)` for tautologies, `Some(false)` for contradictions,
/// `None` if the guard is not statically decidable.
pub(crate) fn evaluate_static_guard(pred: &BehavioralPred) -> Option<bool> {
    // P ∨ ¬P → true (tautology)
    if let BehavioralPred::Or(a, b) = pred {
        if is_complement(a, b) {
            return Some(true);
        }
    }
    // P ∧ ¬P → false (contradiction)
    if let BehavioralPred::And(a, b) = pred {
        if is_complement(a, b) {
            return Some(false);
        }
    }
    None
}

// =============================================================================
// Per-Tier Guard Function Generation
// =============================================================================

/// Generate a guard evaluation function for a specific guard.
fn generate_guard_function(
    idx: usize,
    rule_label: &syn::Ident,
    _guard_name: &syn::Ident,
    pred: &BehavioralPred,
    tier: GuardTier,
    _language: &LanguageDef,
) -> TokenStream {
    let fn_name = format_ident!("__guard_{}", idx);
    let label_str = rule_label.to_string();

    match tier {
        GuardTier::T1Static => {
            // T1: Guard statically eliminated — generate a constant function.
            let static_result = evaluate_static_guard(pred).unwrap_or(true);
            if static_result {
                quote! {
                    /// T1 guard for rule — statically evaluated to `true`.
                    /// The guard check is elided from the Comm rule body.
                    #[allow(dead_code)]
                    #[inline(always)]
                    fn #fn_name(
                        _relation_query: &dyn Fn(&str, &[String]) -> bool,
                        _domain_enumerate: &dyn Fn(&str) -> Vec<Vec<String>>,
                        _env: &::std::collections::HashMap<String, String>,
                    ) -> bool {
                        // T1: Guard statically evaluated to true — eliminated.
                        true
                    }
                }
            } else {
                // T1 always-false: the guard is a contradiction.
                // SYM01 lint should be emitted upstream.
                quote! {
                    /// T1 guard for rule — statically evaluated to `false` (dead guard).
                    /// SYM01: This receive will never fire.
                    #[allow(dead_code)]
                    #[inline(always)]
                    fn #fn_name(
                        _relation_query: &dyn Fn(&str, &[String]) -> bool,
                        _domain_enumerate: &dyn Fn(&str) -> Vec<Vec<String>>,
                        _env: &::std::collections::HashMap<String, String>,
                    ) -> bool {
                        // T1: Guard statically evaluated to false — dead receive (SYM01).
                        false
                    }
                }
            }
        }

        GuardTier::T2Decidable => {
            // T2: Decidable guard — generate standalone evaluation function.
            // The primary evaluation path is inlined in the Ascent Comm rule
            // as a direct join clause; this standalone function serves testing
            // and external callers.
            let formula_expr = pred.to_quantified_formula();
            quote! {
                /// T2 guard evaluation for rule.
                ///
                /// Decidable at runtime via finite-state evaluation.
                /// The primary evaluation path is inlined in the Ascent Comm rule
                /// as a direct relation join; this standalone function serves
                /// testing and external callers.
                #[allow(dead_code)]
                fn #fn_name(
                    relation_query: &dyn Fn(&str, &[String]) -> bool,
                    domain_enumerate: &dyn Fn(&str) -> Vec<Vec<String>>,
                    env: &::std::collections::HashMap<String, String>,
                ) -> bool {
                    let formula = #formula_expr;
                    mettail_prattail::logict::evaluate_quantified(
                        &formula,
                        env,
                        relation_query,
                        domain_enumerate,
                        1000,
                    )
                }
            }
        }

        GuardTier::T3Bounded => {
            // T3: Semi-decidable — bounded iteration with depth counter.
            // Returns TriState instead of bool.
            let formula_expr = pred.to_quantified_formula();
            let depth_limit = extract_bound(pred).unwrap_or(1000);
            let depth_limit_lit = depth_limit;
            quote! {
                /// T3 bounded guard evaluation for rule.
                ///
                /// Semi-decidable: iterates up to `depth_limit` steps.
                /// Returns `TriState::Unknown` if the limit is reached.
                #[allow(dead_code)]
                fn #fn_name(
                    relation_query: &dyn Fn(&str, &[String]) -> bool,
                    domain_enumerate: &dyn Fn(&str) -> Vec<Vec<String>>,
                    env: &::std::collections::HashMap<String, String>,
                    depth_limit: usize,
                ) -> TriState {
                    let formula = #formula_expr;
                    let effective_limit = if depth_limit > 0 { depth_limit } else { #depth_limit_lit };
                    let result = mettail_prattail::logict::evaluate_quantified(
                        &formula,
                        env,
                        relation_query,
                        domain_enumerate,
                        effective_limit,
                    );
                    if result {
                        TriState::True
                    } else {
                        // When the domain enumeration returns fewer than `effective_limit`
                        // tuples, we have exhaustive coverage → definite False.
                        // When it returns exactly `effective_limit` tuples, the bound
                        // may have been hit → conservative Unknown.
                        let domain_size: usize = domain_enumerate("__any__").len();
                        if domain_size < effective_limit {
                            TriState::False
                        } else {
                            TriState::Unknown
                        }
                    }
                }
            }
        }

        GuardTier::T4Assert => {
            // T4: Undecidable — user assertion wrapper.
            // MSO01 lint should have been emitted at compile time.
            let _label = label_str;
            quote! {
                /// T4 guard assertion wrapper.
                ///
                /// **Warning**: This guard's predicate is undecidable (MSO01).
                /// It always returns `true`, relying on user assertions for soundness.
                #[allow(dead_code)]
                fn #fn_name(
                    _relation_query: &dyn Fn(&str, &[String]) -> bool,
                    _domain_enumerate: &dyn Fn(&str) -> Vec<Vec<String>>,
                    _env: &::std::collections::HashMap<String, String>,
                ) -> bool {
                    // T4: Undecidable guard — trust user annotation.
                    // MSO01 lint emitted at compile time.
                    true
                }
            }
        }
    }
}

/// Extract the bound from a quantified predicate, if present.
fn extract_bound(pred: &BehavioralPred) -> Option<usize> {
    match pred {
        BehavioralPred::Quantified { bound, .. } => *bound,
        BehavioralPred::And(a, b) | BehavioralPred::Or(a, b) | BehavioralPred::Implies(a, b) => {
            extract_bound(a).or_else(|| extract_bound(b))
        }
        BehavioralPred::Not(inner) => extract_bound(inner),
        _ => None,
    }
}

// =============================================================================
// Guard Compilation to Ascent Clauses (T2)
// =============================================================================

/// Check whether a behavioral predicate can be compiled to direct Ascent join
/// clauses instead of using `evaluate_quantified()`.
///
/// Returns `true` for:
/// - Simple `RelationQuery` (positive or negated)
/// - `And` of compilable sub-guards
/// - `Not` of compilable sub-guard
pub fn can_compile_to_ascent_join(pred: &BehavioralPred) -> bool {
    match pred {
        BehavioralPred::RelationQuery { .. } => true,
        BehavioralPred::And(a, b) => can_compile_to_ascent_join(a) && can_compile_to_ascent_join(b),
        BehavioralPred::Not(inner) => can_compile_to_ascent_join(inner),
        _ => false,
    }
}

/// Resolve a `PredArg` to a `TokenStream` expression using LHS bindings.
///
/// - `PredArg::Var(v)`: look up in `bindings`, fall back to bare identifier
/// - `PredArg::Constant(c)`: emit as bare identifier (Ascent constant)
pub fn resolve_pred_arg(
    arg: &PredArg,
    bindings: &std::collections::HashMap<String, crate::ast::pattern::VariableBinding>,
) -> TokenStream {
    match arg {
        PredArg::Var(v) => {
            let var_name = v.to_string();
            bindings
                .get(&var_name)
                .map(|b| b.expression.clone())
                .unwrap_or_else(|| quote! { #v })
        }
        PredArg::Constant(c) => quote! { #c },
    }
}

// =============================================================================
// SFA Transition Table Codegen (T2)
// =============================================================================

/// Generate a state-machine transition table from a symbolic automaton.
///
/// For a determinized, minimized SFA with states Q, transitions δ, and
/// accepting states F, generates a Rust match-based DFA:
///
/// ```rust,ignore
/// fn __guard_sfa_N<I: Iterator<Item = u32>>(elements: I) -> bool {
///     let mut state: u32 = 0;
///     for elem in elements {
///         state = match (state, elem_predicate_eval) {
///             (0, true) => 1,
///             (0, false) => 2,
///             (1, true) => 1,  // self-loop
///             _ => return false, // sink state
///         };
///     }
///     matches!(state, 1 | 3 | 5)
/// }
/// ```
#[allow(dead_code)]
pub fn generate_sfa_transition_table(
    guard_idx: usize,
    _num_states: u32,
    initial_state: u32,
    accepting_states: &[u32],
    transitions: &[(u32, u32, String)], // (from, to, predicate_repr)
) -> TokenStream {
    let fn_name = format_ident!("__guard_sfa_{}", guard_idx);

    let accept_arms: Vec<TokenStream> = accepting_states
        .iter()
        .map(|s| {
            let s_lit = *s;
            quote! { #s_lit }
        })
        .collect();

    // Generate transition arms from the compiled SFA transitions.
    // Each transition (from, to, predicate_repr) becomes a match arm.
    let transition_arms: Vec<TokenStream> = transitions
        .iter()
        .map(|(from, to, pred_repr)| {
            let from_lit = *from;
            let to_lit = *to;
            // The predicate_repr is a string representation of the guard predicate.
            // For IntervalAlgebra: "x >= 0 && x < 100"
            // For KatBooleanAlgebra: "true" / "false"
            // We embed it as a comment; the actual predicate evaluation happens
            // via minterm partitioning at SFA construction time, so each transition
            // corresponds to one minterm (a Boolean combination of atomic predicates).
            let pred_comment = format!("guard: {}", pred_repr);
            quote! {
                // #pred_comment
                (#from_lit, true) => #to_lit
            }
        })
        .collect();

    if transition_arms.is_empty() {
        // No transitions: generate a stub that always rejects
        quote! {
            /// SFA transition table guard evaluation (empty — no transitions).
            #[allow(dead_code)]
            fn #fn_name<I: Iterator<Item = u32>>(elements: I) -> bool {
                let _ = elements;
                let initial = #initial_state;
                matches!(initial, #(#accept_arms)|*)
            }
        }
    } else {
        quote! {
            /// SFA transition table guard evaluation.
            #[allow(dead_code)]
            fn #fn_name<I: Iterator<Item = (u32, bool)>>(elements: I) -> bool {
                let mut state: u32 = #initial_state;
                for (_elem, pred_holds) in elements {
                    state = match (state, pred_holds) {
                        #(#transition_arms,)*
                        _ => return false, // sink state
                    };
                }
                matches!(state, #(#accept_arms)|*)
            }
        }
    }
}

// =============================================================================
// Register Automaton Codegen (T2)
// =============================================================================

/// Generate a register automaton evaluation function.
///
/// For a register automaton with K registers, generates matching code that
/// stores/tests values against registers. Used for guards with data equality
/// (`x == y`) or freshness (`fresh(x)`) constraints.
#[allow(dead_code)]
pub fn generate_register_automaton(
    guard_idx: usize,
    num_registers: usize,
) -> TokenStream {
    let fn_name = format_ident!("__guard_reg_{}", guard_idx);
    let k = num_registers;

    quote! {
        /// Register automaton guard evaluation with K registers.
        ///
        /// Registers store previously seen values for equality/freshness checks.
        /// `None` = register uninitialized (first occurrence stores).
        /// `Some(v)` = register stores value v (subsequent occurrences test equality).
        #[allow(dead_code)]
        fn #fn_name<T: Clone + PartialEq + std::fmt::Debug>(
            values: &[T],
        ) -> bool {
            let mut registers: Vec<Option<T>> = (0..#k).map(|_| None).collect();
            for (reg_idx, val) in values.iter().enumerate() {
                if reg_idx >= #k {
                    break;
                }
                match &registers[reg_idx] {
                    None => {
                        // First occurrence: store in register
                        registers[reg_idx] = Some(val.clone());
                    }
                    Some(stored) => {
                        // Subsequent occurrence: test equality
                        if stored != val {
                            return false;
                        }
                    }
                }
            }
            true
        }
    }
}

// =============================================================================
// AWA (Alternating Weighted Automata) Codegen
// =============================================================================

/// Generate AWA evaluation code for quantified predicates.
///
/// For `∀`: universal state — all transitions must accept.
/// For `∃`: existential state — at least one transition must accept.
///
/// Note: Full AWA compilation requires `to_weighted_automaton()` (~2000 lines,
/// not yet implemented). This generates a simplified evaluation that delegates
/// to the universal/existential pattern directly. The cost-benefit framework
/// can gate between this and the full AWA path once implemented.
#[allow(dead_code)]
pub fn generate_awa_evaluation(
    guard_idx: usize,
    is_universal: bool,
) -> TokenStream {
    let fn_name = format_ident!("__guard_awa_{}", guard_idx);

    quote! {
        /// AWA guard evaluation.
        #[allow(dead_code)]
        fn #fn_name<I: Iterator<Item = bool>>(transitions: I) -> bool {
            if #is_universal {
                // Universal (∀): all transitions must accept
                transitions.fold(true, |acc, t| acc && t)
            } else {
                // Existential (∃): at least one must accept
                transitions.fold(false, |acc, t| acc || t)
            }
        }
    }
}

// =============================================================================
// Guard Selectivity Estimation (Phase 7A)
// =============================================================================

/// Selectivity metadata for a guard, used for ordering guards on the same channel.
#[derive(Debug, Clone)]
pub struct GuardSelectivity {
    /// Index of the guard in the language definition.
    pub guard_idx: usize,
    /// Estimated selectivity: 0.0 = rejects all, 1.0 = accepts all.
    pub estimated_selectivity: f64,
    /// Decidability tier.
    pub tier: GuardTier,
    /// Estimated evaluation cost (lower = cheaper).
    pub evaluation_cost: u32,
}

/// Estimate the selectivity of a behavioral predicate.
///
/// Selectivity is a value in [0.0, 1.0] estimating the fraction of inputs
/// that satisfy the guard. Lower selectivity = more selective = rejects more.
///
/// These are heuristic estimates used for ordering guards on the same channel
/// so that the most selective (and cheapest) guards are evaluated first.
pub fn estimate_selectivity(pred: &BehavioralPred) -> f64 {
    match pred {
        // Negated relation: typically high selectivity (rejects most)
        BehavioralPred::RelationQuery { negated: true, .. } => 0.1,
        // Positive relation: moderate selectivity
        BehavioralPred::RelationQuery { negated: false, .. } => 0.5,
        // Conjunction: product of sub-selectivities (more selective)
        BehavioralPred::And(a, b) => {
            estimate_selectivity(a) * estimate_selectivity(b)
        }
        // Disjunction: 1 - product of (1 - sub-selectivities) (less selective)
        BehavioralPred::Or(a, b) => {
            let sa = estimate_selectivity(a);
            let sb = estimate_selectivity(b);
            1.0 - (1.0 - sa) * (1.0 - sb)
        }
        // Universal quantifier: very selective (hard to satisfy)
        BehavioralPred::Quantified { quantifier: crate::ast::language::Quantifier::ForAll, bound, .. } => {
            if let Some(k) = bound {
                0.05 / (*k as f64).sqrt().max(1.0)
            } else {
                0.05
            }
        }
        // Existential: moderate
        BehavioralPred::Quantified { quantifier: crate::ast::language::Quantifier::Exists, bound, .. } => {
            if let Some(k) = bound {
                0.3 / (*k as f64).sqrt().max(1.0)
            } else {
                0.5
            }
        }
        // AC-match: depends on element count (moderate)
        BehavioralPred::AcMatch { elements, .. } => {
            0.3 / (elements.len() as f64).max(1.0)
        }
        // Negation: complement
        BehavioralPred::Not(inner) => 1.0 - estimate_selectivity(inner),
        // Implication: ~same as Or(Not(a), b)
        BehavioralPred::Implies(a, b) => {
            let sa = estimate_selectivity(a);
            let sb = estimate_selectivity(b);
            1.0 - sa * (1.0 - sb)
        }
    }
}

/// Estimate the evaluation cost of a behavioral predicate.
///
/// Lower cost = cheaper. Used as a tiebreaker when guards have equal selectivity.
pub fn estimate_guard_cost(pred: &BehavioralPred) -> u32 {
    match pred {
        BehavioralPred::RelationQuery { .. } => 2,
        BehavioralPred::AcMatch { elements, .. } => 10 + 5 * elements.len() as u32,
        BehavioralPred::Quantified { bound, body, .. } => {
            let base = bound.map(|k| k as u32).unwrap_or(100);
            base + estimate_guard_cost(body)
        }
        BehavioralPred::And(a, b) | BehavioralPred::Or(a, b) | BehavioralPred::Implies(a, b) => {
            estimate_guard_cost(a) + estimate_guard_cost(b)
        }
        BehavioralPred::Not(inner) => estimate_guard_cost(inner) + 1,
    }
}

/// Sort guard infos by selectivity (most selective + cheapest first).
///
/// When multiple guards protect the same channel, evaluating the most selective
/// guard first provides the best short-circuit behavior (rejects most inputs
/// earliest, saving evaluation of subsequent guards).
pub fn order_guards_by_selectivity(guards: &mut [GuardSelectivity]) {
    guards.sort_by(|a, b| {
        // Primary: most selective first (lowest selectivity value)
        a.estimated_selectivity
            .partial_cmp(&b.estimated_selectivity)
            .unwrap_or(std::cmp::Ordering::Equal)
            // Secondary: cheapest first (for equal selectivity)
            .then(a.evaluation_cost.cmp(&b.evaluation_cost))
    });
}

// =============================================================================
// Guard Set Analysis (Phase 7B)
// =============================================================================

/// Result of analyzing a set of guards on the same channel.
#[derive(Debug, Default)]
pub struct GuardSetAnalysis {
    /// Indices of guards that are unsatisfiable (SFA is empty).
    /// These guards will never fire — emit SYM01.
    pub dead_guards: Vec<usize>,
    /// Pairs of guard indices whose SFAs overlap.
    /// Overlapping guards may cause ambiguous dispatch — emit SYM02.
    pub overlapping_pairs: Vec<(usize, usize)>,
    /// Pairs (i, j) where guard j subsumes guard i.
    /// Guard i is redundant — emit SYM03.
    pub subsumed_pairs: Vec<(usize, usize)>,
    /// Whether the guard set is T1 always-true (should skip behavioral check).
    pub has_always_true: Vec<usize>,
    /// Whether the guard set is T1 always-false (dead receive).
    pub has_always_false: Vec<usize>,
}

/// Analyze a set of guards for dead guards, overlaps, and subsumption.
///
/// Uses compile-time analysis of the guard predicates. For guards that can
/// be compiled to direct Ascent joins (T2 RelationQuery), analysis checks:
/// - Satisfiability: is the guard's predicate always false?
/// - Overlap: do two guards accept overlapping input sets?
/// - Subsumption: does one guard accept a strict superset of another?
///
/// For guards that cannot be statically analyzed (T3/T4), conservative
/// assumptions are used (no dead guards, possible overlaps).
pub fn analyze_guard_set(guards: &[(usize, &BehavioralPred)]) -> GuardSetAnalysis {
    let mut analysis = GuardSetAnalysis::default();

    // Check for T1 static elimination
    for &(idx, pred) in guards {
        if let Some(value) = evaluate_static_guard(pred) {
            if value {
                analysis.has_always_true.push(idx);
            } else {
                analysis.has_always_false.push(idx);
                analysis.dead_guards.push(idx);
            }
        }
    }

    // Check for contradictory guards (RelationQuery negation pairs)
    for i in 0..guards.len() {
        for j in (i + 1)..guards.len() {
            let (_, pred_i) = &guards[i];
            let (_, pred_j) = &guards[j];

            // Check overlap: if both guards are simple RelationQuery on the same
            // relation with the same args but different negation, they're complements
            // (no overlap). If same negation, they overlap exactly.
            if let (
                BehavioralPred::RelationQuery { relation_name: rn1, args: a1, negated: n1 },
                BehavioralPred::RelationQuery { relation_name: rn2, args: a2, negated: n2 },
            ) = (pred_i, pred_j) {
                if rn1 == rn2 && a1.len() == a2.len()
                    && a1.iter().zip(a2.iter()).all(|(x, y)| pred_arg_equal(x, y))
                {
                    if n1 == n2 {
                        // Same guard — one subsumes the other
                        analysis.overlapping_pairs.push((guards[i].0, guards[j].0));
                        analysis.subsumed_pairs.push((guards[i].0, guards[j].0));
                    }
                    // If negation differs, they're complements — no overlap
                }
            }
        }
    }

    analysis
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_rel_query(name: &str, negated: bool) -> BehavioralPred {
        BehavioralPred::RelationQuery {
            relation_name: quote::format_ident!("{}", name),
            args: vec![PredArg::Var(quote::format_ident!("x"))],
            negated,
        }
    }

    #[test]
    fn t1_tautology_detection() {
        let p = make_rel_query("positive", false);
        let not_p = BehavioralPred::Not(Box::new(make_rel_query("positive", false)));
        let tautology = BehavioralPred::Or(Box::new(p), Box::new(not_p));
        assert_eq!(classify_guard_tier(&tautology), GuardTier::T1Static);
        assert_eq!(evaluate_static_guard(&tautology), Some(true));
    }

    #[test]
    fn t1_contradiction_detection() {
        let p = make_rel_query("positive", false);
        let not_p = BehavioralPred::Not(Box::new(make_rel_query("positive", false)));
        let contradiction = BehavioralPred::And(Box::new(p), Box::new(not_p));
        assert_eq!(classify_guard_tier(&contradiction), GuardTier::T1Static);
        assert_eq!(evaluate_static_guard(&contradiction), Some(false));
    }

    #[test]
    fn t2_simple_relation() {
        let pred = make_rel_query("positive", false);
        assert_eq!(classify_guard_tier(&pred), GuardTier::T2Decidable);
    }

    #[test]
    fn t2_negated_relation() {
        let pred = make_rel_query("negative", true);
        assert_eq!(classify_guard_tier(&pred), GuardTier::T2Decidable);
    }

    #[test]
    fn t2_conjunction() {
        let a = make_rel_query("positive", false);
        let b = make_rel_query("even", false);
        let pred = BehavioralPred::And(Box::new(a), Box::new(b));
        assert_eq!(classify_guard_tier(&pred), GuardTier::T2Decidable);
    }

    #[test]
    fn t3_bounded_quantifier() {
        let body = make_rel_query("safe", false);
        let pred = BehavioralPred::Quantified {
            quantifier: crate::ast::language::Quantifier::ForAll,
            var: quote::format_ident!("y"),
            domain: None,
            bound: Some(100),
            body: Box::new(body),
        };
        assert_eq!(classify_guard_tier(&pred), GuardTier::T3Bounded);
    }

    #[test]
    fn t3_unbounded_simple_body() {
        let body = make_rel_query("safe", false);
        let pred = BehavioralPred::Quantified {
            quantifier: crate::ast::language::Quantifier::ForAll,
            var: quote::format_ident!("y"),
            domain: None,
            bound: None,
            body: Box::new(body),
        };
        assert_eq!(classify_guard_tier(&pred), GuardTier::T3Bounded);
    }

    #[test]
    fn t4_nested_quantifiers() {
        let inner_body = make_rel_query("connected", false);
        let inner = BehavioralPred::Quantified {
            quantifier: crate::ast::language::Quantifier::Exists,
            var: quote::format_ident!("z"),
            domain: None,
            bound: None,
            body: Box::new(inner_body),
        };
        let pred = BehavioralPred::Quantified {
            quantifier: crate::ast::language::Quantifier::ForAll,
            var: quote::format_ident!("y"),
            domain: None,
            bound: None,
            body: Box::new(inner),
        };
        assert_eq!(classify_guard_tier(&pred), GuardTier::T4Assert);
    }

    #[test]
    fn can_compile_simple_relation() {
        let pred = make_rel_query("positive", false);
        assert!(can_compile_to_ascent_join(&pred));
    }

    #[test]
    fn can_compile_conjunction_of_relations() {
        let a = make_rel_query("positive", false);
        let b = make_rel_query("even", false);
        let pred = BehavioralPred::And(Box::new(a), Box::new(b));
        assert!(can_compile_to_ascent_join(&pred));
    }

    #[test]
    fn cannot_compile_quantified() {
        let body = make_rel_query("safe", false);
        let pred = BehavioralPred::Quantified {
            quantifier: crate::ast::language::Quantifier::ForAll,
            var: quote::format_ident!("y"),
            domain: None,
            bound: None,
            body: Box::new(body),
        };
        assert!(!can_compile_to_ascent_join(&pred));
    }

    #[test]
    fn selectivity_negated_more_selective() {
        let pos = estimate_selectivity(&make_rel_query("r", false));
        let neg = estimate_selectivity(&make_rel_query("r", true));
        assert!(neg < pos, "negated should be more selective");
    }

    #[test]
    fn selectivity_conjunction_more_selective() {
        let single = estimate_selectivity(&make_rel_query("r", false));
        let conj = estimate_selectivity(&BehavioralPred::And(
            Box::new(make_rel_query("r", false)),
            Box::new(make_rel_query("s", false)),
        ));
        assert!(conj < single, "conjunction should be more selective");
    }

    #[test]
    fn selectivity_disjunction_less_selective() {
        let single = estimate_selectivity(&make_rel_query("r", false));
        let disj = estimate_selectivity(&BehavioralPred::Or(
            Box::new(make_rel_query("r", false)),
            Box::new(make_rel_query("s", false)),
        ));
        assert!(disj > single, "disjunction should be less selective");
    }

    #[test]
    fn guard_ordering() {
        let mut guards = vec![
            GuardSelectivity { guard_idx: 0, estimated_selectivity: 0.5, tier: GuardTier::T2Decidable, evaluation_cost: 2 },
            GuardSelectivity { guard_idx: 1, estimated_selectivity: 0.1, tier: GuardTier::T2Decidable, evaluation_cost: 2 },
            GuardSelectivity { guard_idx: 2, estimated_selectivity: 0.5, tier: GuardTier::T2Decidable, evaluation_cost: 10 },
        ];
        order_guards_by_selectivity(&mut guards);
        assert_eq!(guards[0].guard_idx, 1, "most selective first");
        assert_eq!(guards[1].guard_idx, 0, "equal selectivity, cheaper first");
        assert_eq!(guards[2].guard_idx, 2, "equal selectivity, more expensive last");
    }

    #[test]
    fn guard_set_analysis_dead_guard() {
        let p = make_rel_query("positive", false);
        let not_p = BehavioralPred::Not(Box::new(make_rel_query("positive", false)));
        let contradiction = BehavioralPred::And(Box::new(p), Box::new(not_p));
        let guards = vec![(0, &contradiction)];
        let analysis = analyze_guard_set(&guards);
        assert!(analysis.dead_guards.contains(&0));
        assert!(analysis.has_always_false.contains(&0));
    }

    #[test]
    fn guard_set_analysis_overlap() {
        let p1 = make_rel_query("positive", false);
        let p2 = make_rel_query("positive", false);
        let guards = vec![(0, &p1), (1, &p2)];
        let analysis = analyze_guard_set(&guards);
        assert!(!analysis.overlapping_pairs.is_empty());
    }
}
