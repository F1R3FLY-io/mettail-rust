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

use mettail_ast::language::LanguageDef;
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
    // Phase 3D correction (2026-04-08): this function no longer emits
    // per-guard evaluation wrapper functions. Under the corrected
    // design, behavioral predicates are evaluated via direct Ascent
    // JOIN clauses inside the guarded Comm rule body (see
    // `compile_guard_to_ascent_clauses` in `macros/src/logic/rules.rs`
    // and §8.2/§8.4 of `docs/design/predicated-types.md`). Per-instance
    // predicates carried on the generated enum variant are used only
    // for shape dispatch, display, and hash-consing — not runtime
    // evaluation.
    //
    // We keep the `TriState` type emission for backward compatibility
    // with any external consumers that may reference it, but no
    // per-guard functions are generated.
    let _ = language;
    generate_tristate_type()
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
        .map(|(from, to, _pred_repr)| {
            let from_lit = *from;
            let to_lit = *to;
            // Predicate evaluation happens via minterm partitioning at SFA
            // construction time, so each transition corresponds to one minterm.
            quote! {
                (#from_lit, true) => #to_lit
            }
        })
        .collect();

    if transition_arms.is_empty() {
        // No transitions: generate an empty evaluator.
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
pub fn generate_register_automaton(guard_idx: usize, num_registers: usize) -> TokenStream {
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
pub fn generate_awa_evaluation(guard_idx: usize, is_universal: bool) -> TokenStream {
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

