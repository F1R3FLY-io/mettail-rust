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
//! The emitted `TriState` type is included in the `TokenStream` alongside the
//! generated runtime — the Dovetail saturation engine and, for Rho-backed COMM
//! languages, the Rho-native COMM backend. (The legacy Ascent Datalog runtime
//! backend was retired in P6.)
//!
//! ## Guard Evaluation Paths (post-P6)
//!
//! **Rho-backed COMM path:** For a guarded COMM rule in a
//! Rho-backed language, the surviving predicate is enforced at run time by the
//! COMM substrate — RSpace structural matching, a Rholang `where` boolean guard,
//! or a `RhoNativeJoin` bridge. The compile-time substrate (EBA/SFT) classifies
//! only and is never re-evaluated at run time (see
//! `docs/architecture/semantic-predicates/08-runtime-comm-enforcement.md`).
//!
//! **Refinement path (WPDA):** A refinement-type guard `{x:Sort | pred}` is
//! lowered by `wpda_codegen::refinement` to a call to
//! `mettail_runtime::evaluate_pred_with_bindings` against the thread-local fact
//! snapshot.
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
use quote::quote;

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
    // This function no longer emits per-guard evaluation wrapper functions.
    // Post-P6, behavioral predicates are enforced at run time by the
    // Rho-backed COMM path (RSpace structural matching, a Rholang `where`
    // boolean guard, or a `RhoNativeJoin` bridge) for Rho-backed
    // languages, or lowered to `mettail_runtime::evaluate_pred_with_bindings`
    // for WPDA refinement guards (see `wpda_codegen::refinement` and §8 of
    // `docs/design/predicated-types.md`). The legacy Ascent Datalog JOIN-clause
    // lowering was retired in P6. Per-instance predicates carried on the
    // generated enum variant are used only for shape dispatch, display, and
    // hash-consing — not runtime evaluation.
    //
    // We keep the `TriState` type emission for backward compatibility
    // with any external consumers that may reference it, but no
    // per-guard functions are generated.
    let _ = language;
    generate_tristate_type()
}
