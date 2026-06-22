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
