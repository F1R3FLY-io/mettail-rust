//! Weighted MSO Logic — Logical specification language for grammar properties.
//!
//! Implements weighted monadic second-order (MSO) logic following Droste & Gastin's
//! framework for weighted automata and weighted logics. This module provides:
//!
//! - **Formula AST** (`WeightedMsoFormula`): Full weighted MSO syntax
//! - **Classification** (`MsoFormulaClass`): Restricted/Existential/FirstOrder/Full
//! - **Decidability analysis** (`DecidabilityTier`): T1–T4 tiering
//! - **Evaluation** over concrete words with Boolean semiring
//! - **Free variable analysis** and existential/universal closure
//!
//! ## Theoretical Foundation
//!
//! **Droste, M. & Gastin, P.** (2007). "Weighted automata and weighted logics."
//! *Theoretical Computer Science*, 380(1–2), 69–86.
//!
//! ### Theorem 3.7 (Weighted Büchi-Elgot-Trakhtenbrot)
//!
//! For any commutative semiring K and finite alphabet Σ:
//!
//! > A formal power series S: Σ* → K is **recognizable** (accepted by a weighted
//! > finite automaton) if and only if S is **definable** by a sentence in the
//! > **restricted fragment** of weighted MSO logic over K.
//!
//! This establishes the equivalence between:
//! - **Operational** (weighted automata): transition-based computation
//! - **Logical** (weighted MSO): declarative specification
//!
//! The restricted fragment excludes universal second-order quantification (∀X)
//! and restricts universal first-order quantification (∀x) to bodies that are
//! **recognizable step functions** — ensuring the product over positions remains
//! well-defined and computable.
//!
//! ### Formula Semantics (Definition 3.2)
//!
//! For a word w ∈ Σ* and variable assignment σ mapping first-order variables
//! to positions and second-order variables to position sets:
//!
//! ```text
//! ⟦k⟧(w, σ)           = k                           (constant)
//! ⟦Pₐ(x)⟧(w, σ)       = 1 if w[σ(x)] = a, else 0   (label test)
//! ⟦φ ∨ ψ⟧(w, σ)        = ⟦φ⟧(w, σ) ⊕ ⟦ψ⟧(w, σ)     (semiring addition)
//! ⟦φ ∧ ψ⟧(w, σ)        = ⟦φ⟧(w, σ) ⊗ ⟦ψ⟧(w, σ)     (semiring multiplication)
//! ⟦∃x. φ⟧(w, σ)        = ⊕_{i∈pos(w)} ⟦φ⟧(w, σ[x→i])
//! ⟦∃X. φ⟧(w, σ)        = ⊕_{I⊆pos(w)} ⟦φ⟧(w, σ[X→I])
//! ⟦∀x. φ⟧(w, σ)        = ⊗_{i∈pos(w)} ⟦φ⟧(w, σ[x→i])  (restricted: step fn body)
//! ⟦∀X. φ⟧(w, σ)        = ⊗_{I⊆pos(w)} ⟦φ⟧(w, σ[X→I])  (full MSO only)
//! ```
//!
//! ### Connection to Predicated Types Specification
//!
//! In PraTTaIL, weighted MSO formulas serve as a logical specification language
//! for grammar predicates, type constraints, and lint rules:
//!
//! - **Grammar predicates**: Token-label tests (`Pₐ(x)`) and ordering (`x ≤ y`)
//!   capture the structural properties of parse derivations.
//! - **Lint rules**: Existential/universal quantification over positions enables
//!   pattern matching against parse trees (e.g., "there exists a position where
//!   token X follows token Y").
//! - **Cost analysis**: Weighted evaluation with `TropicalWeight` computes
//!   minimum-cost derivations; with `CountingWeight`, it counts derivations.
//!
//! ### Architecture
//!
//! ```text
//! WeightedMsoFormula (AST)
//!       │
//!       ├──→ classify_formula()  ──→ MsoFormulaClass
//!       │                                  │
//!       │                                  └──→ check_decidability() ──→ DecidabilityTier
//!       │
//!       ├──→ free_variables()    ──→ HashSet<String>
//!       ├──→ free_set_variables()──→ HashSet<String>
//!       ├──→ is_sentence()       ──→ bool
//!       │
//!       ├──→ close_existentially() ──→ WeightedMsoFormula (sentence)
//!       ├──→ close_universally()   ──→ WeightedMsoFormula (sentence)
//!       │
//!       ├──→ evaluate_formula_bool()   ──→ BooleanWeight
//!       └──→ evaluate_sentence_bool()  ──→ BooleanWeight
//!
//! MsoAnalysis
//!       │
//!       └──→ analyze_formula() ──→ { class, decidability, free vars, is_sentence }
//! ```
//!
//! ## Feature Gate
//!
//! This module is gated behind the `weighted-mso` feature flag, which
//! depends on `symbolic-automata` (Module 1). The `DecidabilityTier` enum
//! is imported from `crate::symbolic`, and the `BooleanAlgebra` trait from
//! that module provides the predicate algebra for symbolic guard analysis.

use std::collections::{HashMap, HashSet};

use crate::automata::semiring::{BooleanWeight, Semiring};
use crate::symbolic::DecidabilityTier;

// ══════════════════════════════════════════════════════════════════════════════
// Weighted MSO Formula AST (Droste & Gastin Definition 3.1)
// ══════════════════════════════════════════════════════════════════════════════

/// Weighted MSO formula.
///
/// Semantics: `⟦φ⟧(w, σ) ∈ K` for word `w` and variable assignment `σ`.
///
/// The connectives map to semiring operations:
/// - `∨` (disjunction) → `⊕` (semiring addition / `plus`)
/// - `∧` (conjunction) → `⊗` (semiring multiplication / `times`)
/// - `∃x` (first-order existential) → `Σ_i` (sum over positions)
/// - `∃X` (second-order existential) → `Σ_I` (sum over subsets)
/// - `∀x` (first-order universal) → `Π_i` (product over positions)
///   **Restricted**: body must be a recognizable step function.
/// - `∀X` (second-order universal) → NOT in restricted MSO (classified T3/T4).
///
/// The `Constant` variant stores semiring values as string representations
/// to support `Eq` and `Hash` without requiring the semiring type `K` to
/// implement those traits (many semiring types contain `f64`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WeightedMsoFormula {
    /// Semiring constant `k ∈ K` (stored as string representation for `Eq`/`Hash`).
    ///
    /// Canonical values: `"true"`, `"false"`, `"0"`, `"1"`.
    Constant(String),

    /// Atomic position predicate `Pₐ(x)` — "position `x` has label `a`".
    ///
    /// Evaluates to `1_K` if `w[σ(x)] = a`, else `0_K`.
    AtomicPos {
        /// The label (alphabet symbol) to test.
        label: String,
        /// First-order variable naming the position.
        var: String,
    },

    /// Negated atomic `¬Pₐ(x)` — "position `x` does NOT have label `a`".
    ///
    /// Evaluates to `0_K` if `w[σ(x)] = a`, else `1_K`.
    NegAtomicPos {
        /// The label (alphabet symbol) to test.
        label: String,
        /// First-order variable naming the position.
        var: String,
    },

    /// Order predicate `x ≤ y` — "position `x` precedes or equals position `y`".
    ///
    /// Evaluates to `1_K` if `σ(x) ≤ σ(y)`, else `0_K`.
    Order {
        /// Left operand variable.
        x: String,
        /// Right operand variable.
        y: String,
    },

    /// Negated order `¬(x ≤ y)` — "position `x` strictly follows position `y`".
    ///
    /// Evaluates to `0_K` if `σ(x) ≤ σ(y)`, else `1_K`.
    NegOrder {
        /// Left operand variable.
        x: String,
        /// Right operand variable.
        y: String,
    },

    /// Set membership `x ∈ X` — "position `x` belongs to set `X`".
    ///
    /// Evaluates to `1_K` if `σ(x) ∈ σ(X)`, else `0_K`.
    InSet {
        /// First-order variable naming the position.
        var: String,
        /// Second-order variable naming the position set.
        set_var: String,
    },

    /// Negated set membership `¬(x ∈ X)` — "position `x` does NOT belong to set `X`".
    ///
    /// Evaluates to `0_K` if `σ(x) ∈ σ(X)`, else `1_K`.
    NotInSet {
        /// First-order variable naming the position.
        var: String,
        /// Second-order variable naming the position set.
        set_var: String,
    },

    /// Disjunction `φ ∨ ψ` — semantics: `⟦φ⟧ ⊕ ⟦ψ⟧` (semiring addition).
    Or(Box<WeightedMsoFormula>, Box<WeightedMsoFormula>),

    /// Conjunction `φ ∧ ψ` — semantics: `⟦φ⟧ ⊗ ⟦ψ⟧` (semiring multiplication).
    And(Box<WeightedMsoFormula>, Box<WeightedMsoFormula>),

    /// Existential first-order `∃x. φ` — semantics: `Σᵢ ⟦φ⟧[x→i]`.
    ///
    /// Sums the body's value over all positions in the word.
    ExistsFirst {
        /// The bound variable.
        var: String,
        /// The body formula.
        body: Box<WeightedMsoFormula>,
    },

    /// Existential second-order `∃X. φ` — semantics: `Σ_I ⟦φ⟧[X→I]`.
    ///
    /// Sums the body's value over all subsets of positions.
    /// Complexity: exponential in word length (2^n subsets).
    ExistsSecond {
        /// The bound set variable.
        var: String,
        /// The body formula.
        body: Box<WeightedMsoFormula>,
    },

    /// Universal first-order `∀x. φ` — semantics: `Πᵢ ⟦φ⟧[x→i]`.
    ///
    /// **Restricted**: In the restricted MSO fragment (Droste & Gastin, §4),
    /// the body `φ` must be a **recognizable step function** — a finite sum
    /// of formulas of the form `k ∧ ψ` where `k` is a constant and `ψ` is
    /// a Boolean formula. This ensures the product is well-defined.
    ForallFirst {
        /// The bound variable.
        var: String,
        /// The body formula.
        body: Box<WeightedMsoFormula>,
    },

    /// Universal second-order `∀X. φ` — semantics: `Π_I ⟦φ⟧[X→I]`.
    ///
    /// **NOT in restricted MSO** — formulas containing `∀X` are classified as
    /// `Full` MSO (T3 or T4 decidability).
    ForallSecond {
        /// The bound set variable.
        var: String,
        /// The body formula.
        body: Box<WeightedMsoFormula>,
    },
}

// === Rocq Proof Alignment (MsoAutomataEquivalence.v) ===
//
// The Rocq proof establishes the constructive direction of the weighted
// Büchi-Elgot-Trakhtenbrot theorem (Droste & Gastin, Thm 3.7): restricted
// MSO → recognizable series. It proves:
//   - `restricted_mso_recognizable`: structural induction over MsoFormula.
//   - Closure under sum, Hadamard product, and projection.
//   - `concrete_mso_recognizable`: axiom-free version for nat-valued series.
//
// The Rust has `classify_formula()` and `check_decidability()` that correctly
// align with the Rocq's `restricted_mso` predicate (ForallSecond → Full).
// However, the Rust does not yet implement `to_weighted_automaton()` — the
// compilation direction from MSO formula to WFA. The `evaluate_sentence_bool()`
// function provides direct formula evaluation without constructing a WFA.
//
// TODO: Implement `compile_to_automaton()` for the restricted fragment,
// following the Rocq's constructive proof structure (atom → 2-state DFA,
// Or → disjoint union, And → product, Exists → subset construction).
//
// Properties preserved:
//   - Formula classification correctly identifies restricted vs full fragments.
//   - ForallSecond presence → Full MSO classification.
//   - Series operations (sum, Hadamard, projection) align with WFA closures.

// ══════════════════════════════════════════════════════════════════════════════
// Formula Classification
// ══════════════════════════════════════════════════════════════════════════════

/// Classification of MSO formulas for decidability tiering.
///
/// The hierarchy follows Droste & Gastin's fragment taxonomy:
///
/// ```text
/// FirstOrder ⊂ Restricted ⊂ RestrictedExistential ⊂ Full
/// ```
///
/// - **FirstOrder**: No set quantifiers at all. Decidable (T1).
/// - **Restricted**: May use set quantifiers but no `∀X`, and `∀x` only with
///   step-function bodies. Recognizable power series (Theorem 3.7). Decidable (T1).
/// - **RestrictedExistential**: `∃X₁...∃Xₙ. ψ` with `ψ` in the restricted
///   fragment. Still recognizable (closure under existential projection). Runtime
///   decidable (T2).
/// - **Full**: Contains `∀X` or unrestricted `∀x`. May be semi-decidable (T3)
///   or undecidable (T4) depending on the semiring.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MsoFormulaClass {
    /// Restricted MSO: no `∀X`, `∀x` only when body is step function.
    Restricted,
    /// Restricted existential: `∃X₁...∃Xₙ.ψ` with `ψ ∈ RMSO`.
    RestrictedExistential,
    /// First-order fragment (no set quantifiers).
    FirstOrder,
    /// Full MSO: may include `∀X` (generally undecidable over non-finite semirings).
    Full,
}

impl std::fmt::Display for MsoFormulaClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MsoFormulaClass::Restricted => write!(f, "Restricted MSO"),
            MsoFormulaClass::RestrictedExistential => write!(f, "Restricted Existential MSO"),
            MsoFormulaClass::FirstOrder => write!(f, "First-Order"),
            MsoFormulaClass::Full => write!(f, "Full MSO"),
        }
    }
}

/// Classify a weighted MSO formula according to the Droste-Gastin fragment hierarchy.
///
/// The classification proceeds by structural analysis:
///
/// 1. If the formula contains any `ForallSecond` (∀X) → `Full`.
/// 2. If the formula contains `ForallFirst` (∀x) whose body is NOT a recognizable
///    step function → `Full`.
/// 3. If the formula contains `ExistsSecond` (∃X) but no `ForallSecond`/unrestricted
///    `ForallFirst` → `RestrictedExistential`.
/// 4. If the formula has no set quantifiers at all → `FirstOrder`.
/// 5. Otherwise → `Restricted`.
pub fn classify_formula(formula: &WeightedMsoFormula) -> MsoFormulaClass {
    let mut has_forall_second = false;
    let mut has_unrestricted_forall_first = false;
    let mut has_exists_second = false;
    let mut has_forall_first_with_step = false;

    classify_recursive(
        formula,
        &mut has_forall_second,
        &mut has_unrestricted_forall_first,
        &mut has_exists_second,
        &mut has_forall_first_with_step,
    );

    if has_forall_second || has_unrestricted_forall_first {
        MsoFormulaClass::Full
    } else if has_exists_second {
        if has_forall_first_with_step {
            // Has ∃X and restricted ∀x — still RestrictedExistential
            // (the ∃X wraps a restricted body).
            MsoFormulaClass::RestrictedExistential
        } else {
            MsoFormulaClass::RestrictedExistential
        }
    } else if has_forall_first_with_step {
        // Has restricted ∀x but no set quantifiers beyond that.
        MsoFormulaClass::Restricted
    } else {
        // Check if there are any set quantifiers at all.
        if has_any_set_quantifiers(formula) {
            MsoFormulaClass::Restricted
        } else {
            MsoFormulaClass::FirstOrder
        }
    }
}

/// Recursively scan a formula to detect quantifier usage patterns.
fn classify_recursive(
    formula: &WeightedMsoFormula,
    has_forall_second: &mut bool,
    has_unrestricted_forall_first: &mut bool,
    has_exists_second: &mut bool,
    has_forall_first_with_step: &mut bool,
) {
    match formula {
        WeightedMsoFormula::Constant(_)
        | WeightedMsoFormula::AtomicPos { .. }
        | WeightedMsoFormula::NegAtomicPos { .. }
        | WeightedMsoFormula::Order { .. }
        | WeightedMsoFormula::NegOrder { .. }
        | WeightedMsoFormula::InSet { .. }
        | WeightedMsoFormula::NotInSet { .. } => {}

        WeightedMsoFormula::Or(a, b) | WeightedMsoFormula::And(a, b) => {
            classify_recursive(a, has_forall_second, has_unrestricted_forall_first, has_exists_second, has_forall_first_with_step);
            classify_recursive(b, has_forall_second, has_unrestricted_forall_first, has_exists_second, has_forall_first_with_step);
        }

        WeightedMsoFormula::ExistsFirst { body, .. } => {
            classify_recursive(body, has_forall_second, has_unrestricted_forall_first, has_exists_second, has_forall_first_with_step);
        }

        WeightedMsoFormula::ExistsSecond { body, .. } => {
            *has_exists_second = true;
            classify_recursive(body, has_forall_second, has_unrestricted_forall_first, has_exists_second, has_forall_first_with_step);
        }

        WeightedMsoFormula::ForallFirst { body, .. } => {
            if is_step_function(body) {
                *has_forall_first_with_step = true;
            } else {
                *has_unrestricted_forall_first = true;
            }
            classify_recursive(body, has_forall_second, has_unrestricted_forall_first, has_exists_second, has_forall_first_with_step);
        }

        WeightedMsoFormula::ForallSecond { body, .. } => {
            *has_forall_second = true;
            classify_recursive(body, has_forall_second, has_unrestricted_forall_first, has_exists_second, has_forall_first_with_step);
        }
    }
}

/// Check whether a formula contains any second-order quantifiers (∃X or ∀X).
fn has_any_set_quantifiers(formula: &WeightedMsoFormula) -> bool {
    match formula {
        WeightedMsoFormula::Constant(_)
        | WeightedMsoFormula::AtomicPos { .. }
        | WeightedMsoFormula::NegAtomicPos { .. }
        | WeightedMsoFormula::Order { .. }
        | WeightedMsoFormula::NegOrder { .. }
        | WeightedMsoFormula::InSet { .. }
        | WeightedMsoFormula::NotInSet { .. } => false,

        WeightedMsoFormula::Or(a, b) | WeightedMsoFormula::And(a, b) => {
            has_any_set_quantifiers(a) || has_any_set_quantifiers(b)
        }

        WeightedMsoFormula::ExistsFirst { body, .. }
        | WeightedMsoFormula::ForallFirst { body, .. } => has_any_set_quantifiers(body),

        WeightedMsoFormula::ExistsSecond { .. } | WeightedMsoFormula::ForallSecond { .. } => true,
    }
}

/// Check whether a formula is a recognizable step function.
///
/// A **recognizable step function** (Droste & Gastin, Definition 4.1) is a
/// finite sum (disjunction) of terms of the form `k ∧ ψ`, where:
/// - `k` is a semiring constant (`Constant`)
/// - `ψ` is a Boolean (unweighted) formula (only atomic predicates, negations,
///   ∨, ∧, ∃x, ∃X — no constants other than `"true"`/`"false"`)
///
/// In our representation, a formula qualifies as a step function if it is:
/// 1. A `Constant` (trivially a step function with `ψ = true`).
/// 2. A `And(Constant(_), ψ)` or `And(ψ, Constant(_))` where `ψ` is Boolean.
/// 3. A `Or(s₁, s₂)` where both `s₁` and `s₂` are step functions.
/// 4. A Boolean formula (no weighted constants other than "true"/"false").
fn is_step_function(formula: &WeightedMsoFormula) -> bool {
    match formula {
        // A constant is trivially a step function.
        WeightedMsoFormula::Constant(_) => true,

        // Atomic predicates and their negations are Boolean (hence step functions).
        WeightedMsoFormula::AtomicPos { .. }
        | WeightedMsoFormula::NegAtomicPos { .. }
        | WeightedMsoFormula::Order { .. }
        | WeightedMsoFormula::NegOrder { .. }
        | WeightedMsoFormula::InSet { .. }
        | WeightedMsoFormula::NotInSet { .. } => true,

        // Disjunction of step functions is a step function.
        WeightedMsoFormula::Or(a, b) => is_step_function(a) && is_step_function(b),

        // Conjunction: either k ∧ ψ or ψ ∧ k (one constant, one Boolean),
        // or both Boolean (which is also a step function).
        WeightedMsoFormula::And(a, b) => {
            let a_const = matches!(a.as_ref(), WeightedMsoFormula::Constant(_));
            let b_const = matches!(b.as_ref(), WeightedMsoFormula::Constant(_));
            if a_const && b_const {
                // k1 ∧ k2 — product of constants, trivially a step function.
                true
            } else if a_const {
                // k ∧ ψ — ψ must be Boolean (no non-trivial constants).
                is_boolean_formula(b)
            } else if b_const {
                // ψ ∧ k — ψ must be Boolean.
                is_boolean_formula(a)
            } else {
                // Both non-constant: must both be Boolean formulas.
                is_boolean_formula(a) && is_boolean_formula(b)
            }
        }

        // Existential quantifiers over step function bodies remain step functions.
        WeightedMsoFormula::ExistsFirst { body, .. }
        | WeightedMsoFormula::ExistsSecond { body, .. } => is_step_function(body),

        // Universal quantifiers nested inside a step function body are not
        // step functions (they introduce products, violating the finite-sum form).
        WeightedMsoFormula::ForallFirst { .. } | WeightedMsoFormula::ForallSecond { .. } => false,
    }
}

/// Check whether a formula is purely Boolean (unweighted).
///
/// A Boolean formula contains no semiring constants other than the canonical
/// Boolean values `"true"` and `"false"`. This ensures the formula evaluates
/// to either `0_K` or `1_K` for any assignment.
fn is_boolean_formula(formula: &WeightedMsoFormula) -> bool {
    match formula {
        WeightedMsoFormula::Constant(s) => s == "true" || s == "false",

        WeightedMsoFormula::AtomicPos { .. }
        | WeightedMsoFormula::NegAtomicPos { .. }
        | WeightedMsoFormula::Order { .. }
        | WeightedMsoFormula::NegOrder { .. }
        | WeightedMsoFormula::InSet { .. }
        | WeightedMsoFormula::NotInSet { .. } => true,

        WeightedMsoFormula::Or(a, b) | WeightedMsoFormula::And(a, b) => {
            is_boolean_formula(a) && is_boolean_formula(b)
        }

        WeightedMsoFormula::ExistsFirst { body, .. }
        | WeightedMsoFormula::ExistsSecond { body, .. } => is_boolean_formula(body),

        WeightedMsoFormula::ForallFirst { body, .. }
        | WeightedMsoFormula::ForallSecond { body, .. } => is_boolean_formula(body),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Free Variables
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the set of free first-order variables in a formula.
///
/// A first-order variable is **free** if it appears in an atomic predicate
/// (`AtomicPos`, `NegAtomicPos`, `Order`, `NegOrder`, `InSet`, `NotInSet`)
/// but is not bound by an enclosing `∃x` or `∀x` quantifier.
pub fn free_variables(formula: &WeightedMsoFormula) -> HashSet<String> {
    let mut free = HashSet::new();
    let mut bound = HashSet::new();
    collect_free_first_order(formula, &mut free, &mut bound);
    free
}

/// Recursively collect free first-order variables.
fn collect_free_first_order(
    formula: &WeightedMsoFormula,
    free: &mut HashSet<String>,
    bound: &mut HashSet<String>,
) {
    match formula {
        WeightedMsoFormula::Constant(_) => {}

        WeightedMsoFormula::AtomicPos { var, .. } | WeightedMsoFormula::NegAtomicPos { var, .. } => {
            if !bound.contains(var) {
                free.insert(var.clone());
            }
        }

        WeightedMsoFormula::Order { x, y } | WeightedMsoFormula::NegOrder { x, y } => {
            if !bound.contains(x) {
                free.insert(x.clone());
            }
            if !bound.contains(y) {
                free.insert(y.clone());
            }
        }

        WeightedMsoFormula::InSet { var, .. } | WeightedMsoFormula::NotInSet { var, .. } => {
            if !bound.contains(var) {
                free.insert(var.clone());
            }
        }

        WeightedMsoFormula::Or(a, b) | WeightedMsoFormula::And(a, b) => {
            collect_free_first_order(a, free, bound);
            collect_free_first_order(b, free, bound);
        }

        WeightedMsoFormula::ExistsFirst { var, body }
        | WeightedMsoFormula::ForallFirst { var, body } => {
            let was_bound = bound.contains(var);
            bound.insert(var.clone());
            collect_free_first_order(body, free, bound);
            if !was_bound {
                bound.remove(var);
            }
        }

        WeightedMsoFormula::ExistsSecond { body, .. }
        | WeightedMsoFormula::ForallSecond { body, .. } => {
            // Second-order quantifiers bind set variables, not first-order ones.
            collect_free_first_order(body, free, bound);
        }
    }
}

/// Compute the set of free second-order (set) variables in a formula.
///
/// A second-order variable is **free** if it appears in an `InSet` or `NotInSet`
/// predicate but is not bound by an enclosing `∃X` or `∀X` quantifier.
pub fn free_set_variables(formula: &WeightedMsoFormula) -> HashSet<String> {
    let mut free = HashSet::new();
    let mut bound = HashSet::new();
    collect_free_second_order(formula, &mut free, &mut bound);
    free
}

/// Recursively collect free second-order variables.
fn collect_free_second_order(
    formula: &WeightedMsoFormula,
    free: &mut HashSet<String>,
    bound: &mut HashSet<String>,
) {
    match formula {
        WeightedMsoFormula::Constant(_)
        | WeightedMsoFormula::AtomicPos { .. }
        | WeightedMsoFormula::NegAtomicPos { .. }
        | WeightedMsoFormula::Order { .. }
        | WeightedMsoFormula::NegOrder { .. } => {}

        WeightedMsoFormula::InSet { set_var, .. } | WeightedMsoFormula::NotInSet { set_var, .. } => {
            if !bound.contains(set_var) {
                free.insert(set_var.clone());
            }
        }

        WeightedMsoFormula::Or(a, b) | WeightedMsoFormula::And(a, b) => {
            collect_free_second_order(a, free, bound);
            collect_free_second_order(b, free, bound);
        }

        WeightedMsoFormula::ExistsFirst { body, .. }
        | WeightedMsoFormula::ForallFirst { body, .. } => {
            // First-order quantifiers do not bind set variables.
            collect_free_second_order(body, free, bound);
        }

        WeightedMsoFormula::ExistsSecond { var, body }
        | WeightedMsoFormula::ForallSecond { var, body } => {
            let was_bound = bound.contains(var);
            bound.insert(var.clone());
            collect_free_second_order(body, free, bound);
            if !was_bound {
                bound.remove(var);
            }
        }
    }
}

/// Check whether a formula is a **sentence** (no free variables of either order).
///
/// A sentence defines a formal power series `S: Σ* → K` mapping words to semiring
/// values without dependence on external variable assignments.
pub fn is_sentence(formula: &WeightedMsoFormula) -> bool {
    free_variables(formula).is_empty() && free_set_variables(formula).is_empty()
}

// ══════════════════════════════════════════════════════════════════════════════
// Formula Manipulation
// ══════════════════════════════════════════════════════════════════════════════

/// Close a formula existentially: bind all free first-order variables with `∃`.
///
/// For each free variable `x` in `formula`, wraps the formula as `∃x. formula`.
/// The order of quantifiers is deterministic (sorted alphabetically) to ensure
/// reproducible results.
///
/// This does NOT close free set variables. Use `close_existentially` followed by
/// wrapping with `ExistsSecond` for full closure if needed.
pub fn close_existentially(formula: WeightedMsoFormula) -> WeightedMsoFormula {
    let free = free_variables(&formula);
    let mut vars: Vec<String> = free.into_iter().collect();
    vars.sort();

    let mut result = formula;
    for var in vars {
        result = WeightedMsoFormula::ExistsFirst {
            var,
            body: Box::new(result),
        };
    }
    result
}

/// Close a formula universally: bind all free first-order variables with `∀`.
///
/// For each free variable `x` in `formula`, wraps the formula as `∀x. formula`.
/// The order of quantifiers is deterministic (sorted alphabetically).
///
/// **Warning**: This produces a restricted MSO formula ONLY if the resulting
/// `∀x` bodies are recognizable step functions. If they are not, the formula
/// will be classified as `Full` MSO.
pub fn close_universally(formula: WeightedMsoFormula) -> WeightedMsoFormula {
    let free = free_variables(&formula);
    let mut vars: Vec<String> = free.into_iter().collect();
    vars.sort();

    let mut result = formula;
    for var in vars {
        result = WeightedMsoFormula::ForallFirst {
            var,
            body: Box::new(result),
        };
    }
    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Decidability Check
// ══════════════════════════════════════════════════════════════════════════════

/// Map a weighted MSO formula to its decidability tier.
///
/// Follows Droste & Gastin:
/// - **Corollary 6.5**: Restricted and first-order formulas define recognizable
///   series → compile-time decidable (T1).
/// - **Proposition 4.6**: Restricted existential formulas (∃X₁...∃Xₙ.ψ with
///   ψ restricted) are still recognizable → runtime decidable (T2).
/// - **Full MSO**: With bounded quantifiers → semi-decidable (T3).
///   With unrestricted ∀X → undecidable (T4).
pub fn check_decidability(formula: &WeightedMsoFormula) -> DecidabilityTier {
    let class = classify_formula(formula);
    match class {
        MsoFormulaClass::FirstOrder | MsoFormulaClass::Restricted => {
            DecidabilityTier::CompileTimeDecidable
        }
        MsoFormulaClass::RestrictedExistential => DecidabilityTier::RuntimeDecidable,
        MsoFormulaClass::Full => {
            // Distinguish T3 (bounded) from T4 (unbounded).
            // A Full formula with only bounded quantifiers (no ∀X) is semi-decidable.
            if has_forall_second(formula) {
                DecidabilityTier::Undecidable
            } else {
                // Full due to unrestricted ∀x (non-step-function body).
                // Still semi-decidable: the product over positions is finite
                // for any concrete word, though it may not define a recognizable series.
                DecidabilityTier::SemiDecidable
            }
        }
    }
}

/// Check whether a formula contains any `∀X` quantifier.
fn has_forall_second(formula: &WeightedMsoFormula) -> bool {
    match formula {
        WeightedMsoFormula::Constant(_)
        | WeightedMsoFormula::AtomicPos { .. }
        | WeightedMsoFormula::NegAtomicPos { .. }
        | WeightedMsoFormula::Order { .. }
        | WeightedMsoFormula::NegOrder { .. }
        | WeightedMsoFormula::InSet { .. }
        | WeightedMsoFormula::NotInSet { .. } => false,

        WeightedMsoFormula::Or(a, b) | WeightedMsoFormula::And(a, b) => {
            has_forall_second(a) || has_forall_second(b)
        }

        WeightedMsoFormula::ExistsFirst { body, .. }
        | WeightedMsoFormula::ForallFirst { body, .. }
        | WeightedMsoFormula::ExistsSecond { body, .. } => has_forall_second(body),

        WeightedMsoFormula::ForallSecond { .. } => true,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Formula Evaluation (Boolean Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// Variable assignment: maps first-order variables to positions, second-order
/// variables to position sets.
///
/// Positions are 0-based indices into the word array.
#[derive(Debug, Clone)]
pub struct Assignment {
    /// First-order variable bindings: variable name → position index.
    pub first_order: HashMap<String, usize>,
    /// Second-order variable bindings: variable name → set of position indices.
    pub second_order: HashMap<String, HashSet<usize>>,
}

impl Assignment {
    /// Create an empty assignment.
    pub fn new() -> Self {
        Assignment {
            first_order: HashMap::new(),
            second_order: HashMap::new(),
        }
    }

    /// Create an assignment with pre-allocated capacity.
    pub fn with_capacity(first_order_cap: usize, second_order_cap: usize) -> Self {
        Assignment {
            first_order: HashMap::with_capacity(first_order_cap),
            second_order: HashMap::with_capacity(second_order_cap),
        }
    }
}

impl Default for Assignment {
    fn default() -> Self {
        Self::new()
    }
}

/// Evaluate a weighted MSO sentence over a concrete word using the Boolean semiring.
///
/// A **sentence** is a formula with no free variables. This function creates an
/// empty assignment and delegates to `evaluate_formula_bool`.
///
/// # Panics
///
/// Panics if the formula has free variables (is not a sentence). Use
/// `is_sentence()` to check beforehand, or use `evaluate_formula_bool()`
/// directly with an explicit assignment.
pub fn evaluate_sentence_bool(
    formula: &WeightedMsoFormula,
    word: &[String],
) -> BooleanWeight {
    let free_fo = free_variables(formula);
    let free_so = free_set_variables(formula);
    assert!(
        free_fo.is_empty() && free_so.is_empty(),
        "evaluate_sentence_bool requires a sentence (no free variables), \
         but found free first-order vars {:?} and free set vars {:?}",
        free_fo,
        free_so,
    );
    let assignment = Assignment::new();
    evaluate_formula_bool(formula, word, &assignment)
}

/// Evaluate a weighted MSO formula with assignment over a concrete word
/// using the Boolean semiring.
///
/// Implements Definition 3.2 of Droste & Gastin (2007) instantiated to
/// `K = BooleanWeight = ({0,1}, ∨, ∧, 0, 1)`:
///
/// - `⊕` = `∨` (Boolean OR)
/// - `⊗` = `∧` (Boolean AND)
/// - `0_K` = `BooleanWeight(false)`
/// - `1_K` = `BooleanWeight(true)`
///
/// This means:
/// - `Or` computes the Boolean OR of its operands.
/// - `And` computes the Boolean AND.
/// - `∃x` is true if the body is true for ANY position.
/// - `∃X` is true if the body is true for ANY subset.
/// - `∀x` is true if the body is true for ALL positions.
/// - `∀X` is true if the body is true for ALL subsets.
///
/// # Complexity
///
/// - First-order quantifiers: `O(n)` per quantifier (n = word length).
/// - Second-order quantifiers: `O(2^n)` per quantifier (exponential!).
///   Use with caution on large words.
pub fn evaluate_formula_bool(
    formula: &WeightedMsoFormula,
    word: &[String],
    assignment: &Assignment,
) -> BooleanWeight {
    match formula {
        WeightedMsoFormula::Constant(s) => {
            match s.as_str() {
                "true" | "1" => BooleanWeight::one(),
                "false" | "0" => BooleanWeight::zero(),
                // For BooleanWeight, any non-zero/non-false constant → one().
                _ => BooleanWeight::one(),
            }
        }

        WeightedMsoFormula::AtomicPos { label, var } => {
            let pos = assignment
                .first_order
                .get(var)
                .unwrap_or_else(|| panic!("unbound first-order variable: {}", var));
            if *pos < word.len() && word[*pos] == *label {
                BooleanWeight::one()
            } else {
                BooleanWeight::zero()
            }
        }

        WeightedMsoFormula::NegAtomicPos { label, var } => {
            let pos = assignment
                .first_order
                .get(var)
                .unwrap_or_else(|| panic!("unbound first-order variable: {}", var));
            if *pos < word.len() && word[*pos] == *label {
                BooleanWeight::zero()
            } else {
                BooleanWeight::one()
            }
        }

        WeightedMsoFormula::Order { x, y } => {
            let px = assignment
                .first_order
                .get(x)
                .unwrap_or_else(|| panic!("unbound first-order variable: {}", x));
            let py = assignment
                .first_order
                .get(y)
                .unwrap_or_else(|| panic!("unbound first-order variable: {}", y));
            if px <= py {
                BooleanWeight::one()
            } else {
                BooleanWeight::zero()
            }
        }

        WeightedMsoFormula::NegOrder { x, y } => {
            let px = assignment
                .first_order
                .get(x)
                .unwrap_or_else(|| panic!("unbound first-order variable: {}", x));
            let py = assignment
                .first_order
                .get(y)
                .unwrap_or_else(|| panic!("unbound first-order variable: {}", y));
            if px <= py {
                BooleanWeight::zero()
            } else {
                BooleanWeight::one()
            }
        }

        WeightedMsoFormula::InSet { var, set_var } => {
            let pos = assignment
                .first_order
                .get(var)
                .unwrap_or_else(|| panic!("unbound first-order variable: {}", var));
            let set = assignment
                .second_order
                .get(set_var)
                .unwrap_or_else(|| panic!("unbound second-order variable: {}", set_var));
            if set.contains(pos) {
                BooleanWeight::one()
            } else {
                BooleanWeight::zero()
            }
        }

        WeightedMsoFormula::NotInSet { var, set_var } => {
            let pos = assignment
                .first_order
                .get(var)
                .unwrap_or_else(|| panic!("unbound first-order variable: {}", var));
            let set = assignment
                .second_order
                .get(set_var)
                .unwrap_or_else(|| panic!("unbound second-order variable: {}", set_var));
            if set.contains(pos) {
                BooleanWeight::zero()
            } else {
                BooleanWeight::one()
            }
        }

        WeightedMsoFormula::Or(a, b) => {
            let va = evaluate_formula_bool(a, word, assignment);
            let vb = evaluate_formula_bool(b, word, assignment);
            va.plus(&vb)
        }

        WeightedMsoFormula::And(a, b) => {
            let va = evaluate_formula_bool(a, word, assignment);
            let vb = evaluate_formula_bool(b, word, assignment);
            va.times(&vb)
        }

        WeightedMsoFormula::ExistsFirst { var, body } => {
            // Σ_{i ∈ pos(w)} ⟦body⟧[var→i]
            // For Boolean: ∃ = OR over all positions.
            let mut result = BooleanWeight::zero();
            let mut extended = assignment.clone();
            for i in 0..word.len() {
                extended.first_order.insert(var.clone(), i);
                let val = evaluate_formula_bool(body, word, &extended);
                result = result.plus(&val);
                // Short-circuit: once true, stay true (Boolean OR).
                if result.is_one() {
                    break;
                }
            }
            result
        }

        WeightedMsoFormula::ExistsSecond { var, body } => {
            // Σ_{I ⊆ pos(w)} ⟦body⟧[var→I]
            // For Boolean: ∃X = OR over all subsets.
            let n = word.len();
            let mut result = BooleanWeight::zero();
            let mut extended = assignment.clone();
            // Enumerate all 2^n subsets via bitmask.
            let total_subsets: u64 = 1u64.checked_shl(n as u32).unwrap_or(u64::MAX);
            for mask in 0..total_subsets {
                let mut subset = HashSet::with_capacity(n);
                for bit in 0..n {
                    if mask & (1u64 << bit) != 0 {
                        subset.insert(bit);
                    }
                }
                extended.second_order.insert(var.clone(), subset);
                let val = evaluate_formula_bool(body, word, &extended);
                result = result.plus(&val);
                if result.is_one() {
                    break;
                }
            }
            result
        }

        WeightedMsoFormula::ForallFirst { var, body } => {
            // Π_{i ∈ pos(w)} ⟦body⟧[var→i]
            // For Boolean: ∀ = AND over all positions.
            let mut result = BooleanWeight::one();
            let mut extended = assignment.clone();
            for i in 0..word.len() {
                extended.first_order.insert(var.clone(), i);
                let val = evaluate_formula_bool(body, word, &extended);
                result = result.times(&val);
                // Short-circuit: once false, stay false (Boolean AND).
                if result.is_zero() {
                    break;
                }
            }
            result
        }

        WeightedMsoFormula::ForallSecond { var, body } => {
            // Π_{I ⊆ pos(w)} ⟦body⟧[var→I]
            // For Boolean: ∀X = AND over all subsets.
            let n = word.len();
            let mut result = BooleanWeight::one();
            let mut extended = assignment.clone();
            let total_subsets: u64 = 1u64.checked_shl(n as u32).unwrap_or(u64::MAX);
            for mask in 0..total_subsets {
                let mut subset = HashSet::with_capacity(n);
                for bit in 0..n {
                    if mask & (1u64 << bit) != 0 {
                        subset.insert(bit);
                    }
                }
                extended.second_order.insert(var.clone(), subset);
                let val = evaluate_formula_bool(body, word, &extended);
                result = result.times(&val);
                if result.is_zero() {
                    break;
                }
            }
            result
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// MSO Analysis Result
// ══════════════════════════════════════════════════════════════════════════════

/// Comprehensive analysis result for a weighted MSO formula.
///
/// Aggregates classification, decidability, free variable sets, and sentence
/// status into a single struct for downstream consumers (lint rules, pipeline
/// analysis, cost-benefit gating).
#[derive(Debug, Clone)]
pub struct MsoAnalysis {
    /// The formula's classification in the Droste-Gastin hierarchy.
    pub formula_class: MsoFormulaClass,
    /// The decidability tier derived from the formula class.
    pub decidability: DecidabilityTier,
    /// Free first-order variables (positions not bound by quantifiers).
    pub free_vars: HashSet<String>,
    /// Free second-order variables (sets not bound by quantifiers).
    pub free_set_vars: HashSet<String>,
    /// Whether the formula is a sentence (no free variables of either order).
    pub is_sentence: bool,
}

/// Perform comprehensive analysis of a weighted MSO formula.
///
/// Computes classification, decidability, free variables, and sentence status
/// in a single pass (with internal caching of free variable sets).
pub fn analyze_formula(formula: &WeightedMsoFormula) -> MsoAnalysis {
    let formula_class = classify_formula(formula);
    let decidability = check_decidability(formula);
    let free_vars = free_variables(formula);
    let free_set_vars = free_set_variables(formula);
    let is_sentence = free_vars.is_empty() && free_set_vars.is_empty();

    MsoAnalysis {
        formula_class,
        decidability,
        free_vars,
        free_set_vars,
        is_sentence,
    }
}

/// Analyze grammar properties using weighted MSO logic.
///
/// Constructs a simple MSO formula representing the grammar's rule structure
/// (each rule as an atomic position predicate) and analyzes it for
/// classification and decidability.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    _categories: &[crate::pipeline::CategoryInfo],
) -> MsoAnalysis {
    // Build a simple conjunction of atomic predicates from the grammar.
    // Each rule contributes an existential position predicate.
    if all_syntax.is_empty() {
        return MsoAnalysis {
            formula_class: MsoFormulaClass::Restricted,
            decidability: DecidabilityTier::CompileTimeDecidable,
            free_vars: HashSet::new(),
            free_set_vars: HashSet::new(),
            is_sentence: true,
        };
    }

    // Build ∃x₁.P_{label₁}(x₁) ∧ ∃x₂.P_{label₂}(x₂) ∧ ...
    let mut formula: Option<WeightedMsoFormula> = None;
    for (i, (label, _cat, _)) in all_syntax.iter().enumerate() {
        let var = format!("x{}", i);
        let atom = WeightedMsoFormula::ExistsFirst {
            var: var.clone(),
            body: Box::new(WeightedMsoFormula::AtomicPos {
                label: label.clone(),
                var,
            }),
        };
        formula = Some(match formula {
            Some(existing) => WeightedMsoFormula::And(Box::new(existing), Box::new(atom)),
            None => atom,
        });
    }

    analyze_formula(&formula.expect("all_syntax is non-empty"))
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Weighted MSO module (M10).
///
/// Always active (base module in every dispatch signature).
/// Provides MSO-level specification language analysis.
#[cfg(feature = "predicate-dispatch")]
pub struct MsoCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for MsoCompiler {
    type Output = MsoAnalysis;

    fn compile_predicate(
        &self,
        _pred: &crate::symbolic::PredicateExpr,
        _profile: &crate::predicate_dispatch::PredicateProfile,
        all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
        categories: &[crate::pipeline::CategoryInfo],
    ) -> Self::Output {
        analyze_from_bundle(all_syntax, categories)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── Helper constructors ─────────────────────────────────────────────────

    fn constant(s: &str) -> WeightedMsoFormula {
        WeightedMsoFormula::Constant(s.to_string())
    }

    fn atomic(label: &str, var: &str) -> WeightedMsoFormula {
        WeightedMsoFormula::AtomicPos {
            label: label.to_string(),
            var: var.to_string(),
        }
    }

    fn neg_atomic(label: &str, var: &str) -> WeightedMsoFormula {
        WeightedMsoFormula::NegAtomicPos {
            label: label.to_string(),
            var: var.to_string(),
        }
    }

    fn order(x: &str, y: &str) -> WeightedMsoFormula {
        WeightedMsoFormula::Order {
            x: x.to_string(),
            y: y.to_string(),
        }
    }

    fn neg_order(x: &str, y: &str) -> WeightedMsoFormula {
        WeightedMsoFormula::NegOrder {
            x: x.to_string(),
            y: y.to_string(),
        }
    }

    fn in_set(var: &str, set_var: &str) -> WeightedMsoFormula {
        WeightedMsoFormula::InSet {
            var: var.to_string(),
            set_var: set_var.to_string(),
        }
    }

    fn not_in_set(var: &str, set_var: &str) -> WeightedMsoFormula {
        WeightedMsoFormula::NotInSet {
            var: var.to_string(),
            set_var: set_var.to_string(),
        }
    }

    fn or(a: WeightedMsoFormula, b: WeightedMsoFormula) -> WeightedMsoFormula {
        WeightedMsoFormula::Or(Box::new(a), Box::new(b))
    }

    fn and(a: WeightedMsoFormula, b: WeightedMsoFormula) -> WeightedMsoFormula {
        WeightedMsoFormula::And(Box::new(a), Box::new(b))
    }

    fn exists_first(var: &str, body: WeightedMsoFormula) -> WeightedMsoFormula {
        WeightedMsoFormula::ExistsFirst {
            var: var.to_string(),
            body: Box::new(body),
        }
    }

    fn exists_second(var: &str, body: WeightedMsoFormula) -> WeightedMsoFormula {
        WeightedMsoFormula::ExistsSecond {
            var: var.to_string(),
            body: Box::new(body),
        }
    }

    fn forall_first(var: &str, body: WeightedMsoFormula) -> WeightedMsoFormula {
        WeightedMsoFormula::ForallFirst {
            var: var.to_string(),
            body: Box::new(body),
        }
    }

    fn forall_second(var: &str, body: WeightedMsoFormula) -> WeightedMsoFormula {
        WeightedMsoFormula::ForallSecond {
            var: var.to_string(),
            body: Box::new(body),
        }
    }

    fn word(labels: &[&str]) -> Vec<String> {
        labels.iter().map(|s| s.to_string()).collect()
    }

    // ── Classification tests ────────────────────────────────────────────────

    #[test]
    fn classify_pure_boolean_is_first_order() {
        // P_a(x) ∧ P_b(y) — no quantifiers, no set variables.
        let f = and(atomic("a", "x"), atomic("b", "y"));
        assert_eq!(classify_formula(&f), MsoFormulaClass::FirstOrder);
    }

    #[test]
    fn classify_exists_first_is_first_order() {
        // ∃x. P_a(x) — first-order existential, no set quantifiers.
        let f = exists_first("x", atomic("a", "x"));
        assert_eq!(classify_formula(&f), MsoFormulaClass::FirstOrder);
    }

    #[test]
    fn classify_exists_second_is_restricted_existential() {
        // ∃X. x ∈ X — second-order existential.
        let f = exists_second("X", in_set("x", "X"));
        assert_eq!(classify_formula(&f), MsoFormulaClass::RestrictedExistential);
    }

    #[test]
    fn classify_forall_first_step_body_is_restricted() {
        // ∀x. (k ∧ P_a(x)) — step function body (constant ∧ Boolean).
        let f = forall_first("x", and(constant("true"), atomic("a", "x")));
        assert_eq!(classify_formula(&f), MsoFormulaClass::Restricted);
    }

    #[test]
    fn classify_forall_first_non_step_body_is_full() {
        // ∀x. (∀y. P_a(y)) — body contains ∀y which is not a step function
        // (nested universal quantifier in body).
        let f = forall_first("x", forall_first("y", atomic("a", "y")));
        // The inner ∀y has body P_a(y) which IS a step function, so the inner ∀y
        // is classified as restricted. But the outer ∀x has body = ∀y.P_a(y),
        // which is NOT a step function (contains universal quantifier).
        assert_eq!(classify_formula(&f), MsoFormulaClass::Full);
    }

    #[test]
    fn classify_forall_second_is_full() {
        // ∀X. x ∈ X — universal second-order quantification.
        let f = forall_second("X", in_set("x", "X"));
        assert_eq!(classify_formula(&f), MsoFormulaClass::Full);
    }

    #[test]
    fn classify_mixed_exists_second_and_restricted_forall_first() {
        // ∃X. ∀x. (true ∧ (x ∈ X)) — ∃X wrapping a restricted ∀x body.
        let f = exists_second(
            "X",
            forall_first("x", and(constant("true"), in_set("x", "X"))),
        );
        assert_eq!(classify_formula(&f), MsoFormulaClass::RestrictedExistential);
    }

    // ── Free variable tests ─────────────────────────────────────────────────

    #[test]
    fn free_vars_atomic_pos() {
        let f = atomic("a", "x");
        assert_eq!(free_variables(&f), HashSet::from(["x".to_string()]));
        assert!(free_set_variables(&f).is_empty());
    }

    #[test]
    fn free_vars_bound_by_exists() {
        // ∃x. P_a(x) — x is bound, no free variables.
        let f = exists_first("x", atomic("a", "x"));
        assert!(free_variables(&f).is_empty());
    }

    #[test]
    fn free_vars_mixed_bound_and_free() {
        // ∃x. (P_a(x) ∧ P_b(y)) — x is bound, y is free.
        let f = exists_first("x", and(atomic("a", "x"), atomic("b", "y")));
        assert_eq!(free_variables(&f), HashSet::from(["y".to_string()]));
    }

    #[test]
    fn free_set_vars_in_set() {
        // x ∈ X — X is a free set variable.
        let f = in_set("x", "X");
        assert_eq!(free_variables(&f), HashSet::from(["x".to_string()]));
        assert_eq!(free_set_variables(&f), HashSet::from(["X".to_string()]));
    }

    #[test]
    fn free_set_vars_bound_by_exists_second() {
        // ∃X. x ∈ X — X is bound, x is free.
        let f = exists_second("X", in_set("x", "X"));
        assert!(free_set_variables(&f).is_empty());
        assert_eq!(free_variables(&f), HashSet::from(["x".to_string()]));
    }

    #[test]
    fn is_sentence_true_for_closed_formula() {
        // ∃x. P_a(x) — no free variables.
        let f = exists_first("x", atomic("a", "x"));
        assert!(is_sentence(&f));
    }

    #[test]
    fn is_sentence_false_for_open_formula() {
        // P_a(x) — x is free.
        let f = atomic("a", "x");
        assert!(!is_sentence(&f));
    }

    #[test]
    fn free_vars_order_predicate() {
        // x ≤ y — both x and y are free.
        let f = order("x", "y");
        let free = free_variables(&f);
        assert_eq!(free, HashSet::from(["x".to_string(), "y".to_string()]));
    }

    // ── Decidability tests ──────────────────────────────────────────────────

    #[test]
    fn decidability_first_order_is_t1() {
        let f = exists_first("x", atomic("a", "x"));
        assert_eq!(check_decidability(&f), DecidabilityTier::CompileTimeDecidable);
    }

    #[test]
    fn decidability_restricted_existential_is_t2() {
        let f = exists_second("X", in_set("x", "X"));
        assert_eq!(check_decidability(&f), DecidabilityTier::RuntimeDecidable);
    }

    #[test]
    fn decidability_full_with_forall_second_is_t4() {
        let f = forall_second("X", in_set("x", "X"));
        assert_eq!(check_decidability(&f), DecidabilityTier::Undecidable);
    }

    #[test]
    fn decidability_full_without_forall_second_is_t3() {
        // ∀x. (∀y. P_a(y)) — Full MSO due to nested ∀, but no ∀X → T3.
        let f = forall_first("x", forall_first("y", atomic("a", "y")));
        assert_eq!(check_decidability(&f), DecidabilityTier::SemiDecidable);
    }

    // ── Evaluation tests ────────────────────────────────────────────────────

    #[test]
    fn eval_constant_true() {
        let f = constant("true");
        let w = word(&[]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    #[test]
    fn eval_constant_false() {
        let f = constant("false");
        let w = word(&[]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::zero());
    }

    #[test]
    fn eval_atomic_pos_match() {
        // ∃x. P_a(x) over word ["a", "b"]
        let f = exists_first("x", atomic("a", "x"));
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    #[test]
    fn eval_atomic_pos_no_match() {
        // ∃x. P_c(x) over word ["a", "b"] — no position has label "c".
        let f = exists_first("x", atomic("c", "x"));
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::zero());
    }

    #[test]
    fn eval_neg_atomic_pos() {
        // ∃x. ¬P_a(x) over word ["a", "b"] — position 1 has label "b" ≠ "a".
        let f = exists_first("x", neg_atomic("a", "x"));
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    #[test]
    fn eval_or_composition() {
        // ∃x. (P_a(x) ∨ P_c(x)) over ["a", "b"]
        // Position 0: P_a(0) = true, so OR = true.
        let f = exists_first("x", or(atomic("a", "x"), atomic("c", "x")));
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    #[test]
    fn eval_and_composition() {
        // ∃x. (P_a(x) ∧ P_b(x)) over ["a", "b"]
        // No single position has both label "a" and label "b".
        let f = exists_first("x", and(atomic("a", "x"), atomic("b", "x")));
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::zero());
    }

    #[test]
    fn eval_exists_first_quantification() {
        // ∃x. ∃y. (P_a(x) ∧ P_b(y) ∧ x ≤ y) over ["a", "b"]
        // x=0 has "a", y=1 has "b", 0 ≤ 1.
        let f = exists_first(
            "x",
            exists_first(
                "y",
                and(and(atomic("a", "x"), atomic("b", "y")), order("x", "y")),
            ),
        );
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    #[test]
    fn eval_forall_first_all_same_label() {
        // ∀x. P_a(x) over ["a", "a", "a"] — all positions have label "a".
        let f = forall_first("x", atomic("a", "x"));
        let w = word(&["a", "a", "a"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    #[test]
    fn eval_forall_first_not_all_same() {
        // ∀x. P_a(x) over ["a", "b"] — position 1 has "b" ≠ "a".
        let f = forall_first("x", atomic("a", "x"));
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::zero());
    }

    #[test]
    fn eval_order_predicate() {
        // ∃x. ∃y. (x ≤ y ∧ ¬(y ≤ x)) over ["a", "b"]
        // This asks: do there exist strictly ordered positions? Yes: x=0, y=1.
        let f = exists_first(
            "x",
            exists_first(
                "y",
                and(order("x", "y"), neg_order("y", "x")),
            ),
        );
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    #[test]
    fn eval_set_membership() {
        // ∃X. ∃x. (x ∈ X ∧ P_a(x)) over ["a", "b"]
        // There exists a set X containing position 0, and position 0 has label "a".
        let f = exists_second(
            "X",
            exists_first("x", and(in_set("x", "X"), atomic("a", "x"))),
        );
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    #[test]
    fn eval_not_in_set() {
        // ∃X. ∃x. (¬(x ∈ X) ∧ P_b(x)) over ["a", "b"]
        // X = {0}, x = 1: 1 ∉ {0} and word[1] = "b".
        let f = exists_second(
            "X",
            exists_first("x", and(not_in_set("x", "X"), atomic("b", "x"))),
        );
        let w = word(&["a", "b"]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    // ── Closure tests ───────────────────────────────────────────────────────

    #[test]
    fn close_existentially_binds_free_vars() {
        // P_a(x) ∧ P_b(y) — free vars: {x, y}.
        let f = and(atomic("a", "x"), atomic("b", "y"));
        let closed = close_existentially(f);
        assert!(is_sentence(&closed));
        // Wrapping order: iterate sorted ["x", "y"], each wraps the accumulated
        // result. First wrap: ∃x. body, second wrap: ∃y. ∃x. body.
        // So outermost quantifier binds "y", innermost binds "x".
        match &closed {
            WeightedMsoFormula::ExistsFirst { var, body } => {
                assert_eq!(var, "y");
                match body.as_ref() {
                    WeightedMsoFormula::ExistsFirst { var, .. } => {
                        assert_eq!(var, "x");
                    }
                    _ => panic!("expected nested ExistsFirst"),
                }
            }
            _ => panic!("expected ExistsFirst"),
        }
    }

    #[test]
    fn close_universally_binds_free_vars() {
        let f = and(atomic("a", "x"), atomic("b", "y"));
        let closed = close_universally(f);
        assert!(is_sentence(&closed));
        // Same wrapping order: outermost binds "y", innermost binds "x".
        match &closed {
            WeightedMsoFormula::ForallFirst { var, body } => {
                assert_eq!(var, "y");
                match body.as_ref() {
                    WeightedMsoFormula::ForallFirst { var, .. } => {
                        assert_eq!(var, "x");
                    }
                    _ => panic!("expected nested ForallFirst"),
                }
            }
            _ => panic!("expected ForallFirst"),
        }
    }

    #[test]
    fn close_existentially_no_free_vars_is_identity() {
        let f = constant("true");
        let closed = close_existentially(f.clone());
        assert_eq!(closed, f);
    }

    // ── Analyze formula tests ───────────────────────────────────────────────

    #[test]
    fn analyze_first_order_sentence() {
        let f = exists_first("x", atomic("a", "x"));
        let analysis = analyze_formula(&f);
        assert_eq!(analysis.formula_class, MsoFormulaClass::FirstOrder);
        assert_eq!(analysis.decidability, DecidabilityTier::CompileTimeDecidable);
        assert!(analysis.free_vars.is_empty());
        assert!(analysis.free_set_vars.is_empty());
        assert!(analysis.is_sentence);
    }

    #[test]
    fn analyze_open_formula() {
        let f = atomic("a", "x");
        let analysis = analyze_formula(&f);
        assert_eq!(analysis.formula_class, MsoFormulaClass::FirstOrder);
        assert_eq!(analysis.decidability, DecidabilityTier::CompileTimeDecidable);
        assert_eq!(analysis.free_vars, HashSet::from(["x".to_string()]));
        assert!(analysis.free_set_vars.is_empty());
        assert!(!analysis.is_sentence);
    }

    // ── Step function tests ─────────────────────────────────────────────────

    #[test]
    fn step_function_constant() {
        assert!(is_step_function(&constant("42")));
    }

    #[test]
    fn step_function_constant_and_boolean() {
        // k ∧ P_a(x) — classic step function form.
        let f = and(constant("5"), atomic("a", "x"));
        assert!(is_step_function(&f));
    }

    #[test]
    fn step_function_disjunction_of_steps() {
        // (k1 ∧ P_a(x)) ∨ (k2 ∧ P_b(x)) — disjunction of step functions.
        let f = or(
            and(constant("3"), atomic("a", "x")),
            and(constant("7"), atomic("b", "x")),
        );
        assert!(is_step_function(&f));
    }

    #[test]
    fn not_step_function_nested_forall() {
        // ∀y. P_a(y) — universal quantifier in body, not a step function.
        let f = forall_first("y", atomic("a", "y"));
        assert!(!is_step_function(&f));
    }

    // ── Display tests ───────────────────────────────────────────────────────

    #[test]
    fn display_decidability_tier() {
        assert_eq!(
            format!("{}", DecidabilityTier::CompileTimeDecidable),
            "T1 (compile-time decidable)"
        );
        assert_eq!(
            format!("{}", DecidabilityTier::Undecidable),
            "T4 (undecidable)"
        );
    }

    #[test]
    fn display_formula_class() {
        assert_eq!(format!("{}", MsoFormulaClass::FirstOrder), "First-Order");
        assert_eq!(format!("{}", MsoFormulaClass::Full), "Full MSO");
    }

    // ── Edge case tests ─────────────────────────────────────────────────────

    #[test]
    fn eval_empty_word() {
        // ∃x. P_a(x) over [] — no positions, so existential is false.
        let f = exists_first("x", atomic("a", "x"));
        let w = word(&[]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::zero());
    }

    #[test]
    fn eval_forall_empty_word() {
        // ∀x. P_a(x) over [] — vacuously true (product over empty set = 1).
        let f = forall_first("x", atomic("a", "x"));
        let w = word(&[]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    #[test]
    fn eval_exists_second_empty_word() {
        // ∃X. true over [] — the empty subset exists, and true evaluates to one().
        let f = exists_second("X", constant("true"));
        let w = word(&[]);
        assert_eq!(evaluate_sentence_bool(&f, &w), BooleanWeight::one());
    }

    // ── Rocq Proof Alignment Tests (MsoAutomataEquivalence.v) ────────────────

    #[test]
    fn test_formula_without_forall_second_is_restricted() {
        // Rocq: `restricted_mso` predicate — formulas without ForallSecond are
        // in the restricted fragment (not Full).
        // Build formulas with ExistsFirst, ExistsSecond, And, Or — all non-Full.
        let f1 = WeightedMsoFormula::ExistsFirst {
            var: "x".to_string(),
            body: Box::new(WeightedMsoFormula::AtomicPos {
                label: "a".to_string(),
                var: "x".to_string(),
            }),
        };
        let class1 = classify_formula(&f1);
        assert_ne!(
            class1,
            MsoFormulaClass::Full,
            "ExistsFirst with atomic body should not be Full, got {:?}",
            class1
        );

        // Or of two first-order formulas
        let f2 = WeightedMsoFormula::Or(
            Box::new(f1.clone()),
            Box::new(WeightedMsoFormula::AtomicPos {
                label: "b".to_string(),
                var: "x".to_string(),
            }),
        );
        let class2 = classify_formula(&f2);
        assert_ne!(
            class2,
            MsoFormulaClass::Full,
            "Or of first-order formulas should not be Full, got {:?}",
            class2
        );

        // ExistsSecond wrapping a restricted body → RestrictedExistential
        let f3 = WeightedMsoFormula::ExistsSecond {
            var: "X".to_string(),
            body: Box::new(WeightedMsoFormula::InSet {
                var: "x".to_string(),
                set_var: "X".to_string(),
            }),
        };
        let class3 = classify_formula(&f3);
        assert_ne!(
            class3,
            MsoFormulaClass::Full,
            "ExistsSecond should not be Full, got {:?}",
            class3
        );
    }

    #[test]
    fn test_formula_with_forall_second_is_full() {
        // Rocq: ForallSecond is NOT in the restricted fragment → classify = Full.
        let f = WeightedMsoFormula::ForallSecond {
            var: "X".to_string(),
            body: Box::new(WeightedMsoFormula::InSet {
                var: "x".to_string(),
                set_var: "X".to_string(),
            }),
        };
        let class = classify_formula(&f);
        assert_eq!(
            class,
            MsoFormulaClass::Full,
            "ForallSecond should be classified as Full, got {:?}",
            class
        );

        // ForallSecond nested inside And should still be Full
        let f2 = WeightedMsoFormula::And(
            Box::new(f),
            Box::new(WeightedMsoFormula::Constant("true".to_string())),
        );
        assert_eq!(
            classify_formula(&f2),
            MsoFormulaClass::Full,
            "ForallSecond inside And should still be Full"
        );
    }
}
