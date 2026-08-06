//! MSO → SymbolicAutomaton compilation (Phase 5 of the predicated-types
//! implementation plan).
//!
//! This module implements `to_weighted_automaton()` — the constructive
//! direction of the weighted Büchi-Elgot-Trakhtenbrot theorem (Droste &
//! Gastin, 2007, Theorem 3.7) for the **restricted MSO fragment**:
//! `RMSO = FO + ∃x + ∃X + ∀x[step] + Boolean closure`. The proof of this
//! direction is in `prattail/src/coq/MsoAutomataEquivalence.v`; this
//! module ports it to Rust over `SymbolicAutomaton<KatBooleanAlgebra>`.
//!
//! # Encoding
//!
//! For an MSO formula with free variables `V₁ = {x₁,…,xₘ}` (first-order)
//! and `V₂ = {X₁,…,Xₖ}` (second-order), an input word `w ∈ Σ*` together
//! with an assignment `σ : V₁ ∪ V₂ → positions ∪ position-sets` is
//! encoded as a sequence of **propositional valuations** over the atoms:
//!
//! - `label_a` for each label `a ∈ Σ` — "the current input position
//!   carries label `a`".
//! - `is_x`    for each first-order variable `x ∈ V₁` — "the current
//!   input position is the one assigned to `x`".
//! - `in_X`    for each second-order variable `X ∈ V₂` — "the current
//!   input position is a member of the set assigned to `X`".
//!
//! Each input symbol of the SFA is therefore a `HashMap<String, bool>`
//! that fixes a truth value for every atom. This is exactly what
//! `KatBooleanAlgebra::Domain` already is, so the existing
//! `SymbolicAutomaton<KatBooleanAlgebra>` plus its `intersect` /
//! `union` / `complement` machinery does the heavy lifting.
//!
//! ## Well-formedness side condition
//!
//! For every first-order variable `x`, exactly one position must have
//! `is_x = true`. This is a *global* constraint that no individual
//! atomic SFA can enforce. The compiler emits a separate
//! "uniqueness automaton" `unique_x` for each first-order variable
//! and intersects it with the body. The uniqueness automaton has 2
//! states: `q0` (no witness yet) and `q1` (witness seen). It loops on
//! `¬is_x` in `q0`, transitions on `is_x` to `q1`, and rejects any
//! second `is_x` in `q1`. Only `q1` is accepting.
//!
//! ## Existential projection
//!
//! `∃x. φ` is compiled by FIRST recursively compiling `φ` (which still
//! constrains `is_x`), THEN running the standard NFA projection:
//! drop the `is_x` atom from the alphabet by replacing every transition
//! guard with the existential closure over `is_x`. Concretely, we
//! `intersect` the body with the uniqueness automaton for `x` and then
//! relax the dependency on `is_x` by erasing it from the guard's truth
//! valuations — implemented as a determinize + relabel pass that
//! treats `is_x = true` and `is_x = false` as equivalent inputs.
//!
//! `∃X. φ` is identical with `in_X` in place of `is_x`, but no
//! uniqueness constraint is added (sets need not be singletons).
//!
//! ## Universal first-order
//!
//! `∀x. φ` is compiled as `¬∃x. ¬φ` and then minimized via the existing
//! `complement` + `determinize` pipeline. This is sound iff `φ` is in
//! the restricted fragment (the `classify_formula` invariant).
//!
//! # Out of scope for this module
//!
//! - **Weighted (semiring) lifting.** This module compiles the
//!   *Boolean* fragment to an unweighted SFA. The `Constant(k)` MSO
//!   variant is treated as `True` (k = 1) or `False` (k = 0); other
//!   weights are not supported yet. Lifting to a true weighted
//!   automaton over a semiring is a Phase 7 follow-up.
//! - **Universal second-order.** `∀X. φ` is `Full MSO` per
//!   `classify_formula` and falls outside the restricted fragment;
//!   `compile_formula` returns `MsoCompileError::FullMsoUnsupported`
//!   when it encounters one.
//!
//! # Tests
//!
//! See `compile_tests.rs` (sibling module) for round-trip property
//! tests that compare compiled-automaton `accepts` against the
//! `evaluate_formula_bool` direct evaluator over a fixed alphabet.

use crate::kat::BooleanTest;
use crate::symbolic::{BooleanAlgebra, KatBooleanAlgebra, SymbolicAutomaton};
use crate::weighted_mso::{classify_formula, MsoFormulaClass, WeightedMsoFormula};
use std::collections::{BTreeSet, HashSet};

/// Errors that can arise while compiling an MSO formula to an SFA.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsoCompileError {
    /// The formula is in the `Full MSO` fragment (contains `∀X` or
    /// unrestricted `∀x`) — outside the restricted fragment that
    /// `compile_formula` can handle.
    FullMsoUnsupported {
        /// Human-readable reason (which fragment-specific feature
        /// triggered the error).
        reason: String,
    },
    /// The formula contains a `Constant(k)` with a non-Boolean value.
    /// Only `"true"`, `"false"`, `"0"`, and `"1"` are recognized.
    NonBooleanConstant {
        /// The unrecognized constant string.
        value: String,
    },
}

impl std::fmt::Display for MsoCompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MsoCompileError::FullMsoUnsupported { reason } => {
                write!(f, "MSO compile error: full MSO fragment is unsupported ({})", reason)
            },
            MsoCompileError::NonBooleanConstant { value } => {
                write!(f, "MSO compile error: non-Boolean constant `{}`", value)
            },
        }
    }
}

impl std::error::Error for MsoCompileError {}

/// Atom name conventions.
///
/// All three families share the same `String → bool` alphabet so that
/// arbitrary subsets of constraint families compose via the existing
/// `KatBooleanAlgebra::and / or / not` operators.
pub mod atom {
    /// Atom name for "current position carries label `a`".
    pub fn label(a: &str) -> String {
        format!("label_{}", a)
    }

    /// Atom name for "current position is assigned to first-order
    /// variable `x`".
    pub fn is_var(x: &str) -> String {
        format!("is_{}", x)
    }

    /// Atom name for "current position is a member of second-order
    /// variable `X`".
    pub fn in_set(set_var: &str) -> String {
        format!("in_{}", set_var)
    }
}

/// Build a `KatBooleanAlgebra` covering all atoms used by `formula`
/// over the given fixed label alphabet.
///
/// The atom set is a closed-world enumeration: every label, every
/// free first-order variable, every free second-order variable, plus
/// every variable bound by a quantifier in `formula`. Bound variables
/// must be included because the body's compiled SFA references them
/// before existential projection erases them.
pub fn build_algebra(formula: &WeightedMsoFormula, label_alphabet: &[String]) -> KatBooleanAlgebra {
    let mut atoms: BTreeSet<String> = BTreeSet::new();
    for label in label_alphabet {
        atoms.insert(atom::label(label));
    }
    let mut fo_vars: HashSet<String> = HashSet::new();
    let mut so_vars: HashSet<String> = HashSet::new();
    collect_all_variables(formula, &mut fo_vars, &mut so_vars);
    for v in &fo_vars {
        atoms.insert(atom::is_var(v));
    }
    for v in &so_vars {
        atoms.insert(atom::in_set(v));
    }
    KatBooleanAlgebra::new(atoms.into_iter().collect())
}

fn collect_all_variables(
    formula: &WeightedMsoFormula,
    first_order: &mut HashSet<String>,
    second_order: &mut HashSet<String>,
) {
    use WeightedMsoFormula::*;
    let mut work = vec![formula];
    while let Some(formula) = work.pop() {
        match formula {
            Constant(_) => {},
            AtomicPos { var, .. } | NegAtomicPos { var, .. } => {
                first_order.insert(var.clone());
            },
            Order { x, y } | NegOrder { x, y } => {
                first_order.insert(x.clone());
                first_order.insert(y.clone());
            },
            InSet { var, set_var } | NotInSet { var, set_var } => {
                first_order.insert(var.clone());
                second_order.insert(set_var.clone());
            },
            Or(left, right) | And(left, right) => {
                work.push(right);
                work.push(left);
            },
            ExistsFirst { var, body } | ForallFirst { var, body } => {
                first_order.insert(var.clone());
                work.push(body);
            },
            ExistsSecond { var, body } | ForallSecond { var, body } => {
                second_order.insert(var.clone());
                work.push(body);
            },
        }
    }
}

// ════════════════════════════════════════════════════════════════════
// Atomic compilations
// ════════════════════════════════════════════════════════════════════

/// Compile a `Pₐ(x)` atom to a 3-state NFA over the given algebra.
///
/// The NFA accepts a word iff there exists a position `i` such that
/// (a) `is_x` holds at `i` and (b) `label_a` holds at `i`. The
/// uniqueness of `i` is enforced separately by intersecting with the
/// uniqueness automaton for `x`.
///
/// State layout:
/// - `q0` (initial, non-accepting): no witness seen yet. Loops on
///   `¬is_x`. Transitions to `q1` on `is_x ∧ label_a`. Transitions
///   to a sink on `is_x ∧ ¬label_a` (the witness was found but had
///   the wrong label).
/// - `q1` (accepting): witness has been seen. Loops on anything.
fn compile_atomic_pos(
    label: &str,
    var: &str,
    algebra: &KatBooleanAlgebra,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let mut sfa = SymbolicAutomaton::new(algebra.clone());
    let q0 = sfa.add_state(false, Some(format!("q0[Pa({},{})]", label, var)));
    let q1 = sfa.add_state(true, Some(format!("q1[Pa({},{})]", label, var)));
    sfa.set_initial(q0);

    let is_var = BooleanTest::Atom(atom::is_var(var));
    let label_a = BooleanTest::Atom(atom::label(label));
    let not_is_var = algebra.not(&is_var);

    // q0 →[¬is_x]→ q0 (skip non-witness positions)
    sfa.add_transition(q0, q0, not_is_var.clone());
    // q0 →[is_x ∧ label_a]→ q1 (witness with correct label)
    let witness_correct = algebra.and(&is_var, &label_a);
    sfa.add_transition(q0, q1, witness_correct);
    // q1 →[true]→ q1 (loop)
    sfa.add_transition(q1, q1, algebra.true_pred());

    sfa
}

/// Compile a negated atomic `¬Pₐ(x)` — accepts iff the witness for
/// `x` does NOT have label `a`.
fn compile_neg_atomic_pos(
    label: &str,
    var: &str,
    algebra: &KatBooleanAlgebra,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let mut sfa = SymbolicAutomaton::new(algebra.clone());
    let q0 = sfa.add_state(false, Some(format!("q0[~Pa({},{})]", label, var)));
    let q1 = sfa.add_state(true, Some(format!("q1[~Pa({},{})]", label, var)));
    sfa.set_initial(q0);

    let is_var = BooleanTest::Atom(atom::is_var(var));
    let label_a = BooleanTest::Atom(atom::label(label));
    let not_is_var = algebra.not(&is_var);
    let not_label_a = algebra.not(&label_a);

    sfa.add_transition(q0, q0, not_is_var);
    let witness_wrong = algebra.and(&is_var, &not_label_a);
    sfa.add_transition(q0, q1, witness_wrong);
    sfa.add_transition(q1, q1, algebra.true_pred());

    sfa
}

/// Compile `x ∈ X` — accepts iff the witness position for `x` has
/// `in_X` set.
fn compile_in_set(
    var: &str,
    set_var: &str,
    algebra: &KatBooleanAlgebra,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let mut sfa = SymbolicAutomaton::new(algebra.clone());
    let q0 = sfa.add_state(false, Some(format!("q0[{} ∈ {}]", var, set_var)));
    let q1 = sfa.add_state(true, Some(format!("q1[{} ∈ {}]", var, set_var)));
    sfa.set_initial(q0);

    let is_var = BooleanTest::Atom(atom::is_var(var));
    let in_x = BooleanTest::Atom(atom::in_set(set_var));
    let not_is_var = algebra.not(&is_var);

    sfa.add_transition(q0, q0, not_is_var);
    let hit = algebra.and(&is_var, &in_x);
    sfa.add_transition(q0, q1, hit);
    sfa.add_transition(q1, q1, algebra.true_pred());

    sfa
}

/// Compile `¬(x ∈ X)`.
fn compile_not_in_set(
    var: &str,
    set_var: &str,
    algebra: &KatBooleanAlgebra,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let mut sfa = SymbolicAutomaton::new(algebra.clone());
    let q0 = sfa.add_state(false, Some(format!("q0[~({} ∈ {})]", var, set_var)));
    let q1 = sfa.add_state(true, Some(format!("q1[~({} ∈ {})]", var, set_var)));
    sfa.set_initial(q0);

    let is_var = BooleanTest::Atom(atom::is_var(var));
    let in_x = BooleanTest::Atom(atom::in_set(set_var));
    let not_is_var = algebra.not(&is_var);
    let not_in_x = algebra.not(&in_x);

    sfa.add_transition(q0, q0, not_is_var);
    let miss = algebra.and(&is_var, &not_in_x);
    sfa.add_transition(q0, q1, miss);
    sfa.add_transition(q1, q1, algebra.true_pred());

    sfa
}

/// Compile `x ≤ y` — accepts iff the witness for `x` precedes (or
/// equals) the witness for `y` in the input word.
///
/// State layout:
/// - `q_init` (initial): neither x nor y witnessed.
/// - `q_x_seen`: x has been witnessed; waiting for y.
/// - `q_xy_eq` (accepting): x and y were the same position.
/// - `q_y_after` (accepting): y was seen strictly after x.
fn compile_order(
    x: &str,
    y: &str,
    algebra: &KatBooleanAlgebra,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let mut sfa = SymbolicAutomaton::new(algebra.clone());
    let q_init = sfa.add_state(false, Some(format!("q_init[{}≤{}]", x, y)));
    let q_x_seen = sfa.add_state(false, Some(format!("q_x_seen[{}≤{}]", x, y)));
    let q_xy_eq = sfa.add_state(true, Some(format!("q_xy_eq[{}≤{}]", x, y)));
    let q_y_after = sfa.add_state(true, Some(format!("q_y_after[{}≤{}]", x, y)));
    sfa.set_initial(q_init);

    let is_x = BooleanTest::Atom(atom::is_var(x));
    let is_y = BooleanTest::Atom(atom::is_var(y));
    let not_is_x = algebra.not(&is_x);
    let not_is_y = algebra.not(&is_y);
    let neither = algebra.and(&not_is_x, &not_is_y);

    // q_init: skip non-witness positions
    sfa.add_transition(q_init, q_init, neither.clone());
    // q_init →[is_x ∧ is_y]→ q_xy_eq (same position witnesses both)
    let both = algebra.and(&is_x, &is_y);
    sfa.add_transition(q_init, q_xy_eq, both);
    // q_init →[is_x ∧ ¬is_y]→ q_x_seen
    let only_x = algebra.and(&is_x, &not_is_y);
    sfa.add_transition(q_init, q_x_seen, only_x);

    // q_x_seen: skip non-y positions
    sfa.add_transition(q_x_seen, q_x_seen, not_is_y.clone());
    // q_x_seen →[is_y]→ q_y_after
    sfa.add_transition(q_x_seen, q_y_after, is_y);

    // q_xy_eq, q_y_after: loop on anything
    sfa.add_transition(q_xy_eq, q_xy_eq, algebra.true_pred());
    sfa.add_transition(q_y_after, q_y_after, algebra.true_pred());

    sfa
}

/// Compile `¬(x ≤ y)` — accepts iff the witness for `x` strictly
/// follows the witness for `y`.
fn compile_neg_order(
    x: &str,
    y: &str,
    algebra: &KatBooleanAlgebra,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    // ¬(x ≤ y) ≡ y < x ≡ y precedes x AND y ≠ x.
    let mut sfa = SymbolicAutomaton::new(algebra.clone());
    let q_init = sfa.add_state(false, Some(format!("q_init[~({}≤{})]", x, y)));
    let q_y_seen = sfa.add_state(false, Some(format!("q_y_seen[~({}≤{})]", x, y)));
    let q_x_after = sfa.add_state(true, Some(format!("q_x_after[~({}≤{})]", x, y)));
    sfa.set_initial(q_init);

    let is_x = BooleanTest::Atom(atom::is_var(x));
    let is_y = BooleanTest::Atom(atom::is_var(y));
    let not_is_x = algebra.not(&is_x);
    let not_is_y = algebra.not(&is_y);
    let neither = algebra.and(&not_is_x, &not_is_y);

    sfa.add_transition(q_init, q_init, neither);
    let only_y = algebra.and(&is_y, &not_is_x);
    sfa.add_transition(q_init, q_y_seen, only_y);
    sfa.add_transition(q_y_seen, q_y_seen, not_is_x.clone());
    sfa.add_transition(q_y_seen, q_x_after, is_x);
    sfa.add_transition(q_x_after, q_x_after, algebra.true_pred());

    sfa
}

// ════════════════════════════════════════════════════════════════════
// Uniqueness automaton (well-formedness side condition)
// ════════════════════════════════════════════════════════════════════

/// Build the uniqueness automaton for a first-order variable.
///
/// Accepts iff `is_x` holds at exactly one position in the input.
/// 3-state DFA:
/// - `q0` (initial, non-accepting): no witness yet. Loops on `¬is_x`,
///   transitions to `q1` on `is_x`.
/// - `q1` (accepting): witness seen. Loops on `¬is_x`, transitions
///   to `q_dead` on a second `is_x`.
/// - `q_dead` (rejecting): two or more witnesses. Loops on anything.
pub fn build_unique_var_automaton(
    var: &str,
    algebra: &KatBooleanAlgebra,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let mut sfa = SymbolicAutomaton::new(algebra.clone());
    let q0 = sfa.add_state(false, Some(format!("u0[{}]", var)));
    let q1 = sfa.add_state(true, Some(format!("u1[{}]", var)));
    let q_dead = sfa.add_state(false, Some(format!("u_dead[{}]", var)));
    sfa.set_initial(q0);

    let is_x = BooleanTest::Atom(atom::is_var(var));
    let not_is_x = algebra.not(&is_x);

    sfa.add_transition(q0, q0, not_is_x.clone());
    sfa.add_transition(q0, q1, is_x.clone());
    sfa.add_transition(q1, q1, not_is_x);
    sfa.add_transition(q1, q_dead, is_x);
    sfa.add_transition(q_dead, q_dead, algebra.true_pred());

    sfa
}

// ════════════════════════════════════════════════════════════════════
// Existential projection — implements ∃x. φ
// ════════════════════════════════════════════════════════════════════

/// Project out a first-order variable from a compiled SFA.
///
/// Implementation: NFA-style erasure. The body SFA's transitions
/// reference `is_x` in their guard predicates; after projection, we
/// want a single SFA whose accepted language is "∃ assignment of x
/// such that the body accepts". The standard MSO construction is to
/// project the alphabet — replace every `is_x = true` symbol in the
/// input by a wildcard. Implementation: rewrite each transition's
/// guard using `existential_closure`, which substitutes both
/// truth-values for the projected atom and ORs the results.
///
/// The body SFA must already be intersected with the uniqueness
/// automaton for `x` so that the projection is well-defined.
fn project_first_order(
    body: &SymbolicAutomaton<KatBooleanAlgebra>,
    var: &str,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let atom_name = atom::is_var(var);
    project_atom(body, &atom_name)
}

/// Project out a second-order variable.
fn project_second_order(
    body: &SymbolicAutomaton<KatBooleanAlgebra>,
    set_var: &str,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let atom_name = atom::in_set(set_var);
    project_atom(body, &atom_name)
}

/// Generic atom projection: rewrite every transition guard so that
/// the named atom is existentially closed (replaced by `True` in the
/// satisfaction structure).
///
/// The transformation maps a `BooleanTest` `g` to `g[atom := true] ∨
/// g[atom := false]`. This is the propositional existential closure
/// — equivalent to "either truth value of the atom satisfies the
/// guard". The result is a SFA over the same alphabet but whose
/// transitions no longer reference the projected atom.
fn project_atom(
    body: &SymbolicAutomaton<KatBooleanAlgebra>,
    atom_name: &str,
) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let algebra = body.algebra.clone();
    let mut result = SymbolicAutomaton::new(algebra.clone());
    for state in &body.states {
        result.add_state(state.is_accepting, state.label.clone());
    }
    for &init in &body.initial_states {
        result.set_initial(init);
    }
    for trans in &body.transitions {
        let projected = existential_closure(&trans.guard, atom_name);
        if algebra.is_satisfiable(&projected) {
            result.add_transition(trans.from, trans.to, projected);
        }
    }
    result
}

/// Compute the propositional existential closure of `pred` over `atom`.
///
/// Returns `pred[atom := true] ∨ pred[atom := false]`. The result is
/// equivalent to "there exists a truth value for `atom` that
/// satisfies `pred`".
fn existential_closure(pred: &BooleanTest, atom_name: &str) -> BooleanTest {
    let with_true = substitute_atom(pred, atom_name, true);
    let with_false = substitute_atom(pred, atom_name, false);
    BooleanTest::Or(Box::new(with_true), Box::new(with_false))
}

/// Substitute a fixed truth value for the named atom inside a
/// `BooleanTest`. Pure propositional substitution.
fn substitute_atom(pred: &BooleanTest, atom_name: &str, value: bool) -> BooleanTest {
    enum Task<'test> {
        Visit(&'test BooleanTest),
        Not,
        And,
        Or,
    }

    let mut tasks = vec![Task::Visit(pred)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(BooleanTest::True) => values.push(BooleanTest::True),
            Task::Visit(BooleanTest::False) => values.push(BooleanTest::False),
            Task::Visit(BooleanTest::Atom(name)) => values.push(if name == atom_name {
                if value {
                    BooleanTest::True
                } else {
                    BooleanTest::False
                }
            } else {
                BooleanTest::Atom(name.clone())
            }),
            Task::Visit(BooleanTest::Not(body)) => {
                tasks.push(Task::Not);
                tasks.push(Task::Visit(body));
            },
            Task::Visit(BooleanTest::And(left, right)) => {
                tasks.push(Task::And);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(BooleanTest::Or(left, right)) => {
                tasks.push(Task::Or);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Not => {
                let body = values.pop().expect("Boolean substitution lost negand");
                values.push(BooleanTest::Not(Box::new(body)));
            },
            Task::And | Task::Or => {
                let right = values.pop().expect("Boolean substitution lost binary RHS");
                let left = values.pop().expect("Boolean substitution lost binary LHS");
                values.push(match task {
                    Task::And => BooleanTest::And(Box::new(left), Box::new(right)),
                    Task::Or => BooleanTest::Or(Box::new(left), Box::new(right)),
                    _ => unreachable!(),
                });
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("Boolean substitution produced no value")
}

// ════════════════════════════════════════════════════════════════════
// Top-level recursive compilation
// ════════════════════════════════════════════════════════════════════

/// Compile an MSO formula into a SymbolicAutomaton over the given
/// algebra. The algebra MUST be the one returned by `build_algebra`
/// for this formula and label alphabet — passing a different algebra
/// produces undefined behavior.
pub fn compile_with_algebra(
    formula: &WeightedMsoFormula,
    algebra: &KatBooleanAlgebra,
) -> Result<SymbolicAutomaton<KatBooleanAlgebra>, MsoCompileError> {
    use WeightedMsoFormula::*;

    enum Task<'formula> {
        Visit(&'formula WeightedMsoFormula),
        And,
        Or,
        ExistsFirst(&'formula str),
        ExistsSecond(&'formula str),
        ForallFirst(&'formula str),
    }

    // Reject Full MSO upfront.
    let class = classify_formula(formula);
    if class == MsoFormulaClass::Full {
        return Err(MsoCompileError::FullMsoUnsupported {
            reason: "formula contains ∀X or unrestricted ∀x".to_string(),
        });
    }

    let mut tasks = vec![Task::Visit(formula)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Constant(value)) => values.push(match value.as_str() {
                "true" | "1" => make_universal(algebra),
                "false" | "0" => make_empty(algebra),
                other => {
                    return Err(MsoCompileError::NonBooleanConstant { value: other.to_string() });
                },
            }),
            Task::Visit(AtomicPos { label, var }) => {
                values.push(compile_atomic_pos(label, var, algebra));
            },
            Task::Visit(NegAtomicPos { label, var }) => {
                values.push(compile_neg_atomic_pos(label, var, algebra));
            },
            Task::Visit(InSet { var, set_var }) => {
                values.push(compile_in_set(var, set_var, algebra));
            },
            Task::Visit(NotInSet { var, set_var }) => {
                values.push(compile_not_in_set(var, set_var, algebra));
            },
            Task::Visit(Order { x, y }) => values.push(compile_order(x, y, algebra)),
            Task::Visit(NegOrder { x, y }) => values.push(compile_neg_order(x, y, algebra)),
            Task::Visit(And(left, right)) => {
                tasks.push(Task::And);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(Or(left, right)) => {
                tasks.push(Task::Or);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(ExistsFirst { var, body }) => {
                tasks.push(Task::ExistsFirst(var));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(ExistsSecond { var, body }) => {
                tasks.push(Task::ExistsSecond(var));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(ForallFirst { var, body }) => {
                tasks.push(Task::ForallFirst(var));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(ForallSecond { .. }) => {
                return Err(MsoCompileError::FullMsoUnsupported {
                    reason: "∀X is in the Full MSO fragment".to_string(),
                });
            },
            Task::And | Task::Or => {
                let right = values.pop().expect("weighted-MSO compiler lost binary RHS");
                let left = values.pop().expect("weighted-MSO compiler lost binary LHS");
                values.push(match task {
                    Task::And => left.intersect(&right),
                    Task::Or => left.union(&right),
                    _ => unreachable!(),
                });
            },
            Task::ExistsFirst(var) => {
                let body = values.pop().expect("weighted-MSO compiler lost ∃x body");
                let unique = build_unique_var_automaton(var, algebra);
                values.push(project_first_order(&body.intersect(&unique), var));
            },
            Task::ExistsSecond(var) => {
                let body = values.pop().expect("weighted-MSO compiler lost ∃X body");
                values.push(project_second_order(&body, var));
            },
            Task::ForallFirst(var) => {
                let body = values.pop().expect("weighted-MSO compiler lost ∀x body");
                let unique = build_unique_var_automaton(var, algebra);
                let constrained = body.complement().intersect(&unique);
                values.push(project_first_order(&constrained, var).complement());
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    Ok(values
        .pop()
        .expect("weighted-MSO compiler produced no automaton"))
}

/// Convenience wrapper: build the algebra from the formula's free
/// variables + the given label alphabet, then compile.
pub fn compile_formula(
    formula: &WeightedMsoFormula,
    label_alphabet: &[String],
) -> Result<(KatBooleanAlgebra, SymbolicAutomaton<KatBooleanAlgebra>), MsoCompileError> {
    let algebra = build_algebra(formula, label_alphabet);
    let sfa = compile_with_algebra(formula, &algebra)?;
    Ok((algebra, sfa))
}

/// Build a 1-state SFA accepting every word.
fn make_universal(algebra: &KatBooleanAlgebra) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let mut sfa = SymbolicAutomaton::new(algebra.clone());
    let q0 = sfa.add_state(true, Some("⊤".to_string()));
    sfa.set_initial(q0);
    sfa.add_transition(q0, q0, algebra.true_pred());
    sfa
}

/// Build a 1-state SFA accepting nothing.
fn make_empty(algebra: &KatBooleanAlgebra) -> SymbolicAutomaton<KatBooleanAlgebra> {
    let mut sfa = SymbolicAutomaton::new(algebra.clone());
    let q0 = sfa.add_state(false, Some("⊥".to_string()));
    sfa.set_initial(q0);
    sfa.add_transition(q0, q0, algebra.true_pred());
    sfa
}

// ════════════════════════════════════════════════════════════════════
// Re-export helpers used by external callers
// ════════════════════════════════════════════════════════════════════

pub use crate::weighted_mso::{
    free_set_variables as exported_free_set_variables, free_variables as exported_free_variables,
};
