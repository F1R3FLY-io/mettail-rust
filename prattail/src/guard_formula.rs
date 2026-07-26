//! **The `where`-guard substrate IR** — the wire by which a source-level `where` clause reaches
//! Dovetail/SFT.
//!
//! # The rule this module exists to implement
//!
//! > *If it is in a `where` clause, it is a semantic predicate. All semantic predicates are
//! > evaluated by Dovetail/SFT — at compile time where they can be statically evaluated, at run
//! > time otherwise. If it is in an `if` condition, it is evaluated by Rholang.*
//!
//! The same expression `x == 5` is decided **here** when it sits in a `where`, and by the
//! Rholang interpreter when it sits in an `if`. Nothing depends on the shape of the expression:
//! the *syntactic position* selects the evaluator. This module is the evaluator for the
//! `where` position.
//!
//! # Why an IR at all
//!
//! There are two front ends that need to reach the substrate with the same guard, and they hold
//! the guard in two different representations:
//!
//! | front end | representation | leg |
//! |---|---|---|
//! | `mettail_languages::rhocalc` | the surface `Proc` | run time (the COMM decision) |
//! | `mettail_rholang_runtime` | the lowered `rhoapi::Par` | compile time (discharge) |
//!
//! If each encoded straight into `PresburgerPred`/`AnyPred` there would be two encoders with no
//! shared vocabulary and therefore two places for the two legs to drift apart — the
//! *divergence-A* shape this tree has been burned by before. [`GuardFormula`] is the single
//! vocabulary both encoders target, so "the compile-time leg and the run-time leg decided the
//! same guard differently" becomes a statement about one data type rather than about two
//! unrelated code paths.
//!
//! ```text
//!    Proc ──encode──┐                        ┌── static_verdict ──▶ Valid / Unsatisfiable
//!                   ├──▶  GuardFormula  ──▶──┤                      Contingent / Undecided
//!    Par  ──encode──┘                        └── ground_verdict ──▶ Sat3
//! ```
//!
//! # The three legs
//!
//! | leg | question | procedure | entry point |
//! |---|---|---|---|
//! | **static** | is `φ` true under *every* assignment to the receive's binders? | Büchi/Bartzis–Bultan automata for Presburger; `BooleanAlgebra::is_satisfiable` for the algebraic sorts | [`static_verdict`] |
//! | **ground** | does `φ` hold under *this* assignment (the payload has arrived)? | direct evaluation in each sort's algebra | [`ground_verdict_with`] |
//! | **policy** | what does an *undecided* answer mean at a guard site? | [`dont_know_policy`] — ★ the consensus seam |
//!
//! # ⚠ The bounded-domain caveat (load-bearing for soundness)
//!
//! [`PresburgerPred`]'s decision procedure runs over a **bounded** integer domain
//! (`SubstrateConfig::bit_width`, default [`DEFAULT_BIT_WIDTH`] = 16 ⇒ `[-32768, 32767]`).
//! Over a bounded domain **neither**
//!
//! ```text
//!    valid over 2^w  ⟹  valid over ℤ          (counterexample: x < 40000)
//!    unsat over 2^w  ⟹  unsat over ℤ          (counterexample: x > 40000)
//! ```
//!
//! holds. A [`StaticVerdict`] is therefore a statement **about the bounded domain named in the
//! [`SubstrateConfig`] that produced it**, and it may *not* on its own license an artifact
//! change (such as omitting a `Receive.condition`). Consumers that change the artifact must
//! fence the substrate verdict against an evaluator with the concrete semantics — which is
//! exactly what `mettail_rholang_runtime::guard_discharge::classify` does. The verdict type
//! carries the domain it was decided over ([`StaticVerdict::domain`]) so a consumer cannot
//! misread it by accident.
//!
//! The **ground** leg has no such caveat: it evaluates concretely on `i64`, so it is exact.
//!
//! # What this module deliberately does NOT do
//!
//! It does not match terms. `t matches {φ | ψ}` — the separating conjunction — is an
//! [`GuardAtomKind::Spatial`] atom, and this module has **no** procedure for it: the only way a
//! spatial atom is ever decided is through the resolver a caller passes to
//! [`ground_verdict_with`]. That is a structural guarantee, not a convention: there is no code
//! path here that could become "the second, divergent matcher". The structural leg belongs to
//! the reducer's own spatial matcher (Dovetail's structural core), which is precisely the
//! documented disposition for a `StructuralPattern` obligation.

use std::collections::{BTreeMap, HashMap};

use crate::algebra_tower::Sat3;
use crate::any_algebra::{AnyDomain, AnyPred, Sort};
use crate::kat::BooleanTest;
use crate::presburger::{
    evaluate_presburger, is_satisfiable_nfa, IntAssignment, LinearConstraint, PresburgerPred,
    DEFAULT_BIT_WIDTH,
};
use crate::string_algebra::{StrPred, StringAlgebra};
use crate::symbolic::{BooleanAlgebra, IntervalAlgebra, IntervalPred, KatBooleanAlgebra};

// ══════════════════════════════════════════════════════════════════════════════
// SubstrateConfig — the named domain every static verdict is relative to
// ══════════════════════════════════════════════════════════════════════════════

/// The bounded domain the static leg decides over.
///
/// Named and carried explicitly (rather than defaulted silently) because a [`StaticVerdict`] is
/// only meaningful relative to it — see the bounded-domain caveat in the module docs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SubstrateConfig {
    /// Two's-complement bit width for the Presburger automata. Integers range over
    /// `[-2^(bit_width-1), 2^(bit_width-1))`.
    pub bit_width: usize,
}

impl SubstrateConfig {
    /// The default configuration: [`DEFAULT_BIT_WIDTH`].
    pub const DEFAULT: Self = Self { bit_width: DEFAULT_BIT_WIDTH };

    /// Inclusive lower bound of the integer domain.
    pub fn int_min(self) -> i64 {
        -(1i64 << (self.bit_width - 1))
    }

    /// EXCLUSIVE upper bound of the integer domain (half-open, matching [`IntervalAlgebra`]).
    pub fn int_max_exclusive(self) -> i64 {
        1i64 << (self.bit_width - 1)
    }

    /// The interval algebra over this configuration's integer domain.
    pub fn interval_algebra(self) -> IntervalAlgebra {
        IntervalAlgebra::new(self.int_min(), self.int_max_exclusive())
    }
}

impl Default for SubstrateConfig {
    fn default() -> Self {
        Self::DEFAULT
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GuardVarMap — binder ⇄ substrate variable index
// ══════════════════════════════════════════════════════════════════════════════

/// The receive site's binder → substrate-variable-index map.
///
/// A `where` guard's free variables are exactly the binders of the receive it guards. The
/// substrate indexes variables positionally ([`LinearConstraint`]'s `terms` are
/// `(var_index, coefficient)`), so an encoder must fix an order once and use it for both the
/// formula and every assignment. This type is that fixed order.
///
/// Interning is idempotent, so an encoder can walk the guard in any order and still get a
/// stable map.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GuardVarMap {
    names: Vec<String>,
    index: BTreeMap<String, usize>,
}

impl GuardVarMap {
    /// An empty map.
    pub fn new() -> Self {
        Self::default()
    }

    /// An empty map with room for `capacity` binders — a receive knows its binder count up
    /// front, so the allocation is preallocated rather than grown.
    pub fn with_capacity(capacity: usize) -> Self {
        GuardVarMap { names: Vec::with_capacity(capacity), index: BTreeMap::new() }
    }

    /// The index of `name`, interning it if new. Idempotent.
    pub fn intern(&mut self, name: &str) -> usize {
        if let Some(&existing) = self.index.get(name) {
            return existing;
        }
        let idx = self.names.len();
        self.names.push(name.to_string());
        self.index.insert(name.to_string(), idx);
        idx
    }

    /// The index of `name` if it has been interned.
    pub fn index_of(&self, name: &str) -> Option<usize> {
        self.index.get(name).copied()
    }

    /// The name interned at `idx`.
    pub fn name(&self, idx: usize) -> Option<&str> {
        self.names.get(idx).map(String::as_str)
    }

    /// The number of interned binders.
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// `true` iff no binder has been interned.
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    /// The interned names, in index order.
    pub fn names(&self) -> &[String] {
        &self.names
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GuardValue / GuardAssignment — the ground side of the wire
// ══════════════════════════════════════════════════════════════════════════════

/// A concrete value a binder can take at COMM time.
///
/// A guard-relevant projection of [`AnyDomain`]: the sorts a `where` guard's *scalar* operands
/// can inhabit. Structured payloads (bags, maps, processes) are not [`GuardValue`]s — a guard
/// over one of those is a structural question and reaches the substrate as a
/// [`GuardAtomKind::Spatial`] atom instead.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GuardValue {
    /// Integer-sorted binder.
    Int(i64),
    /// String-sorted binder.
    Str(String),
    /// Boolean-sorted binder.
    Bool(bool),
}

impl GuardValue {
    /// The sort of this value.
    pub fn sort(&self) -> Sort {
        match self {
            GuardValue::Int(_) => Sort::Int,
            GuardValue::Str(_) => Sort::Str,
            GuardValue::Bool(_) => Sort::Bool,
        }
    }

    /// This value as an [`AnyDomain`] element of its sort.
    ///
    /// `Bool` is the interesting case: [`AnyDomain::Bool`] is a *truth assignment* keyed by
    /// proposition name, not a bare `bool`, because [`KatBooleanAlgebra`] is natively n-ary.
    /// A single boolean binder therefore becomes the singleton assignment `{name ↦ b}`, and the
    /// n-ary case is assembled by [`GuardAssignment::truth_assignment`].
    pub fn to_any_domain(&self, name: &str) -> AnyDomain {
        match self {
            GuardValue::Int(v) => AnyDomain::Int(*v),
            GuardValue::Str(s) => AnyDomain::Str(s.clone()),
            GuardValue::Bool(b) => {
                let mut map = HashMap::with_capacity(1);
                map.insert(name.to_string(), *b);
                AnyDomain::Bool(map)
            },
        }
    }
}

/// A (possibly partial) assignment of the receive's binders to concrete values.
///
/// Partial by design: at COMM time some binders may be bound to payloads that are not scalar
/// (a bag, a process), and a guard mentioning one of those is undecidable by the scalar legs.
/// A missing binder yields [`Sat3::DontKnow`] rather than a default — silently defaulting an
/// unbound integer to `0` (which is what [`IntAssignment::get`] does on its own) would turn a
/// *don't know* into a confidently wrong verdict.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GuardAssignment {
    values: Vec<Option<GuardValue>>,
}

impl GuardAssignment {
    /// An assignment sized for `len` binders, all unbound.
    pub fn with_len(len: usize) -> Self {
        GuardAssignment { values: vec![None; len] }
    }

    /// Bind `idx` to `value`, growing the assignment if needed.
    pub fn bind(&mut self, idx: usize, value: GuardValue) {
        if self.values.len() <= idx {
            self.values.resize(idx + 1, None);
        }
        self.values[idx] = Some(value);
    }

    /// The value bound at `idx`, if any.
    pub fn get(&self, idx: usize) -> Option<&GuardValue> {
        self.values.get(idx).and_then(Option::as_ref)
    }

    /// The number of slots (bound or not).
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// `true` iff there are no slots.
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// The integer-sorted projection as an [`IntAssignment`], or `None` if any index in
    /// `required` is unbound or bound to a non-integer.
    ///
    /// The `required` check is what keeps [`IntAssignment::get`]'s zero-default from masking an
    /// unbound variable.
    pub fn int_assignment(&self, required: &[usize]) -> Option<IntAssignment> {
        let width = required.iter().copied().max().map_or(0, |m| m + 1);
        let mut out = vec![0i64; width];
        for &idx in required {
            match self.get(idx) {
                Some(GuardValue::Int(v)) => out[idx] = *v,
                _ => return None,
            }
        }
        Some(IntAssignment::new(out))
    }

    /// The boolean-sorted projection as a truth assignment keyed by binder name, or `None` if
    /// any name in `required` is unbound or bound to a non-boolean.
    pub fn truth_assignment(
        &self,
        vars: &GuardVarMap,
        required: &[String],
    ) -> Option<HashMap<String, bool>> {
        let mut out = HashMap::with_capacity(required.len());
        for name in required {
            let idx = vars.index_of(name)?;
            match self.get(idx) {
                Some(GuardValue::Bool(b)) => {
                    out.insert(name.clone(), *b);
                },
                _ => return None,
            }
        }
        Some(out)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// The formula
// ══════════════════════════════════════════════════════════════════════════════

/// A comparison operator of the guard sublanguage.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CmpOp {
    /// `==`
    Eq,
    /// `!=`
    Ne,
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,
}

impl CmpOp {
    /// Decide this comparison on two values of the same sort. `None` when the sorts differ (a
    /// cross-sort comparison is not a question this operator answers).
    pub fn decide(self, left: &GuardValue, right: &GuardValue) -> Option<bool> {
        if left.sort() != right.sort() {
            return None;
        }
        let ordering = left.partial_cmp(right)?;
        Some(match self {
            CmpOp::Eq => ordering.is_eq(),
            CmpOp::Ne => !ordering.is_eq(),
            CmpOp::Lt => ordering.is_lt(),
            CmpOp::Le => ordering.is_le(),
            CmpOp::Gt => ordering.is_gt(),
            CmpOp::Ge => ordering.is_ge(),
        })
    }

    /// This operator with its operands swapped (`a < b` ⇔ `b > a`).
    pub fn flipped(self) -> CmpOp {
        match self {
            CmpOp::Eq => CmpOp::Eq,
            CmpOp::Ne => CmpOp::Ne,
            CmpOp::Lt => CmpOp::Gt,
            CmpOp::Le => CmpOp::Ge,
            CmpOp::Gt => CmpOp::Lt,
            CmpOp::Ge => CmpOp::Le,
        }
    }
}

/// Why an atom is opaque to this module's decision procedures.
///
/// Every variant is a *permanent* statement about the substrate's coverage, never a transient
/// failure: an atom carrying one of these is undecidable **here** and must be decided by a
/// resolver the caller supplies, or not at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum GuardAtomKind {
    /// `t matches φ` — spatial satisfaction, including the **separating conjunction**
    /// `{φ | ψ}` whose associative-commutative-with-remainder semantics belong to the
    /// reducer's own matcher. This module has no procedure for it *by construction*; see the
    /// module docs.
    Spatial,
    /// Integer arithmetic outside the linear fragment — `x * y` with two variables, `/`, `%`.
    /// Presburger arithmetic is linear by definition, so these are outside the theory rather
    /// than merely hard. Statically undecided; **concretely** decidable by a caller's resolver,
    /// since at COMM time the operands are ground.
    NonLinear,
    /// A process-shaped guard: a send, a `new`, a nested `for`. Not a predicate at all.
    /// Fails closed at every leg.
    ProcessShaped,
    /// A constructor the encoder does not cover.
    Uncovered,
}

/// An atom this module cannot decide, carrying an id the encoding front end can resolve.
///
/// The `id` indexes a caller-owned side table of the original guard fragment. Keeping the
/// payload out of `prattail` is what makes it *impossible* for this crate to grow a spatial
/// matcher of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GuardAtom {
    /// Index into the encoder's side table of opaque fragments.
    pub id: u32,
    /// Why it is opaque here.
    pub kind: GuardAtomKind,
}

/// The substrate image of a `where` guard.
///
/// A boolean combination of **sorted atoms**, each discharged by the substrate module that owns
/// its sort:
///
/// | variant | sort | procedure |
/// |---|---|---|
/// | [`Linear`](GuardFormula::Linear) | `Int` | [`PresburgerPred`] — automata-based, exact over the configured domain |
/// | [`Prop`](GuardFormula::Prop) | `Bool` | [`KatBooleanAlgebra`] — exact |
/// | [`Scalar`](GuardFormula::Scalar) | `Str` (any non-`Int` scalar) | the sort's [`BooleanAlgebra`] — exact |
/// | [`ScalarRel`](GuardFormula::ScalarRel) | two non-`Int` variables | exact at run time; statically undecided ([`AnyPred`] is unary) |
/// | [`Atom`](GuardFormula::Atom) | — | never decided here; see [`GuardAtomKind`] |
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GuardFormula {
    /// The guard `true`.
    True,
    /// The guard `false`.
    False,
    /// Linear integer arithmetic over [`GuardVarMap`] indices.
    Linear(PresburgerPred),
    /// A propositional combination of boolean-sorted binders. [`BooleanTest::Atom`] names are
    /// binder names (not indices) because [`KatBooleanAlgebra`]'s domain is a truth assignment
    /// keyed by name — the sort is natively n-ary, so it needs no positional encoding.
    Prop(BooleanTest),
    /// A non-integer scalar binder constrained against a literal, as a unary [`AnyPred`] leaf
    /// applied to the value bound at `var`.
    Scalar {
        /// The [`GuardVarMap`] index the predicate constrains.
        var: usize,
        /// The leaf predicate, in its sort's algebra.
        pred: AnyPred,
    },
    /// A comparison between two non-integer scalar **variables**.
    ///
    /// [`AnyPred`] is a *unary* predicate, so it cannot relate two positions; this variant
    /// records the relation instead of fabricating one. Statically undecided, exactly decided
    /// at run time — which is the correct split under the rule (compile time where statically
    /// decidable, run time otherwise).
    ScalarRel {
        /// The comparison.
        op: CmpOp,
        /// Left operand's [`GuardVarMap`] index.
        left: usize,
        /// Right operand's [`GuardVarMap`] index.
        right: usize,
    },
    /// `φ and ψ`.
    And(Box<GuardFormula>, Box<GuardFormula>),
    /// `φ or ψ`.
    Or(Box<GuardFormula>, Box<GuardFormula>),
    /// `not φ`.
    Not(Box<GuardFormula>),
    /// `φ implies ψ`.
    Implies(Box<GuardFormula>, Box<GuardFormula>),
    /// An atom this module cannot decide.
    Atom(GuardAtom),
}

impl GuardFormula {
    /// `φ ∧ ψ`, with the two absorbing/unit simplifications applied.
    pub fn and(left: GuardFormula, right: GuardFormula) -> GuardFormula {
        match (left, right) {
            (GuardFormula::False, _) | (_, GuardFormula::False) => GuardFormula::False,
            (GuardFormula::True, other) | (other, GuardFormula::True) => other,
            (a, b) => GuardFormula::And(Box::new(a), Box::new(b)),
        }
    }

    /// `φ ∨ ψ`, with the two absorbing/unit simplifications applied.
    pub fn or(left: GuardFormula, right: GuardFormula) -> GuardFormula {
        match (left, right) {
            (GuardFormula::True, _) | (_, GuardFormula::True) => GuardFormula::True,
            (GuardFormula::False, other) | (other, GuardFormula::False) => other,
            (a, b) => GuardFormula::Or(Box::new(a), Box::new(b)),
        }
    }

    /// `¬φ`, collapsing a double negation and the two constants.
    pub fn not(inner: GuardFormula) -> GuardFormula {
        match inner {
            GuardFormula::True => GuardFormula::False,
            GuardFormula::False => GuardFormula::True,
            GuardFormula::Not(x) => *x,
            other => GuardFormula::Not(Box::new(other)),
        }
    }

    /// `φ ⇒ ψ`.
    pub fn implies(left: GuardFormula, right: GuardFormula) -> GuardFormula {
        GuardFormula::Implies(Box::new(left), Box::new(right))
    }

    /// `true` iff every leaf of this formula is decidable by one of this module's procedures —
    /// i.e. the formula contains no [`GuardFormula::Atom`].
    ///
    /// This is the predicate the measurement harness uses for *"does this guard form reach
    /// Dovetail/SFT?"*.
    pub fn reaches_substrate(&self) -> bool {
        match self {
            GuardFormula::Atom(_) => false,
            GuardFormula::True
            | GuardFormula::False
            | GuardFormula::Linear(_)
            | GuardFormula::Prop(_)
            | GuardFormula::Scalar { .. }
            | GuardFormula::ScalarRel { .. } => true,
            GuardFormula::Not(inner) => inner.reaches_substrate(),
            GuardFormula::And(a, b)
            | GuardFormula::Or(a, b)
            | GuardFormula::Implies(a, b) => {
                a.reaches_substrate() && b.reaches_substrate()
            },
        }
    }

    /// Every opaque atom in this formula, in traversal order.
    pub fn atoms(&self) -> Vec<GuardAtom> {
        let mut out = Vec::new();
        self.collect_atoms(&mut out);
        out
    }

    fn collect_atoms(&self, out: &mut Vec<GuardAtom>) {
        match self {
            GuardFormula::Atom(a) => out.push(*a),
            GuardFormula::Not(inner) => inner.collect_atoms(out),
            GuardFormula::And(a, b) | GuardFormula::Or(a, b) | GuardFormula::Implies(a, b) => {
                a.collect_atoms(out);
                b.collect_atoms(out);
            },
            _ => {},
        }
    }

    /// The `Int`-sorted variable indices this formula constrains.
    pub fn int_vars(&self) -> Vec<usize> {
        let mut out = Vec::new();
        self.collect_int_vars(&mut out);
        out.sort_unstable();
        out.dedup();
        out
    }

    fn collect_int_vars(&self, out: &mut Vec<usize>) {
        match self {
            GuardFormula::Linear(p) => collect_presburger_vars(p, out),
            GuardFormula::Not(inner) => inner.collect_int_vars(out),
            GuardFormula::And(a, b) | GuardFormula::Or(a, b) | GuardFormula::Implies(a, b) => {
                a.collect_int_vars(out);
                b.collect_int_vars(out);
            },
            _ => {},
        }
    }

    /// The boolean-sorted binder names this formula constrains.
    pub fn prop_names(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.collect_prop_names(&mut out);
        out.sort();
        out.dedup();
        out
    }

    fn collect_prop_names(&self, out: &mut Vec<String>) {
        match self {
            GuardFormula::Prop(t) => collect_test_atoms(t, out),
            GuardFormula::Not(inner) => inner.collect_prop_names(out),
            GuardFormula::And(a, b) | GuardFormula::Or(a, b) | GuardFormula::Implies(a, b) => {
                a.collect_prop_names(out);
                b.collect_prop_names(out);
            },
            _ => {},
        }
    }

    /// The non-integer scalar variable indices this formula constrains.
    pub fn scalar_vars(&self) -> Vec<usize> {
        let mut out = Vec::new();
        self.collect_scalar_vars(&mut out);
        out.sort_unstable();
        out.dedup();
        out
    }

    fn collect_scalar_vars(&self, out: &mut Vec<usize>) {
        match self {
            GuardFormula::Scalar { var, .. } => out.push(*var),
            GuardFormula::ScalarRel { left, right, .. } => {
                out.push(*left);
                out.push(*right);
            },
            GuardFormula::Not(inner) => inner.collect_scalar_vars(out),
            GuardFormula::And(a, b) | GuardFormula::Or(a, b) | GuardFormula::Implies(a, b) => {
                a.collect_scalar_vars(out);
                b.collect_scalar_vars(out);
            },
            _ => {},
        }
    }
}

fn collect_presburger_vars(pred: &PresburgerPred, out: &mut Vec<usize>) {
    match pred {
        PresburgerPred::True | PresburgerPred::False => {},
        PresburgerPred::Atom(c) => out.extend(c.terms.iter().map(|&(v, _)| v)),
        PresburgerPred::And(a, b) | PresburgerPred::Or(a, b) => {
            collect_presburger_vars(a, out);
            collect_presburger_vars(b, out);
        },
        PresburgerPred::Not(inner) => collect_presburger_vars(inner, out),
        PresburgerPred::Exists { body, .. } => collect_presburger_vars(body, out),
    }
}

fn collect_test_atoms(test: &BooleanTest, out: &mut Vec<String>) {
    match test {
        BooleanTest::True | BooleanTest::False => {},
        BooleanTest::Atom(name) => out.push(name.clone()),
        BooleanTest::Not(inner) => collect_test_atoms(inner, out),
        BooleanTest::And(a, b) | BooleanTest::Or(a, b) => {
            collect_test_atoms(a, out);
            collect_test_atoms(b, out);
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// ★ THE CONSENSUS SEAM — what `Sat3::DontKnow` means at a guard site
// ══════════════════════════════════════════════════════════════════════════════

/// Where a guard verdict is being consumed. The policy point takes this so a future answer can
/// differ per site without the decision spreading to more than one function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GuardSiteKind {
    /// A `where` clause on a guarded receive: the verdict decides whether a COMM fires.
    ReceiveWhere,
    /// A compile-time discharge decision: the verdict decides whether the guard is omitted from
    /// the emitted artifact.
    CompileTimeDischarge,
}

/// What an undecided ([`Sat3::DontKnow`]) verdict means at a guard site.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DontKnowPolicy {
    /// The guard does **not** pass: the COMM does not fire, the guard is not discharged.
    FailClosedBlock,
    /// The guard passes. Never selected today; present so that "fail closed" is a *choice* the
    /// policy point records rather than an accident of the code's shape.
    FailOpenFire,
}

impl DontKnowPolicy {
    /// The boolean this policy assigns to an undecided guard.
    pub fn as_bool(self) -> bool {
        matches!(self, DontKnowPolicy::FailOpenFire)
    }
}

/// ★ **THE POLICY POINT.** The single place in the tree where an undecided guard verdict becomes
/// a decision.
///
/// # Why this is a seam and not just a default
///
/// [`Sat3::DontKnow`] is documented as *"undecided within the available **budget** / procedure"*
/// ([`crate::algebra_tower::Sat3::DontKnow`]). The *budget* half of that is the problem: if a
/// budget-dependent `DontKnow` decided whether a COMM fires, then two nodes running with
/// different budgets could disagree about whether a COMM **happened** — a consensus fork, not a
/// performance difference. The procedure half is benign (every node runs the same procedure and
/// reaches the same `DontKnow`).
///
/// The two halves are not distinguishable from the `Sat3` value alone, so this function treats
/// the whole variant as consensus-affecting.
///
/// # ⚠ PROVISIONAL — pending a USER decision
///
/// The interim answer is [`DontKnowPolicy::FailClosedBlock`]: an undecided guard blocks. It is
/// the safe direction (a COMM that does not fire leaves a resting, observable continuation;
/// a COMM that fires wrongly is unrecoverable), and it matches the behaviour every existing
/// decider already had — `mettail_languages::rhocalc::receive::eval_guard_disposition`'s
/// `Declines` yields no rewrite, and f1r3node's `guard_passes` maps every non-`true` result to
/// `false`. So adopting it changes nothing observable today.
///
/// It is **not** asserted to be the right long-run answer. The alternatives are a real design
/// question — reject the *program* at compile time rather than blocking at run time; or forbid
/// budget-bearing procedures from the guard path entirely so `DontKnow` can only ever be the
/// benign procedural kind. That choice is the USER's.
pub fn dont_know_policy(_site: GuardSiteKind) -> DontKnowPolicy {
    DontKnowPolicy::FailClosedBlock
}

/// Resolve a three-valued verdict to the boolean a guard site acts on, routing the undecided
/// case through [`dont_know_policy`].
pub fn resolve_verdict(verdict: Sat3, site: GuardSiteKind) -> bool {
    match verdict {
        Sat3::Sat => true,
        Sat3::Unsat => false,
        Sat3::DontKnow => dont_know_policy(site).as_bool(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// The STATIC leg
// ══════════════════════════════════════════════════════════════════════════════

/// Why a static verdict is undecided.
///
/// Distinguishing these matters: only [`UndecidedCause::Budget`] is the consensus-affecting
/// shape that [`dont_know_policy`] exists for. The others are *procedure coverage* facts —
/// every node computes the same one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UndecidedCause {
    /// The formula mixes sorts in a shape outside the decidable fragment this module
    /// implements (see [`static_verdict`]'s coverage table). Deterministic.
    FragmentNotCovered,
    /// The formula contains an atom this module has no procedure for
    /// ([`GuardFormula::Atom`]). Deterministic.
    OpaqueAtom,
    /// A decision procedure exhausted a resource bound. ★ The consensus-affecting shape.
    /// No procedure in this module produces it today; the variant exists so that a future
    /// budget-bearing procedure cannot be added without confronting the seam.
    Budget,
}

/// The static leg's answer for a guard.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StaticVerdict {
    /// True under every assignment **over the domain in [`StaticVerdict::domain`]**.
    Valid(SubstrateConfig),
    /// False under every assignment over that domain.
    Unsatisfiable(SubstrateConfig),
    /// Proved to have both a satisfying and a falsifying assignment: the guard genuinely
    /// depends on the payload, so it belongs to the run-time leg.
    Contingent(SubstrateConfig),
    /// Not decided.
    Undecided(UndecidedCause),
}

impl StaticVerdict {
    /// The domain this verdict is relative to, or `None` for [`StaticVerdict::Undecided`].
    ///
    /// ⚠ A [`StaticVerdict::Valid`] is **only** valid over this domain — see the bounded-domain
    /// caveat in the module docs. A consumer that changes an artifact on the strength of a
    /// static verdict must fence it against a concrete-semantics evaluator.
    pub fn domain(self) -> Option<SubstrateConfig> {
        match self {
            StaticVerdict::Valid(c)
            | StaticVerdict::Unsatisfiable(c)
            | StaticVerdict::Contingent(c) => Some(c),
            StaticVerdict::Undecided(_) => None,
        }
    }

    /// This verdict as a two-valued answer when it settles the guard, `None` otherwise.
    pub fn settled(self) -> Option<bool> {
        match self {
            StaticVerdict::Valid(_) => Some(true),
            StaticVerdict::Unsatisfiable(_) => Some(false),
            StaticVerdict::Contingent(_) | StaticVerdict::Undecided(_) => None,
        }
    }

    /// A short stable tag for diagnostics and golden files.
    pub fn tag(self) -> &'static str {
        match self {
            StaticVerdict::Valid(_) => "Valid",
            StaticVerdict::Unsatisfiable(_) => "Unsatisfiable",
            StaticVerdict::Contingent(_) => "Contingent",
            StaticVerdict::Undecided(_) => "Undecided",
        }
    }
}

/// Decide a guard **statically** — before any payload exists.
///
/// # The decidable fragment
///
/// Satisfiability of a boolean combination of atoms from *different* theories is a theory-
/// combination problem. This module implements the fragment where combination is sound and
/// complete without a solver, and answers [`UndecidedCause::FragmentNotCovered`] everywhere
/// else. Answering `Undecided` is always sound (the consumer falls back to the run-time leg),
/// so incompleteness is a coverage question, never a correctness one.
///
/// | shape | procedure | exact? |
/// |---|---|---|
/// | every atom is `Int` | fold the whole boolean structure into one [`PresburgerPred`], decide with the NFA emptiness test | ✅ over the configured domain |
/// | every atom is `Bool` | fold into one [`BooleanTest`], decide with [`KatBooleanAlgebra`] | ✅ |
/// | every atom is a `Scalar` on **one** variable | fold into one [`AnyPred`], decide in that sort's algebra | ✅ |
/// | a **conjunction** whose conjuncts each fall in one of the above groups | decide each group, combine with [`Sat3::and`] — sound and complete because the groups' variables are disjoint by construction (a binder has exactly one sort) | ✅ |
/// | anything else | [`UndecidedCause::FragmentNotCovered`] | — |
///
/// # Method
///
/// `φ` is **valid** iff `¬φ` is unsatisfiable, and **unsatisfiable** iff `φ` is. So one
/// satisfiability procedure, called twice, yields all three settled answers; the fourth,
/// `Contingent`, is `φ` and `¬φ` both satisfiable, which is a *proof* that the guard depends on
/// the payload.
pub fn static_verdict(formula: &GuardFormula, config: SubstrateConfig) -> StaticVerdict {
    let sat_positive = satisfiable(formula, config);
    let negated = GuardFormula::not(formula.clone());
    let sat_negative = satisfiable(&negated, config);

    match (sat_positive, sat_negative) {
        // ¬φ has no model ⇒ φ holds everywhere.
        (_, Sat3::Unsat) => StaticVerdict::Valid(config),
        // φ has no model ⇒ φ fails everywhere.
        (Sat3::Unsat, _) => StaticVerdict::Unsatisfiable(config),
        // Both have models ⇒ the guard genuinely depends on the payload.
        (Sat3::Sat, Sat3::Sat) => StaticVerdict::Contingent(config),
        _ => StaticVerdict::Undecided(undecided_cause(formula)),
    }
}

fn undecided_cause(formula: &GuardFormula) -> UndecidedCause {
    if formula.atoms().is_empty() {
        UndecidedCause::FragmentNotCovered
    } else {
        UndecidedCause::OpaqueAtom
    }
}

/// Three-valued satisfiability of a guard formula. `Sat3::Sat` means *a model exists over the
/// configured domain*, `Sat3::Unsat` means *provably none does*, `Sat3::DontKnow` means the
/// formula is outside the fragment [`static_verdict`] documents.
pub fn satisfiable(formula: &GuardFormula, config: SubstrateConfig) -> Sat3 {
    match classify_group(formula) {
        Some(group) => decide_single_group(formula, group, config),
        // Mixed groups: sound only for a conjunction, where the groups' variable sets are
        // disjoint by construction and satisfiability therefore distributes.
        None => match conjuncts(formula) {
            Some(parts) => combine_conjuncts(&parts, config),
            None => Sat3::DontKnow,
        },
    }
}

/// Decide satisfiability of a formula that is already known to sit in ONE theory group.
///
/// Total and **non-recursive** with respect to [`satisfiable`]: it never re-enters the mixed
/// branch, so [`combine_conjuncts`] can call it on each regrouped conjunction without any risk
/// of cycling back through the partitioning that produced it.
fn decide_single_group(
    formula: &GuardFormula,
    group: FormulaGroup,
    config: SubstrateConfig,
) -> Sat3 {
    match group {
        FormulaGroup::Constant(true) => Sat3::Sat,
        FormulaGroup::Constant(false) => Sat3::Unsat,
        FormulaGroup::Int => match to_presburger(formula) {
            Some(pred) => Sat3::from_decidable(is_satisfiable_nfa(&pred, config.bit_width)),
            None => Sat3::DontKnow,
        },
        FormulaGroup::Bool => match to_boolean_test(formula) {
            Some(test) => {
                let algebra = KatBooleanAlgebra::from_test(&test);
                Sat3::from_decidable(algebra.is_satisfiable(&test))
            },
            None => Sat3::DontKnow,
        },
        FormulaGroup::Scalar(var) => match to_any_pred(formula, var) {
            Some(pred) => scalar_satisfiable(&pred, config),
            None => Sat3::DontKnow,
        },
    }
}

/// Decide a conjunction whose conjuncts fall in different theory groups.
///
/// # Why the conjuncts must first be REGROUPED, not folded one by one
///
/// `Sat3::and` combines two independent satisfiability answers. Two conjuncts are independent
/// only when their variable sets are disjoint — which holds *across* groups (a binder has
/// exactly one sort, so an `Int` binder and a `Bool` binder are different binders, and two
/// scalar groups are keyed by distinct variables) but emphatically **not within** one. `x == 1`
/// and `x == 2` are each satisfiable while their conjunction is not, so folding them with
/// `Sat3::and` would answer `Sat` for an unsatisfiable formula — unsound in the direction that
/// matters. Conjuncts are therefore partitioned by group, conjoined *inside* each group's own
/// theory (where the decision procedure sees them together), and only the per-group answers are
/// combined.
///
/// `Unsat` annihilates, so a proven-unsatisfiable group settles the whole conjunction even when
/// another conjunct was outside the covered fragment.
fn combine_conjuncts(parts: &[&GuardFormula], config: SubstrateConfig) -> Sat3 {
    let mut int_parts: Vec<GuardFormula> = Vec::new();
    let mut bool_parts: Vec<GuardFormula> = Vec::new();
    let mut scalar_parts: BTreeMap<usize, Vec<GuardFormula>> = BTreeMap::new();
    let mut saw_uncovered = false;
    let mut constants = true;

    for part in parts {
        match classify_group(part) {
            Some(FormulaGroup::Constant(b)) => constants &= b,
            Some(FormulaGroup::Int) => int_parts.push((*part).clone()),
            Some(FormulaGroup::Bool) => bool_parts.push((*part).clone()),
            Some(FormulaGroup::Scalar(var)) => {
                scalar_parts.entry(var).or_default().push((*part).clone());
            },
            None => saw_uncovered = true,
        }
    }

    if !constants {
        return Sat3::Unsat;
    }

    let mut groups: Vec<GuardFormula> = Vec::with_capacity(2 + scalar_parts.len());
    if let Some(conjoined) = conjoin(int_parts) {
        groups.push(conjoined);
    }
    if let Some(conjoined) = conjoin(bool_parts) {
        groups.push(conjoined);
    }
    for (_, group) in scalar_parts {
        if let Some(conjoined) = conjoin(group) {
            groups.push(conjoined);
        }
    }

    let mut answer = Sat3::Sat;
    for group in &groups {
        let verdict = match classify_group(group) {
            Some(single) => decide_single_group(group, single, config),
            // Unreachable by construction (every member of `group` classified into the same
            // single theory, and the theories are closed under conjunction), but answering
            // `DontKnow` rather than recursing keeps the non-recursion property structural.
            None => Sat3::DontKnow,
        };
        answer = answer.and(verdict);
    }
    match (answer, saw_uncovered) {
        // `Unsat` annihilates a conjunction, so it settles the answer even alongside a conjunct
        // the fragment does not cover.
        (Sat3::Unsat, _) => Sat3::Unsat,
        (settled, false) => settled,
        (_, true) => Sat3::DontKnow,
    }
}

/// Conjoin a group of formulas into one, or `None` when the group is empty.
fn conjoin(mut parts: Vec<GuardFormula>) -> Option<GuardFormula> {
    let mut acc = parts.pop()?;
    while let Some(next) = parts.pop() {
        acc = GuardFormula::and(next, acc);
    }
    Some(acc)
}

/// The single theory a formula's atoms all belong to, if there is one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FormulaGroup {
    /// No atoms at all — the formula folds to a constant.
    Constant(bool),
    /// Every atom is `Int`-sorted.
    Int,
    /// Every atom is `Bool`-sorted.
    Bool,
    /// Every atom is a `Scalar` on this one variable.
    Scalar(usize),
}

fn classify_group(formula: &GuardFormula) -> Option<FormulaGroup> {
    let has_opaque = !formula.atoms().is_empty();
    if has_opaque {
        return None;
    }
    let int_vars = formula.int_vars();
    let prop_names = formula.prop_names();
    let scalar_vars = formula.scalar_vars();
    let has_int = has_linear_atom(formula);
    let has_prop = !prop_names.is_empty() || has_prop_constant_atom(formula);
    let has_scalar = !scalar_vars.is_empty();

    match (has_int, has_prop, has_scalar) {
        (false, false, false) => Some(FormulaGroup::Constant(fold_constant(formula)?)),
        (true, false, false) => {
            let _ = int_vars;
            Some(FormulaGroup::Int)
        },
        (false, true, false) => Some(FormulaGroup::Bool),
        // A `ScalarRel` relates two variables, which no unary algebra can express, so a formula
        // containing one is never a single-variable scalar group.
        (false, false, true) if scalar_vars.len() == 1 && !has_scalar_rel(formula) => {
            Some(FormulaGroup::Scalar(scalar_vars[0]))
        },
        _ => None,
    }
}

fn has_linear_atom(formula: &GuardFormula) -> bool {
    match formula {
        GuardFormula::Linear(_) => true,
        GuardFormula::Not(inner) => has_linear_atom(inner),
        GuardFormula::And(a, b) | GuardFormula::Or(a, b) | GuardFormula::Implies(a, b) => {
            has_linear_atom(a) || has_linear_atom(b)
        },
        _ => false,
    }
}

fn has_prop_constant_atom(formula: &GuardFormula) -> bool {
    match formula {
        GuardFormula::Prop(_) => true,
        GuardFormula::Not(inner) => has_prop_constant_atom(inner),
        GuardFormula::And(a, b) | GuardFormula::Or(a, b) | GuardFormula::Implies(a, b) => {
            has_prop_constant_atom(a) || has_prop_constant_atom(b)
        },
        _ => false,
    }
}

fn has_scalar_rel(formula: &GuardFormula) -> bool {
    match formula {
        GuardFormula::ScalarRel { .. } => true,
        GuardFormula::Not(inner) => has_scalar_rel(inner),
        GuardFormula::And(a, b) | GuardFormula::Or(a, b) | GuardFormula::Implies(a, b) => {
            has_scalar_rel(a) || has_scalar_rel(b)
        },
        _ => false,
    }
}

fn fold_constant(formula: &GuardFormula) -> Option<bool> {
    match formula {
        GuardFormula::True => Some(true),
        GuardFormula::False => Some(false),
        GuardFormula::Not(inner) => fold_constant(inner).map(|b| !b),
        GuardFormula::And(a, b) => Some(fold_constant(a)? && fold_constant(b)?),
        GuardFormula::Or(a, b) => Some(fold_constant(a)? || fold_constant(b)?),
        GuardFormula::Implies(a, b) => Some(!fold_constant(a)? || fold_constant(b)?),
        _ => None,
    }
}

/// Flatten a formula into its top-level `∧` conjuncts, or `None` if the top level is not a
/// conjunction.
fn conjuncts(formula: &GuardFormula) -> Option<Vec<&GuardFormula>> {
    match formula {
        GuardFormula::And(_, _) => {
            let mut out = Vec::new();
            push_conjuncts(formula, &mut out);
            Some(out)
        },
        _ => None,
    }
}

fn push_conjuncts<'a>(formula: &'a GuardFormula, out: &mut Vec<&'a GuardFormula>) {
    match formula {
        GuardFormula::And(a, b) => {
            push_conjuncts(a, out);
            push_conjuncts(b, out);
        },
        other => out.push(other),
    }
}

/// Fold an all-`Int` formula into a single [`PresburgerPred`], preserving the boolean structure
/// (Presburger is closed under `∧`, `∨`, `¬`, so nothing is lost).
fn to_presburger(formula: &GuardFormula) -> Option<PresburgerPred> {
    Some(match formula {
        GuardFormula::True => PresburgerPred::True,
        GuardFormula::False => PresburgerPred::False,
        GuardFormula::Linear(p) => p.clone(),
        GuardFormula::And(a, b) => {
            PresburgerPred::And(Box::new(to_presburger(a)?), Box::new(to_presburger(b)?))
        },
        GuardFormula::Or(a, b) => {
            PresburgerPred::Or(Box::new(to_presburger(a)?), Box::new(to_presburger(b)?))
        },
        GuardFormula::Not(inner) => PresburgerPred::Not(Box::new(to_presburger(inner)?)),
        GuardFormula::Implies(a, b) => PresburgerPred::Or(
            Box::new(PresburgerPred::Not(Box::new(to_presburger(a)?))),
            Box::new(to_presburger(b)?),
        ),
        _ => return None,
    })
}

/// Fold an all-`Bool` formula into a single [`BooleanTest`].
fn to_boolean_test(formula: &GuardFormula) -> Option<BooleanTest> {
    Some(match formula {
        GuardFormula::True => BooleanTest::True,
        GuardFormula::False => BooleanTest::False,
        GuardFormula::Prop(t) => t.clone(),
        GuardFormula::And(a, b) => {
            BooleanTest::And(Box::new(to_boolean_test(a)?), Box::new(to_boolean_test(b)?))
        },
        GuardFormula::Or(a, b) => {
            BooleanTest::Or(Box::new(to_boolean_test(a)?), Box::new(to_boolean_test(b)?))
        },
        GuardFormula::Not(inner) => BooleanTest::Not(Box::new(to_boolean_test(inner)?)),
        GuardFormula::Implies(a, b) => BooleanTest::Or(
            Box::new(BooleanTest::Not(Box::new(to_boolean_test(a)?))),
            Box::new(to_boolean_test(b)?),
        ),
        _ => return None,
    })
}

/// Fold a single-variable scalar formula into one [`AnyPred`].
fn to_any_pred(formula: &GuardFormula, var: usize) -> Option<AnyPred> {
    Some(match formula {
        GuardFormula::True => AnyPred::True,
        GuardFormula::False => AnyPred::False,
        GuardFormula::Scalar { var: v, pred } if *v == var => pred.clone(),
        GuardFormula::And(a, b) => AnyPred::And(
            Box::new(to_any_pred(a, var)?),
            Box::new(to_any_pred(b, var)?),
        ),
        GuardFormula::Or(a, b) => {
            AnyPred::Or(Box::new(to_any_pred(a, var)?), Box::new(to_any_pred(b, var)?))
        },
        GuardFormula::Not(inner) => AnyPred::Not(Box::new(to_any_pred(inner, var)?)),
        GuardFormula::Implies(a, b) => AnyPred::Or(
            Box::new(AnyPred::Not(Box::new(to_any_pred(a, var)?))),
            Box::new(to_any_pred(b, var)?),
        ),
        _ => return None,
    })
}

/// Satisfiability of a single-variable [`AnyPred`], dispatched to the leaf sort's algebra.
///
/// Every scalar sort a guard can mention is decided exactly; a leaf sort with no
/// guard-reachable encoding answers [`Sat3::DontKnow`] rather than guessing.
fn scalar_satisfiable(pred: &AnyPred, config: SubstrateConfig) -> Sat3 {
    match leaf_sort_of(pred) {
        Some(Sort::Str) => {
            let algebra = StringAlgebra::new();
            match project_str(pred) {
                Some(p) => Sat3::from_decidable(algebra.is_satisfiable(&p)),
                None => Sat3::DontKnow,
            }
        },
        Some(Sort::Int) => {
            let algebra = config.interval_algebra();
            match project_interval(pred) {
                Some(p) => Sat3::from_decidable(algebra.is_satisfiable(&p)),
                None => Sat3::DontKnow,
            }
        },
        _ => Sat3::DontKnow,
    }
}

/// The single leaf sort of an `AnyPred` whose leaves are all of one sort, if there is one.
fn leaf_sort_of(pred: &AnyPred) -> Option<Sort> {
    match pred {
        AnyPred::True | AnyPred::False => None,
        AnyPred::And(a, b) | AnyPred::Or(a, b) => match (leaf_sort_of(a), leaf_sort_of(b)) {
            (Some(x), Some(y)) if x == y => Some(x),
            (Some(x), None) => Some(x),
            (None, Some(y)) => Some(y),
            _ => None,
        },
        AnyPred::Not(inner) => leaf_sort_of(inner),
        other => other.leaf_sort(),
    }
}

/// Project a single-sort `AnyPred` down to a `StrPred`, preserving boolean structure.
fn project_str(pred: &AnyPred) -> Option<StrPred> {
    Some(match pred {
        AnyPred::True => StrPred::any(),
        AnyPred::False => StrPred::Empty,
        AnyPred::Str(p) => p.clone(),
        AnyPred::And(a, b) => StrPred::Inter(Box::new(project_str(a)?), Box::new(project_str(b)?)),
        AnyPred::Or(a, b) => StrPred::Alt(Box::new(project_str(a)?), Box::new(project_str(b)?)),
        AnyPred::Not(inner) => StrPred::Compl(Box::new(project_str(inner)?)),
        _ => return None,
    })
}

/// Project a single-sort `AnyPred` down to an `IntervalPred`, preserving boolean structure.
fn project_interval(pred: &AnyPred) -> Option<IntervalPred> {
    Some(match pred {
        AnyPred::True => IntervalPred::True,
        AnyPred::False => IntervalPred::False,
        AnyPred::Int(p) => p.clone(),
        // `IntervalPred` has no ∧/∨ constructor; the algebra normalizes unions, so a
        // conjunction/disjunction is expressed through the algebra rather than the syntax.
        AnyPred::And(a, b) => {
            let algebra = SubstrateConfig::DEFAULT.interval_algebra();
            algebra.and(&project_interval(a)?, &project_interval(b)?)
        },
        AnyPred::Or(a, b) => {
            let algebra = SubstrateConfig::DEFAULT.interval_algebra();
            algebra.or(&project_interval(a)?, &project_interval(b)?)
        },
        AnyPred::Not(inner) => IntervalPred::Not(Box::new(project_interval(inner)?)),
        _ => return None,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// The GROUND leg
// ══════════════════════════════════════════════════════════════════════════════

/// Decide a guard **at COMM time**, under a concrete assignment of the receive's binders.
///
/// `resolve_atom` decides the atoms this module has no procedure for. It is a parameter rather
/// than a match arm on purpose: a spatial atom must be decided by the reducer's own matcher, and
/// making that the *only* way one can be decided is what keeps a second, divergent matcher from
/// growing here (see the module docs).
///
/// # ★ The connective discipline is NOT full Kleene
///
/// The connectives below are **left-strict, then short-circuiting**: the left operand is always
/// evaluated, and the right operand is evaluated only when the left did not settle the result.
/// An undecided *left* operand therefore propagates as undecided even where Kleene's tables
/// would answer (`DontKnow ∨ Sat` is `DontKnow` here, not `Sat`).
///
/// This is deliberate and it is a soundness property, not a simplification. f1r3node evaluates
/// **both** operands of `EAnd`/`EOr` unconditionally and its `guard_passes` maps any error or
/// non-boolean result to `false`. So a full-Kleene `or` that answered `Sat` from the right
/// operand alone would fire host-side while the reducer did **not** fire — unsoundness in the
/// firing direction. The discipline here reproduces, arm for arm, the one
/// `mettail_languages::rhocalc::receive::eval_guard_disposition` was measured to have.
pub fn ground_verdict_with<F>(
    formula: &GuardFormula,
    assignment: &GuardAssignment,
    vars: &GuardVarMap,
    config: SubstrateConfig,
    resolve_atom: &mut F,
) -> Sat3
where
    F: FnMut(GuardAtom) -> Sat3,
{
    match formula {
        GuardFormula::True => Sat3::Sat,
        GuardFormula::False => Sat3::Unsat,

        GuardFormula::Linear(pred) => {
            let mut required = Vec::new();
            collect_presburger_vars(pred, &mut required);
            required.sort_unstable();
            required.dedup();
            match assignment.int_assignment(&required) {
                Some(int_assignment) => Sat3::from_decidable(evaluate_presburger(
                    pred,
                    &int_assignment,
                    config.bit_width,
                )),
                None => Sat3::DontKnow,
            }
        },

        GuardFormula::Prop(test) => {
            let mut required = Vec::new();
            collect_test_atoms(test, &mut required);
            required.sort();
            required.dedup();
            match assignment.truth_assignment(vars, &required) {
                Some(truth) => {
                    let algebra = KatBooleanAlgebra::from_test(test);
                    Sat3::from_decidable(algebra.evaluate(test, &truth))
                },
                None => Sat3::DontKnow,
            }
        },

        GuardFormula::Scalar { var, pred } => match (assignment.get(*var), vars.name(*var)) {
            (Some(value), Some(name)) => {
                let domain = value.to_any_domain(name);
                match evaluate_scalar(pred, &domain, config) {
                    Some(b) => Sat3::from_decidable(b),
                    None => Sat3::DontKnow,
                }
            },
            _ => Sat3::DontKnow,
        },

        GuardFormula::ScalarRel { op, left, right } => {
            match (assignment.get(*left), assignment.get(*right)) {
                (Some(a), Some(b)) => match op.decide(a, b) {
                    Some(v) => Sat3::from_decidable(v),
                    None => Sat3::DontKnow,
                },
                _ => Sat3::DontKnow,
            }
        },

        // `a and b`: left-strict, then short-circuit on a decided-FALSE left.
        GuardFormula::And(a, b) => {
            match ground_verdict_with(a, assignment, vars, config, resolve_atom) {
                Sat3::DontKnow => Sat3::DontKnow,
                Sat3::Unsat => Sat3::Unsat,
                Sat3::Sat => ground_verdict_with(b, assignment, vars, config, resolve_atom),
            }
        },

        // `a or b`: dual — short-circuit on a decided-TRUE left.
        GuardFormula::Or(a, b) => {
            match ground_verdict_with(a, assignment, vars, config, resolve_atom) {
                Sat3::DontKnow => Sat3::DontKnow,
                Sat3::Sat => Sat3::Sat,
                Sat3::Unsat => ground_verdict_with(b, assignment, vars, config, resolve_atom),
            }
        },

        // `a implies b ≡ (not a) or b`, i.e. the `Or` discipline on the negated antecedent:
        // a decided-FALSE antecedent short-circuits to true (vacuous truth).
        GuardFormula::Implies(a, b) => {
            match ground_verdict_with(a, assignment, vars, config, resolve_atom) {
                Sat3::DontKnow => Sat3::DontKnow,
                Sat3::Unsat => Sat3::Sat,
                Sat3::Sat => ground_verdict_with(b, assignment, vars, config, resolve_atom),
            }
        },

        GuardFormula::Not(inner) => {
            ground_verdict_with(inner, assignment, vars, config, resolve_atom).not()
        },

        GuardFormula::Atom(atom) => resolve_atom(*atom),
    }
}

/// [`ground_verdict_with`] with no atom resolver: every opaque atom is undecided.
pub fn ground_verdict(
    formula: &GuardFormula,
    assignment: &GuardAssignment,
    vars: &GuardVarMap,
    config: SubstrateConfig,
) -> Sat3 {
    ground_verdict_with(formula, assignment, vars, config, &mut |_| Sat3::DontKnow)
}

/// Evaluate a single-sort scalar [`AnyPred`] on a concrete element.
fn evaluate_scalar(pred: &AnyPred, elem: &AnyDomain, config: SubstrateConfig) -> Option<bool> {
    match elem {
        AnyDomain::Str(s) => {
            let algebra = StringAlgebra::new();
            Some(algebra.evaluate(&project_str(pred)?, s))
        },
        AnyDomain::Int(v) => {
            let algebra = config.interval_algebra();
            Some(algebra.evaluate(&project_interval(pred)?, v))
        },
        AnyDomain::Bool(truth) => {
            let test = project_bool(pred)?;
            let algebra = KatBooleanAlgebra::from_test(&test);
            Some(algebra.evaluate(&test, truth))
        },
        _ => None,
    }
}

fn project_bool(pred: &AnyPred) -> Option<BooleanTest> {
    Some(match pred {
        AnyPred::True => BooleanTest::True,
        AnyPred::False => BooleanTest::False,
        AnyPred::Bool(t) => t.clone(),
        AnyPred::And(a, b) => BooleanTest::And(Box::new(project_bool(a)?), Box::new(project_bool(b)?)),
        AnyPred::Or(a, b) => BooleanTest::Or(Box::new(project_bool(a)?), Box::new(project_bool(b)?)),
        AnyPred::Not(inner) => BooleanTest::Not(Box::new(project_bool(inner)?)),
        _ => return None,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Construction helpers for encoders
// ══════════════════════════════════════════════════════════════════════════════

/// A linear form `Σ aᵢ·xᵢ + c` over [`GuardVarMap`] indices — the shape an encoder builds while
/// walking an integer-sorted operand tree, before it becomes a [`LinearConstraint`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LinearForm {
    /// Coefficient terms `(var_index, coefficient)`, at most one entry per variable.
    pub terms: Vec<(usize, i64)>,
    /// The constant term.
    pub constant: i64,
}

impl LinearForm {
    /// The constant form `c`.
    pub fn constant(c: i64) -> Self {
        LinearForm { terms: Vec::new(), constant: c }
    }

    /// The form `1·x`.
    pub fn var(idx: usize) -> Self {
        LinearForm { terms: vec![(idx, 1)], constant: 0 }
    }

    /// `true` iff this form has no variable terms.
    pub fn is_constant(&self) -> bool {
        self.terms.is_empty()
    }

    /// `self + other`, merging coefficients. Returns `None` on overflow — an encoder must not
    /// silently wrap, because a wrapped coefficient would encode a *different* constraint.
    pub fn add(&self, other: &LinearForm) -> Option<LinearForm> {
        let mut terms: Vec<(usize, i64)> = Vec::with_capacity(self.terms.len() + other.terms.len());
        terms.extend_from_slice(&self.terms);
        for &(var, coeff) in &other.terms {
            match terms.iter_mut().find(|(v, _)| *v == var) {
                Some(slot) => slot.1 = slot.1.checked_add(coeff)?,
                None => terms.push((var, coeff)),
            }
        }
        terms.retain(|&(_, c)| c != 0);
        terms.sort_unstable_by_key(|&(v, _)| v);
        Some(LinearForm { terms, constant: self.constant.checked_add(other.constant)? })
    }

    /// `-self`. Returns `None` on overflow (`i64::MIN`).
    pub fn negate(&self) -> Option<LinearForm> {
        let mut terms = Vec::with_capacity(self.terms.len());
        for &(var, coeff) in &self.terms {
            terms.push((var, coeff.checked_neg()?));
        }
        Some(LinearForm { terms, constant: self.constant.checked_neg()? })
    }

    /// `self - other`.
    pub fn sub(&self, other: &LinearForm) -> Option<LinearForm> {
        self.add(&other.negate()?)
    }

    /// `k · self`. Returns `None` on overflow.
    pub fn scale(&self, k: i64) -> Option<LinearForm> {
        let mut terms = Vec::with_capacity(self.terms.len());
        for &(var, coeff) in &self.terms {
            let scaled = coeff.checked_mul(k)?;
            if scaled != 0 {
                terms.push((var, scaled));
            }
        }
        Some(LinearForm { terms, constant: self.constant.checked_mul(k)? })
    }

    /// The comparison `self ⋈ other` as a [`PresburgerPred`].
    ///
    /// Both sides are moved to the left (`self - other ⋈ 0`) and the constant to the right, so
    /// the result is always in [`LinearConstraint`]'s `Σ aᵢxᵢ ≤ b` normal form.
    pub fn compare(&self, op: CmpOp, other: &LinearForm) -> Option<PresburgerPred> {
        let diff = self.sub(other)?;
        // `Σ aᵢxᵢ + c ⋈ 0`  ⇔  `Σ aᵢxᵢ ⋈ -c`
        let rhs = diff.constant.checked_neg()?;
        let terms = diff.terms;
        Some(match op {
            CmpOp::Eq => PresburgerPred::eq(terms, rhs),
            CmpOp::Ne => PresburgerPred::neq(terms, rhs),
            CmpOp::Lt => PresburgerPred::lt(terms, rhs),
            CmpOp::Le => PresburgerPred::leq(terms, rhs),
            CmpOp::Gt => PresburgerPred::gt(terms, rhs),
            CmpOp::Ge => PresburgerPred::geq(terms, rhs),
        })
    }
}

/// The `AnyPred` leaf constraining a string-sorted binder to equal `literal`.
pub fn str_equals(literal: &str) -> AnyPred {
    AnyPred::Str(StrPred::Literal(literal.to_string()))
}

/// The `AnyPred` leaf constraining a string-sorted binder to differ from `literal`.
pub fn str_differs(literal: &str) -> AnyPred {
    AnyPred::Not(Box::new(str_equals(literal)))
}

/// The propositional atom for a boolean-sorted binder.
pub fn prop_var(name: &str) -> BooleanTest {
    BooleanTest::Atom(name.to_string())
}

/// A bare `LinearConstraint` in `Σ aᵢxᵢ ≤ b` form as a formula (exposed so an encoder can build
/// the brief's `PresburgerPred::Atom(LinearConstraint)` shape directly).
pub fn linear_atom(constraint: LinearConstraint) -> GuardFormula {
    GuardFormula::Linear(PresburgerPred::Atom(constraint))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg() -> SubstrateConfig {
        SubstrateConfig::DEFAULT
    }

    fn int_eq(var: usize, value: i64) -> GuardFormula {
        GuardFormula::Linear(PresburgerPred::eq(vec![(var, 1)], value))
    }

    fn int_lt(var: usize, value: i64) -> GuardFormula {
        GuardFormula::Linear(PresburgerPred::lt(vec![(var, 1)], value))
    }

    // ── GuardVarMap ──────────────────────────────────────────────────────────

    #[test]
    fn interning_is_idempotent_and_order_stable() {
        let mut vars = GuardVarMap::with_capacity(2);
        assert_eq!(vars.intern("x"), 0);
        assert_eq!(vars.intern("y"), 1);
        assert_eq!(vars.intern("x"), 0);
        assert_eq!(vars.name(1), Some("y"));
        assert_eq!(vars.index_of("y"), Some(1));
        assert_eq!(vars.len(), 2);
    }

    // ── The static leg ───────────────────────────────────────────────────────

    #[test]
    fn a_constant_true_guard_is_valid() {
        assert_eq!(static_verdict(&GuardFormula::True, cfg()), StaticVerdict::Valid(cfg()));
        assert_eq!(
            static_verdict(&GuardFormula::False, cfg()),
            StaticVerdict::Unsatisfiable(cfg())
        );
    }

    /// ★ THE CAPABILITY THE PREVIOUS COMPILE-TIME LEG DID NOT HAVE: an OPEN formula (it mentions
    /// a binder) decided statically. `rho_pure_eval` requires a binder-closed condition and
    /// declines this outright.
    #[test]
    fn an_open_tautology_is_statically_valid() {
        // x < x + 1  ⇔  x - x < 1  ⇔  0 < 1
        let x = LinearForm::var(0);
        let x_plus_1 = x.add(&LinearForm::constant(1)).expect("no overflow");
        let pred = x.compare(CmpOp::Lt, &x_plus_1).expect("no overflow");
        assert_eq!(
            static_verdict(&GuardFormula::Linear(pred), cfg()),
            StaticVerdict::Valid(cfg())
        );
    }

    #[test]
    fn an_open_contradiction_is_statically_unsatisfiable() {
        // x == 1 and x == 2
        let formula = GuardFormula::and(int_eq(0, 1), int_eq(0, 2));
        assert_eq!(
            static_verdict(&formula, cfg()),
            StaticVerdict::Unsatisfiable(cfg())
        );
    }

    #[test]
    fn a_payload_dependent_guard_is_contingent() {
        assert_eq!(static_verdict(&int_eq(0, 42), cfg()), StaticVerdict::Contingent(cfg()));
    }

    #[test]
    fn a_propositional_tautology_is_valid() {
        // b or not b
        let b = GuardFormula::Prop(prop_var("b"));
        let formula = GuardFormula::or(b.clone(), GuardFormula::not(b));
        assert_eq!(static_verdict(&formula, cfg()), StaticVerdict::Valid(cfg()));
    }

    #[test]
    fn a_string_contradiction_is_unsatisfiable() {
        let formula = GuardFormula::and(
            GuardFormula::Scalar { var: 0, pred: str_equals("hi") },
            GuardFormula::Scalar { var: 0, pred: str_equals("bye") },
        );
        assert_eq!(static_verdict(&formula, cfg()), StaticVerdict::Unsatisfiable(cfg()));
    }

    /// A conjunction across two theories is decided by the disjoint-signature combination.
    #[test]
    fn a_mixed_conjunction_combines_soundly() {
        // (x == 1 and x == 2) and b   ⇒ unsat, because the Int conjunct alone is unsat.
        let ints = GuardFormula::and(int_eq(0, 1), int_eq(0, 2));
        let formula = GuardFormula::and(ints, GuardFormula::Prop(prop_var("b")));
        assert_eq!(
            static_verdict(&formula, cfg()),
            StaticVerdict::Unsatisfiable(cfg())
        );
    }

    /// A DISJUNCTION across two theories is outside the covered fragment, and the module says so
    /// rather than guessing.
    #[test]
    fn a_mixed_disjunction_is_undecided_not_guessed() {
        let formula = GuardFormula::or(int_eq(0, 1), GuardFormula::Prop(prop_var("b")));
        assert_eq!(
            static_verdict(&formula, cfg()),
            StaticVerdict::Undecided(UndecidedCause::FragmentNotCovered)
        );
    }

    #[test]
    fn an_opaque_atom_is_undecided_with_its_own_cause() {
        let formula = GuardFormula::Atom(GuardAtom { id: 0, kind: GuardAtomKind::Spatial });
        assert_eq!(
            static_verdict(&formula, cfg()),
            StaticVerdict::Undecided(UndecidedCause::OpaqueAtom)
        );
        assert!(!formula.reaches_substrate());
    }

    #[test]
    fn a_static_verdict_names_the_domain_it_was_decided_over() {
        let narrow = SubstrateConfig { bit_width: 8 };
        assert_eq!(
            static_verdict(&GuardFormula::True, narrow).domain(),
            Some(narrow),
            "a verdict must carry its domain — the bounded-domain caveat is not optional"
        );
        assert_eq!(
            StaticVerdict::Undecided(UndecidedCause::Budget).domain(),
            None
        );
    }

    // ── The ground leg ───────────────────────────────────────────────────────

    fn one_var_map(name: &str) -> GuardVarMap {
        let mut vars = GuardVarMap::with_capacity(1);
        vars.intern(name);
        vars
    }

    #[test]
    fn a_linear_guard_evaluates_on_a_concrete_payload() {
        let vars = one_var_map("x");
        let mut assignment = GuardAssignment::with_len(1);
        assignment.bind(0, GuardValue::Int(42));
        assert_eq!(ground_verdict(&int_eq(0, 42), &assignment, &vars, cfg()), Sat3::Sat);
        assert_eq!(ground_verdict(&int_eq(0, 41), &assignment, &vars, cfg()), Sat3::Unsat);
        assert_eq!(ground_verdict(&int_lt(0, 46), &assignment, &vars, cfg()), Sat3::Sat);
    }

    /// ★ An UNBOUND integer variable must be `DontKnow`, never silently `0`.
    /// `IntAssignment::get` defaults out-of-range indices to `0`, which would turn
    /// `x == 0` into a confident `Sat` for an unbound `x`.
    #[test]
    fn an_unbound_variable_is_dont_know_not_zero() {
        let vars = one_var_map("x");
        let empty = GuardAssignment::with_len(1);
        assert_eq!(ground_verdict(&int_eq(0, 0), &empty, &vars, cfg()), Sat3::DontKnow);
    }

    #[test]
    fn a_string_guard_evaluates_on_a_concrete_payload() {
        let vars = one_var_map("s");
        let mut assignment = GuardAssignment::with_len(1);
        assignment.bind(0, GuardValue::Str("hi".to_string()));
        let formula = GuardFormula::Scalar { var: 0, pred: str_equals("hi") };
        assert_eq!(ground_verdict(&formula, &assignment, &vars, cfg()), Sat3::Sat);
        let other = GuardFormula::Scalar { var: 0, pred: str_equals("bye") };
        assert_eq!(ground_verdict(&other, &assignment, &vars, cfg()), Sat3::Unsat);
    }

    #[test]
    fn a_propositional_guard_evaluates_on_a_concrete_payload() {
        let vars = one_var_map("b");
        let mut assignment = GuardAssignment::with_len(1);
        assignment.bind(0, GuardValue::Bool(true));
        let formula = GuardFormula::Prop(prop_var("b"));
        assert_eq!(ground_verdict(&formula, &assignment, &vars, cfg()), Sat3::Sat);
        assert_eq!(
            ground_verdict(&GuardFormula::not(formula), &assignment, &vars, cfg()),
            Sat3::Unsat
        );
    }

    #[test]
    fn a_scalar_relation_between_two_variables_is_exact_at_run_time() {
        let mut vars = GuardVarMap::with_capacity(2);
        vars.intern("a");
        vars.intern("b");
        let mut assignment = GuardAssignment::with_len(2);
        assignment.bind(0, GuardValue::Str("hi".to_string()));
        assignment.bind(1, GuardValue::Str("hi".to_string()));
        let formula = GuardFormula::ScalarRel { op: CmpOp::Eq, left: 0, right: 1 };
        assert_eq!(ground_verdict(&formula, &assignment, &vars, cfg()), Sat3::Sat);
        // ...but statically undecided: `AnyPred` is unary.
        assert!(matches!(
            static_verdict(&formula, cfg()),
            StaticVerdict::Undecided(_)
        ));
    }

    /// The connective discipline is the LEFT-STRICT one, not full Kleene. `DontKnow or Sat` must
    /// be `DontKnow`; a Kleene `Sat` here would fire a COMM the reducer does not fire.
    #[test]
    fn the_connectives_are_left_strict_not_kleene() {
        let vars = GuardVarMap::new();
        let assignment = GuardAssignment::default();
        let unknown = GuardFormula::Atom(GuardAtom { id: 0, kind: GuardAtomKind::Uncovered });

        assert_eq!(
            ground_verdict(
                &GuardFormula::Or(Box::new(unknown.clone()), Box::new(GuardFormula::True)),
                &assignment,
                &vars,
                cfg()
            ),
            Sat3::DontKnow,
            "full Kleene would answer Sat here; that is unsound in the firing direction"
        );
        assert_eq!(
            ground_verdict(
                &GuardFormula::And(Box::new(unknown.clone()), Box::new(GuardFormula::False)),
                &assignment,
                &vars,
                cfg()
            ),
            Sat3::DontKnow,
        );
        // A decided-FALSE LEFT does short-circuit.
        assert_eq!(
            ground_verdict(
                &GuardFormula::And(Box::new(GuardFormula::False), Box::new(unknown.clone())),
                &assignment,
                &vars,
                cfg()
            ),
            Sat3::Unsat,
        );
        // A decided-TRUE LEFT short-circuits an `or`.
        assert_eq!(
            ground_verdict(
                &GuardFormula::Or(Box::new(GuardFormula::True), Box::new(unknown.clone())),
                &assignment,
                &vars,
                cfg()
            ),
            Sat3::Sat,
        );
        // A decided-FALSE antecedent makes an implication vacuously true.
        assert_eq!(
            ground_verdict(
                &GuardFormula::Implies(Box::new(GuardFormula::False), Box::new(unknown)),
                &assignment,
                &vars,
                cfg()
            ),
            Sat3::Sat,
        );
    }

    /// The only way a spatial atom is ever decided is through the caller's resolver — there is
    /// no arm in this module that could become a second matcher.
    #[test]
    fn a_spatial_atom_is_decidable_only_through_the_resolver() {
        let vars = GuardVarMap::new();
        let assignment = GuardAssignment::default();
        let spatial = GuardFormula::Atom(GuardAtom { id: 7, kind: GuardAtomKind::Spatial });

        assert_eq!(ground_verdict(&spatial, &assignment, &vars, cfg()), Sat3::DontKnow);

        let mut seen = Vec::new();
        let verdict = ground_verdict_with(&spatial, &assignment, &vars, cfg(), &mut |atom| {
            seen.push(atom);
            Sat3::Sat
        });
        assert_eq!(verdict, Sat3::Sat);
        assert_eq!(seen, vec![GuardAtom { id: 7, kind: GuardAtomKind::Spatial }]);
    }

    // ── The policy point ─────────────────────────────────────────────────────

    #[test]
    fn the_dont_know_policy_is_fail_closed_at_every_site() {
        for site in [GuardSiteKind::ReceiveWhere, GuardSiteKind::CompileTimeDischarge] {
            assert_eq!(dont_know_policy(site), DontKnowPolicy::FailClosedBlock);
            assert!(!resolve_verdict(Sat3::DontKnow, site));
            assert!(resolve_verdict(Sat3::Sat, site));
            assert!(!resolve_verdict(Sat3::Unsat, site));
        }
    }

    // ── LinearForm ───────────────────────────────────────────────────────────

    #[test]
    fn linear_forms_merge_coefficients_and_refuse_to_wrap() {
        let x = LinearForm::var(0);
        let two_x = x.add(&x).expect("no overflow");
        assert_eq!(two_x.terms, vec![(0, 2)]);
        // x - x cancels to the constant 0.
        assert!(x.sub(&x).expect("no overflow").is_constant());
        // Overflow is reported, never wrapped: a wrapped coefficient encodes a DIFFERENT
        // constraint, which would be a silently wrong guard.
        let huge = LinearForm { terms: vec![(0, i64::MAX)], constant: 0 };
        assert_eq!(huge.add(&huge), None);
        assert_eq!(LinearForm::constant(i64::MIN).negate(), None);
    }

    #[test]
    fn compare_normalizes_both_sides_to_the_leq_form() {
        // x + 3 > 5   ⇔   x > 2
        let lhs = LinearForm::var(0).add(&LinearForm::constant(3)).expect("no overflow");
        let rhs = LinearForm::constant(5);
        let pred = lhs.compare(CmpOp::Gt, &rhs).expect("no overflow");
        let formula = GuardFormula::Linear(pred);

        let vars = one_var_map("x");
        let mut assignment = GuardAssignment::with_len(1);
        assignment.bind(0, GuardValue::Int(3));
        assert_eq!(ground_verdict(&formula, &assignment, &vars, cfg()), Sat3::Sat);
        assignment.bind(0, GuardValue::Int(2));
        assert_eq!(ground_verdict(&formula, &assignment, &vars, cfg()), Sat3::Unsat);
    }

    #[test]
    fn cmp_op_flip_is_involutive_and_correct() {
        for op in [CmpOp::Eq, CmpOp::Ne, CmpOp::Lt, CmpOp::Le, CmpOp::Gt, CmpOp::Ge] {
            assert_eq!(op.flipped().flipped(), op);
            let a = GuardValue::Int(1);
            let b = GuardValue::Int(2);
            assert_eq!(op.decide(&a, &b), op.flipped().decide(&b, &a));
        }
        // A cross-sort comparison is not a question this operator answers.
        assert_eq!(
            CmpOp::Eq.decide(&GuardValue::Int(1), &GuardValue::Str("1".into())),
            None
        );
    }
}
