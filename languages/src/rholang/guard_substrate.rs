//! **The `Proc` → substrate encoder** — the surface half of the `where`-guard wire.
//!
//! # The rule
//!
//! > *If it is in a `where` clause, it is a semantic predicate. All semantic predicates are
//! > evaluated by Dovetail/SFT — at compile time where they can be statically evaluated, at run
//! > time otherwise. If it is in an `if` condition, it is evaluated by Rholang.*
//!
//! A Rholang `where` clause holds an ordinary `Proc`. This module maps that `Proc` into
//! [`GuardFormula`], the substrate vocabulary defined in
//! [`mettail_prattail::guard_formula`] — after which the guard is decided by
//! Presburger automata, by the propositional (KAT) algebra, or by a scalar sort's effective
//! Boolean algebra, and no longer by a bespoke `match` over `Proc`.
//!
//! # The encoding, one row per surface form
//!
//! | `where` form | substrate image | decided by |
//! |---|---|---|
//! | `true` / `false` | [`GuardFormula::True`] / [`False`](GuardFormula::False) | trivially |
//! | `a and b`, `a or b`, `not a`, `a implies b` | the matching connective | the substrate, structurally |
//! | `x ⋈ 42`, `x + y < 10`, `2 * x - 3 >= z` (`⋈` any of `== != < > <= >=`) | [`GuardFormula::Linear`] — a [`PresburgerPred`] over [`LinearConstraint`] | Büchi/Bartzis–Bultan automata |
//! | `s == "hi"`, `s != "hi"` | [`GuardFormula::Scalar`] with a [`StrPred`] leaf | the string algebra |
//! | `b`, `b == true`, `b != false` | [`GuardFormula::Prop`] | `KatBooleanAlgebra` |
//! | `s < "hi"`, big/rational/float comparisons, var-vs-var | [`GuardFormula::ScalarRel`] | exactly, at run time |
//! | `t matches φ` | [`GuardAtomKind::Spatial`] | the STRUCTURAL core (see below) |
//! | list/bag/map equality | [`GuardAtomKind::StructuralEquality`] | the structural core |
//! | `x * y`, `x / y`, `x % y` with a variable operand | [`GuardAtomKind::NonLinear`] | nothing — fails closed |
//! | a send, a `new`, a nested `for` | [`GuardAtomKind::ProcessShaped`] | nothing — fails closed |
//!
//! # ★ The structural leg is DELEGATED, never re-implemented
//!
//! `t matches {φ | ψ}` — the separating conjunction — has associative-commutative-with-remainder
//! semantics that belong to the reducer's own matcher. `crate::rholang::formula` warns in as many
//! words against growing "the second, divergent matcher this design exists to avoid", so this
//! module does not decide it: it emits an opaque atom, and
//! [`GuardAtomResolver`] hands the *original fragment* to the deciders that already exist
//! (`formula::host_matches_verdict` for `matches`, `runtime::compare_collection_equality` for
//! structured equality). Statically discharging a separating conjunction would need AC tree
//! automata — a theory extension, not wiring — so it is routed to run time, which the rule
//! permits.
//!
//! # ⚠ The integer-sort assumption, stated
//!
//! A bare binder has no sort annotation at a guard site, so an operand that appears inside
//! `+`/`-`/`*` is *assumed* integer-sorted. The assumption is contained on both legs:
//!
//! * **run time** — [`GuardAssignment`] is sort-checked, so a binder that turns out to hold a
//!   string yields `Sat3::DontKnow`, and the policy point blocks. No wrong answer.
//! * **compile time** — a static verdict on an unanchored arithmetic formula (`x + y == y + x`
//!   is Presburger-valid, but string concatenation is not commutative) is *fenced*: the
//!   consumer, `mettail_rholang_runtime::guard_discharge::classify`, requires an evaluator with
//!   the concrete semantics to agree before it changes any artifact.
//!
//! [`PresburgerPred`]: mettail_prattail::presburger::PresburgerPred
//! [`LinearConstraint`]: mettail_prattail::presburger::LinearConstraint
//! [`StrPred`]: mettail_prattail::string_algebra::StrPred

use std::sync::Arc;

use mettail_prattail::algebra_tower::Sat3;
use mettail_prattail::guard_formula::{
    ground_verdict_with, linear_atom, prop_var, static_verdict, str_equals, CmpOp, GuardAssignment,
    GuardAtom, GuardAtomKind, GuardFormula, GuardSiteKind, GuardValue, GuardVarMap, LinearForm,
    ScalarOperand, StaticVerdict, CONSENSUS_SUBSTRATE_CONFIG,
};
use mettail_prattail::presburger::LinearConstraint;
use mettail_runtime::{OrdVar, Var};
use num_bigint::BigInt as NumBigInt;
use num_rational::BigRational;
use num_traits::One;

use super::{Bag, BigInt, BigRat, Bool, Fixed, Float, Int, List, Map, Proc, Str, UInt32};
use crate::rholang::receive::GuardDisposition;

// ══════════════════════════════════════════════════════════════════════════════
// The encoding result
// ══════════════════════════════════════════════════════════════════════════════

/// One guard, encoded for the substrate.
///
/// The three fields travel together because they are only meaningful together: the formula's
/// variable indices are indices *into* `vars`, and its atom ids are indices *into* `opaque`.
#[derive(Clone, Debug)]
pub struct GuardEncoding {
    /// The substrate image of the guard.
    pub formula: GuardFormula,
    /// The binder ⇄ substrate-index map the formula's indices refer to.
    pub vars: GuardVarMap,
    /// The original guard fragment behind each opaque atom, indexed by [`GuardAtom::id`].
    ///
    /// Keeping the fragment here (rather than inside `prattail`) is what makes it *impossible*
    /// for the substrate crate to grow a matcher of its own — it never sees a `Proc`.
    pub opaque: Vec<Arc<Proc>>,
}

impl GuardEncoding {
    /// `true` iff every leaf of this guard is decidable by the substrate's own procedures.
    pub fn reaches_substrate(&self) -> bool {
        self.formula.reaches_substrate()
    }

    /// The fragment behind an opaque atom.
    pub fn fragment(&self, atom: GuardAtom) -> Option<&Proc> {
        self.opaque.get(atom.id as usize).map(Arc::as_ref)
    }

    /// The static verdict for this guard, over the CONSENSUS substrate domain.
    ///
    /// The budget is `CONSENSUS_SUBSTRATE_CONFIG`, not a caller-chosen one: a guard verdict
    /// decides whether a COMM fires, and two nodes with different budgets can reach different
    /// verdicts. See that constant's documentation.
    pub fn static_verdict(&self) -> StaticVerdict {
        static_verdict(&self.formula, CONSENSUS_SUBSTRATE_CONFIG)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// The encoder
// ══════════════════════════════════════════════════════════════════════════════

/// Encode a `where` guard into the substrate.
///
/// Total: every `Proc` gets an encoding. A shape outside the covered fragment becomes an opaque
/// atom rather than a wrong answer — the encoder never guesses.
pub fn encode_guard(cond: &Proc) -> GuardEncoding {
    let mut encoder = Encoder {
        vars: GuardVarMap::new(),
        opaque: Vec::new(),
    };
    let formula = encoder.formula(cond);
    GuardEncoding {
        formula,
        vars: encoder.vars,
        opaque: encoder.opaque,
    }
}

/// Encode a `where` guard whose binders are already known, so the substrate indices agree with
/// a caller-chosen order (the receive's bind order).
pub fn encode_guard_with_binders(cond: &Proc, binders: &[String]) -> GuardEncoding {
    let mut vars = GuardVarMap::with_capacity(binders.len());
    for binder in binders {
        vars.intern(binder);
    }
    let mut encoder = Encoder { vars, opaque: Vec::new() };
    let formula = encoder.formula(cond);
    GuardEncoding {
        formula,
        vars: encoder.vars,
        opaque: encoder.opaque,
    }
}

struct Encoder {
    vars: GuardVarMap,
    opaque: Vec<Arc<Proc>>,
}

/// One side of a comparison, classified.
#[derive(Clone, Debug)]
enum Operand {
    /// An integer-sorted linear form `Σ aᵢ·xᵢ + c`.
    Int(LinearForm),
    /// A literal of a non-integer scalar sort.
    Lit(GuardValue),
    /// A binder whose sort is not determined by this operand alone.
    Var(usize),
    /// Integer-shaped but outside the linear fragment (`x * y`, `x / y`, `x % y`).
    NonLinear,
    /// A structured operand (list, bag, map, process): a structural question, not a scalar one.
    Structural,
    /// A shape the encoder does not cover.
    Uncovered,
}

impl Encoder {
    // ── Formula position ────────────────────────────────────────────────────

    fn formula(&mut self, cond: &Proc) -> GuardFormula {
        match cond {
            // ── The logical constants ────────────────────────────────────────
            Proc::CastBool(literal) => match literal.as_ref() {
                Bool::BoolLit(true) => GuardFormula::True,
                Bool::BoolLit(false) => GuardFormula::False,
                #[allow(unreachable_patterns)]
                _ => self.opaque_atom(cond, GuardAtomKind::Uncovered),
            },

            // ── The connectives ──────────────────────────────────────────────
            Proc::And(a, b) => GuardFormula::and(self.formula(a), self.formula(b)),
            Proc::Or(a, b) => GuardFormula::or(self.formula(a), self.formula(b)),
            Proc::Not(a) => GuardFormula::not(self.formula(a)),
            Proc::Implies(a, b) => GuardFormula::implies(self.formula(a), self.formula(b)),

            // ── The comparisons ──────────────────────────────────────────────
            Proc::Eq(a, b) => self.comparison(CmpOp::Eq, a, b, cond),
            Proc::Ne(a, b) => self.comparison(CmpOp::Ne, a, b, cond),
            Proc::Lt(a, b) => self.comparison(CmpOp::Lt, a, b, cond),
            Proc::LtEq(a, b) => self.comparison(CmpOp::Le, a, b, cond),
            Proc::Gt(a, b) => self.comparison(CmpOp::Gt, a, b, cond),
            Proc::GtEq(a, b) => self.comparison(CmpOp::Ge, a, b, cond),

            // ── The spatial atom — DELEGATED, never decided here ─────────────
            Proc::Matches(_, _) => self.opaque_atom(cond, GuardAtomKind::Spatial),

            // ── A bare binder used as a boolean ──────────────────────────────
            //
            // A guard that IS a variable reads it as a proposition. If the payload turns out to
            // be some other sort, the sort-checked ground leg answers `DontKnow` and the policy
            // point blocks — so the reading is safe even when it is wrong.
            //
            // ★ The propositional letter is the binder's NAME, never its index. `Prop`'s own
            // documentation fixes that keyspace: the ground leg resolves each atom through
            // `GuardVarMap::index_of`, a map keyed by the name `intern` was called with. The
            // `intern` call is still made — it is what REGISTERS the name so the lookup can
            // succeed, and what keeps two binders sharing a pretty name distinct — but its
            // return value is an index and an index is not a key here.
            Proc::PVar(var) => match var_key(var) {
                Some(key) => {
                    self.vars.intern(&key);
                    GuardFormula::Prop(prop_var(&key))
                },
                None => self.opaque_atom(cond, GuardAtomKind::Uncovered),
            },

            // ── Everything else ──────────────────────────────────────────────
            other => self.opaque_atom(cond, classify_uncovered(other)),
        }
    }

    // ── Comparison position ─────────────────────────────────────────────────

    fn comparison(&mut self, op: CmpOp, left: &Proc, right: &Proc, whole: &Proc) -> GuardFormula {
        let lhs = self.operand(left);
        let rhs = self.operand(right);
        match (lhs, rhs) {
            // ── Presburger: at least one side pins the integer sort. ─────────
            (Operand::Int(a), Operand::Int(b)) => self.linear(op, &a, &b, whole),
            (Operand::Int(a), Operand::Var(idx)) => {
                self.linear(op, &a, &LinearForm::var(idx), whole)
            },
            (Operand::Var(idx), Operand::Int(b)) => {
                self.linear(op, &LinearForm::var(idx), &b, whole)
            },

            // ── The propositional sort. ──────────────────────────────────────
            (Operand::Var(idx), Operand::Lit(GuardValue::Bool(b))) => self.prop_compare(op, idx, b),
            (Operand::Lit(GuardValue::Bool(b)), Operand::Var(idx)) => {
                self.prop_compare(op.flipped(), idx, b)
            },
            (Operand::Lit(GuardValue::Bool(a)), Operand::Lit(GuardValue::Bool(b))) => {
                constant_formula(op.decide(&GuardValue::Bool(a), &GuardValue::Bool(b)))
            },

            // ── The string sort: EQUALITY is symbolic, ORDER is not. ─────────
            //
            // `StrPred` is a language, so `s == "hi"` is the singleton language `{"hi"}` and a
            // conjunction of two such is decidably empty. Lexicographic order has no such
            // encoding, so it takes the run-time-exact route.
            (Operand::Var(idx), Operand::Lit(GuardValue::Str(s)))
                if matches!(op, CmpOp::Eq | CmpOp::Ne) =>
            {
                self.str_compare(op, idx, &s)
            },
            (Operand::Lit(GuardValue::Str(s)), Operand::Var(idx))
                if matches!(op, CmpOp::Eq | CmpOp::Ne) =>
            {
                self.str_compare(op, idx, &s)
            },

            // ── Run-time-exact scalar comparisons. ───────────────────────────
            (Operand::Lit(a), Operand::Lit(b)) => constant_formula(op.decide(&a, &b)),
            (Operand::Var(a), Operand::Var(b)) => GuardFormula::ScalarRel {
                op,
                left: ScalarOperand::Var(a),
                right: ScalarOperand::Var(b),
            },
            (Operand::Var(a), Operand::Lit(b)) => GuardFormula::ScalarRel {
                op,
                left: ScalarOperand::Var(a),
                right: ScalarOperand::Lit(b),
            },
            (Operand::Lit(a), Operand::Var(b)) => GuardFormula::ScalarRel {
                op,
                left: ScalarOperand::Lit(a),
                right: ScalarOperand::Var(b),
            },

            // ── Structural and uncovered. ────────────────────────────────────
            (Operand::Structural, _) | (_, Operand::Structural) => {
                self.opaque_atom(whole, GuardAtomKind::StructuralEquality)
            },
            (Operand::NonLinear, _) | (_, Operand::NonLinear) => {
                self.opaque_atom(whole, GuardAtomKind::NonLinear)
            },
            _ => self.opaque_atom(whole, GuardAtomKind::Uncovered),
        }
    }

    /// The brief's shape, verbatim: a comparison of two linear forms becomes
    /// `PresburgerPred::Atom(LinearConstraint)` (or the ≤/≥ pair the `==`/`!=` normal forms
    /// expand to).
    fn linear(
        &mut self,
        op: CmpOp,
        left: &LinearForm,
        right: &LinearForm,
        whole: &Proc,
    ) -> GuardFormula {
        match left.compare(op, right) {
            Some(pred) => GuardFormula::Linear(pred),
            // The only failure mode is an `i64` overflow while normalizing the coefficients.
            // Wrapping would encode a DIFFERENT constraint, so the encoder refuses instead.
            None => self.opaque_atom(whole, GuardAtomKind::NonLinear),
        }
    }

    fn prop_compare(&mut self, op: CmpOp, idx: usize, literal: bool) -> GuardFormula {
        // ★ The letter is the binder's NAME (see the `Proc::PVar` arm): the ground leg resolves
        // it through `GuardVarMap::index_of`, which is keyed by name, so an index written here
        // would be undecidable for every payload. `idx` was produced by `intern`, so the name is
        // always present; the `None` arm can only be reached by a corrupted map, and it answers
        // with the run-time-exact form rather than guessing.
        //
        // The name is copied out before the match so that the borrow of `self.vars` ends here
        // rather than spanning the arms.
        let name = self.vars.name(idx).map(str::to_string);
        match (name, op, literal) {
            (Some(name), CmpOp::Eq, true) | (Some(name), CmpOp::Ne, false) => {
                GuardFormula::Prop(prop_var(&name))
            },
            (Some(name), CmpOp::Eq, false) | (Some(name), CmpOp::Ne, true) => {
                GuardFormula::not(GuardFormula::Prop(prop_var(&name)))
            },
            // `<`/`>` on booleans is `false < true`; it has no propositional encoding, so it
            // takes the run-time-exact route.
            _ => GuardFormula::ScalarRel {
                op,
                left: ScalarOperand::Var(idx),
                right: ScalarOperand::Lit(GuardValue::Bool(literal)),
            },
        }
    }

    fn str_compare(&mut self, op: CmpOp, idx: usize, literal: &str) -> GuardFormula {
        let atom = GuardFormula::Scalar { var: idx, pred: str_equals(literal) };
        match op {
            CmpOp::Eq => atom,
            _ => GuardFormula::not(atom),
        }
    }

    // ── Operand position ────────────────────────────────────────────────────

    fn operand(&mut self, term: &Proc) -> Operand {
        match term {
            // ── Integral literals fold into the linear form's constant. ──────
            Proc::CastInt(v) => match v.as_ref() {
                Int::NumLit(n) => Operand::Int(LinearForm::constant(*n)),
                #[allow(unreachable_patterns)]
                _ => Operand::Uncovered,
            },
            Proc::CastUInt32(v) => match v.as_ref() {
                UInt32::NumLit(n) => Operand::Int(LinearForm::constant(i64::from(*n))),
                #[allow(unreachable_patterns)]
                _ => Operand::Uncovered,
            },
            Proc::CastBigInt(v) => match v.as_ref() {
                BigInt::NumLit(n) => Operand::Lit(GuardValue::BigInt(n.get().clone())),
                #[allow(unreachable_patterns)]
                _ => Operand::Uncovered,
            },

            // ── Non-integral scalar literals. ────────────────────────────────
            Proc::CastBool(v) => match v.as_ref() {
                Bool::BoolLit(b) => Operand::Lit(GuardValue::Bool(*b)),
                #[allow(unreachable_patterns)]
                _ => Operand::Uncovered,
            },
            Proc::CastStr(v) => match v.as_ref() {
                Str::StringLit(s) => Operand::Lit(GuardValue::Str(s.clone())),
                #[allow(unreachable_patterns)]
                _ => Operand::Uncovered,
            },
            Proc::CastBigRat(v) => match v.as_ref() {
                BigRat::RatLit(r) => Operand::Lit(GuardValue::BigRat(r.get().clone())),
                #[allow(unreachable_patterns)]
                _ => Operand::Uncovered,
            },
            Proc::CastFixed(v) => match v.as_ref() {
                Fixed::FixedLit(f) => Operand::Lit(GuardValue::Fixed(fixed_to_rational(f))),
                #[allow(unreachable_patterns)]
                _ => Operand::Uncovered,
            },
            Proc::CastFloat(v) => match v.as_ref() {
                Float::FloatLit(f) => Operand::Lit(GuardValue::Float(
                    mettail_prattail::ordered_field::OrderedF64(f.get()),
                )),
                #[allow(unreachable_patterns)]
                _ => Operand::Uncovered,
            },

            // ── A binder. ────────────────────────────────────────────────────
            Proc::PVar(var) => match var_key(var) {
                Some(key) => Operand::Var(self.vars.intern(&key)),
                None => Operand::Uncovered,
            },

            // ── Linear arithmetic. ───────────────────────────────────────────
            Proc::Add(a, b) => self.arithmetic(a, b, LinearForm::add),
            Proc::Sub(a, b) => self.arithmetic(a, b, LinearForm::sub),

            // ── `*` is linear only when one side is a CONSTANT. ──────────────
            //
            // Presburger arithmetic is linear by definition, so `x * y` with two variables is
            // outside the theory rather than merely hard. It is not routed to an SMT solver:
            // a solver's answer can depend on its search budget, and a budget-dependent verdict
            // that decided whether a COMM fires would be consensus-affecting — the same hazard
            // `dont_know_policy` exists for.
            Proc::Mul(a, b) => {
                let (lhs, rhs) = (self.int_form(a), self.int_form(b));
                match (lhs, rhs) {
                    (Some(x), Some(y)) if x.is_constant() => scaled(&y, x.constant),
                    (Some(x), Some(y)) if y.is_constant() => scaled(&x, y.constant),
                    (Some(_), Some(_)) => Operand::NonLinear,
                    _ => Operand::Uncovered,
                }
            },

            // ── `/` and `%` are outside Presburger; CONSTANT operands still fold. ──
            Proc::Div(a, b) => self.integer_division(a, b, |x, y| x.checked_div(y)),
            Proc::Mod(a, b) => self.integer_division(a, b, |x, y| x.checked_rem(y)),

            // ── Structured payloads are a STRUCTURAL question. ───────────────
            Proc::CastList(_) | Proc::CastBag(_) | Proc::CastMap(_) | Proc::CastSet(_) => {
                Operand::Structural
            },

            _ => Operand::Uncovered,
        }
    }

    fn arithmetic(
        &mut self,
        left: &Proc,
        right: &Proc,
        combine: fn(&LinearForm, &LinearForm) -> Option<LinearForm>,
    ) -> Operand {
        match (self.int_form(left), self.int_form(right)) {
            (Some(a), Some(b)) => match combine(&a, &b) {
                Some(form) => Operand::Int(form),
                // Coefficient overflow: refuse rather than wrap (a wrapped coefficient is a
                // different constraint).
                None => Operand::NonLinear,
            },
            _ => Operand::Uncovered,
        }
    }

    fn integer_division(
        &mut self,
        left: &Proc,
        right: &Proc,
        combine: fn(i64, i64) -> Option<i64>,
    ) -> Operand {
        match (self.int_form(left), self.int_form(right)) {
            (Some(a), Some(b)) if a.is_constant() && b.is_constant() => {
                // Both operands are ground, so the result is a constant — exact, and strictly
                // more than "outside Presburger" would give. `checked_*` covers division by zero
                // and `i64::MIN / -1`.
                match combine(a.constant, b.constant) {
                    Some(value) => Operand::Int(LinearForm::constant(value)),
                    None => Operand::NonLinear,
                }
            },
            (Some(_), Some(_)) => Operand::NonLinear,
            _ => Operand::Uncovered,
        }
    }

    /// An operand read as an integer-sorted linear form.
    ///
    /// ⚠ This is where the integer-sort assumption is applied: a bare binder inside an
    /// arithmetic node is taken to be integer-sorted. See the module docs for how the
    /// assumption is contained on each leg.
    fn int_form(&mut self, term: &Proc) -> Option<LinearForm> {
        match self.operand(term) {
            Operand::Int(form) => Some(form),
            Operand::Var(idx) => Some(LinearForm::var(idx)),
            _ => None,
        }
    }

    // ── Opaque atoms ────────────────────────────────────────────────────────

    fn opaque_atom(&mut self, fragment: &Proc, kind: GuardAtomKind) -> GuardFormula {
        let id = self.opaque.len() as u32;
        self.opaque.push(Arc::new(fragment.clone()));
        GuardFormula::Atom(GuardAtom { id, kind })
    }
}

fn scaled(form: &LinearForm, factor: i64) -> Operand {
    match form.scale(factor) {
        Some(scaled) => Operand::Int(scaled),
        None => Operand::NonLinear,
    }
}

fn constant_formula(decided: Option<bool>) -> GuardFormula {
    match decided {
        Some(true) => GuardFormula::True,
        Some(false) => GuardFormula::False,
        // A cross-sort comparison of two literals is not a question the operator answers; the
        // front end's own comparator declines it too.
        None => GuardFormula::ScalarRel {
            op: CmpOp::Eq,
            left: ScalarOperand::Lit(GuardValue::Bool(true)),
            right: ScalarOperand::Lit(GuardValue::Str(String::new())),
        },
    }
}

/// Why a non-comparison, non-connective `Proc` is opaque.
fn classify_uncovered(term: &Proc) -> GuardAtomKind {
    match term {
        // A process in guard position is not a predicate at all.
        Proc::PZero
        | Proc::PPar(_)
        | Proc::POutput(_, _)
        | Proc::PForUser(_, _)
        | Proc::PNew(_)
        | Proc::PDrop(_) => GuardAtomKind::ProcessShaped,
        Proc::Mul(_, _) | Proc::Div(_, _) | Proc::Mod(_, _) => GuardAtomKind::NonLinear,
        Proc::CastList(_) | Proc::CastBag(_) | Proc::CastMap(_) | Proc::CastSet(_) => {
            GuardAtomKind::StructuralEquality
        },
        _ => GuardAtomKind::Uncovered,
    }
}

/// A canonical, collision-free key for a binder.
///
/// `moniker`'s `Display` for a free variable is `name$unique_id`, and equality on `FreeVar` is
/// equality of `unique_id` alone — so the rendered form separates two binders that happen to
/// share a pretty name, which a bare `pretty_name` key would silently merge.
fn var_key(var: &OrdVar) -> Option<String> {
    match &var.0 {
        Var::Free(fv) => Some(fv.to_string()),
        Var::Bound(bv) => Some(format!("bound${}", bv)),
    }
}

fn fixed_to_rational(value: &mettail_runtime::CanonicalFixedPoint) -> BigRational {
    let scale = NumBigInt::from(10u32).pow(value.places());
    let _ = BigRational::one();
    BigRational::new(value.unscaled().clone(), scale)
}

// ══════════════════════════════════════════════════════════════════════════════
// The GROUND leg — the COMM-time decision, derived from the substrate
// ══════════════════════════════════════════════════════════════════════════════

/// Decides the atoms the substrate has no procedure for, by handing the original fragment to
/// the decider that already owns that question.
///
/// This is the *only* way a spatial or structural atom is ever decided. Keeping it a separate,
/// named type (rather than a match arm buried in the evaluator) is what makes "the structural
/// leg is delegated" checkable rather than aspirational.
struct GuardAtomResolver<'a> {
    encoding: &'a GuardEncoding,
}

impl GuardAtomResolver<'_> {
    fn resolve(&mut self, atom: GuardAtom) -> Sat3 {
        let Some(fragment) = self.encoding.fragment(atom) else {
            return Sat3::DontKnow;
        };
        match atom.kind {
            // `t matches φ` — the reducer's spatial semantics, via the existing host decider.
            // NOT a second matcher: `host_matches_verdict` is the one that already exists, and
            // it DECLINES the separating conjunction, whose AC-with-remainder search belongs to
            // the reducer alone.
            GuardAtomKind::Spatial => match fragment {
                Proc::Matches(target, formula) => {
                    from_verdict(crate::rholang::formula::host_matches_verdict(target, formula))
                },
                _ => Sat3::DontKnow,
            },
            // Structured equality — the existing exact collection comparator.
            GuardAtomKind::StructuralEquality => match fragment {
                Proc::Eq(a, b) => {
                    from_verdict(crate::rholang::runtime::compare_collection_equality(a, b))
                },
                Proc::Ne(a, b) => from_verdict(
                    crate::rholang::runtime::compare_collection_equality(a, b).map(|v| !v),
                ),
                _ => Sat3::DontKnow,
            },
            // Outside every theory on the guard path. Fails closed.
            GuardAtomKind::NonLinear | GuardAtomKind::ProcessShaped | GuardAtomKind::Uncovered => {
                Sat3::DontKnow
            },
        }
    }
}

fn from_verdict(verdict: Option<bool>) -> Sat3 {
    match verdict {
        Some(true) => Sat3::Sat,
        Some(false) => Sat3::Unsat,
        None => Sat3::DontKnow,
    }
}

/// **The host `where`-guard decision, derived from the substrate.**
///
/// This is the function the eager-COMM sites call. It is not a second evaluator: it encodes the
/// guard into [`GuardFormula`] and asks the substrate, delegating only the structural atoms the
/// substrate deliberately has no procedure for.
///
/// The guard reaching this function has already been substituted with the arrived payload, so
/// its binders are gone and its operands are ground — which is exactly the *run-time* half of
/// the rule ("…at run time otherwise").
///
/// [`Sat3::DontKnow`] maps to [`GuardDisposition::Declines`], which is what
/// [`mettail_prattail::guard_formula::dont_know_policy`] selects (fail-closed): the COMM does
/// not fire, and the receiver and the send both remain.
pub fn eval_guard_disposition_via_substrate(cond: &Proc) -> GuardDisposition {
    let encoding = encode_guard(cond);
    let assignment = ground_assignment(&encoding);
    let mut resolver = GuardAtomResolver { encoding: &encoding };
    let verdict = ground_verdict_with(
        &encoding.formula,
        &assignment,
        &encoding.vars,
        CONSENSUS_SUBSTRATE_CONFIG,
        &mut |atom| resolver.resolve(atom),
    );
    match verdict {
        Sat3::Sat => GuardDisposition::Fires,
        Sat3::Unsat => GuardDisposition::Blocks,
        // The policy point's answer, spelled out at the site so a future change to
        // `dont_know_policy` is visible here rather than silent.
        Sat3::DontKnow => {
            match mettail_prattail::guard_formula::dont_know_policy(GuardSiteKind::ReceiveWhere) {
                mettail_prattail::guard_formula::DontKnowPolicy::FailClosedBlock => {
                    GuardDisposition::Declines
                },
                mettail_prattail::guard_formula::DontKnowPolicy::FailOpenFire => {
                    GuardDisposition::Fires
                },
            }
        },
    }
}

/// The assignment for an already-substituted guard: empty.
///
/// A substituted guard has no binders left, so nothing needs binding — but the assignment is
/// still sized to the var map so that a *residual* binder (one the substitution could not
/// reach) reads as unbound and yields `DontKnow`, never a silent default.
fn ground_assignment(encoding: &GuardEncoding) -> GuardAssignment {
    GuardAssignment::with_len(encoding.vars.len())
}

// ══════════════════════════════════════════════════════════════════════════════
// Re-exports for the measurement harness and downstream encoders
// ══════════════════════════════════════════════════════════════════════════════

/// Build the `PresburgerPred::Atom(LinearConstraint)` shape directly (exposed for tests that
/// pin the brief's required encoding).
pub fn linear_constraint_formula(constraint: LinearConstraint) -> GuardFormula {
    linear_atom(constraint)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_prattail::guard_formula::{ground_verdict, UndecidedCause};
    use mettail_runtime::get_or_create_var;

    fn int(n: i64) -> Proc {
        Proc::CastInt(Arc::new(Int::NumLit(n)))
    }

    fn boolean(b: bool) -> Proc {
        Proc::CastBool(Arc::new(Bool::BoolLit(b)))
    }

    fn string(s: &str) -> Proc {
        Proc::CastStr(Arc::new(Str::StringLit(s.to_string())))
    }

    fn var(name: &str) -> Proc {
        Proc::PVar(OrdVar(Var::Free(get_or_create_var(name))))
    }

    fn arc(p: Proc) -> Arc<Proc> {
        Arc::new(p)
    }

    // ── The encoder reaches the substrate for each covered form ─────────────

    #[test]
    fn an_integer_comparison_becomes_a_presburger_atom() {
        let guard = Proc::Eq(arc(var("x")), arc(int(42)));
        let encoding = encode_guard(&guard);
        assert!(encoding.reaches_substrate());
        assert!(
            matches!(encoding.formula, GuardFormula::Linear(_)),
            "an integer comparison must land on PresburgerPred, got {:?}",
            encoding.formula
        );
        assert_eq!(encoding.vars.len(), 1);
    }

    #[test]
    fn linear_arithmetic_is_linearized_not_declined() {
        // 2 * x + 3 < y  ⇒  one Presburger atom over two variables.
        let two_x = Proc::Mul(arc(int(2)), arc(var("x")));
        let lhs = Proc::Add(arc(two_x), arc(int(3)));
        let guard = Proc::Lt(arc(lhs), arc(var("y")));
        let encoding = encode_guard(&guard);
        assert!(encoding.reaches_substrate());
        assert!(matches!(encoding.formula, GuardFormula::Linear(_)));
        assert_eq!(encoding.formula.int_vars().len(), 2);
    }

    #[test]
    fn every_connective_reaches_the_substrate() {
        let atom = || Proc::Eq(arc(var("x")), arc(int(1)));
        for guard in [
            Proc::And(arc(atom()), arc(atom())),
            Proc::Or(arc(atom()), arc(atom())),
            Proc::Not(arc(atom())),
            Proc::Implies(arc(atom()), arc(atom())),
        ] {
            assert!(
                encode_guard(&guard).reaches_substrate(),
                "connective must reach the substrate: {guard:?}"
            );
        }
    }

    #[test]
    fn every_comparison_reaches_the_substrate() {
        for build in [
            Proc::Eq as fn(Arc<Proc>, Arc<Proc>) -> Proc,
            Proc::Ne,
            Proc::Lt,
            Proc::LtEq,
            Proc::Gt,
            Proc::GtEq,
        ] {
            let guard = build(arc(var("x")), arc(int(7)));
            assert!(
                encode_guard(&guard).reaches_substrate(),
                "comparison must reach the substrate: {guard:?}"
            );
        }
    }

    #[test]
    fn a_string_equality_becomes_a_string_algebra_leaf() {
        let guard = Proc::Eq(arc(var("s")), arc(string("hi")));
        let encoding = encode_guard(&guard);
        assert!(encoding.reaches_substrate());
        assert!(matches!(encoding.formula, GuardFormula::Scalar { .. }));
    }

    #[test]
    fn a_boolean_binder_becomes_a_proposition() {
        let encoding = encode_guard(&var("b"));
        assert!(encoding.reaches_substrate());
        assert!(matches!(encoding.formula, GuardFormula::Prop(_)));

        // ★ THE ASSERTION THAT MAKES THE SHAPE CHECK ABOVE MEAN SOMETHING.
        //
        // `GuardFormula::Prop`'s own documentation fixes the keyspace: a `BooleanTest::Atom`
        // name is a BINDER NAME, never an index, because `GuardAssignment::truth_assignment`
        // resolves each required atom through `GuardVarMap::index_of` — whose keys are the
        // names `intern` was called with. An atom the var map cannot resolve makes the ground
        // leg answer `DontKnow` for a reason that has nothing to do with the payload, and the
        // `matches!` above passes for such an atom just as happily as for a sound one.
        let names = encoding.formula.prop_names();
        assert!(!names.is_empty(), "a propositional guard must carry at least one atom");
        for name in &names {
            assert!(
                encoding.vars.index_of(name).is_some(),
                "the propositional atom {:?} must resolve in this encoding's own var map \
                 (which holds {:?}); an atom outside that keyspace is undecidable at the ground \
                 leg no matter what the payload binds",
                name,
                encoding.vars.names()
            );
        }
    }

    // ── The encoder never guesses ────────────────────────────────────────────

    #[test]
    fn a_process_shaped_guard_fails_closed() {
        let encoding = encode_guard(&Proc::PZero);
        assert!(!encoding.reaches_substrate());
        assert_eq!(encoding.formula.atoms()[0].kind, GuardAtomKind::ProcessShaped);
        assert_eq!(eval_guard_disposition_via_substrate(&Proc::PZero), GuardDisposition::Declines);
    }

    #[test]
    fn nonlinear_arithmetic_over_variables_fails_closed() {
        let guard = Proc::Lt(arc(Proc::Mul(arc(var("x")), arc(var("y")))), arc(int(10)));
        let encoding = encode_guard(&guard);
        assert!(!encoding.reaches_substrate());
        assert_eq!(encoding.formula.atoms()[0].kind, GuardAtomKind::NonLinear);
        assert!(matches!(
            encoding.static_verdict(),
            StaticVerdict::Undecided(UndecidedCause::OpaqueAtom)
        ));
    }

    /// ...but a GROUND division folds exactly, which is strictly more than "outside Presburger".
    #[test]
    fn ground_division_and_modulo_fold_exactly() {
        let guard = Proc::Eq(arc(Proc::Div(arc(int(7)), arc(int(2)))), arc(int(3)));
        assert_eq!(eval_guard_disposition_via_substrate(&guard), GuardDisposition::Fires);
        let modulo = Proc::Eq(arc(Proc::Mod(arc(int(7)), arc(int(2)))), arc(int(1)));
        assert_eq!(eval_guard_disposition_via_substrate(&modulo), GuardDisposition::Fires);
        // Division by zero is refused, not panicked or wrapped.
        let by_zero = Proc::Eq(arc(Proc::Div(arc(int(7)), arc(int(0)))), arc(int(0)));
        assert_eq!(eval_guard_disposition_via_substrate(&by_zero), GuardDisposition::Declines);
    }

    #[test]
    fn a_spatial_guard_is_an_opaque_atom_the_substrate_refuses_to_decide() {
        let guard = Proc::Matches(arc(int(1)), arc(int(1)));
        let encoding = encode_guard(&guard);
        assert!(!encoding.reaches_substrate());
        assert_eq!(encoding.formula.atoms()[0].kind, GuardAtomKind::Spatial);
        // The substrate ALONE cannot decide it...
        assert_eq!(
            ground_verdict(
                &encoding.formula,
                &GuardAssignment::default(),
                &encoding.vars,
                CONSENSUS_SUBSTRATE_CONFIG
            ),
            Sat3::DontKnow
        );
        // ...but the delegated structural leg can.
        assert_eq!(eval_guard_disposition_via_substrate(&guard), GuardDisposition::Fires);
    }

    // ── The ground leg decides substituted guards ───────────────────────────

    #[test]
    fn a_substituted_integer_guard_fires_and_blocks_correctly() {
        assert_eq!(
            eval_guard_disposition_via_substrate(&Proc::Eq(arc(int(42)), arc(int(42)))),
            GuardDisposition::Fires
        );
        assert_eq!(
            eval_guard_disposition_via_substrate(&Proc::Eq(arc(int(42)), arc(int(41)))),
            GuardDisposition::Blocks
        );
        assert_eq!(
            eval_guard_disposition_via_substrate(&Proc::Lt(arc(int(42)), arc(int(46)))),
            GuardDisposition::Fires
        );
    }

    #[test]
    fn a_substituted_boolean_guard_matches_the_front_ends_structural_equality() {
        // Divergence H's second half: `x == true` after substitution is
        // `Eq(CastBool(true), CastBool(true))`, which must FIRE.
        assert_eq!(
            eval_guard_disposition_via_substrate(&Proc::Eq(arc(boolean(true)), arc(boolean(true)))),
            GuardDisposition::Fires
        );
        assert_eq!(
            eval_guard_disposition_via_substrate(&Proc::Eq(
                arc(boolean(true)),
                arc(boolean(false))
            )),
            GuardDisposition::Blocks
        );
    }

    #[test]
    fn the_constants_decide_immediately() {
        assert_eq!(eval_guard_disposition_via_substrate(&boolean(true)), GuardDisposition::Fires);
        assert_eq!(eval_guard_disposition_via_substrate(&boolean(false)), GuardDisposition::Blocks);
    }

    #[test]
    fn an_unsubstituted_binder_declines_rather_than_defaulting() {
        // A binder the substitution could not reach must NOT read as 0/false.
        assert_eq!(
            eval_guard_disposition_via_substrate(&Proc::Eq(arc(var("x")), arc(int(0)))),
            GuardDisposition::Declines
        );
    }

    // ── The static leg ───────────────────────────────────────────────────────

    #[test]
    fn an_open_tautology_is_statically_valid_which_the_previous_leg_could_not_do() {
        // x < x + 1 — mentions a binder, so `rho_pure_eval` declines it outright.
        let guard = Proc::Lt(arc(var("x")), arc(Proc::Add(arc(var("x")), arc(int(1)))));
        assert!(matches!(encode_guard(&guard).static_verdict(), StaticVerdict::Valid(_)));
    }

    #[test]
    fn an_open_contradiction_is_statically_unsatisfiable() {
        let guard = Proc::And(
            arc(Proc::Eq(arc(var("x")), arc(int(1)))),
            arc(Proc::Eq(arc(var("x")), arc(int(2)))),
        );
        assert!(matches!(encode_guard(&guard).static_verdict(), StaticVerdict::Unsatisfiable(_)));
    }

    #[test]
    fn a_payload_dependent_guard_is_contingent_and_therefore_a_run_time_question() {
        let guard = Proc::Eq(arc(var("x")), arc(int(42)));
        assert!(matches!(encode_guard(&guard).static_verdict(), StaticVerdict::Contingent(_)));
    }

    #[test]
    fn binders_with_the_same_pretty_name_are_not_merged() {
        // Two distinct `FreeVar`s can share a pretty name; the key must separate them, or a
        // guard would constrain the wrong binder.
        let a = Proc::PVar(OrdVar(Var::Free(mettail_runtime::FreeVar::fresh_named("x"))));
        let b = Proc::PVar(OrdVar(Var::Free(mettail_runtime::FreeVar::fresh_named("x"))));
        let guard = Proc::Eq(arc(a), arc(b));
        let encoding = encode_guard(&guard);
        assert_eq!(
            encoding.vars.len(),
            2,
            "two distinct binders sharing a pretty name must get two indices"
        );
    }
}
