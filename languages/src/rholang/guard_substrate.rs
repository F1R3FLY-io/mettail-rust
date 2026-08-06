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
    ground_verdict_with, linear_atom, prop_var, static_verdict as substrate_static_verdict,
    str_equals, CmpOp, GuardAssignment, GuardAtom, GuardAtomKind, GuardFormula, GuardSiteKind,
    GuardValue, GuardVarMap, LinearForm, ScalarOperand, StaticVerdict, CONSENSUS_SUBSTRATE_CONFIG,
};
use mettail_prattail::guard_refusal::{
    GuardRefusal, GuardRefusalCause, GuardRefusalClass, RefusalProvenance,
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
    pub opaque: Vec<OpaqueFragment>,
}

/// One guard fragment the encoder set aside, with the two facts a refusal needs about it.
///
/// The `kind` says which decider owns the fragment; the [`position`](Self::position) says
/// whether it stood where a *verdict* was required. Both are recorded at the moment the encoder
/// sets the fragment aside, because both are things the encoder knows and a later walk over the
/// fragment alone would have to guess — `x * y` is an unanswerable **predicate** inside
/// `x * y == 6` and is simply **not a predicate** when it is the whole guard, and the two are
/// the same `Proc`.
#[derive(Clone, Debug)]
pub struct OpaqueFragment {
    /// The guard fragment, verbatim.
    pub term: Arc<Proc>,
    /// Which decider the fragment belongs to.
    pub kind: GuardAtomKind,
    /// Whether the fragment stood in a position that required a verdict.
    pub position: OpaquePosition,
}

/// Where an opaque fragment was set aside — the fact that separates *"the decider had a
/// predicate and no procedure for it"* from *"this was never a predicate at all"*.
///
/// ★ This is the surface lane's answer to the question `guard_par_substrate::never_a_predicate`
/// answers by an exhaustive walk over `ExprInstance`. It is recorded rather than re-derived
/// because [`Encoder::formula`] has **already** made the distinction: its verdict-producing arms
/// (`matches`, the six comparisons, a bare binder read as a proposition) are exactly the
/// predicate positions, and its `other` catch-all is exactly the complement. Re-deriving the
/// split with a second walk over `Proc` would be a second classifier free to drift from the
/// first — and drift across lanes is the mechanism this whole refusal vocabulary exists to
/// remove.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OpaquePosition {
    /// The fragment stands where a verdict was required: a verdict-producing arm set it aside
    /// because it had no procedure for it. Refusing here is a *coverage* fact.
    Predicate,
    /// The fragment is not one of the verdict-producing constructors, so no payload makes it a
    /// verdict. Refusing here is a *sort* fact.
    NotAPredicate,
}

impl GuardEncoding {
    /// `true` iff every leaf of this guard is decidable by the substrate's own procedures.
    pub fn reaches_substrate(&self) -> bool {
        self.formula.reaches_substrate()
    }

    /// The fragment behind an opaque atom.
    pub fn fragment(&self, atom: GuardAtom) -> Option<&Proc> {
        self.opaque
            .get(atom.id as usize)
            .map(|fragment| fragment.term.as_ref())
    }

    /// The static verdict for this guard, over the CONSENSUS substrate domain.
    ///
    /// The budget is `CONSENSUS_SUBSTRATE_CONFIG`, not a caller-chosen one: a guard verdict
    /// decides whether a COMM fires, and two nodes with different budgets can reach different
    /// verdicts. See that constant's documentation.
    pub fn static_verdict(&self) -> StaticVerdict {
        substrate_static_verdict(&self.formula, CONSENSUS_SUBSTRATE_CONFIG)
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
    opaque: Vec<OpaqueFragment>,
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
        #[derive(Clone, Copy)]
        enum Job<'a> {
            Visit(&'a Proc),
            BuildAnd,
            BuildOr,
            BuildNot,
            BuildImplies,
        }

        let mut jobs = vec![Job::Visit(cond)];
        let mut values = Vec::new();
        while let Some(job) = jobs.pop() {
            match job {
                Job::Visit(cond) => match cond {
                    Proc::CastBool(literal) => values.push(match literal.as_ref() {
                        Bool::BoolLit(true) => GuardFormula::True,
                        Bool::BoolLit(false) => GuardFormula::False,
                        #[allow(unreachable_patterns)]
                        _ => self.opaque_atom(
                            cond,
                            GuardAtomKind::Uncovered,
                            OpaquePosition::Predicate,
                        ),
                    }),

                    // Push right before left so identifiers and variables retain their original
                    // left-to-right allocation order when the work stack pops.
                    Proc::And(left, right) => {
                        jobs.push(Job::BuildAnd);
                        jobs.push(Job::Visit(right));
                        jobs.push(Job::Visit(left));
                    },
                    Proc::Or(left, right) => {
                        jobs.push(Job::BuildOr);
                        jobs.push(Job::Visit(right));
                        jobs.push(Job::Visit(left));
                    },
                    Proc::Not(inner) => {
                        jobs.push(Job::BuildNot);
                        jobs.push(Job::Visit(inner));
                    },
                    Proc::Implies(left, right) => {
                        jobs.push(Job::BuildImplies);
                        jobs.push(Job::Visit(right));
                        jobs.push(Job::Visit(left));
                    },

                    Proc::Eq(a, b) => values.push(self.comparison(CmpOp::Eq, a, b, cond)),
                    Proc::Ne(a, b) => values.push(self.comparison(CmpOp::Ne, a, b, cond)),
                    Proc::Lt(a, b) => values.push(self.comparison(CmpOp::Lt, a, b, cond)),
                    Proc::LtEq(a, b) => values.push(self.comparison(CmpOp::Le, a, b, cond)),
                    Proc::Gt(a, b) => values.push(self.comparison(CmpOp::Gt, a, b, cond)),
                    Proc::GtEq(a, b) => values.push(self.comparison(CmpOp::Ge, a, b, cond)),

                    Proc::Matches(_, _) => values.push(self.opaque_atom(
                        cond,
                        GuardAtomKind::Spatial,
                        OpaquePosition::Predicate,
                    )),

                    Proc::PVar(var) => values.push(match var_key(var) {
                        Some(key) => {
                            self.vars.intern(&key);
                            GuardFormula::Prop(prop_var(&key))
                        },
                        None => self.opaque_atom(
                            cond,
                            GuardAtomKind::Uncovered,
                            OpaquePosition::Predicate,
                        ),
                    }),

                    other => values.push(self.opaque_atom(
                        cond,
                        classify_uncovered(other),
                        OpaquePosition::NotAPredicate,
                    )),
                },
                Job::BuildAnd | Job::BuildOr | Job::BuildImplies => {
                    let right = values.pop().expect("surface guard right formula");
                    let left = values.pop().expect("surface guard left formula");
                    values.push(match job {
                        Job::BuildAnd => GuardFormula::and(left, right),
                        Job::BuildOr => GuardFormula::or(left, right),
                        Job::BuildImplies => GuardFormula::implies(left, right),
                        _ => unreachable!(),
                    });
                },
                Job::BuildNot => {
                    let inner = values.pop().expect("surface guard negated formula");
                    values.push(GuardFormula::not(inner));
                },
            }
        }
        assert_eq!(values.len(), 1);
        values.pop().expect("surface guard formula")
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
            (Operand::Structural, _) | (_, Operand::Structural) => self.opaque_atom(
                whole,
                GuardAtomKind::StructuralEquality,
                OpaquePosition::Predicate,
            ),
            (Operand::NonLinear, _) | (_, Operand::NonLinear) => {
                self.opaque_atom(whole, GuardAtomKind::NonLinear, OpaquePosition::Predicate)
            },
            _ => self.opaque_atom(whole, GuardAtomKind::Uncovered, OpaquePosition::Predicate),
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
            None => self.opaque_atom(whole, GuardAtomKind::NonLinear, OpaquePosition::Predicate),
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
        #[derive(Clone, Copy)]
        enum Job<'a> {
            Visit(&'a Proc),
            BuildArithmetic(fn(&LinearForm, &LinearForm) -> Option<LinearForm>),
            BuildMultiply,
            BuildIntegerDivision(fn(i64, i64) -> Option<i64>),
        }

        let mut jobs = vec![Job::Visit(term)];
        let mut values = Vec::new();
        while let Some(job) = jobs.pop() {
            match job {
                Job::Visit(term) => match term {
                    Proc::CastInt(v) => values.push(match v.as_ref() {
                        Int::NumLit(n) => Operand::Int(LinearForm::constant(*n)),
                        #[allow(unreachable_patterns)]
                        _ => Operand::Uncovered,
                    }),
                    Proc::CastUInt32(v) => values.push(match v.as_ref() {
                        UInt32::NumLit(n) => Operand::Int(LinearForm::constant(i64::from(*n))),
                        #[allow(unreachable_patterns)]
                        _ => Operand::Uncovered,
                    }),
                    Proc::CastBigInt(v) => values.push(match v.as_ref() {
                        BigInt::NumLit(n) => Operand::Lit(GuardValue::BigInt(n.get().clone())),
                        #[allow(unreachable_patterns)]
                        _ => Operand::Uncovered,
                    }),
                    Proc::CastBool(v) => values.push(match v.as_ref() {
                        Bool::BoolLit(b) => Operand::Lit(GuardValue::Bool(*b)),
                        #[allow(unreachable_patterns)]
                        _ => Operand::Uncovered,
                    }),
                    Proc::CastStr(v) => values.push(match v.as_ref() {
                        Str::StringLit(s) => Operand::Lit(GuardValue::Str(s.clone())),
                        #[allow(unreachable_patterns)]
                        _ => Operand::Uncovered,
                    }),
                    Proc::CastBigRat(v) => values.push(match v.as_ref() {
                        BigRat::RatLit(r) => Operand::Lit(GuardValue::BigRat(r.get().clone())),
                        #[allow(unreachable_patterns)]
                        _ => Operand::Uncovered,
                    }),
                    Proc::CastFixed(v) => values.push(match v.as_ref() {
                        Fixed::FixedLit(f) => Operand::Lit(GuardValue::Fixed(fixed_to_rational(f))),
                        #[allow(unreachable_patterns)]
                        _ => Operand::Uncovered,
                    }),
                    Proc::CastFloat(v) => values.push(match v.as_ref() {
                        Float::FloatLit(f) => Operand::Lit(GuardValue::Float(
                            mettail_prattail::ordered_field::OrderedF64(f.get()),
                        )),
                        #[allow(unreachable_patterns)]
                        _ => Operand::Uncovered,
                    }),

                    Proc::PVar(var) => values.push(match var_key(var) {
                        Some(key) => Operand::Var(self.vars.intern(&key)),
                        None => Operand::Uncovered,
                    }),

                    Proc::Add(left, right) => {
                        jobs.push(Job::BuildArithmetic(LinearForm::add));
                        jobs.push(Job::Visit(right));
                        jobs.push(Job::Visit(left));
                    },
                    Proc::Sub(left, right) => {
                        jobs.push(Job::BuildArithmetic(LinearForm::sub));
                        jobs.push(Job::Visit(right));
                        jobs.push(Job::Visit(left));
                    },
                    Proc::Mul(left, right) => {
                        jobs.push(Job::BuildMultiply);
                        jobs.push(Job::Visit(right));
                        jobs.push(Job::Visit(left));
                    },
                    Proc::Div(left, right) => {
                        jobs.push(Job::BuildIntegerDivision(i64::checked_div));
                        jobs.push(Job::Visit(right));
                        jobs.push(Job::Visit(left));
                    },
                    Proc::Mod(left, right) => {
                        jobs.push(Job::BuildIntegerDivision(i64::checked_rem));
                        jobs.push(Job::Visit(right));
                        jobs.push(Job::Visit(left));
                    },

                    Proc::CastList(_) | Proc::CastBag(_) | Proc::CastMap(_) | Proc::CastSet(_) => {
                        values.push(Operand::Structural)
                    },
                    _ => values.push(Operand::Uncovered),
                },
                Job::BuildArithmetic(combine) => {
                    let right = int_form_of(values.pop().expect("surface arithmetic right"));
                    let left = int_form_of(values.pop().expect("surface arithmetic left"));
                    values.push(match (left, right) {
                        (Some(left), Some(right)) => match combine(&left, &right) {
                            Some(form) => Operand::Int(form),
                            None => Operand::NonLinear,
                        },
                        _ => Operand::Uncovered,
                    });
                },
                Job::BuildMultiply => {
                    let right = int_form_of(values.pop().expect("surface multiplication right"));
                    let left = int_form_of(values.pop().expect("surface multiplication left"));
                    values.push(match (left, right) {
                        (Some(left), Some(right)) if left.is_constant() => {
                            scaled(&right, left.constant)
                        },
                        (Some(left), Some(right)) if right.is_constant() => {
                            scaled(&left, right.constant)
                        },
                        (Some(_), Some(_)) => Operand::NonLinear,
                        _ => Operand::Uncovered,
                    });
                },
                Job::BuildIntegerDivision(combine) => {
                    let right = int_form_of(values.pop().expect("surface division right"));
                    let left = int_form_of(values.pop().expect("surface division left"));
                    values.push(match (left, right) {
                        (Some(left), Some(right)) if left.is_constant() && right.is_constant() => {
                            match combine(left.constant, right.constant) {
                                Some(value) => Operand::Int(LinearForm::constant(value)),
                                None => Operand::NonLinear,
                            }
                        },
                        (Some(_), Some(_)) => Operand::NonLinear,
                        _ => Operand::Uncovered,
                    });
                },
            }
        }
        assert_eq!(values.len(), 1);
        values.pop().expect("surface guard operand")
    }

    // ── Opaque atoms ────────────────────────────────────────────────────────

    /// Set a fragment aside as an opaque atom, recording BOTH facts a refusal needs: which
    /// decider owns it, and whether it stood where a verdict was required.
    ///
    /// `position` is a parameter rather than something derived from `kind` because the two are
    /// independent: [`GuardAtomKind::NonLinear`] arrives from an operand of a comparison (a
    /// predicate the encoder could not represent) *and* from the `other` catch-all (a bare
    /// `x * y` guard, which is not a predicate at all). A caller that had to guess would
    /// reproduce, one arm at a time, exactly the conflation the refusal vocabulary removes.
    fn opaque_atom(
        &mut self,
        fragment: &Proc,
        kind: GuardAtomKind,
        position: OpaquePosition,
    ) -> GuardFormula {
        let id = self.opaque.len() as u32;
        self.opaque.push(OpaqueFragment {
            term: Arc::new(fragment.clone()),
            kind,
            position,
        });
        GuardFormula::Atom(GuardAtom { id, kind })
    }
}

fn int_form_of(operand: Operand) -> Option<LinearForm> {
    match operand {
        Operand::Int(form) => Some(form),
        Operand::Var(idx) => Some(LinearForm::var(idx)),
        _ => None,
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
/// This is the function the eager-COMM sites call. It is not a second evaluator: it is a
/// **projection of [`surface_guard_disposition`]**, which is where the decision actually
/// happens. `Declines` is `Undecided(_)` with the refusal thrown away, so the two cannot
/// disagree about which COMMs fire.
///
/// The guard reaching this function has already been substituted with the arrived payload, so
/// its binders are gone and its operands are ground — which is exactly the *run-time* half of
/// the rule ("…at run time otherwise").
///
/// ★ When a binder is **not** gone — the payload did not supply it — this answers
/// [`GuardDisposition::Declines`], and it does so even where the substrate's short-circuits make
/// the formula constant-true. That is [`surface_guard_disposition`]'s step 1, and it is there
/// because the reducer errors on the unresolved operand and **rests**. See that function's
/// "STEP 1 IS A VERDICT-CHANGING SOUNDNESS GUARD" section.
///
/// ⚠ Because the caller supplies only the substituted guard, the refusal's
/// [`RefusalProvenance`] is computed against that image; see
/// [`surface_guard_disposition`]'s "the written guard" section for what that costs and for the
/// call that avoids it.
///
/// [`Sat3::DontKnow`] maps to [`GuardDisposition::Declines`], which is what
/// [`mettail_prattail::guard_formula::dont_know_policy`] selects (fail-closed): the COMM does
/// not fire, and the receiver and the send both remain.
pub fn eval_guard_disposition_via_substrate(cond: &Proc) -> GuardDisposition {
    match surface_guard_disposition(cond, cond) {
        SurfaceGuardDisposition::Admits => GuardDisposition::Fires,
        SurfaceGuardDisposition::Refutes => GuardDisposition::Blocks,
        // The policy point's answer, spelled out at the site so a future change to
        // `dont_know_policy` is visible here rather than silent.
        SurfaceGuardDisposition::Undecided(_) => {
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

/// ★ **The surface lane's COMM-time disposition** — three facts where there used to be one bit.
///
/// The exact twin of `guard_par_substrate::SubstrateGuardDisposition`, and the names are the
/// same on purpose so the tree has ONE guard vocabulary:
///
/// | this lane | lowered lane | host fold |
/// |---|---|---|
/// | [`Admits`](Self::Admits) | `SubstrateGuardDisposition::Admits` | `GuardDisposition::Fires` |
/// | [`Refutes`](Self::Refutes) | `SubstrateGuardDisposition::Refutes` | `GuardDisposition::Blocks` |
/// | [`Undecided`](Self::Undecided) | `SubstrateGuardDisposition::Undecided` | `GuardDisposition::Declines` |
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SurfaceGuardDisposition {
    /// The substrate decided the guard holds — the COMM fires.
    Admits,
    /// The substrate decided the guard does not hold — an ordinary, correct non-fire.
    Refutes,
    /// ★ No verdict was reached. The COMM still does not fire; what has changed is that this is
    /// no longer spelled the same way as [`Refutes`](Self::Refutes).
    Undecided(GuardRefusal),
}

impl SurfaceGuardDisposition {
    /// The fire verdict: `true` only for [`Admits`](Self::Admits).
    ///
    /// ⚠ Unchanged from before the refusal vocabulary existed — see [`GuardRefusalClass`] for
    /// why fail-closed is correct and why it is not what was being fixed.
    pub const fn commits(&self) -> bool {
        matches!(self, SurfaceGuardDisposition::Admits)
    }

    /// The three-valued verdict this disposition projects to.
    pub const fn verdict(&self) -> Sat3 {
        match self {
            SurfaceGuardDisposition::Admits => Sat3::Sat,
            SurfaceGuardDisposition::Refutes => Sat3::Unsat,
            SurfaceGuardDisposition::Undecided(_) => Sat3::DontKnow,
        }
    }

    /// The refusal, when there is one.
    pub const fn refusal(&self) -> Option<&GuardRefusal> {
        match self {
            SurfaceGuardDisposition::Undecided(refusal) => Some(refusal),
            _ => None,
        }
    }
}

/// ★ **THE surface `where`-guard decider, with the reason attached.**
///
/// [`Sat3`] has one symbol, [`Sat3::DontKnow`], for every way this lane can fail to reach a
/// verdict, and `dont_know_policy` then spells that symbol `false`. That is correct as a COMM
/// verdict and wrong as an *observation*: it makes a guard that was evaluated and REFUTED
/// indistinguishable from a guard that was never decided at all. This function answers the same
/// verdict and, when there is no verdict, **what stopped it**.
///
/// # ★★ STEP 1 IS A VERDICT-CHANGING SOUNDNESS GUARD, NOT A DIAGNOSIS
///
/// **THE REDUCER IS NORMATIVE.** `f1r3node/rholang/src/rust/interpreter/reduce.rs:1970` binds
/// **both** operands of `EAnd`/`EOr` with `?` before combining them — unconditionally, with no
/// short-circuit — and its pure twin `rho_pure_eval::eval` does the same, answering
/// `Err(operator_mismatch_binary)` for a non-`GBool` operand. An operand that still mentions a
/// binder the payload did not supply is not a `GBool`: it is an error. The error propagates out
/// of the whole connective, `guard_passes` maps it to *no COMM*, and the **process rests** — the
/// receive and the send both remain, and the datum stays available for a later match.
///
/// `Proc::Implies` is not a third case: it lowers to `(not a) or b` (`rholang_ast::lower_proc`,
/// `Kont::Implies`), so on the machine it is an `EOr` and inherits the same discipline.
///
/// This lane's substrate, by contrast, short-circuits **twice over**:
///
/// | mechanism | example | what it discards |
/// |---|---|---|
/// | `GuardFormula::or`'s CONSTRUCTOR collapse `(True, _) ⟼ True` | `true or (y == 2)` | the disjunct, before any ground check runs — the formula is literally `True` |
/// | [`ground_verdict_with`]'s left-strict EVALUATOR short-circuit | `(1 == 1) or (y == 2)`, `false implies (y == 2)` | the operand, after the formula kept it |
///
/// Each of those fired a COMM the reducer rests on. That is unsoundness in the **firing**
/// direction, which no fail-closed policy excuses, so step 1 now runs **before** the ground leg
/// and refuses the whole guard whenever `encoding.vars` is non-empty — exactly as
/// `substrate_guard_disposition` has always done over the lowered `Par`. The two lanes are once
/// again the same shape as well as the same decider.
///
/// ★ **The check consults `encoding.vars`, NOT the formula, and it must.** `true or (y == 2)`
/// encodes to the formula `True` with no atoms at all, while `encoding.vars` still names `y$…`:
/// the residual binder is gone from the formula before any ground procedure runs. A fix that
/// inspected `formula.atoms()` would find nothing to refuse. This is the same reasoning
/// `substrate_guard_disposition` gives for sweeping `encoding.opaque` rather than
/// `formula.atoms()` in its own step 2.
///
/// ## ⚠ What this cost, and what it deliberately did NOT change
///
/// The change is **conservative in one direction only**: strictly fewer COMMs fire, never more.
/// `languages/tests/guard_residual_binder_is_normative.rs` holds the measurement — of 15
/// residual-binder shapes, 3 used to fire (`true or (y == 2)`, `(1 == 1) or (y == 2)`,
/// `false implies (y == 2)`), 1 used to claim a decided `false` (`false and (y == 2)`), and 11
/// were already declining by the left-strict discipline.
///
/// It also **broke the differential** in `languages/tests/rholang_guard_substrate_wire.rs`:
/// `receive::eval_guard_disposition` short-circuits identically, so it still fires those rows.
/// The gate was **re-derived, not weakened** — it now asserts the exact, named disagreement set
/// and asserts agreement everywhere else, so it can still fail in both directions.
///
/// ⚠⚠ **The refusal is scoped to the RESIDUAL-BINDER class and is NOT extended to
/// `encoding.opaque`.** The lowered lane may sweep its opaque fragments because its delegate
/// *is* `rho_pure_eval`, so *"the delegate could not decide it"* ⟺ *"the machine errors on it"*.
/// This lane's delegates — `formula::host_matches_verdict` and
/// `runtime::compare_collection_equality` — decline fragments the machine decides **totally**
/// (the separating conjunction is exactly such a fragment). Sweeping them here would refuse
/// guards the machine fires, which is divergence **K** of
/// `rholang-runtime/tests/rho_rholang_conformance.rs` made worse, in the resting direction. K is
/// `DontKnow ∨ Sat` and this defect was `Sat ∨ DontKnow`; they are different input classes and
/// neither remedy subsumes the other.
///
/// # The three steps, and what each one names
///
/// | step | when it runs | what stopped the decider | [`GuardRefusalCause`] |
/// |---|---|---|---|
/// | 1 | ★ **before** the ground leg | `encoding.vars` is non-empty — a binder the substitution could not reach | [`ResidualBinder`](GuardRefusalCause::ResidualBinder) |
/// | 2 | on the [`Sat3::DontKnow`] branch | a set-aside fragment the delegated decider could not answer | [`Unsupported`](GuardRefusalCause::Unsupported), [`NotABoolean`](GuardRefusalCause::NotABoolean), [`UnresolvedReference`](GuardRefusalCause::UnresolvedReference) |
/// | 3 | on the [`Sat3::DontKnow`] branch | [`ground_verdict_with`] left the ground formula undecided | [`FormulaUndecided`](GuardRefusalCause::FormulaUndecided) |
///
/// The order is the lowered lane's, arm for arm, so the two lanes name the same fact the same
/// way when they see it.
///
/// ## ★ Which causes this lane can reach, and which it CANNOT
///
/// [`GuardRefusalCause::EvaluationFailed`] and [`GuardRefusalCause::Malformed`] are **not
/// reachable here**, and that is a property of the delegated deciders rather than a gap in this
/// function. The lowered lane reads them off `rho_pure_eval`'s `EvalError` channel; this lane's
/// delegates — `formula::host_matches_verdict` and `runtime::compare_collection_equality` —
/// answer `Option<bool>`, which has no error channel to read. A division by zero inside a
/// surface guard is folded by the encoder into an opaque atom and arrives here as
/// [`Unsupported`], not as a failure, because nothing on this lane ever *ran* and failed.
/// Manufacturing the two causes anyway would be inventing evidence.
///
/// # The written guard
///
/// `written` is the guard **as the author typed it**; `substituted` is its image under the
/// arrived payload. Holding both is what makes [`RefusalProvenance`] *computed* rather than
/// guessed: an obstruction present in `written` obstructs every payload
/// ([`Term`](RefusalProvenance::Term)); one that appears only in `substituted` came in with
/// this datum ([`Datum`](RefusalProvenance::Datum)). A caller that has only the image — such as
/// [`eval_guard_disposition_via_substrate`] — passes it for both, which biases every computed
/// provenance toward `Term`, i.e. toward the louder class. Failing loud on a refusal that was
/// really data-dependent costs a spurious diagnostic; failing quiet on a genuine decider gap
/// costs the silence this whole vocabulary exists to remove.
pub fn surface_guard_disposition(written: &Proc, substituted: &Proc) -> SurfaceGuardDisposition {
    let encoding = encode_guard(substituted);

    // ── ★ 1. A binder the substitution could not reach — BEFORE the ground leg. ────────────
    //
    // Not a diagnosis: a VERDICT. The reducer evaluates both operands of every connective and
    // errors on an unresolved binder, so a guard that still mentions one rests on the machine
    // however the substrate's short-circuits settle the formula. Consulting `encoding.vars` is
    // the only place the fact survives — `GuardFormula::or` has already discarded the offending
    // disjunct from the formula by the time this runs.
    //
    // `refusal_for` is reused rather than a refusal being built here, so there is exactly ONE
    // construction site for a `ResidualBinder` on this lane: `diagnose`'s step 1 is its first
    // arm, and a non-empty `vars` reaches it unconditionally.
    match encoding.vars.is_empty() {
        true => {},
        false => {
            return SurfaceGuardDisposition::Undecided(refusal_for(&encoding, written, substituted))
        },
    }

    // ── 2. The substrate decides what is left. ────────────────────────────────────────────
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
        Sat3::Sat => SurfaceGuardDisposition::Admits,
        Sat3::Unsat => SurfaceGuardDisposition::Refutes,
        Sat3::DontKnow => {
            SurfaceGuardDisposition::Undecided(refusal_for(&encoding, written, substituted))
        },
    }
}

/// Why [`surface_guard_disposition`] reached no verdict, in the lowered lane's step order.
///
/// Total by construction: step 3 is unconditional, so every refusal gets a cause.
///
/// ⚠ Called from **two** places in [`surface_guard_disposition`], and the split is what makes
/// step 1 a verdict rather than a diagnosis: once from the `encoding.vars`-non-empty guard that
/// runs *before* the ground leg, and once from the [`Sat3::DontKnow`] branch *after* it. The two
/// call sites are disjoint — the second is only reached with an empty `vars` — so
/// [`diagnose`]'s step 1 answers the first and its steps 2–3 answer the second, with no cause
/// constructed twice.
fn refusal_for(encoding: &GuardEncoding, written: &Proc, substituted: &Proc) -> GuardRefusal {
    match diagnose(encoding) {
        // ── 1 & the always-`Term` half of 2 ────────────────────────────────────────────────
        //
        // A binder that survived substitution is one no payload supplies: substitution has
        // ALREADY applied every binding this receive will ever get. The same holds for a
        // reference the encoder could not even name. Neither becomes answerable under a
        // different payload, so neither needs the written guard consulted.
        Some((
            cause @ (GuardRefusalCause::ResidualBinder { .. }
            | GuardRefusalCause::UnresolvedReference { .. }),
            _,
        )) => GuardRefusal::new(cause, RefusalProvenance::Term, render_proc_text(substituted)),

        // ── 2, the computed half ───────────────────────────────────────────────────────────
        //
        // ★ The provenance is decided by asking the WRITTEN guard the same question, and
        // comparing the *cause* rather than tabulating a per-variant answer. Tabulating is what
        // lets a gate drift; this way a new cause is classified by the one rule that classifies
        // every other.
        Some((cause, _)) => {
            let in_term = matches!(
                diagnose(&encode_guard(written)),
                Some((written_cause, _)) if discriminant_of(&written_cause) == discriminant_of(&cause)
            );
            let provenance = match in_term {
                true => RefusalProvenance::Term,
                false => RefusalProvenance::Datum,
            };
            // A `Term` obstruction is the same under every payload, so the guard AS WRITTEN is
            // what to name. A `Datum` one is not in the written guard at all, so naming it
            // would point the author at a term that is fine.
            let named = match provenance {
                RefusalProvenance::Term => written,
                RefusalProvenance::Datum => substituted,
            };
            GuardRefusal::new(cause, provenance, render_proc_text(named))
        },

        // ── 3. The substrate's own ground procedures gave up. ──────────────────────────────
        None => GuardRefusal::new(
            GuardRefusalCause::FormulaUndecided,
            RefusalProvenance::Term,
            render_proc_text(substituted),
        ),
    }
}

/// Steps 1 and 2, run against one encoding: the first thing that stops this lane deciding it,
/// or `None` when nothing in the encoding does (step 3's territory).
///
/// Returns the offending fragment alongside the cause so the caller can name it.
///
/// ⚠ This function is a **classifier**, not the control flow: whether step 1 changes a verdict
/// is decided by [`surface_guard_disposition`], which consults `encoding.vars` before the ground
/// leg. Step 1 is kept here as well — rather than moved out — because [`refusal_for`] must stay
/// total over both call sites, and because the *provenance* rule for a residual binder
/// (always `Term`) belongs beside the other causes it is compared against.
///
/// ★ Step 1 is also what makes the second call site's answer honest: reaching this function
/// from the [`Sat3::DontKnow`] branch with a non-empty `vars` is impossible, so a
/// `ResidualBinder` never masquerades as a diagnosis of a formula the substrate merely failed to
/// settle.
fn diagnose(encoding: &GuardEncoding) -> Option<(GuardRefusalCause, Option<Arc<Proc>>)> {
    // ── 1. A binder the substitution could not reach. ──────────────────────────────────────
    if !encoding.vars.is_empty() {
        return Some((
            GuardRefusalCause::ResidualBinder { slots: encoding.vars.names().to_vec() },
            None,
        ));
    }

    // ── 2. The first set-aside fragment the delegated deciders could not answer. ───────────
    //
    // ⚠ The sweep is over `encoding.opaque` and not over `encoding.formula.atoms()`, because
    // `GuardFormula::{and,or,implies,not}` collapse at CONSTRUCTION time: `true or ⟨opaque⟩` is
    // built as `True`, and the fragment is gone from the formula while still being the thing
    // the author has to be told about. This is the same sweep domain
    // `substrate_guard_disposition` gives its own step 2, and for the same reason.
    let mut resolver = GuardAtomResolver { encoding };
    for (id, fragment) in encoding.opaque.iter().enumerate() {
        let atom = GuardAtom { id: id as u32, kind: fragment.kind };
        match resolver.resolve(atom) {
            Sat3::Sat | Sat3::Unsat => continue,
            Sat3::DontKnow => return Some((fragment_cause(fragment), Some(fragment.term.clone()))),
        }
    }
    None
}

/// The cause for one set-aside fragment the delegated deciders could not answer.
///
/// ★ Exhaustive over [`OpaquePosition`] and over [`GuardAtomKind`] with **no catch-all**: a new
/// atom kind must be classified here or this stops compiling. An unclassified kind falling
/// through to one answer would rebuild, one variant at a time, exactly the collapsed set this
/// vocabulary removes.
fn fragment_cause(fragment: &OpaqueFragment) -> GuardRefusalCause {
    match fragment.position {
        // The fragment is not one of the verdict-producing constructors. No payload makes
        // `x + 1` or `0` a verdict — that is a fact about the guard's SORT, and it is the same
        // fact `guard_par_substrate::never_a_predicate` reports as `NotABoolean`.
        OpaquePosition::NotAPredicate => GuardRefusalCause::NotABoolean,

        // The fragment stood where a verdict was required, so the decider had a predicate and
        // no procedure for it — a COVERAGE fact. The node names come from the atom kind, which
        // is the surface lane's own classification of which decider owns the fragment.
        OpaquePosition::Predicate => match fragment.kind {
            // ⚠ A bare binder the encoder could not key. `var_key` is total over `Var` today,
            // so this is unreachable — and it is kept, and kept LOUD, because "unreachable" is
            // a property of `var_key`'s two arms and a third `Var` variant would revive it
            // silently. Row 5 of the cause table: row 1's fact, other route.
            GuardAtomKind::Uncovered if matches!(fragment.term.as_ref(), Proc::PVar(_)) => {
                GuardRefusalCause::UnresolvedReference { slot: render_proc_text(&fragment.term) }
            },
            kind => GuardRefusalCause::Unsupported { nodes: vec![undecidable_node_name(kind)] },
        },
    }
}

/// The author-facing name of the construct an atom kind stands for.
///
/// Exhaustive with no catch-all, for the same reason
/// `rho_pure_eval::decidable::unsupported_kind` is: a new kind must be named here rather than
/// silently joining whichever phrase the fall-through happened to give.
fn undecidable_node_name(kind: GuardAtomKind) -> String {
    match kind {
        GuardAtomKind::Spatial => "spatial match (`matches`)",
        GuardAtomKind::StructuralEquality => "structural equality on a collection",
        GuardAtomKind::NonLinear => "non-linear integer arithmetic (`*`, `/`, `%`)",
        GuardAtomKind::ProcessShaped => "a process in guard position",
        GuardAtomKind::Uncovered => "a construct outside the encoder's coverage",
    }
    .to_string()
}

/// Cause identity **up to payload**: two causes are the same obstruction when they are the same
/// variant carrying the same names, which is exactly what "is this already in the written
/// guard?" has to compare.
fn discriminant_of(
    cause: &GuardRefusalCause,
) -> (std::mem::Discriminant<GuardRefusalCause>, String) {
    let detail = match cause {
        GuardRefusalCause::Unsupported { nodes } => nodes.join(", "),
        GuardRefusalCause::ResidualBinder { slots } => slots.join(", "),
        GuardRefusalCause::UnresolvedReference { slot } => slot.clone(),
        GuardRefusalCause::EvaluationFailed { .. }
        | GuardRefusalCause::NotABoolean
        | GuardRefusalCause::Malformed
        | GuardRefusalCause::FormulaUndecided => String::new(),
    };
    (std::mem::discriminant(cause), detail)
}

/// The surface lane's rendering of a guard term, meeting [`GuardRefusal::guard`]'s contract:
/// total, deterministic, and bounded.
///
/// ★ Unlike the lowered lane — whose `Par` is a protobuf with no stable printer, so
/// `render_par_text` falls back to an opaque hash — the surface `Proc` has a `Display` that IS
/// the surface syntax. The author gets the guard back in the notation they wrote it in.
///
/// Bounded by truncation at [`REFUSAL_GUARD_BUDGET`] bytes on a **character** boundary, with a
/// fixed marker: a guard term is author-written and small, but "bounded" must be a property of
/// the function rather than of the inputs it has been given so far, because this text reaches a
/// diagnostic channel.
fn render_proc_text(proc: &Proc) -> String {
    let rendered = proc.to_string();
    match rendered.len() <= REFUSAL_GUARD_BUDGET {
        true => rendered,
        false => {
            // `floor_char_boundary` is unstable, so the boundary is found by the stable
            // `is_char_boundary` walk. It terminates: byte 0 is always a boundary.
            let mut cut = REFUSAL_GUARD_BUDGET;
            while !rendered.is_char_boundary(cut) {
                cut -= 1;
            }
            format!("{}…", &rendered[..cut])
        },
    }
}

/// The byte budget [`render_proc_text`] truncates a guard rendering at.
///
/// Large enough that no guard in the corpus is truncated (the longest is well under 200 bytes),
/// small enough that a pathological term cannot flood a diagnostic channel.
const REFUSAL_GUARD_BUDGET: usize = 512;

/// The assignment for an already-substituted guard: empty.
///
/// A substituted guard has no binders left, so nothing needs binding — and the assignment is
/// still sized to the var map so that an unbound slot reads as unbound and yields `DontKnow`,
/// never a silent default.
///
/// ⚠ Since [`surface_guard_disposition`]'s step 1 became a verdict, every caller reaching here
/// has an **empty** `vars`, so this is always `GuardAssignment::with_len(0)`. It is written
/// against the var map rather than as a constant because that is a property of the *caller's*
/// control flow: the sizing is what would keep a residual binder undecided if the guard above
/// were ever removed, and a hard-coded zero would silently answer a default instead.
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
#[path = "../../tests/support/rholang_guard_substrate_recursive_oracle.rs"]
mod recursive_oracle;

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
