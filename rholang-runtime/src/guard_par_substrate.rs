//! **The `Par` → substrate encoder** — the compile-time half of the `where`-guard wire.
//!
//! # Why a second encoder, and why it is not a second *decider*
//!
//! A `where` guard is decided twice in this tree's life: once at lowering (can it be settled
//! before any payload exists?) and once at COMM time (does it hold for *this* payload?). The two
//! sites hold the guard in different representations — the surface `Proc` on one side, the
//! lowered `rhoapi::Par` on the other — so each needs its own *encoder*.
//!
//! What they must **not** have is their own *decider*. Both encode into the one substrate
//! vocabulary, [`GuardFormula`], and both then ask the same procedures in
//! [`mettail_prattail::guard_formula`]. The surface half is
//! `mettail_languages::rhocalc::guard_substrate`; this is the lowered half.
//!
//! ```text
//!    Proc ──encode──┐                        ┌── static_verdict   (compile time, HERE)
//!                   ├──▶  GuardFormula  ──▶──┤
//!    Par  ──encode──┘                        └── ground_verdict   (COMM time, the surface half)
//! ```
//!
//! # Variables
//!
//! A lowered guard's variables are de Bruijn indices ([`VarInstance::BoundVar`]) or match-frame
//! slots ([`VarInstance::FreeVar`]), so the [`GuardVarMap`] key is the index with its kind —
//! `bound$3`, `free$0`. A [`VarInstance::Wildcard`] binds anything and is therefore not a
//! *readable* value; it is encoded as an opaque atom rather than as a variable, so nothing can
//! be concluded from it.
//!
//! # Coverage
//!
//! | `ExprInstance` | substrate image |
//! |---|---|
//! | `GBool` | the logical constants |
//! | `GInt`, `GString`, `GDouble` | literal operands |
//! | `EAndBody`, `EOrBody`, `ENotBody` | the connectives |
//! | `EEqBody`, `ENeqBody`, `ELtBody`, `ELteBody`, `EGtBody`, `EGteBody` | comparisons |
//! | `EPlusBody`, `EMinusBody`, `ENegBody`, `EMultBody` (by a constant) | linear arithmetic |
//! | `EDivBody`, `EModBody` | folded when both operands are ground, else `NonLinear` |
//! | `EMatchesBody` | `Spatial` — the structural core's, never decided here |
//! | `EListBody`, `ESetBody`, `EMapBody`, `ETupleBody` | `StructuralEquality` |
//! | anything else, and any `Par` that is not a single expression | fails closed |
//!
//! There is no `_` arm over `ExprInstance`: a new `rhoapi` constructor is a compile error here
//! rather than a silent `Uncovered`.

use models::rhoapi::expr::ExprInstance;
use models::rhoapi::var::VarInstance;
use models::rhoapi::{
    EAnd, EDiv, EEq, EGt, EGte, ELt, ELte, EMatches, EMinus, EMod, EMult, ENeg, ENeq, ENot, EOr,
    EPlus, EVar, Expr, Par, Var,
};

use mettail_prattail::guard_formula::{
    static_verdict, str_equals, CmpOp, GuardAtom, GuardAtomKind, GuardFormula, GuardValue,
    GuardVarMap, LinearForm, ScalarOperand, StaticVerdict, CONSENSUS_SUBSTRATE_CONFIG,
};
use mettail_prattail::ordered_field::OrderedF64;

// ══════════════════════════════════════════════════════════════════════════════════════════════
// The encoding result
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// A lowered guard, encoded for the substrate.
#[derive(Clone, Debug)]
pub struct ParGuardEncoding {
    /// The substrate image.
    pub formula: GuardFormula,
    /// The de Bruijn / match-frame slot ⇄ substrate-index map.
    pub vars: GuardVarMap,
}

impl ParGuardEncoding {
    /// `true` iff every leaf is decidable by the substrate's own procedures.
    pub fn reaches_substrate(&self) -> bool {
        self.formula.reaches_substrate()
    }

    /// The static verdict over the CONSENSUS substrate domain.
    ///
    /// The budget is `CONSENSUS_SUBSTRATE_CONFIG`, not a caller-chosen one — see that
    /// constant's documentation for why the guard path's budget is a consensus parameter.
    pub fn static_verdict(&self) -> StaticVerdict {
        static_verdict(&self.formula, CONSENSUS_SUBSTRATE_CONFIG)
    }
}

/// Encode a lowered `where` guard into the substrate.
///
/// Total: every `Par` gets an encoding. A shape outside the covered fragment becomes an opaque
/// atom, never a wrong answer.
pub fn encode_par_guard(cond: &Par) -> ParGuardEncoding {
    let mut encoder = ParEncoder { vars: GuardVarMap::new(), next_atom: 0 };
    let formula = encoder.par_formula(cond);
    ParGuardEncoding { formula, vars: encoder.vars }
}

/// ★ **THE SUBSTRATE'S VERDICT for a lowered guard** — the compile-time authority leg of
/// `crate::guard_discharge::classify`.
///
/// `Some(true)` iff the guard is VALID (holds under every assignment to the receive's binders),
/// `Some(false)` iff it is UNSATISFIABLE, `None` when it is contingent (a genuine run-time
/// question) or outside the decided fragment.
///
/// # ⚠ This verdict alone may NOT change the artifact
///
/// It is relative to the bounded integer domain the Presburger automata run over
/// (`SubstrateConfig::bit_width`), and over a bounded domain neither
/// `valid over 2^w ⟹ valid over ℤ` nor `unsat over 2^w ⟹ unsat over ℤ` holds. The caller
/// therefore fences it against an evaluator with the concrete semantics before acting — see
/// [`crate::guard_discharge::classify`].
pub fn substrate_verdict(cond: &Par) -> Option<bool> {
    encode_par_guard(cond).static_verdict().settled()
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// The encoder
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// One side of a comparison, classified. Mirrors the surface encoder's `Operand`.
#[derive(Clone, Debug)]
enum Operand {
    Int(LinearForm),
    Lit(GuardValue),
    Var(usize),
    NonLinear,
    Structural,
    Uncovered,
}

struct ParEncoder {
    vars: GuardVarMap,
    /// Opaque-atom ids are dense and monotone. Unlike the surface encoder this one keeps no side
    /// table of fragments: the compile-time leg has nothing to delegate to (the structural core
    /// runs at COMM time, on a payload that does not exist yet), so an opaque atom here is
    /// simply undecided — which is the correct compile-time answer for a structural question.
    next_atom: u32,
}

impl ParEncoder {
    // ── Formula position ──────────────────────────────────────────────────────────────────

    fn par_formula(&mut self, par: &Par) -> GuardFormula {
        match self.sole_expr(par) {
            Some(expr) => self.expr_formula(expr),
            None => self.atom(GuardAtomKind::ProcessShaped),
        }
    }

    fn opt_par_formula(&mut self, par: Option<&Par>) -> GuardFormula {
        match par {
            Some(p) => self.par_formula(p),
            None => self.atom(GuardAtomKind::Uncovered),
        }
    }

    /// The single `Expr` of a guard `Par`, or `None` if the `Par` carries anything else — a
    /// send, a receive, a `new`, a bundle, a connective, a conditional, or more than one
    /// expression. Those are processes, not predicates.
    fn sole_expr<'p>(&self, par: &'p Par) -> Option<&'p Expr> {
        let is_pure_expression = par.sends.is_empty()
            && par.receives.is_empty()
            && par.news.is_empty()
            && par.matches.is_empty()
            && par.bundles.is_empty()
            && par.unforgeables.is_empty()
            && par.connectives.is_empty()
            && par.conditionals.is_empty()
            && par.exprs.len() == 1;
        is_pure_expression.then(|| &par.exprs[0])
    }

    fn expr_formula(&mut self, expr: &Expr) -> GuardFormula {
        let Some(instance) = expr.expr_instance.as_ref() else {
            return self.atom(GuardAtomKind::Uncovered);
        };
        match instance {
            // ── The logical constants. ────────────────────────────────────────────────────
            ExprInstance::GBool(true) => GuardFormula::True,
            ExprInstance::GBool(false) => GuardFormula::False,

            // ── The connectives. ─────────────────────────────────────────────────────────
            ExprInstance::EAndBody(EAnd { p1, p2 }) => {
                let left = self.opt_par_formula(p1.as_ref());
                let right = self.opt_par_formula(p2.as_ref());
                GuardFormula::and(left, right)
            },
            ExprInstance::EOrBody(EOr { p1, p2 }) => {
                let left = self.opt_par_formula(p1.as_ref());
                let right = self.opt_par_formula(p2.as_ref());
                GuardFormula::or(left, right)
            },
            ExprInstance::ENotBody(ENot { p }) => {
                let inner = self.opt_par_formula(p.as_ref());
                GuardFormula::not(inner)
            },

            // ── The comparisons. ─────────────────────────────────────────────────────────
            //
            // ★ `implies` has no `rhoapi` node: `lower_proc` emits `a implies b` as
            // `EOrBody(ENotBody a, b)`, so the material implication arrives here already
            // decomposed and needs no arm of its own.
            ExprInstance::EEqBody(EEq { p1, p2 }) => self.comparison(CmpOp::Eq, p1, p2),
            ExprInstance::ENeqBody(ENeq { p1, p2 }) => self.comparison(CmpOp::Ne, p1, p2),
            ExprInstance::ELtBody(ELt { p1, p2 }) => self.comparison(CmpOp::Lt, p1, p2),
            ExprInstance::ELteBody(ELte { p1, p2 }) => self.comparison(CmpOp::Le, p1, p2),
            ExprInstance::EGtBody(EGt { p1, p2 }) => self.comparison(CmpOp::Gt, p1, p2),
            ExprInstance::EGteBody(EGte { p1, p2 }) => self.comparison(CmpOp::Ge, p1, p2),

            // ── The spatial atom — the structural core's, never decided here. ─────────────
            ExprInstance::EMatchesBody(EMatches { .. }) => self.atom(GuardAtomKind::Spatial),

            // ── A bare variable used as a boolean. ───────────────────────────────────────
            ExprInstance::EVarBody(EVar { v }) => match self.var_index(v.as_ref()) {
                Some(idx) => GuardFormula::Prop(
                    mettail_prattail::guard_formula::prop_var(&idx.to_string()),
                ),
                None => self.atom(GuardAtomKind::Uncovered),
            },

            // ── Arithmetic in FORMULA position is not a predicate. ───────────────────────
            ExprInstance::GInt(_)
            | ExprInstance::GString(_)
            | ExprInstance::GUri(_)
            | ExprInstance::GByteArray(_)
            | ExprInstance::GDouble(_)
            | ExprInstance::GBigInt(_)
            | ExprInstance::GBigRat(_)
            | ExprInstance::GFixedPoint(_)
            | ExprInstance::ENegBody(_)
            | ExprInstance::EPlusBody(_)
            | ExprInstance::EMinusBody(_)
            | ExprInstance::EMultBody(_)
            | ExprInstance::EDivBody(_)
            | ExprInstance::EModBody(_)
            | ExprInstance::EPercentPercentBody(_)
            | ExprInstance::EPlusPlusBody(_)
            | ExprInstance::EMinusMinusBody(_)
            | ExprInstance::EMethodBody(_) => self.atom(GuardAtomKind::Uncovered),

            // ── Collections in formula position. ─────────────────────────────────────────
            ExprInstance::EListBody(_)
            | ExprInstance::ESetBody(_)
            | ExprInstance::EMapBody(_)
            | ExprInstance::ETupleBody(_) => self.atom(GuardAtomKind::StructuralEquality),

            // ── Structures the guard path has never been taught. ─────────────────────────
            ExprInstance::EPathmapBody(_) | ExprInstance::EZipperBody(_) => {
                self.atom(GuardAtomKind::Uncovered)
            },
        }
    }

    // ── Comparison position ───────────────────────────────────────────────────────────────

    fn comparison(&mut self, op: CmpOp, left: &Option<Par>, right: &Option<Par>) -> GuardFormula {
        let lhs = self.opt_operand(left.as_ref());
        let rhs = self.opt_operand(right.as_ref());
        match (lhs, rhs) {
            (Operand::Int(a), Operand::Int(b)) => self.linear(op, &a, &b),
            (Operand::Int(a), Operand::Var(idx)) => self.linear(op, &a, &LinearForm::var(idx)),
            (Operand::Var(idx), Operand::Int(b)) => self.linear(op, &LinearForm::var(idx), &b),

            (Operand::Var(idx), Operand::Lit(GuardValue::Bool(b))) => self.prop_compare(op, idx, b),
            (Operand::Lit(GuardValue::Bool(b)), Operand::Var(idx)) => {
                self.prop_compare(op.flipped(), idx, b)
            },

            (Operand::Var(idx), Operand::Lit(GuardValue::Str(s)))
                if matches!(op, CmpOp::Eq | CmpOp::Ne) =>
            {
                str_compare(op, idx, &s)
            },
            (Operand::Lit(GuardValue::Str(s)), Operand::Var(idx))
                if matches!(op, CmpOp::Eq | CmpOp::Ne) =>
            {
                str_compare(op, idx, &s)
            },

            (Operand::Lit(a), Operand::Lit(b)) => match op.decide(&a, &b) {
                Some(true) => GuardFormula::True,
                Some(false) => GuardFormula::False,
                // A cross-sort comparison is not a question the operator answers.
                None => self.atom(GuardAtomKind::Uncovered),
            },
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

            (Operand::Structural, _) | (_, Operand::Structural) => {
                self.atom(GuardAtomKind::StructuralEquality)
            },
            (Operand::NonLinear, _) | (_, Operand::NonLinear) => {
                self.atom(GuardAtomKind::NonLinear)
            },
            _ => self.atom(GuardAtomKind::Uncovered),
        }
    }

    fn linear(&mut self, op: CmpOp, left: &LinearForm, right: &LinearForm) -> GuardFormula {
        match left.compare(op, right) {
            Some(pred) => GuardFormula::Linear(pred),
            // Coefficient overflow while normalizing. Wrapping would encode a DIFFERENT
            // constraint, so the encoder refuses.
            None => self.atom(GuardAtomKind::NonLinear),
        }
    }

    fn prop_compare(&mut self, op: CmpOp, idx: usize, literal: bool) -> GuardFormula {
        let atom =
            GuardFormula::Prop(mettail_prattail::guard_formula::prop_var(&idx.to_string()));
        match (op, literal) {
            (CmpOp::Eq, true) | (CmpOp::Ne, false) => atom,
            (CmpOp::Eq, false) | (CmpOp::Ne, true) => GuardFormula::not(atom),
            _ => GuardFormula::ScalarRel {
                op,
                left: ScalarOperand::Var(idx),
                right: ScalarOperand::Lit(GuardValue::Bool(literal)),
            },
        }
    }

    // ── Operand position ──────────────────────────────────────────────────────────────────

    fn opt_operand(&mut self, par: Option<&Par>) -> Operand {
        match par {
            Some(p) => self.operand(p),
            None => Operand::Uncovered,
        }
    }

    fn operand(&mut self, par: &Par) -> Operand {
        let Some(expr) = self.sole_expr(par) else {
            return Operand::Uncovered;
        };
        let Some(instance) = expr.expr_instance.as_ref() else {
            return Operand::Uncovered;
        };
        match instance {
            ExprInstance::GInt(n) => Operand::Int(LinearForm::constant(*n)),
            ExprInstance::GBool(b) => Operand::Lit(GuardValue::Bool(*b)),
            ExprInstance::GString(s) => Operand::Lit(GuardValue::Str(s.clone())),
            // `GDouble` carries the IEEE-754 bit pattern, which is how the lowering stores an
            // `f64` — decode it rather than treating a float guard as uncovered.
            ExprInstance::GDouble(bits) => {
                Operand::Lit(GuardValue::Float(OrderedF64(f64::from_bits(*bits))))
            },

            ExprInstance::EVarBody(EVar { v }) => match self.var_index(v.as_ref()) {
                Some(idx) => Operand::Var(idx),
                None => Operand::Uncovered,
            },

            ExprInstance::EPlusBody(EPlus { p1, p2 }) => {
                self.arithmetic(p1.as_ref(), p2.as_ref(), LinearForm::add)
            },
            ExprInstance::EMinusBody(EMinus { p1, p2 }) => {
                self.arithmetic(p1.as_ref(), p2.as_ref(), LinearForm::sub)
            },
            ExprInstance::ENegBody(ENeg { p }) => match self.int_form(p.as_ref()) {
                Some(form) => match form.negate() {
                    Some(negated) => Operand::Int(negated),
                    None => Operand::NonLinear,
                },
                None => Operand::Uncovered,
            },

            // `*` is linear only when one side is a constant; Presburger arithmetic has no
            // multiplication of two variables.
            ExprInstance::EMultBody(EMult { p1, p2 }) => {
                match (self.int_form(p1.as_ref()), self.int_form(p2.as_ref())) {
                    (Some(x), Some(y)) if x.is_constant() => scaled(&y, x.constant),
                    (Some(x), Some(y)) if y.is_constant() => scaled(&x, y.constant),
                    (Some(_), Some(_)) => Operand::NonLinear,
                    _ => Operand::Uncovered,
                }
            },

            ExprInstance::EDivBody(EDiv { p1, p2 }) => {
                self.integer_division(p1.as_ref(), p2.as_ref(), i64::checked_div)
            },
            ExprInstance::EModBody(EMod { p1, p2 }) => {
                self.integer_division(p1.as_ref(), p2.as_ref(), i64::checked_rem)
            },

            ExprInstance::EListBody(_)
            | ExprInstance::ESetBody(_)
            | ExprInstance::EMapBody(_)
            | ExprInstance::ETupleBody(_) => Operand::Structural,

            ExprInstance::GUri(_)
            | ExprInstance::GByteArray(_)
            | ExprInstance::GBigInt(_)
            | ExprInstance::GBigRat(_)
            | ExprInstance::GFixedPoint(_)
            | ExprInstance::ENotBody(_)
            | ExprInstance::EAndBody(_)
            | ExprInstance::EOrBody(_)
            | ExprInstance::EEqBody(_)
            | ExprInstance::ENeqBody(_)
            | ExprInstance::ELtBody(_)
            | ExprInstance::ELteBody(_)
            | ExprInstance::EGtBody(_)
            | ExprInstance::EGteBody(_)
            | ExprInstance::EMatchesBody(_)
            | ExprInstance::EPercentPercentBody(_)
            | ExprInstance::EPlusPlusBody(_)
            | ExprInstance::EMinusMinusBody(_)
            | ExprInstance::EMethodBody(_)
            | ExprInstance::EPathmapBody(_)
            | ExprInstance::EZipperBody(_) => Operand::Uncovered,
        }
    }

    fn arithmetic(
        &mut self,
        left: Option<&Par>,
        right: Option<&Par>,
        combine: fn(&LinearForm, &LinearForm) -> Option<LinearForm>,
    ) -> Operand {
        match (self.int_form(left), self.int_form(right)) {
            (Some(a), Some(b)) => match combine(&a, &b) {
                Some(form) => Operand::Int(form),
                None => Operand::NonLinear,
            },
            _ => Operand::Uncovered,
        }
    }

    fn integer_division(
        &mut self,
        left: Option<&Par>,
        right: Option<&Par>,
        combine: fn(i64, i64) -> Option<i64>,
    ) -> Operand {
        match (self.int_form(left), self.int_form(right)) {
            (Some(a), Some(b)) if a.is_constant() && b.is_constant() => {
                match combine(a.constant, b.constant) {
                    Some(value) => Operand::Int(LinearForm::constant(value)),
                    // Division by zero, or `i64::MIN / -1`.
                    None => Operand::NonLinear,
                }
            },
            (Some(_), Some(_)) => Operand::NonLinear,
            _ => Operand::Uncovered,
        }
    }

    fn int_form(&mut self, par: Option<&Par>) -> Option<LinearForm> {
        match self.opt_operand(par) {
            Operand::Int(form) => Some(form),
            Operand::Var(idx) => Some(LinearForm::var(idx)),
            _ => None,
        }
    }

    // ── Variables and atoms ───────────────────────────────────────────────────────────────

    /// The substrate index for a lowered variable.
    ///
    /// A [`VarInstance::Wildcard`] is deliberately NOT a variable: it binds anything and is
    /// never read, so nothing may be concluded about "its value". It returns `None`, which the
    /// callers turn into an opaque atom.
    fn var_index(&mut self, var: Option<&Var>) -> Option<usize> {
        match var?.var_instance.as_ref()? {
            VarInstance::BoundVar(i) => Some(self.vars.intern(&format!("bound${i}"))),
            VarInstance::FreeVar(i) => Some(self.vars.intern(&format!("free${i}"))),
            VarInstance::Wildcard(_) => None,
        }
    }

    fn atom(&mut self, kind: GuardAtomKind) -> GuardFormula {
        let id = self.next_atom;
        self.next_atom += 1;
        GuardFormula::Atom(GuardAtom { id, kind })
    }
}

fn scaled(form: &LinearForm, factor: i64) -> Operand {
    match form.scale(factor) {
        Some(scaled) => Operand::Int(scaled),
        None => Operand::NonLinear,
    }
}

fn str_compare(op: CmpOp, idx: usize, literal: &str) -> GuardFormula {
    let atom = GuardFormula::Scalar { var: idx, pred: str_equals(literal) };
    match op {
        CmpOp::Eq => atom,
        _ => GuardFormula::not(atom),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::rhoapi::expr::ExprInstance as EI;

    fn expr(instance: EI) -> Par {
        Par { exprs: vec![Expr { expr_instance: Some(instance) }], ..Default::default() }
    }

    fn gint(n: i64) -> Par {
        expr(EI::GInt(n))
    }

    fn gbool(b: bool) -> Par {
        expr(EI::GBool(b))
    }

    fn gstring(s: &str) -> Par {
        expr(EI::GString(s.to_string()))
    }

    fn bound(i: i32) -> Par {
        expr(EI::EVarBody(EVar {
            v: Some(Var { var_instance: Some(VarInstance::BoundVar(i)) }),
        }))
    }

    fn binary(build: fn(Option<Par>, Option<Par>) -> EI, a: Par, b: Par) -> Par {
        expr(build(Some(a), Some(b)))
    }

    fn eq(a: Par, b: Par) -> Par {
        binary(|p1, p2| EI::EEqBody(EEq { p1, p2 }), a, b)
    }

    fn lt(a: Par, b: Par) -> Par {
        binary(|p1, p2| EI::ELtBody(ELt { p1, p2 }), a, b)
    }

    fn plus(a: Par, b: Par) -> Par {
        binary(|p1, p2| EI::EPlusBody(EPlus { p1, p2 }), a, b)
    }

    #[test]
    fn a_ground_constant_guard_settles() {
        assert_eq!(substrate_verdict(&gbool(true)), Some(true));
        assert_eq!(substrate_verdict(&gbool(false)), Some(false));
    }

    #[test]
    fn a_ground_comparison_settles() {
        assert_eq!(substrate_verdict(&eq(gint(42), gint(42))), Some(true));
        assert_eq!(substrate_verdict(&eq(gint(42), gint(41))), Some(false));
        assert_eq!(substrate_verdict(&lt(gint(1), gint(2))), Some(true));
        assert_eq!(substrate_verdict(&lt(gint(2), gint(1))), Some(false));
    }

    #[test]
    fn a_ground_string_comparison_settles() {
        assert_eq!(substrate_verdict(&eq(gstring("hi"), gstring("hi"))), Some(true));
        assert_eq!(substrate_verdict(&eq(gstring("hi"), gstring("bye"))), Some(false));
    }

    #[test]
    fn the_connectives_settle_from_their_operands() {
        let and = binary(|p1, p2| EI::EAndBody(EAnd { p1, p2 }), gbool(true), gbool(false));
        assert_eq!(substrate_verdict(&and), Some(false));
        let or = binary(|p1, p2| EI::EOrBody(EOr { p1, p2 }), gbool(true), gbool(false));
        assert_eq!(substrate_verdict(&or), Some(true));
        let not = expr(EI::ENotBody(ENot { p: Some(Box::new(gbool(false))) }));
        assert_eq!(substrate_verdict(&not), Some(true));
    }

    /// `a implies b` has no `rhoapi` node — the lowering emits `EOr(ENot a, b)`. The encoder
    /// therefore needs no `implies` arm, and material implication still settles.
    #[test]
    fn material_implication_arrives_already_decomposed_and_settles() {
        let not_antecedent = expr(EI::ENotBody(ENot { p: Some(Box::new(gbool(false))) }));
        let implication = binary(
            |p1, p2| EI::EOrBody(EOr { p1, p2 }),
            not_antecedent,
            gbool(false),
        );
        assert_eq!(
            substrate_verdict(&implication),
            Some(true),
            "false implies anything is vacuously true"
        );
    }

    /// ★ THE CAPABILITY GAIN. `rho_pure_eval` requires a binder-closed condition and declines an
    /// OPEN formula outright; the substrate decides this one.
    #[test]
    fn an_open_tautology_settles_which_rho_pure_eval_cannot_do() {
        // x < x + 1
        let guard = lt(bound(0), plus(bound(0), gint(1)));
        assert_eq!(substrate_verdict(&guard), Some(true));
    }

    #[test]
    fn an_open_contradiction_settles() {
        let guard = binary(
            |p1, p2| EI::EAndBody(EAnd { p1, p2 }),
            eq(bound(0), gint(1)),
            eq(bound(0), gint(2)),
        );
        assert_eq!(substrate_verdict(&guard), Some(false));
    }

    #[test]
    fn a_payload_dependent_guard_does_not_settle() {
        assert_eq!(substrate_verdict(&eq(bound(0), gint(42))), None);
    }

    #[test]
    fn a_process_shaped_guard_fails_closed() {
        let process = Par { sends: vec![Default::default()], ..Default::default() };
        assert_eq!(substrate_verdict(&process), None);
        assert!(!encode_par_guard(&process).reaches_substrate());
    }

    #[test]
    fn a_spatial_guard_is_never_decided_here() {
        let guard = expr(EI::EMatchesBody(EMatches {
            target: Some(gint(42)),
            pattern: Some(gint(42)),
        }));
        assert_eq!(
            substrate_verdict(&guard),
            None,
            "the compile-time leg has no payload and no matcher; a spatial guard is a run-time \
             question and must NOT be settled here"
        );
        assert_eq!(
            encode_par_guard(&guard).formula.atoms()[0].kind,
            GuardAtomKind::Spatial
        );
    }

    #[test]
    fn a_wildcard_is_not_a_readable_variable() {
        let guard = eq(
            expr(EI::EVarBody(EVar {
                v: Some(Var { var_instance: Some(VarInstance::Wildcard(Default::default())) }),
            })),
            gint(1),
        );
        assert_eq!(substrate_verdict(&guard), None);
        assert!(!encode_par_guard(&guard).reaches_substrate());
    }

    #[test]
    fn linear_arithmetic_is_linearized() {
        // 2 * x + 3 < 10
        let two_x = binary(|p1, p2| EI::EMultBody(EMult { p1, p2 }), gint(2), bound(0));
        let guard = lt(plus(two_x, gint(3)), gint(10));
        let encoding = encode_par_guard(&guard);
        assert!(encoding.reaches_substrate());
        assert!(matches!(encoding.formula, GuardFormula::Linear(_)));
    }

    #[test]
    fn ground_division_folds_exactly() {
        let div = binary(|p1, p2| EI::EDivBody(EDiv { p1, p2 }), gint(7), gint(2));
        assert_eq!(substrate_verdict(&eq(div, gint(3))), Some(true));
        // Division by zero is refused, not panicked.
        let by_zero = binary(|p1, p2| EI::EDivBody(EDiv { p1, p2 }), gint(7), gint(0));
        assert_eq!(substrate_verdict(&eq(by_zero, gint(0))), None);
    }

    #[test]
    fn nonlinear_arithmetic_over_variables_fails_closed() {
        let product = binary(|p1, p2| EI::EMultBody(EMult { p1, p2 }), bound(0), bound(1));
        let guard = lt(product, gint(10));
        assert_eq!(substrate_verdict(&guard), None);
        assert_eq!(
            encode_par_guard(&guard).formula.atoms()[0].kind,
            GuardAtomKind::NonLinear
        );
    }

    #[test]
    fn distinct_de_bruijn_indices_get_distinct_substrate_variables() {
        let guard = lt(bound(0), bound(1));
        let encoding = encode_par_guard(&guard);
        assert_eq!(encoding.vars.len(), 2);
    }
}
