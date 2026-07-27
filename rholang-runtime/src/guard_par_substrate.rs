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
    BindPattern, EAnd, EDiv, EEq, EGt, EGte, ELt, ELte, EMatches, EMinus, EMod, EMult, ENeg, ENeq,
    ENot, EOr, EPlus, EVar, Expr, ListParWithRandom, Par, TaggedContinuation, Var,
};
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rspace_plus_plus::rspace::r#match::Match;

use mettail_prattail::algebra_tower::Sat3;
use mettail_prattail::guard_formula::{
    dont_know_policy, ground_verdict_with, static_verdict, str_equals, CmpOp, DontKnowPolicy,
    GuardAssignment, GuardAtom, GuardAtomKind, GuardFormula, GuardSiteKind, GuardValue,
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
    /// The original guard fragment behind each opaque atom, indexed by `GuardAtom::id`.
    ///
    /// Present for the same reason the surface encoder keeps one: an atom this module has no
    /// procedure for is decided by DELEGATION to the core that owns it, and delegation needs the
    /// fragment. Keeping it here rather than in `prattail` is what stops the substrate crate
    /// from growing a matcher of its own.
    pub opaque: Vec<Par>,
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

    /// The fragment behind an opaque atom.
    pub fn fragment(&self, atom: GuardAtom) -> Option<&Par> {
        self.opaque.get(atom.id as usize)
    }
}

/// Encode a lowered `where` guard into the substrate.
///
/// Total: every `Par` gets an encoding. A shape outside the covered fragment becomes an opaque
/// atom, never a wrong answer.
pub fn encode_par_guard(cond: &Par) -> ParGuardEncoding {
    let mut encoder = ParEncoder {
        vars: GuardVarMap::new(),
        opaque: Vec::new(),
    };
    let formula = encoder.par_formula(cond);
    ParGuardEncoding {
        formula,
        vars: encoder.vars,
        opaque: encoder.opaque,
    }
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
    substrate_verdict_with(cond, &mut |_| None)
}

/// [`substrate_verdict`], with a resolver for the atoms this module has no procedure for.
///
/// # Why a resolver, and not a match arm
///
/// The atoms are structural — `t matches φ`, equality of two collections — and structural
/// questions belong to the **structural core**, which is a different decider with its own
/// semantics. The substrate does not duplicate it; it *uses* it. Making delegation the only
/// route is what keeps a second, divergent matcher from growing here, exactly as it does on the
/// run-time leg (`mettail_languages::rhocalc::guard_substrate`'s `GuardAtomResolver`).
///
/// A resolver may answer `None` freely: an undecided atom leaves the whole guard undecided,
/// which is the fail-closed direction.
///
/// ## What a delegated verdict means for the fence
///
/// `crate::guard_discharge::classify` supplies a resolver backed by the same concrete-semantics
/// evaluator it later fences against. For a row whose *only* undecided leaf is a ground
/// structural atom, the fence therefore degenerates to "the structural core agrees with itself".
/// That is stated rather than hidden, and it is the correct reading: for a structural question
/// the structural core IS the authority (`StructuralPattern` obligations are covered by
/// `DovetailCoreStructural`), so there is no second opinion to seek. The fence retains its full
/// force on every leaf the substrate decides itself, which is where the bounded-domain hazard
/// lives.
pub fn substrate_verdict_with<F>(cond: &Par, resolve_atom: &mut F) -> Option<bool>
where
    F: FnMut(&Par) -> Option<bool>,
{
    let encoding = encode_par_guard(cond);
    if let Some(settled) = encoding.static_verdict().settled() {
        return Some(settled);
    }
    // Undecided by the substrate's own procedures. Resolve the opaque atoms and retry: the
    // formula is ground-decidable once every atom has a verdict.
    let atoms = encoding.formula.atoms();
    if atoms.is_empty() {
        return None;
    }
    let mut resolved: Vec<Option<bool>> = Vec::with_capacity(atoms.len());
    for atom in &atoms {
        let fragment = encoding.fragment(*atom)?;
        resolved.push(resolve_atom(fragment));
    }
    let substituted = substitute_atoms(&encoding.formula, &atoms, &resolved)?;
    static_verdict(&substituted, CONSENSUS_SUBSTRATE_CONFIG).settled()
}

/// Replace each opaque atom by the constant its resolver returned. `None` if any atom went
/// unresolved — the formula is then still undecided, and saying so is the fail-closed answer.
fn substitute_atoms(
    formula: &GuardFormula,
    atoms: &[GuardAtom],
    resolved: &[Option<bool>],
) -> Option<GuardFormula> {
    Some(match formula {
        GuardFormula::Atom(atom) => {
            let index = atoms.iter().position(|candidate| candidate == atom)?;
            match resolved.get(index).copied().flatten()? {
                true => GuardFormula::True,
                false => GuardFormula::False,
            }
        },
        GuardFormula::And(a, b) => GuardFormula::and(
            substitute_atoms(a, atoms, resolved)?,
            substitute_atoms(b, atoms, resolved)?,
        ),
        GuardFormula::Or(a, b) => GuardFormula::or(
            substitute_atoms(a, atoms, resolved)?,
            substitute_atoms(b, atoms, resolved)?,
        ),
        GuardFormula::Not(inner) => GuardFormula::not(substitute_atoms(inner, atoms, resolved)?),
        GuardFormula::Implies(a, b) => GuardFormula::implies(
            substitute_atoms(a, atoms, resolved)?,
            substitute_atoms(b, atoms, resolved)?,
        ),
        other => other.clone(),
    })
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
    /// The fragment behind each opaque atom, indexed by the atom's id.
    opaque: Vec<Par>,
}

impl ParEncoder {
    // ── Formula position ──────────────────────────────────────────────────────────────────

    fn par_formula(&mut self, par: &Par) -> GuardFormula {
        match self.sole_expr(par).cloned() {
            Some(expr) => self.expr_formula(&expr, par),
            None => self.atom_for(par, GuardAtomKind::ProcessShaped),
        }
    }

    fn opt_par_formula(&mut self, par: Option<&Par>) -> GuardFormula {
        match par {
            Some(p) => self.par_formula(p),
            None => self.atom_for(&Par::default(), GuardAtomKind::Uncovered),
        }
    }

    /// The single `Expr` of a guard `Par`, or `None` if the `Par` carries anything else — a
    /// send, a receive, a `new`, a bundle, a connective, a conditional, or more than one
    /// expression. Those are processes, not predicates.
    fn sole_expr<'p>(&self, par: &'p Par) -> Option<&'p Expr> {
        sole_expr_of(par)
    }

    fn expr_formula(&mut self, expr: &Expr, whole: &Par) -> GuardFormula {
        let Some(instance) = expr.expr_instance.as_ref() else {
            return self.atom_for(whole, GuardAtomKind::Uncovered);
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
            ExprInstance::EEqBody(EEq { p1, p2 }) => self.comparison(CmpOp::Eq, p1, p2, whole),
            ExprInstance::ENeqBody(ENeq { p1, p2 }) => self.comparison(CmpOp::Ne, p1, p2, whole),
            ExprInstance::ELtBody(ELt { p1, p2 }) => self.comparison(CmpOp::Lt, p1, p2, whole),
            ExprInstance::ELteBody(ELte { p1, p2 }) => self.comparison(CmpOp::Le, p1, p2, whole),
            ExprInstance::EGtBody(EGt { p1, p2 }) => self.comparison(CmpOp::Gt, p1, p2, whole),
            ExprInstance::EGteBody(EGte { p1, p2 }) => self.comparison(CmpOp::Ge, p1, p2, whole),

            // ── The spatial atom — the structural core's, never decided here. ─────────────
            ExprInstance::EMatchesBody(EMatches { .. }) => {
                self.atom_for(whole, GuardAtomKind::Spatial)
            },

            // ── A bare variable used as a boolean. ───────────────────────────────────────
            ExprInstance::EVarBody(EVar { v }) => match self.var_index(v.as_ref()) {
                Some(idx) => {
                    GuardFormula::Prop(mettail_prattail::guard_formula::prop_var(&idx.to_string()))
                },
                None => self.atom_for(whole, GuardAtomKind::Uncovered),
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
            | ExprInstance::EMethodBody(_) => self.atom_for(whole, GuardAtomKind::Uncovered),

            // ── Collections in formula position. ─────────────────────────────────────────
            ExprInstance::EListBody(_)
            | ExprInstance::ESetBody(_)
            | ExprInstance::EMapBody(_)
            | ExprInstance::ETupleBody(_) => {
                self.atom_for(whole, GuardAtomKind::StructuralEquality)
            },

            // ── Structures the guard path has never been taught. ─────────────────────────
            ExprInstance::EPathmapBody(_) | ExprInstance::EZipperBody(_) => {
                self.atom_for(whole, GuardAtomKind::Uncovered)
            },
        }
    }

    // ── Comparison position ───────────────────────────────────────────────────────────────

    fn comparison(
        &mut self,
        op: CmpOp,
        left: &Option<Par>,
        right: &Option<Par>,
        whole: &Par,
    ) -> GuardFormula {
        let lhs = self.opt_operand(left.as_ref());
        let rhs = self.opt_operand(right.as_ref());
        match (lhs, rhs) {
            (Operand::Int(a), Operand::Int(b)) => self.linear(op, &a, &b, whole),
            (Operand::Int(a), Operand::Var(idx)) => {
                self.linear(op, &a, &LinearForm::var(idx), whole)
            },
            (Operand::Var(idx), Operand::Int(b)) => {
                self.linear(op, &LinearForm::var(idx), &b, whole)
            },

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
                None => self.atom_for(whole, GuardAtomKind::Uncovered),
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
                self.atom_for(whole, GuardAtomKind::StructuralEquality)
            },
            (Operand::NonLinear, _) | (_, Operand::NonLinear) => {
                self.atom_for(whole, GuardAtomKind::NonLinear)
            },
            _ => self.atom_for(whole, GuardAtomKind::Uncovered),
        }
    }

    fn linear(
        &mut self,
        op: CmpOp,
        left: &LinearForm,
        right: &LinearForm,
        whole: &Par,
    ) -> GuardFormula {
        match left.compare(op, right) {
            Some(pred) => GuardFormula::Linear(pred),
            // Coefficient overflow while normalizing. Wrapping would encode a DIFFERENT
            // constraint, so the encoder refuses.
            None => self.atom_for(whole, GuardAtomKind::NonLinear),
        }
    }

    fn prop_compare(&mut self, op: CmpOp, idx: usize, literal: bool) -> GuardFormula {
        let atom = GuardFormula::Prop(mettail_prattail::guard_formula::prop_var(&idx.to_string()));
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

    /// Record an opaque atom, keeping the fragment it stands for so a caller can delegate it.
    fn atom_for(&mut self, fragment: &Par, kind: GuardAtomKind) -> GuardFormula {
        let id = self.opaque.len() as u32;
        self.opaque.push(fragment.clone());
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

/// The single [`Expr`] a `Par` consists of, when it consists of exactly one and nothing else.
///
/// `None` for a `Par` carrying any process-level slot: such a `Par` is not an expression, and
/// `rho_pure_eval` agrees — it preserves those slots verbatim and its `extract_bool` then
/// refuses the result.
fn sole_expr_of(par: &Par) -> Option<&Expr> {
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

// ══════════════════════════════════════════════════════════════════════════════════════════════
// ★ THE RUN-TIME LEG — the COMM-time `where`-guard decision, decided by Dovetail/SFT
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ **The `where`-guard decider for a mettail-constructed runtime.**
///
/// # The rule
///
/// > *If it is in a `where` clause, it is a semantic predicate. All semantic predicates are
/// > evaluated by Dovetail/SFT — at compile time where they can be statically evaluated, at run
/// > time otherwise. If it is in an `if` condition, it is evaluated by the Rholang interpreter.*
///
/// The compile-time half is [`crate::guard_discharge::classify`]. This is the run-time half: the
/// guards that survive lowering because they are payload-dependent, decided by the substrate at
/// the moment the payload arrives.
///
/// # Where this sits, and why it is a *matcher*
///
/// A `where` guard is never decided by the reducer. `Reduce::eval_receive` only *substitutes* it
/// (at depth 1) and hangs it on the [`TaggedContinuation`] it hands to `consume`; the decision
/// happens later, inside the tuple space, at
/// `rspace++`'s `space_matcher.rs` → [`Match::check_commit`]. And `check_commit` is a method on
/// the `Match` **trait object that `RSpace::create` takes as a parameter** — so *whoever
/// constructs the RSpace chooses the guard decider*. mettail constructs its own
/// ([`crate::run`], [`crate::step`]), which is the whole reason this can be done without a line
/// of f1r3node change.
///
/// ```text
///   eval_receive ── substitute ──▶ TaggedContinuation{ condition } ──▶ consume
///                                                                        │
///                             RSpace<…, Arc<Box<dyn Match<…>>>> ─────────┘
///                                        │
///                                        ├─ Matcher                (f1r3node: rho_pure_eval)
///                                        └─ SubstrateGuardMatcher  (HERE:  Dovetail/SFT)
/// ```
///
/// # What is *not* changed
///
/// * [`Match::get`] delegates **verbatim** to f1r3node's [`Matcher`]. Spatial matching is
///   untouched — the rule is about `where`, not about patterns — and delegating rather than
///   reimplementing is what makes that structural rather than aspirational.
/// * The **selection strategy** is untouched. This swaps the guard *predicate*; the candidate
///   pool order and the lexicographic search that walks it live in `rspace++` and are not
///   reached from here.
/// * **Replay determinism is structural.** `RSpace::create_with_replay` takes ONE
///   `Arc<Box<dyn Match<…>>>` and hands the same object to both the play and the replay space,
///   so they cannot use different deciders; and both reach `check_commit` through the same code
///   (play via `extract_first_match` → `extract_guarded_data_candidates`; replay directly and
///   through its own `extract_first_match`).
///
/// # The production node is unaffected
///
/// f1r3node's three production `RSpace::create*` sites are untouched and keep deciding guards
/// with `rho_pure_eval`. This type is reachable only from a runtime **mettail** constructed.
///
/// # Cost
///
/// `check_commit` runs per candidate commit, so the common case has to be free — and it is: a
/// continuation with no guard (every unguarded receive, and every receive whose guard compile-time
/// discharge removed) returns on the first line, before any substitution or encoding. A guarded
/// receive pays one substitution pass over the guard (linear in its size — see
/// [`substitute_bound_pars`]), one encoding pass, and one `rho_pure_eval` call per fragment the
/// substrate has no procedure for. `Matcher` pays one `rho_pure_eval` call over the whole guard
/// for the same work, so the two are the same order; the substrate's advantage is that the
/// fragments it decides itself never reach an evaluator at all.
#[derive(Clone, Default)]
pub struct SubstrateGuardMatcher {
    /// f1r3node's matcher, held rather than reimplemented: [`Match::get`] is its, verbatim.
    spatial: Matcher,
}

impl SubstrateGuardMatcher {
    /// The decider, ready to be handed to `RSpace::create`.
    pub const fn new() -> Self {
        SubstrateGuardMatcher { spatial: Matcher }
    }
}

impl Match<BindPattern, ListParWithRandom, TaggedContinuation> for SubstrateGuardMatcher {
    /// Spatial matching, **verbatim** f1r3node's. Not a second matcher.
    fn get(&self, pattern: &BindPattern, data: &ListParWithRandom) -> Option<ListParWithRandom> {
        self.spatial.get(pattern, data)
    }

    /// The cross-channel `where`-clause guard, decided by the substrate.
    ///
    /// The bound variables of every bind are concatenated in receive-bind order — exactly as
    /// [`Matcher::check_commit`] does, because that order *is* the de Bruijn numbering the
    /// normalizer assigned — and the guard is then decided by
    /// [`substrate_guard_passes`].
    ///
    /// The two short-circuits ahead of it are f1r3node's own, reproduced arm for arm: a
    /// continuation with no guard, and a guard that is the empty `Par`, both commit. Reproducing
    /// them (rather than letting the substrate answer `True` for an empty formula) keeps the
    /// discharged form — `condition: None` — meaning exactly what it meant before.
    fn check_commit(&self, k: &TaggedContinuation, matched: &[&ListParWithRandom]) -> bool {
        let Some(guard) = k.guard.as_ref() else {
            return true;
        };
        if guard == &Par::default() {
            return true;
        }
        let mut combined: Vec<Par> = Vec::with_capacity(matched.iter().map(|m| m.pars.len()).sum());
        for m in matched {
            combined.extend_from_slice(&m.pars);
        }
        substrate_guard_passes(guard, &combined)
    }
}

/// ★ **The substrate's COMM-time answer for a lowered guard**: does this guard pass for *these*
/// bindings?
///
/// `bound_pars` is the concatenation, in receive-bind order, of every bind's matched data — so
/// `BoundVar(k)` reads `bound_pars[bound_pars.len() - 1 - k]`, which is exactly what
/// `rho_pure_eval::Env::get` computes for the environment `guard_passes` builds by `put`ting
/// them in that same order.
///
/// [`Sat3::DontKnow`] is resolved by [`dont_know_policy`], which selects
/// [`DontKnowPolicy::FailClosedBlock`]: the COMM does not fire, the datum stays resting and
/// observable, and the continuation stays installed. "Fire iff proved" — see that function for
/// why the two failure modes are not symmetric.
pub fn substrate_guard_passes(condition: &Par, bound_pars: &[Par]) -> bool {
    match substrate_guard_verdict(condition, bound_pars) {
        Sat3::Sat => true,
        Sat3::Unsat => false,
        // The policy point's answer, spelled out at the site so a future change to
        // `dont_know_policy` is visible here rather than silent.
        Sat3::DontKnow => match dont_know_policy(GuardSiteKind::ReceiveWhere) {
            DontKnowPolicy::FailClosedBlock => false,
            DontKnowPolicy::FailOpenFire => true,
        },
    }
}

/// [`substrate_guard_passes`] before the policy point: the raw three-valued verdict.
///
/// # ★ SUBSTITUTE FIRST — and why that is a soundness requirement, not a preference
///
/// The obvious construction is to encode the guard with its `BoundVar`s intact and supply their
/// values as a [`GuardAssignment`]. It is **disqualified**: with a non-empty assignment the
/// ground leg evaluates `Σ aᵢ·xᵢ`, and before 2026-07-26 it did so with unchecked `i64` —
/// panicking in debug, wrapping in release. `Match::check_commit` is contractually total, so a
/// path that can panic cannot carry a run-time guard decision, and a path that can *wrap*
/// silently answers the wrong question about which COMMs fire. (That defect is now fixed at
/// source — see [`mettail_prattail::presburger::LinearConstraint::evaluate_checked`] — but the
/// construction below is preferred on its own merits, measured against the real
/// `Matcher::check_commit` over a differential corpus.)
///
/// Substituting first puts every operand in **ground** position, where the encoder folds it
/// through `LinearForm::{add,sub,negate,scale}` and `i64::checked_{div,rem}` — all checked, all
/// degrading to `Operand::NonLinear` ⇒ an opaque atom ⇒ delegation ⇒ `DontKnow` ⇒ fail-closed.
/// That is the same answer `rho_pure_eval` reaches by the same mechanism, since it maps
/// `EvalError::ArithmeticOverflow` to guard-fail. It is also exactly what the surface run-time
/// leg does (`mettail_languages::rhocalc::guard_substrate::eval_guard_disposition_via_substrate`
/// is handed an already-substituted guard), so the two front ends' run-time legs are the same
/// shape as well as the same decider.
///
/// # The three steps, and what each is protecting
///
/// | step | rule | what it protects |
/// |---|---|---|
/// | 1 | a binder the substitution could not reach ⇒ `DontKnow` | the substrate never reads an unbound slot; a `FreeVar` (a match-frame slot, which `rho_pure_eval` rejects outright) is refused here too |
/// | 2 | an opaque fragment the structural core cannot decide ⇒ `DontKnow` | ★ the firing direction — see below |
/// | 3 | the substrate decides what is left | the whole point |
///
/// ## ★ Step 2 is what keeps the leg sound in the FIRING direction
///
/// [`ground_verdict_with`]'s connectives are left-strict *and short-circuiting*: `⊤ ∨ u` is
/// `Sat`, and `GuardFormula::or` even applies that collapse at construction time. But
/// `rho_pure_eval` is strict in **both** operands and maps any error to guard-fail, so on
/// `true or (6 / 0 > 1)` it answers *false* while a short-circuiting substrate would answer
/// *true* — a COMM firing where the reducer rests. That is not fail-closed and it is not
/// acceptable, so this function resolves **every** fragment the encoder set aside — including
/// the ones a constructor-time collapse dropped out of the formula, which is why the sweep is
/// over `encoding.opaque` rather than over `formula.atoms()` — and refuses the whole guard if
/// any of them is undecided.
///
/// The refusal costs nothing that was ever gained: an undecided fragment sits at a position
/// `rho_pure_eval` *does* evaluate (the encoder only sets fragments aside at operand and formula
/// positions, never inside a collection literal or a `matches` pattern), so an undecided
/// fragment implies `rho_pure_eval` errors on the whole guard, which is guard-fail. Step 2
/// therefore converts a firing-direction disagreement into an *agreement*.
///
/// ## Why the delegated fragments may be decided with an EMPTY environment
///
/// [`crate::guard_discharge::machine_verdict`] evaluates with an empty `Env`. That is exact
/// here, and not an approximation, because substitution has already performed precisely the
/// lookups `rho_pure_eval` would have performed: every position it evaluates has been
/// substituted, and every position it does *not* evaluate — a collection's interior, a `matches`
/// pattern, a process-level slot — has been left verbatim, so it is compared or matched in the
/// same unevaluated form on both sides. Step 1 has already refused anything left over.
///
/// ## The bounded-domain caveat does not apply at run time
///
/// `evaluate_presburger_checked` consults `SubstrateConfig::bit_width` only in its `Exists` arm,
/// and a substituted guard is quantifier-free. So the fence that the compile-time leg needs —
/// `classify`'s concrete-semantics leg, which exists because "valid over `2^w`" does not imply
/// "valid over `ℤ`" — has nothing to fence here: the ground answers are answers about `ℤ`.
pub fn substrate_guard_verdict(condition: &Par, bound_pars: &[Par]) -> Sat3 {
    let substituted = substitute_bound_pars(condition, bound_pars);
    let encoding = encode_par_guard(&substituted);

    // ── 1. A binder the substitution could not reach. ─────────────────────────────────────
    match encoding.vars.is_empty() {
        true => {},
        // `bound$k` with `k` past the arrived bindings, or `free$i` — a match-frame slot, which
        // `rho_pure_eval::resolve_var` rejects with `UnboundVariable`. Neither is answerable.
        false => return Sat3::DontKnow,
    }

    // ── 2. Every fragment the substrate has no procedure for, decided by the structural core.
    let mut resolved: Vec<Sat3> = Vec::with_capacity(encoding.opaque.len());
    for fragment in &encoding.opaque {
        match crate::guard_discharge::machine_verdict(fragment) {
            Some(true) => resolved.push(Sat3::Sat),
            Some(false) => resolved.push(Sat3::Unsat),
            None => return Sat3::DontKnow,
        }
    }

    // ── 3. The substrate decides. ─────────────────────────────────────────────────────────
    ground_verdict_with(
        &encoding.formula,
        &GuardAssignment::with_len(encoding.vars.len()),
        &encoding.vars,
        CONSENSUS_SUBSTRATE_CONFIG,
        &mut |atom| {
            resolved
                .get(atom.id as usize)
                .copied()
                .unwrap_or(Sat3::DontKnow)
        },
    )
}

/// Replace every bound-variable reference in `par` by the value bound to it, **exactly where
/// `rho_pure_eval::eval_with` would have resolved one**.
///
/// # The correspondence this function must maintain
///
/// `rho_pure_eval` resolves a variable only at a position it evaluates. Substituting anywhere
/// else would silently change the guard's meaning:
///
/// | position | `rho_pure_eval` | here |
/// |---|---|---|
/// | operands of the connectives, comparisons and arithmetic | evaluated (both, strictly) | substituted |
/// | the **target** of `matches` | evaluated | substituted |
/// | the **pattern** of `matches` | verbatim — its free variables are *binders* | verbatim |
/// | a collection literal's interior | verbatim — "already values when the `Par` was constructed" | verbatim |
/// | process-level slots (`sends`, `receives`, `news`, …) | preserved unchanged | verbatim |
/// | the operands of an unsupported expression (`EMethodBody`, `EPercentPercentBody`, …) | never reached — the arm errors first | verbatim |
///
/// The middle rows are the load-bearing ones. `[x] == [5]` with `x` bound to `5` is **false**
/// for `rho_pure_eval`: `EListBody` passes through unevaluated, so it compares `[BoundVar(0)]`
/// against `[5]`. A substitution that descended into the list would make it *true* — a COMM
/// firing where the reducer rests.
///
/// The substituted value is **not** re-descended into. A payload is a closed value from the
/// tuple space; any `BoundVar` inside it belongs to *its own* binders (a `for` it contains, say),
/// and rewriting those would be capture, not substitution.
///
/// A `BoundVar(k)` with `k` outside the arrived bindings is left in place, where the encoder
/// interns it as a variable and step 1 of [`substrate_guard_verdict`] refuses the guard.
///
/// Public because it is the *whole* semantic content of "substitute first": a differential that
/// wants to compare the substrate leg against `rho_pure_eval` needs to be able to build the same
/// substituted guard, and a reader auditing the correspondence table above needs to be able to
/// call it. The result is an internal artifact — its `locally_free` bitsets are the pre-
/// substitution ones — and is never emitted into an artifact or a tuple space.
pub fn substitute_bound_pars(par: &Par, bindings: &[Par]) -> Par {
    match bound_var_reference(par).and_then(|index| binding_for(index, bindings)) {
        Some(value) => value.clone(),
        None => match par.exprs.is_empty() {
            true => par.clone(),
            false => {
                let mut exprs = Vec::with_capacity(par.exprs.len());
                for expr in &par.exprs {
                    exprs.push(substitute_expr(expr, bindings));
                }
                // Field by field rather than `..par.clone()`: the struct-update form would deep
                // clone `par.exprs` — the whole expression subtree — only to drop it for the
                // rebuilt `exprs`, once per recursion level, which is quadratic in the guard's
                // size on a path the tuple space walks per candidate commit. The process-level
                // slots are cloned because `rho_pure_eval` preserves them verbatim; on a guard
                // they are empty.
                Par {
                    exprs,
                    sends: par.sends.clone(),
                    receives: par.receives.clone(),
                    news: par.news.clone(),
                    matches: par.matches.clone(),
                    unforgeables: par.unforgeables.clone(),
                    bundles: par.bundles.clone(),
                    connectives: par.connectives.clone(),
                    conditionals: par.conditionals.clone(),
                    locally_free: par.locally_free.clone(),
                    connective_used: par.connective_used,
                }
            },
        },
    }
}

/// [`substitute_bound_pars`] through an optional operand, preserving its absence.
fn substitute_opt_par(par: &Option<Par>, bindings: &[Par]) -> Option<Par> {
    par.as_ref().map(|p| substitute_bound_pars(p, bindings))
}

/// [`substitute_bound_pars`] one expression deep.
///
/// There is no `_` arm: a new `rhoapi` constructor is a compile error here rather than a silently
/// unsubstituted operand, exactly as in [`ParEncoder::expr_formula`].
fn substitute_expr(expr: &Expr, bindings: &[Par]) -> Expr {
    let Some(instance) = expr.expr_instance.as_ref() else {
        return expr.clone();
    };
    let substituted = match instance {
        // ── Positions `rho_pure_eval` evaluates: the connectives … ───────────────────────────
        ExprInstance::EAndBody(EAnd { p1, p2 }) => ExprInstance::EAndBody(EAnd {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::EOrBody(EOr { p1, p2 }) => ExprInstance::EOrBody(EOr {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::ENotBody(ENot { p }) => {
            ExprInstance::ENotBody(ENot { p: substitute_opt_par(p, bindings) })
        },

        // ── … the comparisons … ──────────────────────────────────────────────────────────────
        ExprInstance::EEqBody(EEq { p1, p2 }) => ExprInstance::EEqBody(EEq {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::ENeqBody(ENeq { p1, p2 }) => ExprInstance::ENeqBody(ENeq {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::ELtBody(ELt { p1, p2 }) => ExprInstance::ELtBody(ELt {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::ELteBody(ELte { p1, p2 }) => ExprInstance::ELteBody(ELte {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::EGtBody(EGt { p1, p2 }) => ExprInstance::EGtBody(EGt {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::EGteBody(EGte { p1, p2 }) => ExprInstance::EGteBody(EGte {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),

        // ── … and the arithmetic. ────────────────────────────────────────────────────────────
        ExprInstance::EPlusBody(EPlus { p1, p2 }) => ExprInstance::EPlusBody(EPlus {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::EMinusBody(EMinus { p1, p2 }) => ExprInstance::EMinusBody(EMinus {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::EMultBody(EMult { p1, p2 }) => ExprInstance::EMultBody(EMult {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::EDivBody(EDiv { p1, p2 }) => ExprInstance::EDivBody(EDiv {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::EModBody(EMod { p1, p2 }) => ExprInstance::EModBody(EMod {
            p1: substitute_opt_par(p1, bindings),
            p2: substitute_opt_par(p2, bindings),
        }),
        ExprInstance::ENegBody(ENeg { p }) => {
            ExprInstance::ENegBody(ENeg { p: substitute_opt_par(p, bindings) })
        },

        // ── ★ `matches`: the TARGET is evaluated, the PATTERN is not. ────────────────────────
        //
        // A pattern's free variables are BINDERS. `rho_pure_eval` hands the pattern to the
        // spatial oracle verbatim precisely because evaluating them would raise
        // `UnboundVariable` instead of matching, and `eval_receive` has already given the
        // pattern the depth-1 substitution the reducer's `combine_matches` would have.
        ExprInstance::EMatchesBody(EMatches { target, pattern }) => {
            ExprInstance::EMatchesBody(EMatches {
                target: substitute_opt_par(target, bindings),
                pattern: pattern.clone(),
            })
        },

        // ── A bare variable that is not a whole `Par` by itself. ─────────────────────────────
        //
        // `bound_var_reference` handles the ordinary case at `Par` level, where the reference IS
        // the operand. Reaching here means the `Par` holds other exprs beside this one, which
        // `rho_pure_eval` concatenates rather than reduces to a value — `extract_bool` then
        // refuses it. Left verbatim: the encoder makes the whole `Par` an opaque atom and the
        // delegation reproduces that refusal.
        ExprInstance::EVarBody(_) => return expr.clone(),

        // ── Positions `rho_pure_eval` does NOT evaluate. ─────────────────────────────────────
        //
        // Collections pass through unchanged ("their elements were already values when the `Par`
        // was constructed"), so a `BoundVar` inside one is compared as a variable, never as its
        // value. Ground literals have nothing to substitute. The remaining constructors are
        // `UnsupportedExpression` stubs that error before touching an operand.
        ExprInstance::EListBody(_)
        | ExprInstance::ESetBody(_)
        | ExprInstance::EMapBody(_)
        | ExprInstance::ETupleBody(_)
        | ExprInstance::GBool(_)
        | ExprInstance::GInt(_)
        | ExprInstance::GString(_)
        | ExprInstance::GUri(_)
        | ExprInstance::GByteArray(_)
        | ExprInstance::GDouble(_)
        | ExprInstance::GBigInt(_)
        | ExprInstance::GBigRat(_)
        | ExprInstance::GFixedPoint(_)
        | ExprInstance::EPercentPercentBody(_)
        | ExprInstance::EPlusPlusBody(_)
        | ExprInstance::EMinusMinusBody(_)
        | ExprInstance::EMethodBody(_)
        | ExprInstance::EPathmapBody(_)
        | ExprInstance::EZipperBody(_) => return expr.clone(),
    };
    Expr { expr_instance: Some(substituted) }
}

/// The de Bruijn index of `par`, when `par` **is** a bound-variable reference and nothing else.
fn bound_var_reference(par: &Par) -> Option<i32> {
    match sole_expr_of(par)?.expr_instance.as_ref()? {
        ExprInstance::EVarBody(EVar { v }) => match v.as_ref()?.var_instance.as_ref()? {
            VarInstance::BoundVar(index) => Some(*index),
            // A `FreeVar` is a match-frame slot and a `Wildcard` binds without being readable.
            // Neither has a value in `bound_pars`; both are left for step 1 to refuse.
            VarInstance::FreeVar(_) | VarInstance::Wildcard(_) => None,
        },
        _ => None,
    }
}

/// The value bound to de Bruijn index `index`, under the same indexing `rho_pure_eval::Env::get`
/// uses: the most recently pushed binding is index `0`.
///
/// `guard_passes` builds its environment by `put`ting `bound_pars` in order, so `Env::get(k)`
/// reads `env_map[level - k - 1]` with `level == bound_pars.len()`.
fn binding_for(index: i32, bindings: &[Par]) -> Option<&Par> {
    let depth = usize::try_from(index).ok()?;
    bindings.get(bindings.len().checked_sub(1)?.checked_sub(depth)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::rhoapi::expr::ExprInstance as EI;

    fn expr(instance: EI) -> Par {
        Par {
            exprs: vec![Expr { expr_instance: Some(instance) }],
            ..Default::default()
        }
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
            v: Some(Var {
                var_instance: Some(VarInstance::BoundVar(i)),
            }),
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
        let not = expr(EI::ENotBody(ENot { p: Some(gbool(false)) }));
        assert_eq!(substrate_verdict(&not), Some(true));
    }

    /// `a implies b` has no `rhoapi` node — the lowering emits `EOr(ENot a, b)`. The encoder
    /// therefore needs no `implies` arm, and material implication still settles.
    #[test]
    fn material_implication_arrives_already_decomposed_and_settles() {
        let not_antecedent = expr(EI::ENotBody(ENot { p: Some(gbool(false)) }));
        let implication =
            binary(|p1, p2| EI::EOrBody(EOr { p1, p2 }), not_antecedent, gbool(false));
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
        let process = Par {
            sends: vec![Default::default()],
            ..Default::default()
        };
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
        assert_eq!(encode_par_guard(&guard).formula.atoms()[0].kind, GuardAtomKind::Spatial);
    }

    #[test]
    fn a_wildcard_is_not_a_readable_variable() {
        let guard = eq(
            expr(EI::EVarBody(EVar {
                v: Some(Var {
                    var_instance: Some(VarInstance::Wildcard(Default::default())),
                }),
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
        assert_eq!(encode_par_guard(&guard).formula.atoms()[0].kind, GuardAtomKind::NonLinear);
    }

    #[test]
    fn distinct_de_bruijn_indices_get_distinct_substrate_variables() {
        let guard = lt(bound(0), bound(1));
        let encoding = encode_par_guard(&guard);
        assert_eq!(encoding.vars.len(), 2);
    }

    // ══════════════════════════════════════════════════════════════════════════════════════════
    // ★ THE RUN-TIME LEG, against the REAL reducer decision
    // ══════════════════════════════════════════════════════════════════════════════════════════
    //
    // Every row below is driven through BOTH `Match::check_commit` implementations — f1r3node's
    // `Matcher` (rho_pure_eval) and `SubstrateGuardMatcher` — and required to agree. A row that
    // fails in the direction `substrate = true, reducer = false` is the serious one: the COMM
    // fires where the reducer rests, which is not fail-closed.

    fn or(a: Par, b: Par) -> Par {
        binary(|p1, p2| EI::EOrBody(EOr { p1, p2 }), a, b)
    }

    fn and(a: Par, b: Par) -> Par {
        binary(|p1, p2| EI::EAndBody(EAnd { p1, p2 }), a, b)
    }

    fn gt(a: Par, b: Par) -> Par {
        binary(|p1, p2| EI::EGtBody(EGt { p1, p2 }), a, b)
    }

    fn divide(a: Par, b: Par) -> Par {
        binary(|p1, p2| EI::EDivBody(EDiv { p1, p2 }), a, b)
    }

    fn times(a: Par, b: Par) -> Par {
        binary(|p1, p2| EI::EMultBody(EMult { p1, p2 }), a, b)
    }

    fn negate(a: Par) -> Par {
        expr(EI::ENotBody(ENot { p: Some(a) }))
    }

    /// `a implies b`, in the form the lowering emits it: `EOr(ENot a, b)`.
    fn implies(a: Par, b: Par) -> Par {
        or(negate(a), b)
    }

    fn list(items: Vec<Par>) -> Par {
        expr(EI::EListBody(models::rhoapi::EList {
            ps: items,
            locally_free: Vec::new(),
            connective_used: false,
            remainder: None,
        }))
    }

    fn matches_expr(target: Par, pattern: Par) -> Par {
        expr(EI::EMatchesBody(EMatches {
            target: Some(target),
            pattern: Some(pattern),
        }))
    }

    /// `@"c"!(n)` — a process-shaped value, usable as a payload or a `matches` operand.
    fn send(channel: &str, payload: i64) -> Par {
        Par::default().with_sends(vec![models::rhoapi::Send {
            chan: Some(gstring(channel)),
            data: vec![gint(payload)],
            persistent: false,
            locally_free: Vec::new(),
            connective_used: false,
        }])
    }

    /// The reducer's verdict, through f1r3node's own entry point.
    fn reducer_verdict(guard: &Par, binds: &[&[Par]]) -> bool {
        drive_check_commit(&Matcher, guard, binds)
    }

    /// The substrate's verdict, through the same entry point.
    fn substrate_run_time_verdict(guard: &Par, binds: &[&[Par]]) -> bool {
        drive_check_commit(&SubstrateGuardMatcher::new(), guard, binds)
    }

    /// One `ListParWithRandom` per receive-bind, in bind order, exactly as the matcher
    /// coordinator assembles them.
    fn drive_check_commit(
        matcher: &dyn Match<BindPattern, ListParWithRandom, TaggedContinuation>,
        guard: &Par,
        binds: &[&[Par]],
    ) -> bool {
        let owned: Vec<ListParWithRandom> = binds
            .iter()
            .map(|pars| ListParWithRandom {
                pars: pars.to_vec(),
                random_state: Vec::new(),
            })
            .collect();
        let borrowed: Vec<&ListParWithRandom> = owned.iter().collect();
        let continuation = TaggedContinuation {
            guard: Some(guard.clone()),
            tagged_cont: None,
        };
        matcher.check_commit(&continuation, &borrowed)
    }

    /// Every row: `(label, guard, per-bind payloads)`.
    type GuardRow = (&'static str, Par, Vec<Vec<Par>>);

    fn run_time_corpus() -> Vec<GuardRow> {
        vec![
            // ── ordinary payload-dependent rows ───────────────────────────────────────────
            ("x > 0 [5]", gt(bound(0), gint(0)), vec![vec![gint(5)]]),
            ("x > 0 [-3]", gt(bound(0), gint(0)), vec![vec![gint(-3)]]),
            ("x < 100 [40000]", lt(bound(0), gint(100)), vec![vec![gint(40_000)]]),
            ("x > 40000 [50000]", gt(bound(0), gint(40_000)), vec![vec![gint(50_000)]]),
            ("x + 1 > 0 [5]", gt(plus(bound(0), gint(1)), gint(0)), vec![vec![gint(5)]]),
            ("x / 2 > 1 [6]", gt(divide(bound(0), gint(2)), gint(1)), vec![vec![gint(6)]]),
            ("x [true]", bound(0), vec![vec![gbool(true)]]),
            ("x [false]", bound(0), vec![vec![gbool(false)]]),
            ("not (x > 0) [-1]", negate(gt(bound(0), gint(0))), vec![vec![gint(-1)]]),
            ("x > \"a\" [\"b\"]", gt(bound(0), gstring("a")), vec![vec![gstring("b")]]),
            ("x > \"c\" [\"b\"]", gt(bound(0), gstring("c")), vec![vec![gstring("b")]]),
            // ── error-shaped rows: `rho_pure_eval` raises, so the guard must not pass ──────
            (
                "x / 0 > 1 [6] DIV0",
                gt(divide(bound(0), gint(0)), gint(1)),
                vec![vec![gint(6)]],
            ),
            (
                "x + 1 > 0 [i64::MAX] OVERFLOW",
                gt(plus(bound(0), gint(1)), gint(0)),
                vec![vec![gint(i64::MAX)]],
            ),
            (
                "2 * x > 0 [i64::MAX] OVERFLOW",
                gt(times(gint(2), bound(0)), gint(0)),
                vec![vec![gint(i64::MAX)]],
            ),
            ("x [\"s\"] NON-BOOLEAN", bound(0), vec![vec![gstring("s")]]),
            ("x > 0 [\"s\"] SORT MISMATCH", gt(bound(0), gint(0)), vec![vec![gstring("s")]]),
            ("x > 0 [@\"c\"!(1)] PROCESS", gt(bound(0), gint(0)), vec![vec![send("c", 1)]]),
            // ── ★ an undecidable operand in a SHORT-CIRCUITED position ────────────────────
            (
                "true or (x / 0 > 1) [6]",
                or(gbool(true), gt(divide(bound(0), gint(0)), gint(1))),
                vec![vec![gint(6)]],
            ),
            (
                "(x > 0) or (x / 0 > 1) [6]",
                or(gt(bound(0), gint(0)), gt(divide(bound(0), gint(0)), gint(1))),
                vec![vec![gint(6)]],
            ),
            (
                "true or (2 * x > 0) [i64::MAX]",
                or(gbool(true), gt(times(gint(2), bound(0)), gint(0))),
                vec![vec![gint(i64::MAX)]],
            ),
            (
                "false implies (x / 0 > 1) [6]",
                implies(gbool(false), gt(divide(bound(0), gint(0)), gint(1))),
                vec![vec![gint(6)]],
            ),
            (
                "(x matches @\"c\"!(1)) or (x > 9) [@\"c\"!(1)]",
                or(matches_expr(bound(0), send("c", 1)), gt(bound(0), gint(9))),
                vec![vec![send("c", 1)]],
            ),
            // ── the dual: an undecidable operand behind a decided-FALSE `and` ─────────────
            (
                "false and (x / 0 > 1) [6]",
                and(gbool(false), gt(divide(bound(0), gint(0)), gint(1))),
                vec![vec![gint(6)]],
            ),
            (
                "(x > 0) and (x / 0 > 1) [6]",
                and(gt(bound(0), gint(0)), gt(divide(bound(0), gint(0)), gint(1))),
                vec![vec![gint(6)]],
            ),
            // ── ★ positions `rho_pure_eval` does not evaluate ─────────────────────────────
            (
                "[x] == [5] [5]",
                eq(list(vec![bound(0)]), list(vec![gint(5)])),
                vec![vec![gint(5)]],
            ),
            (
                "[x] == [6] [5]",
                eq(list(vec![bound(0)]), list(vec![gint(6)])),
                vec![vec![gint(5)]],
            ),
            (
                "[1,2] == [1,2]",
                eq(list(vec![gint(1), gint(2)]), list(vec![gint(1), gint(2)])),
                vec![vec![gint(5)]],
            ),
            (
                "x matches @\"c\"!(1) [@\"c\"!(1)]",
                matches_expr(bound(0), send("c", 1)),
                vec![vec![send("c", 1)]],
            ),
            (
                "x matches @\"c\"!(2) [@\"c\"!(1)]",
                matches_expr(bound(0), send("c", 2)),
                vec![vec![send("c", 1)]],
            ),
            // ── cross-bind (`&`-join) rows: two binds, de Bruijn in bind order ────────────
            (
                "x - y > 0 [9 | 4]",
                gt(minus_expr(bound(1), bound(0)), gint(0)),
                vec![vec![gint(9)], vec![gint(4)]],
            ),
            (
                "x - y > 0 [4 | 9]",
                gt(minus_expr(bound(1), bound(0)), gint(0)),
                vec![vec![gint(4)], vec![gint(9)]],
            ),
            ("x == y [2 | 2]", eq(bound(1), bound(0)), vec![vec![gint(2)], vec![gint(2)]]),
            (
                "x > 1 and y > 1 [2 | 0]",
                and(gt(bound(1), gint(1)), gt(bound(0), gint(1))),
                vec![vec![gint(2)], vec![gint(0)]],
            ),
            // ── a binder the substitution cannot reach ────────────────────────────────────
            ("bound$3 > 0 [5]", gt(bound(3), gint(0)), vec![vec![gint(5)]]),
            ("free$0 > 0 [5]", gt(free(0), gint(0)), vec![vec![gint(5)]]),
            // ── binder-closed rows, for completeness ──────────────────────────────────────
            ("true", gbool(true), vec![vec![]]),
            ("false", gbool(false), vec![vec![]]),
            ("3 > 2", gt(gint(3), gint(2)), vec![vec![]]),
        ]
    }

    fn minus_expr(a: Par, b: Par) -> Par {
        binary(|p1, p2| EI::EMinusBody(EMinus { p1, p2 }), a, b)
    }

    fn free(i: i32) -> Par {
        expr(EI::EVarBody(EVar {
            v: Some(Var {
                var_instance: Some(VarInstance::FreeVar(i)),
            }),
        }))
    }

    /// ★ THE RUN-TIME DIFFERENTIAL: the substrate and the reducer decide every row alike.
    #[test]
    fn the_run_time_leg_agrees_with_the_reducer_on_every_row() {
        let mut disagreements = Vec::new();
        let mut firing_direction = Vec::new();
        for (label, guard, binds) in run_time_corpus() {
            let borrowed: Vec<&[Par]> = binds.iter().map(Vec::as_slice).collect();
            let reducer = reducer_verdict(&guard, &borrowed);
            let substrate = substrate_run_time_verdict(&guard, &borrowed);
            match (reducer, substrate) {
                (r, s) if r == s => {},
                (false, true) => {
                    firing_direction.push(label);
                    disagreements.push(format!("  {label}: reducer=false substrate=true"));
                },
                (r, s) => disagreements.push(format!("  {label}: reducer={r} substrate={s}")),
            }
        }
        assert!(
            firing_direction.is_empty(),
            "★ NOT FAIL-CLOSED — the substrate fires a COMM the reducer rests on, in {} row(s): \
             {firing_direction:?}",
            firing_direction.len()
        );
        assert!(
            disagreements.is_empty(),
            "the run-time guard leg disagrees with the reducer on {} row(s):\n{}",
            disagreements.len(),
            disagreements.join("\n")
        );
    }

    /// ★ THE MEASURED REASON `substrate_guard_verdict` resolves every fragment instead of
    /// letting `ground_verdict_with` short-circuit past it.
    ///
    /// `ground_verdict_with`'s `or` settles from a decided-true LEFT — and `GuardFormula::or`
    /// even applies `⊤ ∨ φ = ⊤` at construction time, so the right operand does not survive into
    /// the formula at all. `rho_pure_eval`'s `bool_binop` is strict in BOTH operands and maps any
    /// error to guard-fail, so on each row below it answers `false`. Without the sweep over
    /// `encoding.opaque` the substrate answers `true`: a COMM firing where the reducer rests.
    #[test]
    fn an_undecidable_operand_blocks_the_comm_even_where_a_short_circuit_would_skip_it() {
        let rows = [
            // division by zero on the right, skipped by a decided-true left …
            (
                "true or (x / 0 > 1) [6]",
                or(gbool(true), gt(divide(bound(0), gint(0)), gint(1))),
                vec![gint(6)],
            ),
            // … arithmetic overflow on the right …
            (
                "true or (2 * x > 0) [i64::MAX]",
                or(gbool(true), gt(times(gint(2), bound(0)), gint(0))),
                vec![gint(i64::MAX)],
            ),
            // … a sort mismatch on the right …
            (
                "true or (x > \"a\") [1]",
                or(gbool(true), gt(bound(0), gstring("a"))),
                vec![gint(1)],
            ),
            // … the same shape reached through `implies`, which lowers to `EOr(ENot a, b)` …
            (
                "false implies (x / 0 > 1) [6]",
                implies(gbool(false), gt(divide(bound(0), gint(0)), gint(1))),
                vec![gint(6)],
            ),
            // … and a decided-true left that is itself a payload-dependent comparison, so the
            // collapse happens in `ground_verdict_with` rather than in `GuardFormula::or`.
            (
                "(x > 0) or (x / 0 > 1) [6]",
                or(gt(bound(0), gint(0)), gt(divide(bound(0), gint(0)), gint(1))),
                vec![gint(6)],
            ),
        ];
        for (label, guard, bindings) in rows {
            assert!(
                !reducer_verdict(&guard, &[&bindings]),
                "precondition: the reducer rests on {label:?}"
            );
            assert!(
                !substrate_guard_passes(&guard, &bindings),
                "★ {label:?} FIRED. `rho_pure_eval` evaluates both operands of `EOr` and maps \
                 the error to guard-fail; a short-circuiting substrate must not overrule it"
            );
        }
    }

    /// ★ Substitution stops exactly where `rho_pure_eval` stops resolving variables.
    ///
    /// `EListBody` passes through `eval_with` unchanged, so `[x] == [5]` compares
    /// `[BoundVar(0)]` against `[5]` and is FALSE even when `x` is bound to `5`. A substitution
    /// that descended into the list would make it true — a COMM firing where the reducer rests.
    #[test]
    fn a_collection_interior_is_not_substituted() {
        let guard = eq(list(vec![bound(0)]), list(vec![gint(5)]));
        let bindings = [gint(5)];
        assert!(!reducer_verdict(&guard, &[&bindings]), "precondition: the reducer rests");
        assert!(!substrate_guard_passes(&guard, &bindings));
        // The substituted guard still holds the variable, verbatim.
        assert_eq!(substitute_bound_pars(&guard, &bindings), guard);
    }

    /// ★ …and a `matches` PATTERN is not substituted either, while its TARGET is.
    ///
    /// A pattern's variables are binders; `rho_pure_eval` hands the pattern to the spatial
    /// oracle verbatim precisely because evaluating them would raise `UnboundVariable`.
    #[test]
    fn a_matches_target_is_substituted_and_its_pattern_is_not() {
        let guard = matches_expr(bound(0), bound(1));
        let bindings = [gint(7), send("c", 1)];
        let substituted = substitute_bound_pars(&guard, &bindings);
        let EI::EMatchesBody(EMatches { target, pattern }) = substituted.exprs[0]
            .expr_instance
            .clone()
            .expect("the substituted guard is still a `matches`")
        else {
            panic!("substitution changed the expression's constructor")
        };
        assert_eq!(target.expect("target"), send("c", 1), "the target IS substituted");
        assert_eq!(pattern.expect("pattern"), bound(1), "the pattern is NOT substituted");
    }

    /// A payload is a closed value; a `BoundVar` inside one belongs to that value's OWN binders,
    /// so substitution must not descend into what it just substituted.
    #[test]
    fn substitution_does_not_descend_into_the_value_it_substituted() {
        // `x` is bound to a term that itself mentions `BoundVar(0)` under its own binder.
        let payload = expr(EI::EListBody(models::rhoapi::EList {
            ps: vec![bound(0)],
            locally_free: Vec::new(),
            connective_used: false,
            remainder: None,
        }));
        let guard = eq(bound(0), list(vec![gint(1)]));
        let substituted = substitute_bound_pars(&guard, &[payload.clone()]);
        let EI::EEqBody(EEq { p1, .. }) = substituted.exprs[0]
            .expr_instance
            .clone()
            .expect("still an equality")
        else {
            panic!("substitution changed the expression's constructor")
        };
        assert_eq!(p1.expect("left operand"), payload, "the payload is spliced in VERBATIM");
    }

    /// The de Bruijn numbering is "most recently pushed is index 0", over the binds
    /// CONCATENATED in receive-bind order — the same indexing `rho_pure_eval::Env::get` computes
    /// for the environment `guard_passes` builds.
    #[test]
    fn de_bruijn_indices_read_the_concatenated_binds_in_receive_bind_order() {
        let guard = minus_expr(bound(1), bound(0));
        let bindings = [gint(9), gint(4)];
        assert_eq!(
            substitute_bound_pars(&guard, &bindings),
            minus_expr(gint(9), gint(4)),
            "BoundVar(1) is the FIRST bind and BoundVar(0) the second"
        );
        // …and the whole guard decides accordingly, on both sides.
        let guard = gt(guard, gint(0));
        assert!(substrate_run_time_verdict(&guard, &[&[gint(9)], &[gint(4)]]));
        assert!(!substrate_run_time_verdict(&guard, &[&[gint(4)], &[gint(9)]]));
        assert!(reducer_verdict(&guard, &[&[gint(9)], &[gint(4)]]));
        assert!(!reducer_verdict(&guard, &[&[gint(4)], &[gint(9)]]));
    }

    /// A binder the substitution cannot reach leaves the guard undecided, which fails closed.
    #[test]
    fn an_unreachable_binder_fails_closed() {
        assert_eq!(
            substrate_guard_verdict(&gt(bound(3), gint(0)), &[gint(5)]),
            Sat3::DontKnow,
            "`BoundVar(3)` is past the arrived bindings"
        );
        assert_eq!(
            substrate_guard_verdict(&gt(free(0), gint(0)), &[gint(5)]),
            Sat3::DontKnow,
            "a `FreeVar` is a match-frame slot; `rho_pure_eval` rejects it too"
        );
        assert!(!substrate_guard_passes(&gt(bound(3), gint(0)), &[gint(5)]));
    }

    /// `check_commit`'s two short-circuits are f1r3node's, reproduced: a continuation with no
    /// guard, and a guard that is the empty `Par`, both commit. The first is what compile-time
    /// discharge relies on — it omits `Receive.condition` entirely.
    #[test]
    fn a_guardless_continuation_and_an_empty_guard_both_commit() {
        let matcher = SubstrateGuardMatcher::new();
        let matched = ListParWithRandom {
            pars: vec![gint(1)],
            random_state: Vec::new(),
        };
        let guardless = TaggedContinuation { guard: None, tagged_cont: None };
        assert!(matcher.check_commit(&guardless, &[&matched]));
        let empty = TaggedContinuation {
            guard: Some(Par::default()),
            tagged_cont: None,
        };
        assert!(matcher.check_commit(&empty, &[&matched]));
        // …byte-for-byte the reducer's own answer.
        assert!(Matcher.check_commit(&guardless, &[&matched]));
        assert!(Matcher.check_commit(&empty, &[&matched]));
    }

    /// `get` is f1r3node's, verbatim: the two matchers return the same spatial match result.
    #[test]
    fn spatial_matching_is_delegated_verbatim() {
        let pattern = BindPattern {
            patterns: vec![free(0)],
            remainder: None,
            free_count: 1,
        };
        let data = ListParWithRandom {
            pars: vec![gint(42)],
            random_state: Vec::new(),
        };
        assert_eq!(SubstrateGuardMatcher::new().get(&pattern, &data), Matcher.get(&pattern, &data));
        let mismatched = BindPattern {
            patterns: vec![gint(1), gint(2)],
            remainder: None,
            free_count: 0,
        };
        assert_eq!(
            SubstrateGuardMatcher::new().get(&mismatched, &data),
            Matcher.get(&mismatched, &data)
        );
    }
}
