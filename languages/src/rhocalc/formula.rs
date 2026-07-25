//! M-1b — the FORMULA reading of a RhoCalc `Proc`.
//!
//! # Why this lives here and not in the lowering
//!
//! §18.1's design is that **a formula is a `Proc` sub-tree that is read as a
//! Rholang PATTERN**. That reading has two consumers:
//!
//! * `rholang-runtime::rhocalc_formula` COMPILES a formula to a `rhoapi::Par`
//!   pattern, which the reducer's spatial matcher then decides;
//! * `crate::rhocalc::receive::eval_guard_bool` DECIDES a formula host-side, on
//!   the fragment for which the generated first-order matcher is a faithful model
//!   of the reducer's.
//!
//! If each consumer classified `Proc` nodes for itself, the two would be free to
//! drift — one could start reading `not φ` as a connective while the other still
//! read it as a term — and a drift like that is invisible until it silently
//! changes which COMMs commit. So the classification is written ONCE, here, in
//! the crate that owns the RhoCalc syntax, and both consumers match on the same
//! [`FormulaShape`]. It is pure syntax: no `rhoapi`, no matcher, no evaluation.
//!
//! # The shapes (§18.1's table, left column)
//!
//! ```text
//!   true                      ⊤   satisfied by every term
//!   false                     ⊥   satisfied by no term
//!   φ and ψ                   ∧   ordinary conjunction — the WHOLE term satisfies both
//!   φ or ψ                    ∨
//!   not φ                     ¬
//!   φ implies ψ               ⇒   (M-0's connective, read at the pattern level)
//!   { φ | ψ }, φ | ψ,
//!   PPar(φ, ψ)                ∗   SEPARATING conjunction — the term SPLITS
//!   anything else             ·   an ordinary term, read as a pattern
//! ```
//!
//! # Totality and the M-2 extension point
//!
//! [`classify`] is an exhaustive match: every `Proc` receives a shape, and the
//! residual [`FormulaShape::Term`] is what makes the compiler downstream total.
//! M-2 (`<K> true`, rule-enabledness) adds ONE variant plus ONE arm here; the
//! `Term` fall-through is untouched, so a shape M-2 does not recognize keeps
//! reading as a plain pattern rather than silently becoming a modality.

use std::sync::Arc;

use super::{Bool, Proc};

/// The formula reading of a `Proc` node.
///
/// Borrowed rather than owned so classification allocates nothing except the
/// `Separation` part list, which borrows its elements.
#[derive(Debug)]
pub enum FormulaShape<'formula> {
    /// `true` — satisfied by every term.
    Verum,
    /// `false` — satisfied by no term.
    Falsum,
    /// `φ and ψ` — ordinary (NON-separating) conjunction: the whole term must
    /// satisfy both conjuncts.
    Conjunction(&'formula Proc, &'formula Proc),
    /// `φ or ψ`.
    Disjunction(&'formula Proc, &'formula Proc),
    /// `not φ`.
    Negation(&'formula Proc),
    /// `φ implies ψ`.
    Implication(&'formula Proc, &'formula Proc),
    /// `{ φ | ψ | … }`, `φ | ψ`, or `PPar(φ, ψ)` — the SEPARATING conjunction:
    /// the term must split into parallel parts, one satisfying each component.
    Separation(Vec<&'formula Proc>),
    /// Any other `Proc`, read as an ordinary Rholang pattern (a concrete term
    /// shape whose free variables are binders).
    Term,
}

/// Assign `formula` its [`FormulaShape`]. Total: every `Proc` gets a shape.
///
/// Recognition is by CONSTRUCTOR, never by spelling, so the classification cannot
/// drift from the grammar as surface syntax evolves.
pub fn classify(formula: &Proc) -> FormulaShape<'_> {
    match formula {
        // `true`/`false` are `CastBool(BoolLit(_))`. Only the two LITERALS are
        // logical constants; any other `Bool` inhabitant is a term and reads as
        // one.
        Proc::CastBool(literal) => match literal.as_ref() {
            Bool::BoolLit(true) => FormulaShape::Verum,
            Bool::BoolLit(false) => FormulaShape::Falsum,
            #[allow(unreachable_patterns)]
            _ => FormulaShape::Term,
        },
        Proc::And(left, right) => FormulaShape::Conjunction(left.as_ref(), right.as_ref()),
        Proc::Or(left, right) => FormulaShape::Disjunction(left.as_ref(), right.as_ref()),
        Proc::Not(inner) => FormulaShape::Negation(inner.as_ref()),
        Proc::Implies(antecedent, consequent) => {
            FormulaShape::Implication(antecedent.as_ref(), consequent.as_ref())
        },
        // The three spellings of the separating conjunction, all ONE shape:
        //   `PPar(φ, ψ)`   the paper's verbatim connective (omnibus :2010)
        //   `{ φ | ψ }`    the idiomatic host spelling — a `PPar` multiset literal
        //   `φ | ψ`        the same, un-braced, before `merge_pp_parallel` folds it
        Proc::SpatialPPar(left, right) => {
            FormulaShape::Separation(vec![left.as_ref(), right.as_ref()])
        },
        Proc::PParInfix(left, right) => {
            FormulaShape::Separation(vec![left.as_ref(), right.as_ref()])
        },
        Proc::PPar(parts) => FormulaShape::Separation(parts.iter_elements().collect()),
        _ => FormulaShape::Term,
    }
}

/// Is `formula` UNSATISFIABLE by construction — is `t matches φ` false for EVERY
/// `t`?
///
/// §18.1 asks for `false` to "fold the whole guard to `GBool(false)` at
/// lowering". This is that judgement, stated completely over the propositional
/// fragment rather than only for the bare literal.
///
/// It is **syntactic, conservative, and mutually recursive** with
/// [`is_statically_true`]. Soundness, arm by arm (writing `⟦φ⟧` for the set of
/// terms satisfying `φ`, and `ALL` for the set of all terms):
///
/// | Arm | Claim | Why |
/// | --- | --- | --- |
/// | `⊥` | `⟦⊥⟧ = ∅` | by definition |
/// | `φ ∧ ψ` | `⟦φ⟧ = ∅ ∨ ⟦ψ⟧ = ∅ ⟹ ⟦φ∧ψ⟧ = ∅` | `⟦φ∧ψ⟧ = ⟦φ⟧ ∩ ⟦ψ⟧` |
/// | `φ ∨ ψ` | `⟦φ⟧ = ∅ ∧ ⟦ψ⟧ = ∅ ⟹ ⟦φ∨ψ⟧ = ∅` | `⟦φ∨ψ⟧ = ⟦φ⟧ ∪ ⟦ψ⟧` |
/// | `¬φ` | `⟦φ⟧ = ALL ⟹ ⟦¬φ⟧ = ∅` | complement |
/// | `φ ⇒ ψ` | `⟦φ⟧ = ALL ∧ ⟦ψ⟧ = ∅ ⟹ ⟦φ⇒ψ⟧ = ∅` | `⟦φ⇒ψ⟧ = ⟦¬φ⟧ ∪ ⟦ψ⟧` |
/// | `φ ∗ ψ` | `⟦φ⟧ = ∅ ∨ ⟦ψ⟧ = ∅ ⟹ ⟦φ∗ψ⟧ = ∅` | a split needs a witness on BOTH sides |
/// | `⊤`, term | not decided | a term pattern's satisfiability is not syntactic |
///
/// Every arm is an implication in the safe direction, so the judgement can only
/// ever be *incomplete*, never *unsound*.
pub fn is_statically_false(formula: &Proc) -> bool {
    match classify(formula) {
        FormulaShape::Falsum => true,
        FormulaShape::Conjunction(left, right) => {
            is_statically_false(left) || is_statically_false(right)
        },
        FormulaShape::Disjunction(left, right) => {
            is_statically_false(left) && is_statically_false(right)
        },
        FormulaShape::Negation(inner) => is_statically_true(inner),
        FormulaShape::Implication(antecedent, consequent) => {
            is_statically_true(antecedent) && is_statically_false(consequent)
        },
        FormulaShape::Separation(parts) => parts.into_iter().any(is_statically_false),
        FormulaShape::Verum | FormulaShape::Term => false,
    }
}

/// Is `formula` VALID by construction — is `t matches φ` true for EVERY `t`?
///
/// The dual of [`is_statically_false`], and used only BY it (to discharge the
/// `¬φ` and `φ ⇒ ψ` arms) and by the host guard evaluator. The lowering-time fold
/// stays ONE-SIDED — a guard is folded to `GBool(false)`, never to `GBool(true)` —
/// so incompleteness here costs at most a missed optimization.
///
/// ⚠ [`FormulaShape::Separation`] answers "not decided" even when every part is
/// valid. `⊤ ∗ ⊤` very likely IS valid (any `P` splits as `P | Nil`), but that
/// depends on how the reducer's `list_match_single_` treats an empty remainder —
/// a matcher detail this crate does not own. Declining costs nothing; guessing
/// could unsoundly fold a guard.
pub fn is_statically_true(formula: &Proc) -> bool {
    match classify(formula) {
        FormulaShape::Verum => true,
        FormulaShape::Conjunction(left, right) => {
            is_statically_true(left) && is_statically_true(right)
        },
        FormulaShape::Disjunction(left, right) => {
            is_statically_true(left) || is_statically_true(right)
        },
        FormulaShape::Negation(inner) => is_statically_false(inner),
        FormulaShape::Implication(antecedent, consequent) => {
            is_statically_false(antecedent) || is_statically_true(consequent)
        },
        FormulaShape::Falsum | FormulaShape::Separation(_) | FormulaShape::Term => false,
    }
}

/// The HOST verdict for `target matches formula`, or `None` when the host
/// declines to decide.
///
/// # The fragment, and why it stops exactly there
///
/// | Shape | Host verdict | Justification |
/// | --- | --- | --- |
/// | `⊤` | `Some(true)` | satisfied by every term, by definition |
/// | `⊥` | `Some(false)` | satisfied by no term, by definition |
/// | `¬φ`, `φ ∧ ψ`, `φ ∨ ψ`, `φ ⇒ ψ` | the propositional combination of the operands' verdicts | the Boolean algebra of sets; no matcher is involved in the COMBINATION, so nothing can diverge there |
/// | a term pattern, MATCHED | `Some(true)` | a host match PROVES a machine match — see below |
/// | a term pattern, NOT matched | **`None`** | a host non-match proves nothing — see below |
/// | `φ ∗ ψ` (separating) | **`None`** | see below |
///
/// ## ★ The term arm is POSITIVE-ONLY, and that is what makes it sound
///
/// The generated first-order matcher and the reducer's spatial matcher are
/// different algorithms over different representations. They are **not**
/// interchangeable — measured, not assumed: for the target `@"a"!([1, 2])` and
/// the pattern `@"a"!([1, v])` the reducer matches and the generated matcher does
/// not, because the generator's collection-literal arms do not treat an element
/// free variable as a binder. So the host may not simply forward
/// `match_pattern(...).is_some()`.
///
/// What IS provable is the one-sided containment:
///
/// ```math
/// \text{match\_pattern}(t, \varphi) = \mathrm{Some}(\sigma)
///     \;\Longrightarrow\;
///     \text{spatial\_match}(⟦t⟧, ⟦\varphi⟧)
/// ```
///
/// *Proof sketch.* A successful host match decomposes `φ` into (i) positions that
/// agreed structurally with `t` and (ii) placeholder positions absorbed into `σ`.
/// The compiled pattern `⟦φ⟧` lowers group (i) with the SAME `lower_proc` that
/// lowered `t` — so those positions are equal `Par`s — and lowers group (ii) to
/// `Wildcard` (`BoundEnv::free_vars_are_patterns`), which the spatial matcher
/// satisfies with any sub-term whatsoever. Every position the reducer must
/// discharge is therefore discharged. ∎
///
/// The converse does not hold (the `[1, v]` counterexample above is exactly a
/// machine match with no host match), so a host FAILURE proves nothing and is
/// reported as `None` rather than as `Some(false)`. The rule is therefore:
///
/// ```text
///     Some(σ)  ⇒  Some(true)        // proved: the machine matches too
///     None     ⇒  None              // declined: the machine may still match
/// ```
///
/// Note that this costs nothing OPERATIONALLY: `Some(false)` and `None` have the
/// same effect at every call site — the host does not fire the COMM — so the
/// host's observable behaviour is "fire iff a match is PROVED", which is the
/// fail-closed discipline the rest of the guard path already follows.
///
/// One more way the positive direction could slip is `@`-send sugar: `@Nil!(1)`
/// and `@(Nil)!(1)` are DISTINCT `Proc` variants that denote the same process and
/// lower to the same `Par`. Both operands are therefore put through the same
/// `normalize_send_sugar_canon` that rhocalc's own term-equality path uses, so a
/// purely notational difference cannot make the host miss a match the machine
/// finds (which would only lose reduction) — or, more importantly, cannot arise
/// as an asymmetry between the two operands.
///
/// ## Why the separating conjunction is declined
///
/// Its semantics is AC matching with a remainder — `list_match_single_` +
/// `sub_pars` + `MaximumBipartiteMatch`. A host re-implementation would be
/// exactly the second, divergent matcher this design exists to avoid.
///
/// ## What `None` costs, and what it does not
///
/// `None` is not a failure and not a verdict. `eval_guard_bool` propagates it,
/// `eval_where_comm_single` declines the COMM, and `comm_pforwhere_subst` keeps
/// the `CommWhere` marker — so the guard is simply not decided HOST-side and the
/// machine decides it instead, exactly as it does for every guard in production
/// (§17.9.3: the `where` guard is not host-evaluated on the production path).
/// Declining costs host-side reduction; it never costs decidability, and it can
/// never produce a wrong answer.
///
/// A sub-formula that is itself undecided propagates `None` through the
/// propositional arms (via `?`), EXCEPT where the connective's verdict is already
/// forced — `⊥ ∧ φ` is `false` whatever `φ` is. Those short-circuits come from
/// [`is_statically_false`]/[`is_statically_true`], so the host never declines a
/// formula whose value is syntactically determined.
pub fn host_matches_verdict(target: &Proc, formula: &Proc) -> Option<bool> {
    // A statically-determined formula needs no matcher at all, and answering it
    // here means a `{φ|ψ}` buried under a settled connective (e.g. `false and
    // {φ|ψ}`) does not force the whole guard to be deferred.
    if is_statically_false(formula) {
        return Some(false);
    }
    if is_statically_true(formula) {
        return Some(true);
    }
    match classify(formula) {
        FormulaShape::Verum => Some(true),
        FormulaShape::Falsum => Some(false),
        // The propositional arms use KLEENE strong three-valued logic, with `None`
        // reading as "unknown". That is strictly more informative than propagating
        // `None` on first sight of an undecided operand, and it is still sound:
        // Kleene's tables answer a value only where EVERY completion of the unknown
        // operand gives that value. Concretely, `⊥ ∧ ?` is `false` and `⊤ ∨ ?` is
        // `true` whatever `?` turns out to be — and those are common shapes here,
        // because the positive-only term arm makes "unknown" the ordinary answer
        // for a non-matching sub-pattern (`"bye" or "hi"` on the target `"hi"` is
        // TRUE and must be answered as such).
        FormulaShape::Conjunction(left, right) => kleene_and(
            host_matches_verdict(target, left),
            host_matches_verdict(target, right),
        ),
        FormulaShape::Disjunction(left, right) => kleene_or(
            host_matches_verdict(target, left),
            host_matches_verdict(target, right),
        ),
        FormulaShape::Negation(inner) => host_matches_verdict(target, inner).map(|v| !v),
        // `φ ⇒ ψ ≡ ¬φ ∨ ψ`, evaluated in the same three-valued logic.
        FormulaShape::Implication(antecedent, consequent) => kleene_or(
            host_matches_verdict(target, antecedent).map(|v| !v),
            host_matches_verdict(target, consequent),
        ),
        // Deferred to the machine — see the doc comment.
        FormulaShape::Separation(_) => None,
        // ★ POSITIVE-ONLY. See the doc comment for the containment proof: a host
        // match implies a machine match, but a host NON-match implies nothing, so
        // only the success direction may be reported as a verdict.
        //
        // Both operands are canonicalized first, so an `@`-send sugar difference
        // cannot make the operands disagree notationally where they agree
        // semantically.
        FormulaShape::Term => {
            let target = crate::rhocalc::runtime::canon_for_term_equality(target);
            let pattern = crate::rhocalc::runtime::canon_for_term_equality(formula);
            match target.match_pattern(&pattern) {
                Some(_bindings) => Some(true),
                // Declined, NOT `Some(false)`. Operationally identical at every
                // call site (neither fires the COMM), but it keeps the invariant
                // "a host verdict is always the machine's verdict" exactly true.
                None => None,
            }
        },
    }
}

/// Kleene strong conjunction over `Option<bool>` (`None` = unknown).
///
/// | ∧ | T | F | ? |
/// |---|---|---|---|
/// | **T** | T | F | ? |
/// | **F** | F | F | F |
/// | **?** | ? | F | ? |
///
/// Sound because `⟦φ ∧ ψ⟧ = ⟦φ⟧ ∩ ⟦ψ⟧`: a single `false` empties the intersection
/// whatever the other operand is, and `true` is answered only when both are known
/// true.
fn kleene_and(left: Option<bool>, right: Option<bool>) -> Option<bool> {
    match (left, right) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}

/// Kleene strong disjunction over `Option<bool>` (`None` = unknown).
///
/// | ∨ | T | F | ? |
/// |---|---|---|---|
/// | **T** | T | T | T |
/// | **F** | T | F | ? |
/// | **?** | T | ? | ? |
///
/// Sound because `⟦φ ∨ ψ⟧ = ⟦φ⟧ ∪ ⟦ψ⟧`: a single `true` fills the union whatever
/// the other operand is, and `false` is answered only when both are known false.
fn kleene_or(left: Option<bool>, right: Option<bool>) -> Option<bool> {
    match (left, right) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    }
}

/// The `Proc` for the boolean literal `value` — the shape `classify` reads as
/// [`FormulaShape::Verum`] / [`FormulaShape::Falsum`].
///
/// Exposed so callers (tests, and any future formula rewriter) construct the
/// logical constants the same way the classifier recognizes them, rather than
/// re-deriving the `CastBool(BoolLit(_))` spelling.
pub fn bool_formula(value: bool) -> Proc {
    Proc::CastBool(Arc::new(Bool::BoolLit(value)))
}
