//! M-1b — the FORMULA compiler: a RhoCalc `Proc` ⟶ a Rholang PATTERN (`Par`).
//!
//! # The idea (§18.1)
//!
//! > **A guard is a `Proc`. A *formula* is a `Proc` sub-tree that the lowering
//! > interprets as a Rholang PATTERN.**
//!
//! The whole spatial (and, at M-2, modal) fragment of the paper's condition
//! grammar is a **pattern algebra**, not a formula evaluator. Rholang already has
//! pattern-level conjunction, disjunction and negation (`ConnAndBody` /
//! `ConnOrBody` / `ConnNotBody`, decided by
//! `rholang/src/rust/interpreter/matcher/spatial_matcher.rs`), and it already has
//! the separating conjunction (a par-pattern `P | Q`, decided by
//! `list_match_single_` + `sub_pars` + `MaximumBipartiteMatch`). So MeTTaIL needs
//! to contribute a **pattern compiler** and nothing else — in particular **no
//! second matcher**, which is what would create the dual runtime path this design
//! exists to avoid.
//!
//! `t matches φ` therefore lowers to ONE
//! `ExprInstance::EMatchesBody(EMatches{ target: ⟦t⟧, pattern: ⟦φ⟧ })`: an
//! ordinary boolean `Proc` that composes with the existing guard language for
//! free, and that `rho-pure-eval` decides through the caller-injected
//! `SpatialMatch` oracle landed by M-1a (f1r3node `99b7b1c4`,
//! `rho-pure-eval/src/oracle.rs`).
//!
//! ```text
//!        RhoCalc                    this module                 f1r3node
//!   ┌──────────────────┐      ┌──────────────────────┐   ┌────────────────────┐
//!   │  t matches φ     │      │  ⟦t⟧  via lower_proc │   │ rho_pure_eval::    │
//!   │  (a Proc)        │─────▶│  ⟦φ⟧  via THIS file  │──▶│   eval_with        │
//!   └──────────────────┘      │  ⇒ EMatches{t, φ}    │   │     │              │
//!                             └──────────────────────┘   │     ▼              │
//!                                                        │ SpatialMatcher     │
//!                                                        │   Oracle::matches  │
//!                                                        └────────────────────┘
//! ```
//!
//! # The compilation table (§18.1, implemented arm for arm)
//!
//! The left column is [`mettail_languages::rhocalc::formula::FormulaShape`], the
//! single shared classification (see that module for why it lives in the
//! `languages` crate rather than here).
//!
//! | Shape | Surface | Compiles to |
//! | --- | --- | --- |
//! | `Verum` | `true` | `Wildcard` |
//! | `Falsum` | `false` | `ConnNotBody Wildcard` — the pattern satisfied by nothing |
//! | `Conjunction` | `φ and ψ` | `ConnAndBody [⟦φ⟧, ⟦ψ⟧]` |
//! | `Disjunction` | `φ or ψ` | `ConnOrBody [⟦φ⟧, ⟦ψ⟧]` |
//! | `Negation` | `not φ` | `ConnNotBody ⟦φ⟧` |
//! | `Implication` | `φ implies ψ` | `ConnOrBody [ConnNotBody ⟦φ⟧, ⟦ψ⟧]` |
//! | `Separation` | `{φ\|ψ}`, `φ\|ψ`, `PPar(φ,ψ)` | the separating par-pattern `⟦φ⟧ \| ⟦ψ⟧` |
//! | `Term` | anything else | `lower_proc` — the term read as a pattern |
//!
//! # Totality
//!
//! [`lower_formula`] is **total on `&Proc`**: `classify` is exhaustive, every
//! connective shape has a compilation arm, and the residual `Term` shape
//! delegates to `rhocalc_ast::lower_proc_in_env`, which is itself total (it
//! returns `Ok`, or a typed [`RhocalcAstLowerError`] — never a panic). There is
//! no `todo!`, no `unimplemented!`, no placeholder value, and no shape that falls
//! off the end.
//!
//! # The M-2 extension point
//!
//! `FormulaShape` is the seam. M-2 (`<K> true`, rule-enabledness) adds ONE
//! variant there, ONE classification arm, and ONE compilation arm here calling
//! `enabledness_pattern(def, K, fp)`. The `Term` fall-through is untouched, so a
//! formula shape M-2 does not recognize keeps compiling as a plain pattern rather
//! than silently becoming a modality. This is an extension point, not a stub:
//! nothing here is inert or waiting to be filled in.

use mettail_languages::rhocalc::formula::{classify, FormulaShape};
use mettail_languages::rhocalc::Proc;
use models::rhoapi::Par;
use models::rust::utils::{
    new_conn_and_body_par, new_conn_not_body_par, new_conn_or_body_par, new_wildcard_par, union,
};

use crate::rhocalc_ast::{lower_proc_in_env, BoundEnv, RhocalcAstLowerError};

/// §18.1 — compile a formula to the Rholang pattern that decides it.
///
/// The public, environment-free entry: the formula is treated as a CLOSED
/// pattern, which is the shape a `matches` written outside any receive has.
/// Inside the recursive term lowering — where a formula may reference the
/// receive's bound variables — `rhocalc_ast` calls [`lower_formula_in_env`] with
/// the live binder environment instead.
///
/// Total: see the module header.
pub fn lower_formula(formula: &Proc) -> Result<Par, RhocalcAstLowerError> {
    lower_formula_in_env(formula, &BoundEnv::new())
}

/// [`lower_formula`] against a live binder environment.
///
/// The environment is needed because a formula's SUB-TERMS are lowered by
/// `lower_proc`: a reference to a receive-bound variable inside a pattern must
/// become the corresponding `BoundVar`, exactly as it would outside a pattern.
/// (The pattern's own FREE variables are binders and are not resolved — that is
/// `lower_proc_var`'s existing free-variable arm, unchanged here.)
pub fn lower_formula_in_env(formula: &Proc, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match classify(formula) {
        // `true` ⊨ everything. Rholang's "matches everything" pattern is the
        // wildcard, which binds NOTHING — exactly right for a formula, whose job
        // is to answer a boolean, never to produce bindings.
        FormulaShape::Verum => Ok(verum_pattern()),
        // `false` ⊨ nothing. Emitting a real, self-contained pattern (rather than
        // relying on the caller to fold the guard away) is what keeps this
        // function total and COMPOSITIONAL: a `false` nested inside a larger
        // formula — `t matches (false or P)` — must still produce a pattern.
        FormulaShape::Falsum => Ok(falsum_pattern()),
        FormulaShape::Conjunction(left, right) => {
            let operands = [lower_formula_in_env(left, env)?, lower_formula_in_env(right, env)?];
            Ok(connective_par(
                new_conn_and_body_par(operands.to_vec(), Vec::new(), true),
                &operands,
            ))
        },
        FormulaShape::Disjunction(left, right) => {
            let operands = [lower_formula_in_env(left, env)?, lower_formula_in_env(right, env)?];
            Ok(connective_par(new_conn_or_body_par(operands.to_vec(), Vec::new(), true), &operands))
        },
        FormulaShape::Negation(inner) => Ok(negated(lower_formula_in_env(inner, env)?)),
        // `φ ⇒ ψ  ≡  ¬φ ∨ ψ`, at the PATTERN level. Rholang has no `ConnImplies`
        // and needs none, for exactly the reason M-0's EXPRESSION-level lowering
        // needs no `EImplies`: both halves of the identity already exist and are
        // already decided by the matcher (`spatial_matcher.rs`'s `ConnNotBody` and
        // `ConnOrBody` arms). The two levels are deliberately the same identity,
        // so `φ implies ψ` means the same thing whether it is evaluated as a
        // boolean expression or matched as a pattern.
        FormulaShape::Implication(antecedent, consequent) => {
            let operands = [
                negated(lower_formula_in_env(antecedent, env)?),
                lower_formula_in_env(consequent, env)?,
            ];
            Ok(connective_par(new_conn_or_body_par(operands.to_vec(), Vec::new(), true), &operands))
        },
        // The separating conjunction. `Par::append` IS parallel composition at the
        // `Par` level — it concatenates each component list, unions `locally_free`,
        // and ORs `connective_used` — so appending the compiled parts yields the
        // par-pattern `⟦φ⟧ | ⟦ψ⟧ | …`. This is the SAME construction `lower_proc`
        // uses for a `PPar`/`PParInfix` TERM, which is exactly what makes
        // `{ φ | ψ }` denote in pattern position the shape it denotes in term
        // position.
        //
        // The empty par (`{}`) compiles to `Nil` — the pattern satisfied only by
        // the null process, which is the correct nullary unit of the separating
        // conjunction, not a degenerate case to reject.
        FormulaShape::Separation(parts) => parts
            .into_iter()
            .try_fold(Par::default(), |acc, part| Ok(acc.append(lower_formula_in_env(part, env)?))),
        // The residual: an ordinary term, read as a pattern. `lower_proc` is the
        // single source of truth for "which `Par` does this `Proc` denote", so a
        // pattern and the term it is meant to match are lowered by the SAME code —
        // a structural guarantee that `t matches t` cannot fail through a lowering
        // asymmetry.
        //
        // The ONE reading that differs is the UNBOUND free variable: in term
        // position it lowers to a distinguishable marker datum, in PATTERN position
        // it is a placeholder that matches anything. `in_pattern_position()`
        // switches exactly that arm and nothing else — binders and FLT holes are
        // carried over unchanged, so a formula may still reference the receive's
        // bound variables. See `BoundEnv::free_vars_are_patterns` for why
        // `Wildcard` (and not a Rholang `FreeVar`) is the right image, and why it
        // is what makes the host and the machine agree.
        FormulaShape::Term => lower_proc_in_env(formula, &env.in_pattern_position()),
    }
}

/// `⊤` — the pattern satisfied by every term.
fn verum_pattern() -> Par {
    new_wildcard_par(Vec::new(), true)
}

/// `⊥` — the pattern satisfied by no term: `ConnNot Wildcard`.
///
/// `ConnNotBody(b)` matches a target iff the target does NOT match `b`
/// (`spatial_matcher.rs`); with `b = Wildcard`, which every target matches, the
/// negation is satisfied by nothing. So this really is the bottom of the pattern
/// lattice, not an approximation of it.
fn falsum_pattern() -> Par {
    negated(verum_pattern())
}

/// `ConnNotBody ⟦φ⟧` with the operand's free-variable footprint carried over.
fn negated(operand: Par) -> Par {
    connective_par(
        new_conn_not_body_par(operand.clone(), Vec::new(), true),
        std::slice::from_ref(&operand),
    )
}

/// Attach the free-variable footprint of `operands` to a freshly built connective
/// `Par`, and mark it a pattern.
///
/// The `new_conn_*_body_par` builders take `locally_free` as a PARAMETER and do
/// not derive it, so a connective built naively would advertise an EMPTY
/// `locally_free` even when its operands reference outer binders. That matters:
/// `locally_free` is what `substitute` and `Receive` consult to decide whether a
/// subtree needs traversal, and understating it can drop a substitution.
/// Recomputing it here as the union over the operands keeps a compiled formula's
/// footprint equal to the union of its parts' — the same invariant `Par::append`
/// maintains for parallel composition, and the same one `binary_expr_par` /
/// `unary_expr_par` maintain in `rhocalc_ast`.
///
/// `connective_used` is forced to `true`: a `Par` carrying a connective IS a
/// pattern, unconditionally.
fn connective_par(mut par: Par, operands: &[Par]) -> Par {
    let mut locally_free = Vec::new();
    for operand in operands {
        locally_free = union(locally_free, operand.locally_free.clone());
    }
    par.locally_free = locally_free;
    par.connective_used = true;
    par
}
