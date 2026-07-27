//! M-1b — the FORMULA compiler: a Rholang `Proc` ⟶ a Rholang PATTERN (`Par`).
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
//!        Rholang                    this module                 f1r3node
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
//! The left column is [`mettail_languages::rholang::formula::FormulaShape`], the
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
//! delegates to `rholang_ast::lower_proc_in_env`, which is itself total (it
//! returns `Ok`, or a typed [`RholangAstLowerError`] — never a panic). There is
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

use mettail_languages::rholang::Proc;
use models::rhoapi::Par;
use models::rust::utils::{new_conn_not_body_par, new_wildcard_par, union};

use crate::rholang_ast::{BoundEnv, RholangAstLowerError};

/// §18.1 — compile a formula to the Rholang pattern that decides it.
///
/// The public, environment-free entry: the formula is treated as a CLOSED
/// pattern, which is the shape a `matches` written outside any receive has.
/// Inside the recursive term lowering — where a formula may reference the
/// receive's bound variables — `rholang_ast` calls [`lower_formula_in_env`] with
/// the live binder environment instead.
///
/// Total: see the module header.
pub fn lower_formula(formula: &Proc) -> Result<Par, RholangAstLowerError> {
    lower_formula_in_env(formula, &BoundEnv::new())
}

/// [`lower_formula`] against a live binder environment.
///
/// The environment is needed because a formula's SUB-TERMS are lowered by
/// `lower_proc`: a reference to a receive-bound variable inside a pattern must
/// become the corresponding `BoundVar`, exactly as it would outside a pattern.
/// (The pattern's own FREE variables are binders and are not resolved — that is
/// `lower_proc_var`'s existing free-variable arm, unchanged here.)
pub fn lower_formula_in_env(formula: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    // ★ M-2: this function is the 87th member of `rholang_ast`'s recursion component, so it
    // does NOT drive its own recursion. `t matches (φ and (ψ and (…)))` nests through the
    // connective arms, and `FormulaShape::Term` re-enters `lower_proc` — both unbounded — so
    // running the formula walk here would leave a reachable Θ(depth) native-stack path no
    // matter what the term half did. Its `FormulaShape` arms live in the driver's Enter/Combine
    // dispatch (`Job::Formula` / `Kont::Formula*`), which is also what lets a formula and the
    // term it constrains share ONE work stack rather than nesting two machines.
    //
    // The assemblers below (`verum_pattern`, `falsum_pattern`, `negated`, `connective_par`) are
    // the post-order halves and are `pub(crate)` for that reason; the recursive form is kept
    // verbatim in `rholang_ast::recursive_oracle` and is compared against this path by
    // `driver_matches_the_recursive_oracle`.
    crate::rholang_ast::drive_formula(formula, env)
}

/// `⊤` — the pattern satisfied by every term.
pub(crate) fn verum_pattern() -> Par {
    new_wildcard_par(Vec::new(), true)
}

/// `⊥` — the pattern satisfied by no term: `ConnNot Wildcard`.
///
/// `ConnNotBody(b)` matches a target iff the target does NOT match `b`
/// (`spatial_matcher.rs`); with `b = Wildcard`, which every target matches, the
/// negation is satisfied by nothing. So this really is the bottom of the pattern
/// lattice, not an approximation of it.
pub(crate) fn falsum_pattern() -> Par {
    negated(verum_pattern())
}

/// `ConnNotBody ⟦φ⟧` with the operand's free-variable footprint carried over.
pub(crate) fn negated(operand: Par) -> Par {
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
/// `unary_expr_par` maintain in `rholang_ast`.
///
/// `connective_used` is forced to `true`: a `Par` carrying a connective IS a
/// pattern, unconditionally.
pub(crate) fn connective_par(mut par: Par, operands: &[Par]) -> Par {
    let mut locally_free = Vec::new();
    for operand in operands {
        locally_free = union(locally_free, operand.locally_free.clone());
    }
    par.locally_free = locally_free;
    par.connective_used = true;
    par
}
