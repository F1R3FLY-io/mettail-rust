//! M-1b — the FORMULA reading of a Rholang `Proc`.
//!
//! # Why this lives here and not in the lowering
//!
//! §18.1's design is that **a formula is a `Proc` sub-tree that is read as a
//! Rholang PATTERN**. That reading has two consumers:
//!
//! * `rholang-runtime::rholang_formula` COMPILES a formula to a `rhoapi::Par`
//!   pattern, which the reducer's spatial matcher then decides;
//! * `crate::rholang::receive::eval_guard_bool` DECIDES a formula host-side, on
//!   the fragment for which the generated first-order matcher is a faithful model
//!   of the reducer's.
//!
//! If each consumer classified `Proc` nodes for itself, the two would be free to
//! drift — one could start reading `not φ` as a connective while the other still
//! read it as a term — and a drift like that is invisible until it silently
//! changes which COMMs commit. So the classification is written ONCE, here, in
//! the crate that owns the Rholang syntax, and both consumers match on the same
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

use std::{collections::HashMap, sync::Arc};

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
    analyze_formula(formula, None).static_facts.is_false
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
    analyze_formula(formula, None).static_facts.is_true
}

/// The two conservative, syntactic truth judgements for one formula.
///
/// Computing the pair together is not only stack-safe; it also avoids the old mutual recursion's
/// repeated walk of the same subtree at every `not` and `implies` boundary. The pointer-keyed
/// table is an analysis cache, not semantic identity: keys are used only while the borrowed AST
/// is alive, and the returned verdict depends solely on constructor shape and child verdicts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct StaticFacts {
    is_false: bool,
    is_true: bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct FormulaFacts {
    static_facts: StaticFacts,
    host_verdict: Option<bool>,
}

#[derive(Clone, Copy)]
enum StaticBuild {
    Conjunction,
    Disjunction,
    Negation,
    Implication,
    Separation(usize),
}

impl StaticBuild {
    fn arity(self) -> usize {
        match self {
            Self::Negation => 1,
            Self::Conjunction | Self::Disjunction | Self::Implication => 2,
            Self::Separation(arity) => arity,
        }
    }
}

enum StaticWork<'formula> {
    Visit(&'formula Proc),
    Build { key: *const Proc, op: StaticBuild },
}

/// Analyze static truth and, when `target` is supplied, the host verdict in one post-order PDA.
///
/// Invariant: every `Visit` or `Build` produces exactly one [`FormulaFacts`] value. A `Build`
/// consumes its declared arity and produces one replacement, so the final value stack contains
/// exactly the root facts. Shared `Arc` subterms are evaluated once. The target is canonicalized
/// lazily—only if a non-settled term-pattern node is actually reached—and then reused for every
/// such node instead of being rebuilt once per recursive call as before.
fn analyze_formula(root: &Proc, target: Option<&Proc>) -> FormulaFacts {
    let mut work = vec![StaticWork::Visit(root)];
    let mut values = Vec::<FormulaFacts>::new();
    let mut by_node = HashMap::<*const Proc, FormulaFacts>::new();
    let mut canonical_target = None::<Proc>;

    while let Some(step) = work.pop() {
        match step {
            StaticWork::Visit(formula) => {
                let key = formula as *const Proc;
                if let Some(facts) = by_node.get(&key).copied() {
                    values.push(facts);
                    continue;
                }

                match classify(formula) {
                    FormulaShape::Verum => {
                        let facts = FormulaFacts {
                            static_facts: StaticFacts { is_false: false, is_true: true },
                            host_verdict: Some(true),
                        };
                        by_node.insert(key, facts);
                        values.push(facts);
                    },
                    FormulaShape::Falsum => {
                        let facts = FormulaFacts {
                            static_facts: StaticFacts { is_false: true, is_true: false },
                            host_verdict: Some(false),
                        };
                        by_node.insert(key, facts);
                        values.push(facts);
                    },
                    FormulaShape::Term => {
                        let host_verdict = target.and_then(|target| {
                            let canonical_target = canonical_target.get_or_insert_with(|| {
                                crate::rholang::runtime::canon_for_term_equality(target)
                            });
                            let pattern = crate::rholang::runtime::canon_for_term_equality(formula);
                            canonical_target.match_pattern(&pattern).map(|_| true)
                        });
                        let facts = FormulaFacts {
                            static_facts: StaticFacts::default(),
                            host_verdict,
                        };
                        by_node.insert(key, facts);
                        values.push(facts);
                    },
                    FormulaShape::Conjunction(left, right) => {
                        work.push(StaticWork::Build { key, op: StaticBuild::Conjunction });
                        work.push(StaticWork::Visit(right));
                        work.push(StaticWork::Visit(left));
                    },
                    FormulaShape::Disjunction(left, right) => {
                        work.push(StaticWork::Build { key, op: StaticBuild::Disjunction });
                        work.push(StaticWork::Visit(right));
                        work.push(StaticWork::Visit(left));
                    },
                    FormulaShape::Negation(inner) => {
                        work.push(StaticWork::Build { key, op: StaticBuild::Negation });
                        work.push(StaticWork::Visit(inner));
                    },
                    FormulaShape::Implication(antecedent, consequent) => {
                        work.push(StaticWork::Build { key, op: StaticBuild::Implication });
                        work.push(StaticWork::Visit(consequent));
                        work.push(StaticWork::Visit(antecedent));
                    },
                    FormulaShape::Separation(parts) => {
                        work.push(StaticWork::Build {
                            key,
                            op: StaticBuild::Separation(parts.len()),
                        });
                        work.extend(parts.into_iter().rev().map(StaticWork::Visit));
                    },
                }
            },
            StaticWork::Build { key, op } => {
                let arity = op.arity();
                let split = values
                    .len()
                    .checked_sub(arity)
                    .expect("formula PDA: continuation underflow");
                let children = values.split_off(split);
                let (static_facts, unsettled_host_verdict) = match op {
                    StaticBuild::Conjunction => (
                        StaticFacts {
                            is_false: children[0].static_facts.is_false
                                || children[1].static_facts.is_false,
                            is_true: children[0].static_facts.is_true
                                && children[1].static_facts.is_true,
                        },
                        kleene_and(children[0].host_verdict, children[1].host_verdict),
                    ),
                    StaticBuild::Disjunction => (
                        StaticFacts {
                            is_false: children[0].static_facts.is_false
                                && children[1].static_facts.is_false,
                            is_true: children[0].static_facts.is_true
                                || children[1].static_facts.is_true,
                        },
                        kleene_or(children[0].host_verdict, children[1].host_verdict),
                    ),
                    StaticBuild::Negation => (
                        StaticFacts {
                            is_false: children[0].static_facts.is_true,
                            is_true: children[0].static_facts.is_false,
                        },
                        children[0].host_verdict.map(|value| !value),
                    ),
                    StaticBuild::Implication => (
                        StaticFacts {
                            is_false: children[0].static_facts.is_true
                                && children[1].static_facts.is_false,
                            is_true: children[0].static_facts.is_false
                                || children[1].static_facts.is_true,
                        },
                        kleene_or(
                            children[0].host_verdict.map(|value| !value),
                            children[1].host_verdict,
                        ),
                    ),
                    StaticBuild::Separation(_) => (
                        StaticFacts {
                            is_false: children.iter().any(|child| child.static_facts.is_false),
                            // Deliberately undecided even when every component is statically true;
                            // see `is_statically_true`'s matcher-semantics argument above.
                            is_true: false,
                        },
                        None,
                    ),
                };
                // These are the old entry-point short-circuits, applied at every node in the
                // same bottom-up pass. They make `false and ?`, `true or ?`, and a separation
                // with a statically false part decidable without visiting a machine matcher.
                let host_verdict = if static_facts.is_false {
                    Some(false)
                } else if static_facts.is_true {
                    Some(true)
                } else {
                    unsettled_host_verdict
                };
                let facts = FormulaFacts { static_facts, host_verdict };
                by_node.insert(key, facts);
                values.push(facts);
            },
        }
    }

    assert_eq!(values.len(), 1, "formula PDA: the final value stack must contain one result");
    values.pop().expect("formula PDA: missing root result")
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
/// `normalize_send_sugar_canon` that rholang's own term-equality path uses, so a
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
    analyze_formula(formula, Some(target)).host_verdict
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
