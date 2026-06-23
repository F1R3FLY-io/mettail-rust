//! `letprop` recursive predicate definitions (Phase 10 of the
//! predicated-types implementation plan).
//!
//! `letprop` is the surface syntax for defining recursive behavioral
//! predicates. The body of a `letprop` may reference the predicate's
//! own name, allowing constructs like:
//!
//! ```text
//! letprop reachable(x, y) =
//!     edge(x, y) \/ exists(z, nodes, edge(x, z) /\ reachable(z, y));
//! ```
//!
//! Recursive references are lowered to least or greatest fixpoint
//! operators in the modal mu-calculus, then compiled to a Parity
//! Alternating Tree Automaton (PATA) via the existing
//! `parity_tree::mu_calculus_to_pata` infrastructure.
//!
//! ## Polarity-driven μ vs ν selection
//!
//! The choice between least fixpoint (`μ`) and greatest fixpoint
//! (`ν`) is determined by the polarity of the recursive reference:
//!
//! - **Positive polarity** (no `Not` between root and recursive call):
//!   the recursive predicate represents a "smallest set such that"
//!   relation — `μ` (e.g., `reachable` is the LEAST relation closed
//!   under transitivity).
//! - **Negative polarity** (recursive call inside a `Not`): the
//!   predicate represents a "largest set such that" relation — `ν`
//!   (e.g., `safe` is the LARGEST relation closed under one-step
//!   safety).
//!
//! Mixed polarities are rejected with `LetPropError::MixedPolarity`
//! since they yield monotone-impredicative recursion that the
//! mu-calculus cannot directly express.
//!
//! ## Phase 10 scope
//!
//! Phase 10A: parser (this module's `parse_letprop`).
//! Phase 10B: lowering (this module's `lower_to_mu_calculus`).
//! Phase 10C: bridge to PATA (this module's `letprop_to_pata`).
//! Phase 10D: codegen integration (a follow-up in
//!            `macros::gen::runtime::guard_codegen` that will emit a
//!            call to `letprop_to_pata` followed by a runtime PATA
//!            evaluation via Zielonka's algorithm).

use crate::automata::semiring::BooleanWeight;
use crate::parity_tree::{
    try_mu_calculus_to_pata, MuCalculusFormula, ParityAlternatingTreeAutomaton,
};
use std::collections::HashSet;

/// A `letprop` recursive predicate definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursivePredicate {
    /// The predicate's name (used for self-references inside the body).
    pub name: String,
    /// Formal parameter names.
    pub params: Vec<String>,
    /// The body — may reference `name(args)` recursively.
    pub body: LetPropExpr,
}

/// An argument to a relation atom or a recursive self-reference.
///
/// The proposed `letprop` surface admits *argument substitution* — a
/// recursive call may pass a structured term built from the in-scope
/// variables rather than the bare formal parameter names. For example
/// `safe(child(x))` (predicated-types.md:8202) passes the applied term
/// `child(x)` in the position of `safe`'s formal parameter.
///
/// This is a small applicative term language:
/// - [`LetPropArg::Var`] — a variable reference (a formal parameter
///   name or a quantifier-bound variable in scope).
/// - [`LetPropArg::App`] — a function application `func(args)` whose
///   arguments are themselves `LetPropArg`s (so `child(x)`,
///   `child(child(x))`, `pair(x, y)`, … are representable).
///
/// **μ-calculus invariance.** Arguments are *retained on the AST* for
/// the documented runtime-dispatch contract (the runtime PATA evaluator
/// dispatches on `(relation, args)` at call time), but the μ-calculus
/// lowering DROPS them: the modal μ-calculus is propositional, so the
/// argument shape is decision-invariant. Widening `args` from
/// `Vec<String>` to `Vec<LetPropArg>` is therefore a pure representation
/// change — it never alters a satisfiability verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LetPropArg {
    /// A variable reference: a formal parameter or a quantifier-bound
    /// variable that must be in scope at the call site.
    Var(String),
    /// A function application `func(args)` (argument substitution).
    App { func: String, args: Vec<LetPropArg> },
}

impl From<&str> for LetPropArg {
    /// A bare identifier is a variable reference. This is the migration
    /// shim that lets `Vec<String>`-era construction sites widen to
    /// `Vec<LetPropArg>` without restructuring (each old `String`
    /// becomes a [`LetPropArg::Var`]).
    fn from(name: &str) -> Self {
        LetPropArg::Var(name.to_string())
    }
}

impl From<String> for LetPropArg {
    fn from(name: String) -> Self {
        LetPropArg::Var(name)
    }
}

impl LetPropArg {
    /// Collect the set of free variable names referenced by this
    /// argument. A [`LetPropArg::Var`] contributes its own name; a
    /// [`LetPropArg::App`] contributes the union of its arguments' free
    /// variables (the function symbol `func` is a relation/constructor
    /// name, not a variable, so it is NOT collected).
    ///
    /// Used by [`validate_arguments`] to enforce that every recursive
    /// call's arguments reference only in-scope variables.
    pub fn free_vars(&self) -> HashSet<String> {
        let mut acc = HashSet::new();
        self.collect_free_vars(&mut acc);
        acc
    }

    fn collect_free_vars(&self, acc: &mut HashSet<String>) {
        match self {
            LetPropArg::Var(name) => {
                acc.insert(name.clone());
            },
            LetPropArg::App { args, .. } => {
                for arg in args {
                    arg.collect_free_vars(acc);
                }
            },
        }
    }
}

/// Build a `Vec<LetPropArg>` from a slice of bare variable names. A
/// convenience shim for construction sites (tests, callers) that pass
/// the simple "args are just the formal parameter names" case — the
/// common shape before argument substitution was supported.
pub fn vars(names: &[&str]) -> Vec<LetPropArg> {
    names
        .iter()
        .map(|name| LetPropArg::Var(name.to_string()))
        .collect()
}

/// The body expression of a `letprop`.
///
/// Mirrors `BehavioralPred` but adds a `Recursive` variant for
/// self-references and `Forall`/`Exists` for quantifiers. Lowered to
/// `MuCalculusFormula` by `lower_to_mu_calculus`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LetPropExpr {
    /// Always true.
    True,
    /// Always false.
    False,
    /// Atomic relation query: `R(args)`.
    Atom { relation: String, args: Vec<LetPropArg> },
    /// Recursive self-reference: `name(args)`. The args may now be
    /// structured terms (argument substitution, e.g. `safe(child(x))`);
    /// every variable they reference must be in scope (a formal
    /// parameter or a quantifier-bound variable), checked by
    /// [`validate_arguments`].
    Recursive { args: Vec<LetPropArg> },
    /// Universal quantifier `forall(var, body)`. Lowers to the modal
    /// box `□_{→*}` over the reserved abstract reduction direction; the
    /// bound `var` ranges over the (abstract) successors and brings the
    /// name into scope for `body`'s recursive-call arguments.
    Forall { var: String, body: Box<LetPropExpr> },
    /// Existential quantifier `exists(var, body)`. Lowers to the modal
    /// diamond `◇_{→*}` over the reserved abstract reduction direction.
    Exists { var: String, body: Box<LetPropExpr> },
    /// Conjunction.
    And(Box<LetPropExpr>, Box<LetPropExpr>),
    /// Disjunction.
    Or(Box<LetPropExpr>, Box<LetPropExpr>),
    /// Negation.
    Not(Box<LetPropExpr>),
    /// Implication: `a => b ≡ ¬a ∨ b`.
    Implies(Box<LetPropExpr>, Box<LetPropExpr>),
}

/// Errors that can arise from `letprop` parsing or lowering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LetPropError {
    /// The body's recursive references have mixed polarities (some
    /// inside a `Not`, some not), which yield non-monotone
    /// recursion. The mu-calculus only supports monotone fixpoints.
    MixedPolarity { name: String },
    /// A recursive reference passes an argument that references a
    /// variable not in scope (neither a formal parameter nor a
    /// quantifier-bound variable). `actual` is the rendered offending
    /// argument list; `out_of_scope` names the variable(s) that escaped
    /// the parameter ∪ bound-variable scope.
    ArgumentMismatch {
        name: String,
        expected: Vec<String>,
        actual: String,
        out_of_scope: Vec<String>,
    },
    /// The body has no recursive references — use a plain
    /// `BehavioralPred` instead. (Not strictly an error; can be
    /// downgraded to a warning.)
    NotRecursive { name: String },
    /// Lowering produced an ill-scoped mu-calculus formula.
    MuCalculusCompile { message: String },
}

impl std::fmt::Display for LetPropError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LetPropError::MixedPolarity { name } => write!(
                f,
                "letprop `{}`: recursive references have mixed polarities; \
                 the mu-calculus requires uniform monotone polarity",
                name
            ),
            LetPropError::ArgumentMismatch { name, expected, actual, out_of_scope } => write!(
                f,
                "letprop `{}`: recursive call args {} reference out-of-scope \
                 variable(s) {:?}; in scope are the params {:?} plus any \
                 enclosing quantifier-bound variables",
                name, actual, out_of_scope, expected
            ),
            LetPropError::NotRecursive { name } => write!(
                f,
                "letprop `{}`: body has no recursive references; use a \
                 plain BehavioralPred instead",
                name
            ),
            LetPropError::MuCalculusCompile { message } => {
                write!(f, "letprop lowered to an invalid mu-calculus formula: {}", message)
            },
        }
    }
}

impl std::error::Error for LetPropError {}

/// Determine the polarity of every recursive reference in the body
/// and return the unified polarity.
///
/// Returns:
/// - `Some(true)` — all recursive references are positive (`μ`).
/// - `Some(false)` — all recursive references are negative (`ν`).
/// - `None` — no recursive references (will produce
///    `LetPropError::NotRecursive`).
///
/// Mixed-polarity bodies cause this function to return whichever
/// polarity it encountered first AND set the `mixed_polarity` flag
/// in the result tuple.
pub fn analyze_polarity(expr: &LetPropExpr) -> (Option<bool>, bool) {
    let mut positive = false;
    let mut negative = false;
    analyze_polarity_inner(expr, false, &mut positive, &mut negative);
    let mixed = positive && negative;
    let polarity = if positive {
        Some(true)
    } else if negative {
        Some(false)
    } else {
        None
    };
    (polarity, mixed)
}

fn analyze_polarity_inner(
    expr: &LetPropExpr,
    inside_negation: bool,
    positive: &mut bool,
    negative: &mut bool,
) {
    match expr {
        LetPropExpr::True | LetPropExpr::False | LetPropExpr::Atom { .. } => {},
        LetPropExpr::Recursive { .. } => {
            if inside_negation {
                *negative = true;
            } else {
                *positive = true;
            }
        },
        LetPropExpr::Forall { body, .. } | LetPropExpr::Exists { body, .. } => {
            // Quantifiers are polarity-transparent: a `□`/`◇` modality
            // is monotone in its body, so it does not flip the sign of a
            // recursive reference nested inside it.
            analyze_polarity_inner(body, inside_negation, positive, negative);
        },
        LetPropExpr::Not(inner) => {
            analyze_polarity_inner(inner, !inside_negation, positive, negative);
        },
        LetPropExpr::And(a, b) | LetPropExpr::Or(a, b) => {
            analyze_polarity_inner(a, inside_negation, positive, negative);
            analyze_polarity_inner(b, inside_negation, positive, negative);
        },
        LetPropExpr::Implies(a, b) => {
            // P ⟹ Q ≡ ¬P ∨ Q : antecedent flips polarity
            analyze_polarity_inner(a, !inside_negation, positive, negative);
            analyze_polarity_inner(b, inside_negation, positive, negative);
        },
    }
}

/// Render a `LetPropArg` list in surface form (`a, child(x)`), for
/// diagnostics. Not on the hot path — only used to build the
/// `ArgumentMismatch` payload.
fn render_args(args: &[LetPropArg]) -> String {
    args.iter().map(render_arg).collect::<Vec<_>>().join(", ")
}

fn render_arg(arg: &LetPropArg) -> String {
    match arg {
        LetPropArg::Var(name) => name.clone(),
        LetPropArg::App { func, args } => format!("{}({})", func, render_args(args)),
    }
}

/// Verify that every recursive reference's arguments are well-scoped.
///
/// **Scope rule (argument substitution).** Pre-substitution, the only
/// admissible argument list was the bare formal-parameter names; now a
/// recursive call may pass a structured term (`safe(child(x))`). The
/// well-scopedness condition relaxes accordingly from *exact match* to a
/// *scope check*: every variable in every recursive-call argument's
/// [`LetPropArg::free_vars`] must be in scope — i.e. a formal parameter
/// of the predicate, OR a variable bound by an enclosing `forall`/
/// `exists`. An argument referencing any other variable is still
/// rejected with [`LetPropError::ArgumentMismatch`].
pub fn validate_arguments(pred: &RecursivePredicate) -> Result<(), LetPropError> {
    let mut error: Option<LetPropError> = None;
    let mut scope: HashSet<String> = pred.params.iter().cloned().collect();
    walk_recursive_calls(&pred.body, &mut scope, &mut |args, scope| {
        let out_of_scope: Vec<String> = args
            .iter()
            .flat_map(|arg| arg.free_vars())
            .filter(|name| !scope.contains(name))
            .collect();
        if !out_of_scope.is_empty() {
            error.get_or_insert_with(|| LetPropError::ArgumentMismatch {
                name: pred.name.clone(),
                expected: pred.params.clone(),
                actual: render_args(args),
                out_of_scope,
            });
        }
    });
    match error {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// Walk every recursive self-reference in `expr`, invoking `f` with the
/// call's argument list AND the set of variables in scope at the call
/// site (formal parameters plus any enclosing quantifier-bound
/// variables). Quantifiers extend `scope` for the duration of their
/// body and restore it on exit.
fn walk_recursive_calls<F>(expr: &LetPropExpr, scope: &mut HashSet<String>, f: &mut F)
where
    F: FnMut(&[LetPropArg], &HashSet<String>),
{
    match expr {
        LetPropExpr::Recursive { args } => f(args, scope),
        LetPropExpr::Forall { var, body } | LetPropExpr::Exists { var, body } => {
            // Bring the bound variable into scope for the body, then
            // restore (unless it shadowed an already-in-scope name).
            let newly_bound = scope.insert(var.clone());
            walk_recursive_calls(body, scope, f);
            if newly_bound {
                scope.remove(var);
            }
        },
        LetPropExpr::Not(inner) => walk_recursive_calls(inner, scope, f),
        LetPropExpr::And(a, b) | LetPropExpr::Or(a, b) | LetPropExpr::Implies(a, b) => {
            walk_recursive_calls(a, scope, f);
            walk_recursive_calls(b, scope, f);
        },
        _ => {},
    }
}

/// Lower a `RecursivePredicate` to a `MuCalculusFormula` (Phase 10B).
///
/// Choice of `μ` (least fixpoint) vs `ν` (greatest fixpoint) is made
/// by `analyze_polarity`. The body is lowered structurally, with
/// recursive self-references translated to a `Var(name)` reference
/// to the fixpoint binder.
pub fn lower_to_mu_calculus(pred: &RecursivePredicate) -> Result<MuCalculusFormula, LetPropError> {
    validate_arguments(pred)?;
    let (polarity, mixed) = analyze_polarity(&pred.body);
    if mixed {
        return Err(LetPropError::MixedPolarity { name: pred.name.clone() });
    }
    let positive = match polarity {
        Some(p) => p,
        None => {
            // §4-(B): a body with no recursive self-reference but WITH a
            // quantifier (e.g. `halt x = forall(x', ¬rewrites_to(x, x'))`)
            // is still a fixpoint property in the modal μ-calculus — it
            // lowers to the greatest-fixpoint safety reading `νX. □…`
            // (predicated-types.md:5836 `νX. □_{→*}(¬X)`). The bound `X`
            // is vacuous here (the modal body has no `Var(name)`), so the
            // `Nu` wrapper is the doc's stated safety default rather than
            // an actual recursion. A body with NEITHER recursion NOR a
            // quantifier remains a genuine `NotRecursive` error.
            if has_quantifier(&pred.body) {
                let body_mu = lower_expr(&pred.body, &pred.name);
                return Ok(MuCalculusFormula::Nu {
                    var: pred.name.clone(),
                    body: Box::new(body_mu),
                });
            }
            return Err(LetPropError::NotRecursive { name: pred.name.clone() });
        },
    };

    let body_mu = lower_expr(&pred.body, &pred.name);

    Ok(if positive {
        MuCalculusFormula::Mu {
            var: pred.name.clone(),
            body: Box::new(body_mu),
        }
    } else {
        MuCalculusFormula::Nu {
            var: pred.name.clone(),
            body: Box::new(body_mu),
        }
    })
}

/// Does the body contain a `forall`/`exists` quantifier anywhere?
///
/// Used by [`lower_to_mu_calculus`] §4-(B) to decide whether a
/// non-recursive body is still lowerable (as a modal `νX.□`/`◇` safety
/// formula) rather than a `NotRecursive` error.
pub fn has_quantifier(expr: &LetPropExpr) -> bool {
    match expr {
        LetPropExpr::Forall { .. } | LetPropExpr::Exists { .. } => true,
        LetPropExpr::Not(inner) => has_quantifier(inner),
        LetPropExpr::And(a, b) | LetPropExpr::Or(a, b) | LetPropExpr::Implies(a, b) => {
            has_quantifier(a) || has_quantifier(b)
        },
        LetPropExpr::True
        | LetPropExpr::False
        | LetPropExpr::Atom { .. }
        | LetPropExpr::Recursive { .. } => false,
    }
}

/// Recursive lowering of a `LetPropExpr` to `MuCalculusFormula`.
fn lower_expr(expr: &LetPropExpr, self_name: &str) -> MuCalculusFormula {
    match expr {
        LetPropExpr::True => MuCalculusFormula::True,
        LetPropExpr::False => MuCalculusFormula::False,
        LetPropExpr::Atom { relation, .. } => {
            // Atomic relation queries become atom labels in the
            // mu-calculus. The args are dropped at this layer because
            // the mu-calculus is propositional — the runtime PATA
            // evaluator will need to dispatch on (relation, args) at
            // call time.
            MuCalculusFormula::Atom(relation.clone())
        },
        LetPropExpr::Recursive { .. } => MuCalculusFormula::Var(self_name.to_string()),
        // Quantifiers lower to the PATA tree engine's modal operators.
        // `child_idx: 0` is the reserved ABSTRACT REDUCTION DIRECTION
        // (`→*`), NOT an AST argument slot: it mirrors how `And`/`Or`/
        // `Mu`/`Nu` already overload child-direction 0, and is
        // decision-neutral because `check_emptiness` never matches the
        // synthetic `_box_0`/`_diamond_0` transition symbols against real
        // `Term` constructor labels (it works purely on the parity-game
        // graph: priorities + branching + transition target lists). The
        // bound `var` and the quantifier body's args are propositional at
        // this layer (the runtime PATA evaluator dispatches on them).
        LetPropExpr::Forall { body, .. } => MuCalculusFormula::Box {
            child_idx: 0,
            body: Box::new(lower_expr(body, self_name)),
        },
        LetPropExpr::Exists { body, .. } => MuCalculusFormula::Diamond {
            child_idx: 0,
            body: Box::new(lower_expr(body, self_name)),
        },
        LetPropExpr::Not(inner) => MuCalculusFormula::Not(Box::new(lower_expr(inner, self_name))),
        LetPropExpr::And(a, b) => MuCalculusFormula::And(
            Box::new(lower_expr(a, self_name)),
            Box::new(lower_expr(b, self_name)),
        ),
        LetPropExpr::Or(a, b) => MuCalculusFormula::Or(
            Box::new(lower_expr(a, self_name)),
            Box::new(lower_expr(b, self_name)),
        ),
        LetPropExpr::Implies(a, b) => {
            // P ⟹ Q ≡ ¬P ∨ Q
            MuCalculusFormula::Or(
                Box::new(MuCalculusFormula::Not(Box::new(lower_expr(a, self_name)))),
                Box::new(lower_expr(b, self_name)),
            )
        },
    }
}

/// Bridge to PATA (Phase 10C): compile a `RecursivePredicate` all
/// the way through to a Parity Alternating Tree Automaton.
pub fn letprop_to_pata(
    pred: &RecursivePredicate,
    max_arity: usize,
) -> Result<ParityAlternatingTreeAutomaton<BooleanWeight>, LetPropError> {
    let mu_formula = lower_to_mu_calculus(pred)?;
    try_mu_calculus_to_pata(&mu_formula, max_arity)
        .map_err(|err| LetPropError::MuCalculusCompile { message: err.to_string() })
}

/// Collect every distinct atom name referenced by a `LetPropExpr`.
/// Used by codegen to plan the runtime relation snapshot.
pub fn collect_relations(expr: &LetPropExpr) -> HashSet<String> {
    let mut acc = HashSet::new();
    collect_relations_inner(expr, &mut acc);
    acc
}

fn collect_relations_inner(expr: &LetPropExpr, acc: &mut HashSet<String>) {
    match expr {
        LetPropExpr::Atom { relation, .. } => {
            acc.insert(relation.clone());
        },
        LetPropExpr::Forall { body, .. } | LetPropExpr::Exists { body, .. } => {
            collect_relations_inner(body, acc);
        },
        LetPropExpr::Not(inner) => collect_relations_inner(inner, acc),
        LetPropExpr::And(a, b) | LetPropExpr::Or(a, b) | LetPropExpr::Implies(a, b) => {
            collect_relations_inner(a, acc);
            collect_relations_inner(b, acc);
        },
        _ => {},
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rec(args: &[&str]) -> LetPropExpr {
        LetPropExpr::Recursive { args: vars(args) }
    }

    fn atom(name: &str, args: &[&str]) -> LetPropExpr {
        LetPropExpr::Atom {
            relation: name.to_string(),
            args: vars(args),
        }
    }

    #[test]
    fn polarity_positive_recursive() {
        // reachable(x, y) = edge(x, y) \/ reachable(x, y)
        let body = LetPropExpr::Or(Box::new(atom("edge", &["x", "y"])), Box::new(rec(&["x", "y"])));
        let (pol, mixed) = analyze_polarity(&body);
        assert_eq!(pol, Some(true));
        assert!(!mixed);
    }

    #[test]
    fn polarity_negative_recursive() {
        // safe = ¬unsafe \/ ¬reachable
        // (recursive call inside Not → negative)
        let body = LetPropExpr::Or(
            Box::new(LetPropExpr::Not(Box::new(atom("unsafe", &[])))),
            Box::new(LetPropExpr::Not(Box::new(rec(&[])))),
        );
        let (pol, mixed) = analyze_polarity(&body);
        assert_eq!(pol, Some(false));
        assert!(!mixed);
    }

    #[test]
    fn polarity_mixed_is_flagged() {
        // body has both a positive and a negative recursive call
        let body =
            LetPropExpr::And(Box::new(rec(&[])), Box::new(LetPropExpr::Not(Box::new(rec(&[])))));
        let (_pol, mixed) = analyze_polarity(&body);
        assert!(mixed);
    }

    #[test]
    fn polarity_no_recursive_returns_none() {
        let body = atom("foo", &["a"]);
        let (pol, mixed) = analyze_polarity(&body);
        assert_eq!(pol, None);
        assert!(!mixed);
    }

    #[test]
    fn lower_positive_recursive_yields_mu() {
        let pred = RecursivePredicate {
            name: "reachable".to_string(),
            params: vec!["x".to_string(), "y".to_string()],
            body: LetPropExpr::Or(Box::new(atom("edge", &["x", "y"])), Box::new(rec(&["x", "y"]))),
        };
        let mu = lower_to_mu_calculus(&pred).expect("should lower");
        match mu {
            MuCalculusFormula::Mu { var, .. } => assert_eq!(var, "reachable"),
            other => panic!("expected Mu, got {:?}", other),
        }
    }

    #[test]
    fn lower_negative_recursive_yields_nu() {
        let pred = RecursivePredicate {
            name: "alwaysSafe".to_string(),
            params: vec![],
            body: LetPropExpr::And(
                Box::new(atom("safe", &[])),
                Box::new(LetPropExpr::Not(Box::new(LetPropExpr::Not(Box::new(LetPropExpr::Not(
                    Box::new(rec(&[])),
                )))))),
            ),
        };
        // Triple-nested Not: positive → negative → positive → negative
        let mu = lower_to_mu_calculus(&pred).expect("should lower");
        match mu {
            MuCalculusFormula::Nu { var, .. } => assert_eq!(var, "alwaysSafe"),
            other => panic!("expected Nu, got {:?}", other),
        }
    }

    #[test]
    fn lower_mixed_polarity_returns_error() {
        let pred = RecursivePredicate {
            name: "bad".to_string(),
            params: vec![],
            body: LetPropExpr::And(
                Box::new(rec(&[])),
                Box::new(LetPropExpr::Not(Box::new(rec(&[])))),
            ),
        };
        let result = lower_to_mu_calculus(&pred);
        assert!(matches!(result, Err(LetPropError::MixedPolarity { .. })));
    }

    #[test]
    fn lower_non_recursive_returns_error() {
        let pred = RecursivePredicate {
            name: "trivial".to_string(),
            params: vec![],
            body: atom("foo", &[]),
        };
        let result = lower_to_mu_calculus(&pred);
        assert!(matches!(result, Err(LetPropError::NotRecursive { .. })));
    }

    #[test]
    fn lower_arg_mismatch_returns_error() {
        let pred = RecursivePredicate {
            name: "bad".to_string(),
            params: vec!["x".to_string(), "y".to_string()],
            body: LetPropExpr::Or(
                Box::new(atom("edge", &["x", "y"])),
                // Recursive call references `a`, which is neither a formal
                // parameter (`x`, `y`) nor a quantifier-bound variable —
                // out of scope, so the scope check rejects it.
                Box::new(LetPropExpr::Recursive { args: vars(&["a"]) }),
            ),
        };
        let result = lower_to_mu_calculus(&pred);
        assert!(matches!(result, Err(LetPropError::ArgumentMismatch { .. })));
    }

    #[test]
    fn letprop_to_pata_compiles() {
        let pred = RecursivePredicate {
            name: "reachable".to_string(),
            params: vec!["x".to_string(), "y".to_string()],
            body: LetPropExpr::Or(Box::new(atom("edge", &["x", "y"])), Box::new(rec(&["x", "y"]))),
        };
        let pata = letprop_to_pata(&pred, 2).expect("should compile to PATA");
        assert!(pata.num_states() > 0);
    }

    #[test]
    fn collect_relations_finds_atoms() {
        let expr = LetPropExpr::And(
            Box::new(atom("edge", &["x", "y"])),
            Box::new(LetPropExpr::Or(Box::new(atom("node", &["x"])), Box::new(atom("safe", &[])))),
        );
        let rels = collect_relations(&expr);
        assert_eq!(rels.len(), 3);
        assert!(rels.contains("edge"));
        assert!(rels.contains("node"));
        assert!(rels.contains("safe"));
    }

    // ── Quantifier + argument-substitution tests ──────────────────────────────
    //
    // These exercise the (additive) quantifier and argument-substitution
    // surfaces. They are gated on `oslf-letprop` so the DEFAULT build's test
    // count stays byte-identical: `letprop.rs` itself is NOT feature-gated (so
    // its module compiles into the default build), and these tests must not
    // enlarge the default count. The feature build (`--features oslf-letprop`)
    // runs them, alongside the integration suites in `tests/`.
    #[cfg(feature = "oslf-letprop")]
    mod quantifier_argsubst {
        use super::*;

        fn app(func: &str, args: Vec<LetPropArg>) -> LetPropArg {
            LetPropArg::App { func: func.to_string(), args }
        }

        #[test]
        fn letprop_arg_from_str_is_var() {
            assert_eq!(LetPropArg::from("x"), LetPropArg::Var("x".to_string()));
            assert_eq!(
                vars(&["x", "y"]),
                vec![LetPropArg::Var("x".to_string()), LetPropArg::Var("y".to_string())]
            );
        }

        #[test]
        fn letprop_arg_free_vars_collects_nested() {
            // child(child(x)) free-vars = {x}; the function symbols are not vars.
            let arg = app("child", vec![app("child", vec![LetPropArg::from("x")])]);
            let fv = arg.free_vars();
            assert_eq!(fv.len(), 1);
            assert!(fv.contains("x"));
            // pair(x, y) free-vars = {x, y}.
            let arg2 = app("pair", vars(&["x", "y"]));
            let fv2 = arg2.free_vars();
            assert_eq!(fv2.len(), 2);
            assert!(fv2.contains("x") && fv2.contains("y"));
        }

        #[test]
        fn arg_subst_in_scope_validates() {
            // safe(x) = base(x) ∨ (step(x) ∧ safe(child(x))) — `child(x)` only
            // references the in-scope formal `x`, so validation passes.
            let pred = RecursivePredicate {
                name: "safe".to_string(),
                params: vec!["x".to_string()],
                body: LetPropExpr::Or(
                    Box::new(atom("base", &["x"])),
                    Box::new(LetPropExpr::And(
                        Box::new(atom("step", &["x"])),
                        Box::new(LetPropExpr::Recursive {
                            args: vec![app("child", vec![LetPropArg::from("x")])],
                        }),
                    )),
                ),
            };
            assert!(validate_arguments(&pred).is_ok());
            // It has a base case (`base`) ⇒ μ-fixpoint is satisfiable.
            let mu = lower_to_mu_calculus(&pred).expect("should lower");
            assert!(matches!(mu, MuCalculusFormula::Mu { .. }));
        }

        #[test]
        fn arg_subst_out_of_scope_rejected() {
            // safe(child(z)) where `z` is neither a param nor bound ⇒ rejected.
            let pred = RecursivePredicate {
                name: "safe".to_string(),
                params: vec!["x".to_string()],
                body: LetPropExpr::Or(
                    Box::new(atom("base", &["x"])),
                    Box::new(LetPropExpr::Recursive {
                        args: vec![app("child", vec![LetPropArg::from("z")])],
                    }),
                ),
            };
            let result = validate_arguments(&pred);
            match result {
                Err(LetPropError::ArgumentMismatch { out_of_scope, .. }) => {
                    assert_eq!(out_of_scope, vec!["z".to_string()]);
                },
                other => panic!("expected ArgumentMismatch on out-of-scope `z`, got {other:?}"),
            }
        }

        #[test]
        fn quantifier_bound_var_is_in_scope() {
            // safe(x) = base(x) ∨ forall(x', safe(child(x'))) — `x'` is in scope
            // inside the `forall` body, so `child(x')` validates.
            let pred = RecursivePredicate {
                name: "safe".to_string(),
                params: vec!["x".to_string()],
                body: LetPropExpr::Or(
                    Box::new(atom("base", &["x"])),
                    Box::new(LetPropExpr::Forall {
                        var: "x'".to_string(),
                        body: Box::new(LetPropExpr::Recursive {
                            args: vec![app("child", vec![LetPropArg::from("x'")])],
                        }),
                    }),
                ),
            };
            assert!(validate_arguments(&pred).is_ok());
        }

        // ── Quantifier lowering (Forall/Exists → Box/Diamond) ─────────────────────

        #[test]
        fn has_quantifier_detects_nested() {
            let q = LetPropExpr::Or(
                Box::new(atom("a", &[])),
                Box::new(LetPropExpr::Not(Box::new(LetPropExpr::Exists {
                    var: "y".to_string(),
                    body: Box::new(atom("b", &[])),
                }))),
            );
            assert!(has_quantifier(&q));
            assert!(!has_quantifier(&atom("a", &[])));
        }

        #[test]
        fn forall_lowers_to_box() {
            // `Forall` lowers to a `Box{child_idx:0, ...}` modal formula.
            let expr = LetPropExpr::Forall {
                var: "x'".to_string(),
                body: Box::new(LetPropExpr::Not(Box::new(atom("rewrites_to", &["x", "x'"])))),
            };
            match lower_expr(&expr, "halt") {
                MuCalculusFormula::Box { child_idx, .. } => assert_eq!(child_idx, 0),
                other => panic!("expected Box, got {other:?}"),
            }
        }

        #[test]
        fn exists_lowers_to_diamond() {
            let expr = LetPropExpr::Exists {
                var: "y".to_string(),
                body: Box::new(atom("rewrites_to", &["x", "y"])),
            };
            match lower_expr(&expr, "p") {
                MuCalculusFormula::Diamond { child_idx, .. } => assert_eq!(child_idx, 0),
                other => panic!("expected Diamond, got {other:?}"),
            }
        }

        #[test]
        fn quantifier_only_body_lowers_as_nu_not_error() {
            // §4-(B): `halt x = forall(x', ¬rewrites_to(x, x'))` — non-recursive
            // but quantified. It must lower (greatest-fixpoint safety default,
            // `νX. □(¬…)`) rather than erroring NotRecursive.
            let pred = RecursivePredicate {
                name: "halt".to_string(),
                params: vec!["x".to_string()],
                body: LetPropExpr::Forall {
                    var: "x'".to_string(),
                    body: Box::new(LetPropExpr::Not(Box::new(atom("rewrites_to", &["x", "x'"])))),
                },
            };
            let mu =
                lower_to_mu_calculus(&pred).expect("quantifier-only body must lower via §4-(B)");
            match mu {
                MuCalculusFormula::Nu { var, body } => {
                    assert_eq!(var, "halt");
                    assert!(matches!(*body, MuCalculusFormula::Box { child_idx: 0, .. }));
                },
                other => panic!("expected Nu(Box ...), got {other:?}"),
            }
            // And it compiles all the way to a PATA.
            let pata = letprop_to_pata(&pred, 1).expect("halt must compile to a PATA");
            assert!(pata.num_states() > 0);
        }

        #[test]
        fn non_recursive_non_quantified_body_still_errors() {
            // A plain atom (no recursion, no quantifier) is still NotRecursive.
            let pred = RecursivePredicate {
                name: "trivial".to_string(),
                params: vec!["x".to_string()],
                body: atom("foo", &["x"]),
            };
            assert!(matches!(lower_to_mu_calculus(&pred), Err(LetPropError::NotRecursive { .. })));
        }

        #[test]
        fn quantifier_is_polarity_transparent() {
            // A recursive call nested inside a `forall` keeps its positive sign
            // (the modality does not flip polarity).
            let body = LetPropExpr::Forall {
                var: "y".to_string(),
                body: Box::new(rec(&["x"])),
            };
            let (pol, mixed) = analyze_polarity(&body);
            assert_eq!(pol, Some(true));
            assert!(!mixed);
        }
    }
}
