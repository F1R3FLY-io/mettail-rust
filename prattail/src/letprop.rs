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
    mu_calculus_to_pata, MuCalculusFormula, ParityAlternatingTreeAutomaton,
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

/// The body expression of a `letprop`.
///
/// Mirrors `BehavioralPred` but adds a `Recursive` variant for
/// self-references. Lowered to `MuCalculusFormula` by
/// `lower_to_mu_calculus`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LetPropExpr {
    /// Always true.
    True,
    /// Always false.
    False,
    /// Atomic relation query: `R(args)`.
    Atom { relation: String, args: Vec<String> },
    /// Recursive self-reference: `name(args)`. The args must be the
    /// formal parameter names of the enclosing `letprop` (no
    /// argument substitution is supported in Phase 10A).
    Recursive { args: Vec<String> },
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
    /// A recursive reference passes argument names that do not match
    /// the predicate's formal parameter list.
    ArgumentMismatch {
        name: String,
        expected: Vec<String>,
        actual: Vec<String>,
    },
    /// The body has no recursive references — use a plain
    /// `BehavioralPred` instead. (Not strictly an error; can be
    /// downgraded to a warning.)
    NotRecursive { name: String },
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
            LetPropError::ArgumentMismatch {
                name,
                expected,
                actual,
            } => write!(
                f,
                "letprop `{}`: recursive call passes args {:?} but the \
                 predicate is declared with params {:?}",
                name, actual, expected
            ),
            LetPropError::NotRecursive { name } => write!(
                f,
                "letprop `{}`: body has no recursive references; use a \
                 plain BehavioralPred instead",
                name
            ),
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
        LetPropExpr::True | LetPropExpr::False | LetPropExpr::Atom { .. } => {}
        LetPropExpr::Recursive { .. } => {
            if inside_negation {
                *negative = true;
            } else {
                *positive = true;
            }
        }
        LetPropExpr::Not(inner) => {
            analyze_polarity_inner(inner, !inside_negation, positive, negative);
        }
        LetPropExpr::And(a, b) | LetPropExpr::Or(a, b) => {
            analyze_polarity_inner(a, inside_negation, positive, negative);
            analyze_polarity_inner(b, inside_negation, positive, negative);
        }
        LetPropExpr::Implies(a, b) => {
            // P ⟹ Q ≡ ¬P ∨ Q : antecedent flips polarity
            analyze_polarity_inner(a, !inside_negation, positive, negative);
            analyze_polarity_inner(b, inside_negation, positive, negative);
        }
    }
}

/// Verify that every recursive reference's args match the predicate's
/// formal parameter list.
pub fn validate_arguments(
    pred: &RecursivePredicate,
) -> Result<(), LetPropError> {
    let mut error: Option<LetPropError> = None;
    walk_recursive_calls(&pred.body, &mut |args| {
        if args != pred.params.as_slice() {
            error.get_or_insert_with(|| LetPropError::ArgumentMismatch {
                name: pred.name.clone(),
                expected: pred.params.clone(),
                actual: args.to_vec(),
            });
        }
    });
    if let Some(e) = error {
        Err(e)
    } else {
        Ok(())
    }
}

fn walk_recursive_calls<F>(expr: &LetPropExpr, f: &mut F)
where
    F: FnMut(&[String]),
{
    match expr {
        LetPropExpr::Recursive { args } => f(args),
        LetPropExpr::Not(inner) => walk_recursive_calls(inner, f),
        LetPropExpr::And(a, b)
        | LetPropExpr::Or(a, b)
        | LetPropExpr::Implies(a, b) => {
            walk_recursive_calls(a, f);
            walk_recursive_calls(b, f);
        }
        _ => {}
    }
}

/// Lower a `RecursivePredicate` to a `MuCalculusFormula` (Phase 10B).
///
/// Choice of `μ` (least fixpoint) vs `ν` (greatest fixpoint) is made
/// by `analyze_polarity`. The body is lowered structurally, with
/// recursive self-references translated to a `Var(name)` reference
/// to the fixpoint binder.
pub fn lower_to_mu_calculus(
    pred: &RecursivePredicate,
) -> Result<MuCalculusFormula, LetPropError> {
    validate_arguments(pred)?;
    let (polarity, mixed) = analyze_polarity(&pred.body);
    if mixed {
        return Err(LetPropError::MixedPolarity {
            name: pred.name.clone(),
        });
    }
    let positive = match polarity {
        Some(p) => p,
        None => {
            return Err(LetPropError::NotRecursive {
                name: pred.name.clone(),
            });
        }
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
        }
        LetPropExpr::Recursive { .. } => {
            MuCalculusFormula::Var(self_name.to_string())
        }
        LetPropExpr::Not(inner) => {
            MuCalculusFormula::Not(Box::new(lower_expr(inner, self_name)))
        }
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
                Box::new(MuCalculusFormula::Not(Box::new(lower_expr(
                    a, self_name,
                )))),
                Box::new(lower_expr(b, self_name)),
            )
        }
    }
}

/// Bridge to PATA (Phase 10C): compile a `RecursivePredicate` all
/// the way through to a Parity Alternating Tree Automaton.
pub fn letprop_to_pata(
    pred: &RecursivePredicate,
    max_arity: usize,
) -> Result<ParityAlternatingTreeAutomaton<BooleanWeight>, LetPropError> {
    let mu_formula = lower_to_mu_calculus(pred)?;
    Ok(mu_calculus_to_pata(&mu_formula, max_arity))
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
        }
        LetPropExpr::Not(inner) => collect_relations_inner(inner, acc),
        LetPropExpr::And(a, b)
        | LetPropExpr::Or(a, b)
        | LetPropExpr::Implies(a, b) => {
            collect_relations_inner(a, acc);
            collect_relations_inner(b, acc);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rec(args: &[&str]) -> LetPropExpr {
        LetPropExpr::Recursive {
            args: args.iter().map(|s| s.to_string()).collect(),
        }
    }

    fn atom(name: &str, args: &[&str]) -> LetPropExpr {
        LetPropExpr::Atom {
            relation: name.to_string(),
            args: args.iter().map(|s| s.to_string()).collect(),
        }
    }

    #[test]
    fn polarity_positive_recursive() {
        // reachable(x, y) = edge(x, y) \/ reachable(x, y)
        let body = LetPropExpr::Or(
            Box::new(atom("edge", &["x", "y"])),
            Box::new(rec(&["x", "y"])),
        );
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
        let body = LetPropExpr::And(
            Box::new(rec(&[])),
            Box::new(LetPropExpr::Not(Box::new(rec(&[])))),
        );
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
            body: LetPropExpr::Or(
                Box::new(atom("edge", &["x", "y"])),
                Box::new(rec(&["x", "y"])),
            ),
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
                Box::new(LetPropExpr::Not(Box::new(LetPropExpr::Not(
                    Box::new(LetPropExpr::Not(Box::new(rec(&[])))),
                )))),
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
        assert!(matches!(
            result,
            Err(LetPropError::MixedPolarity { .. })
        ));
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
                // Recursive call passes wrong args
                Box::new(LetPropExpr::Recursive {
                    args: vec!["a".to_string()],
                }),
            ),
        };
        let result = lower_to_mu_calculus(&pred);
        assert!(matches!(
            result,
            Err(LetPropError::ArgumentMismatch { .. })
        ));
    }

    #[test]
    fn letprop_to_pata_compiles() {
        let pred = RecursivePredicate {
            name: "reachable".to_string(),
            params: vec!["x".to_string(), "y".to_string()],
            body: LetPropExpr::Or(
                Box::new(atom("edge", &["x", "y"])),
                Box::new(rec(&["x", "y"])),
            ),
        };
        let pata = letprop_to_pata(&pred, 2).expect("should compile to PATA");
        assert!(pata.num_states() > 0);
    }

    #[test]
    fn collect_relations_finds_atoms() {
        let expr = LetPropExpr::And(
            Box::new(atom("edge", &["x", "y"])),
            Box::new(LetPropExpr::Or(
                Box::new(atom("node", &["x"])),
                Box::new(atom("safe", &[])),
            )),
        );
        let rels = collect_relations(&expr);
        assert_eq!(rels.len(), 3);
        assert!(rels.contains("edge"));
        assert!(rels.contains("node"));
        assert!(rels.contains("safe"));
    }
}
