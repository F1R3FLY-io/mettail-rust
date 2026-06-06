//! Behavioral predicate AST.
//!
//! Phase 6 / F.0-sibling: moved from `mettail-runtime` to `mettail-prattail`
//! so the WPDS walker can produce predicates without crossing the
//! `prattail → runtime` cycle (runtime depends on prattail). The runtime
//! crate re-exports this module's types for backward compatibility.
//!
//! This is the runtime-friendly counterpart to
//! `mettail_ast::language::BehavioralPred`. Where the AST type uses
//! `syn::Ident` (because it lives in a proc-macro-consuming crate that
//! reads from `ParseStream`), this type uses `String` so it can be
//! stored in generated runtime enum variants and parsed at source time.
//!
//! ## Role at runtime
//!
//! `BehavioralPred` is a **passive data type** — no `evaluate()` method
//! and no thread-local snapshot. The thread-local fact snapshot and
//! `evaluate_pred_with_bindings` live in `runtime/src/pred_eval.rs`,
//! using these types via re-export.
//!
//! ## Semantics deferred to Ascent
//!
//! - `RelationQuery` — lowered to an Ascent join clause `rel(args)`.
//! - `Quantified { ForAll | Exists, ... }` — lowered via
//!   `prattail::logict::QuantifiedFormula` + `evaluate_quantified`.
//! - `AcMatch` — lowered to specialized Ascent code using
//!   `prattail::logict::multiset_partitions`.
//! - `And`, `Or`, `Not`, `Implies` — Boolean rewrites to DNF + one
//!   Ascent rule per clause.
//! - `Top` — identity predicate; "no join clause".

use moniker::{BoundTerm, Var};
use std::fmt;

/// Runtime behavioral predicate. Stored as a field on guarded receive
/// constructors for per-instance shape dispatch and introspection.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BehavioralPred {
    /// Atomic relation query: `path(x, {})`, `halts(p)`.
    /// `negated = true` corresponds to Ascent's `!path(...)`
    /// (stratified negation).
    RelationQuery {
        relation_name: String,
        args: Vec<PredArg>,
        negated: bool,
    },
    /// Quantified predicate: `forall(y, nodes, body)` / `exists(y, nodes, body)`.
    Quantified {
        quantifier: Quantifier,
        var: String,
        domain: Option<QuantifiedDomain>,
        body: Box<BehavioralPred>,
    },
    /// AC-matching predicate: `ac_match(bag, [elem1, elem2, ...rest])`.
    AcMatch {
        bag: PredArg,
        elements: Vec<PredArg>,
        rest: Option<String>,
    },
    And(Box<BehavioralPred>, Box<BehavioralPred>),
    Or(Box<BehavioralPred>, Box<BehavioralPred>),
    Not(Box<BehavioralPred>),
    Implies(Box<BehavioralPred>, Box<BehavioralPred>),
    /// Always true — used as the identity predicate when the predicate slot is
    /// declared at language-spec time but filled at source-parse time.
    Top,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Quantifier {
    ForAll,
    Exists,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum QuantifiedDomain {
    /// Named domain: `forall(y, nodes, body)` — `nodes` is a declared
    /// relation.
    Named(String),
    /// Bounded depth: `exists(y, 100, body)` — search up to 100 steps.
    Bounded(usize),
    /// Enumerated set: `forall(y, {a, b, c}, body)`.
    Enumerated(Vec<PredArg>),
}

/// Arguments to a behavioral predicate. Variables refer to bindings
/// established by the structural pattern match (the `MatchBindings` of
/// §5 of the predicated-types design).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PredArg {
    /// Variable reference: looked up at compile time in the rule's
    /// MatchBindings context when generating the Ascent join clause.
    Var(String),
    /// Integer literal.
    IntLit(i64),
    /// String literal.
    StringLit(String),
}

impl BehavioralPred {
    /// Substitute variable references in this predicate. Used by the
    /// macro pipeline during pattern-match substitution when a bound
    /// variable's name changes.
    pub fn substitute_var(&self, old: &str, new: &str) -> Self {
        use BehavioralPred::*;
        match self {
            Top => Top,
            RelationQuery { relation_name, args, negated } => RelationQuery {
                relation_name: relation_name.clone(),
                args: args.iter().map(|a| a.substitute_var(old, new)).collect(),
                negated: *negated,
            },
            Quantified { quantifier, var, domain, body } => {
                // Shadowed: bound variable names do not undergo substitution.
                if var == old {
                    self.clone()
                } else {
                    Quantified {
                        quantifier: *quantifier,
                        var: var.clone(),
                        domain: domain.as_ref().map(|d| d.substitute_var(old, new)),
                        body: Box::new(body.substitute_var(old, new)),
                    }
                }
            },
            AcMatch { bag, elements, rest } => AcMatch {
                bag: bag.substitute_var(old, new),
                elements: elements
                    .iter()
                    .map(|e| e.substitute_var(old, new))
                    .collect(),
                rest: rest.clone(),
            },
            And(a, b) => {
                And(Box::new(a.substitute_var(old, new)), Box::new(b.substitute_var(old, new)))
            },
            Or(a, b) => {
                Or(Box::new(a.substitute_var(old, new)), Box::new(b.substitute_var(old, new)))
            },
            Not(inner) => Not(Box::new(inner.substitute_var(old, new))),
            Implies(p, c) => {
                Implies(Box::new(p.substitute_var(old, new)), Box::new(c.substitute_var(old, new)))
            },
        }
    }

    /// Collect all free variable names referenced by this predicate.
    pub fn free_vars(&self) -> std::collections::HashSet<String> {
        let mut acc = std::collections::HashSet::new();
        self.collect_free_vars(&mut acc, &mut std::collections::HashSet::new());
        acc
    }

    fn collect_free_vars(
        &self,
        acc: &mut std::collections::HashSet<String>,
        bound: &mut std::collections::HashSet<String>,
    ) {
        use BehavioralPred::*;
        match self {
            Top => {},
            RelationQuery { args, .. } => {
                for a in args {
                    if let PredArg::Var(v) = a {
                        if !bound.contains(v) {
                            acc.insert(v.clone());
                        }
                    }
                }
            },
            Quantified { var, domain, body, .. } => {
                if let Some(d) = domain {
                    d.collect_free_vars(acc, bound);
                }
                let inserted = bound.insert(var.clone());
                body.collect_free_vars(acc, bound);
                if inserted {
                    bound.remove(var);
                }
            },
            AcMatch { bag, elements, .. } => {
                if let PredArg::Var(v) = bag {
                    if !bound.contains(v) {
                        acc.insert(v.clone());
                    }
                }
                for e in elements {
                    if let PredArg::Var(v) = e {
                        if !bound.contains(v) {
                            acc.insert(v.clone());
                        }
                    }
                }
            },
            And(a, b) | Or(a, b) | Implies(a, b) => {
                a.collect_free_vars(acc, bound);
                b.collect_free_vars(acc, bound);
            },
            Not(inner) => inner.collect_free_vars(acc, bound),
        }
    }
}

impl PredArg {
    pub fn substitute_var(&self, old: &str, new: &str) -> Self {
        match self {
            PredArg::Var(v) if v == old => PredArg::Var(new.to_string()),
            other => other.clone(),
        }
    }
}

// ═════════════════════════════════════════════════════════════════════════
// `moniker::BoundTerm` impl — trivial leaf
// ═════════════════════════════════════════════════════════════════════════
//
// `BehavioralPred` is a passive data field on guarded receive
// constructors. It does NOT participate in host-category alpha-
// equivalence: variables inside a predicate (e.g., `halts(y)`
// referencing a pattern-bound `y`) are bound by the parent's
// `MatchBindings`, not by host-category `FreeVar<String>`s.
//
// We therefore implement `BoundTerm<String>` as a leaf — `term_eq`
// delegates to structural `PartialEq`, and `close_term`/`open_term`/
// `visit_vars`/`visit_mut_vars` are no-ops.
impl BoundTerm<String> for BehavioralPred {
    fn term_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }

    fn close_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_free: &impl moniker::OnFreeFn<String>,
    ) {
        // No host-category variables inside a predicate.
    }

    fn open_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_bound: &impl moniker::OnBoundFn<String>,
    ) {
        // No host-category variables inside a predicate.
    }

    fn visit_vars(&self, _on_var: &mut impl FnMut(&Var<String>)) {
        // No host-category variables inside a predicate.
    }

    fn visit_mut_vars(&mut self, _on_var: &mut impl FnMut(&mut Var<String>)) {
        // No host-category variables inside a predicate.
    }
}

impl QuantifiedDomain {
    fn substitute_var(&self, old: &str, new: &str) -> Self {
        match self {
            QuantifiedDomain::Named(n) => QuantifiedDomain::Named(n.clone()),
            QuantifiedDomain::Bounded(k) => QuantifiedDomain::Bounded(*k),
            QuantifiedDomain::Enumerated(es) => QuantifiedDomain::Enumerated(
                es.iter().map(|e| e.substitute_var(old, new)).collect(),
            ),
        }
    }

    fn collect_free_vars(
        &self,
        acc: &mut std::collections::HashSet<String>,
        bound: &std::collections::HashSet<String>,
    ) {
        if let QuantifiedDomain::Enumerated(es) = self {
            for e in es {
                if let PredArg::Var(v) = e {
                    if !bound.contains(v) {
                        acc.insert(v.clone());
                    }
                }
            }
        }
    }
}

// ═════════════════════════════════════════════════════════════════════════
// Display
// ═════════════════════════════════════════════════════════════════════════

impl fmt::Display for BehavioralPred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BehavioralPred::*;
        match self {
            // Display as "true()" (nullary RelationQuery form) so that the
            // parse→display roundtrip is stable: the guard parser always
            // produces RelationQuery for identifiers, so "true()" round-trips
            // as RelationQuery("true",[]) → "true()". Plain "true" would
            // re-display as "true()" after one parse round, breaking the
            // strong-roundtrip check in generated proptest strategies.
            Top => write!(f, "true()"),
            RelationQuery { relation_name, args, negated } => {
                if *negated {
                    write!(f, "not ")?;
                }
                write!(f, "{}(", relation_name)?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", a)?;
                }
                write!(f, ")")
            },
            Quantified { quantifier, var, domain, body } => {
                let q = match quantifier {
                    Quantifier::ForAll => "forall",
                    Quantifier::Exists => "exists",
                };
                write!(f, "{}({}", q, var)?;
                if let Some(d) = domain {
                    write!(f, ", {}", d)?;
                }
                write!(f, ", {})", body)
            },
            AcMatch { bag, elements, rest } => {
                write!(f, "ac_match({}, [", bag)?;
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                if let Some(r) = rest {
                    write!(f, ", ...{}", r)?;
                }
                write!(f, "])")
            },
            And(a, b) => write!(f, "({} and {})", a, b),
            Or(a, b) => write!(f, "({} or {})", a, b),
            Not(inner) => write!(f, "(not {})", inner),
            Implies(p, c) => write!(f, "({} entails {})", p, c),
        }
    }
}

impl fmt::Display for PredArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PredArg::Var(v) => write!(f, "{}", v),
            PredArg::IntLit(n) => write!(f, "{}", n),
            PredArg::StringLit(s) => write!(f, "\"{}\"", s),
        }
    }
}

impl fmt::Display for QuantifiedDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QuantifiedDomain::Named(n) => write!(f, "{}", n),
            QuantifiedDomain::Bounded(k) => write!(f, "{}", k),
            QuantifiedDomain::Enumerated(es) => {
                write!(f, "{{")?;
                for (i, e) in es.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, "}}")
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relation_query_display_roundtrip() {
        let p = BehavioralPred::RelationQuery {
            relation_name: "halts".to_string(),
            args: vec![PredArg::Var("x".to_string())],
            negated: false,
        };
        assert_eq!(p.to_string(), "halts(x)");
    }

    #[test]
    fn substitute_var_preserves_other_vars() {
        let p = BehavioralPred::RelationQuery {
            relation_name: "rel".to_string(),
            args: vec![PredArg::Var("x".to_string()), PredArg::Var("y".to_string())],
            negated: false,
        };
        let p2 = p.substitute_var("x", "z");
        match &p2 {
            BehavioralPred::RelationQuery { args, .. } => {
                assert!(matches!(&args[0], PredArg::Var(v) if v == "z"));
                assert!(matches!(&args[1], PredArg::Var(v) if v == "y"));
            },
            _ => panic!(),
        }
    }

    #[test]
    fn free_vars_excludes_quantified_var() {
        let p = BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: "y".to_string(),
            domain: None,
            body: Box::new(BehavioralPred::RelationQuery {
                relation_name: "safe".to_string(),
                args: vec![PredArg::Var("y".to_string()), PredArg::Var("z".to_string())],
                negated: false,
            }),
        };
        let fvs = p.free_vars();
        assert!(fvs.contains("z"));
        assert!(!fvs.contains("y"));
    }
}
