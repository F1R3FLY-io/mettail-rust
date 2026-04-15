//! Runtime behavioral predicate AST.
//!
//! This is the runtime-friendly counterpart to
//! `mettail_ast::language::BehavioralPred`. Where the AST type uses
//! `syn::Ident` (because it lives in a proc-macro-consuming crate that
//! reads from `ParseStream`), this type uses `String` so it can be
//! stored in generated runtime enum variants.
//!
//! The macro pipeline provides a `lower_to_runtime` helper (in
//! `mettail-macros::gen::runtime::predicate_lower`) that converts the
//! AST `BehavioralPred` into this runtime form at macro-expansion time.
//! The source-level parser in `mettail-prattail::parser::predicate`
//! produces values of this type directly from user source programs.
//!
//! ## Role at runtime
//!
//! The runtime `BehavioralPred` is a **passive data type**. It is NOT
//! an evaluator — there is no `evaluate()` method and no thread-local
//! snapshot. The predicated-types design specifies that all relation
//! lookups happen via **direct Ascent JOIN clauses** emitted by the
//! macro at compile time (see `mettail-macros::logic::rules::compile_guard_to_ascent_clauses`
//! and the per-relation specialization in §8.3 of
//! `docs/design/predicated-types.md`).
//!
//! This type exists so that:
//! - Generated term values can store per-instance predicates as data
//!   for shape-based dispatch and display.
//! - Tooling (REPL introspection, LSP, doc-gen, fuzzers) can read
//!   predicates programmatically.
//! - The `Display`, `Hash`, and `Eq` impls support hash-consing of
//!   terms that carry predicates.
//!
//! ## Semantics deferred to Ascent
//!
//! - `RelationQuery` — lowered to an Ascent join clause `rel(args)`
//!   in the rule body. Negation (`!rel(args)`) uses Ascent's
//!   stratified negation (Phase 3E).
//! - `Quantified { ForAll | Exists, ... }` — lowered via
//!   `prattail::logict::QuantifiedFormula` + `evaluate_quantified`,
//!   which is invoked from inside the generated rule body
//!   (Phase 6 for theory-guided evaluation).
//! - `AcMatch` — lowered to specialized Ascent code in
//!   `macros/src/logic/rules.rs` using
//!   `prattail::logict::multiset_partitions`.
//! - `And`, `Or`, `Not`, `Implies` — lowered via Boolean rewrites to
//!   DNF + one Ascent rule per clause (design §2 DNF normalization).
//! - `Top` — a placeholder used when the slot is declared at
//!   language-spec time but filled at source-parse time. Lowered as
//!   "no join clause" — the rule body has no guard.

use crate::binding::{BoundTerm, Var};
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
    /// Always true — used as a placeholder when the predicate slot is
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
            }
            AcMatch { bag, elements, rest } => AcMatch {
                bag: bag.substitute_var(old, new),
                elements: elements
                    .iter()
                    .map(|e| e.substitute_var(old, new))
                    .collect(),
                rest: rest.clone(),
            },
            And(a, b) => And(
                Box::new(a.substitute_var(old, new)),
                Box::new(b.substitute_var(old, new)),
            ),
            Or(a, b) => Or(
                Box::new(a.substitute_var(old, new)),
                Box::new(b.substitute_var(old, new)),
            ),
            Not(inner) => Not(Box::new(inner.substitute_var(old, new))),
            Implies(p, c) => Implies(
                Box::new(p.substitute_var(old, new)),
                Box::new(c.substitute_var(old, new)),
            ),
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
            Top => {}
            RelationQuery { args, .. } => {
                for a in args {
                    if let PredArg::Var(v) = a {
                        if !bound.contains(v) {
                            acc.insert(v.clone());
                        }
                    }
                }
            }
            Quantified { var, domain, body, .. } => {
                if let Some(d) = domain {
                    d.collect_free_vars(acc, bound);
                }
                let inserted = bound.insert(var.clone());
                body.collect_free_vars(acc, bound);
                if inserted {
                    bound.remove(var);
                }
            }
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
            }
            And(a, b) | Or(a, b) | Implies(a, b) => {
                a.collect_free_vars(acc, bound);
                b.collect_free_vars(acc, bound);
            }
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
// `visit_vars`/`visit_mut_vars` are no-ops. This mirrors how
// `CanonicalFloat64` (`runtime/src/canonical_float.rs:121`) treats
// itself as a leaf for moniker purposes.
//
// Phase 3A-A1 of the predicated-types implementation plan.
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
            }
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
            }
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
            }
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
            }
        }
    }
}

// ═════════════════════════════════════════════════════════════════════════
// Thread-local fact snapshot for runtime predicate evaluation
// ═════════════════════════════════════════════════════════════════════════
//
// Step 1.2 (guard-gated Comm): the Comm rule's `if { }` guard calls
// `evaluate_pred_with_bindings` which reads this thread-local snapshot
// to check whether a relation tuple exists. The snapshot is populated
// by the generated `run_ascent_typed_with_facts` BEFORE `prog.run()`.
//
// This is NOT the rejected Phase 4 RelationView — that was a broad
// relation-mirroring mechanism. This is a narrow, user-controlled,
// externally-populated fact store that the generated Comm rule
// consults. BehavioralPred remains passive: the evaluation function
// is freestanding, not a method on the type.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

thread_local! {
    static PRED_FACT_SNAPSHOT: RefCell<HashMap<String, HashSet<Vec<String>>>> =
        RefCell::new(HashMap::new());
}

/// Install a fact snapshot for the current thread. Called by generated
/// `run_ascent_typed_with_facts` before `prog.run()`.
pub fn set_pred_fact_snapshot(facts: HashMap<String, HashSet<Vec<String>>>) {
    PRED_FACT_SNAPSHOT.with(|snap| *snap.borrow_mut() = facts);
}

/// Clear the fact snapshot. Called after `prog.run()` returns.
pub fn clear_pred_fact_snapshot() {
    PRED_FACT_SNAPSHOT.with(|snap| snap.borrow_mut().clear());
}

/// Evaluate a per-instance `BehavioralPred` against the thread-local
/// fact snapshot, resolving `PredArg::Var` arguments via the provided
/// bindings.
///
/// `bindings` maps variable names (e.g., `"x"`) to their resolved
/// string values (e.g., `"0"` — the Display form of the received
/// term). The Comm rule codegen supplies bindings derived from the
/// continuation binder: `[(binder_pretty_name, format!("{}", received))]`.
///
/// This function is freestanding (not a method on BehavioralPred) so
/// the type remains passive per the design decision.
pub fn evaluate_pred_with_bindings(
    pred: &BehavioralPred,
    bindings: &[(String, String)],
) -> bool {
    match pred {
        BehavioralPred::Top => true,
        BehavioralPred::RelationQuery {
            relation_name,
            args,
            negated,
        } => {
            let resolved: Vec<String> = args
                .iter()
                .map(|a| match a {
                    PredArg::Var(v) => bindings
                        .iter()
                        .find(|(k, _)| k == v)
                        .map(|(_, val)| val.clone())
                        .unwrap_or_else(|| v.clone()),
                    PredArg::IntLit(n) => n.to_string(),
                    PredArg::StringLit(s) => s.clone(),
                })
                .collect();
            let hit = PRED_FACT_SNAPSHOT.with(|snap| {
                snap.borrow()
                    .get(relation_name)
                    .map(|tuples| tuples.contains(&resolved))
                    .unwrap_or(false)
            });
            if *negated { !hit } else { hit }
        }
        BehavioralPred::And(a, b) => {
            evaluate_pred_with_bindings(a, bindings)
                && evaluate_pred_with_bindings(b, bindings)
        }
        BehavioralPred::Or(a, b) => {
            evaluate_pred_with_bindings(a, bindings)
                || evaluate_pred_with_bindings(b, bindings)
        }
        BehavioralPred::Not(inner) => !evaluate_pred_with_bindings(inner, bindings),
        BehavioralPred::Implies(p, c) => {
            !evaluate_pred_with_bindings(p, bindings)
                || evaluate_pred_with_bindings(c, bindings)
        }
        // Quantified/AcMatch: conservatively true (Phase 6 follow-up)
        _ => true,
    }
}

// ═════════════════════════════════════════════════════════════════════════
// Tests
// ═════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> PredArg {
        PredArg::Var(name.to_string())
    }

    fn rel(name: &str, args: Vec<PredArg>) -> BehavioralPred {
        BehavioralPred::RelationQuery {
            relation_name: name.to_string(),
            args,
            negated: false,
        }
    }

    #[test]
    fn free_vars_simple() {
        let pred = BehavioralPred::And(
            Box::new(rel("halts", vec![var("x")])),
            Box::new(rel("safe", vec![var("y")])),
        );
        let fv = pred.free_vars();
        assert!(fv.contains("x"));
        assert!(fv.contains("y"));
        assert_eq!(fv.len(), 2);
    }

    #[test]
    fn free_vars_shadowed_by_quantifier() {
        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: "x".to_string(),
            domain: Some(QuantifiedDomain::Named("nodes".to_string())),
            body: Box::new(rel("safe", vec![var("x")])), // x is bound
        };
        let fv = pred.free_vars();
        assert!(fv.is_empty(), "x should be shadowed by the forall binder");
    }

    #[test]
    fn free_vars_from_enumerated_domain() {
        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: "y".to_string(),
            domain: Some(QuantifiedDomain::Enumerated(vec![
                var("a"),
                var("b"),
            ])),
            body: Box::new(rel("safe", vec![var("y")])),
        };
        let fv = pred.free_vars();
        assert!(fv.contains("a"));
        assert!(fv.contains("b"));
        assert!(!fv.contains("y"), "y should be shadowed");
    }

    #[test]
    fn substitute_var_rewrites_args() {
        let pred = rel("halts", vec![var("x")]);
        let substituted = pred.substitute_var("x", "x_fresh_0");
        let expected = BehavioralPred::RelationQuery {
            relation_name: "halts".to_string(),
            args: vec![PredArg::Var("x_fresh_0".to_string())],
            negated: false,
        };
        assert_eq!(substituted, expected);
    }

    #[test]
    fn substitute_var_respects_quantifier_shadowing() {
        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: "x".to_string(),
            domain: Some(QuantifiedDomain::Named("nodes".to_string())),
            body: Box::new(rel("safe", vec![var("x")])),
        };
        // Substituting `x` should be a no-op because it's shadowed.
        let substituted = pred.substitute_var("x", "x_fresh_0");
        assert_eq!(substituted, pred);
    }

    #[test]
    fn substitute_var_rewrites_enumerated_domain() {
        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::Exists,
            var: "y".to_string(),
            domain: Some(QuantifiedDomain::Enumerated(vec![var("a")])),
            body: Box::new(rel("safe", vec![var("y")])),
        };
        let substituted = pred.substitute_var("a", "a_fresh");
        match substituted {
            BehavioralPred::Quantified { domain: Some(QuantifiedDomain::Enumerated(es)), .. } => {
                assert_eq!(es, vec![PredArg::Var("a_fresh".to_string())]);
            }
            _ => panic!("expected Quantified/Enumerated after substitution"),
        }
    }

    #[test]
    fn substitute_var_propagates_through_and() {
        let pred = BehavioralPred::And(
            Box::new(rel("halts", vec![var("x")])),
            Box::new(rel("safe", vec![var("x")])),
        );
        let substituted = pred.substitute_var("x", "x_fresh_0");
        let expected = BehavioralPred::And(
            Box::new(BehavioralPred::RelationQuery {
                relation_name: "halts".to_string(),
                args: vec![PredArg::Var("x_fresh_0".to_string())],
                negated: false,
            }),
            Box::new(BehavioralPred::RelationQuery {
                relation_name: "safe".to_string(),
                args: vec![PredArg::Var("x_fresh_0".to_string())],
                negated: false,
            }),
        );
        assert_eq!(substituted, expected);
    }

    #[test]
    fn display_top() {
        // Top displays as "true()" (nullary RelationQuery form) to ensure the
        // parse→display roundtrip is stable: the guard parser produces
        // RelationQuery for any ident, so "true()" → RelationQuery("true",[])
        // → "true()" is idempotent.
        assert_eq!(format!("{}", BehavioralPred::Top), "true()");
    }

    #[test]
    fn display_relation_query() {
        let pred = rel("halts", vec![var("x")]);
        assert_eq!(format!("{}", pred), "halts(x)");
    }

    #[test]
    fn display_negated_relation_query() {
        let pred = BehavioralPred::RelationQuery {
            relation_name: "halts".to_string(),
            args: vec![var("x")],
            negated: true,
        };
        assert_eq!(format!("{}", pred), "not halts(x)");
    }

    #[test]
    fn display_conjunction() {
        let pred = BehavioralPred::And(
            Box::new(rel("halts", vec![var("x")])),
            Box::new(rel("safe", vec![var("x")])),
        );
        assert_eq!(format!("{}", pred), "(halts(x) and safe(x))");
    }

    #[test]
    fn display_quantified() {
        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: "y".to_string(),
            domain: Some(QuantifiedDomain::Named("nodes".to_string())),
            body: Box::new(rel("safe", vec![var("y")])),
        };
        assert_eq!(format!("{}", pred), "forall(y, nodes, safe(y))");
    }

    #[test]
    fn hash_and_eq_consistent() {
        use std::collections::HashSet;
        let pred_a = rel("halts", vec![var("x")]);
        let pred_b = rel("halts", vec![var("x")]);
        let pred_c = rel("halts", vec![var("y")]);

        let mut set = HashSet::new();
        set.insert(pred_a.clone());
        assert!(set.contains(&pred_b), "equal preds must hash the same");
        assert!(!set.contains(&pred_c), "distinct preds must differ");
    }

    // ── Step 1.2: evaluate_pred_with_bindings tests ──

    #[test]
    fn eval_top_is_always_true() {
        clear_pred_fact_snapshot();
        assert!(evaluate_pred_with_bindings(&BehavioralPred::Top, &[]));
    }

    #[test]
    fn eval_relation_query_hits_snapshot() {
        let mut facts = std::collections::HashMap::new();
        let mut tuples = std::collections::HashSet::new();
        tuples.insert(vec!["0".to_string()]);
        facts.insert("halts".to_string(), tuples);
        set_pred_fact_snapshot(facts);

        let pred = rel("halts", vec![var("x")]);
        assert!(evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
        clear_pred_fact_snapshot();
    }

    #[test]
    fn eval_relation_query_misses_snapshot() {
        clear_pred_fact_snapshot();
        let pred = rel("halts", vec![var("x")]);
        assert!(!evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
    }

    #[test]
    fn eval_negated_relation_inverts() {
        clear_pred_fact_snapshot();
        let pred = BehavioralPred::RelationQuery {
            relation_name: "halts".to_string(),
            args: vec![PredArg::Var("x".to_string())],
            negated: true,
        };
        // Empty snapshot → query returns false → negation returns true
        assert!(evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
    }

    #[test]
    fn eval_and_both_must_hold() {
        let mut facts = std::collections::HashMap::new();
        let mut h = std::collections::HashSet::new();
        h.insert(vec!["0".to_string()]);
        facts.insert("halts".to_string(), h);
        // safe is NOT seeded
        set_pred_fact_snapshot(facts);

        let pred = BehavioralPred::And(
            Box::new(rel("halts", vec![var("x")])),
            Box::new(rel("safe", vec![var("x")])),
        );
        assert!(!evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
        clear_pred_fact_snapshot();
    }

    #[test]
    fn eval_or_either_suffices() {
        let mut facts = std::collections::HashMap::new();
        let mut h = std::collections::HashSet::new();
        h.insert(vec!["0".to_string()]);
        facts.insert("halts".to_string(), h);
        set_pred_fact_snapshot(facts);

        let pred = BehavioralPred::Or(
            Box::new(rel("halts", vec![var("x")])),
            Box::new(rel("safe", vec![var("x")])),
        );
        assert!(evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
        clear_pred_fact_snapshot();
    }
}
