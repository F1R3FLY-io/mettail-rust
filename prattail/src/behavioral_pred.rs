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
//! `BehavioralPred` is a **passive carrier type** — no `evaluate()` method
//! and no thread-local snapshot of its own. The thread-local fact snapshot and
//! `evaluate_pred_with_bindings` live in `runtime/src/behavioral_pred.rs`
//! (the runtime crate re-exports these types).
//!
//! ## How the fragments are evaluated (post-P6)
//!
//! For **WPDA refinement guards** (`{x:Sort | pred}`), `wpda_codegen::refinement`
//! lowers the predicate to a call into the runtime evaluator:
//! - `RelationQuery` — `evaluate_pred_with_bindings` against the fact snapshot.
//! - `Quantified { ForAll | Exists, ... }` — `prattail::logict::QuantifiedFormula`
//!   + `evaluate_quantified`.
//! - `AcMatch` — `prattail::logict::multiset_partitions` (a structural/spatial
//!   match; in the OSLF split this is the *structural* leg).
//! - `And`, `Or`, `Not`, `Implies`, `Top` — Boolean combination over the above.
//!
//! For **Rho-backed guarded COMM**, the predicate is instead enforced host-side
//! at COMM time (RSpace structural matching, a Rholang `where` boolean guard, or
//! a host-routed `RhoNativeJoin`); the compile-time substrate classifies only.
//! (The legacy Ascent Datalog join-clause lowering was retired in P6.)

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
// OSLF Phase 9 `.0`-inert: carrier → decider canonical lowering
// ═════════════════════════════════════════════════════════════════════════
//
// `BehavioralPred` (this module — the runtime CARRIER produced by the WPDA
// walker) and `crate::behavioral_algebra::BehavioralFormula` (the DECIDER, the
// `algebra_tower`-backed relational classifier) are two representations of the
// same behavioral-predicate concept. `to_behavioral_formula` is the
// PROVEN-CANONICAL bridge that lowers the carrier into the decider's RELATIONAL
// fragment so the decider's `decidability_tier()` can classify a carrier
// predicate directly.
//
// Parity-safety (the load-bearing fact): the lowering image is the relational
// fragment ONLY — it never emits a modal operator (`Diamond`/`BoxAll`/`Mu`/
// `Nu`/`Atom`/`FixVar`). Therefore every lowered formula's `decidability_tier()`
// is `T1` (`CompileTimeDecidable`, iff the carrier is exactly `Top`) or `T2`
// (`RuntimeDecidable`, for everything else that lowers) — NEVER `T3`. The
// structural `AcMatch` leg fails closed to `None` (it has no relational image),
// recursively, mirroring both the runtime evaluator's fail-closed `AcMatch` arm
// and the symbolic syn-twin's rejection of the structural leg.
//
// `.0`-inert: this is a foundation with NO live caller. The eval-path
// unification (routing `evaluate_pred_with_bindings` through the lowered
// decider) is a deferred increment; the runtime evaluator is UNTOUCHED.
impl BehavioralPred {
    /// Lower this runtime carrier predicate into the decider's relational
    /// fragment (`crate::behavioral_algebra::BehavioralFormula`).
    ///
    /// Returns `None` iff the predicate contains an `AcMatch` anywhere (the
    /// structural leg has no relational image — fail closed, mirroring the
    /// runtime evaluator's `AcMatch ⇒ false` arm). Every `Some(_)` image is in
    /// the **relational** fragment, so its `decidability_tier()` is `T1`/`T2`,
    /// never `T3` (the parity-safe invariant).
    ///
    /// Mapping (each arm preserves the runtime evaluator's semantics in
    /// `runtime/src/behavioral_pred.rs::eval_pred`):
    /// - `RelationQuery { negated: false }` → `Relation` (H1 base case).
    /// - `RelationQuery { negated: true }`  → `Not(Relation)` (H1: the
    ///   `negated` flag becomes an outer `Not` wrapper — exactly the
    ///   evaluator's `if *negated { !hit }`).
    /// - `Quantified { ForAll, .. }` → `Forall`; `{ Exists, .. }` → `Exists`
    ///   (H2: domain mapped by `QuantifiedDomain::to_qdomain`).
    /// - `And`/`Or`/`Not` map homomorphically.
    /// - `Implies(a, b)` → `Or(Not(a), b)` (H4: reject-safe De Morgan
    ///   `a → b ≡ ¬a ∨ b`, matching the evaluator's `!eval(a) || eval(b)`).
    /// - `Top` → `BehavioralFormula::Top` (H5: the algebra's own ⊤, NOT a
    ///   `"true"`/`"__top__"` relation atom — the syn-twin's
    ///   relation-encoding divergence is deliberately NOT copied).
    /// - `AcMatch { .. }` → `None` (H6: structural leg, fail closed).
    pub fn to_behavioral_formula(&self) -> Option<crate::behavioral_algebra::BehavioralFormula> {
        use crate::behavioral_algebra::BehavioralFormula as F;
        use BehavioralPred::*;
        match self {
            // H5: map to the decider's own ⊤. (The `symbolic` syn-twin encodes
            // ⊤ as a nullary `"true"` relation; that is its divergence — here ⊤
            // lowers to `F::Top`, which `decidability_tier()` classifies T1.)
            Top => Some(F::Top),
            RelationQuery { relation_name, args, negated } => {
                let rel = F::Relation {
                    name: relation_name.clone(),
                    args: args.iter().map(PredArg::to_arg).collect(),
                };
                // H1: the stratified-negation flag becomes an outer `Not`.
                if *negated {
                    Some(F::Not(Box::new(rel)))
                } else {
                    Some(rel)
                }
            },
            Quantified { quantifier, var, domain, body } => {
                let body = Box::new(body.to_behavioral_formula()?);
                let qdomain = QuantifiedDomain::to_qdomain(domain.as_ref());
                // H2: ForAll → Forall, Exists → Exists.
                match quantifier {
                    Quantifier::ForAll => {
                        Some(F::Forall { var: var.clone(), domain: qdomain, body })
                    },
                    Quantifier::Exists => {
                        Some(F::Exists { var: var.clone(), domain: qdomain, body })
                    },
                }
            },
            And(a, b) => Some(F::And(
                Box::new(a.to_behavioral_formula()?),
                Box::new(b.to_behavioral_formula()?),
            )),
            Or(a, b) => Some(F::Or(
                Box::new(a.to_behavioral_formula()?),
                Box::new(b.to_behavioral_formula()?),
            )),
            Not(inner) => Some(F::Not(Box::new(inner.to_behavioral_formula()?))),
            // H4: a → b ≡ ¬a ∨ b — matches the evaluator's `!eval(p) || eval(c)`.
            Implies(p, c) => Some(F::Or(
                Box::new(F::Not(Box::new(p.to_behavioral_formula()?))),
                Box::new(c.to_behavioral_formula()?),
            )),
            // H6: structural leg — fail closed (no relational image). The `?`
            // operators above propagate this `None` out of any enclosing arm.
            AcMatch { .. } => None,
        }
    }

    /// The decidability tier of this carrier predicate, read off its lowered
    /// decider image. `None` exactly when `to_behavioral_formula` is `None`
    /// (an `AcMatch` is present). Always `Some(T1)` (iff `Top`) or `Some(T2)` —
    /// never `Some(T3)` (the lowering never produces a modal formula).
    pub fn behavioral_tier(&self) -> Option<crate::symbolic::DecidabilityTier> {
        self.to_behavioral_formula().map(|f| f.decidability_tier())
    }
}

impl PredArg {
    /// Lower a carrier argument into a decider `Arg`.
    ///
    /// H3: an `IntLit(n)` renders as `Arg::Lit(n.to_string())` — the SAME
    /// decimal rendering the runtime evaluator uses (`PredArg::IntLit(n) =>
    /// n.to_string()` in `eval_pred`), so a lowered literal atom resolves to
    /// the identical tuple string the evaluator would match.
    fn to_arg(&self) -> crate::behavioral_algebra::Arg {
        use crate::behavioral_algebra::Arg;
        match self {
            PredArg::Var(v) => Arg::Var(v.clone()),
            PredArg::IntLit(n) => Arg::Lit(n.to_string()),
            PredArg::StringLit(s) => Arg::Lit(s.clone()),
        }
    }
}

impl QuantifiedDomain {
    /// Lower a carrier quantifier domain into the closest FAITHFUL decider
    /// `QDomain`. `None` (an inferred domain) maps to `QDomain::Active`.
    ///
    /// HAZARD H2 — eval-level domain gaps (NOT relied on for the tier, which is
    /// shape-only; these are deferred to the eval-path unification increment):
    /// - `Named(rel)` → `RelationColumn(rel, 0)`. The runtime evaluator's
    ///   `Named` enumerates column 0 of `rel` (`relation_first_column`), so
    ///   `RelationColumn(rel, 0)` is the FAITHFUL map — NOT `Active`.
    /// - `Enumerated(args)` → `Values(args rendered to strings)`. The runtime
    ///   evaluator LATE-BINDS each element against the live env
    ///   (`resolve_arg`); at lowering time there is no env, so a `Var(v)`
    ///   element is rendered as its name `v`. For ground (literal) enumerations
    ///   this is exact; for variable elements it is an over-approximation of the
    ///   eval-time value set. GAP: late binding is not reproduced here.
    /// - `Bounded(k)` → `Bounded(Box::new(Active), k)`. The runtime evaluator
    ///   INFERS the inner set from the body's relation occurrences
    ///   (`infer_domain_values`) then truncates to `k`; the decider has no body-
    ///   inference, so the inner domain is approximated by `Active` (the active
    ///   domain of the fact base) before the same `k` truncation. GAP: the
    ///   inferred inner set is approximated by `Active`.
    /// - `None` → `Active`. The runtime evaluator infers the set from the body;
    ///   the decider approximates by the active domain. GAP: same as `Bounded`.
    fn to_qdomain(domain: Option<&Self>) -> crate::behavioral_algebra::QDomain {
        use crate::behavioral_algebra::QDomain;
        match domain {
            Some(QuantifiedDomain::Named(rel)) => QDomain::RelationColumn(rel.clone(), 0),
            Some(QuantifiedDomain::Enumerated(args)) => {
                QDomain::Values(args.iter().map(PredArg::to_qdomain_value).collect())
            },
            Some(QuantifiedDomain::Bounded(k)) => QDomain::Bounded(Box::new(QDomain::Active), *k),
            None => QDomain::Active,
        }
    }
}

impl PredArg {
    /// Render an enumerated-domain element to its decider domain-value string.
    /// Ground literals render exactly as the runtime evaluator's `resolve_arg`
    /// would with an empty env; a `Var(v)` renders as its name `v` (the
    /// late-binding gap documented in `QuantifiedDomain::to_qdomain` HAZARD H2).
    fn to_qdomain_value(&self) -> String {
        match self {
            PredArg::Var(v) => v.clone(),
            PredArg::IntLit(n) => n.to_string(),
            PredArg::StringLit(s) => s.clone(),
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
