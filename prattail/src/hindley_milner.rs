//! Hindley-Milner type system scaffold (Phase 12 of the
//! predicated-types implementation plan).
//!
//! This module provides a `HindleyMilnerTypeSystem` that implements
//! the `TypeSystem` trait. It supports:
//!
//! - Monomorphic and polymorphic types (`HmType::Mono`, `HmType::Var`,
//!   `HmType::Forall`)
//! - Function types (`HmType::Arrow`)
//! - Algorithm W unification with occurs check
//! - `infer_simple_let` — single `let x = e1 in e2` inference
//!
//! ## Scope
//!
//! Phase 12 is a **scaffold**, not a complete Algorithm W. The
//! `infer` method handles:
//! - Variables (lookup in env)
//! - Literals (unit, int, bool, string)
//! - Lambda abstractions (introduce fresh type variable, infer body)
//! - Function applications (unify domain/codomain)
//! - `let x = e1 in e2` via `infer_simple_let`
//!
//! Full let-polymorphism with generalization and instantiation is a
//! follow-up — `infer_simple_let` handles the simplest case (the
//! body's type is the let-binding's inferred type, no generalization).
//!
//! The `TypeSystem` trait surface is satisfied so user-defined
//! languages can plug in HM as their type system via the
//! `TypeSystemAlgebra<S>` SFA bridge (defined in `type_system.rs`).

use crate::type_system::TypeSystem;
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Hindley-Milner type representation.
///
/// Supports type variables (introduced by lambda binding), monomorphic
/// base types, function types, and let-polymorphic universal types.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum HmType {
    /// Type variable: `α`, `β`, `γ`. Represented as a unique string
    /// identifier (typically `t0`, `t1`, ... from `fresh_type_var`).
    Var(String),
    /// Monomorphic base type: `Int`, `Bool`, `String`, `Unit`, `Float`,
    /// or any user-declared atomic type.
    Mono(String),
    /// Function type: `α → β`.
    Arrow(Box<HmType>, Box<HmType>),
    /// Universally quantified type scheme: `∀α₁...αₙ. τ`.
    /// Created by let-generalization, instantiated at use sites.
    Forall(Vec<String>, Box<HmType>),
}

impl HmType {
    /// Construct a monomorphic type by name.
    pub fn mono(name: &str) -> Self {
        HmType::Mono(name.to_string())
    }

    /// Construct a type variable by name.
    pub fn var(name: &str) -> Self {
        HmType::Var(name.to_string())
    }

    /// Construct a function type `a → b`.
    pub fn arrow(a: HmType, b: HmType) -> Self {
        HmType::Arrow(Box::new(a), Box::new(b))
    }

    /// Universally quantify over the given type variables.
    pub fn forall(vars: Vec<String>, body: HmType) -> Self {
        if vars.is_empty() {
            body
        } else {
            HmType::Forall(vars, Box::new(body))
        }
    }

    /// Collect every type variable that appears free in this type.
    pub fn free_type_vars(&self) -> Vec<String> {
        let mut acc = Vec::new();
        let mut bound = Vec::new();
        self.collect_free_tvs(&mut acc, &mut bound);
        acc.sort();
        acc.dedup();
        acc
    }

    fn collect_free_tvs(&self, acc: &mut Vec<String>, bound: &mut Vec<String>) {
        match self {
            HmType::Var(v) => {
                if !bound.contains(v) {
                    acc.push(v.clone());
                }
            },
            HmType::Mono(_) => {},
            HmType::Arrow(a, b) => {
                a.collect_free_tvs(acc, bound);
                b.collect_free_tvs(acc, bound);
            },
            HmType::Forall(vars, body) => {
                for v in vars {
                    bound.push(v.clone());
                }
                body.collect_free_tvs(acc, bound);
                for _ in vars {
                    bound.pop();
                }
            },
        }
    }
}

/// A substitution: maps type variable names to types.
///
/// Substitutions form a monoid under composition. The identity is
/// the empty substitution; composition is `compose(s2, s1)` =
/// "apply s1 then s2", where applying a substitution replaces every
/// `Var(v)` with `subst[v]` if present.
#[derive(Clone, Debug, Default)]
pub struct Substitution {
    bindings: HashMap<String, HmType>,
}

impl Substitution {
    /// The identity substitution.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Apply this substitution to a type.
    pub fn apply(&self, ty: &HmType) -> HmType {
        match ty {
            HmType::Var(v) => self.bindings.get(v).cloned().unwrap_or_else(|| ty.clone()),
            HmType::Mono(_) => ty.clone(),
            HmType::Arrow(a, b) => HmType::Arrow(Box::new(self.apply(a)), Box::new(self.apply(b))),
            HmType::Forall(vars, body) => {
                // Drop any binding for a quantified variable before
                // descending — the universal binder shadows the
                // substitution.
                let mut shadowed = self.clone();
                for v in vars {
                    shadowed.bindings.remove(v);
                }
                HmType::Forall(vars.clone(), Box::new(shadowed.apply(body)))
            },
        }
    }

    /// Insert a single binding `var ↦ ty`.
    pub fn insert(&mut self, var: String, ty: HmType) {
        self.bindings.insert(var, ty);
    }

    /// Compose two substitutions: `compose(s2, s1)` = "apply s1 then s2".
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = Substitution::empty();
        for (k, v) in &other.bindings {
            result.bindings.insert(k.clone(), self.apply(v));
        }
        for (k, v) in &self.bindings {
            result
                .bindings
                .entry(k.clone())
                .or_insert_with(|| v.clone());
        }
        result
    }
}

/// Errors arising from HM type inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HmError {
    /// Unification failed: the two types are structurally incompatible.
    UnificationFailure { left: HmType, right: HmType },
    /// Occurs check failed: the variable would appear inside its own
    /// solution, producing an infinite type.
    OccursCheck { var: String, ty: HmType },
    /// A reference to an unknown variable.
    UnboundVariable { name: String },
}

impl std::fmt::Display for HmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HmError::UnificationFailure { left, right } => {
                write!(f, "HM unification failure: cannot unify {:?} with {:?}", left, right)
            },
            HmError::OccursCheck { var, ty } => {
                write!(f, "HM occurs check: type variable `{}` appears in {:?}", var, ty)
            },
            HmError::UnboundVariable { name } => {
                write!(f, "HM unbound variable: {}", name)
            },
        }
    }
}

impl std::error::Error for HmError {}

/// Algorithm W unification: produce a substitution that makes
/// `left` and `right` syntactically equal, or fail with a structured
/// error.
pub fn unify(left: &HmType, right: &HmType) -> Result<Substitution, HmError> {
    match (left, right) {
        (HmType::Var(a), HmType::Var(b)) if a == b => Ok(Substitution::empty()),
        (HmType::Var(v), other) | (other, HmType::Var(v)) => {
            if other.free_type_vars().contains(v) {
                Err(HmError::OccursCheck { var: v.clone(), ty: other.clone() })
            } else {
                let mut s = Substitution::empty();
                s.insert(v.clone(), other.clone());
                Ok(s)
            }
        },
        (HmType::Mono(a), HmType::Mono(b)) if a == b => Ok(Substitution::empty()),
        (HmType::Arrow(a1, b1), HmType::Arrow(a2, b2)) => {
            let s1 = unify(a1, a2)?;
            let b1_sub = s1.apply(b1);
            let b2_sub = s1.apply(b2);
            let s2 = unify(&b1_sub, &b2_sub)?;
            Ok(s2.compose(&s1))
        },
        _ => Err(HmError::UnificationFailure { left: left.clone(), right: right.clone() }),
    }
}

/// HM term representation for inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HmTerm {
    /// Variable reference.
    Var(String),
    /// Lambda abstraction: `λx. body`.
    Abs { param: String, body: Box<HmTerm> },
    /// Function application: `f arg`.
    App { f: Box<HmTerm>, arg: Box<HmTerm> },
    /// Let binding: `let x = e1 in e2`.
    Let {
        name: String,
        value: Box<HmTerm>,
        body: Box<HmTerm>,
    },
    /// Integer literal.
    LitInt(i64),
    /// Boolean literal.
    LitBool(bool),
    /// String literal.
    LitStr(String),
}

/// Type environment for HM: maps variable names to type schemes.
#[derive(Debug, Clone, Default)]
pub struct HmEnv {
    bindings: HashMap<String, HmType>,
}

impl HmEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn extend(&self, name: &str, ty: HmType) -> Self {
        let mut new_env = self.clone();
        new_env.bindings.insert(name.to_string(), ty);
        new_env
    }

    pub fn lookup(&self, name: &str) -> Option<&HmType> {
        self.bindings.get(name)
    }

    pub fn apply_subst(&self, s: &Substitution) -> Self {
        let bindings = self
            .bindings
            .iter()
            .map(|(k, v)| (k.clone(), s.apply(v)))
            .collect();
        HmEnv { bindings }
    }
}

/// Fresh type variable generator.
static FRESH_COUNTER: AtomicUsize = AtomicUsize::new(0);

pub fn fresh_type_var() -> HmType {
    let n = FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
    HmType::Var(format!("t{}", n))
}

/// Algorithm W inference (single-pass, no generalization).
///
/// Returns `(substitution, inferred_type)`. The substitution must be
/// applied to any external state that references the input env's
/// types.
pub fn infer(env: &HmEnv, term: &HmTerm) -> Result<(Substitution, HmType), HmError> {
    match term {
        HmTerm::LitInt(_) => Ok((Substitution::empty(), HmType::mono("Int"))),
        HmTerm::LitBool(_) => Ok((Substitution::empty(), HmType::mono("Bool"))),
        HmTerm::LitStr(_) => Ok((Substitution::empty(), HmType::mono("String"))),

        HmTerm::Var(name) => env
            .lookup(name)
            .cloned()
            .map(|ty| (Substitution::empty(), ty))
            .ok_or_else(|| HmError::UnboundVariable { name: name.clone() }),

        HmTerm::Abs { param, body } => {
            let param_ty = fresh_type_var();
            let inner_env = env.extend(param, param_ty.clone());
            let (s, body_ty) = infer(&inner_env, body)?;
            let param_ty_sub = s.apply(&param_ty);
            Ok((s, HmType::arrow(param_ty_sub, body_ty)))
        },

        HmTerm::App { f, arg } => {
            let (s1, f_ty) = infer(env, f)?;
            let env_after = env.apply_subst(&s1);
            let (s2, arg_ty) = infer(&env_after, arg)?;
            let result_ty = fresh_type_var();
            let f_ty_sub = s2.apply(&f_ty);
            let expected = HmType::arrow(arg_ty, result_ty.clone());
            let s3 = unify(&f_ty_sub, &expected)?;
            let final_subst = s3.compose(&s2.compose(&s1));
            let final_result_ty = s3.apply(&result_ty);
            Ok((final_subst, final_result_ty))
        },

        HmTerm::Let { name, value, body } => infer_simple_let(env, name, value, body),
    }
}

/// Phase 12B: simplest let-binding inference.
///
/// Infers `value`'s type, extends the environment with the binding,
/// then infers `body`'s type. NO generalization is performed — the
/// inferred type of `value` is used as a monotype. Full
/// let-polymorphism (generalize free vars at let, instantiate at use)
/// is the documented Phase 12 follow-up.
pub fn infer_simple_let(
    env: &HmEnv,
    name: &str,
    value: &HmTerm,
    body: &HmTerm,
) -> Result<(Substitution, HmType), HmError> {
    let (s1, value_ty) = infer(env, value)?;
    let env_after = env.apply_subst(&s1).extend(name, value_ty);
    let (s2, body_ty) = infer(&env_after, body)?;
    Ok((s2.compose(&s1), body_ty))
}

// ════════════════════════════════════════════════════════════════════
// TypeSystem trait implementation
// ════════════════════════════════════════════════════════════════════

/// Hindley-Milner type system.
///
/// Implements `TypeSystem` so user-defined languages can plug in
/// HM via `TypeSystemAlgebra<S>` (the SFA bridge in
/// `type_system.rs`). Phase 12 covers the trait surface; full
/// integration with the macro pipeline is a follow-up.
#[derive(Clone, Debug, Default)]
pub struct HindleyMilnerTypeSystem;

impl HindleyMilnerTypeSystem {
    pub fn new() -> Self {
        Self
    }
}

impl TypeSystem for HindleyMilnerTypeSystem {
    type Type = HmType;
    type TypeEnv = HmEnv;
    type Term = HmTerm;

    fn empty_env(&self) -> Self::TypeEnv {
        HmEnv::new()
    }

    fn check(&self, env: &Self::TypeEnv, term: &Self::Term, ty: &Self::Type) -> bool {
        match infer(env, term) {
            Ok((_, inferred)) => unify(&inferred, ty).is_ok(),
            Err(_) => false,
        }
    }

    fn infer(&self, env: &Self::TypeEnv, term: &Self::Term) -> Vec<Self::Type> {
        match infer(env, term) {
            Ok((_, ty)) => vec![ty],
            Err(_) => vec![],
        }
    }

    fn is_subtype(&self, _env: &Self::TypeEnv, sub: &Self::Type, sup: &Self::Type) -> bool {
        // HM has no proper subtyping — types are equal iff they
        // unify. Forall types are instantiated to a unifiable monotype.
        unify(sub, sup).is_ok()
    }

    fn join(&self, _env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type> {
        // HM join = unification: the most general unifier IS the
        // least common supertype because there is no subtyping.
        unify(a, b).ok().map(|s| s.apply(a))
    }

    fn meet(&self, _env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type> {
        // HM meet = unification (same as join — no subtyping).
        unify(a, b).ok().map(|s| s.apply(a))
    }

    fn extend(&self, env: &Self::TypeEnv, var: &str, ty: &Self::Type) -> Self::TypeEnv {
        env.extend(var, ty.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unify_identical_monotypes() {
        let t = HmType::mono("Int");
        let s = unify(&t, &t).expect("should unify");
        assert!(s.bindings.is_empty());
    }

    #[test]
    fn unify_distinct_monotypes_fails() {
        let result = unify(&HmType::mono("Int"), &HmType::mono("Bool"));
        assert!(matches!(result, Err(HmError::UnificationFailure { .. })));
    }

    #[test]
    fn unify_var_with_monotype() {
        let result = unify(&HmType::var("a"), &HmType::mono("Int"));
        let s = result.expect("should unify");
        assert_eq!(s.apply(&HmType::var("a")), HmType::mono("Int"));
    }

    #[test]
    fn unify_arrows_recursively() {
        // (a → Int) ⊥ (Bool → b)
        let left = HmType::arrow(HmType::var("a"), HmType::mono("Int"));
        let right = HmType::arrow(HmType::mono("Bool"), HmType::var("b"));
        let s = unify(&left, &right).expect("should unify");
        assert_eq!(s.apply(&HmType::var("a")), HmType::mono("Bool"));
        assert_eq!(s.apply(&HmType::var("b")), HmType::mono("Int"));
    }

    #[test]
    fn occurs_check_detects_infinite_type() {
        // a ⊥ (a → Int) should fail occurs check
        let left = HmType::var("a");
        let right = HmType::arrow(HmType::var("a"), HmType::mono("Int"));
        let result = unify(&left, &right);
        assert!(matches!(result, Err(HmError::OccursCheck { .. })));
    }

    #[test]
    fn infer_int_literal_is_int() {
        let env = HmEnv::new();
        let (_, ty) = infer(&env, &HmTerm::LitInt(42)).unwrap();
        assert_eq!(ty, HmType::mono("Int"));
    }

    #[test]
    fn infer_lambda_yields_arrow() {
        // λx. x — should give a → a
        let env = HmEnv::new();
        let term = HmTerm::Abs {
            param: "x".to_string(),
            body: Box::new(HmTerm::Var("x".to_string())),
        };
        let (_, ty) = infer(&env, &term).unwrap();
        match ty {
            HmType::Arrow(a, b) => assert_eq!(*a, *b),
            other => panic!("expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn infer_application_unifies() {
        // (λx. x) 42 should give Int
        let env = HmEnv::new();
        let id = HmTerm::Abs {
            param: "x".to_string(),
            body: Box::new(HmTerm::Var("x".to_string())),
        };
        let term = HmTerm::App {
            f: Box::new(id),
            arg: Box::new(HmTerm::LitInt(42)),
        };
        let (_, ty) = infer(&env, &term).unwrap();
        assert_eq!(ty, HmType::mono("Int"));
    }

    #[test]
    fn infer_simple_let_binds_value_type() {
        // let x = 42 in x — should give Int
        let env = HmEnv::new();
        let term = HmTerm::Let {
            name: "x".to_string(),
            value: Box::new(HmTerm::LitInt(42)),
            body: Box::new(HmTerm::Var("x".to_string())),
        };
        let (_, ty) = infer(&env, &term).unwrap();
        assert_eq!(ty, HmType::mono("Int"));
    }

    #[test]
    fn type_system_trait_check_works() {
        let hm = HindleyMilnerTypeSystem::new();
        let env = hm.empty_env();
        let term = HmTerm::LitBool(true);
        assert!(hm.check(&env, &term, &HmType::mono("Bool")));
        assert!(!hm.check(&env, &term, &HmType::mono("Int")));
    }

    #[test]
    fn type_system_trait_infer_returns_singleton() {
        let hm = HindleyMilnerTypeSystem::new();
        let env = hm.empty_env();
        let inferred = hm.infer(&env, &HmTerm::LitInt(7));
        assert_eq!(inferred, vec![HmType::mono("Int")]);
    }

    #[test]
    fn substitution_compose_is_associative() {
        // s1 maps a → Int. s2 maps b → a.
        // We want a substitution that, when applied to `b`, yields
        // Int. The convention `s.compose(other)` here means "apply
        // other then self": for each (k, v) in other, the result
        // binds k to s.apply(v). So `s1.compose(&s2)` produces
        // {b ↦ s1.apply(a) = Int} ∪ {a ↦ Int} — applying it to `b`
        // yields `Int`.
        let mut s1 = Substitution::empty();
        s1.insert("a".to_string(), HmType::mono("Int"));
        let mut s2 = Substitution::empty();
        s2.insert("b".to_string(), HmType::var("a"));

        let composed = s1.compose(&s2);
        assert_eq!(composed.apply(&HmType::var("b")), HmType::mono("Int"));
    }

    #[test]
    fn forall_free_vars_excluded() {
        let ty = HmType::Forall(
            vec!["a".to_string()],
            Box::new(HmType::arrow(HmType::var("a"), HmType::var("b"))),
        );
        let free = ty.free_type_vars();
        assert_eq!(free, vec!["b".to_string()]);
    }
}
