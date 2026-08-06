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

#[path = "hindley_milner/lifecycle.rs"]
mod lifecycle;

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
        enum Task<'ty> {
            Visit(&'ty HmType),
            RestoreBound(usize),
        }
        let mut tasks = vec![Task::Visit(self)];
        let mut bound = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(HmType::Var(name)) => {
                    if !bound.contains(&name.as_str()) {
                        acc.push(name.clone());
                    }
                },
                Task::Visit(HmType::Mono(_)) => {},
                Task::Visit(HmType::Arrow(domain, codomain)) => {
                    tasks.push(Task::Visit(codomain));
                    tasks.push(Task::Visit(domain));
                },
                Task::Visit(HmType::Forall(vars, body)) => {
                    let old_len = bound.len();
                    bound.extend(vars.iter().map(String::as_str));
                    tasks.push(Task::RestoreBound(old_len));
                    tasks.push(Task::Visit(body));
                },
                Task::RestoreBound(old_len) => bound.truncate(old_len),
            }
        }
        acc.sort();
        acc.dedup();
        acc
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

    fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Apply this substitution to a type.
    pub fn apply(&self, ty: &HmType) -> HmType {
        enum Task<'ty> {
            Visit(&'ty HmType),
            Arrow,
            Forall {
                vars: Vec<String>,
                removed: Vec<(String, Option<HmType>)>,
            },
        }

        let mut bindings = self.bindings.clone();
        let mut tasks = vec![Task::Visit(ty)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(HmType::Var(name)) => values.push(
                    bindings
                        .get(name)
                        .cloned()
                        .unwrap_or_else(|| HmType::Var(name.clone())),
                ),
                Task::Visit(HmType::Mono(name)) => values.push(HmType::Mono(name.clone())),
                Task::Visit(HmType::Arrow(domain, codomain)) => {
                    tasks.push(Task::Arrow);
                    tasks.push(Task::Visit(codomain));
                    tasks.push(Task::Visit(domain));
                },
                Task::Visit(HmType::Forall(vars, body)) => {
                    let removed = vars
                        .iter()
                        .map(|name| (name.clone(), bindings.remove(name)))
                        .collect();
                    tasks.push(Task::Forall { vars: vars.clone(), removed });
                    tasks.push(Task::Visit(body));
                },
                Task::Arrow => {
                    let codomain = values
                        .pop()
                        .expect("HM substitution PDA lost arrow codomain");
                    let domain = values.pop().expect("HM substitution PDA lost arrow domain");
                    values.push(HmType::Arrow(Box::new(domain), Box::new(codomain)));
                },
                Task::Forall { vars, removed } => {
                    for (name, value) in removed {
                        if let Some(value) = value {
                            bindings.insert(name, value);
                        }
                    }
                    let body = values.pop().expect("HM substitution PDA lost forall body");
                    values.push(HmType::Forall(vars, Box::new(body)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("HM substitution PDA produced no value")
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
    enum Input<'ty> {
        Borrowed(&'ty HmType),
        Owned(HmType),
    }

    impl Input<'_> {
        fn as_ref(&self) -> &HmType {
            match self {
                Input::Borrowed(value) => value,
                Input::Owned(value) => value,
            }
        }

        fn into_owned(self) -> HmType {
            match self {
                Input::Borrowed(value) => value.clone(),
                Input::Owned(value) => value,
            }
        }
    }

    enum Task<'ty> {
        Compare(Input<'ty>, Input<'ty>),
        Codomain(Input<'ty>, Input<'ty>),
        FinishArrow(Substitution),
    }

    fn take_arrow(mut ty: HmType) -> (HmType, HmType) {
        let HmType::Arrow(domain, codomain) = &mut ty else {
            unreachable!("HM unification PDA classified an owned type as Arrow")
        };
        let domain = std::mem::replace(domain, Box::new(HmType::Mono(String::new())));
        let codomain = std::mem::replace(codomain, Box::new(HmType::Mono(String::new())));
        (*domain, *codomain)
    }

    let mut tasks = vec![Task::Compare(Input::Borrowed(left), Input::Borrowed(right))];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Compare(left, right) => {
                if let (HmType::Var(a), HmType::Var(b)) = (left.as_ref(), right.as_ref()) {
                    if a == b {
                        results.push(Substitution::empty());
                        continue;
                    }
                }

                let variable_side = match (left.as_ref(), right.as_ref()) {
                    (HmType::Var(name), other) => Some((name.clone(), other.free_type_vars())),
                    (other, HmType::Var(name)) => Some((name.clone(), other.free_type_vars())),
                    _ => None,
                };
                if let Some((variable, free_vars)) = variable_side {
                    let other = if matches!(left.as_ref(), HmType::Var(_)) {
                        right.into_owned()
                    } else {
                        left.into_owned()
                    };
                    if free_vars.contains(&variable) {
                        return Err(HmError::OccursCheck { var: variable, ty: other });
                    }
                    let mut substitution = Substitution::empty();
                    substitution.insert(variable, other);
                    results.push(substitution);
                    continue;
                }

                if let (HmType::Mono(a), HmType::Mono(b)) = (left.as_ref(), right.as_ref()) {
                    if a == b {
                        results.push(Substitution::empty());
                        continue;
                    }
                }

                if matches!(left.as_ref(), HmType::Arrow(..))
                    && matches!(right.as_ref(), HmType::Arrow(..))
                {
                    match (left, right) {
                        (
                            Input::Borrowed(HmType::Arrow(domain1, codomain1)),
                            Input::Borrowed(HmType::Arrow(domain2, codomain2)),
                        ) => {
                            tasks.push(Task::Codomain(
                                Input::Borrowed(codomain1),
                                Input::Borrowed(codomain2),
                            ));
                            tasks.push(Task::Compare(
                                Input::Borrowed(domain1),
                                Input::Borrowed(domain2),
                            ));
                        },
                        (left, right) => {
                            let (domain1, codomain1) = take_arrow(left.into_owned());
                            let (domain2, codomain2) = take_arrow(right.into_owned());
                            tasks.push(Task::Codomain(
                                Input::Owned(codomain1),
                                Input::Owned(codomain2),
                            ));
                            tasks.push(Task::Compare(Input::Owned(domain1), Input::Owned(domain2)));
                        },
                    }
                    continue;
                }

                return Err(HmError::UnificationFailure {
                    left: left.into_owned(),
                    right: right.into_owned(),
                });
            },
            Task::Codomain(left, right) => {
                let domain_substitution = results
                    .pop()
                    .expect("HM unification PDA lost domain substitution");
                let is_empty = domain_substitution.is_empty();
                tasks.push(Task::FinishArrow(domain_substitution));
                if is_empty {
                    tasks.push(Task::Compare(left, right));
                } else {
                    let substitution = match tasks.last() {
                        Some(Task::FinishArrow(substitution)) => substitution,
                        _ => unreachable!("HM unification PDA lost arrow continuation"),
                    };
                    let left = substitution.apply(left.as_ref());
                    let right = substitution.apply(right.as_ref());
                    tasks.push(Task::Compare(Input::Owned(left), Input::Owned(right)));
                }
            },
            Task::FinishArrow(domain_substitution) => {
                let codomain_substitution = results
                    .pop()
                    .expect("HM unification PDA lost codomain substitution");
                results.push(codomain_substitution.compose(&domain_substitution));
            },
        }
    }
    debug_assert_eq!(results.len(), 1);
    Ok(results
        .pop()
        .expect("HM unification PDA produced no result"))
}

/// HM term representation for inference.
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
    enum Task<'term> {
        Infer(&'term HmTerm),
        Abs {
            param: &'term str,
            previous: Option<HmType>,
            param_ty: HmType,
        },
        AppFunction(&'term HmTerm),
        AppArgument {
            function_substitution: Substitution,
            function_type: HmType,
            previous_bindings: HashMap<String, HmType>,
        },
        LetValue {
            name: &'term str,
            body: &'term HmTerm,
        },
        LetBody {
            value_substitution: Substitution,
            previous_bindings: HashMap<String, HmType>,
        },
    }

    let mut bindings = env.bindings.clone();
    let mut tasks = vec![Task::Infer(term)];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Infer(HmTerm::LitInt(_)) => {
                results.push((Substitution::empty(), HmType::mono("Int")));
            },
            Task::Infer(HmTerm::LitBool(_)) => {
                results.push((Substitution::empty(), HmType::mono("Bool")));
            },
            Task::Infer(HmTerm::LitStr(_)) => {
                results.push((Substitution::empty(), HmType::mono("String")));
            },
            Task::Infer(HmTerm::Var(name)) => {
                let ty = bindings
                    .get(name)
                    .cloned()
                    .ok_or_else(|| HmError::UnboundVariable { name: name.clone() })?;
                results.push((Substitution::empty(), ty));
            },
            Task::Infer(HmTerm::Abs { param, body }) => {
                let param_ty = fresh_type_var();
                let previous = bindings.insert(param.clone(), param_ty.clone());
                tasks.push(Task::Abs { param, previous, param_ty });
                tasks.push(Task::Infer(body));
            },
            Task::Infer(HmTerm::App { f, arg }) => {
                tasks.push(Task::AppFunction(arg));
                tasks.push(Task::Infer(f));
            },
            Task::Infer(HmTerm::Let { name, value, body }) => {
                tasks.push(Task::LetValue { name, body });
                tasks.push(Task::Infer(value));
            },
            Task::Abs { param, previous, param_ty } => {
                let (substitution, body_ty) = results
                    .pop()
                    .expect("HM inference PDA lost abstraction result");
                if let Some(previous) = previous {
                    bindings.insert(param.to_string(), previous);
                } else {
                    bindings.remove(param);
                }
                let param_ty = substitution.apply(&param_ty);
                results.push((substitution, HmType::arrow(param_ty, body_ty)));
            },
            Task::AppFunction(argument) => {
                let (function_substitution, function_type) = results
                    .pop()
                    .expect("HM inference PDA lost function result");
                let next_bindings = bindings
                    .iter()
                    .map(|(name, ty)| (name.clone(), function_substitution.apply(ty)))
                    .collect();
                let previous_bindings = std::mem::replace(&mut bindings, next_bindings);
                tasks.push(Task::AppArgument {
                    function_substitution,
                    function_type,
                    previous_bindings,
                });
                tasks.push(Task::Infer(argument));
            },
            Task::AppArgument {
                function_substitution,
                function_type,
                previous_bindings,
            } => {
                let (argument_substitution, argument_type) = results
                    .pop()
                    .expect("HM inference PDA lost argument result");
                let result_type = fresh_type_var();
                let function_type = argument_substitution.apply(&function_type);
                let expected = HmType::arrow(argument_type, result_type.clone());
                let result_substitution = unify(&function_type, &expected)?;
                let final_substitution = result_substitution
                    .compose(&argument_substitution.compose(&function_substitution));
                let final_result_type = result_substitution.apply(&result_type);
                bindings = previous_bindings;
                results.push((final_substitution, final_result_type));
            },
            Task::LetValue { name, body } => {
                let (value_substitution, value_type) = results
                    .pop()
                    .expect("HM inference PDA lost let value result");
                let mut next_bindings: HashMap<_, _> = bindings
                    .iter()
                    .map(|(name, ty)| (name.clone(), value_substitution.apply(ty)))
                    .collect();
                next_bindings.insert(name.to_string(), value_type);
                let previous_bindings = std::mem::replace(&mut bindings, next_bindings);
                tasks.push(Task::LetBody { value_substitution, previous_bindings });
                tasks.push(Task::Infer(body));
            },
            Task::LetBody { value_substitution, previous_bindings } => {
                let (body_substitution, body_type) = results
                    .pop()
                    .expect("HM inference PDA lost let body result");
                bindings = previous_bindings;
                results.push((body_substitution.compose(&value_substitution), body_type));
            },
        }
    }
    debug_assert_eq!(results.len(), 1);
    Ok(results.pop().expect("HM inference PDA produced no result"))
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

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge (OSLF substrate, Phase 6 — base-sort consistency over the
// grammar's constructor arrow types; the live base-sort pass)
// ══════════════════════════════════════════════════════════════════════════════
//
// This is the live wire for the SHIPPED-but-otherwise-dead `hindley_milner`
// module. It does NOT use the term language (`HmTerm`/`infer`/`Abs`/`App`) — the
// grammar's term language is `SyntaxItemSpec`, not lambda calculus, and there is
// no `SyntaxItemSpec → HmTerm` producer. Instead it performs a **base-sort
// consistency** analysis directly over `HmType` arrows: each grammar rule's
// constructor is read as a principal arrow type
// `Arrow(field_sort_1, …Arrow(field_sort_n, Mono(result_category)))`, and the
// inferred result sort is checked against the rule's declared category by
// `unify`. It touches ONLY `HmType::{Mono, Arrow}` plus the existing
// `unify`/`apply`; it NEVER calls `fresh_type_var` (the global `FRESH_COUNTER`
// is a cross-call determinism hazard — every type produced here is fresh-var-
// free, so the analysis is order-independent and deterministic).
//
// Because every constructor field sort is read from the SAME `SyntaxItemSpec`
// that names the rule's declared category, the inferred result sort always
// unifies on any well-formed grammar (whose referenced categories are all
// declared — the parser guarantees this) ⇒ `sort_mismatches` is empty and the
// pass is fully INERT on every current grammar.

/// Pipeline-level Hindley-Milner base-sort consistency result.
///
/// Shaped to feed the lint layer only (HM01) — it is NOT routed into codegen,
/// so it never extends `AdvancedAnalysisBundle` nor touches a codegen seam.
#[derive(Debug, Clone)]
pub struct HmInferenceAnalysis {
    /// Each constructor's principal arrow type, as `(rule_label, rendered_arrow)`
    /// (e.g. `("AddInt", "Int → Int → Int")`), in `all_syntax` order. Populated
    /// for every rule whose inferred result sort agrees with its declared
    /// category (the inert case — all rules on a well-formed grammar).
    pub inferred_constructor_types: Vec<(String, String)>,
    /// Constructors whose inferred result sort disagrees with their declaration,
    /// as `(rule_label, reason)`. Empty on every well-formed grammar (a field's
    /// category is always declared ⇒ the field/result arrow unifies). A non-empty
    /// entry is a genuine base-sort inconsistency surfaced as the HM01 lint.
    pub sort_mismatches: Vec<(String, String)>,
}

/// Render an [`HmType`] to a compact, deterministic arrow notation
/// (`a → b → c`, right-associated, parenthesizing nested arrow domains). Used
/// only to populate the human-readable `inferred_constructor_types` /
/// `sort_mismatches` strings — never parsed back.
fn render_hm_type(ty: &HmType) -> String {
    ty.to_string()
}

/// Collect the **field sorts** of a rule body, left-to-right, descending into
/// the structural wrappers exactly as the sibling structural collectors do
/// (`Optional`/`Sep`/`Map`/`Zip`).
///
/// `NonTerminal` / `Binder` / `Collection` (element category) each contribute a
/// monomorphic field sort `Mono(category)`; `Terminal`, `IdentCapture`, and
/// `BinderCollection` contribute none (they carry no sub-sort). Mirrors
/// [`crate::bisimulation::collect_nonterminal_targets`] so the arrow's domains
/// track the same notion of "structural child sort" the rest of the substrate
/// uses.
fn collect_field_sorts(items: &[crate::SyntaxItemSpec], out: &mut Vec<HmType>) {
    use crate::SyntaxItemSpec as Item;
    for item in crate::syntax_item::preorder(items) {
        match item {
            Item::NonTerminal { category, .. } => out.push(HmType::Mono(category.clone())),
            Item::Binder { category, .. } => out.push(HmType::Mono(category.clone())),
            Item::Collection { element_category, .. } => {
                out.push(HmType::Mono(element_category.clone()))
            },
            // Terminal, IdentCapture, BinderCollection — no field sort.
            _ => {},
        }
    }
}

/// Build a rule constructor's **principal arrow type** from its body fields:
/// `Arrow(field_sort_1, …Arrow(field_sort_n, Mono(result_category)))`. A
/// nullary constructor (no field sorts) is just `Mono(result_category)`.
///
/// `canonicalize_field` rewrites each field's *domain* sort before it is folded
/// into the arrow: on the inferred side it is the identity; on the declared
/// (expected) side it maps a field category to itself iff that category is
/// declared, else to a distinguished sentinel `Mono("⊥undeclared:<name>")` that
/// cannot unify with the bare `Mono(<name>)` produced on the inferred side. The
/// result/codomain (`Mono(result_category)`) is never canonicalized — it is the
/// declared category by construction.
///
/// Uses ONLY `HmType::{Mono, Arrow}`; introduces NO fresh type variables.
fn infer_constructor_arrow(
    result_category: &str,
    field_sorts: &[HmType],
    canonicalize_field: &impl Fn(&HmType) -> HmType,
) -> HmType {
    // Fold right-to-left so the leftmost field becomes the outermost domain:
    // f1 → (f2 → (… → result)). Preallocation is implicit (the fold reuses the
    // single accumulator), and the result sort seeds the fold.
    let mut acc = HmType::Mono(result_category.to_string());
    for field in field_sorts.iter().rev() {
        acc = HmType::Arrow(Box::new(canonicalize_field(field)), Box::new(acc));
    }
    acc
}

/// Analyze grammar rules for **base-sort consistency** of their constructor
/// arrow types.
///
/// For each rule `(label, category, items)`:
///   1. collect the field sorts (`Mono(child_category)` per structural child);
///   2. build the inferred arrow `Arrow(f1, …Arrow(fn, Mono(category)))`
///      (identity canonicalization) and the declared arrow (field categories
///      canonicalized against the declared-category set, result `Mono(category)`);
///   3. `unify` the two arrows. The codomain leg of that unification IS "the
///      inferred result sort `unify`d with the declared `rule.category`" (both
///      `Mono(category)` ⇒ trivially Ok); the domain legs additionally certify
///      that every field references a *declared* category. On `Ok`, the
///      `apply`-resolved arrow is rendered into `inferred_constructor_types`; on
///      `Err`, a `(label, reason)` is pushed to `sort_mismatches`.
///
/// On every well-formed grammar each field category is declared, so the
/// canonicalization is the identity, the arrows are equal, `unify` succeeds, and
/// `sort_mismatches` is empty — the pass is inert. A field referencing an
/// undeclared category (or otherwise inconsistent use) yields exactly one
/// mismatch with a `unify`-derived reason.
///
/// Uses ONLY `HmType::{Mono, Arrow}` + the existing [`unify`]/[`Substitution::apply`];
/// NO `HmTerm`, NO [`infer`], NO [`fresh_type_var`].
///
/// # Arguments
///
/// * `all_syntax` — `(rule_label, category, items)` triples from the parser
///   bundle (the same slice [`crate::bisimulation::analyze_from_bundle`] consumes).
/// * `categories` — the grammar's [`CategoryInfo`](crate::pipeline::CategoryInfo)
///   list; declared category names seed the field-consistency canonicalization.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> HmInferenceAnalysis {
    // Declared-category set: a field whose category is in this set is consistent
    // (the inferred and declared arrows agree on that domain); one outside it is
    // a base-sort inconsistency. The parser guarantees every referenced category
    // is declared, so on real grammars this set covers all field categories.
    let declared: std::collections::HashSet<&str> =
        categories.iter().map(|c| c.name.as_str()).collect();

    // Identity canonicalization for the inferred side: a field's sort is taken
    // verbatim.
    let identity = |t: &HmType| -> HmType { t.clone() };
    // Declared-side canonicalization: a `Mono(cat)` field stays `Mono(cat)` iff
    // `cat` is declared, else becomes a sentinel that cannot unify with the bare
    // `Mono(cat)` the inferred side produced. Non-`Mono` field sorts (none are
    // produced here, but be total) pass through unchanged.
    let against_declared = |t: &HmType| -> HmType {
        match t {
            HmType::Mono(cat) if !declared.contains(cat.as_str()) => {
                HmType::Mono(format!("⊥undeclared:{cat}"))
            },
            other => other.clone(),
        }
    };

    let mut inferred_constructor_types: Vec<(String, String)> =
        Vec::with_capacity(all_syntax.len());
    let mut sort_mismatches: Vec<(String, String)> = Vec::new();

    for (label, category, items) in all_syntax {
        let mut field_sorts: Vec<HmType> = Vec::new();
        collect_field_sorts(items, &mut field_sorts);

        let inferred_arrow = infer_constructor_arrow(category, &field_sorts, &identity);
        let declared_arrow = infer_constructor_arrow(category, &field_sorts, &against_declared);

        // The codomain leg of this unification is exactly "the inferred result
        // sort unified with the declared category" (`Mono(category)` on both
        // sides ⇒ Ok); the domain legs certify each field's category is declared.
        match unify(&inferred_arrow, &declared_arrow) {
            Ok(subst) => {
                // Resolve the arrow under the (empty, on success) substitution and
                // record the constructor's principal type for evidence.
                let resolved = subst.apply(&inferred_arrow);
                inferred_constructor_types.push((label.clone(), render_hm_type(&resolved)));
            },
            Err(err) => {
                sort_mismatches.push((
                    label.clone(),
                    format!(
                        "inferred constructor type {} disagrees with its declaration: {}",
                        render_hm_type(&inferred_arrow),
                        err
                    ),
                ));
            },
        }
    }

    HmInferenceAnalysis {
        inferred_constructor_types,
        sort_mismatches,
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
        match &ty {
            HmType::Arrow(a, b) => assert_eq!(a, b),
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
