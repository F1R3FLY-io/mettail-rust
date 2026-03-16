//! Pluggable Type System Framework
//!
//! ## Overview
//!
//! This module defines the `TypeSystem` trait — the core abstraction for type
//! checking, inference, and subtyping in any MeTTaIL-defined language. It is
//! analogous to `ConstraintTheory` for constraint domains: languages implement
//! this trait to get pipeline integration (lints, SFA analysis, codegen) for free.
//!
//! ## Architecture
//!
//! ```text
//! ┌───────────────────────────────────────────────────────────────────────┐
//! │                      TypeSystem Trait                                 │
//! │                                                                       │
//! │  check(env, term, type) → bool                                       │
//! │  infer(env, term) → Vec<Type>                                        │
//! │  is_subtype(env, sub, sup) → bool                                    │
//! │  join(env, a, b) → Option<Type>                                      │
//! │  meet(env, a, b) → Option<Type>                                      │
//! │  extend(env, var, type) → TypeEnv                                    │
//! │  is_inhabited(env, type) → bool                                      │
//! │  top() / bottom() → Option<Type>                                     │
//! └──────────────┬────────────────────────────────────────────────────────┘
//!                │
//!    ┌───────────┼───────────┐
//!    │           │           │
//!    ▼           ▼           ▼
//! LatticeType  Refinement  SetTheoretic
//! System       TypeSystem  TypeSystem
//! │            <S, T>      │
//! │            │           │
//! ▼            ▼           ▼
//! Wraps        Composes    Tree automata
//! LatticeTheory base +    Types = states
//!              predicate   Subtype = inclusion
//! ```
//!
//! ## Implementations
//!
//! - **`LatticeTypeSystem`**: Wraps `LatticeTheory` — finite subtype lattice.
//!   Simplest reference implementation. (Sprint RT1)
//! - **`RefinementTypeSystem<S, T>`**: Composes a base `TypeSystem S` with a
//!   `ConstraintTheory T` to form `{ x: S::Type | T::Constraint }` types.
//!   (Sprint RT2)
//! - **`SetTheoreticTypeSystem`**: CDuce/XDuce-style types as regular tree
//!   languages via `WeightedTreeAutomaton<BooleanWeight>`. (Sprint RT3)
//!
//! ## Compile-Time vs Runtime
//!
//! All `TypeSystem` implementations and the `TypeSystemAlgebra` bridge are
//! **compile-time only** — they execute during `language!` macro expansion
//! to analyze types, emit lints (RT01–RT06), and inform codegen. None of
//! this code appears in the generated binary. The only runtime artifacts
//! are generated Ascent relations (`is_refined_*`) and predicate checks.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;

use crate::lattice_theory::{LatticeStore, LatticeTheory, SubtypeConstraint, TypeAssignment, TypeId};
use crate::logict::ConstraintTheory;

// ==============================================================================
// TypeSystem Trait
// ==============================================================================

/// Pluggable type system trait — the core abstraction for type checking,
/// inference, and subtyping in any MeTTaIL-defined language.
///
/// Analogous to `ConstraintTheory` for constraint domains: languages implement
/// this trait to get pipeline integration (lints, SFA analysis, codegen) for
/// free.
///
/// # Associated Types
///
/// - `Type`: Type representation (e.g., `TypeId` for lattice, `SetType` for
///   set-theoretic).
/// - `TypeEnv`: Type environment mapping variables to types.
/// - `Term`: Term representation (what gets type-checked).
///
/// # Guarantees
///
/// Implementations must satisfy:
/// - **Reflexivity**: `is_subtype(env, T, T) == true`
/// - **Transitivity**: `is_subtype(S, T) ∧ is_subtype(T, U) ⟹ is_subtype(S, U)`
/// - **Antisymmetry**: `is_subtype(S, T) ∧ is_subtype(T, S) ⟹ S ≡ T`
/// - **Soundness of check**: `check(env, t, T)` implies `t` denotes a value of
///   type `T` in `env`.
pub trait TypeSystem: Clone + fmt::Debug + Send + Sync + 'static {
    /// Type representation (e.g., TypeId for lattice, SetType for set-theoretic).
    type Type: Clone + fmt::Debug + Eq + Hash + Send + Sync + 'static;

    /// Type environment (bindings from variables to types).
    type TypeEnv: Clone + fmt::Debug + Send + Sync + 'static;

    /// Term representation (what gets type-checked).
    type Term: Clone + fmt::Debug + Send + Sync + 'static;

    /// Create an empty type environment.
    fn empty_env(&self) -> Self::TypeEnv;

    /// Type checking: does `term` have type `ty` in `env`?
    fn check(&self, env: &Self::TypeEnv, term: &Self::Term, ty: &Self::Type) -> bool;

    /// Type inference: what types can `term` have in `env`?
    /// Returns all possible types (nondeterministic for gradual/union types).
    fn infer(&self, env: &Self::TypeEnv, term: &Self::Term) -> Vec<Self::Type>;

    /// Subtyping: is `sub` a subtype of `sup` in `env`?
    fn is_subtype(&self, env: &Self::TypeEnv, sub: &Self::Type, sup: &Self::Type) -> bool;

    /// Join (LUB): narrowest common supertype. None if no finite join.
    fn join(
        &self,
        env: &Self::TypeEnv,
        a: &Self::Type,
        b: &Self::Type,
    ) -> Option<Self::Type>;

    /// Meet (GLB): widest common subtype. None if no finite meet.
    fn meet(
        &self,
        env: &Self::TypeEnv,
        a: &Self::Type,
        b: &Self::Type,
    ) -> Option<Self::Type>;

    /// Extend environment with a new variable binding.
    fn extend(&self, env: &Self::TypeEnv, var: &str, ty: &Self::Type) -> Self::TypeEnv;

    /// Check if a type is inhabited (has at least one value).
    /// Default: assumes all types are inhabited.
    fn is_inhabited(&self, _env: &Self::TypeEnv, _ty: &Self::Type) -> bool {
        true
    }

    /// Top type (if the system has one). All types are subtypes of this.
    fn top(&self) -> Option<Self::Type> {
        None
    }

    /// Bottom type (if the system has one). This is a subtype of all types.
    fn bottom(&self) -> Option<Self::Type> {
        None
    }
}

// ==============================================================================
// LatticeTypeSystem
// ==============================================================================

/// Type environment for the lattice type system.
///
/// Maps variable names to `TypeId` values in the lattice.
#[derive(Clone, Debug)]
pub struct LatticeTypeEnv {
    /// Variable name → TypeId bindings.
    pub bindings: HashMap<String, TypeId>,
}

impl LatticeTypeEnv {
    /// Create an empty type environment.
    pub fn new() -> Self {
        LatticeTypeEnv {
            bindings: HashMap::new(),
        }
    }
}

impl Default for LatticeTypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

/// Simple term representation for lattice type checking.
///
/// Reuses the same structure as `TermExpr` in unification.rs but specialized
/// for type-level reasoning: variables are looked up in the type environment,
/// constants have fixed types, and applications infer from constructor types.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LatticeTerm {
    /// A variable (looked up in the type environment).
    Var(String),
    /// A constant with a known type.
    Const {
        /// The constant's name.
        name: String,
        /// The constant's type (TypeId in the lattice).
        ty: TypeId,
    },
    /// A constructor application C(t₁, ..., tₙ).
    App {
        /// The constructor name (looked up in `constructor_types`).
        head: String,
        /// The argument sub-terms.
        args: Vec<LatticeTerm>,
    },
}

/// Lattice type system — wraps `LatticeTheory` into the `TypeSystem` trait.
///
/// This is the simplest `TypeSystem` implementation: types are `TypeId` values
/// in a finite subtype lattice. Subtyping delegates to `LatticeStore::is_subtype()`
/// via transitive closure. Join/meet delegate to `LatticeStore::join()`/`meet()`.
///
/// Constructor types are declared via `constructor_types`: each constructor name
/// maps to `(arg_types, result_type)`. Type inference for `App` nodes checks
/// argument types and returns the constructor's result type.
#[derive(Clone, Debug)]
pub struct LatticeTypeSystem {
    /// The underlying lattice theory.
    pub theory: LatticeTheory,
    /// The lattice store (subtype edges + transitive closure).
    pub store: LatticeStore,
    /// Constructor types: name → (argument types, result type).
    pub constructor_types: HashMap<String, (Vec<TypeId>, TypeId)>,
    /// Top type (if designated).
    pub top_type: Option<TypeId>,
    /// Bottom type (if designated).
    pub bottom_type: Option<TypeId>,
}

impl LatticeTypeSystem {
    /// Create a new lattice type system from a theory, store, and constructor types.
    pub fn new(
        theory: LatticeTheory,
        store: LatticeStore,
        constructor_types: HashMap<String, (Vec<TypeId>, TypeId)>,
    ) -> Self {
        LatticeTypeSystem {
            theory,
            store,
            constructor_types,
            top_type: None,
            bottom_type: None,
        }
    }

    /// Create a lattice type system with designated top and bottom types.
    pub fn with_bounds(
        theory: LatticeTheory,
        store: LatticeStore,
        constructor_types: HashMap<String, (Vec<TypeId>, TypeId)>,
        top: TypeId,
        bottom: TypeId,
    ) -> Self {
        LatticeTypeSystem {
            theory,
            store,
            constructor_types,
            top_type: Some(top),
            bottom_type: Some(bottom),
        }
    }

    /// Infer the type of a term, returning None if inference fails.
    fn infer_single(
        &self,
        env: &LatticeTypeEnv,
        term: &LatticeTerm,
        store: &mut LatticeStore,
    ) -> Option<TypeId> {
        match term {
            LatticeTerm::Var(name) => env.bindings.get(name).copied(),
            LatticeTerm::Const { ty, .. } => Some(*ty),
            LatticeTerm::App { head, args } => {
                let (expected_arg_types, result_type) =
                    self.constructor_types.get(head)?;
                if args.len() != expected_arg_types.len() {
                    return None;
                }
                for (arg, expected_ty) in args.iter().zip(expected_arg_types.iter()) {
                    let arg_ty = self.infer_single(env, arg, store)?;
                    if !self.theory.is_subtype(store, arg_ty, *expected_ty) {
                        return None;
                    }
                }
                Some(*result_type)
            }
        }
    }
}

impl TypeSystem for LatticeTypeSystem {
    type Type = TypeId;
    type TypeEnv = LatticeTypeEnv;
    type Term = LatticeTerm;

    fn empty_env(&self) -> LatticeTypeEnv {
        LatticeTypeEnv::new()
    }

    fn check(
        &self,
        env: &LatticeTypeEnv,
        term: &LatticeTerm,
        ty: &TypeId,
    ) -> bool {
        let mut store = self.store.clone();
        match self.infer_single(env, term, &mut store) {
            Some(inferred) => self.theory.is_subtype(&mut store, inferred, *ty),
            None => false,
        }
    }

    fn infer(
        &self,
        env: &LatticeTypeEnv,
        term: &LatticeTerm,
    ) -> Vec<TypeId> {
        let mut store = self.store.clone();
        match self.infer_single(env, term, &mut store) {
            Some(ty) => vec![ty],
            None => vec![],
        }
    }

    fn is_subtype(
        &self,
        _env: &LatticeTypeEnv,
        sub: &TypeId,
        sup: &TypeId,
    ) -> bool {
        let mut store = self.store.clone();
        self.theory.is_subtype(&mut store, *sub, *sup)
    }

    fn join(
        &self,
        _env: &LatticeTypeEnv,
        a: &TypeId,
        b: &TypeId,
    ) -> Option<TypeId> {
        let mut store = self.store.clone();
        self.theory.join(&mut store, *a, *b)
    }

    fn meet(
        &self,
        _env: &LatticeTypeEnv,
        a: &TypeId,
        b: &TypeId,
    ) -> Option<TypeId> {
        let mut store = self.store.clone();
        self.theory.meet(&mut store, *a, *b)
    }

    fn extend(
        &self,
        env: &LatticeTypeEnv,
        var: &str,
        ty: &TypeId,
    ) -> LatticeTypeEnv {
        let mut new_env = env.clone();
        new_env.bindings.insert(var.to_string(), *ty);
        new_env
    }

    fn is_inhabited(&self, _env: &LatticeTypeEnv, ty: &TypeId) -> bool {
        // In a finite lattice, all declared types are inhabited
        self.theory.universe.contains(ty)
    }

    fn top(&self) -> Option<TypeId> {
        self.top_type
    }

    fn bottom(&self) -> Option<TypeId> {
        self.bottom_type
    }
}

// ==============================================================================
// TypeSystemAlgebra — Bridge TypeSystem to BooleanAlgebra
// ==============================================================================

/// Type predicate for the TypeSystemAlgebra bridge.
///
/// Analogous to `TheoryPred<T>` for `TheoryAlgebra<T>`. These predicates
/// form a Boolean algebra over type-level propositions.
///
/// Note: `PartialEq`, `Eq`, and `Hash` are manually implemented to avoid
/// Rust's derive macro requiring `S: Eq + Hash` (we only need `S::Type: Eq + Hash`,
/// which the `TypeSystem` trait already guarantees).
#[derive(Clone, Debug)]
pub enum TypePred<S: TypeSystem> {
    /// Always true.
    True,
    /// Always false.
    False,
    /// Type membership: term has type T.
    HasType(S::Type),
    /// Subtype relation: S <: T.
    Subtype {
        sub: S::Type,
        sup: S::Type,
    },
    /// Conjunction.
    And(Box<TypePred<S>>, Box<TypePred<S>>),
    /// Disjunction.
    Or(Box<TypePred<S>>, Box<TypePred<S>>),
    /// Negation.
    Not(Box<TypePred<S>>),
}

impl<S: TypeSystem> PartialEq for TypePred<S> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TypePred::True, TypePred::True) | (TypePred::False, TypePred::False) => true,
            (TypePred::HasType(a), TypePred::HasType(b)) => a == b,
            (TypePred::Subtype { sub: s1, sup: p1 }, TypePred::Subtype { sub: s2, sup: p2 }) => {
                s1 == s2 && p1 == p2
            }
            (TypePred::And(a1, b1), TypePred::And(a2, b2))
            | (TypePred::Or(a1, b1), TypePred::Or(a2, b2)) => a1 == a2 && b1 == b2,
            (TypePred::Not(a), TypePred::Not(b)) => a == b,
            _ => false,
        }
    }
}

impl<S: TypeSystem> Eq for TypePred<S> {}

impl<S: TypeSystem> Hash for TypePred<S> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            TypePred::True | TypePred::False => {}
            TypePred::HasType(ty) => ty.hash(state),
            TypePred::Subtype { sub, sup } => {
                sub.hash(state);
                sup.hash(state);
            }
            TypePred::And(a, b) | TypePred::Or(a, b) => {
                a.hash(state);
                b.hash(state);
            }
            TypePred::Not(inner) => inner.hash(state),
        }
    }
}

/// Bridge from `TypeSystem` to `BooleanAlgebra`.
///
/// Analogous to `TheoryAlgebra<T>` for `ConstraintTheory`: wraps a `TypeSystem`
/// implementation and exposes it as a `BooleanAlgebra` with type predicates.
///
/// This enables SFA-based analysis of type predicates:
/// - `is_satisfiable(HasType(T))` → `is_inhabited(T)`
/// - `implies(Subtype(S,T), Subtype(S,U))` → transitivity check
/// - `witness(HasType(T))` → find a type satisfying the predicate
#[derive(Clone, Debug)]
pub struct TypeSystemAlgebra<S: TypeSystem> {
    /// The underlying type system.
    pub system: S,
    /// Type environment for evaluation.
    pub env: S::TypeEnv,
}

impl<S: TypeSystem> TypeSystemAlgebra<S> {
    /// Create a new TypeSystemAlgebra wrapping a type system.
    pub fn new(system: S) -> Self {
        let env = system.empty_env();
        TypeSystemAlgebra { system, env }
    }

    /// Create a new TypeSystemAlgebra with a specific environment.
    pub fn with_env(system: S, env: S::TypeEnv) -> Self {
        TypeSystemAlgebra { system, env }
    }

    /// Evaluate a type predicate in the current environment.
    pub fn evaluate_pred(&self, pred: &TypePred<S>) -> bool {
        match pred {
            TypePred::True => true,
            TypePred::False => false,
            TypePred::HasType(ty) => self.system.is_inhabited(&self.env, ty),
            TypePred::Subtype { sub, sup } => {
                self.system.is_subtype(&self.env, sub, sup)
            }
            TypePred::And(a, b) => self.evaluate_pred(a) && self.evaluate_pred(b),
            TypePred::Or(a, b) => self.evaluate_pred(a) || self.evaluate_pred(b),
            TypePred::Not(a) => !self.evaluate_pred(a),
        }
    }

    /// Check satisfiability of a type predicate.
    pub fn is_satisfiable_pred(&self, pred: &TypePred<S>) -> bool {
        match pred {
            TypePred::True => true,
            TypePred::False => false,
            TypePred::HasType(ty) => self.system.is_inhabited(&self.env, ty),
            TypePred::Subtype { sub, sup } => {
                self.system.is_subtype(&self.env, sub, sup)
            }
            TypePred::And(a, b) => {
                self.is_satisfiable_pred(a) && self.is_satisfiable_pred(b)
            }
            TypePred::Or(a, b) => {
                self.is_satisfiable_pred(a) || self.is_satisfiable_pred(b)
            }
            TypePred::Not(a) => !self.evaluate_pred(a),
        }
    }

    /// Check if predicate a implies predicate b.
    ///
    /// Returns true if `a ∧ ¬b` is unsatisfiable.
    pub fn implies_pred(&self, a: &TypePred<S>, b: &TypePred<S>) -> bool {
        let counter = TypePred::And(
            Box::new(a.clone()),
            Box::new(TypePred::Not(Box::new(b.clone()))),
        );
        !self.is_satisfiable_pred(&counter)
    }
}

// ==============================================================================
// BooleanAlgebra implementation for TypeSystemAlgebra
// ==============================================================================

#[cfg(feature = "symbolic-automata")]
impl<S: TypeSystem> crate::symbolic::BooleanAlgebra for TypeSystemAlgebra<S> {
    type Predicate = TypePred<S>;
    type Domain = S::Type;

    fn true_pred(&self) -> TypePred<S> {
        TypePred::True
    }

    fn false_pred(&self) -> TypePred<S> {
        TypePred::False
    }

    fn and(&self, a: &TypePred<S>, b: &TypePred<S>) -> TypePred<S> {
        match (a, b) {
            (TypePred::True, _) => b.clone(),
            (_, TypePred::True) => a.clone(),
            (TypePred::False, _) | (_, TypePred::False) => TypePred::False,
            _ => TypePred::And(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn or(&self, a: &TypePred<S>, b: &TypePred<S>) -> TypePred<S> {
        match (a, b) {
            (TypePred::False, _) => b.clone(),
            (_, TypePred::False) => a.clone(),
            (TypePred::True, _) | (_, TypePred::True) => TypePred::True,
            _ => TypePred::Or(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn not(&self, a: &TypePred<S>) -> TypePred<S> {
        match a {
            TypePred::True => TypePred::False,
            TypePred::False => TypePred::True,
            TypePred::Not(inner) => (**inner).clone(),
            _ => TypePred::Not(Box::new(a.clone())),
        }
    }

    fn is_satisfiable(&self, a: &TypePred<S>) -> bool {
        self.is_satisfiable_pred(a)
    }

    fn witness(&self, a: &TypePred<S>) -> Option<S::Type> {
        match a {
            TypePred::True => self.system.top(),
            TypePred::False => None,
            TypePred::HasType(ty) => {
                if self.system.is_inhabited(&self.env, ty) {
                    Some(ty.clone())
                } else {
                    None
                }
            }
            TypePred::Subtype { sub, sup } => {
                if self.system.is_subtype(&self.env, sub, sup) {
                    Some(sub.clone())
                } else {
                    None
                }
            }
            TypePred::And(a_inner, b_inner) => {
                // For conjunction, need a witness that satisfies both
                let wa = self.witness(a_inner)?;
                let wb = self.witness(b_inner)?;
                // Try meeting the two witnesses
                self.system.meet(&self.env, &wa, &wb)
            }
            TypePred::Or(a_inner, b_inner) => {
                self.witness(a_inner).or_else(|| self.witness(b_inner))
            }
            TypePred::Not(inner) => {
                if !self.evaluate_pred(inner) {
                    self.system.top()
                } else {
                    None
                }
            }
        }
    }

    fn evaluate(&self, pred: &TypePred<S>, elem: &S::Type) -> bool {
        match pred {
            TypePred::True => true,
            TypePred::False => false,
            TypePred::HasType(ty) => self.system.is_subtype(&self.env, elem, ty),
            TypePred::Subtype { sub, sup } => {
                self.system.is_subtype(&self.env, sub, sup)
            }
            TypePred::And(a, b) => {
                self.evaluate(a, elem) && self.evaluate(b, elem)
            }
            TypePred::Or(a, b) => {
                self.evaluate(a, elem) || self.evaluate(b, elem)
            }
            TypePred::Not(inner) => !self.evaluate(inner, elem),
        }
    }
}

// ==============================================================================
// RefinementTypeSystem
// ==============================================================================

/// A refined type: `{ var: base_type | predicate }`.
///
/// Combines a base type from a `TypeSystem` with a predicate constraint from
/// a `ConstraintTheory`. The predicate refines the base type to a subset of
/// values satisfying the constraint.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RefinedType<Ty, C> {
    /// Base type (from the underlying TypeSystem).
    pub base: Ty,
    /// Binding variable name for the predicate.
    pub var: String,
    /// Predicate constraint (from a ConstraintTheory).
    pub predicate: C,
}

/// Type in the refinement type system: either a plain base type or a refined one.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RefType<Ty: Clone + fmt::Debug + Eq + Hash, C: Clone + fmt::Debug + Eq + Hash> {
    /// Unrefined base type.
    Base(Ty),
    /// Refinement type: `{ var: base | predicate }`.
    Refined(RefinedType<Ty, C>),
}

/// Type environment for the refinement type system.
#[derive(Clone, Debug)]
pub struct RefinementTypeEnv<BaseEnv: Clone + fmt::Debug, C: Clone + fmt::Debug + Eq + Hash, Ty: Clone + fmt::Debug + Eq + Hash> {
    /// The base type system's environment.
    pub base_env: BaseEnv,
    /// Refinement bindings: variable → (base type, predicate).
    pub refinements: HashMap<String, RefType<Ty, C>>,
}

/// Refinement type system: combines a base `TypeSystem S` with a
/// `ConstraintTheory T`.
///
/// Subtyping rule:
/// ```text
///   { x: S | P(x) } <: { x: T | Q(x) }
///   iff  S <: T   (in base TypeSystem)
///   AND  ∀x. P(x) ⟹ Q(x)  (predicate entailment via ConstraintTheory)
/// ```
///
/// Base types lift: `T` is equivalent to `{ x: T | true }`.
#[derive(Clone, Debug)]
pub struct RefinementTypeSystem<S: TypeSystem, T: ConstraintTheory> {
    /// The base type system.
    pub base_system: S,
    /// The constraint theory for predicate analysis.
    pub constraint_theory: T,
    /// Search bound for LogicT-based entailment checking.
    pub search_bound: usize,
}

impl<S: TypeSystem, T: ConstraintTheory> RefinementTypeSystem<S, T>
where
    T::Constraint: Eq + Hash,
{
    /// Create a new refinement type system.
    pub fn new(base_system: S, constraint_theory: T, search_bound: usize) -> Self {
        RefinementTypeSystem {
            base_system,
            constraint_theory,
            search_bound,
        }
    }

    /// Extract the base type from a RefType.
    pub fn base_type(ty: &RefType<S::Type, T::Constraint>) -> &S::Type {
        match ty {
            RefType::Base(t) => t,
            RefType::Refined(r) => &r.base,
        }
    }

    /// Check if a predicate is satisfiable using the constraint theory.
    pub fn predicate_satisfiable(&self, pred: &T::Constraint) -> bool {
        let store = self.constraint_theory.empty_store();
        self.constraint_theory.propagate(&store, pred).is_some()
    }

    /// Check predicate entailment: does P(x) imply Q(x)?
    ///
    /// Uses ConstraintTheory: propagate P into a store, then check if Q
    /// is consistent with that store.
    pub fn predicate_entails(
        &self,
        premise: &T::Constraint,
        conclusion: &T::Constraint,
    ) -> bool {
        let store = self.constraint_theory.empty_store();
        let Some(store_with_p) = self.constraint_theory.propagate(&store, premise) else {
            // If P is unsatisfiable, P ⟹ Q is vacuously true
            return true;
        };
        // Check if Q is consistent in the context where P holds
        self.constraint_theory
            .propagate(&store_with_p, conclusion)
            .is_some()
    }

    /// Apply a variable substitution to a refinement type.
    ///
    /// Given `{ x: T | P(x) }` and substitution `[x ↦ value_repr]`:
    /// 1. The base type `T` is unchanged (structural types don't change under value substitution)
    /// 2. The predicate `P(x)` has `x` replaced by `value_repr`
    /// 3. The resulting predicate is re-checked for satisfiability
    ///
    /// Returns:
    /// - `Some(RefType::Refined { ... })` if the substitution yields a satisfiable predicate
    /// - `Some(RefType::Base(base))` if all free variables are substituted (predicate becomes ground)
    /// - `None` if the substituted predicate is unsatisfiable
    ///
    /// This is used at **compile time** to analyze guard propagation through substitutions
    /// in Comm rules. The runtime codegen uses the simpler approach of checking
    /// `is_refined_<name>(value)` via the Ascent relation generated by RT8.
    pub fn apply_substitution(
        &self,
        ty: &RefType<S::Type, T::Constraint>,
        var: &str,
        constraint_value: &T::Constraint,
    ) -> Option<RefType<S::Type, T::Constraint>> {
        match ty {
            RefType::Base(base) => Some(RefType::Base(base.clone())),
            RefType::Refined(refined) => {
                if refined.var != var {
                    // Substitution variable doesn't match binding variable — pass through
                    return Some(RefType::Refined(refined.clone()));
                }

                // The predicate's binding variable is being substituted.
                // Propagate both the original predicate and the value constraint
                // into a fresh store. If the result is satisfiable, the substitution
                // is valid.
                let store = self.constraint_theory.empty_store();
                let Some(store_with_pred) = self.constraint_theory.propagate(&store, &refined.predicate) else {
                    return None; // Original predicate was unsatisfiable
                };
                let Some(_store_final) = self.constraint_theory.propagate(&store_with_pred, constraint_value) else {
                    return None; // Value doesn't satisfy the predicate
                };

                // After ground substitution, the refinement is satisfied — return base type
                Some(RefType::Base(refined.base.clone()))
            }
        }
    }

    /// Check whether a value (represented as a constraint) satisfies a refinement type.
    ///
    /// This is the compile-time validation: given `{ x: T | P(x) }` and a concrete
    /// value constraint `V`, check whether `P ∧ V` is satisfiable.
    pub fn value_satisfies_refinement(
        &self,
        ty: &RefType<S::Type, T::Constraint>,
        value_constraint: &T::Constraint,
    ) -> bool {
        match ty {
            RefType::Base(_) => true, // No predicate to check
            RefType::Refined(refined) => {
                let store = self.constraint_theory.empty_store();
                let Some(store_with_pred) = self.constraint_theory.propagate(&store, &refined.predicate) else {
                    return false; // Predicate itself is unsatisfiable
                };
                self.constraint_theory
                    .propagate(&store_with_pred, value_constraint)
                    .is_some()
            }
        }
    }
}

impl<S, T> TypeSystem for RefinementTypeSystem<S, T>
where
    S: TypeSystem,
    T: ConstraintTheory,
    T::Constraint: Eq + Hash,
{
    type Type = RefType<S::Type, T::Constraint>;
    type TypeEnv = RefinementTypeEnv<S::TypeEnv, T::Constraint, S::Type>;
    type Term = S::Term;

    fn empty_env(&self) -> Self::TypeEnv {
        RefinementTypeEnv {
            base_env: self.base_system.empty_env(),
            refinements: HashMap::new(),
        }
    }

    fn check(
        &self,
        env: &Self::TypeEnv,
        term: &Self::Term,
        ty: &Self::Type,
    ) -> bool {
        let base_ty = Self::base_type(ty);
        // First check base type
        if !self.base_system.check(&env.base_env, term, base_ty) {
            return false;
        }
        // If refined, check predicate satisfiability
        // (At compile time, we check that the predicate is satisfiable;
        // at runtime, the generated code evaluates the predicate on the value)
        match ty {
            RefType::Base(_) => true,
            RefType::Refined(r) => self.predicate_satisfiable(&r.predicate),
        }
    }

    fn infer(
        &self,
        env: &Self::TypeEnv,
        term: &Self::Term,
    ) -> Vec<Self::Type> {
        self.base_system
            .infer(&env.base_env, term)
            .into_iter()
            .map(RefType::Base)
            .collect()
    }

    fn is_subtype(
        &self,
        env: &Self::TypeEnv,
        sub: &Self::Type,
        sup: &Self::Type,
    ) -> bool {
        let sub_base = Self::base_type(sub);
        let sup_base = Self::base_type(sup);

        // Base type must be a subtype
        if !self.base_system.is_subtype(&env.base_env, sub_base, sup_base) {
            return false;
        }

        // Check predicate entailment
        match (sub, sup) {
            // Base <: Base → base subtype suffices
            (RefType::Base(_), RefType::Base(_)) => true,
            // Refined <: Base → drop predicate (always ok if base subtype holds)
            (RefType::Refined(_), RefType::Base(_)) => true,
            // Base <: Refined → base subtype + predicate must be tautology
            (RefType::Base(_), RefType::Refined(r)) => {
                // { x: T | true } <: { x: T | Q } iff Q is always true
                // We approximate: check if propagating Q produces a valid store
                // (conservative — this may reject valid subtypings)
                let store = self.constraint_theory.empty_store();
                self.constraint_theory.propagate(&store, &r.predicate).is_some()
            }
            // Refined <: Refined → base subtype + P ⟹ Q
            (RefType::Refined(r1), RefType::Refined(r2)) => {
                self.predicate_entails(&r1.predicate, &r2.predicate)
            }
        }
    }

    fn join(
        &self,
        env: &Self::TypeEnv,
        a: &Self::Type,
        b: &Self::Type,
    ) -> Option<Self::Type> {
        let base_a = Self::base_type(a);
        let base_b = Self::base_type(b);
        let base_join = self.base_system.join(&env.base_env, base_a, base_b)?;
        // Join drops refinements (conservative: the result is a base type
        // that is a supertype of both refinements)
        Some(RefType::Base(base_join))
    }

    fn meet(
        &self,
        env: &Self::TypeEnv,
        a: &Self::Type,
        b: &Self::Type,
    ) -> Option<Self::Type> {
        let base_a = Self::base_type(a);
        let base_b = Self::base_type(b);
        let base_meet = self.base_system.meet(&env.base_env, base_a, base_b)?;
        // Meet drops refinements (conservative)
        Some(RefType::Base(base_meet))
    }

    fn extend(
        &self,
        env: &Self::TypeEnv,
        var: &str,
        ty: &Self::Type,
    ) -> Self::TypeEnv {
        let base_ty = Self::base_type(ty);
        RefinementTypeEnv {
            base_env: self.base_system.extend(&env.base_env, var, base_ty),
            refinements: {
                let mut r = env.refinements.clone();
                r.insert(var.to_string(), ty.clone());
                r
            },
        }
    }

    fn is_inhabited(
        &self,
        env: &Self::TypeEnv,
        ty: &Self::Type,
    ) -> bool {
        let base_ty = Self::base_type(ty);
        if !self.base_system.is_inhabited(&env.base_env, base_ty) {
            return false;
        }
        match ty {
            RefType::Base(_) => true,
            RefType::Refined(r) => self.predicate_satisfiable(&r.predicate),
        }
    }

    fn top(&self) -> Option<Self::Type> {
        self.base_system.top().map(RefType::Base)
    }

    fn bottom(&self) -> Option<Self::Type> {
        self.base_system.bottom().map(RefType::Base)
    }
}

// Re-export from lib.rs for backward compatibility.
pub use crate::{RefinementTypeSpec, RefinementPredKind};

// ==============================================================================
// RT10: SFA Integration for Refinement Type Dispatch
// ==============================================================================

/// Result of SFA-based refinement type dispatch analysis.
///
/// When multiple refinement types share the same base type (e.g., `PosInt` and
/// `NegInt` both refine `Int`), this analysis determines:
/// - Whether the refinement predicates are disjoint (safe dispatch)
/// - Whether one subsumes another (subtype relationship)
/// - Whether they overlap (potential ambiguity in dispatch)
///
/// This is used at **compile time** during pipeline analysis. The results
/// feed into RT03 (empty intersection) and RT04 (subtype detected) lints.
#[derive(Debug, Clone, Default)]
pub struct RefinementDispatchAnalysis {
    /// Pairs of refinement types with disjoint predicates (no overlap).
    /// Safe for unambiguous dispatch: `PosInt ∩ NegInt = ∅`.
    pub disjoint_pairs: Vec<(String, String)>,
    /// Pairs where one refines a subset of the other (subtype).
    /// `StrictlyPositive <: PosInt` means every StrictlyPositive is a PosInt.
    pub subtype_pairs: Vec<(String, String)>, // (sub, super)
    /// Pairs with overlapping predicates (potential dispatch ambiguity).
    pub overlapping_pairs: Vec<(String, String)>,
    /// Groups of refinement types sharing the same base type.
    pub base_type_groups: HashMap<String, Vec<String>>,
}

/// Analyze refinement type dispatch safety using the `TypeSystemAlgebra`.
///
/// For each pair of refinement types sharing a base type, checks:
/// 1. **Disjointness**: `is_satisfiable(P ∧ Q)` — if false, types are disjoint
/// 2. **Subsumption**: `implies(P, Q)` — if true, P-type is subtype of Q-type
///
/// This is the compile-time analogue of SFA intersection/subsumption checking
/// applied to refinement predicates rather than SFA guard predicates.
///
/// Feature-gated on `type-system` (uses `LatticeTypeSystem` and
/// `RefinementTypeSystem` which require `logict` + `lattice-theory`).
pub fn analyze_refinement_dispatch(
    refinement_specs: &[crate::RefinementTypeSpec],
) -> RefinementDispatchAnalysis {
    let mut analysis = RefinementDispatchAnalysis::default();

    // Group by base category
    let mut groups: HashMap<String, Vec<&crate::RefinementTypeSpec>> = HashMap::new();
    for spec in refinement_specs {
        groups
            .entry(spec.base_category.clone())
            .or_default()
            .push(spec);
    }

    for (base, specs) in &groups {
        let names: Vec<String> = specs.iter().map(|s| s.name.clone()).collect();
        analysis.base_type_groups.insert(base.clone(), names);

        // Pairwise analysis within each base type group
        for i in 0..specs.len() {
            for j in (i + 1)..specs.len() {
                let a = specs[i];
                let b = specs[j];

                // Use predicate kind to determine dispatch safety.
                // If both are Presburger, we can reason about their predicates.
                // For now, use a conservative heuristic: same predicate kind
                // + different predicate repr = potentially disjoint.
                // Full SFA analysis requires constructing actual automata from
                // the predicate representations, which is done by the
                // `symbolic-automata` feature.
                let overlap = classify_predicate_overlap(a, b);
                match overlap {
                    PredicateOverlap::Disjoint => {
                        analysis.disjoint_pairs.push((a.name.clone(), b.name.clone()));
                    }
                    PredicateOverlap::Subtype => {
                        analysis.subtype_pairs.push((a.name.clone(), b.name.clone()));
                    }
                    PredicateOverlap::Supertype => {
                        analysis.subtype_pairs.push((b.name.clone(), a.name.clone()));
                    }
                    PredicateOverlap::Overlapping => {
                        analysis.overlapping_pairs.push((a.name.clone(), b.name.clone()));
                    }
                }
            }
        }
    }

    analysis
}

/// Classification of how two refinement predicates overlap.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PredicateOverlap {
    /// Predicates have no shared values: `P ∧ Q ≡ false`.
    Disjoint,
    /// First predicate implies second: `P ⟹ Q`.
    Subtype,
    /// Second predicate implies first: `Q ⟹ P`.
    Supertype,
    /// Predicates overlap but neither subsumes the other.
    Overlapping,
}

/// Classify the overlap between two refinement predicates based on their
/// serialized representations and predicate kinds.
///
/// This is a **conservative heuristic** that catches common cases:
/// - Complementary linear predicates (e.g., `x > 0` vs `x <= 0`)
/// - Identical predicates (trivially subsumption)
/// - Stricter predicates (e.g., `x > 0 && x < 10` vs `x > 0`)
///
/// For full precision, the `symbolic-automata` feature provides SFA-based
/// analysis via `TypeSystemAlgebra` → `BooleanAlgebra` → SFA intersection.
fn classify_predicate_overlap(
    a: &crate::RefinementTypeSpec,
    b: &crate::RefinementTypeSpec,
) -> PredicateOverlap {
    // Same predicate representation → identical → mutual subtype
    if a.predicate_repr == b.predicate_repr {
        return PredicateOverlap::Subtype;
    }

    // Both Presburger → try to detect complementary predicates
    if a.predicate_kind == crate::RefinementPredKind::Presburger
        && b.predicate_kind == crate::RefinementPredKind::Presburger
    {
        // Check for obvious complement patterns in the string repr
        // e.g., "x>0" vs "x<=0", "x>=0" vs "x<0"
        if is_complement_predicate(&a.predicate_repr, &b.predicate_repr) {
            return PredicateOverlap::Disjoint;
        }

        // Check if one repr is a prefix of the other with additional conjuncts
        // (stricter predicate is a subtype)
        if a.predicate_repr.contains(&b.predicate_repr) && a.predicate_repr.len() > b.predicate_repr.len() {
            return PredicateOverlap::Subtype; // a is more restrictive
        }
        if b.predicate_repr.contains(&a.predicate_repr) && b.predicate_repr.len() > a.predicate_repr.len() {
            return PredicateOverlap::Supertype; // b is more restrictive
        }
    }

    // Conservative default: assume overlapping
    PredicateOverlap::Overlapping
}

/// Check if two Presburger predicate representations are complements.
///
/// Detects patterns like:
/// - `x>0` vs `x<=0`
/// - `x>=0` vs `x<0`
/// - `x==0` vs `x!=0`
fn is_complement_predicate(a: &str, b: &str) -> bool {
    let complement_pairs = [
        (">", "<="),
        (">=", "<"),
        ("==", "!="),
    ];

    for (op1, op2) in &complement_pairs {
        // Check a has op1 and b has op2 with same operands
        if let (Some(a_pos), Some(b_pos)) = (a.find(op1), b.find(op2)) {
            let a_before = &a[..a_pos];
            let a_after = &a[a_pos + op1.len()..];
            let b_before = &b[..b_pos];
            let b_after = &b[b_pos + op2.len()..];
            if a_before == b_before && a_after == b_after {
                return true;
            }
        }
        // Check reverse: a has op2, b has op1
        if let (Some(a_pos), Some(b_pos)) = (a.find(op2), b.find(op1)) {
            let a_before = &a[..a_pos];
            let a_after = &a[a_pos + op2.len()..];
            let b_before = &b[..b_pos];
            let b_after = &b[b_pos + op1.len()..];
            if a_before == b_before && a_after == b_after {
                return true;
            }
        }
    }

    false
}

// ==============================================================================
// SetTheoreticTypeSystem (Sprint RT3)
// ==============================================================================

/// A set-theoretic type: union/intersection/negation over named base types.
///
/// Types are modeled as sets of values. Union (∪), intersection (∩), and
/// negation (¬) correspond to set operations. Subtyping is set inclusion:
/// `S <: T` iff every value of type S is also of type T.
///
/// For a term algebra with finitely many constructors, these sets form regular
/// tree languages. `SetTheoreticTypeSystem` uses `TreeAutomaton<BooleanWeight>`
/// to decide subtyping via language inclusion: `S <: T` iff `L(S) ∩ L(¬T) = ∅`.
///
/// References:
/// - Frisch, Castagna, & Benzaken (2008). "Semantic subtyping." JACM 55(4).
/// - Comon et al. (2007). "Tree Automata Techniques and Applications."
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SetType {
    /// Named base type (atom, corresponds to a tree automaton state).
    Atom(String),
    /// Union: S ∪ T — values that are in S or T (or both).
    Union(Box<SetType>, Box<SetType>),
    /// Intersection: S ∩ T — values that are in both S and T.
    Intersection(Box<SetType>, Box<SetType>),
    /// Negation: ¬S — values that are NOT in S.
    Negation(Box<SetType>),
    /// Arrow type: S → T (function types). Covariant in T, contravariant in S.
    Arrow(Box<SetType>, Box<SetType>),
    /// Top type (all values).
    Top,
    /// Bottom type (no values / empty type).
    Bottom,
}

impl fmt::Display for SetType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SetType::Atom(name) => write!(f, "{name}"),
            SetType::Union(a, b) => write!(f, "({a} | {b})"),
            SetType::Intersection(a, b) => write!(f, "({a} & {b})"),
            SetType::Negation(inner) => write!(f, "~{inner}"),
            SetType::Arrow(dom, cod) => write!(f, "({dom} -> {cod})"),
            SetType::Top => write!(f, "Top"),
            SetType::Bottom => write!(f, "Bottom"),
        }
    }
}

/// Type environment for the set-theoretic type system.
#[derive(Clone, Debug)]
pub struct SetTypeEnv {
    /// Variable-to-type bindings.
    pub bindings: HashMap<String, SetType>,
}

/// Set-theoretic type system using tree automata for subtyping decisions.
///
/// Types are modeled as regular tree languages over a ranked alphabet of
/// constructors. Subtyping is decided by tree automaton language inclusion:
/// `S <: T` iff `L(A_S) ⊆ L(A_T)` iff `L(A_S ∩ ¬A_T) = ∅`.
///
/// All operations are **compile-time only** — they execute during `language!`
/// macro expansion to verify type relationships and emit lints. No tree
/// automata appear in the generated binary.
#[cfg(feature = "tree-automata")]
#[derive(Clone, Debug)]
pub struct SetTheoreticTypeSystem {
    /// Constructors with their arities (defines the term algebra).
    pub constructors: HashMap<String, usize>,
    /// Named type definitions: type name → tree automaton accepting the type's values.
    pub type_defs: HashMap<String, crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>>,
}

#[cfg(feature = "tree-automata")]
impl SetTheoreticTypeSystem {
    /// Create a new set-theoretic type system with the given constructors.
    pub fn new(constructors: HashMap<String, usize>) -> Self {
        SetTheoreticTypeSystem {
            constructors,
            type_defs: HashMap::new(),
        }
    }

    /// Register a named type definition backed by a tree automaton.
    pub fn define_type(
        &mut self,
        name: impl Into<String>,
        automaton: crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) {
        self.type_defs.insert(name.into(), automaton);
    }

    /// Build a tree automaton for the given `SetType`.
    ///
    /// Each `SetType` variant maps to tree automaton operations:
    /// - `Atom(name)` → look up the named type's automaton (or build a single-state one)
    /// - `Union(a, b)` → union of automata (combined accepting states)
    /// - `Intersection(a, b)` → product construction
    /// - `Negation(a)` → complement (requires determinization; we use the
    ///   bottom-up completeness property of our automata)
    /// - `Top` → universal automaton (accepts all terms)
    /// - `Bottom` → empty automaton (rejects all terms)
    pub fn type_to_automaton(
        &self,
        ty: &SetType,
    ) -> crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight> {
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::{TreeAutomaton, TreeTransition};

        match ty {
            SetType::Atom(name) => {
                if let Some(aut) = self.type_defs.get(name) {
                    aut.clone()
                } else {
                    // Unknown atom: empty automaton (no values)
                    TreeAutomaton::new()
                }
            }
            SetType::Union(a, b) => {
                let aut_a = self.type_to_automaton(a);
                let aut_b = self.type_to_automaton(b);
                self.union_automata(&aut_a, &aut_b)
            }
            SetType::Intersection(a, b) => {
                let aut_a = self.type_to_automaton(a);
                let aut_b = self.type_to_automaton(b);
                self.intersect_automata(&aut_a, &aut_b)
            }
            SetType::Negation(inner) => {
                let aut = self.type_to_automaton(inner);
                self.complement_automaton(&aut)
            }
            SetType::Arrow(_, _) => {
                // Arrow types are modeled structurally: the "arrow" constructor
                // has arity 2, with domain and codomain as children.
                // For now, treat as an atom named "__arrow" if not defined.
                if let Some(aut) = self.type_defs.get("__arrow") {
                    aut.clone()
                } else {
                    TreeAutomaton::new()
                }
            }
            SetType::Top => {
                // Universal automaton: one accepting state, all constructors
                // transition to it with Boolean true.
                let mut aut = TreeAutomaton::new();
                let q = aut.add_state(true); // single accepting state
                for (sym, &arity) in &self.constructors {
                    let children = vec![q; arity];
                    aut.add_transition(TreeTransition {
                        symbol: sym.clone(),
                        child_states: children,
                        target_state: q,
                        weight: BooleanWeight(true),
                    });
                }
                aut
            }
            SetType::Bottom => {
                // Empty automaton: no final states, no transitions.
                TreeAutomaton::new()
            }
        }
    }

    /// Product construction for tree automata intersection.
    ///
    /// States in the product are pairs `(q_a, q_b)`. A product state is
    /// accepting iff both component states are accepting.
    ///
    /// Transition: `f((q_a1, q_b1), ..., (q_an, q_bn)) → (q_a, q_b)` exists
    /// iff `f(q_a1, ..., q_an) → q_a` in A and `f(q_b1, ..., q_bn) → q_b` in B.
    pub fn intersect_automata(
        &self,
        a: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
        b: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) -> crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight> {
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::{TreeAutomaton, TreeTransition};

        let na = a.num_states();
        let nb = b.num_states();
        if na == 0 || nb == 0 {
            return TreeAutomaton::new();
        }

        let mut product = TreeAutomaton::new();
        // State mapping: (qa, qb) → qa * nb + qb
        let pair_id = |qa: usize, qb: usize| -> usize { qa * nb + qb };

        // Create product states
        for qa in 0..na {
            for qb in 0..nb {
                let is_final = a.final_states.contains(&qa) && b.final_states.contains(&qb);
                let id = product.add_state(is_final);
                debug_assert_eq!(id, pair_id(qa, qb));
            }
        }

        // Create product transitions
        // For each symbol, collect transitions from A and B, then form products
        let mut a_by_sym: HashMap<&str, Vec<&TreeTransition<BooleanWeight>>> = HashMap::new();
        for t in &a.transitions {
            a_by_sym.entry(&t.symbol).or_default().push(t);
        }
        let mut b_by_sym: HashMap<&str, Vec<&TreeTransition<BooleanWeight>>> = HashMap::new();
        for t in &b.transitions {
            b_by_sym.entry(&t.symbol).or_default().push(t);
        }

        for (sym, a_trans) in &a_by_sym {
            let Some(b_trans) = b_by_sym.get(sym) else { continue };
            for ta in a_trans {
                for tb in b_trans {
                    if ta.child_states.len() != tb.child_states.len() {
                        continue;
                    }
                    let product_children: Vec<usize> = ta
                        .child_states
                        .iter()
                        .zip(tb.child_states.iter())
                        .map(|(&qa, &qb)| pair_id(qa, qb))
                        .collect();
                    let product_target = pair_id(ta.target_state, tb.target_state);
                    let product_weight = BooleanWeight(ta.weight.0 && tb.weight.0);
                    product.add_transition(TreeTransition {
                        symbol: sym.to_string(),
                        child_states: product_children,
                        target_state: product_target,
                        weight: product_weight,
                    });
                }
            }
        }

        product
    }

    /// Union construction for tree automata.
    ///
    /// Creates a disjoint union of two automata. States are renumbered:
    /// A's states keep their IDs, B's states are offset by `|A.states|`.
    /// A state is accepting if it's accepting in either component.
    pub fn union_automata(
        &self,
        a: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
        b: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) -> crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight> {
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::{TreeAutomaton, TreeTransition};

        let mut result = TreeAutomaton::new();
        let offset = a.num_states();

        // Add A's states
        for state in &a.states {
            result.add_state(state.is_final);
        }
        // Add B's states (offset)
        for state in &b.states {
            result.add_state(state.is_final);
        }

        // Add A's transitions (no renumbering needed)
        for t in &a.transitions {
            result.add_transition(TreeTransition {
                symbol: t.symbol.clone(),
                child_states: t.child_states.clone(),
                target_state: t.target_state,
                weight: t.weight,
            });
        }
        // Add B's transitions (offset state IDs)
        for t in &b.transitions {
            result.add_transition(TreeTransition {
                symbol: t.symbol.clone(),
                child_states: t.child_states.iter().map(|&s| s + offset).collect(),
                target_state: t.target_state + offset,
                weight: t.weight,
            });
        }

        result
    }

    /// Complement construction for tree automata (bottom-up).
    ///
    /// For bottom-up tree automata, complementation requires:
    /// 1. The automaton must be **complete** (every symbol/state combination
    ///    has at least one transition — add a sink state if needed)
    /// 2. The automaton must be **deterministic** (at most one transition for
    ///    each symbol/state combination)
    /// 3. Swap accepting and non-accepting states
    ///
    /// Since our type automata are generally small (tens of states), we use
    /// a straightforward approach: complete the automaton, then swap finals.
    pub fn complement_automaton(
        &self,
        a: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) -> crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight> {
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::{TreeAutomaton, TreeTransition};

        // Special case: empty automaton → universal automaton
        if a.num_states() == 0 {
            return self.type_to_automaton(&SetType::Top);
        }

        let mut result = TreeAutomaton::new();
        let n = a.num_states();

        // Copy states, swapping accepting status
        for state in &a.states {
            result.add_state(!state.is_final);
        }

        // Add a sink state (non-accepting in the original → accepting in complement)
        let sink = result.add_state(true);

        // Copy existing transitions
        for t in &a.transitions {
            result.add_transition(TreeTransition {
                symbol: t.symbol.clone(),
                child_states: t.child_states.clone(),
                target_state: t.target_state,
                weight: t.weight,
            });
        }

        // Complete the automaton: for every constructor and state combination
        // that has no transition, add a transition to the sink state.
        // This is needed for correct complementation.
        let mut existing: HashSet<(String, Vec<usize>)> = HashSet::new();
        for t in &a.transitions {
            existing.insert((t.symbol.clone(), t.child_states.clone()));
        }

        for (sym, &arity) in &self.constructors {
            if arity == 0 {
                // Leaf constructor: check if there's a transition for it
                let key = (sym.clone(), vec![]);
                if !existing.contains(&key) {
                    result.add_transition(TreeTransition {
                        symbol: sym.clone(),
                        child_states: vec![],
                        target_state: sink,
                        weight: BooleanWeight(true),
                    });
                }
            } else {
                // For non-leaf constructors, add sink transitions for state
                // combinations that don't have transitions. We iterate over
                // all state combinations (including the sink state).
                // For small automata this is tractable; for large ones we'd
                // need a lazier approach.
                let all_states: Vec<usize> = (0..=n).collect(); // 0..n original + sink
                Self::enumerate_missing_transitions(
                    &existing,
                    sym,
                    arity,
                    &all_states,
                    sink,
                    &mut result,
                );
            }
        }

        result
    }

    /// Add transitions to `sink` for state combinations missing from `existing`.
    ///
    /// For tractability, we only enumerate combinations up to a reasonable limit.
    /// For type automata with ~tens of states and constructors with arity ≤ 3,
    /// this is practical.
    fn enumerate_missing_transitions(
        existing: &HashSet<(String, Vec<usize>)>,
        symbol: &str,
        arity: usize,
        states: &[usize],
        sink: usize,
        result: &mut crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) {
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::TreeTransition;

        // For arity 1-3, enumerate explicitly
        match arity {
            1 => {
                for &q in states {
                    let key = (symbol.to_string(), vec![q]);
                    if !existing.contains(&key) {
                        result.add_transition(TreeTransition {
                            symbol: symbol.to_string(),
                            child_states: vec![q],
                            target_state: sink,
                            weight: BooleanWeight(true),
                        });
                    }
                }
            }
            2 => {
                for &q1 in states {
                    for &q2 in states {
                        let key = (symbol.to_string(), vec![q1, q2]);
                        if !existing.contains(&key) {
                            result.add_transition(TreeTransition {
                                symbol: symbol.to_string(),
                                child_states: vec![q1, q2],
                                target_state: sink,
                                weight: BooleanWeight(true),
                            });
                        }
                    }
                }
            }
            3 => {
                for &q1 in states {
                    for &q2 in states {
                        for &q3 in states {
                            let key = (symbol.to_string(), vec![q1, q2, q3]);
                            if !existing.contains(&key) {
                                result.add_transition(TreeTransition {
                                    symbol: symbol.to_string(),
                                    child_states: vec![q1, q2, q3],
                                    target_state: sink,
                                    weight: BooleanWeight(true),
                                });
                            }
                        }
                    }
                }
            }
            _ => {
                // For higher arities, only add the all-sink combination as a fallback.
                // Full enumeration would be |states|^arity which is infeasible.
                let key = (symbol.to_string(), vec![sink; arity]);
                if !existing.contains(&key) {
                    result.add_transition(TreeTransition {
                        symbol: symbol.to_string(),
                        child_states: vec![sink; arity],
                        target_state: sink,
                        weight: BooleanWeight(true),
                    });
                }
            }
        }
    }

    /// Check if a tree automaton's language is empty (no term is accepted).
    ///
    /// Uses bottom-up reachability: iteratively compute which states are
    /// reachable (have at least one term that reaches them). A state is
    /// reachable if there exists a transition `f(q1, ..., qn) → q` where
    /// all child states q1...qn are reachable (or n=0 for leaf transitions).
    ///
    /// The language is empty iff no accepting state is reachable.
    pub fn is_empty(
        a: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) -> bool {
        if a.num_states() == 0 {
            return true;
        }
        if a.final_states.is_empty() {
            return true;
        }

        let mut reachable: HashSet<usize> = HashSet::new();
        let mut changed = true;

        while changed {
            changed = false;
            for t in &a.transitions {
                if !t.weight.0 {
                    continue; // zero-weight transitions don't count
                }
                if reachable.contains(&t.target_state) {
                    continue; // already reached
                }
                // Check if all children are reachable
                let all_children_reachable = t
                    .child_states
                    .iter()
                    .all(|child| reachable.contains(child));
                if all_children_reachable {
                    reachable.insert(t.target_state);
                    changed = true;
                }
            }
        }

        // Empty iff no final state is reachable
        !a.final_states.iter().any(|f| reachable.contains(f))
    }
}

#[cfg(feature = "tree-automata")]
impl TypeSystem for SetTheoreticTypeSystem {
    type Type = SetType;
    type TypeEnv = SetTypeEnv;
    type Term = crate::tree_automaton::Term;

    fn empty_env(&self) -> Self::TypeEnv {
        SetTypeEnv {
            bindings: HashMap::new(),
        }
    }

    fn check(
        &self,
        env: &Self::TypeEnv,
        term: &Self::Term,
        ty: &Self::Type,
    ) -> bool {
        // Bottom-up evaluate the term through the type's automaton.
        // The term has type `ty` if it reaches an accepting state.
        let aut = self.type_to_automaton(ty);
        let state_map = crate::tree_automaton::bottom_up_evaluate(&aut, term);
        state_map
            .iter()
            .any(|(state, weight)| aut.final_states.contains(state) && weight.0)
    }

    fn infer(
        &self,
        env: &Self::TypeEnv,
        term: &Self::Term,
    ) -> Vec<Self::Type> {
        // Check the term against each named type definition
        let mut result = Vec::new();
        for (name, aut) in &self.type_defs {
            let state_map = crate::tree_automaton::bottom_up_evaluate(aut, term);
            let accepted = state_map
                .iter()
                .any(|(state, weight)| aut.final_states.contains(state) && weight.0);
            if accepted {
                result.push(SetType::Atom(name.clone()));
            }
        }
        result
    }

    fn is_subtype(
        &self,
        _env: &Self::TypeEnv,
        sub: &Self::Type,
        sup: &Self::Type,
    ) -> bool {
        // S <: T iff L(S) ⊆ L(T) iff L(S) ∩ L(¬T) = ∅
        let aut_sub = self.type_to_automaton(sub);
        let aut_not_sup = self.type_to_automaton(&SetType::Negation(Box::new(sup.clone())));
        let intersection = self.intersect_automata(&aut_sub, &aut_not_sup);
        Self::is_empty(&intersection)
    }

    fn join(
        &self,
        _env: &Self::TypeEnv,
        a: &Self::Type,
        b: &Self::Type,
    ) -> Option<Self::Type> {
        // Join = union type
        Some(SetType::Union(Box::new(a.clone()), Box::new(b.clone())))
    }

    fn meet(
        &self,
        _env: &Self::TypeEnv,
        a: &Self::Type,
        b: &Self::Type,
    ) -> Option<Self::Type> {
        // Meet = intersection type
        Some(SetType::Intersection(Box::new(a.clone()), Box::new(b.clone())))
    }

    fn extend(
        &self,
        env: &Self::TypeEnv,
        var: &str,
        ty: &Self::Type,
    ) -> Self::TypeEnv {
        let mut bindings = env.bindings.clone();
        bindings.insert(var.to_string(), ty.clone());
        SetTypeEnv { bindings }
    }

    fn is_inhabited(
        &self,
        _env: &Self::TypeEnv,
        ty: &Self::Type,
    ) -> bool {
        let aut = self.type_to_automaton(ty);
        !Self::is_empty(&aut)
    }

    fn top(&self) -> Option<Self::Type> {
        Some(SetType::Top)
    }

    fn bottom(&self) -> Option<Self::Type> {
        Some(SetType::Bottom)
    }
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lattice_theory::{LatticeStore, LatticeTheory, TypeId};

    /// Helper: build a simple type hierarchy for testing.
    ///
    /// Hierarchy:
    ///   Top (0)
    ///   ├── Number (1)
    ///   │   ├── Int (2)
    ///   │   └── Float (3)
    ///   ├── String (4)
    ///   └── Bool (5)
    ///   Bottom (6)
    fn test_lattice() -> (LatticeTheory, LatticeStore) {
        let top: TypeId = 0;
        let number: TypeId = 1;
        let int: TypeId = 2;
        let float: TypeId = 3;
        let string: TypeId = 4;
        let bool_ty: TypeId = 5;
        let bottom: TypeId = 6;

        let universe = vec![top, number, int, float, string, bool_ty, bottom];
        let mut names = HashMap::new();
        names.insert(top, "Top".to_string());
        names.insert(number, "Number".to_string());
        names.insert(int, "Int".to_string());
        names.insert(float, "Float".to_string());
        names.insert(string, "String".to_string());
        names.insert(bool_ty, "Bool".to_string());
        names.insert(bottom, "Bottom".to_string());

        let theory = LatticeTheory::new(universe, names);
        let mut store = LatticeStore::new();

        // Add subtype edges: Int <: Number, Float <: Number, Number <: Top, etc.
        let edges = vec![
            (int, number),
            (float, number),
            (number, top),
            (string, top),
            (bool_ty, top),
            (bottom, int),
            (bottom, float),
            (bottom, string),
            (bottom, bool_ty),
        ];
        for (sub, sup) in &edges {
            let ct = &theory;
            let constraint = SubtypeConstraint { sub: *sub, sup: *sup };
            store = ct.propagate(&store, &constraint).expect("propagation should succeed");
        }

        (theory, store)
    }

    fn test_system() -> LatticeTypeSystem {
        let (theory, store) = test_lattice();
        let mut ctor_types = HashMap::new();
        // Constructor: int_lit(value) → Int
        ctor_types.insert("int_lit".to_string(), (vec![], 2)); // Int = 2
        // Constructor: float_lit(value) → Float
        ctor_types.insert("float_lit".to_string(), (vec![], 3)); // Float = 3
        // Constructor: add(Int, Int) → Int
        ctor_types.insert("add".to_string(), (vec![2, 2], 2));

        LatticeTypeSystem::with_bounds(theory, store, ctor_types, 0, 6)
    }

    // ── TypeSystem trait: reflexivity ──

    #[test]
    fn lattice_subtype_reflexive() {
        let sys = test_system();
        let env = sys.empty_env();
        for &ty in &[0usize, 1, 2, 3, 4, 5, 6] {
            assert!(
                sys.is_subtype(&env, &ty, &ty),
                "is_subtype({ty}, {ty}) should be true (reflexivity)"
            );
        }
    }

    // ── TypeSystem trait: transitivity ──

    #[test]
    fn lattice_subtype_transitive() {
        let sys = test_system();
        let env = sys.empty_env();
        // Int <: Number and Number <: Top, so Int <: Top
        assert!(sys.is_subtype(&env, &2, &1)); // Int <: Number
        assert!(sys.is_subtype(&env, &1, &0)); // Number <: Top
        assert!(sys.is_subtype(&env, &2, &0)); // Int <: Top (transitive)
    }

    // ── TypeSystem trait: antisymmetry (non-subtype) ──

    #[test]
    fn lattice_subtype_not_reverse() {
        let sys = test_system();
        let env = sys.empty_env();
        // Number is NOT a subtype of Int
        assert!(!sys.is_subtype(&env, &1, &2));
        // String is NOT a subtype of Number
        assert!(!sys.is_subtype(&env, &4, &1));
    }

    // ── Join (LUB) ──

    #[test]
    fn lattice_join() {
        let sys = test_system();
        let env = sys.empty_env();
        // join(Int, Float) = Number
        assert_eq!(sys.join(&env, &2, &3), Some(1));
        // join(Int, Int) = Int
        assert_eq!(sys.join(&env, &2, &2), Some(2));
        // join(Int, String) = Top
        assert_eq!(sys.join(&env, &2, &4), Some(0));
    }

    // ── Meet (GLB) ──

    #[test]
    fn lattice_meet() {
        let sys = test_system();
        let env = sys.empty_env();
        // meet(Int, Int) = Int
        assert_eq!(sys.meet(&env, &2, &2), Some(2));
        // meet(Number, Int) = Int (Int is subtype of Number)
        assert_eq!(sys.meet(&env, &1, &2), Some(2));
    }

    // ── Type checking ──

    #[test]
    fn lattice_check_const() {
        let sys = test_system();
        let env = sys.empty_env();
        let term = LatticeTerm::Const {
            name: "42".to_string(),
            ty: 2, // Int
        };
        assert!(sys.check(&env, &term, &2)); // Int <: Int
        assert!(sys.check(&env, &term, &1)); // Int <: Number
        assert!(sys.check(&env, &term, &0)); // Int <: Top
        assert!(!sys.check(&env, &term, &4)); // Int ≮: String
    }

    // ── Type inference ──

    #[test]
    fn lattice_infer_const() {
        let sys = test_system();
        let env = sys.empty_env();
        let term = LatticeTerm::Const {
            name: "42".to_string(),
            ty: 2,
        };
        assert_eq!(sys.infer(&env, &term), vec![2]);
    }

    #[test]
    fn lattice_infer_var() {
        let sys = test_system();
        let env = sys.extend(&sys.empty_env(), "x", &2); // x: Int
        let term = LatticeTerm::Var("x".to_string());
        assert_eq!(sys.infer(&env, &term), vec![2]);
    }

    #[test]
    fn lattice_infer_var_missing() {
        let sys = test_system();
        let env = sys.empty_env();
        let term = LatticeTerm::Var("y".to_string());
        assert_eq!(sys.infer(&env, &term), vec![]);
    }

    // ── Constructor application ──

    #[test]
    fn lattice_check_app() {
        let sys = test_system();
        let env = sys.empty_env();
        let term = LatticeTerm::App {
            head: "add".to_string(),
            args: vec![
                LatticeTerm::Const { name: "1".to_string(), ty: 2 },
                LatticeTerm::Const { name: "2".to_string(), ty: 2 },
            ],
        };
        assert!(sys.check(&env, &term, &2)); // add(Int, Int) : Int
        assert!(sys.check(&env, &term, &1)); // add(Int, Int) : Number
        assert!(!sys.check(&env, &term, &4)); // add(Int, Int) ≠ String
    }

    #[test]
    fn lattice_check_app_wrong_arity() {
        let sys = test_system();
        let env = sys.empty_env();
        let term = LatticeTerm::App {
            head: "add".to_string(),
            args: vec![LatticeTerm::Const { name: "1".to_string(), ty: 2 }],
        };
        assert!(!sys.check(&env, &term, &2)); // wrong arity
    }

    // ── Inhabited ──

    #[test]
    fn lattice_inhabited() {
        let sys = test_system();
        let env = sys.empty_env();
        assert!(sys.is_inhabited(&env, &2)); // Int is inhabited
        assert!(!sys.is_inhabited(&env, &99)); // unknown type is not
    }

    // ── Top/Bottom ──

    #[test]
    fn lattice_top_bottom() {
        let sys = test_system();
        assert_eq!(sys.top(), Some(0));
        assert_eq!(sys.bottom(), Some(6));
    }

    // ── Environment extension ──

    #[test]
    fn lattice_extend_env() {
        let sys = test_system();
        let env = sys.empty_env();
        let env2 = sys.extend(&env, "x", &2);
        assert_eq!(env2.bindings.get("x"), Some(&2));
        assert!(env.bindings.get("x").is_none()); // original unchanged
    }

    // ── RT10: SFA dispatch analysis ──

    #[test]
    fn dispatch_analysis_empty() {
        let result = analyze_refinement_dispatch(&[]);
        assert!(result.disjoint_pairs.is_empty());
        assert!(result.subtype_pairs.is_empty());
        assert!(result.overlapping_pairs.is_empty());
        assert!(result.base_type_groups.is_empty());
    }

    #[test]
    fn dispatch_analysis_different_bases() {
        let specs = vec![
            crate::RefinementTypeSpec {
                name: "PosInt".to_string(),
                base_category: "Int".to_string(),
                variable_name: "x".to_string(),
                predicate_kind: crate::RefinementPredKind::Presburger,
                predicate_repr: "x>0".to_string(),
            },
            crate::RefinementTypeSpec {
                name: "ShortStr".to_string(),
                base_category: "String".to_string(),
                variable_name: "s".to_string(),
                predicate_kind: crate::RefinementPredKind::Presburger,
                predicate_repr: "len(s)<100".to_string(),
            },
        ];
        let result = analyze_refinement_dispatch(&specs);
        // Different bases → no pairwise analysis
        assert!(result.disjoint_pairs.is_empty());
        assert!(result.subtype_pairs.is_empty());
        assert_eq!(result.base_type_groups.len(), 2);
    }

    #[test]
    fn dispatch_analysis_complement_predicates() {
        let specs = vec![
            crate::RefinementTypeSpec {
                name: "PosInt".to_string(),
                base_category: "Int".to_string(),
                variable_name: "x".to_string(),
                predicate_kind: crate::RefinementPredKind::Presburger,
                predicate_repr: "x>0".to_string(),
            },
            crate::RefinementTypeSpec {
                name: "NonPosInt".to_string(),
                base_category: "Int".to_string(),
                variable_name: "x".to_string(),
                predicate_kind: crate::RefinementPredKind::Presburger,
                predicate_repr: "x<=0".to_string(),
            },
        ];
        let result = analyze_refinement_dispatch(&specs);
        assert_eq!(result.disjoint_pairs.len(), 1, "complement predicates should be disjoint");
        assert_eq!(result.disjoint_pairs[0], ("PosInt".to_string(), "NonPosInt".to_string()));
    }

    #[test]
    fn dispatch_analysis_identical_predicates() {
        let specs = vec![
            crate::RefinementTypeSpec {
                name: "PosA".to_string(),
                base_category: "Int".to_string(),
                variable_name: "x".to_string(),
                predicate_kind: crate::RefinementPredKind::Presburger,
                predicate_repr: "x>0".to_string(),
            },
            crate::RefinementTypeSpec {
                name: "PosB".to_string(),
                base_category: "Int".to_string(),
                variable_name: "x".to_string(),
                predicate_kind: crate::RefinementPredKind::Presburger,
                predicate_repr: "x>0".to_string(),
            },
        ];
        let result = analyze_refinement_dispatch(&specs);
        assert_eq!(result.subtype_pairs.len(), 1, "identical predicates should be mutual subtypes");
    }

    #[test]
    fn dispatch_analysis_overlapping() {
        let specs = vec![
            crate::RefinementTypeSpec {
                name: "Positive".to_string(),
                base_category: "Int".to_string(),
                variable_name: "x".to_string(),
                predicate_kind: crate::RefinementPredKind::Presburger,
                predicate_repr: "x>0".to_string(),
            },
            crate::RefinementTypeSpec {
                name: "Small".to_string(),
                base_category: "Int".to_string(),
                variable_name: "x".to_string(),
                predicate_kind: crate::RefinementPredKind::Presburger,
                predicate_repr: "x<10".to_string(),
            },
        ];
        let result = analyze_refinement_dispatch(&specs);
        assert_eq!(result.overlapping_pairs.len(), 1, "non-complementary predicates should be overlapping");
    }

    #[test]
    fn complement_predicate_detection() {
        assert!(is_complement_predicate("x>0", "x<=0"));
        assert!(is_complement_predicate("x>=0", "x<0"));
        assert!(is_complement_predicate("x==0", "x!=0"));
        assert!(!is_complement_predicate("x>0", "x>1"));
        assert!(!is_complement_predicate("x>0", "y<=0")); // different vars
    }

    // ── TypeSystemAlgebra ──

    #[test]
    fn type_algebra_evaluate() {
        let sys = test_system();
        let algebra = TypeSystemAlgebra::new(sys);

        assert!(algebra.evaluate_pred(&TypePred::True));
        assert!(!algebra.evaluate_pred(&TypePred::False));
        assert!(algebra.evaluate_pred(&TypePred::HasType(2))); // Int is inhabited
        assert!(algebra.evaluate_pred(&TypePred::Subtype { sub: 2, sup: 1 })); // Int <: Number
        assert!(!algebra.evaluate_pred(&TypePred::Subtype { sub: 1, sup: 2 })); // Number ≮: Int
    }

    #[test]
    fn type_algebra_satisfiable() {
        let sys = test_system();
        let algebra = TypeSystemAlgebra::new(sys);

        assert!(algebra.is_satisfiable_pred(&TypePred::True));
        assert!(!algebra.is_satisfiable_pred(&TypePred::False));
        assert!(algebra.is_satisfiable_pred(&TypePred::HasType(2)));
        assert!(!algebra.is_satisfiable_pred(&TypePred::HasType(99))); // unknown type
    }

    #[test]
    fn type_algebra_implies() {
        let sys = test_system();
        let algebra = TypeSystemAlgebra::new(sys);

        // Int <: Number implies Int <: Top (transitivity)
        let p = TypePred::Subtype { sub: 2, sup: 1 };
        let q = TypePred::Subtype { sub: 2, sup: 0 };
        assert!(algebra.implies_pred(&p, &q));

        // Int <: Number does NOT imply String <: Number
        let r = TypePred::Subtype { sub: 4, sup: 1 };
        assert!(!algebra.implies_pred(&p, &r));
    }

    #[test]
    fn type_algebra_and_or_not() {
        let sys = test_system();
        let algebra = TypeSystemAlgebra::new(sys);

        let int_inhabited = TypePred::HasType(2);
        let string_inhabited = TypePred::HasType(4);

        // And: both inhabited
        let both = TypePred::And(
            Box::new(int_inhabited.clone()),
            Box::new(string_inhabited.clone()),
        );
        assert!(algebra.evaluate_pred(&both));

        // Or: at least one
        let either = TypePred::Or(
            Box::new(int_inhabited.clone()),
            Box::new(TypePred::False),
        );
        assert!(algebra.evaluate_pred(&either));

        // Not: negation
        let not_false = TypePred::Not(Box::new(TypePred::False));
        assert!(algebra.evaluate_pred(&not_false));
    }

    // ── RefinementTypeSystem ──

    #[test]
    fn refinement_base_subtype() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::new(theory.clone(), store.clone(), HashMap::new());
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        let env = ref_sys.empty_env();
        let int_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(2);
        let number_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(1);

        // Base <: Base: Int <: Number
        assert!(ref_sys.is_subtype(&env, &int_base, &number_base));
        // Not reverse
        assert!(!ref_sys.is_subtype(&env, &number_base, &int_base));
    }

    #[test]
    fn refinement_refined_to_base() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::new(theory.clone(), store.clone(), HashMap::new());
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        let env = ref_sys.empty_env();
        // { x: Int | Int <: Number } — a satisfied predicate
        let refined_int = RefType::Refined(RefinedType {
            base: 2,
            var: "x".to_string(),
            predicate: SubtypeConstraint { sub: 2, sup: 1 },
        });
        let number_base = RefType::Base(1);

        // Refined(Int, pred) <: Base(Number) — should succeed since Int <: Number
        assert!(ref_sys.is_subtype(&env, &refined_int, &number_base));
    }

    #[test]
    fn refinement_inhabited() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::new(theory.clone(), store.clone(), HashMap::new());
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        let env = ref_sys.empty_env();

        // Base type: inhabited
        let int_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(2);
        assert!(ref_sys.is_inhabited(&env, &int_base));

        // Refined with satisfiable predicate: inhabited
        let refined_ok = RefType::Refined(RefinedType {
            base: 2,
            var: "x".to_string(),
            predicate: SubtypeConstraint { sub: 2, sup: 1 }, // Int <: Number (true)
        });
        assert!(ref_sys.is_inhabited(&env, &refined_ok));
    }

    #[test]
    fn refinement_join_drops_predicate() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::new(theory.clone(), store.clone(), HashMap::new());
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        let env = ref_sys.empty_env();
        let int_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(2);
        let float_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(3);

        // join(Int, Float) = Number (as base type)
        let result = ref_sys.join(&env, &int_base, &float_base);
        assert_eq!(result, Some(RefType::Base(1))); // Number
    }

    #[test]
    fn refinement_top_bottom() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::with_bounds(
            theory.clone(), store.clone(), HashMap::new(), 0, 6,
        );
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        assert_eq!(ref_sys.top(), Some(RefType::Base(0))); // Top
        assert_eq!(ref_sys.bottom(), Some(RefType::Base(6))); // Bottom
    }

    // ── RT9: Substitution propagation ──

    #[test]
    fn apply_substitution_base_type_passthrough() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::with_bounds(
            theory.clone(), store.clone(), HashMap::new(), 0, 6,
        );
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        let base_ty: RefType<TypeId, SubtypeConstraint> = RefType::Base(2); // Int
        let constraint = SubtypeConstraint { sub: 2, sup: 1 }; // Int <: Number

        let result = ref_sys.apply_substitution(&base_ty, "x", &constraint);
        assert_eq!(result, Some(RefType::Base(2)), "base type should pass through unchanged");
    }

    #[test]
    fn apply_substitution_mismatched_var() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::with_bounds(
            theory.clone(), store.clone(), HashMap::new(), 0, 6,
        );
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        let refined = RefType::Refined(RefinedType {
            base: 2, // Int
            var: "x".to_string(),
            predicate: SubtypeConstraint { sub: 2, sup: 1 }, // Int <: Number
        });
        let constraint = SubtypeConstraint { sub: 3, sup: 1 }; // Float <: Number

        // Substituting "y" when binding is "x" → pass through
        let result = ref_sys.apply_substitution(&refined, "y", &constraint);
        assert_eq!(result, Some(refined), "mismatched var should pass through");
    }

    #[test]
    fn apply_substitution_matching_var_satisfiable() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::with_bounds(
            theory.clone(), store.clone(), HashMap::new(), 0, 6,
        );
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        let refined = RefType::Refined(RefinedType {
            base: 2, // Int
            var: "x".to_string(),
            predicate: SubtypeConstraint { sub: 2, sup: 1 }, // Int <: Number (always true)
        });
        // The value constraint is consistent with the predicate
        let value_constraint = SubtypeConstraint { sub: 2, sup: 0 }; // Int <: Top

        let result = ref_sys.apply_substitution(&refined, "x", &value_constraint);
        assert!(result.is_some(), "satisfiable substitution should succeed");
        assert_eq!(result, Some(RefType::Base(2)), "should reduce to base type");
    }

    #[test]
    fn value_satisfies_refinement_base_always_true() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::with_bounds(
            theory.clone(), store.clone(), HashMap::new(), 0, 6,
        );
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        let base_ty: RefType<TypeId, SubtypeConstraint> = RefType::Base(2);
        let constraint = SubtypeConstraint { sub: 999, sup: 888 };

        assert!(ref_sys.value_satisfies_refinement(&base_ty, &constraint),
            "base type has no predicate — always satisfied");
    }

    #[test]
    fn value_satisfies_refinement_consistent() {
        let (theory, store) = test_lattice();
        let base_sys = LatticeTypeSystem::with_bounds(
            theory.clone(), store.clone(), HashMap::new(), 0, 6,
        );
        let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

        let refined = RefType::Refined(RefinedType {
            base: 2,
            var: "x".to_string(),
            predicate: SubtypeConstraint { sub: 2, sup: 1 }, // Int <: Number
        });
        let consistent = SubtypeConstraint { sub: 2, sup: 0 }; // Int <: Top

        assert!(ref_sys.value_satisfies_refinement(&refined, &consistent),
            "consistent constraint should satisfy refinement");
    }

    // ── BooleanAlgebra integration ──

    #[cfg(feature = "symbolic-automata")]
    mod boolean_algebra_tests {
        use super::*;
        use crate::symbolic::BooleanAlgebra;

        #[test]
        fn type_algebra_boolean_algebra_contract() {
            let sys = test_system();
            let algebra = TypeSystemAlgebra::new(sys);

            let t = algebra.true_pred();
            let f = algebra.false_pred();

            // true ∧ false = false
            let tf = algebra.and(&t, &f);
            assert!(!algebra.is_satisfiable(&tf));

            // true ∨ false = true
            let t_or_f = algebra.or(&t, &f);
            assert!(algebra.is_satisfiable(&t_or_f));

            // ¬false = true
            let not_f = algebra.not(&f);
            assert!(algebra.is_satisfiable(&not_f));

            // witness(HasType(Int)) = Some(Int)
            let has_int = TypePred::HasType(2);
            assert_eq!(algebra.witness(&has_int), Some(2));

            // witness(false) = None
            assert_eq!(algebra.witness(&f), None);
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    // SetTheoreticTypeSystem tests (Sprint RT3)
    // ══════════════════════════════════════════════════════════════════════════

    #[cfg(feature = "tree-automata")]
    mod set_theoretic_tests {
        use super::*;
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::{Term, TreeAutomaton, TreeTransition};

        /// Build a simple type system with constructors and type definitions:
        ///
        /// Constructors:
        ///   Zero : () → Nat          (arity 0)
        ///   Succ : (Nat) → Nat       (arity 1)
        ///   True : () → Bool         (arity 0)
        ///   False : () → Bool        (arity 0)
        ///   Pair : (Any, Any) → Pair (arity 2)
        ///
        /// Named types:
        ///   Nat  — accepts Zero and Succ(Nat)
        ///   Bool — accepts True and False
        ///   Any  — accepts everything (Top)
        fn test_set_system() -> SetTheoreticTypeSystem {
            let mut ctors = HashMap::new();
            ctors.insert("Zero".to_string(), 0);
            ctors.insert("Succ".to_string(), 1);
            ctors.insert("True".to_string(), 0);
            ctors.insert("False".to_string(), 0);
            ctors.insert("Pair".to_string(), 2);

            let mut sys = SetTheoreticTypeSystem::new(ctors);

            // Nat automaton: state 0 = Nat (accepting)
            //   Zero → q0, Succ(q0) → q0
            let mut nat_aut = TreeAutomaton::new();
            let q0 = nat_aut.add_state(true);
            nat_aut.add_transition(TreeTransition::leaf("Zero", q0, BooleanWeight(true)));
            nat_aut.add_transition(TreeTransition::unary("Succ", q0, q0, BooleanWeight(true)));
            sys.define_type("Nat", nat_aut);

            // Bool automaton: state 0 = Bool (accepting)
            //   True → q0, False → q0
            let mut bool_aut = TreeAutomaton::new();
            let q0 = bool_aut.add_state(true);
            bool_aut.add_transition(TreeTransition::leaf("True", q0, BooleanWeight(true)));
            bool_aut.add_transition(TreeTransition::leaf("False", q0, BooleanWeight(true)));
            sys.define_type("Bool", bool_aut);

            sys
        }

        // ── Emptiness check ──

        #[test]
        fn set_empty_automaton_is_empty() {
            let aut: TreeAutomaton<BooleanWeight> = TreeAutomaton::new();
            assert!(SetTheoreticTypeSystem::is_empty(&aut));
        }

        #[test]
        fn set_nat_automaton_not_empty() {
            let sys = test_set_system();
            let nat_aut = sys.type_to_automaton(&SetType::Atom("Nat".to_string()));
            assert!(!SetTheoreticTypeSystem::is_empty(&nat_aut));
        }

        // ── Basic subtyping ──

        #[test]
        fn set_reflexive_subtype() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            assert!(sys.is_subtype(&env, &nat, &nat));
        }

        #[test]
        fn set_nat_subtype_top() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            // Nat <: Top (all Nat values are values)
            assert!(sys.is_subtype(&env, &nat, &SetType::Top));
        }

        #[test]
        fn set_bottom_subtype_nat() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            // Bottom <: Nat (empty set ⊆ any set)
            assert!(sys.is_subtype(&env, &SetType::Bottom, &nat));
        }

        #[test]
        fn set_nat_not_subtype_bool() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let bool_ty = SetType::Atom("Bool".to_string());
            // Nat ⊄ Bool (Zero is a Nat but not a Bool)
            assert!(!sys.is_subtype(&env, &nat, &bool_ty));
        }

        #[test]
        fn set_bool_not_subtype_nat() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let bool_ty = SetType::Atom("Bool".to_string());
            // Bool ⊄ Nat (True is a Bool but not a Nat)
            assert!(!sys.is_subtype(&env, &bool_ty, &nat));
        }

        // ── Union types ──

        #[test]
        fn set_nat_subtype_nat_union_bool() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let bool_ty = SetType::Atom("Bool".to_string());
            let union = SetType::Union(Box::new(nat.clone()), Box::new(bool_ty));
            // Nat <: (Nat | Bool)
            assert!(sys.is_subtype(&env, &nat, &union));
        }

        #[test]
        fn set_union_not_subtype_nat() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let bool_ty = SetType::Atom("Bool".to_string());
            let union = SetType::Union(Box::new(nat.clone()), Box::new(bool_ty));
            // (Nat | Bool) ⊄ Nat (True ∈ (Nat|Bool) but True ∉ Nat)
            assert!(!sys.is_subtype(&env, &union, &nat));
        }

        // ── Intersection types ──

        #[test]
        fn set_intersection_of_disjoint_is_empty() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let bool_ty = SetType::Atom("Bool".to_string());
            let intersection = SetType::Intersection(Box::new(nat), Box::new(bool_ty));
            // Nat ∩ Bool = ∅ (no value is both a Nat and a Bool)
            assert!(!sys.is_inhabited(&env, &intersection));
        }

        #[test]
        fn set_nat_intersection_top_is_nat() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let intersection = SetType::Intersection(Box::new(nat.clone()), Box::new(SetType::Top));
            // Nat ∩ Top = Nat (subtype equivalence)
            assert!(sys.is_subtype(&env, &intersection, &nat));
            assert!(sys.is_subtype(&env, &nat, &intersection));
        }

        // ── Negation types ──

        #[test]
        fn set_negation_top_is_bottom() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let not_top = SetType::Negation(Box::new(SetType::Top));
            // ¬Top = ∅ (Bottom)
            assert!(!sys.is_inhabited(&env, &not_top));
        }

        // ── Type checking with terms ──

        #[test]
        fn set_check_zero_is_nat() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let zero = Term::leaf("Zero");
            assert!(sys.check(&env, &zero, &nat));
        }

        #[test]
        fn set_check_succ_zero_is_nat() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let succ_zero = Term::new("Succ", vec![Term::leaf("Zero")]);
            assert!(sys.check(&env, &succ_zero, &nat));
        }

        #[test]
        fn set_check_true_is_bool() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let bool_ty = SetType::Atom("Bool".to_string());
            let true_term = Term::leaf("True");
            assert!(sys.check(&env, &true_term, &bool_ty));
        }

        #[test]
        fn set_check_true_not_nat() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let true_term = Term::leaf("True");
            assert!(!sys.check(&env, &true_term, &nat));
        }

        // ── Inference ──

        #[test]
        fn set_infer_zero() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let zero = Term::leaf("Zero");
            let types = sys.infer(&env, &zero);
            // Zero should be inferred as Nat (not Bool)
            assert!(types.contains(&SetType::Atom("Nat".to_string())));
            assert!(!types.contains(&SetType::Atom("Bool".to_string())));
        }

        // ── Join / Meet ──

        #[test]
        fn set_join_is_union() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let bool_ty = SetType::Atom("Bool".to_string());
            let joined = sys.join(&env, &nat, &bool_ty);
            assert_eq!(
                joined,
                Some(SetType::Union(
                    Box::new(nat.clone()),
                    Box::new(bool_ty.clone()),
                ))
            );
        }

        #[test]
        fn set_meet_is_intersection() {
            let sys = test_set_system();
            let env = sys.empty_env();
            let nat = SetType::Atom("Nat".to_string());
            let bool_ty = SetType::Atom("Bool".to_string());
            let met = sys.meet(&env, &nat, &bool_ty);
            assert_eq!(
                met,
                Some(SetType::Intersection(
                    Box::new(nat.clone()),
                    Box::new(bool_ty.clone()),
                ))
            );
        }

        // ── Top / Bottom ──

        #[test]
        fn set_top_bottom() {
            let sys = test_set_system();
            assert_eq!(sys.top(), Some(SetType::Top));
            assert_eq!(sys.bottom(), Some(SetType::Bottom));
        }

        // ── Display ──

        #[test]
        fn set_type_display() {
            let ty = SetType::Union(
                Box::new(SetType::Atom("Nat".to_string())),
                Box::new(SetType::Negation(Box::new(SetType::Atom("Bool".to_string())))),
            );
            assert_eq!(format!("{ty}"), "(Nat | ~Bool)");
        }
    }
}
