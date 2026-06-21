use super::*;

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
    Subtype { sub: S::Type, sup: S::Type },
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
            },
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
            TypePred::True | TypePred::False => {},
            TypePred::HasType(ty) => ty.hash(state),
            TypePred::Subtype { sub, sup } => {
                sub.hash(state);
                sup.hash(state);
            },
            TypePred::And(a, b) | TypePred::Or(a, b) => {
                a.hash(state);
                b.hash(state);
            },
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
            TypePred::Subtype { sub, sup } => self.system.is_subtype(&self.env, sub, sup),
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
            TypePred::Subtype { sub, sup } => self.system.is_subtype(&self.env, sub, sup),
            TypePred::And(a, b) => self.is_satisfiable_pred(a) && self.is_satisfiable_pred(b),
            TypePred::Or(a, b) => self.is_satisfiable_pred(a) || self.is_satisfiable_pred(b),
            TypePred::Not(a) => !self.evaluate_pred(a),
        }
    }

    /// Check if predicate a implies predicate b.
    ///
    /// Returns true if `a ∧ ¬b` is unsatisfiable.
    pub fn implies_pred(&self, a: &TypePred<S>, b: &TypePred<S>) -> bool {
        let counter =
            TypePred::And(Box::new(a.clone()), Box::new(TypePred::Not(Box::new(b.clone()))));
        !self.is_satisfiable_pred(&counter)
    }
}

// ==============================================================================
// BooleanAlgebra implementation for TypeSystemAlgebra
// ==============================================================================

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
            },
            TypePred::Subtype { sub, sup } => {
                if self.system.is_subtype(&self.env, sub, sup) {
                    Some(sub.clone())
                } else {
                    None
                }
            },
            TypePred::And(a_inner, b_inner) => {
                // For conjunction, need a witness that satisfies both
                let wa = self.witness(a_inner)?;
                let wb = self.witness(b_inner)?;
                // Try meeting the two witnesses
                self.system.meet(&self.env, &wa, &wb)
            },
            TypePred::Or(a_inner, b_inner) => {
                self.witness(a_inner).or_else(|| self.witness(b_inner))
            },
            TypePred::Not(inner) => {
                if !self.evaluate_pred(inner) {
                    self.system.top()
                } else {
                    None
                }
            },
        }
    }

    fn evaluate(&self, pred: &TypePred<S>, elem: &S::Type) -> bool {
        match pred {
            TypePred::True => true,
            TypePred::False => false,
            TypePred::HasType(ty) => self.system.is_subtype(&self.env, elem, ty),
            TypePred::Subtype { sub, sup } => self.system.is_subtype(&self.env, sub, sup),
            TypePred::And(a, b) => self.evaluate(a, elem) && self.evaluate(b, elem),
            TypePred::Or(a, b) => self.evaluate(a, elem) || self.evaluate(b, elem),
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
pub struct RefinementTypeEnv<
    BaseEnv: Clone + fmt::Debug,
    C: Clone + fmt::Debug + Eq + Hash,
    Ty: Clone + fmt::Debug + Eq + Hash,
> {
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
    /// Phase 6E (predicated types): the spec-correct formulation is
    /// `P ⟹ Q is valid iff (P ∧ ¬Q) is unsatisfiable`. Earlier
    /// implementations checked "is Q consistent in a store where P
    /// holds" — that is *joint* satisfiability, not entailment, and
    /// returns true whenever P and Q have any common model
    /// (semantically distinct from ⟹). The corrected version lifts
    /// the constraints into the `TheoryAlgebra<T>` `BooleanAlgebra`
    /// wrapper (which exposes negation) and checks
    /// `!is_satisfiable(P ∧ ¬Q)`.
    pub fn predicate_entails(&self, premise: &T::Constraint, conclusion: &T::Constraint) -> bool {
        use crate::logict::{TheoryAlgebra, TheoryPred};
        use crate::symbolic::BooleanAlgebra;

        // 1024 is the same default search bound used by the runtime
        // guard evaluator (`generate_inline_guard_eval` in macros).
        let algebra = TheoryAlgebra::new(self.constraint_theory.clone(), 1024);
        let p = TheoryPred::Atom(premise.clone());
        let q = TheoryPred::Atom(conclusion.clone());
        let not_q = algebra.not(&q);
        let p_and_not_q = algebra.and(&p, &not_q);
        !algebra.is_satisfiable(&p_and_not_q)
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
                let Some(store_with_pred) =
                    self.constraint_theory.propagate(&store, &refined.predicate)
                else {
                    return None; // Original predicate was unsatisfiable
                };
                let Some(_store_final) = self
                    .constraint_theory
                    .propagate(&store_with_pred, constraint_value)
                else {
                    return None; // Value doesn't satisfy the predicate
                };

                // After ground substitution, the refinement is satisfied — return base type
                Some(RefType::Base(refined.base.clone()))
            },
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
                let Some(store_with_pred) =
                    self.constraint_theory.propagate(&store, &refined.predicate)
                else {
                    return false; // Predicate itself is unsatisfiable
                };
                self.constraint_theory
                    .propagate(&store_with_pred, value_constraint)
                    .is_some()
            },
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

    fn check(&self, env: &Self::TypeEnv, term: &Self::Term, ty: &Self::Type) -> bool {
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

    fn infer(&self, env: &Self::TypeEnv, term: &Self::Term) -> Vec<Self::Type> {
        self.base_system
            .infer(&env.base_env, term)
            .into_iter()
            .map(RefType::Base)
            .collect()
    }

    fn is_subtype(&self, env: &Self::TypeEnv, sub: &Self::Type, sup: &Self::Type) -> bool {
        let sub_base = Self::base_type(sub);
        let sup_base = Self::base_type(sup);

        // Base type must be a subtype
        if !self
            .base_system
            .is_subtype(&env.base_env, sub_base, sup_base)
        {
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
                self.constraint_theory
                    .propagate(&store, &r.predicate)
                    .is_some()
            },
            // Refined <: Refined → base subtype + P ⟹ Q
            (RefType::Refined(r1), RefType::Refined(r2)) => {
                self.predicate_entails(&r1.predicate, &r2.predicate)
            },
        }
    }

    fn join(&self, env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type> {
        let base_a = Self::base_type(a);
        let base_b = Self::base_type(b);
        let base_join = self.base_system.join(&env.base_env, base_a, base_b)?;
        // Join drops refinements (conservative: the result is a base type
        // that is a supertype of both refinements)
        Some(RefType::Base(base_join))
    }

    fn meet(&self, env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type> {
        let base_a = Self::base_type(a);
        let base_b = Self::base_type(b);
        let base_meet = self.base_system.meet(&env.base_env, base_a, base_b)?;
        // Meet drops refinements (conservative)
        Some(RefType::Base(base_meet))
    }

    fn extend(&self, env: &Self::TypeEnv, var: &str, ty: &Self::Type) -> Self::TypeEnv {
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

    fn is_inhabited(&self, env: &Self::TypeEnv, ty: &Self::Type) -> bool {
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
