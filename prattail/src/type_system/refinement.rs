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

#[path = "refinement/type_pred_lifecycle.rs"]
mod type_pred_lifecycle;

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
        evaluate_type_pred(pred, |node| match node {
            TypePredLeaf::True => true,
            TypePredLeaf::False => false,
            TypePredLeaf::HasType(ty) => self.system.is_inhabited(&self.env, ty),
            TypePredLeaf::Subtype { sub, sup } => self.system.is_subtype(&self.env, sub, sup),
        })
    }

    /// Check satisfiability of a type predicate.
    pub fn is_satisfiable_pred(&self, pred: &TypePred<S>) -> bool {
        enum Task<'pred, S: TypeSystem> {
            Visit(&'pred TypePred<S>),
            AndRight(&'pred TypePred<S>),
            OrRight(&'pred TypePred<S>),
        }

        let mut tasks = vec![Task::Visit(pred)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TypePred::True) => values.push(true),
                Task::Visit(TypePred::False) => values.push(false),
                Task::Visit(TypePred::HasType(ty)) => {
                    values.push(self.system.is_inhabited(&self.env, ty));
                },
                Task::Visit(TypePred::Subtype { sub, sup }) => {
                    values.push(self.system.is_subtype(&self.env, sub, sup));
                },
                Task::Visit(TypePred::And(left, right)) => {
                    tasks.push(Task::AndRight(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TypePred::Or(left, right)) => {
                    tasks.push(Task::OrRight(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TypePred::Not(inner)) => values.push(!self.evaluate_pred(inner)),
                Task::AndRight(right) => {
                    if values
                        .pop()
                        .expect("type-predicate satisfiability PDA lost its left value")
                    {
                        tasks.push(Task::Visit(right));
                    } else {
                        values.push(false);
                    }
                },
                Task::OrRight(right) => {
                    if values
                        .pop()
                        .expect("type-predicate satisfiability PDA lost its left value")
                    {
                        values.push(true);
                    } else {
                        tasks.push(Task::Visit(right));
                    }
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("type-predicate satisfiability PDA produced no value")
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
        enum Task<'pred, S: TypeSystem> {
            Visit(&'pred TypePred<S>),
            AndRight(&'pred TypePred<S>),
            AndMeet(S::Type),
            OrRight(&'pred TypePred<S>),
        }

        let mut tasks = vec![Task::Visit(a)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TypePred::True) => values.push(self.system.top()),
                Task::Visit(TypePred::False) => values.push(None),
                Task::Visit(TypePred::HasType(ty)) => {
                    values.push(self.system.is_inhabited(&self.env, ty).then(|| ty.clone()))
                },
                Task::Visit(TypePred::Subtype { sub, sup }) => values.push(
                    self.system
                        .is_subtype(&self.env, sub, sup)
                        .then(|| sub.clone()),
                ),
                Task::Visit(TypePred::And(left, right)) => {
                    tasks.push(Task::AndRight(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TypePred::Or(left, right)) => {
                    tasks.push(Task::OrRight(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TypePred::Not(inner)) => values.push(
                    (!self.evaluate_pred(inner))
                        .then(|| self.system.top())
                        .flatten(),
                ),
                Task::AndRight(right) => {
                    if let Some(left) = values
                        .pop()
                        .expect("type-predicate witness PDA lost its left witness")
                    {
                        tasks.push(Task::AndMeet(left));
                        tasks.push(Task::Visit(right));
                    } else {
                        values.push(None);
                    }
                },
                Task::AndMeet(left) => {
                    let right = values
                        .pop()
                        .expect("type-predicate witness PDA lost its right witness");
                    values.push(right.and_then(|right| self.system.meet(&self.env, &left, &right)));
                },
                Task::OrRight(right) => {
                    let left = values
                        .pop()
                        .expect("type-predicate witness PDA lost its left witness");
                    if left.is_some() {
                        values.push(left);
                    } else {
                        tasks.push(Task::Visit(right));
                    }
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("type-predicate witness PDA produced no value")
    }

    fn evaluate(&self, pred: &TypePred<S>, elem: &S::Type) -> bool {
        evaluate_type_pred(pred, |node| match node {
            TypePredLeaf::True => true,
            TypePredLeaf::False => false,
            TypePredLeaf::HasType(ty) => self.system.is_subtype(&self.env, elem, ty),
            TypePredLeaf::Subtype { sub, sup } => self.system.is_subtype(&self.env, sub, sup),
        })
    }
}

enum TypePredLeaf<'pred, S: TypeSystem> {
    True,
    False,
    HasType(&'pred S::Type),
    Subtype { sub: &'pred S::Type, sup: &'pred S::Type },
}

fn evaluate_type_pred<S, F>(pred: &TypePred<S>, mut leaf: F) -> bool
where
    S: TypeSystem,
    F: for<'pred> FnMut(TypePredLeaf<'pred, S>) -> bool,
{
    enum Task<'pred, S: TypeSystem> {
        Visit(&'pred TypePred<S>),
        Not,
        AndRight(&'pred TypePred<S>),
        OrRight(&'pred TypePred<S>),
    }

    let mut tasks = vec![Task::Visit(pred)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(TypePred::True) => values.push(leaf(TypePredLeaf::True)),
            Task::Visit(TypePred::False) => values.push(leaf(TypePredLeaf::False)),
            Task::Visit(TypePred::HasType(ty)) => {
                values.push(leaf(TypePredLeaf::HasType(ty)));
            },
            Task::Visit(TypePred::Subtype { sub, sup }) => {
                values.push(leaf(TypePredLeaf::Subtype { sub, sup }));
            },
            Task::Visit(TypePred::And(left, right)) => {
                tasks.push(Task::AndRight(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(TypePred::Or(left, right)) => {
                tasks.push(Task::OrRight(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(TypePred::Not(inner)) => {
                tasks.push(Task::Not);
                tasks.push(Task::Visit(inner));
            },
            Task::Not => {
                let value = values
                    .pop()
                    .expect("type-predicate PDA lost its negated value");
                values.push(!value);
            },
            Task::AndRight(right) => {
                if values
                    .pop()
                    .expect("type-predicate PDA lost its left conjunction value")
                {
                    tasks.push(Task::Visit(right));
                } else {
                    values.push(false);
                }
            },
            Task::OrRight(right) => {
                if values
                    .pop()
                    .expect("type-predicate PDA lost its left disjunction value")
                {
                    values.push(true);
                } else {
                    tasks.push(Task::Visit(right));
                }
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("type-predicate PDA produced no value")
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
type ExactRefinementDecider<T> = fn(
    &crate::logict::TheoryAlgebra<T>,
    &crate::logict::TheoryPred<T>,
) -> crate::algebra_tower::Sat3;

#[derive(Clone, Copy, Debug)]
enum RefinementDecisionMode<T: ConstraintTheory> {
    /// Bounded certificate search. `DontKnow` is preserved and fails closed at
    /// the Boolean `TypeSystem` boundary.
    RejectSafe,
    /// A statically trusted complete procedure with checked positive witnesses.
    Exact(ExactRefinementDecider<T>),
}

#[derive(Clone, Debug)]
pub struct RefinementTypeSystem<S: TypeSystem, T: ConstraintTheory> {
    /// The base type system.
    pub base_system: S,
    /// The constraint theory for predicate analysis.
    pub constraint_theory: T,
    /// Search bound for LogicT-based entailment checking.
    pub search_bound: usize,
    /// Whether this instance owns only reject-safe search or a statically
    /// authorized exact decision procedure.
    decision_mode: RefinementDecisionMode<T>,
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
            decision_mode: RefinementDecisionMode::RejectSafe,
        }
    }

    /// Create a refinement system backed by a complete decision procedure.
    ///
    /// The additional trait bound is the authority gate: arbitrary runtime
    /// grammar data cannot opt into classical conclusions. Every positive
    /// result is rechecked against the whole predicate by [`TheoryAlgebra`].
    pub fn new_exact(base_system: S, constraint_theory: T, search_bound: usize) -> Self
    where
        T: crate::logict::DecidableConstraintTheory,
    {
        fn decide<T>(
            algebra: &crate::logict::TheoryAlgebra<T>,
            predicate: &crate::logict::TheoryPred<T>,
        ) -> crate::algebra_tower::Sat3
        where
            T: crate::logict::DecidableConstraintTheory,
        {
            use crate::logict::ExactSatisfiability;
            match algebra.decide_exact_checked(predicate) {
                ExactSatisfiability::Satisfiable(_) => crate::algebra_tower::Sat3::Sat,
                ExactSatisfiability::Unsatisfiable => crate::algebra_tower::Sat3::Unsat,
            }
        }

        RefinementTypeSystem {
            base_system,
            constraint_theory,
            search_bound,
            decision_mode: RefinementDecisionMode::Exact(decide::<T>),
        }
    }

    fn classify_predicate(
        &self,
        predicate: &crate::logict::TheoryPred<T>,
    ) -> crate::algebra_tower::Sat3 {
        use crate::algebra_tower::RejectSafeAlgebra;
        let algebra =
            crate::logict::TheoryAlgebra::new(self.constraint_theory.clone(), self.search_bound);
        match self.decision_mode {
            RefinementDecisionMode::RejectSafe => algebra.is_satisfiable_3v(predicate),
            RefinementDecisionMode::Exact(decide) => decide(&algebra, predicate),
        }
    }

    /// Extract the base type from a RefType.
    pub fn base_type(ty: &RefType<S::Type, T::Constraint>) -> &S::Type {
        match ty {
            RefType::Base(t) => t,
            RefType::Refined(r) => &r.base,
        }
    }

    /// Classify predicate satisfiability without erasing bounded-search
    /// uncertainty.
    pub fn predicate_satisfiability(&self, pred: &T::Constraint) -> crate::algebra_tower::Sat3 {
        self.classify_predicate(&crate::logict::TheoryPred::Atom(pred.clone()))
    }

    /// Check whether a predicate has a certificate-checked witness.
    ///
    /// `DontKnow` fails closed; `propagate(...).is_some()` is not sufficient
    /// because it denotes only "not proven inconsistent" and may carry solver
    /// uncertainty.
    pub fn predicate_satisfiable(&self, pred: &T::Constraint) -> bool {
        matches!(self.predicate_satisfiability(pred), crate::algebra_tower::Sat3::Sat)
    }

    /// Prove that a predicate is valid for every assignment.
    fn predicate_tautological(&self, pred: &T::Constraint) -> bool {
        use crate::algebra_tower::{RejectSafeAlgebra, Sat3};
        use crate::logict::{TheoryAlgebra, TheoryPred};

        let algebra = TheoryAlgebra::new(self.constraint_theory.clone(), self.search_bound);
        let negated = algebra.pseudo_complement(&TheoryPred::Atom(pred.clone()));
        matches!(self.classify_predicate(&negated), Sat3::Unsat)
    }

    /// Check a conjunction by requiring a concrete witness for the whole
    /// predicate rather than treating successful propagation as a proof.
    fn conjunction_satisfiable(&self, left: &T::Constraint, right: &T::Constraint) -> bool {
        use crate::algebra_tower::{RejectSafeAlgebra, Sat3};
        use crate::logict::{TheoryAlgebra, TheoryPred};

        let algebra = TheoryAlgebra::new(self.constraint_theory.clone(), self.search_bound);
        let conjunction =
            algebra.and(&TheoryPred::Atom(left.clone()), &TheoryPred::Atom(right.clone()));
        matches!(self.classify_predicate(&conjunction), Sat3::Sat)
    }

    /// Check predicate entailment: does P(x) imply Q(x)?
    ///
    /// Phase 6E (predicated types): the spec-correct formulation is
    /// `P ⟹ Q is valid iff (P ∧ ¬Q) is unsatisfiable`. Earlier
    /// implementations checked "is Q consistent in a store where P
    /// holds" — that is *joint* satisfiability, not entailment, and
    /// returns true whenever P and Q have any common model
    /// (semantically distinct from ⟹). The corrected version lifts the
    /// constraints into the reject-safe `TheoryAlgebra<T>` and asks whether
    /// `P ∧ ¬Q` is *proven* unsatisfiable. A found witness refutes entailment;
    /// a bounded no-witness result is `DontKnow` and fails closed.
    ///
    /// When the `smt` feature is enabled, the concrete
    /// [`Z3Theory`](crate::logict_smt::Z3Theory) path preserves the solver's
    /// three-valued result. All other theories use the same bounded reject-safe
    /// search.
    #[cfg(not(feature = "smt"))]
    pub fn predicate_entails(&self, premise: &T::Constraint, conclusion: &T::Constraint) -> bool {
        use crate::algebra_tower::{RejectSafeAlgebra, Sat3};
        use crate::logict::{TheoryAlgebra, TheoryPred};

        let algebra = TheoryAlgebra::new(self.constraint_theory.clone(), self.search_bound);
        let p = TheoryPred::Atom(premise.clone());
        let q = TheoryPred::Atom(conclusion.clone());
        let not_q = algebra.pseudo_complement(&q);
        let p_and_not_q = algebra.and(&p, &not_q);
        matches!(self.classify_predicate(&p_and_not_q), Sat3::Unsat)
    }

    /// `smt`-feature variant of [`Self::predicate_entails`].
    ///
    /// For every non-`Z3Theory` constraint domain this follows the default build's
    /// reject-safe path because the concrete downcast fails.
    ///
    /// ONLY for the concrete [`Z3Theory`](crate::logict_smt::Z3Theory) domain (a
    /// genuine SMT constraint — mixed numeric/bitvector — the verified search cannot
    /// decide) Z3 classifies `P ∧ ¬Q` through
    /// [`is_satisfiable_3v`](crate::logict_smt::is_satisfiable_3v):
    ///
    /// - `Unsat` ⇒ entailment PROVEN ⇒ `true`.
    /// - `Sat` ⇒ a genuine counter-model exists (certificate-checked via
    ///   [`checked_witness`](crate::logict_smt::checked_witness)) ⇒ entailment
    ///   FAILS ⇒ `false`.
    /// - `DontKnow` ⇒ do NOT claim entailment (a false-positive would accept an
    ///   invalid subtype) ⇒ `false` (SOUND, incomplete). Never a silent `true`;
    ///   `DontKnow` is never collapsed to Unsat/true.
    #[cfg(feature = "smt")]
    pub fn predicate_entails(&self, premise: &T::Constraint, conclusion: &T::Constraint) -> bool {
        use crate::algebra_tower::{RejectSafeAlgebra, Sat3};
        use crate::logict::{TheoryAlgebra, TheoryPred};
        use crate::logict_smt::{self, SmtConstraint, Z3Theory};
        use std::any::Any;

        // The Z3 branch applies only when both the theory and constraints have the
        // corresponding concrete types. It preserves the three-valued solver
        // result directly; every other theory falls through to bounded
        // reject-safe search below.
        let theory_any: &dyn Any = &self.constraint_theory;
        if let Some(z3) = theory_any.downcast_ref::<Z3Theory>() {
            let premise_any: &dyn Any = premise;
            let conclusion_any: &dyn Any = conclusion;
            if let (Some(p_smt), Some(q_smt)) = (
                premise_any.downcast_ref::<SmtConstraint>(),
                conclusion_any.downcast_ref::<SmtConstraint>(),
            ) {
                // P ∧ ¬Q over the self-contained SMT constraint AST.
                let p_and_not_q_smt = SmtConstraint::And(
                    Box::new(p_smt.clone()),
                    Box::new(SmtConstraint::Not(Box::new(q_smt.clone()))),
                );
                return match logict_smt::is_satisfiable_3v(z3, &p_and_not_q_smt) {
                    // P ∧ ¬Q unsatisfiable ⇒ P ⟹ Q is valid.
                    Sat3::Unsat => true,
                    // A genuine, certificate-checked counter-model ⇒ entailment fails.
                    Sat3::Sat => {
                        let _counter = logict_smt::checked_witness(z3, &p_and_not_q_smt);
                        false
                    },
                    // Undecided ⇒ do NOT claim entailment (a false-positive entailment
                    // would accept an invalid subtype): return `false` — SOUND though
                    // incomplete. Never a silent `true`; `DontKnow` is never collapsed
                    // to Unsat/true.
                    Sat3::DontKnow => false,
                };
            }
        }

        // Default bounded reject-safe path for every non-Z3 theory.
        let algebra = TheoryAlgebra::new(self.constraint_theory.clone(), self.search_bound);
        let p = TheoryPred::Atom(premise.clone());
        let q = TheoryPred::Atom(conclusion.clone());
        let not_q = algebra.pseudo_complement(&q);
        let p_and_not_q = algebra.and(&p, &not_q);
        matches!(self.classify_predicate(&p_and_not_q), Sat3::Unsat)
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
    /// - `None` if the conjunction is refuted or remains undetermined within the
    ///   configured search bound
    ///
    /// This is used at **compile time** to analyze guard propagation through
    /// substitutions in Comm rules. Acceptance requires a checked witness; a
    /// bounded no-witness result cannot authorize the substitution.
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

                if !self.conjunction_satisfiable(&refined.predicate, constraint_value) {
                    return None;
                }

                // After ground substitution, the refinement is satisfied — return base type
                Some(RefType::Base(refined.base.clone()))
            },
        }
    }

    /// Check whether a value (represented as a constraint) satisfies a refinement type.
    ///
    /// This is the compile-time validation: given `{ x: T | P(x) }` and a concrete
    /// value constraint `V`, require a checked witness for `P ∧ V`. Refutation and
    /// bounded uncertainty both fail closed.
    pub fn value_satisfies_refinement(
        &self,
        ty: &RefType<S::Type, T::Constraint>,
        value_constraint: &T::Constraint,
    ) -> bool {
        match ty {
            RefType::Base(_) => true, // No predicate to check
            RefType::Refined(refined) => {
                self.conjunction_satisfiable(&refined.predicate, value_constraint)
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
                // { x: T | true } <: { x: T | Q } iff ¬Q is unsatisfiable.
                self.predicate_tautological(&r.predicate)
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
