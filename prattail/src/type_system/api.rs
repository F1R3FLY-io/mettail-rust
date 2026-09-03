use super::*;

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
/// - **Reflexivity**: `is_subtype(env, T, T) == true` for every semantic type
///   admitted by the implementation
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
    fn join(&self, env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type>;

    /// Meet (GLB): widest common subtype. None if no finite meet.
    fn meet(&self, env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type>;

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

    /// Bottom type (if the system has one). This is the uninhabited subtype of
    /// all types.
    fn bottom(&self) -> Option<Self::Type> {
        None
    }
}

/// Completeness authority for classical predicates over a finite semantic
/// witness domain.
///
/// [`TypeSystem`] alone supplies sound type-checking operations, but it does
/// not promise that an implementation can enumerate representatives of every
/// possible runtime value class. A
/// [`TypeSystemAlgebra`](super::TypeSystemAlgebra) needs that stronger premise
/// because Boolean complement and unsatisfiability quantify over values, not
/// merely over type syntax.
///
/// Implementations must return a terminating, complete enumeration of semantic
/// witness classes for the supplied environment and decide type membership for
/// each witness exactly. Every runtime value must be represented by a witness
/// with the same answers to every `HasType` predicate; duplicates are permitted
/// and affect only performance. The implementation must also recognize every
/// valid type appearing in a predicate and decide `is_subtype` exactly for those
/// types. Runtime DDL data cannot self-assert this native completeness
/// authority; a trusted compiler/verifier may instead derive an equivalent
/// checked runtime artifact from a complete finite declaration.
pub trait DecidableFiniteTypeSystem: TypeSystem {
    /// Finite representative of a semantic runtime-value equivalence class.
    type Witness: Clone + fmt::Debug + Eq + Hash + Send + Sync + 'static;

    /// Enumerate the complete semantic witness domain in deterministic order.
    fn complete_witness_universe(&self, env: &Self::TypeEnv) -> Vec<Self::Witness>;

    /// Decide whether a semantic witness has a type.
    fn witness_has_type(
        &self,
        env: &Self::TypeEnv,
        witness: &Self::Witness,
        ty: &Self::Type,
    ) -> bool;

    /// Decide whether a type representation belongs to the semantic type domain.
    fn is_valid_type(&self, env: &Self::TypeEnv, ty: &Self::Type) -> bool;

    /// Decide whether a witness representation belongs to the semantic domain.
    ///
    /// The default follows directly from [`Self::complete_witness_universe`].
    /// Implementations may override it to avoid allocating the enumeration.
    fn is_valid_witness(&self, env: &Self::TypeEnv, witness: &Self::Witness) -> bool {
        self.complete_witness_universe(env).contains(witness)
    }
}
