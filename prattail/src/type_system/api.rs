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

    /// Bottom type (if the system has one). This is a subtype of all types.
    fn bottom(&self) -> Option<Self::Type> {
        None
    }
}
