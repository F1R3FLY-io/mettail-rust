use super::*;

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
        LatticeTypeEnv { bindings: HashMap::new() }
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
                let (expected_arg_types, result_type) = self.constructor_types.get(head)?;
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
            },
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

    fn check(&self, env: &LatticeTypeEnv, term: &LatticeTerm, ty: &TypeId) -> bool {
        let mut store = self.store.clone();
        match self.infer_single(env, term, &mut store) {
            Some(inferred) => self.theory.is_subtype(&mut store, inferred, *ty),
            None => false,
        }
    }

    fn infer(&self, env: &LatticeTypeEnv, term: &LatticeTerm) -> Vec<TypeId> {
        let mut store = self.store.clone();
        match self.infer_single(env, term, &mut store) {
            Some(ty) => vec![ty],
            None => vec![],
        }
    }

    fn is_subtype(&self, _env: &LatticeTypeEnv, sub: &TypeId, sup: &TypeId) -> bool {
        let mut store = self.store.clone();
        self.theory.is_subtype(&mut store, *sub, *sup)
    }

    fn join(&self, _env: &LatticeTypeEnv, a: &TypeId, b: &TypeId) -> Option<TypeId> {
        let mut store = self.store.clone();
        self.theory.join(&mut store, *a, *b)
    }

    fn meet(&self, _env: &LatticeTypeEnv, a: &TypeId, b: &TypeId) -> Option<TypeId> {
        let mut store = self.store.clone();
        self.theory.meet(&mut store, *a, *b)
    }

    fn extend(&self, env: &LatticeTypeEnv, var: &str, ty: &TypeId) -> LatticeTypeEnv {
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
