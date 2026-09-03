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
//! `TypeSystem` implementations are compile-time analyses. The classical
//! `TypeSystemAlgebra` bridge is available only to a
//! `DecidableFiniteTypeSystem`, whose complete deterministic semantic-witness
//! universe makes Boolean complement and unsatisfiability exact. These analyses execute
//! during `language!` macro expansion to emit lints and inform codegen; only
//! generated relations and predicate checks enter the generated binary.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;

#[cfg(test)]
use crate::lattice_theory::SubtypeConstraint;
use crate::lattice_theory::{FrozenLatticeTheory, LatticeStore, LatticeTheory, TypeId};
use crate::logict::ConstraintTheory;

mod api;
pub use api::*;
mod lattice;
pub use lattice::*;
mod refinement;
pub use refinement::*;
mod dispatch;
pub use dispatch::*;
mod settheoretic;
pub use settheoretic::*;

#[cfg(test)]
mod tests;
#[cfg(test)]
pub(crate) use dispatch::is_complement_predicate;
