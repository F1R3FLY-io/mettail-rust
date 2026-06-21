//! # Predicate Dispatch Automaton — Module Selection via Algebraic Variety Classification
//!
//! Decomposes predicate formulas into algebraic "morphemes" (structural features),
//! classifies them into automata varieties (Eilenberg's variety theorem), and directs
//! only the applicable advanced automata modules (M1–M11) to run in Phase 7.
//!
//! **Eilenberg connection**: Rather than computing syntactic monoids at runtime
//! (exponential), we detect variety membership directly from formula AST structure
//! in O(|AST|) time. Feature extraction is a conservative approximation — it may
//! activate extra modules but never misses a needed one.
//!
//! ## Self-Referential Verification
//!
//! The dispatch algebra (`DispatchAlgebra`) implements M1's `BooleanAlgebra` trait,
//! enabling construction of a `SymbolicAutomaton<DispatchAlgebra>` that formally
//! verifies completeness (every valid predicate activates ≥ M1 + M10) and
//! consistency (no contradictory module combinations).

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::pipeline::CategoryInfo;
use crate::symbolic::{BooleanAlgebra, DecidabilityTier, PredicateExpr, SymbolicAutomaton};
use crate::weighted_mso::WeightedMsoFormula;
use crate::SyntaxItemSpec;

mod signature;
pub use signature::*;
mod features;
pub use features::*;

// crate-internal relation classifiers called by sibling modules + tests (were private fns):
pub(crate) use features::{is_cardinality_relation, is_equality_relation};
mod plan;
pub use plan::*;
mod algebra;
pub use algebra::*;
mod compile;
pub use compile::*;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod proptest_tests;
