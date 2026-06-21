//! WFST-based prediction for weighted dispatch.
//!
//! Provides the `PredictionWfst` — a per-category weighted finite state
//! transducer that ranks parse alternatives by weight. Given a token, the
//! predictor returns candidate `DispatchAction`s ordered by tropical weight
//! (lower = more likely), enabling the parser to try the most-likely path first.
//!
//! ## Architecture
//!
//! The prediction WFST is built at compile time during the PraTTaIL pipeline,
//! after FIRST/FOLLOW set computation. It encodes:
//!
//! - **Unambiguous tokens**: single transition, weight 0.0 (tropical one)
//! - **Ambiguous tokens**: multiple transitions weighted by declaration order
//!   and FIRST-set uniqueness analysis
//! - **Cross-category tokens unique to source**: weight 0.0 (deterministic)
//! - **Shared cross-category tokens**: weight based on overlap analysis
//!
//! ## Derived from lling-llang
//!
//! The `VectorWfst` and `WeightedTransition` types are minimal adaptations
//! from `lling-llang/src/wfst/`. Only the subset needed for prediction is
//! included (~150 LOC), not the full WFST algebra.

use std::collections::HashMap;

use crate::automata::semiring::{ContextWeight, Semiring, TropicalWeight};
use crate::prediction::{CrossCategoryOverlap, DispatchAction, FirstSet};
use crate::token_id::{TokenId, TokenIdMap};

mod types;
pub use types::*;
mod canonical;
pub(crate) use canonical::StateSignature;
pub use canonical::*;
mod prediction;
pub use prediction::*;
mod builder;
#[cfg(test)]
pub(crate) use builder::compute_action_weight;
pub use builder::*;
mod emit;
pub use emit::*;

#[cfg(test)]
mod tests;
