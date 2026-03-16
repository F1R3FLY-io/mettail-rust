//! Term operation generation
//!
//! Generates methods for manipulating terms:
//! - `subst` - Capture-avoiding substitution
//! - `normalize` - Collection canonicalization (flatten + normalize)
//! - `depth` - Term nesting depth measurement (A-RT05)

pub mod depth;
pub mod ground;
pub mod hash_consing_analysis;
pub mod match_pattern;
pub mod normalize;
pub mod subst;
