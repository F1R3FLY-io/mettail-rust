//! Term operation generation
//!
//! Generates methods for manipulating terms:
//! - `subst` - Capture-avoiding substitution
//! - `normalize` - Collection canonicalization (flatten + normalize)
//! - `depth` - Term nesting depth measurement (A-RT05)
//! - `iterative_drop` - Trampolined Drop for stack-safe deallocation
//! - `iterative_clone` - Trampolined Clone for stack-safe cloning
//! - `iterative_cmp` - Trampolined PartialEq/Eq/PartialOrd/Ord for stack-safe comparison
//! - `iterative_hash` - Trampolined Hash for stack-safe hashing

pub mod depth;
pub mod ground;
pub mod hash_consing_analysis;
pub mod iterative_clone;
pub mod iterative_cmp;
pub mod iterative_drop;
pub mod iterative_hash;
pub mod match_pattern;
pub mod normalize;
pub mod parse_alt_filter;
pub mod subst;
