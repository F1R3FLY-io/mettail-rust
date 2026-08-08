//! Term operation generation
//!
//! Generates methods for manipulating terms:
//! - `subst` - Capture-avoiding substitution
//! - `normalize` - Collection canonicalization (flatten + normalize)
//! - `depth` - Term nesting depth measurement (A-RT05)
//! - `iterative_clone` - Trampolined Clone for owned collection subterms
//! - `iterative_drop` - Trampolined Drop for stack-safe deallocation
//! - `iterative_cmp` - Trampolined PartialEq/Eq/PartialOrd/Ord for stack-safe comparison
//! - `iterative_hash` - Trampolined Hash for stack-safe hashing

/// Structural meta-test: no term op may leaf-treat a collection literal
/// (test-only; see the module docs for the ratchet protocol).
#[cfg(test)]
pub mod arm_integrity;
/// ★ The COLLECTION-ELEMENT BOUNDARY — the one place the per-`CollectionType`
/// element walk and its order-faithfulness law are spelled (#162).
pub mod collection_walk;
pub mod depth;
pub mod ground;
pub mod iterative_clone;
pub mod iterative_cmp;
pub mod iterative_drop;
pub mod iterative_hash;
pub mod match_pattern;
pub mod normalize;
pub mod parse_alt_filter;
pub mod semantic_hash;
pub mod subst;
