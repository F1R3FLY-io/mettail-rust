//! Term operation generation
//!
//! Generates methods for manipulating terms:
//! - `subst` - Capture-avoiding substitution
//! - `normalize` - Collection canonicalization (flatten + normalize)

pub mod subst;
pub mod normalize;

pub use subst::{generate_substitution, generate_env_substitution};
pub use normalize::{generate_flatten_helpers, generate_normalize_functions};
