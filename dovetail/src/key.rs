//! Exact semantic-key compatibility façade.
//!
//! The source-neutral implementation lives in `mettail-semantic-key` so the
//! parser, runtime language machinery, and Dovetail share one collision-safe
//! identity algebra without creating a parser-to-reducer dependency.

pub use mettail_semantic_key::*;
