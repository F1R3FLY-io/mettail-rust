//! Re-export facade. `LexicographicWeight` (the production composed weight) now
//! lives in the `dovetail-semiring` crate; this preserves the historical
//! `crate::automata::lex_weight::*` import path for prattail's consumers.

pub use dovetail_semiring::lex_weight::*;
