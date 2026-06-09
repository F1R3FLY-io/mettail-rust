//! Re-export facade. `LexicographicWeight` (the production composed weight) now
//! lives in the `rigail` crate; this preserves the historical
//! `crate::automata::lex_weight::*` import path for prattail's consumers.

pub use rigail::lex_weight::*;
