//! Language-generic parser modules for sub-sublanguages that are
//! embedded inside `language!`-defined languages.
//!
//! Phase 6 / F.0-sibling (2026-04-26): the canonical Pratt-style
//! predicate parser was moved to `mettail_prattail::parser::predicate_pratt`
//! so the WPDS walker can invoke it without crossing the
//! `prattail → runtime` cycle. Runtime re-exports the parser's public
//! surface for backward compatibility — every existing
//! `use mettail_runtime::parser::predicate::...` call site continues
//! to compile.

pub use mettail_prattail::parser::predicate_pratt as predicate;

pub use mettail_prattail::parser::predicate_pratt::{
    parse_predicate_from_str, ParseError, PredicateParser, PredicateParserConfig, TerminatorToken,
};
