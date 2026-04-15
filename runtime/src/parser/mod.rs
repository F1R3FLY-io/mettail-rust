//! Language-generic parser modules for sub-sublanguages that are
//! embedded inside `language!`-defined languages.
//!
//! Currently provides:
//! - `predicate`: a Pratt-style parser for the §2 EBNF predicate
//!   sublanguage from `docs/design/predicated-types.md`. Produces
//!   `mettail_runtime::BehavioralPred` values from either a `&str`
//!   or a slice of already-lexed tokens. Language-generic: the
//!   trigger keyword (`where`, `if`, `|`, etc.) is NOT part of
//!   this parser — it's a literal in each language's `terms { }`
//!   syntax pattern that the macro-generated parser consumes before
//!   dispatching here.

pub mod predicate;

pub use predicate::{
    parse_predicate_from_str, ParseError, PredicateParser,
    PredicateParserConfig, TerminatorToken,
};
