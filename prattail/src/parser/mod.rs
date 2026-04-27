//! Phase 6: parsers used by the WPDS walker for inline sub-language parses
//! that don't fit the main grammar's state machine — e.g., behavioral
//! predicates parsed inside `?guard:Guard` slots.
//!
//! - `predicate` — the WPDS-walker-driven thin parser used by the
//!   `WpdsStepAction::ParsePredicate` action handler.
//! - `predicate_pratt` — the canonical language-generic Pratt-style
//!   parser, moved from `mettail_runtime::parser::predicate` during the
//!   F.0-sibling break (Phase 6, 2026-04-26). Runtime re-exports this.

pub mod predicate;
pub mod predicate_pratt;
