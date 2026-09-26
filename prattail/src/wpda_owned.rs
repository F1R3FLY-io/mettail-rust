//! Owned grammar adapters for the original WPDA runtime.
//! Recognition remains in `WpdaWalker`; these modules expose admitted data.

pub mod absorption;
pub mod actions;
pub mod engine;
mod semantic_keys;
pub mod semantic_roster;
pub mod source;
pub mod structural;
pub mod token_bindings;
