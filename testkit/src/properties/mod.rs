//! Property assertion functions for generated tests.
//!
//! These functions are called by auto-generated `#[test]` and `proptest!` code
//! in `languages/tests/generated/`. Each module provides assertions for a
//! specific category of properties.

pub mod algebraic;
pub mod semantic;
pub mod structural;
