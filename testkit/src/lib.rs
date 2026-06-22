//! MeTTaIL Test Kit — auto-generated test framework for `language!` specifications.
//!
//! This crate provides reusable property assertion functions, proptest strategy helpers,
//! and analytical test drivers. Generated `#[test]` code in `languages/tests/generated/`
//! calls into these functions.
//!
//! ## Module Structure
//!
//! - `properties/` — Property assertion functions (structural, semantic, algebraic)
//! - `analytical/` — Analytical test drivers (confluence, termination)
//! - `strategies` — Shared proptest strategy helpers
//! - `alpha` — Alpha-equivalence assertion utilities
//! - `program` — `ProgramTestSuite` builder for application-level testing

pub mod alpha;
pub mod analytical;
pub mod program;
pub mod properties;
pub mod runtime_report;
pub mod strategies;

// Re-export commonly used items for convenience in generated test code
pub use alpha::assert_alpha_eq;
pub use properties::algebraic;
pub use properties::semantic;
pub use properties::structural;
