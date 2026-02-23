//! Query operations on string rows (no provenance).

mod difference;
mod join;
mod project;

pub use difference::difference;
pub use join::equijoin;
pub use project::project;

/// Row = vector of string values.
pub type Row = Vec<String>;
