pub mod examples;
pub mod pretty;
pub mod registry;
pub mod repl;
pub mod state;
pub mod theories;
pub mod theory;

// Re-export eqrel for the generated Ascent code
pub use ascent_byods_rels::eqrel;

pub use examples::Example;
pub use pretty::format_term_pretty;
pub use registry::{build_registry, TheoryRegistry};
pub use repl::Repl;
pub use state::{HistoryEntry, ReplState};
pub use theories::{
    AmbCalculusTheory, 
    RhoCalculusTheory};
pub use theory::{AscentResults, EquivClass, Rewrite, Term, TermInfo, Theory};
