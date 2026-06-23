pub mod examples;
pub mod pretty;
pub mod registry;
pub mod repl;
#[cfg(feature = "bundled-languages")]
pub mod rho_backends;
pub mod state;

pub use examples::Example;
pub use pretty::format_term_pretty;
pub use registry::{build_registry, LanguageRegistry, RegisteredLanguageInfo};
pub use repl::Repl;
pub use state::{HistoryEntry, ReplState};

// Re-export language types from runtime
pub use mettail_runtime::{EquivClass, Language, LanguageMetadata, Rewrite, Term, TermInfo};
