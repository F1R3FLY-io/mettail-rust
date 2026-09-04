//! Runtime-neutral semantic grammar representation for MeTTaIL.
//!
//! Front ends lower into [`GrammarCoreV1`]. Compiler back ends consume only
//! that representation and may emit a verified [`ParserImageV1`]. The image is
//! a cache: the grammar value, not an image supplied beside it, is authoritative.

mod canonical;
mod capability;
mod core;
mod dynamic;
mod image;
mod installed;
mod language_core;
mod normalize;
mod runtime;
mod semantic_machine;
mod semantic_term;
mod string_literal;
mod theorem;
mod theory_rule;
mod weight;

pub use canonical::*;
pub use capability::*;
pub use core::*;
pub use dynamic::*;
pub use image::*;
pub use installed::*;
pub use language_core::*;
pub use normalize::*;
pub use runtime::*;
pub use semantic_machine::*;
pub use semantic_term::*;
pub use string_literal::*;
pub use theorem::*;
pub use theory_rule::*;
pub use weight::*;
