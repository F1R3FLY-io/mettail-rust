//! Runtime-neutral semantic grammar representation for MeTTaIL.
//!
//! Front ends lower into [`GrammarCoreV1`]. Compiler back ends consume only
//! that representation and may emit a verified [`ParserImageV1`]. The image is
//! a cache: the grammar value, not an image supplied beside it, is authoritative.

mod authored;
mod authored_capture;
mod canonical;
mod capability;
mod core;
pub mod context_items;
mod dynamic;
mod image;
mod installed;
mod language_core;
mod lexical_selection;
mod native_kind;
mod normalize;
mod nonterminal;
mod runtime;
mod semantic_machine;
mod semantic_term;
mod string_literal;
mod term_param;
mod theorem;
mod theory_image;
mod theory_image_codec;
mod theory_rule;
mod weight;

pub use authored::*;
pub use authored_capture::*;
pub use canonical::*;
pub use capability::*;
pub use core::*;
pub use dynamic::*;
pub use image::*;
pub use installed::*;
pub use language_core::*;
pub use lexical_selection::{visit_lexical_survivors, LexicalSelectionError};
pub use native_kind::NativeKind;
pub use normalize::*;
pub use nonterminal::NonTerminalKind;
pub use runtime::*;
pub use semantic_machine::*;
pub use semantic_term::*;
pub use string_literal::*;
pub use term_param::{TermParamObservation, TermParamReader};
pub use theorem::*;
pub use theory_image::*;
pub use theory_rule::*;
pub use weight::*;
