//! Term generation for languages
//!
//! Provides both exhaustive enumeration and random sampling of terms.

mod exhaustive;
mod random;

pub use exhaustive::*;
pub use random::*;

use crate::ast::language::LanguageDef;
use syn::Ident;

pub fn is_lang_type(cat: &Ident, language: &LanguageDef) -> bool {
    language.types.iter().any(|t| &t.name == cat)
}