//! User test code generation for `language!` specifications.
//!
//! Generates `#[test]` functions from user-supplied `tests { }` blocks
//! in the language definition. Forward-compatible: if the `LanguageDef`
//! struct does not yet have a `tests` field, this module generates nothing
//! but still compiles.
//!
//! Everything is derived from the `language!` spec.

use mettail_ast::language::LanguageDef;

/// Generate user-supplied tests for the language.
///
/// Checks if the `LanguageDef` has a `tests` field. Since the spec change
/// for `tests { }` blocks has not yet been approved, this emits an explanatory
/// generated section and no `#[test]` functions.
///
/// Returns a string of `#[test]` functions (currently empty).
pub fn generate_user_tests(language: &LanguageDef) -> String {
    let lang_name = language.name.to_string();

    let mut out = String::with_capacity(256);

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// User tests (from `tests { }` block)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
    out.push_str(&format!(
        "// No user tests defined for {} — `tests {{}}` block not yet supported in spec.\n\n",
        lang_name
    ));

    out
}
