//! Program test code generation for `language!` specifications.
//!
//! Generates `#[test]` functions from `program { }` blocks in the language
//! definition. Forward-compatible: if the `LanguageDef` struct does not yet
//! have program test blocks, this module generates nothing but still compiles.
//!
//! If program test blocks are added to the AST, this module is the generator
//! boundary that will consume them.
//!
//! Everything is derived from the `language!` spec.

use mettail_ast::language::LanguageDef;

/// Generate program-level tests for the language.
///
/// Checks if the `LanguageDef` has `program` blocks in a `tests` field.
/// Since `LanguageDef` has no program-test field, this emits an explanatory
/// generated section and no `#[test]` functions.
///
/// Returns a string of `#[test]` functions (currently empty).
pub fn generate_program_tests(language: &LanguageDef) -> String {
    let lang_name = language.name.to_string();

    let mut out = String::with_capacity(256);

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// Program tests (from `program { }` blocks)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
    out.push_str(&format!(
        "// No program tests defined for {} — `program {{}}` blocks not yet supported in spec.\n\n",
        lang_name
    ));

    out
}
