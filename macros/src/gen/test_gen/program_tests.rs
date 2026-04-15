//! Program test code generation for `language!` specifications.
//!
//! Generates `#[test]` functions from `program { }` blocks in the language
//! definition. Forward-compatible: if the `LanguageDef` struct does not yet
//! have program test blocks, this module generates nothing but still compiles.
//!
//! When implemented, program tests will exercise application-level semantics
//! by parsing, evaluating, and asserting on complete program fragments using
//! the `mettail_testkit::program::ProgramTestSuite` builder.
//!
//! Everything is derived from the `language!` spec.

use mettail_ast::language::LanguageDef;

/// Generate program-level tests for the language.
///
/// Checks if the `LanguageDef` has `program` blocks in a `tests` field.
/// Since the spec change for `program { }` blocks has not yet been approved,
/// this currently generates no tests. The module exists as a forward-compatible
/// placeholder that compiles unconditionally.
///
/// When the `program` test blocks are added to `LanguageDef`, this function
/// will iterate over them and generate corresponding `#[test]` functions
/// that use `ProgramTestSuite` to exercise full program semantics.
///
/// Returns a string of `#[test]` functions (currently empty).
pub fn generate_program_tests(language: &LanguageDef) -> String {
    let lang_name = language.name.to_string();

    // Forward-compatible: the LanguageDef struct does not yet have program test blocks.
    // When they are added, uncomment and implement the following:
    //
    // if let Some(tests) = &language.tests {
    //     for program_block in tests.programs() {
    //         // Generate #[test] fn using ProgramTestSuite:
    //         //   ProgramTestSuite::new(&lang)
    //         //       .source(program_block.source)
    //         //       .expect_parses()
    //         //       .expect_terminates(program_block.max_steps)
    //         //       .run()
    //     }
    // }

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
