//! Analytical test code generation for `language!` specifications.
//!
//! Generates `#[test]` functions that call the testkit analytical modules
//! (confluence, termination, etc.) for each language definition.
//!
//! All tests are always generated (no feature gates). The testkit modules
//! themselves handle feature-gated analytical backends, so the generated tests
//! compile and run regardless of which testkit features are enabled.
//!
//! Everything is derived from the `language!` spec.

use mettail_ast::language::LanguageDef;
use mettail_prattail::PipelineAnalysis;

/// Generate analytical tests for the language.
///
/// Produces a string of `#[test]` functions to be spliced into the generated
/// test file. Each test calls into the corresponding testkit analytical module.
///
/// Generated tests:
/// - `{lang}_confluence_check()` — calls `mettail_testkit::analytical::confluence::check_language_confluence()`
/// - `{lang}_termination_check()` — calls `mettail_testkit::analytical::termination::check_language_termination()`
///
/// These tests always compile and run. The testkit functions call directly
/// into the prattail analysis modules (no feature gates).
pub fn generate_analytical_tests(language: &LanguageDef, _pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut out = String::with_capacity(2048);

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// Analytical tests (confluence, termination)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");

    // Only generate TRS analysis tests if the language has rewrites
    // (otherwise TRS analysis is trivial and the tests add no value)
    if language.rewrites.is_empty() {
        out.push_str("// No rewrites defined — TRS analytical tests skipped.\n\n");
        return out;
    }

    // Confluence check — verifies all critical pairs are joinable.
    // FAILS if any non-joinable critical pair is found.
    out.push_str("#[test]\n");
    out.push_str(&format!("fn {}_confluence_check() {{\n", lang_name_lower));
    out.push_str(&format!("    let lang = {};\n", lang_struct));
    out.push_str("    let meta = lang.metadata();\n");
    out.push_str("    let result = mettail_testkit::analytical::confluence::check_language_confluence(meta);\n");
    out.push_str(&format!(
        "    assert!(\n\
         \x20       result.is_confluent,\n\
         \x20       \"{lang} confluence FAILED: {{}} non-joinable critical pair(s) out of {{}}. Summary: {{}}\",\n\
         \x20       result.non_joinable_count,\n\
         \x20       result.critical_pair_count,\n\
         \x20       result.summary,\n\
         \x20   );\n",
        lang = lang_name
    ));
    out.push_str("}\n\n");

    // Termination check — asserts only when the analysis is conclusive.
    // An inconclusive result silently passes (analysis incomplete, not a bug).
    out.push_str("#[test]\n");
    out.push_str(&format!("fn {}_termination_check() {{\n", lang_name_lower));
    out.push_str(&format!("    let lang = {};\n", lang_struct));
    out.push_str("    let meta = lang.metadata();\n");
    out.push_str("    let result = mettail_testkit::analytical::termination::check_language_termination(meta);\n");
    out.push_str("    if result.is_conclusive {\n");
    out.push_str(&format!(
        "        assert!(\n\
         \x20           result.is_terminating,\n\
         \x20           \"{lang} termination FAILED (conclusive): {{}}\",\n\
         \x20           result.summary\n\
         \x20       );\n",
        lang = lang_name
    ));
    out.push_str("    }\n");
    out.push_str("    // If not conclusive: pass silently (analysis incomplete, not a bug).\n");
    out.push_str("}\n\n");

    out
}
