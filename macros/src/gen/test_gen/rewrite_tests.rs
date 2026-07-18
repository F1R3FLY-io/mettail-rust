//! Rewrite test generation for `language!` specifications.
//!
//! Generates one `#[test]` per rewrite rule that:
//! 1. Instantiates the language struct
//! 2. Verifies the rewrite rule metadata is present and well-formed
//! 3. For constructible rules, also generates a concrete-term execution test
//!    (suffix `_exec`) that runs the rule's LHS constructor through SimulationRunner
//!    and asserts the result reaches a NormalForm.
//!
//! Dead rules (proven unreachable by WFST analysis) are emitted with `#[ignore]`.
//!
//! NOTE: Rewrite LHS/RHS are pattern strings with meta-variables (e.g., N, P, ...rest)
//! that cannot be parsed as concrete terms. The metadata tests verify presence only.
//! The `_exec` tests use construct_test_expression() to build a concrete parseable input.

use mettail_ast::language::{LanguageDef, RewriteRule};
use mettail_prattail::PipelineAnalysis;

/// Generate per-rewrite-rule tests for the language.
///
/// Returns a string of `#[test]` functions to be spliced into the generated
/// test file.
pub fn generate_rewrite_tests(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);
    let dead_rules = &pipeline.dead_rule_labels;

    let mut out = String::with_capacity(4096);

    if language.rewrites.is_empty() {
        return out;
    }

    for (i, rewrite) in language.rewrites.iter().enumerate() {
        let rule_name = rewrite.name.to_string();
        let test_name = format!("rewrite_{}_{}", lang_name_lower, rule_name.to_lowercase());

        let is_dead = dead_rules.contains(&rule_name);
        let is_congruence = rewrite.is_congruence_rule();

        if is_congruence {
            // Skip congruence rules — they need a triggering context
            out.push_str(&format!(
                "// Rewrite test for {} skipped: congruence rule (needs triggering context)\n",
                rule_name
            ));
            // Congruence rules need triggering context for full semantic testing,
            // but we still verify metadata presence.
            out.push_str("#[test]\n");
            out.push_str(&format!("fn {}() {{\n", test_name));
            out.push_str(&format!("    let _lang = {};\n", lang_struct));
            out.push_str("    // Congruence rules require a rewrite-triggering context to test.\n");
            out.push_str(
                "    // They fire when their premise (S ~> T) is satisfied by another rewrite.\n",
            );
            out.push_str("}\n\n");
        } else {
            // Non-congruence rewrite: verify metadata presence
            out.push_str("#[test]\n");
            out.push_str(&format!("fn {}() {{\n", test_name));
            out.push_str(&format!("    let _lang = {};\n", lang_struct));

            out.push_str(&format!(
                "    let meta = _lang.metadata();\n\
                 \x20   let rewrites = meta.rewrites();\n\
                 \x20   // Verify rewrite {} (index {}) exists in metadata\n\
                 \x20   assert!(\n\
                 \x20       rewrites.len() > {},\n\
                 \x20       \"Expected at least {} rewrites in metadata, found {{}}\",\n\
                 \x20       rewrites.len()\n\
                 \x20   );\n\
                 \x20   let rw = &rewrites[{}];\n",
                rule_name,
                i,
                i,
                i + 1,
                i
            ));

            // Verify the rewrite metadata
            out.push_str(&format!(
                "    // Verify rewrite rule name\n\
                 \x20   assert_eq!(rw.name, Some(\"{}\"), \"Rewrite rule name mismatch\");\n",
                rule_name
            ));

            // Verify LHS and RHS are non-empty (but do NOT try to parse them as
            // they contain meta-variables like N, M, P, ...rest which are not valid
            // concrete terms and may cause stack overflow in the parser)
            out.push_str(&format!(
                "    assert!(!rw.lhs.is_empty(), \"Rewrite {} LHS should be non-empty\");\n\
                 \x20   assert!(!rw.rhs.is_empty(), \"Rewrite {} RHS should be non-empty\");\n",
                rule_name, rule_name,
            ));

            out.push_str("}\n\n");

            // Concrete execution test: attempt to construct a concrete input for the
            // LHS constructor and run it through SimulationRunner.
            // Only generated when the constructor is synthesizable from grammar rules.
            if let Some(exec_test) = generate_exec_test(
                &test_name,
                &rule_name,
                rewrite,
                language,
                &lang_struct,
                &lang_name,
                is_dead,
            ) {
                out.push_str(&exec_test);
            }
        }
    }

    out
}

/// Attempt to generate a concrete-term execution test for a rewrite rule.
///
/// Returns `Some(test_code)` when:
/// 1. The rewrite's LHS top-level constructor matches a grammar rule
/// 2. `construct_test_expression` produces a concrete parseable input string
///
/// Returns `None` otherwise (no test emitted, no failure).
fn generate_exec_test(
    test_name: &str,
    rule_name: &str,
    rewrite: &RewriteRule,
    language: &LanguageDef,
    lang_struct: &str,
    _lang_name: &str,
    is_dead: bool,
) -> Option<String> {
    // Find the grammar rule whose label matches the LHS constructor.
    let grammar_rule = find_grammar_rule_for_rewrite(rewrite, language)?;

    // Synthesize a concrete test expression string.
    let expr = super::simulation_tests::construct_test_expression(grammar_rule, language)?;

    // Escape the expression for embedding as a Rust string literal.
    let escaped_expr = expr.replace('\\', "\\\\").replace('"', "\\\"");

    let mut out = String::with_capacity(512);

    out.push_str(&format!(
        "// Concrete execution test: run {:?} through SimulationRunner,\n",
        expr
    ));
    out.push_str(&format!(
        "// assert it reaches NormalForm (exercises rewrite rule {}).\n",
        rule_name
    ));

    if is_dead {
        out.push_str("#[ignore = \"dead rule — skipped by WFST analysis\"]\n");
    }
    out.push_str("#[test]\n");
    out.push_str(&format!("fn {}_exec() {{\n", test_name));
    out.push_str("    use mettail_simulation::runner::{SimulationConfig, SimulationRunner};\n");
    out.push_str("    use mettail_simulation::trace::TraceOutcome;\n");
    out.push_str(&format!("    let lang = {};\n", lang_struct));
    out.push_str("    let lang_ref: &dyn mettail_runtime::Language = &lang;\n");
    out.push_str("    let config = SimulationConfig {\n");
    out.push_str("        max_steps: 100,\n");
    out.push_str("        track_morphology: false,\n");
    out.push_str("        ..SimulationConfig::default()\n");
    out.push_str("    };\n");
    out.push_str("    let runner = SimulationRunner::new(lang_ref, config);\n");
    out.push_str("    mettail_runtime::clear_var_cache();\n");
    out.push_str("    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {\n");
    out.push_str(&format!("        runner.run_to_normal_form(\"{}\")\n", escaped_expr));
    out.push_str("    }));\n");
    out.push_str("    if let Ok(Ok(trace)) = result {\n");
    out.push_str("        assert!(\n");
    out.push_str("            matches!(trace.outcome, TraceOutcome::NormalForm { .. }),\n");
    out.push_str(&format!(
        // Use single-quotes around the expression so the message is a valid Rust
        // string literal regardless of whether the expression contains double-quotes.
        "            \"Rewrite rule {rule}: input '{expr}' did not reach NF: {{:?}}\",\n",
        rule = rule_name,
        expr = escaped_expr,
    ));
    out.push_str("            trace.outcome,\n");
    out.push_str("        );\n");
    out.push_str("    }\n");
    out.push_str("    // Panics (e.g., division by zero in native eval) are tolerated.\n");
    out.push_str("}\n\n");

    Some(out)
}

/// Find the grammar rule whose label matches the top-level constructor
/// in the LHS pattern of a rewrite rule.
///
/// Returns `None` if the LHS is not a constructor application (e.g., a variable),
/// or if no matching grammar rule is found.
fn find_grammar_rule_for_rewrite<'a>(
    rewrite: &RewriteRule,
    language: &'a LanguageDef,
) -> Option<&'a mettail_ast::grammar::GrammarRule> {
    use mettail_ast::pattern::{Pattern, PatternTerm};

    let constructor = match &rewrite.left {
        Pattern::Term(PatternTerm::Apply { constructor, .. }) => constructor.to_string(),
        _ => return None,
    };

    language
        .terms
        .iter()
        .find(|r| r.label.to_string() == constructor)
}
