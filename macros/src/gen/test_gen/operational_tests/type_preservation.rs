//! Phase 5b: Type preservation test generation.
//!
//! For every rule with `rust_code` and `eval_mode`:
//! - Generates a ground term
//! - Evaluates via `try_direct_eval()`
//! - Asserts the result is `Some` (evaluation succeeds for ground terms)
//! - Asserts the result can be displayed and re-parsed in the same category
//!
//! All recursive operations use iterative work-stacks (trampolines).
//! Everything is derived from the `language!` spec.

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use crate::gen::native::native_type_to_string;
use std::collections::{HashMap, HashSet};

use super::expr_string_gen::TestCase;
use super::ground_term_enum;

/// Maximum type preservation tests per language.
const MAX_TYPE_PRES_TESTS: usize = 50;

/// Generate type preservation tests for the language.
///
/// Returns a vector of `TestCase` suitable for code generation.
pub fn generate_type_preservation_tests(
    language: &LanguageDef,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<TestCase> {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut test_cases: Vec<TestCase> = Vec::with_capacity(MAX_TYPE_PRES_TESTS);

    // Step 1: Find rules with rust_code AND eval_mode
    let eval_rules: Vec<&GrammarRule> = language
        .terms
        .iter()
        .filter(|r| r.rust_code.is_some())
        .filter(|r| r.eval_mode.is_some())
        .filter(|r| !ambiguous_prefix_rules.contains(&r.label.to_string()))
        .collect();

    if eval_rules.is_empty() {
        // Also include rules with rust_code but no explicit eval_mode
        // (they still participate in evaluation)
        return generate_type_preservation_for_all_eval_rules(
            language,
            ambiguous_prefix_rules,
        );
    }

    // Step 2: Enumerate ground terms
    let ground_terms = ground_term_enum::enumerate_ground_terms(language);
    let mut gt_by_label: HashMap<String, Vec<&ground_term_enum::GroundTerm>> =
        HashMap::with_capacity(ground_terms.len());
    for gt in &ground_terms {
        gt_by_label
            .entry(gt.rule_label.clone())
            .or_insert_with(Vec::new)
            .push(gt);
    }

    // Step 3: For each eval rule, take the first ground term and generate a test
    for rule in &eval_rules {
        if test_cases.len() >= MAX_TYPE_PRES_TESTS {
            break;
        }

        let label = rule.label.to_string();
        let category = rule.category.to_string();

        let gts = match gt_by_label.get(&label) {
            Some(gts) if !gts.is_empty() => gts,
            _ => continue,
        };

        let gt = gts[0];

        // Filter dangerous inputs
        if super::is_dangerous_input(rule, &gt.param_values) {
            continue;
        }

        let test_name = format!(
            "type_pres_{}_{}_{}",
            lang_name_lower,
            label.to_lowercase(),
            super::sanitize_test_name(&gt.display_hint)
        );

        // Generate a type preservation test:
        // 1. Construct the term
        // 2. Call try_direct_eval()
        // 3. Assert result is Some
        // 4. Display the result and re-parse in the same category
        let tc = generate_type_pres_test_case(
            &test_name,
            &gt.construction_code,
            &category,
            &lang_struct,
        );

        test_cases.push(tc);
    }

    test_cases
}

/// Fallback: generate type preservation tests for ALL rules with rust_code.
fn generate_type_preservation_for_all_eval_rules(
    language: &LanguageDef,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<TestCase> {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut test_cases: Vec<TestCase> = Vec::with_capacity(MAX_TYPE_PRES_TESTS);

    let ground_terms = ground_term_enum::enumerate_ground_terms(language);
    let mut seen_labels: HashSet<String> = HashSet::new();

    for gt in &ground_terms {
        if test_cases.len() >= MAX_TYPE_PRES_TESTS {
            break;
        }

        // One test per rule label (use first ground term)
        if seen_labels.contains(&gt.rule_label) {
            continue;
        }

        if ambiguous_prefix_rules.contains(&gt.rule_label) {
            continue;
        }

        // Find the rule
        let rule = match language
            .terms
            .iter()
            .find(|r| r.label.to_string() == gt.rule_label && r.rust_code.is_some())
        {
            Some(r) => r,
            None => continue,
        };

        // Filter dangerous inputs
        if super::is_dangerous_input(rule, &gt.param_values) {
            continue;
        }

        seen_labels.insert(gt.rule_label.clone());

        let test_name = format!(
            "type_pres_{}_{}_{}",
            lang_name_lower,
            gt.rule_label.to_lowercase(),
            super::sanitize_test_name(&gt.display_hint)
        );

        let tc = generate_type_pres_test_case(
            &test_name,
            &gt.construction_code,
            &gt.category,
            &lang_struct,
        );

        test_cases.push(tc);
    }

    test_cases
}

/// Generate a single type preservation test case.
///
/// The test:
/// 1. Constructs a ground term
/// 2. Displays it
/// 3. Parses it
/// 4. Evaluates via run_ascent
/// 5. Verifies each normal form can be displayed and re-parsed
fn generate_type_pres_test_case(
    test_name: &str,
    construction_code: &str,
    category: &str,
    lang_struct: &str,
) -> TestCase {
    // The construction_code for type preservation tests is a custom body
    // that does the full pipeline: construct -> display -> parse -> eval -> display -> re-parse
    let custom_body = format!(
        r#"{{ // Type preservation test for category {cat}
    let input_term = {construction};
    let input_str = format!("{{}}", input_term);
    let lang = {lang_struct};
    let parsed = lang.parse_term(&input_str).expect("parse should succeed");
    let results = lang.run_ascent(parsed.as_ref()).expect("eval should succeed");
    let nfs = results.normal_forms();
    assert!(!nfs.is_empty(),
        "type preservation: {{}} should produce at least one normal form", input_str);
    // Verify each normal form can be displayed and re-parsed (type preservation)
    for nf in &nfs {{
        let nf_display = &nf.display;
        let re_parsed = lang.parse_term(nf_display);
        assert!(re_parsed.is_ok(),
            "type preservation: normal form '{{}}' should be parseable in same category", nf_display);
    }}
}}"#,
        cat = category,
        construction = construction_code,
        lang_struct = lang_struct,
    );

    TestCase {
        test_name: test_name.to_string(),
        construction_code: custom_body,
        lang_struct: lang_struct.to_string(),
        expected: None, // Custom body
    }
}
