//! Phase 4a: WFST-guided dispatch tests.
//!
//! Reads `pipeline.constructor_weights` and `pipeline.dead_rule_labels` to
//! generate evaluation-focused tests. For each non-dead rule with `rust_code`,
//! verifies that the displayed term can be parsed AND evaluated correctly.
//! For ambiguous tokens (multiple rules sharing the first token), generates
//! disambiguation tests.
//!
//! All recursive operations use iterative work-stacks (trampolines).
//! Everything is derived from the `language!` spec.

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use crate::gen::native::native_type_to_string;
use mettail_prattail::PipelineAnalysis;
use std::collections::{HashMap, HashSet};

use super::expr_string_gen::TestCase;
use super::ground_term_enum;

/// Maximum WFST-guided tests per language.
const MAX_WFST_TESTS: usize = 60;

/// Generate WFST-guided dispatch tests.
///
/// Prioritizes tests for frequently-used constructors (lowest weight = most frequent)
/// and skips dead rules.
pub fn generate_wfst_guided_tests(
    language: &LanguageDef,
    pipeline: &PipelineAnalysis,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<TestCase> {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut test_cases: Vec<TestCase> = Vec::with_capacity(MAX_WFST_TESTS);

    // Step 1: Collect rules with rust_code, excluding dead rules
    let mut eligible_rules: Vec<&GrammarRule> = language
        .terms
        .iter()
        .filter(|r| r.rust_code.is_some())
        .filter(|r| !pipeline.dead_rule_labels.contains(&r.label.to_string()))
        .filter(|r| !ambiguous_prefix_rules.contains(&r.label.to_string()))
        .collect();

    // Step 2: Sort by constructor weight (lower = more frequent = higher priority)
    eligible_rules.sort_by(|a, b| {
        let wa = pipeline
            .constructor_weights
            .get(&a.label.to_string())
            .copied()
            .unwrap_or(f64::MAX);
        let wb = pipeline
            .constructor_weights
            .get(&b.label.to_string())
            .copied()
            .unwrap_or(f64::MAX);
        wa.partial_cmp(&wb).unwrap_or(std::cmp::Ordering::Equal)
    });

    // Step 3: Enumerate ground terms
    let ground_terms = ground_term_enum::enumerate_ground_terms(language);
    let mut gt_by_label: HashMap<String, Vec<&ground_term_enum::GroundTerm>> =
        HashMap::with_capacity(ground_terms.len());
    for gt in &ground_terms {
        gt_by_label
            .entry(gt.rule_label.clone())
            .or_insert_with(Vec::new)
            .push(gt);
    }

    // Step 4: Generate tests in weight-priority order
    for rule in &eligible_rules {
        if test_cases.len() >= MAX_WFST_TESTS {
            break;
        }

        let label = rule.label.to_string();
        let category = rule.category.to_string();

        // Get the first safe ground term for this rule
        let gts = match gt_by_label.get(&label) {
            Some(gts) if !gts.is_empty() => gts,
            _ => continue,
        };

        // Find a non-dangerous ground term
        let gt = match gts.iter().find(|gt| !super::is_dangerous_input(rule, &gt.param_values)) {
            Some(gt) => gt,
            None => continue,
        };

        // Compute the weight annotation
        let weight_comment = pipeline
            .constructor_weights
            .get(&label)
            .map(|w| format!("// WFST weight: {:.4}\n", w))
            .unwrap_or_default();

        // Build a full display-parse-eval test
        let test_name = format!(
            "wfst_{}_dispatch_{}_eval",
            lang_name_lower,
            label.to_lowercase()
        );

        // For WFST tests, we do a full construct -> display -> parse -> eval pipeline
        // We don't assert a specific result (smoke test), but verify the pipeline works.
        test_cases.push(TestCase {
            test_name,
            construction_code: gt.construction_code.clone(),
            lang_struct: lang_struct.clone(),
            expected: None, // Smoke: verify the full pipeline works
        });
    }

    // Step 5: Generate disambiguation tests for ambiguous first-tokens
    let disambiguation_tests = generate_disambiguation_tests(
        language,
        pipeline,
        &lang_name_lower,
        &lang_struct,
        &gt_by_label,
    );
    for tc in disambiguation_tests {
        if test_cases.len() >= MAX_WFST_TESTS {
            break;
        }
        test_cases.push(tc);
    }

    test_cases
}

/// Generate disambiguation tests for rules with ambiguous first tokens.
///
/// Groups non-dead rules by (category, first_syntax_literal) and generates
/// a test for each group with multiple members, verifying that each rule's
/// constructed term can round-trip correctly.
fn generate_disambiguation_tests<'a>(
    language: &LanguageDef,
    pipeline: &PipelineAnalysis,
    lang_name_lower: &str,
    lang_struct: &str,
    gt_by_label: &HashMap<String, Vec<&'a ground_term_enum::GroundTerm>>,
) -> Vec<TestCase> {
    let mut test_cases = Vec::new();

    // Group rules by (category, first_literal_token)
    let mut groups: HashMap<(String, String), Vec<String>> = HashMap::new();

    for rule in &language.terms {
        if pipeline.dead_rule_labels.contains(&rule.label.to_string()) {
            continue;
        }
        let cat = rule.category.to_string();
        let first_lit = extract_first_literal(rule);
        if let Some(lit) = first_lit {
            groups
                .entry((cat, lit))
                .or_insert_with(Vec::new)
                .push(rule.label.to_string());
        }
    }

    // For ambiguous groups (>1 member), generate a test for each member
    for ((cat, first_lit), labels) in &groups {
        if labels.len() <= 1 {
            continue;
        }

        for label in labels {
            if let Some(gts) = gt_by_label.get(label) {
                if let Some(gt) = gts.first() {
                    let safe_lit = super::sanitize_test_name(first_lit);
                    let test_name = format!(
                        "wfst_{}_disambig_{}_{}",
                        lang_name_lower,
                        label.to_lowercase(),
                        safe_lit
                    );

                    test_cases.push(TestCase {
                        test_name,
                        construction_code: gt.construction_code.clone(),
                        lang_struct: lang_struct.to_string(),
                        expected: None,
                    });
                }
            }
        }
    }

    test_cases
}

/// Extract the first literal token from a rule's syntax pattern.
fn extract_first_literal(rule: &GrammarRule) -> Option<String> {
    use mettail_ast::grammar::SyntaxExpr;

    if let Some(ref pattern) = rule.syntax_pattern {
        for expr in pattern {
            match expr {
                SyntaxExpr::Literal(s) => return Some(s.clone()),
                _ => return None, // First token is a param, not a literal
            }
        }
    }
    None
}

/// Generate the WFST coverage plan comment for test files.
///
/// Shows which constructors are tested, their weights, and the allocation strategy.
pub fn generate_wfst_coverage_comment(
    language: &LanguageDef,
    pipeline: &PipelineAnalysis,
) -> String {
    let mut out = String::with_capacity(2048);

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// WFST-derived test coverage plan\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n");

    // Dead rules
    if !pipeline.dead_rule_labels.is_empty() {
        out.push_str("// Dead rules (skipped):\n");
        let mut dead: Vec<&String> = pipeline.dead_rule_labels.iter().collect();
        dead.sort();
        for label in dead {
            out.push_str(&format!("//   - {}\n", label));
        }
    }

    // Constructor weights
    if !pipeline.constructor_weights.is_empty() {
        out.push_str("// Constructor weights (lower = more frequent):\n");
        let mut weights: Vec<(&String, &f64)> = pipeline.constructor_weights.iter().collect();
        weights.sort_by(|a, b| a.1.partial_cmp(b.1).unwrap_or(std::cmp::Ordering::Equal));
        for (label, weight) in weights.iter().take(20) {
            out.push_str(&format!("//   {:20} weight: {:.4}\n", label, weight));
        }
        if weights.len() > 20 {
            out.push_str(&format!("//   ... and {} more\n", weights.len() - 20));
        }
    }

    // Category weights
    if !pipeline.category_weights.is_empty() {
        out.push_str("// Category weights:\n");
        let mut cat_weights: Vec<(&String, &f64)> = pipeline.category_weights.iter().collect();
        cat_weights.sort_by(|a, b| a.1.partial_cmp(b.1).unwrap_or(std::cmp::Ordering::Equal));
        for (cat, weight) in &cat_weights {
            out.push_str(&format!("//   {:20} weight: {:.4}\n", cat, weight));
        }
    }

    out.push_str("//\n\n");
    out
}
