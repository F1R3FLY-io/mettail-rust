//! Phase 5a: WPDS-guided path coverage tests.
//!
//! Uses available WPDS/pipeline data to guide test generation:
//! - `constructor_weights` — prioritize tests for frequently-used constructors
//! - `dead_rule_labels` — skip dead rules
//! - `category_weights` — allocate test budget proportionally
//!
//! Generates a comment in the test file showing the WPDS-derived test coverage plan.
//!
//! All recursive operations use iterative work-stacks (trampolines).
//! Everything is derived from the `language!` spec.

use mettail_ast::language::LanguageDef;
use mettail_prattail::PipelineAnalysis;
use std::collections::{HashMap, HashSet};

use super::expr_string_gen::TestCase;
use super::ground_term_enum;

/// Maximum WPDS-guided tests per language.
const MAX_WPDS_TESTS: usize = 40;

/// Generate WPDS-guided path coverage tests.
///
/// Allocates test budget proportionally to category weights and prioritizes
/// frequently-used constructors. Each test constructs a ground term, evaluates
/// it through the full pipeline, and verifies the result.
pub fn generate_wpda_guided_tests(
    language: &LanguageDef,
    pipeline: &PipelineAnalysis,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<TestCase> {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut test_cases: Vec<TestCase> = Vec::with_capacity(MAX_WPDS_TESTS);

    // Step 1: Compute per-category test budget
    let category_budgets = compute_category_budgets(language, pipeline, MAX_WPDS_TESTS);

    // Step 2: Enumerate ground terms
    let ground_terms = ground_term_enum::enumerate_ground_terms(language);
    let mut gt_by_category: HashMap<String, Vec<&ground_term_enum::GroundTerm>> =
        HashMap::with_capacity(language.types.len());
    for gt in &ground_terms {
        gt_by_category
            .entry(gt.category.clone())
            .or_insert_with(Vec::new)
            .push(gt);
    }

    // Step 3: For each category, select ground terms by constructor weight priority
    for (category, budget) in &category_budgets {
        if test_cases.len() >= MAX_WPDS_TESTS {
            break;
        }

        let gts = match gt_by_category.get(category) {
            Some(gts) if !gts.is_empty() => gts,
            _ => continue,
        };

        // Sort ground terms by constructor weight (lower = higher priority)
        let mut sorted_gts: Vec<&&ground_term_enum::GroundTerm> = gts.iter().collect();
        sorted_gts.sort_by(|a, b| {
            let wa = pipeline
                .constructor_weights
                .get(&a.rule_label)
                .copied()
                .unwrap_or(f64::MAX);
            let wb = pipeline
                .constructor_weights
                .get(&b.rule_label)
                .copied()
                .unwrap_or(f64::MAX);
            wa.partial_cmp(&wb).unwrap_or(std::cmp::Ordering::Equal)
        });

        // Take up to `budget` tests for this category
        let mut cat_count = 0;
        for gt in sorted_gts {
            if cat_count >= *budget || test_cases.len() >= MAX_WPDS_TESTS {
                break;
            }

            // Skip dead rules and ambiguous prefix rules
            if pipeline.dead_rule_labels.contains(&gt.rule_label) {
                continue;
            }
            if ambiguous_prefix_rules.contains(&gt.rule_label) {
                continue;
            }

            // Skip dangerous inputs (div-by-zero, overflow, etc.)
            let maybe_rule = language
                .terms
                .iter()
                .find(|r| r.label.to_string() == gt.rule_label);
            if let Some(rule) = maybe_rule {
                if super::is_dangerous_input(rule, &gt.param_values) {
                    continue;
                }
            }

            let test_name = format!(
                "wpda_{}_{}_{}",
                lang_name_lower,
                gt.rule_label.to_lowercase(),
                super::sanitize_test_name(&gt.display_hint)
            );

            test_cases.push(TestCase {
                test_name,
                construction_code: gt.construction_code.clone(),
                lang_struct: lang_struct.clone(),
                expected: None, // Smoke test — verify full pipeline
            });

            cat_count += 1;
        }
    }

    test_cases
}

/// Compute per-category test budget based on category weights.
///
/// Categories with lower weights (more frequent) get more tests.
/// Uses an iterative approach.
fn compute_category_budgets(
    language: &LanguageDef,
    pipeline: &PipelineAnalysis,
    total_budget: usize,
) -> Vec<(String, usize)> {
    let categories: Vec<String> = language
        .types
        .iter()
        .map(|t| t.name.to_string())
        .filter(|c| !pipeline.unreachable_categories.contains(c))
        .collect();

    if categories.is_empty() {
        return Vec::new();
    }

    // Assign inverse-weight scores (lower weight = higher score)
    let scores: Vec<(String, f64)> = categories
        .iter()
        .map(|cat| {
            let weight = pipeline.category_weights.get(cat).copied().unwrap_or(1.0);
            // Inverse weight, clamped to avoid division by zero
            let score = if weight > 0.001 { 1.0 / weight } else { 1000.0 };
            (cat.clone(), score)
        })
        .collect();

    let total_score: f64 = scores.iter().map(|(_, s)| s).sum();
    if total_score <= 0.0 {
        // Equal distribution
        let per_cat = total_budget / categories.len().max(1);
        return categories
            .into_iter()
            .map(|c| (c, per_cat.max(1)))
            .collect();
    }

    // Proportional allocation
    let mut budgets: Vec<(String, usize)> = scores
        .iter()
        .map(|(cat, score)| {
            let proportion = score / total_score;
            let budget = (proportion * total_budget as f64).round() as usize;
            (cat.clone(), budget.max(1)) // Ensure at least 1 test per category
        })
        .collect();

    // Adjust to not exceed total budget
    let total_allocated: usize = budgets.iter().map(|(_, b)| b).sum();
    if total_allocated > total_budget {
        // Trim from the end
        let excess = total_allocated - total_budget;
        let mut trimmed = 0;
        for (_, budget) in budgets.iter_mut().rev() {
            if trimmed >= excess {
                break;
            }
            let can_trim = (*budget).saturating_sub(1);
            let trim = can_trim.min(excess - trimmed);
            *budget -= trim;
            trimmed += trim;
        }
    }

    budgets
}

/// Generate the WPDS coverage plan as a comment string.
pub fn generate_wpda_coverage_comment(
    language: &LanguageDef,
    pipeline: &PipelineAnalysis,
) -> String {
    let mut out = String::with_capacity(1024);

    out.push_str("// ─────────────────────────────────────────────────────────\n");
    out.push_str("// WPDS path coverage plan\n");
    out.push_str("// ─────────────────────────────────────────────────────────\n");

    let budgets = compute_category_budgets(language, pipeline, MAX_WPDS_TESTS);
    for (cat, budget) in &budgets {
        let weight = pipeline
            .category_weights
            .get(cat)
            .map(|w| format!("{:.4}", w))
            .unwrap_or_else(|| "n/a".to_string());
        out.push_str(&format!(
            "//   {:20} budget: {:3}  (category weight: {})\n",
            cat, budget, weight
        ));
    }

    out.push_str("//\n\n");
    out
}
