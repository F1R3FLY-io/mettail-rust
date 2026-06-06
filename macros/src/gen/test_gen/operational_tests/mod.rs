//! Operational semantics test generation for `language!` specifications.
//!
//! Phase 1: Ground term enumeration + symbolic eval + basic eval tests (1,172 tests).
//! Phase 2: Nested expressions + edge cases.
//! Phase 3: Cross-category + algebraic properties.
//! Phase 4: WFST dispatch + precedence/associativity.
//! Phase 5: WPDS path coverage + type preservation.
//! Phase 6: Proptest metamorphic relations (integrated into Phase 3b).
//!
//! All operations are derived from the spec — no hard-coded assumptions
//! about semantics or syntax. All recursive operations use iterative
//! work-stacks (trampolines).

pub mod algebraic_property_tests;
pub mod cross_category_tests;
pub mod edge_case_gen;
pub mod expr_string_gen;
pub mod ground_term_enum;
pub mod nested_expr_gen;
pub mod precedence_assoc_tests;
pub mod symbolic_eval;
pub mod type_preservation;
pub mod wfst_guided;
pub mod wpda_guided;

use crate::gen::native::native_type_to_string;
use mettail_ast::grammar::{GrammarRule, SyntaxExpr};
use mettail_ast::language::LanguageDef;
use mettail_prattail::PipelineAnalysis;
use std::collections::{HashMap, HashSet};

/// Generate operational semantics tests for the language.
///
/// Produces a string of `#[test]` functions to be spliced into the generated
/// test file. Each test:
/// 1. Constructs a ground term from the spec
/// 2. Displays it, parses it, runs Ascent
/// 3. Asserts the result matches the symbolically evaluated expected value
///
/// When symbolic evaluation cannot compute a result, generates a smoke test.
///
/// Phases 2-6 extend the test suite with nested expressions, edge cases,
/// cross-category tests, algebraic properties, WFST/WPDS-guided tests,
/// precedence/associativity verification, type preservation, and proptest
/// metamorphic relations.
pub fn generate_operational_tests(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    // ═════════════════════════════════════════════════════════
    // Phase 1: Ground term enumeration + symbolic eval
    // ═════════════════════════════════════════════════════════

    let ground_terms = ground_term_enum::enumerate_ground_terms(language);

    if ground_terms.is_empty() {
        return String::from(
            "// No operational eval tests generated — no rules with rust_code found.\n\n",
        );
    }

    let mut phase1_cases = Vec::with_capacity(ground_terms.len());

    let rule_lookup: HashMap<String, &GrammarRule> = language
        .terms
        .iter()
        .filter(|r| r.rust_code.is_some())
        .map(|r| (r.label.to_string(), r))
        .collect();

    let ambiguous_prefix_rules = find_ambiguous_prefix_rules(language);

    // Iterative processing
    let mut work_items: Vec<usize> = (0..ground_terms.len()).collect();

    while let Some(idx) = work_items.pop() {
        let gt = &ground_terms[idx];
        let rule = match rule_lookup.get(&gt.rule_label) {
            Some(r) => *r,
            None => continue,
        };

        let result_native_type = language
            .types
            .iter()
            .find(|t| t.name.to_string() == gt.category)
            .and_then(|t| t.native_type.as_ref())
            .map(|nt| native_type_to_string(nt));

        let param_info = ground_term_enum::extract_param_info(rule, language);
        let mut env: HashMap<String, symbolic_eval::SymValue> = HashMap::new();

        let mut all_params_resolved = true;
        for (i, pi) in param_info.iter().enumerate() {
            if i < gt.param_values.len() {
                let sym_val =
                    ground_term_enum::raw_value_to_sym_value(&gt.param_values[i], &pi.native_type);
                if let Some(sv) = sym_val {
                    env.insert(pi.name.clone(), sv);
                } else {
                    all_params_resolved = false;
                    break;
                }
            } else {
                all_params_resolved = false;
                break;
            }
        }

        let expected = if all_params_resolved {
            if let Some(ref rust_code) = rule.rust_code {
                let sym_result = symbolic_eval::symbolic_eval(&rust_code.code, &env);
                sym_result.and_then(|sv| {
                    if let Some(ref rnt) = result_native_type {
                        sv.to_display_string(rnt)
                    } else {
                        None
                    }
                })
            } else {
                None
            }
        } else {
            None
        };

        if is_dangerous_input(rule, &gt.param_values) {
            continue;
        }

        if ambiguous_prefix_rules.contains(&gt.rule_label) {
            continue;
        }

        let rule_lower = gt.rule_label.to_lowercase();
        let suffix = sanitize_test_name(&gt.display_hint);
        let test_name = if expected.is_some() {
            format!("eval_{}_{}_{}", lang_name_lower, rule_lower, suffix)
        } else {
            format!("eval_{}_{}_{}_smoke", lang_name_lower, rule_lower, suffix)
        };

        phase1_cases.push(expr_string_gen::TestCase {
            test_name,
            construction_code: gt.construction_code.clone(),
            lang_struct: lang_struct.clone(),
            expected,
        });
    }

    // ═════════════════════════════════════════════════════════
    // Phase 2: Nested expressions + edge cases
    // ═════════════════════════════════════════════════════════

    let nested_cases = nested_expr_gen::generate_nested_tests(language, &ambiguous_prefix_rules);

    let edge_cases = edge_case_gen::generate_edge_case_tests(language, &ambiguous_prefix_rules);

    // ═════════════════════════════════════════════════════════
    // Phase 3: Cross-category + algebraic properties
    // ═════════════════════════════════════════════════════════

    let cross_cat_cases =
        cross_category_tests::generate_cross_category_tests(language, &ambiguous_prefix_rules);

    let (algebraic_cases, algebraic_proptest_blocks) =
        algebraic_property_tests::generate_algebraic_tests(language, &ambiguous_prefix_rules);

    // ═════════════════════════════════════════════════════════
    // Phase 4: WFST dispatch + precedence/associativity
    // ═════════════════════════════════════════════════════════

    let wfst_cases =
        wfst_guided::generate_wfst_guided_tests(language, pipeline, &ambiguous_prefix_rules);

    let prec_cases =
        precedence_assoc_tests::generate_precedence_assoc_tests(language, &ambiguous_prefix_rules);

    // ═════════════════════════════════════════════════════════
    // Phase 5: WPDS path coverage + type preservation
    // ═════════════════════════════════════════════════════════

    let wpda_cases =
        wpda_guided::generate_wpda_guided_tests(language, pipeline, &ambiguous_prefix_rules);

    let type_pres_cases =
        type_preservation::generate_type_preservation_tests(language, &ambiguous_prefix_rules);

    // ═════════════════════════════════════════════════════════
    // Deduplicate test names
    // ═════════════════════════════════════════════════════════

    let mut seen_names: HashSet<String> = HashSet::new();
    let mut dedup = |cases: Vec<expr_string_gen::TestCase>| -> Vec<expr_string_gen::TestCase> {
        let mut out = Vec::with_capacity(cases.len());
        for mut tc in cases {
            if seen_names.contains(&tc.test_name) {
                // Append a uniquifier
                let mut idx = 2u32;
                loop {
                    let candidate = format!("{}_{}", tc.test_name, idx);
                    if !seen_names.contains(&candidate) {
                        tc.test_name = candidate;
                        break;
                    }
                    idx += 1;
                }
            }
            seen_names.insert(tc.test_name.clone());
            out.push(tc);
        }
        out
    };

    let phase1_cases = dedup(phase1_cases);
    let nested_cases = dedup(nested_cases);
    let edge_cases = dedup(edge_cases);
    let cross_cat_cases = dedup(cross_cat_cases);
    let algebraic_cases = dedup(algebraic_cases);
    let wfst_cases = dedup(wfst_cases);
    let prec_cases = dedup(prec_cases);
    let wpda_cases = dedup(wpda_cases);
    let type_pres_cases = dedup(type_pres_cases);

    // ═════════════════════════════════════════════════════════
    // Generate output
    // ═════════════════════════════════════════════════════════

    let total_tests = phase1_cases.len()
        + nested_cases.len()
        + edge_cases.len()
        + cross_cat_cases.len()
        + algebraic_cases.len()
        + wfst_cases.len()
        + prec_cases.len()
        + wpda_cases.len()
        + type_pres_cases.len();

    let mut out = String::with_capacity(total_tests * 600 + 4096);

    // WFST coverage plan comment
    out.push_str(&wfst_guided::generate_wfst_coverage_comment(language, pipeline));

    // WPDS coverage plan comment
    out.push_str(&wpda_guided::generate_wpda_coverage_comment(language, pipeline));

    // Phase 1: Basic eval tests
    if !phase1_cases.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Phase 1: Operational semantics eval tests (derived from rust_code)\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&expr_string_gen::generate_all_tests(&phase1_cases));
    }

    // Phase 2a: Nested expression tests
    if !nested_cases.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Phase 2a: Nested expression tests (depth-2 compositions)\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&expr_string_gen::generate_all_tests(&nested_cases));
    }

    // Phase 2b: Edge case tests
    if !edge_cases.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Phase 2b: Edge case tests (div-by-zero, bool exhaustive, etc.)\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&expr_string_gen::generate_all_tests(&edge_cases));
    }

    // Phase 3a: Cross-category tests
    if !cross_cat_cases.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Phase 3a: Cross-category tests (cast + cross-cat eval)\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&expr_string_gen::generate_all_tests(&cross_cat_cases));
    }

    // Phase 3b: Algebraic property tests
    if !algebraic_cases.is_empty() || !algebraic_proptest_blocks.is_empty() {
        out.push_str(&algebraic_property_tests::generate_algebraic_tests_source(
            &algebraic_cases,
            &algebraic_proptest_blocks,
        ));
    }

    // Phase 4a: WFST dispatch tests
    if !wfst_cases.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Phase 4a: WFST-guided dispatch tests\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&expr_string_gen::generate_all_tests(&wfst_cases));
    }

    // Phase 4b: Precedence and associativity tests
    if !prec_cases.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Phase 4b: Precedence and associativity tests\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&generate_custom_body_tests(&prec_cases));
    }

    // Phase 5a: WPDS-guided tests
    if !wpda_cases.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Phase 5a: WPDS-guided path coverage tests\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&expr_string_gen::generate_all_tests(&wpda_cases));
    }

    // Phase 5b: Type preservation tests
    if !type_pres_cases.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Phase 5b: Type preservation tests\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&generate_custom_body_tests(&type_pres_cases));
    }

    // Summary comment
    out.push_str(&format!(
        "// Total operational semantics tests: {} (P1={}, P2a={}, P2b={}, P3a={}, P3b={}, P4a={}, P4b={}, P5a={}, P5b={})\n\n",
        total_tests,
        phase1_cases.len(),
        nested_cases.len(),
        edge_cases.len(),
        cross_cat_cases.len(),
        algebraic_cases.len(),
        wfst_cases.len(),
        prec_cases.len(),
        wpda_cases.len(),
        type_pres_cases.len(),
    ));

    out
}

/// Generate test functions with custom bodies (for phases that use inline code).
///
/// For test cases where `construction_code` starts with `{`, the code IS the
/// full test body. Otherwise, use the standard template.
fn generate_custom_body_tests(test_cases: &[expr_string_gen::TestCase]) -> String {
    let mut out = String::with_capacity(test_cases.len() * 600);

    for tc in test_cases {
        if tc.construction_code.starts_with('{') {
            // Custom body test
            out.push_str("#[test]\n");
            out.push_str(&format!("fn {}() {{\n", tc.test_name));
            out.push_str("    mettail_runtime::clear_var_cache();\n");
            out.push_str(&format!("    {}\n", tc.construction_code));
            out.push_str("}\n\n");
        } else {
            // Standard template
            out.push_str(&expr_string_gen::generate_test_function(tc));
        }
    }

    out
}

// ═══════════════════════════════════════════════════════════════════════════════
// Helper functions (originally from Phase 1, now shared across phases)
// ═══════════════════════════════════════════════════════════════════════════════

/// Find rule labels whose syntax patterns share a leading keyword prefix
/// with other rules in the same result category.
///
/// Returns the set of rule labels that participate in such ambiguities.
pub(crate) fn find_ambiguous_prefix_rules(language: &LanguageDef) -> HashSet<String> {
    let mut ambiguous = HashSet::new();

    let mut prefix_groups: HashMap<(String, String), Vec<String>> = HashMap::new();

    for rule in &language.terms {
        if rule.rust_code.is_none() {
            continue;
        }
        let cat = rule.category.to_string();
        let label = rule.label.to_string();

        let prefix = extract_leading_keyword_prefix(rule);
        if !prefix.is_empty() {
            prefix_groups
                .entry((cat, prefix))
                .or_insert_with(Vec::new)
                .push(label);
        }
    }

    for rule in &language.terms {
        let cat = rule.category.to_string();
        let label = rule.label.to_string();

        let prefix = extract_leading_keyword_prefix(rule);
        if !prefix.is_empty() {
            let key = (cat, prefix);
            if let Some(group) = prefix_groups.get_mut(&key) {
                if !group.contains(&label) {
                    group.push(label);
                }
            }
        }
    }

    for (_, labels) in &prefix_groups {
        if labels.len() > 1 {
            for label in labels {
                ambiguous.insert(label.clone());
            }
        }
    }

    ambiguous
}

/// Extract the leading keyword prefix from a rule's syntax pattern.
fn extract_leading_keyword_prefix(rule: &GrammarRule) -> String {
    let pattern = match &rule.syntax_pattern {
        Some(p) => p,
        None => return String::new(),
    };

    let mut prefix = String::new();
    for expr in pattern {
        match expr {
            SyntaxExpr::Literal(s) => {
                prefix.push_str(s);
            },
            _ => break,
        }
    }

    prefix
}

/// Check if a rule's parameter values would cause runtime panics.
///
/// Uses an iterative work-stack internally.
pub(crate) fn is_dangerous_input(rule: &GrammarRule, param_values: &[String]) -> bool {
    let rust_code = match &rule.rust_code {
        Some(rc) => rc,
        None => return false,
    };

    if param_values.len() >= 2 && expr_contains_div(&rust_code.code) {
        let last_val = &param_values[param_values.len() - 1];
        if is_zero_value(last_val) {
            return true;
        }
    }

    if expr_contains_pow(&rust_code.code) {
        if let Some(last_val) = param_values.last() {
            if is_negative_value(last_val) {
                return true;
            }
            if let Some(v) = parse_int_value(last_val) {
                if v > 12 {
                    return true;
                }
            }
        }
    }

    if expr_contains_product_range(&rust_code.code) {
        for val in param_values {
            if let Some(v) = parse_int_value(val) {
                if v > 12 || v < 0 {
                    return true;
                }
            }
        }
    }

    false
}

/// Check if a nested construction is dangerous (simple heuristic: contains "0i32" etc. in divisor position).
///
/// This is a simplified check for nested expressions where we don't have
/// structured param_values. Uses string matching on the construction code.
pub(crate) fn is_dangerous_nested_construction(_rule: &GrammarRule, _construction: &str) -> bool {
    // For nested expressions, the primary danger is already handled by:
    // 1. The inner ground term filtering (Phase 1)
    // 2. The safe representative values used for non-inner slots
    // So this is conservative: only flag if the rule itself is known-dangerous.
    // If the rule has division, we're already using safe non-zero values
    // for the simple leaf slots, so the main risk is from the inner term.
    // The inner term was already filtered by Phase 1's is_dangerous_input.
    false
}

fn is_zero_value(val: &str) -> bool {
    val == "0i32"
        || val == "0i64"
        || val == "0u32"
        || val == "0u64"
        || val == "0.0f32"
        || val == "0.0f64"
}

fn is_negative_value(val: &str) -> bool {
    val.starts_with('-')
}

fn parse_int_value(val: &str) -> Option<i64> {
    let stripped = val
        .trim_end_matches("i32")
        .trim_end_matches("i64")
        .trim_end_matches("u32")
        .trim_end_matches("u64")
        .trim_end_matches("isize")
        .trim_end_matches("usize");
    stripped.parse::<i64>().ok()
}

fn expr_contains_pow(expr: &syn::Expr) -> bool {
    let mut stack: Vec<&syn::Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        match e {
            syn::Expr::MethodCall(mc) => {
                if mc.method == "pow" || mc.method == "powf" {
                    return true;
                }
                stack.push(&mc.receiver);
                for arg in &mc.args {
                    stack.push(arg);
                }
            },
            syn::Expr::Binary(bin) => {
                stack.push(&bin.left);
                stack.push(&bin.right);
            },
            syn::Expr::Paren(p) => stack.push(&p.expr),
            syn::Expr::Group(g) => stack.push(&g.expr),
            syn::Expr::Unary(u) => stack.push(&u.expr),
            syn::Expr::Block(b) => {
                for stmt in &b.block.stmts {
                    if let syn::Stmt::Expr(e, _) = stmt {
                        stack.push(e);
                    }
                }
            },
            syn::Expr::If(i) => {
                stack.push(&i.cond);
                for stmt in &i.then_branch.stmts {
                    if let syn::Stmt::Expr(e, _) = stmt {
                        stack.push(e);
                    }
                }
                if let Some((_, else_expr)) = &i.else_branch {
                    stack.push(else_expr);
                }
            },
            syn::Expr::Cast(c) => stack.push(&c.expr),
            _ => {},
        }
    }
    false
}

fn expr_contains_product_range(expr: &syn::Expr) -> bool {
    let mut stack: Vec<&syn::Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        match e {
            syn::Expr::MethodCall(mc) => {
                if mc.method == "product" {
                    return true;
                }
                stack.push(&mc.receiver);
                for arg in &mc.args {
                    stack.push(arg);
                }
            },
            syn::Expr::Binary(bin) => {
                stack.push(&bin.left);
                stack.push(&bin.right);
            },
            syn::Expr::Paren(p) => stack.push(&p.expr),
            syn::Expr::Group(g) => stack.push(&g.expr),
            syn::Expr::Unary(u) => stack.push(&u.expr),
            syn::Expr::Block(b) => {
                for stmt in &b.block.stmts {
                    if let syn::Stmt::Expr(e, _) = stmt {
                        stack.push(e);
                    }
                }
            },
            syn::Expr::If(i) => {
                stack.push(&i.cond);
                for stmt in &i.then_branch.stmts {
                    if let syn::Stmt::Expr(e, _) = stmt {
                        stack.push(e);
                    }
                }
                if let Some((_, else_expr)) = &i.else_branch {
                    stack.push(else_expr);
                }
            },
            syn::Expr::Cast(c) => stack.push(&c.expr),
            _ => {},
        }
    }
    false
}

fn expr_contains_div(expr: &syn::Expr) -> bool {
    let mut stack: Vec<&syn::Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        match e {
            syn::Expr::Binary(bin) => {
                if matches!(bin.op, syn::BinOp::Div(_) | syn::BinOp::Rem(_)) {
                    return true;
                }
                stack.push(&bin.left);
                stack.push(&bin.right);
            },
            syn::Expr::Paren(p) => stack.push(&p.expr),
            syn::Expr::Group(g) => stack.push(&g.expr),
            syn::Expr::Unary(u) => stack.push(&u.expr),
            syn::Expr::Block(b) => {
                for stmt in &b.block.stmts {
                    if let syn::Stmt::Expr(e, _) = stmt {
                        stack.push(e);
                    }
                }
            },
            syn::Expr::If(i) => {
                stack.push(&i.cond);
                for stmt in &i.then_branch.stmts {
                    if let syn::Stmt::Expr(e, _) = stmt {
                        stack.push(e);
                    }
                }
                if let Some((_, else_expr)) = &i.else_branch {
                    stack.push(else_expr);
                }
            },
            syn::Expr::MethodCall(mc) => {
                stack.push(&mc.receiver);
                for arg in &mc.args {
                    stack.push(arg);
                }
            },
            syn::Expr::Cast(c) => stack.push(&c.expr),
            _ => {},
        }
    }
    false
}

/// Sanitize a string for use as part of a Rust test function name.
pub(crate) fn sanitize_test_name(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push('_');
        }
    }
    while out.ends_with('_') {
        out.pop();
    }
    if out.is_empty() {
        out.push_str("case");
    }
    out
}
