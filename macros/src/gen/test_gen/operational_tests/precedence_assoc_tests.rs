//! Phase 4b: Precedence and associativity test generation.
//!
//! Uses `language_def_to_spec()` + `analyze_binding_powers()` to compute binding
//! powers at macro time. Generates tests verifying:
//! - Higher-precedence operators bind tighter (e.g., `2 + 3 * 4 = 14`)
//! - Left-associative chaining (e.g., `10 - 3 - 2 = 5`)
//! - Right-associative chaining (e.g., `2 ^ 3 ^ 2 = 512`)
//! - Parenthesization overrides (e.g., `(2 + 3) * 4 = 20`)
//!
//! All recursive operations use iterative work-stacks (trampolines).
//! Everything is derived from the `language!` spec.

use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
use crate::gen::native::native_type_to_string;
use crate::gen::syntax::parser::prattail_bridge::language_def_to_spec;
use mettail_prattail::binding_power::{
    analyze_binding_powers, Associativity, BindingPowerTable, InfixOperator, InfixRuleInfo,
};
use mettail_prattail::SyntaxItemSpec;
use std::collections::{HashMap, HashSet};

use super::expr_string_gen::TestCase;
use super::symbolic_eval::{self, SymValue};

/// Maximum precedence/associativity tests per language.
const MAX_PREC_TESTS: usize = 40;

/// An infix operator with its binding power and category, derived from the spec.
#[derive(Debug, Clone)]
struct InfixOpInfo {
    label: String,
    terminal: String,
    category: String,
    left_bp: u8,
    right_bp: u8,
    is_right_assoc: bool,
}

/// Generate precedence and associativity tests.
///
/// Returns a vector of `TestCase` suitable for code generation.
pub fn generate_precedence_assoc_tests(
    language: &LanguageDef,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<TestCase> {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut test_cases: Vec<TestCase> = Vec::with_capacity(MAX_PREC_TESTS);

    // Step 1: Build the binding power table from the spec
    let spec = language_def_to_spec(language);
    let bp_table = build_bp_table_from_spec(&spec);

    // Step 2: Extract infix operator info for each category
    let ops_by_category = collect_infix_ops(&bp_table, language);

    // Step 3: Build leaf map for concrete values
    let leaf_map = super::nested_expr_gen::build_simple_leaf_map_pub(language);

    // Step 4: Generate precedence tests (pairs at different levels).
    // 2026-05-14: sort categories alphabetically so generated test
    // output is deterministic across runs (HashMap iteration order is
    // non-deterministic, and `MAX_PREC_TESTS` cap means earlier
    // categories fill the cap → testgen output churns on rebuild).
    let mut sorted_cats: Vec<&String> = ops_by_category.keys().collect();
    sorted_cats.sort();
    for category in sorted_cats {
        let ops = &ops_by_category[category];
        if test_cases.len() >= MAX_PREC_TESTS {
            break;
        }

        // Get a leaf value for this category
        let leaf = match leaf_map.get(category.as_str()) {
            Some(l) => l,
            None => continue,
        };

        // Get representative concrete values (we need 3 for a op1 b op2 c)
        let values = get_three_values(category, language);
        if values.is_none() {
            continue;
        }
        let (val_a, val_b, val_c) = values.expect("checked above");

        // Generate precedence tests for each pair of ops at different bp levels
        let mut work_stack: Vec<(usize, usize)> = Vec::new();
        for i in 0..ops.len() {
            for j in (i + 1)..ops.len() {
                work_stack.push((i, j));
            }
        }

        while let Some((i, j)) = work_stack.pop() {
            if test_cases.len() >= MAX_PREC_TESTS {
                break;
            }

            let low_op = &ops[i]; // lower precedence (declared first)
            let high_op = &ops[j]; // higher precedence (declared later)

            // Skip if same binding power
            if low_op.left_bp == high_op.left_bp {
                continue;
            }

            // Skip ambiguous rules
            if ambiguous_prefix_rules.contains(&low_op.label)
                || ambiguous_prefix_rules.contains(&high_op.label)
            {
                continue;
            }

            // Skip pairs involving power operations — they easily cause overflow
            // when one operand feeds into the exponent of the other.
            if involves_power(&low_op.label) || involves_power(&high_op.label) {
                continue;
            }

            // Generate: "a low_op b high_op c"
            // With concrete values, verify high_op binds tighter
            let prec_test = generate_precedence_test(
                &val_a, &val_b, &val_c,
                low_op, high_op,
                category,
                &lang_name_lower,
                &lang_struct,
                language,
            );
            if let Some(tc) = prec_test {
                test_cases.push(tc);
            }

            // Generate parenthesization override: "(a low_op b) high_op c"
            let paren_test = generate_paren_override_test(
                &val_a, &val_b, &val_c,
                low_op, high_op,
                category,
                &lang_name_lower,
                &lang_struct,
                language,
            );
            if let Some(tc) = paren_test {
                test_cases.push(tc);
            }
        }

        // Generate associativity tests for each operator
        for op in ops {
            if test_cases.len() >= MAX_PREC_TESTS {
                break;
            }

            if ambiguous_prefix_rules.contains(&op.label) {
                continue;
            }

            // Skip power operations for associativity tests — a^(b^c) easily overflows
            if involves_power(&op.label) {
                continue;
            }

            let assoc_test = generate_associativity_test(
                &val_a, &val_b, &val_c,
                op,
                category,
                &lang_name_lower,
                &lang_struct,
                language,
            );
            if let Some(tc) = assoc_test {
                test_cases.push(tc);
            }
        }
    }

    test_cases
}

/// Build a BindingPowerTable from a LanguageSpec by extracting infix rules
/// and running analyze_binding_powers. This replicates what the pipeline does.
fn build_bp_table_from_spec(spec: &mettail_prattail::LanguageSpec) -> BindingPowerTable {
    let infix_rules: Vec<InfixRuleInfo> = spec
        .rules
        .iter()
        .filter(|r| r.is_infix)
        .map(|r| {
            let terminal = r
                .syntax
                .iter()
                .find_map(|item| {
                    if let SyntaxItemSpec::Terminal(t) = item {
                        Some(t.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or_default();

            InfixRuleInfo {
                label: r.label.clone(),
                terminal,
                category: r.category.clone(),
                result_category: r.category.clone(),
                associativity: r.associativity,
                is_cross_category: r.is_cross_category,
                is_postfix: r.is_postfix,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
            }
        })
        .collect();

    analyze_binding_powers(&infix_rules)
}

/// Collect infix operators from the binding power table, grouped by category.
///
/// Filters out postfix, mixfix, cross-category, and operators that take more
/// than 2 parameters (e.g., ternary operators).
fn collect_infix_ops(
    bp_table: &BindingPowerTable,
    language: &LanguageDef,
) -> HashMap<String, Vec<InfixOpInfo>> {
    // Build a set of labels with more than 2 Simple params (ternary/multi-arg)
    let non_binary_labels: HashSet<String> = language
        .terms
        .iter()
        .filter(|r| {
            let param_count = r
                .term_context
                .as_ref()
                .map(|ctx| {
                    ctx.iter()
                        .filter(|p| matches!(p, mettail_ast::grammar::TermParam::Simple { .. }))
                        .count()
                })
                .unwrap_or(0);
            param_count != 2
        })
        .map(|r| r.label.to_string())
        .collect();

    let mut by_category: HashMap<String, Vec<InfixOpInfo>> = HashMap::new();

    for op in &bp_table.operators {
        if op.is_postfix || op.is_mixfix || op.is_cross_category {
            continue;
        }

        // Skip operators backed by non-binary rules (ternary, etc.)
        if non_binary_labels.contains(&op.label) {
            continue;
        }

        let info = InfixOpInfo {
            label: op.label.clone(),
            terminal: op.terminal.clone(),
            category: op.category.clone(),
            left_bp: op.left_bp,
            right_bp: op.right_bp,
            is_right_assoc: op.left_bp > op.right_bp,
        };

        by_category
            .entry(op.category.clone())
            .or_insert_with(Vec::new)
            .push(info);
    }

    // Sort each category's ops by binding power (ascending), tiebroken
    // by label so equal-bp operators always appear in the same order
    // regardless of declaration order. 2026-05-14: extra tiebreak
    // protects testgen determinism if two infix ops share both
    // left_bp and right_bp (rare but possible).
    for ops in by_category.values_mut() {
        ops.sort_by(|a, b| {
            a.left_bp
                .min(a.right_bp)
                .cmp(&b.left_bp.min(b.right_bp))
                .then_with(|| a.label.cmp(&b.label))
        });
    }

    by_category
}

/// Check if an operator label likely involves power/exponentiation.
///
/// Detected by checking if the label contains "pow" (case-insensitive).
fn involves_power(label: &str) -> bool {
    let lower = label.to_lowercase();
    lower.contains("pow") || lower.contains("exp") || lower.contains("factorial")
}

/// Get three distinct concrete values for a category.
///
/// Returns (val_a_display, val_b_display, val_c_display) as strings suitable
/// for embedding in test source expressions like `"1 + 2 * 3"`.
///
/// Uses small values (1, 2, 3) to avoid overflow issues with power operations.
fn get_three_values(
    category: &str,
    language: &LanguageDef,
) -> Option<(String, String, String)> {
    let lt = language.types.iter().find(|t| t.name.to_string() == category)?;
    let native_type = lt.native_type.as_ref()?;
    let type_str = native_type_to_string(native_type);

    match type_str.as_str() {
        "i32" | "i64" | "u32" | "u64" => Some(("1".to_string(), "2".to_string(), "3".to_string())),
        "f32" | "f64" => Some(("1.0".to_string(), "2.0".to_string(), "3.0".to_string())),
        _ => None,
    }
}

/// Get three SymValues for symbolic evaluation.
fn get_three_sym_values(
    category: &str,
    language: &LanguageDef,
) -> Option<(SymValue, SymValue, SymValue)> {
    let lt = language.types.iter().find(|t| t.name.to_string() == category)?;
    let native_type = lt.native_type.as_ref()?;
    let type_str = native_type_to_string(native_type);

    match type_str.as_str() {
        "i32" | "i64" | "u32" | "u64" => Some((SymValue::Int(1), SymValue::Int(2), SymValue::Int(3))),
        "f32" | "f64" => Some((SymValue::Float(1.0), SymValue::Float(2.0), SymValue::Float(3.0))),
        _ => None,
    }
}

/// Generate a precedence test: `a low_op b high_op c`.
///
/// Verifies that `high_op` binds tighter, so the expression evaluates as
/// `a low_op (b high_op c)`.
fn generate_precedence_test(
    val_a: &str,
    val_b: &str,
    val_c: &str,
    low_op: &InfixOpInfo,
    high_op: &InfixOpInfo,
    category: &str,
    lang_name_lower: &str,
    lang_struct: &str,
    language: &LanguageDef,
) -> Option<TestCase> {
    // Build the string expression: "a low_terminal b high_terminal c"
    let expr_str = format!(
        "{} {} {} {} {}",
        val_a, low_op.terminal, val_b, high_op.terminal, val_c
    );

    // Symbolically evaluate: first high_op(b, c), then low_op(a, result)
    let sym_vals = get_three_sym_values(category, language)?;
    let (sym_a, sym_b, sym_c) = sym_vals;

    // Find the rules for both operators
    let low_rule = language
        .terms
        .iter()
        .find(|r| r.label.to_string() == low_op.label)?;
    let high_rule = language
        .terms
        .iter()
        .find(|r| r.label.to_string() == high_op.label)?;

    // Evaluate high_op(b, c)
    let high_param_info = super::ground_term_enum::extract_param_info(high_rule, language);
    if high_param_info.len() < 2 {
        return None;
    }

    let mut high_env: HashMap<String, SymValue> = HashMap::new();
    high_env.insert(high_param_info[0].name.clone(), sym_b);
    high_env.insert(high_param_info[1].name.clone(), sym_c);

    let high_result = symbolic_eval::symbolic_eval(
        &high_rule.rust_code.as_ref()?.code,
        &high_env,
    )?;

    // Evaluate low_op(a, high_result)
    let low_param_info = super::ground_term_enum::extract_param_info(low_rule, language);
    if low_param_info.len() < 2 {
        return None;
    }

    let mut low_env: HashMap<String, SymValue> = HashMap::new();
    low_env.insert(low_param_info[0].name.clone(), sym_a);
    low_env.insert(low_param_info[1].name.clone(), high_result);

    let final_result = symbolic_eval::symbolic_eval(
        &low_rule.rust_code.as_ref()?.code,
        &low_env,
    )?;

    // Guard against overflow: skip if result is too large
    if let SymValue::Int(v) = &final_result {
        if v.abs() > 1_000_000 {
            return None;
        }
    }

    let result_native_type = language
        .types
        .iter()
        .find(|t| t.name.to_string() == category)
        .and_then(|t| t.native_type.as_ref())
        .map(|nt| native_type_to_string(nt));

    let expected = if let Some(ref rnt) = result_native_type {
        final_result.to_display_string(rnt)
    } else {
        None
    };

    let test_name = format!(
        "prec_{}_{}_{}_tighter_than_{}",
        lang_name_lower,
        high_op.label.to_lowercase(),
        low_op.label.to_lowercase(),
        super::sanitize_test_name(&expr_str)
    );

    // Generate a test that parses the string expression and evaluates it
    let construction_code = format!(
        "{{ // Precedence test: {} binds tighter than {}\n    \
        let input_str = \"{}\";\n    \
        let lang = {};\n    \
        let parsed = lang.parse_term(input_str).expect(\"parse should succeed\");\n    \
        let results = lang.run_ascent(parsed.as_ref()).expect(\"eval should succeed\");\n    \
        let nfs: Vec<String> = results.normal_forms().iter().map(|nf| nf.display.clone()).collect();\n    \
        {}}}",
        high_op.label,
        low_op.label,
        expr_str,
        lang_struct,
        if let Some(ref exp) = expected {
            format!(
                "assert!(nfs.iter().any(|d| d == \"{}\"),\n        \
                \"{{}} should evaluate to {}, got {{:?}}\", input_str, nfs);",
                exp, exp
            )
        } else {
            "assert!(!nfs.is_empty(), \"{} should produce at least one normal form\", input_str);".to_string()
        },
    );

    Some(TestCase {
        test_name,
        construction_code,
        lang_struct: lang_struct.to_string(),
        expected: None, // Custom body
    })
}

/// Generate a parenthesization override test: `(a low_op b) high_op c`.
///
/// The parentheses should force low_op to bind first.
fn generate_paren_override_test(
    val_a: &str,
    val_b: &str,
    val_c: &str,
    low_op: &InfixOpInfo,
    high_op: &InfixOpInfo,
    category: &str,
    lang_name_lower: &str,
    lang_struct: &str,
    language: &LanguageDef,
) -> Option<TestCase> {
    // Build: "(a low_terminal b) high_terminal c"
    let expr_str = format!(
        "({} {} {}) {} {}",
        val_a, low_op.terminal, val_b, high_op.terminal, val_c
    );

    // Evaluate: first low_op(a, b), then high_op(result, c)
    let sym_vals = get_three_sym_values(category, language)?;
    let (sym_a, sym_b, sym_c) = sym_vals;

    let low_rule = language
        .terms
        .iter()
        .find(|r| r.label.to_string() == low_op.label)?;
    let high_rule = language
        .terms
        .iter()
        .find(|r| r.label.to_string() == high_op.label)?;

    // Evaluate low_op(a, b)
    let low_param_info = super::ground_term_enum::extract_param_info(low_rule, language);
    if low_param_info.len() < 2 {
        return None;
    }

    let mut low_env: HashMap<String, SymValue> = HashMap::new();
    low_env.insert(low_param_info[0].name.clone(), sym_a);
    low_env.insert(low_param_info[1].name.clone(), sym_b);

    let low_result = symbolic_eval::symbolic_eval(
        &low_rule.rust_code.as_ref()?.code,
        &low_env,
    )?;

    // Evaluate high_op(low_result, c)
    let high_param_info = super::ground_term_enum::extract_param_info(high_rule, language);
    if high_param_info.len() < 2 {
        return None;
    }

    let mut high_env: HashMap<String, SymValue> = HashMap::new();
    high_env.insert(high_param_info[0].name.clone(), low_result);
    high_env.insert(high_param_info[1].name.clone(), sym_c);

    let final_result = symbolic_eval::symbolic_eval(
        &high_rule.rust_code.as_ref()?.code,
        &high_env,
    )?;

    // Guard against overflow
    if let SymValue::Int(v) = &final_result {
        if v.abs() > 1_000_000 {
            return None;
        }
    }

    let result_native_type = language
        .types
        .iter()
        .find(|t| t.name.to_string() == category)
        .and_then(|t| t.native_type.as_ref())
        .map(|nt| native_type_to_string(nt));

    let expected = if let Some(ref rnt) = result_native_type {
        final_result.to_display_string(rnt)
    } else {
        None
    };

    let test_name = format!(
        "prec_{}_paren_override_{}_{}_{}",
        lang_name_lower,
        low_op.label.to_lowercase(),
        high_op.label.to_lowercase(),
        super::sanitize_test_name(&expr_str)
    );

    let construction_code = format!(
        "{{ // Parenthesization override: ({low}) {high}\n    \
        let input_str = \"{expr}\";\n    \
        let lang = {lang_struct};\n    \
        let parsed = lang.parse_term(input_str).expect(\"parse should succeed\");\n    \
        let results = lang.run_ascent(parsed.as_ref()).expect(\"eval should succeed\");\n    \
        let nfs: Vec<String> = results.normal_forms().iter().map(|nf| nf.display.clone()).collect();\n    \
        {assertion}}}",
        low = low_op.label,
        high = high_op.label,
        expr = expr_str,
        lang_struct = lang_struct,
        assertion = if let Some(ref exp) = expected {
            format!(
                "assert!(nfs.iter().any(|d| d == \"{}\"),\n        \
                \"{{}} should evaluate to {}, got {{:?}}\", input_str, nfs);",
                exp, exp
            )
        } else {
            "assert!(!nfs.is_empty(), \"{} should produce at least one normal form\", input_str);".to_string()
        },
    );

    Some(TestCase {
        test_name,
        construction_code,
        lang_struct: lang_struct.to_string(),
        expected: None, // Custom body
    })
}

/// Generate an associativity test: `a op b op c`.
///
/// For left-assoc: verifies `(a op b) op c`.
/// For right-assoc: verifies `a op (b op c)`.
fn generate_associativity_test(
    val_a: &str,
    val_b: &str,
    val_c: &str,
    op: &InfixOpInfo,
    category: &str,
    lang_name_lower: &str,
    lang_struct: &str,
    language: &LanguageDef,
) -> Option<TestCase> {
    // Build: "a terminal b terminal c"
    let expr_str = format!(
        "{} {} {} {} {}",
        val_a, op.terminal, val_b, op.terminal, val_c
    );

    let sym_vals = get_three_sym_values(category, language)?;
    let (sym_a, sym_b, sym_c) = sym_vals;

    let rule = language
        .terms
        .iter()
        .find(|r| r.label.to_string() == op.label)?;

    let param_info = super::ground_term_enum::extract_param_info(rule, language);
    if param_info.len() < 2 {
        return None;
    }

    let expected = if op.is_right_assoc {
        // Right-assoc: a op (b op c) — evaluate inner first
        let mut inner_env: HashMap<String, SymValue> = HashMap::new();
        inner_env.insert(param_info[0].name.clone(), sym_b);
        inner_env.insert(param_info[1].name.clone(), sym_c);
        let inner_result = symbolic_eval::symbolic_eval(
            &rule.rust_code.as_ref()?.code,
            &inner_env,
        )?;

        let mut outer_env: HashMap<String, SymValue> = HashMap::new();
        outer_env.insert(param_info[0].name.clone(), sym_a);
        outer_env.insert(param_info[1].name.clone(), inner_result);
        symbolic_eval::symbolic_eval(&rule.rust_code.as_ref()?.code, &outer_env)?
    } else {
        // Left-assoc: (a op b) op c — evaluate inner first
        let mut inner_env: HashMap<String, SymValue> = HashMap::new();
        inner_env.insert(param_info[0].name.clone(), sym_a);
        inner_env.insert(param_info[1].name.clone(), sym_b);
        let inner_result = symbolic_eval::symbolic_eval(
            &rule.rust_code.as_ref()?.code,
            &inner_env,
        )?;

        let mut outer_env: HashMap<String, SymValue> = HashMap::new();
        outer_env.insert(param_info[0].name.clone(), inner_result);
        outer_env.insert(param_info[1].name.clone(), sym_c);
        symbolic_eval::symbolic_eval(&rule.rust_code.as_ref()?.code, &outer_env)?
    };

    // Guard against overflow
    if let SymValue::Int(v) = &expected {
        if v.abs() > 1_000_000 {
            return None;
        }
    }

    let result_native_type = language
        .types
        .iter()
        .find(|t| t.name.to_string() == category)
        .and_then(|t| t.native_type.as_ref())
        .map(|nt| native_type_to_string(nt));

    let expected_str = if let Some(ref rnt) = result_native_type {
        expected.to_display_string(rnt)
    } else {
        None
    };

    let assoc_str = if op.is_right_assoc { "right" } else { "left" };
    let test_name = format!(
        "assoc_{}_{}_{}",
        lang_name_lower,
        op.label.to_lowercase(),
        assoc_str
    );

    let construction_code = format!(
        "{{ // Associativity test: {label} is {assoc}-associative\n    \
        let input_str = \"{expr}\";\n    \
        let lang = {lang_struct};\n    \
        let parsed = lang.parse_term(input_str).expect(\"parse should succeed\");\n    \
        let results = lang.run_ascent(parsed.as_ref()).expect(\"eval should succeed\");\n    \
        let nfs: Vec<String> = results.normal_forms().iter().map(|nf| nf.display.clone()).collect();\n    \
        {assertion}}}",
        label = op.label,
        assoc = assoc_str,
        expr = expr_str,
        lang_struct = lang_struct,
        assertion = if let Some(ref exp) = expected_str {
            format!(
                "assert!(nfs.iter().any(|d| d == \"{}\"),\n        \
                \"{{}} ({}-assoc) should evaluate to {}, got {{:?}}\", input_str, nfs);",
                exp, assoc_str, exp
            )
        } else {
            format!(
                "assert!(!nfs.is_empty(), \"{{}} ({}-assoc) should produce at least one normal form\", input_str);",
                assoc_str
            )
        },
    );

    Some(TestCase {
        test_name,
        construction_code,
        lang_struct: lang_struct.to_string(),
        expected: None, // Custom body
    })
}
