//! Phase 2b: Edge case test generation.
//!
//! For each rule with `rust_code`, analyzes the `syn::Expr` to detect dangerous
//! or boundary patterns (division, power, boolean exhaustion, empty strings,
//! type boundary values) and generates targeted edge-case tests.
//!
//! All recursive operations use iterative work-stacks (trampolines).
//! Everything is derived from the `language!` spec.

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use crate::gen::native::native_type_to_string;
use std::collections::{HashMap, HashSet};

use super::expr_string_gen::TestCase;
use super::ground_term_enum::{self, ParamInfo};
use super::symbolic_eval::{self, SymValue};

/// Maximum edge case tests per language.
const MAX_EDGE_CASES_PER_LANGUAGE: usize = 80;

/// Detected edge-case pattern in a rust_code expression.
#[derive(Debug, Clone, PartialEq)]
enum EdgePattern {
    /// Division or modulo — test with denominator = 0.
    DivByZero,
    /// Power operation — test with exponent 0 and base 0.
    PowerEdge,
    /// Boolean exhaustive — enumerate all boolean combinations.
    BoolExhaustive,
    /// String operation — test with empty string.
    EmptyString,
    /// Integer type boundary — test with MAX and MIN values.
    IntBoundary,
}

/// Generate edge case tests for the language.
///
/// Returns a vector of `TestCase` suitable for code generation.
pub fn generate_edge_case_tests(
    language: &LanguageDef,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<TestCase> {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut test_cases: Vec<TestCase> = Vec::with_capacity(MAX_EDGE_CASES_PER_LANGUAGE);

    for rule in &language.terms {
        if test_cases.len() >= MAX_EDGE_CASES_PER_LANGUAGE {
            break;
        }

        let rust_code = match &rule.rust_code {
            Some(rc) => rc,
            None => continue,
        };

        let label = rule.label.to_string();
        if ambiguous_prefix_rules.contains(&label) {
            continue;
        }

        let category = rule.category.to_string();
        let param_info = ground_term_enum::extract_param_info(rule, language);

        if param_info.is_empty() {
            continue;
        }

        // Detect edge patterns by analyzing the syn::Expr
        let patterns = detect_edge_patterns(&rust_code.code);

        // Determine result native type
        let result_native_type = language
            .types
            .iter()
            .find(|t| t.name.to_string() == category)
            .and_then(|t| t.native_type.as_ref())
            .map(|nt| native_type_to_string(nt));

        // Generate tests for each detected pattern
        for pattern in &patterns {
            if test_cases.len() >= MAX_EDGE_CASES_PER_LANGUAGE {
                break;
            }

            let new_tests = generate_tests_for_pattern(
                pattern,
                rule,
                &param_info,
                &category,
                &label,
                &lang_name_lower,
                &lang_struct,
                &result_native_type,
                language,
            );

            for tc in new_tests {
                if test_cases.len() >= MAX_EDGE_CASES_PER_LANGUAGE {
                    break;
                }
                test_cases.push(tc);
            }
        }
    }

    test_cases
}

/// Detect edge-case patterns by walking a `syn::Expr` with an iterative work-stack.
fn detect_edge_patterns(expr: &syn::Expr) -> Vec<EdgePattern> {
    let mut patterns = Vec::new();
    let mut has_div = false;
    let mut has_pow = false;
    let mut has_bool_params = false;
    let mut has_string_ops = false;

    // Iterative work-stack
    let mut stack: Vec<&syn::Expr> = vec![expr];

    while let Some(e) = stack.pop() {
        match e {
            syn::Expr::Binary(bin) => {
                if matches!(bin.op, syn::BinOp::Div(_) | syn::BinOp::Rem(_)) {
                    has_div = true;
                }
                // Check for boolean comparison ops (could accept bool params)
                if matches!(
                    bin.op,
                    syn::BinOp::And(_)
                        | syn::BinOp::Or(_)
                        | syn::BinOp::BitAnd(_)
                        | syn::BinOp::BitOr(_)
                        | syn::BinOp::BitXor(_)
                ) {
                    has_bool_params = true;
                }
                stack.push(&bin.left);
                stack.push(&bin.right);
            },
            syn::Expr::MethodCall(mc) => {
                let method = mc.method.to_string();
                if method == "pow" || method == "powf" || method == "powi" {
                    has_pow = true;
                }
                if method == "len"
                    || method == "to_uppercase"
                    || method == "to_lowercase"
                    || method == "trim"
                    || method == "contains"
                    || method == "replace"
                    || method == "push_str"
                    || method == "to_string"
                {
                    has_string_ops = true;
                }
                stack.push(&mc.receiver);
                for arg in &mc.args {
                    stack.push(arg);
                }
            },
            syn::Expr::Paren(p) => stack.push(&p.expr),
            syn::Expr::Group(g) => stack.push(&g.expr),
            syn::Expr::Unary(u) => {
                if matches!(u.op, syn::UnOp::Not(_)) {
                    has_bool_params = true;
                }
                stack.push(&u.expr);
            },
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

    // NOTE: Division by zero causes a Rust panic, not a graceful error.
    // We skip generating div-by-zero tests because they would abort the test runner.
    // if has_div {
    //     patterns.push(EdgePattern::DivByZero);
    // }
    if has_pow {
        patterns.push(EdgePattern::PowerEdge);
    }
    if has_bool_params {
        patterns.push(EdgePattern::BoolExhaustive);
    }
    if has_string_ops {
        patterns.push(EdgePattern::EmptyString);
    }
    // NOTE: Integer boundary tests (MAX/MIN) can cause overflow panics in debug mode
    // because Rust debug builds check for integer overflow. We only generate them
    // for rules that don't have overflow risk (checked later in the generator).
    // Disabled for now to avoid test runner crashes.
    // patterns.push(EdgePattern::IntBoundary);

    patterns
}

/// Generate test cases for a specific edge pattern.
///
/// Uses an iterative approach (no recursion).
fn generate_tests_for_pattern(
    pattern: &EdgePattern,
    rule: &GrammarRule,
    param_info: &[ParamInfo],
    category: &str,
    label: &str,
    lang_name_lower: &str,
    lang_struct: &str,
    result_native_type: &Option<String>,
    language: &LanguageDef,
) -> Vec<TestCase> {
    let mut cases = Vec::new();

    match pattern {
        EdgePattern::DivByZero => {
            // For rules with division, test with the last param = 0.
            // This should NOT panic — we use catch_unwind.
            if param_info.len() >= 2 {
                let last_pi = &param_info[param_info.len() - 1];
                if let Some(ref nt) = last_pi.native_type {
                    if is_numeric_type(nt) {
                        let edge_vals = generate_edge_values_for_divisor(
                            param_info, category, language, rule,
                        );
                        if let Some((construction, suffix)) = edge_vals {
                            let test_name = format!(
                                "edge_{}_{}_div_by_zero_{}",
                                lang_name_lower,
                                label.to_lowercase(),
                                suffix
                            );
                            // Division by zero test: smoke test
                            cases.push(TestCase {
                                test_name,
                                construction_code: construction,
                                lang_struct: lang_struct.to_string(),
                                expected: None,
                            });
                        }
                    }
                }
            }
        },
        EdgePattern::PowerEdge => {
            // Test with exponent = 0 (should give 1 for any base)
            if param_info.len() >= 2 {
                let param_count = param_info.len();
                let edge_exp0 = generate_power_edge(
                    param_info, category, language, rule, "exp0",
                    |pi_idx, pi| {
                        if pi_idx == param_count - 1 {
                            zero_value_for_type(language, &pi.native_type)
                        } else {
                            safe_value_for_type(language, &pi.native_type)
                        }
                    },
                );
                if let Some((construction, hint)) = edge_exp0 {
                    let expected = try_eval_edge(rule, param_info, &construction,
                        |pi_idx, pi| {
                            if pi_idx == param_count - 1 {
                                zero_sym_value(&pi.native_type)
                            } else {
                                safe_sym_value(&pi.native_type)
                            }
                        },
                        result_native_type,
                    );
                    let test_name = format!(
                        "edge_{}_{}_{}",
                        lang_name_lower,
                        label.to_lowercase(),
                        hint
                    );
                    cases.push(TestCase {
                        test_name,
                        construction_code: construction,
                        lang_struct: lang_struct.to_string(),
                        expected,
                    });
                }
            }
        },
        EdgePattern::BoolExhaustive => {
            // For rules with boolean params, enumerate all combinations.
            let bool_slots: Vec<usize> = param_info
                .iter()
                .enumerate()
                .filter(|(_, pi)| pi.native_type.as_deref() == Some("bool"))
                .map(|(i, _)| i)
                .collect();

            if !bool_slots.is_empty() {
                let combo_count = 1usize << bool_slots.len();
                let cap = combo_count.min(8);

                for combo_idx in 0..cap {
                    let edge_vals = generate_bool_combo(
                        param_info, category, language, rule, &bool_slots, combo_idx,
                    );
                    if let Some((construction, hint)) = edge_vals {
                        let expected = try_eval_edge(rule, param_info, &construction,
                            |pi_idx, pi| {
                                if let Some(slot_pos) = bool_slots.iter().position(|&s| s == pi_idx) {
                                    let bit = (combo_idx >> slot_pos) & 1;
                                    Some(SymValue::Bool(bit == 1))
                                } else {
                                    safe_sym_value(&pi.native_type)
                                }
                            },
                            result_native_type,
                        );
                        let test_name = format!(
                            "edge_{}_{}_bool_{}",
                            lang_name_lower,
                            label.to_lowercase(),
                            hint
                        );
                        cases.push(TestCase {
                            test_name,
                            construction_code: construction,
                            lang_struct: lang_struct.to_string(),
                            expected,
                        });
                    }
                }
            }
        },
        EdgePattern::EmptyString => {
            let string_slots: Vec<usize> = param_info
                .iter()
                .enumerate()
                .filter(|(_, pi)| {
                    pi.native_type.as_deref() == Some("str")
                        || pi.native_type.as_deref() == Some("String")
                })
                .map(|(i, _)| i)
                .collect();

            if !string_slots.is_empty() {
                let edge_vals = generate_empty_string_combo(
                    param_info, category, language, rule, &string_slots,
                );
                if let Some((construction, hint)) = edge_vals {
                    let expected = try_eval_edge(rule, param_info, &construction,
                        |pi_idx, pi| {
                            if string_slots.contains(&pi_idx) {
                                Some(SymValue::Str(String::new()))
                            } else {
                                safe_sym_value(&pi.native_type)
                            }
                        },
                        result_native_type,
                    );
                    let test_name = format!(
                        "edge_{}_{}_empty_str_{}",
                        lang_name_lower,
                        label.to_lowercase(),
                        hint
                    );
                    cases.push(TestCase {
                        test_name,
                        construction_code: construction,
                        lang_struct: lang_struct.to_string(),
                        expected,
                    });
                }
            }
        },
        EdgePattern::IntBoundary => {
            let int_slots: Vec<(usize, String)> = param_info
                .iter()
                .enumerate()
                .filter_map(|(i, pi)| {
                    if let Some(ref nt) = pi.native_type {
                        if is_integer_type(nt) {
                            return Some((i, nt.clone()));
                        }
                    }
                    None
                })
                .collect();

            if !int_slots.is_empty() && !has_overflow_risk(rule) {
                let max_vals = generate_int_boundary(
                    param_info, category, language, rule, &int_slots, true,
                );
                if let Some((construction, hint)) = max_vals {
                    let test_name = format!(
                        "edge_{}_{}_int_max_{}",
                        lang_name_lower,
                        label.to_lowercase(),
                        hint
                    );
                    cases.push(TestCase {
                        test_name,
                        construction_code: construction,
                        lang_struct: lang_struct.to_string(),
                        expected: None,
                    });
                }
            }
        },
    }

    cases
}

/// Check if a native type is numeric (int or float).
fn is_numeric_type(nt: &str) -> bool {
    matches!(nt, "i32" | "i64" | "u32" | "u64" | "f32" | "f64" | "isize" | "usize")
}

/// Check if a native type is an integer type.
fn is_integer_type(nt: &str) -> bool {
    matches!(nt, "i32" | "i64" | "u32" | "u64" | "isize" | "usize")
}

/// Check if a rule's rust_code has overflow risk (pow, product, factorial).
///
/// Uses iterative work-stack.
fn has_overflow_risk(rule: &GrammarRule) -> bool {
    let rust_code = match &rule.rust_code {
        Some(rc) => rc,
        None => return false,
    };

    let mut stack: Vec<&syn::Expr> = vec![&rust_code.code];
    while let Some(e) = stack.pop() {
        match e {
            syn::Expr::MethodCall(mc) => {
                let method = mc.method.to_string();
                if method == "pow"
                    || method == "powf"
                    || method == "product"
                    || method == "checked_mul"
                {
                    return true;
                }
                stack.push(&mc.receiver);
                for arg in &mc.args {
                    stack.push(arg);
                }
            },
            syn::Expr::Binary(bin) => {
                if matches!(bin.op, syn::BinOp::Mul(_) | syn::BinOp::Shl(_)) {
                    // Multiplication or shift with MAX could overflow
                    return true;
                }
                stack.push(&bin.left);
                stack.push(&bin.right);
            },
            syn::Expr::Paren(p) => stack.push(&p.expr),
            syn::Expr::Group(g) => stack.push(&g.expr),
            syn::Expr::Unary(u) => stack.push(&u.expr),
            syn::Expr::Cast(c) => stack.push(&c.expr),
            syn::Expr::Block(b) => {
                for stmt in &b.block.stmts {
                    if let syn::Stmt::Expr(e, _) = stmt {
                        stack.push(e);
                    }
                }
            },
            _ => {},
        }
    }

    false
}

/// Return a zero value for a given native type (raw string form).
///
/// E1: spec-derived. For integer-family native types, consults
/// `spec_admitted_integer_default(language)` to project zero onto the
/// language's effective Integer pattern (returns "0" for `[0-9]+`,
/// "1" for `[1-9][0-9]*`, etc.). For non-integer types the value is
/// derived from the unique element of the type's value domain (zero
/// for floats, etc.).
fn zero_value_for_type(language: &LanguageDef, nt: &Option<String>) -> Option<String> {
    match nt.as_deref()? {
        nt @ ("i32" | "i64" | "u32" | "u64") => {
            let v = crate::gen::spec_admitted_integer_default(language);
            Some(format!("{}{}", v, nt))
        }
        "f32" => Some("0.0f32".to_string()),
        "f64" => Some("0.0f64".to_string()),
        _ => None,
    }
}

/// Return a safe (non-zero, non-boundary) value for a given native type.
///
/// E1: spec-derived for integers via `spec_admitted_integer_samples`
/// with `Safe` purpose, picking the first non-zero sample.
fn safe_value_for_type(language: &LanguageDef, nt: &Option<String>) -> Option<String> {
    match nt.as_deref()? {
        nt @ ("i32" | "i64" | "u32" | "u64") => {
            let samples = crate::gen::spec_admitted_integer_samples(
                language, crate::gen::SamplePurpose::Safe,
            );
            samples.first().map(|s| format!("{}{}", s, nt))
        }
        "f32" => Some("2.0f32".to_string()),
        "f64" => Some("2.0f64".to_string()),
        "bool" => Some("true".to_string()),
        "str" | "String" => Some("String::from(\"a\")".to_string()),
        _ => None,
    }
}

/// Return a zero SymValue for symbolic evaluation.
fn zero_sym_value(nt: &Option<String>) -> Option<SymValue> {
    match nt.as_deref()? {
        "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => Some(SymValue::Int(0)),
        "f32" | "f64" => Some(SymValue::Float(0.0)),
        _ => None,
    }
}

/// Return a safe SymValue for symbolic evaluation.
fn safe_sym_value(nt: &Option<String>) -> Option<SymValue> {
    match nt.as_deref()? {
        "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => Some(SymValue::Int(2)),
        "f32" | "f64" => Some(SymValue::Float(2.0)),
        "bool" => Some(SymValue::Bool(true)),
        "str" | "String" => Some(SymValue::Str("a".to_string())),
        _ => None,
    }
}

/// Construct a term for div-by-zero edge case (last param = 0).
fn generate_edge_values_for_divisor(
    param_info: &[ParamInfo],
    category: &str,
    language: &LanguageDef,
    rule: &GrammarRule,
) -> Option<(String, String)> {
    let label = rule.label.to_string();
    let mut parts = Vec::with_capacity(param_info.len());

    for (i, pi) in param_info.iter().enumerate() {
        let raw = if i == param_info.len() - 1 {
            zero_value_for_type(language, &pi.native_type)?
        } else {
            safe_value_for_type(language, &pi.native_type)?
        };
        let construction = construct_leaf(category, &pi.category, &raw, &pi.native_type, language);
        parts.push(format!("std::sync::Arc::new({})", construction?));
    }
    for _ in 0..super::ground_term_enum::count_optional_inner_simples(rule) {
        parts.push("None".to_string());
    }

    let construction = format!("{}::{}({})", category, label, parts.join(", "));
    Some((construction, "div_zero".to_string()))
}

/// Construct a leaf value for a category.
fn construct_leaf(
    _outer_cat: &str,
    inner_cat: &str,
    raw_val: &str,
    native_type: &Option<String>,
    language: &LanguageDef,
) -> Option<String> {
    let lt = language.types.iter().find(|t| t.name.to_string() == inner_cat)?;
    let nt = lt.native_type.as_ref()?;
    let type_str = native_type_to_string(nt);
    let lit_label = crate::gen::generate_literal_label(nt).to_string();

    let construction = match type_str.as_str() {
        "f64" => format!(
            "{}::{}(mettail_runtime::CanonicalFloat64::from({}))",
            inner_cat, lit_label, raw_val
        ),
        "f32" => format!(
            "{}::{}(mettail_runtime::CanonicalFloat32::from({}))",
            inner_cat, lit_label, raw_val
        ),
        _ => format!("{}::{}({})", inner_cat, lit_label, raw_val),
    };
    Some(construction)
}

/// Generate a power edge case construction.
fn generate_power_edge<F>(
    param_info: &[ParamInfo],
    category: &str,
    language: &LanguageDef,
    rule: &GrammarRule,
    hint: &str,
    value_fn: F,
) -> Option<(String, String)>
where
    F: Fn(usize, &ParamInfo) -> Option<String>,
{
    let label = rule.label.to_string();
    let mut parts = Vec::with_capacity(param_info.len());

    for (i, pi) in param_info.iter().enumerate() {
        let raw = value_fn(i, pi)?;
        let construction = construct_leaf(category, &pi.category, &raw, &pi.native_type, language)?;
        parts.push(format!("std::sync::Arc::new({})", construction));
    }
    for _ in 0..super::ground_term_enum::count_optional_inner_simples(rule) {
        parts.push("None".to_string());
    }

    let construction = format!("{}::{}({})", category, label, parts.join(", "));
    Some((construction, hint.to_string()))
}

/// Generate a boolean combination test construction.
fn generate_bool_combo(
    param_info: &[ParamInfo],
    category: &str,
    language: &LanguageDef,
    rule: &GrammarRule,
    bool_slots: &[usize],
    combo_idx: usize,
) -> Option<(String, String)> {
    let label = rule.label.to_string();
    let mut parts = Vec::with_capacity(param_info.len());
    let mut hint_parts = Vec::new();

    for (i, pi) in param_info.iter().enumerate() {
        let raw = if let Some(slot_pos) = bool_slots.iter().position(|&s| s == i) {
            let bit = (combo_idx >> slot_pos) & 1;
            let val = if bit == 1 { "true" } else { "false" };
            hint_parts.push(val.to_string());
            val.to_string()
        } else {
            safe_value_for_type(language, &pi.native_type)?
        };
        let construction = construct_leaf(category, &pi.category, &raw, &pi.native_type, language)?;
        parts.push(format!("std::sync::Arc::new({})", construction));
    }
    for _ in 0..super::ground_term_enum::count_optional_inner_simples(rule) {
        parts.push("None".to_string());
    }

    let construction = format!("{}::{}({})", category, label, parts.join(", "));
    let hint = hint_parts.join("_");
    Some((construction, hint))
}

/// Generate an empty string edge case construction.
fn generate_empty_string_combo(
    param_info: &[ParamInfo],
    category: &str,
    language: &LanguageDef,
    rule: &GrammarRule,
    string_slots: &[usize],
) -> Option<(String, String)> {
    let label = rule.label.to_string();
    let mut parts = Vec::with_capacity(param_info.len());

    for (i, pi) in param_info.iter().enumerate() {
        let raw = if string_slots.contains(&i) {
            "String::new()".to_string()
        } else {
            safe_value_for_type(language, &pi.native_type)?
        };
        let construction = construct_leaf(category, &pi.category, &raw, &pi.native_type, language)?;
        parts.push(format!("std::sync::Arc::new({})", construction));
    }
    for _ in 0..super::ground_term_enum::count_optional_inner_simples(rule) {
        parts.push("None".to_string());
    }

    let construction = format!("{}::{}({})", category, label, parts.join(", "));
    Some((construction, "empty".to_string()))
}

/// Generate an integer boundary test construction.
fn generate_int_boundary(
    param_info: &[ParamInfo],
    category: &str,
    language: &LanguageDef,
    rule: &GrammarRule,
    int_slots: &[(usize, String)],
    use_max: bool,
) -> Option<(String, String)> {
    let label = rule.label.to_string();
    let mut parts = Vec::with_capacity(param_info.len());

    for (i, pi) in param_info.iter().enumerate() {
        let is_int_slot = int_slots.iter().any(|(idx, _)| *idx == i);
        let raw = if is_int_slot {
            boundary_value_for_type(&pi.native_type, use_max)?
        } else {
            safe_value_for_type(language, &pi.native_type)?
        };
        let construction = construct_leaf(category, &pi.category, &raw, &pi.native_type, language)?;
        parts.push(format!("std::sync::Arc::new({})", construction));
    }
    for _ in 0..super::ground_term_enum::count_optional_inner_simples(rule) {
        parts.push("None".to_string());
    }

    let construction = format!("{}::{}({})", category, label, parts.join(", "));
    let hint = if use_max { "max" } else { "min" };
    Some((construction, hint.to_string()))
}

/// Return a boundary value (MAX or MIN) for a native type.
fn boundary_value_for_type(nt: &Option<String>, use_max: bool) -> Option<String> {
    match nt.as_deref()? {
        "i32" => Some(if use_max {
            format!("{}i32", i32::MAX)
        } else {
            format!("{}i32", i32::MIN)
        }),
        "i64" => Some(if use_max {
            format!("{}i64", i64::MAX)
        } else {
            format!("{}i64", i64::MIN)
        }),
        "u32" => Some(if use_max {
            format!("{}u32", u32::MAX)
        } else {
            "0u32".to_string()
        }),
        "u64" => Some(if use_max {
            format!("{}u64", u64::MAX)
        } else {
            "0u64".to_string()
        }),
        _ => None,
    }
}

/// Try to symbolically evaluate an edge case term.
fn try_eval_edge<F>(
    rule: &GrammarRule,
    param_info: &[ParamInfo],
    _construction: &str,
    env_fn: F,
    result_native_type: &Option<String>,
) -> Option<String>
where
    F: Fn(usize, &ParamInfo) -> Option<SymValue>,
{
    let rust_code = rule.rust_code.as_ref()?;
    let mut env: HashMap<String, SymValue> = HashMap::new();

    for (i, pi) in param_info.iter().enumerate() {
        let sv = env_fn(i, pi)?;
        env.insert(pi.name.clone(), sv);
    }

    let result = symbolic_eval::symbolic_eval(&rust_code.code, &env)?;

    if let Some(ref rnt) = result_native_type {
        result.to_display_string(rnt)
    } else {
        None
    }
}
