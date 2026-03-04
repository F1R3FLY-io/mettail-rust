//! Exhaustive edge case test suite for all supported grammars.
//!
//! Covers cross-category operators inside cast parentheses, comparisons after
//! cast results, nested keyword-prefix functions, operator chains, postfix +
//! cross-category combinations, ternary edge cases, parenthesization stress,
//! whitespace variations, negative tests, and language-specific edge cases for
//! Lambda, Ambient, RhoCalc, Composition languages, and LedTest.
//!
//! Run:
//!   cargo test -p mettail-languages --test edge_case_tests
//!   cargo test -p mettail-languages --test edge_case_tests --features led-test

use mettail_languages::calculator::{self as calc};
use mettail_runtime::Language;

// ════════════════════════════════════════════════════════════════════════════════
// Shared helpers
// ════════════════════════════════════════════════════════════════════════════════

/// Parse input via the Calculator language, run Ascent, assert `expected` is
/// among the normal-form display strings.
fn calc_normal_form(input: &str, expected: &str) {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang
        .parse_term(input)
        .unwrap_or_else(|e| panic!("parse({:?}) failed: {}", input, e));
    let results = lang
        .run_ascent(term.as_ref())
        .unwrap_or_else(|e| panic!("run_ascent({:?}) failed: {}", input, e));
    let displays: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        displays.contains(&expected.to_string()),
        "expected normal form {:?} for {:?}, got: {:?}",
        expected,
        input,
        displays,
    );
}

/// Parse input via the Calculator language — assert parse succeeds (no Ascent).
fn calc_parses(input: &str) {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    lang.parse_term(input)
        .unwrap_or_else(|e| panic!("parse({:?}) failed: {}", input, e));
}

/// Parse input via the Calculator language — assert parse FAILS.
fn calc_parse_fails(input: &str) {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    assert!(
        lang.parse_term(input).is_err(),
        "expected parse failure for {:?}, but it succeeded",
        input,
    );
}

/// Parse + Ascent via a generic Language, assert `expected` is among normal forms.
fn lang_normal_form(lang: &dyn Language, input: &str, expected: &str) {
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(input)
        .unwrap_or_else(|e| panic!("parse({:?}) failed: {}", input, e));
    let results = lang
        .run_ascent(term.as_ref())
        .unwrap_or_else(|e| panic!("run_ascent({:?}) failed: {}", input, e));
    let displays: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        displays.contains(&expected.to_string()),
        "expected normal form {:?} for {:?}, got: {:?}",
        expected,
        input,
        displays,
    );
}

/// Parse via a generic Language — assert parse succeeds (no Ascent).
fn lang_parses(lang: &dyn Language, input: &str) {
    mettail_runtime::clear_var_cache();
    lang.parse_term(input)
        .unwrap_or_else(|e| panic!("parse({:?}) failed: {}", input, e));
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 1: Cross-Category Operators Inside Cast Parentheses (~36 tests)
// ════════════════════════════════════════════════════════════════════════════════
//
// The core bug class: every cast function must handle arguments containing
// cross-category comparison operators.

mod cross_cat_ops_inside_casts {
    use super::*;

    // 1A: Comparison operators inside str()

    #[test]
    fn str_of_int_eq() {
        calc_normal_form("str(3 == 3)", r#""true""#);
    }

    #[test]
    fn str_of_int_ne() {
        calc_normal_form("str(3 != 3)", r#""false""#);
    }

    #[test]
    fn str_of_int_gt() {
        calc_normal_form("str(3 > 1)", r#""true""#);
    }

    #[test]
    fn str_of_int_lt() {
        calc_normal_form("str(1 < 3)", r#""true""#);
    }

    #[test]
    fn str_of_int_ge() {
        calc_normal_form("str(3 >= 3)", r#""true""#);
    }

    #[test]
    fn str_of_int_le() {
        calc_normal_form("str(3 <= 3)", r#""true""#);
    }

    #[test]
    fn str_of_zero_gt_zero_regression() {
        // Bug 4 regression: str(0 > 0) must parse and evaluate
        calc_normal_form("str(0 > 0)", r#""false""#);
    }

    // 1B: Comparisons inside bool()

    #[test]
    fn bool_of_int_eq() {
        calc_normal_form("bool(1 == 1)", "true");
    }

    #[test]
    fn bool_of_int_ne() {
        calc_normal_form("bool(1 != 2)", "true");
    }

    #[test]
    fn bool_of_int_gt() {
        calc_normal_form("bool(3 > 1)", "true");
    }

    #[test]
    fn bool_of_int_lt() {
        calc_normal_form("bool(1 < 3)", "true");
    }

    #[test]
    fn bool_of_int_ge() {
        calc_normal_form("bool(3 >= 3)", "true");
    }

    #[test]
    fn bool_of_int_le() {
        calc_normal_form("bool(3 <= 3)", "true");
    }

    // 1C: Float comparisons inside casts

    #[test]
    fn str_of_float_gt() {
        calc_normal_form("str(1.0 > 0.0)", r#""true""#);
    }

    #[test]
    fn str_of_float_eq() {
        calc_normal_form("str(1.0 == 1.0)", r#""true""#);
    }

    #[test]
    fn str_of_float_lt() {
        calc_normal_form("str(1.0 < 2.0)", r#""true""#);
    }

    // 1D: Same-category arithmetic inside casts (verify no regression)

    #[test]
    fn str_of_int_add() {
        calc_normal_form("str(1 + 2)", r#""3""#);
    }

    #[test]
    fn str_of_int_mul() {
        calc_normal_form("str(3 * 4)", r#""12""#);
    }

    #[test]
    fn str_of_int_pow() {
        calc_normal_form("str(2 ^ 3)", r#""8""#);
    }

    #[test]
    fn str_of_bool_and() {
        calc_normal_form("str(true and false)", r#""false""#);
    }

    #[test]
    fn str_of_bool_or() {
        calc_normal_form("str(true or false)", r#""true""#);
    }

    #[test]
    fn str_of_bool_not() {
        calc_normal_form("str(not true)", r#""false""#);
    }

    #[test]
    fn float_of_int_add() {
        calc_normal_form("float(1 + 2)", "3.0");
    }

    #[test]
    fn float_of_int_sub() {
        calc_normal_form("float(10 - 3)", "7.0");
    }

    #[test]
    fn float_of_int_mul() {
        calc_normal_form("float(3 * 4)", "12.0");
    }

    #[test]
    fn float_of_int_pow() {
        calc_normal_form("float(2 ^ 3)", "8.0");
    }

    #[test]
    fn int_of_float_add() {
        calc_normal_form("int(1.0 + 2.0)", "3");
    }

    #[test]
    fn int_of_float_sub() {
        calc_normal_form("int(3.5 - 1.5)", "2");
    }

    #[test]
    fn bool_of_int_add_truthy() {
        calc_normal_form("bool(1 + 0)", "true");
    }

    #[test]
    fn bool_of_int_sub_falsy() {
        calc_normal_form("bool(1 - 1)", "false");
    }

    #[test]
    fn bool_of_int_mul_falsy() {
        calc_normal_form("bool(2 * 0)", "false");
    }

    // 1E: Complex expressions inside casts

    #[test]
    fn str_of_grouped_mul() {
        calc_normal_form("str((1 + 2) * 3)", r#""9""#);
    }

    #[test]
    fn str_of_factorial() {
        calc_normal_form("str(5!)", r#""120""#);
    }

    #[test]
    fn bool_of_factorial_minus() {
        calc_normal_form("bool(3! - 6)", "false");
    }

    #[test]
    fn float_of_precedence() {
        calc_normal_form("float(1 + 2 * 3)", "7.0");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 2: Comparison After Cast/Function Results (~14 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod comparison_after_cast_results {
    use super::*;

    #[test]
    fn float_cast_eq() {
        calc_normal_form("float(3) == 3.0", "true");
    }

    #[test]
    fn float_cast_ne() {
        calc_normal_form("float(3) != 3.0", "false");
    }

    #[test]
    fn float_cast_gt() {
        calc_normal_form("float(3) > 2.0", "true");
    }

    #[test]
    fn float_cast_lt() {
        calc_normal_form("float(3) < 4.0", "true");
    }

    #[test]
    fn float_cast_ge() {
        calc_normal_form("float(3) >= 3.0", "true");
    }

    #[test]
    fn float_cast_le() {
        calc_normal_form("float(3) <= 3.0", "true");
    }

    #[test]
    fn int_cast_eq() {
        calc_normal_form("int(3.14) == 3", "true");
    }

    #[test]
    fn int_cast_gt() {
        calc_normal_form("int(3.14) > 2", "true");
    }

    #[test]
    fn int_cast_ge_regression() {
        // Bug 2 regression: int(3.14) >= 3 must parse and evaluate
        calc_normal_form("int(3.14) >= 3", "true");
    }

    #[test]
    fn int_cast_ne() {
        calc_normal_form("int(3.14) != 4", "true");
    }

    #[test]
    fn int_cast_lt() {
        calc_normal_form("int(3.14) < 4", "true");
    }

    #[test]
    fn int_cast_le() {
        calc_normal_form("int(3.14) <= 3", "true");
    }

    #[test]
    fn bool_cast_eq() {
        calc_normal_form("bool(1) == true", "true");
    }

    #[test]
    fn bool_cast_ne() {
        calc_normal_form("bool(0) != true", "true");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 3: Nested Keyword-Prefix Functions (~26 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod nested_keyword_prefix_functions {
    use super::*;

    // 3A: Nested cast functions (cross-type matrix)

    #[test]
    fn str_of_int_of_float() {
        calc_normal_form("str(int(3.14))", r#""3""#);
    }

    #[test]
    fn str_of_float_of_int() {
        calc_normal_form("str(float(3))", r#""3.0""#);
    }

    #[test]
    fn str_of_bool_of_int() {
        calc_normal_form("str(bool(1))", r#""true""#);
    }

    #[test]
    fn bool_of_int_of_float() {
        calc_normal_form("bool(int(3.14))", "true");
    }

    #[test]
    fn bool_of_float_of_int() {
        calc_normal_form("bool(float(3))", "true");
    }

    #[test]
    fn int_of_bool_true() {
        calc_normal_form("int(bool(true))", "1");
    }

    #[test]
    fn float_of_bool_false() {
        calc_normal_form("float(bool(false))", "0.0");
    }

    #[test]
    fn bool_of_bool_identity() {
        calc_normal_form("bool(bool(true))", "true");
    }

    #[test]
    fn deep_chain_str_float_int_bool() {
        // str(float(int(bool(true)))) → str(float(int(true))) → str(float(1)) → str(1.0) → "1.0"
        calc_normal_form("str(float(int(bool(true))))", r#""1.0""#);
    }

    // 3B: Nested math functions

    #[test]
    fn sin_of_cos() {
        // sin(cos(1.0)) — just verify it parses and evaluates
        calc_parses("sin(cos(1.0))");
    }

    #[test]
    fn cos_of_sin_zero() {
        calc_normal_form("cos(sin(0.0))", "1.0");
    }

    #[test]
    fn exp_of_ln_one() {
        calc_normal_form("exp(ln(1.0))", "1.0");
    }

    #[test]
    fn ln_of_exp_one() {
        calc_normal_form("ln(exp(1.0))", "1.0");
    }

    #[test]
    fn sin_cos_sin_three_deep() {
        calc_parses("sin(cos(sin(1.0)))");
    }

    // 3C: Cast wrapping math functions

    #[test]
    fn str_of_sin() {
        calc_parses("str(sin(1.0))");
    }

    #[test]
    fn int_of_sin() {
        calc_parses("int(sin(1.0))");
    }

    #[test]
    fn sin_of_float_cast() {
        calc_parses("sin(float(3))");
    }

    #[test]
    fn cos_of_float_cast() {
        calc_parses("cos(float(3))");
    }

    #[test]
    fn exp_of_float_cast() {
        calc_parses("exp(float(1))");
    }

    #[test]
    fn ln_of_float_one() {
        calc_normal_form("ln(float(1))", "0.0");
    }

    // 3D: Three-deep mixed nesting

    #[test]
    fn int_float_int_roundtrip() {
        calc_normal_form("int(float(int(3.14)))", "3");
    }

    #[test]
    fn float_int_float_roundtrip() {
        calc_normal_form("float(int(float(3)))", "3.0");
    }

    #[test]
    fn exp_ln_exp_three_deep() {
        calc_parses("exp(ln(exp(1.0)))");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 4: Operator Chains After Cast Results (~12 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod operator_chains_after_casts {
    use super::*;

    #[test]
    fn float_cast_add_float_cast() {
        calc_normal_form("float(3) + float(4)", "7.0");
    }

    #[test]
    fn float_cast_mul_float_cast() {
        calc_normal_form("float(3) * float(4)", "12.0");
    }

    #[test]
    fn float_cast_pow_float_cast() {
        calc_normal_form("float(2) ^ float(3)", "8.0");
    }

    #[test]
    fn int_cast_add_int_cast() {
        calc_normal_form("int(1.0) + int(2.0)", "3");
    }

    #[test]
    fn literal_add_float_cast() {
        calc_normal_form("1.0 + float(3)", "4.0");
    }

    #[test]
    fn literal_mul_int_cast() {
        calc_normal_form("2 * int(3.14)", "6");
    }

    #[test]
    fn three_int_casts_chained() {
        calc_normal_form("int(1.0) + int(2.0) + int(3.0)", "6");
    }

    #[test]
    fn float_cast_add_literal_eq() {
        calc_normal_form("float(3) + 1.0 == 4.0", "true");
    }

    #[test]
    fn int_cast_mul_gt() {
        calc_normal_form("int(3.14) * 2 > 5", "true");
    }

    #[test]
    fn sin_add_cos() {
        calc_parses("sin(1.0) + cos(1.0)");
    }

    #[test]
    fn pythagorean_identity() {
        calc_normal_form("sin(1.0) * sin(1.0) + cos(1.0) * cos(1.0)", "1.0");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 5: Postfix + Cross-Category Combinations (~12 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod postfix_cross_category {
    use super::*;

    #[test]
    fn factorial_eq() {
        calc_normal_form("3! == 6", "true");
    }

    #[test]
    fn factorial_ne() {
        calc_normal_form("3! != 5", "true");
    }

    #[test]
    fn factorial_gt() {
        calc_normal_form("3! > 5", "true");
    }

    #[test]
    fn factorial_lt() {
        calc_normal_form("3! < 7", "true");
    }

    #[test]
    fn factorial_ge() {
        calc_normal_form("3! >= 6", "true");
    }

    #[test]
    fn factorial_le() {
        calc_normal_form("3! <= 6", "true");
    }

    #[test]
    fn grouped_factorial_eq() {
        calc_normal_form("(3 + 2)! == 120", "true");
    }

    #[test]
    fn grouped_factorial_gt() {
        calc_normal_form("(3 + 2)! > 100", "true");
    }

    #[test]
    fn float_of_factorial() {
        calc_normal_form("float(3!)", "6.0");
    }

    #[test]
    fn str_of_factorial() {
        calc_normal_form("str(3!)", r#""6""#);
    }

    #[test]
    fn bool_of_factorial() {
        calc_normal_form("bool(3!)", "true");
    }

    #[test]
    fn bool_of_zero_factorial() {
        // 0! = 1, bool(1) = true
        calc_normal_form("bool(0!)", "true");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 6: Unary Prefix + Ternary Combinations (~9 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod unary_prefix_ternary {
    use super::*;

    #[test]
    fn neg_ternary_true() {
        calc_normal_form("-(1 ? 2 : 3)", "-2");
    }

    #[test]
    fn neg_ternary_false() {
        calc_normal_form("-(0 ? 2 : 3)", "-3");
    }

    #[test]
    fn ternary_neg_then() {
        calc_normal_form("1 ? -2 : 3", "-2");
    }

    #[test]
    fn ternary_neg_else() {
        calc_normal_form("0 ? 2 : -3", "-3");
    }

    #[test]
    fn ternary_add_then() {
        calc_normal_form("1 ? 2 + 3 : 4", "5");
    }

    #[test]
    fn ternary_add_else() {
        calc_normal_form("0 ? 2 : 3 + 4", "7");
    }

    #[test]
    fn ternary_mul_both() {
        calc_normal_form("1 ? 2 * 3 : 4 * 5", "6");
    }

    #[test]
    fn ternary_factorial_then() {
        calc_normal_form("1 ? 3! : 0", "6");
    }

    #[test]
    fn ternary_factorial_else() {
        calc_normal_form("0 ? 0 : 3!", "6");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 7: Casts Inside Ternary Branches (~6 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod casts_inside_ternary {
    use super::*;

    #[test]
    fn int_cast_in_then() {
        calc_normal_form("1 ? int(3.14) : 0", "3");
    }

    #[test]
    fn int_cast_in_else() {
        calc_normal_form("0 ? 0 : int(3.14)", "3");
    }

    #[test]
    fn int_cast_expr_in_then() {
        calc_normal_form("1 ? int(1.0 + 2.0) : 0", "3");
    }

    #[test]
    fn int_cast_expr_in_else() {
        calc_normal_form("0 ? 0 : int(1.0 + 2.0)", "3");
    }

    #[test]
    fn int_cast_as_condition_truthy() {
        // int(3.14) = 3 (nonzero → then branch)
        calc_normal_form("int(3.14) ? 10 : 20", "10");
    }

    #[test]
    fn int_cast_as_condition_falsy() {
        // int(0.0) = 0 (zero → else branch)
        calc_normal_form("int(0.0) ? 10 : 20", "20");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 8: Chained Casts with Operators Between (~8 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod chained_casts_with_operators {
    use super::*;

    #[test]
    fn str_of_int_cast_plus_one() {
        calc_normal_form("str(int(3.14) + 1)", r#""4""#);
    }

    #[test]
    fn float_of_int_cast_plus_one() {
        calc_parses("float(int(3.14) + 1)");
    }

    #[test]
    fn bool_of_int_cast_plus_one() {
        calc_normal_form("bool(int(3.14) + 1)", "true");
    }

    #[test]
    fn str_of_float_cast_add_float_cast() {
        calc_parses("str(float(3) + float(4))");
    }

    #[test]
    fn str_of_int_cast_mul_plus() {
        calc_parses("str(int(3.14) * 2 + 1)");
    }

    #[test]
    fn str_of_cross_cat_eq_true() {
        calc_normal_form("str(3 + 5 == 8)", r#""true""#);
    }

    #[test]
    fn str_of_cross_cat_eq_false() {
        calc_normal_form("str(1 + 2 == 4)", r#""false""#);
    }

    #[test]
    fn str_of_not_eq() {
        calc_normal_form("str(not (1 == 2))", r#""true""#);
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 9: Bool Logic with Parenthesized Cross-Category (~8 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod bool_logic_cross_category {
    use super::*;

    #[test]
    fn triple_and_eq() {
        calc_normal_form("(1 == 1) and (2 == 2) and (3 == 3)", "true");
    }

    #[test]
    fn or_gt_lt() {
        calc_normal_form("(1 > 0) or (1 < 0)", "true");
    }

    #[test]
    fn not_eq() {
        calc_normal_form("not (1 == 2)", "true");
    }

    #[test]
    fn xor_same() {
        calc_normal_form("(1 == 1) xor (2 == 2)", "false");
    }

    #[test]
    fn xor_different() {
        calc_normal_form("(1 == 1) xor (1 == 2)", "true");
    }

    #[test]
    fn not_gt_and_gt() {
        calc_normal_form("not (1 > 2) and (3 > 2)", "true");
    }

    #[test]
    fn bool_cast_and_bool_cast() {
        calc_normal_form("bool(1) and bool(1)", "true");
    }

    #[test]
    fn not_bool_cast_zero() {
        calc_normal_form("not bool(0)", "true");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 10: String-Specific Edge Cases (~6 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod string_edge_cases {
    use super::*;

    #[test]
    fn len_hello_world() {
        calc_normal_form(r#"|"hello" ++ "world"|"#, "10");
    }

    #[test]
    fn len_empty() {
        calc_normal_form(r#"|""|"#, "0");
    }

    #[test]
    fn str_cast_concat_str_cast() {
        calc_parses(r#"str(42) ++ str(43)"#);
    }

    #[test]
    fn str_cast_add_str_cast() {
        calc_parses(r#"str(42) + str(43)"#);
    }

    #[test]
    fn str_cast_eq_literal() {
        calc_normal_form(r#"str(1 + 2) == "3""#, "true");
    }

    #[test]
    fn str_of_true_eq_literal() {
        calc_normal_form(r#"str(true) == "true""#, "true");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 11: Parenthesization Stress (~10 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod parenthesization_stress {
    use super::*;

    #[test]
    fn quad_nested_parens() {
        calc_normal_form("((((1))))", "1");
    }

    #[test]
    fn double_paren_add() {
        calc_normal_form("((1 + 2))", "3");
    }

    #[test]
    fn float_cast_paren() {
        calc_normal_form("float((3))", "3.0");
    }

    #[test]
    fn paren_float_cast_paren() {
        calc_normal_form("(float((3)))", "3.0");
    }

    #[test]
    fn int_cast_paren() {
        calc_normal_form("int((3.14))", "3");
    }

    #[test]
    fn str_cast_paren_add() {
        calc_normal_form("str((1 + 2))", r#""3""#);
    }

    #[test]
    fn double_paren_mul() {
        calc_normal_form("((1 + 2) * (3 + 4))", "21");
    }

    #[test]
    fn paren_bool_and() {
        calc_normal_form("((true) and (false))", "false");
    }

    #[test]
    fn paren_not_true() {
        calc_normal_form("(not (true))", "false");
    }

    #[test]
    fn paren_eq_paren() {
        calc_normal_form("(1 == (2))", "false");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 12: Whitespace Variations (~10 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod whitespace_variations {
    use super::*;

    #[test]
    fn no_spaces() {
        calc_normal_form("1+2", "3");
    }

    #[test]
    fn space_before_op() {
        calc_normal_form("1 +2", "3");
    }

    #[test]
    fn space_after_op() {
        calc_normal_form("1+ 2", "3");
    }

    #[test]
    fn extra_leading_trailing_spaces() {
        calc_normal_form("  1 + 2  ", "3");
    }

    #[test]
    fn float_cast_inner_spaces() {
        calc_normal_form("float( 3 )", "3.0");
    }

    #[test]
    fn sin_inner_spaces() {
        calc_parses("sin( 1.0 )");
    }

    #[test]
    fn str_cast_inner_spaces() {
        calc_parses("str(  1 + 2  )");
    }

    #[test]
    fn ternary_no_spaces() {
        calc_normal_form("1?2:3", "2");
    }

    #[test]
    fn neg_with_spaces() {
        calc_normal_form("-  3", "-3");
    }

    #[test]
    fn not_with_spaces() {
        calc_normal_form("not  true", "false");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 13: Negative Tests — Expected Parse Failures (~12 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod negative_tests {
    use super::*;

    #[test]
    fn unclosed_float_paren() {
        calc_parse_fails("float(");
    }

    #[test]
    fn unclosed_str_paren() {
        calc_parse_fails("str(3");
    }

    #[test]
    fn empty_float_args() {
        calc_parse_fails("float()");
    }

    #[test]
    fn empty_int_args() {
        calc_parse_fails("int()");
    }

    #[test]
    fn empty_str_args() {
        calc_parse_fails("str()");
    }

    #[test]
    fn empty_bool_args() {
        calc_parse_fails("bool()");
    }

    #[test]
    fn empty_sin_args() {
        calc_parse_fails("sin()");
    }

    #[test]
    fn empty_cos_args() {
        calc_parse_fails("cos()");
    }

    #[test]
    fn incomplete_expression() {
        calc_parse_fails("1 + ");
    }

    #[test]
    fn trailing_tokens() {
        calc_parse_fails("1 2 3");
    }

    #[test]
    fn nested_unclosed_float() {
        calc_parse_fails("float(float(");
    }

    #[test]
    fn nested_unclosed_str_int() {
        calc_parse_fails("str(int(");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 14: Lambda Language Edge Cases (~10 tests, parse-only)
// ════════════════════════════════════════════════════════════════════════════════

mod lambda_edge_cases {
    use mettail_languages::lambda::Term;

    fn lambda_parses(input: &str) {
        mettail_runtime::clear_var_cache();
        Term::parse(input)
            .unwrap_or_else(|e| panic!("lambda parse({:?}) failed: {}", input, e));
    }

    #[test]
    fn identity() {
        lambda_parses("lam x.x");
    }

    #[test]
    fn application() {
        lambda_parses("(lam x.x, y)");
    }

    #[test]
    fn k_combinator() {
        lambda_parses("lam x.lam y.x");
    }

    #[test]
    fn apply_to_nested() {
        lambda_parses("(lam x.lam y.x, a)");
    }

    #[test]
    fn apply_application_result() {
        lambda_parses("((lam x.x, a), b)");
    }

    #[test]
    fn self_application_body() {
        lambda_parses("lam x.(x, x)");
    }

    #[test]
    fn omega_variant() {
        lambda_parses("(lam x.(x, x), lam y.y)");
    }

    #[test]
    fn church_numeral_two() {
        lambda_parses("lam f.lam x.(f, (f, x))");
    }

    #[test]
    fn church_one_applied() {
        lambda_parses("(lam f.lam x.(f, x), lam y.y)");
    }

    #[test]
    fn s_combinator() {
        lambda_parses("lam x.lam y.lam z.((x, z), (y, z))");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 15: Ambient Calculus Edge Cases (~10 tests, parse-only)
// ════════════════════════════════════════════════════════════════════════════════

mod ambient_edge_cases {
    use mettail_languages::ambient::Proc;

    fn ambient_parses(input: &str) {
        mettail_runtime::clear_var_cache();
        Proc::parse(input)
            .unwrap_or_else(|e| panic!("ambient parse({:?}) failed: {}", input, e));
    }

    #[test]
    fn simple_ambient() {
        ambient_parses("n[0]");
    }

    #[test]
    fn parallel_ambients() {
        ambient_parses("{n[0] | m[0]}");
    }

    #[test]
    fn in_capability() {
        ambient_parses("in(m, 0)");
    }

    #[test]
    fn out_capability() {
        ambient_parses("out(m, 0)");
    }

    #[test]
    fn open_capability() {
        ambient_parses("open(n, 0)");
    }

    #[test]
    fn bound_var_as_ambient_name() {
        ambient_parses("new(x, x[0])");
    }

    #[test]
    fn nested_new() {
        ambient_parses("new(x, new(y, {x[0] | y[0]}))");
    }

    #[test]
    fn nested_capabilities() {
        ambient_parses("{in(m, in(n, 0))}");
    }

    #[test]
    fn mixed_in_ambient() {
        ambient_parses("n[{in(m, 0) | out(m, 0)}]");
    }

    #[test]
    fn open_plus_target() {
        ambient_parses("{open(n, 0) | n[{0}]}");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 16: RhoCalc Edge Cases (~16 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod rhocalc_edge_cases {
    use mettail_languages::rhocalc::{Proc, RhoCalcLanguage};
    use mettail_runtime::Language;

    fn rhocalc_parses(input: &str) {
        mettail_runtime::clear_var_cache();
        Proc::parse(input)
            .unwrap_or_else(|e| panic!("rhocalc parse({:?}) failed: {}", input, e));
    }

    fn rhocalc_reduces_to(input: &str, expected: &str) {
        mettail_runtime::clear_var_cache();
        let lang = RhoCalcLanguage;
        let term = lang
            .parse_term(input)
            .unwrap_or_else(|e| panic!("parse({:?}) failed: {}", input, e));
        let results = lang
            .run_ascent(term.as_ref())
            .unwrap_or_else(|e| panic!("run_ascent({:?}) failed: {}", input, e));
        let nfs: Vec<String> = results
            .normal_forms()
            .iter()
            .map(|nf| nf.display.clone())
            .collect();

        // Parse expected in a fresh context for display comparison
        mettail_runtime::clear_var_cache();
        let expected_proc = Proc::parse(expected)
            .unwrap_or_else(|e| panic!("parse expected({:?}) failed: {}", expected, e));
        let expected_display = expected_proc.to_string();

        assert!(
            nfs.iter().any(|nf| nf == &expected_display),
            "expected {:?} for {:?}, got: {:?}",
            expected_display,
            input,
            nfs,
        );
    }

    // 16A: Arithmetic & comparisons

    #[test]
    fn chained_add() {
        rhocalc_reduces_to("{1 + 2 + 3}", "6");
    }

    #[test]
    fn grouped_mul() {
        rhocalc_reduces_to("{(1 + 2) * 3}", "9");
    }

    #[test]
    fn comparison_and() {
        rhocalc_parses("{1 == 1 and 2 == 2}");
    }

    #[test]
    fn not_eq() {
        rhocalc_parses("{not (1 == 2)}");
    }

    #[test]
    fn chained_gt() {
        rhocalc_parses("{3 > 2 and 2 > 1}");
    }

    // 16B: Type conversions with expressions

    #[test]
    fn str_of_add() {
        rhocalc_reduces_to(r#"{str(1 + 2)}"#, r#""3""#);
    }

    #[test]
    fn str_of_eq() {
        rhocalc_reduces_to(r#"{str(1 == 1)}"#, r#""true""#);
    }

    #[test]
    fn str_of_zero_gt_zero() {
        // Bug 4 analog in RhoCalc
        rhocalc_reduces_to(r#"{str(0 > 0)}"#, r#""false""#);
    }

    #[test]
    fn int_of_float_add() {
        rhocalc_parses("{int(1.5 + 2.5)}");
    }

    #[test]
    fn bool_of_int_add() {
        rhocalc_parses("{bool(1 + 0)}");
    }

    #[test]
    fn float_of_int_add() {
        rhocalc_parses("{float(1 + 2)}");
    }

    // 16C: Process calculus nesting

    #[test]
    fn comm_under_new() {
        rhocalc_parses("new(x) in { {(x?y).{*(y)} | x!(42)} }");
    }

    #[test]
    fn exec_of_quoted_arithmetic() {
        rhocalc_parses("{*(@(1 + 2))}");
    }

    #[test]
    fn nested_concat() {
        rhocalc_parses(r#"{concat("hello", concat("wor", "ld"))}"#);
    }

    #[test]
    fn len_of_concat() {
        rhocalc_parses(r#"{len(concat("a", "bc"))}"#);
    }

    #[test]
    fn dollar_proc_regression() {
        // Existing dollar syntax — regression test
        rhocalc_parses("$proc(^f.{f}, {})");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 17: Composition Language Edge Cases (~10 tests)
// ════════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "test-languages")]
mod composition_edge_cases {
    use super::*;
    use mettail_languages::composition::composed_lang::CalcLambdaLanguage;
    use mettail_languages::composition::extended_lang::ExtMathLanguage;
    use mettail_languages::composition::grammar_import_lang::ImportedMathLanguage;
    use mettail_languages::composition::mixed_lang::MixedMathLanguage;

    #[test]
    fn ext_math_grouped_add() {
        lang_normal_form(&ExtMathLanguage, "(1 + 2) + (3 + 4)", "10");
    }

    #[test]
    fn ext_math_chained_ops() {
        lang_normal_form(&ExtMathLanguage, "1 + 2 - 3 + 4", "4");
    }

    #[test]
    fn mixed_math_neg_add() {
        lang_normal_form(&MixedMathLanguage, "-1 + 2", "1");
    }

    #[test]
    fn mixed_math_neg_grouped() {
        lang_normal_form(&MixedMathLanguage, "-(1 + 2)", "-3");
    }

    #[test]
    fn mixed_math_and_not() {
        lang_normal_form(&MixedMathLanguage, "true and (not false)", "true");
    }

    #[test]
    fn mixed_math_not_and() {
        lang_normal_form(&MixedMathLanguage, "not (true and false)", "true");
    }

    #[test]
    fn imported_math_div_add() {
        lang_normal_form(&ImportedMathLanguage, "(10 / 2) + (10 / 5)", "7");
    }

    #[test]
    fn imported_math_div_add_precedence() {
        // Verify precedence: 10 / 2 + 3 — depends on operator precedence
        lang_parses(&ImportedMathLanguage, "10 / 2 + 3");
    }

    #[test]
    fn calc_lambda_arithmetic() {
        lang_normal_form(&CalcLambdaLanguage, "1 + 2", "3");
    }

    #[test]
    fn calc_lambda_lambda_expr() {
        lang_parses(&CalcLambdaLanguage, "lam x.x");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 18: LedTest Edge Cases (~9 tests)
// ════════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "test-languages")]
mod led_test_edge_cases {
    use mettail_languages::led_test::{self as lt, Expr, LedTestLanguage, Num};
    use mettail_runtime::Language;

    fn led_normal_form(input: &str, expected: &str) {
        mettail_runtime::clear_var_cache();
        let lang = LedTestLanguage;
        let term = lang
            .parse_term(input)
            .unwrap_or_else(|e| panic!("parse({:?}) failed: {}", input, e));
        let results = lang
            .run_ascent(term.as_ref())
            .unwrap_or_else(|e| panic!("run_ascent({:?}) failed: {}", input, e));
        let displays: Vec<String> = results
            .normal_forms()
            .iter()
            .map(|nf| nf.display.clone())
            .collect();
        assert!(
            displays.contains(&expected.to_string()),
            "expected normal form {:?} for {:?}, got: {:?}",
            expected,
            input,
            displays,
        );
    }

    fn led_parses(input: &str) {
        mettail_runtime::clear_var_cache();
        let lang = LedTestLanguage;
        lang.parse_term(input)
            .unwrap_or_else(|e| panic!("parse({:?}) failed: {}", input, e));
    }

    #[test]
    fn precedence_chain() {
        led_normal_form("1 + 2 * 3 + 4", "11");
    }

    #[test]
    fn grouping() {
        led_normal_form("(1 + 2) * (3 + 4)", "21");
    }

    #[test]
    fn postfix_plus_precedence() {
        // 3! + 2! * 3 = 6 + 2*3 = 6 + 6 = 12
        led_normal_form("3! + 2! * 3", "12");
    }

    #[test]
    fn unary_plus_infix_via_delegation() {
        led_normal_form("-3 + 4", "1");
    }

    #[test]
    fn grouped_unary() {
        led_normal_form("-(3 + 4)", "-7");
    }

    #[test]
    fn led_chain_num_to_pred() {
        // 1 + 2 == 3 and 4 == 4 → cross-category chain
        led_parses("1 + 2 == 3 and 4 == 4");
    }

    #[test]
    fn delegation_plus_own_op() {
        // 1 + 2 | 3 + 4 — delegation on both sides of own Expr op
        led_parses("1 + 2 | 3 + 4");
    }

    #[test]
    fn auto_projection_plus_cross_cat() {
        // x + y == z — auto-projection + cross-category
        led_parses("x + y == z");
    }

    #[test]
    fn auto_projection_postfix() {
        // x! + y! — auto-projection with postfix on both operands
        led_parses("x! + y!");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 19: Precedence/Associativity Stress (~10 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod precedence_associativity_stress {
    use super::*;

    #[test]
    fn power_before_addition_right() {
        calc_normal_form("2 ^ 3 + 1", "9");
    }

    #[test]
    fn power_before_addition_left() {
        calc_normal_form("1 + 2 ^ 3", "9");
    }

    #[test]
    fn power_before_multiplication() {
        calc_normal_form("2 ^ 3 * 2", "16");
    }

    #[test]
    fn unary_binds_tighter_than_power() {
        // -3 ^ 2 = (-3) ^ 2 = 9 (unary binds tighter)
        calc_normal_form("-3 ^ 2", "9");
    }

    #[test]
    fn postfix_binds_tighter_than_unary() {
        // -3! = -(3!) = -6
        calc_normal_form("-3!", "-6");
    }

    #[test]
    fn complex_postfix_pow_add() {
        // 3! ^ 2 + 1 = 6^2 + 1 = 36 + 1 = 37
        calc_normal_form("3! ^ 2 + 1", "37");
    }

    #[test]
    fn mul_factorial_add() {
        // 2 * 3! + 1 = 2 * 6 + 1 = 13
        calc_normal_form("2 * 3! + 1", "13");
    }

    #[test]
    fn left_assoc_subtraction() {
        // 10 - 3 - 2 - 1 = ((10-3)-2)-1 = 4
        calc_normal_form("10 - 3 - 2 - 1", "4");
    }

    #[test]
    fn right_assoc_power() {
        // 2 ^ 3 ^ 2 = 2 ^ (3^2) = 2 ^ 9 = 512 (right-associative)
        // Uses direct eval() since Ascent doesn't fully reduce chained power.
        use mettail_languages::calculator::Int;
        mettail_runtime::clear_var_cache();
        let result = Int::parse("2 ^ 3 ^ 2").expect("should parse");
        assert_eq!(result.eval(), 512, "^ should be right-associative");
    }

    #[test]
    fn long_chain_addition() {
        calc_normal_form("1 + 2 + 3 + 4 + 5", "15");
    }
}
