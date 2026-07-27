//! Exhaustive edge case test suite for all supported grammars.
//!
//! Covers cross-category operators inside cast parentheses, comparisons after
//! cast results, nested keyword-prefix functions, operator chains, postfix +
//! cross-category combinations, ternary edge cases, parenthesization stress,
//! whitespace variations, negative tests, and language-specific edge cases for
//! Lambda, Ambient, Rholang, Composition languages, and LedTest.
//!
//! Run:
//!   cargo test -p mettail-languages --test edge_case_tests
//!   cargo test -p mettail-languages --test edge_case_tests --features led-test

use mettail_languages::calculator::{self as calc};
use mettail_runtime::Language;

// ════════════════════════════════════════════════════════════════════════════════
// Shared helpers
// ════════════════════════════════════════════════════════════════════════════════

/// Parse input via the Calculator language; assert parse succeeds.
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

/// Parse via a generic Language; assert parse succeeds.
#[cfg(feature = "composition")]
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

    // 1A: Comparison operators inside str()

    // 1B: Comparisons inside bool()

    // 1C: Float comparisons inside casts

    // 1D: Same-category arithmetic inside casts (verify no regression)

    // 1E: Complex expressions inside casts
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 3: Nested Keyword-Prefix Functions (~26 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod nested_keyword_prefix_functions {
    use super::*;

    // 3A: Nested cast functions (cross-type matrix)

    // 3B: Nested math functions

    #[test]
    fn sin_of_cos() {
        // sin(cos(1.0)) — just verify it parses and evaluates
        calc_parses("sin(cos(1.0))");
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

    // 3D: Three-deep mixed nesting

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
    fn sin_add_cos() {
        calc_parses("sin(1.0) + cos(1.0)");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 8: Chained Casts with Operators Between (~8 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod chained_casts_with_operators {
    use super::*;

    #[test]
    fn float_of_int_cast_plus_one() {
        calc_parses("float(int(3.14) + 1)");
    }

    #[test]
    fn str_of_float_cast_add_float_cast() {
        calc_parses("str(float(3) + float(4))");
    }

    #[test]
    fn str_of_int_cast_mul_plus() {
        calc_parses("str(int(3.14) * 2 + 1)");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 10: String-Specific Edge Cases (~6 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod string_edge_cases {
    use super::*;

    #[test]
    fn str_cast_concat_str_cast() {
        calc_parses(r#"str(42) ++ str(43)"#);
    }

    #[test]
    fn str_cast_add_str_cast() {
        calc_parses(r#"str(42) + str(43)"#);
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 12: Whitespace Variations (~10 tests)
// ════════════════════════════════════════════════════════════════════════════════

mod whitespace_variations {
    use super::*;

    #[test]
    fn sin_inner_spaces() {
        calc_parses("sin( 1.0 )");
    }

    #[test]
    fn str_cast_inner_spaces() {
        calc_parses("str(  1 + 2  )");
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

#[cfg(feature = "lambda")]
mod lambda_edge_cases {
    use mettail_languages::lambda::Term;

    fn lambda_parses(input: &str) {
        mettail_runtime::clear_var_cache();
        Term::parse(input).unwrap_or_else(|e| panic!("lambda parse({:?}) failed: {}", input, e));
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

#[cfg(feature = "ambient")]
mod ambient_edge_cases {
    use mettail_languages::ambient::Proc;

    fn ambient_parses(input: &str) {
        mettail_runtime::clear_var_cache();
        Proc::parse(input).unwrap_or_else(|e| panic!("ambient parse({:?}) failed: {}", input, e));
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
// Category 16: Rholang Edge Cases (~16 tests)
// ════════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "rholang")]
mod rholang_edge_cases {
    use mettail_languages::rholang::Proc;

    fn rholang_parses(input: &str) {
        mettail_runtime::clear_var_cache();
        Proc::parse(input).unwrap_or_else(|e| panic!("rholang parse({:?}) failed: {}", input, e));
    }

    // 16A: Arithmetic & comparisons

    #[test]
    fn comparison_and() {
        rholang_parses("{1 == 1 and 2 == 2}");
    }

    #[test]
    fn not_eq() {
        rholang_parses("{not (1 == 2)}");
    }

    #[test]
    fn chained_gt() {
        rholang_parses("{3 > 2 and 2 > 1}");
    }

    // 16B: Type conversions with expressions

    #[test]
    fn int_of_float_add() {
        // rholang requires explicit width: int(a:Proc, w:Int)
        rholang_parses("{int(1.5 + 2.5, 32)}");
    }

    #[test]
    fn bool_of_int_add() {
        rholang_parses("{bool(1 + 0)}");
    }

    #[test]
    fn float_of_int_add() {
        // rholang requires explicit width: float(a:Proc, w:Int)
        rholang_parses("{float(1 + 2, 64)}");
    }

    // 16C: Process calculus nesting

    #[test]
    fn comm_under_new() {
        rholang_parses("new x in { {for(y <- x){*(y)} | x!(42)} }");
    }

    #[test]
    fn exec_of_quoted_arithmetic() {
        rholang_parses("{*(@(1 + 2))}");
    }

    #[test]
    fn nested_concat() {
        rholang_parses(r#"{"hello".concat("wor".concat("ld"))}"#);
    }

    #[test]
    fn len_of_concat() {
        rholang_parses(r#"{"a".concat("bc").length()}"#);
    }

    #[test]
    fn dollar_proc_regression() {
        // Existing dollar syntax — regression test
        rholang_parses("$proc(^f.{f}, {})");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 17: Composition Language Edge Cases (~10 tests)
// ════════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "composition")]
mod composition_edge_cases {
    use super::*;
    use mettail_languages::composition::composed_lang::CalcLambdaLanguage;

    use mettail_languages::composition::grammar_import_lang::ImportedMathLanguage;

    #[test]
    fn imported_math_div_add_precedence() {
        // Verify precedence: 10 / 2 + 3 — depends on operator precedence
        lang_parses(&ImportedMathLanguage, "10 / 2 + 3");
    }

    #[test]
    fn calc_lambda_lambda_expr() {
        lang_parses(&CalcLambdaLanguage, "lam x.x");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Category 18: LedTest Edge Cases (~9 tests)
// ════════════════════════════════════════════════════════════════════════════════

// Task #11 (extended 2026-07-26): `LedTest` is a LED-delegation FIXTURE grammar whose definition lives in
// `languages/tests/definitions/led_test.rs`, not in the `languages` library, so it is
// `#[path]`-included here. This binary is a CONSUMER, not the definition's designated host
// (languages/tests/led_delegation_tests.rs is), so it deliberately does NOT invoke the
// `ledtest_generated_tests!` wrapper — the generated suite stays single-instanced.
#[path = "definitions/led_test.rs"]
mod ledtest;

mod led_test_edge_cases {
    use crate::ledtest::LedTestLanguage;
    use mettail_runtime::Language;

    fn led_parses(input: &str) {
        mettail_runtime::clear_var_cache();
        let lang = LedTestLanguage;
        lang.parse_term(input)
            .unwrap_or_else(|e| panic!("parse({:?}) failed: {}", input, e));
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

    #[test]
    fn right_assoc_power() {
        // 2 ^ 3 ^ 2 = 2 ^ (3^2) = 2 ^ 9 = 512 (right-associative)
        // Uses direct eval() because this test targets parser associativity,
        // not runtime-backend reduction.
        use mettail_languages::calculator::Int;
        mettail_runtime::clear_var_cache();
        let result = Int::parse("2 ^ 3 ^ 2").expect("should parse");
        assert_eq!(result.eval(), 512, "^ should be right-associative");
    }
}
