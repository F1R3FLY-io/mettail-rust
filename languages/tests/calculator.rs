use mettail_languages::calculator::{self as calc};
use mettail_runtime::Language;

/// Parse input, run Ascent, return the single normal form's display. Panics if expected is not among normal form displays.
fn calc_normal_form(input: &str, expected_display: &str) {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term(input).expect("parse");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    let displays: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        displays.contains(&expected_display.to_string()),
        "expected normal form {:?} for {:?}, got: {:?}",
        expected_display,
        input,
        displays
    );
}

// --- Int: simple and precedence ---

#[test]
fn test_int_literal() {
    calc_normal_form("42", "42");
}

#[test]
fn test_int_add() {
    calc_normal_form("3 + 5", "8");
}

#[test]
fn test_int_sub() {
    calc_normal_form("10 - 4", "6");
    calc_normal_form("5 - -3", "8");
}

#[test]
fn test_int_left_associativity() {
    calc_normal_form("10 + 5 - 3 + 2", "14");
}

#[test]
fn test_int_unary_minus() {
    calc_normal_form("-7", "-7");
}

#[test]
fn test_int_power() {
    calc_normal_form("2 ^ 3", "8");
    calc_normal_form("5 ^ 0", "1");
}

#[test]
fn test_int_custom_op() {
    calc_normal_form("1 ~ 2", "8");
}

// --- Int: corner ---

#[test]
fn test_int_zero() {
    calc_normal_form("0", "0");
}

#[test]
fn test_int_neg_zero() {
    calc_normal_form("-0", "0");
}

#[test]
fn test_int_len_string() {
    calc_normal_form(r#"|"abc"|"#, "3");
}

// --- Float: simple and corner ---

#[test]
fn test_float_literal_0_5() {
    calc_normal_form("0.5", "0.5");
}

#[test]
fn test_float_literal_0_0() {
    calc_normal_form("0.0", "0.0");
}

#[test]
fn test_float_add() {
    calc_normal_form("1.5 + 2.5", "4.0");
}

#[test]
fn test_float_scientific() {
    calc_normal_form("1.0E2", "100.0");
    calc_normal_form("2.5E-1", "0.25");
    calc_normal_form("1.0e2", "100.0");
    calc_normal_form("2.5E+3", "2500.0");
    calc_normal_form("1.23e10", "12300000000.0");
}

// --- Bool ---

#[test]
fn test_bool_literals() {
    calc_normal_form("true", "true");
    calc_normal_form("false", "false");
}

#[test]
fn test_bool_not() {
    calc_normal_form("not true", "false");
    calc_normal_form("not false", "true");
}

#[test]
fn test_bool_eq_int() {
    calc_normal_form("1 == 1", "true");
    calc_normal_form("1 == 2", "false");
}

#[test]
fn test_bool_eq_float() {
    calc_normal_form("1.0 == 1.0", "true");
}

#[test]
fn test_bool_and() {
    calc_normal_form("true and false", "false");
    calc_normal_form("true and true", "true");
}

// --- Str ---

#[test]
fn test_str_empty() {
    calc_normal_form(r#""""#, r#""""#);
}

#[test]
fn test_str_literal() {
    calc_normal_form(r#""a""#, r#""a""#);
}

#[test]
fn test_str_concat() {
    calc_normal_form(r#""a" + "b""#, r#""ab""#);
}

#[test]
fn test_str_add() {
    calc_normal_form(r#""x" + "y""#, r#""xy""#);
}

// --- Environment ---

#[test]
fn test_env_add_and_list() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let term = lang.parse_term_for_env("7").expect("parse 7");
    lang.add_to_env(env.as_mut(), "x", term.as_ref())
        .expect("add x");
    let bindings = lang.list_env(env.as_ref());
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "x");
    assert_eq!(bindings[0].1, "7");
}

#[test]
fn test_env_substitute_and_exec() {
    // "a + b" is Ambiguous across Float/Int/Str (all have '+' operator). Float env values
    // ensure the Float alternative progresses during substitution (Stage B resolution).
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    for (name, src) in [("a", "1.0"), ("b", "2.0")] {
        let term = lang.parse_term_for_env(src).expect(src);
        lang.add_to_env(env.as_mut(), name, term.as_ref())
            .expect(name);
    }
    let term = lang.parse_term_for_env("a + b").expect("parse a + b");
    let substituted = lang
        .substitute_env(term.as_ref(), env.as_ref())
        .expect("substitute_env");
    let results = lang.run_ascent(substituted.as_ref()).expect("run_ascent");
    let normal = results.normal_forms();
    let displays: Vec<&str> = normal.iter().map(|nf| nf.display.as_str()).collect();
    assert!(displays.contains(&"3.0"), "expected normal form \"3.0\" among {:?}", displays);
}

#[test]
fn test_env_remove_and_clear() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let t1 = lang.parse_term_for_env("1").expect("parse");
    let t2 = lang.parse_term_for_env("2").expect("parse");
    lang.add_to_env(env.as_mut(), "a", t1.as_ref())
        .expect("add a");
    lang.add_to_env(env.as_mut(), "b", t2.as_ref())
        .expect("add b");
    assert_eq!(lang.list_env(env.as_ref()).len(), 2);
    lang.remove_from_env(env.as_mut(), "a").expect("remove a");
    assert_eq!(lang.list_env(env.as_ref()).len(), 1);
    lang.clear_env(env.as_mut());
    assert!(lang.is_env_empty(env.as_ref()));
}

// --- Float literal parsing ---

/// Float support: parse float literal and check canonical wrapper (Eq/Hash/Ord via CanonicalFloat64).
#[test]
fn test_float_literal_parse() {
    mettail_runtime::clear_var_cache();
    let term = calc::Float::parse("1.5").expect("parse 1.5");
    if let calc::Float::FloatLit(v) = term {
        assert!((v.get() - 1.5).abs() < 1e-10);
    } else {
        panic!("expected FloatLit, got {:?}", term);
    }
}

/// REPL-style: "1.0" parses as Float (parser order Float-before-Int) via full language parse.
#[test]
fn test_exec_float_1_0() {
    mettail_runtime::clear_var_cache();
    let term = calc::CalculatorLanguage::parse("1.0").expect("parse 1.0");
    if let calc::CalculatorTermInner::Float(inner) = &term.0 {
        if let calc::Float::FloatLit(v) = inner {
            assert!((v.get() - 1.0).abs() < 1e-10, "expected 1.0, got {}", v.get());
        } else {
            panic!("expected FloatLit, got {:?}", inner);
        }
    } else {
        panic!("expected Float variant, got {:?}", term.0);
    }
}

// --- PraTTaIL-specific: unary prefix, right-assoc, postfix, ternary ---

use mettail_languages::calculator::Int;

#[test]
fn test_unary_minus_literal() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-3").expect("should parse -3");
    assert_eq!(result.eval(), -3);
}

#[test]
fn test_unary_minus_with_addition() {
    mettail_runtime::clear_var_cache();
    // Should parse as (-3) + 5 = 2, NOT -(3 + 5) = -8
    let result = Int::parse("-3 + 5").expect("should parse -3 + 5");
    assert_eq!(result.eval(), 2, "unary minus should bind tighter than addition");
}

#[test]
fn test_unary_minus_with_subtraction() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-3 - 5").expect("should parse -3 - 5");
    assert_eq!(result.eval(), -8, "unary minus should bind tighter than subtraction");
}

#[test]
fn test_binary_minus_with_unary() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("3 - -5").expect("should parse 3 - -5");
    assert_eq!(result.eval(), 8, "binary minus then unary minus in prefix position");
}

#[test]
fn test_double_negation() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("--3").expect("should parse --3");
    assert_eq!(result.eval(), 3, "double negation should cancel out");
}

#[test]
fn test_unary_minus_with_exponentiation() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-3 ^ 2").expect("should parse -3 ^ 2");
    assert_eq!(result.eval(), 9, "unary minus should bind tighter than exponentiation");
}

#[test]
fn test_unary_minus_variable() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-x");
    assert!(result.is_ok(), "should parse -x as Neg(IVar(x))");
}

#[test]
fn test_not_binds_tight() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();
    let result = Bool::parse("not true and false").expect("should parse not true and false");
    assert_eq!(result.eval(), false, "not should bind tighter than and");
}

// ── Right-associativity tests ──

#[test]
fn test_pow_right_associativity() {
    mettail_runtime::clear_var_cache();
    // 2 ^ 3 ^ 2 should parse as 2 ^ (3 ^ 2) = 2 ^ 9 = 512
    let result = Int::parse("2 ^ 3 ^ 2").expect("should parse");
    assert_eq!(result.eval(), 512, "^ should be right-associative");
}

#[test]
fn test_pow_simple() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("2 ^ 10").expect("should parse");
    assert_eq!(result.eval(), 1024, "2 ^ 10 = 1024");
}

// ── Postfix operator tests ──

#[test]
fn test_factorial_simple() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("5!").expect("should parse 5!");
    assert_eq!(result.eval(), 120, "5! = 120");
}

#[test]
fn test_factorial_zero() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("0!").expect("should parse 0!");
    assert_eq!(result.eval(), 1, "0! = 1");
}

#[test]
fn test_factorial_with_addition() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("3 + 5!").expect("should parse 3 + 5!");
    assert_eq!(result.eval(), 123, "postfix ! should bind tighter than +");
}

#[test]
fn test_factorial_with_negation() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-5!").expect("should parse -5!");
    assert_eq!(result.eval(), -120, "postfix ! should bind tighter than unary -");
}

#[test]
fn test_factorial_with_parentheses() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("(3 + 2)!").expect("should parse (3 + 2)!");
    assert_eq!(result.eval(), 120, "(3 + 2)! = 5! = 120");
}

#[test]
fn test_factorial_precedence_over_pow() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("3! ^ 2").expect("should parse 3! ^ 2");
    assert_eq!(result.eval(), 36, "3! ^ 2 = 6^2 = 36");
}

// ── Mixfix operator tests (ternary) ──

#[test]
fn test_ternary_true_branch() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("1 ? 42 : 0").expect("should parse ternary");
    assert_eq!(result.eval(), 42, "nonzero condition selects then-branch");
}

#[test]
fn test_ternary_false_branch() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("0 ? 42 : 99").expect("should parse ternary");
    assert_eq!(result.eval(), 99, "zero condition selects else-branch");
}

#[test]
fn test_ternary_negative_condition() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-1 ? 10 : 20").expect("should parse ternary with negative condition");
    assert_eq!(result.eval(), 10, "negative nonzero condition selects then-branch");
}

#[test]
fn test_ternary_with_expressions() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("(1 + 0) ? (3 + 4) : (10 - 5)").expect("should parse");
    assert_eq!(result.eval(), 7, "ternary with subexpressions");
}

#[test]
fn test_ternary_right_associativity() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("1 ? 2 : 1 ? 3 : 4").expect("should parse nested ternary");
    assert_eq!(result.eval(), 2, "first condition is nonzero, selects 2");
}

#[test]
fn test_ternary_nested_else() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("0 ? 2 : 1 ? 3 : 4").expect("should parse nested ternary else");
    assert_eq!(result.eval(), 3, "fall through to nested ternary");
}

#[test]
fn test_ternary_lowest_precedence() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("1 + 0 ? 3 + 4 : 5").expect("should parse");
    assert_eq!(result.eval(), 7, "ternary has lower precedence than +");
}

#[test]
fn test_ternary_display_roundtrip() {
    mettail_runtime::clear_var_cache();
    let term = Int::parse("1 ? 2 : 3").expect("should parse");
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let reparsed = Int::parse(&displayed).expect("should reparse displayed ternary");
    assert_eq!(term, reparsed, "display roundtrip should preserve structure");
}

// ── NFA-style multi-category parse (Ambiguous) tests ──

#[test]
fn test_env_int_substitute_and_exec() {
    // Variables parsed ambiguously across Float/Int, but env has Int bindings.
    // After substitution, only the Int alternative makes progress → disambiguation collapses to Int.
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    for (name, src) in [("a", "1"), ("b", "2")] {
        let term = lang.parse_term_for_env(src).expect(src);
        lang.add_to_env(env.as_mut(), name, term.as_ref())
            .expect(name);
    }
    let term = lang.parse_term_for_env("a + b").expect("parse a + b");
    let substituted = lang
        .substitute_env(term.as_ref(), env.as_ref())
        .expect("substitute_env");
    let results = lang.run_ascent(substituted.as_ref()).expect("run_ascent");
    let displays: Vec<&str> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.as_str())
        .collect();
    assert!(displays.contains(&"3"), "expected \"3\" among {:?}", displays);
}

#[test]
fn test_ambiguous_parse_variable_expr() {
    // "a + b" should parse successfully (ambiguous across Float/Int).
    mettail_runtime::clear_var_cache();
    let result = calc::CalculatorLanguage::parse("a + b");
    assert!(result.is_ok(), "ambiguous expression should parse: {:?}", result);
    // Display should show the expression regardless of internal ambiguity
    assert_eq!(format!("{}", result.expect("already checked")), "a + b");
}

#[test]
fn test_unambiguous_int_literal() {
    // "42" should parse unambiguously as Int (Float parser doesn't accept Integer tokens).
    mettail_runtime::clear_var_cache();
    let result = calc::CalculatorLanguage::parse("42").expect("parse 42");
    if let calc::CalculatorTermInner::Int(inner) = &result.0 {
        assert_eq!(inner.eval(), 42);
    } else {
        panic!("expected Int variant for '42', got {:?}", result.0);
    }
}

#[test]
fn test_unambiguous_float_literal() {
    // "1.5" should parse unambiguously as Float (Int parser doesn't accept Float tokens).
    mettail_runtime::clear_var_cache();
    let result = calc::CalculatorLanguage::parse("1.5").expect("parse 1.5");
    if let calc::CalculatorTermInner::Float(_) = &result.0 {
        // ok
    } else {
        panic!("expected Float variant for '1.5', got {:?}", result.0);
    }
}

/// `infer_var_types` should find variable `x` in `x + 1` for multi-type Calculator
/// (previously stubbed to return empty Vec for multi-type languages).
#[test]
fn test_calculator_infer_var_types() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("x + 1").expect("parse x + 1");
    let var_types = lang.infer_var_types(term.as_ref());
    let x_info = var_types.iter().find(|v| v.name == "x");
    assert!(x_info.is_some(), "x should be found in var types, got: {:?}", var_types);
}

/// `infer_var_type` should find variable `x` by name for multi-type Calculator
/// (previously stubbed to return None for multi-type languages).
#[test]
fn test_calculator_infer_var_type() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("x + 1").expect("parse x + 1");
    let x_type = lang.infer_var_type(term.as_ref(), "x");
    assert!(x_type.is_some(), "x should have inferred type");
}

// ── Bug 2: All comparison operators (not just ==) ──

#[test]
fn test_gt_int() {
    calc_normal_form("3 > 1", "true");
    calc_normal_form("1 > 3", "false");
}

#[test]
fn test_lt_int() {
    calc_normal_form("1 < 3", "true");
    calc_normal_form("3 < 1", "false");
}

#[test]
fn test_lteq_int() {
    calc_normal_form("3 <= 3", "true");
    calc_normal_form("1 <= 3", "true");
    calc_normal_form("3 <= 1", "false");
}

#[test]
fn test_gteq_int() {
    calc_normal_form("3 >= 3", "true");
    calc_normal_form("3 >= 1", "true");
    calc_normal_form("1 >= 3", "false");
}

#[test]
fn test_ne_int() {
    calc_normal_form("3 != 4", "true");
    calc_normal_form("3 != 3", "false");
}

#[test]
fn test_gt_float() {
    calc_normal_form("3.0 > 1.0", "true");
    calc_normal_form("1.0 > 3.0", "false");
}

#[test]
fn test_eq_str() {
    calc_normal_form(r#""a" == "a""#, "true");
    calc_normal_form(r#""a" == "b""#, "false");
}

// ── Bug 1: Parenthesized cross-category expressions ──

#[test]
fn test_parenthesized_eq_int() {
    calc_normal_form("(3 == 3)", "true");
    calc_normal_form("(1 == 2)", "false");
}

#[test]
fn test_parenthesized_gt_int() {
    calc_normal_form("(3 > 1)", "true");
    calc_normal_form("(1 > 3)", "false");
}

#[test]
fn test_parenthesized_lt_int() {
    calc_normal_form("(1 < 3)", "true");
}

#[test]
fn test_parenthesized_bool_same() {
    calc_normal_form("(true and false)", "false");
    calc_normal_form("(not true)", "false");
}

#[test]
fn test_nested_paren_cross() {
    calc_normal_form("((3 == 3))", "true");
}

#[test]
fn test_paren_cross_in_bool_expr() {
    calc_normal_form("(1 == 1) and (2 == 2)", "true");
    calc_normal_form("(1 == 2) and (2 == 2)", "false");
}

#[test]
fn test_paren_int_still_works() {
    calc_normal_form("(3 + 2)", "5");
    calc_normal_form("(3 + 2)!", "120");
}

// ── Bug 1+2 combined: parenthesized non-equality comparisons ──

#[test]
fn test_paren_gt_int() {
    calc_normal_form("(3 > 1)", "true");
}

#[test]
fn test_paren_ne_int() {
    calc_normal_form("(3 != 4)", "true");
}

// ── REPL-style exec scenario ──

#[test]
fn test_exec_paren_cross_category() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("(3 == 3)").expect("parse (3 == 3)");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    let displays: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        displays.contains(&"true".to_string()),
        "expected normal form \"true\" for \"(3 == 3)\", got: {:?}",
        displays
    );
}

/// Bare variable `a` in an all-native language (Calculator) should infer as `Int`
/// (the primary category). Calculator has no non-native categories, so all parsers
/// are tried unconditionally. The Ambiguous result gets the primary category preference
/// from `infer_term_type`.
#[test]
fn test_bare_variable_type_is_int() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("a").expect("parse 'a'");
    let term_type = lang.infer_term_type(term.as_ref());
    // Calculator is all-native, so "a" is Ambiguous across all categories;
    // type should show primary (Int)
    assert_eq!(format!("{}", term_type), "Int");
}

// ── NFA disambiguation: nested casts (duplicate-token prefix arms) ──

#[test]
fn test_float_float_nested() {
    calc_normal_form("float(float(3))", "3.0");
}

#[test]
fn test_int_int_nested() {
    calc_normal_form("int(int(3))", "3");
}

#[test]
fn test_float_int_roundtrip() {
    calc_normal_form("float(int(3.14))", "3.0");
}

#[test]
fn test_int_float_roundtrip() {
    calc_normal_form("int(float(3))", "3");
}

#[test]
fn test_all_to_float() {
    calc_normal_form("float(3)", "3.0");
    calc_normal_form("float(true)", "1.0");
    calc_normal_form("float(3.0)", "3.0");
}

#[test]
fn test_all_to_int() {
    calc_normal_form("int(3.14)", "3");
    calc_normal_form("int(true)", "1");
    calc_normal_form("int(3)", "3");
}

#[test]
fn test_all_to_str() {
    calc_normal_form("str(3)", r#""3""#);
    calc_normal_form("str(3.14)", r#""3.14""#);
    calc_normal_form("str(true)", r#""true""#);
}

#[test]
fn test_all_to_bool() {
    calc_normal_form("bool(1)", "true");
    calc_normal_form("bool(0)", "false");
    calc_normal_form("bool(3.14)", "true");
    calc_normal_form("bool(true)", "true");
}

#[test]
fn test_float_cast_in_expr() {
    calc_normal_form("float(3) + 1.0", "4.0");
}

#[test]
fn test_int_cast_in_expr() {
    calc_normal_form("int(3.14) * 2", "6");
}

// ── NFA spillover + forced-prefix replay disambiguation tests ──

/// `float(x)` where x is bound to Bool(true) → NFA spillover produces multiple
/// alternatives (IntToFloat, BoolToFloat, StrToFloat, FloatId). After env
/// substitution, BoolToFloat(Bool(true)) becomes ground while others remain
/// variables → from_alternatives picks BoolToFloat. The result is `1.0`.
#[test]
fn test_nfa_spillover_float_bool_var() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let bool_term = lang.parse_term_for_env("true").expect("parse true");
    lang.add_to_env(env.as_mut(), "x", bool_term.as_ref())
        .expect("add x");
    let term = lang.parse_term_for_env("float(x)").expect("parse float(x)");
    let substituted = lang
        .substitute_env(term.as_ref(), env.as_ref())
        .expect("substitute_env");
    let results = lang.run_ascent(substituted.as_ref()).expect("run_ascent");
    let displays: Vec<&str> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.as_str())
        .collect();
    assert!(
        displays.contains(&"1.0"),
        "expected \"1.0\" for float(x) with x=true, got: {:?}",
        displays
    );
}

/// `float(x) + 1.0` where x is Bool(true) → forced-prefix replay runs the
/// full parser (prefix + infix loop), so the BoolToFloat alternative gets
/// wrapped in FloatAdd(BoolToFloat(Bool(true)), FloatLit(1.0)).
/// After env substitution + Ascent: `1.0 + 1.0 = 2.0`.
#[test]
fn test_nfa_spillover_float_bool_var_in_expr() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let bool_term = lang.parse_term_for_env("true").expect("parse true");
    lang.add_to_env(env.as_mut(), "x", bool_term.as_ref())
        .expect("add x");
    let term = lang
        .parse_term_for_env("float(x) + 1.0")
        .expect("parse float(x) + 1.0");
    let substituted = lang
        .substitute_env(term.as_ref(), env.as_ref())
        .expect("substitute_env");
    let results = lang.run_ascent(substituted.as_ref()).expect("run_ascent");
    let displays: Vec<&str> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.as_str())
        .collect();
    assert!(
        displays.contains(&"2.0"),
        "expected \"2.0\" for float(x) + 1.0 with x=true, got: {:?}",
        displays
    );
}

/// `float(x)` where x is bound to Int(42) → IntToFloat(42) → 42.0
#[test]
fn test_nfa_spillover_float_int_var() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let int_term = lang.parse_term_for_env("42").expect("parse 42");
    lang.add_to_env(env.as_mut(), "x", int_term.as_ref())
        .expect("add x");
    let term = lang.parse_term_for_env("float(x)").expect("parse float(x)");
    let substituted = lang
        .substitute_env(term.as_ref(), env.as_ref())
        .expect("substitute_env");
    let results = lang.run_ascent(substituted.as_ref()).expect("run_ascent");
    let displays: Vec<&str> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.as_str())
        .collect();
    assert!(
        displays.contains(&"42.0"),
        "expected \"42.0\" for float(x) with x=42, got: {:?}",
        displays
    );
}

/// `int(x)` where x is bound to Float(3.14) → FloatToInt(3.14) → 3
#[test]
fn test_nfa_spillover_int_float_var() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let float_term = lang.parse_term_for_env("3.14").expect("parse 3.14");
    lang.add_to_env(env.as_mut(), "x", float_term.as_ref())
        .expect("add x");
    let term = lang.parse_term_for_env("int(x)").expect("parse int(x)");
    let substituted = lang
        .substitute_env(term.as_ref(), env.as_ref())
        .expect("substitute_env");
    let results = lang.run_ascent(substituted.as_ref()).expect("run_ascent");
    let displays: Vec<&str> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.as_str())
        .collect();
    assert!(
        displays.contains(&"3"),
        "expected \"3\" for int(x) with x=3.14, got: {:?}",
        displays
    );
}

/// Unambiguous `float(3)` — the Int literal 3 matches IntToFloat only.
/// Verify no regression (this already worked, confirms zero-spillover path).
#[test]
fn test_nfa_spillover_unambiguous_float_int_literal() {
    calc_normal_form("float(3)", "3.0");
}

/// Unambiguous `float(3) + 1.0` — IntToFloat in expression context.
/// Verify no regression.
#[test]
fn test_nfa_spillover_unambiguous_float_int_literal_in_expr() {
    calc_normal_form("float(3) + 1.0", "4.0");
}

// ── Bug B: Ambiguous dispatch must try ALL operators, not just first ──
//
// When a FIRST token (e.g. Ident) is ambiguous between the target category
// (Bool) and multiple source categories (Int, Float, Str, Bool), ALL
// cross-category operators sharing that FIRST token must be tried. Previously
// only the first operator (by WFST weight) was emitted, so `x >= 1` failed
// while `x == 1` worked.

/// Variable-operand comparisons: Ident tokens hit the ambiguous dispatch path.
/// These test that ALL comparison operators are tried (not just ==).
#[test]
fn test_ambiguous_dispatch_gteq_int() {
    // x >= 1 was the motivating failure — must parse via GtEqInt
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x >= 1");
    assert!(result.is_ok(), "x >= 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_gt_int() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x > 1");
    assert!(result.is_ok(), "x > 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_lt_int() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x < 1");
    assert!(result.is_ok(), "x < 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_lteq_int() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x <= 1");
    assert!(result.is_ok(), "x <= 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_ne_int() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x != 1");
    assert!(result.is_ok(), "x != 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_eq_int_regression() {
    // x == 1 should still work (regression check — was working before)
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x == 1");
    assert!(result.is_ok(), "x == 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_eq_ident_both_sides() {
    // Both sides are Ident (ambiguous)
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x == y");
    assert!(result.is_ok(), "x == y should parse: {:?}", result);
}

/// Parenthesized variable comparisons go through the LParen grouping path
/// which re-enters the dispatch.
#[test]
fn test_ambiguous_dispatch_paren_gteq() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("(x >= 1)");
    assert!(result.is_ok(), "(x >= 1) should parse: {:?}", result);
}

/// Full end-to-end: x >= 1 with x bound to 3 → true
#[test]
fn test_ambiguous_dispatch_gteq_env() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let val = lang.parse_term_for_env("3").expect("parse 3");
    lang.add_to_env(env.as_mut(), "x", val.as_ref()).expect("add x");
    let term = lang.parse_term_for_env("x >= 1").expect("parse x >= 1");
    let substituted = lang.substitute_env(term.as_ref(), env.as_ref()).expect("sub");
    let results = lang.run_ascent(substituted.as_ref()).expect("ascent");
    let displays: Vec<String> = results.normal_forms().iter().map(|nf| nf.display.clone()).collect();
    assert!(
        displays.contains(&"true".to_string()),
        "expected \"true\" for x >= 1 with x=3, got: {:?}",
        displays
    );
}

/// Full end-to-end: x > 1 with x bound to 0 → false
#[test]
fn test_ambiguous_dispatch_gt_env() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let val = lang.parse_term_for_env("0").expect("parse 0");
    lang.add_to_env(env.as_mut(), "x", val.as_ref()).expect("add x");
    let term = lang.parse_term_for_env("x > 1").expect("parse x > 1");
    let substituted = lang.substitute_env(term.as_ref(), env.as_ref()).expect("sub");
    let results = lang.run_ascent(substituted.as_ref()).expect("ascent");
    let displays: Vec<String> = results.normal_forms().iter().map(|nf| nf.display.clone()).collect();
    assert!(
        displays.contains(&"false".to_string()),
        "expected \"false\" for x > 1 with x=0, got: {:?}",
        displays
    );
}

// --- BCG05 regression test ---

/// Regression test for BCG05 normalize-on-insert dedup epoch bug.
///
/// BCG05 uses thread-local HashSets to skip redundant normalize() calls.
/// Without epoch-based clearing, these HashSets persist across Ascent
/// evaluations within the same thread, causing the second (and subsequent)
/// evaluations to skip rule firings for previously-seen hashes, producing
/// incorrect (unreduced) results.
#[test]
fn test_bcg05_repeated_evaluation_produces_correct_results() {
    let lang = calc::CalculatorLanguage;

    // First evaluation: 3 + 5 = 8
    calc_normal_form("3 + 5", "8");

    // Second evaluation of the SAME expression on the SAME thread:
    // must still produce 8 (not the unreduced form).
    calc_normal_form("3 + 5", "8");

    // Third evaluation: different expression with overlapping substructure.
    calc_normal_form("3 + 5 + 2", "10");

    // Fourth: repeat the different expression — must still reduce correctly.
    calc_normal_form("3 + 5 + 2", "10");

    // Fifth: original expression again — still correct.
    let term = lang.parse_term("3 + 5").expect("parse");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    let displays: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        displays.contains(&"8".to_string()),
        "BCG05 regression: fifth evaluation of '3 + 5' should produce '8', got: {:?}",
        displays
    );
}

#[test]
fn debug_cross_category_cast() {
    use mettail_languages::calculator::Int;

    mettail_runtime::clear_var_cache();
    let r1 = Int::parse("int(0.5)");
    println!("int(0.5) -> {:?}", r1.as_ref().map(|p| format!("{}", p)));

    mettail_runtime::clear_var_cache();
    let r2 = Int::parse("int(true)");
    println!("int(true) -> {:?}", r2.as_ref().map(|p| format!("{}", p)));

    mettail_runtime::clear_var_cache();
    let r3 = Int::parse(r#"int(str("hello"))"#);
    println!(r#"int(str("hello")) -> {:?}"#, r3.as_ref().map(|p| format!("{}", p)));

    mettail_runtime::clear_var_cache();
    let r4 = Int::parse("int(b + 0.5)");
    println!("int(b + 0.5) -> {:?}", r4.as_ref().map(|p| format!("{}", p)));

    // Assert the simple cases work
    assert!(r1.is_ok(), "int(0.5) should parse: {:?}", r1.err());
    assert!(r2.is_ok(), "int(true) should parse: {:?}", r2.err());
    assert!(r3.is_ok(), r#"int(str("hello")) should parse: {:?}"#, r3.err());
}

#[test]
fn debug_complex_cast() {
    use mettail_languages::calculator::Int;

    // Simplified version of simulation failure
    mettail_runtime::clear_var_cache();
    let r = Int::parse("int(-0.5 ^ y)");
    println!("int(-0.5 ^ y) -> {:?}", r.as_ref().map(|p| format!("{}", p)).map_err(|e| &e[..100.min(e.len())]));

    mettail_runtime::clear_var_cache();
    let r2 = Int::parse("int(-0.5)");
    println!("int(-0.5) -> {:?}", r2.as_ref().map(|p| format!("{}", p)).map_err(|e| &e[..100.min(e.len())]));

    mettail_runtime::clear_var_cache();
    let r3 = Int::parse("int(0.5 ^ 2.0)");
    println!("int(0.5 ^ 2.0) -> {:?}", r3.as_ref().map(|p| format!("{}", p)).map_err(|e| &e[..100.min(e.len())]));
}

#[test]
fn debug_simulation_failures() {
    use mettail_languages::calculator::Int;

    let cases = vec![
        r#"int(b == str("mnxbf"))"#,
        "int(b >= true)",
        r#"int((z <= "wn") != (true < a))"#,
        "int((c > b) > 0.5)",
        "int(x >= y)",
    ];

    for input in &cases {
        mettail_runtime::clear_var_cache();
        match Int::parse(input) {
            Ok(p) => println!("{} -> OK: {}", input, p),
            Err(e) => println!("{} -> ERR: {}", input, &e[..e.len().min(80)]),
        }
    }
}

#[test]
fn debug_bool_parse_comparison() {
    use mettail_languages::calculator::Bool;
    
    let cases = vec![
        "b >= true",
        "x >= y", 
        "true >= false",
        "b == true",
    ];
    for input in &cases {
        mettail_runtime::clear_var_cache();
        match Bool::parse(input) {
            Ok(p) => println!("Bool::parse({}) -> OK: {}", input, p),
            Err(e) => println!("Bool::parse({}) -> ERR: {}", input, &e[..e.len().min(100)]),
        }
    }
}

#[test]
fn test_cross_category_infix_backtracking() {
    use mettail_languages::calculator::{Bool, Int};

    mettail_runtime::clear_var_cache();
    let r1 = Bool::parse("b >= true");
    assert!(r1.is_ok(), "b >= true should parse: {:?}", r1.err());

    mettail_runtime::clear_var_cache();
    let r2 = Bool::parse("b == true");
    assert!(r2.is_ok(), "b == true should parse: {:?}", r2.err());

    mettail_runtime::clear_var_cache();
    let r3 = Int::parse("int(b >= true)");
    assert!(r3.is_ok(), "int(b >= true) should parse: {:?}", r3.err());

    mettail_runtime::clear_var_cache();
    let r4 = Bool::parse("b == str(\"hello\")");
    assert!(r4.is_ok(), "b == str(\"hello\") should parse: {:?}", r4.err());
}

#[test]
fn debug_ne_operator() {
    use mettail_languages::calculator::{Bool, Int};

    let cases: Vec<(&str, Box<dyn Fn(&str) -> Result<String, String>>)> = vec![
        ("b != true", Box::new(|s| Bool::parse(s).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(80)].to_string()))),
        ("b != false", Box::new(|s| Bool::parse(s).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(80)].to_string()))),
        ("int(b != true)", Box::new(|s| Int::parse(s).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(80)].to_string()))),
        ("int(y != 0.5)", Box::new(|s| Int::parse(s).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(80)].to_string()))),
        ("int(y != -0.5)", Box::new(|s| Int::parse(s).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(80)].to_string()))),
        ("b < true", Box::new(|s| Bool::parse(s).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(80)].to_string()))),
        ("b > true", Box::new(|s| Bool::parse(s).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(80)].to_string()))),
        ("b <= true", Box::new(|s| Bool::parse(s).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(80)].to_string()))),
    ];
    for (input, parse_fn) in &cases {
        mettail_runtime::clear_var_cache();
        match parse_fn(input) {
            Ok(p) => println!("{} -> OK: {}", input, p),
            Err(e) => println!("{} -> ERR: {}", input, e),
        }
    }
}

#[test]
fn debug_chained_comparisons() {
    use mettail_languages::calculator::{Bool, Int};

    let cases: Vec<(&str, &str)> = vec![
        ("y != 0.5", "Bool"),
        ("y != 0.5 > y", "Bool"),  // chained: (y != 0.5) > y or y != (0.5 > y)?
        ("int(y != 0.5)", "Int"),
        ("int(y != 0.5 > y)", "Int"),
        ("int(y != 0.5 > y != 0.5)", "Int"),
    ];
    for (input, cat) in &cases {
        mettail_runtime::clear_var_cache();
        let result = if *cat == "Bool" {
            Bool::parse(input).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(100)].to_string())
        } else {
            Int::parse(input).map(|p| format!("{}", p)).map_err(|e| e[..e.len().min(100)].to_string())
        };
        match result {
            Ok(p) => println!("{} -> OK: {}", input, p),
            Err(e) => println!("{} -> ERR: {}", input, e),
        }
    }
}

#[test]
fn debug_display_chained_comparison() {
    use mettail_languages::calculator::{Bool, Int};

    // Construct GtBool(NeBool(BVar(x), BoolLit(true)), BVar(y))
    mettail_runtime::clear_var_cache();
    let x = mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("x")));
    let y_var = mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("y")));
    let inner = Bool::NeBool(Box::new(Bool::BVar(x.clone())), Box::new(Bool::BoolLit(true)));
    let outer = Bool::GtBool(Box::new(inner), Box::new(Bool::BVar(y_var)));
    let displayed = format!("{}", outer);
    println!("GtBool(NeBool(x, true), y) displays as: '{}'", displayed);

    // Try to parse it back
    mettail_runtime::clear_var_cache();
    match Bool::parse(&displayed) {
        Ok(p) => println!("  Parsed back: {}", p),
        Err(e) => println!("  Parse error: {}", &e[..e.len().min(100)]),
    }
}

#[test]
fn debug_int_chained_comparison() {
    use mettail_languages::calculator::Int;

    let cases = vec![
        "int(x != true > y)",
        "int(x != 0.5 > y)",
        "int(y != 0.5 > y != 0.5)",
    ];
    for input in &cases {
        mettail_runtime::clear_var_cache();
        match Int::parse(input) {
            Ok(p) => println!("{} -> OK: {}", input, p),
            Err(e) => println!("{} -> ERR: {}", input, &e[..e.len().min(80)]),
        }
    }
}

// --- Display roundtrip regression tests ---

#[test]
fn test_bool_display_roundtrip_nested_lt() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();

    // LtBool(LtBool(true,true), LtBool(true,true))
    let a = || Bool::BoolLit(true);
    let inner_left = Bool::LtBool(Box::new(a()), Box::new(a()));
    let inner_right = Bool::LtBool(Box::new(a()), Box::new(a()));
    let term = Bool::LtBool(Box::new(inner_left), Box::new(inner_right));

    let displayed = format!("{}", term);
    eprintln!("displayed: {:?}", displayed);

    let parsed = Bool::parse(&displayed).expect("parse should succeed");
    let re_displayed = format!("{}", parsed);
    eprintln!("re_displayed: {:?}", re_displayed);

    assert_eq!(displayed, re_displayed, "Display roundtrip should be idempotent");
}

#[test]
fn test_bool_display_roundtrip_deep_lt() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();

    // LtBool(LtBool(LtBool(true,true), LtBool(true,true)), LtBool(LtBool(true,true), LtBool(true,true)))
    let a = || Bool::BoolLit(true);
    let l1 = Bool::LtBool(Box::new(a()), Box::new(a()));
    let l2 = Bool::LtBool(Box::new(a()), Box::new(a()));
    let l3 = Bool::LtBool(Box::new(a()), Box::new(a()));
    let l4 = Bool::LtBool(Box::new(a()), Box::new(a()));
    let left = Bool::LtBool(Box::new(l1), Box::new(l2));
    let right = Bool::LtBool(Box::new(l3), Box::new(l4));
    let term = Bool::LtBool(Box::new(left), Box::new(right));

    let displayed = format!("{}", term);
    eprintln!("displayed: {:?}", displayed);

    let parsed = Bool::parse(&displayed).expect("parse should succeed");
    let re_displayed = format!("{}", parsed);
    eprintln!("re_displayed: {:?}", re_displayed);

    assert_eq!(displayed, re_displayed, "Display roundtrip should be idempotent");
}

#[test]
fn test_bool_display_roundtrip_deep_lt_vars() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();

    // Same tree but with variables instead of literals
    let a = || Bool::BVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
        mettail_runtime::get_or_create_var("a".to_string())
    )));
    let l1 = Bool::LtBool(Box::new(a()), Box::new(a()));
    let l2 = Bool::LtBool(Box::new(a()), Box::new(a()));
    let l3 = Bool::LtBool(Box::new(a()), Box::new(a()));
    let l4 = Bool::LtBool(Box::new(a()), Box::new(a()));
    let left = Bool::LtBool(Box::new(l1), Box::new(l2));
    let right = Bool::LtBool(Box::new(l3), Box::new(l4));
    let term = Bool::LtBool(Box::new(left), Box::new(right));

    let displayed = format!("{}", term);
    eprintln!("displayed: {:?}", displayed);

    let parsed = Bool::parse(&displayed).expect("parse should succeed");
    let re_displayed = format!("{}", parsed);
    eprintln!("re_displayed: {:?}", re_displayed);
    eprintln!("parsed debug: {:?}", parsed);

    assert_eq!(displayed, re_displayed, "Display roundtrip for LtBool with vars");
}

// --- Display roundtrip regression tests ---
// These test that cross-category dispatch backtracking and the cur_bp == 0
// guard produce stable canonical forms for same-category expressions.

#[test]
fn display_roundtrip_bool_xor_lt() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();
    // From proptest failure: Or(LtBool(Xor(c,c), a), ...)
    // Inside xor RHS (cur_bp > 0), cross-cat dispatch is blocked → same-cat LtBool
    let input = "(c xor c < a) or false";
    let parsed = Bool::parse(input).expect("parse should succeed");
    let displayed = format!("{}", parsed);
    let reparsed = Bool::parse(&displayed).expect("reparse should succeed");
    let redisplayed = format!("{}", reparsed);
    assert_eq!(displayed, redisplayed, "Canonical form should be stable for '{}'", input);
}

#[test]
fn display_roundtrip_bool_nested_not_lt() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();
    // From proptest failure: Not(LtBool(Not(c), c))
    let input = "not (not c < c)";
    let parsed = Bool::parse(input).expect("parse should succeed");
    let displayed = format!("{}", parsed);
    let reparsed = Bool::parse(&displayed).expect("reparse should succeed");
    let redisplayed = format!("{}", reparsed);
    assert_eq!(displayed, redisplayed, "Canonical form should be stable for '{}'", input);
}

#[test]
fn display_roundtrip_bool_mixed_lt_lteq() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();
    // From proptest failure: mixed < and <= operators
    let input = "not (not a < a <= c)";
    let parsed = Bool::parse(input).expect("parse should succeed");
    let displayed = format!("{}", parsed);
    let reparsed = Bool::parse(&displayed).expect("reparse should succeed");
    let redisplayed = format!("{}", reparsed);
    assert_eq!(displayed, redisplayed, "Canonical form should be stable for '{}'", input);
}

// --- Cross-category dispatch regression tests ---
// These test cases come from stochastic simulator failures where cross-category
// comparison operators inside int(...) casts failed to parse because the Bool
// parser's cross-cat dispatch had duplicate match arms for tokens shared across
// multiple source categories (e.g., Token::Minus in both Int and Float FIRST sets).

#[test]
fn parse_int_cross_cat_comparison_ne() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    // int(-N != b) requires Bool to dispatch Token::Minus to Int source
    for input in &[
        "int(-1 != 0)",
        "int(-1 != b)",
        "int(-543610622 != b)",
    ] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn parse_int_cross_cat_comparison_lt() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    for input in &[
        "int(-1 < 0)",
        "int(-1924974980 < x)",
    ] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn parse_int_cross_cat_comparison_le() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    for input in &[
        "int(-1 <= 0)",
        "int(-928988166 <= y)",
        "int(-928988166 <= y <= (-928988166 <= y))",
    ] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn parse_int_cross_cat_comparison_ge() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    for input in &[
        "int(-1 >= 0)",
        "int(-715541275 >= a)",
    ] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn parse_int_cross_cat_eq_with_modulo() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    // int(a == x % x): == is both Bool infix (EqBool) and cross-cat (EqInt).
    // The cross-cat dispatch must handle this without a peek-ahead blocking it.
    let result = Int::parse("int(a == x % x)");
    assert!(result.is_ok(), "Failed to parse 'int(a == x % x)': {:?}", result.err());
}

#[test]
fn parse_int_nested_cross_cat_str() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    // int(str(...)) requires Str → Int cast to exist or Bool to handle str(...)
    let input = "int(str(-1 <= a))";
    // This may or may not parse depending on grammar rules. If it fails, that's
    // acceptable — but it should not crash.
    let _ = Int::parse(input);
}

#[test]
fn parse_int_cross_cat_in_expression() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    // Cross-category comparison as operand of Int operators
    for input in &[
        "int(-1 != 0)!",          // postfix on cross-cat result
        "-1 ^ int(-1 != 0)",      // cross-cat in RHS of power
    ] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

// --- Stochastic simulator regression tests ---
// All 30 unique failing inputs collected from simulate_calculator runs.
// These are the AUTHORITATIVE regression suite for cross-category parsing bugs.
// Each input is tested for parse success (Ok) or graceful error (Err) — no panics.
// Inputs that SHOULD parse successfully use assert!(result.is_ok()).
// Inputs that are genuinely unparsable (grammar limitation) use let _ = result.

#[test]
fn trace_cross_cat_parse_steps() {
    use mettail_languages::calculator::{Bool, Int};

    let cases: &[(&str, &str)] = &[
        ("Bool", "c == -1"),
        ("Bool", "c == -1 <= -2"),
        ("Bool", "c > a"),
        ("Bool", r#"c > a ++ """#),
        ("Int",  "int(c == -1)"),
        ("Int",  "int(c == -1 <= -2)"),
        ("Int",  "int(c > a)"),
        ("Int",  r#"int(c > a ++ "")"#),
        ("Int",  "int(-1 != 0)"),
        ("Int",  "int(-a > c % x)"),
        ("Bool", r#"z != "lv" >= (false >= true)"#),
        ("Int",  r#"int(z != "lv" >= (false >= true))"#),
    ];
    for (cat, input) in cases {
        mettail_runtime::clear_var_cache();
        let result = match *cat {
            "Bool" => Bool::parse(input).map(|v| format!("{:?}", v)),
            "Int"  => Int::parse(input).map(|v| format!("{:?}", v)),
            _ => unreachable!(),
        };
        match &result {
            Ok(v) => eprintln!("[{}] '{}' => OK: {}", cat, input, &v[..v.len().min(120)]),
            Err(e) => eprintln!("[{}] '{}' => ERR: {}", cat, input, &e[..e.len().min(120)]),
        }
    }
    // No assertion — this test is purely diagnostic
}

#[test]
fn simulator_regression_original_6() {
    use mettail_languages::calculator::Int;
    // The original 6 failures from the user's first report.
    // All involve cross-category comparison operators inside int(...) casts.
    let must_parse = &[
        r#"int(-543610622 != b)"#,                    // int(NeInt(Neg, IVar))
        r#"int(-928988166 <= y <= (-928988166 <= y))"#, // chained cross-cat <=
        r#"int(-715541275 >= a)"#,                     // simplified: no postfix
        r#"int(-1924974980 < x)"#,                     // simplified: no tilde
        r#"int(-1364203178 != -724684863)"#,           // both operands negative
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_full_expressions() {
    use mettail_languages::calculator::Int;
    // Full expressions from the original report (with surrounding context).
    let must_parse = &[
        r#"int(-744428796) ^ int(c) ? y ~ int(-379296706) : int(-543610622 != b)"#,
        r#"-1313951767 ^ (-165227314 * x) - int(-1364203178 != -724684863)"#,
        r#"int(-715541275 >= a)!"#,
        r#"int(-1924974980 < x) ~ -|a|"#,
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_cross_cat_dispatch_chaining() {
    use mettail_languages::calculator::Int;
    // Failures caused by duplicate deterministic match arms in cross-cat dispatch.
    // Token::Minus shared by Int and Float FIRST sets → second arm was dead code.
    let must_parse = &[
        r#"int(-a > c % x)"#,                          // -a as cross-cat prefix
        r#"int(-y == y!)"#,                             // -y with postfix on RHS
        r#"int(c == -301055575 <= -1136349513)"#,       // chained comparisons
        r#"int(-220439700 > 1827376848 == c != -0.5)"#, // 3 chained operators
        r#"int(b >= 2039068204 <= b >= -2074699644)"#,  // 3 chained >= and <=
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_cross_cat_with_strings() {
    use mettail_languages::calculator::Int;
    // Comparisons involving string operands inside int(...).
    // Fixed by longest-match dispatch (Str source consumes ++ and string literals).
    let must_parse = &[
        r#"int(c > a ++ "")"#,                         // Str concat in comparison
        r#"int(z >= x ++ "")"#,                         // >= with Str concat
        r#"int(b == y ++ "")"#,                         // == with Str concat
        r#"int(x == a ++ "")"#,                         // == with Str concat
        r#"int(y < "edce" == y < "edce")"#,             // Str comparison chain
        r#"int(z > 1691216401 == a < "um")"#,           // mixed Int/Str comparisons
        r#"int(a >= "opnxjvm" < a >= "opnxjvm")"#,     // Str >= chain
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_cross_cat_with_parens() {
    use mettail_languages::calculator::Int;
    // Cross-category expressions with parenthesized sub-expressions.
    // Fixed by chain detection + implicit cast synthesis.
    let must_parse = &[
        r#"int((c > y) < c != 0.5)"#,                  // parenthesized LHS
        r#"int((1077498015 == x) > b != "")"#,          // parenthesized EqInt
        r#"int((-0.5 < 0.5) <= b != "hh")"#,           // Float comparison in parens
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_bool_prefix_tokens() {
    use mettail_languages::calculator::Int;
    // Expressions where Bool-only prefix tokens (true/false/bool(...)) appear
    // inside int(...). Fixed by implicit cast synthesis in deterministic arms
    // (e.g., Token::Minus → IntToBool, Token::StringLit → StrToBool).
    let must_parse = &[
        r#"int(false > b < -2080280922)"#,
        r#"int(false > a > z < "eoxyaib")"#,
        r#"int(true >= z < x <= "a")"#,
        r#"int(bool(a) < y <= 807406639)"#,
        r#"int(bool(x) >= c != -1798717939)"#,
        r#"int((c < true) <= c >= -562932638)"#,
        r#"int(y != true > x < "qua")"#,
        r#"int(y and b == y < "x")"#,
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_nested_casts() {
    use mettail_languages::calculator::Int;
    // Nested cast expressions. Fixed by implicit cast synthesis enabling
    // cross-category dispatch to chain through nested NFA alternatives.
    let must_parse = &[
        r#"int(str(-1633226738 <= a))"#,
        r#"int(str(-1 <= a))"#,
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_cross_cat_with_floats() {
    use mettail_languages::calculator::Int;
    // Cross-category expressions with float literals.
    // Fixed by chain detection + implicit cast synthesis (FloatToBool for 0.5).
    let must_parse = &[
        r#"int(y <= z < b <= 0.5)"#,                   // Float in comparison chain
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

// ─── Deep-tree try_eval tests (stack safety / PDA trampoline) ────────────────
//
// These tests verify that `try_eval` handles deeply-nested same-category trees
// without Rust-stack overflow. The work-stack PDA generated by the `language!`
// macro turns what would be O(tree-depth) call-stack frames into O(1) call-stack
// + O(tree-depth) heap-allocated work-stack frames.

#[test]
fn test_try_eval_deep_addint_10000() {
    use mettail_languages::calculator::Int;
    // Build AddInt(Lit(0), AddInt(Lit(1), ... AddInt(Lit(9999), Lit(10000)))).
    // A 10 000-deep right-skewed chain of `+`. Recursive try_eval would overflow
    // the default Rust stack; the PDA heap-allocates its work stack.
    let mut term = Int::NumLit(10_000);
    for i in (0..10_000).rev() {
        term = Int::AddInt(Box::new(Int::NumLit(i)), Box::new(term));
    }
    let v = term.try_eval();
    // Sum of 0..=10000 = 50_005_000 (within i32 range).
    assert_eq!(v, Some(50_005_000),
        "deep AddInt chain should evaluate without stack overflow");
}

#[test]
fn test_try_eval_deep_neg_10000() {
    use mettail_languages::calculator::Int;
    // 10 000 nested unary negations of Lit(1). Even number of negs → result is 1.
    let mut term = Int::NumLit(1);
    for _ in 0..10_000 {
        term = Int::Neg(Box::new(term));
    }
    let v = term.try_eval();
    assert_eq!(v, Some(1),
        "deep Neg chain should evaluate without stack overflow");
}

#[test]
fn test_try_eval_deep_fact_no_panic() {
    use mettail_languages::calculator::Int;
    // Factorial of 50 overflows i32. Calculator's Fact rule uses
    // `try_fold(..., checked_mul).unwrap_or(0)` so overflow returns 0, not panic.
    // The important property: no panic, no stack overflow.
    let term = Int::Fact(Box::new(Int::NumLit(50)));
    let _ = term.try_eval(); // Should not panic.
}

#[test]
fn test_try_eval_deep_mixed_ops_1000() {
    use mettail_languages::calculator::Int;
    // Alternating AddInt / MulInt / Neg at depth 1000. Tests that
    // interleaving different same-category reductions on the work stack
    // doesn't corrupt the value stack.
    let mut term = Int::NumLit(1);
    for i in 0..1000 {
        term = match i % 3 {
            0 => Int::AddInt(Box::new(term), Box::new(Int::NumLit(1))),  // +1
            1 => Int::MulInt(Box::new(term), Box::new(Int::NumLit(1))),  // × 1 (identity)
            _ => Int::Neg(Box::new(Int::Neg(Box::new(term)))),           // double-neg (identity)
        };
    }
    let v = term.try_eval();
    // `i % 3 == 0` for i in 0..1000 happens 334 times (0, 3, 6, ..., 999).
    // Only the Add branch changes the value; Muls and double-Negs are identity.
    // Start = 1, +334 increments of 1 → 335.
    assert_eq!(v, Some(335),
        "deep mixed-op chain: 1 initial + 334 increments");
}
