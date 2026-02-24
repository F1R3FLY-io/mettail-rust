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
