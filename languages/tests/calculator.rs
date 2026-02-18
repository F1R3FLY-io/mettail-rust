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
    let normal = results.normal_forms();
    assert_eq!(normal.len(), 1);
    assert_eq!(normal[0].display, "3");
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

/// Float support: parse float literal and check canonical wrapper (Eq/Hash/Ord via CanonicalFloat64).
#[test]
fn test_float_literal_parse() {
    mettail_runtime::clear_var_cache();
    let parser = calc::calculator::FloatParser::new();
    let term = parser.parse("1.5").expect("parse 1.5");
    if let calc::Float::FloatLit(v) = term {
        assert!((v.get() - 1.5).abs() < 1e-10);
    } else {
        panic!("expected FloatLit, got {:?}", term);
    }
    // Float is used in relations in the main crate (calculator_source); parsing confirms the type works.
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

/// Rust-style suffix: "1.0f32" parses as Float via full language parse.
#[test]
fn test_exec_float_1_0_f32() {
    mettail_runtime::clear_var_cache();
    let term = calc::CalculatorLanguage::parse("1.0f32").expect("parse 1.0f32");
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

/// Unary minus and scientific notation: "-1.0E01" parses as Float (-10.0).
#[test]
fn test_exec_float_neg_scientific() {
    mettail_runtime::clear_var_cache();
    let term = calc::CalculatorLanguage::parse("-1.0E01").expect("parse -1.0E01");
    if let calc::CalculatorTermInner::Float(inner) = &term.0 {
        if let calc::Float::FloatLit(v) = inner {
            assert!((v.get() - (-10.0)).abs() < 1e-10, "expected -10.0, got {}", v.get());
        } else {
            panic!("expected FloatLit, got {:?}", inner);
        }
    } else {
        panic!("expected Float variant, got {:?}", term.0);
    }
}

/// exec x when x = 2.0E3 + 1.5: display of x must re-parse (whole-number float as "2000.0"),
/// then running ascent yields 2001.5.
#[test]
fn test_exec_env_float_scientific_whole() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();

    let term = lang
        .parse_term_for_env("2.0E3 + 1.5")
        .expect("parse 2.0E3 + 1.5");
    lang.add_to_env(env.as_mut(), "x", term.as_ref())
        .expect("add x");

    let bindings = lang.list_env(env.as_ref());
    let display = bindings
        .iter()
        .find(|(name, _, _)| name == "x")
        .map(|(_, d, _)| d.clone())
        .expect("x in env");

    let parsed = lang
        .parse_term(&display)
        .expect("display must re-parse as Float (e.g. 2000.0 + 1.5)");
    let substituted = lang
        .substitute_env(parsed.as_ref(), env.as_ref())
        .expect("substitute_env");
    let results = lang.run_ascent(substituted.as_ref()).expect("run_ascent");

    let normal = results.normal_forms();
    assert_eq!(normal.len(), 1, "one normal form");
    assert_eq!(normal[0].display, "2001.5", "result is 2001.5");
}
