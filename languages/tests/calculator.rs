// use mettail_languages::calculator::{parse_and_eval_with_env, CalculatorEnv};

use mettail_languages::calculator::{self as calc};

// #[test]
// fn test_numeric_literal() {
//     let mut env = CalculatorEnv::new();
//     assert_eq!(parse_and_eval_with_env("3", &mut env).unwrap(), 3);
// }

// #[test]
// fn test_addition() {
//     let mut env = CalculatorEnv::new();
//     assert_eq!(parse_and_eval_with_env("3 + 3", &mut env).unwrap(), 6);
//     assert_eq!(parse_and_eval_with_env("10+5", &mut env).unwrap(), 15);
// }

// #[test]
// fn test_subtraction() {
//     let mut env = CalculatorEnv::new();
//     assert_eq!(parse_and_eval_with_env("5-2", &mut env).unwrap(), 3);
//     assert_eq!(parse_and_eval_with_env("10 - 7", &mut env).unwrap(), 3);
// }

// #[test]
// fn test_left_associativity() {
//     let mut env = CalculatorEnv::new();
//     // (1+2)-3 == 0 and 1+2-3 parsed left-to-right -> (1+2)-3
//     assert_eq!(parse_and_eval_with_env("1+2-3", &mut env).unwrap(), 0);
//     assert_eq!(parse_and_eval_with_env("(1+2)-3", &mut env).unwrap(), 0);
// }

// #[test]
// fn test_negative_integers() {
//     let mut env = CalculatorEnv::new();
//     assert_eq!(parse_and_eval_with_env("-5", &mut env).unwrap(), -5);
//     assert_eq!(parse_and_eval_with_env("-10", &mut env).unwrap(), -10);
//     assert_eq!(parse_and_eval_with_env("5 + -3", &mut env).unwrap(), 2);
//     assert_eq!(parse_and_eval_with_env("5 - -3", &mut env).unwrap(), 8);
//     assert_eq!(parse_and_eval_with_env("-5 + 3", &mut env).unwrap(), -2);
//     assert_eq!(parse_and_eval_with_env("-5 - 3", &mut env).unwrap(), -8);
// }

// #[test]
// fn test_simple_assignment() {
//     let mut env = CalculatorEnv::new();
//     assert_eq!(parse_and_eval_with_env("x = 3 + 2", &mut env).unwrap(), 5);
//     // Verify variable was stored
//     assert_eq!(env.get("x"), Some(5));
// }

// #[test]
// fn test_variable_lookup() {
//     let mut env = CalculatorEnv::new();
//     parse_and_eval_with_env("x = 10", &mut env).unwrap();
//     assert_eq!(parse_and_eval_with_env("x", &mut env).unwrap(), 10);
// }

// #[test]
// fn test_reassignment() {
//     let mut env = CalculatorEnv::new();
//     parse_and_eval_with_env("y = 3", &mut env).unwrap();
//     assert_eq!(env.get("y"), Some(3));
//     parse_and_eval_with_env("y = 10", &mut env).unwrap();
//     assert_eq!(env.get("y"), Some(10));
// }

// #[test]
// fn test_multiple_assignments() {
//     let mut env = CalculatorEnv::new();
//     parse_and_eval_with_env("x = 3 + 2", &mut env).unwrap();
//     assert_eq!(env.get("x"), Some(5));
//     parse_and_eval_with_env("y = 10 - 1", &mut env).unwrap();
//     assert_eq!(env.get("y"), Some(9));
// }

// #[test]
// fn test_variable_in_expression() {
//     let mut env = CalculatorEnv::new();
//     parse_and_eval_with_env("x = 5", &mut env).unwrap();
//     assert_eq!(parse_and_eval_with_env("x + 3", &mut env).unwrap(), 8);
//     assert_eq!(parse_and_eval_with_env("x - 2", &mut env).unwrap(), 3);
// }

// #[test]
// fn test_assignment_with_variable_reference() {
//     let mut env = CalculatorEnv::new();
//     parse_and_eval_with_env("x = 3 + 2", &mut env).unwrap();
//     assert_eq!(parse_and_eval_with_env("y = x - 4 + 8", &mut env).unwrap(), 9);
//     assert_eq!(env.get("x"), Some(5));
//     assert_eq!(env.get("y"), Some(9));
// }

// #[test]
// fn test_multiple_vars_in_expression() {
//     let mut env = CalculatorEnv::new();
//     parse_and_eval_with_env("a = 10", &mut env).unwrap();
//     parse_and_eval_with_env("b = 5", &mut env).unwrap();
//     assert_eq!(parse_and_eval_with_env("a + b", &mut env).unwrap(), 15);
//     assert_eq!(parse_and_eval_with_env("a - b", &mut env).unwrap(), 5);
// }

// #[test]
// fn test_undefined_variable() {
//     let mut env = CalculatorEnv::new();
//     let result = parse_and_eval_with_env("x", &mut env);
//     assert!(result.is_err());
//     assert!(result.unwrap_err().contains("undefined variable"));
// }

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
    use mettail_runtime::Language;

    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();

    let term = lang
        .parse_term_for_env("2.0E3 + 1.5")
        .expect("parse 2.0E3 + 1.5");
    lang.add_to_env(env.as_mut(), "x", term.as_ref()).expect("add x");

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
