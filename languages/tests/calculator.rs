// use mettail_languages::calculator::{parse_and_eval_with_env, CalculatorEnv};

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

// ── Unary prefix operator tests ──

use mettail_languages::calculator::Int;

#[test]
fn test_unary_minus_literal() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-3").expect("should parse -3");
    // Result should be Neg(NumLit(3)) — check via eval
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
    // Should parse as (-3) - 5 = -8, NOT -(3 - 5) = 2
    let result = Int::parse("-3 - 5").expect("should parse -3 - 5");
    assert_eq!(result.eval(), -8, "unary minus should bind tighter than subtraction");
}

#[test]
fn test_binary_minus_with_unary() {
    mettail_runtime::clear_var_cache();
    // Should parse as Sub(3, Neg(5)) → 3 - (-5) = 8
    let result = Int::parse("3 - -5").expect("should parse 3 - -5");
    assert_eq!(result.eval(), 8, "binary minus then unary minus in prefix position");
}

#[test]
fn test_double_negation() {
    mettail_runtime::clear_var_cache();
    // Should parse as Neg(Neg(3)) → --3 = 3
    let result = Int::parse("--3").expect("should parse --3");
    assert_eq!(result.eval(), 3, "double negation should cancel out");
}

#[test]
fn test_unary_minus_with_multiplication() {
    mettail_runtime::clear_var_cache();
    // Should parse as (-3) ^ 2 = 9 (unary binds tighter than pow)
    let result = Int::parse("-3 ^ 2").expect("should parse -3 ^ 2");
    assert_eq!(result.eval(), 9, "unary minus should bind tighter than exponentiation");
}

#[test]
fn test_unary_minus_variable() {
    mettail_runtime::clear_var_cache();
    // Should parse without error (produces Neg(IVar(x)))
    let result = Int::parse("-x");
    assert!(result.is_ok(), "should parse -x as Neg(IVar(x))");
}

#[test]
fn test_not_binds_tight() {
    // Verify behavioral change: "not true && false" should parse as "(not true) && false"
    // which is false && false = false, NOT not(true && false) = not(false) = true
    use mettail_languages::calculator::Bool;

    mettail_runtime::clear_var_cache();
    let result = Bool::parse("not true && false").expect("should parse not true && false");
    assert_eq!(result.eval(), false, "not should bind tighter than &&");
}

// ── Right-associativity tests ──

#[test]
fn test_pow_right_associativity() {
    mettail_runtime::clear_var_cache();
    // 2 ^ 3 ^ 2 should parse as 2 ^ (3 ^ 2) = 2 ^ 9 = 512
    // NOT (2 ^ 3) ^ 2 = 8 ^ 2 = 64
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
    // 3 + 5! should parse as 3 + (5!) = 3 + 120 = 123
    let result = Int::parse("3 + 5!").expect("should parse 3 + 5!");
    assert_eq!(result.eval(), 123, "postfix ! should bind tighter than +");
}

#[test]
fn test_factorial_with_negation() {
    mettail_runtime::clear_var_cache();
    // -5! should parse as -(5!) = -120, not (-5)! = undefined
    let result = Int::parse("-5!").expect("should parse -5!");
    assert_eq!(result.eval(), -120, "postfix ! should bind tighter than unary -");
}

#[test]
fn test_factorial_with_parentheses() {
    mettail_runtime::clear_var_cache();
    // (3 + 2)! should parse as (5)! = 120
    let result = Int::parse("(3 + 2)!").expect("should parse (3 + 2)!");
    assert_eq!(result.eval(), 120, "(3 + 2)! = 5! = 120");
}

#[test]
fn test_factorial_precedence_over_pow() {
    mettail_runtime::clear_var_cache();
    // 3! ^ 2 should parse as (3!)^2 = 6^2 = 36
    // because postfix binds tighter than infix
    let result = Int::parse("3! ^ 2").expect("should parse 3! ^ 2");
    assert_eq!(result.eval(), 36, "3! ^ 2 = 6^2 = 36");
}

// ── Mixfix operator tests (ternary) ──

#[test]
fn test_ternary_true_branch() {
    mettail_runtime::clear_var_cache();
    // 1 ? 42 : 0 → condition is nonzero → 42
    let result = Int::parse("1 ? 42 : 0").expect("should parse ternary");
    assert_eq!(result.eval(), 42, "nonzero condition selects then-branch");
}

#[test]
fn test_ternary_false_branch() {
    mettail_runtime::clear_var_cache();
    // 0 ? 42 : 99 → condition is zero → 99
    let result = Int::parse("0 ? 42 : 99").expect("should parse ternary");
    assert_eq!(result.eval(), 99, "zero condition selects else-branch");
}

#[test]
fn test_ternary_negative_condition() {
    mettail_runtime::clear_var_cache();
    // -1 ? 10 : 20 → nonzero → 10
    let result = Int::parse("-1 ? 10 : 20").expect("should parse ternary with negative condition");
    assert_eq!(result.eval(), 10, "negative nonzero condition selects then-branch");
}

#[test]
fn test_ternary_with_expressions() {
    mettail_runtime::clear_var_cache();
    // (1 + 0) ? (3 + 4) : (10 - 5) → 1 ? 7 : 5 → 7
    let result = Int::parse("(1 + 0) ? (3 + 4) : (10 - 5)").expect("should parse");
    assert_eq!(result.eval(), 7, "ternary with subexpressions");
}

#[test]
fn test_ternary_right_associativity() {
    mettail_runtime::clear_var_cache();
    // a ? b : c ? d : e parses as a ? b : (c ? d : e) (right-associative)
    // 1 ? 2 : 1 ? 3 : 4 → 1 ? 2 : (1 ? 3 : 4) → 2
    let result = Int::parse("1 ? 2 : 1 ? 3 : 4").expect("should parse nested ternary");
    assert_eq!(result.eval(), 2, "first condition is nonzero, selects 2");
}

#[test]
fn test_ternary_nested_else() {
    mettail_runtime::clear_var_cache();
    // 0 ? 2 : 1 ? 3 : 4 → 0 ? 2 : (1 ? 3 : 4) → (1 ? 3 : 4) → 3
    let result = Int::parse("0 ? 2 : 1 ? 3 : 4").expect("should parse nested ternary else");
    assert_eq!(result.eval(), 3, "fall through to nested ternary");
}

#[test]
fn test_ternary_lowest_precedence() {
    mettail_runtime::clear_var_cache();
    // 1 + 0 ? 3 + 4 : 5 → (1 + 0) ? (3 + 4) : 5 → 1 ? 7 : 5 → 7
    // Ternary should have lower precedence than +
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
