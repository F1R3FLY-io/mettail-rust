// use mettail_theories::calculator::{parse_and_eval_with_env, CalculatorEnv};

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
