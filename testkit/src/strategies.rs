//! Shared proptest strategy helpers for generated test code.
//!
//! These functions are used by the macro-generated `arb_strategy()` methods
//! on each category type.

use proptest::prelude::*;

/// Strategy for generating fresh variable names.
///
/// Produces lowercase names of 1-4 characters, avoiding reserved keywords.
pub fn arb_var_name() -> impl Strategy<Value = String> {
    proptest::string::string_regex("[a-z][a-z0-9]{0,3}")
        .expect("valid regex for var names")
        .prop_filter("avoid reserved names", |s| {
            !matches!(
                s.as_str(),
                "lam" | "let" | "in" | "for" | "new" | "if" | "then" | "else" | "true" | "false"
            )
        })
}

/// Strategy for i32 values with interesting edge cases.
///
/// Biased toward values that tend to expose bugs: 0, 1, -1, small values,
/// and boundary values.
pub fn arb_i32_interesting() -> impl Strategy<Value = i32> {
    prop_oneof![
        3 => Just(0i32),
        2 => Just(1),
        2 => Just(-1),
        2 => Just(2),
        1 => Just(i32::MAX),
        1 => Just(i32::MIN),
        1 => Just(i32::MAX / 2),
        1 => Just(i32::MIN / 2),
        10 => -100i32..100,
        5 => any::<i32>(),
    ]
}

/// Strategy for i64 values with interesting edge cases (for languages using `![i64]`).
pub fn arb_i64_interesting() -> impl Strategy<Value = i64> {
    prop_oneof![
        3 => Just(0i64),
        2 => Just(1),
        2 => Just(-1),
        2 => Just(2),
        1 => Just(i64::MAX),
        1 => Just(i64::MIN),
        1 => Just(i64::MAX / 2),
        1 => Just(i64::MIN / 2),
        10 => -100i64..100,
        5 => any::<i64>(),
    ]
}

/// Strategy for f64 values with interesting edge cases.
pub fn arb_f64_interesting() -> impl Strategy<Value = f64> {
    prop_oneof![
        3 => Just(0.0f64),
        2 => Just(1.0),
        2 => Just(-1.0),
        1 => Just(0.5),
        1 => Just(f64::INFINITY),
        1 => Just(f64::NEG_INFINITY),
        10 => -100.0f64..100.0,
        5 => any::<f64>().prop_filter("exclude NaN", |x| !x.is_nan()),
    ]
}

/// Strategy for bool values.
pub fn arb_bool() -> impl Strategy<Value = bool> {
    any::<bool>()
}

/// Strategy for short strings (0-8 characters).
pub fn arb_string_short() -> impl Strategy<Value = String> {
    proptest::string::string_regex("[a-zA-Z0-9_]{0,8}")
        .expect("valid regex for short strings")
}
