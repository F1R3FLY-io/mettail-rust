//! Structural property assertions: roundtrip, display idempotence, parse determinism.

use std::fmt::Display;

#[allow(unused_imports)]
use mettail_runtime::Term;
use proptest::test_runner::TestCaseError;

/// Assert `parse(display(term)).term_eq(term)` — round-trip via alpha-equivalence.
///
/// Clears the var cache before display and before parse to ensure isolation.
pub fn assert_roundtrip<T>(term: &T) -> Result<(), TestCaseError>
where
    T: Display + Term,
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: Display,
{
    mettail_runtime::clear_var_cache();
    let displayed = format!("{}", term);

    mettail_runtime::clear_var_cache();
    let parsed: T = displayed.parse().map_err(|e| {
        TestCaseError::fail(format!(
            "Failed to parse displayed term: '{}'\nOriginal: {:?}\nError: {}",
            displayed, term, e
        ))
    })?;

    if !term.term_eq(&parsed) {
        return Err(TestCaseError::fail(format!(
            "Roundtrip failed (alpha-equivalence):\n  displayed: '{}'\n  original:  {:?}\n  parsed:    {:?}",
            displayed, term, parsed
        )));
    }

    Ok(())
}

/// Assert `display(parse(display(term))) == display(term)` — display idempotence.
///
/// Uses string equality on the display output (not alpha-equivalence on terms).
pub fn assert_display_idempotence<T>(term: &T) -> Result<(), TestCaseError>
where
    T: Display + Term,
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: Display,
{
    mettail_runtime::clear_var_cache();
    let displayed_1 = format!("{}", term);

    mettail_runtime::clear_var_cache();
    let parsed: T = displayed_1.parse().map_err(|e| {
        TestCaseError::fail(format!(
            "Failed to parse for idempotence check: '{}'\nError: {}",
            displayed_1, e
        ))
    })?;

    mettail_runtime::clear_var_cache();
    let displayed_2 = format!("{}", parsed);

    if displayed_1 != displayed_2 {
        return Err(TestCaseError::fail(format!(
            "Display not idempotent:\n  first:  '{}'\n  second: '{}'",
            displayed_1, displayed_2
        )));
    }

    Ok(())
}

/// Assert `parse(input)` succeeds, returning the parsed term.
pub fn assert_parses<T>(input: &str) -> Result<T, String>
where
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: Display,
{
    mettail_runtime::clear_var_cache();
    input
        .parse::<T>()
        .map_err(|e| format!("Expected parse to succeed for '{}', but got: {}", input, e))
}

/// Assert `parse(input)` fails.
pub fn assert_parse_fails<T>(input: &str) -> Result<(), String>
where
    T: std::str::FromStr,
{
    mettail_runtime::clear_var_cache();
    match input.parse::<T>() {
        Ok(_) => Err(format!("Expected parse to fail for '{}', but it succeeded", input)),
        Err(_) => Ok(()),
    }
}
