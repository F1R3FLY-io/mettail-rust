//! Alpha-equivalence assertion utilities.
//!
//! Thin wrappers around `Term::term_eq()` for use in generated test code.

use mettail_runtime::Term;

/// Assert two terms are alpha-equivalent via `Term::term_eq()`.
///
/// Uses moniker's `BoundTerm::term_eq` which handles binder renaming correctly.
pub fn assert_alpha_eq(left: &dyn Term, right: &dyn Term) -> Result<(), String> {
    if left.term_eq(right) {
        Ok(())
    } else {
        Err(format!(
            "Terms are not alpha-equivalent:\n  left:  {:?}\n  right: {:?}",
            left, right
        ))
    }
}

/// Assert two terms (given as strings) are alpha-equivalent after parsing.
pub fn assert_alpha_eq_str(
    lang: &dyn mettail_runtime::Language,
    left_str: &str,
    right_str: &str,
) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let left = lang
        .parse_term(left_str)
        .map_err(|e| format!("Failed to parse left '{}': {}", left_str, e))?;

    mettail_runtime::clear_var_cache();
    let right = lang
        .parse_term(right_str)
        .map_err(|e| format!("Failed to parse right '{}': {}", right_str, e))?;

    assert_alpha_eq(left.as_ref(), right.as_ref())
}
