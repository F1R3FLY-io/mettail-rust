//! Algebraic property assertions: equation symmetry, rewrite progress,
//! rewrite-to, normal form checking.

#[allow(unused_imports)]
use mettail_runtime::{Language, Term};

/// Run Ascent on lhs, verify rhs appears in equivalence class (and vice versa).
pub fn assert_equation_symmetry(
    lang: &dyn Language,
    lhs_str: &str,
    rhs_str: &str,
) -> Result<(), String> {
    // Forward: lhs => check rhs in equiv class
    mettail_runtime::clear_var_cache();
    let lhs = lang
        .parse_term(lhs_str)
        .map_err(|e| format!("Failed to parse LHS '{}': {}", lhs_str, e))?;

    mettail_runtime::clear_var_cache();
    let results = lang
        .run_ascent(lhs.as_ref())
        .map_err(|e| format!("Ascent failed on LHS '{}': {}", lhs_str, e))?;

    // Check that rhs appears somewhere in the reachable terms
    let rhs_found = results
        .all_terms
        .iter()
        .any(|t| t.display == rhs_str);

    if !rhs_found {
        let all_displays: Vec<&str> = results.all_terms.iter().map(|t| t.display.as_str()).collect();
        return Err(format!(
            "Equation LHS->RHS failed: '{}' does not produce '{}'\n  reachable: {:?}",
            lhs_str, rhs_str, all_displays
        ));
    }

    // Backward: rhs => check lhs in equiv class
    mettail_runtime::clear_var_cache();
    let rhs = lang
        .parse_term(rhs_str)
        .map_err(|e| format!("Failed to parse RHS '{}': {}", rhs_str, e))?;

    mettail_runtime::clear_var_cache();
    let results = lang
        .run_ascent(rhs.as_ref())
        .map_err(|e| format!("Ascent failed on RHS '{}': {}", rhs_str, e))?;

    let lhs_found = results
        .all_terms
        .iter()
        .any(|t| t.display == lhs_str);

    if !lhs_found {
        let all_displays: Vec<&str> = results.all_terms.iter().map(|t| t.display.as_str()).collect();
        return Err(format!(
            "Equation RHS->LHS failed: '{}' does not produce '{}'\n  reachable: {:?}",
            rhs_str, lhs_str, all_displays
        ));
    }

    Ok(())
}

/// Run Ascent on term, verify at least one rewrite fires.
pub fn assert_rewrite_fires(lang: &dyn Language, input: &str) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(input)
        .map_err(|e| format!("Failed to parse '{}': {}", input, e))?;

    mettail_runtime::clear_var_cache();
    let results = lang
        .run_ascent(term.as_ref())
        .map_err(|e| format!("Ascent failed for '{}': {}", input, e))?;

    if results.rewrites.is_empty() {
        return Err(format!(
            "Expected at least one rewrite to fire for '{}', but none did",
            input
        ));
    }

    Ok(())
}

/// Run Ascent, verify rewrite reaches expected normal form.
pub fn assert_rewrites_to(
    lang: &dyn Language,
    input: &str,
    expected: &str,
) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(input)
        .map_err(|e| format!("Failed to parse '{}': {}", input, e))?;

    mettail_runtime::clear_var_cache();
    let results = lang
        .run_ascent(term.as_ref())
        .map_err(|e| format!("Ascent failed for '{}': {}", input, e))?;

    let normal_forms = results.normal_forms();
    for nf in &normal_forms {
        if nf.display == expected {
            return Ok(());
        }
    }

    let nf_displays: Vec<&str> = normal_forms.iter().map(|nf| nf.display.as_str()).collect();
    Err(format!(
        "Rewrite mismatch:\n  input:    '{}'\n  expected: '{}'\n  got:      {:?}",
        input, expected, nf_displays
    ))
}

/// Verify term is in normal form (no rewrites apply).
pub fn assert_normal_form(lang: &dyn Language, input: &str) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(input)
        .map_err(|e| format!("Failed to parse '{}': {}", input, e))?;

    mettail_runtime::clear_var_cache();
    let results = lang
        .run_ascent(term.as_ref())
        .map_err(|e| format!("Ascent failed for '{}': {}", input, e))?;

    if !results.rewrites.is_empty() {
        let targets: Vec<String> = results
            .rewrites
            .iter()
            .filter_map(|rw| {
                results
                    .all_terms
                    .iter()
                    .find(|t| t.term_id == rw.to_id)
                    .map(|t| t.display.clone())
            })
            .collect();
        return Err(format!(
            "Expected '{}' to be in normal form, but rewrites fired to: {:?}",
            input, targets
        ));
    }

    Ok(())
}
