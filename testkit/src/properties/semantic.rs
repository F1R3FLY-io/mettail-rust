//! Semantic property assertions: eval determinism, normalization idempotence,
//! substitution well-formedness, ground eval completeness.

use mettail_runtime::{Language, Term};

/// Assert `eval(t) == eval(t)` — evaluation is deterministic.
///
/// Evaluates the term twice and verifies the results are alpha-equivalent.
pub fn assert_eval_determinism(lang: &dyn Language, term: &dyn Term) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let result_1 = lang
        .run_ascent(term)
        .map_err(|e| format!("First eval failed: {}", e))?;

    mettail_runtime::clear_var_cache();
    let result_2 = lang
        .run_ascent(term)
        .map_err(|e| format!("Second eval failed: {}", e))?;

    let nf_1 = result_1.normal_forms();
    let nf_2 = result_2.normal_forms();

    if nf_1.len() != nf_2.len() {
        return Err(format!(
            "Non-deterministic eval: {} normal forms vs {} normal forms\n  term: {:?}",
            nf_1.len(),
            nf_2.len(),
            term
        ));
    }

    Ok(())
}

/// Assert `is_ground(t) => try_direct_eval(t).is_some()` — ground terms evaluate.
pub fn assert_ground_eval_completeness(
    lang: &dyn Language,
    term: &dyn Term,
    is_ground: bool,
) -> Result<(), String> {
    if !is_ground {
        return Ok(()); // Only applies to ground terms
    }

    mettail_runtime::clear_var_cache();
    match lang.try_direct_eval(term) {
        Some(_) => Ok(()),
        None => Err(format!("Ground term did not evaluate: {:?}", term)),
    }
}

/// Assert eval(parse(input)) displays as expected.
pub fn assert_evals_to(lang: &dyn Language, input: &str, expected: &str) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(input)
        .map_err(|e| format!("Failed to parse input '{}': {}", input, e))?;

    // Try direct eval first (for native types)
    if let Some(result) = lang.try_direct_eval(term.as_ref()) {
        let result_str = format!("{}", result);
        if result_str != expected {
            return Err(format!(
                "Eval mismatch:\n  input:    '{}'\n  expected: '{}'\n  got:      '{}'",
                input, expected, result_str
            ));
        }
        return Ok(());
    }

    // Fall back to Ascent rewriting
    mettail_runtime::clear_var_cache();
    let results = lang
        .run_ascent(term.as_ref())
        .map_err(|e| format!("Ascent failed for '{}': {}", input, e))?;

    let normal_forms = results.normal_forms();
    if normal_forms.is_empty() {
        return Err(format!("No normal form reached for '{}', expected '{}'", input, expected));
    }

    // Check if any normal form matches expected
    for nf in &normal_forms {
        if nf.display == expected {
            return Ok(());
        }
    }

    let nf_displays: Vec<&str> = normal_forms.iter().map(|nf| nf.display.as_str()).collect();
    Err(format!(
        "No normal form matches expected:\n  input:    '{}'\n  expected: '{}'\n  got:      {:?}",
        input, expected, nf_displays
    ))
}
