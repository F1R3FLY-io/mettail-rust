//! Stage 3.13e (2026-05-01) — Bug A regression test.
//!
//! Verifies that auto-injected cast wrappers propagate inner reductions
//! through the synthetic congruence rule emitted by
//! `wpds_codegen/auto_inject.rs::make_injection_cong_rule`.
//!
//! Pre-3.13e: `auto_inject.rs::emit_auto_injection_rules` emitted only
//! the `<Source>To<Target>` term constructor; no congruence rewrite was
//! produced for it. Inner `rw_<source>` reductions stopped at the cast
//! wrapper because no rule like `rw_<target>(<S>To<T>(s), <S>To<T>(t))
//! <-- <target>(<S>To<T>(s)), rw_<source>(s, t)` existed.
//!
//! Post-3.13e: synthetic `<S>To<T>Cong` rewrite is emitted alongside the
//! term, restoring the propagation chain.
//!
//! Verification corpus: small expressions where the parse produces a
//! cast-wrapped AST and the inner expression has a known reduction. The
//! test asserts the reduced form is in the result's normal-forms.

use mettail_languages::calculator::CalculatorLanguage;
use mettail_runtime::Language;

#[test]
fn float_addfloat_inside_bigrat_cast_reduces() {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let parsed = lang.parse_term("2.0 + 2.5").expect("parse");
    let results = lang.run_ascent(parsed.as_ref()).expect("eval");

    // The rewrite engine must produce at least one rewrite via the
    // FloatToBigRatCong (or AddFloatCong) propagation chain.
    assert!(
        !results.rewrites.is_empty(),
        "expected at least one rewrite for 2.0 + 2.5; got 0. \
         all_terms: {:?}",
        results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect::<Vec<_>>()
    );

    // Some normal form must contain the reduced value `4.5` somewhere
    // in its display (either as plain `4.5` if Float-typed, or wrapped
    // in a cast like `4.5` itself if BigRat displays Float values
    // naturally).
    let nfs: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|t| t.display.clone())
        .collect();
    assert!(
        nfs.iter().any(|d| d.contains("4.5")),
        "expected a normal form containing reduced value 4.5; got: {:?}",
        nfs
    );
}

#[test]
fn intops_inside_bigint_cast_reduce() {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let parsed = lang.parse_term("3 + 4").expect("parse");
    let results = lang.run_ascent(parsed.as_ref()).expect("eval");

    let nfs: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|t| t.display.clone())
        .collect();
    assert!(
        nfs.iter().any(|d| d.contains('7')),
        "expected normal form containing reduced value 7; got: {:?}",
        nfs
    );
}
