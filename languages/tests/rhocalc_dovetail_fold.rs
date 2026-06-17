//! Step G of the Dovetail native-fold reduction work (Increments 2/3): end-to-end proof that
//! RhoCalc's `Proc`-output `fold` rules — whose `![{..}]` bodies (`numeric_dispatch::rho_proc_*`)
//! reduced NOWHERE after the Ascent retirement — now reduce IN-ENGINE via the typed-`L`
//! native-rewrite dispatcher, surfacing the normal form through funded extraction.
#![cfg(all(feature = "rhocalc", feature = "dovetail-codegen"))]

use mettail_languages::rhocalc::RhoCalcLanguage;
use mettail_runtime::Language;

/// Parse `src`, run it through the typed Dovetail report, assert it converges to a `Complete`
/// report, and return every term op-display in the derivation forest.
fn fold_report_ops(src: &str) -> Vec<String> {
    let lang = RhoCalcLanguage;
    let term = lang.parse_term(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"));
    let report = RhoCalcLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .unwrap_or_else(|e| panic!("`{src}` must compile to a Dovetail report: {e}"));
    assert!(report.is_complete(), "`{src}` must reduce to a Complete (converged, acyclic) report");
    assert!(!report.roots.is_empty(), "`{src}` must produce at least one root");
    report.terms.iter().map(|t| t.op_display.clone()).collect()
}

#[test]
fn nested_int_cast_folds_via_saturation() {
    // `int(1 + 2, 8)` = IntBinProc(Add(CastInt 1, CastInt 2), 8). The inner `Add` is a Proc
    // fold redex; it must fire FIRST (the dispatcher's fold-readiness guard defers the `int`
    // cast until its child is a value), congruence shares the `3`, then the cast fires. The
    // strong witness that the fold actually computed `1 + 2 = 3` is a `NumLit(3)` op — it
    // appears ONLY if the native body ran (the input carries `1` and `2`, never `3`).
    let ops = fold_report_ops("int(1 + 2, 8)");
    assert!(
        ops.iter().any(|o| o.contains("CastInt")),
        "int(1+2,8) must fold to a CastInt normal form; ops: {ops:?}"
    );
    assert!(
        ops.iter().any(|o| o.contains("NumLit(3)")),
        "int(1+2,8) must compute 1+2=3 in-engine (NumLit(3)); ops: {ops:?}"
    );
}

#[test]
fn int_cast_of_literal_is_complete() {
    // `int(7, 64)` = IntBinProc(CastInt 7, 64): a single cast fold over an already-value child.
    let ops = fold_report_ops("int(7, 64)");
    assert!(
        ops.iter().any(|o| o.contains("CastInt")),
        "int(7,64) folds to CastInt; ops: {ops:?}"
    );
}

#[test]
fn proc_arithmetic_folds() {
    // `1 + 2`: a bare Proc `Add` fold (no surrounding cast). The native `Add` body folds two
    // CastInt operands to `CastInt 3`.
    let ops = fold_report_ops("1 + 2");
    assert!(
        ops.iter().any(|o| o.contains("NumLit(3)")),
        "1 + 2 must fold to 3 in-engine (NumLit(3)); ops: {ops:?}"
    );
}
