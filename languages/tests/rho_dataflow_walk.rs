//! E3 walk-classification gate: the per-language emitter
//! `<Lang>::rho_fold_dataflow_invocation_to` (macros/.../rho_dataflow.rs) walks a real generated
//! language's ORIGINAL parsed AST and correctly classifies a term as `Run` (lowerable to a Rholang
//! dataflow) or `Defer` (must run on Dovetail). It also produces the expected dataflow `Par` SHAPE
//! for a nested expression — the shape `rholang-runtime/tests/run_dataflow.rs` separately verifies
//! executes to the right value on the real RhoRuntime. Together they cover the full E3 path
//! (parse → walk → dataflow → run); the downstream Calculator wrapper test exercises it end-to-end.
//!
//! Crucially the walk runs on the ORIGINAL term (Calculator's Dovetail folds would collapse
//! `(2+3)*(4-1)` to the literal `15`, degenerating the dataflow — red-team FATAL-1).
#![cfg(all(feature = "calculator", feature = "rho-codegen"))]

use mettail_languages::calculator::CalculatorLanguage;
use mettail_rholang_codegen::RhoFoldDataflowDisposition;
use mettail_runtime::Language;

#[test]
fn nested_scalar_expression_classifies_as_run_with_dataflow_shape() {
    let lang = CalculatorLanguage;
    let term = lang
        .parse_term("(2 + 3) * (4 - 1)")
        .expect("parse nested calculator expression");
    match CalculatorLanguage::rho_fold_dataflow_invocation_to(term.as_ref(), "OUT")
        .expect("walk must not hard-error")
    {
        RhoFoldDataflowDisposition::Run(invocation) => {
            assert_eq!(invocation.out_channel, "OUT");
            // (2+3)*(4-1): two leaf-only producer sends (Add, Sub) + one root JOIN (Mul over both
            // intermediate channels) — the exact shape run_dataflow.rs runs to 15.
            assert_eq!(invocation.call.sends.len(), 2, "two leaf-only producer sends");
            assert_eq!(invocation.call.receives.len(), 1, "one root multi-bind JOIN");
            assert!(
                invocation.call.locally_free.is_empty(),
                "the assembled dataflow call must be a closed term"
            );
        },
        RhoFoldDataflowDisposition::Defer => {
            panic!("a nested all-scalar expression must lower to a Rho dataflow, not Defer")
        },
    }
}

#[test]
fn division_by_zero_classifies_as_defer() {
    // `5 / 0` is structurally lowerable (DivInt has a Rho contract) but `try_eval` declines
    // (safe_div → None), so the walk Defers to Dovetail rather than emit an unguarded `EDiv` that
    // would hard-error in the Rho reducer. This is behavioral parity with Dovetail's safe arithmetic.
    let lang = CalculatorLanguage;
    let term = lang.parse_term("5 / 0").expect("parse division by zero");
    assert!(
        matches!(
            CalculatorLanguage::rho_fold_dataflow_invocation_to(term.as_ref(), "OUT")
                .expect("walk must not hard-error"),
            RhoFoldDataflowDisposition::Defer
        ),
        "5 / 0 must Defer (try_eval declines; the Rho `/` contract is unguarded)"
    );
}
