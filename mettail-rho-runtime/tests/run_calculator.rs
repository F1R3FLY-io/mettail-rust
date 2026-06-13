//! M-RHO.0.5 / M-RHO.0.4: run the lowered calculator scalar-op contracts on a
//! REAL in-memory f1r3node-rust `RhoRuntime` and assert the computed results.
//!
//! For each Int operator the Rho-default planner validates the lowered Rholang
//! AST contract artifact, the runtime injects that validated artifact directly,
//! sends a concrete AST call process, and reads the result back from a fixed
//! output channel. The asserted values ARE the calculator's defined arithmetic semantics
//! (`AddInt = a + b`, …) — i.e. exactly what the Ascent backend computes — so
//! this is the per-op differential oracle (rho-backend ≡ Ascent) executed
//! end-to-end without routing generated code through source text.

use mettail_ast::language::LanguageDef;
use mettail_rho_codegen::{
    plan_rho_default_backend, RhoArtifactKind, RhoCoverageEvidence, RhoDefaultBackendEvidence,
};
use mettail_rho_runtime::{PlannedRhoBackend, RhoExecutionBoundary};
use models::rhoapi::Par;
use models::rust::utils::{new_gint_par, new_gstring_par, new_send_par};
use std::collections::{BTreeMap, BTreeSet};

// The calculator's Int scalar-op fragment, body-less (the lowering keys on the
// concrete-syntax operator + operand types). Every rule here lowers to a Rholang
// contract.
const CALC_RUN_FRAGMENT: &str = r#"
    name: CalcRun,
    types { Proc }
    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ;
        SubInt . a:Int, b:Int |- a "-" b : Int ;
        MulInt . a:Int, b:Int |- a "*" b : Int ;
        DivInt . a:Int, b:Int |- a "/" b : Int ;
        ModInt . a:Int, b:Int |- a "%" b : Int ;
        Neg . a:Int |- "-" a : Int ;
    }
"#;

fn quoted_channel(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

fn passing_evidence() -> RhoDefaultBackendEvidence {
    RhoDefaultBackendEvidence {
        proofs_passed: true,
        oracle_parity_passed: true,
        coverage_audit_passed: true,
        coverage: RhoCoverageEvidence::AllRulesLowered,
    }
}

fn calculator_backend() -> PlannedRhoBackend {
    let def =
        syn::parse_str::<LanguageDef>(CALC_RUN_FRAGMENT).expect("calculator fragment must parse");
    let plan = plan_rho_default_backend(&def, passing_evidence())
        .expect("all calculator Int scalar ops must pass the Rho-default gate");
    assert_eq!(
        plan.lowering.lowered,
        vec!["AddInt", "SubInt", "MulInt", "DivInt", "ModInt", "Neg"],
        "all six Int scalar ops must lower"
    );
    assert!(plan.lowering.rejected.is_empty(), "no rule should be rejected here");
    PlannedRhoBackend::from_plan(plan)
}

/// `@"OP"!(a, b, @"OUT")`
fn binary_call(op: &str, a: i64, b: i64) -> Par {
    new_send_par(
        quoted_channel(op),
        vec![
            new_gint_par(a, Vec::new(), false),
            new_gint_par(b, Vec::new(), false),
            quoted_channel("OUT"),
        ],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// `@"OP"!(a, @"OUT")`
fn unary_call(op: &str, a: i64) -> Par {
    new_send_par(
        quoted_channel(op),
        vec![new_gint_par(a, Vec::new(), false), quoted_channel("OUT")],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

#[tokio::test]
async fn lowered_calculator_int_ops_compute_correctly_on_rho_runtime() {
    let backend = calculator_backend();

    assert_eq!(backend.artifact_kind(), RhoArtifactKind::NormalizedAst);
    assert!(
        backend.ast_par().is_some(),
        "generated execution must use normalized AST, not source text"
    );
    assert!(
        backend.text_annotation().contains("contract @\"AddInt\""),
        "reader annotation remains available but is not the execution boundary"
    );

    let cases: &[(&str, i64, i64, i64)] = &[
        ("AddInt", 2, 3, 5),
        ("SubInt", 10, 4, 6),
        ("MulInt", 3, 7, 21),
        ("DivInt", 20, 4, 5),
        ("ModInt", 17, 5, 2),
    ];
    for &(op, a, b, expected) in cases {
        let call = binary_call(op, a, b);
        let report = backend
            .run_with_call_and_observe_ints(&call, "OUT")
            .await
            .unwrap_or_else(|e| panic!("{op}({a},{b}) failed to run: {e}"));
        assert_eq!(report.boundary, RhoExecutionBoundary::PlannedDefaultBackend);
        assert_eq!(report.artifact_kind, RhoArtifactKind::NormalizedAst);
        assert_eq!(report.channel, "OUT");
        assert_eq!(report.values, vec![expected], "{op}({a}, {b}) on RhoRuntime");
        assert_eq!(report.observed_count(), 1);
        assert_eq!(report.membership_fingerprint(), BTreeSet::from([expected]));
        assert_eq!(report.multiplicity_fingerprint(), BTreeMap::from([(expected, 1_usize)]));
    }

    // Unary negation.
    let call = unary_call("Neg", 7);
    let report = backend
        .run_with_call_and_observe_ints(&call, "OUT")
        .await
        .unwrap_or_else(|e| panic!("Neg(7) failed to run: {e}"));
    assert_eq!(report.values, vec![-7], "Neg(7) on RhoRuntime");
    assert_eq!(report.membership_fingerprint(), BTreeSet::from([-7]));
    assert_eq!(report.multiplicity_fingerprint(), BTreeMap::from([(-7, 1_usize)]));
}
