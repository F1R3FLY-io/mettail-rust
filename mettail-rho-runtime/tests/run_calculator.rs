//! M-RHO.0.5 / M-RHO.0.4: run the lowered calculator scalar-op contracts on a
//! REAL in-memory f1r3node-rust `RhoRuntime` and assert the computed results.
//!
//! For each native scalar operator covered here, the Rho-default planner
//! validates the lowered Rholang AST contract artifact, the runtime injects
//! that validated artifact directly, sends a concrete AST call process, and
//! reads the result back from a fixed output channel. The asserted values are
//! the calculator's defined Int, Bool, and Str scalar semantics — i.e. exactly
//! what the Ascent backend computes — so this is the per-op differential oracle
//! (rho-backend ≡ Ascent) executed end-to-end without routing generated code
//! through source text.

use mettail_ast::language::LanguageDef;
use mettail_rho_codegen::{
    plan_rho_default_backend_with_evidence_audit, RhoArtifactKind, RhoAstLiteral, RhoAstSend,
    RhoCoverageEvidence, RhoDefaultBackendEvidence,
};
use mettail_rho_runtime::{PlannedRhoBackend, RhoExecutionBoundary};
use models::rhoapi::Par;
use std::collections::{BTreeMap, BTreeSet};

mod support;

// The calculator's Rholang-native scalar-op fragment, body-less. Lowering keys
// on concrete-syntax operator, operand types, and result type. Every rule here
// lowers to a Rholang contract.
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
        EqInt . a:Int, b:Int |- a "==" b : Bool ;
        NeInt . a:Int, b:Int |- a "!=" b : Bool ;
        LtInt . a:Int, b:Int |- a "<" b : Bool ;
        GtInt . a:Int, b:Int |- a ">" b : Bool ;
        LtEqInt . a:Int, b:Int |- a "<=" b : Bool ;
        GtEqInt . a:Int, b:Int |- a ">=" b : Bool ;
        EqBool . a:Bool, b:Bool |- a "==" b : Bool ;
        NeBool . a:Bool, b:Bool |- a "!=" b : Bool ;
        LtBool . a:Bool, b:Bool |- a "<" b : Bool ;
        GtBool . a:Bool, b:Bool |- a ">" b : Bool ;
        LtEqBool . a:Bool, b:Bool |- a "<=" b : Bool ;
        GtEqBool . a:Bool, b:Bool |- a ">=" b : Bool ;
        EqStr . a:Str, b:Str |- a "==" b : Bool ;
        NeStr . a:Str, b:Str |- a "!=" b : Bool ;
        LtStr . a:Str, b:Str |- a "<" b : Bool ;
        GtStr . a:Str, b:Str |- a ">" b : Bool ;
        LtEqStr . a:Str, b:Str |- a "<=" b : Bool ;
        GtEqStr . a:Str, b:Str |- a ">=" b : Bool ;
        And . a:Bool, b:Bool |- a "and" b : Bool ;
        Or . a:Bool, b:Bool |- a "or" b : Bool ;
        Not . a:Bool |- "not" a : Bool ;
        Concat . a:Str, b:Str |- a "++" b : Str ;
        AddStr . a:Str, b:Str |- a "+" b : Str ;
    }
"#;

fn passing_evidence() -> RhoDefaultBackendEvidence {
    RhoDefaultBackendEvidence {
        proofs_passed: true,
        proof_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v".to_string()
        ],
        oracle_parity_passed: true,
        oracle_parity_evidence_refs: vec!["mettail-rho-runtime/tests/run_calculator.rs".to_string()],
        coverage_audit_passed: true,
        coverage_audit_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoRejectedCoverage.v".to_string()
        ],
        scheduler_fairness_passed: true,
        scheduler_fairness_evidence_refs: vec![
            "formal/tla/rho_machine/RhoNetScheduler.tla".to_string()
        ],
        coverage: RhoCoverageEvidence::AllRulesLowered,
    }
}

fn calculator_backend() -> PlannedRhoBackend {
    let def =
        syn::parse_str::<LanguageDef>(CALC_RUN_FRAGMENT).expect("calculator fragment must parse");
    let audit_policy = support::strict_evidence_audit_policy();
    let plan =
        plan_rho_default_backend_with_evidence_audit(&def, passing_evidence(), &audit_policy)
            .expect("all calculator Int scalar ops must pass the Rho-default gate");
    assert_eq!(
        plan.lowering.lowered,
        vec![
            "AddInt", "SubInt", "MulInt", "DivInt", "ModInt", "Neg", "EqInt", "NeInt", "LtInt",
            "GtInt", "LtEqInt", "GtEqInt", "EqBool", "NeBool", "LtBool", "GtBool", "LtEqBool",
            "GtEqBool", "EqStr", "NeStr", "LtStr", "GtStr", "LtEqStr", "GtEqStr", "And", "Or",
            "Not", "Concat", "AddStr",
        ],
        "all Int, Bool, and Str native scalar ops in the fragment must lower"
    );
    assert!(plan.lowering.rejected.is_empty(), "no rule should be rejected here");
    PlannedRhoBackend::from_plan(plan)
}

/// `@"OP"!(a, b, @"OUT")`
fn binary_call(op: &str, a: i64, b: i64) -> Par {
    RhoAstSend::binary_int_call(op, a, b, "OUT")
        .expect("binary calculator call must build")
        .par()
        .clone()
}

/// `@"OP"!(a, @"OUT")`
fn unary_call(op: &str, a: i64) -> Par {
    RhoAstSend::unary_int_call(op, a, "OUT")
        .expect("unary calculator call must build")
        .par()
        .clone()
}

/// `@"OP"!(a, b, @"OUT")` where the operands are booleans.
fn binary_bool_call(op: &str, a: bool, b: bool) -> Par {
    RhoAstSend::contract_call(op, vec![RhoAstLiteral::Bool(a), RhoAstLiteral::Bool(b)], "OUT")
        .expect("binary Bool calculator call must build")
        .par()
        .clone()
}

/// `@"OP"!(a, @"OUT")` where the operand is a boolean.
fn unary_bool_call(op: &str, a: bool) -> Par {
    RhoAstSend::contract_call(op, vec![RhoAstLiteral::Bool(a)], "OUT")
        .expect("unary Bool calculator call must build")
        .par()
        .clone()
}

/// `@"OP"!(a, b, @"OUT")` where the operands are strings.
fn binary_string_call(op: &str, a: &str, b: &str) -> Par {
    RhoAstSend::contract_call(
        op,
        vec![RhoAstLiteral::String(a.to_string()), RhoAstLiteral::String(b.to_string())],
        "OUT",
    )
    .expect("binary Str calculator call must build")
    .par()
    .clone()
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
    assert!(
        backend
            .evidence_refs()
            .iter()
            .any(|evidence_ref| evidence_ref
                == "formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v"),
        "planned runtime backend must expose flip-gate evidence refs for metadata"
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

#[tokio::test]
async fn lowered_calculator_bool_ops_compute_correctly_on_rho_runtime() {
    let backend = calculator_backend();

    let int_predicates: &[(&str, i64, i64, bool)] = &[
        ("EqInt", 2, 2, true),
        ("EqInt", 2, 3, false),
        ("NeInt", 2, 3, true),
        ("NeInt", 2, 2, false),
        ("LtInt", 2, 3, true),
        ("LtInt", 3, 2, false),
        ("GtInt", 3, 2, true),
        ("GtInt", 2, 3, false),
        ("LtEqInt", 2, 2, true),
        ("LtEqInt", 3, 2, false),
        ("GtEqInt", 3, 3, true),
        ("GtEqInt", 2, 3, false),
    ];
    for &(op, a, b, expected) in int_predicates {
        let call = binary_call(op, a, b);
        let report = backend
            .run_with_call_and_observe_bools(&call, "OUT")
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

    let bool_cases: &[(&str, bool, bool, bool)] = &[
        ("EqBool", true, true, true),
        ("EqBool", true, false, false),
        ("NeBool", true, false, true),
        ("NeBool", false, false, false),
        ("LtBool", false, true, true),
        ("LtBool", true, false, false),
        ("GtBool", true, false, true),
        ("GtBool", false, true, false),
        ("LtEqBool", false, false, true),
        ("LtEqBool", true, false, false),
        ("GtEqBool", true, true, true),
        ("GtEqBool", false, true, false),
        ("And", true, true, true),
        ("And", true, false, false),
        ("Or", false, true, true),
    ];
    for &(op, a, b, expected) in bool_cases {
        let call = binary_bool_call(op, a, b);
        let report = backend
            .run_with_call_and_observe_bools(&call, "OUT")
            .await
            .unwrap_or_else(|e| panic!("{op}({a},{b}) failed to run: {e}"));
        assert_eq!(report.values, vec![expected], "{op}({a}, {b}) on RhoRuntime");
        assert_eq!(report.membership_fingerprint(), BTreeSet::from([expected]));
        assert_eq!(report.multiplicity_fingerprint(), BTreeMap::from([(expected, 1_usize)]));
    }

    let call = unary_bool_call("Not", true);
    let report = backend
        .run_with_call_and_observe_bools(&call, "OUT")
        .await
        .unwrap_or_else(|e| panic!("Not(true) failed to run: {e}"));
    assert_eq!(report.values, vec![false], "Not(true) on RhoRuntime");
    assert_eq!(report.membership_fingerprint(), BTreeSet::from([false]));
    assert_eq!(report.multiplicity_fingerprint(), BTreeMap::from([(false, 1_usize)]));

    let string_predicates: &[(&str, &str, &str, bool)] = &[
        ("EqStr", "rho", "rho", true),
        ("EqStr", "rho", "net", false),
        ("NeStr", "rho", "net", true),
        ("NeStr", "rho", "rho", false),
        ("LtStr", "alpha", "beta", true),
        ("LtStr", "beta", "alpha", false),
        ("GtStr", "beta", "alpha", true),
        ("GtStr", "alpha", "beta", false),
        ("LtEqStr", "same", "same", true),
        ("LtEqStr", "beta", "alpha", false),
        ("GtEqStr", "same", "same", true),
        ("GtEqStr", "alpha", "beta", false),
    ];
    for &(op, left, right, expected) in string_predicates {
        let call = binary_string_call(op, left, right);
        let report = backend
            .run_with_call_and_observe_bools(&call, "OUT")
            .await
            .unwrap_or_else(|e| panic!("{op}({left:?},{right:?}) failed to run: {e}"));
        assert_eq!(report.values, vec![expected], "{op}({left:?}, {right:?}) on RhoRuntime");
        assert_eq!(report.membership_fingerprint(), BTreeSet::from([expected]));
        assert_eq!(report.multiplicity_fingerprint(), BTreeMap::from([(expected, 1_usize)]));
    }
}

#[tokio::test]
async fn lowered_calculator_string_ops_compute_correctly_on_rho_runtime() {
    let backend = calculator_backend();

    let cases: &[(&str, &str, &str, &str)] = &[
        ("Concat", "hello", " world", "hello world"),
        ("Concat", "", "tail", "tail"),
        ("Concat", "head", "", "head"),
        ("AddStr", "rho", "net", "rhonet"),
        ("AddStr", "", "tail", "tail"),
    ];
    for &(op, left, right, expected) in cases {
        let call = binary_string_call(op, left, right);
        let report = backend
            .run_with_call_and_observe_strings(&call, "OUT")
            .await
            .unwrap_or_else(|e| panic!("{op}({left:?},{right:?}) failed to run: {e}"));
        assert_eq!(report.boundary, RhoExecutionBoundary::PlannedDefaultBackend);
        assert_eq!(report.artifact_kind, RhoArtifactKind::NormalizedAst);
        assert_eq!(report.channel, "OUT");
        assert_eq!(report.values, vec![expected.to_string()]);
        assert_eq!(report.observed_count(), 1);
        assert_eq!(report.membership_fingerprint(), BTreeSet::from([expected.to_string()]));
        assert_eq!(
            report.multiplicity_fingerprint(),
            BTreeMap::from([(expected.to_string(), 1_usize)])
        );
    }
}
