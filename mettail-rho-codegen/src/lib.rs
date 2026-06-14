//! # mettail-rho-codegen — COMPILE-TIME GSLT → Rholang VM lowering
//!
//! MeTTaIL is the COMPILER; f1r3node-rust's Rho machine is the parallel RUNTIME.
//! This crate lowers a MeTTaIL `LanguageDef` into a **parallel-optimized Rholang
//! VM** — three artifacts:
//!  1. reduction rules as `Par` contracts (the COMM family),
//!  2. native `Vec<Definition>` system processes (HOL `fold`/`step`),
//!  3. the `OslfResourceLogic` adapter wiring (see `mettail-rho-adapter`).
//!
//! Rule classification drives the lowering: COMM/interaction → RSpace
//! produce/consume; structural/congruence → par-context (`eval_par` — the AMBIENT
//! structural rule, emit `Par`, never fork); HOL `fold`/`step` → native
//! `Definition` handler; equations → compile-time e-graph; injection/cast → `Par`
//! wrapper. The e-graph / WTA / decision-tree remain **compile-time analyses**
//! that GENERATE indexing + ordering + recognition plugging into f1r3node's
//! existing matcher/join/lock/`check_commit` — speed + parallelism without
//! forking the runtime.
//!
//! ## Dependency direction (STRICTLY one-way)
//! Depends ONE-WAY on f1r3node-rust; never the reverse (proven in
//! `formal/rocq/rho_bridge/theories/BridgeInertness.v`; enforced by the host
//! guard test `mettail_rust_is_not_a_cargo_dependency`).
//!
//! ## Status
//! Integrated scalar lowering plus Rho-default backend planning.
//! `lower_language_def` emits normalized Rholang AST (`rhoapi::Par`) for the
//! supported native scalar subset, records every unsupported rule as an explicit
//! rejection, and keeps Rholang-looking text only as a reader/debug annotation.
//! `plan_rho_default_backend` then ties that lowering to proof, oracle, coverage,
//! artifact-validation, scheduler-fairness, and deadlock evidence before
//! returning the concrete backend plan. Generic call-by-need admission is bounded
//! by explicit lookahead and heap budgets, and the memoized-thunk slice keeps a
//! verified contract/state/memo topology while `CallByNeedThunkSpec`
//! parameterizes generated-language values, evaluation markers, and observation
//! channels. The builder emits a normalized `rhoapi::Par` `RhoProgram` with a
//! call-by-need validation profile, then wraps it in `CallByNeedThunkPlan` after
//! budget admission, validation, and evidence-reference checks before runtime
//! execution. The totality-or-explicit-rejection proof is
//! `formal/rocq/rho_bridge/theories/RhoLoweringTotalOrRejects.v`; the flip-gate
//! proof is `formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v`.

#![forbid(unsafe_code)]

/// Stable Rho AST ABI tag for rhocalc bag payloads.
///
/// Rholang has native list, tuple, set, and map bodies, but no native multiset
/// expression body. MeTTaIL/rhocalc bags therefore lower as a tagged list:
/// `[private_tag, [[value, count], ...]]`, where `private_tag` is constructed
/// by F1r3node's `GPrivateBuilder::new_par_from_string(RHOCALC_BAG_ABI_TAG)`.
/// The tag is not raw UTF-8 bytes; it must match the host private-name builder
/// so codegen and runtime observation decode the same nominal bag ABI.
pub const RHOCALC_BAG_ABI_TAG: &str = "mettail.rhocalc.bag.v1";

pub mod ast;
pub mod backend;
pub mod deadlock;
pub mod flip;
pub mod lower;
pub mod need;
pub mod validate;
pub use ast::{RhoAstBuildError, RhoAstLiteral, RhoAstSend};
pub use backend::{
    classify_rejected_rules, collect_guard_obligations, plan_rho_default_backend,
    plan_rho_default_backend_with_evidence_audit, RhoCoverageEvidence, RhoDefaultBackendEvidence,
    RhoDefaultBackendEvidenceGate, RhoDefaultBackendPlan, RhoDefaultBackendPlanError,
    RhoEvidenceRefAuditDiagnostic, RhoEvidenceRefAuditPolicy, RhoGateEvidenceDiagnostic,
    RhoGuardCoverageEvidence, RhoGuardDisposition, RhoGuardDispositionDiagnostic,
    RhoGuardDispositionKind, RhoGuardObligation, RhoGuardObligationKind,
    RhoRejectedRuleClassification, RhoRejectedRuleClassificationReason, RhoRejectedRuleDisposition,
    RhoRejectedRuleDispositionDiagnostic, RhoRejectedRuleDispositionKind,
};
pub use deadlock::{
    analyze_channel_deadlocks, ChannelDeadlockDiagnostic, ChannelDeadlockReport, ChannelNetwork,
    ContractFlow,
};
pub use flip::{decide_rho_flip, RhoFlipBlocker, RhoFlipDecision, RhoFlipGates};
pub use lower::{
    lower_language_def, RhoArtifactKind, RhoAstProgram, RhoAstValidationProfile, RhoLowering,
    RhoProgram,
};
pub use need::{
    admit_call_by_need_force, build_call_by_need_thunk_ast, build_call_by_need_thunk_ast_from_spec,
    build_call_by_need_thunk_program, build_call_by_need_thunk_program_from_spec,
    plan_call_by_need_thunk, plan_call_by_need_thunk_with_spec, CallByNeedAdmission,
    CallByNeedBudget, CallByNeedBudgetBlocker, CallByNeedForce, CallByNeedForceAdmissionRecord,
    CallByNeedInitialState, CallByNeedPlanEvidence, CallByNeedPlanEvidenceDiagnostic,
    CallByNeedPlanEvidenceGate, CallByNeedThunkAst, CallByNeedThunkPlan, CallByNeedThunkPlanError,
    CallByNeedThunkSpec, CallByNeedThunkSpecError,
};
pub use validate::{
    validate_rho_program, RhoValidationError, ValidatedRhoAstProgram, ValidatedRhoProgram,
};

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::LanguageDef;
    use models::rhoapi::expr::ExprInstance;
    use models::rhoapi::var::VarInstance;
    use models::rhoapi::Par;

    // The calculator's scalar-operator fragment, by its real rule names. Body-less
    // (the lowering keys on the concrete-syntax operator + operand types, not the
    // `![…]` eval body), so this parses by `syn::parse_str` without validation.
    // First block = Rholang-native scalar ops (lower to contracts); last block =
    // out-of-subset (`^`/`bitand` have no Rholang op; `!` is postfix;
    // `AddFloat`/`AddBigInt` have non-native operands) and MUST be rejected,
    // never silently dropped.
    const CALC_SCALAR_FRAGMENT: &str = r#"
        name: CalcScalarFrag,
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
            PowInt . a:Int, b:Int |- a "^" b : Int ;
            BitAndInt . a:Int, b:Int |- a "bitand" b : Int ;
            Fact . a:Int |- a "!" : Int ;
            AddFloat . a:Float, b:Float |- a "+" b : Float ;
            AddBigInt . a:BigInt, b:BigInt |- a "+" b : BigInt ;
        }
    "#;

    fn parse_fragment() -> LanguageDef {
        syn::parse_str::<LanguageDef>(CALC_SCALAR_FRAGMENT)
            .expect("calculator scalar fragment must parse as a LanguageDef")
    }

    fn gstring(par: &Par) -> Option<&str> {
        match par.exprs.as_slice() {
            [expr] => match expr.expr_instance.as_ref()? {
                ExprInstance::GString(s) => Some(s.as_str()),
                _ => None,
            },
            _ => None,
        }
    }

    fn bound_index(par: &Par) -> Option<i32> {
        match par.exprs.as_slice() {
            [expr] => match expr.expr_instance.as_ref()? {
                ExprInstance::EVarBody(var) => match var.v.as_ref()?.var_instance.as_ref()? {
                    VarInstance::BoundVar(index) => Some(*index),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    #[test]
    fn lowers_supported_scalar_ops_and_rejects_the_rest() {
        let def = parse_fragment();
        let out = lower_language_def(&def);
        assert_eq!(
            out.lowered,
            vec![
                "AddInt", "SubInt", "MulInt", "DivInt", "ModInt", "Neg", "EqInt", "NeInt", "LtInt",
                "GtInt", "LtEqInt", "GtEqInt", "EqBool", "NeBool", "LtBool", "GtBool", "LtEqBool",
                "GtEqBool", "EqStr", "NeStr", "LtStr", "GtStr", "LtEqStr", "GtEqStr", "And", "Or",
                "Not", "Concat", "AddStr",
            ],
            "Rholang-native scalar ops must lower to contracts"
        );
        assert_eq!(
            out.rejected,
            vec!["PowInt", "BitAndInt", "Fact", "AddFloat", "AddBigInt"],
            "out-of-subset rules must be rejected (surfaced), never silently dropped"
        );
    }

    #[test]
    fn lowering_is_total_and_disjoint() {
        // Miss nothing: every term rule is accounted for in exactly one of
        // lowered / rejected (the operational image of RhoLoweringTotalOrRejects.v).
        let def = parse_fragment();
        let out = lower_language_def(&def);
        assert_eq!(
            out.lowered.len() + out.rejected.len(),
            def.terms.len(),
            "every rule must be classified exactly once (total)"
        );
        for name in &out.lowered {
            assert!(!out.rejected.contains(name), "lowered/rejected must be disjoint: {name}");
        }
    }

    #[test]
    fn lowering_emits_normalized_ast_not_source_text() {
        let def = parse_fragment();
        let out = lower_language_def(&def);
        let par = out
            .ast_par()
            .expect("current Rho artifact must be normalized Par");
        assert_eq!(
            par.receives.len(),
            out.lowered.len(),
            "each lowered rule must install one persistent contract receive"
        );
        assert!(
            par.sends.is_empty(),
            "the lowered language artifact installs contracts; calls are supplied by the runtime"
        );
        assert!(
            out.text_annotation().contains("contract @\"AddInt\""),
            "annotation remains available for readers/debugging"
        );
    }

    #[test]
    fn binary_contract_uses_operands_first_return_channel_last_abi() {
        let def = parse_fragment();
        let out = lower_language_def(&def);
        let add = out
            .ast_par()
            .expect("current Rho artifact must be normalized Par")
            .receives
            .iter()
            .find(|receive| {
                receive
                    .binds
                    .first()
                    .and_then(|bind| bind.source.as_ref())
                    .and_then(gstring)
                    == Some("AddInt")
            })
            .expect("AddInt contract must be present");

        assert!(add.persistent, "lowered contracts are reusable services");
        assert_eq!(add.bind_count, 3);
        let bind = add
            .binds
            .first()
            .expect("contract must have one receive bind");
        assert_eq!(bind.free_count, 3);
        assert_eq!(bind.patterns.len(), 3);

        let body = add.body.as_ref().expect("contract must have a body");
        let send = body.sends.first().expect("body must send the result");
        assert_eq!(
            bound_index(send.chan.as_ref().expect("result send must have a channel")),
            Some(0),
            "the last formal `ret` is the newest binding and therefore de Bruijn 0"
        );
        let result = send.data.first().expect("result send must carry one datum");
        let expr = result
            .exprs
            .first()
            .expect("result datum must be an expression");
        match expr
            .expr_instance
            .as_ref()
            .expect("result expression must be present")
        {
            ExprInstance::EPlusBody(add_expr) => {
                assert_eq!(
                    bound_index(add_expr.p1.as_ref().expect("lhs must be present")),
                    Some(2),
                    "first operand formal maps to oldest binding"
                );
                assert_eq!(
                    bound_index(add_expr.p2.as_ref().expect("rhs must be present")),
                    Some(1),
                    "second operand formal maps to middle binding"
                );
            },
            other => panic!("AddInt must lower to EPlusBody, got {other:?}"),
        }
    }

    #[test]
    fn string_plus_lowers_to_rholang_concat_not_integer_plus() {
        let def = parse_fragment();
        let out = lower_language_def(&def);
        assert!(
            out.text_annotation()
                .contains("contract @\"AddStr\"(@a, @b, ret) = { ret!(a ++ b) }"),
            "the reader annotation must show the Rholang string-concat artifact"
        );

        let add_str = out
            .ast_par()
            .expect("current Rho artifact must be normalized Par")
            .receives
            .iter()
            .find(|receive| {
                receive
                    .binds
                    .first()
                    .and_then(|bind| bind.source.as_ref())
                    .and_then(gstring)
                    == Some("AddStr")
            })
            .expect("AddStr contract must be present");
        let result = add_str
            .body
            .as_ref()
            .and_then(|body| body.sends.first())
            .and_then(|send| send.data.first())
            .and_then(|datum| datum.exprs.first())
            .and_then(|expr| expr.expr_instance.as_ref())
            .expect("AddStr must return one expression");
        assert!(
            matches!(result, ExprInstance::EPlusPlusBody(_)),
            "Str '+' must lower to Rholang EPlusPlusBody, got {result:?}"
        );
    }

    #[test]
    fn scalar_lowering_emits_clean_deadlock_report() {
        let def = parse_fragment();
        let out = lower_language_def(&def);
        assert!(
            out.deadlock_report.no_new_deadlocks(),
            "exported scalar service contracts should not introduce channel deadlocks: {:?}",
            out.deadlock_report.diagnostics
        );
        for lowered in &out.lowered {
            assert!(
                out.deadlock_report.external_channels.contains(lowered),
                "lowered scalar service must be marked as an external entry channel: {lowered}"
            );
        }
    }

    #[test]
    fn scalar_lowering_deadlock_report_allows_flip_when_coverage_gate_is_external() {
        let def = parse_fragment();
        let out = lower_language_def(&def);
        let decision = decide_rho_flip(
            RhoFlipGates {
                proofs_passed: true,
                oracle_parity_passed: true,
                coverage_passed: true,
                artifact_validated: true,
                scheduler_fairness_passed: true,
            },
            &out.deadlock_report,
        );

        assert!(
            decision.can_flip_to_rho(),
            "the deadlock side of scalar lowering should pass when proof/oracle/coverage gates pass: {:?}",
            decision.blockers
        );
    }
}
