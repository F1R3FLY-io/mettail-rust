//! # mettail-rho-codegen — COMPILE-TIME GSLT → Rholang VM lowering
//!
//! MeTTaIL is the COMPILER; f1r3node-rust's Rho machine is the parallel RUNTIME.
//! This crate lowers a MeTTaIL `LanguageDef` into a **parallel-optimized Rholang
//! VM**. The `LanguageDef` is the structured value produced by the `language!`
//! macro expansion; reader-facing display strings and pretty-printed examples
//! are never parsed back into compiler input. The lowering emits three
//! artifacts:
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
//! `plan_rho_default_backend` then ties that lowering to exact coverage,
//! artifact-validation, and deadlock gates before returning the concrete backend
//! plan. Generic call-by-need admission is bounded
//! by explicit lookahead and heap budgets, and the memoized-thunk slice keeps a
//! verified contract/state/memo topology while `CallByNeedThunkSpec`
//! parameterizes generated-language values, evaluation markers, and observation
//! channels. The builder emits a normalized `rhoapi::Par` `RhoProgram` with a
//! call-by-need validation profile, then wraps it in `CallByNeedThunkPlan` after
//! budget admission and validation before runtime execution. The
//! totality-or-explicit-rejection proof is
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

/// Reconstruct a generated language's exact macro-time augmented `LanguageDef`
/// from its `LanguageMetadata::definition_source()`.
///
/// Re-exported from `mettail_ast` so backend-planning callers can rebuild the
/// real augmented definition (composition + auto-injection) that a generated
/// language's `definition_fingerprint()` was computed over — instead of
/// fingerprint-spoofing fragment shims. See
/// [`mettail_ast::auto_inject::reconstruct_language_def`] for exactness scope.
pub use mettail_ast::auto_inject::reconstruct_language_def;

pub mod ast;
pub mod backend;
pub mod deadlock;
pub mod flip;
pub mod guard_quality;
pub mod invocation;
pub mod lower;
pub mod need;
pub mod validate;
pub use ast::{RhoAstBuildError, RhoAstLiteral, RhoAstSend};
pub use backend::{
    audit_rho_default_backend, classify_rejected_rules, collect_guard_obligations,
    plan_rho_default_backend, RhoCoverageEvidence, RhoDefaultBackendAudit, RhoDefaultBackendPlan,
    RhoDefaultBackendPlanError, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
    RhoGuardDisposition, RhoGuardDispositionDiagnostic, RhoGuardDispositionKind,
    RhoGuardObligation, RhoGuardObligationKind, RhoRejectedRuleClassification,
    RhoRejectedRuleClassificationReason, RhoRejectedRuleDisposition,
    RhoRejectedRuleDispositionDiagnostic, RhoRejectedRuleDispositionKind,
};
pub use deadlock::{
    analyze_channel_deadlocks, ChannelDeadlockDiagnostic, ChannelDeadlockReport, ChannelNetwork,
    ContractFlow,
};
pub use flip::{decide_rho_flip, RhoFlipBlocker, RhoFlipDecision, RhoFlipGates};
pub use invocation::{
    plan_scalar_invocations, RhoScalarContractInvocation, RhoScalarInvocationOperand,
    RhoScalarInvocationPlan, RhoScalarInvocationPlanError,
};
pub use lower::{
    lower_language_def, RhoArtifactKind, RhoAstProgram, RhoAstValidationProfile, RhoLowering,
    RhoProgram, RhoScalarContractAbi, RhoScalarContractShape, RhoScalarType,
};
pub use need::{
    admit_call_by_need_force, build_call_by_need_thunk_ast, build_call_by_need_thunk_ast_from_spec,
    build_call_by_need_thunk_program, build_call_by_need_thunk_program_from_spec,
    plan_call_by_need_thunk, plan_call_by_need_thunk_with_spec, CallByNeedAdmission,
    CallByNeedBudget, CallByNeedBudgetBlocker, CallByNeedForce, CallByNeedForceAdmissionRecord,
    CallByNeedInitialState, CallByNeedThunkAst, CallByNeedThunkPlan, CallByNeedThunkPlanError,
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
        types {
            Proc
            ![i32] as Int
            ![bool] as Bool
            ![str] as Str
            ![f64] as Float
            ![mettail_runtime::CanonicalBigInt] as BigInt
        }
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

    const RENAMED_NATIVE_SCALAR_FRAGMENT: &str = r#"
        name: RenamedScalarFrag,
        types {
            ![i32] as Number
            ![bool] as Truth
            ![str] as Text
        }
        terms {
            AddNumber . a:Number, b:Number |- a "+" b : Number ;
            EqNumber . a:Number, b:Number |- a "==" b : Truth ;
            AndTruth . a:Truth, b:Truth |- a "and" b : Truth ;
            AddText . a:Text, b:Text |- a "+" b : Text ;
        }
    "#;

    const SCALAR_NAMED_STRUCTURAL_FRAGMENT: &str = r#"
        name: ScalarNamedStructuralFrag,
        types {
            Int
            Bool
            Str
        }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
            AndBool . a:Bool, b:Bool |- a "and" b : Bool ;
            AddStr . a:Str, b:Str |- a "+" b : Str ;
        }
    "#;

    fn parse_fragment() -> LanguageDef {
        syn::parse_str::<LanguageDef>(CALC_SCALAR_FRAGMENT)
            .expect("calculator scalar fragment must parse as a LanguageDef")
    }

    fn binary_abi(
        label: &str,
        left: RhoScalarType,
        right: RhoScalarType,
        result: RhoScalarType,
    ) -> RhoScalarContractAbi {
        RhoScalarContractAbi {
            rule_label: label.to_string(),
            shape: RhoScalarContractShape::BinaryInfix { left, right, result },
        }
    }

    fn unary_abi(
        label: &str,
        argument: RhoScalarType,
        result: RhoScalarType,
    ) -> RhoScalarContractAbi {
        RhoScalarContractAbi {
            rule_label: label.to_string(),
            shape: RhoScalarContractShape::UnaryPrefix { argument, result },
        }
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
    fn scalar_lowering_reports_generated_contract_abi_inventory() {
        use RhoScalarType::{Bool, Int, Str};

        let def = parse_fragment();
        let out = lower_language_def(&def);
        let abi_labels: Vec<_> = out
            .scalar_contract_abi
            .iter()
            .map(|abi| abi.rule_label.as_str())
            .collect();
        let lowered_labels: Vec<_> = out.lowered.iter().map(String::as_str).collect();

        assert_eq!(
            abi_labels, lowered_labels,
            "ABI inventory must stay in exact lowered-contract order"
        );
        assert_eq!(
            out.scalar_contract_abi,
            vec![
                binary_abi("AddInt", Int, Int, Int),
                binary_abi("SubInt", Int, Int, Int),
                binary_abi("MulInt", Int, Int, Int),
                binary_abi("DivInt", Int, Int, Int),
                binary_abi("ModInt", Int, Int, Int),
                unary_abi("Neg", Int, Int),
                binary_abi("EqInt", Int, Int, Bool),
                binary_abi("NeInt", Int, Int, Bool),
                binary_abi("LtInt", Int, Int, Bool),
                binary_abi("GtInt", Int, Int, Bool),
                binary_abi("LtEqInt", Int, Int, Bool),
                binary_abi("GtEqInt", Int, Int, Bool),
                binary_abi("EqBool", Bool, Bool, Bool),
                binary_abi("NeBool", Bool, Bool, Bool),
                binary_abi("LtBool", Bool, Bool, Bool),
                binary_abi("GtBool", Bool, Bool, Bool),
                binary_abi("LtEqBool", Bool, Bool, Bool),
                binary_abi("GtEqBool", Bool, Bool, Bool),
                binary_abi("EqStr", Str, Str, Bool),
                binary_abi("NeStr", Str, Str, Bool),
                binary_abi("LtStr", Str, Str, Bool),
                binary_abi("GtStr", Str, Str, Bool),
                binary_abi("LtEqStr", Str, Str, Bool),
                binary_abi("GtEqStr", Str, Str, Bool),
                binary_abi("And", Bool, Bool, Bool),
                binary_abi("Or", Bool, Bool, Bool),
                unary_abi("Not", Bool, Bool),
                binary_abi("Concat", Str, Str, Str),
                binary_abi("AddStr", Str, Str, Str),
            ],
            "contract ABI must be generated from typed lowering, including Str + Str -> Str"
        );
        for abi in &out.scalar_contract_abi {
            assert_eq!(
                abi.return_channel_position(),
                abi.operand_count(),
                "return channel must be last in the generated scalar-contract ABI"
            );
            assert_eq!(
                abi.formal_count(),
                abi.operand_count() + 1,
                "generated scalar contracts receive operands plus one return channel"
            );
        }
    }

    #[test]
    fn scalar_lowering_uses_native_type_inventory_not_category_names() {
        use RhoScalarType::{Bool, Int, Str};

        let def = syn::parse_str::<LanguageDef>(RENAMED_NATIVE_SCALAR_FRAGMENT)
            .expect("renamed native scalar fragment must parse as a LanguageDef");
        let out = lower_language_def(&def);
        assert_eq!(
            out.lowered,
            vec!["AddNumber", "EqNumber", "AndTruth", "AddText"],
            "native scalar categories should lower even when category names are domain-specific"
        );
        assert!(
            out.rejected.is_empty(),
            "renamed native scalar rules must not be rejected by a category-name whitelist"
        );
        assert_eq!(
            out.scalar_contract_abi,
            vec![
                binary_abi("AddNumber", Int, Int, Int),
                binary_abi("EqNumber", Int, Int, Bool),
                binary_abi("AndTruth", Bool, Bool, Bool),
                binary_abi("AddText", Str, Str, Str),
            ],
            "ABI inventory must also follow native payload families, not category names"
        );
    }

    #[test]
    fn scalar_named_structural_categories_do_not_lower_as_native_scalars() {
        let def = syn::parse_str::<LanguageDef>(SCALAR_NAMED_STRUCTURAL_FRAGMENT)
            .expect("structural scalar-named fragment must parse as a LanguageDef");
        let out = lower_language_def(&def);
        assert!(
            out.lowered.is_empty(),
            "category names alone must not authorize Rho scalar lowering"
        );
        assert_eq!(
            out.rejected,
            vec!["AddInt", "AndBool", "AddStr"],
            "structural categories named like scalars must be surfaced as rejected rules"
        );
        assert!(
            out.scalar_contract_abi.is_empty(),
            "rejected structural scalar-looking rules must not receive callable Rho ABI entries"
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
                coverage_passed: true,
                artifact_validated: true,
            },
            &out.deadlock_report,
            Vec::new(),
        );

        assert!(
            decision.can_flip_to_rho(),
            "the deadlock side of scalar lowering should pass when coverage/artifact gates pass: {:?}",
            decision.blockers
        );
    }
}
