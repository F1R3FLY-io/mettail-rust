//! E3 — run a generated **nested** native-fold scalar expression as a Rholang dataflow on a REAL
//! in-memory f1r3node-rust `RhoRuntime`, and assert the computed result.
//!
//! Where `run_calculator.rs` exercises the single-op path (`@"AddInt"!(2,3,@"OUT")` → 5), this
//! exercises the E3 dataflow assembler ([`mettail_rholang_codegen::build_dataflow_call_par`]): a
//! NESTED expression like `(2+3)*(4-1)` compiles to two producer sends to intermediate channels
//! `@"__e3_c0"`/`@"__e3_c1"` plus a multi-bind JOIN that calls `@"MulInt"` to `@"OUT"`. Composed
//! with the SAME persistent scalar contracts (via `par.append`), the runtime reduces the whole
//! dataflow to quiescence — each contract publishes its result on the next channel by pure data
//! dependency — and the observed `@"OUT"` value equals the term's denotation. This is the per-op
//! differential oracle (rho contract ≡ Ascent/Dovetail semantics) lifted to a multi-node graph.
//!
//! The node lists here are hand-built (the per-language WALK that produces them — the macro emitter
//! `<Lang>::rho_fold_dataflow_invocation_to` — is covered separately); this isolates the dataflow
//! ASSEMBLY + RUNTIME EXECUTION, the novel E3 surface.

use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{
    build_dataflow_call_par, plan_rho_default_backend, RhoAstLiteral, RhoCoverageEvidence,
    RhoDataflowChild, RhoDataflowNode, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::PlannedRhoBackend;

const CALC_RUN_FRAGMENT: &str = r#"
    name: CalcDataflowRun,
    types {
        Proc
        ![i64] as Int
        ![bool] as Bool
        ![str] as Str
    }
    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ;
        SubInt . a:Int, b:Int |- a "-" b : Int ;
        MulInt . a:Int, b:Int |- a "*" b : Int ;
        EqInt . a:Int, b:Int |- a "==" b : Bool ;
        Concat . a:Str, b:Str |- a "++" b : Str ;
    }
"#;

fn passing_requirements() -> RhoDefaultBackendRequirements {
    RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::AllRulesLowered,
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    }
}

fn dataflow_backend() -> PlannedRhoBackend {
    let def =
        syn::parse_str::<LanguageDef>(CALC_RUN_FRAGMENT).expect("calculator fragment must parse");
    let plan = plan_rho_default_backend(&def, passing_requirements())
        .expect("all scalar ops must pass the Rho-default gate");
    assert!(plan.lowering.rejected.is_empty(), "no rule should be rejected here");
    PlannedRhoBackend::from_plan(plan)
}

fn int(v: i64) -> RhoDataflowChild {
    RhoDataflowChild::Leaf(RhoAstLiteral::Int(v))
}

fn string(s: &str) -> RhoDataflowChild {
    RhoDataflowChild::Leaf(RhoAstLiteral::String(s.to_string()))
}

fn node(label: &str, operands: Vec<RhoDataflowChild>) -> RhoDataflowNode {
    RhoDataflowNode { label: label.to_string(), operands }
}

/// `(2+3)*(4-1)` = 15 — the flagship nested-int dataflow, end-to-end on RhoRuntime.
#[tokio::test]
async fn nested_int_expression_computes_on_rho_runtime() {
    let backend = dataflow_backend();
    let nodes = vec![
        node("AddInt", vec![int(2), int(3)]),                                   // → @"__e3_c0" = 5
        node("SubInt", vec![int(4), int(1)]),                                   // → @"__e3_c1" = 3
        node("MulInt", vec![RhoDataflowChild::Node(0), RhoDataflowChild::Node(1)]), // → @"OUT"   = 15
    ];
    let call = build_dataflow_call_par(&nodes, &RhoDataflowChild::Node(2), "OUT")
        .expect("nested dataflow must build");
    let report = backend
        .run_with_call_and_observe_ints(&call, "OUT")
        .await
        .unwrap_or_else(|e| panic!("(2+3)*(4-1) dataflow failed to run: {e}"));
    assert_eq!(report.channel, "OUT");
    assert_eq!(report.values, vec![15], "(2+3)*(4-1) = 15 on RhoRuntime");
    assert_eq!(report.observed_count(), 1, "exactly one result on OUT");
}

/// `((10-4)+1)==7` = true — a Bool-rooted dataflow over Int internal nodes.
#[tokio::test]
async fn nested_bool_rooted_expression_computes_on_rho_runtime() {
    let backend = dataflow_backend();
    let nodes = vec![
        node("SubInt", vec![int(10), int(4)]),                                  // 6
        node("AddInt", vec![RhoDataflowChild::Node(0), int(1)]),                // 7
        node("EqInt", vec![RhoDataflowChild::Node(1), int(7)]),                 // true
    ];
    let call = build_dataflow_call_par(&nodes, &RhoDataflowChild::Node(2), "OUT")
        .expect("bool-rooted dataflow must build");
    let report = backend
        .run_with_call_and_observe_bools(&call, "OUT")
        .await
        .unwrap_or_else(|e| panic!("((10-4)+1)==7 dataflow failed to run: {e}"));
    assert_eq!(report.values, vec![true], "((10-4)+1)==7 = true on RhoRuntime");
    assert_eq!(report.observed_count(), 1);
}

/// `"a"++"b"++"c"` = "abc" — a String-rooted left-nested concat dataflow.
#[tokio::test]
async fn nested_string_expression_computes_on_rho_runtime() {
    let backend = dataflow_backend();
    let nodes = vec![
        node("Concat", vec![string("a"), string("b")]),                         // "ab"
        node("Concat", vec![RhoDataflowChild::Node(0), string("c")]),           // "abc"
    ];
    let call = build_dataflow_call_par(&nodes, &RhoDataflowChild::Node(1), "OUT")
        .expect("string dataflow must build");
    let report = backend
        .run_with_call_and_observe_strings(&call, "OUT")
        .await
        .unwrap_or_else(|e| panic!("\"a\"++\"b\"++\"c\" dataflow failed to run: {e}"));
    assert_eq!(report.values, vec!["abc".to_string()], "\"a\"++\"b\"++\"c\" = abc on RhoRuntime");
    assert_eq!(report.observed_count(), 1);
}

/// A single literal (`exec 42`) → a direct `@"OUT"!(42)` (no contract), observed as 42.
#[tokio::test]
async fn single_literal_observed_directly_on_rho_runtime() {
    let backend = dataflow_backend();
    let call = build_dataflow_call_par(&[], &int(42), "OUT").expect("literal must build");
    let report = backend
        .run_with_call_and_observe_ints(&call, "OUT")
        .await
        .unwrap_or_else(|e| panic!("literal dataflow failed to run: {e}"));
    assert_eq!(report.values, vec![42], "a bare literal is observed directly");
}

/// A deep left-nested chain `((…((1+1)+1)+1…)+1)` — a multi-node dataflow whose JOINs chain through
/// many intermediate channels — reduces correctly to quiescence (no lost data, no deadlock).
#[tokio::test]
async fn deep_chain_dataflow_computes_on_rho_runtime() {
    let backend = dataflow_backend();
    // node0 = 1+1 = 2; node_i = node_{i-1} + 1 = i + 2. With 8 nodes the root (node7) = 9.
    let depth = 8;
    let mut nodes = vec![node("AddInt", vec![int(1), int(1)])];
    for i in 1..depth {
        nodes.push(node("AddInt", vec![RhoDataflowChild::Node(i - 1), int(1)]));
    }
    let root = RhoDataflowChild::Node(depth - 1);
    let call = build_dataflow_call_par(&nodes, &root, "OUT").expect("deep chain must build");
    let report = backend
        .run_with_call_and_observe_ints(&call, "OUT")
        .await
        .unwrap_or_else(|e| panic!("deep chain dataflow failed to run: {e}"));
    assert_eq!(report.values, vec![(depth as i64) + 1], "deep chain reduces to depth+1");
    assert_eq!(report.observed_count(), 1);
}
