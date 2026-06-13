//! AST-first rhocalc lowering into the Rho machine.
//!
//! The examples are written as rhocalc source for readability, parsed by the
//! MeTTaIL/WPDA parser, and lowered directly to normalized `rhoapi::Par`.
//! Rholang source text is not generated or parsed on this path.

use std::sync::Arc;

use mettail_languages::rhocalc::{Bag, Int, List, Map, Proc, Str};
use mettail_rho_runtime::{
    lower_rhocalc_proc, run_normalized_par_for_oracle,
    run_normalized_par_for_oracle_and_read_strings, RhocalcAstLowerError,
};
use mettail_runtime::clear_var_cache;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::Par;

fn parse_lower(source: &str) -> Par {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rhocalc WPDA parse failed for {source:?}: {err:?}"));
    lower_rhocalc_proc(&proc)
        .unwrap_or_else(|err| panic!("rhocalc AST lowering failed for {source:?}: {err:?}"))
}

async fn read_strings(source: &str) -> Vec<String> {
    let par = parse_lower(source);
    let mut values = run_normalized_par_for_oracle_and_read_strings(&par, "OUT")
        .await
        .unwrap_or_else(|err| panic!("lowered rhocalc execution failed for {source:?}: {err}"));
    values.sort();
    values
}

#[tokio::test]
async fn single_channel_comm_executes_payload_process() {
    let source = r#"{ (@("c")?x).{*(x)} | @("c")!(@("OUT")!("p")) }"#;

    assert_eq!(read_strings(source).await, vec!["p".to_string()]);
}

#[tokio::test]
async fn multi_channel_comm_runs_as_one_atomic_join() {
    let source = r#"{
        (@("left")?x,@("right")?y).{{*(x)|*(y)}}
        | @("left")!(@("OUT")!("p"))
        | @("right")!(@("OUT")!("q"))
    }"#;

    assert_eq!(read_strings(source).await, vec!["p".to_string(), "q".to_string()]);
}

#[tokio::test]
async fn received_name_can_be_reused_as_channel() {
    let source = r#"{
        (@("c")?x).{x!(@("OUT")!("routed"))}
        | @("c")!(*(@("sink")))
        | (@("sink")?y).{*(y)}
    }"#;

    assert_eq!(read_strings(source).await, vec!["routed".to_string()]);
}

#[tokio::test]
async fn drop_of_quoted_process_executes_without_source_generation() {
    let source = r#"*(@(@("OUT")!("p")))"#;

    assert_eq!(read_strings(source).await, vec!["p".to_string()]);
}

#[tokio::test]
async fn new_name_scope_lowers_to_private_rho_binding() {
    let source = r#"new(x)in{x!(@("OUT")!("private"))}"#;
    let par = parse_lower(source);

    run_normalized_par_for_oracle(&par)
        .await
        .unwrap_or_else(|err| panic!("lowered new-scope rhocalc failed: {err}"));
    assert!(
        run_normalized_par_for_oracle_and_read_strings(&par, "OUT")
            .await
            .expect("rerun for OUT observation")
            .is_empty(),
        "private new-name datum must not leak to OUT"
    );
}

#[test]
fn lowered_comm_is_normalized_ast_with_receive_and_send_members() {
    let par = parse_lower(r#"{ (@("c")?x).{*(x)} | @("c")!(@("OUT")!("p")) }"#);

    assert_eq!(par.receives.len(), 1);
    assert_eq!(par.sends.len(), 1);
    assert!(par.exprs.is_empty());
    assert!(par.matches.is_empty());
}

#[test]
fn list_literal_lowers_to_elist_ast_preserving_order() {
    let proc = Proc::CastList(Arc::new(List::ListLit(vec![
        Proc::CastInt(Arc::new(Int::NumLit(1))),
        Proc::CastStr(Arc::new(Str::StringLit("two".to_string()))),
    ])));

    let par = lower_rhocalc_proc(&proc).expect("list literal should lower");
    let ExprInstance::EListBody(list) = only_expr(&par) else {
        panic!("expected EListBody");
    };

    assert_eq!(list.ps.len(), 2);
    assert!(matches!(only_expr(&list.ps[0]), ExprInstance::GInt(1)));
    assert!(matches!(only_expr(&list.ps[1]), ExprInstance::GString(value) if value == "two"));
}

#[test]
fn map_literal_lowers_to_emap_ast() {
    let mut entries = mettail_runtime::HashMapLit::new();
    entries.insert(
        Proc::CastStr(Arc::new(Str::StringLit("key".to_string()))),
        Proc::CastInt(Arc::new(Int::NumLit(7))),
    );
    let proc = Proc::CastMap(Arc::new(Map::MapLit(entries)));

    let par = lower_rhocalc_proc(&proc).expect("map literal should lower");
    let ExprInstance::EMapBody(map) = only_expr(&par) else {
        panic!("expected EMapBody");
    };

    assert_eq!(map.kvs.len(), 1);
    let pair = &map.kvs[0];
    assert!(matches!(
        only_expr(pair.key.as_ref().expect("map key")),
        ExprInstance::GString(value) if value == "key"
    ));
    assert!(matches!(
        only_expr(pair.value.as_ref().expect("map value")),
        ExprInstance::GInt(7)
    ));
}

#[test]
fn bag_literal_remains_fail_closed_without_exact_rholang_multiset_node() {
    let proc = Proc::CastBag(Arc::new(Bag::BagLit(mettail_runtime::HashBag::new())));

    assert_eq!(
        lower_rhocalc_proc(&proc),
        Err(RhocalcAstLowerError::UnsupportedProc("bag literal process"))
    );
}

fn only_expr(par: &Par) -> &ExprInstance {
    assert_eq!(par.exprs.len(), 1, "expected exactly one expression");
    par.exprs[0]
        .expr_instance
        .as_ref()
        .expect("expression instance")
}
