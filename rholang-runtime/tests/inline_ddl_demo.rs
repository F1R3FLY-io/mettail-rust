#![cfg(feature = "rholang-runtime")]

use mettail_languages::rholang::Proc;
use mettail_rholang_runtime::{
    language_runtime_definitions, lower_rholang_proc,
    run_normalized_par_with_definitions_and_read_par_channels, EmptyRegistrySnapshot,
    LanguageInstallPolicy, LanguageInstallService, RholangLanguageRuntime,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{KeyValuePair, Par};
use std::collections::BTreeMap;
use std::sync::Arc;

const APPLICATION: &str = include_str!("../../demos/mettail-inline-ddl/inline-ddl.rho");

fn exact_expr(value: &Par) -> Option<&ExprInstance> {
    if !value.sends.is_empty()
        || !value.receives.is_empty()
        || !value.news.is_empty()
        || !value.matches.is_empty()
        || !value.unforgeables.is_empty()
        || !value.bundles.is_empty()
        || !value.connectives.is_empty()
        || !value.conditionals.is_empty()
    {
        return None;
    }
    let [expr] = value.exprs.as_slice() else {
        return None;
    };
    expr.expr_instance.as_ref()
}

fn exact_list(value: &Par) -> Option<&[Par]> {
    let ExprInstance::EListBody(list) = exact_expr(value)? else {
        return None;
    };
    list.remainder.is_none().then_some(list.ps.as_slice())
}

fn exact_map(value: &Par) -> Option<&[KeyValuePair]> {
    let ExprInstance::EMapBody(map) = exact_expr(value)? else {
        return None;
    };
    map.remainder.is_none().then_some(map.kvs.as_slice())
}

fn exact_string(value: &Par) -> Option<&str> {
    let ExprInstance::GString(value) = exact_expr(value)? else {
        return None;
    };
    Some(value)
}

fn map_entry<'a>(value: &'a Par, key: &str) -> Option<&'a Par> {
    exact_map(value)?.iter().find_map(|pair| {
        (pair.key.as_ref().and_then(exact_string) == Some(key))
            .then(|| pair.value.as_ref())
            .flatten()
    })
}

fn parse_status(response: &Par) -> Option<&str> {
    let result = map_entry(response, "ok")?;
    map_entry(result, "status").and_then(exact_string)
}

fn error_code(response: &Par) -> Option<&str> {
    let error = map_entry(response, "error")?;
    map_entry(error, "code").and_then(exact_string)
}

#[tokio::test]
async fn committed_application_runs_the_inline_ddl_installation_contract_end_to_end() {
    mettail_runtime::clear_var_cache();
    let service = Arc::new(LanguageInstallService::new(
        Arc::new(EmptyRegistrySnapshot),
        LanguageInstallPolicy::default(),
    ));
    let runtime = Arc::new(RholangLanguageRuntime::new(service.clone()));

    let parsed = Proc::parse_via_wpda(APPLICATION)
        .expect("the committed application parses through nouveau Rholang");
    let program = lower_rholang_proc(&parsed)
        .expect("the committed application lowers without source reconstruction");
    let outputs = run_normalized_par_with_definitions_and_read_par_channels(
        &program,
        language_runtime_definitions(runtime),
        &["OUT"],
    )
    .await
    .expect("the committed application runs on the real Rholang evaluator");

    let mut labelled = BTreeMap::new();
    for output in outputs.get("OUT").expect("OUT was requested") {
        let [label, response] = exact_list(output).expect("OUT datum is [label, response]") else {
            panic!("OUT datum must have arity two")
        };
        let label = exact_string(label).expect("OUT label is a string");
        assert!(labelled.insert(label, response).is_none(), "duplicate OUT label `{label}`");
    }

    assert_eq!(labelled.len(), 7, "every application branch must reply exactly once");
    for label in ["left-positive", "right-positive"] {
        assert_eq!(parse_status(labelled[label]), Some("accepted"), "{label}");
    }
    for label in ["left-negative", "right-negative", "left-crossfire", "right-crossfire"] {
        assert_eq!(parse_status(labelled[label]), Some("rejected"), "{label}");
    }
    assert_eq!(
        error_code(labelled["atomic-failure"]),
        Some("InvalidSurfaceDdl"),
        "the invalid suffix must reject the complete installation batch",
    );
    assert_eq!(
        service
            .installed_count()
            .expect("installed table is readable"),
        2,
        "only Left and Right are visible; ValidPrefix from the failed batch was never published",
    );

    for (label, response) in &labelled {
        let result = parse_status(response).or_else(|| error_code(response));
        println!("{label}: {}", result.expect("every labelled response has a result"));
    }
    println!("installed-languages: 2");
}
