//! AST-first ambiguity witness integration.
//!
//! Generated ambiguity evidence is represented as explicit receive-less Rho
//! facts. The execution artifact here is normalized `rhoapi::Par`; the
//! Rholang-looking strings carried by `RhoAstSend` are reader annotations only.

use mettail_rho_adapter::{
    collect_enabled_ambiguity_witnesses, AmbiguityCandidate, AmbiguityWitnessSet,
};
use mettail_rho_codegen::RhoAstSend;
use mettail_rho_runtime::run_normalized_par_for_oracle_and_read_string_tuples;
use models::rhoapi::Par;
use std::collections::BTreeMap;

const WITNESS_CHANNEL: &str = "MTL_AMBIGUITY";

fn witness(key: &str, payload: &str) -> Par {
    RhoAstSend::ambiguity_witness(WITNESS_CHANNEL, key, payload)
        .expect("test witness must build")
        .par()
        .clone()
}

fn append_all(parts: impl IntoIterator<Item = Par>) -> Par {
    parts
        .into_iter()
        .fold(Par::default(), |program, part| program.append(part))
}

fn candidates_from_tuples(tuples: Vec<Vec<String>>) -> Vec<AmbiguityCandidate<String, String>> {
    tuples
        .into_iter()
        .map(|tuple| {
            let [key, payload]: [String; 2] = tuple
                .try_into()
                .expect("ambiguity witness fact must have exactly key and payload");
            AmbiguityCandidate::enabled(key, payload)
        })
        .collect()
}

async fn observed(order: &[(&str, &str)]) -> AmbiguityWitnessSet<String, String> {
    let program = append_all(order.iter().map(|(key, payload)| witness(key, payload)));
    let tuples = run_normalized_par_for_oracle_and_read_string_tuples(&program, WITNESS_CHANNEL)
        .await
        .expect("AST witness facts must execute");
    collect_enabled_ambiguity_witnesses(candidates_from_tuples(tuples))
        .expect("witness facts in this test are conflict-free")
}

#[tokio::test]
async fn ast_witness_facts_preserve_ambiguity_set_across_schedule_order() {
    let left = observed(&[
        ("branch:a", "payload:a"),
        ("branch:b", "payload:b"),
        ("branch:c", "payload:c"),
    ])
    .await;
    let right = observed(&[
        ("branch:c", "payload:c"),
        ("branch:a", "payload:a"),
        ("branch:b", "payload:b"),
    ])
    .await;

    assert_eq!(left, right);
    assert_eq!(
        left.into_inner(),
        BTreeMap::from([
            ("branch:a".to_string(), "payload:a".to_string()),
            ("branch:b".to_string(), "payload:b".to_string()),
            ("branch:c".to_string(), "payload:c".to_string()),
        ])
    );
}

#[tokio::test]
async fn ast_witness_exact_duplicates_are_idempotent_after_runtime_observation() {
    let set = observed(&[
        ("branch:a", "payload:a"),
        ("branch:a", "payload:a"),
        ("branch:b", "payload:b"),
    ])
    .await;

    assert_eq!(set.len(), 2);
    assert_eq!(set.get(&"branch:a".to_string()), Some(&"payload:a".to_string()));
    assert_eq!(set.get(&"branch:b".to_string()), Some(&"payload:b".to_string()));
}

#[tokio::test]
async fn ast_witness_conflicting_payload_rejects_after_runtime_observation() {
    let program =
        append_all([witness("branch:a", "payload:a"), witness("branch:a", "payload:other")]);
    let tuples = run_normalized_par_for_oracle_and_read_string_tuples(&program, WITNESS_CHANNEL)
        .await
        .expect("AST witness facts must execute");

    let conflict = collect_enabled_ambiguity_witnesses(candidates_from_tuples(tuples))
        .expect_err("same exact key with different payload must reject");
    assert_eq!(conflict.key, "branch:a");
}
