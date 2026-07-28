//! E-6a EQUIVALENCE GATE (Phase 2, BEFORE any measurement — pgmcp experiment
//! 145): the PathMap-index TREATMENT arm must land the SAME fired-set multiset
//! as the CURRENT spread+drive CONTROL arm on every admitted corpus cell, and
//! on the nested multi-candidate cells (where the control locate-all fails
//! closed with `NestedEntryMultiSite`) the treatment is pinned against the
//! DIRECTLY-COMPUTED expected redex sets. The machine-enumerated candidate
//! sites are additionally pinned against the directly-computed host walk (the
//! same `collect_redex_sites` derivation restated in `multi_rule_shared_sites`).
//!
//! Mirrors `rho_net_naive_equivalence.rs`'s discipline: fresh counting
//! runtimes, sorted-multiset comparison, `clear_var_cache` before language
//! compiles.

// `dead_code` is wrong HERE: `workloads.rs` is ONE support module shared by FOUR
// consumers through `#[path]` (this file, the sibling bench, and the two driver
// bins), and each needs a different subset of the workload registry. The lint sees
// only this consumer, so every item the OTHER three use reads as dead. The module
// is not a dependency because a `[dev-dependencies]` crate cannot be shared with a
// `src/bin` target — one source, four consumers.
#[allow(dead_code)]
#[path = "../benches/support/workloads.rs"]
mod workloads;

use std::collections::BTreeSet;

use mettail_rholang_codegen::{in_rho_match_all_sites_call_par, AutomatonUnsupported};
use workloads::{
    compile_workload, e6a_control_matcher, multi_rule_shared_sites, run_compiled_workload,
    run_e6a_treatment_workload, GuardEncodingKind, WorkloadKind, OUT_CHANNEL, ROOT_SITE,
};

use mettail_rholang_runtime::par_as_runtime_observation_value;
use mettail_runtime::RuntimeObservationValue;
use models::rhoapi::Par;

fn decode_sorted(observed: &[Par]) -> Vec<RuntimeObservationValue> {
    let mut values: Vec<RuntimeObservationValue> = observed
        .iter()
        .map(|par| {
            par_as_runtime_observation_value(par)
                .unwrap_or_else(|| panic!("undecodable OUT value: {par:?}"))
        })
        .collect();
    values.sort_by_key(|value| format!("{value:?}"));
    values
}

/// Run control + treatment for one cell on fresh runtimes and assert:
/// (i) treatment observed multiset == the compiled DIRECTLY-COMPUTED expected;
/// (ii) treatment observed multiset == control observed multiset;
/// (iii) the union of machine-enumerated candidate sites == the
///       directly-computed host-walk site set.
async fn assert_cell_equivalence(kind: WorkloadKind, n: u64) {
    mettail_runtime::clear_var_cache();
    let compiled =
        compile_workload(kind, n).unwrap_or_else(|e| panic!("{}({n}) compiles: {e}", kind.name()));
    let control_matcher =
        e6a_control_matcher(kind).expect("every E-6a corpus cell has a control column");

    let control =
        run_compiled_workload(&compiled, control_matcher, GuardEncodingKind::PatternGuard, 0)
            .await
            .unwrap_or_else(|failure| {
                panic!(
                    "{}({n}) control ({}): {}",
                    kind.name(),
                    control_matcher.name(),
                    failure.reason
                )
            });
    let treatment = run_e6a_treatment_workload(&compiled, 0)
        .await
        .unwrap_or_else(|failure| panic!("{}({n}) treatment: {}", kind.name(), failure.reason));

    // (i) Treatment vs the directly-computed expected multiset. (The treatment
    // drive itself verifies this fail-closed; re-assert here so the GATE also
    // pins it explicitly.)
    let expected_sorted = {
        let mut expected = compiled.expected.clone();
        expected.sort_by_key(|value| format!("{value:?}"));
        expected
    };
    assert_eq!(
        decode_sorted(&treatment.result.observed),
        expected_sorted,
        "{}({n}): treatment fired-set != directly-computed expected",
        kind.name(),
    );

    // (ii) Treatment vs control fired-set multiset equality.
    assert_eq!(
        decode_sorted(&treatment.result.observed),
        decode_sorted(&control.result.observed),
        "{}({n}): treatment fired-set != control ({}) fired-set",
        kind.name(),
        control_matcher.name(),
    );

    // (iii) Machine-enumerated candidate sites vs the directly-computed host
    // walk (per-op union; lambda_chain compares the FIRST step's enumeration
    // against the full chain's walk).
    let subject = &compiled.subject;
    let expected_sites: BTreeSet<String> =
        multi_rule_shared_sites(compiled.ruleset(), subject, ROOT_SITE)
            .into_iter()
            .collect();
    let machine_sites: BTreeSet<String> = treatment
        .machine_sites
        .values()
        .flat_map(|sites| sites.iter().cloned())
        .collect();
    assert_eq!(
        machine_sites,
        expected_sites,
        "{}({n}): machine-enumerated candidate sites != directly-computed host walk",
        kind.name(),
    );

    // Structural claims of the treatment: zero spread-channel traffic, every
    // COMM classified.
    assert_eq!(
        treatment.result.comm.matching_tau,
        0,
        "{}({n}): the treatment must publish NO loc:/col:/cap: traffic; got {:?}",
        kind.name(),
        treatment.result.comm,
    );
    // `other` COMMs come only from the shared FIRING cascade (e.g. the β
    // subst-TRS's one fresh-name `^cmp`-result COMM per firing, on a
    // `new`-allocated channel — the same family the control column records),
    // never from the treatment's own machinery: assert LIKE-FOR-LIKE equality
    // with the control instead of zero.
    assert_eq!(
        treatment.result.comm.other,
        control.result.comm.other,
        "{}({n}): treatment `other` COMMs must equal the control's (the shared firing \
         cascade); treatment samples: {:?}, control samples: {:?}",
        kind.name(),
        treatment.result.comm.unknown_channel_samples,
        control.result.comm.unknown_channel_samples,
    );
    assert!(
        treatment.result.comm.pathmap_index > 0,
        "{}({n}): the treatment's query COMMs must be visible; got {:?}",
        kind.name(),
        treatment.result.comm,
    );
}

/// (Flat multi-site) swap_comb m ∈ {1, 4}: both arms admitted; fired sets
/// equal; machine sites = the m Swap positions.
#[tokio::test]
async fn swap_comb_treatment_matches_control() {
    assert_cell_equivalence(WorkloadKind::SwapComb, 1).await;
    assert_cell_equivalence(WorkloadKind::SwapComb, 4).await;
}

/// (Single nested-below-wrappers site) swap_small k = 3.
#[tokio::test]
async fn swap_small_treatment_matches_control() {
    assert_cell_equivalence(WorkloadKind::SwapSmall, 3).await;
}

/// (NESTED MULTI-CANDIDATE — the `NestedEntryMultiSite` dissolution cells)
/// nested_spine k ∈ {2, 8}: the control ONE-call locate-all FAILS CLOSED
/// (pinned here), the naive comprehension is the current in-Rho control, and
/// the treatment admits the cell IN-RHO with the same fired set.
#[tokio::test]
async fn nested_spine_treatment_dissolves_nested_entry_multi_site() {
    for k in [2u64, 8] {
        mettail_runtime::clear_var_cache();
        let compiled = compile_workload(WorkloadKind::NestedSpine, k).expect("compiles");
        assert_eq!(
            in_rho_match_all_sites_call_par(
                compiled.ruleset(),
                &compiled.subject,
                ROOT_SITE,
                OUT_CHANNEL,
            ),
            Err(AutomatonUnsupported::NestedEntryMultiSite),
            "k={k}: the control locate-all still fails closed (the dissolution context)"
        );
        assert_cell_equivalence(WorkloadKind::NestedSpine, k).await;
    }
}

/// (NESTED MULTI-CANDIDATE, multi-RULE) multi_rule_shared n = 402 (r = 4,
/// s = 2): the ONE-call locate-all fails closed (pinned), the per-rule sa
/// drive is the control, and the treatment admits with the same fired set.
#[tokio::test]
async fn multi_rule_shared_treatment_matches_per_rule_control() {
    mettail_runtime::clear_var_cache();
    let compiled = compile_workload(WorkloadKind::MultiRuleShared, 402).expect("compiles");
    assert_eq!(
        in_rho_match_all_sites_call_par(
            compiled.ruleset(),
            &compiled.subject,
            ROOT_SITE,
            OUT_CHANNEL,
        ),
        Err(AutomatonUnsupported::NestedEntryMultiSite),
        "the control ONE-call locate-all still fails closed for r ≥ 2"
    );
    assert_cell_equivalence(WorkloadKind::MultiRuleShared, 402).await;
}

/// (Per-step β chain) lambda_chain n = 4: both arms run the per-step ROOT
/// discipline; the treatment reaches the same normal-form ladder from the
/// machine-enumerated root site.
#[tokio::test]
async fn lambda_chain_treatment_matches_per_step_control() {
    assert_cell_equivalence(WorkloadKind::LambdaChain, 4).await;
}
