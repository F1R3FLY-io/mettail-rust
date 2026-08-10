//! Stage 4 S-AC (AC4) end-to-end: the in-Rho AC matcher — which handles the process-soup `HashBag`
//! carrier (AC1–AC3) — extended to the NATIVE collection carriers `ESet` (`HashSet`), `EMap`
//! (`HashMap`), and a STRUCTURED paired/correlated set match under a `Receive.condition` guard
//! (`ZipAc`). Each carrier is built from a reflected subject collection (`reflect_ground_term_par`,
//! the SPREAD side of M-reflect) and matched ON the live f1r3node reducer by a co-installed
//! `ac_sigma_receiver_par` whose native connective pattern (`ac_set_pattern` / `ac_map_pattern` /
//! a structured `ESet` pattern) picks k-of-n + binds the residual collection to the remainder —
//! inside ONE atomic `consume`, the whole match on the interpreter (production
//! `spatial_matcher_pda::ListMachine` over `ParSet`/`ParMap`).
//!
//! These are DIRECT-construction firing tests (the established `rho_net_equivalence` pattern —
//! `ac_sigma_receiver_par_builds_a_working_receiver` / `ac_contract_call_fires_the_ac_receiver`):
//! the carrier + receiver are built by the production codegen builders and run on the reducer, with
//! NO host-σ report in the loop. So OUT is provably the NATIVE PICK over the reflected collection
//! (the only input) — the AC4 analogue of `s_ac_bag_is_produced_by_the_spread_not_the_report`.

use mettail_rholang_codegen::{
    ac_set_correlation_condition, ac_set_element_pattern, ac_set_paired_receiver_par,
    ac_sigma_receiver_par_with_condition, reflect_ground_term_par, CollectionType, GroundTerm,
};
use mettail_rholang_runtime::run_normalized_par_for_oracle_and_read_runtime_values;
use mettail_runtime::RuntimeObservationValue;
use models::create_bit_vector;
use models::rust::utils::{new_boundvar_par, new_gstring_par, new_send_par};

/// A fixed reflection fingerprint: the carrier's element tags and the receiver's frame share it, so
/// the reflected tags are internally consistent (the decoder reads the embedded constructor name,
/// which is fingerprint-agnostic).
const FINGERPRINT: &str = "ac4-mapzip-fingerprint";

/// The observed constructor label of a decoded runtime observation value.
fn observation_constructor(value: &RuntimeObservationValue) -> String {
    match value {
        RuntimeObservationValue::Term { constructor, .. } => constructor.clone(),
        other => format!("?{other:?}"),
    }
}

/// Build + run `receiver ∥ source!(⟦collection⟧, @OUT)` on the reducer and read the OUT values.
async fn fire(
    collection: GroundTerm,
    kind: CollectionType,
    op: &str,
    k: usize,
    rhs_bound_var: i32,
) -> Vec<RuntimeObservationValue> {
    mettail_runtime::clear_var_cache();
    let carrier = reflect_ground_term_par(&collection, FINGERPRINT);
    // The receiver fires `rhs` (a σ slot, referenced as `BoundVar(rhs_bound_var)`) on the dynamic out.
    let rhs = new_boundvar_par(rhs_bound_var, create_bit_vector(&[rhs_bound_var as usize]), false);
    let receiver = ac_sigma_receiver_par_with_condition(
        kind,
        FINGERPRINT,
        op,
        k,
        rhs,
        new_gstring_par("c_ac4".to_string(), Vec::new(), false),
        None,
    );
    let injection = new_send_par(
        new_gstring_par("c_ac4".to_string(), Vec::new(), false),
        vec![carrier, new_gstring_par("OUT".to_string(), Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    let program = receiver.append(injection);
    run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the AC4 native-collection receiver must fire on the reducer")
}

/// AC4-set (`HashSet` → `ESet`): the linear `SetOp{x, ...rest} ~> x` picks ONE element of the native
/// `ESet` carrier + binds the residual set, firing the element on OUT. The element σ is
/// `FreeVar(0)` → `BoundVar(slots+1) = BoundVar(2)` (k=1, slots=1). OUT is provably a member of the
/// reflected set `{A, B}` — the native pick over the SPREAD, never a report.
#[tokio::test]
async fn mapzipdemo_set_rewrite_fires_as_a_comm_on_the_reducer() {
    let set = GroundTerm::collection(
        CollectionType::HashSet,
        "SetOp",
        vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
    );
    let observed = fire(set, CollectionType::HashSet, "SetOp", 1, 2).await;
    assert_eq!(observed.len(), 1, "the ESet AC receiver fires once (got {observed:?})");
    let fired = observation_constructor(&observed[0]);
    assert!(
        fired == "A" || fired == "B",
        "OUT is a member of the reflected set, got {fired}"
    );
}

/// AC4-map (`HashMap` → `EMap`): the linear `MapOp{k => v, ...rest} ~> v` picks ONE `(key, value)`
/// entry of the native `EMap` carrier + binds the residual map, firing the VALUE on OUT. The value σ
/// is `FreeVar(1)` → `BoundVar(2)` (k=1, slots=2). OUT is the value `B` of the sole entry `A => B`.
#[tokio::test]
async fn mapzipdemo_map_rewrite_fires_as_a_comm_on_the_reducer() {
    let map = GroundTerm::collection(
        CollectionType::HashMap,
        "MapOp",
        vec![GroundTerm::map_entry(GroundTerm::nullary("A"), GroundTerm::nullary("B"))],
    );
    // value slot = FreeVar(1) → BoundVar(free_count-1-1) = BoundVar(2) for free_count = 2*1+2 = 4.
    let observed = fire(map, CollectionType::HashMap, "MapOp", 1, 2).await;
    assert_eq!(observed.len(), 1, "the EMap AC receiver fires once (got {observed:?})");
    let fired = observation_constructor(&observed[0]);
    assert_eq!(fired, "B", "OUT is the value of the sole map entry A => B, got {fired}");
}

/// AC4-map KEY-UNIQUENESS: the `EMap`/`ParMap` sorted-dedup invariant (map keys unique) survives the
/// reflect → match → RHS split. The carrier map has TWO entries with the SAME key `A` (`{A => B,
/// A => C}`), which `ParMap::new` collapses to ONE entry on reflect (key-uniqueness). So the k=1
/// receiver picks that SOLE surviving entry (residual map EMPTY) and fires ONCE — not twice. A
/// per-multiplicity bag would fire twice; the deduped map fires exactly once, its value the survivor.
#[tokio::test]
async fn mapzipdemo_map_key_uniqueness_survives_the_reflect_match_split() {
    let map = GroundTerm::collection(
        CollectionType::HashMap,
        "MapOp",
        vec![
            GroundTerm::map_entry(GroundTerm::nullary("A"), GroundTerm::nullary("B")),
            GroundTerm::map_entry(GroundTerm::nullary("A"), GroundTerm::nullary("C")),
        ],
    );
    let observed = fire(map, CollectionType::HashMap, "MapOp", 1, 2).await;
    assert_eq!(
        observed.len(),
        1,
        "duplicate key A collapses to ONE entry (key-uniqueness) — one firing, not two (got {observed:?})"
    );
    let fired = observation_constructor(&observed[0]);
    assert!(
        fired == "B" || fired == "C",
        "OUT is the surviving value of the deduped key A, got {fired}"
    );
}

/// AC4-zip (`ZipAc`): a STRUCTURED paired/correlated set match under a `Receive.condition`. The
/// carrier `ZipOp{Pair(A, B), Pair(A, C), Pair(D, E)}` reflects to a native `ESet` of three `Pair`
/// elements; the receiver's `ESet` connective pattern matches TWO `Pair(a, _)` elements
/// (`ac_set_element_pattern`) whose FIRST components are correlated by the `EEq(a_0, a_1)` guard
/// (`ac_set_correlation_condition`), binding the residual set to the remainder — inside ONE atomic
/// `consume` ON the reducer. Only the two `A`-keyed pairs share a first component, so the UNIQUE
/// correlated match is `a = A` and OUT is `A` — the `D`-keyed pair is rejected by the guard on the
/// reducer (the paired correlation, not a report). This is the AC4 analogue of the Comm/structural-AC
/// correlated match, over an `ESet` carrier.
#[tokio::test]
async fn mapzipdemo_zip_rewrite_fires_as_a_comm_on_the_reducer() {
    use models::create_bit_vector;
    use models::rust::utils::{new_boundvar_par, new_gstring_par, new_send_par};

    mettail_runtime::clear_var_cache();
    let pair = |a: &str, b: &str| {
        GroundTerm::new("Pair", vec![GroundTerm::nullary(a), GroundTerm::nullary(b)])
    };
    let carrier = reflect_ground_term_par(
        &GroundTerm::collection(
            CollectionType::HashSet,
            "ZipOp",
            vec![pair("A", "B"), pair("A", "C"), pair("D", "E")],
        ),
        FINGERPRINT,
    );

    // Two structured `Pair(a, _)` element patterns: elem0 binds (FreeVar0=a0, FreeVar1=b0), elem1
    // binds (FreeVar2=a1, FreeVar3=b1); element_slots = 4, free_count = 6.
    let elem0 = ac_set_element_pattern("Pair", 2, 0, FINGERPRINT);
    let elem1 = ac_set_element_pattern("Pair", 2, 2, FINGERPRINT);
    // The correlation guard EEq(a0, a1) over slots 0 and 2 (free_count = 6).
    let condition = ac_set_correlation_condition(&[0, 2], 6);
    // Fire the shared first component a0 = FreeVar(0) → BoundVar(free_count-1-0) = BoundVar(5).
    let rhs = new_boundvar_par(5, create_bit_vector(&[5]), false);
    let receiver = ac_set_paired_receiver_par(
        vec![elem0, elem1],
        4,
        Some(condition),
        rhs,
        new_gstring_par("c_zip".to_string(), Vec::new(), false),
    );
    let injection = new_send_par(
        new_gstring_par("c_zip".to_string(), Vec::new(), false),
        vec![carrier, new_gstring_par("OUT".to_string(), Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );

    let program = receiver.append(injection);
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the structured paired ESet AC receiver must fire on the reducer");
    assert_eq!(observed.len(), 1, "the correlated pair match fires once (got {observed:?})");
    let fired = observation_constructor(&observed[0]);
    assert_eq!(
        fired, "A",
        "OUT is the UNIQUE correlated first component A (the guard rejects the D-keyed pair), got {fired}"
    );
}
