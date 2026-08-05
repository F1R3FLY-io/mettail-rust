//! E-6a Phase-1 FEASIBILITY SPIKE (pgmcp experiment 145) — the smallest
//! possible in-Rho probes of the PathMap-backed subject index, on live
//! counting f1r3node runtimes (`bench-naive-baseline` quarantine):
//!
//! * (U1, homogeneous-mode arm) a set-mode [`EPathMap`] receive pattern does
//!   not cross-match the map-mode subject index, while a map-mode pattern does
//!   bind a native value slot through the PathMap matcher PDA; a bare free-var
//!   pattern still binds the whole value byte-identically;
//! * (U1, positive arm + U2/U3) the process-context QUERY CHAIN works end to
//!   end: persistent index publish → machine-side per-op site enumeration
//!   (`readZipperAt(..).getSubtrie()`) → exact map-key guards (`contains`) + σ
//!   extraction (`atPath`) →
//!   accept fires in the `build_accept_send` ABI, with ZERO `loc:`/`col:`/
//!   `cap:` traffic (`matching_tau == 0`) and a deterministic COMM profile;
//! * (U2) THREE repeated runs produce bit-identical observed multisets,
//!   site-enumeration readbacks (including order), and counter snapshots.

use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EPathMap, Expr, Par, ReceiveBind};
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_gstring_par, new_receive_par,
    new_send_par,
};

use mettail_rholang_codegen::{reflect_ground_term_par, GroundTerm, InRhoMatchingRuleset};
use mettail_rholang_runtime::{
    bench_inj_and_read, bench_runtime_with_counters, decode_sites_par, discovery_call_par,
    e6a_index_channel, e6a_sites_channel, e6a_tag_string, entry_query_match_par, entry_query_shape,
    pathmap_spread_term_par, sites_non_ancestral, BenchWorkloadParams, CommCounterSnapshot,
};
use models::rust::epathmap_trie_codec::EPathMapMode;
use rholang::rust::interpreter::matcher::spatial_matcher::SpatialMatcherContext;
use rholang::rust::interpreter::rho_runtime::RhoRuntime;

use dovetail::rules::Pattern;
use dovetail::set_automaton::{PatternId, SetAutomaton};

const FP: &str = "fp";
const ROOT_SITE: &str = "site0";
const OUT: &str = "OUT";

fn quoted(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

fn epathmap_par(pathmap: EPathMap, connective_used: bool) -> Par {
    let mut par = Par::default();
    par.exprs = vec![Expr {
        expr_instance: Some(ExprInstance::EPathmapBody(pathmap)),
    }];
    par.connective_used = connective_used;
    par
}

fn single_epathmap(par: &Par) -> &EPathMap {
    match par.exprs.as_slice() {
        [Expr {
            expr_instance: Some(ExprInstance::EPathmapBody(pathmap)),
        }] => pathmap,
        other => panic!("expected one EPathMap expression, got {other:?}"),
    }
}

fn string_path(parts: &[&str]) -> Par {
    new_elist_par(
        parts.iter().map(|part| quoted(part)).collect(),
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    )
}

fn workload(name: &str) -> BenchWorkloadParams {
    BenchWorkloadParams {
        name: name.to_string(),
        matcher: "e6a-spike".to_string(),
        encoding: "-".to_string(),
        n: 1,
        rep: 0,
    }
}

/// A one-shot σ-echo (the B2/Track-B shape, verbatim):
/// `for(y_0,…,y_{k-1}, o <- accept){ o!(y_0) | … | o!(y_{k-1}) }`.
fn sigma_echo_receiver(accept_channel: &str, arity: usize) -> Par {
    let mut body = Par::default();
    for i in 0..arity {
        let yi = arity - i;
        let send = new_send_par(
            new_boundvar_par(0, create_bit_vector(&[0]), false),
            vec![new_boundvar_par(yi as i32, create_bit_vector(&[yi]), false)],
            false,
            create_bit_vector(&[0, yi]),
            false,
            create_bit_vector(&[0, yi]),
            false,
        );
        body = body.append(send);
    }
    if arity > 0 {
        body.locally_free = create_bit_vector(&(0..=arity).collect::<Vec<_>>());
    }
    new_receive_par(
        vec![ReceiveBind {
            patterns: (0..arity + 1)
                .map(|i| new_freevar_par(i as i32, Vec::new()))
                .collect(),
            source: Some(quoted(accept_channel)),
            remainder: None,
            free_count: (arity + 1) as i32,
        }],
        body,
        false,
        false,
        (arity + 1) as i32,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// The direct-construction flat `Swap(x, y)` ruleset (admission-matrix style).
fn swap_ruleset() -> InRhoMatchingRuleset {
    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
    )])
    .expect("Swap(x, y) compiles");
    InRhoMatchingRuleset {
        automaton,
        accept_channels: vec![(PatternId(0), "sa:swap".to_string())],
        language_fingerprint: FP.to_string(),
        deferred: Vec::new(),
        native_dispatch: Vec::new(),
        ac_dispatch: Vec::new(),
        contextual_dispatch: Vec::new(),
        structural_ac_dispatch: Vec::new(),
        nested_structural_ac_dispatch: Vec::new(),
    }
}

/// The direct-construction NESTED `f(g(x))` ruleset (the divergent-admission
/// shape the control path fails closed on at ≥ 2 sites).
fn nested_ruleset() -> InRhoMatchingRuleset {
    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app("f".to_string(), vec![Pattern::app("g".to_string(), vec![Pattern::var("x")])]),
    )])
    .expect("f(g(x)) compiles");
    InRhoMatchingRuleset {
        automaton,
        accept_channels: vec![(PatternId(0), "sa:fg".to_string())],
        language_fingerprint: FP.to_string(),
        deferred: Vec::new(),
        native_dispatch: Vec::new(),
        ac_dispatch: Vec::new(),
        contextual_dispatch: Vec::new(),
        structural_ac_dispatch: Vec::new(),
        nested_structural_ac_dispatch: Vec::new(),
    }
}

/// `Pair(Swap(A, B), Swap(C, D))` — TWO flat candidate sites.
fn two_swap_subject() -> GroundTerm {
    GroundTerm::new(
        "Pair",
        vec![
            GroundTerm::new("Swap", vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")]),
            GroundTerm::new("Swap", vec![GroundTerm::nullary("C"), GroundTerm::nullary("D")]),
        ],
    )
}

fn sorted_renderings(pars: &[Par]) -> Vec<String> {
    let mut rendered: Vec<String> = pars.iter().map(|par| format!("{par:?}")).collect();
    rendered.sort();
    rendered
}

/// (U1) A set-mode EPathMap pattern cannot cross-match the map-mode subject
/// index. A bare free-variable pattern still binds the whole map value, which
/// round-trips byte-identically.
#[tokio::test]
async fn u1_set_pattern_does_not_cross_match_map_index() {
    let subject = two_swap_subject();
    let (publish, built) = pathmap_spread_term_par(&subject, FP, ROOT_SITE);
    assert_eq!(built.site_entries, 7, "one «s» entry per node");
    assert_eq!(built.value_entries, 7, "one native «v» map entry per node");

    assert_eq!(
        single_epathmap(&built.index).mode(),
        EPathMapMode::Map,
        "the subject index stores native PathMap keys with associated Par values"
    );

    // Cross-mode attempt: set pattern = {| free-var |} (connective marked).
    let set_pattern = EPathMap::new(vec![new_freevar_par(0, Vec::new())], Vec::new(), true, None);
    assert_eq!(set_pattern.mode(), EPathMapMode::Set);
    let mut destructuring_pattern = Par::default();
    destructuring_pattern.exprs = vec![Expr {
        expr_instance: Some(ExprInstance::EPathmapBody(set_pattern)),
    }];
    destructuring_pattern.connective_used = true;
    let destructuring_receive = new_receive_par(
        vec![ReceiveBind {
            patterns: vec![destructuring_pattern],
            source: Some(quoted(&e6a_index_channel(FP, ROOT_SITE))),
            remainder: None,
            free_count: 1,
        }],
        new_send_par(
            quoted("u1:witness"),
            vec![quoted("fired")],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        ),
        false,
        false,
        1,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );

    // Whole-value bind: `for(@x <- e6a:idx:site0){ OUT!(x) }`.
    let bind_receive = new_receive_par(
        vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(quoted(&e6a_index_channel(FP, ROOT_SITE))),
            remainder: None,
            free_count: 1,
        }],
        new_send_par(
            quoted(OUT),
            vec![new_boundvar_par(0, create_bit_vector(&[0]), false)],
            false,
            create_bit_vector(&[0]),
            false,
            create_bit_vector(&[0]),
            false,
        ),
        false,
        false,
        1,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );

    let program = publish.append(destructuring_receive).append(bind_receive);
    let (mut runtime, comm, matches) = bench_runtime_with_counters(Vec::new(), OUT)
        .await
        .expect("counting runtime builds");
    let result = bench_inj_and_read(&mut runtime, &program, OUT, workload("u1"), &comm, &matches)
        .await
        .expect("inj executes");

    // The whole-value bind fired: OUT carries the index value…
    assert_eq!(result.observed.len(), 1, "the free-var bind forwarded the index to OUT");
    // …byte-identically (the eval/substitution round trip preserves the value).
    let expected_index = &built.index;
    assert_eq!(
        &result.observed[0], expected_index,
        "the bound EPathMap round-trips byte-identically through bind + forward"
    );

    // The cross-mode receive did NOT fire: no witness, and its consume rests.
    let witness = runtime.get_data(&quoted("u1:witness")).await;
    assert!(
        witness.is_empty(),
        "homogeneous EPathMap modes must not cross-match; got {witness:?}"
    );
}

/// (U1, positive arm) A map-mode pattern with a concrete key and a dynamic
/// value traverses the native EPathMap matcher and binds the PathMap value
/// slot. This keeps the historical cross-mode refusal from being mistaken for
/// a lack of EPathMap receive-pattern support.
#[test]
fn u1_map_pattern_binds_native_value_slot() {
    let key = quoted("u1:key");
    let value = quoted("u1:value");
    let target = epathmap_par(
        EPathMap::new_map([(key.clone(), value.clone())], Vec::new(), false, None),
        false,
    );
    let pattern = epathmap_par(
        EPathMap::new_map([(key, new_freevar_par(0, Vec::new()))], Vec::new(), true, None),
        true,
    );

    let mut matcher = SpatialMatcherContext::new();
    assert!(
        matcher.spatial_match_result(target, pattern).is_some(),
        "a homogeneous map-mode pattern must traverse the native EPathMap matcher"
    );
    assert_eq!(matcher.free_map.get(&0), Some(&value));
}

/// The native map layout crosses both retired codec ceilings: symbol bytes and
/// path-segment count. Reflected subtrees occupy value slots at exact location
/// keys even when those keys are prefixes of deeper entries.
#[test]
fn native_map_index_crosses_legacy_symbol_and_depth_boundaries() {
    let long_constructor = "Constructor".repeat(9); // 99 bytes; the old cap was 62.
    let long_root = "root".repeat(20); // 80 bytes; the old cap was 62.
    let mut subject = GroundTerm::nullary(long_constructor);
    for _ in 0..72 {
        subject = GroundTerm::new("Node", vec![subject]);
    }

    let built = mettail_rholang_runtime::build_pathmap_index(&subject, FP, &long_root);
    let index = single_epathmap(&built.index);
    assert_eq!(index.mode(), EPathMapMode::Map);
    assert_eq!(built.site_entries, 73);
    assert_eq!(built.value_entries, 73);
    assert_eq!(index.len(), 146, "two native map keys per subject node");

    let root_value_key = string_path(&["v", &long_root]);
    assert_eq!(
        index
            .get_map_value(&root_value_key)
            .expect("the index is map-mode"),
        Some(&reflect_ground_term_par(&subject, FP)),
        "the reflected root subtree is stored directly in the map value slot"
    );

    let root_tag = e6a_tag_string(FP, "Node");
    let root_site_key = string_path(&[&root_tag, &long_root]);
    assert_eq!(
        index
            .get_map_value(&root_site_key)
            .expect("the index is map-mode"),
        Some(&Par::default()),
        "the compressed tag/location key uses Nil as its membership marker"
    );
}

/// Drive the FLAT two-site treatment end to end on one fresh counting runtime,
/// returning (sorted OUT renderings, decoded site enumeration, counters).
async fn drive_flat_two_swap() -> (Vec<String>, Vec<String>, CommCounterSnapshot) {
    let subject = two_swap_subject();
    let ruleset = swap_ruleset();
    let (publish, _built) = pathmap_spread_term_par(&subject, FP, ROOT_SITE);
    let discovery = discovery_call_par(&ruleset, FP, ROOT_SITE);
    let shape = entry_query_shape(&ruleset.automaton.view(), 0).expect("Swap(x,y) is linear");

    // The spike installs the per-site query processes at the two host-KNOWN
    // sites (the harness two-phase readback discipline is exercised by the
    // equivalence suite; the spike validates the query-chain mechanics and
    // separately CHECKS the machine enumeration below).
    let sites = ["site0/Pair.0".to_string(), "site0/Pair.1".to_string()];
    assert!(sites_non_ancestral(&sites));
    let mut program = publish.append(discovery);
    for site in &sites {
        program =
            program.append(entry_query_match_par(&shape, FP, ROOT_SITE, site, "sa:swap", OUT));
        program = program.append(sigma_echo_receiver("sa:swap", 2));
    }

    let (mut runtime, comm, matches) = bench_runtime_with_counters(Vec::new(), OUT)
        .await
        .expect("counting runtime builds");
    let result = bench_inj_and_read(&mut runtime, &program, OUT, workload("flat"), &comm, &matches)
        .await
        .expect("inj executes");

    // Machine-side site enumeration readback.
    let sites_channel = e6a_sites_channel(FP, ROOT_SITE, "Swap");
    let sites_data = runtime.get_data(&quoted(&sites_channel)).await;
    assert_eq!(sites_data.len(), 1, "exactly one discovery result rests on {sites_channel}");
    let decoded = decode_sites_par(&sites_data[0].a.pars[0], &e6a_tag_string(FP, "Swap"))
        .expect("the subtrie decodes");

    (sorted_renderings(&result.observed), decoded, result.comm.clone())
}

/// (Positive arm) The FLAT query chain fires both candidate sites from the
/// index with ZERO spread-channel traffic, the machine enumerates exactly the
/// two Swap sites, and the COMM profile is the mechanism's prediction.
#[tokio::test]
async fn flat_query_chain_guard_sigma_accept_and_machine_enumeration() {
    let (observed, machine_sites, comm) = drive_flat_two_swap().await;

    // σ slots delivered: ⟦A⟧, ⟦B⟧, ⟦C⟧, ⟦D⟧ (each echo forwards its 2 slots).
    let expected: Vec<String> = {
        let mut expected: Vec<String> = ["A", "B", "C", "D"]
            .iter()
            .map(|leaf| format!("{:?}", reflect_ground_term_par(&GroundTerm::nullary(*leaf), FP)))
            .collect();
        expected.sort();
        expected
    };
    assert_eq!(observed, expected, "both sites fired with byte-exact σ values");

    // The MACHINE enumerated the candidate sites (order = trie DFS byte order).
    let mut machine_sorted = machine_sites.clone();
    machine_sorted.sort();
    assert_eq!(
        machine_sorted,
        vec!["site0/Pair.0".to_string(), "site0/Pair.1".to_string()],
        "the getSubtrie discovery returns exactly the two head-Swap sites"
    );

    // COMM profile: 3 pathmap_index COMMs (1 discovery bind + 2 per-site
    // binds), 2 accepts, ZERO matching_tau (no loc:/col:/cap: at all — the
    // treatment's structural claim), 0 other (fully classified).
    assert_eq!(comm.pathmap_index, 3, "1 discovery + 2 per-site index binds; got {comm:?}");
    assert_eq!(comm.firing_visible, 2, "one accept COMM per fired site; got {comm:?}");
    assert_eq!(comm.matching_tau, 0, "NO spread-channel traffic in the treatment; got {comm:?}");
    assert_eq!(
        comm.other, 0,
        "all channels classified; unknown: {:?}",
        comm.unknown_channel_samples
    );
    assert_eq!(comm.subst_tau, 0, "no subst TRS in this workload; got {comm:?}");
    assert_eq!(comm.ac_carrier, 0, "no AC in this workload; got {comm:?}");
}

/// (U2) Three repeated runs are bit-identical: observed multiset, machine
/// site-enumeration READBACK INCLUDING ORDER, and the full counter snapshot.
#[tokio::test]
async fn treatment_is_deterministic_across_three_runs() {
    let mut outcomes = Vec::with_capacity(3);
    for _ in 0..3 {
        outcomes.push(drive_flat_two_swap().await);
    }
    assert_eq!(outcomes[0], outcomes[1], "run 1 ≡ run 2");
    assert_eq!(outcomes[1], outcomes[2], "run 2 ≡ run 3");
}

/// (NestedEntryMultiSite dissolution mechanics) The NESTED `f(g(x))` query
/// chain — a tag guard at the site, a DESCENT tag guard one level down, and a
/// depth-2 σ extraction — fires from the index with zero spread traffic, at
/// TWO co-installed nested candidate sites (exactly the shape the control
/// locate-all fails closed on).
#[tokio::test]
async fn nested_query_chain_fires_two_sites_from_the_index() {
    // Pair(f(g(L0)), f(g(L1))) — two nested candidate sites.
    let subject = GroundTerm::new(
        "Pair",
        vec![
            GroundTerm::new("f", vec![GroundTerm::new("g", vec![GroundTerm::nullary("L0")])]),
            GroundTerm::new("f", vec![GroundTerm::new("g", vec![GroundTerm::nullary("L1")])]),
        ],
    );
    let ruleset = nested_ruleset();
    let (publish, _built) = pathmap_spread_term_par(&subject, FP, ROOT_SITE);
    let discovery = discovery_call_par(&ruleset, FP, ROOT_SITE);
    let shape = entry_query_shape(&ruleset.automaton.view(), 0).expect("f(g(x)) is linear");
    assert_eq!(shape.guards.len(), 2, "root f + nested g descent");
    assert_eq!(shape.sigma_positions.len(), 1, "one σ slot at f.0/g.0");

    let sites = ["site0/Pair.0".to_string(), "site0/Pair.1".to_string()];
    let mut program = publish.append(discovery);
    for site in &sites {
        program = program.append(entry_query_match_par(&shape, FP, ROOT_SITE, site, "sa:fg", OUT));
        program = program.append(sigma_echo_receiver("sa:fg", 1));
    }

    let (mut runtime, comm, matches) = bench_runtime_with_counters(Vec::new(), OUT)
        .await
        .expect("counting runtime builds");
    let result =
        bench_inj_and_read(&mut runtime, &program, OUT, workload("nested"), &comm, &matches)
            .await
            .expect("inj executes");

    let observed = sorted_renderings(&result.observed);
    let expected: Vec<String> = {
        let mut expected: Vec<String> = ["L0", "L1"]
            .iter()
            .map(|leaf| format!("{:?}", reflect_ground_term_par(&GroundTerm::nullary(*leaf), FP)))
            .collect();
        expected.sort();
        expected
    };
    assert_eq!(
        observed, expected,
        "both NESTED candidate sites fired in-Rho from the index — the shape the control \
         locate-all fails closed on (NestedEntryMultiSite)"
    );
    assert_eq!(result.comm.matching_tau, 0, "no spread traffic; got {:?}", result.comm);
    assert_eq!(result.comm.other, 0, "all channels classified; got {:?}", result.comm);
}

/// (Guard soundness) A candidate site whose guard chain FAILS fires nothing:
/// installing a query process at a NON-site (the root Pair position, wrong
/// head tag) and at a STALE site (no node at all) is a no-op, never a wrong
/// match, and never an injection abort.
#[tokio::test]
async fn guard_failing_sites_fire_nothing_and_never_abort() {
    let subject = two_swap_subject();
    let ruleset = swap_ruleset();
    let (publish, _built) = pathmap_spread_term_par(&subject, FP, ROOT_SITE);
    let shape = entry_query_shape(&ruleset.automaton.view(), 0).expect("linear");

    // Root site: head is Pair, not Swap (guard false). Stale site: no node.
    let mut program = publish;
    for site in ["site0".to_string(), "site0/Pair.0/Swap.9".to_string()] {
        program =
            program.append(entry_query_match_par(&shape, FP, ROOT_SITE, &site, "sa:swap", OUT));
    }
    program = program.append(sigma_echo_receiver("sa:swap", 2));

    let (mut runtime, comm, matches) = bench_runtime_with_counters(Vec::new(), OUT)
        .await
        .expect("counting runtime builds");
    let result =
        bench_inj_and_read(&mut runtime, &program, OUT, workload("guard"), &comm, &matches)
            .await
            .expect("a guard-failing site must not abort the injection");
    assert!(
        result.observed.is_empty(),
        "no accept may fire at a guard-failing site; got {:?}",
        result.observed
    );
    assert_eq!(result.comm.firing_visible, 0, "no accept COMM; got {:?}", result.comm);
}
