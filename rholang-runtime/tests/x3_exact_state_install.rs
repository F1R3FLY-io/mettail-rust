//! **X3 — is `revert_to_soft_checkpoint` on a FRESH EMPTY sandbox an exact
//! state install?**
//!
//! # The premise under test
//!
//! The speculative-evaluation design needs to plant an arbitrary, caller-built
//! tuplespace state into a sandbox space and get *exactly* that state back —
//! no residue from whatever ran in the sandbox before, no contribution from a
//! cold history layer. It proposes to do this with
//! [`ISpace::revert_to_soft_checkpoint`], handing it a `SoftCheckpoint` whose
//! `cache_snapshot` the caller built by hand.
//!
//! The mechanism (`rspace++/src/rspace/rspace.rs:311-329` — the design's cited
//! `:311-330` is right to within one line):
//!
//! ```text
//! let history        = self.get_history_repository();
//! let history_reader = history.get_history_reader(&history.root())?;
//! let hot_store      = HotStoreInstances::create_from_hs_and_hr(
//!                          checkpoint.cache_snapshot,      // ← the caller's state, WHOLESALE
//!                          history_reader.base(),          // ← the COLD layer, re-attached
//!                      );
//! *self.store.write()          = Arc::new(hot_store);
//! *self.event_log.lock()       = checkpoint.log;
//! *self.produce_counter.lock() = checkpoint.produce_counter;
//! ```
//!
//! The hot layer is replaced wholesale, so it is exact. The COLD layer is
//! re-attached from `history.root()` — and *that* is why the sandbox must be
//! FRESH and EMPTY rather than a copy of a live space: only when
//! `create_checkpoint` has never been called is `history.root()` invariantly
//! the empty root, so the cold layer contributes nothing to a subsequent read.
//!
//! # Two directions, both tested
//!
//! | direction | question | test |
//! | --- | --- | --- |
//! | ⟶ install | does the state that goes in come back out unchanged? | [`d1_hand_built_state_installs_exactly`] |
//! | ⟵ erase | does a second install fully erase the first run's effects? | [`d2_reinstall_erases_a_previous_runs_effects`] |
//!
//! # ⚠ A finding that changes the design's own test recipe
//!
//! The design says "read back with `to_map()`". **`to_map()` is not a faithful
//! readback.** `InMemHotStore::to_map` (`hot_store.rs:653-695`) iterates the
//! *data* map and joins continuations onto it:
//!
//! ```text
//! for (k, v) in data.into_iter() { … wks: all_continuations.get(&k) … }
//! ```
//!
//! so a waiting continuation on a channel that holds **no data** never appears
//! in the result, and `joins` never appear at all. A speculative sandbox is
//! *full* of exactly that shape — a receiver installed and waiting is the
//! normal quiescent state. [`d0_teeth_to_map_is_not_a_faithful_readback`] pins
//! this, and the two direction tests use `HotStore::snapshot()` (the exact
//! `HotStoreState`) as the primary observable, with `to_map()` reported
//! alongside.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::tagged_continuation::TaggedCont;
use models::rhoapi::{
    BindPattern, ListParWithRandom, Par, ParWithRandom, Receive, ReceiveBind, Send,
    TaggedContinuation,
};
use models::rust::utils::{new_freevar_par, new_gint_par, new_gstring_par};
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::has_cost::HasCost;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime};
use rho_pure_eval::Env;
use rspace_plus_plus::rspace::checkpoint::SoftCheckpoint;
use rspace_plus_plus::rspace::hot_store::HotStoreState;
use rspace_plus_plus::rspace::internal::{Datum, Row, WaitingContinuation};
use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::rspace_interface::ISpace;
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;

type Space = RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation>;
type State = HotStoreState<Par, BindPattern, ListParWithRandom, TaggedContinuation>;

// ══════════════════════════════════════════════════════════════════════════
// Sandbox construction — the `rholang-runtime/src/step.rs:605-631` template
// ══════════════════════════════════════════════════════════════════════════

/// A FRESH, EMPTY, in-memory space. `create_checkpoint` is never called on it,
/// so `history.root()` stays the empty root for its whole life — the precise
/// condition the install's exactness rests on.
async fn fresh_sandbox() -> Space {
    let mut kvm = InMemoryStoreManager::new();
    let store = kvm
        .r_space_stores()
        .await
        .expect("in-memory rspace stores must build");
    RSpace::create(store, Arc::new(Box::new(Matcher)))
        .expect("a fresh in-memory RSpace must build")
}

async fn install(space: &Space, state: State) {
    let checkpoint = SoftCheckpoint {
        cache_snapshot: state,
        log: Vec::new(),
        produce_counter: BTreeMap::new(),
    };
    space
        .revert_to_soft_checkpoint(checkpoint)
        .await
        .expect("revert_to_soft_checkpoint must succeed on a fresh sandbox");
}

fn snapshot(space: &Space) -> State {
    space.get_store().snapshot()
}

// ══════════════════════════════════════════════════════════════════════════
// Fixture state — one of every shape a speculative sandbox actually holds
// ══════════════════════════════════════════════════════════════════════════

fn chan(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

fn payload(value: i64) -> ListParWithRandom {
    ListParWithRandom {
        pars: vec![new_gint_par(value, Vec::new(), false)],
        random_state: Blake2b512Random::create_from_bytes(&[7u8, 7, 7]).to_bytes(),
    }
}

fn datum(channel: &Par, value: i64, persist: bool) -> Datum<ListParWithRandom> {
    Datum::create(channel, payload(value), persist)
}

fn wildcard_bind() -> BindPattern {
    BindPattern {
        patterns: vec![new_freevar_par(0, Vec::new())],
        remainder: None,
        free_count: 1,
    }
}

fn continuation_body(marker: i64) -> TaggedContinuation {
    TaggedContinuation {
        tagged_cont: Some(TaggedCont::ParBody(ParWithRandom {
            body: Some(Par::default().with_sends(vec![Send {
                chan: Some(chan("x3-marker")),
                data: vec![new_gint_par(marker, Vec::new(), false)],
                persistent: false,
                locally_free: Vec::new(),
                connective_used: false,
            }])),
            random_state: Blake2b512Random::create_from_bytes(&[9u8, 9]).to_bytes(),
        })),
        // No `where` guard on these fixtures — the guard path is X1's subject.
        guard: None,
    }
}

fn waiting(
    channels: &Vec<Par>,
    persist: bool,
    peeks: BTreeSet<i32>,
    marker: i64,
) -> WaitingContinuation<BindPattern, TaggedContinuation> {
    let patterns = vec![wildcard_bind(); channels.len()];
    WaitingContinuation::create(
        channels,
        &patterns,
        &continuation_body(marker),
        persist,
        peeks,
    )
}

/// A state exercising every field of `HotStoreState`, including the two the
/// design's proposed `to_map()` readback cannot see:
///
/// * `data` on a channel that ALSO has a waiting continuation (visible),
/// * a waiting continuation on a channel with NO data (invisible to `to_map`),
/// * a JOIN over two channels plus its `joins` index entries (invisible),
/// * an `installed_continuation` + `installed_joins` (the `install` lane),
/// * a PEEK continuation (`peeks = {0}`) and a PERSISTENT one.
fn fixture_state() -> State {
    let mut state = State::default();

    // ── data ──
    state
        .data
        .insert(chan("alpha"), vec![datum(&chan("alpha"), 1, false), datum(&chan("alpha"), 2, false)]);
    state
        .data
        .insert(chan("gamma"), vec![datum(&chan("gamma"), 3, true)]);

    // ── a linear continuation on a channel that HAS data ──
    state
        .continuations
        .insert(vec![chan("alpha")], vec![waiting(&vec![chan("alpha")], false, BTreeSet::new(), 10)]);

    // ── a PEEK continuation on a channel with NO data (to_map-invisible) ──
    let mut peeks = BTreeSet::new();
    peeks.insert(0i32);
    state
        .continuations
        .insert(vec![chan("beta")], vec![waiting(&vec![chan("beta")], false, peeks, 11)]);

    // ── a PERSISTENT continuation, and a JOIN over two channels ──
    let join_channels = vec![chan("delta"), chan("epsilon")];
    state.continuations.insert(
        join_channels.clone(),
        vec![waiting(&join_channels, true, BTreeSet::new(), 12)],
    );
    state.joins.insert(chan("delta"), vec![join_channels.clone()]);
    state.joins.insert(chan("epsilon"), vec![join_channels.clone()]);

    // ── the `install` lane ──
    state.installed_continuations.insert(
        vec![chan("zeta")],
        waiting(&vec![chan("zeta")], true, BTreeSet::new(), 13),
    );
    state
        .installed_joins
        .insert(chan("zeta"), vec![vec![chan("zeta")]]);

    state
}

// ══════════════════════════════════════════════════════════════════════════
// Comparison
// ══════════════════════════════════════════════════════════════════════════

/// Every field difference between two states, as human-readable lines. Empty
/// ⟺ the two states are identical.
fn diff(expected: &State, actual: &State) -> Vec<String> {
    let mut out = Vec::new();
    if expected.data != actual.data {
        out.push(format!(
            "data differs:\n  expected {} channel(s): {:?}\n  actual   {} channel(s): {:?}",
            expected.data.len(),
            sorted_keys(&expected.data),
            actual.data.len(),
            sorted_keys(&actual.data)
        ));
    }
    if expected.continuations != actual.continuations {
        out.push(format!(
            "continuations differ:\n  expected {:?}\n  actual   {:?}",
            sorted_group_keys(&expected.continuations),
            sorted_group_keys(&actual.continuations)
        ));
    }
    if expected.installed_continuations != actual.installed_continuations {
        out.push("installed_continuations differ".to_string());
    }
    if expected.joins != actual.joins {
        out.push(format!(
            "joins differ:\n  expected {:?}\n  actual   {:?}",
            sorted_keys(&expected.joins),
            sorted_keys(&actual.joins)
        ));
    }
    if expected.installed_joins != actual.installed_joins {
        out.push("installed_joins differ".to_string());
    }
    out
}

fn sorted_keys<V>(map: &HashMap<Par, V>) -> Vec<String> {
    let mut keys: Vec<String> = map.keys().map(describe).collect();
    keys.sort();
    keys
}

fn sorted_group_keys<V>(map: &HashMap<Vec<Par>, V>) -> Vec<String> {
    let mut keys: Vec<String> = map
        .keys()
        .map(|group| group.iter().map(describe).collect::<Vec<_>>().join("+"))
        .collect();
    keys.sort();
    keys
}

/// A short, DISTINCTIVE name for a channel — the `GString` when there is one,
/// else a truncated debug. Distinctive on purpose: the report matches on these
/// and a substring collision would silently weaken an assertion.
fn describe(par: &Par) -> String {
    for expr in &par.exprs {
        if let Some(models::rhoapi::expr::ExprInstance::GString(s)) = &expr.expr_instance {
            return format!("@\"{s}\"");
        }
    }
    let debug = format!("{par:?}");
    format!("<{}>", &debug[..debug.len().min(48)])
}

fn total_data(state: &State) -> usize {
    state.data.values().map(|v| v.len()).sum()
}

fn total_continuations(state: &State) -> usize {
    state.continuations.values().map(|v| v.len()).sum::<usize>()
        + state.installed_continuations.len()
}

fn describe_state(label: &str, state: &State) {
    println!(
        "  {label:22} data={} ({} channels)  conts={} ({} groups)  installed_conts={}  joins={}  installed_joins={}",
        total_data(state),
        state.data.len(),
        total_continuations(state),
        state.continuations.len(),
        state.installed_continuations.len(),
        state.joins.len(),
        state.installed_joins.len(),
    );
}

// ══════════════════════════════════════════════════════════════════════════
// D0 — TEETH. Both the comparator and the `to_map()` claim.
// ══════════════════════════════════════════════════════════════════════════

/// The comparator must SEE a planted difference. Without this, every "no diff"
/// below is worthless.
#[tokio::test]
async fn d0_teeth_the_comparator_sees_a_planted_difference() {
    let base = fixture_state();

    // (1) one extra datum
    let mut plus_datum = fixture_state();
    plus_datum
        .data
        .get_mut(&chan("alpha"))
        .expect("alpha has data")
        .push(datum(&chan("alpha"), 999, false));
    assert!(
        !diff(&base, &plus_datum).is_empty(),
        "TEETH FAILED: the comparator cannot see an extra datum"
    );

    // (2) one extra waiting continuation, on a channel with NO data
    let mut plus_cont = fixture_state();
    plus_cont.continuations.insert(
        vec![chan("x3-planted-continuation-channel")],
        vec![waiting(
            &vec![chan("x3-planted-continuation-channel")],
            false,
            BTreeSet::new(),
            777,
        )],
    );
    assert!(
        !diff(&base, &plus_cont).is_empty(),
        "TEETH FAILED: the comparator cannot see an extra continuation"
    );

    // (3) one extra join
    let mut plus_join = fixture_state();
    plus_join
        .joins
        .insert(chan("x3-planted-join-channel"), vec![vec![chan("x3-planted-join-channel")]]);
    assert!(
        !diff(&base, &plus_join).is_empty(),
        "TEETH FAILED: the comparator cannot see an extra join"
    );

    // (4) and it must report NO difference for a state compared with itself
    assert!(
        diff(&base, &fixture_state()).is_empty(),
        "the comparator reports a spurious difference between two identical states: {:?}",
        diff(&base, &fixture_state())
    );
}

/// ⚠ The design's proposed readback, `to_map()`, is NOT faithful. This test
/// documents exactly what it drops, so the design stops relying on it.
#[tokio::test]
async fn d0_teeth_to_map_is_not_a_faithful_readback() {
    let space = fresh_sandbox().await;
    let planted = fixture_state();
    install(&space, planted.clone()).await;

    let read_back = snapshot(&space);
    let map: HashMap<Vec<Par>, Row<BindPattern, ListParWithRandom, TaggedContinuation>> =
        space.to_map().await;

    println!("\n── X3 D0: snapshot() vs to_map() over the same installed state ──");
    describe_state("installed", &planted);
    describe_state("snapshot()", &read_back);
    println!(
        "  to_map()               {} row(s): {:?}",
        map.len(),
        sorted_group_keys(&map)
    );

    // snapshot() sees everything…
    assert_eq!(total_continuations(&read_back), 4, "snapshot must see all 4 continuations");
    assert_eq!(read_back.joins.len(), 2, "snapshot must see both join index entries");

    // …to_map() does not. A continuation on a data-less channel is INVISIBLE.
    let beta_group = vec![chan("beta")];
    assert!(
        !map.contains_key(&beta_group),
        "to_map() unexpectedly surfaced the data-less `@\"beta\"` continuation — if this \
         assertion starts failing, `to_map` was fixed and the design may use it after all"
    );
    let join_group = vec![chan("delta"), chan("epsilon")];
    assert!(
        !map.contains_key(&join_group),
        "to_map() unexpectedly surfaced the data-less join group"
    );
    assert_eq!(
        map.len(),
        2,
        "to_map() should surface exactly the two channels that hold data: {:?}",
        sorted_group_keys(&map)
    );
}

// ══════════════════════════════════════════════════════════════════════════
// D1 — ⟶ the install direction
// ══════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn d1_hand_built_state_installs_exactly() {
    let space = fresh_sandbox().await;
    let planted = fixture_state();

    // A fresh sandbox starts genuinely empty (the premise's other half).
    let before = snapshot(&space);
    println!("\n── X3 D1: install a hand-built state into a fresh sandbox ──");
    describe_state("fresh sandbox", &before);
    assert!(
        diff(&State::default(), &before).is_empty(),
        "a fresh sandbox is not empty: {:?}",
        diff(&State::default(), &before)
    );

    install(&space, planted.clone()).await;
    let after = snapshot(&space);
    describe_state("planted", &planted);
    describe_state("read back", &after);

    let differences = diff(&planted, &after);
    assert!(
        differences.is_empty(),
        "X3 REFUTED (install direction) — the state that came back is not the \
         state that went in:\n  {}",
        differences.join("\n  ")
    );

    // And the reads that the RUNTIME uses (not just the raw snapshot) agree:
    // `get_data` consults the cold history layer, so this is where a non-empty
    // cold root would show up.
    let alpha = space.get_data(&chan("alpha")).await;
    assert_eq!(alpha.len(), 2, "get_data must see exactly the planted data, got {alpha:?}");
    let beta_conts = space.get_waiting_continuations(vec![chan("beta")]).await;
    assert_eq!(
        beta_conts.len(),
        1,
        "get_waiting_continuations must see the planted data-less continuation"
    );
    let joins = space.get_joins(chan("delta")).await;
    assert_eq!(joins.len(), 1, "get_joins must see the planted join, got {joins:?}");
}

// ══════════════════════════════════════════════════════════════════════════
// D2 — ⟵ the erase direction
// ══════════════════════════════════════════════════════════════════════════

/// A program whose effects are unmistakable and DISTINCTIVELY named: two
/// resting sends on `@"x3-run-residue"`, and a receive left waiting on
/// `@"x3-run-waiting"` (no datum, so it is exactly the `to_map`-invisible
/// shape). If the second install leaks, these are what leak.
fn residue_program() -> Par {
    let sends = Par::default().with_sends(vec![
        Send {
            chan: Some(chan("x3-run-residue")),
            data: vec![new_gint_par(101, Vec::new(), false)],
            persistent: false,
            locally_free: Vec::new(),
            connective_used: false,
        },
        Send {
            chan: Some(chan("x3-run-residue")),
            data: vec![new_gint_par(102, Vec::new(), false)],
            persistent: false,
            locally_free: Vec::new(),
            connective_used: false,
        },
    ]);
    let receive = Par::default().with_receives(vec![Receive {
        binds: vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(chan("x3-run-waiting")),
            remainder: None,
            free_count: 1,
        }],
        body: Some(Par::default()),
        persistent: false,
        peek: false,
        bind_count: 1,
        locally_free: Vec::new(),
        connective_used: false,
        condition: None,
    }]);
    sends.append(receive)
}

#[tokio::test]
async fn d2_reinstall_erases_a_previous_runs_effects() {
    let space = fresh_sandbox().await;
    let planted = fixture_state();

    install(&space, planted.clone()).await;

    // ── run a program that leaves obvious residue ────────────────────────
    // `RSpace` is `Clone` and every field is `Arc`-shared, so the runtime and
    // this test observe the SAME store.
    let mut runtime = create_rho_runtime(
        space.clone(),
        Arc::new(HashMap::new()),
        false,
        &mut Vec::new(),
        ExternalServices::noop(),
    )
    .await;
    runtime.cost().set(Cost::unsafe_max());
    runtime
        .inj(
            residue_program(),
            Env::new(),
            Blake2b512Random::create_from_bytes(&[3u8, 1, 4, 1, 5]),
        )
        .await
        .expect("the residue program must reduce");

    let dirty = snapshot(&space);
    println!("\n── X3 D2: install → inj → install ──");
    describe_state("after inj (dirty)", &dirty);
    let dirtied = diff(&planted, &dirty);
    assert!(
        !dirtied.is_empty(),
        "TEETH FAILED: the residue program left NO trace, so the erase test \
         below would pass vacuously"
    );
    assert!(
        dirty.data.contains_key(&chan("x3-run-residue")),
        "TEETH FAILED: the two sends did not rest on @\"x3-run-residue\""
    );
    assert!(
        dirty.continuations.contains_key(&vec![chan("x3-run-waiting")]),
        "TEETH FAILED: the receive did not wait on @\"x3-run-waiting\""
    );

    // ── the second install ───────────────────────────────────────────────
    install(&space, planted.clone()).await;
    let clean = snapshot(&space);
    describe_state("after re-install", &clean);

    let residue = diff(&planted, &clean);
    assert!(
        residue.is_empty(),
        "X3 REFUTED (erase direction) — the second install did not fully erase \
         the run:\n  {}",
        residue.join("\n  ")
    );
    assert!(
        !clean.data.contains_key(&chan("x3-run-residue")),
        "the run's resting sends survived the re-install"
    );
    assert!(
        !clean.continuations.contains_key(&vec![chan("x3-run-waiting")]),
        "the run's waiting receive survived the re-install"
    );

    // The runtime-facing reads agree too — this is where a cold-layer leak
    // would surface, since `get_data` (unlike `snapshot`) consults history.
    assert!(
        space.get_data(&chan("x3-run-residue")).await.is_empty(),
        "get_data still sees the erased run's data — the COLD layer leaked"
    );
    assert!(
        space
            .get_waiting_continuations(vec![chan("x3-run-waiting")])
            .await
            .is_empty(),
        "get_waiting_continuations still sees the erased run's receive"
    );
}

/// The install must also be exact when the target state is EMPTY — the
/// "sandbox reset between branches" operation the design performs most often.
#[tokio::test]
async fn d3_reinstall_of_the_empty_state_returns_a_pristine_sandbox() {
    let space = fresh_sandbox().await;
    install(&space, fixture_state()).await;

    let mut runtime = create_rho_runtime(
        space.clone(),
        Arc::new(HashMap::new()),
        false,
        &mut Vec::new(),
        ExternalServices::noop(),
    )
    .await;
    runtime.cost().set(Cost::unsafe_max());
    runtime
        .inj(
            residue_program(),
            Env::new(),
            Blake2b512Random::create_from_bytes(&[2u8, 7, 1, 8]),
        )
        .await
        .expect("the residue program must reduce");

    install(&space, State::default()).await;
    let clean = snapshot(&space);
    println!("\n── X3 D3: install(empty) after a dirty run ──");
    describe_state("after install(empty)", &clean);

    let residue = diff(&State::default(), &clean);
    assert!(
        residue.is_empty(),
        "X3 REFUTED — installing the EMPTY state did not produce a pristine \
         sandbox:\n  {}",
        residue.join("\n  ")
    );
    assert!(space.to_map().await.is_empty(), "to_map must be empty after install(empty)");
}
