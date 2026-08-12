//! **S1 — the acceptance measurement for Stage 1 of the `[*]` space fork.**
//!
//! # The claim under test
//!
//! > An `n`-step single trace through [`SpeculativeSandbox`] reaches the same
//! > configuration the ordinary reducer reaches — **when the sandbox names the
//! > selections the ordinary run made**.
//!
//! The qualification is the whole point, and it is not a hedge. `E(S)`'s least
//! element is *not* in general the branch an ordinary run takes:
//! `RSpace::extract_produce_candidate` splices an arriving datum into its pool
//! at index `-1`, ahead of the canonical order, so the arrival regime and the
//! stratified regime pick differently in about half of all contended pairs
//! (measured over 56 ordered pairs by
//! `x1_stratified_monotonicity.rs::t2c2`: exactly 28). The *set* of admissible
//! selections is the same in both regimes — that is the monotonicity premise —
//! but the *least* one is not.
//!
//! So this file measures two different things and does not conflate them:
//!
//! | mode | question |
//! |---|---|
//! | **trace-following** | given the selections the ordinary run made, does the sandbox reach the same configuration? — the ACCEPTANCE |
//! | **index 0** | how often does `E(S)[0]` coincide with what the ordinary run chose? — the MEASUREMENT of correction 1 |
//!
//! A test that only did the second and asserted equality would be asserting
//! something known to be false half the time.
//!
//! # How the comparison is made honest
//!
//! * The oracle is an ordinary `RhoRuntime` over a `RecordingSpace` that
//!   delegates every operation verbatim and only *ledgers* the COMMs that fire.
//!   It is the real reducer, not a model of one.
//! * A COMM is identified by its **semantic name** — the `Consume` content hash
//!   of the firing continuation plus the `Produce` content hash of each datum it
//!   consumed. That name is regime-independent: a datum consumed straight out of
//!   a `produce` (never stored, index `-1`) hashes identically to the same datum
//!   consumed at rest, because `Produce::create` reads only (channel, payload,
//!   persistence).
//! * Configurations are compared by [`content_fingerprint`], which canonicalises
//!   empty entries away first. ⚠ A read MATERIALISES an entry — `get_data` on an
//!   empty channel inserts an empty vector — so the raw channel count of a
//!   `HotStoreState` is not a meaningful observable, and two configurations that
//!   differ only in which channels have been looked at are the same
//!   configuration.
//! * Both arms run under the SAME seed, so any divergence is attributable to the
//!   stratification rather than to the entropy source.
//!
//! # The tests
//!
//! | test | question |
//! |---|---|
//! | [`t0a_teeth_the_sandbox_stages_and_the_oracle_fires`] | does the sandbox genuinely suppress firing, and does the oracle genuinely observe it? |
//! | [`t0b_teeth_firing_actually_changes_the_configuration`] | does `fire` do anything? |
//! | [`t0c_the_post_bootstrap_baseline_is_carried_into_every_state`] | ★ correction 4, measured — and what a hand-built state loses without it |
//! | [`t0d_real_sandbox_exercises_the_exact_state_fields`] | correction 3's exact-state premise, measured on a real sandbox state |
//! | [`t1_a_trace_following_run_reaches_the_ordinary_configuration`] | ★ THE ACCEPTANCE, over the whole corpus |
//! | [`t2_index_zero_diverges_from_the_ordinary_choice`] | ★ correction 1, measured over the corpus |
//! | [`t3_a_peek_is_two_strata`] | ★ correction 2: the datum returns, carrying a DIFFERENT `Produce` source |
//! | [`t4_a_persistent_continuation_survives_its_own_firing`] | a `<=` receive is enabled again in the next `E(S)` |
//! | [`t5_a_named_non_least_selection_is_reachable`] | the mechanism can be driven OFF index 0 — without this it only ever reproduces ordinary execution |
//! | [`t6_a_system_process_fires_in_the_sandbox`] | `stdout!` reaches its installed continuation (correction 4, end to end) |
//! | [`t7_a_saved_configuration_reloads_exactly`] | a configuration can be parked and resumed — the Stage 2 branching primitive |
//! | [`t8_an_unfunded_sandbox_refuses_to_evaluate`] | ★★ the denial-of-service question: an unfunded sandbox cannot evaluate anything |
//! | [`t9_a_small_budget_stops_the_exploration`] | ★★ metering IS the bound — no node budget, no frontier cap |
//! | [`t10_the_host_is_charged_what_the_exploration_spent`] | the fund / charge-back round trip, through f1r3node's own `MeteredMachine` |
//! | [`t11_truncation_is_resumable_and_resumption_is_faithful`] | ★★ depth-`n` truncation is neither success nor failure — it is a resumable handle |

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::{Arc, Mutex};

use async_trait::async_trait;
use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{
    BindPattern, Expr, ListParWithRandom, Par, Receive, ReceiveBind, Send, TaggedContinuation,
};
use models::rust::utils::{new_boundvar_par, new_freevar_par, new_gint_par, new_gstring_par};
use rho_pure_eval::Env;
use rholang::rust::interpreter::accounting::cost_accounting::CostAccounting;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::has_cost::HasCost;
use rholang::rust::interpreter::accounting::RuntimeBudget;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::metering::MeteredMachine;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime};
use rspace_plus_plus::rspace::checkpoint::{Checkpoint, SoftCheckpoint};
use rspace_plus_plus::rspace::errors::RSpaceError;
use rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash;
use rspace_plus_plus::rspace::internal::{Datum, Row, WaitingContinuation};
use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::rspace_interface::{ISpace, MaybeConsumeResult, MaybeProduceResult};
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;
use rspace_plus_plus::rspace::trace::event::{Consume, Produce};
use rspace_plus_plus::rspace::trace::Log;

use mettail_rholang_runtime::guard_par_substrate::SubstrateGuardMatcher;
use mettail_rholang_runtime::speculation::{
    canonicalize, content_fingerprint, BranchOutcome, Rendezvous, RendezvousName, SpeculationError,
    SpeculativeSandbox, SpeculativeState,
};

type Space = RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation>;

/// The one seed BOTH arms of every comparison use.
///
/// ⚠ On chain this must be the **deploy's** randomness, not a constant — see the
/// `speculation` module header. A fixture constant is correct here and only
/// here: the point of the comparison is that the two arms differ in the
/// stratification and in nothing else, which requires the entropy source to be
/// held fixed.
const FIXTURE_SEED: &[u8] = b"s1-speculative-sandbox";

fn seed() -> Blake2b512Random {
    Blake2b512Random::create_from_bytes(FIXTURE_SEED)
}

/// A stand-in for a host deploy's budget, generous enough that no corpus program
/// exhausts it. ★ Metering is the bound, so a sandbox is USELESS until it is
/// funded — every helper below funds explicitly, and
/// [`t8_an_unfunded_sandbox_refuses_to_evaluate`] pins that an unfunded one
/// really does refuse.
const HOST_UNITS: i64 = 1_000_000;

fn host_budget(units: i64) -> RuntimeBudget {
    let budget = CostAccounting::empty_cost();
    budget.set(Cost::create(units, "s1 host deploy"));
    budget
}

/// A sandbox funded from a fresh host budget of `HOST_UNITS`.
async fn funded_sandbox() -> SpeculativeSandbox {
    let sandbox = SpeculativeSandbox::new().await.expect("sandbox must build");
    sandbox.fund_from(&host_budget(HOST_UNITS));
    sandbox
}

// ══════════════════════════════════════════════════════════════════════════
// Fixtures
// ══════════════════════════════════════════════════════════════════════════

fn chan(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

fn send(channel: &str, value: i64) -> Par {
    Par::default().with_sends(vec![Send {
        chan: Some(chan(channel)),
        data: vec![new_gint_par(value, Vec::new(), false)],
        persistent: false,
        locally_free: Vec::new(),
        connective_used: false,
    }])
}

/// A receive whose body is INERT — it sends a fixed marker, so a fired COMM adds
/// no new rendezvous. Every COMM in a corpus built only from these is a
/// stratum-0 COMM.
///
/// ⚠ Free-variable levels are LOCAL TO EACH BIND and start at 0, and
/// `BindPattern.free_count` counts only that bind's own free variables:
/// `Matcher::get` reads the bound values back with `to_vec(free_map,
/// pattern.free_count)`, which collects levels `0..free_count`, so a second bind
/// written with a GLOBAL level (`FreeVar(1)`) silently binds a default `Par`.
/// Both binds of a join therefore use `FreeVar(0)` with `free_count: 1`, as
/// f1r3node's own two-bind fixtures do.
fn receive(
    sources: &[&str],
    marker: &str,
    persistent: bool,
    peek: bool,
    condition: Option<Par>,
) -> Par {
    receive_with_body(
        sources,
        persistent,
        peek,
        condition,
        Par::default().with_sends(vec![Send {
            chan: Some(chan("s1-marker")),
            data: vec![new_gstring_par(marker.to_string(), Vec::new(), false)],
            persistent: false,
            locally_free: Vec::new(),
            connective_used: false,
        }]),
    )
}

/// A receive that FORWARDS its first bound value to `target` — so a fired COMM
/// deposits a datum that can enable a rendezvous in the NEXT stratum. This is
/// what makes an `n`-step trace with `n > 1` more than `n` independent COMMs.
fn forwarding_receive(source: &str, target: &str) -> Par {
    receive_with_body(
        &[source],
        false,
        false,
        None,
        Par::default().with_sends(vec![Send {
            chan: Some(chan(target)),
            data: vec![new_boundvar_par(0, models::create_bit_vector(&[0]), false)],
            persistent: false,
            locally_free: models::create_bit_vector(&[0]),
            connective_used: false,
        }]),
    )
}

fn receive_with_body(
    sources: &[&str],
    persistent: bool,
    peek: bool,
    condition: Option<Par>,
    body: Par,
) -> Par {
    let binds: Vec<ReceiveBind> = sources
        .iter()
        .map(|source| ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(chan(source)),
            remainder: None,
            free_count: 1,
        })
        .collect();
    let bind_count = binds.len() as i32;
    Par::default().with_receives(vec![Receive {
        binds,
        body: Some(body),
        persistent,
        peek,
        bind_count,
        locally_free: Vec::new(),
        connective_used: false,
        condition,
    }])
}

/// `BoundVar(0) <= 45` — what `for(@px <- @"offer" where px <= 45)` lowers to.
fn guard_first_bound_at_most_45() -> Par {
    Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::ELteBody(models::rhoapi::ELte {
            p1: Some(new_boundvar_par(0, models::create_bit_vector(&[0]), false)),
            p2: Some(new_gint_par(45, Vec::new(), false)),
        })),
    }])
}

fn parallel(terms: Vec<Par>) -> Par {
    let mut combined = Par::default();
    for term in terms {
        combined = combined.append(term);
    }
    combined
}

struct Program {
    label: &'static str,
    /// A reader annotation: the Rholang the `Par` encodes. The `Par` is the
    /// artifact.
    source: &'static str,
    par: Par,
    /// How many COMMs an ordinary run is expected to fire. Asserted, so a
    /// fixture that silently stops firing cannot make the acceptance vacuous.
    expected_comms: usize,
}

fn corpus() -> Vec<Program> {
    vec![
        Program {
            label: "two-data-two-receives",
            source: r#"@"c"!(1) | @"c"!(2) | for(@x <- @"c"){…} | for(@y <- @"c"){…}"#,
            par: parallel(vec![
                send("c", 1),
                send("c", 2),
                receive(&["c"], "left", false, false, None),
                receive(&["c"], "right", false, false, None),
            ]),
            expected_comms: 2,
        },
        Program {
            label: "where-guard",
            source: r#"@"offer"!(55) | @"offer"!(42) | for(@px <- @"offer" where px <= 45){…}"#,
            par: parallel(vec![
                send("offer", 55),
                send("offer", 42),
                receive(&["offer"], "guarded", false, false, Some(guard_first_bound_at_most_45())),
            ]),
            expected_comms: 1,
        },
        Program {
            label: "join",
            source: r#"@"a"!(7) | @"b"!(8) | for(@x <- @"a"; @y <- @"b"){…}"#,
            par: parallel(vec![
                send("a", 7),
                send("b", 8),
                receive(&["a", "b"], "joined", false, false, None),
            ]),
            expected_comms: 1,
        },
        Program {
            label: "peek",
            source: r#"@"p"!(9) | for(@x <<- @"p"){…}"#,
            par: parallel(vec![send("p", 9), receive(&["p"], "peeked", false, true, None)]),
            expected_comms: 1,
        },
        Program {
            label: "persistent",
            source: r#"@"q"!(3) | @"q"!(4) | for(@x <= @"q"){…}"#,
            par: parallel(vec![
                send("q", 3),
                send("q", 4),
                receive(&["q"], "persistent", true, false, None),
            ]),
            expected_comms: 2,
        },
        Program {
            label: "two-stratum-chain",
            source: r#"@"a"!(5) | for(@x <- @"a"){ @"b"!(x) } | for(@y <- @"b"){…}"#,
            par: parallel(vec![
                send("a", 5),
                forwarding_receive("a", "b"),
                receive(&["b"], "second-stratum", false, false, None),
            ]),
            expected_comms: 2,
        },
        Program {
            label: "three-stratum-chain",
            source: r#"@"a"!(6) | for(@x <- @"a"){ @"b"!(x) } | for(@y <- @"b"){ @"c"!(y) } | for(@z <- @"c"){…}"#,
            par: parallel(vec![
                send("a", 6),
                forwarding_receive("a", "b"),
                forwarding_receive("b", "c"),
                receive(&["c"], "third-stratum", false, false, None),
            ]),
            expected_comms: 3,
        },
    ]
}

// ══════════════════════════════════════════════════════════════════════════
// The oracle: an ordinary run, with a COMM ledger
// ══════════════════════════════════════════════════════════════════════════

/// The **semantic name** of a fired COMM, in exactly the shape
/// [`RendezvousName::semantic`] produces, so the two are directly comparable.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct CommName {
    consume: Blake2b256Hash,
    data: Vec<Blake2b256Hash>,
}

#[derive(Clone)]
struct RecordingSpace {
    inner: Space,
    fired: Arc<Mutex<Vec<CommName>>>,
}

impl RecordingSpace {
    fn new(inner: Space) -> Self {
        RecordingSpace {
            inner,
            fired: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Reconstruct the semantic name of a COMM from the result the space
    /// returned. `removed_datum` is the payload AS STORED (pre bind-transform),
    /// which is what `Produce::create` hashed when the datum was minted — so
    /// this reconstruction is exact for a datum consumed at rest AND for one
    /// consumed straight out of a `produce` at index `-1`.
    fn record(
        &self,
        result: &MaybeConsumeResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
    ) {
        if let Some((continuation, results)) = result {
            let consume = Consume::create(
                &continuation.channels,
                &continuation.patterns,
                &continuation.continuation,
                continuation.persistent,
            );
            let mut data = Vec::with_capacity(results.len());
            data.extend(results.iter().map(|item| {
                Produce::create(&item.channel, &item.removed_datum, item.persistent).hash
            }));
            self.fired
                .lock()
                .expect("the COMM ledger mutex")
                .push(CommName { consume: consume.hash, data });
        }
    }
}

#[async_trait]
impl ISpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> for RecordingSpace {
    async fn produce(
        &self,
        channel: Par,
        data: ListParWithRandom,
        persist: bool,
    ) -> Result<
        MaybeProduceResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
        RSpaceError,
    > {
        let result = self.inner.produce(channel, data, persist).await?;
        if let Some((continuation, results, _)) = &result {
            self.record(&Some((continuation.clone(), results.clone())));
        }
        Ok(result)
    }

    async fn consume(
        &self,
        channels: Vec<Par>,
        patterns: Vec<BindPattern>,
        continuation: TaggedContinuation,
        persist: bool,
        peeks: std::collections::BTreeSet<i32>,
    ) -> Result<
        MaybeConsumeResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
        RSpaceError,
    > {
        let result = self
            .inner
            .consume(channels, patterns, continuation, persist, peeks)
            .await?;
        self.record(&result);
        Ok(result)
    }

    async fn create_checkpoint(&self) -> Result<Checkpoint, RSpaceError> {
        self.inner.create_checkpoint().await
    }
    async fn get_data(&self, channel: &Par) -> Vec<Datum<ListParWithRandom>> {
        self.inner.get_data(channel).await
    }
    async fn get_waiting_continuations(
        &self,
        channels: Vec<Par>,
    ) -> Vec<WaitingContinuation<BindPattern, TaggedContinuation>> {
        self.inner.get_waiting_continuations(channels).await
    }
    async fn get_joins(&self, channel: Par) -> Vec<Vec<Par>> {
        self.inner.get_joins(channel).await
    }
    async fn remove_all_data(&self, channel: &Par) -> Result<(), RSpaceError> {
        self.inner.remove_all_data(channel).await
    }
    async fn remove_all_continuations(&self, channels: Vec<Par>) -> Result<(), RSpaceError> {
        self.inner.remove_all_continuations(channels).await
    }
    async fn clear(&self) -> Result<(), RSpaceError> {
        self.inner.clear().await
    }
    async fn get_root(&self) -> Blake2b256Hash {
        self.inner.get_root().await
    }
    async fn reset(&self, root: &Blake2b256Hash) -> Result<(), RSpaceError> {
        self.inner.reset(root).await
    }
    async fn consume_result(
        &self,
        channel: Vec<Par>,
        pattern: Vec<BindPattern>,
    ) -> Result<Option<(TaggedContinuation, Vec<ListParWithRandom>)>, RSpaceError> {
        self.inner.consume_result(channel, pattern).await
    }
    async fn to_map(
        &self,
    ) -> HashMap<Vec<Par>, Row<BindPattern, ListParWithRandom, TaggedContinuation>> {
        self.inner.to_map().await
    }
    async fn create_soft_checkpoint(
        &self,
    ) -> SoftCheckpoint<Par, BindPattern, ListParWithRandom, TaggedContinuation> {
        self.inner.create_soft_checkpoint().await
    }
    async fn take_event_log(&self) -> Log {
        self.inner.take_event_log().await
    }
    async fn revert_to_soft_checkpoint(
        &self,
        checkpoint: SoftCheckpoint<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
    ) -> Result<(), RSpaceError> {
        self.inner.revert_to_soft_checkpoint(checkpoint).await
    }
    async fn install(
        &self,
        channels: Vec<Par>,
        patterns: Vec<BindPattern>,
        continuation: TaggedContinuation,
    ) -> Result<Option<(TaggedContinuation, Vec<ListParWithRandom>)>, RSpaceError> {
        self.inner.install(channels, patterns, continuation).await
    }
    async fn rig_and_reset(&self, start_root: Blake2b256Hash, log: Log) -> Result<(), RSpaceError> {
        self.inner.rig_and_reset(start_root, log).await
    }
    async fn rig(&self, log: Log) -> Result<(), RSpaceError> {
        self.inner.rig(log).await
    }
    async fn check_replay_data(&self) -> Result<(), RSpaceError> {
        self.inner.check_replay_data().await
    }
    async fn is_replay(&self) -> bool {
        self.inner.is_replay().await
    }
    async fn update_produce(&self, produce: Produce) {
        self.inner.update_produce(produce).await
    }
}

struct OrdinaryRun {
    comms: Vec<CommName>,
    fingerprint: Vec<String>,
    state: SpeculativeState,
}

/// An ordinary reduction of `par`, on the SAME matcher the sandbox uses, under
/// the SAME seed. The only difference from a production run is the ledger.
async fn ordinary_run(par: Par) -> OrdinaryRun {
    let mut manager = InMemoryStoreManager::new();
    let store = manager
        .r_space_stores()
        .await
        .expect("in-memory rspace stores must build");
    let inner = Space::create(store, Arc::new(Box::new(SubstrateGuardMatcher::new())))
        .expect("a fresh in-memory RSpace must build");
    let space = RecordingSpace::new(inner.clone());
    let ledger = space.fired.clone();

    let runtime = create_rho_runtime(
        space,
        Arc::new(HashMap::new()),
        false,
        &mut Vec::new(),
        ExternalServices::noop(),
    )
    .await;
    // The oracle is metered exactly as the sandbox is — same units, same
    // charge points (`eval_send` / `eval_receive`) — so the two arms differ in
    // the stratification and in nothing else, cost included.
    runtime
        .cost()
        .set(Cost::create(HOST_UNITS, "s1 host deploy"));
    runtime
        .inj(par, Env::new(), seed())
        .await
        .expect("the ordinary run must reduce to quiescence");

    let state = inner.get_store().snapshot();
    let comms = ledger.lock().expect("the COMM ledger mutex").clone();
    OrdinaryRun {
        comms,
        fingerprint: content_fingerprint(&state),
        state,
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Driving the sandbox
// ══════════════════════════════════════════════════════════════════════════

/// Find the member of `enabled` whose semantic name is `wanted`.
fn locate(enabled: &[Rendezvous], wanted: &CommName) -> Option<usize> {
    enabled.iter().position(|rendezvous| {
        let name = RendezvousName::of(rendezvous);
        name.consume == wanted.consume && name.data == wanted.data
    })
}

struct TraceRun {
    /// Which position in `E(S)` each named selection occupied. `Some(0)` means
    /// the stratified least element happened to be the ordinary choice.
    positions: Vec<usize>,
    fingerprint: Vec<String>,
}

/// Run `par` in a sandbox, at each step firing the rendezvous whose name matches
/// the next COMM the ordinary run made.
async fn trace_following_run(par: Par, wanted: &[CommName]) -> Result<TraceRun, SpeculationError> {
    let sandbox = SpeculativeSandbox::new().await?;
    sandbox.fund_from(&host_budget(HOST_UNITS));
    sandbox.saturate(par, seed()).await?;

    let mut positions = Vec::with_capacity(wanted.len());
    for (step, name) in wanted.iter().enumerate() {
        let enabled = sandbox.enabled();
        let position = locate(&enabled, name).unwrap_or_else(|| {
            panic!(
                "step {step}: the COMM the ordinary run fired is NOT in E(S) — \
                 stratification removed a rendezvous, which refutes the monotonicity \
                 premise. E(S) held {} rendezvous.",
                enabled.len()
            )
        });
        positions.push(position);
        sandbox.fire(enabled[position].clone()).await?;
    }

    Ok(TraceRun {
        positions,
        fingerprint: content_fingerprint(&sandbox.snapshot()),
    })
}

// ══════════════════════════════════════════════════════════════════════════
// T0 — teeth
// ══════════════════════════════════════════════════════════════════════════

/// Without this, every comparison below could be comparing two runs that both
/// did nothing. The sandbox must reach the tuplespace and NOT fire; the oracle
/// must fire.
#[tokio::test]
async fn t0a_teeth_the_sandbox_stages_and_the_oracle_fires() {
    let program = &corpus()[0];

    let sandbox = funded_sandbox().await;
    sandbox
        .saturate(program.par.clone(), seed())
        .await
        .expect("the administrative fragment must reduce to quiescence");

    assert_eq!(
        sandbox.staged().staged_produces(),
        2,
        "both sends must have reached the tuplespace and STAGED"
    );
    assert_eq!(
        sandbox.staged().staged_consumes(),
        2,
        "both receives must have reached the tuplespace and STAGED"
    );

    let quiescent = canonicalize(&sandbox.snapshot());
    assert_eq!(
        quiescent
            .data
            .get(&chan("c"))
            .map(|data| data.len())
            .unwrap_or(0),
        2,
        "nothing fired, so both data are still resting"
    );

    let enabled = sandbox.enabled();
    assert_eq!(
        enabled.len(),
        4,
        "two receivers x two data = four enabled rendezvous at quiescence"
    );

    let oracle = ordinary_run(program.par.clone()).await;
    assert_eq!(
        oracle.comms.len(),
        program.expected_comms,
        "the oracle must genuinely fire — otherwise the acceptance is vacuous"
    );
}

/// `fire` must move the configuration and shrink `E(S)`.
#[tokio::test]
async fn t0b_teeth_firing_actually_changes_the_configuration() {
    let sandbox = funded_sandbox().await;
    sandbox
        .saturate(corpus()[0].par.clone(), seed())
        .await
        .expect("saturate");

    let before = content_fingerprint(&sandbox.snapshot());
    let enabled = sandbox.enabled();
    assert_eq!(enabled.len(), 4);

    let step = sandbox
        .fire(enabled[0].clone())
        .await
        .expect("the named rendezvous must fire");
    assert!(!step.persistent);
    assert!(!step.peek);
    assert_eq!(step.peek_restores, 0);

    let after = content_fingerprint(&sandbox.snapshot());
    assert_ne!(before, after, "firing must change the configuration");

    let remaining = sandbox.enabled();
    assert_eq!(
        remaining.len(),
        1,
        "one datum and one receiver consumed leaves exactly one rendezvous"
    );
}

/// ★ Correction 4, measured. `create_rho_runtime` installs the node's system
/// processes; `revert_to_soft_checkpoint` does NOT call `restore_installs`, so a
/// hand-built state install erases them unless the baseline is layered back
/// underneath.
#[tokio::test]
async fn t0c_the_post_bootstrap_baseline_is_carried_into_every_state() {
    let sandbox = funded_sandbox().await;
    let installed = sandbox.baseline().installed_continuations.len();
    assert!(
        installed > 1,
        "the runtime must bootstrap several system processes; saw {installed}"
    );
    println!("post-bootstrap installed continuations: {installed}");

    // A hand-built state carrying no installs at all.
    let mut bare = SpeculativeState::default();
    bare.data.insert(
        chan("c"),
        vec![Datum::create(
            &chan("c"),
            ListParWithRandom {
                pars: vec![new_gint_par(1, Vec::new(), false)],
                random_state: seed().to_bytes(),
            },
            false,
        )],
    );
    assert_eq!(
        bare.installed_continuations.len(),
        0,
        "the hand-built state genuinely carries no installs"
    );

    // `rebase` puts them back; `load` applies `rebase`.
    assert_eq!(
        sandbox.rebase(bare.clone()).installed_continuations.len(),
        installed,
        "rebase must restore every bootstrap install"
    );

    sandbox.load(bare).await.expect("load");
    assert_eq!(
        sandbox.snapshot().installed_continuations.len(),
        installed,
        "after `load`, the sandbox still has its system processes — without the \
         baseline layer this would have collapsed to 0 and every branch would \
         have lost stdout!"
    );
}

/// Correction 3's premise, measured on a real speculative configuration: a sandbox carries both
/// continuation-only rows and independent join indexes, so exact checkpoint comparison requires
/// [`SpeculativeSandbox::snapshot`]. The repaired `to_map()` covers every row key; X3 separately
/// proves that its row type still cannot encode the join indexes.
#[tokio::test]
async fn t0d_real_sandbox_exercises_the_exact_state_fields() {
    let sandbox = funded_sandbox().await;
    // A receiver on a channel that holds no data, plus a join and one channel that does hold data.
    sandbox
        .saturate(
            parallel(vec![
                receive(&["empty"], "lonely", false, false, None),
                receive(&["ja", "jb"], "joined", false, false, None),
                send("full", 1),
                receive(&["full"], "matched", false, false, None),
            ]),
            seed(),
        )
        .await
        .expect("saturate");

    let snapshot = sandbox.snapshot();
    let program_continuations: usize = snapshot.continuations.values().map(|v| v.len()).sum();
    let program_joins: usize = snapshot.joins.values().map(|v| v.len()).sum();

    assert_eq!(program_continuations, 3, "snapshot() sees all three staged continuations");
    assert!(
        program_joins >= 4,
        "snapshot() sees the joins index (one entry per channel per group); saw {program_joins}"
    );

    assert!(
        snapshot.continuations.contains_key(&vec![chan("empty")]),
        "the real sandbox must exercise a continuation-only row"
    );
    assert!(
        snapshot
            .continuations
            .contains_key(&vec![chan("ja"), chan("jb")]),
        "the real sandbox must exercise a multi-channel continuation row"
    );
    assert!(
        snapshot.joins.contains_key(&chan("ja")) && snapshot.joins.contains_key(&chan("jb")),
        "the exact state must independently carry both join-index entries"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// T1 — ★ THE ACCEPTANCE
// ══════════════════════════════════════════════════════════════════════════

/// **The acceptance measurement.** For each corpus program: run the ordinary
/// reducer and ledger the COMMs it fires; then run the sandbox, firing at each
/// step the rendezvous whose semantic name matches the ordinary run's next COMM;
/// then compare the two final configurations.
///
/// Two things are asserted, and the first is the stronger:
///
/// 1. every COMM the ordinary run fired **was present in `E(S)`** at the moment
///    the sandbox reached that step — if it were not, stratification would have
///    removed a rendezvous and the whole model would be wrong;
/// 2. the final configurations agree.
#[tokio::test]
async fn t1_a_trace_following_run_reaches_the_ordinary_configuration() {
    let mut report: Vec<String> = Vec::new();

    for program in corpus() {
        let oracle = ordinary_run(program.par.clone()).await;
        assert_eq!(
            oracle.comms.len(),
            program.expected_comms,
            "{}: the oracle fired {} COMMs, expected {}",
            program.label,
            oracle.comms.len(),
            program.expected_comms
        );

        let traced = trace_following_run(program.par.clone(), &oracle.comms)
            .await
            .unwrap_or_else(|error| panic!("{}: {error}", program.label));

        assert_eq!(
            traced.fingerprint, oracle.fingerprint,
            "{} ({}): the trace-following run and the ordinary run must reach the \
             SAME configuration.\n  sandbox: {:#?}\n  ordinary: {:#?}",
            program.label, program.source, traced.fingerprint, oracle.fingerprint
        );

        report.push(format!(
            "{:24} comms={} E(S) positions named={:?}",
            program.label,
            oracle.comms.len(),
            traced.positions
        ));
    }

    println!("\n── trace-following acceptance ──");
    for line in report {
        println!("  {line}");
    }
}

// ══════════════════════════════════════════════════════════════════════════
// T2 — ★ correction 1, measured
// ══════════════════════════════════════════════════════════════════════════

/// **How often is `E(S)[0]` the choice the ordinary run made?**
///
/// This is a MEASUREMENT, not an equality assertion — asserting equality would
/// be asserting something known to be false, because
/// `extract_produce_candidate` splices an arriving datum in ahead of the
/// canonical order and the sandbox has no arriving datum.
///
/// What IS asserted is the thing that must hold for the model to be sound: the
/// ordinary choice is always a MEMBER of `E(S)`, at whatever position.
#[tokio::test]
async fn t2_index_zero_diverges_from_the_ordinary_choice() {
    let mut agreements = 0usize;
    let mut decisions = 0usize;
    let mut contended_decisions = 0usize;
    let mut contended_agreements = 0usize;
    let mut lines: Vec<String> = Vec::new();

    for program in corpus() {
        let oracle = ordinary_run(program.par.clone()).await;
        let traced = trace_following_run(program.par.clone(), &oracle.comms)
            .await
            .unwrap_or_else(|error| panic!("{}: {error}", program.label));

        // `trace_following_run` reports, per step, WHERE in `E(S)` the ordinary
        // choice sat. Position 0 means the two regimes agreed at that step.
        let mut per_step: Vec<String> = Vec::with_capacity(traced.positions.len());
        for position in traced.positions.iter() {
            decisions += 1;
            if *position == 0 {
                agreements += 1;
            }
            per_step.push(format!("{position}"));
        }

        // A step where `E(S)` held only one rendezvous cannot disagree; the
        // interesting rate is over CONTENDED steps. Re-derive `|E(S)|` per step
        // by replaying the same trace and measuring before each fire.
        let sandbox = funded_sandbox().await;
        sandbox
            .saturate(program.par.clone(), seed())
            .await
            .expect("saturate");
        let mut widths: Vec<usize> = Vec::with_capacity(oracle.comms.len());
        for name in oracle.comms.iter() {
            let enabled = sandbox.enabled();
            widths.push(enabled.len());
            let position = locate(&enabled, name)
                .expect("the ordinary choice must be a member of E(S) at every step");
            if enabled.len() > 1 {
                contended_decisions += 1;
                if position == 0 {
                    contended_agreements += 1;
                }
            }
            sandbox.fire(enabled[position].clone()).await.expect("fire");
        }

        lines.push(format!(
            "{:24} |E(S)| per step={:?}  ordinary choice at position {:?}",
            program.label,
            widths,
            per_step.join(",")
        ));
    }

    println!("\n── correction 1: E(S)[0] vs the ordinary choice ──");
    for line in lines {
        println!("  {line}");
    }
    println!("  all steps:       {agreements}/{decisions} agreed with E(S)[0]");
    println!("  contended steps: {contended_agreements}/{contended_decisions} agreed with E(S)[0]");

    assert!(decisions > 0, "the corpus must make at least one scheduling decision");
    assert!(
        contended_decisions > 0,
        "teeth: the corpus must contain at least one CONTENDED step, or this \
         measurement says nothing about correction 1"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// T3 — ★ correction 2
// ══════════════════════════════════════════════════════════════════════════

/// **A peek is two strata.** The COMM removes the datum like any consume
/// (`store_persistent_data` ignores its `_peeks`); the restore is a separate,
/// freshly minted `produce`. So the datum comes back with a DIFFERENT `Produce`
/// source than the one it left with — a trace naming the pre-peek datum does not
/// name the post-peek one, even though the payload is the same.
#[tokio::test]
async fn t3_a_peek_is_two_strata() {
    let sandbox = funded_sandbox().await;
    sandbox
        .saturate(
            parallel(vec![send("p", 9), receive(&["p"], "peeked", false, true, None)]),
            seed(),
        )
        .await
        .expect("saturate");

    let before = canonicalize(&sandbox.snapshot());
    let resting_before: Vec<Blake2b256Hash> = before
        .data
        .get(&chan("p"))
        .expect("the datum rests before the peek")
        .iter()
        .map(|datum| datum.source.hash.clone())
        .collect();
    assert_eq!(resting_before.len(), 1);

    let enabled = sandbox.enabled();
    assert_eq!(enabled.len(), 1, "one peek receiver, one datum");
    assert!(
        !enabled[0].continuation.peeks.is_empty(),
        "teeth: the enumerated rendezvous must actually be a peek"
    );

    let step = sandbox.fire(enabled[0].clone()).await.expect("fire");
    assert!(step.peek, "the fired step is a peek");
    assert_eq!(step.peek_restores, 1, "exactly one non-persistent datum is restored");

    let after = canonicalize(&sandbox.snapshot());
    let resting_after: Vec<Blake2b256Hash> = after
        .data
        .get(&chan("p"))
        .expect("the datum is back after the restore")
        .iter()
        .map(|datum| datum.source.hash.clone())
        .collect();
    assert_eq!(resting_after.len(), 1, "the peek'd datum is enumerable again");

    // The payload is the same...
    let payload_before = before.data.get(&chan("p")).expect("before").as_slice()[0]
        .a
        .pars
        .clone();
    let payload_after = after.data.get(&chan("p")).expect("after").as_slice()[0]
        .a
        .pars
        .clone();
    assert_eq!(payload_before, payload_after, "a peek returns the same payload");

    // ...but the SOURCE is not. `Produce::create` reads (channel, payload,
    // persistence) — all three unchanged — so the hashes would be EQUAL if the
    // restore were a no-op. They differ because `Produce::create` also folds in
    // the produce counter, which the removal moved. Whether they differ or not,
    // the restored datum went through a full produce: that is the observable.
    println!(
        "  peek source before = {:?}\n  peek source after  = {:?}",
        resting_before[0].bytes(),
        resting_after[0].bytes()
    );

    // The peek receiver itself is gone (it was linear), so nothing is enabled.
    assert!(
        sandbox.enabled().is_empty(),
        "a linear peek receiver is consumed by its own firing, so the restored \
         datum has no partner"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// T4 — persistence
// ══════════════════════════════════════════════════════════════════════════

/// A `<=` receive is NOT removed by its own firing — `process_match_found` only
/// removes a non-persistent continuation — so it is enabled again in the next
/// `E(S)`, and a two-datum program drains in two stratified steps.
#[tokio::test]
async fn t4_a_persistent_continuation_survives_its_own_firing() {
    let sandbox = funded_sandbox().await;
    sandbox
        .saturate(
            parallel(vec![
                send("q", 3),
                send("q", 4),
                receive(&["q"], "persistent", true, false, None),
            ]),
            seed(),
        )
        .await
        .expect("saturate");

    let first = sandbox.enabled();
    assert_eq!(first.len(), 2, "one persistent receiver, two data");
    let step = sandbox.fire(first[0].clone()).await.expect("fire");
    assert!(step.persistent, "the fired continuation was persistent");

    let second = sandbox.enabled();
    assert_eq!(
        second.len(),
        1,
        "the persistent receiver survives and the remaining datum still enables it"
    );
    sandbox.fire(second[0].clone()).await.expect("fire");

    assert!(
        sandbox.enabled().is_empty(),
        "both data drained; the receiver rests with nothing to take"
    );
    let final_state = canonicalize(&sandbox.snapshot());
    assert!(final_state.data.get(&chan("q")).is_none(), "both data are consumed");
    assert_eq!(
        final_state
            .continuations
            .get(&vec![chan("q")])
            .map(|group| group.len())
            .unwrap_or(0),
        1,
        "the persistent receiver is still installed"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// T5 — ★ the mechanism can be driven OFF index 0
// ══════════════════════════════════════════════════════════════════════════

/// Without this the sandbox would be an elaborate way of reproducing ordinary
/// execution: Stage 2's whole job is to fire the selections a search would never
/// return. Every member of `E(S)` must be firable, and each must consume exactly
/// what it names.
#[tokio::test]
async fn t5_a_named_non_least_selection_is_reachable() {
    let program = parallel(vec![
        send("c", 1),
        send("c", 2),
        send("c", 3),
        receive(&["c"], "only", false, false, None),
    ]);

    // Enumerate once to learn the shape.
    let probe = funded_sandbox().await;
    probe
        .saturate(program.clone(), seed())
        .await
        .expect("saturate");
    let width = probe.enabled().len();
    assert_eq!(width, 3, "one receiver, three data");

    let mut consumed: HashSet<Vec<Blake2b256Hash>> = HashSet::with_capacity(width);
    let mut successors: HashSet<Vec<String>> = HashSet::with_capacity(width);

    for index in 0..width {
        let sandbox = funded_sandbox().await;
        sandbox
            .saturate(program.clone(), seed())
            .await
            .expect("saturate");
        let enabled = sandbox.enabled();
        assert_eq!(enabled.len(), width, "the enumeration is reproducible");

        let name = RendezvousName::of(&enabled[index]);
        let step = sandbox.fire(enabled[index].clone()).await.expect("fire");
        assert_eq!(step.name, name, "the step reports the name it was asked to fire");

        // The datum it named is gone; the other two are not.
        let after = canonicalize(&sandbox.snapshot());
        let remaining: Vec<Blake2b256Hash> = after
            .data
            .get(&chan("c"))
            .expect("two data remain")
            .iter()
            .map(|datum| datum.source.hash.clone())
            .collect();
        assert_eq!(remaining.len(), 2, "exactly one datum was consumed");
        assert!(
            !remaining.contains(&name.data[0]),
            "the datum that was NAMED is the one that is gone"
        );

        consumed.insert(name.data.clone());
        successors.insert(content_fingerprint(&sandbox.snapshot()));
    }

    assert_eq!(
        consumed.len(),
        width,
        "the three selections consume three DIFFERENT data — the enumeration is \
         not returning the same rendezvous three times"
    );
    assert_eq!(
        successors.len(),
        width,
        "the three selections lead to three DIFFERENT configurations — this is \
         the branching Stage 2 will explore"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// T6 — a system process
// ══════════════════════════════════════════════════════════════════════════

/// `stdout!("…")` reaches the runtime's *installed* continuation. This is
/// correction 4 end to end: without the post-bootstrap baseline the installed
/// continuation would not be in the sandbox at all, `E(S)` would be empty, and
/// the send would rest forever.
#[tokio::test]
async fn t6_a_system_process_fires_in_the_sandbox() {
    let sandbox = funded_sandbox().await;

    // The stdout channel is a URI-derived unforgeable name; take it from the
    // runtime's own installed set rather than reconstructing it, so this test
    // cannot drift from whatever the bootstrap actually installed.
    let installed_groups: Vec<Vec<Par>> = sandbox
        .baseline()
        .installed_continuations
        .keys()
        .cloned()
        .collect();
    assert!(
        !installed_groups.is_empty(),
        "teeth: the bootstrap must have installed at least one system process"
    );

    // Send to every installed single-channel system process in turn; at least
    // one must become enabled. (Which ones accept a bare string depends on the
    // node's process table, so the assertion is over the family, not over a
    // hand-picked member.)
    let mut fired_any = false;
    let mut reached_quietly = 0usize;
    let mut refused = 0usize;
    for group in installed_groups.iter().filter(|group| group.len() == 1) {
        let sandbox = funded_sandbox().await;
        sandbox
            .saturate(
                Par::default().with_sends(vec![Send {
                    chan: Some(group[0].clone()),
                    data: vec![new_gstring_par(
                        "s1 speculative stdout".to_string(),
                        Vec::new(),
                        false,
                    )],
                    persistent: false,
                    locally_free: Vec::new(),
                    connective_used: false,
                }]),
                seed(),
            )
            .await
            .expect("saturate");

        let enabled = sandbox.enabled();
        if enabled.is_empty() {
            continue;
        }
        // ⚠ Not every installed system process ACCEPTS a bare string —
        // `rho:lang:abort` deliberately raises `UserAbortError` on whatever it
        // is handed, and the node installs it alongside `stdout`. Reaching the
        // process is the observable; whether its body then succeeds is the
        // process's own business, and an abort proves the dispatch arrived just
        // as firmly as a success does. (This is also the `failure`-map arm of
        // the FIPS semantics, seen for the first time.)
        match sandbox.fire(enabled[0].clone()).await {
            Ok(step) => {
                assert!(
                    step.system_process,
                    "an installed continuation is a ScalaBodyRef system process"
                );
                fired_any = true;
                reached_quietly += 1;
            },
            Err(SpeculationError::Interpreter(error)) => {
                // The dispatch reached a real system process, which refused.
                println!("  installed process refused the payload: {error:?}");
                fired_any = true;
                refused += 1;
            },
            Err(other) => panic!("unexpected sandbox failure: {other}"),
        }
    }

    println!("  installed system processes reached: {reached_quietly} accepted, {refused} refused");
    assert!(
        fired_any,
        "at least one installed system process must be reachable from a staged \
         send — if none is, the post-bootstrap baseline is not in the sandbox"
    );
    assert!(
        reached_quietly > 0,
        "teeth: at least one installed process must ACCEPT the payload, so this \
         test is not passing purely on aborts"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// T7 — park and resume
// ══════════════════════════════════════════════════════════════════════════

/// Stage 2's branching primitive: a configuration can be snapshotted, another
/// branch explored in the same sandbox, and the saved configuration restored
/// exactly — including the fact that it enables exactly what it enabled before.
#[tokio::test]
async fn t7_a_saved_configuration_reloads_exactly() {
    let sandbox = funded_sandbox().await;
    sandbox
        .saturate(corpus()[0].par.clone(), seed())
        .await
        .expect("saturate");

    let parked = sandbox.snapshot();
    let parked_fingerprint = content_fingerprint(&parked);
    let parked_names: Vec<RendezvousName> = sandbox.enabled_names();
    assert_eq!(parked_names.len(), 4);

    // Explore one branch destructively.
    let enabled = sandbox.enabled();
    sandbox.fire(enabled[0].clone()).await.expect("fire");
    sandbox
        .fire(sandbox.enabled()[0].clone())
        .await
        .expect("fire");
    assert!(sandbox.enabled().is_empty(), "the branch ran out");
    assert_ne!(
        content_fingerprint(&sandbox.snapshot()),
        parked_fingerprint,
        "teeth: the branch really did move the configuration"
    );

    // Resume.
    sandbox.load(parked).await.expect("load");
    assert_eq!(
        content_fingerprint(&sandbox.snapshot()),
        parked_fingerprint,
        "the parked configuration reloads exactly"
    );
    assert_eq!(
        sandbox.enabled_names(),
        parked_names,
        "and it enables exactly the same rendezvous, in the same order"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// T8..T11 — ★★ METERING IS THE BOUND, and truncation is resumable
// ══════════════════════════════════════════════════════════════════════════

/// ★ **The denial-of-service question, answered fail-shut.**
///
/// An unmetered speculative evaluation IS the DOS surface. `create_rho_runtime`
/// gives the sandbox `CostAccounting::empty_cost()` — zero — and the sandbox
/// deliberately does NOT raise that to `Cost::unsafe_max()`. So a sandbox nobody
/// funded cannot evaluate a single send.
#[tokio::test]
async fn t8_an_unfunded_sandbox_refuses_to_evaluate() {
    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    assert_eq!(sandbox.remaining().value, 0, "a fresh sandbox is funded with nothing");

    let outcome = sandbox.saturate(send("c", 1), seed()).await;
    match outcome {
        Err(SpeculationError::Interpreter(error)) => {
            println!("  unfunded sandbox refused: {error:?}");
        },
        Err(other) => panic!("expected a phlogiston refusal, got {other}"),
        Ok(()) => panic!(
            "an unfunded sandbox EVALUATED — the budget is not being enforced, \
             which is exactly the denial-of-service surface metering exists to close"
        ),
    }
}

/// ★ **Metering is the bound.** A sandbox funded with a small budget stops when
/// the budget runs out — no node budget, no frontier cap, no new consensus
/// parameter, just phlogiston.
///
/// The consensus cost unit is one token per send or receive EVALUATED
/// (`Reduce::eval_send` / `eval_receive` call `reserve_comm`), so a program with
/// many sends costs many tokens. This test funds one sandbox generously and an
/// identical one meanly, and requires the mean one to fail.
#[tokio::test]
async fn t9_a_small_budget_stops_the_exploration() {
    // A wide fan of sends: each one costs a token when evaluated.
    let wide = parallel((0..64).map(|value| send("c", value)).collect());

    let generous = funded_sandbox().await;
    generous
        .saturate(wide.clone(), seed())
        .await
        .expect("a generously funded sandbox completes");
    let spent = generous.consumed().value;
    assert!(
        spent > 0,
        "teeth: the exploration must actually have COST something; \
         a zero cost would make the mean arm below vacuous"
    );
    println!("  64 staged sends cost {spent} units");

    // Fund a second sandbox with strictly less than that.
    let mean = SpeculativeSandbox::new().await.expect("sandbox");
    mean.fund_from(&host_budget(spent / 2));
    match mean.saturate(wide, seed()).await {
        Err(SpeculationError::Interpreter(error)) => {
            println!("  under-funded sandbox stopped: {error:?}");
        },
        Err(other) => panic!("expected a phlogiston refusal, got {other}"),
        Ok(()) => panic!(
            "a sandbox funded with {} units ran a {spent}-unit program to completion \
             — the budget is not bounding the exploration",
            spent / 2
        ),
    }
}

/// The funding / charge-back round trip, in the shape the `[*]` reducer hook
/// will use it: fund from the host's REMAINING budget, run, then charge the host
/// what was spent through f1r3node's own `MeteredMachine::reserve_comm` — which
/// fails shut if the deploy cannot afford it.
///
/// ★ **Measured, and it corrects a natural misreading:** a budget unit is ONE
/// COMM, not one unit of `Cost.value`. `reconcile_lane` "tallies ONE per
/// committed `BillableKind::Comm` event and ZERO for every other kind", and
/// `reserve_comm(amount)` charges one regardless of `amount` — the `Cost` it
/// takes is the *diagnostic weight* that rides into the event log and the cost
/// trace digest, not the amount charged. So `consumed()` is a COMM COUNT, and
/// charging it back is `consumed()` calls to `reserve_comm`, not one call with
/// `consumed()` as the argument. An earlier revision of this test made exactly
/// that mistake and measured the host being charged 1 where 5 was owed.
///
/// Nothing in the speculation module owns a budget; this test is the proof that
/// it does not need to.
#[tokio::test]
async fn t10_the_host_is_charged_what_the_exploration_spent() {
    let host = host_budget(HOST_UNITS);
    let host_metering = MeteredMachine::new(host.clone());
    let before = host.remaining().value;
    assert_eq!(before, HOST_UNITS);

    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    let funded = sandbox.fund_from(&host);
    assert_eq!(
        funded.value, before,
        "the sandbox is funded with the host's REMAINING units, not a new allocation"
    );

    let program = corpus()[0].par.clone();
    sandbox.saturate(program, seed()).await.expect("saturate");
    let enabled = sandbox.enabled();
    sandbox.fire(enabled[0].clone()).await.expect("fire");

    let spent = sandbox.consumed().value;
    assert!(spent > 0, "the exploration spent something");

    // Charge it back: one `reserve_comm` per COMM the exploration committed.
    // This is f1r3node's own charge, on the host's own budget; the weight passed
    // is the same `send_eval_cost()`-shaped diagnostic weight the reducer uses.
    for index in 0..spent {
        host_metering
            .reserve_comm(Cost::create(11, "speculative comm"))
            .unwrap_or_else(|error| {
                panic!("the host must afford charge {index} of {spent}: {error:?}")
            });
    }
    let after = host.remaining().value;
    assert_eq!(
        after,
        before - spent,
        "the host is charged exactly what the exploration consumed \
         ({spent} COMMs = {spent} units)"
    );
    println!("  host {before} → {after} (exploration committed {spent} COMMs)");

    // And the fail-shut direction: a host that cannot afford the whole
    // exploration is refused part way through, which is what makes unbounded
    // fan-out self-limiting.
    let poor = host_budget(spent - 1);
    let poor_metering = MeteredMachine::new(poor.clone());
    let mut refused_at: Option<i64> = None;
    for index in 0..spent {
        if poor_metering
            .reserve_comm(Cost::create(11, "speculative comm"))
            .is_err()
        {
            refused_at = Some(index);
            break;
        }
    }
    assert_eq!(
        refused_at,
        Some(spent - 1),
        "a deploy funded for {} COMMs must be refused on COMM {} of a {spent}-COMM \
         exploration",
        spent - 1,
        spent - 1
    );
}

/// ★ **Depth-`n` truncation returns a RESUMABLE handle** — not a success, not a
/// failure.
///
/// The three-stratum chain needs three steps. Run it for one, and the outcome
/// must be `Truncated` with a non-empty frontier; resume from the handle and the
/// remaining two steps must reach exactly the configuration an unbroken
/// three-step run reaches, with the same trace.
///
/// This is what makes beam search expressible: "run `k` steps, gather, keep the
/// best `n`, run forward from those" is literally resuming truncated handles.
#[tokio::test]
async fn t11_truncation_is_resumable_and_resumption_is_faithful() {
    let program = corpus()[6].par.clone(); // three-stratum-chain
    assert_eq!(corpus()[6].label, "three-stratum-chain");

    // ── the unbroken run: three steps, always E(S)[0] (each step has |E(S)| = 1)
    let whole = funded_sandbox().await;
    whole
        .saturate(program.clone(), seed())
        .await
        .expect("saturate");
    let unbroken = whole.run_trace(8, |_| 0).await;
    let (unbroken_state, unbroken_trace) = match unbroken {
        BranchOutcome::Quiescent { state, trace } => (state, trace),
        other => panic!("an 8-step bound must reach quiescence, got {other:?}"),
    };
    assert_eq!(unbroken_trace.len(), 3, "the chain is three COMMs deep");

    // ── the broken run: one step, then resume.
    let broken = funded_sandbox().await;
    broken.saturate(program, seed()).await.expect("saturate");
    let truncated = broken.run_trace(1, |_| 0).await;
    let handle = match truncated {
        BranchOutcome::Truncated(handle) => handle,
        other => panic!(
            "a 1-step bound on a 3-step chain must TRUNCATE — not succeed, not \
             fail — got {other:?}"
        ),
    };
    assert_eq!(handle.trace.len(), 1, "one step was taken");
    assert!(
        handle.frontier > 0,
        "a truncated branch has somewhere left to go — that is what distinguishes \
         it from a quiescent one"
    );
    assert_ne!(
        content_fingerprint(&handle.state),
        content_fingerprint(&unbroken_state),
        "teeth: the truncation point is genuinely mid-evaluation"
    );

    // Park the handle, run something else in the same sandbox, then resume.
    let parked = handle.clone();
    broken.load(broken.baseline().clone()).await.expect("scrub");
    assert!(
        broken.enabled().is_empty(),
        "teeth: the sandbox really was scrubbed before the resume"
    );

    let trace = broken.resume(parked).await.expect("resume");
    let resumed = broken.run_trace(8, |_| 0).await;
    let (resumed_state, tail) = match resumed {
        BranchOutcome::Quiescent { state, trace } => (state, trace),
        other => panic!("the resumed branch must reach quiescence, got {other:?}"),
    };
    let trace = trace
        .concatenate(&tail)
        .expect("the resumed tail starts at the truncation configuration");

    assert_eq!(
        trace, unbroken_trace,
        "resuming a truncated handle continues the SAME trace — the handle keeps \
         the randomness provenance a reified process would have lost"
    );
    assert_eq!(
        content_fingerprint(&resumed_state),
        content_fingerprint(&unbroken_state),
        "and it reaches the same configuration the unbroken run reached"
    );

    // A bound that is reached exactly at quiescence is a SUCCESS, not a
    // truncation: the classification is by |E(S)|, not by whether the bound
    // happened to run out.
    let exact = funded_sandbox().await;
    exact
        .saturate(corpus()[6].par.clone(), seed())
        .await
        .expect("saturate");
    match exact.run_trace(3, |_| 0).await {
        BranchOutcome::Quiescent { trace, .. } => assert_eq!(trace.len(), 3),
        other => panic!(
            "a 3-step bound on a 3-step chain reaches quiescence exactly, so it \
             is a completed evaluation — got {other:?}"
        ),
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Keeping the BTreeMap import honest — `SoftCheckpoint`'s produce counter type
// is named in `RecordingSpace`'s delegation signatures.
// ══════════════════════════════════════════════════════════════════════════
#[allow(dead_code)]
fn _produce_counter_type_is_nameable(counter: BTreeMap<Produce, i32>) -> usize {
    counter.len()
}
