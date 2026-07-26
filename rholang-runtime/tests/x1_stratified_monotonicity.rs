//! **X1 — the monotonicity premise of stratified COMM-choice semantics.**
//!
//! # The premise
//!
//! > Delaying every COMM to administrative quiescence preserves the reachable
//! > state set.
//!
//! The supporting argument: in Rholang a datum that finds no continuation rests
//! and stays available; a continuation that finds no datum rests and stays
//! available; nothing expires; the reduction relation has no negative
//! construct. So delaying a COMM cannot *remove* a rendezvous.
//!
//! If the premise is false the trace model is wrong and every downstream stage
//! of the speculative-evaluation design is wasted, so this file is written to
//! **refute** it, not to confirm it.
//!
//! # The experiment
//!
//! Two spaces wrap the same real `RSpace`:
//!
//! * [`SpeculativeSpace`] — `produce` STAGES the datum (`put_datum`) and
//!   returns `Ok(None)`; `consume` STAGES the continuation (`put_continuation`
//!   + `put_join`) and returns `Ok(None)`. Nothing ever fires. Running `inj` on
//!   it therefore reduces exactly the administrative fragment — `new`, `match`,
//!   arithmetic, methods, `|` fan-out, substitution, and the *installation* of
//!   a produce/consume — and stops at **administrative quiescence** with the
//!   whole soup resting in the store.
//! * [`RecordingSpace`] — delegates everything verbatim and records each COMM
//!   that actually fires. This is the control: an ordinary run.
//!
//! From the speculative quiescent state the **enabled rendezvous set** `E(S)`
//! is computed by [`enabled_set`]: for each resting waiting-continuation, a
//! FRESH probe sandbox is loaded with the quiescent state *minus that one
//! continuation* and the continuation is re-issued as a real `consume`. RSpace's
//! own candidate search — canonical ordering, spatial matching, `where`-guard
//! selection, joins, peeks — then answers "enabled or not". No matcher logic is
//! reimplemented here, so the answer is the engine's, not the harness's.
//!
//! The refutable claim, stated so it can fail:
//!
//! > **Every rendezvous the ordinary run fires must be a member of `E(S)`.**
//!
//! A COMM the ordinary run fires but that `E(S)` does not contain is a
//! rendezvous stratification REMOVED — a refutation.
//!
//! ## Rendezvous identity
//!
//! A rendezvous is identified by its `Consume`
//! (`rspace++/src/rspace/trace/event.rs:194-198`) — the content hash of
//! (channels, patterns, continuation, persistent). The control run reconstructs
//! it from the fired `ContResult`; the speculative store already carries it as
//! `WaitingContinuation::source`. The identity therefore includes the
//! continuation's `random_state`, which makes the comparison sensitive to the
//! randomness-splitting question folded in below: if splitting were dynamic the
//! keys would not line up at all.
//!
//! ## Two granularities of `E(S)`
//!
//! [`enabled_set`] answers *is this continuation enabled* and reports whichever
//! datum the canonical order presents first. [`enabled_pairs`] recovers the
//! finer (continuation × datum) set for single-bind continuations by probing a
//! sandbox per candidate datum. Both are asserted against the control run; the
//! finer one is the one that matches the design's own branching factor.
//!
//! # What each test measures
//!
//! | test | question |
//! | --- | --- |
//! | [`t0_teeth_the_two_spaces_differ_exactly_as_intended`] | does the harness suppress firing, observe firing, and can the probe SEE an obvious rendezvous? |
//! | [`t0b_teeth_the_probe_reports_a_lone_receiver_as_not_enabled`] | can the probe say NO? |
//! | [`t1_stratification_removes_no_rendezvous_over_the_corpus`] | ★ the premise, over the whole corpus, at both granularities |
//! | [`t2_peek`] | is a peek enabled at quiescence, and does a peek'd datum remain enumerable? |
//! | [`t2b_persistent`] | is a `<=` receive enabled at quiescence? |
//! | [`t2c_the_least_admissible_selection_may_differ`] | ordinary selections vs `E(S)` selections on the two-data program |
//! | [`t2c2_the_fresh_datum_index_moves_the_least_admissible_selection`] | ★ the `-1` index, swept over 56 ordered pairs |
//! | [`t2d_where_guard`] | does the guard decide SELECTION under stratification too? |
//! | [`t2e_join`] | is a joined rendezvous enabled at quiescence? |
//! | [`r1_randomness_splitting_is_structural`] | is `Blake2b512Random` splitting positional or task-order dependent? |
//! | [`r2_the_whole_run_is_reproducible_under_the_multi_threaded_runtime`] | is a CONTENDED run reproducible? |
//! | [`c1_check_commit_is_a_pure_predicate`] | is `Matcher::check_commit` pure? |
//! | [`c2_the_matching_cost_of_enumeration`] | what does staging cost the matcher? |

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
use std::sync::{Arc, Mutex};

use async_trait::async_trait;
use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{
    BindPattern, Expr, ListParWithRandom, Par, Receive, ReceiveBind, Send, TaggedContinuation,
};
use models::rust::utils::{new_freevar_par, new_gint_par, new_gstring_par};
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::has_cost::HasCost;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime};
use rho_pure_eval::Env;
use rspace_plus_plus::rspace::checkpoint::{Checkpoint, SoftCheckpoint};
use rspace_plus_plus::rspace::errors::RSpaceError;
use rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash;
use rspace_plus_plus::rspace::hot_store::HotStoreState;
use rspace_plus_plus::rspace::internal::{Datum, Row, WaitingContinuation};
use rspace_plus_plus::rspace::r#match::Match;
use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::rspace_interface::{
    ISpace, MaybeConsumeResult, MaybeProduceResult,
};
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;
use rspace_plus_plus::rspace::trace::event::{Consume, Produce};
use rspace_plus_plus::rspace::trace::Log;

type Space = RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation>;
type State = HotStoreState<Par, BindPattern, ListParWithRandom, TaggedContinuation>;

/// The one seed both arms of every comparison use, so any divergence is
/// attributable to the stratification and not to the entropy source.
const FIXED_SEED: &[u8] = b"x1-stratified-monotonicity";

// ══════════════════════════════════════════════════════════════════════════
// The counting matcher — the `check_commit` cost/purity instrument
// ══════════════════════════════════════════════════════════════════════════

/// f1r3node's production [`Matcher`], wrapped so the harness can count how many
/// times the two halves of the match are asked. `get` is delegated verbatim;
/// `check_commit` is delegated verbatim. Nothing about the verdict changes —
/// only the counters move.
#[derive(Clone, Default)]
struct CountingMatcher {
    inner: Matcher,
    get_calls: Arc<AtomicUsize>,
    check_commit_calls: Arc<AtomicUsize>,
}

impl CountingMatcher {
    fn new() -> Self {
        Self::default()
    }
    fn counters(&self) -> (Arc<AtomicUsize>, Arc<AtomicUsize>) {
        (self.get_calls.clone(), self.check_commit_calls.clone())
    }
}

impl Match<BindPattern, ListParWithRandom, TaggedContinuation> for CountingMatcher {
    fn get(&self, pattern: &BindPattern, data: &ListParWithRandom) -> Option<ListParWithRandom> {
        self.get_calls.fetch_add(1, AtomicOrdering::Relaxed);
        self.inner.get(pattern, data)
    }

    fn check_commit(&self, k: &TaggedContinuation, matched: &[&ListParWithRandom]) -> bool {
        self.check_commit_calls.fetch_add(1, AtomicOrdering::Relaxed);
        self.inner.check_commit(k, matched)
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Space construction
// ══════════════════════════════════════════════════════════════════════════

async fn fresh_space(
    matcher: Arc<Box<dyn Match<BindPattern, ListParWithRandom, TaggedContinuation>>>,
) -> Space {
    let mut kvm = InMemoryStoreManager::new();
    let store = kvm
        .r_space_stores()
        .await
        .expect("in-memory rspace stores must build");
    RSpace::create(store, matcher).expect("a fresh in-memory RSpace must build")
}

async fn install(space: &Space, state: State) {
    space
        .revert_to_soft_checkpoint(SoftCheckpoint {
            cache_snapshot: state,
            log: Vec::new(),
            produce_counter: BTreeMap::new(),
        })
        .await
        .expect("install must succeed on a fresh sandbox");
}

// ══════════════════════════════════════════════════════════════════════════
// SpeculativeSpace — stage everything, fire nothing
// ══════════════════════════════════════════════════════════════════════════

#[derive(Clone)]
struct SpeculativeSpace {
    inner: Space,
    /// How many produce / consume calls were staged. Non-zero is the harness's
    /// own proof that the program actually reached the tuplespace.
    staged_produces: Arc<AtomicUsize>,
    staged_consumes: Arc<AtomicUsize>,
}

impl SpeculativeSpace {
    fn new(inner: Space) -> Self {
        Self {
            inner,
            staged_produces: Arc::new(AtomicUsize::new(0)),
            staged_consumes: Arc::new(AtomicUsize::new(0)),
        }
    }
}

#[async_trait]
impl ISpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> for SpeculativeSpace {
    // ── THE TWO OVERRIDDEN OPERATIONS ────────────────────────────────────

    /// Stage, never fire. `put_datum` is exactly what `RSpace::store_data`
    /// (`rspace.rs:1046-1060`) does on the no-match path, so the resulting
    /// store entry is byte-identical to the one an ordinary run leaves behind
    /// when a produce finds no continuation.
    async fn produce(
        &self,
        channel: Par,
        data: ListParWithRandom,
        persist: bool,
    ) -> Result<
        MaybeProduceResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
        RSpaceError,
    > {
        let source = Produce::create(&channel, &data, persist);
        self.inner.get_store().put_datum(&channel, Datum {
            a: Arc::new(data),
            persist,
            source,
        });
        self.staged_produces.fetch_add(1, AtomicOrdering::Relaxed);
        Ok(None)
    }

    /// Stage, never fire. `put_continuation` + `put_join` per channel is
    /// exactly `RSpace::store_waiting_continuation` (`rspace.rs:1032-1042`).
    async fn consume(
        &self,
        channels: Vec<Par>,
        patterns: Vec<BindPattern>,
        continuation: TaggedContinuation,
        persist: bool,
        peeks: BTreeSet<i32>,
    ) -> Result<
        MaybeConsumeResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
        RSpaceError,
    > {
        let wk = WaitingContinuation::create(
            &channels,
            &patterns,
            &continuation,
            persist,
            peeks,
        );
        let store = self.inner.get_store();
        let _ = store.put_continuation(&channels, wk);
        for channel in channels.iter() {
            store.put_join(channel, &channels);
        }
        self.staged_consumes.fetch_add(1, AtomicOrdering::Relaxed);
        Ok(None)
    }

    // ── everything else: verbatim delegation ─────────────────────────────

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

// ══════════════════════════════════════════════════════════════════════════
// RecordingSpace — an ordinary run, with a COMM ledger
// ══════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
struct FiredComm {
    trigger: &'static str,
    channels: Vec<Par>,
    patterns: Vec<BindPattern>,
    continuation: TaggedContinuation,
    persistent: bool,
    peek: bool,
    consumed: Vec<ListParWithRandom>,
}

impl FiredComm {
    fn key(&self) -> Consume {
        Consume::create(
            &self.channels,
            &self.patterns,
            &self.continuation,
            self.persistent,
        )
    }
    fn consumed_ints(&self) -> Vec<i64> {
        let mut values: Vec<i64> = self
            .consumed
            .iter()
            .flat_map(|item| item.pars.iter())
            .flat_map(|par| par.exprs.iter())
            .filter_map(|expr| match expr.expr_instance {
                Some(ExprInstance::GInt(v)) => Some(v),
                _ => None,
            })
            .collect();
        values.sort();
        values
    }
}

#[derive(Clone)]
struct RecordingSpace {
    inner: Space,
    fired: Arc<Mutex<Vec<FiredComm>>>,
}

impl RecordingSpace {
    fn new(inner: Space) -> Self {
        Self { inner, fired: Arc::new(Mutex::new(Vec::new())) }
    }

    fn record(
        &self,
        trigger: &'static str,
        result: &MaybeConsumeResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
    ) {
        if let Some((cont, matched)) = result {
            self.fired.lock().expect("fired ledger").push(FiredComm {
                trigger,
                channels: cont.channels.clone(),
                patterns: cont.patterns.clone(),
                continuation: cont.continuation.clone(),
                persistent: cont.persistent,
                peek: cont.peek,
                consumed: matched.iter().map(|r| r.matched_datum.clone()).collect(),
            });
        }
    }
}

#[async_trait]
impl ISpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> for RecordingSpace {
    async fn consume(
        &self,
        channels: Vec<Par>,
        patterns: Vec<BindPattern>,
        continuation: TaggedContinuation,
        persist: bool,
        peeks: BTreeSet<i32>,
    ) -> Result<
        MaybeConsumeResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
        RSpaceError,
    > {
        let result = self
            .inner
            .consume(channels, patterns, continuation, persist, peeks)
            .await?;
        self.record("consume", &result);
        Ok(result)
    }

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
        self.record(
            "produce",
            &result
                .as_ref()
                .map(|(cont, matched, _)| (cont.clone(), matched.clone())),
        );
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

// ══════════════════════════════════════════════════════════════════════════
// The corpus — Par-level, so no parser or grammar overlay is in the loop
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

/// A receive whose BODY is inert and carries no bound variable — so that a
/// fired COMM adds nothing to the next stratum and every COMM in the corpus is
/// a stratum-0 COMM. `marker` makes each continuation textually distinct, so
/// two receives on the same channel have distinct `Consume` identities for
/// reasons a reader can see rather than only via the random state.
fn receive(
    sources: &[&str],
    marker: &str,
    persistent: bool,
    peek: bool,
    condition: Option<Par>,
) -> Par {
    // ⚠ Free-variable levels are LOCAL TO EACH BIND and start at 0, and
    // `BindPattern.free_count` counts only that bind's own free variables.
    // `Matcher::get` reads the bound values back with `to_vec(free_map,
    // pattern.free_count)` (`models/src/rust/utils.rs:229-236`), which collects
    // levels `0..free_count` — so a bind whose pattern used a GLOBAL level
    // (`FreeVar(1)` on the second bind) yields a DEFAULT `Par` instead of the
    // datum, and the join silently binds nothing on that leg. An earlier
    // revision of this fixture did exactly that; f1r3node's own two-bind
    // fixtures (`rholang/tests/reduce_spec.rs`, the `chan_a`/`chan_b` join) use
    // `new_freevar_par(0, …)` with `free_count: 1` on BOTH binds.
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
        body: Some(Par::default().with_sends(vec![Send {
            chan: Some(chan("x1-body-marker")),
            data: vec![new_gstring_par(marker.to_string(), Vec::new(), false)],
            persistent: false,
            locally_free: Vec::new(),
            connective_used: false,
        }])),
        persistent,
        peek,
        bind_count,
        locally_free: Vec::new(),
        connective_used: false,
        condition,
    }])
}

/// `BoundVar(0) <= 45` — the guard `for(@px <- @"offer" where px <= 45)` lowers
/// to. Lifted verbatim from f1r3node's own D1 fixture
/// (`rholang/tests/reduce_spec.rs`, commit `5d37f67e`).
fn guard_first_bound_at_most_45() -> Par {
    Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::ELteBody(models::rhoapi::ELte {
            p1: Some(models::rust::utils::new_boundvar_par(
                0,
                models::create_bit_vector(&vec![0]),
                false,
            )),
            p2: Some(new_gint_par(45, Vec::new(), false)),
        })),
    }])
}

struct Program {
    label: &'static str,
    /// A human-readable Rholang rendering of what the `Par` encodes. The `Par`
    /// is the artifact; this is a reader annotation.
    source: &'static str,
    par: Par,
}

fn corpus() -> Vec<Program> {
    vec![
        // (a) two data, two linear receives, one channel
        Program {
            label: "a-two-data-two-receives",
            source: r#"x!(1) | x!(2) | for(y<-x){…} | for(z<-x){…}"#,
            par: send("x1-a", 1)
                .append(send("x1-a", 2))
                .append(receive(&["x1-a"], "a-first", false, false, None))
                .append(receive(&["x1-a"], "a-second", false, false, None)),
        },
        // (b) a `where`-guarded receive with two matching data — D1's own shape
        Program {
            label: "b-where-guard",
            source: r#"@"offer"!(55) | @"offer"!(42) | for(@px <- @"offer" where px <= 45){…}"#,
            par: send("x1-offer", 55)
                .append(send("x1-offer", 42))
                .append(receive(
                    &["x1-offer"],
                    "b-guarded",
                    false,
                    false,
                    Some(guard_first_bound_at_most_45()),
                )),
        },
        // (c) a join
        Program {
            label: "c-join",
            source: r#"for(a<-x & b<-y){…} | x!(1) | y!(2)"#,
            par: receive(&["x1-jx", "x1-jy"], "c-join", false, false, None)
                .append(send("x1-jx", 1))
                .append(send("x1-jy", 2)),
        },
        // (d) ★ a PEEK — the design's prime suspect
        Program {
            label: "d-peek",
            source: r#"x!(7) | for(y<<-x){…}"#,
            par: send("x1-pk", 7).append(receive(&["x1-pk"], "d-peek", false, true, None)),
        },
        // (e) a PERSISTENT receive
        Program {
            label: "e-persistent",
            source: r#"x!(8) | for(y<=x){…}"#,
            par: send("x1-ps", 8).append(receive(&["x1-ps"], "e-persistent", true, false, None)),
        },
        // (f) ★ a PEEK racing a LINEAR receive for the SAME datum. This is the
        // shape that makes the peek mechanism visible: at the RSpace layer a
        // peek REMOVES the datum (`store_persistent_data` ignores its `_peeks`
        // argument, `rspace.rs:1062-1110`) and the reducer restores it with a
        // fresh `produce` (`Reduce::produce_peeks`, `reduce.rs:1236-1269`). So
        // between the peek COMM and the re-produce the datum is ABSENT, and the
        // linear receive can only fire before or after that window — never
        // "during" it.
        Program {
            label: "f-peek-races-linear",
            source: r#"x!(9) | for(y<<-x){…} | for(z<-x){…}"#,
            par: send("x1-pl", 9)
                .append(receive(&["x1-pl"], "f-peek", false, true, None))
                .append(receive(&["x1-pl"], "f-linear", false, false, None)),
        },
    ]
}

// ══════════════════════════════════════════════════════════════════════════
// The two runs
// ══════════════════════════════════════════════════════════════════════════

struct SpeculativeRun {
    quiescent: State,
    staged_produces: usize,
    staged_consumes: usize,
    get_calls: usize,
    check_commit_calls: usize,
}

async fn run_speculative(par: Par) -> SpeculativeRun {
    let matcher = CountingMatcher::new();
    let (get_calls, check_commit_calls) = matcher.counters();
    let inner = fresh_space(Arc::new(Box::new(matcher))).await;
    let space = SpeculativeSpace::new(inner.clone());
    let staged_produces = space.staged_produces.clone();
    let staged_consumes = space.staged_consumes.clone();

    let mut runtime = create_rho_runtime(
        space,
        Arc::new(HashMap::new()),
        false,
        &mut Vec::new(),
        ExternalServices::noop(),
    )
    .await;
    runtime.cost().set(Cost::unsafe_max());
    runtime
        .inj(
            par,
            Env::new(),
            Blake2b512Random::create_from_bytes(FIXED_SEED),
        )
        .await
        .expect("the administrative fragment must reduce to quiescence");

    SpeculativeRun {
        quiescent: inner.get_store().snapshot(),
        staged_produces: staged_produces.load(AtomicOrdering::Relaxed),
        staged_consumes: staged_consumes.load(AtomicOrdering::Relaxed),
        get_calls: get_calls.load(AtomicOrdering::Relaxed),
        check_commit_calls: check_commit_calls.load(AtomicOrdering::Relaxed),
    }
}

struct OrdinaryRun {
    fired: Vec<FiredComm>,
    final_state: State,
    get_calls: usize,
    check_commit_calls: usize,
}

async fn run_ordinary(par: Par) -> OrdinaryRun {
    let matcher = CountingMatcher::new();
    let (get_calls, check_commit_calls) = matcher.counters();
    let inner = fresh_space(Arc::new(Box::new(matcher))).await;
    let space = RecordingSpace::new(inner.clone());
    let ledger = space.fired.clone();

    let mut runtime = create_rho_runtime(
        space,
        Arc::new(HashMap::new()),
        false,
        &mut Vec::new(),
        ExternalServices::noop(),
    )
    .await;
    runtime.cost().set(Cost::unsafe_max());
    runtime
        .inj(
            par,
            Env::new(),
            Blake2b512Random::create_from_bytes(FIXED_SEED),
        )
        .await
        .expect("the ordinary run must reduce to quiescence");

    let fired = ledger.lock().expect("fired ledger").clone();
    OrdinaryRun {
        fired,
        final_state: inner.get_store().snapshot(),
        get_calls: get_calls.load(AtomicOrdering::Relaxed),
        check_commit_calls: check_commit_calls.load(AtomicOrdering::Relaxed),
    }
}

// ══════════════════════════════════════════════════════════════════════════
// E(S) — the enabled rendezvous set at administrative quiescence
// ══════════════════════════════════════════════════════════════════════════

#[derive(Debug)]
struct EnabledRendezvous {
    channels: Vec<Par>,
    key: Consume,
    selected: Vec<i64>,
}

/// Probe the quiescent state, one resting waiting-continuation at a time, using
/// a FRESH sandbox per probe and RSpace's own `consume`.
async fn enabled_set(quiescent: &State) -> Vec<EnabledRendezvous> {
    let mut enabled = Vec::new();
    // `installed_continuations` holds the runtime's own system processes, not
    // the program's rendezvous, so they are deliberately not probed.
    let groups: Vec<(Vec<Par>, usize)> = quiescent
        .continuations
        .iter()
        .flat_map(|(group, wks)| (0..wks.len()).map(move |i| (group.clone(), i)))
        .collect();

    for (group, index) in groups {
        let wk = quiescent.continuations[&group][index].clone();

        let mut trimmed = quiescent.clone();
        {
            let bucket = trimmed
                .continuations
                .get_mut(&group)
                .expect("the group exists by construction");
            bucket.remove(index);
            if bucket.is_empty() {
                trimmed.continuations.remove(&group);
            }
        }

        let probe = fresh_space(Arc::new(Box::new(Matcher))).await;
        install(&probe, trimmed).await;
        let result = probe
            .consume(
                group.clone(),
                (*wk.patterns).clone(),
                (*wk.continuation).clone(),
                wk.persist,
                wk.peeks.clone(),
            )
            .await
            .expect("the probe consume must not error");

        if let Some((_cont, matched)) = result {
            let mut selected: Vec<i64> = matched
                .iter()
                .flat_map(|r| r.matched_datum.pars.iter())
                .flat_map(|par| par.exprs.iter())
                .filter_map(|expr| match expr.expr_instance {
                    Some(ExprInstance::GInt(v)) => Some(v),
                    _ => None,
                })
                .collect();
            selected.sort();
            enabled.push(EnabledRendezvous {
                channels: group.clone(),
                key: wk.source.clone(),
                selected,
            });
        }
    }
    enabled
}

/// The FULL admissible set, at (continuation × datum) granularity, for
/// SINGLE-BIND continuations.
///
/// [`enabled_set`] answers "is this continuation enabled", and the datum it
/// reports is whichever the canonical order presents first. That is the right
/// granularity for the monotonicity claim, but it is coarser than the design's
/// `E(S)`, which branches on every admissible *selection*. This routine
/// recovers the finer set the only way that keeps RSpace as the oracle: for
/// each single-bind continuation and each datum resting on its channel, probe a
/// sandbox in which that channel holds EXACTLY that one datum. The engine then
/// answers "is this pair admissible" with its own matcher and its own guard.
///
/// Joins (`bind_count > 1`) are skipped: their admissible set is a cross
/// product and is measured by [`enabled_set`] at continuation granularity.
async fn enabled_pairs(quiescent: &State) -> Vec<(Consume, Vec<i64>)> {
    let mut pairs = Vec::new();
    let groups: Vec<(Vec<Par>, usize)> = quiescent
        .continuations
        .iter()
        .flat_map(|(group, wks)| (0..wks.len()).map(move |i| (group.clone(), i)))
        .collect();

    for (group, index) in groups {
        if group.len() != 1 {
            continue; // joins: see `enabled_set`
        }
        let channel = group[0].clone();
        let wk = quiescent.continuations[&group][index].clone();
        let resting = quiescent.data.get(&channel).cloned().unwrap_or_default();

        for datum in resting {
            let mut trimmed = quiescent.clone();
            {
                let bucket = trimmed
                    .continuations
                    .get_mut(&group)
                    .expect("the group exists by construction");
                bucket.remove(index);
                if bucket.is_empty() {
                    trimmed.continuations.remove(&group);
                }
            }
            trimmed.data.insert(channel.clone(), vec![datum.clone()]);

            let probe = fresh_space(Arc::new(Box::new(Matcher))).await;
            install(&probe, trimmed).await;
            let result = probe
                .consume(
                    group.clone(),
                    (*wk.patterns).clone(),
                    (*wk.continuation).clone(),
                    wk.persist,
                    wk.peeks.clone(),
                )
                .await
                .expect("the probe consume must not error");

            if let Some((_cont, matched)) = result {
                let mut selected: Vec<i64> = matched
                    .iter()
                    .flat_map(|r| r.matched_datum.pars.iter())
                    .flat_map(|par| par.exprs.iter())
                    .filter_map(|expr| match expr.expr_instance {
                        Some(ExprInstance::GInt(v)) => Some(v),
                        _ => None,
                    })
                    .collect();
                selected.sort();
                pairs.push((wk.source.clone(), selected));
            }
        }
    }
    pairs
}

fn describe_channels(channels: &[Par]) -> String {
    channels
        .iter()
        .map(|par| {
            par.exprs
                .iter()
                .find_map(|expr| match &expr.expr_instance {
                    Some(ExprInstance::GString(s)) => Some(format!("@\"{s}\"")),
                    _ => None,
                })
                .unwrap_or_else(|| "<unforgeable>".to_string())
        })
        .collect::<Vec<_>>()
        .join(" & ")
}

fn resting_ints(state: &State, channel: &Par) -> Vec<i64> {
    let mut values: Vec<i64> = state
        .data
        .get(channel)
        .map(|data| {
            data.iter()
                .flat_map(|datum| datum.a.pars.iter())
                .flat_map(|par| par.exprs.iter())
                .filter_map(|expr| match expr.expr_instance {
                    Some(ExprInstance::GInt(v)) => Some(v),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();
    values.sort();
    values
}

// ══════════════════════════════════════════════════════════════════════════
// T0 — TEETH
// ══════════════════════════════════════════════════════════════════════════

/// The `SpeculativeSpace` must genuinely suppress firing, and the
/// `RecordingSpace` must genuinely see firing. Without both, the corpus
/// comparison is meaningless in both directions.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn t0_teeth_the_two_spaces_differ_exactly_as_intended() {
    let program = send("x1-teeth", 1).append(receive(&["x1-teeth"], "teeth", false, false, None));

    let ordinary = run_ordinary(program.clone()).await;
    assert_eq!(
        ordinary.fired.len(),
        1,
        "TEETH FAILED: the ordinary run fired {} COMM(s), expected exactly 1 — \
         the RecordingSpace is not observing the rendezvous",
        ordinary.fired.len()
    );

    let speculative = run_speculative(program).await;
    assert_eq!(
        speculative.staged_produces, 1,
        "TEETH FAILED: the speculative run staged {} produce(s), expected 1",
        speculative.staged_produces
    );
    assert_eq!(
        speculative.staged_consumes, 1,
        "TEETH FAILED: the speculative run staged {} consume(s), expected 1",
        speculative.staged_consumes
    );
    // Both participants MUST be resting side by side — that is what
    // "administrative quiescence" means and it is what E(S) is computed from.
    assert_eq!(
        resting_ints(&speculative.quiescent, &chan("x1-teeth")),
        vec![1],
        "TEETH FAILED: the datum did not rest in the speculative store"
    );
    assert_eq!(
        speculative
            .quiescent
            .continuations
            .get(&vec![chan("x1-teeth")])
            .map(|v| v.len())
            .unwrap_or(0),
        1,
        "TEETH FAILED: the continuation did not rest in the speculative store"
    );

    // And E(S) must SEE that rendezvous. If the probe cannot find a rendezvous
    // this obvious, every "not enabled" result below is untrustworthy.
    let enabled = enabled_set(&speculative.quiescent).await;
    assert_eq!(
        enabled.len(),
        1,
        "TEETH FAILED: the E(S) probe found {} enabled rendezvous, expected 1",
        enabled.len()
    );
    assert_eq!(enabled[0].selected, vec![1]);
}

/// The E(S) probe must also be able to say NO. A continuation with no datum
/// available must not be reported enabled.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn t0b_teeth_the_probe_reports_a_lone_receiver_as_not_enabled() {
    let program = receive(&["x1-lonely"], "lonely", false, false, None);
    let speculative = run_speculative(program).await;
    assert_eq!(speculative.staged_consumes, 1);
    let enabled = enabled_set(&speculative.quiescent).await;
    assert!(
        enabled.is_empty(),
        "TEETH FAILED: a receiver with no datum was reported ENABLED: {enabled:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// T1 — THE MONOTONICITY TEST over the whole corpus
// ══════════════════════════════════════════════════════════════════════════

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn t1_stratification_removes_no_rendezvous_over_the_corpus() {
    println!("\n╔══ X1 — stratified COMM choice vs an ordinary run ══════════════════╗");
    let mut refutations: Vec<String> = Vec::new();

    for program in corpus() {
        let ordinary = run_ordinary(program.par.clone()).await;
        let speculative = run_speculative(program.par.clone()).await;
        let enabled = enabled_set(&speculative.quiescent).await;
        let pairs = enabled_pairs(&speculative.quiescent).await;

        println!("\n── {} ──", program.label);
        println!("   source                 {}", program.source);
        println!(
            "   ordinary run           {} COMM(s) fired; matcher get={} check_commit={}",
            ordinary.fired.len(),
            ordinary.get_calls,
            ordinary.check_commit_calls
        );
        for fired in &ordinary.fired {
            println!(
                "     · via {:<8} on {:<28} consumed {:?} (persistent={}, peek={})",
                fired.trigger,
                describe_channels(&fired.channels),
                fired.consumed_ints(),
                fired.persistent,
                fired.peek
            );
        }
        println!(
            "   speculative quiescence staged {} produce(s) + {} consume(s); matcher get={} check_commit={}",
            speculative.staged_produces,
            speculative.staged_consumes,
            speculative.get_calls,
            speculative.check_commit_calls
        );
        println!("   |E(S)| = {} (continuation granularity)", enabled.len());
        for rendezvous in &enabled {
            println!(
                "     · enabled on {:<28} selects {:?}",
                describe_channels(&rendezvous.channels),
                rendezvous.selected
            );
        }
        println!(
            "   |E(S)| = {} (continuation × datum granularity, single-bind only)",
            pairs.len()
        );
        {
            let mut rendered: Vec<String> =
                pairs.iter().map(|(_, data)| format!("{data:?}")).collect();
            rendered.sort();
            println!("     admissible selections: {}", rendered.join(" "));
        }

        // ── non-vacuity: a program that fires nothing proves nothing ──────
        if ordinary.fired.is_empty() {
            refutations.push(format!(
                "{}: VACUOUS — the ordinary run fired no COMM at all, so the \
                 subset assertion below is empty. Fix the fixture, not the claim.",
                program.label
            ));
        }

        // ★ THE ASSERTION. Every rendezvous the ordinary run fired must be a
        // member of E(S).
        let enabled_keys: BTreeSet<Consume> =
            enabled.iter().map(|r| r.key.clone()).collect();
        for fired in &ordinary.fired {
            if !enabled_keys.contains(&fired.key()) {
                refutations.push(format!(
                    "{}: the ordinary run fired a rendezvous on {} (consuming {:?}) that is \
                     NOT enabled at administrative quiescence",
                    program.label,
                    describe_channels(&fired.channels),
                    fired.consumed_ints()
                ));
            }
        }

        // ★ THE STRONGER FORM, at (continuation × datum) granularity. For
        // every single-bind rendezvous the ordinary run fired, the exact
        // (continuation, datum) pair must be admissible at quiescence.
        let pair_set: BTreeSet<(Consume, Vec<i64>)> = pairs.into_iter().collect();
        for fired in &ordinary.fired {
            if fired.channels.len() != 1 {
                continue; // joins are covered at continuation granularity above
            }
            let pair = (fired.key(), fired.consumed_ints());
            if !pair_set.contains(&pair) {
                refutations.push(format!(
                    "{}: the ordinary run fired ({} consuming {:?}) but that exact \
                     (continuation, datum) pair is NOT admissible at administrative \
                     quiescence",
                    program.label,
                    describe_channels(&fired.channels),
                    fired.consumed_ints()
                ));
            }
        }

        // The speculative run must not have LOST participants either: every
        // COMM the ordinary run fired needs a staged counterpart.
        if !ordinary.fired.is_empty() && speculative.staged_consumes == 0 {
            refutations.push(format!(
                "{}: the ordinary run fired {} COMM(s) but the speculative run staged \
                 NO consume at all",
                program.label,
                ordinary.fired.len()
            ));
        }
    }

    println!("\n╚═══════════════════════════════════════════════════════════════════╝");
    assert!(
        refutations.is_empty(),
        "X1 REFUTED — stratification removed a rendezvous:\n  {}",
        refutations.join("\n  ")
    );
}

// ══════════════════════════════════════════════════════════════════════════
// T2 — the two rows the design singles out
// ══════════════════════════════════════════════════════════════════════════

/// ★ PEEK. Two questions, both answered here:
///
/// 1. Is a peek rendezvous ENABLED at administrative quiescence?
/// 2. Does a peek'd datum **remain enumerable** — i.e. after an ordinary peek
///    COMM, is the datum still resting and still a candidate?
///
/// The second is where the mechanism is not what a reader expects. At the
/// RSpace layer a peek is NOT a pure read: `store_persistent_data`
/// (`rspace.rs:1062-1110`) ignores its `_peeks` argument and REMOVES the
/// non-persistent datum. It is the *reducer* that restores it —
/// `Reduce::produce_peeks` (`reduce.rs:1236-1262`) re-issues it as a fresh
/// `produce`. So the datum is enumerable again only once that re-produce has
/// completed, and it comes back carrying a DIFFERENT `Produce` source than the
/// one it left with.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn t2_peek() {
    let program = corpus()
        .into_iter()
        .find(|p| p.label == "d-peek")
        .expect("the peek program is in the corpus");

    let ordinary = run_ordinary(program.par.clone()).await;
    let speculative = run_speculative(program.par.clone()).await;
    let enabled = enabled_set(&speculative.quiescent).await;

    println!("\n── X1 · PEEK ──");
    println!("   ordinary COMMs fired : {}", ordinary.fired.len());
    println!(
        "   ordinary peek flag   : {:?}",
        ordinary.fired.iter().map(|f| f.peek).collect::<Vec<_>>()
    );
    println!(
        "   datum resting AFTER  : {:?}",
        resting_ints(&ordinary.final_state, &chan("x1-pk"))
    );
    println!("   |E(S)| at quiescence : {}", enabled.len());

    assert_eq!(ordinary.fired.len(), 1, "the peek must fire exactly one COMM");
    assert!(ordinary.fired[0].peek, "the fired COMM must be flagged as a peek");
    assert_eq!(
        enabled.len(),
        1,
        "X1 REFUTED (peek) — the peek rendezvous is NOT enabled at administrative \
         quiescence, so stratification removed it"
    );
    assert_eq!(enabled[0].selected, vec![7]);

    // The peek'd datum must still be resting after the ordinary run — this is
    // the "remains enumerable" half.
    assert_eq!(
        resting_ints(&ordinary.final_state, &chan("x1-pk")),
        vec![7],
        "X1 FINDING — the peek'd datum did NOT remain in the store"
    );

    // …but its `Produce` source is the RE-PRODUCE's, not the original's. That
    // is what makes a peek a stratum boundary rather than a pure read.
    let original_source = Produce::create(
        &chan("x1-pk"),
        &ListParWithRandom {
            pars: vec![new_gint_par(7, Vec::new(), false)],
            random_state: Vec::new(),
        },
        false,
    );
    let resting_sources: Vec<Blake2b256Hash> = ordinary
        .final_state
        .data
        .get(&chan("x1-pk"))
        .map(|data| data.iter().map(|d| d.source.hash.clone()).collect())
        .unwrap_or_default();
    println!(
        "   resting datum source hashes differ from a naive reconstruction: {}",
        !resting_sources.contains(&original_source.hash)
    );
}

/// ★ PERSISTENT. A `<=` receive stays installed after firing, so at
/// administrative quiescence it is a resting continuation like any other, and
/// it must be enabled.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn t2b_persistent() {
    let program = corpus()
        .into_iter()
        .find(|p| p.label == "e-persistent")
        .expect("the persistent program is in the corpus");

    let ordinary = run_ordinary(program.par.clone()).await;
    let speculative = run_speculative(program.par.clone()).await;
    let enabled = enabled_set(&speculative.quiescent).await;

    println!("\n── X1 · PERSISTENT ──");
    println!("   ordinary COMMs fired : {}", ordinary.fired.len());
    println!(
        "   ordinary persistent  : {:?}",
        ordinary.fired.iter().map(|f| f.persistent).collect::<Vec<_>>()
    );
    println!(
        "   continuation resting AFTER : {}",
        ordinary
            .final_state
            .continuations
            .get(&vec![chan("x1-ps")])
            .map(|v| v.len())
            .unwrap_or(0)
    );
    println!("   |E(S)| at quiescence : {}", enabled.len());

    assert_eq!(ordinary.fired.len(), 1, "the persistent receive must fire once");
    assert!(
        ordinary.fired[0].persistent,
        "the fired COMM must be flagged persistent"
    );
    assert_eq!(
        enabled.len(),
        1,
        "X1 REFUTED (persistent) — the persistent rendezvous is NOT enabled at \
         administrative quiescence"
    );
    assert_eq!(enabled[0].selected, vec![8]);
}

/// ★ The `-1` fresh-datum index. `locked_produce` (`rspace.rs:743-843`, with
/// the explanatory comment at `:778-802` — the design cites `:776-800`, two
/// lines early) inserts the freshly-produced datum into the candidate pool at
/// index `-1`, i.e. AHEAD of every resting datum in the canonical order. Under
/// stratification there is no fresh datum, so the *set* of admissible
/// selections is unchanged but the *least* one need not be.
///
/// This test does not assert which datum wins; it MEASURES whether the two
/// regimes agree, because that difference is a design input.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn t2c_the_least_admissible_selection_may_differ() {
    let program = corpus()
        .into_iter()
        .find(|p| p.label == "a-two-data-two-receives")
        .expect("program (a) is in the corpus");

    let ordinary = run_ordinary(program.par.clone()).await;
    let speculative = run_speculative(program.par.clone()).await;
    let enabled = enabled_set(&speculative.quiescent).await;

    let mut ordinary_selections: Vec<Vec<i64>> =
        ordinary.fired.iter().map(|f| f.consumed_ints()).collect();
    ordinary_selections.sort();
    let mut speculative_selections: Vec<Vec<i64>> =
        enabled.iter().map(|r| r.selected.clone()).collect();
    speculative_selections.sort();

    println!("\n── X1 · least-admissible-selection comparison (program a) ──");
    println!("   ordinary run selected    : {ordinary_selections:?}");
    println!("   E(S) probes selected     : {speculative_selections:?}");
    println!(
        "   agree                    : {}",
        ordinary_selections == speculative_selections
    );

    // The SET of enabled rendezvous is the claim under test, and it must hold.
    assert_eq!(
        enabled.len(),
        2,
        "both receives must be enabled at administrative quiescence"
    );
    // Each probe, run against the FULL resting pool, must be able to take
    // either datum — so each selection is one of the two available.
    for selection in &speculative_selections {
        assert!(
            selection == &vec![1i64] || selection == &vec![2i64],
            "an E(S) probe selected something that was never sent: {selection:?}"
        );
    }
}

/// ★ The `-1` fresh-datum index, measured DIRECTLY at the RSpace layer with no
/// reducer in the loop, so the two regimes differ in exactly one thing.
///
/// `extract_produce_candidate` (`rspace.rs:875-882`) splices the arriving datum
/// into the candidate pool at index `-1`:
///
/// ```text
/// if channel == bat_channel { shuffled_data.insert(0, (data.clone(), -1)); }
/// ```
///
/// which puts it AHEAD of every resting datum in the canonical order. Under
/// stratification there is no arriving datum: everything rests, and the pool is
/// the canonical order alone. The *set* of admissible selections is the same;
/// the *least* one need not be. This test measures whether it is.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn t2c2_the_fresh_datum_index_moves_the_least_admissible_selection() {
    fn wildcard_patterns() -> Vec<BindPattern> {
        vec![BindPattern {
            patterns: vec![new_freevar_par(0, Vec::new())],
            remainder: None,
            free_count: 1,
        }]
    }
    fn item(value: i64) -> ListParWithRandom {
        ListParWithRandom {
            pars: vec![new_gint_par(value, Vec::new(), false)],
            random_state: Vec::new(),
        }
    }
    fn taken(
        result: &MaybeConsumeResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
    ) -> Vec<i64> {
        result
            .as_ref()
            .map(|(_, matched)| {
                let mut values: Vec<i64> = matched
                    .iter()
                    .flat_map(|r| r.matched_datum.pars.iter())
                    .flat_map(|par| par.exprs.iter())
                    .filter_map(|expr| match expr.expr_instance {
                        Some(ExprInstance::GInt(v)) => Some(v),
                        _ => None,
                    })
                    .collect();
                values.sort();
                values
            })
            .unwrap_or_default()
    }

    // A SWEEP, not a single instance. For an unordered pair {p, q} the
    // canonical order names one winner, say q. Then "p arrives" diverges from
    // the stratified regime (p wins by `-1`, q wins canonically) while
    // "q arrives" agrees. A single pair therefore proves nothing either way;
    // the divergence RATE over many pairs is the measurement.
    const VALUES: &[i64] = &[2, 3, 5, 7, 11, 13, 17, 19];

    let channel = chan("x1-fresh-vs-resting");
    let mut trials = 0usize;
    let mut divergences = 0usize;
    let mut examples: Vec<String> = Vec::new();

    for (i, &resting) in VALUES.iter().enumerate() {
        for &arriving in VALUES.iter().skip(i + 1) {
            for (resting, arriving) in [(resting, arriving), (arriving, resting)] {
                // ── Arm A: ARRIVAL regime — continuation installed first, one
                //    datum resting, the other arriving as a `produce`.
                let arrival = fresh_space(Arc::new(Box::new(Matcher))).await;
                let installed = arrival
                    .consume(
                        vec![channel.clone()],
                        wildcard_patterns(),
                        TaggedContinuation::default(),
                        false,
                        BTreeSet::new(),
                    )
                    .await
                    .expect("consume must not error");
                assert!(installed.is_none(), "the continuation must install, not fire");
                // Rest one datum WITHOUT `produce`, so it cannot fire the
                // installed receive and must wait in the pool.
                arrival
                    .get_store()
                    .put_datum(&channel, Datum::create(&channel, item(resting), false));
                let arrival_taken = taken(
                    &arrival
                        .produce(channel.clone(), item(arriving), false)
                        .await
                        .expect("produce must not error")
                        .map(|(cont, matched, _)| (cont, matched)),
                );

                // ── Arm B: STRATIFIED regime — BOTH rest, continuation last.
                let stratified = fresh_space(Arc::new(Box::new(Matcher))).await;
                stratified
                    .get_store()
                    .put_datum(&channel, Datum::create(&channel, item(resting), false));
                stratified
                    .get_store()
                    .put_datum(&channel, Datum::create(&channel, item(arriving), false));
                let stratified_taken = taken(
                    &stratified
                        .consume(
                            vec![channel.clone()],
                            wildcard_patterns(),
                            TaggedContinuation::default(),
                            false,
                            BTreeSet::new(),
                        )
                        .await
                        .expect("consume must not error"),
                );

                // Both regimes must fire, and both must take one of the two
                // data — the SET of admissible selections is unchanged. That is
                // the monotonicity claim, and it is what must not break.
                assert_eq!(
                    arrival_taken,
                    vec![arriving],
                    "the arriving datum did not win the pool despite its `-1` index \
                     (resting={resting}, arriving={arriving}) — if this fails, the \
                     splice at rspace.rs:875-882 is no longer ahead of the canonical \
                     order and the comment at :778-802 has gone stale"
                );
                assert!(
                    stratified_taken == vec![resting] || stratified_taken == vec![arriving],
                    "the stratified regime took something never sent: {stratified_taken:?}"
                );

                trials += 1;
                if arrival_taken != stratified_taken {
                    divergences += 1;
                    if examples.len() < 4 {
                        examples.push(format!(
                            "resting={resting} arriving={arriving}: arrival takes \
                             {arrival_taken:?}, stratified takes {stratified_taken:?}"
                        ));
                    }
                }
            }
        }
    }

    println!("\n── X1 · the `-1` fresh-datum index (sweep over {trials} ordered pairs) ──");
    println!("   arrival regime ALWAYS takes the arriving datum : true (asserted)");
    println!(
        "   the LEAST admissible selection differs         : {divergences}/{trials} pairs \
         ({:.0}%)",
        100.0 * divergences as f64 / trials as f64
    );
    for example in &examples {
        println!("     · {example}");
    }
    assert!(trials > 0, "the sweep must run at least one pair");
}

/// ★ The `where` guard participates in SELECTION. Program (b) rests a 55 the
/// guard rejects next to a 42 it admits; exactly one rendezvous must be
/// enabled, and it must take the 42.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn t2d_where_guard() {
    let program = corpus()
        .into_iter()
        .find(|p| p.label == "b-where-guard")
        .expect("program (b) is in the corpus");

    let ordinary = run_ordinary(program.par.clone()).await;
    let speculative = run_speculative(program.par.clone()).await;
    let enabled = enabled_set(&speculative.quiescent).await;

    println!("\n── X1 · WHERE GUARD ──");
    println!(
        "   ordinary consumed    : {:?}",
        ordinary.fired.iter().map(|f| f.consumed_ints()).collect::<Vec<_>>()
    );
    println!(
        "   resting after        : {:?}",
        resting_ints(&ordinary.final_state, &chan("x1-offer"))
    );
    println!("   |E(S)|               : {}", enabled.len());
    for rendezvous in &enabled {
        println!("     selects {:?}", rendezvous.selected);
    }

    assert_eq!(enabled.len(), 1, "exactly one guarded rendezvous must be enabled");
    assert_eq!(
        enabled[0].selected,
        vec![42],
        "the guard must select the admissible 42, not the rejected 55"
    );
}

/// ★ JOIN. Both channels must carry a datum at quiescence and the joined
/// rendezvous must be enabled.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn t2e_join() {
    let program = corpus()
        .into_iter()
        .find(|p| p.label == "c-join")
        .expect("program (c) is in the corpus");

    let ordinary = run_ordinary(program.par.clone()).await;
    let speculative = run_speculative(program.par.clone()).await;
    let enabled = enabled_set(&speculative.quiescent).await;

    println!("\n── X1 · JOIN ──");
    println!("   ordinary COMMs fired : {}", ordinary.fired.len());
    println!(
        "   join index at quiescence : {:?}",
        speculative
            .quiescent
            .joins
            .keys()
            .map(|k| describe_channels(std::slice::from_ref(k)))
            .collect::<Vec<_>>()
    );
    println!("   |E(S)|               : {}", enabled.len());

    assert_eq!(ordinary.fired.len(), 1, "the join must fire exactly one COMM");
    assert_eq!(
        enabled.len(),
        1,
        "X1 REFUTED (join) — the joined rendezvous is NOT enabled at administrative \
         quiescence"
    );
    assert_eq!(enabled[0].selected, vec![1, 2]);
    assert_eq!(
        speculative.quiescent.joins.len(),
        2,
        "both join-index entries must be staged"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// R — the randomness-splitting premise (folded in)
// ══════════════════════════════════════════════════════════════════════════

/// A program whose COMM structure is CONFLUENT (no contended rendezvous at
/// all) but whose parallel width is large, so the only thing that could vary
/// across runs is the random split assigned to each parallel term. Each `new`
/// mints an unforgeable name whose bytes come from that split, and each is sent
/// to its own channel.
fn confluent_new_fan(width: usize) -> Par {
    let mut program = Par::default();
    for index in 0..width {
        program = program.append(models::rust::utils::new_new_par(
            1,
            Par::default().with_sends(vec![Send {
                chan: Some(chan(&format!("x1-rand-{index}"))),
                data: vec![models::rust::utils::new_boundvar_par(
                    0,
                    models::create_bit_vector(&vec![0]),
                    false,
                )],
                persistent: false,
                locally_free: models::create_bit_vector(&vec![0]),
                connective_used: false,
            }]),
            Vec::new(),       // uri
            BTreeMap::new(),  // injections
            Vec::new(),       // locally_free (of the New)
            Vec::new(),       // locally_free (of the wrapping Par)
            false,            // connective_used
        ));
    }
    program
}

/// A stable fingerprint of the whole tuplespace: every channel's resting data,
/// rendered with prost encoding and sorted. Two runs agree ⟺ their stores are
/// byte-identical.
fn store_fingerprint(state: &State) -> Vec<String> {
    use prost::Message;
    let mut lines: Vec<String> = state
        .data
        .iter()
        .flat_map(|(channel, data)| {
            let channel_bytes = hex(&channel.encode_to_vec());
            data.iter()
                .map(|datum| {
                    let mut payload: Vec<String> =
                        datum.a.pars.iter().map(|p| hex(&p.encode_to_vec())).collect();
                    payload.sort();
                    format!("{channel_bytes} → [{}]", payload.join(","))
                })
                .collect::<Vec<_>>()
        })
        .collect();
    lines.sort();
    lines
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// **Is `Blake2b512Random` splitting structural (positional, reproducible) or
/// dynamic (task-order dependent)?**
///
/// The mechanism says structural: `Reduce::eval_par` (`reduce.rs:642-704`)
/// computes `split(index, &terms, rand.clone())` with `index` the POSITIONAL
/// index of the term in a `terms` vector assembled in a fixed field order
/// (sends, receives, news, matches, conditionals, bundles, exprs), and it
/// computes it EAGERLY inside `.map(...)`, before any future is polled. Nothing
/// about completion order can reach it.
///
/// This test tries to break that empirically: 5 runs of a 16-wide `new` fan on
/// a multi-threaded runtime, comparing the resulting stores byte for byte.
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn r1_randomness_splitting_is_structural() {
    const RUNS: usize = 5;
    let program = confluent_new_fan(16);

    let mut fingerprints: Vec<Vec<String>> = Vec::with_capacity(RUNS);
    for _ in 0..RUNS {
        let run = run_ordinary(program.clone()).await;
        fingerprints.push(store_fingerprint(&run.final_state));
    }

    println!("\n── X1 · randomness splitting ({RUNS} runs, 8 worker threads) ──");
    println!("   channels per run : {}", fingerprints[0].len());
    let all_equal = fingerprints.iter().all(|f| f == &fingerprints[0]);
    println!("   all runs byte-identical : {all_equal}");
    if !all_equal {
        for (index, fingerprint) in fingerprints.iter().enumerate() {
            println!("   run {index}: {} entries", fingerprint.len());
        }
    }

    assert!(
        !fingerprints[0].is_empty(),
        "TEETH FAILED: the fan produced nothing, so the comparison is vacuous"
    );
    assert!(
        all_equal,
        "RANDOMNESS SPLITTING IS DYNAMIC — {RUNS} runs of a confluent program on a \
         multi-threaded runtime produced different stores. Speculation results are \
         not reproducible and the design needs rethinking."
    );
}

/// The same question for a genuinely CONTENDED program: two data, two
/// receivers, one channel. RSpace's candidate order is a content hash with the
/// store index as tie breaker (`rspace.rs:1313-1325` — "this never shuffled"),
/// so even the contended outcome should be reproducible. If it is not, the
/// speculative trace model would have to enumerate schedules it cannot
/// reproduce.
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn r2_the_whole_run_is_reproducible_under_the_multi_threaded_runtime() {
    const RUNS: usize = 5;
    let program = corpus()
        .into_iter()
        .find(|p| p.label == "a-two-data-two-receives")
        .expect("program (a) is in the corpus")
        .par;

    let mut outcomes: Vec<Vec<Vec<i64>>> = Vec::with_capacity(RUNS);
    let mut fingerprints: Vec<Vec<String>> = Vec::with_capacity(RUNS);
    for _ in 0..RUNS {
        let run = run_ordinary(program.clone()).await;
        let mut selections: Vec<Vec<i64>> =
            run.fired.iter().map(|f| f.consumed_ints()).collect();
        selections.sort();
        outcomes.push(selections);
        fingerprints.push(store_fingerprint(&run.final_state));
    }

    println!("\n── X1 · reproducibility of a CONTENDED run ({RUNS} runs, 8 threads) ──");
    for (index, outcome) in outcomes.iter().enumerate() {
        println!("   run {index}: selections {outcome:?}");
    }
    let outcomes_equal = outcomes.iter().all(|o| o == &outcomes[0]);
    let stores_equal = fingerprints.iter().all(|f| f == &fingerprints[0]);
    println!("   selections identical across runs : {outcomes_equal}");
    println!("   stores byte-identical            : {stores_equal}");

    assert!(
        outcomes_equal && stores_equal,
        "A CONTENDED RUN IS NOT REPRODUCIBLE across {RUNS} multi-threaded runs — \
         speculation over traces cannot be replayed."
    );
}

// ══════════════════════════════════════════════════════════════════════════
// C — `check_commit` purity (folded in)
// ══════════════════════════════════════════════════════════════════════════

/// **Is `Matcher::check_commit` a pure predicate?**
///
/// By construction (`rholang/src/rust/interpreter/matcher/match.rs:79-91`) it
/// reads `k.guard`, builds a FRESH `rho_pure_eval::Env` from the matched pars,
/// and evaluates with a FRESH `SpatialMatcherContext` per question. `Matcher`
/// is a unit struct, so there is no state to mutate and no cost handle to
/// charge; the only effects are two `tracing::debug!` events on the two
/// fail-shut branches.
///
/// This test attacks the claim from the outside: ask the same question many
/// times, interleaved with DIFFERENT questions, and require a constant verdict.
/// A stateful matcher — the failure mode the fresh-context discipline exists to
/// prevent — would drift.
#[tokio::test]
async fn c1_check_commit_is_a_pure_predicate() {
    assert_eq!(
        std::mem::size_of::<Matcher>(),
        0,
        "Matcher is expected to be a zero-sized type — it has no state to carry"
    );

    let matcher = Matcher;
    let guard = guard_first_bound_at_most_45();
    let admissible = ListParWithRandom {
        pars: vec![new_gint_par(42, Vec::new(), false)],
        random_state: Vec::new(),
    };
    let inadmissible = ListParWithRandom {
        pars: vec![new_gint_par(55, Vec::new(), false)],
        random_state: Vec::new(),
    };
    let guarded = TaggedContinuation {
        guard: Some(guard),
        ..TaggedContinuation::default()
    };
    let unguarded = TaggedContinuation::default();

    for _ in 0..256 {
        assert!(
            matcher.check_commit(&guarded, &[&admissible]),
            "check_commit drifted: the admissible datum stopped passing"
        );
        assert!(
            !matcher.check_commit(&guarded, &[&inadmissible]),
            "check_commit drifted: the inadmissible datum started passing"
        );
        assert!(
            matcher.check_commit(&unguarded, &[&inadmissible]),
            "an unguarded continuation must always commit"
        );
    }
    println!("\n── X1 · check_commit purity ──");
    println!("   256 interleaved repetitions: verdicts constant");
    println!("   size_of::<Matcher>() = 0 (no state, no cost handle reachable)");
}

/// How much MORE matching does enumerating the enabled set cost than one
/// ordinary run? This is a measurement, not an assertion about a threshold:
/// the design needs the number, and it needs to know that the extra work is
/// paid in wall time rather than in consensus-visible phlogiston (which
/// `check_commit` has no handle to charge).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn c2_the_matching_cost_of_enumeration() {
    println!("\n── X1 · matcher call counts (ordinary run vs speculative staging) ──");
    println!(
        "   {:<28} {:>10} {:>14} {:>10} {:>14}",
        "program", "ord.get", "ord.check", "spec.get", "spec.check"
    );
    for program in corpus() {
        let ordinary = run_ordinary(program.par.clone()).await;
        let speculative = run_speculative(program.par.clone()).await;
        println!(
            "   {:<28} {:>10} {:>14} {:>10} {:>14}",
            program.label,
            ordinary.get_calls,
            ordinary.check_commit_calls,
            speculative.get_calls,
            speculative.check_commit_calls
        );
        // Staging asks the matcher NOTHING — the produce/consume overrides never
        // reach the candidate search. That is the whole point of the two-phase
        // split, and it means the enumeration cost is entirely in the E(S)
        // probes, where it is explicit and boundable.
        assert_eq!(
            speculative.get_calls, 0,
            "{}: the speculative staging path must not invoke the matcher",
            program.label
        );
        assert_eq!(
            speculative.check_commit_calls, 0,
            "{}: the speculative staging path must not invoke check_commit",
            program.label
        );
    }
}
