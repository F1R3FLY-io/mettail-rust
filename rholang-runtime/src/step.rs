//! Reactive, back-pressured **single-step COMM stepper** for the Rho machine — the
//! `step` command's live evidence when a language's default backend is `RhoMachine`, and the
//! runtime-observation half of the MeTTaIL cost-accounting integration.
//!
//! ## How it works
//!
//! A [`StepSession`] spawns a dedicated **worker thread** that builds an in-memory f1r3node
//! `RhoRuntime`, wraps its live `RSpace` in a [`SteppingSpace`] observer, and runs `inj` to
//! quiescence under a **deterministic** seed. The observer and the reducer's
//! back-pressure gate cooperate so the reduction advances **exactly one COMM per
//! [`StepSession::next_step`]** (pay-as-you-go — works for divergent Rholang; dropping the session
//! aborts the worker mid-flight). The two halves are decoupled:
//!
//! - **EMIT** (`produce`/`consume`, on the worker): clones the successful COMM result and sends it
//!   to the driver without rendering.
//! - **GATE** (`StepGate`, a synchronous permit): the worker parks after each committed COMM;
//!   `next_step` releases one permit to advance.
//! - **RENDER** (the driver, on a dedicated **large-stack** thread): turns the raw payload `Par`s
//!   into strings via f1r3node's `PrettyPrinter`. The printer is recursive and not yet stack-safe;
//!   running it on a big stack is an interim measure (a stack-safe printer is a separate f1r3node
//!   PR), per the directive to enlarge the stack when interacting with Rholang rather than fork it.
//!
//! Determinism rides the fixed seed + RSpace content-hash match ordering + a monotone emit ordinal,
//! so a trace reproduces bit-identically.
#![cfg(feature = "runtime-report")]

use std::collections::{BTreeSet, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;

use async_trait::async_trait;
use crossbeam_channel::{bounded, Receiver, Sender};

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::tagged_continuation::TaggedCont;
use models::rhoapi::{BindPattern, ListParWithRandom, Par, TaggedContinuation};
use rho_pure_eval::Env;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::has_cost::HasCost;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rholang::rust::interpreter::pretty_printer::PrettyPrinter;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime};
use rholang::rust::interpreter::system_processes::Definition;
use rspace_plus_plus::rspace::checkpoint::{Checkpoint, SoftCheckpoint};
use rspace_plus_plus::rspace::errors::RSpaceError;
use rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash;
use rspace_plus_plus::rspace::internal::{Datum, Row, WaitingContinuation};
use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::rspace_interface::{ISpace, MaybeConsumeResult, MaybeProduceResult};
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;
use rspace_plus_plus::rspace::trace::event::Produce;
use rspace_plus_plus::rspace::trace::Log;

use mettail_runtime::{
    ReductionStepper, RuntimeCommEvent, RuntimeReductionEngine, RuntimeReductionKind,
    RuntimeReductionStep,
};

/// Deterministic seed for the stepper's `inj`. Mirrors the fixed-bytes pattern of f1r3node's
/// `bootstrap_rand` (NOT the entropy `create_from_length`), so the COMM trace reproduces
/// bit-identically across runs and on replay.
const FIXED_SEED: &[u8] =
    b"mettail-oslf reactive single-step COMM tracer :: deterministic seed v1 (do not change)";

/// Stack size for the dedicated thread that renders COMM-payload `Par`s through f1r3node's
/// (recursive, not-yet-stack-safe) `PrettyPrinter`. Large so deeply-nested payloads don't overflow.
/// This is virtual memory (reserved, not committed), so a generous value is cheap. Interim measure.
const RENDER_STACK_SIZE: usize = 256 * 1024 * 1024;

/// Bounded capacity of the COMM-event channel. The back-pressure gate keeps the worker at most one
/// COMM ahead of the driver, so a comfortable bound is never reached.
const STEP_QUEUE_CAP: usize = 4096;

/// A committed COMM, raw (un-rendered). The live-space wrapper pushes this off the reduction thread;
/// the driver renders the `Par`s later, on a large stack.
struct RawCommEvent {
    ordinal: u64,
    label: String,
    channels: Vec<Par>,
    consumed: Vec<ListParWithRandom>,
    /// The firing receive's continuation body (`ParBody`), if any — the receive side of the
    /// rendezvous, rendered later on the large stack.
    continuation: Option<Par>,
}

/// A value resting on the observation channel at quiescence — the program's observable output, read
/// from the tuplespace AFTER `inj` (not a reducer hook). The driver renders `value` on the large stack.
struct RawOutputEvent {
    ordinal: u64,
    channel: String,
    value: Par,
}

/// One emitted step on the single ordered channel — a COMM rendezvous or a terminal observable
/// output. All carry the same monotone ordinal stream (assigned by the observer), so the driver
/// reads them in emit order; the single-permit gate serializes COMM emits one at a time, and the
/// output emits follow once `inj` reaches quiescence.
enum RawStepEvent {
    Comm(RawCommEvent),
    Output(RawOutputEvent),
}

struct StepGateState {
    permits: u64,
    aborted: bool,
}

/// Synchronous one-permit gate used by the live-space wrapper.
struct StepGate {
    state: Mutex<StepGateState>,
    cvar: Condvar,
}

impl StepGate {
    fn new() -> Self {
        Self {
            state: Mutex::new(StepGateState { permits: 0, aborted: false }),
            cvar: Condvar::new(),
        }
    }

    fn release_one(&self) {
        let mut state = self.state.lock().expect("step gate lock");
        state.permits = state.permits.saturating_add(1);
        self.cvar.notify_one();
    }

    fn abort(&self) {
        let mut state = self.state.lock().expect("step gate lock");
        state.aborted = true;
        self.cvar.notify_all();
    }

    fn wait_for_release(&self) -> bool {
        let mut state = self.state.lock().expect("step gate lock");
        while state.permits == 0 && !state.aborted {
            state = self.cvar.wait(state).expect("step gate condvar wait");
        }
        if state.permits > 0 {
            state.permits -= 1;
            true
        } else {
            false
        }
    }
}

/// Shared event emitter used by the live-space wrapper and post-quiescence output reader.
struct StepObserver {
    sender: Sender<RawStepEvent>,
    gate: Arc<StepGate>,
    ordinal: AtomicU64,
}

impl StepObserver {
    fn emit_comm(
        &self,
        label: &'static str,
        channels: Vec<Par>,
        consumed: Vec<ListParWithRandom>,
        continuation: TaggedContinuation,
    ) {
        let ordinal = self.ordinal.fetch_add(1, Ordering::Relaxed);
        let event = RawStepEvent::Comm(RawCommEvent {
            ordinal,
            label: label.to_string(),
            channels,
            consumed,
            continuation: tagged_continuation_body(&continuation),
        });
        if self.sender.send(event).is_err() || !self.gate.wait_for_release() {
            panic!("rho stepper aborted");
        }
    }

    /// Emit a terminal observable-output step — a value resting on the configured output channel at
    /// quiescence. Called by the worker AFTER `inj` returns (NOT by the reducer), so it self-numbers
    /// on the same shared ordinal stream (after all reductions) and pushes non-blocking. No gate
    /// pause: the outputs are the final tuplespace read, collected by the driver after the reductions.
    fn emit_output(&self, channel: String, value: Par) {
        let ordinal = self.ordinal.fetch_add(1, Ordering::Relaxed);
        let _ =
            self.sender
                .try_send(RawStepEvent::Output(RawOutputEvent { ordinal, channel, value }));
    }
}

#[derive(Clone)]
struct SteppingSpace {
    inner: RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
    observer: Arc<StepObserver>,
}

impl SteppingSpace {
    fn emit_if_comm(
        &self,
        label: &'static str,
        result: &MaybeConsumeResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
    ) {
        if let Some((continuation, matched)) = result {
            self.observer.emit_comm(
                label,
                continuation.channels.clone(),
                matched
                    .iter()
                    .map(|item| item.matched_datum.clone())
                    .collect(),
                continuation.continuation.clone(),
            );
        }
    }
}

#[async_trait]
impl ISpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> for SteppingSpace {
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
        self.emit_if_comm("comm.consume", &result);
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
        self.emit_if_comm(
            "comm.produce",
            &result
                .as_ref()
                .map(|(continuation, matched, _)| (continuation.clone(), matched.clone())),
        );
        Ok(result)
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

/// A live, incremental Rho-machine COMM single-stepper. Holds the worker thread, the shared
/// back-pressure gate, and the COMM-event receiver. Implements [`ReductionStepper`]: each
/// `next_step` releases one gate permit (advancing the reducer by exactly one COMM) and renders the
/// resulting event. Dropping the session aborts the worker (closes the gate so a paused `inj`
/// unwinds + the soft-checkpoint reverts) and joins it.
pub struct StepSession {
    receiver: Receiver<RawStepEvent>,
    gate: Arc<StepGate>,
    worker: Option<JoinHandle<Result<(), String>>>,
    done: bool,
}

impl StepSession {
    /// Start a stepper for a lowered `Par` plus its Tier-3 fold-contract `Definition`s (empty `Vec`
    /// for a pure-COMM term — Tier 3 fills it for held-fold terms). Spawns the worker thread, which
    /// builds an in-memory `RhoRuntime` with the COMM observer wrapper and runs `inj` under the
    /// deterministic seed. Returns immediately; the worker runs to the first COMM and pauses on the
    /// gate. A term with no COMMs simply runs to quiescence, and the first `next_step` returns
    /// `None`. `out_channel`, when `Some`, is the program's observation channel: after `inj` reaches
    /// quiescence the worker reads its resting value(s) and emits them as terminal `Output` steps
    /// (the same channel-scoped tuplespace read the `exec` path uses); `None` for Dovetail-only
    /// languages, preserving today's behavior.
    pub fn start(
        par: Par,
        fold_defs: Vec<Definition>,
        out_channel: Option<String>,
    ) -> Result<StepSession, String> {
        let (sender, receiver) = bounded::<RawStepEvent>(STEP_QUEUE_CAP);
        let gate = Arc::new(StepGate::new());
        let observer = Arc::new(StepObserver {
            sender,
            gate: gate.clone(),
            ordinal: AtomicU64::new(0),
        });
        let worker = std::thread::Builder::new()
            .name("mettail-rho-stepper".to_string())
            .spawn(move || run_stepped_inj(par, observer, fold_defs, out_channel))
            .map_err(|e| format!("spawn stepper worker thread: {e}"))?;
        Ok(StepSession {
            receiver,
            gate,
            worker: Some(worker),
            done: false,
        })
    }

    fn join_worker(&mut self) -> Result<(), String> {
        match self.worker.take() {
            Some(handle) => match handle.join() {
                Ok(result) => result,
                Err(_) => Err("stepper worker thread panicked".to_string()),
            },
            None => Ok(()),
        }
    }
}

impl ReductionStepper for StepSession {
    fn next_step(&mut self) -> Result<Option<RuntimeReductionStep>, String> {
        if self.done {
            return Ok(None);
        }
        // Grant the paused worker one step (advance one COMM), then read the front of the queue. The
        // worker emits a COMM event *before* it pauses, so each event is buffered ahead of the
        // release that advances past it; `recv` blocks until the next event or until the worker
        // finishes and drops the observer's `Sender` (disconnect = quiescence).
        self.gate.release_one();
        match self.receiver.recv() {
            Ok(raw) => Ok(Some(render_step(raw))),
            Err(_) => {
                self.done = true;
                self.join_worker()?;
                Ok(None)
            },
        }
    }
}

impl Drop for StepSession {
    fn drop(&mut self) {
        // Abort a paused reducer so `inj` unwinds and the soft-checkpoint reverts, then join the
        // worker so no thread is leaked.
        self.gate.abort();
        if let Some(handle) = self.worker.take() {
            let _ = handle.join();
        }
    }
}

/// The worker body: build an in-memory `RhoRuntime` over a live-space COMM observer, then run `inj`
/// under the deterministic seed. On error, revert the soft checkpoint.
/// Returns when the reduction reaches quiescence (or errors); dropping the runtime here drops the
/// observer's `Sender`, which the driver reads as completion.
fn run_stepped_inj(
    par: Par,
    observer: Arc<StepObserver>,
    mut fold_defs: Vec<Definition>,
    out_channel: Option<String>,
) -> Result<(), String> {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("stepper tokio runtime: {e}"))?;
    runtime.block_on(async move {
        let mut kvm = InMemoryStoreManager::new();
        let store = kvm
            .r_space_stores()
            .await
            .map_err(|e| format!("in-mem store: {e:?}"))?;
        let inner_space =
            RSpace::<Par, BindPattern, ListParWithRandom, TaggedContinuation>::create(
                store,
                Arc::new(Box::new(Matcher)),
            )
            .map_err(|e| format!("rspace: {e:?}"))?;
        let output_observer = observer.clone();
        let space = SteppingSpace { inner: inner_space, observer };
        let mut rho_runtime = create_rho_runtime(
            space,
            Arc::new(HashMap::new()), // mergeable tags: none (single-node eval)
            false,                    // init_registry: not needed
            &mut fold_defs, // Tier-3 fold-contract Definitions (empty for pure-COMM terms)
            ExternalServices::noop(), // inert — no AI/gRPC/Chroma
        )
        .await;
        let checkpoint = rho_runtime.create_soft_checkpoint().await;
        let rand = Blake2b512Random::create_from_bytes(FIXED_SEED);
        rho_runtime.cost().set(Cost::unsafe_max());
        match rho_runtime.inj(par, Env::new(), rand).await {
            Ok(()) => {
                // Post-quiescence: surface the program's observable output(s). The resting value(s)
                // on the configured channel are read with the SAME `get_data` the `exec` path uses
                // (`run::read_ground_from_runtime`); scoping to that channel means a consumed internal
                // send (e.g. `@"c"`, now empty) is never surfaced. Emitted after the reduction steps
                // with no gate pause — the driver collects them, then the dropped `Sender` ⇒ quiescence.
                if let Some(out) = &out_channel {
                    let data = rho_runtime.get_data(&crate::run::quoted_channel(out)).await;
                    for datum in data {
                        for value in datum.a.pars {
                            output_observer.emit_output(out.clone(), value);
                        }
                    }
                }
                Ok(())
            },
            Err(err) => {
                rho_runtime.revert_to_soft_checkpoint(checkpoint).await;
                Err(format!("inj: {err:?}"))
            },
        }
    })
}

fn tagged_continuation_body(continuation: &TaggedContinuation) -> Option<Par> {
    match &continuation.tagged_cont {
        Some(TaggedCont::ParBody(body)) => body.body.clone(),
        _ => None,
    }
}

/// Render a raw step (COMM rendezvous or terminal output) into a [`RuntimeReductionStep`]
/// (rendering happens on a large stack).
fn render_step(raw: RawStepEvent) -> RuntimeReductionStep {
    match raw {
        RawStepEvent::Comm(raw) => {
            let (channels, consumed, continuation) =
                render_payload(&raw.channels, &raw.consumed, raw.continuation.as_ref());
            let display = format_comm(&raw.label, &channels, &consumed, continuation.as_deref());
            RuntimeReductionStep {
                ordinal: raw.ordinal,
                engine: RuntimeReductionEngine::RhoComm,
                kind: RuntimeReductionKind::Comm,
                display,
                comm: Some(RuntimeCommEvent {
                    channels,
                    consumed,
                    label: raw.label,
                    continuation,
                }),
            }
        },
        RawStepEvent::Output(raw) => {
            // A value resting on the observation channel at quiescence — the program's observable
            // output, rendered as `<channel> observes <value>`.
            let value = render_redex(&raw.value);
            RuntimeReductionStep {
                ordinal: raw.ordinal,
                engine: RuntimeReductionEngine::RhoComm,
                kind: RuntimeReductionKind::Output,
                display: format!("{} observes {}", raw.channel, value),
                comm: None,
            }
        },
    }
}

/// Render a single redex `Par` on the dedicated large-stack thread (the `PrettyPrinter` is recursive
/// and not yet stack-safe — same interim measure as [`render_payload`]).
fn render_redex(par: &Par) -> String {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("mettail-rho-par-render".to_string())
            .stack_size(RENDER_STACK_SIZE)
            .spawn_scoped(scope, || render_par(par))
            .expect("spawn par-render thread")
            .join()
            .expect("par-render thread panicked")
    })
}

/// Render the raw COMM `Par`s on a dedicated **large-stack** thread — f1r3node's `PrettyPrinter` is
/// recursive and not yet stack-safe, so deeply-nested payloads would overflow a normal stack.
/// Interim measure (see the module/`Cargo.toml` notes; a stack-safe printer is a separate PR).
fn render_payload(
    channels: &[Par],
    consumed: &[ListParWithRandom],
    continuation: Option<&Par>,
) -> (Vec<String>, Vec<String>, Option<String>) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("mettail-rho-par-render".to_string())
            .stack_size(RENDER_STACK_SIZE)
            .spawn_scoped(scope, || {
                let rendered_channels = channels.iter().map(render_par).collect::<Vec<_>>();
                let rendered_consumed = consumed
                    .iter()
                    .flat_map(|datum| datum.pars.iter())
                    .map(render_par)
                    .collect::<Vec<_>>();
                let rendered_continuation = continuation.map(render_par);
                (rendered_channels, rendered_consumed, rendered_continuation)
            })
            .expect("spawn par-render thread")
            .join()
            .expect("par-render thread panicked")
    })
}

fn render_par(par: &Par) -> String {
    let mut printer = PrettyPrinter::new();
    printer.build_string_from_message(par)
}

/// One-line COMM rendering: `COMM[consume] <channels> ⇐ {<consumed data>}`, with the receive's
/// continuation appended (`▸ cont <body>`) when present, so both sides of the rendezvous show.
fn format_comm(
    label: &str,
    channels: &[String],
    consumed: &[String],
    continuation: Option<&str>,
) -> String {
    let side = match label {
        "comm.consume" => "consume",
        "comm.produce" => "produce",
        other => other,
    };
    let base = format!("COMM[{}] {} ⇐ {{{}}}", side, channels.join(", "), consumed.join(", "));
    match continuation {
        Some(cont) if !cont.is_empty() => format!("{base} ▸ cont {cont}"),
        _ => base,
    }
}

#[cfg(all(test, feature = "rhocalc-runtime"))]
mod tests {
    use super::*;
    use crate::rhocalc_ast::lower_rhocalc_term;
    use mettail_languages::rhocalc::{Int, Proc, RhoCalcLanguage, RhoCalcTerm, RhoCalcTermInner};
    use mettail_runtime::Language;

    /// The flagship COMM term: a receive on `@"c"` and a matching send carrying the process
    /// `@"OUT"!("p")` — exactly one rendezvous fires.
    // Guarded-receive sugar `(@("c")?x).{p}` was superseded by main's `for(x <- c){p}`
    // (RhoCalc → Rholang 1.4 merge). `(c?x).{p} ≡ for(x <- c){p}`; the sibling oracle
    // `tests/rho_rhocalc_ast.rs` uses the same `for(...)` form.
    const COMM_SRC: &str = r#"{ for(x <- @("c")){*(x)} | @("c")!(@("OUT")!("p")) }"#;

    fn lower(src: &str) -> Par {
        let term = RhoCalcLanguage.parse_term(src).expect("parse rhocalc term");
        lower_rhocalc_term(term.as_ref()).expect("lower rhocalc term to a Par")
    }

    fn drive(par: Par) -> Vec<RuntimeReductionStep> {
        // RhoCalc observes `"OUT"`; the stepper reads its resting output post-quiescence. (A term
        // whose send rests on a different channel simply yields no output step.)
        let mut session = StepSession::start(par, Vec::new(), Some("OUT".to_string()))
            .expect("start step session");
        let mut steps = Vec::new();
        while let Some(step) = session.next_step().expect("next_step must not error") {
            steps.push(step);
        }
        steps
    }

    fn pure_int_fold_term(value: i64, width: i64) -> RhoCalcTerm {
        RhoCalcTerm(RhoCalcTermInner::Proc(Proc::IntBinProc(
            Arc::new(Proc::CastInt(Arc::new(Int::NumLit(value)))),
            Arc::new(Int::NumLit(width)),
        )))
    }

    #[test]
    fn comm_term_yields_comm_and_output_steps() {
        // Current f1r3node no longer exposes a separate structural-reduction hook. The stepper
        // records live COMM results at the RSpace boundary and the terminal `OUT` observation
        // produced by the continuation.
        let steps = drive(lower(COMM_SRC));
        let kinds: Vec<RuntimeReductionKind> = steps.iter().map(|s| s.kind).collect();
        assert_eq!(
            kinds,
            vec![RuntimeReductionKind::Comm, RuntimeReductionKind::Output],
            "COMM, then the OUT output; got {kinds:?}",
        );
        for (index, step) in steps.iter().enumerate() {
            assert_eq!(step.ordinal, index as u64, "ordinals must be dense and monotone");
            assert_eq!(step.engine, RuntimeReductionEngine::RhoComm, "all Rho-machine steps");
        }
        let comm = &steps[0];
        let comm_event = comm
            .comm
            .as_ref()
            .expect("the COMM step carries its event payload");
        assert!(
            comm.display.starts_with("COMM["),
            "COMM rendered as a COMM line: {}",
            comm.display
        );
        assert!(
            comm_event.continuation.is_some() && comm.display.contains("cont"),
            "the COMM step surfaces the receive's continuation: {}",
            comm.display,
        );
        let output = &steps[1];
        assert!(output.comm.is_none(), "the output step has no COMM payload");
        assert!(
            output.display.contains("OUT") && output.display.contains("observes"),
            "the output step shows the OUT observation: {}",
            output.display,
        );
    }

    #[test]
    fn lone_send_yields_no_reduction_steps() {
        // A send with no matching receive never rendezvouses, and depositing it is not a reduction
        // (a resting output is a residual, not a step) — so the worker reaches quiescence with zero
        // reduction steps and the first `next_step` returns `None`.
        let steps = drive(lower(r#"{ @("c")!(@("OUT")!("p")) }"#));
        assert!(steps.is_empty(), "a lone send fires no reduction; got {} step(s)", steps.len());
    }

    #[test]
    fn trace_is_deterministic_under_the_fixed_seed() {
        let displays = |par: Par| {
            drive(par)
                .into_iter()
                .map(|s| s.display)
                .collect::<Vec<_>>()
        };
        assert_eq!(
            displays(lower(COMM_SRC)),
            displays(lower(COMM_SRC)),
            "the COMM trace must reproduce bit-identically (deterministic FIXED_SEED + match order)"
        );
    }

    #[test]
    fn wrapper_start_reduction_stepper_drives_a_comm_term() {
        // End-to-end through the production RhoCalc wrapper: `Language::start_reduction_stepper`
        // runs the D-stage + F-stage lowering and hands back a live stepper over the program Par.
        use crate::rhocalc_ast::dovetail_rho_backed_rhocalc;
        let language = dovetail_rho_backed_rhocalc("OUT").expect("build RhoCalc wrapper");
        let term = RhoCalcLanguage
            .parse_term(COMM_SRC)
            .expect("parse COMM term");
        let mut stepper = language
            .start_reduction_stepper(term.as_ref())
            .expect("wrapper starts a stepper");
        let mut count = 0usize;
        while stepper.next_step().expect("next_step").is_some() {
            count += 1;
        }
        assert!(count >= 1, "the wrapper's stepper must yield ≥1 COMM step; got {count}");
    }

    #[test]
    fn held_fold_lowering_emits_one_fold_contract_spec() {
        // A-S4 (lowering purity): EVERY fold lifts — the held `int(*(x),8)` AND the ground
        // send-side `int(5,8)` (which pre-A-S4 folded in place, host-side). Two folds ⇒ two
        // fold-contract specs, both Int width 8. The top level is now the ground fold's
        // trampoline scope (`new ret0 { @fold0!(5, ret0) | for(@r0 <- ret0){ … } }`), so the
        // original send/receive pair sits INSIDE that `new`.
        let term = RhoCalcLanguage
            .parse_term(r#"{ for(x <- @("c")){ int(*(x), 8) } | @("c")!(int(5,8)) }"#)
            .expect("parse");
        let (par, specs) = crate::rhocalc_ast::lower_rhocalc_term_with_folds(term.as_ref())
            .expect("both folds lift, so lowering succeeds");
        assert_eq!(specs.len(), 2, "held fold + ground fold ⇒ two fold-contract specs (A-S4)");
        for spec in &specs {
            assert_eq!(spec.kind, crate::fold_contract::FoldKind::Int);
            assert_eq!(spec.width, 8);
        }
        assert_eq!(
            par.news.len(),
            1,
            "the top level is the ground fold's trampoline `new` scope"
        );
    }

    #[test]
    fn held_fold_over_comm_received_value_reduces_via_trampoline() {
        // Tier-3 flagship: `int(*(x), 8)` whose operand `x` is bound by the COMM `receive` — stuck
        // on Dovetail. The lowering lifts it to a fold-contract trampoline; stepping must show the
        // receive/send COMM AND the fold-contract COMM(s), proving the held fold reduces on the Rho
        // machine.
        use crate::rhocalc_ast::dovetail_rho_backed_rhocalc;
        let language = dovetail_rho_backed_rhocalc("OUT").expect("build RhoCalc wrapper");
        let term = RhoCalcLanguage
            .parse_term(r#"{ for(x <- @("c")){ int(*(x), 8) } | @("c")!(int(5,8)) }"#)
            .expect("parse held-fold term");
        let mut stepper = language
            .start_reduction_stepper(term.as_ref())
            .expect("the held fold lifts to a COMM program, so a stepper starts");
        let mut steps = Vec::new();
        while let Some(step) = stepper.next_step().expect("next_step") {
            steps.push(step);
        }
        assert!(
            steps.len() >= 2,
            "held-fold term yields the receive COMM + the fold-contract COMM; got {} step(s): {:?}",
            steps.len(),
            steps.iter().map(|s| &s.display).collect::<Vec<_>>()
        );
    }

    #[test]
    fn wrapper_pure_fold_term_steps_to_output_only() {
        // A-S4: a pure ground fold is no longer host-folded at lowering time — the trace now
        // SHOWS the machine computing it: the fold-contract COMM step(s) first (the trampoline
        // rendezvous that produces the folded value), then the terminal output observing the
        // machine-computed result on OUT.
        use crate::rhocalc_ast::dovetail_rho_backed_rhocalc;
        let language = dovetail_rho_backed_rhocalc("OUT").expect("build RhoCalc wrapper");
        let term = pure_int_fold_term(5, 8);
        let mut stepper = language
            .start_reduction_stepper(&term)
            .expect("pure fold has a Rho observation program");
        let mut steps = Vec::new();
        while let Some(step) = stepper.next_step().expect("next_step must not error") {
            steps.push(step);
        }
        assert!(
            steps.len() >= 2,
            "the ground fold trampolines on the machine (fold-contract COMM) before the \
             terminal output; got {} step(s): {:?}",
            steps.len(),
            steps.iter().map(|s| &s.display).collect::<Vec<_>>()
        );
        let last = steps.last().expect("checked non-empty");
        assert_eq!(
            last.kind,
            RuntimeReductionKind::Output,
            "the trace ends with the terminal OUT observation"
        );
        assert!(
            last.display.contains("OUT") && last.display.contains("5"),
            "pure fold output should observe the machine-computed 5 on OUT: {}",
            last.display
        );
    }

    #[test]
    fn dropping_a_session_mid_trace_aborts_cleanly() {
        // Start a session, take one step, then drop it: the gate aborts the paused worker and the
        // Drop impl joins it without leaking a thread or panicking.
        let mut session = StepSession::start(lower(COMM_SRC), Vec::new(), Some("OUT".to_string()))
            .expect("start");
        let _first = session.next_step().expect("first step");
        drop(session); // must not hang or panic
    }
}
