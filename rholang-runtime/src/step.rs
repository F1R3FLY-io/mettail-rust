//! Reactive, lock-free, back-pressured **single-step COMM stepper** for the Rho machine — the
//! `step` command's live evidence when a language's default backend is `RhoMachine`, and the
//! runtime-observation half of the MeTTaIL/OSLF cost-accounting integration.
//!
//! ## How it works
//!
//! A [`StepSession`] spawns a dedicated **worker thread** that builds an in-memory f1r3node
//! `RhoRuntime`, installs a [`StepObserver`] on the base `RSpace` (the lock-free COMM emit seam),
//! and runs `inj` to quiescence under a **deterministic** seed. The observer and the reducer's
//! back-pressure gate cooperate so the reduction advances **exactly one COMM per
//! [`StepSession::next_step`]** (pay-as-you-go — works for divergent Rholang; dropping the session
//! aborts the worker mid-flight). The two halves are decoupled:
//!
//! - **EMIT** (`observe_comm`, on the worker, possibly under a tuplespace lock): clones the raw COMM
//!   payload and `try_send`s it — never blocks, never renders.
//! - **GATE** (`StepGate`, an async pause at a reducer boundary that holds no lock): the worker
//!   parks after each committed COMM; `next_step` releases one permit to advance.
//! - **RENDER** (the driver, on a dedicated **large-stack** thread): turns the raw payload `Par`s
//!   into strings via f1r3node's `PrettyPrinter`. The printer is recursive and not yet stack-safe;
//!   running it on a big stack is an interim measure (a stack-safe printer is a separate f1r3node
//!   PR), per the directive to enlarge the stack when interacting with Rholang rather than fork it.
//!
//! Determinism rides the fixed seed + RSpace content-hash match ordering + a monotone emit ordinal,
//! so a trace reproduces bit-identically.
#![cfg(feature = "runtime-report")]

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::thread::JoinHandle;

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
use rspace_plus_plus::rspace::logging::{ReductionKind, StepCommObserver, StepGate};
use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;
use rspace_plus_plus::rspace::trace::event::COMM;

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
/// COMM ahead of the driver, so a comfortable bound is never reached — it only provides slack so
/// the lock-free `try_send` in `observe_comm` cannot lose an event.
const STEP_QUEUE_CAP: usize = 4096;

/// A committed COMM, raw (un-rendered). The observer pushes this lock-free off the reduction thread;
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

/// A committed non-COMM structural reduction, raw (un-rendered). The observer pushes this lock-free
/// off the reduction thread; the driver renders the `redex` Par later, on a large stack.
struct RawReductionEvent {
    ordinal: u64,
    kind: ReductionKind,
    redex: Par,
}

/// A value resting on the observation channel at quiescence — the program's observable output, read
/// from the tuplespace AFTER `inj` (not a reducer hook). The driver renders `value` on the large stack.
struct RawOutputEvent {
    ordinal: u64,
    channel: String,
    value: Par,
}

/// One emitted step on the single ordered channel — a COMM rendezvous, a non-COMM structural
/// reduction, or a terminal observable output. All carry the same monotone ordinal stream (assigned
/// by the observer), so the driver reads them in emit order; the single-permit gate serializes the
/// reduction emits one at a time, and the output emits follow once `inj` reaches quiescence.
enum RawStepEvent {
    Comm(RawCommEvent),
    Reduction(RawReductionEvent),
    Output(RawOutputEvent),
}

/// The COMM observer the stepper installs on the `RSpace`. `observe_comm` clones the payload and
/// pushes it (non-blocking); `step_gate` hands the reducer the shared back-pressure gate so it
/// pauses after each committed COMM.
struct StepObserver {
    sender: Sender<RawStepEvent>,
    gate: Arc<StepGate>,
    ordinal: AtomicU64,
}

impl StepObserver {
    /// Emit a terminal observable-output step — a value resting on the configured output channel at
    /// quiescence. Called by the worker AFTER `inj` returns (NOT by the reducer), so it self-numbers
    /// on the same shared ordinal stream (after all reductions) and pushes non-blocking. No gate
    /// pause: the outputs are the final tuplespace read, collected by the driver after the reductions.
    fn emit_output(&self, channel: String, value: Par) {
        let ordinal = self.ordinal.fetch_add(1, Ordering::Relaxed);
        let _ =
            self.sender.try_send(RawStepEvent::Output(RawOutputEvent { ordinal, channel, value }));
    }
}

impl StepCommObserver<Par, BindPattern, ListParWithRandom, TaggedContinuation> for StepObserver {
    fn observe_comm(
        &self,
        channels: &[Par],
        consumed: &[ListParWithRandom],
        _patterns: &[BindPattern],
        continuation: &TaggedContinuation,
        _comm: &COMM,
        label: &str,
    ) {
        let ordinal = self.ordinal.fetch_add(1, Ordering::Relaxed);
        // The receive side of the rendezvous: the firing waiting-continuation's body (`*x`, …). Carry
        // it raw; the driver renders it on the large stack so both sides of the COMM are visible.
        let continuation = match &continuation.tagged_cont {
            Some(TaggedCont::ParBody(body)) => body.body.clone(),
            _ => None,
        };
        let event = RawStepEvent::Comm(RawCommEvent {
            ordinal,
            label: label.to_string(),
            channels: channels.to_vec(),
            consumed: consumed.to_vec(),
            continuation,
        });
        // Non-blocking: never block under the tuplespace lock. The gate keeps us ≤1 step ahead of
        // the driver, so the bounded queue cannot fill in practice; if it ever did, dropping the
        // event is strictly safer than stalling the reducer.
        let _ = self.sender.try_send(event);
    }

    fn observe_reduction(&self, redex: &Par, kind: ReductionKind) {
        // Self-number on the SAME monotone ordinal stream as `observe_comm`, so COMM and structural
        // reductions interleave in one ordered sequence (the single-permit gate serializes emits).
        // Clone the redex (cheap, and only this installed observer runs) and push non-blocking off
        // the reduction thread; rendering happens later on a large stack.
        let ordinal = self.ordinal.fetch_add(1, Ordering::Relaxed);
        let event =
            RawStepEvent::Reduction(RawReductionEvent { ordinal, kind, redex: redex.clone() });
        let _ = self.sender.try_send(event);
    }

    fn step_gate(&self) -> Option<Arc<StepGate>> {
        Some(self.gate.clone())
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
    /// builds an in-memory `RhoRuntime` with the COMM observer installed and runs `inj` under the
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
        let observer =
            Arc::new(StepObserver { sender, gate: gate.clone(), ordinal: AtomicU64::new(0) });
        let worker = std::thread::Builder::new()
            .name("mettail-rho-stepper".to_string())
            .spawn(move || run_stepped_inj(par, observer, fold_defs, out_channel))
            .map_err(|e| format!("spawn stepper worker thread: {e}"))?;
        Ok(StepSession { receiver, gate, worker: Some(worker), done: false })
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

/// The worker body: build an in-memory `RhoRuntime` with the COMM observer installed on its
/// `RSpace`, then run `inj` under the deterministic seed. On error, revert the soft checkpoint.
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
        let store = kvm.r_space_stores().await.map_err(|e| format!("in-mem store: {e:?}"))?;
        let mut space: RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> =
            RSpace::create(store, Arc::new(Box::new(Matcher))).map_err(|e| format!("rspace: {e:?}"))?;
        // Install the COMM observer (+ shared back-pressure gate) BEFORE building the runtime, so the
        // reducer's `self.space.step_gate()` sees it and pauses after each COMM.
        // Keep a handle for the post-quiescence output emit before the cast moves this Arc into the
        // space (the reducer reaches the installed observer through `self.space`).
        let output_observer = observer.clone();
        space.set_step_observer(Some(observer
            as Arc<dyn StepCommObserver<Par, BindPattern, ListParWithRandom, TaggedContinuation>>));
        let mut rho_runtime = create_rho_runtime(
            space,
            Arc::new(HashMap::new()), // mergeable tags: none (single-node eval)
            false,                    // init_registry: not needed
            &mut fold_defs,           // Tier-3 fold-contract Definitions (empty for pure-COMM terms)
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

/// Render a raw step (COMM rendezvous or non-COMM structural reduction) into a
/// [`RuntimeReductionStep`] (rendering happens on a large stack).
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
                comm: Some(RuntimeCommEvent { channels, consumed, label: raw.label, continuation }),
            }
        },
        RawStepEvent::Reduction(raw) => {
            // The redex Par is the process the reducer is about to evaluate (the dereferenced
            // process, the matched case body, …); render it on the large stack. The kind (the node
            // label) supplies the "what kind of step" context.
            let display = render_redex(&raw.redex);
            RuntimeReductionStep {
                ordinal: raw.ordinal,
                engine: RuntimeReductionEngine::RhoComm,
                kind: map_reduction_kind(raw.kind),
                display,
                comm: None,
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

/// Map the fork's `ReductionKind` to the runtime-neutral `RuntimeReductionKind` (1:1).
fn map_reduction_kind(kind: ReductionKind) -> RuntimeReductionKind {
    match kind {
        ReductionKind::Deref => RuntimeReductionKind::Deref,
        ReductionKind::Match => RuntimeReductionKind::Match,
        ReductionKind::If => RuntimeReductionKind::If,
        ReductionKind::New => RuntimeReductionKind::New,
        ReductionKind::Bundle => RuntimeReductionKind::Bundle,
        ReductionKind::Method => RuntimeReductionKind::Method,
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
    use mettail_languages::rhocalc::RhoCalcLanguage;
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

    #[test]
    fn comm_term_yields_comm_deref_output_steps() {
        // The per-reduction stepper observes EVERY meaningful reduction AND the program's observable
        // output: the flagship term reduces by one COMM rendezvous, then the receive's continuation
        // `*(x)` dereferences to the send `@("OUT")!("p")`, which finally produces on `@"OUT"` ⇒
        // `OUT observes "p"`. Engine is `RhoComm` throughout; the COMM carries its event payload (and
        // the receive's continuation in its display), the deref and output do not.
        let steps = drive(lower(COMM_SRC));
        let kinds: Vec<RuntimeReductionKind> = steps.iter().map(|s| s.kind).collect();
        assert_eq!(
            kinds,
            vec![
                RuntimeReductionKind::Comm,
                RuntimeReductionKind::Deref,
                RuntimeReductionKind::Output,
            ],
            "COMM, dereference, then the OUT output; got {kinds:?}",
        );
        for (index, step) in steps.iter().enumerate() {
            assert_eq!(step.ordinal, index as u64, "ordinals must be dense and monotone");
            assert_eq!(step.engine, RuntimeReductionEngine::RhoComm, "all Rho-machine steps");
        }
        let comm = &steps[0];
        let comm_event = comm.comm.as_ref().expect("the COMM step carries its event payload");
        assert!(comm.display.starts_with("COMM["), "COMM rendered as a COMM line: {}", comm.display);
        assert!(
            comm_event.continuation.is_some() && comm.display.contains("cont"),
            "the COMM step surfaces the receive's continuation: {}",
            comm.display,
        );
        let deref = &steps[1];
        assert!(deref.comm.is_none(), "a structural reduction has no COMM payload");
        assert!(
            deref.display.contains("OUT") && deref.display.contains('p'),
            "the deref yields the OUT send: {}",
            deref.display,
        );
        let output = &steps[2];
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
        let displays = |par: Par| drive(par).into_iter().map(|s| s.display).collect::<Vec<_>>();
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
        let term = RhoCalcLanguage.parse_term(COMM_SRC).expect("parse COMM term");
        let mut stepper =
            language.start_reduction_stepper(term.as_ref()).expect("wrapper starts a stepper");
        let mut count = 0usize;
        while stepper.next_step().expect("next_step").is_some() {
            count += 1;
        }
        assert!(count >= 1, "the wrapper's stepper must yield ≥1 COMM step; got {count}");
    }

    #[test]
    fn held_fold_lowering_emits_one_fold_contract_spec() {
        // The held fold `int(*(x),8)` lifts (1 fold-spec); the ground send-side `int(5,8)` folds in
        // place; the lifted call has the original send + receive.
        let term = RhoCalcLanguage
            .parse_term(r#"{ for(x <- @("c")){ int(*(x), 8) } | @("c")!(int(5,8)) }"#)
            .expect("parse");
        let (par, specs) = crate::rhocalc_ast::lower_rhocalc_term_with_folds(term.as_ref())
            .expect("the held fold lifts, so lowering succeeds");
        assert_eq!(specs.len(), 1, "one held fold ⇒ one fold-contract spec");
        assert_eq!(specs[0].kind, crate::fold_contract::FoldKind::Int);
        assert_eq!(specs[0].width, 8);
        assert_eq!(par.sends.len(), 1, "the original `@(\"c\")!(5)` send");
        assert_eq!(par.receives.len(), 1, "the original `@(\"c\")?x` receive");
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
    fn wrapper_rejects_pure_fold_term_for_stepping() {
        // A pure value/fold lowers to no COMM program ⇒ the wrapper fails to start a stepper, so
        // the REPL falls back to the Dovetail derivation graph (Layer 1).
        use crate::rhocalc_ast::dovetail_rho_backed_rhocalc;
        let language = dovetail_rho_backed_rhocalc("OUT").expect("build RhoCalc wrapper");
        let term = RhoCalcLanguage.parse_term("int(1+2, 8)").expect("parse fold term");
        assert!(
            language.start_reduction_stepper(term.as_ref()).is_err(),
            "a pure-fold term has no COMM program to single-step"
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
