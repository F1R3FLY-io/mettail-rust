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
use models::rhoapi::{BindPattern, ListParWithRandom, Par, TaggedContinuation};
use rho_pure_eval::Env;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::has_cost::HasCost;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rholang::rust::interpreter::pretty_printer::PrettyPrinter;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime};
use rholang::rust::interpreter::system_processes::Definition;
use rspace_plus_plus::rspace::logging::{StepCommObserver, StepGate};
use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;
use rspace_plus_plus::rspace::trace::event::COMM;

use mettail_runtime::{
    ReductionStepper, RuntimeCommEvent, RuntimeReductionEngine, RuntimeReductionStep,
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
}

/// The COMM observer the stepper installs on the `RSpace`. `observe_comm` clones the payload and
/// pushes it (non-blocking); `step_gate` hands the reducer the shared back-pressure gate so it
/// pauses after each committed COMM.
struct StepObserver {
    sender: Sender<RawCommEvent>,
    gate: Arc<StepGate>,
    ordinal: AtomicU64,
}

impl StepCommObserver<Par, BindPattern, ListParWithRandom, TaggedContinuation> for StepObserver {
    fn observe_comm(
        &self,
        channels: &[Par],
        consumed: &[ListParWithRandom],
        _patterns: &[BindPattern],
        _continuation: &TaggedContinuation,
        _comm: &COMM,
        label: &str,
    ) {
        let ordinal = self.ordinal.fetch_add(1, Ordering::Relaxed);
        let event = RawCommEvent {
            ordinal,
            label: label.to_string(),
            channels: channels.to_vec(),
            consumed: consumed.to_vec(),
        };
        // Non-blocking: never block under the tuplespace lock. The gate keeps us ≤1 COMM ahead of
        // the driver, so the bounded queue cannot fill in practice; if it ever did, dropping the
        // event is strictly safer than stalling the reducer.
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
    receiver: Receiver<RawCommEvent>,
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
    /// `None`.
    pub fn start(par: Par, fold_defs: Vec<Definition>) -> Result<StepSession, String> {
        let (sender, receiver) = bounded::<RawCommEvent>(STEP_QUEUE_CAP);
        let gate = Arc::new(StepGate::new());
        let observer = Arc::new(StepObserver { sender, gate: gate.clone(), ordinal: AtomicU64::new(0) });
        let worker = std::thread::Builder::new()
            .name("mettail-rho-stepper".to_string())
            .spawn(move || run_stepped_inj(par, observer, fold_defs))
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
            Ok(()) => Ok(()),
            Err(err) => {
                rho_runtime.revert_to_soft_checkpoint(checkpoint).await;
                Err(format!("inj: {err:?}"))
            },
        }
    })
}

/// Render a raw COMM event into a [`RuntimeReductionStep`] (rendering happens on a large stack).
fn render_step(raw: RawCommEvent) -> RuntimeReductionStep {
    let (channels, consumed) = render_payload(&raw.channels, &raw.consumed);
    let display = format_comm(&raw.label, &channels, &consumed);
    RuntimeReductionStep {
        ordinal: raw.ordinal,
        engine: RuntimeReductionEngine::RhoComm,
        display,
        comm: Some(RuntimeCommEvent { channels, consumed, label: raw.label }),
    }
}

/// Render the raw COMM `Par`s on a dedicated **large-stack** thread — f1r3node's `PrettyPrinter` is
/// recursive and not yet stack-safe, so deeply-nested payloads would overflow a normal stack.
/// Interim measure (see the module/`Cargo.toml` notes; a stack-safe printer is a separate PR).
fn render_payload(channels: &[Par], consumed: &[ListParWithRandom]) -> (Vec<String>, Vec<String>) {
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
                (rendered_channels, rendered_consumed)
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

/// One-line COMM rendering: `COMM[consume] <channels> ⇐ {<consumed data>}`.
fn format_comm(label: &str, channels: &[String], consumed: &[String]) -> String {
    let side = match label {
        "comm.consume" => "consume",
        "comm.produce" => "produce",
        other => other,
    };
    format!("COMM[{}] {} ⇐ {{{}}}", side, channels.join(", "), consumed.join(", "))
}

#[cfg(all(test, feature = "rhocalc-runtime"))]
mod tests {
    use super::*;
    use crate::rhocalc_ast::lower_rhocalc_term;
    use mettail_languages::rhocalc::RhoCalcLanguage;
    use mettail_runtime::Language;

    /// The flagship COMM term: a receive on `@"c"` and a matching send carrying the process
    /// `@"OUT"!("p")` — exactly one rendezvous fires.
    const COMM_SRC: &str = r#"{ (@("c")?x).{*(x)} | @("c")!(@("OUT")!("p")) }"#;

    fn lower(src: &str) -> Par {
        let term = RhoCalcLanguage.parse_term(src).expect("parse rhocalc term");
        lower_rhocalc_term(term.as_ref()).expect("lower rhocalc term to a Par")
    }

    fn drive(par: Par) -> Vec<RuntimeReductionStep> {
        let mut session = StepSession::start(par, Vec::new()).expect("start step session");
        let mut steps = Vec::new();
        while let Some(step) = session.next_step().expect("next_step must not error") {
            steps.push(step);
        }
        steps
    }

    #[test]
    fn comm_term_yields_ordered_comm_steps() {
        let steps = drive(lower(COMM_SRC));
        assert!(!steps.is_empty(), "a COMM term must yield at least one COMM step");
        for (index, step) in steps.iter().enumerate() {
            assert_eq!(step.ordinal, index as u64, "ordinals must be dense and monotone");
            assert_eq!(step.engine, RuntimeReductionEngine::RhoComm, "Rho COMM steps");
            assert!(step.comm.is_some(), "a Rho COMM step carries its event payload");
            assert!(step.display.starts_with("COMM["), "rendered as a COMM line: {}", step.display);
        }
    }

    #[test]
    fn lone_send_yields_no_comm_steps() {
        // A send with no matching receive never rendezvouses — the worker reaches quiescence with
        // zero COMMs, so the first `next_step` returns `None` (the REPL then falls back to the
        // Dovetail derivation graph).
        let steps = drive(lower(r#"{ @("c")!(@("OUT")!("p")) }"#));
        assert!(steps.is_empty(), "a lone send fires no COMM; got {} step(s)", steps.len());
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
            .parse_term(r#"{ (@("c")?x).{ int(*(x), 8) } | @("c")!(int(5,8)) }"#)
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
            .parse_term(r#"{ (@("c")?x).{ int(*(x), 8) } | @("c")!(int(5,8)) }"#)
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
        let mut session = StepSession::start(lower(COMM_SRC), Vec::new()).expect("start");
        let _first = session.next_step().expect("first step");
        drop(session); // must not hang or panic
    }
}
