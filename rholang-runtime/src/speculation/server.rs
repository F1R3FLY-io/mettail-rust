//! # The `[*]` / `[n]` REQUEST SERVER — the bolt between the surface and the engine
//!
//! [`crate::lookahead`] owns the **wire**: a lowered `x!(P)[*]` is the send
//! `@"^spec-all"!(⟦P⟧, x)`, and a request that nothing consumes is reported as a typed
//! [`UnservedRequest`](crate::lookahead::UnservedRequest). [`super::service`] owns the
//! **answer**: given a request's operands it runs a real branching exploration and hands
//! back the values each report channel carries. Neither of them makes a request *happen*.
//! This module does: it is a pair of **system-process `Definition`s**, installed on those two
//! reserved channels, that consume a request out of a **running program**, serve it, and
//! publish the results back into that same program.
//!
//! ## ★ Why a system process, and not a host-side driver
//!
//! The obvious alternative is a host-side fixpoint driver: run the program, notice a request
//! resting on `^spec-all`, serve it, inject the answers, run again. It is simpler, and it is
//! **semantically wrong**, because it stages the execution:
//!
//! ```text
//!   host driver                    system process
//!   ───────────                    ──────────────
//!   round 1: program runs          the request's COMM fires
//!            request rests         │
//!            for(…) blocks         ├─ handler runs the exploration
//!   ─────── program is done ──────┤
//!   round 2: answers injected      └─ handler PRODUCES onto x
//!            for(…) finally fires     for(…) matches, in the SAME reduction
//! ```
//!
//! In the staged reading the collecting `for` fires *a round later* than the request, so a
//! program cannot express "speculate and consume the result" as one concurrent process —
//! which is the only thing `x!(P)[*] | for(@r <- x){ … }` was ever asking for. The system
//! process is concurrent by construction: the request is an ordinary COMM against an
//! *installed* continuation, the handler `produce`s through f1r3node's own
//! [`ContractCall`] producer (which dispatches whatever continuation the produce matches),
//! and the waiting `for` is matched inside the same reduction. There is one round.
//!
//! Installed continuations are also **persistent** — `RSpace::install` writes
//! `installed_continuations`, which no COMM removes — so `n` independent `[*]` sends in one
//! program are each served, without the caller arranging anything.
//!
//! ## ★★ The field it is easiest to get wrong: `prelude`
//!
//! A reflected guest term is **inert**. `⟦(λx.x) (λa.λb.a)⟧` is an `EList` of `GPrivate`
//! tags: it contains no send, no receive, and nothing in it can reduce. It only computes
//! alongside two things the *caller* has and the request does not:
//!
//! 1. the guest's **installed program** — the σ-receivers, the `^drive` receiver family, the
//!    per-rule carrier receivers ([`SpeculationGuest::prelude`]); and
//! 2. a **seed** that hands the term to that program ([`SpeculationGuest::seed`]).
//!
//! Omit either and the exploration runs over an inert term, finds one leaf, and returns a
//! wrong-but-entirely-plausible answer — the subject itself, unreduced. So a guest is
//! *registered*, with both, and the server composes `prelude | seed(⟦P⟧)` — which is
//! byte-for-byte the program an ordinary run of that guest injects.
//!
//! ## Which guest? The subject says so
//!
//! The server does not guess and is not configured with a default. A reflected term carries
//! its language fingerprint in its own head tag (`mettail.term.{fingerprint}.{label}` — the
//! constructor-reflection ABI, read with the single shared inverse
//! [`parse_reflected_tag`](mettail_rholang_codegen::parse_reflected_tag)), so the **subject
//! selects the guest**:
//!
//! | subject | what the server injects | projection |
//! |---|---|---|
//! | a reflected term of a REGISTERED guest | `prelude \| seed(⟦P⟧)` | the data resting on [`SPEC_LEAF_CHANNEL`] |
//! | a reflected term of an UNREGISTERED language | nothing — a typed refusal on [`SPEC_ERR_CHANNEL`] | — |
//! | anything else (an ordinary process or value) | the subject itself | the reified terminal configuration |
//!
//! The middle row is the one that matters: speculating over a foreign term with no evaluator
//! installed is refused **loudly**, because the alternative is to explore an inert term and
//! deliver the subject back as though it were a normal form.
//!
//! ## ★ This is not the shortcut `x5` forbids
//!
//! `tests/x5_lookahead_lowering.rs::lookahead_does_not_lower_onto_the_single_path_drive`
//! asserts that the LOWERING emits no `^drive` seed, because a `[*]` that lowers onto the
//! host's single-path quiescence driver returns the right answer for every λ term (λ is
//! confluent) and is silently wrong on the first guest that has two.
//!
//! The seed this module builds is a different object in a different place. It is injected
//! into a **speculative sandbox**, where every COMM is enumerated by BFS over `E(S)`
//! ([`super::search`]) rather than scheduled by tokio: the guest's driver is the *evaluator*
//! being explored, not the answer being trusted. Where a guest's lowering presents a choice
//! to the tuplespace the search branches and every outcome is delivered
//! (`tests/s2_speculative_branching.rs`: `c!(1) | c!(2) | for(@x <- c){OUT!(x)}` yields two
//! leaves, `max_conflict_class == 2`); where it does not, one leaf is the honest answer and
//! `max_conflict_class == 1` says so in the machine's own words
//! (`tests/s2_ambient_open_race.rs`). The lowering stays clean: `x!(P)[*]` still emits
//! nothing but the request.
//!
//! ## What is published, and where
//!
//! One exploration, five channels, no information dropped:
//!
//! ```text
//!            @"^spec-all"!( ⟦P⟧ , x )
//!                     │  (a COMM against the installed continuation)
//!                     ▼
//!         ┌──────────────────────────────────┐
//!         │  LookaheadService::serve         │
//!         │  prelude | seed(⟦P⟧) ⟶ BFS E(S) │
//!         └──────────────────────────────────┘
//!                     │
//!   ┌─────────┬───────┴────┬───────────────┬──────────────────┬─────────────────┐
//!   ▼         ▼            ▼               ▼                  ▼                 ▼
//!   x     ^spec-success  ^spec-failure  ^spec-truncated   ^spec-delivery    ^spec-err
//!  bare   [trace, term]  [trace,        [trace, handle,   [success,        [code,
//!  term                   [code,msg]]    |E(S)|]           truncated,       message]
//!                                                          failure]
//! ```
//!
//! The bare term on `x` is what makes an ordinary FLT receive pattern match a speculative
//! result **verbatim**; the trace-keyed data on the companion channels are the provenance;
//! the FIPS's own three collections are on [`SPEC_DELIVERY_CHANNEL`] for a consumer that
//! wants one value rather than data on channels. See [`SPEC_DELIVERY_CHANNEL`] for why all
//! three readings are published rather than one being chosen.
//!
//! ### A guest branch that computed nothing is a FAILURE, not silence
//!
//! A branch whose guest driver hit an unrecognized head or ran out of per-path fuel reaches
//! tuplespace quiescence like any other: nothing raised, `E(S)` merely emptied. Its
//! projection is empty, so a server that only published `reply` would deliver **nothing at
//! all** for it and be indistinguishable from a branch that legitimately published nothing.
//! The server therefore reads the guest's own `^drive-err` / `^drive-fuel` channels out of
//! each leaf and republishes them as trace-keyed branch failures
//! ([`ErrorCode::GuestEvaluatorRefused`] / [`ErrorCode::GuestEvaluatorExhausted`]) — the
//! same fail-closed check the `rhocalc` interpreter makes before it reports a normal form,
//! made per-branch.
//!
//! ## Metering
//!
//! The handler funds its sandbox from the host deploy's remaining phlogiston and charges
//! back what it spent, one [`reserve_comm`](rholang::rust::interpreter::metering::MeteredMachine::reserve_comm)
//! call per committed COMM ([`charge_host_comms`]). `ProcessContext` carries no budget — no
//! f1r3node system process has ever needed one — so the host's [`RuntimeBudget`] is bound
//! into the engine by whoever builds the runtime, through [`LookaheadEngine::bind_host`],
//! **after** `create_rho_runtime` returns. Until it is bound the server refuses requests
//! typed rather than running an unfunded (and therefore silently empty) exploration: budgets
//! are F1r3node's, and a speculation that cannot name the budget it draws on must not run.

use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, OnceLock};

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use mettail_rholang_codegen::{
    drive_err_channel, drive_fuel_channel, parse_reflected_tag, rho_net_drive_call_par,
    rho_net_drive_float_call_par, LOOKAHEAD_BAND,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{ListParWithRandom, Par};
use models::rust::utils::{new_gint_par, new_gstring_par};
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;
use rholang::rust::interpreter::contract_call::ContractCall;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::system_processes::Definition;

use crate::lookahead::{
    spec_channel_par, SPEC_ALL_CHANNEL, SPEC_DELIVERY_CHANNEL, SPEC_ERR_CHANNEL,
    SPEC_FAILURE_CHANNEL, SPEC_LEAF_CHANNEL, SPEC_N_CHANNEL, SPEC_SUCCESS_CHANNEL,
    SPEC_TRUNCATED_CHANNEL,
};
use crate::native_contract::private_name_tag;
use crate::observation::render_par_text;

use super::delivery::{resting_on_string, trace_digest};
use super::search::{charge_host_comms, ErrorCode, Lookahead, QuiescentLeaf, TraceMode};
use super::service::{LeafProjection, LookaheadRequest, LookaheadResponse, LookaheadService};

/// The ABI version the two `body_ref`s are derived from. Bumping it re-derives both, which is
/// what a wire-incompatible change to the request shape should do.
pub const LOOKAHEAD_ABI_VERSION: &str = "mettail-lookahead-v1";

/// The lookahead band index of the unbounded request channel.
const SPEC_ALL_INDEX: u8 = 0;
/// The lookahead band index of the bounded request channel.
const SPEC_N_INDEX: u8 = 1;

/// The diagnostic weight each charged-back COMM rides into the host's event log with. The
/// *amount* charged is one COMM per call regardless (see [`charge_host_comms`]); this is the
/// label that makes speculation legible in a cost trace.
fn speculation_weight() -> Cost {
    Cost::create(1, "speculative COMM charged back to the host deploy")
}

// ══════════════════════════════════════════════════════════════════════════
// A registered guest
// ══════════════════════════════════════════════════════════════════════════

/// How a reflected term of ONE guest language is made to run inside a speculative sandbox.
///
/// Both halves are the caller's to supply because both are the caller's to know — see the
/// module header's `prelude` section.
#[derive(Clone)]
pub struct SpeculationGuest {
    fingerprint: String,
    prelude: Par,
    seed: Arc<dyn Fn(&str, Par, &str) -> Par + Send + Sync>,
    definitions: Option<Arc<dyn Fn() -> Vec<Definition> + Send + Sync>>,
}

impl SpeculationGuest {
    /// A guest whose reflected terms are seeded into its in-Rho quiescence driver with the
    /// ordinary `^drive` seed — `⌜^drive⌝!(⟦P⟧, fuel, @out)`.
    ///
    /// `prelude` is the guest's installed Rho-net program
    /// (`RhoDefaultBackendPlan::installed_rho_net_program_par`).
    pub fn driven(fingerprint: impl Into<String>, prelude: Par) -> Self {
        SpeculationGuest {
            fingerprint: fingerprint.into(),
            prelude,
            seed: Arc::new(|fingerprint, subject, out| {
                rho_net_drive_call_par(fingerprint, subject, out)
            }),
            definitions: None,
        }
    }

    /// A guest whose driver needs the A-S5.8 **float-routed** seed — the shape a
    /// float-bearing language's production run uses, which canonicalizes the raw subject
    /// through the installed `^float` dispatcher before the first `^drive` frame sees it.
    ///
    /// Selected by the caller (`language_is_float_bearing`), never guessed here: a guest
    /// served with the wrong seed reduces differently, and differently-but-plausibly is the
    /// failure mode this module is written to make impossible.
    pub fn float_driven(fingerprint: impl Into<String>, prelude: Par) -> Self {
        SpeculationGuest {
            fingerprint: fingerprint.into(),
            prelude,
            seed: Arc::new(|fingerprint, subject, out| {
                rho_net_drive_float_call_par(fingerprint, subject, out)
            }),
            definitions: None,
        }
    }

    /// A guest with an arbitrary seed builder `(fingerprint, subject, out_channel) -> Par`,
    /// for an evaluator that is neither of the two drive shapes.
    pub fn with_seed(
        fingerprint: impl Into<String>,
        prelude: Par,
        seed: Arc<dyn Fn(&str, Par, &str) -> Par + Send + Sync>,
    ) -> Self {
        SpeculationGuest {
            fingerprint: fingerprint.into(),
            prelude,
            seed,
            definitions: None,
        }
    }

    /// The guest's Tier-3 fold-contract / A-S3 native-handler system processes.
    ///
    /// A **factory**, not a `Vec`: `Definition` is not `Clone` (it carries a boxed handler),
    /// and every served request builds its own fresh sandbox, so each needs its own set.
    /// Speculation over a language's terms needs these for the same reason ordinary
    /// execution does — a native `fold` rule that cannot dispatch simply does not fire, and
    /// the branch quietly reaches a *different* normal form.
    pub fn with_definitions(
        mut self,
        definitions: Arc<dyn Fn() -> Vec<Definition> + Send + Sync>,
    ) -> Self {
        self.definitions = Some(definitions);
        self
    }

    /// The language fingerprint this guest's reflected terms carry.
    pub fn fingerprint(&self) -> &str {
        &self.fingerprint
    }

    /// The guest's installed Rho-net program.
    pub fn prelude(&self) -> &Par {
        &self.prelude
    }

    /// The seed that hands `subject` to this guest's evaluator, pointed at `out_channel`.
    pub fn seed(&self, subject: Par, out_channel: &str) -> Par {
        (self.seed)(&self.fingerprint, subject, out_channel)
    }

    fn definitions(&self) -> Vec<Definition> {
        match &self.definitions {
            Some(factory) => factory(),
            None => Vec::new(),
        }
    }
}

/// Hand-written because two fields are closures, which have no `Debug`. The fingerprint is
/// the guest's identity and is what a diagnostic needs; the other three are reported by
/// presence, which is exactly the question a reader of a failed lookup is asking ("was a
/// prelude registered at all?").
impl std::fmt::Debug for SpeculationGuest {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SpeculationGuest")
            .field("fingerprint", &self.fingerprint)
            .field("prelude_is_empty", &(self.prelude == Par::default()))
            .field("has_definitions", &self.definitions.is_some())
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════
// The engine
// ══════════════════════════════════════════════════════════════════════════

/// **The installable request server.** Hand [`definitions`](Self::definitions) to
/// `create_rho_runtime`'s `extra_system_processes` seam, then [`bind_host`](Self::bind_host)
/// the runtime's budget, and `[*]` / `[n]` are live in every program that runtime reduces.
///
/// Cheap to clone (everything inside is behind an `Arc`), which is what lets one engine be
/// captured by both `Definition` handlers and still share one host-budget binding.
#[derive(Clone)]
pub struct LookaheadEngine {
    guests: Arc<Vec<SpeculationGuest>>,
    trace_mode: TraceMode,
    /// The host deploy's budget, bound after `create_rho_runtime` returns. A `OnceLock`
    /// rather than a lock: it is written once, read from every handler invocation, and read
    /// on the reduction's hot path — so the read must not be able to block a reducer task.
    host: Arc<OnceLock<RuntimeBudget>>,
}

impl Default for LookaheadEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl LookaheadEngine {
    /// An engine with no registered guests: `[*]` over an ordinary process works, `[*]` over
    /// a reflected foreign term is refused typed.
    pub fn new() -> Self {
        LookaheadEngine {
            guests: Arc::new(Vec::new()),
            trace_mode: TraceMode::default(),
            host: Arc::new(OnceLock::new()),
        }
    }

    /// Register a guest language. The subject's own fingerprint selects it.
    pub fn with_guest(mut self, guest: SpeculationGuest) -> Self {
        Arc::make_mut(&mut self.guests).push(guest);
        self
    }

    /// The search mode every request is served under.
    ///
    /// [`TraceMode::IndependenceReduced`] (the default) is the only mode in which a guest
    /// whose driver fans out over many independent receivers is tractable at all: the λ
    /// drive of `plus 2 3` expands 404 nodes under it and prunes 513 redundant interleavings.
    pub fn with_trace_mode(mut self, trace_mode: TraceMode) -> Self {
        self.trace_mode = trace_mode;
        self
    }

    /// **Bind the host deploy's budget.** Call once, after `create_rho_runtime` returns, with
    /// `runtime.cost()`.
    ///
    /// The ordering is forced and is not an inconvenience to design around: the
    /// `Definition`s have to exist *before* the runtime that dispatches them, and the budget
    /// belongs to that runtime. `RuntimeBudget` is a handle over shared atomics, so a clone
    /// bound here observes every later `set` — including
    /// `run.rs::inj_on_runtime`'s — rather than a snapshot.
    ///
    /// Returns whether this call is the one that bound it; a second call changes nothing,
    /// because two different budgets behind one engine would mean two answers to *"whose
    /// tokens paid for this exploration?"*.
    pub fn bind_host(&self, budget: RuntimeBudget) -> bool {
        self.host.set(budget).is_ok()
    }

    /// Whether a host budget has been bound.
    pub fn host_bound(&self) -> bool {
        self.host.get().is_some()
    }

    /// **The two system-process `Definition`s** — `^spec-all` (arity 2) and `^spec-n`
    /// (arity 3).
    ///
    /// The `fixed_channel`s are the **quoted strings** the lowering sends on, not band
    /// channels: a `Definition` installs a continuation on exactly the channel named, and the
    /// surface emits `@"^spec-all"!(…)`. The `body_ref`s come from
    /// [`LOOKAHEAD_BAND`](mettail_rholang_codegen::LOOKAHEAD_BAND), so they are deterministic
    /// and provably disjoint from f1r3node's own and from the two MeTTaIL contract bands.
    pub fn definitions(&self) -> Vec<Definition> {
        vec![self.definition(false), self.definition(true)]
    }

    fn definition(&self, bounded: bool) -> Definition {
        let (channel, arity, index, urn) = match bounded {
            false => (SPEC_ALL_CHANNEL, 2, SPEC_ALL_INDEX, "mtl:spec:all"),
            true => (SPEC_N_CHANNEL, 3, SPEC_N_INDEX, "mtl:spec:n"),
        };
        let engine = self.clone();
        Definition {
            urn: urn.to_string(),
            fixed_channel: spec_channel_par(channel),
            arity,
            body_ref: LOOKAHEAD_BAND.body_ref(index, LOOKAHEAD_ABI_VERSION),
            remainder: None,
            handler: Box::new(move |context| {
                let space = context.space.clone();
                let dispatcher = context.dispatcher.clone();
                let engine = engine.clone();
                Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                    let call = ContractCall {
                        space: space.clone(),
                        dispatcher: dispatcher.clone(),
                    };
                    let engine = engine.clone();
                    Box::pin(async move { engine.serve(call, args, bounded).await })
                        as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
                })
            }),
        }
    }

    // ── serving one request ──────────────────────────────────────────────

    /// Consume one request, explore, publish. The whole of the server.
    async fn serve(
        &self,
        call: ContractCall,
        args: (Vec<ListParWithRandom>, bool, Vec<Par>),
        bounded: bool,
    ) -> Result<Vec<Par>, InterpreterError> {
        let urn = match bounded {
            false => SPEC_ALL_CHANNEL,
            true => SPEC_N_CHANNEL,
        };
        // The arriving datum's randomness IS the deploy's, split at the position the send
        // occupied — so every name a speculation mints is a function of the deploy and two
        // validators serving the same request mint the same ones. Read before `unapply`,
        // which consumes `args`.
        let seed_random = args
            .0
            .first()
            .map(|datum| datum.random_state.clone())
            .unwrap_or_default();
        let Some((_produce, is_replay, previous, payload)) = call.unapply(args) else {
            return Err(InterpreterError::IllegalArgumentError(format!(
                "{urn}: not a single-message contract call"
            )));
        };

        let mut publisher = Publisher {
            call: &call,
            random: Blake2b512Random::from_bytes(&seed_random),
            is_replay,
            previous,
            index: 0,
        };

        // ── the operands ─────────────────────────────────────────────────
        let (subject, lookahead, reply) = match parse_request(&payload, bounded) {
            Ok(operands) => operands,
            Err(message) => {
                // A malformed request is REPORTED, not silently dropped: the send committed,
                // so something is going to wait for an answer forever otherwise.
                publisher
                    .publish(
                        request_error_datum(ErrorCode::Interpreter, &message),
                        &spec(SPEC_ERR_CHANNEL),
                    )
                    .await?;
                return Err(InterpreterError::IllegalArgumentError(format!("{urn}: {message}")));
            },
        };

        // ── the budget ───────────────────────────────────────────────────
        let Some(host) = self.host.get() else {
            let message = format!(
                "{urn}: no host budget is bound to the lookahead engine, so this exploration \
                 cannot be funded or charged back. An unfunded sandbox evaluates nothing and \
                 would return an empty answer that is indistinguishable from a search that \
                 found none — refusing instead. Bind it with LookaheadEngine::bind_host."
            );
            publisher
                .publish(
                    request_error_datum(ErrorCode::Bootstrap, &message),
                    &spec(SPEC_ERR_CHANNEL),
                )
                .await?;
            return Err(InterpreterError::SetupError(message));
        };

        // ── which guest, if any ──────────────────────────────────────────
        let guest = match self.guest_for(&subject) {
            Ok(guest) => guest,
            Err(message) => {
                publisher
                    .publish(
                        request_error_datum(ErrorCode::Bootstrap, &message),
                        &spec(SPEC_ERR_CHANNEL),
                    )
                    .await?;
                return Ok(Vec::new());
            },
        };

        // ★ `prelude | seed(⟦P⟧)` for a registered guest; the bare subject otherwise. This
        // is the line the module header's `prelude` warning is about.
        let request = match guest {
            Some(guest) => LookaheadRequest::new(guest.seed(subject, SPEC_LEAF_CHANNEL), lookahead)
                .with_prelude(guest.prelude.clone())
                .with_projection(LeafProjection::resting_on(SPEC_LEAF_CHANNEL))
                .with_definitions(guest.definitions()),
            None => LookaheadRequest::new(subject, lookahead)
                .with_projection(LeafProjection::Configuration),
        }
        .with_trace_mode(self.trace_mode);

        // ── the exploration ──────────────────────────────────────────────
        let response = match LookaheadService::serve(request, publisher.random.clone(), host).await
        {
            Ok(response) => response,
            Err(error) => {
                let datum = request_error_datum(
                    ErrorCode::of(&error),
                    &format!("the exploration could not run: {error}"),
                );
                publisher.publish(datum, &spec(SPEC_ERR_CHANNEL)).await?;
                return Ok(Vec::new());
            },
        };

        // ── the charge-back, BEFORE anything is delivered ────────────────
        //
        // An exploration the deploy cannot afford must not also hand back an answer: the
        // failure is reported and the results are withheld, exactly as an over-budget
        // program produces no output.
        let consumed = response.consumed.clone();
        if let Err((charged, error)) =
            charge_host_comms(host, consumed.clone(), speculation_weight())
        {
            let datum = request_error_datum(
                ErrorCode::OutOfPhlogistons,
                &format!(
                    "the exploration committed {} COMM(s) the host could not pay for: \
                     {charged} charged before {error:?}",
                    consumed.value
                ),
            );
            publisher.publish(datum, &spec(SPEC_ERR_CHANNEL)).await?;
            return Err(InterpreterError::OutOfPhlogistonsError);
        }

        self.publish_response(&mut publisher, response, guest, &reply)
            .await
    }

    /// Publish one served response onto the five channels of the module header's diagram.
    async fn publish_response(
        &self,
        publisher: &mut Publisher<'_>,
        response: LookaheadResponse,
        guest: Option<&SpeculationGuest>,
        reply: &Par,
    ) -> Result<Vec<Par>, InterpreterError> {
        let LookaheadResponse {
            reply: terms,
            success,
            failure,
            truncated,
            error,
            delivery,
            exploration,
            ..
        } = response;

        // ★ The bare terminal term on the send's own channel — one datum per success branch,
        // so an ordinary FLT receive pattern matches it verbatim.
        let mut published = Vec::with_capacity(terms.len());
        for term in terms {
            publisher.publish(term.clone(), reply).await?;
            published.push(term);
        }

        // The trace-keyed per-branch provenance.
        for report in success.iter() {
            publisher
                .publish(report.datum.clone(), &spec(SPEC_SUCCESS_CHANNEL))
                .await?;
        }
        for datum in failure.iter() {
            publisher
                .publish(datum.clone(), &spec(SPEC_FAILURE_CHANNEL))
                .await?;
        }
        for datum in truncated.iter() {
            publisher
                .publish(datum.clone(), &spec(SPEC_TRUNCATED_CHANNEL))
                .await?;
        }

        // ★ A guest branch that reached quiescence WITHOUT computing anything: the driver
        // refused the head or ran out of fuel. Republished as a trace-keyed branch failure
        // rather than left as an empty projection nobody can see. See the module header.
        if let Some(guest) = guest {
            for leaf in exploration.success.iter() {
                for datum in guest_evaluator_failures(guest, leaf) {
                    publisher
                        .publish(datum, &spec(SPEC_FAILURE_CHANNEL))
                        .await?;
                }
            }
        }

        // A request-level refusal the service itself raised (a leaf it could not render).
        if let Some(datum) = error {
            publisher.publish(datum, &spec(SPEC_ERR_CHANNEL)).await?;
        }

        // ★ The FIPS's own three collections, as ONE datum.
        let [success_set, truncated_set, failure_set] = delivery.as_slice();
        let collections =
            ground_list(vec![success_set.clone(), truncated_set.clone(), failure_set.clone()]);
        publisher
            .publish(collections, &spec(SPEC_DELIVERY_CHANNEL))
            .await?;

        Ok(published)
    }

    /// The registered guest a subject belongs to.
    ///
    /// `Ok(None)` is *"this is not a reflected foreign term at all"* — an ordinary process,
    /// explored as itself. `Err` is *"this IS a foreign term and no evaluator is
    /// registered"*, which must never be silently explored as an inert value.
    fn guest_for(&self, subject: &Par) -> Result<Option<&SpeculationGuest>, String> {
        let Some(fingerprint) = reflected_fingerprint(subject) else {
            return Ok(None);
        };
        match self
            .guests
            .iter()
            .find(|guest| guest.fingerprint == fingerprint)
        {
            Some(guest) => Ok(Some(guest)),
            None => {
                let registered: Vec<&str> = self
                    .guests
                    .iter()
                    .map(|guest| guest.fingerprint.as_str())
                    .collect();
                Err(format!(
                    "the subject is a reflected term of language {fingerprint:?}, for which no \
                     evaluator is registered with the lookahead engine (registered: \
                     {registered:?}). A reflected term is INERT without its guest's installed \
                     program, so exploring it would find one leaf and hand back the subject \
                     itself as though it were a normal form. Refusing instead."
                ))
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Publishing
// ══════════════════════════════════════════════════════════════════════════

/// Produces the server's data back into the running program, one datum at a time, each with
/// its own randomness.
///
/// Every publication goes through f1r3node's own [`ContractCall`] producer, which is what
/// makes the delivery **concurrent**: `produce` matches whatever continuation is waiting and
/// dispatches it inside this reduction, so the collecting `for` fires in the same round the
/// request did.
///
/// [`ContractCall::unapply`]'s producer is `FnOnce`, so one is built per datum. That is not a
/// workaround: it is the seam at which each datum gets its own `Blake2b512Random`, split from
/// the request's at the datum's position — exactly as `Reduce::eval_par` splits a parallel
/// composition's, and with the same `i16` position type.
struct Publisher<'call> {
    call: &'call ContractCall,
    random: Blake2b512Random,
    is_replay: bool,
    previous: Vec<Par>,
    index: i16,
}

impl Publisher<'_> {
    async fn publish(&mut self, datum: Par, channel: &Par) -> Result<(), InterpreterError> {
        // `Blake2b512Random::split_short` takes an `i16`, which is also the width
        // `Reduce::eval_par` splits a parallel composition at. Exhausting it would mean one
        // request delivered 32 768 data; refusing is honest, silently reusing a split would
        // mint two names that must differ.
        if self.index == i16::MAX {
            return Err(InterpreterError::IllegalArgumentError(
                "a lookahead response exceeded 32767 published data, which is the width of \
                 the randomness split f1r3node uses for a parallel composition"
                    .to_string(),
            ));
        }
        let random = self.random.split_short(self.index);
        self.index += 1;
        let Some((produce, _, _, _)) = self.call.unapply((
            vec![ListParWithRandom {
                pars: Vec::new(),
                random_state: random.to_bytes(),
            }],
            self.is_replay,
            self.previous.clone(),
        )) else {
            return Err(InterpreterError::IllegalArgumentError(
                "the lookahead publisher could not build a producer".to_string(),
            ));
        };
        produce(&[datum], channel).await?;
        Ok(())
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Request parsing and wire shapes
// ══════════════════════════════════════════════════════════════════════════

/// `(subject, lookahead, replyChannel)` from a request's payload.
///
/// ★ Every operand here is **program-controlled**, and the refusals are consensus-visible. The
/// surface's `lookahead_bound` (`rhocalc_ast`) restricts `[n]` to a ground non-negative literal,
/// but `^spec-n` is an ordinary Rholang channel served by an installed system process: a program
/// can write `@"^spec-n"!(P, <any Par at all>, x)` and reach this function directly. So the
/// malformed-bound arm renders its operand through [`render_par_text`] — bounded and
/// derive-independent — for the reason spelled out on [`guest_evaluator_failures`], with the
/// aggravation that here the input is attacker-chosen rather than merely large.
fn parse_request(payload: &[Par], bounded: bool) -> Result<(Par, Lookahead, Par), String> {
    match bounded {
        false => match payload {
            [subject, reply] => Ok((subject.clone(), Lookahead::Unbounded, reply.clone())),
            _ => Err(format!("expected (subject, replyChannel), got arity {}", payload.len())),
        },
        true => match payload {
            [subject, bound, reply] => {
                let bound = ground_int(bound).ok_or_else(|| {
                    format!(
                        "the `[n]` bound must be a ground integer, got {}",
                        render_par_text(bound)
                    )
                })?;
                let bound = u64::try_from(bound)
                    .map_err(|_| format!("the `[n]` bound must be non-negative, got {bound}"))?;
                Ok((subject.clone(), Lookahead::Steps(bound), reply.clone()))
            },
            _ => {
                Err(format!("expected (subject, bound, replyChannel), got arity {}", payload.len()))
            },
        },
    }
}

/// The `i64` a ground-integer `Par` carries.
fn ground_int(par: &Par) -> Option<i64> {
    match par.exprs.as_slice() {
        [expr] => match expr.expr_instance.as_ref() {
            Some(ExprInstance::GInt(value)) => Some(*value),
            _ => None,
        },
        _ => None,
    }
}

/// The language fingerprint of a reflected constructor term, or `None` if `subject` is not
/// one.
///
/// Reads the constructor-reflection ABI head — `EList[GPrivate("mettail.term.{fp}.{label}"),
/// …]` — with the tree's single shared tag inverse, so it can never disagree with
/// [`crate::native_contract::par_to_ground_term`] about what a reflected term is.
fn reflected_fingerprint(subject: &Par) -> Option<String> {
    let [expr] = subject.exprs.as_slice() else {
        return None;
    };
    let Some(ExprInstance::EListBody(list)) = expr.expr_instance.as_ref() else {
        return None;
    };
    let (head, _) = list.ps.split_first()?;
    let tag = private_name_tag(head)?;
    let (fingerprint, _) = parse_reflected_tag(&tag)?;
    Some(fingerprint.to_string())
}

/// A quoted-string channel `@"name"`.
fn spec(name: &str) -> Par {
    spec_channel_par(name)
}

/// A ground `EList`.
fn ground_list(elements: Vec<Par>) -> Par {
    models::rust::utils::new_elist_par(
        elements,
        Vec::new(),
        false,
        None::<models::rhoapi::Var>,
        Vec::new(),
        false,
    )
}

/// `[code, message]` — a REQUEST-level refusal, the same shape
/// [`super::service`] uses. The request was not served, as opposed to a path that died.
fn request_error_datum(code: ErrorCode, message: &str) -> Par {
    ground_list(vec![
        new_gint_par(code.as_i64(), Vec::new(), false),
        new_gstring_par(message.to_string(), Vec::new(), false),
    ])
}

/// `[trace, [code, message]]` per guest-evaluator diagnostic resting in `leaf`'s terminal
/// configuration — the FIPS failure shape, so a consumer reads a guest refusal and a reducer
/// abort with one rule.
///
/// ★ The stuck redex goes through [`render_par_text`], **never** `format!("{par:?}")`. Two
/// reasons, and the second is the load-bearing one:
///
/// 1. prost's derived `Debug` for the reflected Ω redex is 14 KB of nested-struct noise; the
///    same fact in the neutral notation is 30 characters.
/// 2. This string is published by [`Publisher::publish`], which calls `produce` into the
///    **live** deploy's RSpace — so it is part of the post-deploy state and therefore of the
///    checkpoint root. A derived `Debug` is generated code: a `prost` bump that re-spells it
///    silently changes those bytes, and a node built against the new derive can no longer
///    replay a block produced by the old one. That is precisely the hazard
///    [`ErrorCode`](super::search::ErrorCode) writes its discriminants out longhand to
///    prevent, and the `message` beside the code had no such protection.
fn guest_evaluator_failures(guest: &SpeculationGuest, leaf: &QuiescentLeaf) -> Vec<Par> {
    let err = drive_err_channel(&guest.fingerprint);
    let fuel = drive_fuel_channel(&guest.fingerprint);
    let refused = resting_on_string(&leaf.state, &err);
    let exhausted = resting_on_string(&leaf.state, &fuel);
    let mut data = Vec::with_capacity(refused.len() + exhausted.len());
    for (code, channel, resting) in [
        (ErrorCode::GuestEvaluatorRefused, err.as_str(), refused),
        (ErrorCode::GuestEvaluatorExhausted, fuel.as_str(), exhausted),
    ] {
        for stuck in resting {
            data.push(ground_list(vec![
                trace_list(leaf),
                ground_list(vec![
                    new_gint_par(code.as_i64(), Vec::new(), false),
                    new_gstring_par(
                        format!(
                            "the guest evaluator rested on {channel}: the stuck redex is {}",
                            render_par_text(&stuck),
                        ),
                        Vec::new(),
                        false,
                    ),
                ]),
            ]));
        }
    }
    data
}

/// A branch's trace as the single-element handle list a guest-evaluator failure is keyed by.
///
/// The handle is [`trace_digest`] — the same name a truncated branch publishes and the same
/// one [`LookaheadService::resume`] takes back — so a guest failure and a resumable branch
/// are keyed alike.
fn trace_list(leaf: &QuiescentLeaf) -> Par {
    models::rust::utils::new_gbytearray_par(trace_digest(&leaf.trace).bytes(), Vec::new(), false)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The two `body_ref`s are distinct, positive, inside the lookahead band, and outside
    /// f1r3node's own ranges — so installing both cannot shadow either, nor anything of
    /// f1r3node's.
    #[test]
    fn the_two_request_definitions_occupy_distinct_reserved_body_refs() {
        let all = LOOKAHEAD_BAND.body_ref(SPEC_ALL_INDEX, LOOKAHEAD_ABI_VERSION);
        let bounded = LOOKAHEAD_BAND.body_ref(SPEC_N_INDEX, LOOKAHEAD_ABI_VERSION);
        assert_ne!(all, bounded, "the two request channels need distinct body_refs");
        let band = LOOKAHEAD_BAND.body_ref_range();
        assert!(band.contains(&all) && band.contains(&bounded));
        assert!(*band.start() > 108, "above f1r3node's std and test-framework body_refs");
    }

    /// The `Definition`s install on the QUOTED-STRING channels the lowering sends on, with
    /// the arities the two request shapes carry.
    #[test]
    fn the_definitions_install_on_the_wire_channels() {
        let engine = LookaheadEngine::new();
        let definitions = engine.definitions();
        assert_eq!(definitions.len(), 2);
        assert_eq!(definitions[0].fixed_channel, spec_channel_par(SPEC_ALL_CHANNEL));
        assert_eq!(definitions[0].arity, 2, "(subject, replyChannel)");
        assert_eq!(definitions[1].fixed_channel, spec_channel_par(SPEC_N_CHANNEL));
        assert_eq!(definitions[1].arity, 3, "(subject, bound, replyChannel)");
    }

    /// A request's operands are read positionally, and a malformed one is a typed refusal
    /// rather than a guess.
    #[test]
    fn request_operands_are_read_or_refused() {
        let subject = spec_channel_par("subject");
        let reply = spec_channel_par("results");
        let (read_subject, lookahead, read_reply) =
            parse_request(&[subject.clone(), reply.clone()], false).expect("the `[*]` shape");
        assert_eq!(read_subject, subject);
        assert_eq!(read_reply, reply);
        assert_eq!(lookahead, Lookahead::Unbounded);

        let bound = new_gint_par(7, Vec::new(), false);
        let (_, lookahead, _) =
            parse_request(&[subject.clone(), bound, reply.clone()], true).expect("the `[n]` shape");
        assert_eq!(lookahead, Lookahead::Steps(7));

        assert!(parse_request(&[subject.clone()], false).is_err(), "arity 1 is not a request");
        assert!(
            parse_request(&[subject.clone(), reply.clone(), reply.clone()], true).is_err(),
            "a non-integer bound must be refused, never coerced"
        );
        let negative = new_gint_par(-1, Vec::new(), false);
        assert!(
            parse_request(&[subject, negative, reply], true).is_err(),
            "a negative bound must be refused"
        );
    }

    /// ★ A refused `[n]` bound is named **legibly and boundedly**, because the refusal becomes
    /// a datum.
    ///
    /// `parse_request`'s `Err` is wrapped by `request_error_datum` and published on
    /// `^spec-err` — i.e. it is `produce`d into the live tuplespace, so it is part of the
    /// post-deploy state. This message used to be `format!("{bound:?}")`, prost's derived
    /// `Debug`: unbounded, and derive-version-dependent, which is a replay hazard in exactly
    /// the way [`ErrorCode`](super::search::ErrorCode) writes its discriminants out longhand
    /// to avoid.
    ///
    /// ## On reachability — measured, and narrower than first claimed
    ///
    /// I originally asserted that "any program can write `@\"^spec-n\"!(P, ⟨anything⟩, x)`".
    /// That is **not** true of RhoCalc source: `@c!(a, b, c)` lowers to a send of a single
    /// **list** payload (`⟦[a, b, c]⟧`), not to a polyadic send, so it arrives at arity 1 and
    /// the arity-3 `^spec-n` `Definition` never matches it. An end-to-end cell written that
    /// way does not exercise this path at all.
    ///
    /// The path is real all the same, and this is the level at which it is testable: `^spec-n`
    /// is an ordinary channel in the shared tuplespace served by an installed system process,
    /// and Rholang — f1r3node's own surface, which *does* have polyadic sends — can reach it.
    /// So the contract belongs to `parse_request`, and it is asserted here rather than through
    /// a surface that cannot express the shape.
    #[test]
    fn a_refused_bound_is_rendered_not_dumped() {
        let subject = spec_channel_par("subject");
        let reply = spec_channel_par("results");
        // A bound that is a whole reflected term rather than an integer — the shape an
        // adversary would choose, being both non-integer and arbitrarily large.
        let bound = ground_list(vec![
            spec_channel_par("not-an-integer"),
            new_gint_par(1, Vec::new(), false),
        ]);

        let message = parse_request(&[subject, bound, reply], true)
            .expect_err("a list is not a ground integer");

        assert!(
            message.contains("ground integer"),
            "the refusal must say what was wrong: {message}"
        );
        assert!(
            message.contains('⟦') || message.contains('⟨'),
            "the refusal must RENDER the offending operand rather than omit it: {message}"
        );
        assert!(
            message.chars().count() < 256,
            "an attacker-chosen operand must not become an unbounded consensus-visible \
             string; got {} chars",
            message.chars().count()
        );
        for marker in ["expr_instance", "EListBody", "unforgeables", "connective_used"] {
            assert!(
                !message.contains(marker),
                "★ {marker:?} means the operand was dumped through prost `Debug`: {message}"
            );
        }
    }

    /// A plain value is not a reflected foreign term, so it is explored as itself.
    #[test]
    fn a_plain_value_selects_no_guest() {
        let engine = LookaheadEngine::new();
        assert!(reflected_fingerprint(&new_gint_par(1, Vec::new(), false)).is_none());
        assert!(engine
            .guest_for(&new_gint_par(1, Vec::new(), false))
            .expect("a plain value is not a refusal")
            .is_none());
    }

    /// ★ A reflected term of an UNREGISTERED language is refused, never explored inert.
    #[test]
    fn an_unregistered_foreign_subject_is_refused() {
        let term = mettail_rholang_codegen::reflect_ground_term_par(
            &mettail_rholang_codegen::GroundTerm::nullary("PZero"),
            "mettail-langdef-v1:unregistered",
        );
        assert_eq!(
            reflected_fingerprint(&term).as_deref(),
            Some("mettail-langdef-v1:unregistered"),
            "the subject carries its own language fingerprint"
        );
        let error = LookaheadEngine::new()
            .guest_for(&term)
            .expect_err("no evaluator is registered, so this must be a refusal");
        assert!(error.contains("unregistered"), "{error}");

        // …and registering the guest resolves it.
        let engine = LookaheadEngine::new().with_guest(SpeculationGuest::driven(
            "mettail-langdef-v1:unregistered",
            Par::default(),
        ));
        assert!(engine
            .guest_for(&term)
            .expect("the registered guest resolves")
            .is_some());
    }

    /// An engine with no bound host budget has not been made live; the handler's refusal
    /// path depends on this being observable.
    #[test]
    fn an_unbound_engine_says_so() {
        let engine = LookaheadEngine::new();
        assert!(!engine.host_bound());
        let budget =
            rholang::rust::interpreter::accounting::cost_accounting::CostAccounting::empty_cost();
        assert!(engine.bind_host(budget.clone()), "the first binding takes");
        assert!(engine.host_bound());
        assert!(!engine.bind_host(budget), "a second binding is refused, not silently swapped");
    }
}
