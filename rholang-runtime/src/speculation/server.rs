//! # The `[*]` / `[n]` REQUEST SERVER — the bolt between the surface and the engine
//!
//! [`crate::lookahead`] owns the **wire**: a lowered `x!(P)[*]` is the send
//! `@"^spec-all"!(⟦P⟧, x)`, and a request that nothing consumes is reported as a typed
//! [`UnservedRequest`](crate::lookahead::UnservedRequest). [`super::service`] owns the
//! **answer**: given a request's operands it runs a real branching exploration and hands
//! back the values each report channel carries. Neither of them makes a request *happen*.
//! This module does: it installs four **system-process `Definition`s**, two v1
//! and two v2, which consume requests out of a running program and publish
//! results back into that same program.
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
//! The v1 channels retain their original bare-result replies and companion
//! reports. A v2 request uses the same exploration and delivers one atomic
//! `(successPathMap, failurePathMap)` datum on `x`. An internal
//! `^spec-truncated-v2` report carries `[2, truncatedPathMap]`; it does not
//! change the approved two-payload reply. The existing companion reports and
//! aggregate delivery remain available for both request versions.
//!
//! The v1 publication path is:
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
//! the aggregate three collections are on [`SPEC_DELIVERY_CHANNEL`] for an
//! existing consumer that wants one value rather than data on channels.
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
//! same fail-closed check the `rholang` interpreter makes before it reports a normal form,
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
use mettail_dovetail_runtime::{SemanticInputLimits, SemanticTransitionInput};
use mettail_grammar_core::{
    CategoryId, InstalledLanguage, InstalledLanguageHandle, InstalledLanguageTable, LanguageRight,
    TheorySortId,
};
use mettail_rholang_codegen::{
    drive_err_channel, drive_fuel_channel, encode_dynamic_native_label, parse_reflected_tag,
    rho_net_drive_call_par, rho_net_drive_float_call_par, DynamicNativeRef, ReflectedCodecBudget,
    ReflectedPositionalContext, LOOKAHEAD_BAND,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{ListParWithRandom, Par};
use models::rust::utils::{new_gint_par, new_gstring_par};
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;
use rholang::rust::interpreter::contract_call::ContractCall;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::metering::MeteredMachine;
use rholang::rust::interpreter::system_processes::Definition;
use rspace_plus_plus::rspace::errors::RSpaceError;
use rspace_plus_plus::rspace::rspace_interface::ProduceCommitGuard;

use crate::installed_flt::InstalledFltAdapter;
use crate::language_install::{
    exact_expr, exact_list, exact_string, grammar_fingerprint_label, RholangLanguageRuntime,
};
use crate::lookahead::{
    spec_channel_par, SPEC_ALL_CHANNEL, SPEC_ALL_V2_CHANNEL, SPEC_ALL_V3_CHANNEL,
    SPEC_DELIVERY_CHANNEL, SPEC_ERR_CHANNEL, SPEC_FAILURE_CHANNEL, SPEC_LEAF_CHANNEL,
    SPEC_N_CHANNEL, SPEC_N_V2_CHANNEL, SPEC_N_V3_CHANNEL, SPEC_SUCCESS_CHANNEL,
    SPEC_TRUNCATED_CHANNEL, SPEC_TRUNCATED_V2_CHANNEL,
};
use crate::native_contract::private_name_tag;
use crate::observation::render_par_text;
use crate::semantic_service::SemanticServiceLimits;

use super::delivery::{resting_on_string, trace_digest};
use super::occurrences::{
    scan_installed_occurrences, scan_top_level_reflected_exprs, split_preflighted_top_level_expr,
    term_at_path, SubjectOccurrence, TopLevelExprOccurrence,
};
use super::search::{ErrorCode, Lookahead, QuiescentLeaf, TraceMode};
use super::service::{LeafProjection, LookaheadRequest, LookaheadResponse, LookaheadService};

/// The ABI version the two `body_ref`s are derived from. Bumping it re-derives both, which is
/// what a wire-incompatible change to the request shape should do.
pub const LOOKAHEAD_ABI_VERSION: &str = "mettail-lookahead-v1";
/// V2 handlers use new channels and body refs; v1 registrations stay exact.
pub const LOOKAHEAD_ABI_VERSION_V2: &str = "mettail-lookahead-v2";
pub const LOOKAHEAD_ABI_VERSION_V3: &str = "mettail-lookahead-v3";

/// The lookahead band index of the unbounded request channel.
const SPEC_ALL_INDEX: u8 = 0;
/// The lookahead band index of the bounded request channel.
const SPEC_N_INDEX: u8 = 1;
const SPEC_ALL_V2_INDEX: u8 = 2;
const SPEC_N_V2_INDEX: u8 = 3;
const SPEC_ALL_V3_INDEX: u8 = 4;
const SPEC_N_V3_INDEX: u8 = 5;

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
    installed_runtime: Option<Arc<RholangLanguageRuntime>>,
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
            installed_runtime: None,
            trace_mode: TraceMode::default(),
            host: Arc::new(OnceLock::new()),
        }
    }

    /// Register a guest language. The subject's own fingerprint selects it.
    pub fn with_guest(mut self, guest: SpeculationGuest) -> Self {
        Arc::make_mut(&mut self.guests).push(guest);
        self
    }

    /// Bind the authority directory used to admit versioned installed FLT
    /// requests. Each request still resolves and rechecks its opaque selector.
    pub fn with_language_runtime(mut self, runtime: Arc<RholangLanguageRuntime>) -> Self {
        self.installed_runtime = Some(runtime);
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

    /// Admit the request's installed owner claims before constructing a
    /// sandbox. The structural scanner supplies the complete tagged occurrence
    /// roster; explicit scalar claims are resolved by the same path numbering.
    fn admit_subject(
        &self,
        wire_subject: Par,
        host: &RuntimeBudget,
        versioned: bool,
    ) -> Result<(Par, Vec<AdmittedLookaheadBinding>), String> {
        if !versioned {
            if !self.scan_and_charge(&wire_subject, host)?.is_empty() {
                return Err("legacy lookahead request cannot authorize an installed FLT".into());
            }
            return Ok((wire_subject, Vec::new()));
        }
        let admitted = {
            let (subject, bindings) = self
                .parse_envelope_and_charge(&wire_subject, host)?
                .ok_or_else(|| "v2 request requires [2, subject, owner-bindings]".to_string())?;
            let occurrences = self.scan_and_charge(subject, host)?;
            if bindings
                .windows(2)
                .any(|pair| pair[1].path.starts_with(&pair[0].path))
            {
                return Err("v2 owner binding paths may not overlap".into());
            }
            for occurrence in &occurrences {
                if bindings
                    .binary_search_by(|binding| binding.path.cmp(&occurrence.path))
                    .is_err()
                {
                    return Err(
                        "v2 owner bindings do not cover the exact installed occurrence roster"
                            .into(),
                    );
                }
            }
            if bindings.is_empty() {
                Vec::new()
            } else {
                let runtime = self
                    .installed_runtime
                    .as_ref()
                    .ok_or_else(|| "v2 installed language runtime is not bound".to_string())?;
                let mut admitted = Vec::new();
                admitted
                    .try_reserve(bindings.len())
                    .map_err(|_| "v2 admitted binding roster allocation failed".to_string())?;
                for binding in &bindings {
                    let term = self.term_at_path_and_charge(subject, &binding.path, host)?;
                    admitted.push(self.admit_binding(binding, term, runtime, host)?);
                }
                admitted
            }
        };
        // The exact envelope has already been parsed and charged. Move its
        // subject out after all borrowed claims expire; cloning it here would
        // duplicate arbitrary caller-controlled structure without metering.
        let subject = take_envelope_subject(wire_subject)
            .ok_or_else(|| "validated v2 envelope lost its subject".to_string())?;
        Ok((subject, admitted))
    }

    fn admit_top_level_subject(
        &self,
        wire_subject: Par,
        host: &RuntimeBudget,
    ) -> Result<(Par, Vec<AdmittedLookaheadBinding>), String> {
        let (subject, claim) = self
            .parse_envelope_v3_and_charge(&wire_subject, host)?
            .ok_or_else(|| "v3 request requires [3, subject, owner-bindings]".to_string())?;
        if claim.context != 0 {
            return Err("v3 top-level guest must be closed".into());
        }
        let occurrences = self.scan_top_level_and_charge(subject, host)?;
        let [occurrence] = occurrences.as_slice() else {
            return Err(
                "v3 requires exactly one top-level reflected expression and no nested guest".into(),
            );
        };
        if occurrence.index != claim.expr_index {
            return Err("v3 owner locator does not name the exact installed occurrence".into());
        }
        let runtime = self
            .installed_runtime
            .as_ref()
            .ok_or_else(|| "v3 installed language runtime is not bound".to_string())?;
        // The preceding complete, bounded preflight funds the shared
        // iterative split and its single exact guest expression.
        let (_, guest) = split_preflighted_top_level_expr(subject, occurrence.index)
            .ok_or_else(|| "v3 owner locator disappeared after preflight".to_string())?;
        let borrowed_claim = WireOwnerBinding {
            path: Vec::new(),
            token: claim.token,
            category: claim.category,
            context: claim.context,
        };
        let mut admitted = self.admit_binding(&borrowed_claim, &guest, runtime, host)?;
        if grammar_fingerprint_label(admitted.installed.commitment().language_fingerprint)
            != occurrence.fingerprint
        {
            return Err("v3 occurrence fingerprint differs from admitted owner".into());
        }
        admitted.top_level_expr = Some(occurrence.index);
        let subject = take_envelope_subject(wire_subject)
            .ok_or_else(|| "validated v3 envelope lost its subject".to_string())?;
        Ok((subject, vec![admitted]))
    }

    fn admit_binding(
        &self,
        binding: &WireOwnerBinding<'_>,
        subject: &Par,
        runtime: &RholangLanguageRuntime,
        host: &RuntimeBudget,
    ) -> Result<AdmittedLookaheadBinding, String> {
        if binding.context != 0 {
            return Err("v2 nonzero guest context is not supported by closed-term admission".into());
        }
        let handle = runtime
            .resolve(binding.token, LanguageRight::Reduce)
            .map_err(|_| "v2 installed owner selector is not authorized for Reduce".to_string())?;
        let installed = runtime
            .service()
            .table()
            .authorize(&handle, LanguageRight::Reduce)
            .map_err(|_| "v2 installed owner is no longer live".to_string())?;
        let fingerprint = grammar_fingerprint_label(installed.commitment().language_fingerprint);
        // Native admission is intentionally limited to the three codec forms
        // below. BigInt, BigRat, and Fixed need their own exact bounded codec
        // paths before they can be accepted as untagged v2 roots.
        if let Some(actual) = reflected_fingerprint(subject) {
            if actual != fingerprint {
                return Err("v2 subject does not have the bound installed owner".into());
            }
        } else if !matches!(
            exact_expr(subject),
            Some(ExprInstance::GString(_) | ExprInstance::GInt(_) | ExprInstance::GBool(_))
        ) {
            return Err(
                "v2 root is neither a reflected FLT nor a supported text/int64/bool literal".into(),
            );
        }
        let limits = installed.language_core().theory.limits;
        let policy = runtime.service().policy().semantic_service;
        let available = host.remaining().value.max(0) as u64;
        let work_limit = u64::from(limits.max_steps)
            .min(policy.execution.work)
            .min(available);
        if work_limit == 0 {
            return Err("v2 installed admission has no funded host work".into());
        }
        let byte_limit = (limits.max_output_bytes as usize)
            .min(policy.execution.term_bytes)
            .min(policy.boundary_payload_bytes);
        let mut used = 0;
        let mut cancelled = || false;
        let mut budget =
            ReflectedCodecBudget::new(&mut used, work_limit, byte_limit, &mut cancelled);
        let checked = (|| {
            let native = match exact_expr(subject) {
                Some(ExprInstance::GString(value)) => Some(DynamicNativeRef::Text(value)),
                Some(ExprInstance::GInt(value)) => {
                    Some(DynamicNativeRef::Integer(i128::from(*value)))
                },
                Some(ExprInstance::GBool(value)) => Some(DynamicNativeRef::Boolean(*value)),
                _ => None,
            };
            let reflected_native = if let Some(native) = native {
                let context = ReflectedPositionalContext::new(&fingerprint, &mut budget)
                    .map_err(|_| "v2 native owner context could not be prepared".to_string())?;
                let label = encode_dynamic_native_label(native, &mut budget)
                    .map_err(|_| "v2 native literal could not be reflected".to_string())?;
                Some(
                    context
                        .assemble(&label, Vec::new(), &mut budget)
                        .map_err(|_| "v2 native literal could not be reflected".to_string())?
                        .0,
                )
            } else {
                None
            };
            let adapter = InstalledFltAdapter::new(&installed, &mut budget)
                .map_err(|_| "v2 installed image could not be prepared".to_string())?;
            let (category, sort) = adapter
                .select_category(binding.category, &mut budget)
                .map_err(|_| "v2 expected category is not bound by the owner".to_string())?;
            let input = adapter
                .to_kernel(
                    reflected_native.as_ref().unwrap_or(subject),
                    category,
                    SemanticInputLimits {
                        work: work_limit,
                        nodes: (limits.max_term_nodes as usize).min(policy.execution.term_nodes),
                        bytes: byte_limit,
                    },
                    &mut budget,
                )
                .map_err(|_| {
                    "v2 subject is not a canonical term of the declared sort".to_string()
                })?;
            Ok::<_, String>((category, sort, input))
        })();
        let spent = budget.work_used();
        drop(budget);
        if spent > 0 {
            MeteredMachine::new(host.clone())
                .reserve_primitive(Cost::create(
                    i64::try_from(spent).unwrap_or(i64::MAX),
                    "installed lookahead request admission",
                ))
                .map_err(|_| "v2 installed admission exhausted host phlogiston".to_string())?;
        }
        let (category, sort, input) = checked?;
        let admitted = AdmittedLookaheadBinding {
            path: binding.path.clone(),
            top_level_expr: None,
            handle,
            installed,
            sort,
            category,
            context: binding.context,
            input,
        };
        Ok(admitted)
    }

    fn term_at_path_and_charge<'a>(
        &self,
        subject: &'a Par,
        path: &[u32],
        host: &RuntimeBudget,
    ) -> Result<&'a Par, String> {
        let policy = self
            .installed_runtime
            .as_ref()
            .map(|runtime| runtime.service().policy().semantic_service)
            .unwrap_or_else(SemanticServiceLimits::default);
        let work_limit = policy
            .execution
            .work
            .min(host.remaining().value.max(0) as u64);
        if work_limit == 0 {
            return Err("v2 owner path lookup has no funded host work".into());
        }
        let mut used = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(
            &mut used,
            work_limit,
            policy.boundary_payload_bytes,
            &mut cancelled,
        );
        let located = term_at_path(subject, path, &mut budget);
        let spent = budget.work_used();
        drop(budget);
        if spent > 0 {
            MeteredMachine::new(host.clone())
                .reserve_primitive(Cost::create(
                    i64::try_from(spent).unwrap_or(i64::MAX),
                    "lookahead owner path lookup",
                ))
                .map_err(|_| "v2 owner path lookup exhausted host phlogiston".to_string())?;
        }
        located
            .map_err(|error| error.to_string())?
            .ok_or_else(|| "v2 owner binding path does not exist in subject".to_string())
    }

    fn scan_and_charge<'a>(
        &self,
        subject: &'a Par,
        host: &RuntimeBudget,
    ) -> Result<Vec<SubjectOccurrence<'a>>, String> {
        let policy = self
            .installed_runtime
            .as_ref()
            .map(|runtime| runtime.service().policy().semantic_service)
            .unwrap_or_else(SemanticServiceLimits::default);
        let work_limit = policy
            .execution
            .work
            .min(host.remaining().value.max(0) as u64);
        if work_limit == 0 {
            return Err("lookahead subject scan has no funded host work".into());
        }
        let mut used = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(
            &mut used,
            work_limit,
            policy.boundary_payload_bytes,
            &mut cancelled,
        );
        let scanned = scan_installed_occurrences(subject, &mut budget);
        let spent = budget.work_used();
        drop(budget);
        if spent > 0 {
            MeteredMachine::new(host.clone())
                .reserve_primitive(Cost::create(
                    i64::try_from(spent).unwrap_or(i64::MAX),
                    "lookahead subject occurrence scan",
                ))
                .map_err(|_| "lookahead subject scan exhausted host phlogiston".to_string())?;
        }
        scanned.map_err(|error| error.to_string())
    }

    fn scan_top_level_and_charge<'a>(
        &self,
        subject: &'a Par,
        host: &RuntimeBudget,
    ) -> Result<Vec<TopLevelExprOccurrence<'a>>, String> {
        let policy = self
            .installed_runtime
            .as_ref()
            .map(|runtime| runtime.service().policy().semantic_service)
            .unwrap_or_else(SemanticServiceLimits::default);
        let work_limit = policy
            .execution
            .work
            .min(host.remaining().value.max(0) as u64);
        if work_limit == 0 {
            return Err("v3 top-level scan has no funded host work".into());
        }
        let mut used = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(
            &mut used,
            work_limit,
            policy.boundary_payload_bytes,
            &mut cancelled,
        );
        let scanned = scan_top_level_reflected_exprs(subject, &mut budget);
        let spent = budget.work_used();
        drop(budget);
        // One proportional charge for the scan and one for the bounded
        // iterative clone performed by the caller after successful preflight.
        let charged = spent
            .checked_mul(2)
            .and_then(|work| i64::try_from(work).ok())
            .ok_or_else(|| "v3 scan and clone work exceeds the host charge domain".to_string())?;
        MeteredMachine::new(host.clone())
            .reserve_primitive(Cost::create(charged, "lookahead v3 scan and clone"))
            .map_err(|_| "v3 scan and clone exhausted host phlogiston".to_string())?;
        scanned.map_err(|error| error.to_string())
    }

    fn parse_envelope_v3_and_charge<'a>(
        &self,
        subject: &'a Par,
        host: &RuntimeBudget,
    ) -> Result<Option<(&'a Par, WireTopLevelBinding<'a>)>, String> {
        let policy = self
            .installed_runtime
            .as_ref()
            .map(|runtime| runtime.service().policy().semantic_service)
            .unwrap_or_else(SemanticServiceLimits::default);
        let work_limit = policy
            .execution
            .work
            .min(host.remaining().value.max(0) as u64);
        if work_limit == 0 {
            return Err("v3 envelope parsing has no funded host work".into());
        }
        let mut used = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(
            &mut used,
            work_limit,
            policy.boundary_payload_bytes,
            &mut cancelled,
        );
        let parsed = parse_envelope_v3_with_charge(subject, |work, bytes| {
            budget
                .charge(work, bytes)
                .map_err(|_| "v3 envelope exceeds the funded request budget".to_string())
        });
        let spent = budget.work_used();
        drop(budget);
        if spent != 0 {
            let charged = i64::try_from(spent)
                .map_err(|_| "v3 envelope work exceeds the host charge domain".to_string())?;
            MeteredMachine::new(host.clone())
                .reserve_primitive(Cost::create(charged, "lookahead v3 envelope parsing"))
                .map_err(|_| "v3 envelope parsing exhausted host phlogiston".to_string())?;
        }
        parsed
    }

    fn parse_envelope_and_charge<'a>(
        &self,
        subject: &'a Par,
        host: &RuntimeBudget,
    ) -> Result<Option<(&'a Par, Vec<WireOwnerBinding<'a>>)>, String> {
        let policy = self
            .installed_runtime
            .as_ref()
            .map(|runtime| runtime.service().policy().semantic_service)
            .unwrap_or_else(SemanticServiceLimits::default);
        let work_limit = policy
            .execution
            .work
            .min(host.remaining().value.max(0) as u64);
        if work_limit == 0 {
            return Err("v2 envelope parsing has no funded host work".into());
        }
        let mut used = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(
            &mut used,
            work_limit,
            policy.boundary_payload_bytes,
            &mut cancelled,
        );
        let parsed = parse_envelope_v2_with_charge(subject, |work, bytes| {
            budget
                .charge(work, bytes)
                .map_err(|_| "v2 envelope exceeds the funded request budget".to_string())
        });
        let spent = budget.work_used();
        drop(budget);
        if spent > 0 {
            MeteredMachine::new(host.clone())
                .reserve_primitive(Cost::create(
                    i64::try_from(spent).unwrap_or(i64::MAX),
                    "lookahead v2 envelope parsing",
                ))
                .map_err(|_| "v2 envelope parsing exhausted host phlogiston".to_string())?;
        }
        parsed
    }

    /// Four system-process definitions: the original two v1 channels and two
    /// dedicated v2 channels, each retaining its family's outer arity.
    ///
    /// The `fixed_channel`s are the **quoted strings** the lowering sends on, not band
    /// channels: a `Definition` installs a continuation on exactly the channel named, and the
    /// surface emits `@"^spec-all"!(…)`. The `body_ref`s come from
    /// [`LOOKAHEAD_BAND`](mettail_rholang_codegen::LOOKAHEAD_BAND), so they are deterministic
    /// and provably disjoint from f1r3node's own and from the two MeTTaIL contract bands.
    pub fn definitions(&self) -> Vec<Definition> {
        vec![
            self.definition(false, false, false),
            self.definition(true, false, false),
            self.definition(false, true, false),
            self.definition(true, true, false),
            self.definition(false, true, true),
            self.definition(true, true, true),
        ]
    }

    fn definition(&self, bounded: bool, versioned: bool, composite: bool) -> Definition {
        let (channel, arity, index, urn, abi) = match (bounded, versioned, composite) {
            (false, false, false) => {
                (SPEC_ALL_CHANNEL, 2, SPEC_ALL_INDEX, "mtl:spec:all", LOOKAHEAD_ABI_VERSION)
            },
            (true, false, false) => {
                (SPEC_N_CHANNEL, 3, SPEC_N_INDEX, "mtl:spec:n", LOOKAHEAD_ABI_VERSION)
            },
            (false, true, false) => (
                SPEC_ALL_V2_CHANNEL,
                2,
                SPEC_ALL_V2_INDEX,
                "mtl:spec:all:v2",
                LOOKAHEAD_ABI_VERSION_V2,
            ),
            (true, true, false) => {
                (SPEC_N_V2_CHANNEL, 3, SPEC_N_V2_INDEX, "mtl:spec:n:v2", LOOKAHEAD_ABI_VERSION_V2)
            },
            (false, true, true) => (
                SPEC_ALL_V3_CHANNEL,
                2,
                SPEC_ALL_V3_INDEX,
                "mtl:spec:all:v3",
                LOOKAHEAD_ABI_VERSION_V3,
            ),
            (true, true, true) => {
                (SPEC_N_V3_CHANNEL, 3, SPEC_N_V3_INDEX, "mtl:spec:n:v3", LOOKAHEAD_ABI_VERSION_V3)
            },
            (_, false, true) => unreachable!("composite requests are versioned"),
        };
        let engine = self.clone();
        Definition {
            urn: urn.to_string(),
            fixed_channel: spec_channel_par(channel),
            arity,
            body_ref: LOOKAHEAD_BAND.body_ref(index, abi),
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
                    Box::pin(async move {
                        engine
                            .serve(call, args, bounded, versioned, composite)
                            .await
                    })
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
        versioned: bool,
        composite: bool,
    ) -> Result<Vec<Par>, InterpreterError> {
        let urn = match (bounded, versioned, composite) {
            (false, false, false) => SPEC_ALL_CHANNEL,
            (true, false, false) => SPEC_N_CHANNEL,
            (false, true, false) => SPEC_ALL_V2_CHANNEL,
            (true, true, false) => SPEC_N_V2_CHANNEL,
            (false, true, true) => SPEC_ALL_V3_CHANNEL,
            (true, true, true) => SPEC_N_V3_CHANNEL,
            (_, false, true) => unreachable!("composite requests are versioned"),
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
            guard: None,
        };

        // ── the operands ─────────────────────────────────────────────────
        let (subject, lookahead, reply) = match parse_request_owned(payload, bounded) {
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

        let (subject, installed_bindings) = match if composite {
            self.admit_top_level_subject(subject, host)
        } else {
            self.admit_subject(subject, host, versioned)
        } {
            Ok(admitted) => admitted,
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
        if !installed_bindings.is_empty() {
            let runtime = self
                .installed_runtime
                .as_ref()
                .expect("admitted installed bindings require a live runtime");
            publisher.guard = Some(Arc::new(InstalledLookaheadPublication {
                table: Arc::clone(runtime.service().table()),
                handles: installed_bindings
                    .iter()
                    .map(|binding| binding.handle.clone())
                    .collect(),
            }));
        }

        // ── which guest, if any ──────────────────────────────────────────
        let guest = match if installed_bindings.is_empty() {
            self.guest_for(&subject)
        } else {
            Ok(None)
        } {
            Ok(guest) => guest,
            Err(refusal) => {
                // ★ The DATUM names only the refused fingerprint. The engine's guest list —
                // which languages this binary was built with, in the order they were
                // registered — is node configuration, and goes to the operator's log instead.
                // See [`GuestRefusal`].
                publisher
                    .publish(
                        request_error_datum(ErrorCode::Bootstrap, &refusal.published()),
                        &spec(SPEC_ERR_CHANNEL),
                    )
                    .await?;
                tracing::warn!("lookahead: {refusal}");
                return Ok(Vec::new());
            },
        };

        // ★ `prelude | seed(⟦P⟧)` for a registered guest; the bare subject otherwise. This
        // is the line the module header's `prelude` warning is about.
        let request = if !installed_bindings.is_empty() {
            let projection = if installed_bindings.len() == 1
                && installed_bindings[0].path.is_empty()
                && installed_bindings[0].top_level_expr.is_none()
            {
                LeafProjection::InstalledGuestRoot
            } else {
                LeafProjection::Configuration
            };
            let runtime = self
                .installed_runtime
                .as_ref()
                .expect("admitted installed bindings require a live runtime")
                .clone();
            LookaheadRequest::new(subject, lookahead)
                .with_projection(projection)
                .with_installed_bindings(runtime, installed_bindings)
        } else {
            match guest {
                Some(guest) => {
                    LookaheadRequest::new(guest.seed(subject, SPEC_LEAF_CHANNEL), lookahead)
                        .with_prelude(guest.prelude.clone())
                        .with_projection(LeafProjection::resting_on(SPEC_LEAF_CHANNEL))
                        .with_definitions(guest.definitions())
                },
                None => LookaheadRequest::new(subject, lookahead)
                    .with_projection(LeafProjection::Configuration),
            }
        }
        .with_trace_mode(self.trace_mode);

        // ── the exploration ──────────────────────────────────────────────
        let attempt = LookaheadService::serve(request, publisher.random.clone(), host).await;

        // ── the charge-back, BEFORE anything is delivered ────────────────
        //
        // An exploration the deploy cannot afford must not also hand back an answer: the
        // failure is reported and the results are withheld, exactly as an over-budget
        // program produces no output.
        // The attempt carries the same receipt after a response or an error.
        // A provider may refuse after earlier sandbox COMMs; settle those
        // before publishing even the refusal datum.
        let outcome = match attempt.settle(host, speculation_weight()) {
            Ok(outcome) => outcome,
            Err(failure) => {
                // `{error}`, not `{error:?}`: this string becomes a `^spec-err` datum, and
                // `InterpreterError`'s derived `Debug` is generated code — the same
                // build-artifact-in-consensus-bytes hazard `SpeculationError`'s `Display` header
                // spells out. `InterpreterError` has a hand-written `Display`.
                let datum = request_error_datum(
                    ErrorCode::OutOfPhlogistons,
                    &format!(
                        "the exploration committed {} COMM(s) the host could not pay for: \
                     {charged} charged before {error}",
                        failure.owed.value,
                        charged = failure.charged,
                        error = failure.error,
                    ),
                );
                publisher.publish(datum, &spec(SPEC_ERR_CHANNEL)).await?;
                return Err(InterpreterError::OutOfPhlogistonsError);
            },
        };

        let response = match outcome {
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

        self.publish_response(&mut publisher, response, guest, &reply, versioned)
            .await
    }

    /// Publish one served response onto the five channels of the module header's diagram.
    async fn publish_response(
        &self,
        publisher: &mut Publisher<'_>,
        response: LookaheadResponse,
        guest: Option<&SpeculationGuest>,
        reply: &Par,
        versioned: bool,
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

        // A v2 reply is ONE RSpace produce with two PathMap payloads in the
        // approved order. The complete delivery was assembled before this
        // point; a service-level rendering refusal cannot leak a partial
        // success/failure answer onto the public channel. V1 retains its
        // original one-bare-term-per-success ABI for existing programs.
        let published = if versioned {
            if let Some(datum) = error.as_ref() {
                publisher
                    .publish(datum.clone(), &spec(SPEC_ERR_CHANNEL))
                    .await?;
                return Ok(Vec::new());
            }
            let [success_name, failure_name] = delivery.fips_reply();
            let payloads = [success_name.clone(), failure_name.clone()];
            publisher.publish_payloads(&payloads, reply).await?;
            payloads.to_vec()
        } else {
            let mut published = Vec::with_capacity(terms.len());
            for term in terms {
                publisher.publish(term.clone(), reply).await?;
                published.push(term);
            }
            published
        };

        if versioned {
            publisher
                .publish(
                    ground_list(vec![
                        new_gint_par(2, Vec::new(), false),
                        delivery.truncated.clone(),
                    ]),
                    &spec(SPEC_TRUNCATED_V2_CHANNEL),
                )
                .await?;
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
    ///
    /// The `Err` is a [`GuestRefusal`] rather than a `String` because the refusal has **two
    /// audiences with different rules**: see that type's header.
    fn guest_for(&self, subject: &Par) -> Result<Option<&SpeculationGuest>, GuestRefusal> {
        let Some(fingerprint) = reflected_fingerprint(subject) else {
            return Ok(None);
        };
        match self
            .guests
            .iter()
            .find(|guest| guest.fingerprint == fingerprint)
        {
            Some(guest) => Ok(Some(guest)),
            None => Err(GuestRefusal {
                fingerprint,
                registered: self
                    .guests
                    .iter()
                    .map(|guest| guest.fingerprint.clone())
                    .collect(),
            }),
        }
    }
}

/// **A refused subject, split by audience.** The whole type exists because the two audiences
/// obey different rules, and rendering one string for both put node configuration on chain.
///
/// The refusal used to be one `String` embedding `{registered:?}` — the engine's guest list,
/// built by iterating `self.guests` in `with_guest` **registration order** — and that string
/// became a `^spec-err` datum, which `Publisher::publish` `produce`s into the live deploy's
/// RSpace.
///
/// Both halves of it are node configuration rather than a function of the program:
///
/// | what | why it is not a property of the deploy |
/// |---|---|
/// | the **contents** | which languages this binary was built with — a `--features` decision, and for a host embedding the engine, a decision made in that host's `main` |
/// | the **order** | the sequence of [`LookaheadEngine::with_guest`] calls, which no deploy can observe or reproduce |
///
/// ★ It is the one member of this defect class that **no deploy-derived seed could ever
/// repair**: the former store indices in `step_digest` and `reify`'s map order were at least
/// computed from the configuration, so canonicalising them recovers a function of the program. A list of what
/// some other binary was compiled with is not in the program at all. Two validators built from
/// the same source with different feature sets would publish different bytes for the same
/// refusal — and *neither would be wrong*.
///
/// So the datum names only the **refused fingerprint**, which is read off the subject and is
/// therefore program-derived; the engine's inventory goes to the operator through
/// [`Display`](std::fmt::Display) and `tracing`, where it is a diagnostic and not a value
/// anybody has to agree on.
///
/// ⚠ The two renderings must stay different. `the_refusal_datum_carries_no_node_configuration`
/// asserts exactly that: the published text names the fingerprint and no registered guest.
#[derive(Clone, Debug, PartialEq, Eq)]
struct GuestRefusal {
    /// The language fingerprint carried by the refused subject. **Program-derived** — read off
    /// the reflected term's own ABI head — so it is safe to publish.
    fingerprint: String,
    /// The fingerprints registered with this engine, in registration order. **Node
    /// configuration**, host-side only, never a datum.
    registered: Vec<String>,
}

impl GuestRefusal {
    /// The text that becomes the `^spec-err` datum: the refused fingerprint and the reason,
    /// and nothing about this node.
    ///
    /// It still says *"no evaluator is registered"* — the phrase a consumer greps and
    /// `x7_lookahead_end_to_end::an_unregistered_guest_is_refused_loudly` asserts — because the
    /// fix is to stop publishing the **inventory**, not to stop publishing the **fact**.
    fn published(&self) -> String {
        format!(
            "the subject is a reflected term of language {:?}, for which no evaluator is \
             registered with the lookahead engine. A reflected term is INERT without its \
             guest's installed program, so exploring it would find one leaf and hand back the \
             subject itself as though it were a normal form. Refusing instead.",
            self.fingerprint
        )
    }
}

/// The **host-side** rendering: the published text plus the engine's inventory, for an operator
/// who has to work out which feature or which `with_guest` call is missing. Never published.
impl std::fmt::Display for GuestRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "{} Registered with this engine, in registration order: {:?}.",
            self.published(),
            self.registered
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Publishing
// ══════════════════════════════════════════════════════════════════════════

/// Recheck every installed owner at the exact RSpace produce commit. The
/// registry lock is held only around the synchronous commit closure, never
/// across the asynchronous producer or the speculative search.
struct InstalledLookaheadPublication {
    table: Arc<InstalledLanguageTable>,
    handles: Vec<InstalledLanguageHandle>,
}

impl ProduceCommitGuard for InstalledLookaheadPublication {
    fn with_commit(&self, commit: Box<dyn FnOnce() + '_>) -> Result<(), RSpaceError> {
        const REQUIRED: &[LanguageRight] = &[LanguageRight::Reduce];
        self.table
            .with_authorized_batch(self.handles.iter().map(|handle| (handle, REQUIRED)), commit)
            .map_err(|_| RSpaceError::ProduceCommitDenied)
    }
}

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
    guard: Option<Arc<dyn ProduceCommitGuard>>,
}

impl Publisher<'_> {
    async fn publish(&mut self, datum: Par, channel: &Par) -> Result<(), InterpreterError> {
        self.publish_payloads(&[datum], channel).await
    }

    /// One RSpace produce, so all payloads enter the same datum atomically.
    async fn publish_payloads(
        &mut self,
        payloads: &[Par],
        channel: &Par,
    ) -> Result<(), InterpreterError> {
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
        let args = (
            vec![ListParWithRandom {
                pars: Vec::new(),
                random_state: random.to_bytes(),
            }],
            self.is_replay,
            self.previous.clone(),
        );
        let producer = match &self.guard {
            Some(guard) => self.call.unapply_guarded(args, Arc::clone(guard)),
            None => self.call.unapply(args),
        };
        let Some((produce, _, _, _)) = producer else {
            return Err(InterpreterError::IllegalArgumentError(
                "the lookahead publisher could not build a producer".to_string(),
            ));
        };
        produce(payloads, channel).await?;
        Ok(())
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Request parsing and wire shapes
// ══════════════════════════════════════════════════════════════════════════

/// Authority admitted against the live installed table, independent of the
/// caller's serialized claims. The opaque handle retains its revocation epoch;
/// publication must revalidate it under the table's commit guard.
pub(crate) struct AdmittedLookaheadBinding {
    pub(crate) path: Vec<u32>,
    /// `Some(index)` is the disjoint v3 top-level expression locator. Its
    /// `path` is empty only for compatibility with the shared checked adapter;
    /// it is never interpreted as a v2 root binding.
    pub(crate) top_level_expr: Option<usize>,
    pub(crate) handle: InstalledLanguageHandle,
    pub(crate) installed: Arc<InstalledLanguage>,
    pub(crate) sort: TheorySortId,
    pub(crate) category: CategoryId,
    pub(crate) context: u32,
    /// Exact, checked structural input, including native-literal roots that
    /// have no constructor-head fingerprint.
    pub(crate) input: SemanticTransitionInput,
}

struct WireOwnerBinding<'a> {
    path: Vec<u32>,
    token: &'a Par,
    category: &'a str,
    context: u32,
}

struct WireTopLevelBinding<'a> {
    expr_index: usize,
    token: &'a Par,
    category: &'a str,
    context: u32,
}

/// Move the validated subject out of an owned v2 envelope. The caller must
/// first run `parse_envelope_v2_with_charge` so this positional extraction has
/// no independent interpretation of program-controlled wire data.
fn take_envelope_subject(mut envelope: Par) -> Option<Par> {
    let ExprInstance::EListBody(list) = envelope.exprs.first_mut()?.expr_instance.as_mut()? else {
        return None;
    };
    (list.ps.len() == 3).then(|| std::mem::take(&mut list.ps[1]))
}

/// The exact v2 first datum is `[2, subject, owner-bindings]`; each binding is
/// `[path, opaque-handle, expected-category, context]`. A claim never grants
/// authority: resolution and structural admission happen separately.
fn parse_envelope_v2_with_charge<'a>(
    subject: &'a Par,
    mut charge: impl FnMut(usize, usize) -> Result<(), String>,
) -> Result<Option<(&'a Par, Vec<WireOwnerBinding<'a>>)>, String> {
    charge(1, 0)?;
    let Some([version, actual, claims]) = exact_list(subject) else {
        return Ok(None);
    };
    if ground_int(version) != Some(2) {
        return Ok(None);
    }
    let claims =
        exact_list(claims).ok_or_else(|| "v2 owner-bindings must be an exact list".to_string())?;
    charge(
        claims.len(),
        claims
            .len()
            .checked_mul(32)
            .ok_or_else(|| "v2 binding roster is too large".to_string())?,
    )?;
    let mut bindings = Vec::new();
    bindings
        .try_reserve(claims.len())
        .map_err(|_| "v2 binding roster allocation failed".to_string())?;
    for claim in claims {
        charge(1, 0)?;
        let Some([path, token, category, context]) = exact_list(claim) else {
            return Err("v2 owner binding must have four fields".into());
        };
        let indices =
            exact_list(path).ok_or_else(|| "v2 owner path must be an exact list".to_string())?;
        charge(
            indices.len(),
            indices
                .len()
                .checked_mul(4)
                .ok_or_else(|| "v2 owner path is too long".to_string())?,
        )?;
        let mut path = Vec::new();
        path.try_reserve(indices.len())
            .map_err(|_| "v2 owner path allocation failed".to_string())?;
        for index in indices {
            path.push(
                ground_int(index)
                    .and_then(|index| u32::try_from(index).ok())
                    .ok_or_else(|| "v2 owner path contains a noncanonical index".to_string())?,
            );
        }
        let category = exact_string(category)
            .filter(|category| !category.is_empty())
            .ok_or_else(|| "v2 owner category must be a nonempty string".to_string())?;
        charge(category.len(), 0)?;
        let context = ground_int(context)
            .and_then(|context| u32::try_from(context).ok())
            .ok_or_else(|| "v2 owner context must be a nonnegative coordinate".to_string())?;
        bindings.push(WireOwnerBinding { path, token, category, context });
    }
    charge(bindings.len(), 0)?;
    if bindings.windows(2).any(|pair| pair[0].path >= pair[1].path) {
        return Err("v2 owner paths must be distinct and strictly ordered".into());
    }
    Ok(Some((actual, bindings)))
}

/// V3 retains the three-field envelope but uses a disjoint, typed locator.
/// Exactly one closed top-level expression is supported; every other shape
/// fails before any sandbox is constructed.
fn parse_envelope_v3_with_charge<'a>(
    envelope: &'a Par,
    mut charge: impl FnMut(usize, usize) -> Result<(), String>,
) -> Result<Option<(&'a Par, WireTopLevelBinding<'a>)>, String> {
    charge(1, 0)?;
    let Some([version, subject, claims]) = exact_list(envelope) else {
        return Ok(None);
    };
    if ground_int(version) != Some(3) {
        return Ok(None);
    }
    let claims =
        exact_list(claims).ok_or_else(|| "v3 owner-bindings must be an exact list".to_string())?;
    let [claim] = claims else {
        return Err("v3 requires exactly one closed top-level owner binding".into());
    };
    charge(2, 64)?;
    let Some([locator, token, category, context]) = exact_list(claim) else {
        return Err("v3 owner binding must have four fields".into());
    };
    let Some([kind, index]) = exact_list(locator) else {
        return Err("v3 owner locator must have a typed kind and index".into());
    };
    if exact_string(kind) != Some("expr") {
        return Err("v3 only admits a top-level expression locator".into());
    }
    let expr_index = ground_int(index)
        .and_then(|index| usize::try_from(index).ok())
        .ok_or_else(|| "v3 expression index is not canonical".to_string())?;
    let category = exact_string(category)
        .filter(|category| !category.is_empty())
        .ok_or_else(|| "v3 owner category must be a nonempty string".to_string())?;
    charge(category.len(), category.len())?;
    let context = ground_int(context)
        .and_then(|context| u32::try_from(context).ok())
        .ok_or_else(|| "v3 owner context must be a nonnegative coordinate".to_string())?;
    Ok(Some((subject, WireTopLevelBinding { expr_index, token, category, context })))
}

#[cfg(test)]
fn parse_envelope_v2(subject: &Par) -> Result<Option<(&Par, Vec<WireOwnerBinding<'_>>)>, String> {
    parse_envelope_v2_with_charge(subject, |_, _| Ok(()))
}

/// `(subject, lookahead, replyChannel)` from a request's payload.
///
/// ★ Every operand here is **program-controlled**, and the refusals are consensus-visible. The
/// surface's `lookahead_bound` (`rholang_ast`) restricts `[n]` to a ground
/// unsigned-64-bit literal,
/// but `^spec-n` is an ordinary Rholang channel served by an installed system process: a program
/// can write `@"^spec-n"!(P, <any Par at all>, x)` and reach this function directly. So the
/// malformed-bound arm renders its operand through [`render_par_text`] — bounded and
/// derive-independent — for the reason spelled out on [`guest_evaluator_failures`], with the
/// aggravation that here the input is attacker-chosen rather than merely large.
fn parse_request_owned(
    mut payload: Vec<Par>,
    bounded: bool,
) -> Result<(Par, Lookahead, Par), String> {
    match bounded {
        false if payload.len() == 2 => {
            let reply = payload.pop().expect("arity checked");
            let subject = payload.pop().expect("arity checked");
            Ok((subject, Lookahead::Unbounded, reply))
        },
        false => Err(format!("expected (subject, replyChannel), got arity {}", payload.len())),
        true if payload.len() == 3 => {
            let reply = payload.pop().expect("arity checked");
            let bound = payload.pop().expect("arity checked");
            let subject = payload.pop().expect("arity checked");
            let bound = crate::semantic_wire::decode_u64_literal(&bound).map_err(|_| {
                format!(
                    "the `[n]` bound must be a ground integer in canonical unsigned 64-bit form, got {}",
                    render_par_text(&bound)
                )
            })?;
            Ok((subject, Lookahead::Steps(bound), reply))
        },
        true => {
            Err(format!("expected (subject, bound, replyChannel), got arity {}", payload.len()))
        },
    }
}

#[cfg(test)]
fn parse_request(payload: &[Par], bounded: bool) -> Result<(Par, Lookahead, Par), String> {
    parse_request_owned(payload.to_vec(), bounded)
}

/// The `i64` a ground-integer `Par` carries.
fn ground_int(par: &Par) -> Option<i64> {
    match crate::language_install::exact_expr(par) {
        Some(ExprInstance::GInt(value)) => Some(*value),
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
///
/// The message goes through [`super::budgeted_message`]: this datum is published on
/// `^spec-err`, so its free-text field is consensus-visible and must be bounded. Two of the
/// callers interpolate a foreign error whose own `Display` may embed a `Par`.
fn request_error_datum(code: ErrorCode, message: &str) -> Par {
    ground_list(vec![
        new_gint_par(code.as_i64(), Vec::new(), false),
        new_gstring_par(super::budgeted_message(message), Vec::new(), false),
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
                        // `render_par_text` bounds the redex; `budgeted_message` bounds the
                        // whole line, so the ONE contract holds at the datum rather than at
                        // one of its two ingredients.
                        super::budgeted_message(&format!(
                            "the guest evaluator rested on {channel}: the stuck redex is {}",
                            render_par_text(&stuck),
                        )),
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

    fn lower_plain(source: &str) -> Par {
        use mettail_languages::rholang::Proc;

        let parsed = Proc::parse_via_wpda(source).expect("plain Rholang test process parses");
        crate::rholang_ast::lower_rholang_proc(&parsed).expect("plain Rholang test process lowers")
    }

    fn pathmap_length(value: &Par) -> usize {
        let Some(ExprInstance::EPathmapBody(map)) = exact_expr(value) else {
            panic!("reply payload must be a PathMap");
        };
        // The native carrier represents an empty set with its dedicated
        // `Empty` mode; populated trace collections use `Set` mode.
        let expected_mode = if map.is_empty() {
            models::rust::epathmap_trie_codec::EPathMapMode::Empty
        } else {
            models::rust::epathmap_trie_codec::EPathMapMode::Set
        };
        assert_eq!(map.mode(), expected_mode);
        map.len()
    }

    #[test]
    fn authored_native_owner_request_matches_the_versioned_builder() {
        use crate::lookahead::{spec_all_request_v2, LookaheadOwnerBinding};

        let authored =
            lower_plain(r#"@"^spec-all-v2"!([2, "a", [[[], "token", "Scalar", 0]]], "reply")"#);
        let expected = spec_all_request_v2(
            new_gstring_par("a".into(), Vec::new(), false),
            vec![LookaheadOwnerBinding {
                path: Vec::new(),
                handle: new_gstring_par("token".into(), Vec::new(), false),
                expected_category: "Scalar".into(),
                context: 0,
            }],
            spec_channel_par("reply"),
        );
        assert_eq!(authored.sends.len(), 1);
        assert_eq!(expected.sends.len(), 1);
        assert_eq!(authored.sends[0].chan, expected.sends[0].chan);
        assert_eq!(authored.sends[0].data.len(), expected.sends[0].data.len());
        assert_eq!(authored.sends[0].data[0], expected.sends[0].data[0]);
    }

    #[test]
    fn authored_native_owner_request_keeps_two_operands_under_new() {
        let authored = lower_plain(
            r#"new regex, lookaheadNative in {
                @"^spec-all-v2"!([2, "a", [[[], *regex, "Scalar", 0]]], *lookaheadNative)
            }"#,
        );
        let body = authored.news[0].p.as_ref().expect("new body");
        assert_eq!(body.sends.len(), 1);
        assert_eq!(body.sends[0].data.len(), 2, "v2 ABI has two operands");
    }

    #[tokio::test]
    async fn versioned_reply_is_one_two_pathmap_datum() {
        use crate::lookahead::spec_all_request_v2;

        let receiver = lower_plain(
            r#"for (@success, @failure <- @"reply") {
                 @"seen-success"!(success) | @"seen-failure"!(failure)
               }"#,
        );
        let request = spec_all_request_v2(
            new_gint_par(7, Vec::new(), false),
            Vec::new(),
            spec_channel_par("reply"),
        );
        let rest = crate::run_normalized_par_with_lookahead_engine(
            &request.append(receiver),
            &LookaheadEngine::new(),
            &[
                "reply",
                "seen-success",
                "seen-failure",
                SPEC_TRUNCATED_V2_CHANNEL,
                SPEC_ERR_CHANNEL,
            ],
        )
        .await
        .expect("versioned lookahead runs in the same RSpace as its receiver");

        assert!(rest["reply"].is_empty(), "the two-payload datum was consumed once");
        assert_eq!(rest["seen-success"].len(), 1);
        assert_eq!(rest["seen-failure"].len(), 1);
        assert_eq!(pathmap_length(&rest["seen-success"][0]), 1);
        assert_eq!(pathmap_length(&rest["seen-failure"][0]), 0);
        assert!(rest[SPEC_ERR_CHANNEL].is_empty());

        let reports = &rest[SPEC_TRUNCATED_V2_CHANNEL];
        assert_eq!(reports.len(), 1, "one typed extension per v2 request");
        let fields = exact_list(&reports[0]).expect("typed truncation is a list");
        assert_eq!(fields.len(), 2);
        assert!(matches!(exact_expr(&fields[0]), Some(ExprInstance::GInt(2))));
        assert_eq!(pathmap_length(&fields[1]), 0);
    }

    #[tokio::test]
    async fn versioned_bound_keeps_truncation_off_the_public_reply() {
        use crate::lookahead::spec_n_request_v2;

        let subject = lower_plain(r#"@"tick"!(1) | for (@value <- @"tick") { @"OUT"!(value) }"#);
        let request = spec_n_request_v2(subject, 0, Vec::new(), spec_channel_par("reply"));
        let rest = crate::run_normalized_par_with_lookahead_engine(
            &request,
            &LookaheadEngine::new(),
            &["reply", SPEC_TRUNCATED_V2_CHANNEL, SPEC_ERR_CHANNEL],
        )
        .await
        .expect("bounded versioned lookahead runs");

        assert_eq!(rest["reply"].len(), 2, "x has exactly the approved two map payloads");
        assert_eq!(pathmap_length(&rest["reply"][0]), 0);
        assert_eq!(pathmap_length(&rest["reply"][1]), 0);
        assert!(rest[SPEC_ERR_CHANNEL].is_empty());
        let reports = &rest[SPEC_TRUNCATED_V2_CHANNEL];
        assert_eq!(reports.len(), 1);
        let fields = exact_list(&reports[0]).expect("typed truncation is a list");
        assert_eq!(fields.len(), 2);
        assert!(matches!(exact_expr(&fields[0]), Some(ExprInstance::GInt(2))));
        assert!(pathmap_length(&fields[1]) > 0, "the cut branch remains queryable");
    }

    #[tokio::test]
    async fn native_scalar_root_admits_with_explicit_installed_owner() {
        use crate::lookahead::{spec_envelope_v2, LookaheadOwnerBinding};

        let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
        let runtime = Arc::new(runtime);
        let engine = LookaheadEngine::new().with_language_runtime(Arc::clone(&runtime));
        let host = RuntimeBudget::new(Cost::create(10_000_000, "native lookahead test"));
        let subject = new_gstring_par("a".into(), Vec::new(), false);
        let envelope = spec_envelope_v2(
            subject.clone(),
            vec![LookaheadOwnerBinding {
                path: Vec::new(),
                handle: token,
                expected_category: "Scalar".into(),
                context: 0,
            }],
        );
        let (admitted, bindings) = engine
            .admit_subject(envelope, &host, true)
            .expect("explicit Scalar owner admits the native root");
        assert_eq!(admitted, subject);
        assert_eq!(bindings.len(), 1);
        let response = LookaheadService::serve(
            LookaheadRequest::new(admitted, Lookahead::Unbounded)
                .with_projection(LeafProjection::InstalledGuestRoot)
                .with_installed_bindings(runtime, bindings),
            Blake2b512Random::create_from_length(128),
            &host,
        )
        .await
        .settle(&host, Cost::create(1, "server lookahead test charge"))
        .expect("the host can pay for the exploration")
        .expect("native Scalar search has a complete checked roster");
        assert!(response.error.is_none());
        assert!(response.failure.is_empty());
        assert_eq!(response.reply, vec![subject]);
    }

    #[test]
    fn native_root_rejects_forged_and_revoked_installed_owner_handles() {
        use crate::lookahead::{spec_envelope_v2, LookaheadOwnerBinding};

        let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
        let runtime = Arc::new(runtime);
        let engine = LookaheadEngine::new().with_language_runtime(Arc::clone(&runtime));
        let host = RuntimeBudget::new(Cost::create(10_000_000, "native owner refusal test"));
        let subject = new_gstring_par("a".into(), Vec::new(), false);
        let request = |handle| {
            spec_envelope_v2(
                subject.clone(),
                vec![LookaheadOwnerBinding {
                    path: Vec::new(),
                    handle,
                    expected_category: "Scalar".into(),
                    context: 0,
                }],
            )
        };

        let forged = models::rust::rholang::implicits::GPrivateBuilder::new_par_from_string(
            "forged-installed-owner".to_string(),
        );
        let forged_error = engine
            .admit_subject(request(forged), &host, true)
            .err()
            .expect("an arbitrary private name is not an installed authority");
        assert!(forged_error.contains("not authorized for Reduce"));

        runtime.revoke(&token).expect("revoke installed owner");
        let revoked_error = engine
            .admit_subject(request(token), &host, true)
            .err()
            .expect("a revoked token cannot authorize a native literal");
        assert!(revoked_error.contains("not authorized for Reduce"));
    }

    #[test]
    fn top_level_guest_admission_requires_exact_locator_and_live_owner() {
        use crate::lookahead::{spec_envelope_v3, LookaheadTopLevelBinding};

        let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
        let guest = runtime
            .construct_template(
                &token,
                &[mettail_grammar_core::RuntimeTemplatePiece::Text("a+".into())],
                &[],
                Some("Pattern"),
                &std::collections::BTreeMap::new(),
            )
            .expect("installed guest constructor");
        assert_eq!(guest.exprs.len(), 1);
        let subject = guest.clone().append(lower_plain(r#"@"tick"!(1)"#));
        let runtime = Arc::new(runtime);
        let engine = LookaheadEngine::new().with_language_runtime(Arc::clone(&runtime));
        let host = RuntimeBudget::new(Cost::create(10_000_000, "v3 admission test"));
        let claim = |handle, expr_index| LookaheadTopLevelBinding {
            expr_index,
            handle,
            expected_category: "Pattern".into(),
            context: 0,
        };

        let (admitted, bindings) = engine
            .admit_top_level_subject(
                spec_envelope_v3(subject.clone(), claim(token.clone(), 0)),
                &host,
            )
            .expect("one exact top-level reflected guest admits");
        assert_eq!(admitted, subject);
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].top_level_expr, Some(0));

        let wrong_index = engine
            .admit_top_level_subject(
                spec_envelope_v3(subject.clone(), claim(token.clone(), 1)),
                &host,
            )
            .err()
            .expect("a host sibling cannot be selected as the guest");
        assert!(wrong_index.contains("exact installed occurrence"));

        let nested = models::rust::utils::new_elist_par(
            vec![guest],
            Vec::new(),
            false,
            None::<models::rhoapi::Var>,
            Vec::new(),
            false,
        );
        let nested_error = engine
            .admit_top_level_subject(spec_envelope_v3(nested, claim(token.clone(), 0)), &host)
            .err()
            .expect("a transported guest has no top-level owner slot");
        assert!(
            nested_error.contains("reflected FLT is embedded in a composite Par"),
            "{nested_error}"
        );

        let forged = models::rust::rholang::implicits::GPrivateBuilder::new_par_from_string(
            "forged-v3-owner".into(),
        );
        let forged_error = engine
            .admit_top_level_subject(spec_envelope_v3(subject.clone(), claim(forged, 0)), &host)
            .err()
            .expect("a forged owner cannot authorize the guest");
        assert!(forged_error.contains("not authorized for Reduce"));

        runtime.revoke(&token).expect("revoke installed owner");
        let revoked_error = engine
            .admit_top_level_subject(spec_envelope_v3(subject, claim(token, 0)), &host)
            .err()
            .expect("a revoked owner cannot authorize the guest");
        assert!(revoked_error.contains("not authorized for Reduce"));
    }

    #[test]
    fn generated_top_level_admission_requires_exact_live_owner_and_locator() {
        use crate::lookahead::{spec_envelope_v3, LookaheadTopLevelBinding};
        use proptest::prelude::*;
        use proptest::test_runner::{Config, TestRunner};

        let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
        let guest = runtime
            .construct_template(
                &token,
                &[mettail_grammar_core::RuntimeTemplatePiece::Text("a+".into())],
                &[],
                Some("Pattern"),
                &std::collections::BTreeMap::new(),
            )
            .expect("installed Pattern constructor");
        let runtime = Arc::new(runtime);
        let engine = LookaheadEngine::new().with_language_runtime(Arc::clone(&runtime));
        let host = RuntimeBudget::new(Cost::create(100_000_000, "generated v3 admission"));
        let forged = models::rust::rholang::implicits::GPrivateBuilder::new_par_from_string(
            "forged-generated-v3-owner".into(),
        );

        let mut runner = TestRunner::new(Config::with_cases(128));
        runner
            .run(
                &(proptest::collection::vec(any::<i16>(), 0..16), any::<usize>()),
                |(host_values, placement)| {
                    let guest_index = placement % (host_values.len() + 1);
                    let mut subject = Par::default();
                    subject.exprs = host_values
                        .into_iter()
                        .map(|value| {
                            new_gint_par(i64::from(value), Vec::new(), false)
                                .exprs
                                .remove(0)
                        })
                        .collect();
                    subject.exprs.insert(guest_index, guest.exprs[0].clone());

                    let claim = |handle: Par, expr_index: usize, category: &str, context| {
                        LookaheadTopLevelBinding {
                            expr_index: u32::try_from(expr_index).expect("small generated index"),
                            handle,
                            expected_category: category.into(),
                            context,
                        }
                    };
                    let admitted = engine.admit_top_level_subject(
                        spec_envelope_v3(
                            subject.clone(),
                            claim(token.clone(), guest_index, "Pattern", 0),
                        ),
                        &host,
                    );
                    let (accepted, bindings) = admitted.map_err(|error| {
                        TestCaseError::fail(format!("valid generated owner refused: {error}"))
                    })?;
                    prop_assert_eq!(accepted, subject.clone());
                    prop_assert_eq!(bindings.len(), 1);
                    prop_assert_eq!(bindings[0].top_level_expr, Some(guest_index));

                    let wrong_index = if subject.exprs.len() == 1 {
                        1
                    } else {
                        (guest_index + 1) % subject.exprs.len()
                    };
                    prop_assert!(engine
                        .admit_top_level_subject(
                            spec_envelope_v3(
                                subject.clone(),
                                claim(token.clone(), wrong_index, "Pattern", 0),
                            ),
                            &host,
                        )
                        .is_err());
                    prop_assert!(engine
                        .admit_top_level_subject(
                            spec_envelope_v3(
                                subject.clone(),
                                claim(token.clone(), guest_index, "Scalar", 0),
                            ),
                            &host,
                        )
                        .is_err());
                    prop_assert!(engine
                        .admit_top_level_subject(
                            spec_envelope_v3(
                                subject.clone(),
                                claim(token.clone(), guest_index, "Pattern", 1),
                            ),
                            &host,
                        )
                        .is_err());
                    prop_assert!(engine
                        .admit_top_level_subject(
                            spec_envelope_v3(
                                subject,
                                claim(forged.clone(), guest_index, "Pattern", 0),
                            ),
                            &host,
                        )
                        .is_err());
                    Ok(())
                },
            )
            .expect("generated v3 authority and locator properties");
    }

    #[test]
    fn installed_publication_commits_once_only_while_every_owner_is_live() {
        use rspace_plus_plus::rspace::rspace_interface::commit_produce;

        let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
        let handle = runtime
            .resolve(&token, LanguageRight::Reduce)
            .expect("live installed owner");
        let guard = InstalledLookaheadPublication {
            table: Arc::clone(runtime.service().table()),
            handles: vec![handle.clone(), handle],
        };
        let mut commits = 0;
        assert_eq!(commit_produce(Some(&guard), || commits += 1), Ok(()));
        assert_eq!(commits, 1, "one produce runs its commit exactly once");

        runtime
            .revoke(&token)
            .expect("no table lock survives commit");
        assert_eq!(
            commit_produce(Some(&guard), || commits += 1),
            Err(RSpaceError::ProduceCommitDenied)
        );
        assert_eq!(commits, 1, "a revoked owner cannot enter the commit closure");
    }

    /// Each wire version retains distinct deterministic IDs in the reserved band.
    #[test]
    fn request_definitions_occupy_distinct_reserved_body_refs() {
        let all = LOOKAHEAD_BAND.body_ref(SPEC_ALL_INDEX, LOOKAHEAD_ABI_VERSION);
        let bounded = LOOKAHEAD_BAND.body_ref(SPEC_N_INDEX, LOOKAHEAD_ABI_VERSION);
        let all_v2 = LOOKAHEAD_BAND.body_ref(SPEC_ALL_V2_INDEX, LOOKAHEAD_ABI_VERSION_V2);
        let bounded_v2 = LOOKAHEAD_BAND.body_ref(SPEC_N_V2_INDEX, LOOKAHEAD_ABI_VERSION_V2);
        let all_v3 = LOOKAHEAD_BAND.body_ref(SPEC_ALL_V3_INDEX, LOOKAHEAD_ABI_VERSION_V3);
        let bounded_v3 = LOOKAHEAD_BAND.body_ref(SPEC_N_V3_INDEX, LOOKAHEAD_ABI_VERSION_V3);
        assert_eq!(all, LOOKAHEAD_BAND.body_ref(0, "mettail-lookahead-v1"));
        assert_eq!(bounded, LOOKAHEAD_BAND.body_ref(1, "mettail-lookahead-v1"));
        assert_eq!(
            [all, bounded, all_v2, bounded_v2, all_v3, bounded_v3]
                .into_iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            6,
        );
        let band = LOOKAHEAD_BAND.body_ref_range();
        assert!([all, bounded, all_v2, bounded_v2, all_v3, bounded_v3]
            .iter()
            .all(|body_ref| band.contains(body_ref)));
        assert!(*band.start() > 108, "above f1r3node's std and test-framework body_refs");
    }

    /// The `Definition`s install on the QUOTED-STRING channels the lowering sends on, with
    /// the arities each mode carries.
    #[test]
    fn the_definitions_install_on_the_wire_channels() {
        let engine = LookaheadEngine::new();
        let definitions = engine.definitions();
        assert_eq!(definitions.len(), 6);
        assert_eq!(definitions[0].fixed_channel, spec_channel_par(SPEC_ALL_CHANNEL));
        assert_eq!(definitions[0].arity, 2, "(subject, replyChannel)");
        assert_eq!(definitions[1].fixed_channel, spec_channel_par(SPEC_N_CHANNEL));
        assert_eq!(definitions[1].arity, 3, "(subject, bound, replyChannel)");
        assert_eq!(definitions[2].fixed_channel, spec_channel_par(SPEC_ALL_V2_CHANNEL));
        assert_eq!(definitions[2].arity, 2);
        assert_eq!(definitions[3].fixed_channel, spec_channel_par(SPEC_N_V2_CHANNEL));
        assert_eq!(definitions[3].arity, 3);
        assert_eq!(definitions[4].fixed_channel, spec_channel_par(SPEC_ALL_V3_CHANNEL));
        assert_eq!(definitions[4].arity, 2);
        assert_eq!(definitions[5].fixed_channel, spec_channel_par(SPEC_N_V3_CHANNEL));
        assert_eq!(definitions[5].arity, 3);
    }

    #[test]
    fn legacy_host_list_starting_with_two_is_never_an_envelope() {
        use crate::language_install::wire_list;

        let host_subject = wire_list(vec![
            new_gint_par(2, Vec::new(), false),
            spec_channel_par("ordinary-host-data"),
            wire_list(Vec::new()),
        ]);
        let host = RuntimeBudget::unmetered();
        let engine = LookaheadEngine::new();
        let (legacy, bindings) = engine
            .admit_subject(host_subject.clone(), &host, false)
            .expect("v1 channel preserves host list data");
        assert_eq!(legacy, host_subject);
        assert!(bindings.is_empty());
        let (versioned, bindings) = engine
            .admit_subject(host_subject, &host, true)
            .expect("same datum is the v2 envelope only on the v2 channel");
        assert_eq!(versioned, spec_channel_par("ordinary-host-data"));
        assert!(bindings.is_empty());
    }

    #[test]
    fn versioned_subject_is_moved_out_of_the_owned_envelope() {
        use crate::language_install::wire_list;
        use crate::lookahead::spec_envelope_v2;

        let subject = wire_list(vec![spec_channel_par("retained-child")]);
        let child_storage = exact_list(&subject).expect("subject list").as_ptr();
        let envelope = spec_envelope_v2(subject, Vec::new());
        let (admitted, bindings) = LookaheadEngine::new()
            .admit_subject(envelope, &RuntimeBudget::unmetered(), true)
            .expect("empty v2 binding roster preserves the host subject");
        assert!(bindings.is_empty());
        assert_eq!(
            exact_list(&admitted)
                .expect("admitted subject list")
                .as_ptr(),
            child_storage
        );
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

        assert!(
            parse_request(std::slice::from_ref(&subject), false).is_err(),
            "arity 1 is not a request"
        );
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

    #[test]
    fn request_bound_accepts_full_u64_and_rejects_noncanonical_wide_values() {
        let subject = spec_channel_par("subject");
        let reply = spec_channel_par("results");
        for expected in [i64::MAX as u64 + 1, u64::MAX] {
            let bound = crate::semantic_wire::encode_u64_literal(expected);
            let (_, actual, _) = parse_request(&[subject.clone(), bound, reply.clone()], true)
                .expect("canonical upper-half bound");
            assert_eq!(actual, Lookahead::Steps(expected));
        }
        for bytes in [vec![], vec![0], vec![0; 9], vec![0; 10], vec![0xff; 9]] {
            let bound =
                Par::default().with_exprs(vec![models::rust::utils::new_gbigint_expr(bytes)]);
            assert!(
                parse_request(&[subject.clone(), bound, reply.clone()], true).is_err(),
                "malformed or out-of-range BigInt bound must be refused"
            );
        }
    }

    #[test]
    fn versioned_request_enforces_exact_ordered_binding_paths() {
        use crate::language_install::wire_list;
        use crate::lookahead::{spec_envelope_v2, LookaheadOwnerBinding};

        let subject = spec_channel_par("subject");
        let binding = |path| LookaheadOwnerBinding {
            path,
            handle: spec_channel_par("selector"),
            expected_category: "Term".into(),
            context: 0,
        };
        let envelope = spec_envelope_v2(subject.clone(), vec![binding(vec![0]), binding(vec![1])]);
        let (actual, claims) = parse_envelope_v2(&envelope)
            .expect("canonical envelope")
            .expect("versioned");
        assert_eq!(actual, &subject);
        assert_eq!(claims.len(), 2);
        assert_eq!(claims[0].path, vec![0]);
        assert_eq!(claims[1].path, vec![1]);

        for paths in [[vec![0], vec![0]], [vec![1], vec![0]]] {
            let envelope =
                spec_envelope_v2(subject.clone(), paths.into_iter().map(binding).collect());
            assert!(parse_envelope_v2(&envelope).is_err());
        }
        let malformed = wire_list(vec![
            new_gint_par(2, Vec::new(), false),
            subject,
            new_gint_par(0, Vec::new(), false),
        ]);
        assert!(parse_envelope_v2(&malformed).is_err());
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
    /// That is **not** true of Rholang source: `@c!(a, b, c)` lowers to a send of a single
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
        let refusal = LookaheadEngine::new()
            .guest_for(&term)
            .expect_err("no evaluator is registered, so this must be a refusal");
        assert!(refusal.published().contains("unregistered"), "{refusal}");

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

    /// ★★ **The refusal DATUM carries nothing about this node.** (D5.)
    ///
    /// The published message used to embed `{registered:?}` — the engine's guest list, built by
    /// iterating `self.guests` in `with_guest` registration order. Both the contents (which
    /// languages this binary was built with) and the order (the sequence of builder calls) are
    /// node configuration, and the message is `produce`d into the live deploy's RSpace by
    /// `Publisher::publish`.
    ///
    /// The cell is written as a **differential between two engines** rather than as a grep for
    /// a phrase: two engines with different, non-empty, differently-ordered guest lists must
    /// publish the *same bytes* for the same refused subject. That is the property — a grep
    /// only rules out the spellings someone thought of.
    #[test]
    fn the_refusal_datum_carries_no_node_configuration() {
        let term = mettail_rholang_codegen::reflect_ground_term_par(
            &mettail_rholang_codegen::GroundTerm::nullary("PZero"),
            "mettail-langdef-v1:absent",
        );
        let refuse = |guests: &[&str]| -> GuestRefusal {
            let mut engine = LookaheadEngine::new();
            for guest in guests {
                engine = engine.with_guest(SpeculationGuest::driven(*guest, Par::default()));
            }
            engine
                .guest_for(&term)
                .expect_err("none of these engines can serve the subject")
        };

        let lean = refuse(&["mettail-langdef-v1:lambda"]);
        // A different feature set, in a different registration order.
        let rich = refuse(&[
            "mettail-langdef-v1:ambient",
            "mettail-langdef-v1:calculator",
            "mettail-langdef-v1:lambda",
        ]);
        let bare = refuse(&[]);

        assert_eq!(
            lean.published(),
            rich.published(),
            "★ two nodes built with different guest sets published different refusals for one \
             program. No deploy-derived seed can repair that: the guest list is not in the \
             deploy at all."
        );
        assert_eq!(
            bare.published(),
            rich.published(),
            "★ …and a node with NO guests must publish the same bytes as a node with three"
        );

        // The fact still reaches the reader — this is not a fix by deletion.
        assert!(
            rich.published().contains("no evaluator is registered"),
            "the refusal must still SAY it is a refusal: {}",
            rich.published()
        );
        assert!(
            rich.published().contains("absent"),
            "…and must name the refused fingerprint, which is read off the SUBJECT and is \
             therefore program-derived: {}",
            rich.published()
        );
        for guest in ["ambient", "calculator", "lambda"] {
            assert!(
                !rich.published().contains(guest),
                "★ {guest:?} is this node's build configuration and must not be in a datum: {}",
                rich.published()
            );
        }

        // …and the operator still gets the inventory, on the HOST-side rendering, which is
        // what `tracing::warn!` prints and what nothing publishes.
        let host_side = format!("{rich}");
        for guest in ["ambient", "calculator", "lambda"] {
            assert!(
                host_side.contains(guest),
                "the host-side rendering must keep the hint that was dropped from the datum: \
                 {host_side}"
            );
        }
        assert_ne!(
            host_side,
            format!("{lean}"),
            "★ …and it is the rendering that DOES vary with node configuration, which is the \
             whole reason the two are separate"
        );
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
