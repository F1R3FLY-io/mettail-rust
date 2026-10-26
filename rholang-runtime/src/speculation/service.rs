//! # The engine's side of the `[*]` / `[n]` ABI
//!
//! [`crate::lookahead`] owns the **wire**: the reserved request channels, the
//! two request-seed builders, and the fail-closed unserved-request readback.
//! This module owns the **answer**: given a request's operands, it runs a real
//! branching exploration and hands back exactly the values the wire's report
//! channels carry — typed, named, and already in `Par` form.
//!
//! The split is deliberate. The engine never names a channel, so a change to the
//! wire cannot silently change what the search computes; the wire never runs a
//! reduction, so a change to the search cannot silently change what a program
//! sees. The two meet here, at a struct with named fields.
//!
//! ## The mapping the surface applies
//!
//! | [`LookaheadResponse`] field | `crate::lookahead` channel |
//! |---|---|
//! | [`reply`](LookaheadResponse::reply) | v1 `x` — one bare datum per success branch |
//! | [`delivery`](LookaheadResponse::delivery) | v2 `x` — one datum with the success and failure PathMap names |
//! | [`success`](LookaheadResponse::success) | `SPEC_SUCCESS_CHANNEL` — `[trace, term]` per branch |
//! | [`failure`](LookaheadResponse::failure) | `SPEC_FAILURE_CHANNEL` — `[trace, [code, message]]` per branch |
//! | [`truncated`](LookaheadResponse::truncated) | `SPEC_TRUNCATED_CHANNEL` — `[trace, handle]` per branch |
//! | [`error`](LookaheadResponse::error) | `SPEC_ERR_CHANNEL` — a typed *request*-level refusal, distinct from a branch failure |
//!
//! A trace rides the wire as an `EList`: input, saturated initial configuration,
//! and each successor, with a proof marker immediately before every guest
//! successor. A handle is the 32-byte [`delivery::trace_digest`]
//! of that whole sequence, which is also the key
//! [`LookaheadService::resume`] takes back.
//!
//! ## What a branch's "term" is
//!
//! A leaf is a whole terminal *configuration*, which is the FIPS-faithful
//! answer. But a program that wrote `x!(P)[*]` asked *"what did `P` compute?"*,
//! and for a guest lowered onto a receiver network the configuration also
//! contains the network. [`LeafProjection`] names the two readings explicitly
//! rather than picking one silently:
//!
//! * [`LeafProjection::RestingOn`] — the data resting on a designated channel.
//!   For a guest driven to quiescence by the generated `^drive` family this is
//!   the quiescent term, i.e. exactly what a live run reads back, and it is what
//!   makes the ordinary FLT receive pattern work verbatim on the reply channel.
//! * [`LeafProjection::Configuration`] — the reified terminal configuration as a
//!   process. The FIPS's own leaf, and the one the Lambdas use case
//!   pattern-matches (`match inst { for (_, _ <- instCh) { _ } => … }`).
//!
//! ## ★★ Metering
//!
//! [`LookaheadService::serve`] funds its sandbox from the host deploy's
//! remaining phlogiston, runs, and reports what it spent
//! ([`LookaheadAttempt::consumed`]) — a **COMM count** even if exploration
//! later refuses. A fired COMM costs one unit, and staging is free (DR-131).
//! The caller charges it back with
//! [`crate::speculation::search::Explorer::charge_host`], which is `consumed()`
//! *calls* to f1r3node's own `reserve_comm`. The request server passes a weight
//! of one unit for each call, so each speculative COMM is one COMM event of
//! weight one on the host's lane. Nothing here owns a budget; budgets are
//! F1r3node's.
//!
//! `serve` and `resume` do **not** charge the host themselves. The public
//! handler consumes the attempt with [`LookaheadAttempt::settle`] against its
//! live host budget before it can inspect either a response or a refusal. The
//! charge amount remains the one defined by f1r3node's `reserve_comm`.
//!
//! Standalone requests use [`LookaheadService::serve_local`] and
//! [`LookaheadService::resume_local`]. Each builds a fresh local CostV2
//! sandbox that can commit a resting rendezvous; its COMMs are charged back
//! like any other. Native consensus and replay cannot use this authority, and
//! no host work is metered (DR-131 extension to F1R3Lang, user decision 1).

use std::sync::Arc;

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::Par;
use models::rhoapi::Var;
use models::rust::utils::{new_elist_par, new_gbytearray_par, new_gint_par, new_gstring_par};
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::system_processes::Definition;

use crate::language_install::RholangLanguageRuntime;

use super::delivery::{reify, resting_on, trace_digest, ReificationError, SpeculationDelivery};
use super::installed_provider::InstalledCheckedGuestProvider;
use super::search::{
    charge_host_comms, AbortedLeaf, ErrorCode, Exploration, Explorer, Lookahead, QuiescentLeaf,
    TraceMode, TruncatedLeaf,
};
use super::server::AdmittedLookaheadBinding;
#[cfg(test)]
use super::RendezvousName;
use super::{ReductionTrace, ResumableBranch, SpeculationError, SpeculativeSandbox};

// ══════════════════════════════════════════════════════════════════════════
// What a leaf's "term" is
// ══════════════════════════════════════════════════════════════════════════

/// How a branch's terminal *term* is read out of its terminal *configuration*.
/// See the module header.
#[derive(Clone, Debug, PartialEq)]
pub enum LeafProjection {
    /// The data resting on this channel — the guest's answer, exactly as a live
    /// run reads it back. One `Par` per resting datum; a branch that published
    /// nothing contributes nothing.
    RestingOn(Par),
    /// The reified terminal configuration as a process — the FIPS's own leaf.
    Configuration,
    /// The normal-form term of a directly submitted, checked root FLT. The
    /// complete composite configuration still remains in the public trace.
    InstalledGuestRoot,
}

impl LeafProjection {
    /// The observation channel by name, for the usual `GString` case (`"OUT"`
    /// and the reserved `^…` channels are all `GString` names).
    pub fn resting_on(channel: &str) -> Self {
        LeafProjection::RestingOn(new_gstring_par(channel.to_string(), Vec::new(), false))
    }

    /// Apply the projection to one configuration.
    fn apply(&self, leaf: &QuiescentLeaf) -> Result<Vec<Par>, ReificationError> {
        match self {
            LeafProjection::RestingOn(channel) => Ok(resting_on(&leaf.state, channel)),
            LeafProjection::Configuration => match &leaf.guest {
                Some(guest) => Ok(vec![guest.public_configuration.clone()]),
                None => Ok(vec![reify(&leaf.state)?]),
            },
            LeafProjection::InstalledGuestRoot => match &leaf.guest {
                Some(guest) if guest.slots.len() == 1 && guest.slots[0].binding_index == 0 => {
                    Ok(vec![guest.slots[0].value.clone()])
                },
                _ => Err(ReificationError::InvalidInstalledGuestRoot),
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// The request
// ══════════════════════════════════════════════════════════════════════════

/// Everything the engine needs to serve one `x!(P)[n]`.
///
/// `prelude` is the piece a reader is most likely to omit: a reflected guest
/// term is inert on its own, and only reduces alongside the guest's **installed
/// program** — the σ-receivers, the `^drive` receiver family and the per-rule
/// carrier receivers. The caller supplies it because the caller is the one that
/// knows which guest a subject belongs to; the engine composes
/// `prelude | subject` and injects the pair, which is byte-for-byte the program
/// an ordinary run injects.
pub struct LookaheadRequest {
    /// The guest's installed Rho-net program, or `Par::default()` for a plain
    /// process that needs no receiver network.
    pub prelude: Par,
    /// The subject: `⟦P⟧` for a reflected guest term, or the lowered process
    /// itself.
    pub subject: Par,
    /// The bracket: `[n]` or `[*]`.
    pub lookahead: Lookahead,
    /// How to read a branch's terminal term out of its configuration.
    pub projection: LeafProjection,
    /// Whether the search enumerates configurations (default) or every trace.
    pub trace_mode: TraceMode,
    /// The guest's Tier-3 fold-contract / native-handler system processes, if
    /// any. Speculation over a language's terms needs them for the same reason
    /// ordinary execution does.
    pub definitions: Vec<Definition>,
    /// Installed FLT occurrences admitted against the live capability table.
    /// This is owned checked context, never the caller's wire claims.
    pub(crate) installed_bindings: Vec<AdmittedLookaheadBinding>,
    /// The live directory used to revalidate each installed owner at every
    /// guest step and before publication; snapshots alone are not authority.
    pub(crate) installed_runtime: Option<Arc<RholangLanguageRuntime>>,
}

impl LookaheadRequest {
    /// A request over `subject` with no prelude, no definitions, the default
    /// trace mode, and the configuration projection.
    pub fn new(subject: Par, lookahead: Lookahead) -> Self {
        LookaheadRequest {
            prelude: Par::default(),
            subject,
            lookahead,
            projection: LeafProjection::Configuration,
            trace_mode: TraceMode::default(),
            definitions: Vec::new(),
            installed_bindings: Vec::new(),
            installed_runtime: None,
        }
    }

    /// With a guest's installed program.
    pub fn with_prelude(mut self, prelude: Par) -> Self {
        self.prelude = prelude;
        self
    }

    /// With a leaf projection.
    pub fn with_projection(mut self, projection: LeafProjection) -> Self {
        self.projection = projection;
        self
    }

    /// With a trace mode.
    pub fn with_trace_mode(mut self, trace_mode: TraceMode) -> Self {
        self.trace_mode = trace_mode;
        self
    }

    /// With guest system processes.
    pub fn with_definitions(mut self, definitions: Vec<Definition>) -> Self {
        self.definitions = definitions;
        self
    }

    pub(crate) fn with_installed_bindings(
        mut self,
        runtime: Arc<RholangLanguageRuntime>,
        bindings: Vec<AdmittedLookaheadBinding>,
    ) -> Self {
        self.installed_bindings = bindings;
        self.installed_runtime = Some(runtime);
        self
    }
}

// ══════════════════════════════════════════════════════════════════════════
// The response
// ══════════════════════════════════════════════════════════════════════════

/// One branch's report on the `success` wire: `[trace, term]`.
#[derive(Clone, Debug, PartialEq)]
pub struct BranchReport {
    /// The wire form: the two-element `EList` `[trace, [term…]]` — ready to be
    /// published as one datum. The trace is its own `EList` of public path nodes and
    /// the projected terms are their own `EList` **nested inside** it; a
    /// consumer therefore destructures `[trace, terms]` and indexes `terms`.
    ///
    /// ⚠ This doc used to say *"an `EList` of the branch's trace nodes followed
    /// by the branch's term(s)"* — i.e. the FLAT, concatenated shape. That is
    /// the FIPS `success`-map ENTRY ([`super::delivery::success_entry`]), not
    /// what this field holds, and the two are not interchangeable: the flat
    /// reading makes the datum's length the trace length plus the term count,
    /// while it is always exactly 2. The wrong reading reached a demo before it
    /// was caught, so the correction is recorded rather than merely applied.
    /// `pair` (below) is the constructor, and
    /// `tests/x8_publication_is_scheduler_invariant.rs` destructures `ps[1]` as
    /// the term list.
    pub datum: Par,
    /// The branch's handle name — [`trace_digest`] of its trace. Stable across
    /// re-derivation and the key [`LookaheadService::resume`] takes.
    pub handle: [u8; 32],
    /// The branch's projected term(s), unwrapped, for a caller that publishes
    /// the bare term on the reply channel rather than the pair.
    pub terms: Vec<Par>,
}

/// What the engine hands back for one request. See the module header for the
/// channel each field maps onto.
pub struct LookaheadResponse {
    /// One datum per success branch for the legacy v1 reply channel: the **bare
    /// projected term**, so an ordinary receive pattern matches it verbatim.
    /// A branch whose projection yields several terms contributes several.
    pub reply: Vec<Par>,
    /// `[trace, term]` per branch that reached quiescence.
    pub success: Vec<BranchReport>,
    /// `[trace, [code, message]]` per branch that raised.
    pub failure: Vec<Par>,
    /// `[trace, handle]` per branch the bound cut short.
    pub truncated: Vec<Par>,
    /// A typed **request**-level refusal — the subject could not be reified, or
    /// the exploration could not be started. Distinct from a branch failure:
    /// this says the request was not served, not that a path died.
    pub error: Option<Par>,
    /// The resumable handles, keyed by the same digests
    /// [`truncated`](Self::truncated) publishes. Held host-side because a `Par`
    /// cannot carry a datum's `Blake2b512Random` or a continuation's source, so
    /// a branch resumed from a reified process would mint different unforgeable
    /// names.
    pub handles: Vec<(Vec<u8>, ResumableBranch)>,
    /// The FIPS three-collection delivery of the same exploration, for a
    /// consumer that wants one value rather than data on channels.
    pub delivery: SpeculationDelivery,
    /// The exploration itself — counters, leaves, root.
    pub exploration: Exploration,
}

impl LookaheadResponse {
    /// The handle for a published truncated branch.
    pub fn handle(&self, key: &[u8]) -> Option<&ResumableBranch> {
        self.handles
            .iter()
            .find(|(digest, _)| digest.as_slice() == key)
            .map(|(_, branch)| branch)
    }
}

/// The result and resource receipt of one complete service attempt. The
/// receipt exists on both success and refusal, so a caller cannot lose COMMs
/// already committed before a later provider or reification error. A failed
/// sandbox bootstrap has a zero receipt.
pub struct LookaheadAttempt {
    outcome: Result<LookaheadResponse, SpeculationError>,
    /// Sandbox COMMs to charge back one `reserve_comm` call at a time, before
    /// publishing either a response or a request-level refusal.
    consumed: Cost,
}

/// A host that could not pay for every COMM already committed in the isolated
/// exploration. The caller reports this instead of publishing an answer.
#[derive(Debug)]
pub struct LookaheadChargeFailure {
    pub owed: Cost,
    pub charged: usize,
    pub error: InterpreterError,
}

impl LookaheadAttempt {
    /// Inspect the receipt without exposing an uncharged response.
    pub fn consumed(&self) -> &Cost {
        &self.consumed
    }

    /// Charge the live host for every sandbox COMM before revealing either a
    /// response or a refusal. Failed explorations use the same receipt path.
    pub fn settle(
        self,
        host: &RuntimeBudget,
        weight: Cost,
    ) -> Result<Result<LookaheadResponse, SpeculationError>, LookaheadChargeFailure> {
        let owed = self.consumed;
        match charge_host_comms(host, owed.clone(), weight) {
            Ok(_) => Ok(self.outcome),
            Err((charged, error)) => Err(LookaheadChargeFailure { owed, charged, error }),
        }
    }

    fn before_sandbox(error: SpeculationError) -> Self {
        Self {
            outcome: Err(error),
            consumed: Cost::create(0, "lookahead bootstrap"),
        }
    }

    pub(super) fn after_sandbox(
        sandbox: &SpeculativeSandbox,
        outcome: Result<LookaheadResponse, SpeculationError>,
    ) -> Self {
        Self { outcome, consumed: sandbox.consumed() }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// The service
// ══════════════════════════════════════════════════════════════════════════

/// Serves lookahead requests: one sandbox, one exploration, one response.
///
/// A unit struct rather than a stateful server because a speculative sandbox is
/// deliberately *fresh* per request — that is what makes a branch's tuplespace
/// isolated from the host's, which is the confinement use case's whole point.
pub struct LookaheadService;

impl LookaheadService {
    /// **Serve one request.**
    ///
    /// Builds a fresh sandbox, funds it from `host`'s remaining phlogiston,
    /// injects `prelude | subject`, explores, and assembles the wire values.
    ///
    /// `rand` must derive from the **deploy's** randomness on chain: two
    /// validators speculating over the same deploy have to mint the same
    /// unforgeable names.
    ///
    /// Returns an error *inside the attempt* only for an infrastructure failure
    /// (the sandbox could not be built, a retained configuration could not be
    /// re-installed). Everything
    /// a *program* can do wrong — aborting, exhausting the budget, failing to
    /// reduce — arrives as branch failures inside the response, because those
    /// are answers, not faults.
    pub async fn serve(
        request: LookaheadRequest,
        rand: Blake2b512Random,
        host: &RuntimeBudget,
    ) -> LookaheadAttempt {
        Self::serve_with_authority(request, rand, host, false).await
    }

    /// Serve a standalone local request. This creates an isolated local
    /// CostV2 sandbox that can commit a resting rendezvous; it does not
    /// configure a native recording, authorize consensus, or permit replay.
    /// Production node requests obtain the same authority through the
    /// trusted, one-shot `LookaheadEngine::bind_standalone_host` binding.
    pub async fn serve_local(
        request: LookaheadRequest,
        rand: Blake2b512Random,
        host: &RuntimeBudget,
    ) -> LookaheadAttempt {
        Self::serve_with_authority(request, rand, host, true).await
    }

    async fn serve_with_authority(
        request: LookaheadRequest,
        rand: Blake2b512Random,
        host: &RuntimeBudget,
        standalone: bool,
    ) -> LookaheadAttempt {
        if standalone && host.native_execution_active() {
            return LookaheadAttempt::before_sandbox(SpeculationError::Bootstrap(
                "standalone lookahead cannot enter active native accounting or consensus".into(),
            ));
        }
        // `Definition` is not `Clone` (it carries a boxed system-process fn), so
        // the request is destructured and its definitions MOVED into the
        // sandbox. Nothing else needs them.
        let LookaheadRequest {
            prelude,
            subject,
            lookahead,
            projection,
            trace_mode,
            definitions,
            installed_bindings,
            installed_runtime,
        } = request;
        let sandbox = if standalone {
            SpeculativeSandbox::with_definitions_for_standalone(definitions).await
        } else {
            SpeculativeSandbox::with_definitions(definitions).await
        };
        let sandbox = match sandbox {
            Ok(sandbox) => sandbox,
            Err(error) => return LookaheadAttempt::before_sandbox(error),
        };
        if standalone {
            if let Err(error) = sandbox.fund_from_standalone(host) {
                return LookaheadAttempt::after_sandbox(&sandbox, Err(error));
            }
        } else {
            sandbox.fund_from(host);
        }
        let program = prelude.append(subject);
        let outcome = async {
            let mut explorer = if installed_bindings.is_empty() {
                Explorer::with_mode(&sandbox, trace_mode)
            } else {
                let runtime = installed_runtime.ok_or_else(|| {
                    SpeculationError::Bootstrap(
                        "installed lookahead bindings have no live authority directory".into(),
                    )
                })?;
                let provider =
                    InstalledCheckedGuestProvider::new(runtime, installed_bindings, host.clone())?;
                Explorer::with_checked_guest_provider(&sandbox, provider)
            };
            let exploration = explorer.explore(program, rand, lookahead).await?;
            Self::respond(exploration, &projection)
        }
        .await;
        LookaheadAttempt::after_sandbox(&sandbox, outcome)
    }

    /// **Beam search's second half** — continue from handles a previous response
    /// published.
    ///
    /// The sandbox is fresh, as it is for [`serve`](Self::serve): a handle
    /// carries its whole `HotStoreState`, so a resumption needs no continuity of
    /// machine, only continuity of configuration.
    pub async fn resume(
        handles: &[ResumableBranch],
        lookahead: Lookahead,
        projection: &LeafProjection,
        trace_mode: TraceMode,
        definitions: Vec<Definition>,
        host: &RuntimeBudget,
    ) -> LookaheadAttempt {
        Self::resume_with_authority(
            handles,
            lookahead,
            projection,
            trace_mode,
            definitions,
            host,
            false,
        )
        .await
    }

    /// Resume local-only handles in a fresh local CostV2 sandbox. The handle
    /// carries state, not authority; the trusted caller supplies funding on
    /// every resumed request.
    pub async fn resume_local(
        handles: &[ResumableBranch],
        lookahead: Lookahead,
        projection: &LeafProjection,
        trace_mode: TraceMode,
        definitions: Vec<Definition>,
        host: &RuntimeBudget,
    ) -> LookaheadAttempt {
        Self::resume_with_authority(
            handles,
            lookahead,
            projection,
            trace_mode,
            definitions,
            host,
            true,
        )
        .await
    }

    async fn resume_with_authority(
        handles: &[ResumableBranch],
        lookahead: Lookahead,
        projection: &LeafProjection,
        trace_mode: TraceMode,
        definitions: Vec<Definition>,
        host: &RuntimeBudget,
        standalone: bool,
    ) -> LookaheadAttempt {
        if standalone && host.native_execution_active() {
            return LookaheadAttempt::before_sandbox(SpeculationError::Bootstrap(
                "standalone lookahead cannot enter active native accounting or consensus".into(),
            ));
        }
        if handles.iter().any(|handle| handle.guest.is_some()) {
            return LookaheadAttempt::before_sandbox(SpeculationError::Bootstrap(
                "installed guest resumption requires a live checked provider and is not admitted by the host-only resume API".into(),
            ));
        }
        let sandbox = if standalone {
            SpeculativeSandbox::with_definitions_for_standalone(definitions).await
        } else {
            SpeculativeSandbox::with_definitions(definitions).await
        };
        let sandbox = match sandbox {
            Ok(sandbox) => sandbox,
            Err(error) => return LookaheadAttempt::before_sandbox(error),
        };
        if standalone {
            if let Err(error) = sandbox.fund_from_standalone(host) {
                return LookaheadAttempt::after_sandbox(&sandbox, Err(error));
            }
        } else {
            sandbox.fund_from(host);
        }
        let outcome = async {
            let mut explorer = Explorer::with_mode(&sandbox, trace_mode);
            let exploration = explorer.resume(handles, lookahead).await?;
            Self::respond(exploration, projection)
        }
        .await;
        LookaheadAttempt::after_sandbox(&sandbox, outcome)
    }

    /// Assemble the wire values from a finished exploration.
    fn respond(
        exploration: Exploration,
        projection: &LeafProjection,
    ) -> Result<LookaheadResponse, SpeculationError> {
        let mut reply = Vec::with_capacity(exploration.success.len());
        let mut success = Vec::with_capacity(exploration.success.len());
        let mut error = None;

        for leaf in exploration.success.iter() {
            match Self::success_report(leaf, projection) {
                Ok(report) => {
                    reply.extend(report.terms.iter().cloned());
                    success.push(report);
                },
                Err(reification) => {
                    // ★ A request-level refusal, not a branch failure: the branch
                    // succeeded and the ENGINE could not render it. Reported
                    // rather than dropped, because a partial success set is
                    // indistinguishable from a smaller search.
                    error = Some(request_error(
                        ErrorCode::Interpreter,
                        &format!("a success leaf could not be reified: {reification}"),
                    ));
                },
            }
        }

        let mut truncated = Vec::with_capacity(exploration.truncated.len());
        let mut handles = Vec::with_capacity(exploration.truncated.len());
        for leaf in exploration.truncated.iter() {
            let digest = trace_digest(leaf.trace()).bytes();
            truncated.push(truncated_datum(leaf, &digest));
            handles.push((digest, leaf.branch.clone()));
        }

        let mut failure = Vec::with_capacity(exploration.failure.len());
        failure.extend(exploration.failure.iter().map(failure_datum));

        let delivery = super::delivery::deliver(&exploration).map_err(|reification| {
            SpeculationError::Bootstrap(format!("result assembly: {reification}"))
        })?;

        Ok(LookaheadResponse {
            reply,
            success,
            failure,
            truncated,
            error,
            handles,
            delivery,
            exploration,
        })
    }

    fn success_report(
        leaf: &QuiescentLeaf,
        projection: &LeafProjection,
    ) -> Result<BranchReport, ReificationError> {
        let terms = projection.apply(leaf)?;
        let digest = trace_digest(&leaf.trace).bytes();
        let mut handle = [0u8; 32];
        // A `Blake2b256Hash` is 32 bytes by construction; the copy is bounded by
        // the shorter of the two so a future hash width cannot make this panic.
        let width = handle.len().min(digest.len());
        handle[..width].copy_from_slice(&digest[..width]);
        Ok(BranchReport {
            datum: pair(trace_list(&leaf.trace), ground_list(terms.clone())),
            handle,
            terms,
        })
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Wire shapes
// ══════════════════════════════════════════════════════════════════════════

fn ground_list(elements: Vec<Par>) -> Par {
    new_elist_par(elements, Vec::new(), false, None::<Var>, Vec::new(), false)
}

/// A trace as the complete root-to-leaf public path, including guest proofs.
fn trace_list(trace: &ReductionTrace) -> Par {
    ground_list(trace.public_nodes())
}

/// `[left, right]` — the two-element list every report datum is.
fn pair(left: Par, right: Par) -> Par {
    ground_list(vec![left, right])
}

/// `[trace, handle]` for a truncated branch — plus `|E(S)|` at the cut, because
/// a consumer ranking handles for beam search wants to know how many ways each
/// could continue before it spends budget on one.
fn truncated_datum(leaf: &TruncatedLeaf, digest: &[u8]) -> Par {
    ground_list(vec![
        trace_list(leaf.trace()),
        new_gbytearray_par(digest.to_vec(), Vec::new(), false),
        new_gint_par(leaf.branch.frontier as i64, Vec::new(), false),
    ])
}

/// `[trace, [code, message]]` for an aborted branch — the FIPS's *"extra
/// two-element list containing an error code for the failure and a message"*.
fn failure_datum(leaf: &AbortedLeaf) -> Par {
    pair(
        trace_list(&leaf.trace),
        ground_list(vec![
            new_gint_par(leaf.code.as_i64(), Vec::new(), false),
            new_gstring_par(leaf.message.clone(), Vec::new(), false),
        ]),
    )
}

/// `[code, message]` for a REQUEST-level refusal — the request was not served,
/// as opposed to a path that died.
///
/// The message goes through [`super::budgeted_message`]: this datum is published on
/// `^spec-err`, so its free-text field is consensus-visible and must be bounded.
fn request_error(code: ErrorCode, message: &str) -> Par {
    ground_list(vec![
        new_gint_par(code.as_i64(), Vec::new(), false),
        new_gstring_par(super::budgeted_message(message), Vec::new(), false),
    ])
}

#[cfg(test)]
mod wire_shape_tests {
    use super::*;
    use crate::observation::RENDER_BUDGET_CHARS;
    use crate::speculation::{
        CheckedGuestConfiguration, GuestRewriteIdentity, GuestSlotState, SpeculativeState,
    };
    use models::rhoapi::expr::ExprInstance;
    use prost::Message;
    use rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash;

    fn name(consume: u8, datum: u8, cont_index: i32, datum_index: i32) -> RendezvousName {
        RendezvousName {
            consume: Blake2b256Hash::new(&[consume]),
            data: vec![Blake2b256Hash::new(&[datum])],
            continuation_index: cont_index,
            datum_indices: vec![datum_index],
        }
    }

    fn trace(steps: impl IntoIterator<Item = (RendezvousName, i64)>) -> ReductionTrace {
        let mut trace = ReductionTrace::from_process(new_gint_par(0, Vec::new(), false));
        for (name, result) in steps {
            trace = trace.extend(name, new_gint_par(result, Vec::new(), false));
        }
        trace
    }

    #[test]
    fn checked_root_guest_projection_returns_the_term_not_the_composite_trace_node() {
        let term = new_gint_par(9, Vec::new(), false);
        let composite = new_gint_par(100, Vec::new(), false);
        let leaf = QuiescentLeaf {
            trace: ReductionTrace::from_process(composite.clone()),
            state: Default::default(),
            guest: Some(CheckedGuestConfiguration {
                slots: vec![GuestSlotState {
                    binding_index: 0,
                    value: term.clone(),
                    exact_key: vec![1],
                }],
                public_configuration: composite.clone(),
            }),
        };
        assert_eq!(LeafProjection::InstalledGuestRoot.apply(&leaf), Ok(vec![term]));
        assert_eq!(LeafProjection::Configuration.apply(&leaf), Ok(vec![composite]));

        let mut ambiguous = leaf.clone();
        ambiguous
            .guest
            .as_mut()
            .unwrap()
            .slots
            .push(GuestSlotState {
                binding_index: 1,
                value: new_gint_par(10, Vec::new(), false),
                exact_key: vec![2],
            });
        assert_eq!(
            LeafProjection::InstalledGuestRoot.apply(&ambiguous),
            Err(ReificationError::InvalidInstalledGuestRoot),
        );
    }

    #[tokio::test]
    async fn host_only_resume_refuses_a_retained_installed_guest() {
        let host = RuntimeBudget::unmetered();
        let process = new_gint_par(7, Vec::new(), false);
        let handle = ResumableBranch {
            state: SpeculativeState::default(),
            guest: Some(CheckedGuestConfiguration {
                slots: Vec::new(),
                public_configuration: process.clone(),
            }),
            trace: ReductionTrace::from_process(process),
            frontier: 1,
        };
        let error = LookaheadService::resume(
            &[handle],
            Lookahead::Steps(1),
            &LeafProjection::Configuration,
            TraceMode::EveryTrace,
            Vec::new(),
            &host,
        )
        .await
        .settle(&host, Cost::create(1, "resume refusal test charge"))
        .expect("a pre-sandbox refusal has no charge")
        .err()
        .expect("host-only resume cannot silently discard installed authority");
        assert!(
            matches!(error, SpeculationError::Bootstrap(message) if message.contains("live checked provider"))
        );
    }

    /// ★ LAYER 4, on this module's own wire shape. [`trace_list`] is what every
    /// `^spec-success` / `^spec-truncated` / `^spec-failure` datum carries as its first
    /// element. It materializes the complete process sequence, so it is index-free only if
    /// nothing here re-adds a local store position. Nothing does, and this says so rather than
    /// assuming it.
    #[test]
    fn the_wire_trace_list_does_not_carry_a_store_index() {
        let indexed = trace([(name(1, 2, 0, 0), 1), (name(3, 4, 5, 6), 2)]);
        let renumbered = trace([(name(1, 2, 9, 9), 1), (name(3, 4, 0, 1), 2)]);
        assert_eq!(
            trace_list(&indexed).encode_to_vec(),
            trace_list(&renumbered).encode_to_vec(),
            "★ a published trace keyed by store position is keyed by task-arrival order"
        );
        // …and it still separates traces that differ in content or order.
        let reordered = trace([(name(3, 4, 5, 6), 2), (name(1, 2, 0, 0), 1)]);
        assert_ne!(
            trace_list(&indexed).encode_to_vec(),
            trace_list(&reordered).encode_to_vec(),
            "the ORDER of the resulting configurations is the branch's identity and must survive"
        );
    }

    #[test]
    fn report_trace_includes_guest_proof_before_terminal_configuration() {
        let terminal = new_gint_par(8, Vec::new(), false);
        let root = ReductionTrace::from_input_and_configuration(
            new_gint_par(0, Vec::new(), false),
            new_gint_par(1, Vec::new(), false),
        );
        let first = root.extend_guest(
            GuestRewriteIdentity::new(
                vec![0],
                [2; 32],
                [3; 32],
                10,
                new_gint_par(4, Vec::new(), false),
            ),
            terminal.clone(),
        );
        let second = root.extend_guest(
            GuestRewriteIdentity::new(
                vec![0],
                [2; 32],
                [3; 32],
                11,
                new_gint_par(5, Vec::new(), false),
            ),
            terminal.clone(),
        );
        assert_ne!(trace_list(&first).encode_to_vec(), trace_list(&second).encode_to_vec());
        let first_list = trace_list(&first);
        let Some(ExprInstance::EListBody(list)) = first_list
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref())
        else {
            panic!("report trace is a list");
        };
        assert_eq!(list.ps.len(), 4);
        let Some(ExprInstance::EListBody(marker)) = list.ps[2]
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref())
        else {
            panic!("guest proof marker is a tagged list");
        };
        assert_eq!(marker.ps.len(), 6);
        assert_eq!(marker.ps[5], new_gint_par(4, Vec::new(), false));
        assert_eq!(list.ps.last(), Some(&terminal));
    }

    /// The request-refusal datum's free text is bounded — the `^spec-err` half of the contract
    /// [`super::budgeted_message`] states, asserted where the datum is actually built.
    #[test]
    fn a_request_refusal_publishes_a_bounded_message() {
        let huge = "q".repeat(RENDER_BUDGET_CHARS * 10);
        let datum = request_error(ErrorCode::Bootstrap, &huge);
        let Some(ExprInstance::EListBody(list)) = datum
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref())
        else {
            panic!("a request refusal is an EList, got {datum:?}");
        };
        let Some(ExprInstance::GString(message)) = list.ps[1]
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref())
        else {
            panic!("its second element is the message");
        };
        assert!(
            message.chars().count() <= RENDER_BUDGET_CHARS + 128,
            "★ a {}-character refusal became a {}-character consensus-visible datum",
            huge.chars().count(),
            message.chars().count()
        );
        assert!(message.contains("(elided,"), "and it says it was cut: {message}");
    }
}
