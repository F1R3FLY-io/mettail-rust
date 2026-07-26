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
//! | [`reply`](LookaheadResponse::reply) | the send's own channel `x` — one datum per success branch |
//! | [`success`](LookaheadResponse::success) | `SPEC_SUCCESS_CHANNEL` — `[trace, term]` per branch |
//! | [`failure`](LookaheadResponse::failure) | `SPEC_FAILURE_CHANNEL` — `[trace, [code, message]]` per branch |
//! | [`truncated`](LookaheadResponse::truncated) | `SPEC_TRUNCATED_CHANNEL` — `[trace, handle]` per branch |
//! | [`error`](LookaheadResponse::error) | `SPEC_ERR_CHANNEL` — a typed *request*-level refusal, distinct from a branch failure |
//!
//! A trace rides the wire as an `EList` of 32-byte step digests
//! ([`delivery::step_digest`]); a handle is the 32-byte
//! [`delivery::trace_digest`] of the branch's whole trace, which is also the key
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
//! ([`LookaheadResponse::consumed`]) — a **COMM count**. The caller charges it
//! back with [`crate::speculation::search::Explorer::charge_host`], which is
//! `consumed()` *calls* to f1r3node's own `reserve_comm`, not one call passing
//! `consumed()`. Nothing here owns a budget; budgets are F1r3node's.
//!
//! The service does **not** charge the host itself, and that is not an omission:
//! the charge has to happen against the live host budget at the call site, and a
//! service that charged an argument it was handed would be a second place cost
//! is decided.

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::Par;
use models::rust::utils::{new_elist_par, new_gbytearray_par, new_gint_par, new_gstring_par};
use models::rhoapi::Var;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;
use rholang::rust::interpreter::system_processes::Definition;

use super::delivery::{
    reify, resting_on, step_digest, trace_digest, ReificationError, SpeculationDelivery,
};
use super::search::{
    AbortedLeaf, ErrorCode, Exploration, Explorer, Lookahead, QuiescentLeaf, TraceMode,
    TruncatedLeaf,
};
use super::{RendezvousName, ResumableBranch, SpeculationError, SpeculativeSandbox};

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
}

impl LeafProjection {
    /// The observation channel by name, for the usual `GString` case (`"OUT"`
    /// and the reserved `^…` channels are all `GString` names).
    pub fn resting_on(channel: &str) -> Self {
        LeafProjection::RestingOn(new_gstring_par(channel.to_string(), Vec::new(), false))
    }

    /// Apply the projection to one configuration.
    fn apply(
        &self,
        state: &super::SpeculativeState,
    ) -> Result<Vec<Par>, ReificationError> {
        match self {
            LeafProjection::RestingOn(channel) => Ok(resting_on(state, channel)),
            LeafProjection::Configuration => Ok(vec![reify(state)?]),
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
}

// ══════════════════════════════════════════════════════════════════════════
// The response
// ══════════════════════════════════════════════════════════════════════════

/// One branch's report on the `success` wire: `[trace, term]`.
#[derive(Clone, Debug, PartialEq)]
pub struct BranchReport {
    /// The wire form: an `EList` of the branch's step digests followed by the
    /// branch's term(s) — ready to be published as one datum.
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
    /// One datum per success branch, for the send's own channel `x`: the **bare
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
    /// What the sandbox spent: a **COMM count**, to be charged back one
    /// `reserve_comm` call at a time.
    pub consumed: Cost,
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
    /// Returns `Err` only for an infrastructure failure (the sandbox could not
    /// be built, a retained configuration could not be re-installed). Everything
    /// a *program* can do wrong — aborting, exhausting the budget, failing to
    /// reduce — arrives as branch failures inside the response, because those
    /// are answers, not faults.
    pub async fn serve(
        request: LookaheadRequest,
        rand: Blake2b512Random,
        host: &RuntimeBudget,
    ) -> Result<LookaheadResponse, SpeculationError> {
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
        } = request;
        let sandbox = SpeculativeSandbox::with_definitions(definitions).await?;
        sandbox.fund_from(host);
        let program = prelude.append(subject);
        let mut explorer = Explorer::with_mode(&sandbox, trace_mode);
        let exploration = explorer.explore(program, rand, lookahead).await?;
        Self::respond(&sandbox, exploration, &projection)
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
    ) -> Result<LookaheadResponse, SpeculationError> {
        let sandbox = SpeculativeSandbox::with_definitions(definitions).await?;
        sandbox.fund_from(host);
        let mut explorer = Explorer::with_mode(&sandbox, trace_mode);
        let exploration = explorer.resume(handles, lookahead).await?;
        Self::respond(&sandbox, exploration, projection)
    }

    /// Assemble the wire values from a finished exploration.
    fn respond(
        sandbox: &SpeculativeSandbox,
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
            consumed: sandbox.consumed(),
        })
    }

    fn success_report(
        leaf: &QuiescentLeaf,
        projection: &LeafProjection,
    ) -> Result<BranchReport, ReificationError> {
        let terms = projection.apply(&leaf.state)?;
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

/// A trace as an `EList` of 32-byte step digests.
fn trace_list(trace: &[RendezvousName]) -> Par {
    let mut steps = Vec::with_capacity(trace.len());
    steps.extend(
        trace
            .iter()
            .map(|name| new_gbytearray_par(step_digest(name).bytes(), Vec::new(), false)),
    );
    ground_list(steps)
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
fn request_error(code: ErrorCode, message: &str) -> Par {
    ground_list(vec![
        new_gint_par(code.as_i64(), Vec::new(), false),
        new_gstring_par(message.to_string(), Vec::new(), false),
    ])
}
