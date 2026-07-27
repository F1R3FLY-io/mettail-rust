//! # `SpeculativeSandbox` — the space-fork mechanism for `x!(P)[n]`
//!
//! Stage 1 of the `[*]` speculation space fork, with **branching pinned to 1**:
//! one sandbox, one trace, one rendezvous fired per step. The branching search,
//! the `PathMap` assembly, the `[*]` surface syntax and the demo are later
//! stages and are deliberately absent — but every primitive they need is here
//! and is named, because a mechanism that cannot be driven off-index is a
//! mechanism that only ever reproduces ordinary execution.
//!
//! ## What `[*]` is
//!
//! `x!(P)[n]` evaluates `P` speculatively along **all** execution paths for `n`
//! steps, gathers each branch's terminal state into a `success` `PathMap` keyed
//! by the **trace** — the sequence of scheduling choices — collects aborted
//! paths into a `failure` `PathMap`, and places both on `x`. See the approved
//! FIPS `2026-01-08-Lookahead`. The four use cases it exists for are MeTTaIL
//! theories, dynamically-instantiated lambdas, **confinement**, and beam search;
//! confinement is the one that forces a real space fork rather than any form of
//! value threading, because Bob has to observe *every* message Alice's code
//! emits, including the ones she emits on channels he never handed her.
//!
//! ## The model: stratified COMM choice
//!
//! An ordinary reduction interleaves administrative steps (`new`, `match`,
//! arithmetic, `|` fan-out, substitution, the *installation* of a send or a
//! receive) with COMMs, and the interleaving is chosen by the tokio scheduler.
//! Speculation cannot enumerate a scheduler. So the sandbox **stratifies**:
//!
//! ```text
//!    inject P ──▶ [ administrative saturation ] ──▶ quiescence, state S
//!                                                      │
//!                                                      ▼
//!                                              E(S) = enabled rendezvous
//!                                                      │  choose one
//!                                                      ▼
//!                                          [ fire ] ──▶ [ saturate ] ──▶ S'
//! ```
//!
//! Nothing fires until every administrative step has run out, so a *step* of the
//! model is exactly one COMM, and a *trace* is exactly the sequence of choices
//! made at the `E(S)` fork points. The premise this rests on — that delaying
//! every COMM to quiescence removes no rendezvous — is not assumed here: it is
//! measured by `tests/x1_stratified_monotonicity.rs`, whose corpus covers two
//! data/two receives, a `where` guard, a join, a peek, a persistent receive and
//! a peek racing a linear receive, and which computes `E(S)` using RSpace's own
//! matcher as the oracle rather than reimplementing one.
//!
//! ## ★ Four measured corrections this module is built around
//!
//! Each of these was measured, and each contradicts something a reasonable
//! reader would otherwise assume.
//!
//! ### 1. `E(S)`'s least element is NOT the branch an ordinary run takes
//!
//! `RSpace::extract_produce_candidate` splices the **arriving** datum of a
//! `produce` into that channel's candidate pool at index `-1`, ahead of every
//! resting datum in the canonical order. Under stratification there is no
//! arriving datum: everything rests, and the pool is the canonical order alone.
//! The *set* of admissible selections is preserved (admissibility is monotone in
//! the pool — adding a datum can only create selections that contain it) but the
//! *least* one is not: swept over 56 ordered pairs the two regimes pick
//! differently in exactly 28, i.e. 50%.
//!
//! Consequence, and it is the governing one for this whole module: **a trace
//! names its selection explicitly.** [`SpeculativeSandbox::fire`] takes the
//! rendezvous it is to fire; it never re-searches. Nothing here assumes index 0
//! reproduces ordinary execution, and the acceptance test
//! (`tests/s1_speculative_sandbox.rs`) compares against the selection it named,
//! not against "what the reducer did".
//!
//! ### 2. A peek is TWO strata
//!
//! `RSpace::store_persistent_data` takes a `_peeks` argument and **ignores it** —
//! it removes the datum like any other consume. It is the *reducer* that puts
//! the datum back: `Reduce::produce_peeks` re-issues it as a **fresh `produce`**
//! spawned as a parallel sibling of the dispatch. So between the COMM and the
//! restore the datum is absent and not enumerable, and it returns carrying a
//! **different `Produce` source** than the one it left with.
//!
//! This module reproduces both strata rather than papering over them:
//! [`SpeculativeSandbox::fire`] performs the removal (inside f1r3node's own
//! `process_match_found`) and then [`SpeculativeSandbox::stage_peek_restores`]
//! re-produces each non-persistent datum through the ordinary `produce` path, so
//! the restored datum's `Produce` source is minted afresh exactly as it is in an
//! ordinary run. The two are separate named steps precisely so that Stage 2 can
//! treat the restore as its own branch point; within Stage 1's single trace the
//! window between them is not observable, because `E(S)` is only ever computed
//! at quiescence.
//!
//! ### 3. Read the sandbox back with `HotStore::snapshot()`, NEVER `to_map()`
//!
//! `InMemHotStore::to_map` iterates the **data** map and joins continuations
//! onto it, so a waiting continuation on a channel that holds no data is
//! invisible and `joins` never appear at all. A speculative sandbox is *mostly*
//! that shape — a staged receiver waiting for a datum that a later step will
//! produce is the normal quiescent state. Measured: `snapshot()` saw 4
//! continuations and 2 joins where `to_map()` returned 2 rows.
//! [`SpeculativeSandbox::snapshot`] is `snapshot()`; `to_map` is never called.
//!
//! ### 4. Every sandbox state is based on the runtime's POST-BOOTSTRAP snapshot
//!
//! `create_rho_runtime` installs the node's system processes (`stdout`, `stderr`,
//! the registry hooks, …) as *installed* continuations. `revert_to_soft_checkpoint`
//! replaces the hot store wholesale and does **not** call `restore_installs`
//! (which is private), so installing a hand-built `HotStoreState` erases them —
//! measured, 26 installed continuations down to 1 — and every branch loses
//! `stdout!`. [`SpeculativeSandbox`] therefore captures the post-bootstrap
//! snapshot once in [`SpeculativeSandbox::new`] and
//! [`SpeculativeSandbox::load`] layers the caller's content onto it.
//!
//! ## ★ On-chain from the start, and what that decided
//!
//! Speculation runs **on chain**: the exploration is part of the deploy, not a
//! node-local convenience. Four consequences are visible in this module's API.
//!
//! | consequence | how it shows up here |
//! |---|---|
//! | the exploration is a deterministic function of the deploy | [`SpeculativeSandbox::saturate`] takes the `Blake2b512Random` from its caller — there is no seed constant in this file. The sandbox's randomness must derive from the **deploy's**, never from a fixture seed such as `step.rs`'s `FIXED_SEED`. |
//! | replay must RE-DERIVE the whole exploration | speculation emits no COMM events into the deploy log, so there is nothing for replay to filter against. Every ordering this module depends on is content-derived and total — see the determinism note on `SpaceMatcher::enumerate_enabled_rendezvous`, which is why that query lives on the trait `ReplayRSpace` also implements. Because the exploration is metered (below), replay re-deriving it costs exactly what play cost: cost agreement is structural, not separately arranged. |
//! | **metering is the bound** | see the section below. There is no node budget, no frontier cap, no new consensus parameter. |
//! | a replay-equivalence differential is required | it is a later stage, templated on `casper/tests/util/rholang/async_driver_differential.rs`. The consensus-side half it needs already exists: `ReplayRSpace::enabled_rendezvous` shares one implementation with `RSpace::enabled_rendezvous`, pinned by `rspace++/tests/enabled_rendezvous_spec.rs::t6`. |
//!
//! ## ★★ Metering is the bound — there is no separate budget
//!
//! An unmetered speculative evaluation IS the denial-of-service surface. A
//! metered one has none, and needs no new parameter to acquire one: an
//! exploration that would run away simply exhausts the deploy's phlogiston and
//! is rejected, exactly like any other over-budget program.
//!
//! This is not something the sandbox has to arrange — it is already true, and
//! the reason is worth writing down because it is not where a reader would look
//! for it. The consensus cost unit is **one token per send or receive
//! EVALUATED**, and it is levied in `Reduce::eval_send` and
//! `Reduce::eval_receive` (`self.metering.reserve_comm(send_eval_cost())?` /
//! `receive_eval_cost()`), i.e. when the *term* is evaluated, upstream of
//! whether any rendezvous fires. `MeteredMachine::reserve_reduction` — the
//! non-COMM structural charge — is explicitly diagnostic and contributes zero to
//! the consensus consumed cost, so `reserve_comm` is the whole of it.
//!
//! Every speculative step passes through that charge:
//!
//! | speculative step | route | charged |
//! |---|---|---|
//! | administrative saturation | `RhoRuntime::inj` → `eval_send` / `eval_receive` | ✔ one token per send, one per receive |
//! | the store mutation of a firing | `RSpace::process_match_found` | — already paid when the send and the receive were evaluated |
//! | the continuation body | `DebruijnInterpreter::eval` → `eval_send` / `eval_receive` | ✔ one token per send, one per receive |
//! | a peek restore | `StagedSpace::produce` | — the send that produced it was already charged |
//!
//! So there is no unmetered path through this module, and the ONE thing that
//! could have created one is not done: the sandbox's budget is **never** set to
//! `Cost::unsafe_max()`. `create_rho_runtime` gives it `CostAccounting::empty_cost()`
//! — zero — so a sandbox that is never funded refuses to evaluate anything at
//! all, which is the fail-shut direction. [`SpeculativeSandbox::fund_from`] is
//! the only way to give it phlogiston, and it takes it from the **host deploy's
//! remaining budget**, under the host's own signature, so the speculation draws
//! on the same tokens and the same lane the deploy does.
//!
//! The charge-back is the mirror: after the exploration,
//! [`SpeculativeSandbox::consumed`] is what it spent, and the caller charges the
//! host that much through f1r3node's own `MeteredMachine::reserve_comm` — which
//! returns `Err(OutOfPhlogistonsError)` if the deploy cannot afford it. Nothing
//! in this module owns a budget: budgets are F1r3node's, from `wallet.txt`.
//!
//! ### ⚠ A budget unit is ONE COMM, not one unit of `Cost.value`
//!
//! Measured, and it corrects the natural misreading of the API's types.
//! `RuntimeBudget::reconcile_lane` "tallies ONE per committed
//! `BillableKind::Comm` event and ZERO for every other kind", and
//! `MeteredMachine::reserve_comm(amount)` charges **one** regardless of
//! `amount` — the `Cost` it takes is the *diagnostic weight* that rides into the
//! event log and the cost-trace digest, not the amount charged. A budget of `k`
//! tokens therefore commits at most `k` COMMs and then raises on the next one.
//!
//! Two consequences for a caller:
//!
//! * [`SpeculativeSandbox::consumed`] is a **COMM count**. Measured: 64 staged
//!   sends cost exactly 64 units.
//! * Charging it back is `consumed()` *calls* to `reserve_comm`, not one call
//!   with `consumed()` as the argument. `s1_speculative_sandbox.rs::t10` made
//!   that mistake in an earlier revision and measured the host being charged 1
//!   where 5 was owed; it now charges per COMM and asserts the arithmetic.
//!
//! ## Depth-`n` truncation is RESUMABLE — not success, not failure
//!
//! A branch can end three ways, and [`BranchOutcome`] keeps them apart:
//!
//! | outcome | meaning | the FIPS map it belongs in |
//! |---|---|---|
//! | [`BranchOutcome::Quiescent`] | `E(S)` is empty: nothing further can fire | `success` |
//! | [`BranchOutcome::Truncated`] | the step bound `n` ran out while `E(S)` was still non-empty | ⚠ NEITHER — see below |
//! | [`BranchOutcome::Aborted`] | the reduction raised (`abort`, out of phlogistons, any error) | `failure` |
//!
//! A truncated branch is **not** an abort and **not** a completed normal form.
//! It carries a [`ResumableBranch`] — the retained configuration plus the trace
//! that produced it — and [`SpeculativeSandbox::resume`] continues from it.
//! Resumption is bounded by the remaining token budget and by nothing else,
//! which is what makes beam search literally expressible: "run `k` steps, gather
//! the leaves, keep the best `n`, run forward from those" *is* resuming `n`
//! truncated handles.
//!
//! This is why the FIPS leaf is a **handle to a retained configuration** rather
//! than a reified process: a process alone loses randomness provenance — a
//! datum's `Blake2b512Random` and a continuation's `Produce`/`Consume` source
//! are not expressible as a `Par` — so a branch resumed from a reified process
//! would mint different unforgeable names than the branch that was truncated.
//! The handle keeps the `HotStoreState`, which keeps both.
//!
//! ⚠ **Open point for the `PathMap` stage, stated rather than silently
//! resolved:** the FIPS specifies two maps, `success` and `failure`. A truncated
//! branch belongs in neither — putting it in `failure` alongside genuine errors
//! would make "did this abort?" unanswerable, and putting it in `success` would
//! claim a normal form that was not reached. The proposal is a **third map**,
//! `truncated`, keyed by the same trace, whose leaf is the resumable handle; the
//! alternative is a marked leaf in `success`, which is cheaper on the surface
//! syntax but makes every consumer of `success` responsible for checking the
//! mark. This module implements the distinction and leaves the surface choice to
//! the stage that owns the surface.
//!
//! ## The f1r3node surface this uses
//!
//! | call | what it is |
//! |---|---|
//! | `RSpace::enabled_rendezvous()` | `E(S)`. Read-only. The whole query lives on `SpaceMatcher`, so play and replay run one enumeration. |
//! | `RSpace::process_match_found(pc)` | fire the rendezvous `pc` NAMES: remove its data and continuation by store index, drop the joins, emit the `COMM`, return the continuation and matched payloads. |
//! | `DebruijnInterpreter::eval` | the public, self-contained reduction entry — seeds its own completion driver and drains it. |
//! | `RholangAndScalaDispatcher::dispatch` | the system-process (`ScalaBodyRef`) arm. |
//! | `ISpace::revert_to_soft_checkpoint` | exact state install on a fresh sandbox — pinned by `tests/x3_exact_state_install.rs`. |
//!
//! ## Why the dispatch is spelled out rather than delegated
//!
//! f1r3node's post-COMM protocol lives in `Reduce::continue_consume_process`,
//! which is private, and — more to the point — is not the protocol a stratified
//! firing needs. It is written for the *arrival* regimes: on the consume path a
//! persistent continuation was never stored, so the reducer re-issues the
//! consume to put it back; on the produce path it was never removed, so the
//! reducer does not. In the sandbox the continuation is **resting** when the step
//! begins, which is the produce-path shape, and `process_match_found` already
//! implements it exactly (`if !persist { remove_continuation }`). Calling
//! `continue_consume_process` would re-install a persistent continuation that is
//! already there and duplicate it.
//!
//! What is left is genuinely small, and each piece is f1r3node's own code:
//! `dispatch::build_env` verbatim, `Blake2b512Random::merge` verbatim, and
//! `reducer.eval` — the entry whose own documentation calls it the public
//! reduction entry point for external callers. The one deliberate difference
//! from `RholangAndScalaDispatcher::dispatch`'s `ParBody` arm is `eval` in place
//! of `eval_with_path`: `eval_with_path` spawns onto the *ambient* completion
//! driver, and a stratified step has no ambient driver to spawn onto, so its
//! detached children would never be awaited. `eval` seeds a fresh driver and
//! drains it, which is precisely a stratified step's contract.
//!
//! ## What Stage 1 does NOT contain
//!
//! Branching/BFS, the `PathMap` assembly, the `[*]` surface syntax, the demo.
//! Those are later stages by design, not by omission.
//!
//! ## ★ Stage 2 — where the rest of it lives
//!
//! Stage 2 removed the branching pin. The mechanism above is unchanged; two
//! sibling modules build on it, and they are separate because they answer
//! separate questions and must not be able to constrain one another:
//!
//! | module | what it is |
//! |---|---|
//! | [`search`] | the **branching engine**: BFS over `E(S)` with an explicit preallocated frontier, the `[n]`/`[*]` bracket as a first-class mode, the three-outcome classification, and resumption for beam search. It builds no `Par`, so the search cannot depend on the shape of a leaf. |
//! | [`delivery`] | **result assembly**: a configuration reified as a process, and the three collections a receiving program reads (`ESet` of `EList`, the FIPS's own entry shape). It runs no reduction, so the delivery cannot depend on how a leaf was found. |
//!
//! The entry points are [`search::Explorer::explore`] (`x!(P)[n]`),
//! [`search::Explorer::resume`] (beam search's second half),
//! [`delivery::deliver`] (the three collections) and
//! [`search::Explorer::charge_host`] (the metering mirror of
//! [`SpeculativeSandbox::fund_from`]).

/// **Stage 2 — the branching engine.** BFS over `E(S)`: the `[n]`/`[*]`
/// bracket, the three outcomes, trace-vs-configuration modes, resumption.
pub mod search;

/// **Stage 2 — result assembly.** A configuration reified as a process, and the
/// three collections `x!(P)[n]` places on `x`.
pub mod delivery;

/// **Stage 2 — the engine's side of the `[*]` / `[n]` ABI.** Takes a request's
/// operands, runs a real branching exploration, and hands back exactly the
/// values [`crate::lookahead`]'s report channels carry. The wire names no
/// search; the search names no channel.
pub mod service;

/// **Stage 3 — the REQUEST SERVER.** The system-process `Definition`s on
/// `^spec-all` / `^spec-n` that consume a request out of a *running* program,
/// call [`service::LookaheadService::serve`], and publish the results back into
/// that same program — concurrently, so the collecting `for` fires in the same
/// round. This is what makes `x!(P)[*]` an executable construct rather than a
/// wire shape.
pub mod server;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
use std::sync::Arc;

use async_trait::async_trait;
use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::tagged_continuation::TaggedCont;
use models::rhoapi::{BindPattern, ListParWithRandom, Par, TaggedContinuation};
use rho_pure_eval::Env;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::has_cost::HasCost;
use rholang::rust::interpreter::accounting::{RuntimeBudget, Sig, Token};
use rholang::rust::interpreter::dispatch::build_env;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime, RhoRuntimeImpl};
use rholang::rust::interpreter::system_processes::Definition;
use rspace_plus_plus::rspace::checkpoint::{Checkpoint, SoftCheckpoint};
use rspace_plus_plus::rspace::errors::RSpaceError;
use rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash;
use rspace_plus_plus::rspace::hot_store::HotStoreState;
use rspace_plus_plus::rspace::internal::{Datum, ProduceCandidate, Row, WaitingContinuation};
use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::rspace_interface::{ISpace, MaybeConsumeResult, MaybeProduceResult};
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;
use rspace_plus_plus::rspace::trace::event::Produce;
use rspace_plus_plus::rspace::trace::Log;

use crate::guard_par_substrate::SubstrateGuardMatcher;

/// The concrete tuplespace the sandbox runs over.
pub type Space = RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation>;

/// The exact hot-store state — the sandbox's unit of configuration. Every
/// speculative branch is one of these plus the trace that produced it.
pub type SpeculativeState = HotStoreState<Par, BindPattern, ListParWithRandom, TaggedContinuation>;

/// One enabled rendezvous, exactly as f1r3node enumerates and fires it: the
/// channel group, the firing continuation **with its store index**, and the
/// selected data **with theirs**.
///
/// Both index families are the ones `HotStore::remove_continuation` and
/// `HotStore::remove_datum` address, computed once at enumeration time, so an
/// enumerated rendezvous can be fired verbatim without a second search.
pub type Rendezvous = ProduceCandidate<Par, BindPattern, ListParWithRandom, TaggedContinuation>;

// ══════════════════════════════════════════════════════════════════════════
// Errors
// ══════════════════════════════════════════════════════════════════════════

/// Everything that can go wrong inside a speculative step.
#[derive(Debug)]
pub enum SpeculationError {
    /// The tuplespace refused an operation (store construction, state install,
    /// a staged produce/consume).
    Space(RSpaceError),
    /// The reducer refused a term. In the `[*]` semantics this is what will
    /// route a branch into the `failure` `PathMap` — Stage 1 surfaces it to the
    /// caller unchanged rather than classifying it, because the error-code and
    /// message shape the FIPS specifies is the `PathMap` stage's business.
    Interpreter(InterpreterError),
    /// [`SpeculativeSandbox::fire`] was handed a rendezvous the store does not
    /// admit — a stale index, or a rendezvous enumerated against a different
    /// state. `process_match_found` returned no result.
    NotFired,
    /// The sandbox could not be built: the in-memory key-value store or the
    /// history repository refused. Carried as text because the two failures come
    /// from different foreign error types (`heed::Error`,
    /// `HistoryRepositoryError`) and neither is part of this module's contract —
    /// a blanket `From` for either would let an unrelated error silently become
    /// a speculation error at any future call site.
    Bootstrap(String),
}

impl std::fmt::Display for SpeculationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpeculationError::Space(error) => write!(formatter, "tuplespace: {error:?}"),
            SpeculationError::Interpreter(error) => write!(formatter, "reducer: {error:?}"),
            SpeculationError::NotFired => write!(
                formatter,
                "the named rendezvous did not fire: its store indices do not address this state"
            ),
            SpeculationError::Bootstrap(detail) => {
                write!(formatter, "sandbox bootstrap: {detail}")
            },
        }
    }
}

impl std::error::Error for SpeculationError {}

impl From<RSpaceError> for SpeculationError {
    fn from(error: RSpaceError) -> Self {
        SpeculationError::Space(error)
    }
}

impl From<InterpreterError> for SpeculationError {
    fn from(error: InterpreterError) -> Self {
        SpeculationError::Interpreter(error)
    }
}

// ══════════════════════════════════════════════════════════════════════════
// The name of a rendezvous — what a trace records
// ══════════════════════════════════════════════════════════════════════════

/// The **name** of a rendezvous: what a trace element is.
///
/// A trace is the sequence of scheduling choices a branch made, and the FIPS
/// keys the `success` / `failure` `PathMap`s by it, so a name has to be (a)
/// content-derived, so two validators agree on it, and (b) precise enough to
/// distinguish selections that lead to different states.
///
/// Both halves are recorded:
///
/// * `consume` / `data` are **content hashes** — `WaitingContinuation::source`
///   (the hash of channels, patterns, continuation and persistence) and each
///   selected datum's `Datum::source` (the hash of channel, payload and
///   persistence). These are the semantic name, stable across any re-derivation
///   that reaches the same configuration.
/// * `continuation_index` / `datum_indices` are the **store positions** at the
///   moment of enumeration. They disambiguate the case content hashing cannot:
///   two byte-identical sends on one channel produce two data with the same
///   `Produce` hash. Firing either yields the same successor state, so the
///   distinction is not semantically load-bearing — but recording it makes a
///   name reproduce a *specific* enumeration exactly, which is what a
///   replay-equivalence differential compares.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RendezvousName {
    /// `WaitingContinuation::source` — the `Consume` content hash.
    pub consume: Blake2b256Hash,
    /// Each selected datum's `Produce` content hash, in bind order.
    pub data: Vec<Blake2b256Hash>,
    /// The continuation's index in its channel group's candidate order.
    pub continuation_index: i32,
    /// Each selected datum's store index, in bind order.
    pub datum_indices: Vec<i32>,
}

impl RendezvousName {
    /// Name the rendezvous `rendezvous`.
    pub fn of(rendezvous: &Rendezvous) -> Self {
        let mut data = Vec::with_capacity(rendezvous.data_candidates.len());
        let mut datum_indices = Vec::with_capacity(rendezvous.data_candidates.len());
        for candidate in rendezvous.data_candidates.iter() {
            data.push(candidate.datum.source.hash.clone());
            datum_indices.push(candidate.datum_index);
        }
        RendezvousName {
            consume: rendezvous.continuation.source.hash.clone(),
            data,
            continuation_index: rendezvous.continuation_index,
            datum_indices,
        }
    }

    /// The **semantic** name alone — content hashes, no store positions. Two
    /// rendezvous that agree here fire to the same successor state.
    pub fn semantic(&self) -> (Blake2b256Hash, Vec<Blake2b256Hash>) {
        (self.consume.clone(), self.data.clone())
    }
}

// ══════════════════════════════════════════════════════════════════════════
// What one fired step did
// ══════════════════════════════════════════════════════════════════════════

/// The record of one stratified step, returned by [`SpeculativeSandbox::fire`].
///
/// It exists so a driver can build a trace without re-deriving what it just did,
/// and so the two strata of a peek (correction 2) are separately visible.
#[derive(Clone, Debug)]
pub struct FiredStep {
    /// The name of the rendezvous that fired — one element of the trace.
    pub name: RendezvousName,
    /// Whether the fired continuation was persistent (`<=`). A persistent
    /// continuation is NOT removed by the firing, so it may be enabled again in
    /// the next `E(S)`.
    pub persistent: bool,
    /// Whether the fired continuation was a peek (`<<-`).
    pub peek: bool,
    /// How many data the peek restore re-produced — the second stratum. Zero for
    /// a non-peek rendezvous, and zero for a peek all of whose selected data
    /// were persistent (a persistent datum was never removed, so there is
    /// nothing to restore; this mirrors `Reduce::produce_peeks`'s own
    /// `filter(|(_, _, _, persist)| !persist)`).
    pub peek_restores: usize,
    /// Whether the fired continuation was a system process (`ScalaBodyRef`)
    /// rather than a Rholang body (`ParBody`).
    pub system_process: bool,
}

// ══════════════════════════════════════════════════════════════════════════
// How a branch ended — and the handle that makes truncation resumable
// ══════════════════════════════════════════════════════════════════════════

/// A **handle to a retained configuration** — the FIPS leaf, and what a
/// truncated branch returns.
///
/// It is a handle rather than a reified process on purpose. A `Par` cannot
/// express a datum's `Blake2b512Random`, nor a continuation's `Consume` source,
/// nor a datum's `Produce` source; a branch resumed from a reified process would
/// therefore mint different unforgeable names than the branch that was
/// truncated, and the resumption would not be a continuation of anything. The
/// `HotStoreState` keeps all three.
///
/// Reification remains available *as an operation for inspection* — it is the
/// `PathMap` stage's, because the shape it must produce is the one the FIPS's
/// own pattern matches against (`let @{=ret!(squared) | _} <- trace.last()`),
/// which is a decision about the leaf encoding rather than about the mechanism.
#[derive(Clone, Debug)]
pub struct ResumableBranch {
    /// The retained configuration. `SpeculativeSandbox::resume` installs it.
    pub state: SpeculativeState,
    /// The trace that produced it — the sequence of scheduling choices, in
    /// order. This is what the FIPS keys its `PathMap`s by.
    pub trace: Vec<RendezvousName>,
    /// `|E(S)|` at the truncation point: how many ways this branch could have
    /// continued. Non-zero by construction — a branch with an empty `E(S)` is
    /// [`BranchOutcome::Quiescent`], not truncated.
    pub frontier: usize,
}

/// How a speculative branch ended. Three cases, kept apart because a consumer
/// has to be able to tell them apart.
///
/// See the module header for why truncation belongs in neither of the FIPS's two
/// maps, and for the third-map proposal.
///
/// Not `Clone`: the aborted arm carries a [`SpeculationError`], which wraps
/// f1r3node's `InterpreterError` and `RSpaceError` — neither of which is
/// `Clone`, and neither of which should be made so on this module's account.
/// [`ResumableBranch`] *is* `Clone`, which is the arm a driver actually
/// duplicates (it parks handles and re-explores from them).
#[derive(Debug)]
pub enum BranchOutcome {
    /// `E(S)` is empty: no rendezvous is enabled, nothing further can fire. A
    /// completed evaluation — the FIPS's `success`.
    Quiescent {
        /// The terminal configuration.
        state: SpeculativeState,
        /// The trace that reached it.
        trace: Vec<RendezvousName>,
    },
    /// The step bound ran out while `E(S)` was still non-empty. Neither a
    /// success nor a failure: the evaluation as it stood at exhaustion,
    /// **resumable** up to the remaining token budget.
    Truncated(ResumableBranch),
    /// The reduction raised — `abort`, out of phlogistons, or any other error.
    /// The FIPS's `failure`, whose leaf is the trace with an error code and a
    /// message appended.
    Aborted {
        /// The trace up to the failing step.
        trace: Vec<RendezvousName>,
        /// What went wrong. Classifying this into the FIPS's (code, message)
        /// pair is the `PathMap` stage's job; nothing is discarded here.
        error: SpeculationError,
    },
}

impl BranchOutcome {
    /// The trace this branch made, whatever its outcome.
    pub fn trace(&self) -> &[RendezvousName] {
        match self {
            BranchOutcome::Quiescent { trace, .. } => trace,
            BranchOutcome::Truncated(branch) => &branch.trace,
            BranchOutcome::Aborted { trace, .. } => trace,
        }
    }

    /// The retained configuration, for the two outcomes that have one. An
    /// aborted branch has no well-defined configuration: the failing step may
    /// have mutated the store before raising.
    pub fn state(&self) -> Option<&SpeculativeState> {
        match self {
            BranchOutcome::Quiescent { state, .. } => Some(state),
            BranchOutcome::Truncated(branch) => Some(&branch.state),
            BranchOutcome::Aborted { .. } => None,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// StagedSpace — stage everything, fire nothing
// ══════════════════════════════════════════════════════════════════════════

/// The `ISpace` the sandbox's reducer runs over: `produce` and `consume`
/// **stage** into the hot store and return `Ok(None)`, so no COMM ever fires
/// from inside a reduction. Everything else is delegated verbatim.
///
/// The two staged writes are byte-identical to what an ordinary run leaves
/// behind on its no-match path:
///
/// * `produce` ⇒ `put_datum` with `Produce::create(channel, data, persist)` —
///   `RSpace::store_data`'s body with the same freshly minted source.
/// * `consume` ⇒ `put_continuation` + one `put_join` per channel —
///   `RSpace::store_waiting_continuation`'s body.
///
/// So a staged state is not an approximation of a resting state; it *is* one.
///
/// The counters are the harness's own evidence that a program reached the
/// tuplespace at all: a run that stages nothing has not been suppressed, it has
/// not run.
#[derive(Clone)]
pub struct StagedSpace {
    inner: Space,
    staged_produces: Arc<AtomicUsize>,
    staged_consumes: Arc<AtomicUsize>,
}

impl StagedSpace {
    /// Wrap `inner`. The wrapper shares `inner`'s hot store by `Arc`, so a
    /// caller holding the `RSpace` sees every staged write.
    pub fn new(inner: Space) -> Self {
        StagedSpace {
            inner,
            staged_produces: Arc::new(AtomicUsize::new(0)),
            staged_consumes: Arc::new(AtomicUsize::new(0)),
        }
    }

    /// How many produces have been staged since construction.
    pub fn staged_produces(&self) -> usize {
        self.staged_produces.load(AtomicOrdering::Relaxed)
    }

    /// How many consumes have been staged since construction.
    pub fn staged_consumes(&self) -> usize {
        self.staged_consumes.load(AtomicOrdering::Relaxed)
    }
}

#[async_trait]
impl ISpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> for StagedSpace {
    // ── the two overridden operations ────────────────────────────────────

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
        let waiting =
            WaitingContinuation::create(&channels, &patterns, &continuation, persist, peeks);
        let store = self.inner.get_store();
        let _ = store.put_continuation(&channels, waiting);
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
        // ⚠ Correction 3: this is NOT a faithful readback of a speculative
        // sandbox — see the module header. Delegated so the `ISpace` contract is
        // complete; `SpeculativeSandbox` never calls it.
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
        // NOT staged: `install` is the system-process lane, run once at
        // bootstrap, and it must reach `installed_continuations` (which
        // `put_continuation` does not write) or correction 4 bites immediately.
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
// SpeculativeSandbox
// ══════════════════════════════════════════════════════════════════════════

/// A fresh, empty, in-memory tuplespace and a `RhoRuntime` over it, wired so
/// that **nothing fires until told to**.
///
/// One sandbox holds one configuration at a time. A driver explores by
/// snapshotting a configuration, choosing a rendezvous, firing it, and either
/// continuing in place (Stage 1: one trace) or re-loading a saved configuration
/// into a fresh sandbox (Stage 2: branching).
pub struct SpeculativeSandbox {
    /// The real space. Held separately from the runtime's `StagedSpace` because
    /// `enabled_rendezvous` and `process_match_found` are `RSpace`'s, not
    /// `ISpace`'s — and because the whole point is that the *reducer* cannot
    /// reach them.
    inner: Space,
    /// The staged space the reducer sees. Shares `inner`'s hot store.
    staged: StagedSpace,
    runtime: RhoRuntimeImpl,
    /// ★ Correction 4: the post-bootstrap state, captured once. Every
    /// [`SpeculativeSandbox::load`] layers onto this.
    baseline: SpeculativeState,
}

impl SpeculativeSandbox {
    /// A sandbox with no extra system processes.
    ///
    /// The matcher is [`SubstrateGuardMatcher`] — the same `where`→Dovetail/SFT
    /// decider `run::build_runtime` and `step.rs` install, so a speculative
    /// branch decides a `where` guard exactly as an ordinary reduction does. A
    /// sandbox on f1r3node's bare `Matcher` would be a second guard semantics.
    pub async fn new() -> Result<Self, SpeculationError> {
        Self::with_definitions(Vec::new()).await
    }

    /// A sandbox carrying `definitions` — the Tier-3 fold-contract system
    /// processes a generated language installs. Speculation over a language's
    /// terms needs them for the same reason ordinary execution does.
    pub async fn with_definitions(
        mut definitions: Vec<Definition>,
    ) -> Result<Self, SpeculationError> {
        let mut manager = InMemoryStoreManager::new();
        let store = manager
            .r_space_stores()
            .await
            .map_err(|error| SpeculationError::Bootstrap(format!("in-memory stores: {error:?}")))?;
        let inner = Space::create(store, Arc::new(Box::new(SubstrateGuardMatcher::new())))
            .map_err(|error| SpeculationError::Bootstrap(format!("rspace: {error:?}")))?;
        let staged = StagedSpace::new(inner.clone());

        let runtime = create_rho_runtime(
            staged.clone(),
            Arc::new(HashMap::new()), // mergeable tags: none (single-space speculation)
            false,                    // init_registry: the registry is not part of a sandbox
            &mut definitions,
            ExternalServices::noop(), // inert — a speculative branch calls no external service
        )
        .await;

        // ★★ NO `Cost::unsafe_max()` HERE, and that is the point.
        //
        // `create_rho_runtime` gives the sandbox `CostAccounting::empty_cost()`
        // — a budget of zero — so an unfunded sandbox refuses to evaluate
        // anything. That is the fail-shut direction, and it is what makes an
        // unmetered speculative evaluation unrepresentable rather than merely
        // discouraged. `fund_from` is the only way in, and it draws on the host
        // deploy's remaining phlogiston. See the metering section of the module
        // header.

        // ★ Correction 4: capture AFTER bootstrap, so the installed system
        // continuations are in every state this sandbox ever loads.
        let baseline = inner.get_store().snapshot();

        Ok(SpeculativeSandbox {
            inner,
            staged,
            runtime,
            baseline,
        })
    }

    /// **Fund the sandbox from the host deploy's remaining phlogiston.** The
    /// only way to give a sandbox anything to spend.
    ///
    /// The sandbox's budget is reset from a token carrying (a) the host's
    /// **remaining** units and (b) the host's **signature**, so the speculation
    /// draws on the same tokens and is attributed to the same per-signature lane
    /// the deploy is. It is not a new allocation: whatever the exploration
    /// spends, the caller charges back to the host with
    /// `MeteredMachine::reserve_comm(sandbox.consumed())`, which fails shut with
    /// `OutOfPhlogistonsError` if the deploy cannot afford it.
    ///
    /// An exploration that would run away therefore exhausts the deploy and is
    /// rejected exactly like any other over-budget program — which is why there
    /// is no node budget, no frontier cap, and no new consensus parameter
    /// anywhere in this module.
    ///
    /// Returns what the sandbox was funded with, so a caller can compute the
    /// charge-back without reading the host twice.
    pub fn fund_from(&self, host: &RuntimeBudget) -> Cost {
        let available = host.remaining();
        self.runtime.cost().reset_from_token(&Token::coalesced(
            host.signature(),
            available.value.max(0) as u64,
        ));
        available
    }

    /// Fund the sandbox with an explicit number of units, under the host's
    /// signature — for a caller that wants to cap a single exploration below the
    /// deploy's whole remaining budget (a *self*-imposed cap, not a consensus
    /// parameter: the deploy is still the hard bound, and spending less than it
    /// is always allowed).
    pub fn fund_units(&self, signature: Sig, units: u64) {
        self.runtime
            .cost()
            .reset_from_token(&Token::coalesced(signature, units));
    }

    /// The sandbox's own budget handle — for a caller that needs to read the
    /// deploy-signature lane or the cost trace directly.
    pub fn budget(&self) -> RuntimeBudget {
        self.runtime.cost().clone()
    }

    /// What this sandbox has spent: the consensus consumed cost, i.e. one token
    /// per send and per receive evaluated. This is the amount to charge back to
    /// the host.
    pub fn consumed(&self) -> Cost {
        self.runtime.cost().total_cost()
    }

    /// What this sandbox has left. Zero means the next send or receive it
    /// evaluates will raise `OutOfPhlogistonsError`.
    pub fn remaining(&self) -> Cost {
        self.runtime.cost().remaining()
    }

    /// The post-bootstrap state: the system processes and nothing else. The base
    /// every speculative configuration is layered onto.
    pub fn baseline(&self) -> &SpeculativeState {
        &self.baseline
    }

    /// The sandbox's current configuration, read with `snapshot()` (correction 3
    /// — never `to_map()`).
    pub fn snapshot(&self) -> SpeculativeState {
        self.inner.get_store().snapshot()
    }

    /// The staged space, for a caller that wants the staging counters.
    pub fn staged(&self) -> &StagedSpace {
        &self.staged
    }

    /// Install `state` exactly, layering the bootstrap installs (correction 4)
    /// underneath whatever `state` carries.
    ///
    /// A state produced by [`SpeculativeSandbox::snapshot`] already carries them,
    /// so re-loading a snapshot is idempotent; a hand-built state does not, and
    /// would otherwise lose `stdout!` and every other system process.
    ///
    /// Exactness rests on the sandbox being FRESH: `revert_to_soft_checkpoint`
    /// re-attaches the cold history layer at `history.root()`, and only a space
    /// on which `create_checkpoint` was never called has the empty root
    /// invariantly. `SpeculativeSandbox` never calls `create_checkpoint`.
    /// Pinned by `tests/x3_exact_state_install.rs`.
    pub async fn load(&self, state: SpeculativeState) -> Result<(), SpeculationError> {
        self.inner
            .revert_to_soft_checkpoint(SoftCheckpoint {
                cache_snapshot: self.rebase(state),
                log: Vec::new(),
                produce_counter: BTreeMap::new(),
            })
            .await?;
        Ok(())
    }

    /// `state` with the bootstrap installs restored under it. Entries `state`
    /// already carries win, so a snapshot round-trips unchanged.
    pub fn rebase(&self, mut state: SpeculativeState) -> SpeculativeState {
        for (channels, installed) in self.baseline.installed_continuations.iter() {
            state
                .installed_continuations
                .entry(channels.clone())
                .or_insert_with(|| installed.clone());
        }
        for (channel, joins) in self.baseline.installed_joins.iter() {
            state
                .installed_joins
                .entry(channel.clone())
                .or_insert_with(|| joins.clone());
        }
        state
    }

    /// Reduce `par` to **administrative quiescence** under `rand`: `new`,
    /// `match`, arithmetic, methods, `|` fan-out, substitution, and the
    /// *installation* of every send and receive it reaches. No COMM fires.
    ///
    /// ★ `rand` is the caller's, and on chain it must derive from the **deploy's**
    /// randomness — never from a fixture constant. Two validators speculating
    /// over the same deploy have to mint the same unforgeable names, and a name
    /// is minted from the split of the seed at a positional index. (That the
    /// split is positional rather than task-order dependent is measured:
    /// `Reduce::eval_par` computes `split(index, …)` eagerly, before any future
    /// is polled, and five runs of a 16-wide `new` fan on eight worker threads
    /// are byte-identical — `x1_stratified_monotonicity.rs::r1`.)
    pub async fn saturate(
        &self,
        par: Par,
        rand: Blake2b512Random,
    ) -> Result<(), SpeculationError> {
        self.runtime.inj(par, Env::new(), rand).await?;
        Ok(())
    }

    /// `E(S)` — every rendezvous the current configuration admits, in
    /// f1r3node's own deterministic enumeration order.
    ///
    /// Read-only: no store mutation, no event, no produce-counter movement
    /// (pinned by `rspace++/tests/enabled_rendezvous_spec.rs::t3`). The count is
    /// known before any of it is materialised, which is what lets a Stage 2
    /// driver preallocate its frontier.
    ///
    /// ⚠ `enabled()[0]` is what a `consume` ARRIVING at this state would take —
    /// **not** what an ordinary run does. See correction 1.
    pub fn enabled(&self) -> Vec<Rendezvous> {
        self.inner.enabled_rendezvous()
    }

    /// `E(S)`, named. Convenience for a driver building a trace.
    pub fn enabled_names(&self) -> Vec<RendezvousName> {
        let enabled = self.enabled();
        let mut names = Vec::with_capacity(enabled.len());
        names.extend(enabled.iter().map(RendezvousName::of));
        names
    }

    /// Fire exactly the rendezvous `rendezvous` **names**, then run the
    /// resulting configuration to administrative quiescence.
    ///
    /// Three things happen, in this order:
    ///
    /// 1. **The store mutation and the COMM event**, inside f1r3node's own
    ///    `RSpace::process_match_found`: the selected data are removed by store
    ///    index (highest first, so a receive taking two data from one channel
    ///    does not shift an index out from under itself), the continuation is
    ///    removed unless it is persistent, the joins are dropped, and the `COMM`
    ///    is appended to the event log.
    /// 2. **The dispatch**, which is also the saturation: the continuation body
    ///    is evaluated with the matched data bound, and everything it reaches
    ///    stages. It returns at quiescence.
    /// 3. **The peek restore** (correction 2), if the fired continuation was a
    ///    peek: each non-persistent selected datum is re-produced through the
    ///    ordinary `produce` path, so it comes back carrying a freshly minted
    ///    `Produce` source exactly as `Reduce::produce_peeks` gives it.
    ///
    /// Steps 2 and 3 are f1r3node's parallel detached siblings, and their order
    /// is immaterial here: under staging both terminate in the store rather than
    /// in a rendezvous, and `E(S)` is only computed at quiescence, so no
    /// intermediate configuration is observable. Keeping them as two named steps
    /// is what will let Stage 2 treat the restore as its own branch point.
    ///
    /// Returns [`SpeculationError::NotFired`] if the rendezvous does not address
    /// this configuration — a stale index, or one enumerated against a different
    /// state.
    pub async fn fire(&self, rendezvous: Rendezvous) -> Result<FiredStep, SpeculationError> {
        let name = RendezvousName::of(&rendezvous);
        let persistent = rendezvous.continuation.persist;
        let peek = !rendezvous.continuation.peeks.is_empty();

        // (1) mutate + log, in f1r3node.
        let (continuation, results) = self
            .inner
            .process_match_found(rendezvous)
            .ok_or(SpeculationError::NotFired)?;

        let mut payloads = Vec::with_capacity(results.len());
        payloads.extend(results.iter().map(|result| result.matched_datum.clone()));

        // (2) dispatch, which saturates.
        let system_process = self.dispatch(continuation.continuation, payloads).await?;

        // (3) the peek restore — the second stratum.
        let peek_restores = match peek {
            true => self.stage_peek_restores(&results).await?,
            false => 0,
        };

        Ok(FiredStep {
            name,
            persistent,
            peek,
            peek_restores,
            system_process,
        })
    }

    /// Resume a truncated branch: install its retained configuration and hand
    /// back the trace that produced it, so a driver can continue appending to
    /// the same trace.
    ///
    /// Resumption is bounded by the sandbox's remaining token budget and by
    /// nothing else. Because the handle carries the whole `HotStoreState`, the
    /// resumed branch mints the same unforgeable names the truncated one would
    /// have: every datum's `Blake2b512Random` and every continuation's source
    /// survive the round trip, which a reified process could not have preserved.
    pub async fn resume(
        &self,
        branch: ResumableBranch,
    ) -> Result<Vec<RendezvousName>, SpeculationError> {
        self.load(branch.state).await?;
        Ok(branch.trace)
    }

    /// Drive ONE trace for at most `steps` stratified steps, letting `choose`
    /// pick a member of `E(S)` at each fork.
    ///
    /// Branching is pinned to 1 by construction: `choose` returns one index, so
    /// exactly one successor is explored. A Stage 2 search drives this once per
    /// branch, parking each [`BranchOutcome::Truncated`] handle and resuming the
    /// ones it keeps.
    ///
    /// `choose` receives the whole of `E(S)` and returns an index into it. An
    /// index out of range is a caller bug and is reported as
    /// [`SpeculationError::NotFired`] rather than silently clamped, because
    /// clamping would substitute a different rendezvous for the one named.
    ///
    /// The three outcomes are exactly the module header's table:
    /// empty `E(S)` ⇒ quiescent, `steps` exhausted with `E(S)` non-empty ⇒
    /// truncated and resumable, an error ⇒ aborted. Running out of phlogistons
    /// arrives as an abort, which is correct: the deploy could not afford the
    /// exploration.
    pub async fn run_trace(
        &self,
        steps: usize,
        mut choose: impl FnMut(&[Rendezvous]) -> usize,
    ) -> BranchOutcome {
        let mut trace: Vec<RendezvousName> = Vec::with_capacity(steps);
        for _ in 0..steps {
            let enabled = self.enabled();
            if enabled.is_empty() {
                return BranchOutcome::Quiescent {
                    state: self.snapshot(),
                    trace,
                };
            }
            let index = choose(&enabled);
            if index >= enabled.len() {
                return BranchOutcome::Aborted {
                    trace,
                    error: SpeculationError::NotFired,
                };
            }
            match self.fire(enabled[index].clone()).await {
                Ok(step) => trace.push(step.name),
                Err(error) => return BranchOutcome::Aborted { trace, error },
            }
        }

        // The bound ran out. Quiescent or truncated is decided by whether
        // anything is still enabled — NOT by whether the bound was reached, so a
        // branch that happens to finish on its last allotted step is reported as
        // the completed evaluation it is.
        let frontier = self.enabled().len();
        let state = self.snapshot();
        match frontier {
            0 => BranchOutcome::Quiescent { state, trace },
            _ => BranchOutcome::Truncated(ResumableBranch {
                state,
                trace,
                frontier,
            }),
        }
    }

    /// Restore the data a peek's COMM removed, as `Reduce::produce_peeks` does:
    /// one fresh, non-persistent `produce` of the **removed** payload per
    /// non-persistent selected datum.
    ///
    /// The restored datum is NOT the one that left. Its `Produce` source is
    /// minted anew from (channel, payload, persistence), which is why a peek is
    /// two strata rather than a read: a trace that names the pre-peek datum does
    /// not name the post-peek one, even though they carry the same payload.
    ///
    /// Returns how many were restored. Public and separately callable so a Stage
    /// 2 driver can treat the restore as its own branch point.
    pub async fn stage_peek_restores(
        &self,
        results: &[rspace_plus_plus::rspace::rspace_interface::RSpaceResult<
            Par,
            ListParWithRandom,
        >],
    ) -> Result<usize, SpeculationError> {
        let mut restored = 0usize;
        for result in results.iter().filter(|result| !result.persistent) {
            self.staged
                .produce(
                    result.channel.clone(),
                    result.removed_datum.clone(),
                    false,
                )
                .await?;
            restored += 1;
        }
        Ok(restored)
    }

    /// Evaluate a fired continuation. Returns whether it was a system process.
    ///
    /// See the module header for why this is spelled out rather than delegated
    /// to `Reduce::continue_consume_process`, and why the `ParBody` arm uses
    /// `eval` where `RholangAndScalaDispatcher::dispatch` uses `eval_with_path`.
    async fn dispatch(
        &self,
        continuation: TaggedContinuation,
        payloads: Vec<ListParWithRandom>,
    ) -> Result<bool, SpeculationError> {
        match &continuation.tagged_cont {
            Some(TaggedCont::ParBody(body_with_random)) => {
                // `dispatch.rs`'s `ParBody` arm, verbatim except for `eval`.
                let environment = build_env(payloads.clone());
                let mut randoms = Vec::with_capacity(payloads.len() + 1);
                randoms.push(Blake2b512Random::from_bytes(&body_with_random.random_state));
                randoms.extend(
                    payloads
                        .iter()
                        .map(|payload| Blake2b512Random::from_bytes(&payload.random_state)),
                );
                let body = body_with_random.body.clone().unwrap_or_default();
                self.runtime
                    .reducer
                    .eval(body, &environment, Blake2b512Random::merge(randoms))
                    .await?;
                Ok(false)
            }
            Some(TaggedCont::ScalaBodyRef(_)) => {
                // A system process. The dispatch table's functions are plain
                // async fns — they do not spawn onto a completion driver — so
                // this arm is reached through f1r3node's dispatcher unchanged.
                // `path` is display-only and is ignored on this arm.
                self.runtime
                    .reducer
                    .dispatcher
                    // The reduction coordinate is display-only and is ignored
                    // on this arm. Spelled `Default::default()` rather than
                    // `SmallVec::new()` so this crate does not need a
                    // `smallvec` dependency of its own — the type comes from
                    // f1r3node's signature, which is the only place it should
                    // be pinned.
                    .dispatch(
                        continuation.clone(),
                        payloads,
                        false,
                        Vec::new(),
                        Default::default(),
                    )
                    .await?;
                Ok(true)
            }
            // `TaggedContinuation { tagged_cont: None }` is `dispatch`'s `Skip`.
            None => Ok(false),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// State comparison
// ══════════════════════════════════════════════════════════════════════════

/// `state` with every empty entry dropped.
///
/// ★ A read materialises an entry: `HotStore::get_data` on a channel with no
/// data inserts an empty vector (the history-fill path), and
/// `remove_matched_datum_and_join` leaves an empty joins vector behind. So the
/// **number of channels** in a `HotStoreState` is not a meaningful observable —
/// two configurations that differ only in which channels have been *looked at*
/// are the same configuration.
///
/// Every comparison of two configurations must canonicalise first. This is that
/// canonicalisation: drop empty `data`, `continuations`, `joins` and
/// `installed_joins` entries. `installed_continuations` holds a single
/// continuation per key rather than a vector and cannot be empty.
pub fn canonicalize(state: &SpeculativeState) -> SpeculativeState {
    let mut canonical = SpeculativeState::default();
    canonical.data.reserve(state.data.len());
    for (channel, data) in state.data.iter() {
        if !data.is_empty() {
            canonical.data.insert(channel.clone(), data.clone());
        }
    }
    canonical.continuations.reserve(state.continuations.len());
    for (channels, continuations) in state.continuations.iter() {
        if !continuations.is_empty() {
            canonical
                .continuations
                .insert(channels.clone(), continuations.clone());
        }
    }
    canonical.joins.reserve(state.joins.len());
    for (channel, joins) in state.joins.iter() {
        if !joins.is_empty() {
            canonical.joins.insert(channel.clone(), joins.clone());
        }
    }
    canonical.installed_joins.reserve(state.installed_joins.len());
    for (channel, joins) in state.installed_joins.iter() {
        if !joins.is_empty() {
            canonical
                .installed_joins
                .insert(channel.clone(), joins.clone());
        }
    }
    canonical.installed_continuations = state.installed_continuations.clone();
    canonical
}

/// A stable, order-independent fingerprint of a configuration's **program
/// content** — the data resting on each channel and the continuations waiting on
/// each channel group, keyed by content hash.
///
/// This is the observable two configurations are compared on. It is built from
/// content hashes (`Datum::source`, `WaitingContinuation::source`) rather than
/// from encoded `Par`s, so it is exactly as discriminating as the tuplespace's
/// own identity notion and no more; and it is sorted, so `HashMap` iteration
/// order cannot leak into a comparison.
///
/// Installed (system) continuations are excluded: they are the runtime's, not
/// the program's, and they are identical in every sandbox by construction
/// (correction 4).
pub fn content_fingerprint(state: &SpeculativeState) -> Vec<String> {
    let canonical = canonicalize(state);
    let mut lines: Vec<String> =
        Vec::with_capacity(canonical.data.len() + canonical.continuations.len());

    for (channel, data) in canonical.data.iter() {
        let mut sources: Vec<String> = Vec::with_capacity(data.len());
        sources.extend(data.iter().map(|datum| {
            format!(
                "{}:{}",
                hex(&datum.source.hash.bytes()),
                match datum.persist {
                    true => "persistent",
                    false => "linear",
                }
            )
        }));
        sources.sort();
        lines.push(format!(
            "data {} => [{}]",
            hex(&Blake2b256Hash::new(&prost_bytes(channel)).bytes()),
            sources.join(", ")
        ));
    }

    for (channels, continuations) in canonical.continuations.iter() {
        let mut sources: Vec<String> = Vec::with_capacity(continuations.len());
        sources.extend(continuations.iter().map(|waiting| {
            format!(
                "{}:{}{}",
                hex(&waiting.source.hash.bytes()),
                match waiting.persist {
                    true => "persistent",
                    false => "linear",
                },
                match waiting.peeks.is_empty() {
                    true => "",
                    false => "+peek",
                }
            )
        }));
        sources.sort();
        let mut group: Vec<String> = Vec::with_capacity(channels.len());
        group.extend(
            channels
                .iter()
                .map(|channel| hex(&Blake2b256Hash::new(&prost_bytes(channel)).bytes())),
        );
        lines.push(format!(
            "cont [{}] => [{}]",
            group.join(" & "),
            sources.join(", ")
        ));
    }

    lines.sort();
    lines
}

fn prost_bytes(par: &Par) -> Vec<u8> {
    use prost::Message;
    par.encode_to_vec()
}

fn hex(bytes: &[u8]) -> String {
    let mut rendered = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        rendered.push_str(&format!("{byte:02x}"));
    }
    rendered
}
