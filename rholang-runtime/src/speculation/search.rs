//! # Stage 2 — the branching engine: BFS over `E(S)`
//!
//! Stage 1 gave the mechanism with **branching pinned to 1**: one sandbox, one
//! trace, one rendezvous fired per step. This module removes the pin. It is the
//! search — the thing that makes `[*]` mean *all* execution paths rather than
//! *one*.
//!
//! ## The reduction graph, and why breadth first
//!
//! Stratification (see the [`super`] module header) makes a speculative
//! execution a walk on a directed graph:
//!
//! ```text
//!                     ┌───────────────────────┐
//!                     │  S₀  (root: `P`       │
//!                     │      saturated)       │
//!                     └───────────┬───────────┘
//!                     E(S₀) = { r₀ , r₁ }
//!                    ┌────────────┴────────────┐
//!                    ▼                         ▼
//!            ┌───────────────┐         ┌───────────────┐
//!            │  S₁ = r₀(S₀)  │         │  S₂ = r₁(S₀)  │
//!            └───────┬───────┘         └───────┬───────┘
//!             E(S₁)={r₁}                 E(S₂)={r₀}
//!                    ▼                         ▼
//!            ┌───────────────┐         ┌───────────────┐
//!            │  S₃           │  ═════  │  S₃           │   ← the DIAMOND:
//!            └───────────────┘  equal  └───────────────┘     two traces, one
//!                                                            configuration
//! ```
//!
//! * **Nodes** are configurations — `HotStoreState`s at administrative
//!   quiescence.
//! * **Edges** are enabled rendezvous, and an edge is *named* by
//!   [`RendezvousName`] (correction 1: the least element of `E(S)` is not the
//!   branch an ordinary run takes, so a trace must name its selection and never
//!   assume an index).
//! * **A trace** is the sequence of edge names from the root.
//!
//! The search is **breadth first** because the depth bound `n` of `x!(P)[n]` is
//! a bound on *trace length*: a BFS level is exactly the set of configurations
//! reachable in `k` steps, so the bound is enforced by counting levels rather
//! than by pruning inside a recursion, and every truncated leaf is truncated at
//! the same depth. A depth-first search would have to carry the bound down every
//! spine and would deliver the leaves of the first spine before discovering that
//! a shallower branch had already finished — the wrong order for beam search,
//! which wants *all* the depth-`k` leaves before it ranks them.
//!
//! The frontier is explicit and **preallocated**: `|E(S)|` is known before any
//! child is materialised (the enumeration returns a `Vec`), so each node
//! reserves exactly its out-degree before pushing.
//!
//! ## Firing a sibling: re-install, re-enumerate, verify the name
//!
//! One sandbox holds one configuration, so exploring the `i`-th child of a node
//! means putting the node's configuration back:
//!
//! ```text
//!   load(S) ─▶ enumerate E(S) ─▶ fire E(S)[0] ─▶ snapshot ─▶ child₀
//!   load(S) ─▶ enumerate E(S) ─▶ fire E(S)[1] ─▶ snapshot ─▶ child₁
//!   …
//! ```
//!
//! Re-enumerating rather than reusing the first enumeration's `Vec` is
//! deliberate. A [`Rendezvous`] carries **store indices**, and firing addresses
//! the store by them; reusing a rendezvous enumerated against a *different*
//! store instance would be exactly the stale-index bug
//! [`SpeculationError::NotFired`] exists to catch. Re-enumeration is safe
//! because the enumeration is deterministic — three composed total orders,
//! pinned by `rspace++/tests/enabled_rendezvous_spec.rs::t4` over permuted
//! insertion orders and ten repetitions — and this module does not *assume*
//! that: [`Explorer`] compares the re-enumerated name against the name it
//! recorded at planning time and reports [`SpeculationError::NotFired`] if they
//! differ, so a determinism regression in f1r3node surfaces here as a failure
//! rather than as a silently different exploration.
//!
//! ## ★ Three outcomes, three maps
//!
//! | outcome | when | map |
//! |---|---|---|
//! | [`BranchOutcome::Quiescent`] | `E(S)` is empty | `success` |
//! | [`BranchOutcome::Truncated`] | the depth bound ran out with `E(S)` non-empty | `truncated` (the **third** map) |
//! | [`BranchOutcome::Aborted`] | the reduction raised — `abort`, out of phlogistons, `^drive-err`, `^drive-fuel` | `failure` |
//!
//! Truncation is decided by `E(S)`, never by "the bound was reached": a branch
//! that happens to finish on its last allotted step is the completed evaluation
//! it is. A truncated leaf is a [`ResumableBranch`] — the retained configuration
//! plus its trace — and [`Explorer::resume`] continues from it, bounded by the
//! remaining token budget and nothing else. That is beam search stated
//! literally.
//!
//! ## ★ Trace mode: every trace, or every configuration
//!
//! Both are implemented, because they answer different questions and the FIPS
//! and the use cases pull in different directions.
//!
//! [`TraceMode::EveryTrace`] is the FIPS read verbatim — *"for each possible
//! trace `t` of length `n` a new, empty RSpace `empty_t` will be created"*. It
//! is a **tree** search: the diamond above yields two entries whose leaves are
//! equal and whose traces differ. It is the right answer when the trace itself
//! is the object of interest (a scheduling audit, a replay differential), and it
//! is the only mode that reproduces the FIPS's entry *count*.
//!
//! [`TraceMode::DistinctConfigurations`] is the **graph** search: a
//! configuration already reached is not expanded again, and the trace retained
//! is the first (hence, under BFS, a shortest) one that reached it. It answers
//! *"what outcomes are possible?"*, which is what all four FIPS use cases
//! actually ask — MeTTaIL theories, dynamically-instantiated lambdas,
//! confinement and beam search all rank or inspect *results*.
//!
//! Merging is **sound**: a configuration determines its own `E(S)` and hence its
//! entire future, so two branches that meet have identical continuations and
//! merging discards no reachable leaf. It discards only alternative trace
//! *labels* — which is precisely what distinguishes graph search from tree
//! search — and the number discarded is reported as
//! [`ExplorationStats::merged_configurations`] rather than left invisible.
//!
//! The distinction is not academic. A confluent guest with `k` independent
//! redexes has `k!` traces and one normal form: λ-calculus is confluent, so
//! `[*]` over a λ term has a **singleton** distinct-configuration success set —
//! by mathematics, not by limitation — while its every-trace success set has
//! `k!` entries carrying the same leaf `k!` times. A non-confluent guest
//! separates: Ambient's open race
//! `{ open(n, a[0]) | n[b[0]] | open(n, c[0]) }` has **two** normal forms and
//! both modes find two.
//!
//! Configurations are compared by [`super::content_fingerprint`] — content
//! hashes, sorted, with empty entries canonicalised away, and installed (system)
//! continuations excluded. It is *not* `Term::term_id()` / `exact_key`: parsing
//! the same source twice mints different moniker gensyms, so a syntactic key
//! would report two identical states as distinct.
//!
//! ## ★★ Metering is the bound — and it is the ONLY bound
//!
//! There is no node budget, no frontier cap, no new consensus parameter, and
//! nothing in this module owns a budget. The sandbox is funded from the host
//! deploy's remaining phlogiston ([`SpeculativeSandbox::fund_from`]); every
//! administrative saturation and every fired continuation body passes through
//! f1r3node's `MeteredMachine::reserve_comm`; an exploration that would run away
//! exhausts the deploy and its branches arrive as
//! [`BranchOutcome::Aborted`] one by one until the frontier empties. That is the
//! termination argument for [`Lookahead::Unbounded`]: it is not "assume the
//! guest terminates", it is "the deploy's budget is finite and every step spends
//! from it".
//!
//! ⚠ A budget unit is **one COMM**, not one unit of `Cost.value`:
//! `reserve_comm(amount)` charges one regardless of `amount`. So
//! [`SpeculativeSandbox::consumed`] is a COMM **count** and charging it back to
//! the host is `consumed()` *calls* to `reserve_comm` —
//! [`Explorer::charge_host`] does exactly that, and exists so no caller has to
//! rediscover it (Stage 1's own test measured the host charged 1 where 5 was
//! owed before this was understood).
//!
//! ## What this module deliberately does NOT do
//!
//! It does not build a `Par`. Turning an [`Exploration`] into the three
//! collections a receiving program reads is [`super::delivery`], because the
//! shape of a leaf is a decision about the *surface* and the search must not
//! depend on it.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::Par;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::metering::MeteredMachine;

use rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash;

use super::{
    content_fingerprint, Rendezvous, RendezvousName, ResumableBranch, SpeculationError,
    SpeculativeSandbox, SpeculativeState,
};

// ══════════════════════════════════════════════════════════════════════════
// The bracket: `[n]` and `[*]`
// ══════════════════════════════════════════════════════════════════════════

/// The bracket of `x!(P)[n]` — a **first-class mode**, not a special case of
/// unbounded search.
///
/// The FIPS gives `n` as *"either a uint64 or an asterisk `*`"* and says the
/// feature *"is isomorphic to the current semantics when `n = 0`"*: with zero
/// steps no COMM fires, so the single leaf is `P` administratively saturated —
/// exactly what an ordinary `x!(P)` leaves behind — and it is reported
/// [`BranchOutcome::Truncated`] if anything was still enabled, which is the
/// honest statement that a normal form was not reached.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lookahead {
    /// `x!(P)[n]` — at most `n` stratified steps along every path. A `u64`
    /// because that is the FIPS's own type for the bracket.
    Steps(u64),
    /// `x!(P)[*]` — every path to quiescence. Bounded by metering and by
    /// nothing else.
    Unbounded,
}

impl Lookahead {
    /// Whether a branch that has already fired `depth` steps may fire another.
    fn admits(&self, depth: u64) -> bool {
        match self {
            Lookahead::Steps(bound) => depth < *bound,
            Lookahead::Unbounded => true,
        }
    }

    /// The bound as a capacity hint for the trace vector: the FIPS's `n`, or a
    /// small non-zero start for `[*]` (whose length is not known in advance).
    fn trace_capacity(&self) -> usize {
        match self {
            // A `u64` bound may exceed `usize`; a capacity hint must never be
            // the reason an exploration allocates the whole address space, so
            // the hint is clamped. Correctness does not depend on it — a `Vec`
            // grows.
            Lookahead::Steps(bound) => (*bound).min(64) as usize,
            Lookahead::Unbounded => 8,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Trace mode
// ══════════════════════════════════════════════════════════════════════════

/// Whether the search enumerates **traces** (a tree), **configurations** (a
/// graph), or **Mazurkiewicz trace classes** (a graph with partial-order
/// reduction). See the module header for why all three exist and why each
/// reduction is sound.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum TraceMode {
    /// Graph search **plus partial-order reduction**: independent rendezvous are
    /// explored in one order only, because firing them in either order reaches
    /// the same configuration. The default, and the only mode in which a
    /// concurrent guest is tractable at all.
    #[default]
    IndependenceReduced,
    /// Graph search: a configuration reached before is not expanded again, and
    /// the retained trace is the first (shortest, under BFS) that reached it.
    /// Every interleaving of every independent pair is still walked, so the
    /// reachable-state count is exponential in the concurrency width.
    DistinctConfigurations,
    /// Tree search: every distinct sequence of choices is its own branch, even
    /// when two sequences meet. The FIPS's *"for each possible trace `t`"*
    /// verbatim, and factorial in the concurrency width.
    EveryTrace,
}

impl TraceMode {
    /// Whether a configuration reached before is skipped.
    fn merges(&self) -> bool {
        !matches!(self, TraceMode::EveryTrace)
    }

    /// Whether independent rendezvous are explored in one order only.
    fn reduces(&self) -> bool {
        matches!(self, TraceMode::IndependenceReduced)
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Independence — the partial order the reduction is over
// ══════════════════════════════════════════════════════════════════════════

/// One **resource** a rendezvous consumes.
///
/// A rendezvous conflicts with another exactly when they compete for a
/// resource, and a resource is something a firing *removes*: the continuation
/// (unless it is persistent — a persistent continuation is not removed and two
/// rendezvous may both fire it) and each selected datum (unless it is
/// persistent, for the same reason).
///
/// Identified by **content hash**, never by store index: `process_match_found`
/// removes data by index highest-first, so firing one rendezvous renumbers the
/// data after it and an index-keyed resource would name a different datum in the
/// successor. Content hashes are stable across the firing.
///
/// ⚠ Two byte-identical sends on one channel share a `Produce` hash, so they are
/// treated as ONE resource. That over-approximates conflict — the search then
/// explores both orders where one would have done — and over-approximating
/// conflict is the safe direction: it costs work, never coverage.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Resource {
    /// A linear continuation, by its `Consume` content hash.
    Continuation(Blake2b256Hash),
    /// A linear datum, by its `Produce` content hash.
    Datum(Blake2b256Hash),
}

/// The resources a rendezvous removes. Empty for a rendezvous that removes
/// nothing at all (a persistent continuation consuming persistent data), which
/// is independent of everything — correctly, since firing it changes no other
/// rendezvous's availability.
fn resources(rendezvous: &Rendezvous) -> BTreeSet<Resource> {
    let mut set = BTreeSet::new();
    if !rendezvous.continuation.persist {
        set.insert(Resource::Continuation(
            rendezvous.continuation.source.hash.clone(),
        ));
    }
    for candidate in rendezvous.data_candidates.iter() {
        // ⚠ A PEEK removes its datum too — `store_persistent_data` ignores its
        // `_peeks` argument — and the reducer puts it back with a FRESH produce
        // as a separate stratum. So a peeked datum IS a consumed resource, and
        // treating it as one is what keeps the two strata of a peek from being
        // reordered against a competing consume.
        if !candidate.datum.persist {
            set.insert(Resource::Datum(candidate.datum.source.hash.clone()));
        }
    }
    set
}

/// **The independence relation.** Two rendezvous are independent when they
/// compete for no resource.
///
/// The diamond this licenses: if `r₁ ⊥ r₂` then both remain enabled after either
/// fires (neither touched the other's resources), the two firings remove
/// disjoint sets and dispatch bodies that are functions of their own
/// continuation and their own matched data alone, so `r₁(r₂(S))` and `r₂(r₁(S))`
/// agree on every datum, every continuation and every randomness — up to the
/// *position* a newly staged datum takes within its channel, which
/// [`content_fingerprint`] sorts away because a channel holds a multiset.
///
/// This is the standard Mazurkiewicz independence of concurrency theory, read
/// off the tuplespace's own notion of what a COMM consumes.
pub fn independent(left: &Rendezvous, right: &Rendezvous) -> bool {
    resources(left).is_disjoint(&resources(right))
}

/// The **conflict class** of `E(S)[0]` — the persistent set the reduction
/// expands.
///
/// `resource_sets` is `E(S)`'s resource sets in enumeration order. The returned
/// indices are the connected component of index 0 in the conflict graph
/// (`i ~ j` iff their resource sets intersect), computed by closure so that
/// conflict is treated as the transitive relation it is: if `r₀` conflicts with
/// `r₁` and `r₁` with `r₂` then all three are one choice, even though `r₀` and
/// `r₂` are disjoint.
///
/// ## Why a class, and why this is sound
///
/// Two **independent** rendezvous are not alternatives — they are both going to
/// happen, and the order in which they do is not a decision the program makes.
/// A *choice* exists only where two rendezvous compete, so the branch factor of
/// a stratified step is the size of a conflict class, never `|E(S)|`.
///
/// Expanding only this class postpones every other class. That loses nothing:
/// a postponed rendezvous `r` is independent of everything expanded in the
/// meantime, so it stays enabled, and firing it later reaches exactly the
/// configuration firing it earlier would have reached — that is the commutation
/// [`independent`] establishes. If something that conflicts with `r` is created
/// later, `r` and its new competitor land in one class and the search branches
/// over them then; the branch in which `r` fires is still taken, and by
/// commutation it reaches the same configuration as the branch in which `r`
/// fired before the competitor existed.
///
/// Determinism: the class of `E(S)[0]` is a function of the enumeration alone,
/// and the enumeration is f1r3node's own total order, so two validators expand
/// the same class.
///
/// ⚠ This is what makes a real concurrent guest tractable, and the numbers say
/// so. Measured on the production `Ambient` in-Rho quiescence driver: **every**
/// rendezvous it ever enables is the same *persistent* dispatcher continuation
/// taking a *distinct* datum, so every pair is independent, every class is a
/// singleton, and the reduction turns a subset lattice into a line. Without it
/// the frontier grew 1 → 2 → 5 → 12 → 25 → 49 → 93 → 169 → 291 → 479 → 754 →
/// 1130 and climbing, over a program whose reduction is deterministic.
fn conflict_class(resource_sets: &[BTreeSet<Resource>]) -> Vec<usize> {
    let mut class = vec![0usize];
    let mut claimed = vec![false; resource_sets.len()];
    claimed[0] = true;
    let mut frontier = vec![0usize];
    while let Some(current) = frontier.pop() {
        for candidate in 0..resource_sets.len() {
            if claimed[candidate] {
                continue;
            }
            if !resource_sets[current].is_disjoint(&resource_sets[candidate]) {
                claimed[candidate] = true;
                class.push(candidate);
                frontier.push(candidate);
            }
        }
    }
    class.sort_unstable();
    class
}

// ══════════════════════════════════════════════════════════════════════════
// Leaves
// ══════════════════════════════════════════════════════════════════════════

/// A branch that reached **quiescence**: nothing further can fire. The FIPS's
/// `success`.
#[derive(Clone, Debug)]
pub struct QuiescentLeaf {
    /// The sequence of named selections that reached it.
    pub trace: Vec<RendezvousName>,
    /// The terminal configuration.
    pub state: SpeculativeState,
}

/// A branch the depth bound cut short with `E(S)` still non-empty — **neither**
/// a success nor a failure, and resumable.
#[derive(Clone, Debug)]
pub struct TruncatedLeaf {
    /// The retained configuration, its trace, and `|E(S)|` at the cut.
    pub branch: ResumableBranch,
}

impl TruncatedLeaf {
    /// The trace that reached the cut.
    pub fn trace(&self) -> &[RendezvousName] {
        &self.branch.trace
    }
}

/// A branch that raised. The FIPS's `failure`, whose leaf is *"an extra
/// two-element list containing an error code for the failure and a message"*.
#[derive(Clone, Debug)]
pub struct AbortedLeaf {
    /// The trace up to the failing step.
    pub trace: Vec<RendezvousName>,
    /// The FIPS error code. See [`ErrorCode`].
    pub code: ErrorCode,
    /// The FIPS message — f1r3node's own rendering of the error, never a
    /// re-worded one, so a reader can find the raising site.
    pub message: String,
}

/// The FIPS `failure` leaf's **error code**: a small, stable, total
/// classification of everything a speculative branch can raise.
///
/// Stable because it is a consensus-visible value once `[*]` is on chain — two
/// validators must place the same branch in the same `failure` entry — so the
/// discriminants are written out and are append-only.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(i64)]
pub enum ErrorCode {
    /// The deploy could not afford the exploration:
    /// `InterpreterError::OutOfPhlogistonsError`. Split out from every other
    /// interpreter error because it is the one failure that is a statement
    /// about the *budget* rather than about the program, and because it is the
    /// failure metering-as-the-bound is expected to produce.
    OutOfPhlogistons = 1,
    /// The program called `abort`: `InterpreterError::UserAbortError`.
    UserAbort = 2,
    /// Any other reducer refusal.
    Interpreter = 3,
    /// The tuplespace refused an operation.
    Tuplespace = 4,
    /// A named rendezvous did not address the configuration it was enumerated
    /// against — a stale index, or an f1r3node enumeration-determinism
    /// regression. An internal inconsistency rather than a program error, and
    /// coded separately so it cannot hide among program failures.
    NotFired = 5,
    /// The sandbox could not be built.
    Bootstrap = 6,
    /// ★ The branch reached tuplespace quiescence, but the **guest's own
    /// evaluator** refused the subject along it: the in-Rho quiescence driver
    /// rested a typed diagnostic on its `^drive-err:{fingerprint}` channel
    /// (an unrecognized driven head).
    ///
    /// Distinct from [`ErrorCode::Interpreter`], which is the *reducer*
    /// refusing a term. Here the reducer was content — nothing raised, `E(S)`
    /// simply emptied — and the branch nevertheless computed no answer. Without
    /// this code such a branch would deliver an empty projection and be
    /// indistinguishable from a branch that legitimately published nothing,
    /// which is the silence the whole fail-closed design exists to prevent.
    GuestEvaluatorRefused = 7,
    /// ★ The branch reached tuplespace quiescence with the guest's evaluator
    /// **out of per-path fuel**: the driver rested the stuck redex on its
    /// `^drive-fuel:{fingerprint}` channel. Ω under `[*]` is this.
    ///
    /// Separate from [`ErrorCode::GuestEvaluatorRefused`] for the same reason
    /// truncation is separate from failure: *"I could not reduce this"* and
    /// *"I stopped before finishing"* are different facts and a consumer must
    /// be able to tell them apart.
    GuestEvaluatorExhausted = 8,
}

impl ErrorCode {
    /// The wire value — what the `failure` leaf's first element carries.
    pub fn as_i64(self) -> i64 {
        self as i64
    }

    /// Classify a [`SpeculationError`]. Total by construction: every variant of
    /// [`SpeculationError`] and every arm of [`InterpreterError`] that is
    /// distinguished has an explicit case, and the rest fall to
    /// [`ErrorCode::Interpreter`].
    pub fn of(error: &SpeculationError) -> Self {
        match error {
            SpeculationError::Interpreter(InterpreterError::OutOfPhlogistonsError) => {
                ErrorCode::OutOfPhlogistons
            },
            SpeculationError::Interpreter(InterpreterError::UserAbortError) => ErrorCode::UserAbort,
            SpeculationError::Interpreter(_) => ErrorCode::Interpreter,
            SpeculationError::Space(_) => ErrorCode::Tuplespace,
            SpeculationError::NotFired => ErrorCode::NotFired,
            SpeculationError::Bootstrap(_) => ErrorCode::Bootstrap,
        }
    }
}

impl AbortedLeaf {
    /// Build the FIPS `failure` leaf from a raised error, keeping f1r3node's
    /// own message.
    pub fn of(trace: Vec<RendezvousName>, error: &SpeculationError) -> Self {
        AbortedLeaf {
            trace,
            code: ErrorCode::of(error),
            message: error.to_string(),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// The result of an exploration
// ══════════════════════════════════════════════════════════════════════════

/// What one exploration measured, and the evidence that it measured it.
///
/// The three leaf collections are the three FIPS maps; [`ExplorationStats`] is
/// the arithmetic a reader needs to tell a search that branched from one that
/// only reproduced ordinary execution.
#[derive(Clone, Debug)]
pub struct Exploration {
    /// Branches that reached quiescence — the FIPS `success`.
    pub success: Vec<QuiescentLeaf>,
    /// Branches the depth bound cut short — the **third** map, resumable.
    pub truncated: Vec<TruncatedLeaf>,
    /// Branches that raised — the FIPS `failure`.
    pub failure: Vec<AbortedLeaf>,
    /// The configuration the exploration started from: `P` administratively
    /// saturated, before any COMM. Retained so a caller can diff a leaf against
    /// the root, and so a resumption can be re-rooted.
    pub root: SpeculativeState,
    /// Counters — see [`ExplorationStats`].
    pub stats: ExplorationStats,
}

impl Exploration {
    /// Total leaves across the three maps.
    pub fn leaves(&self) -> usize {
        self.success.len() + self.truncated.len() + self.failure.len()
    }

    /// The number of **distinct terminal configurations** among the successful
    /// branches, compared by [`content_fingerprint`].
    ///
    /// This is the number the non-confluence question asks: two for Ambient's
    /// open race, one for any λ term. Under
    /// [`TraceMode::DistinctConfigurations`] it equals `success.len()` by
    /// construction; under [`TraceMode::EveryTrace`] it is generally smaller,
    /// and the gap is exactly the confluence of the guest.
    pub fn distinct_success_configurations(&self) -> usize {
        let mut seen: std::collections::HashSet<Vec<String>> =
            std::collections::HashSet::with_capacity(self.success.len());
        for leaf in self.success.iter() {
            seen.insert(content_fingerprint(&leaf.state));
        }
        seen.len()
    }

    /// Every truncated branch, as a resumable handle.
    pub fn handles(&self) -> Vec<ResumableBranch> {
        let mut handles = Vec::with_capacity(self.truncated.len());
        handles.extend(self.truncated.iter().map(|leaf| leaf.branch.clone()));
        handles
    }
}

/// Counters over one exploration. Every field is evidence for a claim a reader
/// would otherwise have to take on faith.
/// Not `Copy`: `consumed` is f1r3node's `Cost`, which carries the operation
/// label and is not `Copy`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExplorationStats {
    /// Configurations whose `E(S)` was enumerated.
    pub nodes_expanded: usize,
    /// Rendezvous fired — edges of the reduction graph walked. The count that
    /// separates a real search from a single trace: an exploration with
    /// `edges_fired > nodes_expanded - 1` branched.
    pub edges_fired: usize,
    /// Children not expanded because an equal configuration had already been
    /// reached under a sleep set permitting at least as much. Zero under
    /// [`TraceMode::EveryTrace`] by construction.
    pub merged_configurations: usize,
    /// Rendezvous NOT fired because an earlier, independent sibling's subtree
    /// already covers the interleaving — the partial-order reduction's yield.
    /// Zero unless [`TraceMode::IndependenceReduced`].
    pub independence_pruned: usize,
    /// Configurations re-expanded because they were reached a second time under
    /// a sleep set permitting strictly more than the first arrival's. The
    /// correctness valve of combining sleep sets with a visited set: without it
    /// a branch out of an already-seen state could be lost.
    pub reopened_configurations: usize,
    /// The largest BFS level.
    pub max_frontier: usize,
    /// The deepest trace produced.
    pub depth_reached: u64,
    /// The sandbox's consumed cost after the exploration — a **COMM count**.
    /// This, in `consumed` *calls* to `reserve_comm`, is what the host owes.
    pub consumed: Cost,
    /// The largest `|E(S)|` seen at any node. `> 1` at least once is the
    /// necessary condition for a branch to exist at all.
    pub max_out_degree: usize,
    /// The largest CONFLICT CLASS expanded at any node — the real branch factor.
    /// `max_conflict_class == 1` says the guest made no choice: every rendezvous
    /// it ever enabled was independent of every other, so its reduction is
    /// deterministic however large `max_out_degree` grew.
    pub max_conflict_class: usize,
}

// ══════════════════════════════════════════════════════════════════════════
// A frontier entry
// ══════════════════════════════════════════════════════════════════════════

/// One node of the current BFS level: a configuration, the trace that reached
/// it, and its **sleep set**.
///
/// The sleep set holds the *semantic names* of rendezvous this node must not
/// fire, because firing them would re-walk an interleaving an already-explored
/// sibling covers. It is keyed semantically — the `Consume` hash and the
/// selected `Produce` hashes — rather than by store index, because indices
/// renumber across a firing and a sleeping rendezvous has to stay recognisable
/// in the successor.
#[derive(Clone, Debug)]
struct Node {
    state: SpeculativeState,
    trace: Vec<RendezvousName>,
    sleep: SleepSet,
}

/// A rendezvous's index-free identity: the `Consume` content hash and the
/// selected data's `Produce` content hashes, in bind order.
type SemanticName = (Blake2b256Hash, Vec<Blake2b256Hash>);

/// A sleep set: the semantic name of each rendezvous this node must not fire,
/// **with the resources it would consume**.
///
/// The resources ride along rather than being looked up in the node's own
/// enumeration because a slept rendezvous need not be enabled at every node it
/// sleeps through — a transiently-disabled one that becomes enabled again must
/// still be recognised as covered, and a sleep set that dropped it would wake it
/// and re-walk the interleaving it was pruned for.
type SleepSet = BTreeMap<SemanticName, BTreeSet<Resource>>;

/// The sleep set a child inherits: everything the parent slept on, plus every
/// earlier sibling already explored, restricted to those INDEPENDENT of the
/// rendezvous being fired.
///
/// This is Godefroid's sleep-set rule, read onto a tuplespace. Firing a slept
/// rendezvous `t` later would walk `…·r·t`, and because `t ⊥ r` that reaches the
/// same configuration as `…·t·r`, which the earlier sibling's subtree already
/// covers. The restriction to independent members is what makes it sound: a
/// slept rendezvous that CONFLICTS with `r` is woken, because after `r` it is a
/// genuinely different transition.
fn inherit_sleep(
    parent: &SleepSet,
    earlier: &[(SemanticName, BTreeSet<Resource>)],
    fired: &BTreeSet<Resource>,
) -> SleepSet {
    let mut inherited = SleepSet::new();
    for (name, other) in parent.iter() {
        if other.is_disjoint(fired) {
            inherited.insert(name.clone(), other.clone());
        }
    }
    for (name, other) in earlier.iter() {
        if other.is_disjoint(fired) {
            inherited.insert(name.clone(), other.clone());
        }
    }
    inherited
}

/// Whether `wider` permits at least as much as `narrower` — i.e. `wider` is a
/// SUBSET of `narrower` as a set of prohibitions.
fn permits_at_least(wider: &SleepSet, narrower: &SleepSet) -> bool {
    wider.keys().all(|name| narrower.contains_key(name))
}

/// The pointwise intersection of two sleep sets: the prohibitions BOTH arrivals
/// carry.
fn intersect_sleep(left: &SleepSet, right: &SleepSet) -> SleepSet {
    let mut both = SleepSet::new();
    for (name, resources) in left.iter() {
        if right.contains_key(name) {
            both.insert(name.clone(), resources.clone());
        }
    }
    both
}

// ══════════════════════════════════════════════════════════════════════════
// The metering mirror
// ══════════════════════════════════════════════════════════════════════════

/// **Charge `host` for `owed` committed COMMs.** The single implementation of
/// the charge-back; [`Explorer::charge_host`] is this with `owed` read off its
/// own sandbox.
///
/// ⚠ A budget unit is ONE COMM, not one unit of `Cost.value`:
/// `MeteredMachine::reserve_comm(amount)` charges **one** regardless of `amount`
/// (the `Cost` is the diagnostic weight that rides into the event log and the
/// cost-trace digest). So charging back `k` COMMs is `k` *calls*, which is what
/// this does — one call passing `owed` would charge 1.
///
/// It is a free function because the charge-back has two callers with different
/// lifetimes: the [`Explorer`], which still holds its sandbox, and the request
/// server ([`crate::speculation::server`]), which holds only the
/// [`LookaheadResponse::consumed`](crate::speculation::service::LookaheadResponse::consumed)
/// a finished `serve` handed back. Two call sites reimplementing "one
/// `reserve_comm` per committed COMM" is exactly how a metering path drifts, so
/// there is one.
///
/// Fails with `OutOfPhlogistonsError` on the call that exceeds the host's
/// budget, exactly like any other over-budget program, and reports how many were
/// charged before it did.
///
/// This owns no budget and defines no cost: `host` is f1r3node's own
/// `RuntimeBudget` and `reserve_comm` is f1r3node's own charge point. Budgets
/// are F1r3node's.
pub fn charge_host_comms(
    host: &RuntimeBudget,
    owed: Cost,
    weight: Cost,
) -> Result<usize, (usize, InterpreterError)> {
    let owed = owed.value.max(0) as usize;
    let machine = MeteredMachine::new(host.clone());
    for charged in 0..owed {
        // `Cost` is not `Copy` (it carries its operation label), so each charge
        // takes its own clone. The label is diagnostic and identical across the
        // calls by design: the charge-back is one COMM per COMM the exploration
        // committed, and they are all the same kind of event.
        if let Err(error) = machine.reserve_comm(weight.clone()) {
            return Err((charged, error));
        }
    }
    Ok(owed)
}

// ══════════════════════════════════════════════════════════════════════════
// The explorer
// ══════════════════════════════════════════════════════════════════════════

/// The branching engine: BFS over `E(S)` on one [`SpeculativeSandbox`].
///
/// Owns nothing the sandbox does not already own. It exists as a type rather
/// than as a free function so a caller can run several explorations against one
/// funded sandbox (beam search: explore, rank, [`Explorer::resume`] the kept
/// handles) with one budget and one charge-back.
pub struct Explorer<'sandbox> {
    sandbox: &'sandbox SpeculativeSandbox,
    mode: TraceMode,
    // ★ `Send` is not decoration. An exploration is awaited from inside the `[*]`
    // request server's system-process handler
    // ([`crate::speculation::server`]), and f1r3node requires a system process's
    // future to be `Send` — it is polled on a multi-threaded tokio runtime and
    // may migrate between workers. A non-`Send` observer would make the whole
    // `serve` future non-`Send` and the server unrepresentable. An observer that
    // is only ever a progress print is `Send` in every existing caller anyway;
    // requiring it makes that a type-checked fact rather than a coincidence.
    observer: Option<Box<dyn FnMut(&LevelReport) + Send + 'sandbox>>,
}

/// One BFS level, as it completes — the search's own progress report.
///
/// An exploration is a walk on a graph whose size is not known in advance, so
/// "it is still running" has to be distinguishable from "it is diverging". This
/// is that distinction, and it is a first-class part of the engine rather than a
/// debug print because the shape of the level sequence is the *diagnosis*: a
/// frontier that grows geometrically while `independence_pruned` stays flat says
/// the independence relation is too coarse, and a frontier that stays flat while
/// the depth climbs says the guest is simply long.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LevelReport {
    /// Which BFS level just completed, counted from the exploration's root.
    pub level: u64,
    /// Nodes expanded at this level.
    pub expanded: usize,
    /// The next level's frontier size.
    pub frontier: usize,
    /// `|E(S)|` at each expanded node, in expansion order.
    pub out_degrees: Vec<usize>,
    /// The size of the CONFLICT CLASS expanded at each node — the real branch
    /// factor. Equal to the out-degree when the reduction is off. A run whose
    /// class sizes are all 1 made no choice at all: its guest is deterministic.
    pub class_sizes: Vec<usize>,
    /// Children discarded because an equal configuration was already covered.
    pub merged: usize,
    /// Rendezvous not fired because an independent sibling covers them.
    pub pruned: usize,
    /// Branches that reached quiescence at this level.
    pub quiescent: usize,
    /// Branches that raised at this level.
    pub aborted: usize,
    /// The sandbox's consumed COMM count after this level.
    pub consumed: Cost,
}

impl<'sandbox> Explorer<'sandbox> {
    /// An explorer over `sandbox` in the default mode
    /// ([`TraceMode::DistinctConfigurations`]).
    pub fn new(sandbox: &'sandbox SpeculativeSandbox) -> Self {
        Explorer {
            sandbox,
            mode: TraceMode::default(),
            observer: None,
        }
    }

    /// An explorer over `sandbox` in `mode`.
    pub fn with_mode(sandbox: &'sandbox SpeculativeSandbox, mode: TraceMode) -> Self {
        Explorer {
            sandbox,
            mode,
            observer: None,
        }
    }

    /// Attach a per-level progress observer. See [`LevelReport`], and the `Send` note on
    /// [`Explorer`]'s `observer` field for why the bound is what it is.
    pub fn observing(mut self, observer: impl FnMut(&LevelReport) + Send + 'sandbox) -> Self {
        self.observer = Some(Box::new(observer));
        self
    }

    /// The sandbox being explored.
    pub fn sandbox(&self) -> &SpeculativeSandbox {
        self.sandbox
    }

    /// The trace mode.
    pub fn mode(&self) -> TraceMode {
        self.mode
    }

    /// **`x!(P)[n]`** — inject `P`, saturate it administratively, and explore
    /// every execution path for at most `lookahead` stratified steps.
    ///
    /// `rand` is the caller's randomness and on chain must derive from the
    /// **deploy's**: two validators speculating over the same deploy have to
    /// mint the same unforgeable names. (The split is positional and computed
    /// eagerly, so it does not depend on the scheduler — measured,
    /// `tests/x1_stratified_monotonicity.rs::r1`.)
    ///
    /// The sandbox must already be funded ([`SpeculativeSandbox::fund_from`]);
    /// an unfunded one refuses to evaluate anything at all, which is the
    /// fail-shut direction, and the refusal arrives as a single
    /// [`ErrorCode::OutOfPhlogistons`] `failure` leaf with an empty trace.
    pub async fn explore(
        &mut self,
        program: Par,
        rand: Blake2b512Random,
        lookahead: Lookahead,
    ) -> Result<Exploration, SpeculationError> {
        // The root: a clean sandbox, `P` injected, administrative saturation to
        // quiescence. Nothing has fired.
        self.sandbox.load(SpeculativeState::default()).await?;
        if let Err(error) = self.sandbox.saturate(program, rand).await {
            // ★ A root that cannot even be saturated is ONE aborted branch with
            // an EMPTY trace — not an `Err`. Out of phlogistons arrives here
            // when the deploy cannot afford the injection at all, and the FIPS
            // is explicit that running out of gas is a `failure`, not an
            // infrastructure fault.
            let root = self.sandbox.snapshot();
            return Ok(Exploration {
                success: Vec::new(),
                truncated: Vec::new(),
                failure: vec![AbortedLeaf::of(Vec::new(), &error)],
                root,
                stats: ExplorationStats {
                    consumed: self.sandbox.consumed(),
                    ..ExplorationStats::default()
                },
            });
        }
        let root = self.sandbox.snapshot();
        self.search(
            vec![Node {
                state: root.clone(),
                trace: Vec::with_capacity(lookahead.trace_capacity()),
                sleep: SleepSet::new(),
            }],
            root,
            lookahead,
            0,
        )
        .await
    }

    /// **Beam search's second half** — continue from truncated handles.
    ///
    /// "Run `k` steps, gather the leaves, keep the best `n`, run forward from
    /// those" *is* resuming `n` truncated handles, so this takes a slice of
    /// them and explores all of them together, each continuing to append to its
    /// own trace. `lookahead` is a bound on the ADDITIONAL steps, so a caller
    /// that ran `[k]` and resumes `[k]` has explored `2k` along every kept
    /// path.
    ///
    /// The root of the returned exploration is the first handle's
    /// configuration when there is exactly one, and the empty configuration
    /// otherwise, because a set of handles has no single root; the handles
    /// themselves are the ground truth and each leaf carries its whole trace
    /// from the original root.
    pub async fn resume(
        &mut self,
        handles: &[ResumableBranch],
        lookahead: Lookahead,
    ) -> Result<Exploration, SpeculationError> {
        let mut frontier = Vec::with_capacity(handles.len());
        let mut deepest = 0u64;
        for handle in handles.iter() {
            deepest = deepest.max(handle.trace.len() as u64);
            frontier.push(Node {
                state: handle.state.clone(),
                trace: handle.trace.clone(),
                // A resumed handle sleeps on nothing: the reduction that
                // truncated it is over, and the branch is free to fire anything
                // its configuration admits.
                sleep: SleepSet::new(),
            });
        }
        let root = match handles.len() {
            1 => handles[0].state.clone(),
            _ => SpeculativeState::default(),
        };
        // The bound is on ADDITIONAL steps, so the level counter starts at the
        // depth already travelled; `Lookahead::Steps(n)` then admits `n` more.
        self.search(frontier, root, lookahead, deepest).await
    }

    /// **Charge the host what the exploration spent.**
    ///
    /// ⚠ A budget unit is ONE COMM, not one unit of `Cost.value`:
    /// `MeteredMachine::reserve_comm(amount)` charges **one** regardless of
    /// `amount` (the `Cost` is the diagnostic weight that rides into the event
    /// log and the cost-trace digest). So charging back `k` COMMs is `k`
    /// *calls*, which is what this does — one call passing `consumed()` would
    /// charge 1.
    ///
    /// Fails with `OutOfPhlogistonsError` on the call that exceeds the host's
    /// budget, exactly like any other over-budget program, and reports how many
    /// were charged before it did.
    ///
    /// This owns no budget and defines no cost: `host` is f1r3node's own
    /// `RuntimeBudget` and `reserve_comm` is f1r3node's own charge point.
    /// Budgets are F1r3node's.
    pub fn charge_host(
        &self,
        host: &RuntimeBudget,
        weight: Cost,
    ) -> Result<usize, (usize, InterpreterError)> {
        charge_host_comms(host, self.sandbox.consumed(), weight)
    }

    // ── the search itself ────────────────────────────────────────────────

    /// BFS from `frontier`, at most `lookahead` further levels.
    ///
    /// `depth_offset` is the number of steps the frontier's traces have already
    /// travelled (zero for a fresh exploration, the handles' depth for a
    /// resumption) and exists so the *bound* is on additional steps while the
    /// *reported* depth is absolute.
    async fn search(
        &mut self,
        mut frontier: Vec<Node>,
        root: SpeculativeState,
        lookahead: Lookahead,
        depth_offset: u64,
    ) -> Result<Exploration, SpeculationError> {
        let mut success: Vec<QuiescentLeaf> = Vec::new();
        let mut truncated: Vec<TruncatedLeaf> = Vec::new();
        let mut failure: Vec<AbortedLeaf> = Vec::new();
        let mut stats = ExplorationStats {
            max_frontier: frontier.len(),
            depth_reached: depth_offset,
            ..ExplorationStats::default()
        };

        // ★ The visited map. A configuration is expanded once per sleep set that
        // permits strictly more than the one it was expanded under: a state
        // first reached asleep on `{r}` and later reached awake must be
        // re-expanded, or the `r` branch out of it would be lost. Storing the
        // running INTERSECTION and re-expanding whenever a new arrival is not a
        // superset of it is the standard sound rule, and it terminates because
        // sleep sets only ever shrink and are finite.
        let mut visited: HashMap<Vec<String>, SleepSet> = HashMap::new();
        if self.mode.merges() {
            visited.reserve(frontier.len());
            for node in frontier.iter() {
                visited.insert(content_fingerprint(&node.state), node.sleep.clone());
            }
        }

        let mut level = 0u64;
        while !frontier.is_empty() && lookahead.admits(level) {
            // ★ Preallocate: at least one child per node, and each node reserves
            // its exact out-degree before pushing (below).
            let mut next: Vec<Node> = Vec::with_capacity(frontier.len());
            let mut report = LevelReport {
                level: depth_offset + level,
                expanded: 0,
                frontier: 0,
                out_degrees: Vec::with_capacity(frontier.len()),
                class_sizes: Vec::with_capacity(frontier.len()),
                merged: 0,
                pruned: 0,
                quiescent: 0,
                aborted: 0,
                consumed: Cost::create(0, "speculation level"),
            };

            for node in frontier.drain(..) {
                // Install the node's configuration and enumerate `E(S)`.
                self.sandbox.load(node.state.clone()).await?;
                let enabled = self.sandbox.enabled();
                stats.nodes_expanded += 1;
                stats.max_out_degree = stats.max_out_degree.max(enabled.len());
                report.expanded += 1;
                report.out_degrees.push(enabled.len());

                if enabled.is_empty() {
                    report.quiescent += 1;
                    success.push(QuiescentLeaf {
                        trace: node.trace,
                        state: node.state,
                    });
                    continue;
                }

                // The plan: every admissible selection's name, its semantic
                // (index-free) name, and its resource set, computed ONCE. Each
                // sibling is then fired by NAME against a re-installed
                // configuration and the re-enumeration is verified.
                let mut planned = Vec::with_capacity(enabled.len());
                for rendezvous in enabled.iter() {
                    let name = RendezvousName::of(rendezvous);
                    let semantic = name.semantic();
                    planned.push((name, semantic, resources(rendezvous)));
                }
                drop(enabled);

                // ★ THE SLEEP SET. Siblings are visited in enumeration order;
                // when the `i`-th is fired, the child sleeps on every rendezvous
                // this node was already asleep on PLUS every earlier sibling,
                // restricted to those INDEPENDENT of the one just fired. Firing
                // a slept rendezvous later would re-walk an interleaving the
                // earlier sibling's subtree already covers, and — because the
                // two are independent — would reach a configuration that subtree
                // also reaches.
                let mut fired_earlier: Vec<(SemanticName, BTreeSet<Resource>)> =
                    Vec::with_capacity(planned.len());
                // Whether the sandbox still holds `node.state`. The first
                // expanded sibling inherits the enumeration above; every later
                // one re-installs, because firing moved the configuration.
                let mut dirty = false;

                // ★ THE PERSISTENT SET. Under the reduction only the conflict
                // class of `E(S)[0]` is expanded: the members of other classes
                // are not alternatives to it, they are things that will also
                // happen, and postponing them loses no configuration (see
                // `conflict_class`). Without the reduction every member of
                // `E(S)` is expanded, which enumerates every interleaving of
                // every independent pair.
                let expanded: Vec<usize> = match self.mode.reduces() {
                    true => {
                        let resource_sets: Vec<BTreeSet<Resource>> = planned
                            .iter()
                            .map(|(_, _, resource_set)| resource_set.clone())
                            .collect();
                        let class = conflict_class(&resource_sets);
                        stats.independence_pruned += planned.len() - class.len();
                        report.pruned += planned.len() - class.len();
                        class
                    },
                    false => (0..planned.len()).collect(),
                };
                report.class_sizes.push(expanded.len());
                stats.max_conflict_class = stats.max_conflict_class.max(expanded.len());

                next.reserve(expanded.len());
                for index in expanded.into_iter() {
                    let (planned_name, semantic, resource_set) = &planned[index];

                    // Asleep: this branch is covered by an earlier sibling's.
                    if self.mode.reduces() && node.sleep.contains_key(semantic) {
                        stats.independence_pruned += 1;
                        report.pruned += 1;
                        continue;
                    }

                    // Re-install for every sibling after the first — firing the
                    // previous one moved the configuration.
                    if dirty {
                        self.sandbox.load(node.state.clone()).await?;
                    }
                    dirty = true;
                    let live = self.sandbox.enabled();
                    // Teeth: f1r3node's enumeration is deterministic (pinned by
                    // `enabled_rendezvous_spec.rs::t4`) and this does not assume
                    // it. A drift here would silently explore a different graph.
                    if live.len() != planned.len()
                        || RendezvousName::of(&live[index]) != *planned_name
                    {
                        failure.push(AbortedLeaf::of(
                            node.trace.clone(),
                            &SpeculationError::NotFired,
                        ));
                        continue;
                    }

                    // The child's sleep set, computed BEFORE the firing (it is a
                    // function of the plan alone).
                    let mut child_sleep = match self.mode.reduces() {
                        true => inherit_sleep(&node.sleep, &fired_earlier, resource_set),
                        false => SleepSet::new(),
                    };

                    match self.sandbox.fire(live[index].clone()).await {
                        Ok(step) => {
                            stats.edges_fired += 1;
                            fired_earlier.push((semantic.clone(), resource_set.clone()));
                            let child_state = self.sandbox.snapshot();
                            let mut child_trace = Vec::with_capacity(node.trace.len() + 1);
                            child_trace.extend_from_slice(&node.trace);
                            child_trace.push(step.name);

                            if self.mode.merges() {
                                let fingerprint = content_fingerprint(&child_state);
                                match visited.get_mut(&fingerprint) {
                                    Some(seen) if permits_at_least(seen, &child_sleep) => {
                                        // Already expanded under a sleep set that
                                        // permits at least as much: its whole
                                        // future is covered. Merging discards
                                        // this trace LABEL and no reachable leaf.
                                        stats.merged_configurations += 1;
                                        report.merged += 1;
                                        continue;
                                    },
                                    Some(seen) => {
                                        // Reached permitting strictly more than
                                        // the first arrival: re-expand under the
                                        // intersection, so the newly-permitted
                                        // branches are taken and the already-
                                        // explored ones are not re-taken.
                                        *seen = intersect_sleep(seen, &child_sleep);
                                        child_sleep = seen.clone();
                                        stats.reopened_configurations += 1;
                                    },
                                    None => {
                                        visited.insert(fingerprint, child_sleep.clone());
                                    },
                                }
                            }

                            next.push(Node {
                                state: child_state,
                                trace: child_trace,
                                sleep: child_sleep,
                            });
                        },
                        Err(error) => {
                            // ★ The FIPS's `failure`: the trace up to the failing
                            // step, plus a code and a message. The step is NOT
                            // appended — it did not happen.
                            report.aborted += 1;
                            failure.push(AbortedLeaf::of(node.trace.clone(), &error));
                        },
                    }
                }
            }

            level += 1;
            stats.depth_reached = depth_offset + level;
            stats.max_frontier = stats.max_frontier.max(next.len());
            report.frontier = next.len();
            report.consumed = self.sandbox.consumed();
            if let Some(observer) = self.observer.as_mut() {
                observer(&report);
            }
            frontier = next;
        }

        // ★ The bound ran out (or `[*]` emptied the frontier — then this loop is
        // empty). Whether a surviving node is QUIESCENT or TRUNCATED is decided
        // by `E(S)`, never by "the bound was reached": a branch that finished on
        // its last allotted step is the completed evaluation it is.
        for node in frontier.drain(..) {
            self.sandbox.load(node.state.clone()).await?;
            let frontier_size = self.sandbox.enabled().len();
            stats.nodes_expanded += 1;
            stats.max_out_degree = stats.max_out_degree.max(frontier_size);
            match frontier_size {
                0 => success.push(QuiescentLeaf {
                    trace: node.trace,
                    state: node.state,
                }),
                _ => truncated.push(TruncatedLeaf {
                    branch: ResumableBranch {
                        state: node.state,
                        trace: node.trace,
                        frontier: frontier_size,
                    },
                }),
            }
        }

        stats.consumed = self.sandbox.consumed();
        Ok(Exploration {
            success,
            truncated,
            failure,
            root,
            stats,
        })
    }
}
