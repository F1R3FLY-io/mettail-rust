//! # Stage 2 — result assembly: turning an [`Exploration`] into values a
//! receiving program can actually read
//!
//! The search ([`super::search`]) produces Rust leaves. The FIPS puts the
//! results *on a channel*: **"The names of `success` and `failure` are then
//! placed on the channel `x`."** So something has to become a `Par`. This module
//! is that something, and every choice it makes is a choice about what a RhoCalc
//! program on the other end can do with the answer.
//!
//! ## ★ What the delivery is NOT built on, and why
//!
//! The FIPS names the collection a `PathMap`, and `{| … |}` is RhoCalc's PathMap
//! literal. **PathMap methods do not lower on the reducer path** — all 22 zipper
//! methods fail, and a `Pathmap` lowers to an `EMap` — so a receiving program
//! cannot iterate, filter, or fold a delivered PathMap. Delivering one would be
//! delivering a value whose only useful operations are unavailable: the demo
//! would type-check and do nothing.
//!
//! Nondeterministic *pattern* peeling is not the answer either. The FIPS's own
//! consumption pattern `for (@{| trace, ..._ |}, _ <- x)` peels one arbitrary
//! entry, which is sound in its λ example **only because confluence makes the
//! choice unobservable**. Over a non-confluent guest — the case `[*]` exists for
//! — peeling one entry silently discards the others.
//!
//! ## ★ What it IS built on: `ESet` of `EList`
//!
//! ```text
//!   success  ::=  {| entry , … |}                    -- an ESet
//!   entry    ::=  [ step₀ , … , step_{k-1} , leaf ]  -- an EList: the trace, then the leaf
//!   step     ::=  GByteArray(32)                     -- the content digest of one named selection
//! ```
//!
//! Four properties, each load-bearing:
//!
//! 1. **`ESet` and `EList` are native `rhoapi` and lower.** They are ordinary
//!    Rholang collections: the reducer constructs them, sorts them, rests them
//!    on a channel, and pattern-matches them. Nothing here depends on a method
//!    that does not lower.
//! 2. **The entry is the FIPS's own shape.** The FIPS says of a failure that
//!    *"an extra two-element list containing an error code for the failure and a
//!    message is **concatenated to the end of the trace**"* — the trace with its
//!    leaf appended IS the entry, and the FIPS's own reader takes the leaf as
//!    `trace.last()`. The success and truncated maps use the same shape so a
//!    consumer needs one rule, not three.
//! 3. **A set, not a list.** Branches are unordered; delivering a list would
//!    make enumeration order an observable, and two validators that agree on the
//!    branch *set* must agree on the delivered value. `ParSet` sorts, so the
//!    encoding is canonical.
//! 4. **A step is one 32-byte digest.** A [`RendezvousName`] is a `Consume`
//!    hash, the selected data's `Produce` hashes, and the store positions; all
//!    of it is folded into one content digest ([`step_digest`]) because a
//!    consumer *keys* on a trace — it never destructures one — and because the
//!    digest of a whole trace ([`trace_digest`]) is then the natural **handle
//!    name** for resuming a truncated branch. The structured form remains
//!    available Rust-side on [`RendezvousName`] and is where a replay
//!    differential looks.
//!
//! ## The three leaves
//!
//! | map | leaf | why |
//! |---|---|---|
//! | `success` | the reified terminal **configuration**, as a process | the FIPS's leaf is *the contents of* `empty_t`; its Lambdas example pattern-matches the leaf as a running process (`match inst { for (_, _ <- instCh) { _ } => … }`) |
//! | `truncated` | `(handle, frontier, configuration)` | the USER decision: the leaf is a **handle to a retained configuration**, resumable — `handle` names it, `frontier` is `\|E(S)\|` at the cut (how many ways it could have continued), and the configuration is there to be inspected before deciding whether to resume |
//! | `failure` | `[code, message]` | the FIPS verbatim: *"a two-element list containing an error code for the failure and a message"* |
//!
//! ⚠ The truncated leaf's handle is a **name**, not the resumable state itself.
//! A `Par` cannot express a datum's `Blake2b512Random`, a continuation's
//! `Consume` source, or a datum's `Produce` source, so a branch resumed from a
//! reified process would mint different unforgeable names than the branch that
//! was truncated — the resumption would not be a continuation of anything. The
//! retained `HotStoreState` stays host-side in the [`ResumableBranch`]; the
//! delivered handle is how a program names which one it wants. The reified
//! configuration in the same tuple is for *inspection* (ranking, in beam
//! search), not for resumption.
//!
//! ## Reification: a configuration as a process
//!
//! A tuplespace configuration is a multiset of resting data and waiting
//! continuations, and its process form is the obvious one:
//!
//! ```text
//!     ⟦ S ⟧  =  ∏  channel!(payload)          for every resting datum
//!            ∥  ∏  for(patterns <- channels) { body }   for every waiting continuation
//! ```
//!
//! with `!!` for a persistent datum and `contract` / `for(…<<-…)` shape carried
//! by the `Receive`'s `persistent` / `peek` flags. Three details are not
//! obvious and each is measured rather than assumed:
//!
//! * **Installed continuations are excluded.** They are the *runtime's* system
//!   processes (`stdout`, …), identical in every sandbox by construction
//!   (correction 4), and not part of the program. This is the same exclusion
//!   [`super::content_fingerprint`] makes, for the same reason.
//! * **The `where` guard travels on the continuation, not the pattern.**
//!   `Receive.condition` is lifted onto `TaggedContinuation.guard` when the
//!   continuation is registered with rspace (`Reduce::eval_receive` →
//!   `consume(… subst_guard …)`), so reification puts it back on
//!   `Receive.condition`. Dropping it would reify a guarded receive as an
//!   unguarded one — a strictly more permissive process.
//! * **`locally_free` is recomputed the way the normalizer computes it**
//!   (union of the sources' and patterns' free sets with the body's filtered and
//!   adjusted by `bind_count`), because `Par`'s `Ord` includes `locally_free`
//!   and a mis-computed bitset would make two equal processes sort differently.
//!
//! A continuation that is a **system process** (`ScalaBodyRef`) has no `Par`
//! body and cannot be reified as a receive. Rather than invent a surface for it
//! or silently emit a receive whose body is `Nil` — which would be a strictly
//! weaker process presented as the configuration — reification fails closed with
//! [`ReificationError::SystemContinuation`].

use models::rhoapi::tagged_continuation::TaggedCont;
use models::rhoapi::{Expr, Par, Receive, ReceiveBind, Send, Var};
use models::rust::utils::{
    new_elist_par, new_eset_par, new_etuple_par, new_gbytearray_par, new_gint_par, new_gstring_par,
    union,
};
use rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash;

use super::search::{AbortedLeaf, Exploration, QuiescentLeaf, TruncatedLeaf};
use super::{RendezvousName, SpeculativeState};
use crate::lookahead::{SPEC_FAILURE_CHANNEL, SPEC_SUCCESS_CHANNEL, SPEC_TRUNCATED_CHANNEL};

// ══════════════════════════════════════════════════════════════════════════
// Trace naming
// ══════════════════════════════════════════════════════════════════════════

/// The **content digest of one named selection** — what a delivered trace
/// element is.
///
/// Folds the [`RendezvousName`]'s **semantic** identity — the `Consume` content
/// hash and every selected datum's `Produce` content hash in bind order — into
/// one 32-byte `Blake2b256Hash`.
///
/// ## ★ Store indices are DELIBERATELY EXCLUDED, and this used to be a defect
///
/// This function previously also folded `continuation_index` and
/// `datum_indices`, with a comment arguing that content hashing alone cannot
/// separate two byte-identical sends on one channel, and that including the
/// indices makes a digest name a *specific* enumeration. That comment also
/// conceded, correctly, that *"the distinction is not semantically
/// load-bearing"* — and the indices turned out to be the one non-content input
/// in the whole chain.
///
/// A store index is **not content. It is a local address assigned by
/// task-arrival order.** `HotStore::put_datum` / `put_continuation` *prepend*
/// (`rspace++/src/rspace/hot_store.rs:270, 289, 400-410`), so a datum's position
/// is "how many data were staged after it on that channel". Arrival races by
/// design: every branch of a `|` is a detached `tokio::spawn`
/// (`rholang/src/rust/interpreter/reduce.rs:653-664`), whose own `DriveState`
/// doc concedes *"Push order is non-deterministic."*
/// `order_candidates_with_index` then decorates candidates with their position
/// in the received `Vec` and sorts by `(content_hash, store_index)` — the
/// content hash dominates, so the **selection** is content-determined, but the
/// index carried alongside is arrival order, and it used to land here.
///
/// Measured, on `demos/flt-lookahead/04-divergence.rho`, before the fix:
///
/// | `TOKIO_WORKER_THREADS` | runs | distinct digests |
/// |---|---|---|
/// | 1 | 5 | **1** |
/// | 2 | 12 | 2 (mode = the 1-thread value) |
/// | 32 (default) | 20 | 20 |
///
/// Monotone in scheduler width, with the 2-thread mode equal to the 1-thread
/// value. Nothing but an arrival-order dependence has that shape.
///
/// ★ The search itself already knew this. `SemanticName` — [`RendezvousName::semantic`] —
/// is the sleep-set key, chosen because *"indices renumber across a firing"*. The search
/// treated indices as not-a-name and delivery did not. This aligns them.
///
/// ## What this costs
///
/// Two byte-identical sends on one channel are now indistinguishable in a
/// published trace. By the old comment's own argument that is semantically
/// nothing — firing either yields the same successor. It does cost a
/// replay-equivalence differential its index leg, but that leg was comparing
/// scheduler noise and would have reported spurious mismatches on every honest
/// replay; the structured [`RendezvousName`] is still available in-process for a
/// differential that wants it.
///
/// ## Why it mattered beyond reproducibility
///
/// The digest is published — `^spec-success`, `^spec-failure`, `^spec-truncated`
/// and all three `^spec-delivery` collections carry it — and publication is a
/// `produce` into the live tuplespace. A local address promoted into a published
/// name is a value two validators can disagree on *without either being wrong*:
/// core count, load and tokio version all move it, and no deploy-derived seed
/// can fix it, because it is not about randomness. `[*]` is on no deploy path
/// today, so this was prospective — but it was prospective on a worse footing
/// than the injection-randomness cause beside it, which the deploy envelope does
/// determine.
pub fn step_digest(name: &RendezvousName) -> Blake2b256Hash {
    // 32 (consume) + 32 per datum.
    let mut bytes = Vec::with_capacity(32 + 32 * name.data.len());
    bytes.extend_from_slice(&name.consume.bytes());
    for datum in name.data.iter() {
        bytes.extend_from_slice(&datum.bytes());
    }
    Blake2b256Hash::new(&bytes)
}

#[cfg(test)]
mod step_digest_tests {
    use super::*;

    fn hash(byte: u8) -> Blake2b256Hash {
        Blake2b256Hash::new(&[byte])
    }

    fn name(consume: u8, data: &[u8], cont_index: i32, datum_indices: &[i32]) -> RendezvousName {
        RendezvousName {
            consume: hash(consume),
            data: data.iter().copied().map(hash).collect(),
            continuation_index: cont_index,
            datum_indices: datum_indices.to_vec(),
        }
    }

    /// ★ THE INVARIANT, in one line and with no runtime: store positions do not name a
    /// selection. Two rendezvous identical in `consume` and `data` but differing in the
    /// scheduler-assigned indices are the SAME step, because firing either yields the same
    /// successor — which is what the superseded doc comment already conceded while folding
    /// them in anyway.
    #[test]
    fn store_indices_do_not_change_the_digest() {
        let a = name(1, &[2, 3], 0, &[0, 1]);
        let b = name(1, &[2, 3], 7, &[4, 9]);
        assert_eq!(
            step_digest(&a),
            step_digest(&b),
            "★ a store index is a local address assigned by task-arrival order, not content. \
             Folding it makes the digest a function of the scheduler."
        );
    }

    /// …and the digest still separates what it must. Content differences are load-bearing.
    #[test]
    fn content_differences_do_change_the_digest() {
        let base = name(1, &[2, 3], 0, &[0, 1]);
        for (label, other) in [
            ("a different consume", name(9, &[2, 3], 0, &[0, 1])),
            ("a different datum", name(1, &[2, 9], 0, &[0, 1])),
            ("a different bind ORDER", name(1, &[3, 2], 0, &[0, 1])),
            ("a different arity", name(1, &[2], 0, &[0])),
        ] {
            assert_ne!(
                step_digest(&base),
                step_digest(&other),
                "{label} must be a different step"
            );
        }
    }
}

/// The **handle name of a whole trace**: the digest of the concatenated step
/// digests, in order.
///
/// This is what a truncated leaf carries and what a program passes back to say
/// *"resume that one"*. Order-sensitive by construction — two branches that
/// fired the same rendezvous in different orders are different branches — and
/// the empty trace has a well-defined digest (the digest of no bytes), so the
/// root is nameable too.
pub fn trace_digest(trace: &[RendezvousName]) -> Blake2b256Hash {
    let mut bytes = Vec::with_capacity(32 * trace.len());
    for name in trace.iter() {
        bytes.extend_from_slice(&step_digest(name).bytes());
    }
    Blake2b256Hash::new(&bytes)
}

/// f1r3node's `filter_and_adjust_bitset`, mirrored **verbatim**
/// (`rholang/src/rust/interpreter/util/mod.rs`).
///
/// `locally_free` is a positional bit vector — index = de-Bruijn level, value =
/// 0/1 — and this is the `bodyResult.par.locallyFree.from(boundCount).map(x => x
/// - boundCount)` step of the receive normalizer: drop the first `bound_count`
/// positions and renumber.
///
/// ⚠ It is mirrored rather than called because f1r3node declares it
/// `pub(crate)`, and it is mirrored **exactly** — including that it emits the
/// adjusted *index* where a bit vector would emit the *bit* — because the
/// purpose of computing it here at all is to agree with the normalizer
/// byte-for-byte. A reified receive whose `locally_free` differed from the
/// normalizer's for the same process would sort and compare differently
/// (`Par`'s `Ord` includes `locally_free`), which is exactly the failure this
/// function exists to avoid. Widening a consensus crate's API for a
/// result-assembly concern is the wrong trade; diverging from it silently is
/// worse.
fn filter_and_adjust_bitset(bitset: Vec<u8>, bound_count: usize) -> Vec<u8> {
    bitset
        .into_iter()
        .enumerate()
        .filter_map(|(index, _)| match index >= bound_count {
            true => Some(index as u8 - bound_count as u8),
            false => None,
        })
        .collect()
}

/// One trace as the `Par`s a delivered entry's prefix is made of.
fn trace_pars(trace: &[RendezvousName]) -> Vec<Par> {
    let mut pars = Vec::with_capacity(trace.len() + 1);
    pars.extend(
        trace
            .iter()
            .map(|name| new_gbytearray_par(step_digest(name).bytes(), Vec::new(), false)),
    );
    pars
}

// ══════════════════════════════════════════════════════════════════════════
// Reification
// ══════════════════════════════════════════════════════════════════════════

/// Why a configuration could not be reified as a process.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReificationError {
    /// A waiting continuation is a **system process** (`ScalaBodyRef`): it has
    /// no `Par` body, so no receive can carry it. Fails closed rather than
    /// emitting a receive with a `Nil` body, which would present a strictly
    /// weaker process as the configuration.
    ///
    /// Not reachable from an ordinary speculative state: system processes are
    /// *installed*, and installed continuations are excluded from reification.
    /// It exists so that if one ever does rest in the ordinary map, the caller
    /// hears about it.
    SystemContinuation {
        /// The `scala_body_ref` that could not be reified.
        body_ref: i64,
    },
    /// A waiting continuation's channel group is empty. A `for` with no binds is
    /// not a process.
    EmptyChannelGroup,
}

impl std::fmt::Display for ReificationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReificationError::SystemContinuation { body_ref } => write!(
                formatter,
                "a waiting continuation is the system process {body_ref}, which has no Par body"
            ),
            ReificationError::EmptyChannelGroup => {
                write!(formatter, "a waiting continuation has no channels")
            },
        }
    }
}

impl std::error::Error for ReificationError {}

/// **A configuration as a process.** See the module header for the shape and
/// for the three non-obvious details (installed continuations excluded, the
/// guard restored onto `Receive.condition`, `locally_free` recomputed the
/// normalizer's way).
///
/// Deterministic: `HotStoreState`'s maps are `BTreeMap`s (channel-ordered), and
/// within a channel the store order is preserved, so two validators reifying the
/// same configuration emit the same `Par` bytes.
pub fn reify(state: &SpeculativeState) -> Result<Par, ReificationError> {
    let mut process = Par::default();

    for (channel, data) in state.data.iter() {
        for datum in data.iter() {
            let payload = &datum.a.pars;
            let mut locally_free = channel.locally_free.clone();
            for par in payload.iter() {
                locally_free = union(locally_free, par.locally_free.clone());
            }
            let connective_used =
                channel.connective_used || payload.iter().any(|par| par.connective_used);
            process = process.prepend_send(Send {
                chan: Some(channel.clone()),
                data: payload.clone(),
                persistent: datum.persist,
                locally_free,
                connective_used,
            });
        }
    }

    for (channels, continuations) in state.continuations.iter() {
        if channels.is_empty() {
            return Err(ReificationError::EmptyChannelGroup);
        }
        for waiting in continuations.iter() {
            let (body, guard) = match &waiting.continuation.tagged_cont {
                Some(TaggedCont::ParBody(body_with_random)) => (
                    body_with_random.body.clone().unwrap_or_default(),
                    waiting.continuation.guard.clone(),
                ),
                Some(TaggedCont::ScalaBodyRef(body_ref)) => {
                    return Err(ReificationError::SystemContinuation { body_ref: *body_ref })
                },
                // `TaggedContinuation { tagged_cont: None }` is the dispatcher's
                // `Skip`: a receive whose body really is `Nil`.
                None => (Par::default(), waiting.continuation.guard.clone()),
            };

            // `WaitingContinuation::patterns` is one `BindPattern` per channel,
            // in channel order — the same pairing `Reduce::eval_receive` unzips.
            let mut binds = Vec::with_capacity(channels.len());
            let mut bind_count = 0i32;
            let mut sources_locally_free: Vec<u8> = Vec::new();
            let mut patterns_locally_free: Vec<u8> = Vec::new();
            let mut connective_used = false;
            for (position, channel) in channels.iter().enumerate() {
                let pattern = waiting.patterns.get(position).cloned().unwrap_or_default();
                bind_count += pattern.free_count;
                sources_locally_free = union(sources_locally_free, channel.locally_free.clone());
                for par in pattern.patterns.iter() {
                    patterns_locally_free = union(patterns_locally_free, par.locally_free.clone());
                }
                connective_used = connective_used || channel.connective_used;
                binds.push(ReceiveBind {
                    patterns: pattern.patterns,
                    source: Some(channel.clone()),
                    remainder: pattern.remainder,
                    free_count: pattern.free_count,
                });
            }

            // The normalizer's own computation (`p_input_normalizer.rs`): the
            // sources' and patterns' free sets, unioned with the body's and the
            // guard's filtered and adjusted by `bind_count`.
            let guard_locally_free = guard
                .as_ref()
                .map(|par| par.locally_free.clone())
                .unwrap_or_default();
            let guard_connective_used = guard
                .as_ref()
                .map(|par| par.connective_used)
                .unwrap_or(false);
            let locally_free = union(
                sources_locally_free,
                union(
                    patterns_locally_free,
                    filter_and_adjust_bitset(
                        union(body.locally_free.clone(), guard_locally_free),
                        bind_count as usize,
                    ),
                ),
            );

            process = process.prepend_receive(Receive {
                binds,
                persistent: waiting.persist,
                peek: !waiting.peeks.is_empty(),
                bind_count,
                locally_free,
                connective_used: connective_used || body.connective_used || guard_connective_used,
                condition: guard,
                body: Some(body),
            });
        }
    }

    Ok(process)
}

// ══════════════════════════════════════════════════════════════════════════
// The three delivered collections
// ══════════════════════════════════════════════════════════════════════════

/// The three collections `x!(P)[n]` places on `x`: the FIPS's `success` and
/// `failure`, plus the USER-decided third map `truncated`.
///
/// Each is an `ESet` of `EList` entries. See the module header for the shape and
/// the reasoning.
#[derive(Clone, Debug, PartialEq)]
pub struct SpeculationDelivery {
    /// Branches that reached quiescence. Entry: `[step…, configuration]`.
    pub success: Par,
    /// Branches the depth bound cut short. Entry:
    /// `[step…, (handle, frontier, configuration)]`.
    pub truncated: Par,
    /// Branches that raised. Entry: `[step…, [code, message]]`.
    pub failure: Par,
}

impl SpeculationDelivery {
    /// The three collections in FIPS order, for a caller placing them on a
    /// channel.
    ///
    /// ⚠ This is a *positional* reading — `[success, truncated, failure]` — and
    /// a caller that pairs it with channel names by position is one edit away
    /// from publishing the failure set on the truncated channel. Use
    /// [`on_report_channels`](Self::on_report_channels) when the pairing is what
    /// is wanted; this stays because
    /// [`SPEC_DELIVERY_CHANNEL`](crate::lookahead::SPEC_DELIVERY_CHANNEL)
    /// publishes the three as one ordered datum, where position IS the shape.
    pub fn as_slice(&self) -> [&Par; 3] {
        [&self.success, &self.truncated, &self.failure]
    }

    /// **Each collection paired with the reserved channel it belongs on.**
    ///
    /// [`crate::lookahead`] owns the channel names; this module owns the values.
    /// Naming the pairing here — in one place, from the constants themselves
    /// rather than from a parallel spelling — is what stops the two from
    /// drifting: a renamed channel is a compile-time edit in exactly one file,
    /// and a reordered field cannot silently move a collection onto the wrong
    /// wire.
    ///
    /// The order is [`SPEC_REPORT_CHANNELS`](crate::lookahead::SPEC_REPORT_CHANNELS)'s,
    /// which is the order a transcript shows, NOT [`as_slice`](Self::as_slice)'s
    /// FIPS order — and the fact that those two differ is precisely why the
    /// pairing must not be positional.
    pub fn on_report_channels(&self) -> [(&'static str, &Par); 3] {
        [
            (SPEC_SUCCESS_CHANNEL, &self.success),
            (SPEC_FAILURE_CHANNEL, &self.failure),
            (SPEC_TRUNCATED_CHANNEL, &self.truncated),
        ]
    }
}

/// A ground `ESet` over `elements` — no remainder, no free variables, no
/// connective. `ParSet` sorts, so the encoding is canonical.
fn ground_set(elements: Vec<Par>) -> Par {
    new_eset_par(elements, Vec::new(), false, None::<Var>, Vec::new(), false)
}

/// A ground `EList` over `elements`.
fn ground_list(elements: Vec<Par>) -> Par {
    new_elist_par(elements, Vec::new(), false, None::<Var>, Vec::new(), false)
}

/// One `success` entry: `[step₀, …, step_{k-1}, ⟦configuration⟧]`.
pub fn success_entry(leaf: &QuiescentLeaf) -> Result<Par, ReificationError> {
    let mut elements = trace_pars(&leaf.trace);
    elements.push(reify(&leaf.state)?);
    Ok(ground_list(elements))
}

/// One `truncated` entry: `[step₀, …, step_{k-1}, (handle, frontier,
/// ⟦configuration⟧)]`.
///
/// `handle` is [`trace_digest`] of the branch's trace — the name a program uses
/// to say which branch to resume; `frontier` is `|E(S)|` at the cut, i.e. how
/// many ways this branch could have continued.
pub fn truncated_entry(leaf: &TruncatedLeaf) -> Result<Par, ReificationError> {
    let mut elements = trace_pars(&leaf.branch.trace);
    elements.push(new_etuple_par(vec![
        new_gbytearray_par(trace_digest(&leaf.branch.trace).bytes(), Vec::new(), false),
        new_gint_par(leaf.branch.frontier as i64, Vec::new(), false),
        reify(&leaf.branch.state)?,
    ]));
    Ok(ground_list(elements))
}

/// One `failure` entry: `[step₀, …, step_{k-1}, [code, message]]` — the FIPS's
/// *"extra two-element list containing an error code for the failure and a
/// message … concatenated to the end of the trace"*.
pub fn failure_entry(leaf: &AbortedLeaf) -> Par {
    let mut elements = trace_pars(&leaf.trace);
    elements.push(ground_list(vec![
        new_gint_par(leaf.code.as_i64(), Vec::new(), false),
        new_gstring_par(leaf.message.clone(), Vec::new(), false),
    ]));
    ground_list(elements)
}

/// **Assemble the three collections.**
///
/// Fails closed if any leaf's configuration cannot be reified
/// ([`ReificationError`]) rather than delivering a partial `success` set — a
/// consumer that filters over the results would silently be filtering over
/// fewer branches than the search found.
pub fn deliver(exploration: &Exploration) -> Result<SpeculationDelivery, ReificationError> {
    let mut success = Vec::with_capacity(exploration.success.len());
    for leaf in exploration.success.iter() {
        success.push(success_entry(leaf)?);
    }
    let mut truncated = Vec::with_capacity(exploration.truncated.len());
    for leaf in exploration.truncated.iter() {
        truncated.push(truncated_entry(leaf)?);
    }
    let mut failure = Vec::with_capacity(exploration.failure.len());
    failure.extend(exploration.failure.iter().map(failure_entry));

    Ok(SpeculationDelivery {
        success: ground_set(success),
        truncated: ground_set(truncated),
        failure: ground_set(failure),
    })
}

// ══════════════════════════════════════════════════════════════════════════
// Projection: the answer, without the rest of the configuration
// ══════════════════════════════════════════════════════════════════════════

/// The data resting on **one channel** of a configuration — the projection a
/// consumer that only wants the answer reads.
///
/// A leaf is the whole terminal configuration, which is the FIPS-faithful
/// answer and is also everything a caller injected: a guest whose lowering
/// installs a receiver network leaves that network resting in every leaf. When
/// the question is *"what did this branch compute?"* rather than *"what does
/// this branch consist of?"*, the answer is the data on the channel the program
/// published to — exactly what a live run reads back — and this is that read,
/// against a retained configuration instead of a live store.
///
/// Read from a [`SpeculativeState`], never from `to_map()`: `to_map` iterates
/// the *data* map and would miss a continuation on a data-less channel entirely
/// (correction 3). Here only data is wanted, so the distinction does not bite —
/// but the state this reads was captured with `snapshot()` for that reason.
pub fn resting_on(state: &SpeculativeState, channel: &Par) -> Vec<Par> {
    let Some(data) = state.data.get(channel) else {
        return Vec::new();
    };
    let mut values = Vec::with_capacity(data.len());
    for datum in data.iter() {
        // One `Par` per datum. A `ListParWithRandom` carrying several `Par`s is
        // a polyadic send; the flattening matches how the runtime readback
        // helpers present resting data.
        values.extend(datum.a.pars.iter().cloned());
    }
    values
}

/// [`resting_on`] for a `GString` channel — the shape every observation channel
/// in this tree uses (`"OUT"`, the reserved `^fired` / `^drive-err` /
/// `^drive-fuel` channels).
pub fn resting_on_string(state: &SpeculativeState, channel: &str) -> Vec<Par> {
    resting_on(state, &new_gstring_par(channel.to_string(), Vec::new(), false))
}

/// A stable textual fingerprint of the data resting on `channel` — the
/// discriminator an acceptance test counts distinct outcomes with.
///
/// Sorted, so the multiset is compared rather than the store order.
pub fn resting_fingerprint(state: &SpeculativeState, channel: &str) -> Vec<String> {
    use prost::Message;
    let resting = resting_on_string(state, channel);
    let mut rendered = Vec::with_capacity(resting.len());
    for par in resting.iter() {
        let bytes = par.encode_to_vec();
        let mut hex = String::with_capacity(bytes.len() * 2);
        for byte in bytes.iter() {
            hex.push_str(&format!("{byte:02x}"));
        }
        rendered.push(hex);
    }
    rendered.sort();
    rendered
}

/// The `Expr` a delivered collection carries, for a caller that needs to embed
/// it somewhere an `Expr` is wanted rather than a `Par`.
pub fn as_expr(collection: &Par) -> Option<&Expr> {
    collection.exprs.first()
}
