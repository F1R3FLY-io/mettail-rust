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
mod reify_tests {
    use super::*;
    use models::rhoapi::{BindPattern, ListParWithRandom, ParWithRandom, TaggedContinuation};
    use models::rust::utils::new_freevar_par;
    use prost::Message;
    use rspace_plus_plus::rspace::internal::{Datum, WaitingContinuation};

    fn channel(name: &str) -> Par {
        new_gstring_par(name.to_string(), Vec::new(), false)
    }

    /// A datum built the way the store builds one, so its `source` is a real content hash
    /// rather than a default — the reified `Par` does not read it, but constructing the
    /// fixture faithfully keeps the test from passing for a reason the production path lacks.
    ///
    /// ★ It *is* read now: [`reify`] and [`resting_on`] order a channel's data by
    /// `source.hash`, so a fixture with a default source would order by a constant and the
    /// within-channel cells below would pass vacuously.
    fn datum(chan: &Par, value: i64) -> Datum<ListParWithRandom> {
        Datum::create(
            chan,
            ListParWithRandom {
                pars: vec![new_gint_par(value, Vec::new(), false)],
                random_state: Vec::new(),
            },
            false,
        )
    }

    /// A waiting continuation built the way `consume` builds one, for the same reason: its
    /// `source` is a real `Consume` hash, which is the key the group's order is now taken from.
    fn waiting(
        channels: &[Par],
        body: i64,
        persist: bool,
        peek: bool,
    ) -> WaitingContinuation<BindPattern, TaggedContinuation> {
        let patterns: Vec<BindPattern> = channels
            .iter()
            .map(|_| BindPattern {
                patterns: vec![new_freevar_par(0, Vec::new())],
                remainder: None,
                free_count: 1,
            })
            .collect();
        let continuation = TaggedContinuation {
            guard: None,
            tagged_cont: Some(TaggedCont::ParBody(ParWithRandom {
                body: Some(new_gint_par(body, Vec::new(), false)),
                random_state: Vec::new(),
            })),
        };
        let peeks = match peek {
            true => std::collections::BTreeSet::from([0i32]),
            false => std::collections::BTreeSet::new(),
        };
        WaitingContinuation::create(&channels.to_vec(), &patterns, &continuation, persist, peeks)
    }

    /// ★ Insertion order into the store must not reach the reified bytes.
    ///
    /// `HotStoreState`'s maps are `HashMap`s with a per-process `RandomState`, so their
    /// iteration order is not a property of the configuration. `reify` builds a `Par` with
    /// `prepend_send`/`prepend_receive`, which do not sort — so before the canonical ordering
    /// landed, map order *was* field order *was* emitted bytes, and those bytes ride inside
    /// `^spec-success` / `^spec-truncated` / `^spec-delivery` and the bare reply term.
    ///
    /// Permuting insertion order is the unit-test form of the cross-process check: it is what
    /// a different `RandomState` amounts to, without needing a second process.
    #[test]
    fn reify_does_not_depend_on_insertion_order() {
        // Enough channels that a hash order is very unlikely to coincide with any fixed order.
        let names = ["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta"];

        let build = |order: &dyn Fn(usize) -> usize| -> Par {
            let mut state = SpeculativeState::default();
            for slot in 0..names.len() {
                let index = order(slot);
                let chan = channel(names[index]);
                let value = datum(&chan, index as i64);
                state.data.insert(chan, vec![value]);
            }
            reify(&state).expect("a data-only configuration reifies")
        };

        let forward = build(&|slot| slot);
        let reverse = build(&|slot| names.len() - 1 - slot);
        // A third, non-monotone permutation, so the test cannot pass by the two orders being
        // symmetric under whatever the map happens to do.
        let shuffled_order = [3usize, 0, 6, 1, 7, 4, 2, 5];
        let shuffled = build(&|slot| shuffled_order[slot]);

        assert_eq!(
            forward.encode_to_vec(),
            reverse.encode_to_vec(),
            "★ reversing insertion order changed the reified bytes — the configuration's \
             identity must not include the order the host happened to stage it in"
        );
        assert_eq!(
            forward.encode_to_vec(),
            shuffled.encode_to_vec(),
            "★ permuting insertion order changed the reified bytes"
        );
        assert_eq!(forward.sends.len(), names.len(), "every send must survive the ordering");
    }

    // ── the WITHIN-channel axis (D1/D2) ──────────────────────────────────────────────────
    //
    // ★ The cell above inserts exactly ONE datum per channel, so it pins the ACROSS-channel
    // axis only. It was green for the whole time `reify` emitted a channel's data in store
    // order — which is *reverse arrival* order, because `HotStore::put_datum` prepends and
    // every branch of a `|` is a detached `tokio::spawn`. The two cells below are the missing
    // axis, and they are the cells that go red if the `sort_by_cached_key` in `reify` is
    // removed.

    /// ★ Permuting the data WITHIN one channel must not reach the reified bytes.
    ///
    /// Three permutations of five data on a single channel — forward, reverse, and a
    /// non-monotone shuffle so the cell cannot pass by the first two being symmetric under
    /// whatever the emitter happens to do.
    #[test]
    fn reify_does_not_depend_on_the_order_within_one_channel() {
        let chan = channel("one");
        // Five DISTINCT payloads: two byte-identical data on one channel have the same
        // `Produce` hash and the same emitted `Send`, so they could not witness an ordering
        // dependence at all. Distinctness is what makes this cell able to fail.
        let data: Vec<Datum<ListParWithRandom>> = (0..5).map(|value| datum(&chan, value)).collect();

        let build = |order: &[usize]| -> Vec<u8> {
            let mut state = SpeculativeState::default();
            state
                .data
                .insert(chan.clone(), order.iter().map(|index| data[*index].clone()).collect());
            reify(&state)
                .expect("a data-only configuration reifies")
                .encode_to_vec()
        };

        let forward = build(&[0, 1, 2, 3, 4]);
        assert_eq!(
            forward,
            build(&[4, 3, 2, 1, 0]),
            "★ reversing the order of the data ON ONE CHANNEL changed the reified bytes. A \
             channel's `Vec` is REVERSE-ARRIVAL order — `HotStore::put_datum` prepends — so \
             that is the scheduler deciding published bytes, not the configuration."
        );
        assert_eq!(
            forward,
            build(&[2, 0, 4, 1, 3]),
            "★ permuting the data on one channel changed the reified bytes"
        );
        let reified = reify(&{
            let mut state = SpeculativeState::default();
            state.data.insert(chan.clone(), data.clone());
            state
        })
        .expect("reify");
        assert_eq!(reified.sends.len(), 5, "every datum must survive the ordering");
    }

    /// ★ …and the same for two continuations waiting on ONE channel group.
    ///
    /// `HotStore::put_continuation` prepends too (`insert(0, wc)`), so a group's `Vec` carries
    /// the identical artifact. The two continuations differ in their bodies, so the emitted
    /// `Receive`s are distinguishable and the cell can fail.
    #[test]
    fn reify_does_not_depend_on_the_order_within_one_continuation_group() {
        let group = vec![channel("alpha"), channel("beta")];
        let first = waiting(&group, 1, false, false);
        let second = waiting(&group, 2, false, false);
        // A third that ties with `second` on the `Consume` hash and differs only in `peeks` —
        // the one bit the hash does NOT cover and the emitted `Receive` DOES read. Its
        // presence is why the sort key carries `peeks.is_empty()` alongside the hash.
        let peeking = waiting(&group, 2, false, true);
        assert_eq!(
            second.source.hash.bytes(),
            peeking.source.hash.bytes(),
            "the fixture's premise: `Consume::create` does not hash `peeks`"
        );

        let build = |order: &[usize]| -> Vec<u8> {
            let members = [first.clone(), second.clone(), peeking.clone()];
            let mut state = SpeculativeState::default();
            state
                .continuations
                .insert(group.clone(), order.iter().map(|index| members[*index].clone()).collect());
            reify(&state)
                .expect("a continuation-only configuration reifies")
                .encode_to_vec()
        };

        let forward = build(&[0, 1, 2]);
        assert_eq!(
            forward,
            build(&[2, 1, 0]),
            "★ reversing the order of the continuations IN ONE GROUP changed the reified bytes"
        );
        assert_eq!(forward, build(&[1, 2, 0]), "★ …and so did permuting them");
    }

    /// …and the ordering is canonical rather than merely stable: it is the channels' own
    /// encoded bytes, so it is a function of the configuration and of nothing else.
    #[test]
    fn reify_orders_sends_by_their_channel_encoding() {
        let mut state = SpeculativeState::default();
        for name in ["gamma", "alpha", "beta"] {
            let chan = channel(name);
            let value = datum(&chan, 0);
            state.data.insert(chan, vec![value]);
        }
        let reified = reify(&state).expect("a data-only configuration reifies");

        let mut emitted: Vec<Vec<u8>> = reified
            .sends
            .iter()
            .map(|send| {
                send.chan
                    .as_ref()
                    .expect("every send has a channel")
                    .encode_to_vec()
            })
            .collect();
        let mut canonical = emitted.clone();
        canonical.sort();
        // `prepend_send` pushes to the FRONT, so the emitted order is the reverse of the
        // iteration order. Assert against the reversal rather than asserting a direction the
        // constructor does not promise.
        emitted.reverse();
        assert_eq!(emitted, canonical, "sends must be ordered by their channel's encoding");
    }

    // ── the projection the registered-guest path actually takes (D3) ─────────────────────

    /// ★ [`resting_on`] must not publish store order either — and this is the projection the
    /// `[*]` demos take, so it is the one with a live consumer.
    ///
    /// Two effects, and the second is why this is not merely cosmetic: the `EList` published on
    /// `^spec-success` is order-sensitive, and the request server publishes **one bare reply
    /// datum per term in this order** while `Publisher::publish` splits the request's
    /// randomness `split_short(index)` **by position** — so a permutation of the terms permutes
    /// their `random_state`, their `Produce` hashes, and the post-deploy tuplespace content.
    #[test]
    fn resting_on_does_not_depend_on_the_order_within_the_channel() {
        let chan = channel("OUT");
        let data: Vec<Datum<ListParWithRandom>> = (0..4).map(|value| datum(&chan, value)).collect();

        let build = |order: &[usize]| -> Vec<Vec<u8>> {
            let mut state = SpeculativeState::default();
            state
                .data
                .insert(chan.clone(), order.iter().map(|index| data[*index].clone()).collect());
            resting_on(&state, &chan)
                .iter()
                .map(|par| par.encode_to_vec())
                .collect()
        };

        let forward = build(&[0, 1, 2, 3]);
        assert_eq!(forward.len(), 4, "every datum must be projected");
        assert_eq!(
            forward,
            build(&[3, 2, 1, 0]),
            "★ reversing the store order changed the PROJECTED SEQUENCE — and the reply datum \
             at position i is minted with `split_short(i)`, so this permutes unforgeable names"
        );
        assert_eq!(forward, build(&[2, 0, 3, 1]), "★ …and so does any other permutation");
    }

    /// ⚠ …but the flattening WITHIN one datum stays put. A polyadic send's payload is
    /// genuinely ordered — `@c!(1, 2)` and `@c!(2, 1)` are different sends — so sorting there
    /// would erase a distinction the program wrote down.
    ///
    /// This is the cell that stops the D3 fix from being over-applied, which is the failure
    /// mode a "sort everything" reading of the defect would produce.
    #[test]
    fn resting_on_preserves_the_order_within_one_polyadic_datum() {
        let chan = channel("OUT");
        let polyadic = |first: i64, second: i64| {
            Datum::create(
                &chan,
                ListParWithRandom {
                    pars: vec![
                        new_gint_par(first, Vec::new(), false),
                        new_gint_par(second, Vec::new(), false),
                    ],
                    random_state: Vec::new(),
                },
                false,
            )
        };
        let read = |datum: Datum<ListParWithRandom>| -> Vec<i64> {
            let mut state = SpeculativeState::default();
            state.data.insert(chan.clone(), vec![datum]);
            resting_on(&state, &chan)
                .iter()
                .map(|par| match par.exprs.first().and_then(|e| e.expr_instance.as_ref()) {
                    Some(models::rhoapi::expr::ExprInstance::GInt(value)) => *value,
                    other => panic!("the fixture publishes GInts, got {other:?}"),
                })
                .collect()
        };
        assert_eq!(read(polyadic(1, 2)), vec![1, 2], "a polyadic payload keeps its order");
        assert_eq!(read(polyadic(2, 1)), vec![2, 1], "★ …including when it is the reverse");
    }
}

// ══════════════════════════════════════════════════════════════════════════
// ★★ LAYER 1 — THE PUBLICATION LAW
// ══════════════════════════════════════════════════════════════════════════

/// **The law that generalises the whole defect class**, as one property:
///
/// > for any two configurations `S`, `S'` with
/// > `content_fingerprint(S) == content_fingerprint(S')`, **every published projection is
/// > byte-identical** — [`reify`], [`resting_on`] on every channel, and [`deliver`] over
/// > leaves built from each.
///
/// ## Why a law rather than more cells
///
/// Each defect in this class was found by noticing that some *particular* published field was
/// keyed by something the host assigned. Fixing them one at a time leaves the next one
/// invisible until someone notices it too — which is exactly how D1 and D3 survived the fix
/// that named them (826bb96e canonicalised the across-channel order and *wrote down* that the
/// within-channel order was fine).
///
/// The law removes the enumeration. Configuration **identity** —
/// [`super::content_fingerprint`], what the search compares states with, what
/// `distinct_success_configurations` counts — and configuration **publication** are asserted to
/// be *the same equivalence relation*. Anything a projection reads that identity does not carry
/// makes publication strictly finer and fails this test, whether or not anybody thought to
/// write a cell for it.
///
/// ## The witness, and why it is a permutation
///
/// The generator produces a **blueprint** (what rests where, with no order committed to) and
/// two seeds. Each seed realises the blueprint into a `SpeculativeState` with a different
/// `HashMap` insertion order *and* a different `Vec` order within every channel and group.
/// Those are precisely the two axes [`super::content_fingerprint`] is invariant under by
/// construction — it sorts both — and precisely the two axes a real node varies along, because
/// `HashMap` is `RandomState`-seeded per process and `HotStore` prepends into a `Vec` whose
/// arrival order races.
///
/// So the antecedent is **established, not assumed**: the property asserts the two fingerprints
/// are equal before it asserts anything about bytes. A generator that accidentally produced
/// two different configurations would fail there, loudly, rather than passing vacuously.
///
/// No tokio, no threads, no subprocess — the permutation is what a second process amounts to.
#[cfg(test)]
mod publication_law {
    use super::*;
    use crate::speculation::content_fingerprint;
    use models::rhoapi::{BindPattern, ListParWithRandom, ParWithRandom, TaggedContinuation};
    use models::rust::utils::new_freevar_par;
    use proptest::prelude::*;
    use prost::Message;
    use rspace_plus_plus::rspace::internal::{Datum, WaitingContinuation};

    use crate::speculation::search::{
        AbortedLeaf, ErrorCode, Exploration, ExplorationStats, QuiescentLeaf, TruncatedLeaf,
    };
    use crate::speculation::ResumableBranch;

    /// A configuration **described without an order**: which payloads rest on which channel,
    /// and which continuations wait on which group. Two realisations of one blueprint are two
    /// configurations that are equal as configurations and differ only in host-assigned order.
    #[derive(Clone, Debug)]
    struct Blueprint {
        /// `(channel index, the payload value of each datum resting on it)`.
        data: Vec<(usize, Vec<i64>)>,
        /// `(the channel-index group, the `(body, persist, peek)` of each waiting continuation)`.
        continuations: Vec<(Vec<usize>, Vec<(i64, bool, bool)>)>,
    }

    /// SplitMix64 — Steele, Lea & Flood, *"Fast splittable pseudorandom number generators"*
    /// (OOPSLA 2014), <https://doi.org/10.1145/2660193.2660195>. Used here only as a cheap,
    /// dependency-free, fully deterministic mixer for the permutation witness.
    fn splitmix64(state: u64) -> u64 {
        let mut z = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A permutation of `0..len`, a pure function of `(seed, salt)`.
    ///
    /// A *witness* rather than a shuffle: nothing here reads a thread-local RNG, so a failing
    /// case reproduces exactly from the proptest seed alone. Key collisions are harmless — a
    /// stable sort still yields a permutation.
    fn permutation(len: usize, seed: u64, salt: u64) -> Vec<usize> {
        let mut order: Vec<usize> = (0..len).collect();
        order.sort_by_key(|index| splitmix64(seed ^ splitmix64(salt ^ (*index as u64))));
        order
    }

    fn channel(index: usize) -> Par {
        new_gstring_par(format!("chan-{index}"), Vec::new(), false)
    }

    fn datum(chan: &Par, value: i64) -> Datum<ListParWithRandom> {
        Datum::create(
            chan,
            ListParWithRandom {
                pars: vec![new_gint_par(value, Vec::new(), false)],
                random_state: Vec::new(),
            },
            false,
        )
    }

    fn waiting(
        channels: &[Par],
        body: i64,
        persist: bool,
        peek: bool,
    ) -> WaitingContinuation<BindPattern, TaggedContinuation> {
        let patterns: Vec<BindPattern> = channels
            .iter()
            .map(|_| BindPattern {
                patterns: vec![new_freevar_par(0, Vec::new())],
                remainder: None,
                free_count: 1,
            })
            .collect();
        let continuation = TaggedContinuation {
            guard: None,
            tagged_cont: Some(TaggedCont::ParBody(ParWithRandom {
                body: Some(new_gint_par(body, Vec::new(), false)),
                random_state: Vec::new(),
            })),
        };
        let peeks = match peek {
            true => std::collections::BTreeSet::from([0i32]),
            false => std::collections::BTreeSet::new(),
        };
        WaitingContinuation::create(&channels.to_vec(), &patterns, &continuation, persist, peeks)
    }

    /// Realise a blueprint under one permutation witness.
    ///
    /// `seed` decides the `HashMap` insertion order across channels and groups **and** the
    /// `Vec` order within each — the two axes a second process varies along.
    fn realize(blueprint: &Blueprint, seed: u64) -> SpeculativeState {
        let mut state = SpeculativeState::default();

        let channel_order = permutation(blueprint.data.len(), seed, 0);
        for (slot, position) in channel_order.into_iter().enumerate() {
            let (index, values) = &blueprint.data[position];
            let chan = channel(*index);
            let built: Vec<_> = values.iter().map(|value| datum(&chan, *value)).collect();
            let within = permutation(built.len(), seed, 1 + slot as u64);
            let ordered: Vec<_> = within.into_iter().map(|at| built[at].clone()).collect();
            // A repeated channel index in the blueprint is a legitimate shape (`insert`
            // replaces); it is not special-cased because the two realisations agree on which
            // entry wins only if they agree on the whole multiset, which is the point.
            state.data.entry(chan).or_default().extend(ordered);
        }

        let group_order = permutation(blueprint.continuations.len(), seed, 1_000);
        for (slot, position) in group_order.into_iter().enumerate() {
            let (indices, members) = &blueprint.continuations[position];
            let group: Vec<Par> = indices.iter().map(|index| channel(*index)).collect();
            let built: Vec<_> = members
                .iter()
                .map(|(body, persist, peek)| waiting(&group, *body, *persist, *peek))
                .collect();
            let within = permutation(built.len(), seed, 1_001 + slot as u64);
            let ordered: Vec<_> = within.into_iter().map(|at| built[at].clone()).collect();
            state
                .continuations
                .entry(group)
                .or_default()
                .extend(ordered);
        }

        state
    }

    /// Every channel named by a blueprint, so `resting_on` can be checked on all of them —
    /// including the ones that carry only continuations, where the projection is empty and the
    /// law still has to hold.
    fn every_channel(blueprint: &Blueprint) -> Vec<Par> {
        let mut indices: Vec<usize> = blueprint.data.iter().map(|(index, _)| *index).collect();
        for (group, _) in blueprint.continuations.iter() {
            indices.extend(group.iter().copied());
        }
        indices.sort_unstable();
        indices.dedup();
        indices.into_iter().map(channel).collect()
    }

    /// The three delivered collections over leaves built from one configuration, encoded.
    ///
    /// One leaf of each kind, so the property covers `success_entry` (which reifies),
    /// `truncated_entry` (which reifies inside a tuple) and `failure_entry` (which does not) in
    /// one comparison.
    fn delivered(state: &SpeculativeState) -> Vec<Vec<u8>> {
        let exploration = Exploration {
            success: vec![QuiescentLeaf { trace: Vec::new(), state: state.clone() }],
            truncated: vec![TruncatedLeaf {
                branch: ResumableBranch {
                    state: state.clone(),
                    trace: Vec::new(),
                    frontier: 1,
                },
            }],
            failure: vec![AbortedLeaf {
                trace: Vec::new(),
                code: ErrorCode::Interpreter,
                message: "a fixed message, so the failure leaf cannot mask a real difference"
                    .to_string(),
            }],
            root: state.clone(),
            stats: ExplorationStats::default(),
        };
        let delivery = deliver(&exploration).expect("the fixture configurations reify");
        delivery
            .as_slice()
            .iter()
            .map(|collection| collection.encode_to_vec())
            .collect()
    }

    prop_compose! {
        /// A blueprint over a small channel alphabet, so collisions — two channels sharing an
        /// index, two data sharing a payload, two continuations sharing a body — are *likely*
        /// rather than merely possible. Ties on the sort key are the case a "sort by content"
        /// fix is least obviously correct on, so the generator is tuned to produce them.
        ///
        /// ★ The first entry is fixed: two DISTINCT data on ONE channel. That shape is what
        /// makes the property able to fail at all — a channel carrying one datum, or two
        /// identical ones, cannot witness a within-channel ordering dependence — and no
        /// generated blueprint is allowed to omit it. It is the anti-vacuity guard, in the
        /// generator rather than in a comment.
        fn blueprint()(
            data in prop::collection::vec(
                (0usize..4, prop::collection::vec(-3i64..3, 1..4)),
                0..4,
            ),
            continuations in prop::collection::vec(
                (
                    prop::collection::vec(0usize..4, 1..3),
                    prop::collection::vec((-3i64..3, any::<bool>(), any::<bool>()), 1..3),
                ),
                0..3,
            ),
        ) -> Blueprint {
            let mut all = Vec::with_capacity(data.len() + 1);
            all.push((7usize, vec![0i64, 1i64]));
            all.extend(data);
            Blueprint { data: all, continuations }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// ★★ THE LAW. See the module header.
        #[test]
        fn publication_is_a_function_of_the_configuration(
            blueprint in blueprint(),
            left_seed in any::<u64>(),
            right_seed in any::<u64>(),
        ) {
            let left = realize(&blueprint, left_seed);
            let right = realize(&blueprint, right_seed);

            // ── the ANTECEDENT, established rather than assumed ──────────────────────────
            prop_assert_eq!(
                content_fingerprint(&left),
                content_fingerprint(&right),
                "the two realisations must be the SAME configuration — if this fails the \
                 generator is wrong and everything below it would be vacuous"
            );

            // ── 1. `reify` ───────────────────────────────────────────────────────────────
            let left_reified = reify(&left).expect("a fixture configuration reifies");
            let right_reified = reify(&right).expect("a fixture configuration reifies");
            prop_assert_eq!(
                left_reified.encode_to_vec(),
                right_reified.encode_to_vec(),
                "★ two configurations with one identity published two different processes"
            );

            // ── 2. `resting_on`, on every channel the blueprint names ────────────────────
            for chan in every_channel(&blueprint) {
                let left_resting: Vec<Vec<u8>> =
                    resting_on(&left, &chan).iter().map(|par| par.encode_to_vec()).collect();
                let right_resting: Vec<Vec<u8>> =
                    resting_on(&right, &chan).iter().map(|par| par.encode_to_vec()).collect();
                prop_assert_eq!(
                    left_resting,
                    right_resting,
                    "★ the projection onto one channel depended on the store order — and the \
                     reply datum at position i is minted with `split_short(i)`"
                );
            }

            // ── 3. `deliver` ─────────────────────────────────────────────────────────────
            prop_assert_eq!(
                delivered(&left),
                delivered(&right),
                "★ the three FIPS collections differed for one configuration"
            );
        }
    }

    /// The generator's own guarantee, asserted rather than trusted: every blueprint carries a
    /// channel with two DISTINCT data, which is the shape without which the law is vacuous.
    ///
    /// ★ This exists because the failure mode it guards against is silent. A property that
    /// generates only single-datum channels passes whether or not `reify` sorts within a
    /// channel, and reads exactly like a property that does not.
    #[test]
    fn the_generator_always_produces_the_discriminating_shape() {
        use proptest::strategy::{Strategy, ValueTree};
        use proptest::test_runner::TestRunner;

        let mut runner = TestRunner::deterministic();
        for _ in 0..64 {
            let blueprint = blueprint()
                .new_tree(&mut runner)
                .expect("the blueprint strategy must produce a value")
                .current();
            let discriminating = blueprint.data.iter().any(|(_, values)| {
                let mut distinct = values.clone();
                distinct.sort_unstable();
                distinct.dedup();
                distinct.len() >= 2
            });
            assert!(
                discriminating,
                "★ a blueprint with no channel carrying two distinct data cannot witness a \
                 within-channel ordering dependence: {blueprint:?}"
            );
        }
    }
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
            assert_ne!(step_digest(&base), step_digest(&other), "{label} must be a different step");
        }
    }

    // ── LAYER 4: the same invariant, on everything DOWNSTREAM of the digest ─────────────
    //
    // ★ `store_indices_do_not_change_the_digest` covers `step_digest` alone. Every published
    // artifact that folds it — the trace handle, the wire trace list, the three collections —
    // inherits the property only if nothing along the way reintroduces an index. Asserting
    // that at the leaf and hoping it propagates is exactly the reasoning that left D1 and D3
    // in place.

    /// The **trace handle** — what a truncated leaf publishes and what `resume` takes back —
    /// is index-free too.
    #[test]
    fn store_indices_do_not_change_the_trace_digest() {
        let indexed = vec![name(1, &[2, 3], 0, &[0, 1]), name(4, &[5], 2, &[7])];
        let renumbered = vec![name(1, &[2, 3], 9, &[6, 4]), name(4, &[5], 0, &[3])];
        assert_eq!(
            trace_digest(&indexed),
            trace_digest(&renumbered),
            "★ a resumption handle keyed by store position would name a branch nobody else \
             can reproduce"
        );
        // …and the handle still separates traces that differ in CONTENT, and in ORDER.
        assert_ne!(
            trace_digest(&indexed),
            trace_digest(&[indexed[1].clone(), indexed[0].clone()]),
            "two branches that fired the same rendezvous in different orders are different \
             branches"
        );
    }

    /// The **wire trace list** — the `EList` of step digests every report datum carries —
    /// is index-free, encoded.
    #[test]
    fn store_indices_do_not_change_the_published_trace_list() {
        use prost::Message;
        let indexed = vec![name(1, &[2, 3], 0, &[0, 1]), name(4, &[5], 2, &[7])];
        let renumbered = vec![name(1, &[2, 3], 9, &[6, 4]), name(4, &[5], 0, &[3])];
        let encode = |trace: &[RendezvousName]| -> Vec<Vec<u8>> {
            trace_pars(trace)
                .iter()
                .map(|par| par.encode_to_vec())
                .collect()
        };
        assert_eq!(encode(&indexed), encode(&renumbered));
        assert_eq!(encode(&indexed).len(), 2, "and it is not empty");
    }

    /// ★ …and the whole [`deliver`] output. This is the end of the chain: three collections,
    /// each folding trace digests and reified configurations, byte-identical under a
    /// renumbering of every store index in every trace.
    #[test]
    fn store_indices_do_not_change_the_delivered_collections() {
        use crate::speculation::search::{
            AbortedLeaf, ErrorCode, Exploration, ExplorationStats, QuiescentLeaf, TruncatedLeaf,
        };
        use crate::speculation::ResumableBranch;
        use prost::Message;

        let build = |trace: Vec<RendezvousName>| -> Vec<Vec<u8>> {
            let state = SpeculativeState::default();
            let exploration = Exploration {
                success: vec![QuiescentLeaf {
                    trace: trace.clone(),
                    state: state.clone(),
                }],
                truncated: vec![TruncatedLeaf {
                    branch: ResumableBranch {
                        state: state.clone(),
                        trace: trace.clone(),
                        frontier: 2,
                    },
                }],
                failure: vec![AbortedLeaf {
                    trace,
                    code: ErrorCode::NotFired,
                    message: "fixed".to_string(),
                }],
                root: state,
                stats: ExplorationStats::default(),
            };
            deliver(&exploration)
                .expect("an empty configuration reifies")
                .as_slice()
                .iter()
                .map(|collection| collection.encode_to_vec())
                .collect()
        };

        assert_eq!(
            build(vec![name(1, &[2, 3], 0, &[0, 1])]),
            build(vec![name(1, &[2, 3], 9, &[6, 4])]),
            "★ the three FIPS collections must not carry a store index either"
        );
    }

    // ── the STRUCTURAL FACT, pinned ────────────────────────────────────────────────────

    /// ★★ **`^spec-delivery`'s order-independence is a side effect, and this is what stops it
    /// from evaporating silently.**
    ///
    /// [`deliver`] wraps each collection in [`ground_set`] → `new_eset_par` →
    /// `SortedParHashSet::create_from_vec` → `Ordering::sort_pars`, which canonicalises the
    /// entries. So the order in which leaves happen to be enumerated does not reach the
    /// published bytes — but **only because a set type was chosen**, not because anybody
    /// decided the order was not content. `^spec-success` and the bare reply use
    /// [`ground_list`], which sorts nothing; the difference is invisible at every call site.
    ///
    /// This cell asserts both halves: the three collections **are** `ESet`s, and permuting the
    /// leaves leaves the bytes alone. Changing `deliver` to emit a list would fail the first
    /// assertion at the moment of the edit rather than at the moment somebody notices two
    /// validators disagreeing.
    #[test]
    fn the_delivered_collections_are_sets_and_not_lists() {
        use crate::speculation::search::{
            AbortedLeaf, ErrorCode, Exploration, ExplorationStats, QuiescentLeaf, TruncatedLeaf,
        };
        use crate::speculation::ResumableBranch;
        use models::rhoapi::expr::ExprInstance;
        use prost::Message;

        let step = |byte: u8| name(byte, &[byte.wrapping_add(1)], 0, &[0]);
        let leaves = |order: [u8; 3]| -> Exploration {
            let state = SpeculativeState::default();
            Exploration {
                success: order
                    .iter()
                    .map(|byte| QuiescentLeaf {
                        trace: vec![step(*byte)],
                        state: state.clone(),
                    })
                    .collect(),
                truncated: order
                    .iter()
                    .map(|byte| TruncatedLeaf {
                        branch: ResumableBranch {
                            state: state.clone(),
                            trace: vec![step(*byte)],
                            frontier: 1,
                        },
                    })
                    .collect(),
                failure: order
                    .iter()
                    .map(|byte| AbortedLeaf {
                        trace: vec![step(*byte)],
                        code: ErrorCode::Interpreter,
                        message: "fixed".to_string(),
                    })
                    .collect(),
                root: state,
                stats: ExplorationStats::default(),
            }
        };

        let forward = deliver(&leaves([1, 2, 3])).expect("reify");
        let shuffled = deliver(&leaves([3, 1, 2])).expect("reify");

        for (label, collection) in [
            ("success", &forward.success),
            ("truncated", &forward.truncated),
            ("failure", &forward.failure),
        ] {
            let instance = collection
                .exprs
                .first()
                .and_then(|expr| expr.expr_instance.as_ref());
            assert!(
                matches!(instance, Some(ExprInstance::ESetBody(_))),
                "★ the `{label}` collection must be an ESet. Its order-independence is a \
                 CONSEQUENCE of that choice — `ParSet` sorts, `EList` does not — so an edit \
                 that emits a list here silently republishes enumeration order: {instance:?}"
            );
        }

        for (label, left, right) in [
            ("success", &forward.success, &shuffled.success),
            ("truncated", &forward.truncated, &shuffled.truncated),
            ("failure", &forward.failure, &shuffled.failure),
        ] {
            assert_eq!(
                left.encode_to_vec(),
                right.encode_to_vec(),
                "★ permuting the leaves changed the published `{label}` collection"
            );
        }
    }

    /// ★★ **The incidental protection, MEASURED — and it is broader than "the set is sorted".**
    ///
    /// `new_eset_par` → `SortedParHashSet::create_from_vec` → `Ordering::sort_pars`, and
    /// `sort_pars` is f1r3node's **normalizer sorter** (`ParSortMatcher::sort_match`): it
    /// canonicalises each entry *recursively*, so a configuration's `sends` come out sorted too
    /// — not merely the set's members reordered. [`ground_list`] does none of it.
    ///
    /// The consequence is the one a reader has to know before trusting any of these bytes:
    ///
    /// | published as | constructor | order-protected? |
    /// |---|---|---|
    /// | `^spec-delivery`'s three collections | [`ground_set`] | **yes**, by `sort_pars` |
    /// | `^spec-success` / `^spec-truncated` / `^spec-failure` entries | [`ground_list`] | **no** |
    /// | the bare reply datum on `x` | published verbatim | **no** |
    ///
    /// So `^spec-delivery` was never exposed to the within-channel defect this file fixes, and
    /// the two rows below it always were — which is why a cell written against [`deliver`]
    /// alone would have passed with [`reify`]'s sort reverted. Measured against exactly that
    /// revert, through `x8_publication_is_scheduler_invariant`: `^spec-delivery` byte-identical
    /// across widths, `^spec-success` and the reply different.
    ///
    /// This cell demonstrates the mechanism directly and without going through [`reify`], so it
    /// keeps holding whatever `reify` later does — and it is what makes the table above a
    /// *measurement* rather than a paragraph.
    #[test]
    fn the_set_constructor_canonicalises_each_entry_and_the_list_constructor_does_not() {
        use models::rust::utils::new_gstring_par;
        use prost::Message;

        let chan = new_gstring_par("OUT".to_string(), Vec::new(), false);
        let one_send = |value: i64| Send {
            chan: Some(chan.clone()),
            data: vec![new_gint_par(value, Vec::new(), false)],
            persistent: false,
            locally_free: Vec::new(),
            connective_used: false,
        };
        // Two processes that differ ONLY in the order of their sends — the shape an unsorted
        // `reify` would emit from one configuration staged two ways.
        let forward = Par::default().with_sends(vec![one_send(1), one_send(2)]);
        let reverse = Par::default().with_sends(vec![one_send(2), one_send(1)]);
        assert_ne!(
            forward.encode_to_vec(),
            reverse.encode_to_vec(),
            "the fixture's premise: the two processes really do differ as raw bytes"
        );

        assert_eq!(
            ground_set(vec![forward.clone()]).encode_to_vec(),
            ground_set(vec![reverse.clone()]).encode_to_vec(),
            "★ an ESet canonicalises its entries RECURSIVELY, so `^spec-delivery` is protected \
             from a send order it never chose"
        );
        assert_ne!(
            ground_list(vec![forward]).encode_to_vec(),
            ground_list(vec![reverse]).encode_to_vec(),
            "★★ …and an EList is NOT. `^spec-success`, `^spec-truncated`, `^spec-failure` and \
             the bare reply all use this constructor, so their order-independence has to be \
             established by the PRODUCER — which is what `reify`'s canonical ordering is for. \
             If this assertion ever flips, the delivery side stopped needing that argument and \
             somebody should find out why before relying on it."
        );
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
/// ## ★ Determinism, and the premise that was false
///
/// This comment used to read: *"Deterministic: `HotStoreState`'s maps are
/// `BTreeMap`s (channel-ordered), and within a channel the store order is
/// preserved, so two validators reifying the same configuration emit the same
/// `Par` bytes."*
///
/// **They are `HashMap`s** — `rspace++/src/rspace/hot_store.rs:90-94` declares
/// `continuations`, `data` and `joins` as `std::collections::HashMap`. Their
/// iteration order is `RandomState`-seeded per process. And `prepend_send` /
/// `prepend_receive` push to the front of a `Vec` without sorting
/// (`models/src/rust/utils.rs`), so map order became `Par` field order, which
/// became emitted bytes. The conclusion was right and the premise it rested on
/// was not, which is the worse of the two failure modes: a stated reason nobody
/// re-checks.
///
/// This went unnoticed because a reified configuration is never *rendered* —
/// it rides inside `^spec-success` / `^spec-truncated` entries and all three
/// `^spec-delivery` collections, and (for a subject with no registered guest,
/// via `LeafProjection::Configuration`) inside the bare reply term published on
/// the caller's own channel. Nothing in any transcript shows it.
///
/// It is the same class as the store-index defect in
/// [`step_digest`] — a local, host-assigned ordering promoted into published
/// bytes — and it is fixed the same way: **iterate a canonical, content-derived
/// order**, not the map's.
///
/// Both key sets are ordered by their protobuf encoding: total (a byte-string
/// order over a canonical serialization), content-derived (nothing but the
/// channel's own bytes decides it), and already the tree's idiom for naming a
/// `Par` when a name is needed.
///
/// ## ★★ The SECOND false premise, in the paragraph that replaced the first
///
/// The fix above shipped with this sentence attached: *"Within a channel the
/// store order is preserved as before — that part of the old comment was true
/// and remains load-bearing, because two data on one channel are genuinely
/// ordered."*
///
/// **They are not ordered, and two things in this tree already said so.**
///
/// 1. `rspace++/src/rspace/candidate_order.rs`'s module header: *"The pools come
///    out of the hot store in **insertion order**, which is an artifact of how a
///    particular node interleaved its reductions rather than a property of the
///    program."* That module exists precisely to replace that artifact with a
///    function of the candidate values alone.
/// 2. [`super::content_fingerprint`] — the tree's own definition of *"are these
///    two configurations the same?"* — **sorts within a channel** before
///    comparing (`sources.sort()`), for exactly this reason.
///
/// The mechanism is the same one that made the across-channel order arbitrary:
/// `HotStore::put_datum` / `put_continuation` **prepend** (`insert(0, …)`,
/// `rspace++/src/rspace/hot_store.rs:271, 289, 400-405`), so a channel's `Vec`
/// is *reverse arrival order*, and arrival races because every branch of a `|`
/// is a detached `tokio::spawn`. That order became `Par.sends` / `Par.receives`
/// order and then emitted bytes.
///
/// ★ **Why this ranked ahead of the across-channel case.** Leaving it in place
/// meant configuration *identity* and configuration *publication* were no longer
/// the same equivalence relation: publication was strictly finer, and the extra
/// discrimination was exactly the host-assigned arrival order. Two validators
/// agreeing on [`super::content_fingerprint`] could still publish different
/// bytes.
///
/// So the within-channel order is canonicalised too, by the key
/// [`super::content_fingerprint`] already uses:
///
/// | side | key | why it determines the emitted bytes |
/// |---|---|---|
/// | data | `Datum::source.hash` | the `Produce` hash covers `(channel, payload, persist)`, which is everything the emitted `Send` reads |
/// | continuations | `(WaitingContinuation::source.hash, persist, peeks.is_empty())` | the `Consume` hash covers `(channels, patterns, continuation, persistent)`; `peeks` is **not** in it and the emitted `Receive.peek` reads it, so it rides alongside — exactly as `content_fingerprint` spells the same key |
///
/// Two entries that tie on that key are byte-identical as emitted terms (the
/// hash determines every field the term reads), so a tie cannot reintroduce the
/// dependence through the sort's stability. This is the same injectivity
/// assumption [`super::content_fingerprint`] already rests on — *"exactly as
/// discriminating as the tuplespace's own identity notion and no more"* — not a
/// new one.
///
/// The law this restores is pinned by `reify_tests::the_publication_law` and by
/// `publication_is_a_function_of_the_configuration`.
pub fn reify(state: &SpeculativeState) -> Result<Par, ReificationError> {
    use prost::Message;

    let mut process = Par::default();

    // ★ Canonical, not `HashMap` order. See the header above.
    let mut data_channels: Vec<_> = state.data.iter().collect();
    data_channels.sort_by_cached_key(|(channel, _)| channel.encode_to_vec());

    for (channel, data) in data_channels {
        // ★ …and canonical WITHIN the channel, not the store's `Vec` order, which is
        // reverse-arrival order. See "the SECOND false premise" above.
        let mut ordered: Vec<_> = data.iter().collect();
        ordered.sort_by_cached_key(|datum| datum.source.hash.bytes());
        for datum in ordered {
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

    // ★ Same canonicalisation for the continuation side. The key is a channel
    // GROUP (`Vec<Par>`), so the sort key is the concatenation of the members'
    // encodings in their own order — group order is load-bearing (it pairs
    // positionally with `WaitingContinuation::patterns`) and must not be sorted
    // away, only the ORDER AMONG GROUPS is the map's arbitrary contribution.
    let mut continuation_groups: Vec<_> = state.continuations.iter().collect();
    continuation_groups.sort_by_cached_key(|(channels, _)| {
        let mut key = Vec::new();
        for channel in channels.iter() {
            channel
                .encode(&mut key)
                .expect("encoding a Par into a Vec cannot fail");
        }
        key
    });

    for (channels, continuations) in continuation_groups {
        if channels.is_empty() {
            return Err(ReificationError::EmptyChannelGroup);
        }
        // ★ …and canonical WITHIN the group, for the same reason and by the same key
        // `content_fingerprint` uses for a continuation — the `Consume` hash plus the two
        // bits the hash does not cover but the emitted `Receive` reads.
        let mut ordered: Vec<_> = continuations.iter().collect();
        ordered.sort_by_cached_key(|waiting| {
            (waiting.source.hash.bytes(), waiting.persist, !waiting.peeks.is_empty())
        });
        for waiting in ordered {
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
///
/// ## ★ The order is the DATA's, not the store's
///
/// This used to flatten `state.data[channel]` in `Vec` order. That `Vec` is
/// reverse-arrival order — `HotStore::put_datum` prepends, and arrival races
/// because every branch of a `|` is a detached `tokio::spawn` — so a local,
/// host-assigned ordering decided the order of a **published** sequence. It is
/// the same defect as the one [`reify`]'s header documents, on the projection
/// the registered-guest path actually takes
/// ([`LeafProjection::RestingOn`](super::service::LeafProjection::RestingOn)),
/// and it had two effects rather than one:
///
/// 1. the `EList` published on `^spec-success` is order-sensitive; and — worse —
/// 2. the request server publishes **one bare reply datum per term, in this
///    order**, while `Publisher::publish` assigns `split_short(index)` **by
///    position**. Permuting the terms therefore permuted their `random_state`,
///    hence their `Produce` hashes, hence the post-deploy tuplespace content
///    itself. A reordering that changed no answer still changed the checkpoint.
///
/// So the data are ordered by `Datum::source.hash` — the same content key
/// [`super::content_fingerprint`] and [`reify`] use — before they are flattened.
///
/// ⚠ The flattening **within** one datum stays in `ListParWithRandom` order. A
/// polyadic send's payload genuinely *is* ordered: `@c!(1, 2)` and `@c!(2, 1)`
/// are different sends, and sorting there would erase a distinction the program
/// wrote down. The sibling [`resting_fingerprint`] one function below has sorted
/// across data since it was written, which is the third witness in this file
/// that within-channel order is not content.
pub fn resting_on(state: &SpeculativeState, channel: &Par) -> Vec<Par> {
    let Some(data) = state.data.get(channel) else {
        return Vec::new();
    };
    // ★ Canonical, not store order. See the header above.
    let mut ordered: Vec<_> = data.iter().collect();
    ordered.sort_by_cached_key(|datum| datum.source.hash.bytes());
    let mut values = Vec::with_capacity(ordered.iter().map(|datum| datum.a.pars.len()).sum());
    for datum in ordered {
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
