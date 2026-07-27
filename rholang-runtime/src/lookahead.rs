//! # The `[*]` / `[n]` lookahead ABI — the seam between the SURFACE and the ENGINE
//!
//! This module is the **frontend half** of the lookahead feature: the wire shape a lowered
//! `x!(P)[*]` / `x!(P)[n]` puts on the reducer, and the fail-closed readback that proves an
//! engine actually served it. The **backend half** — the branching search that enumerates
//! `E(S)`, fires each enabled rendezvous, and assembles the three result maps — lives in
//! [`crate::speculation`] and is deliberately NOT here. Splitting them at a named ABI is what
//! lets the two be built and reviewed independently.
//!
//! ## ★ The design constraint this module exists to honor
//!
//! λ-calculus is **confluent**. A `[*]` implemented as "drive the term once to quiescence and
//! wrap the answer in something map-shaped" returns the *correct answer* for every λ term, and
//! would look perfect in a demo. It is nevertheless **wrong in principle**, and it breaks
//! silently on the first non-confluent guest.
//!
//! This module therefore does **not** lower `[*]` onto the `^drive` quiescence driver, even
//! though that path is measured, working, and would produce a convincing transcript tonight
//! (`tests/x3_inprocess_lookahead_probe.rs`). It lowers onto a **speculation request** that only
//! a genuine enumerator can answer, and if no enumerator is installed the request **rests
//! unanswered and is reported as a typed error** ([`unserved_requests`]) rather than silently
//! producing nothing — or, worse, silently producing a single-path answer.
//!
//! The distinction, stated once so it cannot be lost:
//!
//! | | mechanism | λ result | non-confluent guest |
//! |---|---|---|---|
//! | ✅ honest | enumerate `E(S)`, branch, collect terminal states | one entry, **by confluence** | several entries |
//! | ❌ hack | drive once, wrap the answer | one entry, **by construction** | one entry — WRONG |
//!
//! The gate that separates them is a **non-confluent** guest: Ambient's open race
//! `{ open(n, a[0]) | n[b[0]] | open(n, c[0]) }` has exactly two normal forms. A real
//! enumerator returns two; a faked one returns one and looks fine.
//!
//! ## The wire shape
//!
//! ```text
//!   x!(P)[*]   ⟿   @"^spec-all"!( ⟦P⟧, x )
//!   x!(P)[n]   ⟿   @"^spec-n"!( ⟦P⟧, n, x )
//! ```
//!
//! `⟦P⟧` is the **reflected** subject — for an FLT payload this is the guest term produced by
//! the guest's own reflector, exactly as an ordinary send would carry it, so the speculation
//! subject and an ordinary payload are the same bytes. `x` is the send's channel, passed as a
//! `Par` rather than a channel *name*, so `new r in { r!(P)[*] }` works on an unforgeable name
//! and not only on a quoted string.
//!
//! ## The result shape, and why it is data-on-channels rather than a `PathMap`
//!
//! ⚠ **PathMap methods do not lower on the reducer path** — all 22 zipper methods fail, and a
//! `Pathmap` lowers to an `EMap`. So a delivery built on PathMap operations is one the receiving
//! program cannot then read. The FIPS's "success map / failure map" is therefore realized as
//! **resting data on channels**, which is the shape Rholang can actually consume:
//!
//! | what | where | datum |
//! |---|---|---|
//! | each SUCCESS branch's terminal term | the send's own channel `x` | the bare reflected term |
//! | success provenance | [`SPEC_SUCCESS_CHANNEL`] | `[trace, term]` |
//! | each ABORTED branch | [`SPEC_FAILURE_CHANNEL`] | `[trace, reason]` |
//! | each TRUNCATED branch (`[n]` only) | [`SPEC_TRUNCATED_CHANNEL`] | `[trace, handle]` |
//! | the request was never served | [`SPEC_ALL_CHANNEL`] / [`SPEC_N_CHANNEL`] | the request itself, resting |
//!
//! Publishing the **bare terminal term** on `x` (rather than a tuple) is what makes the ordinary
//! FLT receive pattern work verbatim —
//!
//! ```text
//! @"results"!(lambda`((plus, two), three)`)[*] |
//! for(@lambda`lam f. lam x. ${body}` <- @"results") { @"OUT"!(lambda`${body}`) }
//! ```
//!
//! — so a program filters over values the machine **computed**, not constants someone
//! transcribed. One datum per success branch means a confluent guest leaves exactly one (and the
//! `for` above consumes it), while a non-confluent guest leaves several, which is precisely the
//! resting-data shape the assay desk already filters over. The trace-keyed pairs are on a
//! companion channel for programs that want provenance, so keying by trace is preserved without
//! forcing every consumer to destructure a pair.
//!
//! ## Truncation is a THIRD outcome, not a failure
//!
//! `[n]` has three outcomes — **quiescent**, **truncated-and-resumable**, **aborted** — and a
//! truncated branch is not an error: it is a branch whose exploration hit the step bound with
//! work remaining. It returns a **handle to a retained configuration**, resumable, bounded by
//! the remaining token budget. Truncated results go on their own channel and are never folded
//! into the failure side, because "I stopped early, here is where to resume" and "this branch
//! died" are different facts and a consumer must be able to tell them apart.

use models::rhoapi::Par;
use models::rust::utils::{new_gint_par, new_gstring_par};

// ════════════════════════════════════════════════════════════════════════════════════════════
// The reserved channel names
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Request channel for the unbounded exploration `x!(P)[*]`.
///
/// Payload: `(⟦P⟧, replyChannel)`.
pub const SPEC_ALL_CHANNEL: &str = "^spec-all";

/// Request channel for the bounded exploration `x!(P)[n]`.
///
/// Payload: `(⟦P⟧, GInt(n), replyChannel)`.
pub const SPEC_N_CHANNEL: &str = "^spec-n";

/// Provenance for each branch that reached quiescence: `[trace, term]`.
pub const SPEC_SUCCESS_CHANNEL: &str = "^spec-success";

/// One datum per ABORTED branch: `[trace, reason]`.
pub const SPEC_FAILURE_CHANNEL: &str = "^spec-failure";

/// One datum per TRUNCATED-and-resumable branch: `[trace, handle]`. `[n]` only.
pub const SPEC_TRUNCATED_CHANNEL: &str = "^spec-truncated";

/// Typed engine-side failures (a subject the enumerator cannot speculate over, an exhausted
/// budget, a not-yet-implemented capability). Distinct from [`SPEC_FAILURE_CHANNEL`], which is
/// about a *branch*; this is about the *request*.
pub const SPEC_ERR_CHANNEL: &str = "^spec-err";

/// The FIPS's own three collections, as ONE datum: `[success, truncated, failure]`, each an
/// `ESet` of `EList` entries `[step₀ … step_{k-1}, leaf]`
/// ([`crate::speculation::delivery::SpeculationDelivery`]).
///
/// ★ This is the **other half** of the shape reconciliation, and it exists because the two
/// readings answer different questions and neither subsumes the other:
///
/// | reading | where | leaf | the question it answers |
/// |---|---|---|---|
/// | the bare projected term | the send's own channel `x` | the guest's answer | *"what did `P` compute?"* — an ordinary FLT receive pattern matches it verbatim |
/// | the trace-keyed per-branch datum | [`SPEC_SUCCESS_CHANNEL`] & co. | the projected term | *"which branch computed it, and how did it get there?"* |
/// | the FIPS collection | this channel | the reified terminal **configuration** | *"what is the whole path set?"* — one value, keyed by trace, the FIPS's `success`/`failure` maps verbatim |
///
/// Delivering only the first would discard provenance; delivering only the third would force
/// every consumer to destructure an `ESet` before it could read an answer. All three are
/// published, from one exploration.
pub const SPEC_DELIVERY_CHANNEL: &str = "^spec-delivery";

/// ⚠ **Sandbox-internal, never host-visible.** The channel a guest's in-Rho quiescence driver
/// is pointed at when the request server seeds it, and therefore the channel
/// [`crate::speculation::service::LeafProjection::RestingOn`] reads a branch's answer off.
///
/// It is listed here, with the wire names, because it is a reserved name and reserved names
/// that live in two places drift apart. It is *not* in [`SPEC_REPORT_CHANNELS`]: nothing ever
/// rests on it in the host store — it exists only inside a speculative sandbox, where it is the
/// address the guest's `^drive` publishes each branch's normal form to before the projection
/// lifts it onto the reply channel.
pub const SPEC_LEAF_CHANNEL: &str = "^spec-leaf";

/// Every channel a lookahead request can rest on unanswered — the fail-closed check's input.
pub const SPEC_REQUEST_CHANNELS: &[&str] = &[SPEC_ALL_CHANNEL, SPEC_N_CHANNEL];

/// Every channel the engine reports on, in the order a transcript should show them.
pub const SPEC_REPORT_CHANNELS: &[&str] = &[
    SPEC_SUCCESS_CHANNEL,
    SPEC_FAILURE_CHANNEL,
    SPEC_TRUNCATED_CHANNEL,
    SPEC_ERR_CHANNEL,
    SPEC_DELIVERY_CHANNEL,
];

// ════════════════════════════════════════════════════════════════════════════════════════════
// The seed builders — what the lowering emits
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The `[*]` request: explore **every** path of `subject`, delivering each branch's terminal
/// term to `reply_channel`.
///
/// `subject` is the reflected term (`⟦P⟧`); `reply_channel` is the lowered `Par` of the send's
/// channel, so both quoted-string and `new`-bound unforgeable channels are supported.
pub fn spec_all_request(subject: Par, reply_channel: Par) -> Par {
    send_to(SPEC_ALL_CHANNEL, vec![subject, reply_channel])
}

/// The `[n]` request: explore `subject` for at most `bound` steps, where a **step is one COMM**
/// (the stratified-choice model of [`crate::speculation`] — administrative reduction is
/// saturated to quiescence between steps and is not counted).
///
/// A branch that reaches quiescence within the bound is a success; a branch still enabled at the
/// bound is **truncated**, and its retained configuration handle is published on
/// [`SPEC_TRUNCATED_CHANNEL`] so it can be resumed.
pub fn spec_n_request(subject: Par, bound: i64, reply_channel: Par) -> Par {
    send_to(
        SPEC_N_CHANNEL,
        vec![subject, new_gint_par(bound, Vec::new(), false), reply_channel],
    )
}

/// A quoted-string channel `@"name"`, the same shape the `^drive` observation channels use.
pub fn spec_channel_par(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

fn send_to(channel: &str, data: Vec<Par>) -> Par {
    use models::rust::utils::new_send_par;
    // `new_send_par(chan, data, persistent, send_locally_free, send_connective_used,
    // par_locally_free, par_connective_used)` — the last two are the enclosing `Par`'s,
    // which the `Send`'s own do not imply. A request seed is ground on both.
    new_send_par(spec_channel_par(channel), data, false, Vec::new(), false, Vec::new(), false)
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The fail-closed readback
// ════════════════════════════════════════════════════════════════════════════════════════════

/// A lookahead request that was still resting on its request channel when the program reached
/// quiescence — i.e. **no engine consumed it**.
///
/// This is the fail-closed guard that makes the missing-engine case loud. Without it a program
/// containing `[*]` would run, publish nothing, and rest — indistinguishable from a program
/// whose exploration legitimately found no successful branch. A caller that reads back a
/// lookahead-bearing program MUST check this and report, exactly as the `rholang` interpreter
/// already fails closed on non-empty `^drive-err` / `^drive-fuel` before reporting a normal form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnservedRequest {
    /// Which request channel it rested on.
    pub channel: &'static str,
    /// The resting request datum, rendered by
    /// [`render_par_text`](crate::observation::render_par_text) — **total, deterministic,
    /// bounded**.
    ///
    /// This was `format!("{datum:?}")`, which put ~15 KB of prost `Debug` noise in front of
    /// anyone whose engine was missing — the exact case where a diagnostic has to be readable.
    /// It is not consensus-visible (this struct is host-side readback, not a datum), so the
    /// contract here is legibility rather than replay safety; it uses the same renderer because
    /// there should be one answer to *"how do we name a `Par` in prose?"*, not two.
    pub rendered: String,
}

/// Partition resting request data into the unserved-request diagnostics.
///
/// `resting` is `(channel, data)` as read back from the quiescent store — the caller supplies it
/// because reading the store is the runtime's job, not this module's.
pub fn unserved_requests(resting: &[(&'static str, Vec<Par>)]) -> Vec<UnservedRequest> {
    let total: usize = resting.iter().map(|(_, data)| data.len()).sum();
    let mut unserved = Vec::with_capacity(total);
    for (channel, data) in resting {
        for datum in data {
            unserved.push(UnservedRequest {
                channel,
                rendered: crate::observation::render_par_text(datum),
            });
        }
    }
    unserved
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ★ This cell reads the wire through prost's derived `Debug` **on purpose**, and it is the
    /// one place in this tree that may. It is therefore a free canary: if a `prost` bump
    /// re-spells the derive, this goes red — which is exactly the change that would silently
    /// have altered consensus-visible bytes back when `guest_evaluator_failures` and
    /// `parse_request` embedded `{:?}` in their messages. Do not "fix" it to use
    /// `render_par_text`; that would decode the datum and stop testing the encoding.
    #[test]
    fn the_two_request_shapes_are_distinct_and_carry_their_operands() {
        let subject = spec_channel_par("subject");
        let reply = spec_channel_par("results");
        let all = spec_all_request(subject.clone(), reply.clone());
        let bounded = spec_n_request(subject, 7, reply);
        assert_ne!(all, bounded, "`[*]` and `[n]` must not lower to the same request");
        // The bounded request carries its bound; the unbounded one does not.
        assert!(format!("{bounded:?}").contains("Int(7)"), "the `[n]` bound must ride the wire");
    }

    #[test]
    fn an_unconsumed_request_is_reported_rather_than_silently_dropped() {
        let resting: Vec<(&'static str, Vec<Par>)> =
            vec![(SPEC_ALL_CHANNEL, vec![spec_channel_par("a-resting-request")])];
        let unserved = unserved_requests(&resting);
        assert_eq!(unserved.len(), 1, "a resting request must surface as unserved");
        assert_eq!(unserved[0].channel, SPEC_ALL_CHANNEL);
    }

    #[test]
    fn no_unserved_requests_when_nothing_rests() {
        let resting: Vec<(&'static str, Vec<Par>)> =
            vec![(SPEC_ALL_CHANNEL, vec![]), (SPEC_N_CHANNEL, vec![])];
        assert!(unserved_requests(&resting).is_empty());
    }
}
