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
//! ## The result shape
//!
//! The versioned request places one datum with two trace-set `EPathMap` payloads
//! on the send's reply channel `x`: `(success, failure)`. A receiving program can
//! bind both names and query their trace entries through the PathMap API. The
//! original v1 request channels retain their bare-term reply ABI for existing
//! programs and demonstrations. A nonempty trace set has native `Set` mode;
//! an empty one has native `Empty` mode.
//!
//! | what | where | datum |
//! |---|---|---|
//! | v2 FIPS reply | the send's own channel `x` | one datum `(successPathMap, failurePathMap)` |
//! | v1 legacy reply | the send's own channel `x` | one bare projected term per success branch |
//! | success provenance | [`SPEC_SUCCESS_CHANNEL`] | `[trace, term]` |
//! | each ABORTED branch | [`SPEC_FAILURE_CHANNEL`] | `[trace, reason]` |
//! | each TRUNCATED branch (`[n]` only) | [`SPEC_TRUNCATED_CHANNEL`] | `[trace, handle, frontier]` |
//! | v2 internal truncation extension | [`SPEC_TRUNCATED_V2_CHANNEL`] | `[2, truncatedPathMap]` |
//! | the request was never served | [`SPEC_ALL_CHANNEL`] / [`SPEC_N_CHANNEL`] | the request itself, resting |
//!
//! The two v2 payloads are one RSpace produce, so a receiver cannot observe
//! only one of the two maps. The versioned truncation datum is separate and
//! never adds a third payload to the approved reply.
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

use crate::language_install::wire_list;

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

/// Versioned unbounded request channel. The separate channel keeps a legacy
/// host list such as `[2, P, []]` from being parsed as a v2 envelope.
pub const SPEC_ALL_V2_CHANNEL: &str = "^spec-all-v2";

/// Versioned bounded request channel, with the same outer arity as `^spec-n`.
pub const SPEC_N_V2_CHANNEL: &str = "^spec-n-v2";

/// Composite installed-language requests use a disjoint wire version because
/// a top-level expression slot cannot be named by a v2 borrowed-`Par` path.
pub const SPEC_ALL_V3_CHANNEL: &str = "^spec-all-v3";
pub const SPEC_N_V3_CHANNEL: &str = "^spec-n-v3";

/// Provenance for each branch that reached quiescence: `[trace, term]`.
pub const SPEC_SUCCESS_CHANNEL: &str = "^spec-success";

/// One datum per ABORTED branch: `[trace, reason]`.
pub const SPEC_FAILURE_CHANNEL: &str = "^spec-failure";

/// One datum per TRUNCATED-and-resumable branch: `[trace, handle]`. `[n]` only.
pub const SPEC_TRUNCATED_CHANNEL: &str = "^spec-truncated";

/// Internal v2 truncation extension: one datum `[2, truncatedPathMap]` per
/// bounded request. The approved public reply remains exactly the success and
/// failure PathMap payloads on the send's channel; this channel is not part of
/// that FIPS wire. The old per-branch `^spec-truncated` reports remain intact.
pub const SPEC_TRUNCATED_V2_CHANNEL: &str = "^spec-truncated-v2";

/// Typed engine-side failures (a subject the enumerator cannot speculate over, an exhausted
/// budget, a not-yet-implemented capability). Distinct from [`SPEC_FAILURE_CHANNEL`], which is
/// about a *branch*; this is about the *request*.
pub const SPEC_ERR_CHANNEL: &str = "^spec-err";

/// The legacy aggregate of three collections, as ONE datum:
/// `[success, truncated, failure]`, each a set-mode `EPathMap` of `EList` entries
/// `[step₀ … step_{k-1}, leaf]`
/// ([`crate::speculation::delivery::SpeculationDelivery`]).
///
/// ★ This is the **other half** of the shape reconciliation, and it exists because the two
/// readings answer different questions and neither subsumes the other:
///
/// | reading | where | leaf | the question it answers |
/// |---|---|---|---|
/// | the bare projected term | a v1 send's own channel `x` | the guest's answer | *"what did `P` compute?"* — an ordinary FLT receive pattern matches it verbatim |
/// | the trace-keyed per-branch datum | [`SPEC_SUCCESS_CHANNEL`] & co. | the projected term | *"which branch computed it, and how did it get there?"* |
/// | the aggregate collection | this channel | the reified terminal **configuration** | *"what is the whole path set?"* — one legacy value with all three outcomes |
///
/// The v2 public reply uses the `success` and `failure` PathMaps directly on
/// `x`. This aggregate remains for existing consumers.
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
pub const SPEC_REQUEST_CHANNELS: &[&str] = &[
    SPEC_ALL_CHANNEL,
    SPEC_N_CHANNEL,
    SPEC_ALL_V2_CHANNEL,
    SPEC_N_V2_CHANNEL,
    SPEC_ALL_V3_CHANNEL,
    SPEC_N_V3_CHANNEL,
];

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

/// One exact owner claim for a reflected installed-language occurrence.
///
/// `handle` is the original opaque installed-language selector. The category is
/// resolved through that handle's admitted image; it is not an authority token.
/// A path is a sequence of child indices in the subject. The current direct
/// FLT lowering supplies the root path `[]` and context zero.
#[derive(Clone, Debug, PartialEq)]
pub struct LookaheadOwnerBinding {
    pub path: Vec<u32>,
    pub handle: Par,
    pub expected_category: String,
    pub context: u32,
}

/// A v3 owner claim for an exact top-level expression in a parallel subject.
/// Its index is in `subject.exprs`, not in the v2 borrowed-child path domain.
#[derive(Clone, Debug, PartialEq)]
pub struct LookaheadTopLevelBinding {
    pub expr_index: u32,
    pub handle: Par,
    pub expected_category: String,
    pub context: u32,
}

fn owner_binding_datum(binding: LookaheadOwnerBinding) -> Par {
    wire_list(vec![
        wire_list(
            binding
                .path
                .into_iter()
                .map(|index| new_gint_par(i64::from(index), Vec::new(), false))
                .collect(),
        ),
        binding.handle,
        new_gstring_par(binding.expected_category, Vec::new(), false),
        new_gint_par(i64::from(binding.context), Vec::new(), false),
    ])
}

/// The exact v2 first datum: `[2, subject, owner-bindings]`.
///
/// A versioned request has the same outer arity and reply channel as v1. An
/// empty binding list is valid only for a subject with no installed FLT.
pub fn spec_envelope_v2(subject: Par, bindings: Vec<LookaheadOwnerBinding>) -> Par {
    wire_list(vec![
        new_gint_par(2, Vec::new(), false),
        subject,
        wire_list(bindings.into_iter().map(owner_binding_datum).collect()),
    ])
}

/// Build an unbounded request with explicit installed owner bindings.
pub fn spec_all_request_v2(
    subject: Par,
    bindings: Vec<LookaheadOwnerBinding>,
    reply_channel: Par,
) -> Par {
    send_to(SPEC_ALL_V2_CHANNEL, vec![spec_envelope_v2(subject, bindings), reply_channel])
}

/// Build a bounded request with explicit installed owner bindings.
pub fn spec_n_request_v2(
    subject: Par,
    bound: u64,
    bindings: Vec<LookaheadOwnerBinding>,
    reply_channel: Par,
) -> Par {
    send_to(
        SPEC_N_V2_CHANNEL,
        vec![
            spec_envelope_v2(subject, bindings),
            crate::semantic_wire::encode_u64_literal(bound),
            reply_channel,
        ],
    )
}

fn top_level_binding_datum(binding: LookaheadTopLevelBinding) -> Par {
    wire_list(vec![
        wire_list(vec![
            new_gstring_par("expr".to_string(), Vec::new(), false),
            new_gint_par(i64::from(binding.expr_index), Vec::new(), false),
        ]),
        binding.handle,
        new_gstring_par(binding.expected_category, Vec::new(), false),
        new_gint_par(i64::from(binding.context), Vec::new(), false),
    ])
}

/// The v3 envelope is `[3, subject, [[ ["expr", index], owner, category, 0 ]]]`.
/// Its typed locator is deliberately not interpreted as a v2 child path.
pub fn spec_envelope_v3(subject: Par, binding: LookaheadTopLevelBinding) -> Par {
    wire_list(vec![
        new_gint_par(3, Vec::new(), false),
        subject,
        wire_list(vec![top_level_binding_datum(binding)]),
    ])
}

pub fn spec_all_request_v3(
    subject: Par,
    binding: LookaheadTopLevelBinding,
    reply_channel: Par,
) -> Par {
    send_to(SPEC_ALL_V3_CHANNEL, vec![spec_envelope_v3(subject, binding), reply_channel])
}

pub fn spec_n_request_v3(
    subject: Par,
    bound: u64,
    binding: LookaheadTopLevelBinding,
    reply_channel: Par,
) -> Par {
    send_to(
        SPEC_N_V3_CHANNEL,
        vec![
            spec_envelope_v3(subject, binding),
            crate::semantic_wire::encode_u64_literal(bound),
            reply_channel,
        ],
    )
}

/// A quoted-string channel `@"name"`, the same shape the `^drive` observation channels use.
pub fn spec_channel_par(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

fn send_to(channel: &str, data: Vec<Par>) -> Par {
    use models::rust::utils::{new_send_par, union};
    // A staged installed request contains a bound selector and a bound FLT
    // result. The caches must follow those children so substitution descends
    // through the send and through its versioned first datum.
    let locally_free = data
        .iter()
        .fold(Vec::new(), |acc, item| union(acc, item.locally_free.clone()));
    let connective_used = data.iter().any(|item| item.connective_used);
    new_send_par(
        spec_channel_par(channel),
        data,
        false,
        locally_free.clone(),
        connective_used,
        locally_free,
        connective_used,
    )
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
    use crate::language_install::exact_list;

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
    fn v2_keeps_the_same_outer_arity_and_places_exact_owner_claims_first() {
        let subject = spec_channel_par("subject");
        let selector = spec_channel_par("opaque-selector-test-shape");
        let reply = spec_channel_par("results");
        let request = spec_all_request_v2(
            subject.clone(),
            vec![LookaheadOwnerBinding {
                path: vec![],
                handle: selector.clone(),
                expected_category: "Term".into(),
                context: 0,
            }],
            reply.clone(),
        );
        let send = request.sends.first().expect("one request send");
        assert_eq!(send.chan.as_ref(), Some(&spec_channel_par(SPEC_ALL_V2_CHANNEL)));
        assert_eq!(send.data.len(), 2);
        assert_eq!(send.data[1], reply);
        let [version, actual, bindings] = exact_list(&send.data[0]).expect("v2 envelope") else {
            panic!("v2 first datum has exactly three fields")
        };
        assert_eq!(version, &new_gint_par(2, Vec::new(), false));
        assert_eq!(actual, &subject);
        let [binding] = exact_list(bindings).expect("binding list") else {
            panic!("one binding")
        };
        let [path, handle, category, context] = exact_list(binding).expect("binding fields") else {
            panic!("four binding fields")
        };
        assert!(exact_list(path).expect("root path").is_empty());
        assert_eq!(handle, &selector);
        assert_eq!(category, &spec_channel_par("Term"));
        assert_eq!(context, &new_gint_par(0, Vec::new(), false));

        let bounded = spec_n_request_v2(subject, 7, Vec::new(), spec_channel_par("bounded"));
        let bounded_send = bounded.sends.first().expect("one bounded request send");
        assert_eq!(bounded_send.chan.as_ref(), Some(&spec_channel_par(SPEC_N_V2_CHANNEL)));
        assert_eq!(bounded_send.data.len(), 3);
        assert_eq!(bounded_send.data[1], new_gint_par(7, Vec::new(), false));

        let maximum = spec_n_request_v2(
            spec_channel_par("subject"),
            u64::MAX,
            Vec::new(),
            spec_channel_par("bounded"),
        );
        let maximum_send = maximum.sends.first().expect("one maximum-bound request");
        assert_eq!(
            maximum_send.data[1],
            crate::semantic_wire::encode_u64_literal(u64::MAX),
            "the upper half is transported by the existing exact BigInt scalar codec",
        );
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
