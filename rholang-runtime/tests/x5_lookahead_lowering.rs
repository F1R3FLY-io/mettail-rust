//! X5 — what `x!(P)[*]` and `x!(P)[n]` **lower to**, and the fail-closed guarantee.
//!
//! The parse half is measured by `languages/tests/x4_rholang_lookahead_parse.rs`; the in-process
//! evaluation substrate by `x3_inprocess_lookahead_probe.rs`. This file is the lowering, and its
//! central assertion is a **negative** one.
//!
//! ## Why the negative assertion is the important one
//!
//! λ-calculus is confluent. A `[*]` implemented as "drive the term once to quiescence, publish
//! the answer" returns the **correct normal form for every λ term**. It would pass every
//! λ-flavoured test anyone would think to write, and produce a flawless demo transcript. It is
//! nevertheless not `[*]`: it never enumerates the path set, and it silently returns one answer
//! for a guest that has several.
//!
//! So [`lookahead_does_not_lower_onto_the_single_path_drive`] asserts that the lowering does
//! **not** emit a `^drive` seed — the exact shortcut that would look perfect and be wrong. And
//! [`an_unserved_lookahead_request_rests_and_is_reported`] asserts that with no engine installed
//! the program produces **nothing on the reply channel and a loud resting request**, rather than
//! quietly falling back to anything.
#![cfg(all(feature = "rholang-runtime", feature = "lambda-runtime"))]

use std::sync::Arc;

use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rholang::Proc;
use mettail_rholang_codegen::{FltRegistry, FltResolve};
use mettail_rholang_runtime::lookahead::{
    spec_all_request, spec_n_request, SPEC_ALL_CHANNEL, SPEC_N_CHANNEL, SPEC_REQUEST_CHANNELS,
};
use mettail_rholang_runtime::{
    lower_rholang_proc_with_resolver,
    run_normalized_par_for_oracle_and_read_runtime_value_channels, RholangAstLowerError,
};
use mettail_runtime::clear_var_cache;
use models::rhoapi::Par;

fn guest_resolver() -> Arc<dyn FltResolve> {
    Arc::new(FltRegistry::new().with_guest("lambda", Box::new(LambdaLanguage)))
}

fn lower(source: &str) -> Result<Par, RholangAstLowerError> {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("X5 source must parse: {source}\n{err}"));
    lower_rholang_proc_with_resolver(&proc, guest_resolver())
}

fn lower_ok(source: &str) -> Par {
    lower(source).unwrap_or_else(|err| panic!("X5 source must lower: {source}\n{err:?}"))
}

/// The `(channel, payload)` of a program that is exactly one send.
fn sole_send(par: &Par) -> (Par, Par) {
    assert_eq!(par.sends.len(), 1, "expected exactly one send, got {}", par.sends.len());
    let send = &par.sends[0];
    let chan = send.chan.clone().expect("a send must carry a channel");
    assert_eq!(send.data.len(), 1, "expected a unary send payload");
    (chan, send.data[0].clone())
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// 1. The request shapes
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `x!(P)[*]` lowers to the unbounded request, carrying the SAME reflected subject an ordinary
/// send of `P` would carry, and the send's own channel as the reply channel.
#[test]
fn lookahead_all_lowers_to_the_unbounded_speculation_request() {
    let ordinary = lower_ok(r#"@"results"!(lambda`(lam x. x, lam a. lam b. a)`)"#);
    let (channel, subject) = sole_send(&ordinary);

    let speculated = lower_ok(r#"@"results"!(lambda`(lam x. x, lam a. lam b. a)`)[*]"#);
    assert_eq!(
        speculated,
        spec_all_request(subject, channel),
        "`[*]` must lower to the `{SPEC_ALL_CHANNEL}` request over the reflected subject"
    );
}

/// `x!(P)[n]` lowers to the bounded request, carrying the step bound.
#[test]
fn bounded_lookahead_lowers_to_the_bounded_speculation_request() {
    let ordinary = lower_ok(r#"@"results"!(lambda`(lam x. x, lam a. a)`)"#);
    let (channel, subject) = sole_send(&ordinary);

    let speculated = lower_ok(r#"@"results"!(lambda`(lam x. x, lam a. a)`)[7]"#);
    assert_eq!(
        speculated,
        spec_n_request(subject, 7, channel),
        "`[7]` must lower to the `{SPEC_N_CHANNEL}` request with bound 7"
    );
}

/// `[0]` is admitted and is the identity of the bounded family — it explores nothing.
#[test]
fn a_zero_bound_is_admitted() {
    let lowered = lower_ok(r#"@"r"!(Nil)[0]"#);
    assert!(format!("{lowered:?}").contains(SPEC_N_CHANNEL), "a `[0]` bound must lower");
}

/// The lookahead attaches to every send SUGAR, not only the one the demo uses.
#[test]
fn every_send_sugar_accepts_the_lookahead_suffix() {
    for source in [
        r#"@"r"!(Nil)[*]"#,
        r#"@Nil!(Nil)[*]"#,
        "new r in { r!(Nil)[*] }",
        r#"@"r"!(Nil, Nil)[*]"#,
    ] {
        let lowered = lower_ok(source);
        assert!(
            format!("{lowered:?}").contains(SPEC_ALL_CHANNEL),
            "{source:?} must lower to a speculation request"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// 2. ★ THE NEGATIVE ASSERTION — the shortcut that would look perfect and be wrong
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `[*]` must NOT lower onto the `^drive` single-path quiescence driver.
///
/// Driving once is measured, working, and returns the correct answer for every λ term (λ is
/// confluent). That is exactly what makes it dangerous: it is indistinguishable from a real
/// enumerator on the guest the demo uses, and wrong on the first guest that has two normal forms.
#[test]
fn lookahead_does_not_lower_onto_the_single_path_drive() {
    let lowered = lower_ok(r#"@"results"!(lambda`(lam x. x, lam a. lam b. a)`)[*]"#);
    let rendered = format!("{lowered:?}");
    assert!(
        !rendered.contains("^drive"),
        "`[*]` must not lower onto the single-path `^drive` seed — that returns the right \
         answer for a CONFLUENT guest and is wrong in principle. Lowered: {rendered}"
    );
    assert!(
        rendered.contains(SPEC_ALL_CHANNEL),
        "`[*]` must lower to a speculation request: {rendered}"
    );
}

/// A lookahead is NOT also an ordinary send: `x!(P)[*]` must not deposit `P` on `x`. The data
/// that eventually rest on `x` are the terminal terms the engine computed, never the subject.
#[test]
fn a_lookahead_does_not_also_send_the_subject_on_the_channel() {
    let lowered = lower_ok(r#"@"results"!(lambda`(lam x. x, lam a. lam b. a)`)[*]"#);
    assert_eq!(
        lowered.sends.len(),
        1,
        "a lookahead emits exactly ONE send — the request — and no send on the reply channel"
    );
    let channel = lowered.sends[0]
        .chan
        .clone()
        .expect("a send must carry a channel");
    let rendered = format!("{channel:?}");
    assert!(
        rendered.contains(SPEC_ALL_CHANNEL),
        "the ONLY send a lookahead emits is the request; it must not also send on the reply \
         channel. Channel was: {rendered}"
    );
    // The request is binary: the reflected subject, then the reply channel.
    assert_eq!(
        lowered.sends[0].data.len(),
        2,
        "the `[*]` request carries (subject, replyChannel)"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// 3. Fail-closed admission
// ════════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn a_non_send_operand_is_rejected_with_a_typed_error() {
    for (source, what) in
        [(r#"@"r"!!(Nil)[*]"#, "a persistent send (`!!`)"), ("[1][*]", "a list literal")]
    {
        match lower(source) {
            Err(RholangAstLowerError::LookaheadOperandNotASend(found)) => {
                println!("X5 rejected {source:?} → operand is {found}");
                assert_eq!(found, what, "{source:?} must name its operand precisely");
            },
            other => panic!("{source:?} must be rejected as a non-send operand, got {other:?}"),
        }
    }
}

#[test]
fn a_non_ground_or_negative_bound_is_rejected_with_a_typed_error() {
    for source in [r#"@"r"!(Nil)[-1]"#, r#"@"r"!(Nil)[Nil]"#] {
        match lower(source) {
            Err(RholangAstLowerError::LookaheadBoundNotAGroundNonNegativeInt(found)) => {
                println!("X5 rejected bound in {source:?} → {found}");
            },
            other => panic!("{source:?} must be rejected as an unusable bound, got {other:?}"),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// 4. ★ THE FAIL-CLOSED GUARANTEE — no engine ⟹ nothing delivered, and it is LOUD
// ════════════════════════════════════════════════════════════════════════════════════════════

/// With no speculation engine installed, a `[*]` program must deliver **nothing** on the reply
/// channel and leave its request **resting** where a caller can see it.
///
/// This is the property that makes the missing-engine case honest. The failure mode it excludes
/// is the one that matters: a `[*]` that quietly degrades to a single-path answer would publish
/// a plausible term on `@"results"`, the demo would look correct, and nobody would learn that
/// the exploration never happened.
#[tokio::test]
async fn an_unserved_lookahead_request_rests_and_is_reported() {
    let program = lower_ok(
        r#"@"results"!(lambda`(lam x. x, lam a. lam b. a)`)[*] |
           for(@r <- @"results") { @"OUT"!(r) }"#,
    );

    let mut channels: Vec<&str> = Vec::with_capacity(SPEC_REQUEST_CHANNELS.len() + 1);
    channels.push("OUT");
    channels.extend_from_slice(SPEC_REQUEST_CHANNELS);

    let rest = run_normalized_par_for_oracle_and_read_runtime_value_channels(&program, &channels)
        .await
        .expect("the lookahead program must run to rest");

    for (channel, data) in &rest {
        println!("X5 unserved: {channel} ← {} datum(a)", data.len());
    }
    let on = |name: &str| {
        rest.iter()
            .find(|(c, _)| c.as_str() == name)
            .map(|(_, d)| d.len())
            .unwrap_or_default()
    };

    assert_eq!(
        on("OUT"),
        0,
        "★ with no engine installed NOTHING may be delivered — a `[*]` that quietly degrades to \
         a single-path drive would publish a plausible answer here and the demo would look correct"
    );
    // The readback yields one value per DATA ELEMENT of the resting send, and the `[*]` request
    // is binary — `(subject, replyChannel)` — so one unserved request surfaces as two values.
    assert_eq!(
        on(SPEC_ALL_CHANNEL),
        2,
        "the unserved request must REST on {SPEC_ALL_CHANNEL} where the caller can report it \
         (2 values = the one binary request's subject + reply channel)"
    );
}
