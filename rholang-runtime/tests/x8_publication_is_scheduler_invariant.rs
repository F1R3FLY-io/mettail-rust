//! # X8 — ★★ LAYER 3: what a `[*]` **publishes** does not depend on the scheduler
//!
//! `lookahead_demo::the_transcript_does_not_depend_on_the_scheduler_width` compares a
//! **transcript** across `TOKIO_WORKER_THREADS`. A transcript is what the interpreter chose to
//! print; the thing that has to agree between two validators is what the deploy `produce`d into
//! the tuplespace. Those are not the same set of bytes, and the gap between them is exactly
//! where D1 (`reify` emitting a channel's data in arrival order) and D3 (`resting_on` doing the
//! same on the guest path) lived: neither reaches a transcript, so no transcript could see them.
//!
//! This file closes that gap. It runs a lookahead-bearing program **in process** at several
//! tokio worker-thread widths, reads back every channel a `[*]` writes to, encodes each datum,
//! and requires the **sorted byte multiset** to be the same at every width.
//!
//! ```text
//!         width 1        width 2        width 8
//!            │              │              │
//!            ├──run──┐      ├──run──┐      ├──run──┐        two runs per width, so a
//!            └──run──┤      └──run──┤      └──run──┤        FLAKE is distinguishable
//!                    ▼              ▼              ▼        from a WIDTH effect
//!             ┌───────────────────────────────────────┐
//!             │  x  ·  ^spec-success  ·  ^spec-failure │     encode_to_vec each datum
//!             │  ^spec-truncated · ^spec-err           │     sort  ⇒  a byte multiset
//!             │  ^spec-delivery                        │
//!             └───────────────────────────────────────┘
//!                                 ║
//!                                 ▼
//!                    every multiset must be equal
//! ```
//!
//! ## ★ Why the multiset is over DATA and not over the concatenation
//!
//! Sorting the datums makes the test insensitive to the order in which the publisher happened
//! to emit them onto one channel — which is a genuine non-observable — while staying fully
//! sensitive to any ordering **inside** a datum. `^spec-success` carries `[trace, [term…]]` and
//! `^spec-delivery` carries three collections of reified configurations, so a permutation of a
//! channel's data or of a configuration's sends changes *a datum's own bytes* and moves the
//! multiset. That is the discrimination the defect class needs.
//!
//! ## ★ The second program, and why one was missing
//!
//! Every committed `[*]` demo drives a **λ** subject: confluent, one branch, one datum per
//! channel. A configuration with **two data on one channel** never arose, and that is the only
//! shape in which a within-channel ordering dependence is observable at all — which is why D1
//! and D3 survived the fix that named them.
//!
//! [`two_data_on_one_channel`] is that shape: `@"OUT"!(1) | … | @"OUT"!(n)` as the subject of a
//! `[*]` send with **no registered guest**, so the server takes
//! `LeafProjection::Configuration` — the whole non-guest path — and the leaf it reifies has
//! every one of those sends on one channel.
//!
//! ## Reproducibility
//!
//! Nothing here is seeded from entropy: the injection randomness is `run::deploy_rand`, a
//! content hash of the program, so two runs of one program differ only if something
//! host-assigned reached the output. That is the property under test, stated as its own cell
//! ([`two_runs_at_one_width_publish_the_same_data`]) so a failure reads as *"irreproducible"*
//! rather than as *"width-dependent"*.
#![cfg(feature = "runtime-report")]

use std::collections::BTreeMap;

use models::rhoapi::{Par, ReceiveBind, Send};
use models::rust::utils::{
    new_boundvar_par, new_freevar_par, new_gint_par, new_gstring_par, new_receive_par,
};
use prost::Message;

use mettail_rholang_runtime::lookahead::{
    spec_all_request, SPEC_ALL_CHANNEL, SPEC_DELIVERY_CHANNEL, SPEC_ERR_CHANNEL,
    SPEC_FAILURE_CHANNEL, SPEC_N_CHANNEL, SPEC_SUCCESS_CHANNEL, SPEC_TRUNCATED_CHANNEL,
};
use mettail_rholang_runtime::run_normalized_par_with_lookahead_engine;
use mettail_rholang_runtime::speculation::server::LookaheadEngine;

// ════════════════════════════════════════════════════════════════════════════════════════════
// Program fixtures — built as `Par`s, never parsed
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The reply channel every fixture sends its speculative results to.
const REPLY: &str = "results";

/// The channel the fixtures' subjects publish on.
const OUT: &str = "OUT";

fn chan(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

fn send(channel: &str, value: i64) -> Par {
    Par::default().with_sends(vec![Send {
        chan: Some(chan(channel)),
        data: vec![new_gint_par(value, Vec::new(), false)],
        persistent: false,
        locally_free: Vec::new(),
        connective_used: false,
    }])
}

/// `for(@x <- source) { target!(x) }`.
fn forward(source: &str, target: &str) -> Par {
    new_receive_par(
        vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(chan(source)),
            remainder: None,
            free_count: 1,
        }],
        Par::default().with_sends(vec![Send {
            chan: Some(chan(target)),
            data: vec![new_boundvar_par(0, Vec::new(), false)],
            persistent: false,
            locally_free: Vec::new(),
            connective_used: false,
        }]),
        false,
        false,
        1,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// How many data the fixture puts on one channel.
///
/// ★ Two is the minimum that makes the defect *observable*; it is a poor size for the
/// **width** cells, which detect an arrival-order dependence only when the arrival order
/// actually differs between runs. Measured, with the fix reverted: `WIDTH = 2` diverged in
/// 1 of 5 runs of [`the_published_data_do_not_depend_on_the_scheduler_width`], because two
/// detached `tokio::spawn`s usually land in spawn order anyway. Eight data give `8! = 40 320`
/// arrival orders instead of two, and diverge on essentially every run.
///
/// The deterministic guarantee is not this number's job — see
/// [`the_published_leaf_is_invariant_under_permuting_the_retained_store`], and Layers 1/2/4 in
/// `speculation::delivery`. This number is what makes the *race* detector actually detect.
const FAN: i64 = 8;

/// ★★ **The shape no demo produces.** `@"OUT"!(1) | … | @"OUT"!(8)` speculated with `[*]`.
///
/// The subject is an ordinary process, not a reflected foreign term, so `guest_for` returns
/// `Ok(None)` and the request server takes `LeafProjection::Configuration`. There is nothing to
/// fire, so the exploration has exactly one leaf — and that leaf's configuration holds
/// [`FAN`] **data on one channel**, which is precisely what `reify` has to order by content.
fn two_data_on_one_channel() -> Par {
    let mut subject = send(OUT, 1);
    for value in 2..=FAN {
        subject = subject.append(send(OUT, value));
    }
    spec_all_request(subject, chan(REPLY))
}

/// The same, with a real tuplespace conflict underneath: one receive, two data, so the search
/// genuinely branches and each of the two leaves still carries a resting datum beside the
/// consumed one.
///
/// Kept alongside the minimal fixture because the two exercise different code: the minimal one
/// reifies a *quiescent* configuration reached in zero steps, this one reifies two
/// configurations reached by firing, and publishes two `^spec-success` entries whose traces are
/// non-empty.
fn a_branching_subject() -> Par {
    spec_all_request(
        send("c", 1)
            .append(send("c", 2))
            .append(send(OUT, 9))
            .append(forward("c", OUT)),
        chan(REPLY),
    )
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The harness
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Every channel a `[*]`-bearing program writes to: the five report channels, the reply
/// channel, and the two request channels (which must end EMPTY — a request still resting means
/// nothing served it, and a silently unserved request would make every comparison below hold
/// trivially).
fn observed() -> Vec<&'static str> {
    vec![
        REPLY,
        OUT,
        SPEC_SUCCESS_CHANNEL,
        SPEC_FAILURE_CHANNEL,
        SPEC_TRUNCATED_CHANNEL,
        SPEC_ERR_CHANNEL,
        SPEC_DELIVERY_CHANNEL,
        SPEC_ALL_CHANNEL,
        SPEC_N_CHANNEL,
    ]
}

/// What one run published: per channel, the sorted multiset of its data's encoded bytes.
type Published = BTreeMap<&'static str, Vec<Vec<u8>>>;

/// Run `program` on a tokio runtime of exactly `threads` worker threads and read back what it
/// published.
///
/// ★ The width is set on a runtime built here rather than through `TOKIO_WORKER_THREADS`,
/// because that variable is read once per process and this test needs several widths in one.
fn publish_at_width(threads: usize, program: Par) -> Published {
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(threads)
        .enable_all()
        .build()
        .expect("a tokio runtime of the requested width must build");

    let rest = runtime.block_on(async move {
        // A guestless engine: every fixture's subject is an ordinary process, so no guest is
        // needed and none is registered. That also keeps this file independent of which
        // generated languages the build happens to include.
        let engine = LookaheadEngine::new();
        run_normalized_par_with_lookahead_engine(&program, &engine, &observed())
            .await
            .expect("the lookahead-bearing program must run to rest")
    });

    let mut published = Published::new();
    for channel in observed() {
        let mut encoded: Vec<Vec<u8>> = rest
            .get(channel)
            .map(|data| data.iter().map(|par| par.encode_to_vec()).collect())
            .unwrap_or_default();
        encoded.sort();
        published.insert(channel, encoded);
    }
    published
}

/// A run's shape, for a failure message that says *what* differed rather than only *that*
/// something did.
fn census(published: &Published) -> String {
    published
        .iter()
        .filter(|(_, data)| !data.is_empty())
        .map(|(channel, data)| format!("{channel}:{}", data.len()))
        .collect::<Vec<_>>()
        .join(" · ")
}

/// The requests were served and the engine raised nothing — without this, an empty answer
/// would make every equality below hold for the wrong reason.
fn assert_the_run_did_something(published: &Published, expected_success: usize) {
    for channel in [SPEC_ALL_CHANNEL, SPEC_N_CHANNEL] {
        assert!(
            published[channel].is_empty(),
            "★ a lookahead request RESTED on {channel}: nothing served it, so this run \
             published nothing and every comparison over it would be vacuous"
        );
    }
    assert!(
        published[SPEC_ERR_CHANNEL].is_empty(),
        "the engine reported a request-level refusal: {:?}",
        published[SPEC_ERR_CHANNEL]
    );
    assert_eq!(
        published[SPEC_SUCCESS_CHANNEL].len(),
        expected_success,
        "★ the exploration must have found {expected_success} branch(es) — census {}",
        census(published)
    );
    assert_eq!(
        published[SPEC_DELIVERY_CHANNEL].len(),
        1,
        "one FIPS collection triple per served request"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The cells
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The reproducibility baseline: **one** width, two runs. A failure here is *"the run is not a
/// function of the program"*, which is a different diagnosis from the cell below it.
#[test]
fn two_runs_at_one_width_publish_the_same_data() {
    let first = publish_at_width(8, two_data_on_one_channel());
    assert_the_run_did_something(&first, 1);
    let second = publish_at_width(8, two_data_on_one_channel());
    assert_eq!(
        first,
        second,
        "★ two runs of one program at one width published different data. The injection \
         randomness is a content hash of the program (`run::deploy_rand`), so this is not \
         entropy — something host-assigned reached the output. census {} vs {}",
        census(&first),
        census(&second)
    );
}

/// ★★ **THE CELL.** Two data on one channel, published identically at every scheduler width.
///
/// This is the shape that makes D1 observable: the leaf's configuration holds two data on
/// `@"OUT"`, `reify` emits them as two `Send`s, and the store `Vec` they come from is
/// *reverse-arrival* order — `HotStore::put_datum` prepends, and the two `|` branches that
/// staged them are detached `tokio::spawn`s racing each other. Widening the pool widens the
/// race.
///
/// Two runs per width, so a single differing run reads as a flake at that width rather than as
/// a width effect — the distinction the recorded scheduler-width dose-response
/// measurement turned on.
#[test]
fn the_published_data_do_not_depend_on_the_scheduler_width() {
    let baseline = publish_at_width(1, two_data_on_one_channel());
    assert_the_run_did_something(&baseline, 1);

    for threads in [1usize, 2, 4, 8, 16] {
        for run in 1..=2 {
            let observed = publish_at_width(threads, two_data_on_one_channel());
            assert_the_run_did_something(&observed, 1);
            assert_eq!(
                observed,
                baseline,
                "★ worker_threads={threads}, run {run}: the PUBLISHED DATA differed from the \
                 single-threaded run. Something a `[*]` produces into the tuplespace is keyed \
                 by task-arrival order rather than by content — a value two validators could \
                 disagree on without either being wrong. census {} vs baseline {}",
                census(&observed),
                census(&baseline)
            );
        }
    }
}

/// …and the same over a subject that genuinely branches, so the comparison covers a
/// configuration reached by *firing* and two `^spec-success` entries with non-empty traces.
#[test]
fn a_branching_exploration_publishes_the_same_data_at_every_width() {
    let baseline = publish_at_width(1, a_branching_subject());
    assert_the_run_did_something(&baseline, 2);

    for threads in [2usize, 4, 8, 16] {
        for run in 1..=2 {
            let observed = publish_at_width(threads, a_branching_subject());
            assert_the_run_did_something(&observed, 2);
            assert_eq!(
                observed,
                baseline,
                "★ worker_threads={threads}, run {run}: a branching exploration published \
                 different data. census {} vs baseline {}",
                census(&observed),
                census(&baseline)
            );
        }
    }
}

/// ★ The fixture's own premise, asserted rather than assumed: the leaf really does hold **two
/// data on one channel**, and the reified configuration really does carry both.
///
/// Without this the two cells above would still pass if the subject silently stopped producing
/// the discriminating shape — the failure mode that made D1 invisible for as long as it was.
#[test]
fn the_fixture_really_does_put_two_data_on_one_channel() {
    use models::rhoapi::expr::ExprInstance;

    let published = publish_at_width(1, two_data_on_one_channel());
    assert_the_run_did_something(&published, 1);

    // The `^spec-success` entry is `[trace, [term]]`, and for the Configuration projection the
    // single term is the reified leaf: a process with two sends on `@"OUT"`.
    let entry = Par::decode(published[SPEC_SUCCESS_CHANNEL][0].as_slice())
        .expect("a published datum re-decodes");
    let Some(ExprInstance::EListBody(pair)) = entry
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("a provenance datum is an EList, got {entry:?}");
    };
    let Some(ExprInstance::EListBody(terms)) = pair.ps[1]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("its second element is the list of projected terms");
    };
    assert_eq!(terms.ps.len(), 1, "the Configuration projection yields one term: the leaf");
    assert_eq!(
        terms.ps[0].sends.len(),
        FAN as usize,
        "★ the reified leaf must carry {FAN} sends — the shape without which a within-channel \
         ordering dependence cannot be observed at all: {:?}",
        terms.ps[0]
    );

    // …and they are all on the SAME channel, which is the other half of the shape.
    let channels: Vec<Option<&Par>> = terms.ps[0]
        .sends
        .iter()
        .map(|send| send.chan.as_ref())
        .collect();
    assert!(channels.windows(2).all(|pair| pair[0] == pair[1]), "★ …and all on ONE channel");
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// ★★ The DETERMINISTIC twin: a real configuration, permuted on purpose
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★★ **The same property, with the race taken out of the measurement.**
///
/// The width cells above are honest but *probabilistic*: they detect an arrival-order
/// dependence only on runs where the arrival order actually differed, and a scheduler is under
/// no obligation to differ. Measured, with the `reify` fix reverted and `FAN = 2`, they caught
/// it once in five runs. A gate that finds a defect one time in five is a gate that reports
/// green four times in five.
///
/// This cell removes the dependence on luck without leaving the integration level. It serves a
/// real request through [`LookaheadService`] — the real reducer, the real tuplespace, the real
/// leaves — and then **permutes the retained configuration's store vectors itself**, which is
/// exactly the difference a differently-scheduled node would have handed back. Both published
/// projections must be byte-identical across the permutation:
///
/// | projection | published as | taken by | the defect it pins |
/// |---|---|---|---|
/// | `reify(leaf)` | the bare reply datum on `x`, and the term inside `^spec-success` | every non-guest `[*]` (`LeafProjection::Configuration`) | D1 / D2 |
/// | `resting_on(leaf, x)` | the same two, one datum per term | every registered-guest `[*]` (`LeafProjection::RestingOn`) | D3 |
///
/// ★ **`deliver` is deliberately NOT the comparison here.** The three FIPS collections are
/// set-mode `EPathMap`s. PathMap absorbs collection enumeration order but preserves the bytes
/// of every process placed in a key; it cannot repair non-canonical `reify` output. This cell
/// therefore compares the process-producing boundary directly, while delivery's own tests pin
/// the separate trie-membership invariant.
///
/// ★ `reverse()` rather than a shuffle: `HotStore::put_datum` **prepends**, so a channel's
/// `Vec` is reverse-arrival order and reversing it is precisely *"the same data, staged in the
/// opposite order"* — the transformation with a mechanism behind it rather than an arbitrary
/// one.
#[test]
fn the_published_leaf_is_invariant_under_permuting_the_retained_store() {
    use mettail_rholang_runtime::speculation::delivery::{reify, resting_on_string};
    use mettail_rholang_runtime::speculation::search::Lookahead;
    use mettail_rholang_runtime::speculation::service::{
        LeafProjection, LookaheadRequest, LookaheadService,
    };
    use rholang::rust::interpreter::accounting::cost_accounting::CostAccounting;
    use rholang::rust::interpreter::accounting::costs::Cost;

    let mut subject = send(OUT, 1);
    for value in 2..=FAN {
        subject = subject.append(send(OUT, value));
    }

    let runtime = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(4)
        .enable_all()
        .build()
        .expect("a tokio runtime must build");

    let exploration = runtime.block_on(async move {
        let host = CostAccounting::empty_cost();
        host.set(Cost::create(1_000_000, "x8 host deploy"));
        LookaheadService::serve(
            LookaheadRequest::new(subject, Lookahead::Unbounded)
                .with_projection(LeafProjection::Configuration),
            crypto::rust::hash::blake2b512_random::Blake2b512Random::create_from_length(128),
            &host,
        )
        .await
        .expect("the service must serve the request")
        .exploration
    });

    assert_eq!(exploration.success.len(), 1, "an inert subject reaches one leaf");
    let leaf = &exploration.success[0];
    let staged: usize = leaf.state.data.values().map(Vec::len).sum();
    assert_eq!(
        staged, FAN as usize,
        "★ the premise: the REAL reducer staged {FAN} data, all on one channel — without that \
         this cell measures nothing"
    );

    let permuted = {
        let mut exploration = exploration.clone();
        for leaf in exploration.success.iter_mut() {
            for data in leaf.state.data.values_mut() {
                data.reverse();
            }
        }
        exploration
    };

    // ── the NON-GUEST path: the reified configuration IS the published datum ────────────
    let reified = reify(&exploration.success[0].state).expect("the leaf reifies");
    assert_eq!(
        reified.sends.len(),
        FAN as usize,
        "the premise again, on the reified side: {FAN} sends"
    );
    assert_eq!(
        reified.encode_to_vec(),
        reify(&permuted.success[0].state)
            .expect("the permuted leaf reifies")
            .encode_to_vec(),
        "★ reversing the staging order of the data on ONE channel changed the reified \
         configuration. That order is `HotStore`'s prepend order — reverse-arrival order — and \
         this `Par` is published verbatim as the bare reply datum on `x` and again inside the \
         `^spec-success` entry."
    );

    // ── the GUEST path: the projection onto the observation channel ────────────────────
    let project = |exploration: &mettail_rholang_runtime::speculation::search::Exploration| {
        resting_on_string(&exploration.success[0].state, OUT)
            .iter()
            .map(|par| par.encode_to_vec())
            .collect::<Vec<_>>()
    };
    let projected = project(&exploration);
    assert_eq!(projected.len(), FAN as usize, "every datum is projected");
    assert_eq!(
        projected,
        project(&permuted),
        "★ …and the guest path's projection moved too. The reply datum at position `i` is \
         minted with `split_short(i)`, so permuting the terms permutes their `random_state`, \
         their `Produce` hashes, and the post-deploy tuplespace content."
    );
}
