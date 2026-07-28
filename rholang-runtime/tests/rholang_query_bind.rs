//! The `!?` QUERY BIND, end to end: `for(p <- svc!?(a…)){B}` must actually query the service.
//!
//! # What was wrong
//!
//! `!?` is request/response sugar. `for(p <- svc!?(a, b)){B}` means: mint a private return
//! channel `r`, send `(*r, a, b)` to the service `svc`, and run `B` with `p` bound to whatever
//! the service replies on `r` — i.e.
//!
//! ```text
//!   new r in { svc!(*r, a, b) | for(p <- r){B} }
//! ```
//!
//! Until 2026-07-28 **the whole feature did nothing**. Not "did the wrong thing" — *nothing*:
//! the expansion above was computed and then discarded, so the program that ran still contained
//! the raw `InputBindQuery`, which resembles an ordinary receive closely enough that the
//! lowering read `svc` as the receive channel, dropped the arguments, and emitted **no request
//! send at all**. The receive then waited forever on a channel nobody sends to.
//!
//! That failure mode is the reason this suite is shaped the way it is. A receive with no
//! partner is *supposed* to rest, so the defect produced no error, no diagnostic, and exit code
//! zero. The program simply printed nothing — which is byte-identical to what a correct program
//! prints when its service happens not to reply.
//!
//! The expansion itself was never the problem. `receive::desugar_for_rows` was correct and was
//! *called* — by `Proc::term_eq`, through `rholang/runtime.rs::normalize_send_sugar_canon`. But
//! `term_eq` builds a COMPARISON KEY. The grammar had declared the expansion as the `PForUser`
//! rule's action (`languages/src/rholang.rs`, `![{ desugar_for_rows(rows, body) }] fold`), but
//! the `fold` marker routes an action to the logic-relation metadata rather than to the parser's
//! semantic action, so nothing expanded the term the parser built. The fix injects the same
//! expansion into `rholang_ast.rs`'s `desugar_surface_sugar_node` — the node hook every other
//! Rholang surface sugar already goes through, run to fixpoint by the lowering driver at every
//! depth.
//!
//! # Why the tests look like this
//!
//! **Every program below carries its own positive control, in the same source and the same
//! run.** A `.rho` that publishes nothing looks exactly the same whether the COMM failed or the
//! harness never observed anything, so a negative result is only evidence next to a positive one
//! that fired under identical conditions. [`harness_has_teeth`] makes that argument explicitly
//! before any other row is trusted.
//!
//! **Every responder RELAYS; none publishes to `@"OUT"` itself.** A marker on `@"OUT"` from a
//! query row is therefore reachable only through the complete round trip — request send on the
//! service channel, reply on the *private* return channel, and the query row's own receive
//! firing. A responder that published directly would produce the same observation whether or not
//! the return channel worked at all.
//!
//! **Every responder pins the request ARGUMENTS by pattern** (`for(@r, @"…ARG…" <- svc)`), so a
//! reply also witnesses that the arguments travelled. An expansion that forwarded only the
//! return channel would leave every one of these resting.
//!
//! # Measured
//!
//! Interpreter run of the three-form matrix, before and after, same source:
//!
//! ```text
//!   before:  @"OUT" observations (1):  [0] ⟦11⟧                        ← the control, alone
//!   after:   @"OUT" observations (4):  [0] ⟦6⟧ [1] ⟦5⟧ [2] ⟦70⟧ [3] ⟦11⟧
//! ```
//!
//! Exit code `0` in both cases — the distinction this suite must preserve is *rests* versus
//! *errors*, and the behaviour was **rests**, which is the harder one to notice.
#![cfg(feature = "rholang-runtime")]

use mettail_languages::rholang::receive::{is_query_bind, pfor_user_still_has_query_rows};
use mettail_languages::rholang::{ForRow, InputBind, Name, Proc, RholangLanguage};
use mettail_rholang_runtime::{
    lower_rholang_proc, run_normalized_par_for_oracle_and_read_runtime_values,
};
use mettail_runtime::{clear_var_cache, Language, RuntimeObservationValue};
use std::sync::Arc;

/// The control marker every program publishes through an ordinary send/receive pair. Its
/// presence says "this harness observed this run"; its absence invalidates the whole row.
const CONTROL: &str = "ZQCONTROLZQ";

/// Parse via the PRODUCTION entry. `Proc::parse` round-trips through the display, which is not
/// term-preserving for a projection operand (see `rholang_guard_lowering.rs`'s header); every
/// production caller uses `parse_via_wpda`, so the gate must too.
fn parse(source: &str) -> Proc {
    clear_var_cache();
    Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rholang parse failed for {source:?}: {err:?}"))
}

/// Run `source` to rest and return the `Text` markers resting on `@"OUT"`, sorted.
///
/// Sorted because `@"OUT"` is a multiset and the reduction order across independent branches is
/// not a property this suite is about; every marker is distinct, so sorting loses nothing.
async fn markers(source: &str) -> Vec<String> {
    let par = lower_rholang_proc(&parse(source))
        .unwrap_or_else(|err| panic!("rholang lowering failed for {source:?}: {err:?}"));
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&par, "OUT")
        .await
        .unwrap_or_else(|err| panic!("reduction failed for {source:?}: {err}"));
    let mut texts: Vec<String> = observed
        .into_iter()
        .filter_map(|value| match value {
            RuntimeObservationValue::Text(text) => Some(text),
            _ => None,
        })
        .collect();
    texts.sort();
    texts
}

/// The control fragment: an ordinary send/receive pair publishing [`CONTROL`].
const CONTROL_FRAGMENT: &str = r#"@"ctl"!("ZQCONTROLZQ") | for(@c <- @"ctl") { @"OUT"!(c) }"#;

/// Assert that `query_fragment` — composed in parallel with the control — publishes exactly
/// `expected` alongside the control.
async fn assert_query_delivers(query_fragment: &str, expected: &str) {
    let source = format!("{CONTROL_FRAGMENT} | {query_fragment}");
    let observed = markers(&source).await;
    let mut wanted = vec![CONTROL.to_string(), expected.to_string()];
    wanted.sort();
    assert_eq!(
        observed, wanted,
        "the query bind must deliver {expected:?} through its private return channel, with the \
         control firing beside it in the same run\nsource:\n{source}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The teeth test — run before anything else is believed
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The detector separates a firing from a non-firing.
///
/// Without this, every assertion below could be satisfied by a harness that observes nothing:
/// "the query marker is absent" and "the harness cannot see markers" are the same reading, and
/// the second is exactly the mistake the `!?` defect survived for as long as it did. So the
/// control is shown to fire on its own, and a receive with no partner is shown to publish
/// nothing while that same control still fires.
#[tokio::test(flavor = "multi_thread")]
async fn harness_has_teeth() {
    assert_eq!(
        markers(CONTROL_FRAGMENT).await,
        vec![CONTROL.to_string()],
        "the control must fire on its own"
    );
    let partnerless = format!(
        r#"{CONTROL_FRAGMENT} | for(@x <- @"nobody-sends-here") {{ @"OUT"!("ZQNEVERZQ") }}"#
    );
    assert_eq!(
        markers(&partnerless).await,
        vec![CONTROL.to_string()],
        "a receive with no partner must rest silently WHILE the control still fires — the two \
         readings this suite must never confuse"
    );
}

/// ★ The defect was **rests**, not **errors** — and those are different findings.
///
/// A query bind whose service never answers must leave the program resting and the run
/// successful, exactly as an ordinary partnerless receive does. Pinning this keeps a future
/// "fix" from turning an unanswered query into a failure, and records that the original symptom
/// was silence rather than a fault.
#[tokio::test(flavor = "multi_thread")]
async fn an_unanswered_query_rests_it_does_not_error() {
    let no_responder =
        format!(r#"{CONTROL_FRAGMENT} | for(p <- @"unserved"!?("Q")) {{ @"OUT"!(*p) }}"#);
    assert_eq!(
        markers(&no_responder).await,
        vec![CONTROL.to_string()],
        "an unanswered query rests; the run still succeeds and the control still fires"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// THE PER-FORM MATRIX — one row per `!?` surface the grammar admits
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `lhs <- n!?(args…)` — `InputBindQuery`. The reply binds a NAME, dropped in the body.
#[tokio::test(flavor = "multi_thread")]
async fn plain_query_bind_completes_the_round_trip() {
    assert_query_delivers(
        r#"for(@rp, @"ZQPLAINARGZQ" <- @"svcP") { @rp!("ZQPLAINZQ") }
           | for(p <- @"svcP"!?("ZQPLAINARGZQ")) { @"OUT"!(*p) }"#,
        "ZQPLAINZQ",
    )
    .await;
}

/// `@pat <- n!?(args…)` — `InputBindQuotedQuery`. The reply binds a PROCESS pattern.
///
/// ★ This is the arm that stayed inert even after the injection landed: `desugar_query_bind`
/// handled `InputBindQuery` and `InputBindEmptyQuery` and fell through on the quoted form, while
/// `pfor_user_still_has_query_rows` — whose doc comment named `InputBindQuotedQuery` — omitted it
/// from all four of its arms, so nothing could report the omission.
#[tokio::test(flavor = "multi_thread")]
async fn quoted_query_bind_completes_the_round_trip() {
    assert_query_delivers(
        r#"for(@rq, @"ZQQUOTEDARGZQ" <- @"svcQ") { @rq!("ZQQUOTEDZQ") }
           | for(@y <- @"svcQ"!?("ZQQUOTEDARGZQ")) { @"OUT"!(y) }"#,
        "ZQQUOTEDZQ",
    )
    .await;
}

/// `<- n!?(args…)` — `InputBindEmptyQuery`. Nothing is bound, so the body firing IS the
/// observation: it runs only when the empty reply arrives on the private return channel.
#[tokio::test(flavor = "multi_thread")]
async fn empty_query_bind_completes_the_round_trip() {
    assert_query_delivers(
        r#"for(@re, @"ZQEMPTYARGZQ" <- @"svcE") { @re!() }
           | for(<- @"svcE"!?("ZQEMPTYARGZQ")) { @"OUT"!("ZQEMPTYZQ") }"#,
        "ZQEMPTYZQ",
    )
    .await;
}

/// A query with NO arguments — the request carries the return channel and nothing else.
///
/// The arity is the whole point of this row. `c!?()` expands to `c!(*r)`, a MONADIC send whose
/// datum is `⟦*r⟧`, so the ordinary responder `for(@r <- c)` must match it. `mk_output` used to
/// wrap unconditionally, making the datum `⟦[*r]⟧` — matchable only by `for(@[r] <- c)`. No `!?`
/// shape test could see that, because they all compare through `term_eq`, whose canon maps a
/// scalar payload to its one-element list precisely so the two spellings compare EQUAL.
#[tokio::test(flavor = "multi_thread")]
async fn zero_argument_query_sends_a_monadic_request() {
    assert_query_delivers(
        r#"for(@rz <- @"svcZ") { @rz!("ZQZEROZQ") }
           | for(z <- @"svcZ"!?()) { @"OUT"!(*z) }"#,
        "ZQZEROZQ",
    )
    .await;
}

/// Several arguments, pinned positionally by the responder's pattern.
#[tokio::test(flavor = "multi_thread")]
async fn multi_argument_query_forwards_every_argument_in_order() {
    assert_query_delivers(
        r#"for(@rm, @"A1", @"A2", @"A3" <- @"svcM") { @rm!("ZQMULTIZQ") }
           | for(m <- @"svcM"!?("A1", "A2", "A3")) { @"OUT"!(*m) }"#,
        "ZQMULTIZQ",
    )
    .await;
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Placement — a query bind is expanded wherever it appears, not only at the top
// ════════════════════════════════════════════════════════════════════════════════════════════

/// A query bind in the BODY of another `for`.
///
/// This position had its own hole. The lowering driver's `schedule_for_body` recognises a body
/// that is itself a `for` and hands its rows STRAIGHT to the receive machinery, bypassing the
/// node hook where surface sugar is expanded — a shortcut that is valid only when the inner
/// `for` really is a receive. A `!?` row denotes a `new`-scoped `send | receive`, so it now
/// takes the ordinary body route instead; without that, this row would keep exactly the inert
/// reading the top-level form was fixed to lose.
#[tokio::test(flavor = "multi_thread")]
async fn query_bind_nested_in_a_receive_body_is_expanded() {
    assert_query_delivers(
        r#"for(@rn, @"ZQNESTARGZQ" <- @"svcN") { @rn!("ZQNESTEDZQ") }
           | for(@t <- @"tick") { for(@o <- @"svcN"!?("ZQNESTARGZQ")) { @"OUT"!(o) } }
           | @"tick"!(1)"#,
        "ZQNESTEDZQ",
    )
    .await;
}

/// A query bind inside a `new` scope.
#[tokio::test(flavor = "multi_thread")]
async fn query_bind_inside_a_new_scope_is_expanded() {
    assert_query_delivers(
        r#"for(@rw, @"ZQNEWARGZQ" <- @"svcW") { @rw!("ZQINNEWZQ") }
           | new local in { for(@v <- @"svcW"!?("ZQNEWARGZQ")) { @"OUT"!(v) | local!(0) } }"#,
        "ZQINNEWZQ",
    )
    .await;
}

/// Two query rows in ONE `for`, each getting its OWN private return channel.
///
/// The expansion hoists both requests under a single `new` with two binders. If the two rows
/// shared a return channel, either reply could satisfy either row and this would still pass — so
/// the two services answer with DIFFERENT markers and the body publishes both, which pins the
/// pairing rather than merely the arrival.
#[tokio::test(flavor = "multi_thread")]
async fn two_query_rows_get_distinct_private_return_channels() {
    let source = format!(
        r#"{CONTROL_FRAGMENT}
           | for(@r1, @"ARG1" <- @"svc1") {{ @r1!("ZQONEZQ") }}
           | for(@r2, @"ARG2" <- @"svc2") {{ @r2!("ZQTWOZQ") }}
           | for(@a <- @"svc1"!?("ARG1") & @b <- @"svc2"!?("ARG2")) {{ @"OUT"!(a) | @"OUT"!(b) }}"#
    );
    let observed = markers(&source).await;
    let mut wanted = vec![CONTROL.to_string(), "ZQONEZQ".to_string(), "ZQTWOZQ".to_string()];
    wanted.sort();
    assert_eq!(
        observed, wanted,
        "each query row must query its OWN service on its OWN return channel\nsource:\n{source}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Structure — the expanded program really is a `new`-scoped send ∥ receive
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The lowered program CONTAINS the request send, and no receive is left waiting on the service
/// channel.
///
/// The behavioural rows above prove a reply arrived; this proves the shape that carried it, so a
/// future regression that reached the same observation by a different route (a host-side
/// shortcut, say) would still be visible as a change here. `svc!(…)` must appear as a real send
/// in the emitted `Par` — under the `new`, hence one `news` entry and no top-level `receives`.
#[test]
fn a_query_bind_lowers_to_a_new_scoped_send_and_receive() {
    let par = lower_rholang_proc(&parse(r#"for(p <- @"svc"!?(1)) { @"OUT"!(*p) }"#))
        .expect("a query bind must lower");
    assert_eq!(
        par.news.len(),
        1,
        "the expansion mints a private return channel, so the program is a `new` scope: {par:?}"
    );
    assert!(
        par.receives.is_empty() && par.sends.is_empty(),
        "everything lives UNDER the `new`; nothing may escape it: {par:?}"
    );
    let scope = par.news[0]
        .p
        .as_ref()
        .expect("the `new` scope must carry a body");
    assert_eq!(
        (scope.sends.len(), scope.receives.len()),
        (1, 1),
        "inside the `new`: exactly one request SEND and one reply RECEIVE — the send is the leg \
         whose absence made the whole feature inert: {scope:?}"
    );
}

/// Nothing survives the expansion. Whatever the driver hands to the receive machinery must be
/// free of query rows, or the driver's expansion fixpoint would re-offer it forever.
#[test]
fn expansion_leaves_no_query_rows_behind() {
    for source in [
        r#"for(p <- @"s"!?(1)) { Nil }"#,
        r#"for(@p <- @"s"!?(1)) { Nil }"#,
        r#"for(<- @"s"!?(1)) { Nil }"#,
        r#"for(p <- @"s"!?(1) & q <- @"t"!?(2)) { Nil }"#,
        r#"for(p <- @"s"!?(1); q <- @"t"!?(2)) { Nil }"#,
    ] {
        let parsed = parse(source);
        let Proc::PForUser(rows, _) = &parsed else {
            panic!("{source:?} must parse to a `for`, got {parsed:?}");
        };
        assert!(
            pfor_user_still_has_query_rows(rows),
            "{source:?} must PARSE with its query rows intact — otherwise this row proves \
             nothing about the expansion"
        );
        let expanded =
            mettail_languages::rholang::receive::desugar_for_rows(rows.clone(), &Proc::PZero);
        let Proc::PNew(scope) = &expanded else {
            panic!("{source:?} must expand to a `new` scope, got {expanded:?}");
        };
        let (_, body) = scope.clone().unbind::<String>();
        let mut receives = 0usize;
        if let Proc::PPar(parts) = body.as_ref() {
            for part in parts.iter_elements() {
                if let Proc::PForUser(inner_rows, _) = part {
                    receives += 1;
                    assert!(
                        !pfor_user_still_has_query_rows(inner_rows),
                        "{source:?} left an unexpanded query row behind: {inner_rows:?}"
                    );
                }
            }
        }
        assert_eq!(receives, 1, "{source:?} must expand to exactly one receive: {body:?}");
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The ENUMERATING GATE — the covered set is read off the GRAMMAR, not hand-listed
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The `!?` surfaces this suite covers behaviourally, one per grammar rule.
const COVERED_QUERY_RULES: &[&str] =
    &["InputBindQuery", "InputBindEmptyQuery", "InputBindQuotedQuery"];

/// Every `InputBind` rule whose DECLARED SYNTAX carries `!?(`, read out of the language
/// metadata.
///
/// Derived rather than listed, because a hand-listed set is what failed here: the rewriter's
/// list and the guard's list were each written by hand, each omitted `InputBindQuotedQuery`, and
/// the guard's own doc comment named the rule it did not check. A census taken from the grammar
/// cannot drift from the grammar.
fn declared_query_rules() -> Vec<&'static str> {
    let mut names: Vec<&'static str> = RholangLanguage
        .metadata()
        .terms()
        .iter()
        .filter(|term| term.type_name == "InputBind" && term.syntax.contains("!?("))
        .map(|term| term.name)
        .collect();
    names.sort_unstable();
    names
}

/// ★ Adding a fourth `!?` rule to the grammar fails HERE until it is covered.
///
/// This is the gate the feature never had. `!?` shipped with three surfaces and an expansion
/// that handled two; nothing in the tree related the two counts, so the third could stay inert
/// indefinitely while thirty-odd `query_receive_sugar_*` tests passed around it.
#[test]
fn every_declared_query_bind_surface_is_covered_behaviourally() {
    let declared = declared_query_rules();
    let mut covered = COVERED_QUERY_RULES.to_vec();
    covered.sort_unstable();
    assert_eq!(
        declared, covered,
        "the grammar's `!?` surfaces and this suite's behavioural coverage have diverged. \
         Add the missing form to the matrix above (and to `receive::as_query_bind`, which the \
         expansion and its guard both read) — do not edit COVERED_QUERY_RULES to match."
    );
    assert!(
        !declared.is_empty(),
        "the census found NO `!?` rules, so this gate is inert — the metadata shape it reads \
         (`TermDef.type_name` / `TermDef.syntax`) must have changed"
    );
}

/// The classifier agrees with the census, variant for variant.
///
/// The census above is over rule NAMES; this is over constructed VALUES, so together they pin
/// that each declared surface is not merely named but actually recognised by the one predicate
/// the expansion and the guard both consult.
#[test]
fn the_classifier_recognises_every_declared_query_surface() {
    let channel = || Arc::new(Name::NQuote(Arc::new(Proc::PZero)));
    let lhs = || Arc::new(Name::NQuote(Arc::new(Proc::PZero)));
    let pat = || Arc::new(Proc::PZero);
    let args = || vec![Proc::PZero];

    let by_rule: Vec<(&str, InputBind)> = vec![
        ("InputBindQuery", InputBind::InputBindQuery(lhs(), channel(), args())),
        ("InputBindEmptyQuery", InputBind::InputBindEmptyQuery(channel(), args())),
        (
            "InputBindQuotedQuery",
            InputBind::InputBindQuotedQuery(pat(), channel(), args()),
        ),
    ];
    let named: Vec<&str> = by_rule.iter().map(|(name, _)| *name).collect();
    let mut named_sorted = named.clone();
    named_sorted.sort_unstable();
    assert_eq!(
        named_sorted,
        declared_query_rules(),
        "this test must exhibit one value per DECLARED query rule"
    );
    for (name, bind) in &by_rule {
        assert!(is_query_bind(bind), "`{name}` must be recognised as a query bind");
    }

    // And the ordinary binds are NOT queries — a classifier that answered `true` for everything
    // would satisfy the loop above and spin the expansion fixpoint.
    for (name, bind) in [
        ("InputBind", InputBind::InputBind(lhs(), channel())),
        ("InputBindQuoted", InputBind::InputBindQuoted(pat(), channel())),
        ("InputBindEmpty", InputBind::InputBindEmpty(channel())),
        ("InputBindPersistent", InputBind::InputBindPersistent(lhs(), channel())),
    ] {
        assert!(!is_query_bind(&bind), "`{name}` is an ordinary bind, not a query");
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The RESIDUE GUARD — non-vacuous over every (ForRow shape × query form) pair
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `pfor_user_still_has_query_rows` reports every query form in every row shape that carries
/// binds.
///
/// The guard it replaces claimed `InputBindQuotedQuery` in its documentation and checked for it
/// in none of its four arms, and no test ever built one — so the claim and the code disagreed in
/// silence. This walks the full matrix: three query forms × four bind-carrying `ForRow` shapes ×
/// both bind POSITIONS (row head and `&`-join tail), and pins the negative direction too.
#[test]
fn the_residue_guard_sees_every_query_form_in_every_row_shape() {
    let channel = || Arc::new(Name::NQuote(Arc::new(Proc::PZero)));
    let lhs = || Arc::new(Name::NQuote(Arc::new(Proc::PZero)));
    let pat = || Arc::new(Proc::PZero);
    let args = || vec![Proc::PZero];
    let ordinary = || InputBind::InputBind(lhs(), channel());

    let queries: Vec<(&str, InputBind)> = vec![
        ("InputBindQuery", InputBind::InputBindQuery(lhs(), channel(), args())),
        ("InputBindEmptyQuery", InputBind::InputBindEmptyQuery(channel(), args())),
        (
            "InputBindQuotedQuery",
            InputBind::InputBindQuotedQuery(pat(), channel(), args()),
        ),
    ];

    for (name, query) in &queries {
        // The query bind as the row HEAD, in each of the four bind-carrying row shapes.
        let heads: Vec<(&str, ForRow)> = vec![
            ("ForRowSingleNoWhere", ForRow::ForRowSingleNoWhere(Arc::new(query.clone()))),
            (
                "ForRowSingleWhere",
                ForRow::ForRowSingleWhere(Arc::new(query.clone()), Arc::new(Proc::PZero)),
            ),
            (
                "ForRowNoWhere",
                ForRow::ForRowNoWhere(Arc::new(query.clone()), vec![ordinary()]),
            ),
            (
                "ForRowWhere",
                ForRow::ForRowWhere(
                    Arc::new(query.clone()),
                    vec![ordinary()],
                    Arc::new(Proc::PZero),
                ),
            ),
        ];
        for (shape, row) in heads {
            assert!(
                pfor_user_still_has_query_rows(std::slice::from_ref(&row)),
                "`{name}` as the head of `{shape}` must be reported as residue"
            );
        }

        // And in the `&`-join TAIL, where an ordinary head could mask it.
        let tails: Vec<(&str, ForRow)> = vec![
            (
                "ForRowNoWhere",
                ForRow::ForRowNoWhere(Arc::new(ordinary()), vec![query.clone()]),
            ),
            (
                "ForRowWhere",
                ForRow::ForRowWhere(
                    Arc::new(ordinary()),
                    vec![query.clone()],
                    Arc::new(Proc::PZero),
                ),
            ),
        ];
        for (shape, row) in tails {
            assert!(
                pfor_user_still_has_query_rows(std::slice::from_ref(&row)),
                "`{name}` in the `&`-join tail of `{shape}` must be reported as residue"
            );
        }
    }

    // The negative direction: a guard that answered `true` unconditionally would satisfy every
    // assertion above AND would make the expansion fixpoint spin.
    let plain_rows = vec![
        ForRow::ForRowSingleNoWhere(Arc::new(ordinary())),
        ForRow::ForRowNoWhere(Arc::new(ordinary()), vec![ordinary()]),
    ];
    assert!(
        !pfor_user_still_has_query_rows(&plain_rows),
        "rows with no query bind must not be reported as residue"
    );
    assert!(!pfor_user_still_has_query_rows(&[]), "an empty row list has no residue");
}
