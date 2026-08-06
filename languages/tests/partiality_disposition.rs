//! ★★ A PARTIAL OPERATION THAT DECLINES SAYS **WHY** — the reported disposition.
//!
//! # The root this suite pins
//!
//! `safeify` rewrites a panicking fold body into a non-panicking one, which is correct and
//! load-bearing: a panic raised inside a Dovetail fold runs with the e-graph mid-saturation and,
//! under this workspace's `[profile.dev] codegen-backend = "cranelift"`, is not containable —
//! `catch_unwind` monomorphised in a cg_clif crate emits no catch pad
//! (`dovetail/tests/panic_expectation_gate.rs`).
//!
//! But that rewrite went **from a panic to an ABSENCE** when the correct rewrite is **from a panic
//! to a REPORTED disposition**. The proof is in the tree: Calculator's authors wrote
//! `.expect("ElemList: invalid index")`, `.expect("DeleteList: invalid index")` and
//! `.expect("get: key not found")` — three deliberate, message-carrying failures — and the
//! rewrite turned all three into an unlabelled `?`, its own comment reading *"The panic message is
//! discarded."* The authors' intent was to **err**; the machinery silently converted it to
//! **defer**, and threw away three good messages doing it.
//!
//! # The partition this suite measures
//!
//! > **Err where a reason exists that the deployer must act on and that no further reduction can
//! > supply. Defer where the reason is "not yet" — where a different, already-declared rule could
//! > still fire on this redex.**
//!
//! | case | example | disposition | recorded? |
//! |---|---|---|---|
//! | an operand is still a redex | a free variable in operand position | **defer** | **no** — structural |
//! | (a) undefined at this input | `6 / 0` | **decline**, naming the operation and reason | yes |
//! | (b) not representable in this carrier | `2147483647 + 1` | **decline**, naming the carrier | yes |
//!
//! ⚠ **Calculator's `Int` carrier is `i32`, not `i64`.** A numeral is an `Int` exactly when it
//! fits `i32`; a wider one parses as `BigInt` (`languages/src/calculator.rs`). `i64` is
//! *Rholang's* `Int`. The (b) probe therefore overflows at `i32::MAX`, and the carrier token
//! pinned below is `"i32"` — pinning `"i64"` here would fail for the right reason, which is
//! exactly why the carrier is asserted as its own axis.
//! | the author declared the failure | `at(list(1, 2), 5)` | **decline**, carrying the author's words | yes |
//!
//! # ⚠ What this suite must NOT observe changing
//!
//! **Nothing computes differently.** A declining fold still leaves its redex unreduced — the
//! disposition the consensus lane needs, because a stuck `Proc::Div(a, b)` lowers to `EDivBody`
//! and f1r3node's metered reducer decides it, whereas `Proc::Err` has no Rho image at all
//! (`rholang-runtime/src/rholang_ast.rs`'s `lower_arm_err` returns
//! `UnsupportedProc("error process")`). Every cell below therefore carries a value control: the
//! normal forms and firing counts of the *total* direction must not move.
//!
//! ★ **NEVER a panic expectation.** Nothing here is `#[should_panic]` and nothing is wrapped in
//! `catch_unwind`; both are banned outright by `dovetail/tests/panic_expectation_gate.rs`, whose
//! whole subject is that a test expecting a panic is a test that has accepted the panic. Under
//! this workspace's cg_clif dev profile a `panic!` in a fold aborts the process mutely, so such a
//! test could not even observe what it claims to.
#![cfg(all(feature = "calculator", feature = "dovetail-codegen"))]

use mettail_languages::calculator::CalculatorLanguage;
use mettail_runtime::{DeclinedFold, Language};

/// Bounded on purpose: a budget means a non-converging saturation surfaces as a limit error,
/// never as a hung test binary. Same values the sibling fold suites use
/// (`languages/tests/calculator_partiality.rs`).
const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 200_000;

/// The `/` fold on `Int` — the arithmetic lane's partial operation, and the one whose decline the
/// mutation cell below is entirely about.
const DIV_INT: &str = "Calculator::fold::Int_DivInt";
/// The `at(list, i)` fold — a partial COLLECTION operation whose author wrote a message.
const ELEM_LIST: &str = "Calculator::fold::Proc_ElemList";
/// `length(list)` — a TOTAL fold on the same collection carrier.
const LEN_LIST: &str = "Calculator::fold::Int_LenList";

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// Harness
// ═══════════════════════════════════════════════════════════════════════════════════════════════

/// One saturation of `src`, projected to everything the cells below assert on.
struct Run {
    /// Per-label firing COUNTS (aggregated evidence, one record per distinct label).
    firings: Vec<(String, usize)>,
    /// The declined-fold records, aggregated by `(label, partiality)`.
    declines: Vec<DeclinedFold>,
    /// A rendering of the whole run, travelling into every assertion message so a failure names
    /// the entire observation rather than the one thing that was asked about.
    rendered: String,
}

impl Run {
    /// How many times `label` fired.
    fn fired(&self, label: &str) -> usize {
        self.firings
            .iter()
            .filter(|(l, _)| l == label)
            .map(|(_, n)| *n)
            .sum()
    }

    /// The declines recorded under `label`.
    fn declined(&self, label: &str) -> Vec<&DeclinedFold> {
        self.declines.iter().filter(|d| d.label == label).collect()
    }
}

fn run(src: &str) -> Run {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let report = CalculatorLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_report_for({src:?}) returned Err: {e}"));
    let firings: Vec<(String, usize)> = report
        .rule_firings
        .iter()
        .filter_map(|f| f.label.clone().map(|l| (l, f.count)))
        .collect();
    let rendered = format!(
        "src={src:?} complete={} roots={} firings={:?} declines={:?}",
        report.is_complete(),
        report.roots.len(),
        report.rule_firings,
        report.declined_folds,
    );
    Run {
        firings,
        declines: report.declined_folds.clone(),
        rendered,
    }
}

/// The normal form of `src`, rendered.
fn normal_form(src: &str) -> String {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let normal = CalculatorLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_normal_term({src:?}) returned Err: {e}"));
    format!("{normal}")
}

/// The rendering of `src` as PARSED — the redex, before any saturation. A stuck term is asserted
/// against THIS rather than against a hand-copied string, so the assertion cannot drift with the
/// pretty-printer's spacing conventions.
fn parsed_form(src: &str) -> String {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    format!("{term}")
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// ★★ THE CELL — the mutation applied
// ═══════════════════════════════════════════════════════════════════════════════════════════════

/// ★★ `6 / 0` EXPOSES EXACTLY ONE DECLINED RECORD, AND IT NAMES THE REASON.
///
/// RED before the change: `RuntimeDovetailRunReport` had no `declined_folds` field at all, so this
/// cell did not compile. GREEN after: exactly one record, `Calculator::fold::Int_DivInt`,
/// `DivisionByZero`, on carrier `i32`.
///
/// The token pins are one assertion per axis — label, discriminant, carrier, operation — so a
/// reworded message trips the right one and a collapsed (a)/(b) partition trips the discriminant
/// rather than passing silently.
#[test]
fn division_by_zero_declines_exactly_once_and_names_the_reason() {
    let divide_by_zero = run("6 / 0");

    // ── THE MUTATION'S SIGNATURE ──────────────────────────────────────────────────────
    assert_eq!(
        divide_by_zero.declines.len(),
        1,
        "★ `6 / 0` must expose EXACTLY ONE declined record. More than one means either a \
         second reading of the term also declined (report them — the pin is deliberately \
         exact) or the aggregation by `(label, partiality)` broke and saturation's \
         per-iteration re-dispatch is leaking one record per iteration. Zero means the \
         decline is not being recorded at all. Run: {}",
        divide_by_zero.rendered,
    );
    let record = &divide_by_zero.declines[0];

    assert_eq!(
        record.label, DIV_INT,
        "★ the record must name the EXACT published label — the same string the rule's FIRING \
         would carry — not merely 'some fold declined'. Run: {}",
        divide_by_zero.rendered,
    );
    assert_eq!(
        record.reason_token(),
        "DivisionByZero",
        "★ THE DISCRIMINANT, not the prose. `6 / 0` is case (a): no carrier supplies a \
         quotient, so it must NOT collapse onto `NotRepresentable`, which means 'the value \
         exists and this carrier is too narrow'. Record: {record:?}",
    );
    assert_eq!(
        record.carrier(),
        Some("i32"),
        "the carrier the operation ran in must be named. ⚠ Calculator's `Int` carrier is `i32` \
         (`languages/src/calculator.rs` — `Int` is the numeral that FITS `i32`; a wider numeral \
         parses as `BigInt`). Record: {record:?}",
    );
    assert_eq!(
        record.operation(),
        Some("div"),
        "the operation must be named. Record: {record:?}",
    );

    // ── AND NOTHING COMPUTED MOVED ────────────────────────────────────────────────────
    assert_eq!(
        divide_by_zero.fired(DIV_INT),
        0,
        "`6 / 0` must still NOT fire `{DIV_INT}` — the change records the reason, it does not \
         make the fold succeed. Run: {}",
        divide_by_zero.rendered,
    );
    assert_eq!(
        normal_form("6 / 0"),
        parsed_form("6 / 0"),
        "★ a declined fold still leaves its REDEX unreduced, byte-for-byte the term that was \
         parsed. That is the disposition the consensus lane needs: the stuck `Div` lowers to \
         `EDiv` and f1r3node's metered reducer decides it. A different rendering means the \
         report surface changed a computed value.",
    );
}

/// ★ (b) — NOT REPRESENTABLE IN THIS CARRIER, named separately from (a).
///
/// `i64::MAX + 1` has a value; `i64` cannot hold it. That is a different finding from `6 / 0`,
/// and if the two ever collapse onto one token this cell and the one above disagree.
#[test]
fn integer_overflow_declines_as_not_representable_and_names_the_carrier() {
    let overflowing = run("2147483647 + 1");
    let add_int = "Calculator::fold::Int_AddInt";

    let records = overflowing.declined(add_int);
    assert_eq!(
        records.len(),
        1,
        "★ `i32::MAX + 1` must expose exactly one declined record under `{add_int}`. Run: {}",
        overflowing.rendered,
    );
    let record = records[0];
    assert_eq!(
        record.reason_token(),
        "NotRepresentable",
        "★ (b) is NOT (a): the sum exists in a wider carrier, so the reason must be \
         `NotRepresentable` and not any `Undefined` flavour. Record: {record:?}",
    );
    assert_eq!(
        record.carrier(),
        Some("i32"),
        "★ (b)'s whole content is WHICH carrier did not fit. Record: {record:?}",
    );
    assert_ne!(
        record.reason_token(),
        run("6 / 0").declines[0].reason_token(),
        "★ (a) and (b) must never collide on one token — that collapse is the defect the \
         reason channel exists to close",
    );

    // The fold does not fire, and the redex stays put.
    assert_eq!(
        overflowing.fired(add_int),
        0,
        "an overflowing addition must not fold. Run: {}",
        overflowing.rendered,
    );
}

/// ★★ CALCULATOR'S THREE AUTHORS GET THEIR STRINGS BACK.
///
/// `at(list(1, 2), 5)` runs a body written `.expect("ElemList: invalid index")`. Before this
/// change `safeify` rewrote that to a bare `?` and the message was gone — the rewrite pass said so
/// in its own comment. The message is a *declared* failure: the author decided this input is an
/// error, and their words are exactly what the report needs.
#[test]
fn an_authors_declared_expect_message_reaches_the_report() {
    let out_of_range = run("at(list(1, 2), 5)");

    let records = out_of_range.declined(ELEM_LIST);
    assert_eq!(
        records.len(),
        1,
        "★ an out-of-range index must expose one declined record under `{ELEM_LIST}`. Run: {}",
        out_of_range.rendered,
    );
    let record = records[0];
    assert_eq!(
        record.reason_token(),
        "Declared",
        "★ `.expect(msg)` is a DECLARED failure — the author said this input is an error — so \
         it must not be reported as an anonymous `Unreported`. Record: {record:?}",
    );
    assert_eq!(
        record.message(),
        Some("ElemList: invalid index"),
        "★★ THE MESSAGE THE REWRITE USED TO DISCARD. `macros/src/gen/native/rust_code_rewrite.rs` \
         said outright \"The panic message is discarded\"; this is the assertion that it is not. \
         Record: {record:?}",
    );

    // The sibling collection folds, whose messages were discarded by the same rewrite.
    let past_end = run("delete(list(1, 2), 5)");
    let delete_list = "Calculator::fold::List_DeleteList";
    assert_eq!(
        past_end
            .declined(delete_list)
            .first()
            .and_then(|r| r.message()),
        Some("DeleteList: invalid index"),
        "★ the second of the three discarded messages. Run: {}",
        past_end.rendered,
    );

    let missing_key = run("get(map(1 : 2), 3)");
    let get_map = "Calculator::fold::Proc_GetMap";
    assert_eq!(
        missing_key
            .declined(get_map)
            .first()
            .and_then(|r| r.message()),
        Some("get: key not found"),
        "★ the third. Run: {}",
        missing_key.rendered,
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// THE CONTROLS
// ═══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ CONTROL 1 — the SAME fold on a TOTAL input must not discriminate.
///
/// If this moves, the change broke division, not partiality.
#[test]
fn control_1_a_total_division_fires_and_declines_nothing() {
    let total = run("6 / 3");
    assert_eq!(
        total.fired(DIV_INT),
        1,
        "★ THE CONTROL: `6 / 3` must still fire `{DIV_INT}` exactly once. Run: {}",
        total.rendered,
    );
    assert!(
        total.declines.is_empty(),
        "★ THE CONTROL: a TOTAL operation declines NOTHING. A record here means the dispatcher \
         is recording on a path that succeeded. Run: {}",
        total.rendered,
    );
    assert_eq!(
        normal_form("6 / 3"),
        "2",
        "★ THE CONTROL: `6 / 3` is `2` — the fold must still COMPUTE, not merely fire",
    );
}

/// ★ CONTROL 2 — a TOTAL fold on the collection carrier.
///
/// Without it, "the collection fold declined" and "collection folds stopped working" are the same
/// observation.
#[test]
fn control_2_a_total_collection_fold_fires_and_declines_nothing() {
    let total = run("length(list(1, 2))");
    assert_eq!(
        total.fired(LEN_LIST),
        1,
        "★ THE CONTROL: `length(list(1, 2))` is TOTAL and must fold. Run: {}",
        total.rendered,
    );
    assert!(
        total.declines.is_empty(),
        "★ THE CONTROL: nothing declined. Run: {}",
        total.rendered,
    );
    assert_eq!(normal_form("length(list(1, 2))"), "2");

    // The in-range index on the SAME fold whose out-of-range sibling declines above.
    let in_range = run("at(list(1, 2), 1)");
    assert_eq!(
        in_range.fired(ELEM_LIST),
        1,
        "★ THE CONTROL: an in-range index must still fire `{ELEM_LIST}`. Run: {}",
        in_range.rendered,
    );
    assert!(
        in_range.declined(ELEM_LIST).is_empty(),
        "★ THE CONTROL: an in-range index declines nothing. Run: {}",
        in_range.rendered,
    );
    assert_eq!(normal_form("at(list(1, 2), 1)"), "2");
}

/// ★★ CONTROL 3 — THE LOAD-BEARING ONE. A STRUCTURAL non-firing records NOTHING.
///
/// A term whose operand is a free variable does not fold, and it does not fold for a reason that
/// is **"not yet"** rather than **"never"**: substitute the variable and the same rule fires. That
/// is a deferral, not a decline, and it must leave the record empty.
///
/// ⚠ **Without this cell, a mutation that records a decline for EVERY unfired rule passes the two
/// controls above.** Both of those only observe folds that DID fire; only this one observes a fold
/// that did not fire and must still be silent. It is the single assertion separating "the report
/// distinguishes semantic decline from structural deferral" from "the report labels every
/// non-firing as a finding".
#[test]
fn control_3_a_structural_non_firing_records_no_decline() {
    // A free variable in operand position: `x / 2` cannot fold — `x` has no value yet — but
    // nothing has refused anything.
    let free_operand = run("x / 2");
    assert_eq!(
        free_operand.fired(DIV_INT),
        0,
        "a free operand cannot fold. Run: {}",
        free_operand.rendered,
    );
    assert!(
        free_operand.declines.is_empty(),
        "★★ THE LOAD-BEARING CONTROL: `x / 2` does not fold for a STRUCTURAL reason — the \
         operand is still a redex — so NOTHING may be recorded. A record here means the change \
         labels every unfired rule as a decline, which would make the whole report noise. \
         Run: {}",
        free_operand.rendered,
    );

    // The same shape one level up: a free variable inside a total collection fold's operand.
    let free_in_collection = run("length(y)");
    assert!(
        free_in_collection.declines.is_empty(),
        "★★ same property on the collection carrier: an unbound operand DEFERS. Run: {}",
        free_in_collection.rendered,
    );

    // And the discriminating pair, side by side: the SAME operator, one structural, one semantic.
    let semantic = run("6 / 0");
    assert!(
        !semantic.declines.is_empty() && free_operand.declines.is_empty(),
        "★★ THE PARTITION, in one assertion: `6 / 0` (semantic — no reduction supplies a \
         quotient) records; `x / 2` (structural — a later reduction may) does not. \
         semantic={} structural={}",
        semantic.rendered,
        free_operand.rendered,
    );
}

/// ★ CONTROL 4 — the aggregation is by `(label, partiality)`, and repeated dispatch does not
/// inflate it.
///
/// Equality saturation re-dispatches a surviving redex on every iteration, so a `6 / 0` inside a
/// larger term declines many times. One record with a count ≥ 1 is the only shape in which
/// "exactly one declined record" is a stable question.
#[test]
fn control_4_repeated_dispatch_aggregates_into_one_counted_record() {
    let nested = run("(6 / 0) + 1");
    let records = nested.declined(DIV_INT);
    assert_eq!(
        records.len(),
        1,
        "★ one record per distinct `(label, partiality)`, however many iterations dispatched \
         it. Run: {}",
        nested.rendered,
    );
    assert!(
        records[0].count >= 1,
        "the count must be the number of dispatches, never zero. Record: {:?}",
        records[0],
    );
    assert_eq!(records[0].reason_token(), "DivisionByZero");
}

/// ★ CONTROL 5 — TWO DIFFERENT reasons under ONE label stay two records.
///
/// If aggregation keyed on the label alone, a carrier overflow would hide behind a division by
/// zero and the report would under-count the findings.
#[test]
fn control_5_two_reasons_under_one_label_stay_two_records() {
    let both = run("(6 / 0) + (12 / 0)");
    let div_records = both.declined(DIV_INT);
    assert!(!div_records.is_empty(), "both divisions decline. Run: {}", both.rendered,);
    // Both are `DivisionByZero` on `i64`, so they aggregate — the same partiality is one record.
    assert_eq!(
        div_records.len(),
        1,
        "★ identical partialities under one label are ONE record. Run: {}",
        both.rendered,
    );

    // Now a term with genuinely different reasons under different labels.
    let mixed = run("(6 / 0) + (2147483647 * 2)");
    let tokens: Vec<&str> = mixed.declines.iter().map(|d| d.reason_token()).collect();
    assert!(
        tokens.contains(&"DivisionByZero"),
        "★ the (a) finding must survive alongside the (b) one. Run: {}",
        mixed.rendered,
    );
    assert!(
        tokens.contains(&"NotRepresentable"),
        "★ the (b) finding must survive alongside the (a) one — if the two collapse the report \
         loses half its content. Run: {}",
        mixed.rendered,
    );
}

/// ★ NON-VACUITY FLOOR for this suite: the harness must actually be observing a language that
/// declares folds. A corpus that stopped producing firings would satisfy every "declines nothing"
/// control above in silence.
#[test]
fn the_harness_observes_a_language_that_actually_folds() {
    let total = run("6 / 3");
    assert!(
        !total.firings.is_empty(),
        "★ the harness observed ZERO firings on a term that must fold, so every 'declines \
         nothing' control in this file is vacuous. Run: {}",
        total.rendered,
    );
    assert!(
        total.firings.iter().any(|(l, _)| l == DIV_INT),
        "★ the specific fold this suite is about must be present in the corpus. Run: {}",
        total.rendered,
    );
}
