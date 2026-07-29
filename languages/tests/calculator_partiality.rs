//! ★★ #100 — A PARTIAL COLLECTION OPERATION LEAVES A STUCK TERM, EXACTLY AS `6 / 0` DOES.
//!
//! # The asymmetry this suite pins
//!
//! Calculator declares two families of partial operation and, until this suite, treated them
//! differently *inside one generated function*:
//!
//! | family | example | before #100 | after #100 |
//! |---|---|---|---|
//! | numeric | `6 / 0` | `safe_div → None` → the fold DEFERS, the redex is left unreduced, the report stays `Complete` | unchanged |
//! | collection | `at(list(1, 2), 5)` | `.expect("ElemList: invalid index")` → **panic inside the engine closure** | the fold DEFERS, identically |
//!
//! # The root, and why the `.expect()` was not merely a style choice
//!
//! `macros/src/gen/runtime/dovetail_report/typed_report.rs` chose the body's treatment with a
//! three-way gate. A fold whose parameters are all native scalars *and* whose output is a native
//! scalar (`is_pure_native_arith`) had its body rewritten by
//! `macros/src/gen/native/rust_code_rewrite::safeify_and_wrap` — which turns `a / b` into
//! `SafeArith::safe_div(a, b)?` **and `.expect(msg)` into `(recv)?`**. Everything else fell to a
//! syntactic detector, `body_returns_option`, and then to a raw splice.
//!
//! ★ That is a CIRCULARITY, and it is the root. `body_returns_option`'s own documentation said a
//! body that `.expect()`s an inner `Option` "is NOT an `Option` at the outermost position" — so
//! the author's `.expect()` both **created** the panic and **hid the body** from the only
//! detector that would have deferred it. The machinery that already knew how to demote
//! `.expect()` to `?` was never reached, because `safeify_and_wrap` was invoked only behind
//! `is_pure_native_arith`, which a collection parameter or a collection output makes `false` **by
//! construction**.
//!
//! The repair is at the gate: EVERY fold body is routed through `safeify_and_wrap`; only the
//! OPERAND BINDING (`try_eval()` versus `&Cat`) stays gated on `is_pure_native_arith`, because
//! only that half is about parameter categories. `safeify` is a syntactic rewrite over
//! `syn::Expr` and does not care what category a parameter has.
//!
//! # ⚠ How this suite manifested BEFORE the repair — recorded in prose, never as an expectation
//!
//! MEASURED at `0808b258` (the commit before the repair), by running this exact file against
//! the then-current generator:
//!
//! ```text
//!   running 4 tests
//!   test a_total_collection_fold_on_the_same_carrier_still_fires ... ok
//!   test division_by_zero_defers_exactly_as_it_did_before ... ok
//!   test out_of_range_index_leaves_a_stuck_term_the_way_division_by_zero_does ...
//!   thread '…' panicked at target/generated/calculator/dovetail_report.rs:27108:30:
//!   ElemList: invalid index
//!   FAILED
//!   test the_sibling_partial_collection_folds_defer_too ...
//!   thread '…' panicked at target/generated/calculator/dovetail_report.rs:27149:30:
//!   DeleteList: invalid index
//!   FAILED
//!
//!   test result: FAILED. 2 passed; 2 failed
//! ```
//!
//! ★ The failure names the GENERATED line, which is the whole evidential point: the panic is
//! not in this suite and not in the language definition's own reasoning — it is in the code the
//! macro emitted from a body that said `.expect(…)`. Both controls were already green, so the
//! two failures are attributable to the collection lane alone.
//!
//! ⚠ The two lanes matter for how far this generalises. Under `cargo test` the panic unwinds
//! into the harness and is reported. In hosts that do NOT have a per-test unwind boundary — the
//! REPL, `simulate_*`, the Rho runtime, and any nextest run that trips the double-panic path —
//! the same `panic!` inside the saturation closure takes the process down with no assertion
//! message at all. The observable severity depends on the caller; the defect does not.
//!
//! This is why the cells below assert the POST-repair stuck-term property rather than being
//! written as `#[should_panic]` or wrapped in `catch_unwind`. A panic expectation would have
//! *encoded* the defect as the specification, and both constructs are banned outright by
//! `dovetail/tests/panic_expectation_gate.rs`, whose whole subject is that a test expecting a
//! panic is a test that has accepted the panic.
//!
//! # The controls
//!
//! Every cell here carries a control that must NOT move across the repair:
//!
//! * `at(list(1, 2), 1)` — an IN-RANGE index — must still fire `Calculator::fold::Proc_ElemList` and
//!   still reduce to `2`. A repair that defers the in-range case too turns this red.
//! * `6 / 0` — already deferred through `safeify`, so it pins that this suite measures the
//!   COLLECTION lane and not the arithmetic one.
//! * `length(list(1, 2))` — a TOTAL collection fold on the same collection carrier — must still fire.
//!   Without it, "the collection fold did not fire" cannot be told apart from "collection folds
//!   stopped firing".
#![cfg(all(feature = "calculator", feature = "dovetail-codegen"))]

use mettail_languages::calculator::CalculatorLanguage;
use mettail_runtime::Language;

/// Bounded on purpose: a budget means a non-converging saturation surfaces as a limit error,
/// never as a hung test binary. Same values the sibling fold suites use
/// (`languages/tests/collection_fold_carriers.rs`).
const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 200_000;

/// Saturate `src` and return `(per-label firing COUNTS, a rendering of the whole report)`.
///
/// ⚠ COUNTS, not label occurrences: `RuntimeDovetailRuleFiring` is AGGREGATED evidence — one
/// record per distinct label carrying a `count`. The rendering travels into every assertion
/// message so a failure names the whole report rather than the one thing that was asked about.
fn firings(src: &str) -> (Vec<(String, usize)>, String) {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let report = CalculatorLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_report_for({src:?}) returned Err: {e}"));
    let counted: Vec<(String, usize)> = report
        .rule_firings
        .iter()
        .filter_map(|f| f.label.clone().map(|l| (l, f.count)))
        .collect();
    let rendered = format!(
        "src={src:?} complete={} roots={} firings={:?}",
        report.is_complete(),
        report.roots.len(),
        report.rule_firings,
    );
    (counted, rendered)
}

/// How many times `label` fired while saturating `src`.
fn fired(counted: &[(String, usize)], label: &str) -> usize {
    counted
        .iter()
        .filter(|(l, _)| l == label)
        .map(|(_, n)| *n)
        .sum()
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

/// The exact label the `ElemList` fold publishes: `<Language>::fold::<Category>_<Label>`
/// (`macros/.../typed_report.rs`'s `collect_fold_rules`). Pinned as a token, because "the report
/// is non-empty" would pass on any firing at all — including the one that panics.
const ELEM_LIST: &str = "Calculator::fold::Proc_ElemList";
/// The `length` fold — a TOTAL operation on the same `List` carrier.
const LEN_LIST: &str = "Calculator::fold::Int_LenList";
/// The `/` fold on `Int` — the arithmetic lane's partial operation.
const DIV_INT: &str = "Calculator::fold::Int_DivInt";

// ═══════════════════════════════════════════════════════════════════════════════
// THE CELL
// ═══════════════════════════════════════════════════════════════════════════════

/// ★★ An out-of-range index DEFERS. The redex is left unreduced; nothing panics.
///
/// The assertion is pinned to the exact firing label, not to "the report is non-empty": before
/// the repair the fold *did* fire — it fired and then aborted the process from inside the engine
/// closure — so a non-emptiness assertion is satisfied by the defect.
#[test]
fn out_of_range_index_leaves_a_stuck_term_the_way_division_by_zero_does() {
    // ── CONTROL (must NOT discriminate): the IN-RANGE index still folds. ───────────────
    let (in_range, in_range_report) = firings("at(list(1, 2), 1)");
    assert_eq!(
        fired(&in_range, ELEM_LIST),
        1,
        "★ THE CONTROL: an in-range index must still fire `{ELEM_LIST}` exactly once. If this \
         is 0 the repair deferred the TOTAL case as well, which is over-broad — the property \
         being fixed is partiality, not indexing. Report: {in_range_report}",
    );
    assert_eq!(
        normal_form("at(list(1, 2), 1)"),
        "2",
        "★ THE CONTROL: `at(list(1, 2), 1)` is `2` — the fold must still COMPUTE, not merely fire",
    );

    // ── THE MUTATION'S SIGNATURE: the out-of-range index does NOT fold. ────────────────
    let (out_of_range, out_of_range_report) = firings("at(list(1, 2), 5)");
    assert_eq!(
        fired(&out_of_range, ELEM_LIST),
        0,
        "★ `at(list(1, 2), 5)` must NOT fire `{ELEM_LIST}`: index 5 is not in a 2-element list, so \
         the fold body's `a.get(idx)` is `None` and the dispatcher must return `None` — the \
         same shape `safe_div` gives `6 / 0`. A firing here means the body was spliced RAW \
         and the `.expect(\"ElemList: invalid index\")` is live. Report: {out_of_range_report}",
    );

    // ── AND THE TERM IS STUCK, not fabricated into something. ─────────────────────────
    assert_eq!(
        normal_form("at(list(1, 2), 5)"),
        parsed_form("at(list(1, 2), 5)"),
        "★ a declined fold leaves its REDEX unreduced — the normal form of an out-of-range \
         index is the index expression itself, byte-for-byte the term that was parsed. A \
         different rendering means the engine invented a value for an operation that has none.",
    );
}

/// ★ A TOTAL fold on the same carrier keeps firing.
///
/// Without this, "the collection fold did not fire" and "collection folds stopped firing" are
/// the same observation. `length` takes the identical `BindKind::Collection` binding as `at`,
/// so it moves if and only if the repair broke the carrier rather than the partiality.
#[test]
fn a_total_collection_fold_on_the_same_carrier_still_fires() {
    let (counted, report) = firings("length(list(1, 2))");
    assert_eq!(
        fired(&counted, LEN_LIST),
        1,
        "`length(list(1, 2))` is TOTAL and must fold. Report: {report}",
    );
    assert_eq!(normal_form("length(list(1, 2))"), "2", "`length(list(1, 2))` is `2`");
}

/// ★ THE SECOND CONTROL: the ARITHMETIC lane is unchanged.
///
/// `6 / 0` already went through `safeify_and_wrap` before the repair (`DivInt` is
/// `is_pure_native_arith`), so it pins that the cell above measures the COLLECTION lane. If this
/// moves, the repair changed the lane that was already correct.
#[test]
fn division_by_zero_defers_exactly_as_it_did_before() {
    let (counted, report) = firings("6 / 0");
    assert_eq!(
        fired(&counted, DIV_INT),
        0,
        "`6 / 0` must not fire `{DIV_INT}` — `safe_div` declines and the fold defers. \
         Report: {report}",
    );
    assert_eq!(
        normal_form("6 / 0"),
        parsed_form("6 / 0"),
        "the division-by-zero redex stays unreduced",
    );

    // The positive half of the same lane: a DEFINED division still folds.
    let (defined, defined_report) = firings("6 / 3");
    assert_eq!(
        fired(&defined, DIV_INT),
        1,
        "`6 / 3` must still fire `{DIV_INT}`. Report: {defined_report}",
    );
    assert_eq!(normal_form("6 / 3"), "2", "`6 / 3` is `2`");
}

/// ★ The two SIBLING partial collection folds — `delete` past the end and `get` on a missing key.
///
/// #100's site inventory is four; three of them are Calculator's, and a repair that closed only
/// the one with a test would leave the class open. Each carries its DEFINED counterpart on the
/// same line of reasoning as the controls above.
#[test]
fn the_sibling_partial_collection_folds_defer_too() {
    const DELETE_LIST: &str = "Calculator::fold::List_DeleteList";
    const GET_MAP: &str = "Calculator::fold::Proc_GetMap";

    let (past_end, past_end_report) = firings("delete(list(1, 2), 5)");
    assert_eq!(
        fired(&past_end, DELETE_LIST),
        0,
        "`delete(list(1, 2), 5)` must NOT fire `{DELETE_LIST}`. Report: {past_end_report}",
    );
    // CONTROL on the same fold: an in-range delete still folds.
    let (in_range, in_range_report) = firings("delete(list(1, 2), 0)");
    assert_eq!(
        fired(&in_range, DELETE_LIST),
        1,
        "★ THE CONTROL: `delete(list(1, 2), 0)` is in range and must still fire `{DELETE_LIST}`. \
         Report: {in_range_report}",
    );

    let (missing, missing_report) = firings("get(map(1 : 2), 3)");
    assert_eq!(
        fired(&missing, GET_MAP),
        0,
        "`get(map(1 : 2), 3)` must NOT fire `{GET_MAP}`: key `3` is absent from \
         `map(1 : 2)`, so the body's `m.get(&k)` is `None`. Report: {missing_report}",
    );
    // CONTROL on the same fold: a present key still folds.
    let (present, present_report) = firings("get(map(1 : 2), 1)");
    assert_eq!(
        fired(&present, GET_MAP),
        1,
        "★ THE CONTROL: `get(map(1 : 2), 1)` names a key that IS present and must still fire \
         `{GET_MAP}`. Report: {present_report}",
    );
}
