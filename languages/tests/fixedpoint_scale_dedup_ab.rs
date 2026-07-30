//! Does the Dovetail e-graph's hashcons collapse two `Eq`-equal fixed-point literals that
//! differ in `places`, and does a scale-reading operator then observe the SURVIVOR?
//!
//! # The exposure
//!
//! `mettail_runtime::CanonicalFixedPoint` keys `PartialEq` (`runtime/src/canonical_fixed_point.rs:139`),
//! `Ord` (`:153`) and `Hash` (`:159`) on `value_ratio()` — the reduced rational
//! `unscaled / 10^places`. So `7.00p2` and `7.0p1` are `Eq`-equal and hash identically: both are
//! the rational `7/1`. But `align_pair` (`:93`) reads `places` directly, and its three callers
//! — `checked_div` (`:104`), `checked_rem` (`:115`), `bitwise_aligned` (`:128`) — plus the
//! `Add` (`:231`) and `Sub` (`:239`) operator impls therefore distinguish them:
//!
//! ```text
//!   7.00p2 / 3.00p2 = 2.33p2 = 233/100
//!   7.0p1  / 3.0p1  = 2.3p1  =  23/10
//! ```
//!
//! `233/100 != 23/10`, so `/` is NOT a function on this type's own `Eq` classes.
//!
//! # The mechanism (named, not assumed)
//!
//! The dedup is the e-graph hashcons at **`dovetail/src/egraph.rs:188`**:
//!
//! ```text
//!   memo: HashMap<ENode<L>, EClassId>
//! ```
//!
//! `ENode<L>` derives `PartialEq, Eq, Hash` (`dovetail/src/egraph.rs:32-36`), so the key is
//! `L`'s own `Eq`/`Hash`. `EGraph::add` (`:292-295`) returns the EXISTING class on a memo hit
//! and never inserts the incoming node — the class keeps only the FIRST-INSERTED one.
//!
//! On the live typed-fold path `L = <Lang>DovetailOp`, emitted at
//! `macros/src/gen/runtime/dovetail_report/op_enum.rs:586` with
//! `#[derive(Clone, PartialEq, Eq, Hash)]` and the leaf variant
//! `Fixed_FixedLit(CanonicalFixedPoint)`. So the hashcons key for a fixed-point literal leaf IS
//! `CanonicalFixedPoint::{eq,hash}` — i.e. `value_ratio()`, which ignores `places`.
//!
//! ⚠ NOTE for the reader: this is NOT `SemanticHash`. `to_canonical_bytes`'s doc comment
//! (`runtime/src/canonical_fixed_point.rs:63-70`) attributes the dedup to a
//! "`SemanticHash`<->`Eq` agreement that the Dovetail e-graph relies on to dedup", but
//! `dovetail/src/egraph.rs` says of `content_key` explicitly that it "does NOT participate in
//! hashcons identity". The content key is used for AC keys, extraction and reporting; the
//! hashcons is the derive. The doc's conclusion is right for the wrong reason.
//!
//! # Why the operator sees the survivor
//!
//! The generated fold body reads its operands out of the e-CLASS, not out of the source term
//! (`target/generated/calculator/dovetail_report.rs`, `Fixed_DivFixed`):
//!
//! ```text
//!   let __cls_a = *__subst.get("a")?;
//!   let mut __ex = Extractor::new(&*__eg, __weigh);
//!   __ex.kth(__eg.find(__cls_a), 0).value?
//! ```
//!
//! So whichever `places` survives the hashcons is the `places` that reaches `align_pair`.
#![cfg(all(feature = "calculator", feature = "dovetail-codegen"))]

use dovetail::egraph::{EGraph, ENode};
use mettail_languages::calculator::{CalculatorDovetailOp as Op, CalculatorLanguage};
use mettail_runtime::{parse_fixed_lit, CanonicalFixedPoint, Language};

/// Bounded on purpose: a budget means a non-converging saturation surfaces as a limit error,
/// never as a hung test binary. Same values the sibling calculator fold suites use.
const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 200_000;

fn fixed(src: &str) -> CanonicalFixedPoint {
    parse_fixed_lit(src).unwrap_or_else(|()| panic!("parse_fixed_lit({src:?}) failed"))
}

fn leaf(src: &str) -> ENode<Op> {
    ENode::leaf(Op::Fixed_FixedLit(fixed(src)))
}

/// The `places` of the single surviving `Fixed_FixedLit` node of `class`, plus the class's
/// node count — the direct read of "which representative survived".
fn survivor(eg: &EGraph<Op>, class: dovetail::egraph::EClassId) -> (usize, Vec<u32>) {
    let nodes = eg.nodes(eg.find(class));
    let places: Vec<u32> = nodes
        .iter()
        .filter_map(|n| match &n.op {
            Op::Fixed_FixedLit(v) => Some(v.places()),
            _ => None,
        })
        .collect();
    (nodes.len(), places)
}

// ─────────────────────────────────────────────────────────────────────────────
// PROBE A — the mechanism, read directly off `EGraph<CalculatorDovetailOp>`.
// ─────────────────────────────────────────────────────────────────────────────

/// Control (a): dedup happens AT ALL for fixed-point literal leaves.
///
/// ⚠ Without this a null A/B result is uninformative — "no dedup anywhere" and "dedup that
/// does not reach the operator" are indistinguishable.
#[test]
fn control_a_positive_same_scale_literals_dedup() {
    let mut eg = EGraph::<Op>::new();
    let c1 = eg.add(leaf("7.00p2"));
    let c2 = eg.add(leaf("7.00p2"));
    assert_eq!(eg.find(c1), eg.find(c2), "same-scale twins must land in one class");
    assert_eq!(eg.class_count(), 1, "one class");
    assert_eq!(eg.node_count(), 1, "one live e-node — the hashcons refused the second insert");
}

/// Control (b): the instrument is not merely responding to "one more term".
#[test]
fn control_b_negative_different_value_does_not_dedup() {
    let mut eg = EGraph::<Op>::new();
    let c1 = eg.add(leaf("7.00p2"));
    let c2 = eg.add(leaf("5.0p1"));
    assert_ne!(eg.find(c1), eg.find(c2), "5 != 7 — distinct classes");
    assert_eq!(eg.class_count(), 2, "two classes");
    assert_eq!(eg.node_count(), 2, "two live e-nodes");
}

/// H, mechanism level: `Eq`-equal / different-`places` literals share ONE class, and the class
/// keeps exactly ONE node — so `places` does NOT survive alongside. This distinguishes
/// attribution case (2) ("dedup happens but `places` survives") from case (1)/witnessed.
#[test]
fn different_places_literals_share_one_class_with_one_surviving_node() {
    let mut eg = EGraph::<Op>::new();
    let c1 = eg.add(leaf("7.00p2"));
    let c2 = eg.add(leaf("7.0p1"));

    assert_eq!(
        eg.find(c1),
        eg.find(c2),
        "7.00p2 and 7.0p1 are Eq-equal (both 7/1) so the hashcons at \
         dovetail/src/egraph.rs:292 must return the same class"
    );
    assert_eq!(eg.class_count(), 1, "ONE class, not two");

    let (n_nodes, places) = survivor(&eg, c1);
    assert_eq!(
        n_nodes, 1,
        "the class keeps exactly ONE node — `places` does NOT survive as a second e-node \
         (this rules out attribution case (2): scale living outside the deduped key)"
    );
    assert_eq!(
        places,
        vec![2],
        "the FIRST-INSERTED representative survives: places=2 from 7.00p2"
    );
}

/// ★ The survivor is chosen by INSERTION ORDER. Swapping the order swaps the `places` that any
/// downstream `align_pair` will read. This is the order-dependence class of finding.
#[test]
fn surviving_places_is_determined_by_insertion_order() {
    let mut a = EGraph::<Op>::new();
    let ca = a.add(leaf("7.00p2"));
    a.add(leaf("7.0p1"));

    let mut b = EGraph::<Op>::new();
    let cb = b.add(leaf("7.0p1"));
    b.add(leaf("7.00p2"));

    let (_, places_a) = survivor(&a, ca);
    let (_, places_b) = survivor(&b, cb);
    assert_eq!(places_a, vec![2], "p2-first => p2 survives");
    assert_eq!(places_b, vec![1], "p1-first => p1 survives");
    assert_ne!(
        places_a, places_b,
        "the surviving scale depends on TEXTUAL/INSERTION ORDER, not on the value"
    );
}

/// The consequence, arithmetically: the two survivors give DIFFERENT quotients, so the
/// order-dependent survivor is an order-dependent ANSWER.
#[test]
fn the_two_survivors_compute_different_quotients() {
    let p2 = fixed("7.00p2").checked_div(fixed("3.00p2")).expect("nonzero divisor");
    let p1 = fixed("7.0p1").checked_div(fixed("3.0p1")).expect("nonzero divisor");
    assert_eq!(format!("{p2}"), "2.33p2");
    assert_eq!(format!("{p1}"), "2.3p1");
    assert_ne!(p2, p1, "233/100 != 23/10 — a genuine value difference, not a rendering one");
}

// ─────────────────────────────────────────────────────────────────────────────
// PROBE B — the end-to-end A/B through the production `dovetail_normal_term`.
//
// Carrier: `(x - x) - (y - y)` is rationally `0p0`, and `0p0 + q` re-aligns to `q.places`, so
// the observable is EXACTLY the quotient. The carrier's only job is to put `x`/`y` literal
// leaves into the e-graph BEFORE the divide's operands are lowered.
// ─────────────────────────────────────────────────────────────────────────────

fn normal_form(src: &str) -> Result<String, String> {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let term = lang.parse_term(src).map_err(|e| format!("parse error: {e}"))?;
    let normal = CalculatorLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .map_err(|e| format!("dovetail_normal_term error: {e}"))?;
    Ok(format!("{normal}"))
}

/// P0 — the baseline. No sibling literal at all.
const P0: &str = "7.00p2 / 3.00p2";
/// P0' — size-matched control: siblings present but SAME scale. Isolates "one more term".
const P0_SAME_SCALE: &str =
    "((7.00p2 - 7.00p2) - (3.00p2 - 3.00p2)) + (7.00p2 / 3.00p2)";
/// P1 — the A/B: siblings of EQUAL VALUE but LOWER SCALE, lowered first.
const P1_LOWER_SCALE_FIRST: &str = "((7.0p1 - 7.0p1) - (3.0p1 - 3.0p1)) + (7.00p2 / 3.00p2)";
/// P2 — order control: the same siblings, but AFTER the divide.
const P2_LOWER_SCALE_LAST: &str = "(7.00p2 / 3.00p2) + ((7.0p1 - 7.0p1) - (3.0p1 - 3.0p1))";
/// P3 — negative control: siblings of a DIFFERENT value. Must not move the answer.
const P3_DIFFERENT_VALUE: &str = "((5.0p1 - 5.0p1) - (2.0p1 - 2.0p1)) + (7.00p2 / 3.00p2)";

/// Diagnostic: print every program's normal form (or its error) in ONE run, so the A/B table
/// can be read off a single output rather than reconstructed from five failures.
#[test]
fn ab_table_diagnostic() {
    let rows = [
        ("P0  baseline           ", P0),
        ("P0' same-scale sibling ", P0_SAME_SCALE),
        ("P1  lower-scale FIRST  ", P1_LOWER_SCALE_FIRST),
        ("P2  lower-scale LAST   ", P2_LOWER_SCALE_LAST),
        ("P3  different value    ", P3_DIFFERENT_VALUE),
    ];
    let mut report = String::new();
    for (name, src) in rows {
        let outcome = match normal_form(src) {
            Ok(nf) => nf,
            Err(e) => format!("<{e}>"),
        };
        report.push_str(&format!("{name} {src:<62} => {outcome}\n"));
    }
    eprintln!("\n=== fixed-point scale dedup A/B ===\n{report}");
    assert!(
        normal_form(P0).is_ok(),
        "the BASELINE must at least evaluate, else the instrument is broken:\n{report}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// THE GATE. ⚠⚠ These two tests PIN A DEFECT. They are GREEN because the product is
// WRONG, and they exist so it cannot silently change in either direction.
//
// The RED form of this gate — the invariant that SHOULD hold — was run first and is
// preserved verbatim in `must_hold_after_the_root_fix` below, commented out rather
// than deleted. Its observed failure was:
//
//     thread 'red_demo_answer_must_not_depend_on_equal_value_sibling' panicked at
//     languages/tests/fixedpoint_scale_dedup_ab.rs:242:5:
//     assertion `left == right` failed: adding an equal-value, different-scale sibling
//     literal changed the quotient
//       left: "2.33p2"
//      right: "2.3p1"
//
//     thread 'red_demo_answer_must_not_depend_on_textual_order' panicked at
//     languages/tests/fixedpoint_scale_dedup_ab.rs:253:5:
//     assertion `left == right` failed: reordering two summands changed the quotient
//       left: "2.3p1"
//      right: "2.33p2"
//
// This gate depends on NO product change: nothing outside this test file was touched, so
// deleting this file is the only way to "revert" it, and the assertions read only the
// production `dovetail_normal_term` path.
// ─────────────────────────────────────────────────────────────────────────────

/// ⚠ DEFECT WITNESS — an equal-value, different-scale SIBLING literal changes the quotient.
///
/// When the root cause is fixed, this test MUST be deleted and replaced by
/// `must_hold_after_the_root_fix` (commented out below). Do NOT "repair" it by updating the
/// expected strings: the whole point is that P0 and P1 must eventually agree.
#[test]
fn witness_equal_value_sibling_changes_the_quotient() {
    let p0 = normal_form(P0).expect("P0 must evaluate");
    let p1 = normal_form(P1_LOWER_SCALE_FIRST).expect("P1 must evaluate");
    let p0_same = normal_form(P0_SAME_SCALE).expect("P0' must evaluate");
    let p3 = normal_form(P3_DIFFERENT_VALUE).expect("P3 must evaluate");

    assert_eq!(p0, "2.33p2", "baseline 7/3 truncated at scale 2");
    assert_eq!(
        p0_same, "2.33p2",
        "control (a-size): a SAME-scale sibling must not move the answer — so the effect below \
         is not merely 'one more term in the program'"
    );
    assert_eq!(
        p3, "2.33p2",
        "control (b-negative): a DIFFERENT-VALUE sibling (5.0p1/2.0p1) must not move the answer \
         — so the instrument responds to the Eq-collision specifically, not to program size"
    );
    assert_eq!(
        p1, "2.3p1",
        "⚠ WITNESS: an equal-value LOWER-SCALE sibling (7.0p1/3.0p1) seeds the hashcons first \
         (dovetail/src/egraph.rs:292), so the divide's operands resolve to the p1 survivors and \
         align_pair (runtime/src/canonical_fixed_point.rs:93) truncates one digit shallower"
    );
    assert_ne!(
        p0, p1,
        "⚠ 233/100 != 23/10 — a genuine VALUE difference, not a rendering difference"
    );
}

/// ⚠ DEFECT WITNESS — and it is ORDER-DEPENDENT: the same two summands, swapped, disagree.
///
/// This is the stronger and worse form. Which representative survives the hashcons is decided
/// by insertion order, and insertion order follows the source text, so fixed-point division in
/// this lane is not order-invariant.
#[test]
fn witness_the_quotient_depends_on_textual_order() {
    let p1 = normal_form(P1_LOWER_SCALE_FIRST).expect("P1 must evaluate");
    let p2 = normal_form(P2_LOWER_SCALE_LAST).expect("P2 must evaluate");
    assert_eq!(p1, "2.3p1", "siblings FIRST => the p1 representative survives");
    assert_eq!(p2, "2.33p2", "siblings LAST => the p2 representative survives");
    assert_ne!(
        p1, p2,
        "⚠ WITNESS: P1 and P2 differ ONLY in the order of two summands of `+`, yet the quotient \
         differs. Fixed-point `/` is not invariant under reordering of unrelated siblings."
    );
}

// The invariant that MUST hold once the root cause is fixed. Commented out rather than
// deleted (it is RED today — its verbatim failure is quoted in the banner above), so that the
// correct assertion is already written and reviewed when the fix lands. It is NOT `#[ignore]`d:
// an ignored test reads as "flaky", whereas this is "known-wrong product, assertion pre-staged".
//
// #[test]
// fn must_hold_after_the_root_fix() {
//     // A scale-reading operator's answer must not depend on whether an EQUAL-VALUE sibling
//     // literal of a different scale happens to appear elsewhere in the program...
//     assert_eq!(normal_form(P0).expect("P0"), normal_form(P1_LOWER_SCALE_FIRST).expect("P1"));
//     // ...nor on the textual ORDER in which it appears.
//     assert_eq!(
//         normal_form(P1_LOWER_SCALE_FIRST).expect("P1"),
//         normal_form(P2_LOWER_SCALE_LAST).expect("P2"),
//     );
// }

/// Sibling enumeration, measured not asserted-by-hand: WHICH scale-reading operations change
/// their VALUE (not merely their rendering) when the surviving representative flips scale?
///
/// `align_pair` (`runtime/src/canonical_fixed_point.rs:93`) has FOUR callers — `checked_div`
/// (`:104`), `checked_rem` (`:197`), `Add::add` (`:312`), `Sub::sub` (`:320`) — and
/// `bitwise_aligned` (`:205`) has THREE (`BitAnd` `:360`, `BitOr` `:367`, `BitXor` `:374`).
/// `Mul::mul` (`:329`) and `Neg::neg` (`:353`) read `places` without either helper. NINE
/// scale-reading operations in total.
///
/// ⚠ This table is REVISION-SENSITIVE, so it is printed rather than hard-coded. Measured
/// before/after `afcc9e8f` ("`%` is the remainder on the unscaled integers, per upstream"):
/// `checked_rem` moved from VALUE-CHANGING (`0.01p2` vs `0.1p1`) to RENDERING-ONLY (`1.00p2`
/// vs `1.0p1`) — i.e. that fix independently closed one of the value-changing exposures.
/// At `afcc9e8f` the split is VALUE-CHANGING 4 / RENDERING-ONLY 5.
#[test]
fn sibling_enumeration_which_ops_change_value_on_scale_flip() {
    let a2 = fixed("7.00p2");
    let b2 = fixed("3.00p2");
    let a1 = fixed("7.0p1");
    let b1 = fixed("3.0p1");
    assert_eq!(a2, a1, "premise: the two spellings are Eq-equal");
    assert_eq!(b2, b1, "premise: the two spellings are Eq-equal");

    let rows: Vec<(&str, CanonicalFixedPoint, CanonicalFixedPoint)> = vec![
        ("checked_div  (align_pair)", a2.checked_div(b2).expect("div"), a1.checked_div(b1).expect("div")),
        ("checked_rem  (align_pair)", a2.checked_rem(b2).expect("rem"), a1.checked_rem(b1).expect("rem")),
        ("Add          (align_pair)", a2 + b2, a1 + b1),
        ("Sub          (align_pair)", a2 - b2, a1 - b1),
        ("Mul          (places sum)", a2 * b2, a1 * b1),
        ("BitAnd  (bitwise_aligned)", a2 & b2, a1 & b1),
        ("BitOr   (bitwise_aligned)", a2 | b2, a1 | b1),
        ("BitXor  (bitwise_aligned)", a2 ^ b2, a1 ^ b1),
        ("Neg          (places kept)", -a2, -a1),
    ];
    let mut value_changing = Vec::new();
    let mut render_only = Vec::new();
    let mut report = String::new();
    for (name, at_p2, at_p1) in &rows {
        let differs = at_p2 != at_p1;
        report.push_str(&format!(
            "  {name}  p2-survivor={:<10} p1-survivor={:<10} VALUE-DIFFERS={differs}\n",
            format!("{at_p2}"),
            format!("{at_p1}")
        ));
        if differs {
            value_changing.push(*name);
        } else if format!("{at_p2}") != format!("{at_p1}") {
            render_only.push(*name);
        }
    }
    eprintln!(
        "\n=== scale-reading operations: value-changing vs rendering-only ===\n{report}\n\
         VALUE-CHANGING ({}): {value_changing:?}\n\
         RENDERING-ONLY ({}): {render_only:?}\n",
        value_changing.len(),
        render_only.len()
    );
}
