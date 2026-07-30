//! Does the Dovetail e-graph's hashcons collapse two fixed-point literals that differ in
//! `places`, and does a scale-reading operator then observe the SURVIVOR?
//!
//! ★★ **It did until 2026-07-30. Work item #200 closed it, and this file is now the gate that
//! keeps it closed.** Every test below was written against the defect; the ones that read the
//! mechanism have been INVERTED, the two that pinned the wrong answers have been retired into
//! [`the_answer_must_not_depend_on_an_equal_value_sibling`]'s doc, and the invariant that was
//! pre-staged commented-out is now LIVE.
//!
//! # The exposure, as it was
//!
//! `mettail_runtime::CanonicalFixedPoint` used to key `PartialEq`, `Ord` and `Hash` on
//! `value_ratio()` — the reduced rational `unscaled / 10^places`. So `7.00p2` and `7.0p1` were
//! `Eq`-equal and hashed identically: both are the rational `7/1`. But `align_pair`
//! (`runtime/src/canonical_fixed_point.rs:93`) reads `places` directly, and its callers —
//! `checked_div` (`:104`), `checked_rem` (`:197`), `Add::add` (`:312`), `Sub::sub` (`:320`) —
//! plus `bitwise_aligned` (`:205`, for `BitAnd` `:360` / `BitOr` `:367` / `BitXor` `:374`),
//! `Mul::mul` (`:329`) and `Neg::neg` (`:353`) all distinguish them:
//!
//! ```text
//!   7.00p2 / 3.00p2 = 2.33p2 = 233/100
//!   7.0p1  / 3.0p1  = 2.3p1  =  23/10
//! ```
//!
//! `233/100 != 23/10`, so `/` was not a function on this type's own `Eq` classes.
//!
//! ⚠ **Those coordinates are the SECOND set this header has carried.** The first cited `:139`,
//! `:153`, `:159`, `checked_rem :115`, `bitwise_aligned :128`, `Add :231`, `Sub :239` — every
//! one of them wrong, and wrong on the day the file was written, while the SAME file's
//! `sibling_enumeration` doc carried the correct ones. Two coordinate systems in one file. The
//! set above is re-derived at `7fad51db`; re-derive again rather than trusting it.
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
//! `CanonicalFixedPoint::{eq,hash}`.
//!
//! ⇒ **The repair is at the key, not at the e-graph.** Work item #200 moved `Eq`/`Hash`/`Ord`
//! onto the raw `(unscaled, places)` pair, so `7.00p2` and `7.0p1` no longer hash alike and the
//! memo no longer conflates them. Nothing in `dovetail` changed.
//!
//! ⚠ NOTE for the reader: this is NOT `SemanticHash`. `to_canonical_bytes`'s doc comment used
//! to attribute the dedup to a "`SemanticHash`<->`Eq` agreement that the Dovetail e-graph relies
//! on to dedup", but `dovetail/src/egraph.rs` says of `content_key` explicitly that it "does NOT
//! participate in hashcons identity". The content key is used for AC keys, extraction and
//! reporting; the hashcons is the derive. The doc's conclusion was right for the wrong reason,
//! and it has now been corrected in the product file as well as here.
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
//! So whichever `places` survives the hashcons is the `places` that reaches `align_pair` — and
//! the fix is that nothing is eliminated, so what survives is what was written.
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

/// ★★ INVERTED 2026-07-30 (work item #200) — the mechanism-level pin that the collapse is gone.
///
/// It was `different_places_literals_share_one_class_with_one_surviving_node` and asserted, on
/// the same two leaves, `eg.find(c1) == eg.find(c2)`, `class_count() == 1`, `n_nodes == 1` and
/// `places == vec![2]`. Every one of those is now the opposite, because
/// `CanonicalFixedPoint::{eq,hash}` key on the raw `(unscaled, places)` pair, so `7.00p2` and
/// `7.0p1` are different hashcons keys.
///
/// ⚠ This test reads `EGraph<Op>` DIRECTLY. It is therefore immune to anything that changes at
/// the language/carrier level, which is exactly what makes it the load-bearing mechanism pin:
/// a carrier can go vacuous, this cannot.
#[test]
fn different_places_literals_are_distinct_e_nodes() {
    let mut eg = EGraph::<Op>::new();
    let c1 = eg.add(leaf("7.00p2"));
    let c2 = eg.add(leaf("7.0p1"));

    assert_ne!(
        eg.find(c1),
        eg.find(c2),
        "7.00p2 and 7.0p1 denote the same NUMBER but are distinct VALUES since work item #200, \
         so the hashcons at dovetail/src/egraph.rs:292 must NOT conflate them"
    );
    assert_eq!(eg.class_count(), 2, "TWO classes, not one");

    let (n1, places1) = survivor(&eg, c1);
    let (n2, places2) = survivor(&eg, c2);
    assert_eq!((n1, n2), (1, 1), "one node in each class — neither absorbed the other");
    assert_eq!(places1, vec![2], "the p2 spelling keeps places=2");
    assert_eq!(places2, vec![1], "the p1 spelling keeps places=1 — it is no longer eliminated");
}

/// ★★ INVERTED 2026-07-30 (work item #200) — the order-dependence is gone.
///
/// It was `surviving_places_is_determined_by_insertion_order` and asserted
/// `places_a == vec![2]`, `places_b == vec![1]`, `assert_ne!(places_a, places_b)` — i.e. that
/// the surviving scale followed the SOURCE TEXT. Both insertion orders now keep both
/// representatives, so the two orders agree.
#[test]
fn surviving_places_is_order_independent() {
    let mut a = EGraph::<Op>::new();
    let ca_p2 = a.add(leaf("7.00p2"));
    let ca_p1 = a.add(leaf("7.0p1"));

    let mut b = EGraph::<Op>::new();
    let cb_p1 = b.add(leaf("7.0p1"));
    let cb_p2 = b.add(leaf("7.00p2"));

    // Read each order's classes by SPELLING rather than by insertion position, which is the
    // whole point: the spelling now determines the class.
    let (_, a_p2) = survivor(&a, ca_p2);
    let (_, a_p1) = survivor(&a, ca_p1);
    let (_, b_p2) = survivor(&b, cb_p2);
    let (_, b_p1) = survivor(&b, cb_p1);

    assert_eq!(a_p2, vec![2]);
    assert_eq!(a_p1, vec![1]);
    assert_eq!(
        (a_p2, a_p1),
        (b_p2, b_p1),
        "the two insertion orders must now agree completely — the surviving scale depends on \
         the VALUE WRITTEN, never on where in the source text it appeared"
    );
    assert_eq!(a.class_count(), 2);
    assert_eq!(b.class_count(), 2, "and both orders keep both, rather than one eliminating one");
}

/// ★ RENAMED 2026-07-30 (was `the_two_survivors_compute_different_quotients`): after work item
/// #200 there is no "survivor", because neither spelling eliminates the other. What the test
/// asserts is UNCHANGED and still true — and it is still the reason the collapse mattered. If
/// the two scales computed the same quotient, conflating them would have been harmless.
#[test]
fn the_two_scales_compute_different_quotients() {
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

// ─────────────────────────────────────────────────────────────────────────────
// The SECOND carrier set (Q0–Q3), added 2026-07-30 alongside the fix.
//
// Why a second set, when P0–P3 above already witnessed the defect and now pin the repair: the
// P-carriers rely on `(x - x) - (y - y)` normalizing to `0p0` and on `0p0 + q` re-aligning to
// `q.places`. That is a MIXED-SCALE addition, so if upstream's scale-equality refusal is ever
// adopted (work item #186) every P-program becomes `error` and this gate goes VACUOUSLY GREEN —
// a passing test that measures nothing, which is the worst possible outcome for a gate.
//
// The Q-carriers use a non-zero rescale instead, so every binary operation in them has
// equal-scale operands and they survive that precondition. They are pre-positioned, not
// speculative: they are measured here today.
//
// ⚠ Both operands of the divide need an equal-value lower-scale sibling. A carrier supplying
// only ONE (say `7.0p1`, leaving `3.00p2` with no p1 twin) does NOT reproduce the defect —
// `align_pair` still lifts to `max(places) = 2` and the quotient is unchanged. MEASURED, and it
// refuted the first draft of this carrier: `fixed((7.0p1 - 4.0p1), 2) + (7.00p2 / 3.00p2)`
// answers `5.33p2` both before AND after the fix, so it discriminates nothing.
// ─────────────────────────────────────────────────────────────────────────────

/// Q0 — control: the rescale's operands are already at the divide's scale.
const Q0_SAME_SCALE: &str = "fixed((7.00p2 - 3.00p2), 2) + (7.00p2 / 3.00p2)";
/// Q1 — the A/B: BOTH divide operands get an equal-value p1 sibling, lowered FIRST.
const Q1_LOWER_SCALE_FIRST: &str = "fixed((7.0p1 - 3.0p1), 2) + (7.00p2 / 3.00p2)";
/// Q2 — order control: the same siblings, but AFTER the divide.
const Q2_LOWER_SCALE_LAST: &str = "(7.00p2 / 3.00p2) + fixed((7.0p1 - 3.0p1), 2)";
/// Q3 — negative control: siblings of DIFFERENT values (5 and 1) whose difference is the SAME
/// number as Q0's (4), so the totals are comparable while the literals cannot collide with the
/// divide's 7 and 3.
const Q3_DIFFERENT_VALUE: &str = "fixed((5.0p1 - 1.0p1), 2) + (7.00p2 / 3.00p2)";

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
        ("Q0  same-scale rescale ", Q0_SAME_SCALE),
        ("Q1  lower-scale FIRST  ", Q1_LOWER_SCALE_FIRST),
        ("Q2  lower-scale LAST   ", Q2_LOWER_SCALE_LAST),
        ("Q3  different value    ", Q3_DIFFERENT_VALUE),
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
// THE GATE. ★★ TURNED LIVE 2026-07-30 by work item #200.
//
// Until then this section held two tests that PINNED A DEFECT — they were green because the
// product was wrong — plus the correct invariant, commented out because it was red. The two
// witnesses have been retired (their assertions are quoted verbatim in the invariant's doc
// below, so nothing is lost) and the invariant is now live.
//
// This gate reads only the production `dovetail_normal_term` path.
// ─────────────────────────────────────────────────────────────────────────────

/// ★★ THE INVARIANT. A scale-reading operator's answer must not depend on whether an
/// EQUAL-VALUE, different-scale sibling literal happens to appear elsewhere in the program, nor
/// on the textual ORDER in which it appears.
///
/// This was pre-staged commented-out (it was red) with the note *"the correct assertion is
/// already written and reviewed when the fix lands"*. It lands here.
///
/// # ⚠ What it replaces — the two retired witnesses, verbatim
///
/// The defect they pinned is quoted in full rather than deleted, so a future reader can see
/// exactly what the product used to compute and cannot mistake the repair for a re-blessing.
///
/// `witness_equal_value_sibling_changes_the_quotient` asserted:
///
/// ```text
/// assert_eq!(p0,      "2.33p2", "baseline 7/3 truncated at scale 2");
/// assert_eq!(p0_same, "2.33p2", "control (a-size): a SAME-scale sibling must not move it");
/// assert_eq!(p3,      "2.33p2", "control (b-negative): a DIFFERENT-VALUE sibling …");
/// assert_eq!(p1,      "2.3p1",  "⚠ WITNESS: an equal-value LOWER-SCALE sibling (7.0p1/3.0p1)
///                                seeds the hashcons first (dovetail/src/egraph.rs:292), so the
///                                divide's operands resolve to the p1 survivors and align_pair
///                                truncates one digit shallower");
/// assert_ne!(p0, p1,            "⚠ 233/100 != 23/10 — a genuine VALUE difference");
/// ```
///
/// `witness_the_quotient_depends_on_textual_order` asserted:
///
/// ```text
/// assert_eq!(p1, "2.3p1",  "siblings FIRST => the p1 representative survives");
/// assert_eq!(p2, "2.33p2", "siblings LAST => the p2 representative survives");
/// assert_ne!(p1, p2,       "⚠ WITNESS: P1 and P2 differ ONLY in the order of two summands of
///                           `+`, yet the quotient differs. Fixed-point `/` is not invariant
///                           under reordering of unrelated siblings.");
/// ```
///
/// And the originally-observed RED failure of THIS assertion was:
///
/// ```text
/// assertion `left == right` failed: adding an equal-value, different-scale sibling literal
/// changed the quotient
///   left: "2.33p2"
///  right: "2.3p1"
/// ```
#[test]
fn the_answer_must_not_depend_on_an_equal_value_sibling() {
    let p0 = normal_form(P0).expect("P0");
    let p0_same = normal_form(P0_SAME_SCALE).expect("P0'");
    let p1 = normal_form(P1_LOWER_SCALE_FIRST).expect("P1");
    let p2 = normal_form(P2_LOWER_SCALE_LAST).expect("P2");
    let p3 = normal_form(P3_DIFFERENT_VALUE).expect("P3");

    assert_eq!(p0, "2.33p2", "the baseline is unmoved: 7/3 truncated at scale 2");
    assert_eq!(
        p1, p0,
        "★ THE FIX: an equal-value LOWER-SCALE sibling no longer changes the quotient. This \
         answered `2.3p1` before work item #200",
    );
    assert_eq!(
        p2, p1,
        "★ …nor does the ORDER in which it appears. P1 and P2 differ only in the order of two \
         summands of `+`; before the fix they answered `2.3p1` and `2.33p2`",
    );
    assert_eq!(p0_same, p0, "control (a-size): a SAME-scale sibling never moved it");
    assert_eq!(p3, p0, "control (b-negative): a DIFFERENT-VALUE sibling never moved it");
}

/// ★★ The same invariant on the Q-carriers, which have no mixed-scale operation in them and so
/// cannot go vacuous under a future scale-equality precondition (work item #186). See the
/// Q-constants' banner for why the P-carriers alone are not enough.
///
/// ⚠ Q1's pre-fix value is MEASURED, not assumed: `6.3p1`, against `6.33p2` for the other
/// three. It really did discriminate.
#[test]
fn the_answer_must_not_depend_on_an_equal_value_sibling_q_carriers() {
    let q0 = normal_form(Q0_SAME_SCALE).expect("Q0");
    let q1 = normal_form(Q1_LOWER_SCALE_FIRST).expect("Q1");
    let q2 = normal_form(Q2_LOWER_SCALE_LAST).expect("Q2");
    let q3 = normal_form(Q3_DIFFERENT_VALUE).expect("Q3");

    assert_eq!(q0, "6.33p2", "control: 4.00p2 + 2.33p2");
    assert_eq!(
        q1, q0,
        "★ THE FIX on a precondition-safe carrier: this answered `6.3p1` before work item #200 \
         — both divide operands had an equal-value p1 sibling seeded ahead of them",
    );
    assert_eq!(q2, q1, "★ …and it is order-independent");
    assert_eq!(q3, q0, "control (b-negative): siblings of a different VALUE never moved it");
}

/// ★★ A CONSEQUENCE OF THE FIX THAT NOTHING ELSE PINS, and it is the language's whole
/// scale-repair story: **`fixed(x, w)` only works because of work item #200.**
///
/// A widening rescale PRESERVES the number. Under the old value-keyed `Eq` its result was
/// therefore `Eq`-equal to its own input, landed in the input's e-class, and the extractor
/// handed back the first-inserted (un-rescaled) representative. So the rescale was computed and
/// then thrown away — silently, with no sibling literal required and no order-dependence:
/// `fixed(x, w)` was a NO-OP for every value-preserving `w`.
///
/// MEASURED at `7fad51db`, immediately before the fix — note the perfect correlation between
/// "value preserved" and "rescale erased", which is what identifies the mechanism:
///
/// | program | preserves the number? | answered |
/// |---|---|---|
/// | `fixed(3.0p1, 2)`  | yes | `3.0p1`  ← erased |
/// | `fixed(3p0, 2)`    | yes | `3p0`    ← erased |
/// | `fixed(1.25p2, 4)` | yes | `1.25p2` ← erased |
/// | `fixed(1.20p2, 1)` | yes | `1.20p2` ← erased |
/// | `fixed(1.25p2, 1)` | NO (1.25 → 1.2) | `1.2p1` ← visible |
/// | `fixed(1.25p2, 0)` | NO (1.25 → 1)   | `1p0`   ← visible |
///
/// ⚠ This matters well beyond tidiness: `fixed(x, w)` is the ONLY way a program can repair a
/// scale mismatch, so it is the escape hatch any future scale-equality precondition (work item
/// #186) depends on. That precondition would have been unshippable while its escape hatch was
/// a no-op, and nothing recorded that.
///
/// ★ `fixed(0p0, 2)` is deliberately NOT in the green list below. It stays `0p0` for a SECOND,
/// independent reason — `CanonicalFixedPoint::normalize_in_place` collapses true zero to `0p0`
/// at construction — which this ruling does not touch. Asserted as such so the two causes are
/// not confused.
#[test]
fn the_rescale_operator_is_no_longer_erased_by_its_own_input() {
    for (src, want) in [
        ("fixed(3.0p1, 2)", "3.00p2"),
        ("fixed(3p0, 2)", "3.00p2"),
        ("fixed(1.25p2, 4)", "1.2500p4"),
        ("fixed(1.20p2, 1)", "1.2p1"),
    ] {
        assert_eq!(
            normal_form(src).expect("the rescale must evaluate"),
            want,
            "`{src}` must actually rescale. Before work item #200 it answered its own \
             (un-rescaled) input, because the rescaled result was `Eq`-equal to it and the \
             extractor returned the first-inserted representative",
        );
    }

    // The value-CHANGING rescales were always visible; they are the control proving the test
    // above is not merely asserting that `fixed` exists.
    for (src, want) in [("fixed(1.25p2, 1)", "1.2p1"), ("fixed(1.25p2, 0)", "1p0")] {
        assert_eq!(normal_form(src).expect("rescale"), want, "`{src}` truncates, as it always did");
    }

    assert_eq!(
        normal_form("fixed(0p0, 2)").expect("rescale"),
        "0p0",
        "⚠ RESIDUAL, and NOT this ruling's: zero cannot be rescaled because \
         `CanonicalFixedPoint::normalize_in_place` forces `places = 0` at construction. That is \
         a separate divergence from upstream (`make_fixedpoint_expr` does not normalize) and \
         needs its own ruling",
    );
}

/// Sibling enumeration, measured not asserted-by-hand: WHICH scale-reading operations change
/// their VALUE (not merely their rendering) when the operand representative flips scale?
///
/// `align_pair` (`runtime/src/canonical_fixed_point.rs:93`) has FOUR callers — `checked_div`
/// (`:104`), `checked_rem` (`:197`), `Add::add` (`:312`), `Sub::sub` (`:320`) — and
/// `bitwise_aligned` (`:205`) has THREE (`BitAnd` `:360`, `BitOr` `:367`, `BitXor` `:374`).
/// `Mul::mul` (`:329`) and `Neg::neg` (`:353`) read `places` without either helper. NINE
/// scale-reading operations in total.
///
/// ⚠⚠ **RE-DERIVED 2026-07-30 (work item #200): this table would otherwise have gone
/// VACUOUS.** It classified each row by `at_p2 != at_p1`, i.e. by `PartialEq`. `PartialEq` now
/// keys on the raw `(unscaled, places)` pair, and every row's two answers differ in `places` by
/// construction — so all nine rows would read `VALUE-DIFFERS=true`, the 4/5 split would collapse
/// to 9/0, and the table would be measuring the ruling instead of the operators. The comparison
/// is therefore made EXPLICITLY on `value_ratio()`, which is what "value" meant all along.
///
/// The superseded classifier, verbatim:
///
/// ```text
/// let differs = at_p2 != at_p1;
/// …
/// } else if format!("{at_p2}") != format!("{at_p1}") {
///     render_only.push(*name);
/// }
/// ```
///
/// ⚠ This table is REVISION-SENSITIVE, so it is printed rather than hard-coded. Measured
/// before/after `afcc9e8f` ("`%` is the remainder on the unscaled integers, per upstream"):
/// `checked_rem` moved from VALUE-CHANGING (`0.01p2` vs `0.1p1`) to RENDERING-ONLY (`1.00p2`
/// vs `1.0p1`) — i.e. that fix independently closed one of the value-changing exposures.
///
/// At `afcc9e8f` the split was VALUE-CHANGING 4 / RENDERING-ONLY 5. Re-measured at `7fad51db`
/// immediately before work item #200 it was unchanged, with these rows:
///
/// ```text
///   checked_div  (align_pair)  p2=2.33p2     p1=2.3p1      VALUE-DIFFERS=true
///   checked_rem  (align_pair)  p2=1.00p2     p1=1.0p1      VALUE-DIFFERS=false
///   Add          (align_pair)  p2=10.00p2    p1=10.0p1     VALUE-DIFFERS=false
///   Sub          (align_pair)  p2=4.00p2     p1=4.0p1      VALUE-DIFFERS=false
///   Mul          (places sum)  p2=21.0000p4  p1=21.00p2    VALUE-DIFFERS=false
///   BitAnd  (bitwise_aligned)  p2=0.44p2     p1=0.6p1      VALUE-DIFFERS=true
///   BitOr   (bitwise_aligned)  p2=9.56p2     p1=9.4p1      VALUE-DIFFERS=true
///   BitXor  (bitwise_aligned)  p2=9.12p2     p1=8.8p1      VALUE-DIFFERS=true
///   Neg          (places kept)  p2=-7.00p2    p1=-7.0p1    VALUE-DIFFERS=false
/// ```
///
/// The 4/5 split must be UNCHANGED by this ruling: #200 stops the two spellings from being
/// conflated, it does not change what any operator computes from a given pair of operands. The
/// split is asserted, not merely printed, so a silent drift is caught.
///
/// ★ Of the four value-changing rows, `BitXor` is DORMANT — neither `calculator` nor `rholang`
/// declares `bitxor`/`^` on `Fixed`, and they are the only two languages carrying a `Fixed`
/// category — so three are reachable from a program. A fourth reachable one is NOT in this
/// table at all because it is UNARY and so has no operand pair: `bitnot`, whose fold body reads
/// `places` inline (`languages/src/calculator.rs:386`, `languages/src/rholang.rs:1470-1471`)
/// and answers `-7.01p2` versus `-7.1p1`. ★★ That is the cleanest proof that this ruling was
/// load-bearing and could not be replaced by a scale-equality precondition: no precondition on
/// operand pairs can reach a one-operand operator.
#[test]
fn sibling_enumeration_which_ops_change_value_on_scale_flip() {
    let a2 = fixed("7.00p2");
    let b2 = fixed("3.00p2");
    let a1 = fixed("7.0p1");
    let b1 = fixed("3.0p1");
    assert_ne!(
        a2, a1,
        "premise, INVERTED by work item #200: the two spellings are distinct VALUES…",
    );
    assert_eq!(
        a2.to_rational_canonical_bytes(),
        a1.to_rational_canonical_bytes(),
        "…denoting the same NUMBER, which is what makes the flip meaningful at all",
    );
    assert_ne!(b2, b1, "premise: likewise for the divisor");
    assert_eq!(b2.to_rational_canonical_bytes(), b1.to_rational_canonical_bytes());

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
        // ★ EXPLICITLY on the NUMBER. `at_p2 != at_p1` would now be true for every row.
        //
        // `to_rational_canonical_bytes` is used rather than `value_ratio()` because the latter
        // is `pub(crate)` in `mettail-runtime` and this ruling gave no reason to widen it. The
        // former's documented contract is exactly value-equality — the length-framed reduced
        // `(numer, denom)` — so byte-equality here IS "denotes the same number", and using it
        // pins the value-keyed method from the language side as a bonus.
        let differs = at_p2.to_rational_canonical_bytes() != at_p1.to_rational_canonical_bytes();
        report.push_str(&format!(
            "  {name}  p2-operands={:<10} p1-operands={:<10} VALUE-DIFFERS={differs}\n",
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
    assert_eq!(
        (value_changing.len(), render_only.len()),
        (4, 5),
        "the 4/5 split is a property of the OPERATORS and must not move with the identity \
         ruling. If it just became 9/0, the classifier has drifted back onto `PartialEq`",
    );
}
