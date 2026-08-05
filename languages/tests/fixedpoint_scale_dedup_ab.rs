//! Fixed-point scale identity and explicit-rescaling regression gates.
//!
//! Before work item #200, `CanonicalFixedPoint` keyed identity on its reduced rational value. The
//! Dovetail hashcons therefore merged equal-number literals such as `7.00p2` and `7.0p1`, even
//! though scale-sensitive division produced `2.33p2` and `2.3p1`. The first-inserted spelling
//! could change an unrelated expression's result.
//!
//! Identity now keys on the raw `(unscaled, places)` pair, exactly like upstream Rholang's
//! structural `GFixedPoint`. The gates below establish three consequences:
//!
//! 1. different scales remain distinct e-nodes regardless of insertion order;
//! 2. equal-scale expressions do not depend on equal-number siblings at other scales; and
//! 3. `fixed(value, places)` is an observable scale-repair operation, including for zero.
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
//! The repair is at the key, not at the e-graph. Work item #200 moved `Eq`/`Hash`/`Ord`
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
//! The fix ensures nothing is eliminated: each fixed-point value retains the scale that was
//! written, while mixed-scale binary operations now refuse before evaluation.
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
    let p2 = fixed("7.00p2")
        .checked_div(fixed("3.00p2"))
        .expect("nonzero divisor");
    let p1 = fixed("7.0p1")
        .checked_div(fixed("3.0p1"))
        .expect("nonzero divisor");
    assert_eq!(format!("{p2}"), "2.33p2");
    assert_eq!(format!("{p1}"), "2.3p1");
    assert_ne!(p2, p1, "233/100 != 23/10 — a genuine value difference, not a rendering one");
}

fn normal_form(src: &str) -> Result<String, String> {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let term = lang
        .parse_term(src)
        .map_err(|e| format!("parse error: {e}"))?;
    let normal = CalculatorLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .map_err(|e| format!("dovetail_normal_term error: {e}"))?;
    Ok(format!("{normal}"))
}

// ─────────────────────────────────────────────────────────────────────────────
// End-to-end carriers through production `dovetail_normal_term`.
//
// Every binary operation has equal-scale operands. Explicit `fixed(..., 2)` conversions make the
// scale-repair mechanism part of the gate; the obsolete mixed-scale zero carriers were retired
// when upstream's scale-equality precondition landed.
//
// ⚠ Both operands of the divide need an equal-value lower-scale sibling. A carrier supplying
// only ONE (say `7.0p1`, leaving `3.00p2` with no p1 twin) does NOT reproduce the defect —
// the p2 quotient is unchanged. This refuted the first draft of the carrier:
// `fixed((7.0p1 - 4.0p1), 2) + (7.00p2 / 3.00p2)`
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

/// A scale-reading operator's answer does not depend on an equal-number, different-scale sibling
/// elsewhere in the program or on the sibling's textual order. All binary operations in these
/// carriers have equal scales, so the gate cannot pass merely because mixed-scale evaluation
/// refused.
///
/// ⚠ Q1's pre-fix value is MEASURED, not assumed: `6.3p1`, against `6.33p2` for the other
/// three. It really did discriminate.
#[test]
fn the_answer_must_not_depend_on_an_equal_value_sibling() {
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

#[test]
fn calculator_refuses_mixed_scale_arithmetic_ordering_and_bitwise_ops() {
    for expression in [
        "7.00p2 + 3.000p3",
        "7.00p2 - 3.000p3",
        "7.00p2 * 3.000p3",
        "7.00p2 / 3.000p3",
        "7.00p2 % 3.000p3",
        "7.00p2 bitand 3.000p3",
        "7.00p2 bitor 3.000p3",
        "7.00p2 > 3.000p3",
        "7.00p2 < 3.000p3",
        "7.00p2 >= 3.000p3",
        "7.00p2 <= 3.000p3",
    ] {
        assert_eq!(
            normal_form(expression).expect("the evaluator reaches a normal form"),
            expression,
            "`{expression}` must remain an unreduced redex instead of silently rescaling; \
             Calculator records a fold decline rather than manufacturing its parseable `error` \
             literal",
        );
    }
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
/// This is now the migration mechanism for the scale-equality precondition: a program can make
/// an intended scale explicit before applying a binary operator. Zero is included because its
/// declared scale is no longer normalized away.
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
        "0.00p2",
        "zero retains the scale requested by the explicit conversion",
    );
}

/// Sibling enumeration, measured not asserted-by-hand: WHICH scale-reading operations change
/// their VALUE (not merely their rendering) when the operand representative flips scale?
///
/// The checked arithmetic and bitwise methods all enforce equal scales. This table compares
/// their results for same-number operand pairs represented consistently at p2 versus p1; it
/// detects operations whose numerical answer genuinely depends on declared precision.
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
///   checked_div                  p2=2.33p2     p1=2.3p1      VALUE-DIFFERS=true
///   checked_rem                  p2=1.00p2     p1=1.0p1      VALUE-DIFFERS=false
///   checked_add                  p2=10.00p2    p1=10.0p1     VALUE-DIFFERS=false
///   checked_sub                  p2=4.00p2     p1=4.0p1      VALUE-DIFFERS=false
///   checked_mul                  p2=21.00p2    p1=21.0p1     VALUE-DIFFERS=false
///   checked_bitand               p2=0.44p2     p1=0.6p1      VALUE-DIFFERS=true
///   checked_bitor                p2=9.56p2     p1=9.4p1      VALUE-DIFFERS=true
///   checked_bitxor               p2=9.12p2     p1=8.8p1      VALUE-DIFFERS=true
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
        (
            "checked_div",
            a2.checked_div(b2).expect("div"),
            a1.checked_div(b1).expect("div"),
        ),
        (
            "checked_rem",
            a2.checked_rem(b2).expect("rem"),
            a1.checked_rem(b1).expect("rem"),
        ),
        (
            "checked_add",
            a2.checked_add(b2).expect("add"),
            a1.checked_add(b1).expect("add"),
        ),
        (
            "checked_sub",
            a2.checked_sub(b2).expect("sub"),
            a1.checked_sub(b1).expect("sub"),
        ),
        (
            "checked_mul",
            a2.checked_mul(b2).expect("mul"),
            a1.checked_mul(b1).expect("mul"),
        ),
        (
            "checked_bitand",
            a2.checked_bitand(b2).expect("bitand"),
            a1.checked_bitand(b1).expect("bitand"),
        ),
        (
            "checked_bitor",
            a2.checked_bitor(b2).expect("bitor"),
            a1.checked_bitor(b1).expect("bitor"),
        ),
        (
            "checked_bitxor",
            a2.checked_bitxor(b2).expect("bitxor"),
            a1.checked_bitxor(b1).expect("bitxor"),
        ),
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
