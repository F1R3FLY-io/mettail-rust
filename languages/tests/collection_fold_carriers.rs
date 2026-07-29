//! ★★ Task #101 — THE THREE FIXTURES for the collection fold carriers.
//!
//! # What was broken
//!
//! A fold operand is bound by INVERTING its lowered derivation child. A collection-typed
//! parameter lowered to `FieldOpaque(format!("{:?}", …))` — one shared discriminant, `Debug`
//! bytes, no inverse — so the typed fold gate refused every `Vec(T)` / `HashBag(T)` parameter
//! and fifteen declared folds across the corpus fired nowhere while their surface syntax kept
//! advertising them. One of the fifteen was `Turing::shift_right`: the entire mechanism by
//! which that machine's head advances.
//!
//! # The repair, and the three claims a corpus cannot falsify
//!
//! `TypeExpr::Collection` fold parameters are now admitted PER CARRIER
//! (`macros/src/gen/runtime/dovetail_report.rs`'s `CollectionCarrier`):
//!
//! | container | carrier | lowering |
//! |---|---|---|
//! | `Vec(T)` | `OrderedSeq` | `FieldSeq<T>(Vec<T>)` — the whole value VERBATIM in a labelled leaf, inverted by `__mettail_dovetail_build_seq_<t>_d` |
//! | `HashBag(T)` (whole constructor) | `AcBag` | the n-ary AC bag node it already had |
//! | `HashSet` / `HashMap` / `PathMap` | `Opaque` | unchanged `FieldOpaque` — REFUSED as a fold operand |
//!
//! Three of the claims that repair makes are about shapes the production corpus does not
//! contain, so a corpus-only test suite would assert them vacuously:
//!
//! | fixture | claim it makes falsifiable |
//! |---|---|
//! | [`seq_carrier_demo`] | the ORDERED whole-constructor arm: a constructor NODE restores identity two bare leaves erased, and a single-`Vec` fold fires. Every `VariantKind::Collection` in the corpus is a `HashBag`, so without this the arm is dead code. |
//! | [`map_param_refusal_demo`] | the gate did NOT open to "any `TypeExpr::Collection`". The corpus has zero set/map fold parameters, so "sets and maps stay refused" is otherwise an assertion about an empty set. |
//! | [`turing_loop`] | the head moves MORE THAN ONCE. The production `Turing` table has entries only from `q0`, so its maximal derivation is exactly two firings — enough to show the head moved, not enough to show it keeps moving. |
//!
//! ⚠ Every fixture carries a POSITIVE CONTROL on the same language and the same walk, because
//! an assertion that something is refused cannot otherwise be told apart from a walk that
//! inspected nothing.

#![allow(non_local_definitions)]

use mettail_runtime::{
    Language, LanguageMetadata, LoweredConstructKind, LoweringDispositionDef,
    LoweringOutcomeKind,
};

#[path = "definitions/seq_carrier_demo.rs"]
mod seq_carrier_demo;

#[path = "definitions/map_param_refusal_demo.rs"]
mod map_param_refusal_demo;

#[path = "definitions/turing_loop.rs"]
mod turing_loop;

/// Iteration / node budget for the e-graph saturation. Bounded on purpose: a budget means a
/// non-converging machine surfaces as a limit error, never as a hung test binary.
const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 200_000;

/// A one-line rendering of a whole inventory, for assertion messages.
fn render(inventory: &[LoweringDispositionDef]) -> String {
    inventory
        .iter()
        .map(|d| {
            format!(
                "\n    {:8} {:16} {:18} {:12} {}",
                d.construct_kind.noun(),
                d.construct,
                d.outcome.as_str(),
                d.origin.as_str(),
                d.detail,
            )
        })
        .collect()
}

/// The single disposition recorded for a fold, or a failure naming the whole inventory.
fn fold_disposition<'a>(
    inventory: &'a [LoweringDispositionDef],
    construct: &str,
) -> &'a LoweringDispositionDef {
    let found: Vec<&LoweringDispositionDef> = inventory
        .iter()
        .filter(|d| d.construct_kind == LoweredConstructKind::Fold && d.construct == construct)
        .collect();
    assert_eq!(
        found.len(),
        1,
        "fold `{construct}` must have exactly one disposition.{}",
        render(inventory),
    );
    found[0]
}

// ═════════════════════════════════════════════════════════════════════════════
// FIXTURE 1 — SeqCarrierDemo: the ORDERED whole-constructor carrier
// ═════════════════════════════════════════════════════════════════════════════

/// ★★ CONSTRUCTOR IDENTITY, restored.
///
/// `Boxed` and `Crated` are two DISTINCT single-`Vec` constructors of one category. Before
/// #101, `VariantKind::Collection` with a non-AC container lowered to a BARE
/// `FieldOpaque(format!("{:?}", values))` leaf with **no constructor node**, so the e-node
/// content of `box(0)` and `crate(0)` was byte-identical and the two hash-consed into ONE
/// e-class — a rewrite keyed on either matched both.
///
/// The ordered arm now emits `ENode::new(Cat_Label, [seq_leaf])`. The payload is untouched
/// (the same bytes, in the same order, under a labelled discriminant); what is added is the
/// constructor's own op above it. So the two constructors occupy DIFFERENT e-classes while
/// still SHARING the one payload leaf — which is the second half of the claim, and the half
/// that distinguishes "identity restored" from "payloads duplicated".
#[test]
fn two_single_vec_constructors_no_longer_collide() {
    mettail_runtime::clear_var_cache();
    let lang = seq_carrier_demo::SeqCarrierDemoLanguage;
    let term = lang
        .parse_term("pair(box(0),crate(0))")
        .unwrap_or_else(|e| panic!("parse failed: {e}"));
    let report = seq_carrier_demo::SeqCarrierDemoLanguage::dovetail_report_for(
        term.as_ref(),
        MAX_ITERS,
        MAX_NODES,
    )
    .unwrap_or_else(|e| panic!("dovetail_report_for returned Err: {e}"));

    let rendered = format!(
        "terms={:?}",
        report
            .terms
            .iter()
            .map(|t| (t.class_id, t.op_display.clone()))
            .collect::<Vec<_>>()
    );

    let class_of = |op: &str| -> u32 {
        let hits: Vec<u32> = report
            .terms
            .iter()
            .filter(|t| t.op_display == op)
            .map(|t| t.class_id)
            .collect();
        assert_eq!(hits.len(), 1, "expected exactly one `{op}` term; {rendered}");
        hits[0]
    };

    let boxed = class_of("SeqCarrierDemo::Term::Boxed");
    let crated = class_of("SeqCarrierDemo::Term::Crated");
    assert_ne!(
        boxed, crated,
        "★ two DISTINCT single-`Vec` constructors with equal payloads must occupy DIFFERENT \
         e-classes. Equal class ids are the pre-#101 collision: a bare payload leaf with no \
         constructor node erases constructor identity. {rendered}",
    );

    // ★ The other half: the shared payload is stored ONCE. Both constructor nodes point at the
    // same `<field-seq-Term>([Zero])` leaf, so identity was restored by ADDING a node, not by
    // making the payloads differ.
    let payload_classes: Vec<u32> = report
        .terms
        .iter()
        .filter(|t| t.op_display.starts_with("<field-seq-Term>"))
        .map(|t| t.class_id)
        .collect();
    assert_eq!(
        payload_classes.len(),
        1,
        "the two constructors share ONE payload leaf — identity comes from the constructor \
         node, not from divergent payloads. {rendered}",
    );
}

/// ★ A single-`Vec` FOLD fires — the `VariantKind::Collection` + `OrderedSeq` lowering paired
/// with the ordinary positional `Pattern::app(op, [var xs])` LHS, which is arity-correct
/// precisely because the constructor node has exactly one child.
#[test]
fn single_vec_whole_constructor_fold_fires() {
    mettail_runtime::clear_var_cache();
    let lang = seq_carrier_demo::SeqCarrierDemoLanguage;
    let term = lang
        .parse_term("first(0,0)")
        .unwrap_or_else(|e| panic!("parse failed: {e}"));
    let report = seq_carrier_demo::SeqCarrierDemoLanguage::dovetail_report_for(
        term.as_ref(),
        MAX_ITERS,
        MAX_NODES,
    )
    .unwrap_or_else(|e| panic!("dovetail_report_for returned Err: {e}"));
    let labels: Vec<String> = report
        .rule_firings
        .iter()
        .filter_map(|f| f.label.clone())
        .collect();
    assert_eq!(
        labels,
        vec!["SeqCarrierDemo::fold::Term_Firstly".to_string()],
        "the single-`Vec` fold must fire exactly once; firings={:?} terms={:?}",
        report.rule_firings,
        report.terms.iter().map(|t| t.op_display.clone()).collect::<Vec<_>>(),
    );

    // ★ POSITIVE CONTROL ON THE SATURATION. A term with no redex fires nothing, so the
    // assertion above is not an engine that fires rules indiscriminately.
    let inert = lang.parse_term("pair(0,0)").expect("parse control");
    let control = seq_carrier_demo::SeqCarrierDemoLanguage::dovetail_report_for(
        inert.as_ref(),
        MAX_ITERS,
        MAX_NODES,
    )
    .expect("control report");
    assert!(
        control.rule_firings.is_empty(),
        "a redex-free term fires nothing; firings={:?}",
        control.rule_firings,
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// FIXTURE 2 — MapParamRefusalDemo: the gate did not open too far
// ═════════════════════════════════════════════════════════════════════════════

/// ★★ A MAP FOLD PARAMETER STAYS REFUSED — on a NON-EMPTY set of instances.
///
/// The corpus contains zero folds with a set/map parameter, so a corpus-only assertion that
/// "the gate did not open to any `TypeExpr::Collection`" is an assertion about nothing.
/// `MapFold`'s `m:HashMap(Proc, Proc)` is the live instance, and the refusal must NAME the
/// offending type so the inventory entry is actionable without opening the grammar.
///
/// ⚠ WHY THERE IS NO `HashSet` SIBLING HERE — measured, and recorded so it is not re-attempted.
/// `HashSet(T)` is the one shape that would reach the gate's `CollectionCarrier::Opaque` arm
/// through `TypeExpr::Collection` rather than `TypeExpr::Map`, so it looks like the sharper
/// falsifier. It cannot be declared at all: a `HashSet` collection FIELD emits a raw
/// `std::collections::HashSet<Proc>` AST field, which implements neither `Hash` nor `Ord` nor
/// `BoundTerm` — four hard compile errors in `iterative_hash` / `semantic_hash` /
/// `iterative_cmp` / the `BoundTerm` derive, all of them before any lowering runs, none of them
/// anything #101 touches. `HashMap(K, V)` is therefore the only expressible instance of a
/// refused keyed container, and the `Opaque` carrier arm is a FAIL-CLOSED default over the rest
/// of `CollectionType` rather than a live path. Stating that is more honest than a fixture that
/// cannot be built.
#[test]
fn map_fold_parameter_stays_declined_naming_its_type() {
    let inventory = map_param_refusal_demo::MapParamRefusalDemoMetadata.lowering_dispositions();
    assert!(
        !inventory.is_empty(),
        "an empty inventory would make every assertion below vacuous",
    );

    let map_fold = fold_disposition(inventory, "MapFold");
    assert!(
        map_fold.is_declined(),
        "★ THE GATE OPENED TOO FAR: a keyed container has no stored order to invert — its \
         e-graph content key is a SORTED `Display`, not its `Debug` — so admitting it would \
         claim an inverse that does not exist.{}",
        render(inventory),
    );
    assert!(
        map_fold.detail.contains("HashMap("),
        "the declination must NAME the refusing type, not merely restate the gate.{}",
        render(inventory),
    );

    // ★★ THE POSITIVE CONTROL, on the same language and the same walk. Without it, "the gate
    // declined `MapFold`" is indistinguishable from "the fold walk never ran".
    let vec_fold = fold_disposition(inventory, "VecFold");
    assert_eq!(
        vec_fold.outcome,
        LoweringOutcomeKind::Delivered,
        "an ORDERED collection parameter on the SAME language IS lowered — that is what makes \
         the refusal above a distinction rather than a blanket.{}",
        render(inventory),
    );
    assert_eq!(
        vec_fold.detail, "MapParamRefusalDemo::fold::Proc_VecFold",
        "a Delivered disposition carries the label of the rule it emitted.{}",
        render(inventory),
    );
}

/// ★ The ordered control does not merely record a disposition — it REDUCES.
///
/// A `Delivered` entry naming a rule that never fires would satisfy the disposition assertion
/// above while leaving the capability absent, so the control is exercised end-to-end.
#[test]
fn the_ordered_control_fold_actually_reduces() {
    mettail_runtime::clear_var_cache();
    let lang = map_param_refusal_demo::MapParamRefusalDemoLanguage;
    let term = lang
        .parse_term("vfold([0,0],0)")
        .unwrap_or_else(|e| panic!("parse failed: {e}"));
    let report = map_param_refusal_demo::MapParamRefusalDemoLanguage::dovetail_report_for(
        term.as_ref(),
        MAX_ITERS,
        MAX_NODES,
    )
    .unwrap_or_else(|e| panic!("dovetail_report_for returned Err: {e}"));
    let labels: Vec<String> = report
        .rule_firings
        .iter()
        .filter_map(|f| f.label.clone())
        .collect();
    assert!(
        labels.iter().any(|l| l == "MapParamRefusalDemo::fold::Proc_VecFold"),
        "the ordered control must FIRE, not merely be recorded; firings={:?}",
        report.rule_firings,
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// FIXTURE 3 — TuringLoop: the head keeps moving
// ═════════════════════════════════════════════════════════════════════════════

/// Saturate `src` under `TuringLoop` and return (per-label firing COUNTS, a rendering for
/// messages).
///
/// ⚠ COUNTS, not label occurrences. `RuntimeDovetailRuleFiring` is *aggregated* evidence: one
/// record per distinct rule label, carrying a `count` of how many times that rule fired. A rule
/// that fired three times therefore appears ONCE in `rule_firings` with `count: 3`, so counting
/// label occurrences answers "how many rules fired", not "how many times". Measured: this test
/// first read occurrences and reported `Counted 1` against a report whose own text said
/// `count: 3`.
fn loop_firings(src: &str) -> (Vec<(String, usize)>, String) {
    mettail_runtime::clear_var_cache();
    let lang = turing_loop::TuringLoopLanguage;
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let report =
        turing_loop::TuringLoopLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES)
            .unwrap_or_else(|e| panic!("dovetail_report_for({src:?}) returned Err: {e}"));
    let counted: Vec<(String, usize)> = report
        .rule_firings
        .iter()
        .filter_map(|f| f.label.clone().map(|l| (l, f.count)))
        .collect();
    let rendered = format!(
        "complete={} roots={} firings={:?} terms={:?}",
        report.is_complete(),
        report.roots.len(),
        report.rule_firings,
        report.terms.iter().map(|t| t.op_display.clone()).collect::<Vec<_>>(),
    );
    (counted, rendered)
}

/// ★★ THE HEAD KEEPS MOVING — three transitions and three head moves in one derivation.
///
/// The production `Turing` spec's table has entries only from `q0`, so its maximal derivation
/// is exactly two firings; that is enough to prove the head moved and not enough to prove it
/// keeps moving. `TuringLoop` adds two table entries (from `q1` and `q2`) and nothing else, so
/// this is a statement about the LOWERING, not about a different helper.
///
/// Run from `(q0 , <[] | 0 | [0,0]>)`:
///
/// ```text
///   q0  <[]      | 0 | [0,0]>  --D_q0_0-->  shift_right([],1,[0,0])   ==>  <[1]     | 0 | [0]>
///   q1  <[1]     | 0 | [0]>    --D_q1_0-->  shift_right([1],1,[0])    ==>  <[1,1]   | 0 | []>
///   q2  <[1,1]   | 0 | []>     --D_q2_0-->  shift_right([1,1],1,[])   ==>  <[1,1,1] | _ | []>
/// ```
///
/// The third move takes the helper's OTHER branch (`r.split_first()` on an empty right context
/// yields `Sym::Blank`), so the `![…]` body is executed on both of its arms across the run.
#[test]
fn turing_loop_takes_three_head_moves() {
    let (counted, rendered) = loop_firings("(q0 , <[] | 0 | [0,0]>)");

    let head_moves = counted
        .iter()
        .filter(|(l, _)| l == "TuringLoop::fold::Tape_shift_right")
        .map(|(_, n)| *n)
        .sum::<usize>();
    assert_eq!(
        head_moves, 3,
        "★ the head must move exactly THREE times — one move proves the fold fires, three \
         prove it keeps firing on the tapes its OWN previous move produced, which is the \
         property a two-firing derivation cannot show. Counted {head_moves}; \
         report: {rendered}",
    );

    // Each of the three table entries fires exactly once, so the three head moves are three
    // DISTINCT steps of one machine rather than one step counted thrice.
    for entry in [
        "TuringLoop::rewrite::D_q0_0",
        "TuringLoop::rewrite::D_q1_0",
        "TuringLoop::rewrite::D_q2_0",
    ] {
        let fired = counted
            .iter()
            .filter(|(l, _)| l == entry)
            .map(|(_, n)| *n)
            .sum::<usize>();
        assert_eq!(
            fired, 1,
            "{entry} must fire exactly once on the path; report: {rendered}",
        );
    }

    // ★ THE CONTROL. A halted configuration matches nothing on the same language, so the
    // multi-step derivation above is not saturation running away.
    let (halted, halted_rendered) = loop_firings("(halt , <[] | _ | []>)");
    assert!(
        halted.is_empty(),
        "a halted configuration fires nothing; report: {halted_rendered}",
    );
}

/// ★ THE FINAL TAPE, RECONSTRUCTED — the last head move's result read back as an AST term.
///
/// The third move is the one whose right context is empty, so it exercises the `Sym::Blank`
/// branch of the helper's `![…]` body; reconstructing its result proves the value the fold
/// computed survives the round trip through the e-graph and the `FieldSeq<Sym>` carrier.
///
/// ⚠ Asserted on the TAPE rather than on the whole configuration, and for a stated reason:
/// `Cf` is not a redex head (the `redex_heads` invariant admits only heads whose presence
/// proves an un-fired reduction), so `Cf(Q3, Tp …)` is not cheaper than `Cf(Q0, Tp …)` and
/// funded 1-best extraction may return either. A bare helper application has no such
/// competitor, so its normal form is exactly the moved tape.
#[test]
fn turing_loop_final_tape_reconstructs() {
    mettail_runtime::clear_var_cache();
    let lang = turing_loop::TuringLoopLanguage;
    // The third head move of the run above, applied on its own.
    let term = lang
        .parse_term("(halt , shift_right([1,1],1,[]))")
        .unwrap_or_else(|e| panic!("parse failed: {e}"));
    let normal = turing_loop::TuringLoopLanguage::dovetail_normal_term(
        term.as_ref(),
        MAX_ITERS,
        MAX_NODES,
    )
    .unwrap_or_else(|e| panic!("the final tape must reconstruct; got Err({e})"));
    assert_eq!(
        format!("{normal}"),
        "(halt , <[1 , 1 , 1]|_|[]>)",
        "the reconstructed final tape is the COMPUTED zipper move: write `1` at the head cell, \
         step right off the end of the written tape, and read `_`",
    );
}
