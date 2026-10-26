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
//!
//! (2026-10-20) A fourth fixture, [`sole_collection_carrier_demo`], covers the sole-collection
//! lane (`VariantKind::Collection`): each emitter of that lane follows the declared carrier
//! and the declared element. It also declares the `HashSet` fold parameter that FIXTURE 2
//! records as impossible to declare.

#![allow(non_local_definitions)]

use mettail_runtime::{
    Language, LanguageMetadata, LoweredConstructKind, LoweringDispositionDef, LoweringOutcomeKind,
};

#[path = "definitions/seq_carrier_demo.rs"]
mod seq_carrier_demo;

#[path = "definitions/map_param_refusal_demo.rs"]
mod map_param_refusal_demo;

#[path = "definitions/turing_loop.rs"]
mod turing_loop;

#[path = "definitions/sole_collection_carrier_demo.rs"]
mod sole_collection_carrier_demo;

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
        report
            .terms
            .iter()
            .map(|t| t.op_display.clone())
            .collect::<Vec<_>>(),
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
///
/// (2026-10-20) This is no longer true. A `HashSet(T)` field is now
/// `mettail_runtime::HashSetLit<T>`, which has `Hash`, `Ord` and `BoundTerm`, so FIXTURE 4
/// declares the `HashSet` fold parameter
/// (`a_sole_hash_set_fold_parameter_is_declined_naming_its_type`). The text above is the record
/// from before that change.
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
        vec_fold.detail,
        "MapParamRefusalDemo::fold::Proc_VecFold",
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
        labels
            .iter()
            .any(|l| l == "MapParamRefusalDemo::fold::Proc_VecFold"),
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
        report
            .terms
            .iter()
            .map(|t| t.op_display.clone())
            .collect::<Vec<_>>(),
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
        assert_eq!(fired, 1, "{entry} must fire exactly once on the path; report: {rendered}",);
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
    let normal =
        turing_loop::TuringLoopLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
            .unwrap_or_else(|e| panic!("the final tape must reconstruct; got Err({e})"));
    assert_eq!(
        format!("{normal}"),
        "(halt , <[1 , 1 , 1]|_|[]>)",
        "the reconstructed final tape is the COMPUTED zipper move: write `1` at the head cell, \
         step right off the end of the written tape, and read `_`",
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// FIXTURE 4 — SoleCollectionCarrierDemo: the sole-collection lane follows its declared
// carrier and element (added 2026-10-20)
// ═════════════════════════════════════════════════════════════════════════════

/// `normalize(parse(source))`, or a failure naming the source.
fn normalized(
    lang: &sole_collection_carrier_demo::SoleCollectionCarrierDemoLanguage,
    source: &str,
) -> Box<dyn mettail_runtime::Term> {
    let term = lang
        .parse_term(source)
        .unwrap_or_else(|e| panic!("`{source}` must parse: {e}"));
    lang.normalize_term(term.as_ref())
}

/// ★ Every carrier and element shape of the sole-collection lane parses, normalizes, prints,
/// and reads back to the same normal form. Before 2026-10-20 this language did not compile:
/// the auto-flatten helper was emitted and called for the cross-category bags `PNames` and
/// `PNameBag`, and a `HashSet` field was a raw `std::collections::HashSet`
/// (BinderFloatCanonicalization.v Part 5, `old_gate_emits_and_calls_an_ill_typed_helper`).
#[test]
fn every_sole_collection_shape_reads_back_to_its_normal_form() {
    mettail_runtime::clear_var_cache();
    let lang = sole_collection_carrier_demo::SoleCollectionCarrierDemoLanguage;
    for source in [
        "par{0|par{0|0}}",
        "names{n,n}",
        "metas{m,m}",
        "metaset{m,m,other}",
        "metaseq[m,other,m]",
        "mbag m, m end",
        "mset m, m end",
        "mseq m, other end",
        "set{0,set{0}}",
        "nameset{n}",
        "seq[0,seq[0]]",
        "nameseq[n,n]",
        "bnames n, n end",
        "bnames end",
        "bset 0 end",
        "bseq 0, 0 end",
    ] {
        let first = normalized(&lang, source);
        let printed = lang.format_term(first.as_ref());
        let second = normalized(&lang, &printed);
        assert!(
            second.term_eq(first.as_ref()),
            "`{source}` printed as `{printed}`, which reads back to a different normal form",
        );
    }
}

/// ★ Word-delimited collections of every size print with a space at each delimiter boundary
/// and read back to the same normal form (WpdaDispatchPartition.v, Section
/// DisplayLexicalBoundaries, `collection_policy_is_glom_safe`). Before 2026-10-21 the
/// delimited arm wrote no space, so `bnames n , n end` printed as `bnamesn , nend` and the
/// empty bag printed as the identifier `bnamesend`
/// (`word_delimited_collection_before_fix_is_not_glom_safe`).
mod word_delimited_read_back {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]
        #[test]
        fn word_delimited_collections_of_any_size_read_back(form in 0usize..3, copies in 0usize..6) {
            mettail_runtime::clear_var_cache();
            let lang = sole_collection_carrier_demo::SoleCollectionCarrierDemoLanguage;
            let (opener, item) = [("bnames", "n"), ("bset", "0"), ("bseq", "0")][form];
            let source = if copies == 0 {
                format!("{opener} end")
            } else {
                format!("{opener} {} end", vec![item; copies].join(", "))
            };
            let first = normalized(&lang, &source);
            let printed = lang.format_term(first.as_ref());
            let second = normalized(&lang, &printed);
            prop_assert!(
                second.term_eq(first.as_ref()),
                "`{}` printed as `{}`, which reads back to a different normal form",
                source,
                printed,
            );
        }
    }
}

/// ★ Normalization keeps the multiplicity of a repeated element in an AC bag, for the
/// cross-category bag `PNames` and for the same-category bag `PPar`
/// (TaggedNormalizationMachine.v, "Fused AC bag frames",
/// `fused_bag_shared_values_have_the_total_multiplicity`). Before 2026-10-20 the fused bag
/// frame reserved `len()` slots, one per copy, while the visit filled one slot per stored
/// entry, so a repeated element failed the assembler's cursor check
/// (`fused_bag_check_before_fails_on_a_repeated_element`).
mod fused_bag_multiplicity {
    use super::*;
    use proptest::prelude::*;

    /// The number of elements between the braces of a printed bag.
    fn element_count(printed: &str, separator: char) -> usize {
        let inner = printed
            .split_once('{')
            .and_then(|(_, rest)| rest.rsplit_once('}'))
            .map(|(inner, _)| inner)
            .expect("a braced bag prints with its braces");
        if inner.trim().is_empty() {
            0
        } else {
            inner.split(separator).count()
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]
        #[test]
        fn arbitrary_bags_keep_distinct_entries_and_multiplicities(
            counts in proptest::collection::vec(0usize..8, 0..8), nested in any::<bool>(),
        ) {
            use super::sole_collection_carrier_demo::{Name, Proc};
            use mettail_runtime::{FreeVar, OrdVar, Var};

            let mut names = Vec::with_capacity(counts.iter().sum());
            let mut processes = Vec::with_capacity(counts.iter().sum());
            for (index, count) in counts.into_iter().enumerate() {
                let name = Name::NVar(OrdVar(Var::Free(FreeVar::fresh_named(format!("name{index}")))));
                let process = Proc::PSeq(vec![Proc::PZero; index]);
                names.extend(std::iter::repeat_n(name, count));
                processes.extend(std::iter::repeat_n(process, count));
            }
            let names = Proc::PNames(names.into_iter().collect());
            let flat = Proc::PPar(processes.into_iter().collect());
            let input_bag = if nested {
                Proc::PPar([flat.clone()].into_iter().collect())
            } else {
                flat.clone()
            };
            let input = Proc::PSeq(vec![Proc::PZero, input_bag, names.clone()]);
            let expected = Proc::PSeq(vec![Proc::PZero, flat, names]);
            prop_assert_eq!(input.normalize(), expected.clone());
            prop_assert_eq!(expected.normalize(), expected);
        }

        #[test]
        fn repeated_bag_elements_keep_their_multiplicity(names in 1usize..8, zeros in 1usize..8) {
            mettail_runtime::clear_var_cache();
            let lang = sole_collection_carrier_demo::SoleCollectionCarrierDemoLanguage;
            let name_bag = format!("names{{{}}}", vec!["n"; names].join(","));
            let zero_bag = format!("par{{{}}}", vec!["0"; zeros].join("|"));
            for (source, separator, copies) in [(&name_bag, ',', names), (&zero_bag, '|', zeros)] {
                let first = normalized(&lang, source);
                let printed = lang.format_term(first.as_ref());
                prop_assert_eq!(
                    element_count(&printed, separator),
                    copies,
                    "`{}` printed as `{}`",
                    source,
                    printed,
                );
                let second = normalized(&lang, &printed);
                prop_assert!(
                    second.term_eq(first.as_ref()),
                    "`{}` printed as `{}`, which reads back to a different normal form",
                    source,
                    printed,
                );
            }
        }
    }
}

/// ★ The new gate changes only the cross-category bags. `PPar` keeps its auto-flatten
/// helper (the positive control, `new_gate_equals_the_old_gate_on_same_category`), a
/// cross-category bag keeps its multiplicity under the direct insert
/// (`bag_arm_preserves_flatness`), and a `HashSet` field keeps set semantics through
/// `HashSetLit`.
#[test]
fn each_sole_carrier_keeps_its_own_semantics() {
    mettail_runtime::clear_var_cache();
    let lang = sole_collection_carrier_demo::SoleCollectionCarrierDemoLanguage;
    let same = |left: &str, right: &str| {
        normalized(&lang, left).term_eq(normalized(&lang, right).as_ref())
    };
    assert!(
        same("par{0|par{0|0}}", "par{0|0|0}"),
        "the same-category bag must still flatten its nested layer",
    );
    assert!(
        !same("names{n,n}", "names{n}"),
        "a cross-category bag must keep the multiplicity of its elements",
    );
    assert!(
        !same("bnames n, n end", "bnames n end"),
        "the BNF cross-category bag must keep the multiplicity of its elements",
    );
    assert!(
        !same("metas{m,m}", "metas{m}"),
        "a closed-data bag must keep the multiplicity of its elements",
    );
    assert!(
        same("nameset{n,n}", "nameset{n}"),
        "a set field must keep at most one copy of each element",
    );
}

/// ★ A fold over a cross-category bag fires. The typed inverse of the AC bag lowering
/// rebuilds its operand with a direct `HashBag::insert` of each `Name`
/// (`every_call_has_an_emitted_well_typed_helper`: no call to a helper that does not exist).
#[test]
fn a_cross_category_bag_fold_fires() {
    mettail_runtime::clear_var_cache();
    let lang = sole_collection_carrier_demo::SoleCollectionCarrierDemoLanguage;
    let term = lang
        .parse_term("nfold(n,n)")
        .unwrap_or_else(|e| panic!("parse failed: {e}"));
    let report =
        sole_collection_carrier_demo::SoleCollectionCarrierDemoLanguage::dovetail_report_for(
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
        vec!["SoleCollectionCarrierDemo::fold::Proc_NameBagFold".to_string()],
        "the cross-category bag fold must fire exactly once; firings={:?}",
        report.rule_firings,
    );

    // ★ POSITIVE CONTROL ON THE SATURATION: a term with no redex fires nothing.
    let inert = lang.parse_term("names{n,n}").expect("parse control");
    let control =
        sole_collection_carrier_demo::SoleCollectionCarrierDemoLanguage::dovetail_report_for(
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

/// ★★ A sole `HashSet` fold parameter is refused, and the refusal names the type. Before
/// 2026-10-20 no `HashSet` field could be declared, so the fold gate's `Opaque` carrier arm
/// was reachable only through `TypeExpr::Map` (FIXTURE 2). `NameBagFold` on the same language
/// is the positive control: the same walk delivers an AC bag fold.
#[test]
fn a_sole_hash_set_fold_parameter_is_declined_naming_its_type() {
    let inventory =
        sole_collection_carrier_demo::SoleCollectionCarrierDemoMetadata.lowering_dispositions();
    assert!(
        !inventory.is_empty(),
        "an empty inventory would make every assertion below vacuous",
    );
    let set_fold = fold_disposition(inventory, "SetFold");
    assert!(
        set_fold.is_declined(),
        "a set has no stored order to invert, so its fold must be declined.{}",
        render(inventory),
    );
    assert!(
        set_fold.detail.contains("HashSet("),
        "the declination must NAME the refusing type.{}",
        render(inventory),
    );
    let bag_fold = fold_disposition(inventory, "NameBagFold");
    assert_eq!(
        bag_fold.outcome,
        LoweringOutcomeKind::Delivered,
        "the AC bag fold on the SAME language is lowered.{}",
        render(inventory),
    );
}

mod data_collection_boundaries {
    use super::sole_collection_carrier_demo::{
        Meta, Proc, SoleCollectionCarrierDemoLanguage, SoleCollectionCarrierDemoTerm,
        SoleCollectionCarrierDemoTermInner,
    };
    use mettail_runtime::{FreeVar, Language, OrdVar, Var};
    use proptest::prelude::*;
    use std::sync::Arc;

    fn collection(form: usize, values: Vec<Meta>) -> Proc {
        match form {
            0 => Proc::PMetas(values.into_iter().collect()),
            1 => Proc::PMetaSet(values.into_iter().collect()),
            2 => Proc::PMetaSeq(values),
            3 => Proc::PMetaBagBnf(values.into_iter().collect()),
            4 => Proc::PMetaSetBnf(values.into_iter().collect()),
            5 => Proc::PMetaSeqBnf(values),
            _ => unreachable!("the strategy selects a declared collection"),
        }
    }

    fn variable(name: &FreeVar<String>) -> Proc {
        Proc::PVar(OrdVar(Var::Free(name.clone())))
    }

    fn nested_bag(copies: usize) -> Proc {
        Proc::PPar(
            [Proc::PPar(vec![Proc::PZero; copies].into_iter().collect())]
                .into_iter()
                .collect(),
        )
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(128))]

        #[test]
        fn normalization_preserves_data_and_transforms_object_children(
            form in 0usize..6, copies in 0usize..8, zeros in 1usize..6,
        ) {
            let nested = nested_bag(zeros);
            let data = collection(form, vec![Meta::MProc(Arc::new(nested.clone())); copies]);
            let flat = Proc::PPar(vec![Proc::PZero; zeros].into_iter().collect());
            prop_assert_ne!(&nested, &flat);
            let term = Proc::PSeq(vec![data.clone(), nested]);
            let expected = Proc::PSeq(vec![data.clone(), flat]);
            prop_assert_eq!(data.normalize(), data);
            prop_assert_eq!(term.normalize(), expected);
            prop_assert_eq!(term.normalize().normalize(), term.normalize());
        }

        #[test]
        fn substitution_preserves_data_identity_and_composition(
            form in 0usize..6, copies in 0usize..8,
        ) {
            let x = FreeVar::fresh_named("x");
            let y = FreeVar::fresh_named("y");
            let data = collection(form, vec![Meta::MProc(Arc::new(variable(&x))); copies]);
            let term = Proc::PSeq(vec![data.clone(), variable(&x)]);
            prop_assert_eq!(term.substitute(&x, &variable(&x)), term.clone());
            prop_assert_eq!(data.substitute(&x, &Proc::PZero), data.clone());
            let expected = Proc::PSeq(vec![data, Proc::PZero]);
            prop_assert_eq!(term.substitute(&x, &Proc::PZero), expected.clone());
            prop_assert_eq!(
                term.substitute(&x, &variable(&y)).substitute(&y, &Proc::PZero),
                expected,
            );
        }

        #[test]
        fn matching_compares_data_exactly_and_keeps_object_bindings(
            form in 0usize..6, copies in 1usize..8,
        ) {
            let x = FreeVar::fresh_named("x");
            let data = collection(form, vec![Meta::MProc(Arc::new(Proc::PZero)); copies]);
            let different = collection(form, vec![Meta::MProc(Arc::new(variable(&x))); copies]);
            prop_assert!(data.match_pattern(&different).is_none());
            let exact = data.match_pattern(&data).expect("equal data must match");
            prop_assert!(exact.proc_bindings.is_empty());
            prop_assert!(exact.name_bindings.is_empty());
            let ground = Proc::PSeq(vec![data.clone(), Proc::PZero]);
            let pattern = Proc::PSeq(vec![data, variable(&x)]);
            let matched = ground.match_pattern(&pattern).expect("the object field must bind");
            prop_assert_eq!(matched.proc_bindings.len(), 1);
            prop_assert_eq!(&matched.proc_bindings[0].1, &Proc::PZero);
        }

        #[test]
        fn all_data_carriers_parse_display_and_read_back(
            form in 0usize..6, choices in proptest::collection::vec(0usize..3, 0..8),
        ) {
            mettail_runtime::clear_var_cache();
            let values = choices.into_iter().map(|choice| match choice {
                0 => Meta::MLit,
                1 => Meta::MOther,
                _ => Meta::MProc(Arc::new(nested_bag(2))),
            }).collect();
            let expected = collection(form, values);
            let source = expected.to_string();
            let language = SoleCollectionCarrierDemoLanguage;
            let parsed = language.parse_term(&source).expect("the displayed collection must parse");
            let expected = SoleCollectionCarrierDemoTerm(
                SoleCollectionCarrierDemoTermInner::Proc(expected),
            );
            prop_assert!(parsed.term_eq(&expected), "different parsed structure for {}", source);
        }
    }
}
