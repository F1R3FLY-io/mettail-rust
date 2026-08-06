//! GSLT omnibus conformance suite for **L9 `Turing`** — the hand-written gate on
//! the production spec `languages/src/turing.rs` (`omnibus.tex:1900-1936`), a
//! single-tape Turing machine as a GSLT.
//!
//! The spec's own module header carries the clause-by-clause containment table,
//! the notation notes, the ★ forced delta on native literals in patterns, and
//! the `shift_right` derivation; this file carries the behaviour those clauses
//! claim.
//!
//! ## Why the dynamics are proven from `dovetail_report_for`
//!
//! The tests below assert RULE-FIRING evidence from
//! `TuringLanguage::dovetail_report_for` rather than comparing a reconstructed
//! normal form from `dovetail_normal_term`. The firing evidence is the stronger
//! conformance statement: it names the transition entry that matched, by the
//! paper's own rule label, and it names the head move that followed.
//!
//! ⚠ RECORD CORRECTED (Task #101). This header used to say that
//! `dovetail_normal_term` returns `Err("… reconstruction … failed (stuck
//! term)")` for EVERY `Turing` term — including one with no redex at all, e.g.
//! `(halt , <[] | _ | []>)` — and attributed that to the typed e-graph → AST
//! *reconstruction* for this language's shapes: a `Vec(Sym)` collection field
//! plus a native fold whose OUTPUT is a non-native category. The first half of
//! that diagnosis was exactly right and is now repaired: a `Vec` field lowers to
//! the labelled, losslessly invertible `FieldSeq<Sym>` leaf, so
//! `__mettail_dovetail_build_tape_d` has a `Tp` arm and configurations
//! reconstruct. [`turing_terms_now_reconstruct_because_vec_fields_are_invertible`]
//! pins that, so the claim cannot go stale again unobserved.
//!
//! Firings remain the primary evidence for a different and still-true reason:
//! `Cf` is not a redex head, so a rewritten configuration is not *cheaper* than
//! its predecessor and funded 1-best extraction may return either. Reduction is
//! what fired, not what was extracted.
#![cfg(feature = "turing")]

use mettail_languages::turing::*;
use mettail_runtime::Language;

/// Iteration / node budget for the e-graph saturation. Bounded on purpose: a
/// budget means a non-converging machine surfaces as a limit error, never as a
/// hung test binary.
const MAX_ITERS: usize = 32;
const MAX_NODES: usize = 200_000;

/// Saturate `src` in the Dovetail e-graph and return (fired rule labels, a
/// rendering of the whole report for failure messages).
fn firings(src: &str) -> (Vec<String>, String) {
    let lang = TuringLanguage;
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let report = TuringLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_report_for({src:?}) returned Err: {e}"));
    let labels: Vec<String> = report
        .rule_firings
        .iter()
        .filter_map(|f| f.label.clone())
        .collect();
    let rendered = format!(
        "complete={} roots={} firings={:?} terms={:?}",
        report.is_complete(),
        report.roots.len(),
        report.rule_firings,
        report
            .terms
            .iter()
            .map(|t| (t.op_display.clone(), t.source_display.clone()))
            .collect::<Vec<_>>()
    );
    (labels, rendered)
}

// ═══════════════════════════════════════════════════════════════════════════
// Conformance tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn turing_language_resolves() {
    let lang = TuringLanguage;
    assert_eq!(lang.name(), "Turing");
}

/// Clause coverage: every `terms` production and both transition entries are in
/// metadata under the paper's own names.
#[test]
fn turing_metadata_carries_every_doc_clause() {
    let lang = TuringLanguage;
    let meta = lang.metadata();
    let names: Vec<&str> = meta.terms().iter().map(|t| t.name).collect();
    for clause in ["Blank", "Zero", "One", "Halt", "Q", "Tp", "Cf"] {
        assert!(names.contains(&clause), "omnibus clause {clause} missing; have {names:?}");
    }
    let rewrites: Vec<Option<&str>> = meta.rewrites().iter().map(|r| r.name).collect();
    for entry in ["D_q0_0", "D_q0_1"] {
        assert!(
            rewrites.contains(&Some(entry)),
            "transition entry {entry} missing; have {rewrites:?}"
        );
    }
    assert!(meta.equations().is_empty(), "the omnibus Turing has `equations {{ }}` empty");
}

/// `Blank` / `Zero` / `One` (:1912-1914).
#[test]
fn turing_symbols_parse() {
    mettail_runtime::clear_var_cache();
    for src in ["_", "0", "1"] {
        let s = Sym::parse(src).unwrap_or_else(|e| panic!("Sym parse of {src:?}: {e:?}"));
        assert_eq!(format!("{s}"), src);
    }
}

/// `Halt` (:1916) and `Q . n:UInt32` (:1917) — both State productions.
#[test]
fn turing_states_parse() {
    mettail_runtime::clear_var_cache();
    let h = State::parse("halt").expect("Halt parse");
    assert_eq!(format!("{h}"), "halt");
    // The paper's indexed state former, verbatim: `"q" n` over a UInt32 literal.
    let q = State::parse("q 7u32").expect("Q (indexed state) parse");
    assert!(format!("{q}").contains('7'), "index preserved: {q}");
    // The nullary machine-state constants used by the transition table.
    for src in ["q0", "q1"] {
        let s = State::parse(src).unwrap_or_else(|e| panic!("State parse of {src:?}: {e:?}"));
        assert_eq!(format!("{s}"), src);
    }
}

/// `Tp` (:1920) — the zipper tape, with an empty and a non-empty context.
#[test]
fn turing_tape_parses() {
    mettail_runtime::clear_var_cache();
    let t = Tape::parse("<[] | 0 | [0,1]>").expect("Tp parse (empty left context)");
    let shown = format!("{t}");
    assert!(shown.contains('|'), "tape renders with the zipper bars: {shown:?}");
    let t2 = Tape::parse("<[1,_] | 1 | []>").expect("Tp parse (empty right context)");
    assert!(!format!("{t2}").is_empty());
}

/// `Cf` (:1922) — a configuration, exactly as the paper's CFL program writes it
/// (`omnibus.tex:1949`).
#[test]
fn turing_configuration_parses_and_round_trips() {
    mettail_runtime::clear_var_cache();
    let src = "(q0 , <[] | 0 | [0,1]>)";
    let c = Config::parse(src).unwrap_or_else(|e| panic!("Cf parse failed: {e:?}"));
    let printed = format!("{c}");
    let reparsed = Config::parse(&printed)
        .unwrap_or_else(|e| panic!("re-parse of display {printed:?} failed: {e:?}"));
    assert_eq!(reparsed, c, "display round-trip must be identity (printed {printed:?})");
}

/// `D_q0_0` (:1930-1931) — the write-1-move-right entry FIRES on the paper's own
/// configuration (`omnibus.tex:1949`): reading `0` in state `q0` with left `[]`
/// and right `[0,1]`.
#[test]
fn turing_transition_d_q0_0_fires() {
    let (labels, rendered) = firings("(q0 , <[] | 0 | [0,1]>)");
    assert!(
        labels.iter().any(|l| l == "Turing::rewrite::D_q0_0"),
        "the write-1-move-right transition must fire; report: {rendered}"
    );
}

/// `D_q0_1` (:1932-1933) — reading `1` in `q0` halts, leaving the tape alone.
#[test]
fn turing_transition_d_q0_1_fires() {
    let (labels, rendered) = firings("(q0 , <[0] | 1 | [1]>)");
    assert!(
        labels.iter().any(|l| l == "Turing::rewrite::D_q0_1"),
        "the halt transition must fire; report: {rendered}"
    );
}

/// A configuration with no matching table entry is already a normal form: the
/// machine is stuck, which is exactly the paper's point about non-interactivity
/// (:692-720, :1938-1942).
#[test]
fn turing_halted_configuration_is_a_normal_form() {
    let (labels, rendered) = firings("(halt , <[] | _ | []>)");
    assert!(
        labels.is_empty(),
        "a halted configuration matches no transition, so nothing may fire; report: {rendered}"
    );
}

/// Applying the helper to a bare tape matches no TRANSITION entry — the transition
/// table is keyed on `Cf`, and a bare `Tape` is not a configuration.
///
/// ⚠ RENAMED (Task #94, 2026-07-28). This test was called `turing_shift_right_folds`
/// and its doc-comment claimed "it reduces the moved tape rather than leaving an
/// un-evaluated helper node behind". It asserted neither of those things: it checked
/// `complete=true` and that no `D_q0` entry fired, both of which hold of a helper that
/// never reduces at all. Measured then, `shift_right([0],1,[1,0])` produced
/// `firings=[]` and left `Turing::Tape::shift_right` in the report — so the test
/// passed while the property in its name was FALSE. This is the honest statement of
/// what it actually checks, and the name says so.
///
/// ★ The property the OLD name claimed is now TRUE, and is asserted where it belongs —
/// [`turing_head_moves_because_shift_right_folds`], which reads the same
/// `shift_right([0],1,[1,0])` report and requires the fold to fire, the helper node to
/// be gone, and the computed tape to be present. This test deliberately does NOT absorb
/// that claim: its subject is the transition table's keying on `Cf`, and a test whose
/// name and body describe different properties is the exact shape #94 removed here.
#[test]
fn turing_bare_tape_matches_no_transition_entry() {
    let (labels, rendered) = firings("shift_right([0],1,[1,0])");
    assert!(
        rendered.contains("complete=true"),
        "the helper must reduce to a complete report; got {rendered}"
    );
    assert!(
        !labels.iter().any(|l| l.contains("D_q0")),
        "no transition applies to a bare tape; report: {rendered}"
    );
}

/// ★★ THE REPAIR, MEASURED (Task #101). Retires
/// `turing_head_never_moves_because_shift_right_is_declined`, which pinned the defect this
/// asserts the absence of. The old test is named here rather than deleted silently: it asserted
/// BOTH the recorded cause (`shift_right` is `Declined`) and its measured consequence (exactly
/// ONE firing, and an unreduced helper node left in the report), so that a repair would fail
/// its CAUSE assertion first. Run unchanged against the repaired tree it did exactly that —
/// `turing.rs:261`, "★ Task #101 SIGNAL: `shift_right` is no longer Declined … Disposition:
/// fold `shift_right` :: Delivered :: Turing::fold::Tape_shift_right" — and not at either
/// consequence assertion, which is the evidence that the two halves moved together.
///
/// # What moved
///
/// `shift_right . l:Vec(Sym), h:Sym, r:Vec(Sym)` is annotated `fold` and carries a real `![…]`
/// body computing the zipper move. The typed fold gate used to drop it because its first
/// parameter's type is a `TypeExpr::Collection`, not a `TypeExpr::Base`: a fold operand is
/// bound by INVERTING its lowered derivation child, and a `Vec` field lowered to
/// `FieldOpaque(format!("{:?}", …))`, which has no inverse. Task #101 gave the ordered
/// container a carrier that does — the labelled `FieldSeq<Sym>(Vec<Sym>)` leaf, carrying the
/// whole vector verbatim, with the total inverse `__mettail_dovetail_build_seq_sym_d` — so the
/// parameter now binds like any other.
///
/// # The honest statement of the change
///
/// "every derivation has length ≤ 1" becomes **"length 2, and the second firing is the head
/// move."** Two, not more, because the production transition table has entries only from `q0`
/// and `D_q0_0` lands in `q1`: the maximal derivation from the paper's own configuration is
/// exactly `D_q0_0` followed by the `shift_right` fold it names. A machine that takes THREE or
/// more head moves needs more table entries, which is a change to the theory rather than to
/// the lowering; that is `TuringLoop` in `languages/tests/collection_fold_carriers.rs`, hosted
/// in the test so this production spec is untouched.
///
/// ⚠ Why the assertions are firings and report terms rather than a whole-configuration normal
/// form: `Cf` is not a redex head. The `redex_heads` invariant deliberately admits only heads
/// whose presence PROVES an un-fired reduction (a fold constructor, a β-redex head, a COMM
/// binder, a consumed AC element) — the measured 2026-07-25 decision recorded at
/// `macros/src/gen/runtime/dovetail_report/typed_report.rs`'s `generate_helpers`. So
/// `Cf(Q1, Tp …)` is not cheaper than `Cf(Q0, Tp …)`, funded 1-best extraction may return
/// either, and the reduction statement lives in the firing evidence. Applied DIRECTLY, the
/// helper has no such competitor, and the assertions below read its computed result straight
/// out of the report.
#[test]
fn turing_head_moves_because_shift_right_folds() {
    use mettail_runtime::{LanguageMetadata, LoweredConstructKind, LoweringOutcomeKind};

    // ── (a) the recorded cause: the fold is DELIVERED, and it states its own label ─────────
    let meta = TuringLanguage.metadata();
    let inventory = meta.lowering_dispositions();
    assert!(
        !inventory.is_empty(),
        "an empty inventory would make every assertion below vacuous",
    );
    let shift_right: Vec<_> = inventory
        .iter()
        .filter(|d| d.construct_kind == LoweredConstructKind::Fold && d.construct == "shift_right")
        .collect();
    assert_eq!(
        shift_right.len(),
        1,
        "`shift_right` must have exactly one disposition; inventory: {inventory:?}",
    );
    assert_eq!(
        shift_right[0].outcome,
        LoweringOutcomeKind::Delivered,
        "the head move must be lowered, not declined: {}",
        shift_right[0].summary(),
    );
    assert_eq!(
        shift_right[0].detail,
        "Turing::fold::Tape_shift_right",
        "a Delivered disposition carries the label of the rule it emitted, and that label is \
         what the firing evidence below is matched against: {}",
        shift_right[0].summary(),
    );

    // ── (b) the measured consequence: TWO firings, the second one the head move ────────────
    // The paper's own configuration (`omnibus.tex:1949`).
    let (labels, rendered) = firings("(q0 , <[] | 0 | [0,1]>)");
    assert_eq!(
        labels,
        vec![
            "Turing::rewrite::D_q0_0".to_string(),
            "Turing::fold::Tape_shift_right".to_string(),
        ],
        "★ exactly TWO firings, in order: the transition entry fires, and the head move it \
         names fires after it. This inverts the measured `labels=[\"Turing::rewrite::D_q0_0\"]` \
         of the defect. report: {rendered}",
    );

    // ── (c) the head move APPLIED: the computed tape, and no surviving helper node ─────────
    // `shift_right([0], 1, [1,0])` ≙ `Tp( 1:[0], head([1,0]), tail([1,0]) )`
    //                              =  `Tp([One, Zero], One, [Zero])`.
    // Both halves of the report invert the defect's `firings=[] terms=[("Turing::Tape::
    // shift_right", …)]`: the fold fires, and 1-best extraction now prefers the computed `Tp`
    // (weight 1) over the redex it replaced (weight 100), so the helper is gone.
    let (bare_labels, bare_rendered) = firings("shift_right([0],1,[1,0])");
    assert_eq!(
        bare_labels,
        vec!["Turing::fold::Tape_shift_right".to_string()],
        "the declared helper fires exactly once when applied directly; report: {bare_rendered}",
    );
    assert!(
        !bare_rendered.contains("Turing::Tape::shift_right"),
        "the unreduced helper node must NOT survive into the report — the fold replaced it; \
         report: {bare_rendered}",
    );
    assert!(
        bare_rendered.contains("Turing::Tape::Tp"),
        "the report must carry the MOVED TAPE, a `Tp` the input never contained; \
         report: {bare_rendered}",
    );
    // ★ The tape's CONTENTS, not merely its constructor. The ordered carrier renders its whole
    // payload (`<field-seq-Sym>([…])`), so the moved zipper is readable straight off the
    // report: left context `[1,0]` (the written `1` pushed in front of the old `[0]`), head
    // `1` (the old right-context head), right context `[0]` (its tail).
    for expected in ["<field-seq-Sym>([One, Zero])", "Turing::Sym::One", "<field-seq-Sym>([Zero])"]
    {
        assert!(
            bare_rendered.contains(expected),
            "the computed tape must show {expected} — the head move is COMPUTED here, never \
             transcribed; report: {bare_rendered}",
        );
    }

    // ── (d) THE CONTROL. A halted configuration still matches nothing, so (b) and (c) are not
    //        an engine that fires rules indiscriminately.
    let (halted, halted_rendered) = firings("(halt , <[] | _ | []>)");
    assert!(
        halted.is_empty(),
        "a halted configuration matches no transition and no fold; report: {halted_rendered}",
    );
}

/// ★ (Task #101) Reconstruction of a `Vec`-field constructor, which was impossible before.
///
/// This file's header used to record that `dovetail_normal_term` answered
/// `Err("… reconstruction … failed (stuck term)")` for EVERY `Turing` term, including one with
/// no redex at all, because `Tp`'s `l`/`r` fields are `Vec(Sym)` collections whose lowered
/// child was a lossy `FieldOpaque` sentinel — so `__mettail_dovetail_build_tape_d` had no `Tp`
/// arm and every reconstruction rooted at a tape returned `None`.
///
/// The ordered carrier makes those fields invertible, so the reconstructor gains its `Tp` arm
/// and a whole configuration reads back. Asserting it here is what keeps the header's claim
/// from silently going stale a second time.
#[test]
fn turing_terms_now_reconstruct_because_vec_fields_are_invertible() {
    mettail_runtime::clear_var_cache();
    let term = TuringLanguage
        .parse_term("(q0 , <[] | 0 | [0,1]>)")
        .unwrap_or_else(|e| panic!("parse failed: {e}"));
    let normal = TuringLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| {
            panic!("reconstruction must now succeed for a `Vec`-field constructor; got Err({e})")
        });
    let shown = format!("{normal}");
    assert!(
        shown.contains('|'),
        "the reconstructed configuration renders its zipper tape: {shown:?}",
    );
    // ★ The head move's own result, reconstructed. `Cf` is not a redex head (see
    // `turing_head_moves_because_shift_right_folds`), so a rewritten CONFIGURATION is not
    // cheaper than its predecessor and 1-best extraction may return either; a bare helper
    // application has no such competitor, so its normal form is exactly the moved tape.
    let helper = TuringLanguage
        .parse_term("(halt , shift_right([0],1,[1,0]))")
        .unwrap_or_else(|e| panic!("helper parse failed: {e}"));
    let moved = TuringLanguage::dovetail_normal_term(helper.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("the moved tape must reconstruct; got Err({e})"));
    assert_eq!(
        format!("{moved}"),
        "(halt , <[1 , 0]|1|[0]>)",
        "the reconstructed normal form is the COMPUTED zipper move: write `1` at the head \
         cell, then step right",
    );
}
