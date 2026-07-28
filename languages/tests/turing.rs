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
//! normal form from `dovetail_normal_term`. The latter returns
//! `Err("… reconstruction … failed (stuck term)")` for every `Turing` term —
//! including a term with no redex at all, e.g. `(halt , <[] | _ | []>)` — so the
//! failure is in the typed e-graph → AST *reconstruction* for this language's
//! shapes (a `Vec(Sym)` collection field plus a native fold whose OUTPUT is a
//! non-native category), not in the reduction. The firing evidence is the
//! stronger conformance statement anyway: it names the transition entry that
//! matched, by the paper's own rule label.
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
/// never reduces at all. Measured, `shift_right([0],1,[1,0])` produces
/// `firings=[]` and leaves `Turing::Tape::shift_right` in the report — so the test
/// passed while the property in its name was FALSE. The honest statement of what it
/// actually checks is below; the property its old name claimed is pinned, with the
/// reason it fails, in [`turing_head_never_moves_because_shift_right_is_declined`].
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

/// ★★ ACCEPTED DEBT, NAMED (Task #94; the substantive repair is Task #101).
///
/// `shift_right` — the declared right-move helper, i.e. the entire mechanism by which
/// this machine's head advances — **is lowered nowhere**, so the tape never changes and
/// every derivation has length ≤ 1. The language named `Turing` cannot compute more than
/// one step.
///
/// # Why, exactly
///
/// `shift_right . l:Vec(Sym), h:Sym, r:Vec(Sym)` is annotated `fold` and carries a real
/// `![…]` body computing the zipper move. Both fold lanes refuse it, independently, for
/// the same reason — its first parameter's type is a `TypeExpr::Collection`, not a
/// `TypeExpr::Base`:
///
/// * the native-eval lane skips the whole `Tape` category, which has no native type;
/// * the typed lane's fold gate (`if !all_simple { continue }`) drops the rule.
///
/// The generated artifact of that refusal was `__is_fold_redex ≡ false` plus an empty
/// dispatch — **a declination rendered as a silent identity**, with no diagnostic
/// anywhere. That silence is what Task #94 removed: the refusal is now a `Declined`
/// entry in the language's lowering-disposition inventory, naming the construct and the
/// parameter whose shape refused it.
///
/// # What this test does, and what it will do next
///
/// It asserts BOTH halves together — the recorded cause and its measured consequence —
/// so they can only move together:
///
///   (a) the inventory records `fold shift_right` as `Declined`, for the collection
///       parameter;
///   (b) the paper's own configuration therefore yields exactly ONE firing, and the
///       reduct still carries an unreduced `shift_right` node.
///
/// The multi-step assertion this SHOULD make was written and run against this tree; it
/// fails with `labels=["Turing::rewrite::D_q0_0"]` — one firing — and, applied directly,
/// `shift_right([0],1,[1,0])` yields `firings=[]`. When Task #101 makes collection
/// parameters foldable, (a) fails FIRST and names the construct that changed, which is
/// the signal to replace this test with that multi-step assertion.
#[test]
fn turing_head_never_moves_because_shift_right_is_declined() {
    use mettail_runtime::{LanguageMetadata, LoweredConstructKind};

    // ── (a) the recorded cause ────────────────────────────────────────────────
    let meta = TuringLanguage.metadata();
    let inventory = meta.lowering_dispositions();
    assert!(
        !inventory.is_empty(),
        "an empty inventory would make every assertion below vacuous",
    );
    let shift_right: Vec<_> = inventory
        .iter()
        .filter(|d| {
            d.construct_kind == LoweredConstructKind::Fold && d.construct == "shift_right"
        })
        .collect();
    assert_eq!(
        shift_right.len(),
        1,
        "`shift_right` must have exactly one disposition; inventory: {inventory:?}",
    );
    assert!(
        shift_right[0].is_declined(),
        "★ Task #101 SIGNAL: `shift_right` is no longer Declined. The head move may now \
         execute — replace this test with the multi-step derivation assertion it \
         describes. Disposition: {}",
        shift_right[0].summary(),
    );
    assert!(
        shift_right[0].detail.contains("`l:Vec(Sym)`"),
        "the declination must name the collection parameter that refused the fold: {}",
        shift_right[0].summary(),
    );

    // ── (b) the measured consequence ──────────────────────────────────────────
    // The paper's own configuration (`omnibus.tex:1949`).
    let (labels, rendered) = firings("(q0 , <[] | 0 | [0,1]>)");
    assert_eq!(
        labels,
        vec!["Turing::rewrite::D_q0_0".to_string()],
        "★ exactly ONE firing: the transition entry fires, and the head move it names \
         does not. This is the whole defect, measured. report: {rendered}",
    );
    assert!(
        !labels.iter().any(|l| l.contains("shift_right")),
        "no fold fires for the head move; report: {rendered}",
    );

    // Applied directly, the declared helper reduces not at all — no firing, and the
    // helper node survives in the report.
    let (bare_labels, bare_rendered) = firings("shift_right([0],1,[1,0])");
    assert!(
        bare_labels.is_empty(),
        "a declined fold fires zero times; report: {bare_rendered}",
    );
    assert!(
        bare_rendered.contains("Turing::Tape::shift_right"),
        "the unreduced helper node survives into the report; report: {bare_rendered}",
    );
}
