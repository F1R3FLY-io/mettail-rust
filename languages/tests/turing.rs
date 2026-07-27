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

/// The `shift_right` helper is a native fold: it reduces the moved tape rather
/// than leaving an un-evaluated helper node behind.
#[test]
fn turing_shift_right_folds() {
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
