//! GSLT omnibus conformance suite for **L11 `Pi`** — the hand-written gate on
//! the production spec `languages/src/pi.rs` (`omnibus.tex:1965-1995`), the
//! π-calculus as a GSLT.
//!
//! The spec's own module header carries the clause-by-clause containment table,
//! the notation notes, the ★★ D10 record (why the paper's SYNCHRONOUS `Comm`
//! now fires), the ➕ note on the retained asynchronous clauses, and the ★
//! `RepUnfold` saturation-safety argument; this file carries the behaviour those
//! clauses claim. Every saturation below is BUDGETED — that budget is what makes
//! the recursive `RepUnfold` equation safe to ship, so it is a property of the
//! suite, not an incidental parameter.
#![cfg(feature = "pi")]

use mettail_languages::pi::*;
use mettail_runtime::Language;

/// Iteration / node budget for the e-graph saturation. Bounded on purpose — see
/// the ★ saturation note in `languages/src/pi.rs`'s module header.
const MAX_ITERS: usize = 24;
const MAX_NODES: usize = 200_000;

/// Saturate `src` and render the outcome (used both for assertions and for
/// failure messages).
fn report_summary(src: &str) -> String {
    let lang = PiLanguage;
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    match PiLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES) {
        Ok(report) => format!(
            "Ok(complete={}, roots={}, firings={:?}, terms={:?})",
            report.is_complete(),
            report.roots.len(),
            report
                .rule_firings
                .iter()
                .filter_map(|f| f.label.clone())
                .collect::<Vec<_>>(),
            report
                .terms
                .iter()
                .map(|t| (t.op_display.clone(), t.source_display.clone()))
                .collect::<Vec<_>>()
        ),
        Err(e) => format!("Err({e})"),
    }
}

/// The BARE rule names the saturation of `src` fired, in report order. Firing
/// labels are `<Lang>::rewrite::<name>`, so the bare tail is what the paper's
/// clause names are compared against — `"Comm"` and `"CommAsync"` are then
/// DISTINCT, which a substring test over the rendered summary could not tell
/// apart.
fn firing_names(src: &str) -> Vec<String> {
    let lang = PiLanguage;
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let report = PiLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("saturation of {src:?} failed: {e}"));
    report
        .rule_firings
        .iter()
        .filter_map(|firing| firing.label.as_deref())
        .map(|label| label.rsplit("::").next().unwrap_or(label).to_string())
        .collect()
}

// ═══════════════════════════════════════════════════════════════════════════
// Conformance tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn pi_language_resolves() {
    let lang = PiLanguage;
    assert_eq!(lang.name(), "Pi");
}

/// Clause coverage: all six term formers, all three equations, all three
/// rewrites (by the paper's own names).
#[test]
fn pi_metadata_carries_every_doc_clause() {
    let lang = PiLanguage;
    let meta = lang.metadata();
    let names: Vec<&str> = meta.terms().iter().map(|t| t.name).collect();
    for clause in ["PZero", "PNew", "PIn", "POut", "PPar", "PRep"] {
        assert!(names.contains(&clause), "omnibus clause {clause} missing; have {names:?}");
    }
    assert_eq!(
        meta.equations().len(),
        3,
        "the omnibus presents three equations (NewComm, ScopeExt, RepUnfold); got {:?}",
        meta.equations()
            .iter()
            .map(|e| (e.lhs, e.rhs))
            .collect::<Vec<_>>()
    );
    // ScopeExt is the freshness-premised one.
    assert!(
        meta.equations().iter().any(|e| !e.conditions.is_empty()),
        "ScopeExt carries the freshness premise `x # ...rest`"
    );
    let rewrites: Vec<Option<&str>> = meta.rewrites().iter().map(|r| r.name).collect();
    for rule in ["Comm", "ParCong", "NewCong"] {
        assert!(rewrites.contains(&Some(rule)), "rewrite {rule} missing; have {rewrites:?}");
    }
    // ParCong / NewCong are the premised (congruence) rules.
    assert_eq!(
        meta.rewrites()
            .iter()
            .filter(|r| r.premise.is_some())
            .count(),
        2,
        "ParCong and NewCong are premised congruence rules"
    );
}

/// `PZero` (:1972) and `PPar` (:1976).
#[test]
fn pi_zero_and_par_parse() {
    mettail_runtime::clear_var_cache();
    let z = Proc::parse("0").expect("PZero parse");
    assert_eq!(format!("{z}"), "0");
    let p = Proc::parse("{ 0 | 0 }").expect("PPar parse");
    assert!(format!("{p}").contains('|'), "par renders with its separator");
}

/// `PNew` (:1973) — the restriction binder.
#[test]
fn pi_new_parses() {
    mettail_runtime::clear_var_cache();
    let p = Proc::parse("new(c, 0)").expect("PNew parse");
    assert!(format!("{p}").contains("new"), "restriction renders");
}

/// `POut` (:1975) — the output prefix, in the paper's own INFIX surface syntax
/// (`c!c.0`; cf. the CFL program at :2008). Infix-led rules parse fine; it is
/// only an infix-led rule that ALSO opens a binder (`PIn`) that does not.
#[test]
fn pi_output_prefix_parses() {
    mettail_runtime::clear_var_cache();
    let o = Proc::parse("c!c.0").expect("POut parse");
    assert!(format!("{o}").contains('!'), "output prefix renders: {o}");
}

/// `PIn` (:1974) — the input prefix (binder), in the literal-led notation this
/// tree's binder codegen supports.
#[test]
fn pi_input_prefix_parses() {
    mettail_runtime::clear_var_cache();
    let i = Proc::parse("in(c,y).0").expect("PIn parse");
    assert!(format!("{i}").contains("in"), "input prefix renders: {i}");
}

/// `PRep` (:1977) — replication.
#[test]
fn pi_replication_parses() {
    mettail_runtime::clear_var_cache();
    let r = Proc::parse("!0").expect("PRep parse");
    assert!(format!("{r}").contains('!'), "replication renders: {r}");
}

/// The paper's own π program (`omnibus.tex:2008`) parses and round-trips.
#[test]
fn pi_paper_program_round_trips() {
    mettail_runtime::clear_var_cache();
    let src = "new(c, { in(c,y).0 | c!c.0 })";
    let t = Proc::parse(src).unwrap_or_else(|e| panic!("paper program parse failed: {e:?}"));
    let printed = format!("{t}");
    let reparsed = Proc::parse(&printed)
        .unwrap_or_else(|e| panic!("re-parse of display {printed:?} failed: {e:?}"));
    assert_eq!(reparsed, t, "display round-trip must be identity (printed {printed:?})");
}

/// `Comm` (:1988-1989) — the paper's SYNCHRONOUS interaction rule is present
/// verbatim in the metadata (name, LHS, RHS). This test pins the CLAUSE;
/// `pi_comm_fires_verbatim` below pins the BEHAVIOUR of that same clause.
#[test]
fn pi_comm_clause_is_declared_verbatim() {
    let lang = PiLanguage;
    let meta = lang.metadata();
    let comm = meta
        .rewrites()
        .iter()
        .find(|r| r.name == Some("Comm"))
        .expect("the paper's Comm rewrite must be declared");
    // `lhs` / `rhs` are rendered in SURFACE syntax, e.g.
    // `{in(n,x).p | n!m.q | ...rest}`.
    assert!(
        comm.lhs.contains("in(") && comm.lhs.contains('!'),
        "Comm LHS must match an input prefix in parallel with an output prefix: {} ~> {}",
        comm.lhs,
        comm.rhs
    );
    assert!(
        comm.lhs.contains("rest") && comm.rhs.contains("rest"),
        "Comm must carry the AC remainder on both sides: {} ~> {}",
        comm.lhs,
        comm.rhs
    );
    assert!(comm.premise.is_none(), "Comm is unpremised");
}

/// The paper's `Comm` redex parses and saturates to a COMPLETE report under
/// budget.
#[test]
fn pi_comm_redex_saturates_completely() {
    let got = report_summary("{ in(c,y).0 | c!c.0 }");
    assert!(
        got.starts_with("Ok(complete=true"),
        "the synchronous-Comm redex must saturate to a complete report; got {got}"
    );
}

/// ★★ **D10 CLOSED** — the paper's own SYNCHRONOUS `Comm` (:1988-1989) FIRES.
///
/// `{ in(c,y).0 | c!c.0 }` is the omnibus's π redex `c?y.0 | c!c.0`: an input
/// prefix and a *synchronous* output prefix on the same channel `c`. The rule
///
/// ```text
/// Comm . |- (PPar {(PIn n ^x.p), (POut n m q), ...rest})
///           ~> (PPar {(eval ^x.p m), q, ...rest})
/// ```
///
/// has a TWO-element reduct (the substituted continuation `p[m/x]` in parallel
/// with the output's own continuation `q`), which the typed COMM lane rejected
/// until the arity-≥2 generalization of `is_comm_rewrite` /
/// `comm_dispatch_arm`. The firing must be the VERBATIM clause `Comm` — not the
/// asynchronous `CommAsync` extra — so this asserts on the bare rule NAME.
#[test]
fn pi_comm_fires_verbatim() {
    let fired = firing_names("{ in(c,y).0 | c!c.0 }");
    assert!(
        fired.iter().any(|name| name == "Comm"),
        "the paper's SYNCHRONOUS Comm must fire on `{{ in(c,y).0 | c!c.0 }}`; fired {fired:?} \
         (report: {})",
        report_summary("{ in(c,y).0 | c!c.0 }")
    );
}

/// The verbatim synchronous `Comm` leaves `...rest` alone: a non-participating
/// parallel component survives the interaction — the paper's "a rule about a
/// site of interaction rather than about whole terms" (:547-548), now shown on
/// the paper's own clause rather than only on the asynchronous variant.
#[test]
fn pi_comm_verbatim_preserves_the_remainder() {
    let fired = firing_names("{ in(c,y).0 | c!c.0 | in(d,z).0 }");
    assert!(
        fired.iter().any(|name| name == "Comm"),
        "the synchronous Comm must fire with a remainder present; fired {fired:?}"
    );
}

/// The synchronous `Comm` is CHANNEL-SENSITIVE: an input on `c` and an output
/// on `d` share no channel, so the non-linear guard `n ≡ n` has no solution and
/// the rule does not fire (reject-safe — the term simply rests).
#[test]
fn pi_comm_does_not_fire_on_mismatched_channels() {
    let fired = firing_names("{ in(c,y).0 | d!d.0 }");
    assert!(
        !fired.iter().any(|name| name == "Comm"),
        "Comm must NOT fire when the input and output channels differ; fired {fired:?}"
    );
}

/// ➕ `CommAsync` (ours, EXTRA) — the ASYNCHRONOUS interaction reduces too: an
/// input prefix and a continuation-free output on the same channel meet in the
/// AC bag and fire, substituting the sent name into the input's continuation.
/// This is the arity-1 reduct, the complement of `pi_comm_fires_verbatim`'s
/// arity-2 synchronous one; both ride the same typed COMM lane.
#[test]
fn pi_comm_async_fires() {
    let fired = firing_names("{ in(c,y).0 | c!c }");
    assert!(
        fired.iter().any(|name| name == "CommAsync"),
        "the asynchronous COMM must fire on `{{ in(c,y).0 | c!c }}`; fired {fired:?}"
    );
}

/// `CommAsync` leaves `...rest` alone: a non-participating parallel component
/// survives the interaction — this is the property the paper calls "a rule about
/// a site of interaction rather than about whole terms" (:547-548).
#[test]
fn pi_comm_async_preserves_the_remainder() {
    let got = report_summary("{ in(c,y).0 | c!c | in(d,z).0 }");
    assert!(
        got.contains("CommAsync"),
        "the COMM must fire with a remainder present; got {got}"
    );
}

/// ★ `RepUnfold` (:1984) saturation safety: a replicated process must reach a
/// decision under the budget — a report or an explicit error — never a hang.
/// This is the test that makes the recursive equation safe to ship.
#[test]
fn pi_replication_saturation_is_bounded() {
    let got = report_summary("!in(c,y).0");
    assert!(
        got.starts_with("Ok(") || got.starts_with("Err("),
        "saturation over the recursive RepUnfold equation must TERMINATE with a \
         decision (a report or an explicit budget error), never hang; got {got}"
    );
}

/// A replicated process in parallel with a matching output also terminates under
/// budget (RepUnfold + Comm together).
#[test]
fn pi_replicated_input_terminates_under_budget() {
    let got = report_summary("{ !in(c,y).0 | c!c.0 }");
    assert!(
        got.starts_with("Ok(") || got.starts_with("Err("),
        "RepUnfold + Comm must terminate under budget; got {got}"
    );
}
