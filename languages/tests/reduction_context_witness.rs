//! **#195 — WITNESS: is a `⇝` REDUCTION propagated into a position that is not a reduction
//! context?**
//!
//! Sibling of `languages/tests/congruence_declaration_witness.rs`, and it answers the question
//! that file could not. That file established, measured, that the Dovetail e-graph reduces a
//! redex inside a `POutput` payload even though `POutput` declares no congruence, and #195 was
//! filed on the reading that this is **over-reach** — the e-graph propagating into 51 undeclared
//! Rholang positions.
//!
//! That reading is only a defect if the propagated relation is one whose closure is *narrower*
//! than "everywhere". The rho calculus specifies **two** relations and they have different
//! closures (`context/rho_calculus_context.md` @ `7fad51db`, Meredith–Radestock):
//!
//! ```text
//! ≡_S   STRUCTURAL EQUIVALENCE  ·  symmetric  ·  an equivalence relation on TERMS
//!       α-equivalence · (P, |, 0) a commutative monoid            (:41-60)
//!       *@P =_S P                                                 (:37)
//!       ⇒ its quotient is a CONGRUENCE ⇒ it holds at EVERY position, by definition
//!
//! ⇝     REDUCTION               ·  directional  ·  closed under PAR **only**
//!       COMM  for(y ⇐ x)P | x!(Q)  ⇝  P{@Q/y}                     (:65-72)
//!       PAR   (P ⇝ P') / (P|Q ⇝ P'|Q)                             (:73-80)
//!       STRUCT reduction modulo ≡_S                                (:81-90)
//!       ⇒ a send's PAYLOAD and a `for` CONTINUATION are NOT reduction contexts
//! ```
//!
//! So `@0!(*@1) → @0!(1)` — the over-reach exhibit — is `≡_S` acting at a `≡_S` position, which
//! is the calculus working. The open question, and the one this file measures, is the other one:
//!
//! > ★★★ **Does a `⇝` rule with no PAR justification propagate into a non-reduction context?**
//!
//! # ⚠ A flaw in the context document, and it is the sentence the whole classification turns on
//!
//! `context/rho_calculus_context.md:37` (@ `7fad51db`) asserts `*@P =_S P` in the *grammar*
//! section. §2 **Equations** (`:41-60`), which introduces `≡_S` as *"the smallest equivalence
//! relation on process terms that satisfies the following"* and then enumerates exactly two
//! items — α-equivalence and the commutative-monoid laws — **omits it**. Read literally, §2's
//! "smallest such relation" therefore does *not* contain `*@P =_S P`, and the classification of
//! every `Exec`-family reduct flips. The document also never states the name-side `@*N =_S N` at
//! all, though the language declares it (`QuoteDrop`, below). Both are documentation defects;
//! neither changes what is measured here, because this file measures the two relations by their
//! **carriers**, not by the document's classification of them.
//!
//! # The two lanes, and why a one-lane experiment would have been vacuous
//!
//! Rholang's two relations are carried by two *different* mechanisms, and no single entry point
//! runs both. This is derived below (`the_two_relations_have_different_carriers`), not assumed:
//!
//! | relation | carrier | entry point | declared where |
//! |---|---|---|---|
//! | `≡_S` + host folds | the Dovetail **e-graph** | `RholangLanguage::dovetail_normal_term` | `equations { }` / `rewrites { }` (`7fad51db:languages/src/rholang.rs:3763`, `:3770`) |
//! | `⇝` (COMM) | `receive::try_comm_rw_proc` | `Proc::try_comm_once` | `logic { }` Datalog rule (`7fad51db:languages/src/rholang.rs:4009`) |
//!
//! ★ Driving the probes through `dovetail_normal_term` **alone** would have produced two nulls
//! and a false verdict, because COMM does not fire on that lane **at any position, including the
//! top level** — see `the_egraph_lane_carries_no_reduction_rule`, whose C-TOP row is the failed
//! positive control that proves it. Those nulls are recorded here and explicitly marked
//! **VACUOUS**. The verdict is delivered on the lane that actually carries `⇝`.
//!
//! # The mechanism, verified at a fixed SHA rather than assumed
//!
//! `7fad51db:languages/src/rholang/receive.rs:1197` opens with
//!
//! ```ignore
//! pub fn try_comm_rw_proc(s: &Proc) -> Option<Proc> {
//!     let Proc::PPar(bag) = s else { return None; };
//! ```
//!
//! then flattens nested `PPar`/`PParInfix` into ONE bag and scans **that bag** for a `PForUser`.
//! `flatten_into`'s catch-all arm (`other => bag.insert(other.clone())`) makes a `POutput` and a
//! `PForUser` **opaque bag elements** — their interiors are never entered. So the selector is
//! structurally confined to the PAR bag, which is `PAR` + the monoid laws of `≡_S` and nothing
//! else. `Proc::try_comm_once` (`7fad51db:languages/src/rholang/runtime.rs:801`) first runs
//! `normalize_send_sugar_canon`, which DOES recurse everywhere (`:621` turns a `PParInfix` into a
//! `PPar` bag) — so the canonicalizer reaches the probe positions even though the selector
//! declines them, and the null is about the RELATION, not about reachability.
//!
//! # ★★★ THE MEASUREMENT — 2026-07-30, on `7fad51db`
//!
//! Every source string below parses and round-trips through `Display` (asserted, not claimed).
//! `R` abbreviates the redex `for(x <- c){*(x)} | c!(p)`, byte-identical in every row.
//!
//! ```text
//! LANE E — dovetail_normal_term (the e-graph: ≡_S, congruence closure, host folds)
//!   S-ZERO         *@(1)                          → 1                      REDUCES   ≡_S alive
//!   S-SEND         @(0)!(*@(1))                   → @0!(1)                 REDUCES   ≡_S reaches a SEND PAYLOAD
//!   S-CONT         for(y <- d){ *@(1) }           → for(y <- d){1}         REDUCES   ≡_S reaches a CONTINUATION
//!   C-TOP          R                              → R                      INERT   ★ positive control FAILS
//!   P1             { @(0)!({R}) | Nil }           → unchanged               INERT   ⇒ VACUOUS
//!   P2             { for(y <- d){{R}} | Nil }     → unchanged               INERT   ⇒ VACUOUS
//!
//! LANE C — Proc::try_comm_once (the ⇝ relation: COMM)
//!   C-TOP          R                              → {*(@p)}                FIRES   ★ instrument alive
//!   C-NESTED       { {R₁|Nil} | {R₂|Nil} }        → {*@p | Nil | Nil}      FIRES   ★ ≡_S assoc IS doing work
//!   C-SEND-SIBLING { @(0)!(Nil) | R }             → {*@p | @0!([])}        FIRES   ★ a send SIBLING does not block
//!   P1             { @(0)!({R}) | Nil }           → <none>                 INERT  ★★ payload is not a context
//!   P1-HOIST       { @(0)!(Nil) | {R} }           → {*@p | @0!([])}        FIRES   ★ the minimal-pair twin
//!   P2             { for(y <- d){{R}} | Nil }     → <none>                 INERT  ★★ continuation is frozen
//!   P2-HOIST       { for(y <- d){Nil} | {R} }     → {*@p | for(y<-d){Nil}} FIRES   ★ the minimal-pair twin
//!
//! LANE C — the THAW LADDER (P2 with the outer receive's partner supplied)
//!   seed   { for(y <- d){{R}} | d!(0) }
//!   step1  {{c!([p]) | for(x <- c){*x}}}   ← the OUTER input fires; R is INTACT, untouched
//!   step2  {*@p}                            ← R fires only NOW, having become a PAR member
//!   step3  <inert>
//! ```
//!
//! ⇒ **BOTH PROBES ARE INERT, MEASURED, AND THE NULLS ARE NOT VACUOUS ON LANE C.** Three
//! positive controls fire on that lane, and `P1`/`P1-HOIST` and `P2`/`P2-HOIST` are minimal
//! pairs: the same redex `R`, differing only in whether it sits *inside* the non-reduction
//! context or *beside* it in the bag. Inside — inert. Beside — fires. The thaw ladder closes it
//! from the other side: the continuation's redex is not merely skipped, it becomes reducible
//! **exactly when** the enclosing input fires, which is `⇝` closed under `PAR` and nothing else.
//!
//! ⇒ **There is no semantic over-reach of `⇝` anywhere.** The e-graph propagates `≡_S`, whose
//! quotient is a congruence and which therefore *must* hold at every position; and it carries no
//! `⇝` rule at all. #195's 51-position gap is a **documentation + disposition** defect, not a
//! narrowing defect, and no narrowing work follows from it.
//!
//! # ⚠ THE RESIDUAL, stated rather than softened
//!
//! One class of **directional, non-`≡_S`** reduction does reach both probe positions on lane E:
//! the host arithmetic folds (`the_residual_directional_host_fold`). `@0!(1 + 2) → @0!(3)` and
//! `for(y <- d){1 + 2} → for(y <- d){3}`. The rho calculus is *silent* on these — its BNF has
//! five process constructors (`:20-40`) and none is arithmetic — so this is not a divergence
//! from the calculus, but it is not `≡_S` either, and it is the only inhabitant of the shape
//! #195 was filed about. A ruling on whether a host fold may fire under a send is a USER
//! decision and is deliberately not made here; this file is the pin so it cannot move silently.

#![cfg(feature = "rholang")]

use mettail_languages::rholang::{Proc, RholangLanguage, RholangTerm, RholangTermInner};
use mettail_runtime::Language;

const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

// ══════════════════════════════════════════════════════════════════════════════════════════
// THE SOURCE SPELLINGS — one table, so no probe can drift away from its control
// ══════════════════════════════════════════════════════════════════════════════════════════
//
// ⚠ These are HEAD spellings, derived by measurement, not inherited. The era spellings
// (`(c?x).{…}`, `c!(p)` from the pre-`f6f6f5db` RhoCalc) do not parse. Every string here is
// asserted to parse AND to round-trip through `Display` by `every_probe_parses_and_roundtrips`,
// so a grammar move REPORTS rather than silently turning a probe into a null.

/// The redex, byte-identical in every probe that contains one.
const R: &str = "for(x <- c){*(x)} | c!(p)";

/// `≡_S` at the two probe positions — the reachability controls.
const S_ZERO: &str = "*@(1)";
const S_SEND: &str = "@(0)!(*@(1))";
const S_CONT: &str = "for(y <- d){ *@(1) }";

/// `⇝` where the calculus says it MUST fire.
const C_TOP: &str = "for(x <- c){*(x)} | c!(p)";
const C_NESTED: &str = "{ { for(x <- c){*(x)} | Nil } | { c!(p) | Nil } }";
const C_SEND_SIBLING: &str = "{ @(0)!(Nil) | for(x <- c){*(x)} | c!(p) }";

/// ★ P1 — COMM under a SEND PAYLOAD, and its one-position-out twin.
const P1: &str = "{ @(0)!({ for(x <- c){*(x)} | c!(p) }) | Nil }";
const P1_HOIST: &str = "{ @(0)!(Nil) | { for(x <- c){*(x)} | c!(p) } }";

/// ★ P2 — COMM under a `for` CONTINUATION, its twin, and its thawed form.
const P2: &str = "{ for(y <- d){ { for(x <- c){*(x)} | c!(p) } } | Nil }";
const P2_HOIST: &str = "{ for(y <- d){ Nil } | { for(x <- c){*(x)} | c!(p) } }";
const P2_THAWED: &str = "{ for(y <- d){ { for(x <- c){*(x)} | c!(p) } } | d!(0) }";

/// The residual: a directional HOST FOLD at the same three positions plus the severed one.
const A_ZERO: &str = "1 + 2";
const A_SEND: &str = "@(0)!(1 + 2)";
const A_CONT: &str = "for(y <- d){ 1 + 2 }";
const A_SEVERED: &str = "[1 + 2, 0]";

const ALL_PROBES: &[(&str, &str)] = &[
    ("R", R),
    ("S-ZERO", S_ZERO),
    ("S-SEND", S_SEND),
    ("S-CONT", S_CONT),
    ("C-TOP", C_TOP),
    ("C-NESTED", C_NESTED),
    ("C-SEND-SIBLING", C_SEND_SIBLING),
    ("P1", P1),
    ("P1-HOIST", P1_HOIST),
    ("P2", P2),
    ("P2-HOIST", P2_HOIST),
    ("P2-THAWED", P2_THAWED),
    ("A-ZERO", A_ZERO),
    ("A-SEND", A_SEND),
    ("A-CONT", A_CONT),
    ("A-SEVERED", A_SEVERED),
];

// ══════════════════════════════════════════════════════════════════════════════════════════
// THE TWO LANES
// ══════════════════════════════════════════════════════════════════════════════════════════

fn parse(src: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"))
}

/// LANE E — the host Dovetail e-graph: `≡_S`, congruence closure, host folds.
/// `Err` (a stuck reconstruction) is reported as "unchanged", which is the conservative reading:
/// it can only ever make a probe look MORE inert, never less.
fn fold(src: &str) -> String {
    let term = RholangTerm(RholangTermInner::Proc(parse(src)));
    match RholangLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES) {
        Ok(nf) => match nf.as_any().downcast_ref::<RholangTerm>().map(|t| &t.0) {
            Some(RholangTermInner::Proc(p)) => format!("{p}"),
            other => panic!("`{src}` normalized to a non-`Proc` term: {other:?}"),
        },
        Err(_) => format!("{}", parse(src)),
    }
}

/// LANE C — the `⇝` relation: one COMM step, or `None`.
fn comm(src: &str) -> Option<String> {
    parse(src).try_comm_once().map(|p| format!("{p}"))
}

fn e_reduces(src: &str) -> bool {
    fold(src) != format!("{}", parse(src))
}

fn c_fires(src: &str) -> bool {
    comm(src).is_some()
}

fn render_e(rows: &[(&str, &str)]) -> String {
    let mut out = String::from("\n  LANE E — dovetail_normal_term\n");
    for (name, src) in rows {
        out.push_str(&format!(
            "    {:<15} `{}`\n{:19}→ `{}`   [{}]\n",
            name,
            parse(src),
            "",
            fold(src),
            if e_reduces(src) { "REDUCES" } else { "INERT" }
        ));
    }
    out
}

fn render_c(rows: &[(&str, &str)]) -> String {
    let mut out = String::from("\n  LANE C — Proc::try_comm_once\n");
    for (name, src) in rows {
        out.push_str(&format!(
            "    {:<15} `{}`\n{:19}→ {}   [{}]\n",
            name,
            parse(src),
            "",
            comm(src).map(|c| format!("`{c}`")).unwrap_or_else(|| "<none>".into()),
            if c_fires(src) { "FIRES" } else { "INERT" }
        ));
    }
    out
}

// ══════════════════════════════════════════════════════════════════════════════════════════
// 0 — the spellings are HEAD's, and they are stable
// ══════════════════════════════════════════════════════════════════════════════════════════

/// ★ A probe that fails to parse is not a null result. This runs FIRST in reading order so no
/// later null can be mistaken for inertness when it is really a grammar move.
#[test]
fn every_probe_parses_and_roundtrips() {
    let mut report = String::new();
    let mut broken = Vec::new();
    for (name, src) in ALL_PROBES {
        mettail_runtime::clear_var_cache();
        match Proc::parse(src) {
            Ok(p) => {
                let disp = format!("{p}");
                mettail_runtime::clear_var_cache();
                match Proc::parse(&disp) {
                    Ok(q) if format!("{q}") == disp => {
                        report.push_str(&format!("    {name:<15} `{src}` → `{disp}`  STABLE\n"))
                    },
                    Ok(q) => {
                        broken.push(*name);
                        report.push_str(&format!(
                            "    {name:<15} `{src}` → `{disp}` → `{q}`  DRIFT\n"
                        ));
                    },
                    Err(e) => {
                        broken.push(*name);
                        report.push_str(&format!(
                            "    {name:<15} `{src}` → `{disp}`  RE-PARSE FAILS: {e:?}\n"
                        ));
                    },
                }
            },
            Err(e) => {
                broken.push(*name);
                report.push_str(&format!("    {name:<15} `{src}`  PARSE FAILS: {e:?}\n"));
            },
        }
    }
    assert!(
        broken.is_empty(),
        "the probe spellings must parse and round-trip through `Display`, or every verdict below \
         is measuring a different term than the one it names. BROKEN: {broken:?}\n{report}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════
// 1 — the two relations have DIFFERENT CARRIERS (derived from the reflected metadata)
// ══════════════════════════════════════════════════════════════════════════════════════════

/// ★ DERIVED, not transcribed. The claim *"COMM is not a declared rewrite, so it never enters the
/// e-graph's rule set"* is the mechanism the whole experiment rests on, so it is measured over
/// the generator's own computed domain — every declared rewrite's user-syntax LHS — rather than
/// asserted from a list somebody must remember to update.
///
/// The two halves are independent and both are needed:
///   1. **no declared rewrite is a receive** — `for` appears in no kernel rewrite's LHS, so the
///      e-graph rule set contains no COMM;
///   2. **COMM nevertheless exists** — `try_comm_once` fires on `C-TOP`.
/// Together: the relation is real and is carried somewhere the e-graph is not.
#[test]
fn the_two_relations_have_different_carriers() {
    let mut kernels = Vec::new();
    let mut congruences = Vec::new();
    for rw in RholangLanguage.metadata().rewrites() {
        if rw.is_congruence() {
            congruences.push(rw.lhs);
        } else {
            kernels.push(rw.lhs);
        }
    }
    let receive_shaped: Vec<_> =
        kernels.iter().chain(congruences.iter()).filter(|lhs| lhs.contains("for")).collect();

    let report = format!(
        "\n  declared rewrites (axis B, what `lower_rewrite` walks): {} = {} kernel + {} congruence\
         \n  kernel LHSs: {kernels:#?}\n  receive-shaped LHSs: {receive_shaped:#?}\n  \
         `try_comm_once` on C-TOP: {:?}\n",
        kernels.len() + congruences.len(),
        kernels.len(),
        congruences.len(),
        comm(C_TOP),
    );

    assert!(
        receive_shaped.is_empty(),
        "★ #195 MECHANISM CHANGE: a declared rewrite now mentions a receive, so COMM may have \
         entered the e-graph rule set. The lane split this whole file rests on has moved and the \
         experiment must be re-derived — do not adjust this assertion to match.{report}"
    );
    assert!(
        c_fires(C_TOP),
        "COMM must fire on `{C_TOP}` through `Proc::try_comm_once`, or the `⇝` instrument is dead \
         and every null below is vacuous.{report}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════
// 2 — LANE E: ≡_S reaches BOTH probe positions; ⇝ is absent from this lane entirely
// ══════════════════════════════════════════════════════════════════════════════════════════

/// The e-graph lane, measured on both relations at both probe positions.
///
/// ★★ The load-bearing row is **C-TOP**: the positive control that a `⇝` step fires on this lane
/// **at the top level, where the calculus unambiguously licenses it**. It does not. That makes
/// the `P1`/`P2` nulls on this lane VACUOUS — they are recorded, and marked as such, precisely so
/// that a future reader cannot cite them as evidence of anything. The verdict is on lane C.
#[test]
fn the_egraph_lane_carries_no_reduction_rule() {
    let table = render_e(&[
        ("S-ZERO", S_ZERO),
        ("S-SEND", S_SEND),
        ("S-CONT", S_CONT),
        ("C-TOP", C_TOP),
        ("P1", P1),
        ("P2", P2),
    ]);

    // ── ≡_S is alive, and reaches BOTH positions the calculus says `⇝` may not ──
    assert!(e_reduces(S_ZERO), "the `Exec` kernel must fire on its own, or nothing here reads.{table}");
    assert!(
        e_reduces(S_SEND),
        "`≡_S` must reach a SEND PAYLOAD, or the P1 null becomes a statement about the POSITION \
         being unreachable rather than about the RELATION.{table}"
    );
    assert!(
        e_reduces(S_CONT),
        "`≡_S` must reach a `for` CONTINUATION, or the P2 null becomes a statement about the \
         POSITION rather than about the RELATION.{table}"
    );

    // ── ★★ and `⇝` is absent from this lane at EVERY position, including the top level ──
    assert!(
        !e_reduces(C_TOP),
        "★★ #195 BEHAVIOUR CHANGE: COMM now fires on the DOVETAIL lane. Since #195 was filed, the \
         e-graph has acquired a `⇝` rule — which is exactly the precondition under which \
         `⇝`-over-reach becomes possible, and it makes the P1/P2 nulls on this lane MEANINGFUL \
         instead of vacuous. Re-run both probes on this lane and re-derive the ruling.{table}"
    );
    assert!(!e_reduces(P1), "recorded, and VACUOUS while C-TOP is inert.{table}");
    assert!(!e_reduces(P2), "recorded, and VACUOUS while C-TOP is inert.{table}");
}

// ══════════════════════════════════════════════════════════════════════════════════════════
// 3 — ★★★ LANE C: the verdict. `⇝` is closed under PAR and under nothing else.
// ══════════════════════════════════════════════════════════════════════════════════════════

/// ★★★ THE DECISIVE TABLE.
///
/// Three positive controls establish that the instrument fires, that `≡_S`'s associativity is
/// doing real work inside it (C-NESTED: the input and the output are in *different* nested bags
/// and only the monoid laws bring them adjacent), and that a `POutput` sibling in the bag does
/// not block it (C-SEND-SIBLING — so a null at P1 is not "a send was present").
///
/// Then two MINIMAL PAIRS. `P1` and `P1-HOIST` contain the byte-identical redex `R`; they differ
/// in exactly one thing — whether `R` is *inside* the send payload or *beside* the send in the
/// bag. `P2`/`P2-HOIST` likewise for a `for` continuation. Inside: inert. Beside: fires.
#[test]
fn the_comm_relation_is_closed_under_par_and_nothing_else() {
    let table = render_c(&[
        ("C-TOP", C_TOP),
        ("C-NESTED", C_NESTED),
        ("C-SEND-SIBLING", C_SEND_SIBLING),
        ("P1", P1),
        ("P1-HOIST", P1_HOIST),
        ("P2", P2),
        ("P2-HOIST", P2_HOIST),
    ]);

    // ── the instrument fires, and `≡_S` is doing work inside it ──
    assert!(c_fires(C_TOP), "COMM must fire at top level.{table}");
    assert!(
        c_fires(C_NESTED),
        "COMM must fire when only `≡_S` ASSOCIATIVITY brings the input and output adjacent — \
         otherwise the P1/P2 nulls could be explained by the selector being unable to see nested \
         structure at all, rather than by the relation's closure.{table}"
    );
    assert!(
        c_fires(C_SEND_SIBLING),
        "COMM must fire with a `POutput` sibling in the same bag, or the P1 null could be read as \
         'a send blocks the step' rather than 'a payload is not a reduction context'.{table}"
    );

    // ── ★★ P1 — a send PAYLOAD is not a reduction context ──
    assert!(
        !c_fires(P1),
        "★★★ #195 REFUTED: a COMM fired inside a SEND PAYLOAD. The rho calculus closes `⇝` under \
         PAR only (`context/rho_calculus_context.md:73-80` @ `7fad51db`), so a payload is not a \
         reduction context and this is a GENUINE OVER-REACH of the reduction relation. The \
         reclassification recommendation does NOT survive; #195 needs real narrowing on the `⇝` \
         lane. Do not adjust this assertion to match.{table}"
    );
    assert!(
        c_fires(P1_HOIST),
        "the P1 minimal-pair twin must fire. The redex is byte-identical to P1's and differs only \
         by sitting BESIDE the send instead of inside it; if it does not fire, P1's null says \
         nothing about position.{table}"
    );

    // ── ★★ P2 — a `for` CONTINUATION is not a reduction context ──
    assert!(
        !c_fires(P2),
        "★★★ #195 REFUTED: a COMM fired inside a `for` CONTINUATION, which is frozen until the \
         enclosing input fires. Same consequence as the P1 arm: genuine `⇝` over-reach, and the \
         reclassification recommendation does not survive.{table}"
    );
    assert!(
        c_fires(P2_HOIST),
        "the P2 minimal-pair twin must fire, or P2's null says nothing about position.{table}"
    );
}

/// The other side of the P2 null: the continuation's redex is not *skipped*, it is **frozen**,
/// and it becomes reducible exactly when the enclosing input fires. Two steps, then inert.
#[test]
fn a_frozen_continuation_thaws_exactly_when_its_input_fires() {
    let mut cur = parse(P2_THAWED);
    let mut steps = Vec::new();
    for _ in 0..8 {
        match cur.try_comm_once() {
            Some(next) => {
                steps.push(format!("{next}"));
                cur = next;
            },
            None => break,
        }
    }
    let ladder = format!(
        "\n  seed  `{}`\n{}",
        parse(P2_THAWED),
        steps
            .iter()
            .enumerate()
            .map(|(i, s)| format!("  step{} `{s}`\n", i + 1))
            .collect::<String>()
    );

    assert!(
        !c_fires(P2),
        "the un-thawed twin must still be inert, or this ladder proves nothing.{ladder}"
    );
    assert_eq!(
        steps.len(),
        2,
        "the thawed form must take EXACTLY two COMM steps: the outer input, then the continuation's \
         redex which the outer step released. A different count means the freeze/thaw structure \
         moved.{ladder}"
    );
    // Step 1 fired the OUTER input and left `R` untouched — both halves of the inner redex are
    // still present and un-substituted.
    assert!(
        steps[0].contains("for(x <- c)") && steps[0].contains("c!("),
        "after the outer input fires, the continuation's redex must still be INTACT — that is what \
         distinguishes 'frozen, then released' from 'reduced under the binder all along'.{ladder}"
    );
    assert!(
        !steps[1].contains("for(x <- c)"),
        "the second step must consume the released redex.{ladder}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════
// 4 — the SECOND question: does `QuoteDrop` lower its EXPANDING reverse orientation?
// ══════════════════════════════════════════════════════════════════════════════════════════

/// ★ Rholang's `equations { }` block (`7fad51db:languages/src/rholang.rs:3763-3768`) declares
/// exactly two equations:
///
/// ```ignore
/// QuoteDrop . |- (NQuote (PDrop N)) = N ;                 // @*N  =  N
/// Extrude   . xs.*map(|x| x # ...rest)
///     |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest})) ;
/// ```
///
/// `lower_equation` (`7fad51db:macros/src/gen/runtime/dovetail_report.rs:1545`) emits *"up to
/// TWO"* `RewriteRule`s per equation, and for a cancellation pair the reverse direction is
/// **expanding** — the symmetric expansion `git show 632ced2a:docs/design/exploring/
/// exec-eq-infinite-loop.md` diagnosed and `86483026` suppressed in the Ascent era. So: is it
/// emitted here?
///
/// **Measured: NO. `QuoteDrop` lowers to exactly ONE rule.** The reverse orientation's LHS would
/// be the bare metavariable `N`, and `:1627`'s guard elides it — *"the RHS is a bare
/// metavariable, so the reversed rule would match every e-class"*. `Extrude` lowers to **zero**:
/// its freshness premise is unsupported (`:1563`), and that kills both orientations together.
/// The `equations { }` block therefore contributes exactly **one** rule to the e-graph, and the
/// expanding direction of the cancellation pair is not in it. There is nothing to inflate.
///
/// ⚠ Two corrections this measurement forces on the surrounding record:
///   * `P → *@P` is **not** `QuoteDrop`'s reverse. `QuoteDrop` is the NAME-side `@*N = N`; the
///     process-side `*@P ~> P` is the `Exec` family in `rewrites { }` (`:3774-3776`), a
///     one-directional `~>` that `lower_equation` never sees and that has no reverse to suppress.
///   * `7fad51db:languages/tests/rholang_tests.rs:264` states *"Dovetail **does** carry the
///     [`Extrude`] equation, but it only ever reports ONE extracted normal form"* — offering the
///     single-normal-form projection as the reason scope extrusion never reaches COMM. Measured,
///     the reason is upstream of that: `Extrude` is `Declined` ("has side conditions"), so it
///     contributes **no e-graph rule at all** and there is no extruded form to project.
#[test]
fn quotedrop_lowers_to_exactly_one_rule_and_the_expanding_reverse_is_suppressed() {
    let equations: Vec<_> = RholangLanguage
        .metadata()
        .lowering_dispositions()
        .iter()
        .filter(|d| d.construct_kind == mettail_runtime::LoweredConstructKind::Equation)
        .collect();

    let report = equations
        .iter()
        .map(|d| {
            format!(
                "    {:<12} origin={:?} outcome={:<10} detail: {}\n",
                d.construct,
                d.origin,
                d.outcome.as_str(),
                d.detail
            )
        })
        .collect::<String>();
    let report = format!("\n  ── every EQUATION disposition ──\n{report}");

    let delivered: Vec<_> = equations
        .iter()
        .filter(|d| d.outcome == mettail_runtime::LoweringOutcomeKind::Delivered)
        .collect();
    assert_eq!(
        delivered.len(),
        1,
        "the `equations {{ }}` block must contribute exactly ONE rule to the e-graph. More than \
         one means an orientation that was suppressed or declined is now being emitted — and for \
         a cancellation pair the new one is the EXPANDING direction, which is a saturation \
         hazard.{report}"
    );
    assert!(
        delivered[0].detail.ends_with("::forward") && delivered[0].construct == "QuoteDrop",
        "the single delivered orientation must be `QuoteDrop`'s FORWARD (contracting) one.{report}"
    );

    // ★ DERIVED, not transcribed: NO reverse orientation of ANY equation may be Delivered.
    // Stated over the computed domain so a newly-added equation is covered without anyone
    // remembering to extend a list.
    let delivered_reverses: Vec<_> =
        delivered.iter().filter(|d| d.detail.contains("::reverse")).collect();
    assert!(
        delivered_reverses.is_empty(),
        "an EXPANDING reverse orientation is now emitted into the e-graph: {delivered_reverses:#?}\
         {report}"
    );

    // And the firing census confirms it from the runtime side rather than the metadata side.
    let term = RholangTerm(RholangTermInner::Proc(parse(S_SEND)));
    let run = RholangLanguage::dovetail_report_for(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
        .expect("`@(0)!(*@(1))` must produce a Dovetail report");
    let labels: Vec<String> =
        run.rule_firings.iter().filter_map(|f| f.label.clone()).collect();
    assert!(
        !labels.iter().any(|l| l.contains("::reverse")),
        "a `::reverse` orientation FIRED during saturation of `{S_SEND}`: {labels:#?}{report}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════
// 5 — ⚠ THE RESIDUAL: the one directional relation that DOES reach both positions
// ══════════════════════════════════════════════════════════════════════════════════════════

/// The honest remainder. Host arithmetic folds are **directional** (`1 + 2 → 3`, never the
/// reverse) and therefore are not `≡_S` — yet they fire inside a send payload and inside a `for`
/// continuation, the two positions `⇝` is forbidden from entering.
///
/// This is **not** a divergence from the rho calculus: the calculus's BNF
/// (`context/rho_calculus_context.md:20-40` @ `7fad51db`) has five process constructors and none
/// of them is arithmetic, so it makes no claim either way. But it is the only inhabitant of the
/// shape #195 was filed about, so it is pinned here rather than left for someone to rediscover.
///
/// `A-SEVERED` is the control that keeps the row informative: a `![Vec<Proc>] as List` payload
/// lowers to ONE opaque leaf, so its elements are not e-graph children and the fold cannot reach
/// them — the same under-reach `congruence_declaration_witness.rs`'s SEVERED probe pins.
#[test]
fn the_residual_directional_host_fold_reaches_both_forbidden_positions() {
    let table = render_e(&[
        ("A-ZERO", A_ZERO),
        ("A-SEND", A_SEND),
        ("A-CONT", A_CONT),
        ("A-SEVERED", A_SEVERED),
    ]);
    assert!(e_reduces(A_ZERO), "the arithmetic fold must fire on its own.{table}");
    assert!(
        e_reduces(A_SEND),
        "★ RESIDUAL CHANGE: a directional host fold no longer fires inside a send payload. That \
         is the direction #195 pointed at — record it as a fix, do not silently agree.{table}"
    );
    assert!(
        e_reduces(A_CONT),
        "★ RESIDUAL CHANGE: a directional host fold no longer fires inside a `for` continuation. \
         Record it; do not silently agree.{table}"
    );
    assert!(
        !e_reduces(A_SEVERED),
        "a fold reached inside a `Vec`-carrier payload. Either the carrier classification moved or \
         an element position became an e-graph child.{table}"
    );
}
