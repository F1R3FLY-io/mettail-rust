//! **#140 — WITNESS, not argument: is a declared congruence load-bearing on the lane that
//! declines to emit it?**
//!
//! `macros/src/gen/runtime/dovetail_report.rs:1679` returns
//! `DeliveredElsewhere { EGraphCongruenceClosure }` for **every** rule satisfying
//! `is_congruence_rule()`, on the stated grounds that congruence closure already propagates the
//! kernel rewrite's child-e-class merge through every enclosing e-node.
//!
//! `macros/docs/codegen/congruence-closure.md` states the opposite as a deliberate feature:
//!
//! > **Critical distinction**: Rewrite congruences are NOT auto-generated. Users explicitly
//! > control where rewrites propagate (e.g., rewrites through `PPar` **but not `POutput`**).
//!
//! Exactly one of those can be true, and the difference is **measurable**: reduce a redex under a
//! constructor that DECLARES a congruence, and the same redex under a constructor that does NOT.
//! If they behave identically, the declaration is inert on this lane.
//!
//! The kernel redex used throughout is `Exec . |- (PDrop (NQuote P)) ~> P` — Rholang's only
//! non-congruence rewrite family — spelled `*@(1)`, which reduces to `1`.
//!
//! | probe | enclosing constructor | congruence declared? | position lowers to |
//! |---|---|---|---|
//! | ZERO | `PDrop`/`NQuote` (redex alone) | n/a — the kernel itself | — |
//! | SUBJECT | `Add . a:Proc, b:Proc` | **yes** — `AddCongL`/`AddCongR` | e-graph **child** |
//! | CONTROL | `POutput . n:Name, q:Proc` | **no** — the doc's own named exclusion | e-graph **child** |
//! | SEVERED | `CastList . l:List`, `List = ![Vec<Proc>]` | **no** | one **opaque leaf** |
//!
//! The ZERO probe is load-bearing: without it, "neither reduced" could not be distinguished from
//! "the lane does nothing at all", and "both reduced" could not be distinguished from "the parser
//! folded it before the e-graph ever saw it".
//!
//! SEVERED is the second control, and it is what makes the ruling precise. If CONTROL and SEVERED
//! behaved alike, "the declaration is inert" could be replaced by the weaker "the lane reduces
//! everywhere". They do not behave alike, so the lane's reach is decided by **what a field lowers
//! to** and by nothing else — the declaration is read by neither branch.
//!
//! # ★★★ THE MEASUREMENT, 2026-07-30 — verbatim, as it first came out RED
//!
//! The first form of this file asserted the DOCUMENTED behaviour (`!reduced("CONTROL")`). It
//! failed, and the failure is the finding:
//!
//! ```text
//! thread 'the_witness_table' panicked at languages/tests/congruence_declaration_witness.rs:135:5:
//! ★★ #140 RULING: a redex under `POutput` — which declares NO congruence, and is
//! `macros/docs/codegen/congruence-closure.md`'s own named example of a position where the author
//! withheld propagation — reduced anyway, while SEVERED (also undeclared) did not. The e-graph
//! lane's reach is decided by WHAT THE FIELD LOWERS TO and never by the declaration. The 130
//! declared Rholang congruences are INERT on this lane.
//!   probe    | cong declared | source            | parsed            | dovetail-normal   | reduced?
//! -----------+---------------+-------------------+-------------------+-------------------+---------
//!   ZERO     | n/a kernel    | *@(1)             | *@1               | 1                 | YES
//!   SUBJECT  | YES AddCong   | *@(1) + 2         | *@1 + 2           | 3                 | YES
//!   CONTROL  | NO  POutput   | @(0)!(*@(1))      | @0!(*@1)          | @0!(1)            | YES
//!   SEVERED  | NO  CastList  | [*@(1), 2]        | [*@1, 2]          | [*@1, 2]          | NO
//! ```
//!
//! ⇒ **#140 is a premise inversion in the #95 shape.** The filing reads *"the live backend reads
//! NONE of them"* as missing behaviour. It is not: the closure is supplied by the e-graph itself,
//! **and it reaches further than the declarations do**. The 130 declarations are DEAD EMISSION on
//! this lane, and `DeliveredElsewhere { EGraphCongruenceClosure }` is a TRUE claim for every one
//! of them (the filing's item 1 predicted it would be false for "~31 `Vec`-payload positions";
//! **zero** Rholang congruences name a `Vec`/`HashSet`/`HashMap` position — 128 name a scalar
//! child, `ParCong` names a `HashBag` AC member, `NewCong` names a binder body).
//!
//! What survives the inversion is a genuine, measured DOC/BEHAVIOUR defect and a two-sided
//! asymmetry that the declaration correlates with in NEITHER direction:
//!
//! * **over-reach** — an undeclared scalar position IS an evaluation context (CONTROL);
//! * **under-reach** — a `Vec`-carrier position is NOT one, declared or not (SEVERED).
//!
//! This file is the pin on both, so neither can move silently. **Which way the asymmetry should
//! resolve is a USER RULING** (#140 item 3) and is deliberately not decided here.

#![cfg(feature = "rholang")]

use mettail_languages::rholang::{Proc, RholangLanguage, RholangTerm, RholangTermInner};
use mettail_runtime::Language;

const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

// ══════════════════════════════════════════════════════════════════════════════════════════
// THE DECLARED SET — derived from the generated metadata, never written down
// ══════════════════════════════════════════════════════════════════════════════════════════

/// Every declared Rholang rewrite, split by whether it carries a `Premise::Congruence`.
///
/// `RewriteDef::is_congruence()` is the SAME predicate `dovetail_report::lower_rewrite` and
/// `rho_net::plan` route on (`RewriteDef::premise` is emitted from `Premise::Congruence` by
/// `macros/src/gen/runtime/metadata.rs:872`), so this split is the generator's own, not a
/// re-implementation of it.
fn declared_split() -> (Vec<&'static str>, Vec<&'static str>) {
    let mut congruences = Vec::new();
    let mut kernels = Vec::new();
    for rw in RholangLanguage.metadata().rewrites() {
        let target = if rw.is_congruence() { &mut congruences } else { &mut kernels };
        target.push(rw.lhs);
    }
    (kernels, congruences)
}

/// Whether ANY declared congruence propagates into a `POutput`-family send payload.
///
/// ★ DERIVED, not transcribed. The CONTROL probe below is only informative while `POutput`
/// declares no congruence, and "complete the list" is not a repair — so the property is
/// measured over the computed domain (every congruence's own user-syntax LHS) instead of being
/// asserted from a table somebody has to remember to update. `POutput . n:Name, q:Proc |- n "!"
/// "(" q ")"` is the only Rholang surface spelling `!` immediately before `(`; `Ne`'s `!=` and
/// the persistent `!!` forms do not produce that adjacency without it. So if a `POutputCong` is
/// ever added, this flips and the test says so rather than silently measuring the wrong thing.
fn a_congruence_reaches_a_send_payload(congruences: &[&'static str]) -> bool {
    congruences.iter().any(|lhs| lhs.contains("!("))
}

fn parse(src: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"))
}

/// Parse `src`, then normalize it on the HOST Dovetail e-graph lane — the lane whose
/// `lower_rewrite` declines to emit any congruence rule.
fn fold(src: &str) -> Proc {
    let term = RholangTerm(RholangTermInner::Proc(parse(src)));
    let normal = RholangLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
        .unwrap_or_else(|e| panic!("`{src}` must dovetail-normalize: {e:?}"));
    match normal.as_any().downcast_ref::<RholangTerm>().map(|t| &t.0) {
        Some(RholangTermInner::Proc(p)) => p.clone(),
        other => panic!("`{src}` normalized to a non-`Proc` term: {other:?}"),
    }
}

struct Row {
    probe: &'static str,
    declared: &'static str,
    src: &'static str,
    before: String,
    after: String,
}

fn row(probe: &'static str, declared: &'static str, src: &'static str) -> Row {
    Row { probe, declared, src, before: format!("{}", parse(src)), after: probe_src(src) }
}

fn probe_src(src: &str) -> String {
    format!("{}", fold(src))
}

fn render(rows: &[Row]) -> String {
    let mut out = String::from(
        "\n  probe    | cong declared | source            | parsed            | dovetail-normal   | reduced?\n\
         -----------+---------------+-------------------+-------------------+-------------------+---------\n",
    );
    for r in rows {
        out.push_str(&format!(
            "  {:<8} | {:<13} | {:<17} | {:<17} | {:<17} | {}\n",
            r.probe,
            r.declared,
            r.src,
            r.before,
            r.after,
            if r.before == r.after { "NO" } else { "YES" }
        ));
    }
    out
}

// ══════════════════════════════════════════════════════════════════════════════════════════
// ★★★ THE COUNT — AND THE THREE AXES IT DEPENDS ON
// ══════════════════════════════════════════════════════════════════════════════════════════
//
// #140 was filed as "96 of Rholang's 99 rewrite rules are congruences". Re-derived 2026-07-30
// the figure is right on NO axis, and the three axes disagree with each other by more than the
// drift:
//
// | axis | domain | what reads it | total | kernels | congruences | % cong |
// |---|---|---|---|---|---|---|
// | **A** — AS DECLARED | the `rewrites { }` block in `languages/src/rholang.rs` | the author | 133 | 3 | 130 | 97.7% |
// | **B** — AS AUGMENTED | axis A + `auto_inject`'s synthetic `*Cong`/`NormCast*` rules | `lower_rewrite`, `rho_net::plan` | see `THE_AUGMENTED_*` | | | |
// | **C** — DISPOSITION ENTRIES | one entry per (construct, orientation) the lowering walked | `lowering_disposition_inventory.rs` | see `dispositions()` | | | |
//
// ★ Axis B is the one #140's claim is ABOUT: `lower_rewrite` walks the augmented set, so the
// claim "the live backend reads none of them" ranges over axis B, not axis A. Every figure below
// is asserted so a grammar edit REPORTS rather than silently re-measuring a different corpus.

/// Axis A — the `rewrites { }` block exactly as written. Derived by `grep -cE` over
/// `languages/src/rholang.rs` (the block spans `:3747-4049`): 133 rules, of which 130 carry a
/// `| S ~> T |-` premise. Of those 130: **128 name a scalar child position, `ParCong` names a
/// `HashBag` AC member, `NewCong` names a binder body, and ZERO name a `Vec`/`HashSet`/`HashMap`
/// position** — which is what refutes #140's item-1 prediction of "~31 `Vec`-payload positions".
const DECLARED_IN_SOURCE: (usize, usize, usize) = (133, 3, 130);

/// Axis B — what the generator actually walks, measured from the emitted metadata.
const AUGMENTED: (usize, usize, usize) = (157, 15, 142);

#[test]
fn the_congruence_count_on_every_axis() {
    let (kernels, congruences) = declared_split();
    let augmented = (kernels.len() + congruences.len(), kernels.len(), congruences.len());

    let dispositions = RholangLanguage.metadata().lowering_dispositions();
    let rewrite_dispositions: Vec<_> = dispositions
        .iter()
        .filter(|d| d.construct_kind == mettail_runtime::LoweredConstructKind::Rewrite)
        .collect();
    let elsewhere_cong = rewrite_dispositions
        .iter()
        .filter(|d| d.lane == Some(mettail_runtime::LoweringLane::EGraphCongruenceClosure))
        .count();
    let auto_injected = rewrite_dispositions
        .iter()
        .filter(|d| d.origin == mettail_runtime::LoweredConstructOrigin::AutoInjected)
        .count();

    let report = format!(
        "\n  AXIS A (as declared, textual over languages/src/rholang.rs:3747-4049)\n\
         \x20   total {:>4}  kernels {:>3}  congruences {:>4}  ({:.1}% cong)\n\
         \x20 AXIS B (as augmented, from the emitted `rewrites()` metadata — WHAT lower_rewrite WALKS)\n\
         \x20   total {:>4}  kernels {:>3}  congruences {:>4}  ({:.1}% cong)   auto-injected {auto_injected}\n\
         \x20 AXIS C (disposition entries the lowering recorded for a Rewrite)\n\
         \x20   total {:>4}  of which lane == EGraphCongruenceClosure: {elsewhere_cong}\n\
         \x20 #140 AS FILED: total 99  kernels 3  congruences 96  (97.0% cong) — matches NO axis\n",
        DECLARED_IN_SOURCE.0,
        DECLARED_IN_SOURCE.1,
        DECLARED_IN_SOURCE.2,
        100.0 * DECLARED_IN_SOURCE.2 as f64 / DECLARED_IN_SOURCE.0 as f64,
        augmented.0,
        augmented.1,
        augmented.2,
        100.0 * augmented.2 as f64 / augmented.0 as f64,
        rewrite_dispositions.len(),
    );
    println!("{report}");

    assert_eq!(
        augmented, AUGMENTED,
        "axis B moved. #140 quotes a RATIO over this count, so re-derive the ratio rather than \
         bumping the constant.{report}"
    );

    // ★ THE LOAD-BEARING IDENTITY: every axis-B congruence has a disposition attributing it to
    // the e-graph lane, and nothing else does. This is what makes "the lane reads them and emits
    // nothing for them" a FACT rather than a reading of a comment.
    assert_eq!(
        elsewhere_cong, augmented.2,
        "every congruence must carry a `DeliveredElsewhere {{ EGraphCongruenceClosure }}` \
         disposition. {elsewhere_cong} do, but axis B holds {} congruences — so the two \
         mechanisms disagree about what a congruence is.{report}",
        augmented.2
    );
}

#[test]
fn the_witness_table() {
    let (kernels, congruences) = declared_split();
    assert!(
        !a_congruence_reaches_a_send_payload(&congruences),
        "the CONTROL probe below assumes `POutput` declares NO congruence, and a declared \
         congruence now reaches a send payload — so the probe is no longer a control and the \
         table must be re-derived around a different undeclared position.\n  \
         congruence LHSs containing `!(`: {:#?}",
        congruences.iter().filter(|lhs| lhs.contains("!(")).collect::<Vec<_>>()
    );

    let rows = vec![
        row("ZERO", "n/a kernel", "*@(1)"),
        row("SUBJECT", "YES AddCong", "*@(1) + 2"),
        row("CONTROL", "NO  POutput", "@(0)!(*@(1))"),
        row("SEVERED", "NO  CastList", "[*@(1), 2]"),
    ];
    let table = format!(
        "{}\n  DERIVED (axis B — what `lower_rewrite` walks): {} rewrites = {} kernel(s) + {} \
         congruence(s) ({:.1}% congruence). Kernel LHSs: {kernels:?}\n",
        render(&rows),
        kernels.len() + congruences.len(),
        kernels.len(),
        congruences.len(),
        100.0 * congruences.len() as f64 / (kernels.len() + congruences.len()) as f64,
    );
    let reduced = |name: &str| -> bool {
        let r = rows.iter().find(|r| r.probe == name).expect("probe present");
        r.before != r.after
    };

    // ZERO — the lane is alive at all.
    assert!(
        reduced("ZERO"),
        "the kernel rewrite `Exec` must fire on its own, or nothing below is interpretable.{table}"
    );

    // SUBJECT — a declared congruence position reduces.
    assert!(
        reduced("SUBJECT"),
        "a redex under `Add`, which DECLARES `AddCongL`, must reduce.{table}"
    );

    // ★★ CONTROL — `POutput` declares NO congruence and is
    // `macros/docs/codegen/congruence-closure.md`'s own named example of a position the author
    // withheld propagation from. It reduces anyway. This assertion PINS that, so the day the
    // declaration becomes load-bearing this test says so rather than quietly agreeing.
    assert!(
        reduced("CONTROL"),
        "★★ #140: a redex under `POutput` — which declares NO congruence — did NOT reduce. \
         That is a BEHAVIOUR CHANGE relative to the 2026-07-30 measurement, and it is the \
         direction the doc promises: the declaration would now be load-bearing. Re-derive #140's \
         ruling; do not adjust this assertion to match.{table}"
    );

    // SEVERED — a `Vec`-carrier position does NOT reduce, even though it too is undeclared.
    assert!(
        !reduced("SEVERED"),
        "a redex inside a `![Vec<Proc>] as List` payload reduced. The field lowers to ONE \
         `FieldSeq`/`FieldOpaque` leaf (`dovetail_report::collection_carrier`), so its elements \
         are not e-graph children and the closure cannot reach them. If it now reduces, either \
         the carrier classification moved or an element congruence became load-bearing — either \
         way #140's ruling needs re-deriving.{table}"
    );

    // ══════════════════════════════════════════════════════════════════════════════════════
    // ★★★ THE RULING, stated as the two-way identity the four rows establish
    // ══════════════════════════════════════════════════════════════════════════════════════
    //
    // ① DECLAREDNESS DIFFERS, BEHAVIOUR AGREES  (SUBJECT declared, CONTROL not — both reduce)
    // ② DECLAREDNESS AGREES, BEHAVIOUR DIFFERS  (CONTROL and SEVERED both undeclared — one
    //    reduces, one does not)
    //
    // ① alone would admit "the lane reduces everywhere". ② alone would admit "the lane is
    // selective, and maybe on the declaration". Together they force the conclusion: the
    // discriminator is the FIELD'S CARRIER and the declaration is read by neither branch.
    assert_eq!(
        reduced("SUBJECT"),
        reduced("CONTROL"),
        "① the declared and the undeclared scalar position must behave IDENTICALLY — that \
         identity IS #140.{table}"
    );
    assert_ne!(
        reduced("CONTROL"),
        reduced("SEVERED"),
        "② two positions that are BOTH undeclared must still differ, or the lane's reach is not \
         carrier-decided and the ruling is unsupported.{table}"
    );
}
