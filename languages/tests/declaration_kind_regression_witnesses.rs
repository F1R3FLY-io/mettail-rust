//! ★★★ (#195) **THE BASELINE ANY FUTURE "LOAD-BEARING DECLARATIONS" DESIGN MUST PRESERVE.**
//!
//! This file is **measurement only**. It changes no lowering, declares no language, and
//! asserts nothing about what *ought* to happen — it records what the Dovetail e-graph lane
//! does **today**, for each of the three declaration kinds a `language!` body can carry, so
//! that a later change to the closure machinery either preserves these rows or says so
//! loudly.
//!
//! # 1. Why it exists — the owner's memory is a regression witness
//!
//! Owner, 2026-07-30:
//!
//! > *"congruences worked at one time because I remember having to work with you to get
//! > mutual congruences `*@p == p` and `@*p == p` for RhoCal (now Rholang) to work
//! > correctly."*
//!
//! That mutual pair is live in `languages/src/rholang.rs`, and — the load-bearing detail —
//! it is **split across two declaration kinds**:
//!
//! | half | spelling | kind | site |
//! |---|---|---|---|
//! | `@*N = N` | `QuoteDrop . \|- (NQuote (PDrop N)) = N ;` | **equation** | `rholang.rs:3764` |
//! | `*@P ~> P` | `Exec . \|- (PDrop (NQuote P)) ~> P ;` | **plain rewrite** | `rholang.rs:3752` |
//! | `*@P ~> P` (short surface) | `ExecQuoteShort . \|- (PDrop (NQuoteShort P)) ~> P ;` | plain rewrite | `rholang.rs:3753` |
//! | `*@P ~> P` (paren surface) | `ExecParenQuote . \|- (PDrop (NParen (NQuote P))) ~> P ;` | plain rewrite | `rholang.rs:3754` |
//!
//! ⚠ **And `#140` filed the propagation of `Exec` under `POutput` as a DEFECT.** Its CONTROL
//! row is `@(0)!(*@(1))` reducing to `@0!(1)` — which is `Exec` firing inside a send's
//! payload, i.e. *exactly* the `*@p == p` behaviour the owner worked to obtain. A repair that
//! made declarations load-bearing by **withholding** propagation at undeclared positions
//! would therefore have deleted that behaviour. This file is the executable form of that
//! objection.
//!
//! # 2. Why three kinds and not one
//!
//! `#140`'s witness (`congruence_declaration_witness.rs`) measured **congruences only**.
//! A null result for one kind says nothing about the others, and the three are lowered by
//! three *different* functions:
//!
//! | kind | lowering | disposition today |
//! |---|---|---|
//! | equation | `dovetail_report::lower_equation` — up to TWO `RewriteRule`s (forward + reverse) | `Delivered` |
//! | plain rewrite | `dovetail_report::lower_rewrite` tail — ONE `RewriteRule` | `Delivered` |
//! | congruence | `dovetail_report::lower_rewrite`'s `is_congruence_rule()` branch | `DeliveredElsewhere { EGraphCongruenceClosure }` — **no rule at all** |
//!
//! So "is the declaration load-bearing?" has three answers, and only the third was measured.
//!
//! # 3. What a row means
//!
//! Every row parses a source term, normalizes it on the host Dovetail e-graph lane
//! (`RholangLanguage::dovetail_normal_term` — the same entry point `#140` used), and records
//! the normal form. A row is **GREEN** when the normal form is the expected one. The rows are
//! deliberately spelled as `assert_eq!` on the *rendered* normal form rather than as
//! `reduced?` booleans: "it changed" is a much weaker claim than "it became this".

#![cfg(feature = "rholang")]

use mettail_languages::rholang::{Proc, RholangLanguage, RholangTerm, RholangTermInner};
use mettail_runtime::Language;

/// Saturation bounds. Identical to `congruence_declaration_witness.rs` so the two files
/// cannot disagree because one was given a bigger budget.
const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

fn parse(src: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"))
}

/// Parse `src`, then normalize it on the HOST Dovetail e-graph lane.
fn fold(src: &str) -> String {
    let term = RholangTerm(RholangTermInner::Proc(parse(src)));
    let normal = RholangLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
        .unwrap_or_else(|e| panic!("`{src}` must dovetail-normalize: {e:?}"));
    match normal.as_any().downcast_ref::<RholangTerm>().map(|t| &t.0) {
        Some(RholangTermInner::Proc(p)) => format!("{p}"),
        other => panic!("`{src}` normalized to a non-`Proc` term: {other:?}"),
    }
}

/// One measured row: source, the parse rendering, and the dovetail normal form.
struct Row {
    id: &'static str,
    kind: &'static str,
    declaration: &'static str,
    src: &'static str,
    parsed: String,
    normal: String,
    expected: &'static str,
}

fn row(
    id: &'static str,
    kind: &'static str,
    declaration: &'static str,
    src: &'static str,
    expected: &'static str,
) -> Row {
    Row {
        id,
        kind,
        declaration,
        src,
        parsed: format!("{}", parse(src)),
        normal: fold(src),
        expected,
    }
}

fn render(rows: &[Row]) -> String {
    let mut out = String::from(
        "\n  id   | kind          | declaration      | source          | parsed          | \
         dovetail-normal | expected        | verdict\n\
         -------+---------------+------------------+-----------------+-----------------+\
         -----------------+-----------------+--------\n",
    );
    for r in rows {
        out.push_str(&format!(
            "  {:<4} | {:<13} | {:<16} | {:<15} | {:<15} | {:<15} | {:<15} | {}\n",
            r.id,
            r.kind,
            r.declaration,
            r.src,
            r.parsed,
            r.normal,
            r.expected,
            if r.normal == r.expected { "GREEN" } else { "★ RED" }
        ));
    }
    out
}

/// The five rows the owner's memory puts at risk, plus the two that make them
/// interpretable.
///
/// ★ ROWS W1–W5 are the mandated regression witnesses. W6/W7 are controls without which the
/// others cannot be read:
///
/// * **W6** (`*@(1) + 2` → `3`) is the DECLARED-congruence row (`AddCongL`/`AddCongR`): if it
///   were red, "the declared and the undeclared position behave alike" would be vacuous.
/// * **W7** (`[*@(1), 2]` unchanged) is the SEVERED control: a `Vec`-carrier position where
///   the closure demonstrably does NOT reach, which is what proves the lane is selective at
///   all rather than "reduces everywhere".
fn witness_rows() -> Vec<Row> {
    vec![
        // ── W1: the kernel rewrite alone. Without it nothing below is interpretable.
        row("W1", "plain rewrite", "Exec", "*@(1)", "1"),
        // ── W2 ★★ THE ROW AT RISK. `Exec` firing INSIDE a send payload — `POutput` declares
        //         no congruence, and #140 filed this as over-reach. It is `*@p == p`.
        row("W2", "plain rewrite", "Exec (no cong)", "@(0)!(*@(1))", "@0!(1)"),
        // ── W3: the EQUATION half of the mutual pair, isolated. `@*x` cannot reduce by
        //         `Exec` (`*x` is not `*@P`), so the ONLY route from `@*x` to `x` is the
        //         `QuoteDrop` equation — and it must travel through `POutput`'s CHANNEL
        //         field, which likewise declares no congruence.
        row("W3", "equation", "QuoteDrop", "@(*x)!(0)", "x!(0)"),
        // ── W4a/W4b: the other two quote SURFACES. A repair covering only `NQuote` would
        //         silently drop two of the three `Exec` families.
        row("W4a", "plain rewrite", "ExecQuoteShort", "*@1", "1"),
        row("W4b", "plain rewrite", "ExecParenQuote", "*(@(1))", "1"),
        // ── W5: a DECLARED congruence must keep working.
        row("W5", "congruence", "AddCongL/R", "*@(1) + 2", "3"),
        // ── W6/W7: the two controls (see the doc comment).
        // ⚠ EXPECTED `{1 | 2}`, NOT `1 | 2`, and the difference is NOT the reduction. The
        // parse renders `*@1 | 2` (infix) while the normal form renders `{1 | 2}` (braced
        // bag): `PPar` reconstructs through `insert_into_ppar` into a `HashBag` whose
        // `Display` is the braced collection surface. `*@1` DID become `1` — the `ParCong`
        // propagation fired — so a `reduced?` boolean would have called this GREEN either
        // way. Asserting the RENDERED normal form is what exposed the surface asymmetry, and
        // recording it here is the point: a parse/normal-form display asymmetry on `PPar` is
        // a real (separate) observation, not a congruence defect.
        row("W6", "congruence", "ParCong", "*@(1) | 2", "{1 | 2}"),
        row("W7", "none (severed)", "CastList", "[*@(1), 2]", "[*@1, 2]"),
    ]
}

#[test]
fn the_five_regression_witnesses_and_their_two_controls() {
    let rows = witness_rows();
    let table = render(&rows);
    println!("{table}");

    let reds: Vec<&Row> = rows.iter().filter(|r| r.normal != r.expected).collect();
    assert!(
        reds.is_empty(),
        "★★ {} of the {} baseline rows is/are RED. Each of these is behaviour the owner's \
         `*@p == p` / `@*p == p` work established, so a RED row is either a regression \
         introduced since the last measurement or a finding that the baseline was never what \
         it was believed to be — and either way it must be reported, not adjusted away.\n\
         RED rows: {:?}{table}",
        reds.len(),
        rows.len(),
        reds.iter().map(|r| r.id).collect::<Vec<_>>(),
    );
}

/// ★★ THE PER-KIND VERDICT, derived from the reflected metadata rather than read off a table.
///
/// `#140` asked "is a declaration load-bearing?" of congruences only. This derives the answer
/// for **all three kinds** from `lowering_dispositions()` — the generator's own record of what
/// it did with each declared construct — so the verdict cannot drift from the lowering.
///
/// The three kinds are load-bearing in genuinely different senses, and conflating them is how
/// `#140`'s premise inverted:
///
/// * an **equation** and a **plain rewrite** each become one or more emitted
///   `dovetail::rules::RewriteRule`s — remove the declaration and the rule is gone, so they
///   are load-bearing in the strongest sense (`Delivered`, with the emitted rule's label as
///   the detail);
/// * a **congruence** emits nothing (`DeliveredElsewhere { EGraphCongruenceClosure }`) — the
///   closure that would satisfy it is intrinsic to the e-graph, so removing the declaration
///   changes no behaviour. That is the whole content of `#140`.
#[test]
fn the_per_kind_disposition_verdict_is_derived() {
    use mettail_runtime::{LoweredConstructKind, LoweringLane, LoweringOutcomeKind};

    let metadata = RholangLanguage.metadata();
    let dispositions = metadata.lowering_dispositions();

    let mut equations_delivered = 0usize;
    let mut equations_other = Vec::new();
    let mut rewrites_delivered = 0usize;
    let mut rewrites_elsewhere_closure = 0usize;
    let mut rewrites_other = Vec::new();

    for d in dispositions.iter() {
        match d.construct_kind {
            LoweredConstructKind::Equation => {
                if d.outcome == LoweringOutcomeKind::Delivered {
                    equations_delivered += 1;
                } else {
                    equations_other.push((d.construct, d.outcome.as_str()));
                }
            },
            LoweredConstructKind::Rewrite => {
                if d.outcome == LoweringOutcomeKind::Delivered {
                    rewrites_delivered += 1;
                } else if d.lane == Some(LoweringLane::EGraphCongruenceClosure) {
                    rewrites_elsewhere_closure += 1;
                } else {
                    rewrites_other.push((d.construct, d.outcome.as_str()));
                }
            },
            _ => {},
        }
    }

    // The DECLARED split, from the same metadata: a rewrite carrying `Premise::Congruence`
    // is a congruence, everything else in `rewrites { }` is a plain rewrite.
    let (mut plain, mut congruence) = (0usize, 0usize);
    for rw in metadata.rewrites() {
        if rw.is_congruence() {
            congruence += 1;
        } else {
            plain += 1;
        }
    }
    let equations = metadata.equations().len();

    let report = format!(
        "\n  ★ PER-KIND VERDICT (Rholang, derived from `lowering_dispositions()`)\n\
         \x20 ┌────────────────┬──────────┬───────────────────────────────────────────────┐\n\
         \x20 │ kind           │ declared │ what the lowering did                         │\n\
         \x20 ├────────────────┼──────────┼───────────────────────────────────────────────┤\n\
         \x20 │ equation       │ {equations:>8} │ Delivered: {equations_delivered:<4} other: {:<20?} │\n\
         \x20 │ plain rewrite  │ {plain:>8} │ Delivered: {rewrites_delivered:<4}                              │\n\
         \x20 │ congruence     │ {congruence:>8} │ DeliveredElsewhere{{closure}}: {rewrites_elsewhere_closure:<4}          │\n\
         \x20 └────────────────┴──────────┴───────────────────────────────────────────────┘\n\
         \x20 other rewrite outcomes: {:?}\n",
        equations_other, rewrites_other,
    );
    println!("{report}");

    // ★ THE VERDICT, as three assertions rather than three sentences.
    //
    // (i) EVERY congruence emits nothing and is attributed to the closure. This is #140,
    //     restated as an identity over the metadata.
    assert_eq!(
        rewrites_elsewhere_closure, congruence,
        "every declared congruence must be attributed to the e-graph closure lane, and \
         nothing else may be. If these differ, the two mechanisms disagree about what a \
         congruence is.{report}"
    );
    // (ii) EVERY plain rewrite is Delivered — an emitted rule. So a plain rewrite IS
    //      load-bearing: delete it and the rule vanishes.
    // ⚠ MEASURED, not assumed: 9 of Rholang's 15 plain rewrites are Delivered. The other
    // SIX are the auto-injected `NormCast*InProc` rewrites the generator emits over
    // `CastBool`/`CastInt`/`CastFloat`/`CastFixed` constructors Rholang never declares — an
    // `AutoInjected` declination, i.e. a GENERATOR defect rather than author debt, already
    // inventoried by `languages/tests/lowering_disposition_inventory.rs`. So the honest
    // claim is "every DECLARED plain rewrite is Delivered", and the auto-injected
    // declinations are pinned by count so the set cannot quietly grow.
    let auto_injected_declined = dispositions
        .iter()
        .filter(|d| {
            d.construct_kind == LoweredConstructKind::Rewrite
                && d.is_generator_bug()
        })
        .count();
    assert_eq!(
        rewrites_delivered + auto_injected_declined,
        plain,
        "every plain (non-congruence) rewrite must be either Delivered as an emitted rule or \
         an AutoInjected declination. Delivered {rewrites_delivered} + auto-injected \
         declinations {auto_injected_declined} must account for all {plain}.{report}"
    );
    assert_eq!(
        auto_injected_declined, 6,
        "the auto-injected plain-rewrite declination set is pinned at SIX \
         (`NormCast{{Int,UInt32,BigInt}}To{{BigInt,BigRat,Int}}InProc`). A change here is a \
         change to `ast/src/auto_inject.rs`'s output and must be reported.{report}"
    );
    // (iii) At least one equation is Delivered, and the count is pinned so a silent drop
    //       reports. ⚠ NOT `== equations`: `Extrude` carries a `ForAll` freshness premise
    //       the structural lowering does not model, so it is legitimately not delivered —
    //       and the point of pinning the number is that the legitimate exception cannot
    //       quietly grow.
    // ★★ THE OWNER'S EQUATION HALF, DERIVED. Rholang declares TWO equations and the lowering
    // records THREE dispositions for them, because an equation lowers to up to TWO rules
    // (forward + reverse) and each gets its own:
    //
    //   • `QuoteDrop`  (`(NQuote (PDrop N)) = N`) — FORWARD Delivered; REVERSE `Suppressed`,
    //     because its RHS `N` is a bare metavariable and the reversed rule would match every
    //     e-class. That is correct elision, and `W3` measures the forward rule FIRING.
    //   • `Extrude`    — `Declined`: it carries a `ForAll` freshness premise
    //     (`xs.*map(|x| x # ...rest)`) the structural lowering does not model.
    //
    // ⇒ `QuoteDrop` — the `@*p == p` half of the owner's mutual pair — IS load-bearing:
    //   delete the declaration and the emitted rule disappears with it.
    assert_eq!(
        equations_delivered, 1,
        "exactly ONE equation orientation is Delivered (`QuoteDrop` forward). If this moves, \
         either `Extrude`'s `ForAll` premise became supported or `QuoteDrop`'s elision \
         changed — both are reportable.{report}"
    );
    assert_eq!(
        equations_other.len(),
        2,
        "the two non-delivered equation dispositions are `QuoteDrop` reverse (Suppressed: \
         bare-metavariable RHS) and `Extrude` (Declined: ForAll freshness premise).{report}"
    );
}

/// ★★★ THE CENSUS THAT DECIDES "COMPLETE THE DECLARATION SET".
///
/// One of the three candidate repairs for #195 is **(C) complete the declaration set** — add
/// the congruence declarations the e-graph's intrinsic closure already realizes, so the
/// declarations and the behaviour agree and nothing that reduces today stops reducing.
///
/// That repair's cost is a NUMBER, and it is the number of positions the intrinsic closure
/// reaches. This test derives it, because "complete the list" is only a defensible repair when
/// the list is small enough to be complete-able **and** derived rather than hand-maintained.
///
/// # What is counted
///
/// For every declared constructor of every category, one *propagating position* per field that
/// lowers to a child e-class — i.e. the positions
/// `typed_lowering::field_child_expr_typed` emits `__mettail_dovetail_add_<cat>(eg, …)` for.
/// Those, and exactly those, are where congruence closure propagates.
///
/// ⚠ Derived from the REFLECTED metadata (`terms()`), not from a table: the whole point is
/// that a hand-maintained mirror of a computable domain is the failure mode this campaign has
/// shipped four times.
#[test]
fn the_size_of_the_complete_congruence_set_is_derived() {
    let metadata = RholangLanguage.metadata();

    // Every declared congruence's LHS, so "already declared" is the generator's own answer.
    let declared_congruences: Vec<&str> = metadata
        .rewrites()
        .iter()
        .filter(|rw| rw.is_congruence())
        .map(|rw| rw.lhs)
        .collect();

    // The propagating-position census over the declared TERM constructors.
    //
    // `TermDef::params` records one entry per declared parameter with its category; a
    // parameter whose category is one of the language's own declared CATEGORIES is a child
    // e-class position (a builtin/native category is a `FieldOpaque` leaf and is not).
    // A field is a CHILD E-CLASS position iff its declared type names one of the language's
    // own OBJECT categories — a category with no `native_type`. A native/builtin category
    // (`Int`, `String`, `List`, `Bag`, …) lowers to a `FieldOpaque`/`FieldSeq` carrier leaf,
    // which is exactly the SEVERED case `W7` measures, so it is not a propagating position.
    let object_categories: Vec<&str> = metadata
        .types()
        .iter()
        .filter(|t| t.native_type.is_none())
        .map(|t| t.name)
        .collect();
    let is_object_category = |name: &str| object_categories.contains(&name);

    let mut positions = 0usize;
    let mut constructors_with_positions = 0usize;
    let mut per_category: std::collections::BTreeMap<&str, usize> =
        std::collections::BTreeMap::new();
    for term in metadata.terms().iter() {
        let mut here = 0usize;
        for field in term.fields.iter() {
            if is_object_category(field.ty) {
                here += 1;
            }
        }
        if here > 0 {
            constructors_with_positions += 1;
            positions += here;
            *per_category.entry(term.type_name).or_default() += here;
        }
    }

    let report = format!(
        "\n  ★★ THE COMPLETE-CONGRUENCE-SET CENSUS (Rholang, derived)\n\
         \x20   declared constructors ................ {}\n\
         \x20   constructors with ≥1 child position .. {constructors_with_positions}\n\
         \x20   CHILD-E-CLASS POSITIONS (total) ...... {positions}\n\
         \x20   declared congruences (axis B) ........ {}\n\
         \x20   ⇒ positions a `(C) complete the set` repair would have to declare, MINUS what\n\
         \x20     is already declared, is bounded below by {} − {} = {}\n\
         \x20   per owning category: {per_category:?}\n",
        metadata.terms().len(),
        declared_congruences.len(),
        positions,
        declared_congruences.len(),
        positions as i64 - declared_congruences.len() as i64,
    );
    println!("{report}");

    // ★ The load-bearing claim: the complete set is SUBSTANTIALLY LARGER than the declared
    // set. That is what makes literal (C) — hand-writing the missing declarations — the
    // "complete the list is not a repair" anti-pattern, and what makes DERIVED (C) — emitting
    // them from this very census — the only tractable form of the same idea.
    assert!(
        positions > declared_congruences.len(),
        "if the declared congruences already covered every child-e-class position, `(C) \
         complete the declaration set` would be a no-op and #140's over-reach could not \
         exist. This inequality IS the gap #195 is about.{report}"
    );
    // Pinned so a grammar edit REPORTS rather than silently re-measuring a different corpus.
    assert_eq!(
        (positions, declared_congruences.len()),
        (THE_COMPLETE_SET, THE_DECLARED_SET),
        "the census moved. Re-derive the (A)/(B)/(C) cost comparison rather than bumping the \
         constants.{report}"
    );
}

/// The derived size of the complete congruence set — every child-e-class position in
/// Rholang's declared constructors. **MEASURED 2026-07-30, not chosen: 193.**
///
/// ★ Read against `THE_DECLARED_SET` (142) this is the whole cost argument for #195:
/// **51 propagating positions carry no declaration.** So
///
///  * **(A) narrow the closure to the declarations** would silence 51 positions — and `W2`
///    and `W3` prove two of them carry the owner's `*@p == p` / `@*p == p` behaviour;
///  * **(C) complete the declaration set by hand** means writing 51 new congruence rules and
///    keeping them in step with every future constructor — a hand-maintained mirror of a
///    computable domain, which is the failure mode
///    `feedback_complete_the_list_is_not_a_repair_derive_it` names and which this campaign has
///    already shipped four times;
///  * **(C-derived)** — emit those 51 from THIS census, as `auto_inject` already does for cast
///    congruences — is the same repair with the mirror removed.
const THE_COMPLETE_SET: usize = 193;
/// The derived size of the declared congruence set (axis B: declared + auto-injected).
const THE_DECLARED_SET: usize = 142;
