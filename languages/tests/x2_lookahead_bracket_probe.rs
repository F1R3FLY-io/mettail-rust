//! **X2 — the GLR bracket falsification probe** for the proposed `[*]` / `[n]`
//! speculative-lookahead surface syntax.
//!
//! # What is under test
//!
//! The `[*]` surface is proposed as **two** productions over the whole `Proc`
//! category rather than as suffixes on each of the 22 send productions:
//!
//! ```text
//! PLookahead    . p:Proc, n:Proc |- p "[" n "]"   : Proc
//! PLookaheadAll . p:Proc         |- p "[" "*" "]" : Proc
//! ```
//!
//! The hazard the probe is built to EXPOSE (not to confirm away): `*` is the
//! dereference prefix, so `[*x]` is a legal list literal today. If the GLR
//! engine offers `PLookahead` with `n = *…` as a competing complete parse of
//! `[*]`, the two productions are mutually ambiguous on the very string the
//! design needs to be unambiguous, and the surface must be redesigned.
//!
//! # Method — three languages, one binary
//!
//! Editing `languages/src/rhocalc.rs` is not possible here (another agent holds
//! it), and would in any case conflate the question with rhocalc's 4000-line
//! election lattice. So the probe declares a **scratch minimal language** that
//! reproduces exactly the four rhocalc shapes that can interact with `[` / `]`:
//!
//! | rhocalc shape | scratch analogue | why it matters |
//! | --- | --- | --- |
//! | `![Vec<Proc>] as List { open_parts: ["["], close_parts: ["]"], sep: "," }` (`rhocalc.rs:78-82`) | identical | the ONLY existing consumer of `[` / `]` |
//! | `CastList . l:List \|- l : Proc ;` (`rhocalc.rs:838`) | identical | lifts a list literal into `Proc` |
//! | `PDrop . n:Name \|- "*" n : Proc ;` (`rhocalc.rs:294`) | identical | the `*` dereference prefix — THE hazard |
//! | `POutput . n:Name, q:Proc \|- n "!" "(" q ")" : Proc ;` (`rhocalc.rs:309-310`) | identical | the send the corpus suffixes |
//!
//! plus `PPar` (braced) and `PParInfix` for the two corpus rows that need them.
//!
//! Three languages are declared so the probe can separate three questions that
//! a single language would confound:
//!
//! * [`X2Base`] — the four shapes WITHOUT the new productions. It is the
//!   control: whatever it says a string means is "the meaning today".
//! * [`X2Look`] — `X2Base` **+** `PLookahead` **+** `PLookaheadAll`. The
//!   treatment.
//! * [`X2Teeth`] — `X2Look` **+** a deliberately duplicated `PIndex` production
//!   of exactly `PLookahead`'s shape. This is the harness's **teeth test**: a
//!   string that is ambiguous by construction. If the reading counter cannot
//!   see two readings HERE, then every "exactly one reading" result elsewhere
//!   in this file is worthless, and the tests say so.
//!
//! # What "a reading" means here
//!
//! [`readings`] counts **distinct** complete `Proc` derivations returned by the
//! generated multi-result GLR entry point `Proc::parse_via_wpda_all`, deduped
//! by the `Debug` rendering of the resulting AST. Observationally identical
//! derivations (the same tree reached twice) collapse; genuinely different
//! trees do not. That is the operative notion for this design: the surface is
//! safe iff every corpus string yields exactly one TREE.

#![allow(unused_imports, dead_code)]

use std::collections::BTreeSet;

use mettail_macros::language;
use mettail_runtime::Language;

// ══════════════════════════════════════════════════════════════════════════
// X2Base — the control: the bracket-relevant rhocalc shapes, NO new rules
// ══════════════════════════════════════════════════════════════════════════

pub mod x2base {
    #![allow(unused_imports, dead_code)]
    use mettail_macros::language;
    use mettail_runtime::Language;

    language! {
        name: X2Base,

        options {
            emit_tests: false,
            emit_simulator: false,
            emit_blockly: false,
            // A syntax/lex-only probe: this file MEASURES PARSE READINGS and declares
            // no equations, rewrites, logic, guards, folds or eval bodies. The flag is
            // inert for codegen (only the dovetail/ast inventory tests read it) and it
            // is guard-checked: `has_reduction_semantics` fails the inventory loudly if
            // a `parse_only` language ever gains reduction semantics, so this cannot
            // become a way to hide one.
            parse_only: true,
        },

        types {
            Proc
            Name
            ![i64] as Int
            ![Vec<Proc>] as List {
                open_parts: ["["],
                close_parts: ["]"],
                sep: ",",
            }
        },

        terms {
            PZero . |- "Nil" : Proc;
            PDrop . n:Name |- "*" n : Proc;
            NQuote . p:Proc |- "@" p : Name;
            PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
            POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc;
            CastInt . k:Int |- k : Proc;
            CastList . l:List |- l : Proc;
            PParInfix . a:Proc, b:Proc |- a "|" b : Proc;
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════
// X2Look — the treatment: the same shapes PLUS the two proposed productions
// ══════════════════════════════════════════════════════════════════════════

pub mod x2look {
    #![allow(unused_imports, dead_code)]
    use mettail_macros::language;
    use mettail_runtime::Language;

    language! {
        name: X2Look,

        options {
            emit_tests: false,
            emit_simulator: false,
            emit_blockly: false,
            // A syntax/lex-only probe: this file MEASURES PARSE READINGS and declares
            // no equations, rewrites, logic, guards, folds or eval bodies. The flag is
            // inert for codegen (only the dovetail/ast inventory tests read it) and it
            // is guard-checked: `has_reduction_semantics` fails the inventory loudly if
            // a `parse_only` language ever gains reduction semantics, so this cannot
            // become a way to hide one.
            parse_only: true,
        },

        types {
            Proc
            Name
            ![i64] as Int
            ![Vec<Proc>] as List {
                open_parts: ["["],
                close_parts: ["]"],
                sep: ",",
            }
        },

        terms {
            PZero . |- "Nil" : Proc;
            PDrop . n:Name |- "*" n : Proc;
            NQuote . p:Proc |- "@" p : Name;
            PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
            POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc;
            CastInt . k:Int |- k : Proc;
            CastList . l:List |- l : Proc;
            PParInfix . a:Proc, b:Proc |- a "|" b : Proc;

            // ★ THE PRODUCTIONS UNDER TEST.
            PLookahead . p:Proc, n:Proc |- p "[" n "]" : Proc;
            PLookaheadAll . p:Proc |- p "[" "*" "]" : Proc;
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════
// X2Teeth — the KNOWN-POSITIVE control for the reading counter itself
// ══════════════════════════════════════════════════════════════════════════

pub mod x2teeth {
    #![allow(unused_imports, dead_code)]
    use mettail_macros::language;
    use mettail_runtime::Language;

    language! {
        name: X2Teeth,

        options {
            emit_tests: false,
            emit_simulator: false,
            emit_blockly: false,
            // A syntax/lex-only probe: this file MEASURES PARSE READINGS and declares
            // no equations, rewrites, logic, guards, folds or eval bodies. The flag is
            // inert for codegen (only the dovetail/ast inventory tests read it) and it
            // is guard-checked: `has_reduction_semantics` fails the inventory loudly if
            // a `parse_only` language ever gains reduction semantics, so this cannot
            // become a way to hide one.
            parse_only: true,
        },

        types {
            Proc
            Name
            ![i64] as Int
            ![Vec<Proc>] as List {
                open_parts: ["["],
                close_parts: ["]"],
                sep: ",",
            }
        },

        terms {
            PZero . |- "Nil" : Proc;
            PDrop . n:Name |- "*" n : Proc;
            NQuote . p:Proc |- "@" p : Name;
            PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
            POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc;
            CastInt . k:Int |- k : Proc;
            CastList . l:List |- l : Proc;
            PParInfix . a:Proc, b:Proc |- a "|" b : Proc;

            PLookahead . p:Proc, n:Proc |- p "[" n "]" : Proc;
            PLookaheadAll . p:Proc |- p "[" "*" "]" : Proc;
            // ★ THE TEETH: byte-identical surface to `PLookahead`, different label.
            // Every string `PLookahead` accepts, `PIndex` accepts too — so the
            // reading counter MUST report ≥ 2 on such a string, or it is blind.
            PIndex . p:Proc, n:Proc |- p "[" n "]" : Proc;
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Harness
// ══════════════════════════════════════════════════════════════════════════

/// The set of DISTINCT `Proc` readings of `input`, rendered as `Debug` strings.
/// `Err` (a genuine parse failure) is reported as the empty set so a rejected
/// string and an ambiguous one are distinguishable at the call site.
macro_rules! readings {
    ($proc:path, $input:expr) => {{
        use $proc as P;
        match P::parse_via_wpda_all($input) {
            Ok(terms) => terms
                .iter()
                .map(|t| format!("{:?}", t))
                .collect::<BTreeSet<String>>(),
            Err(_) => BTreeSet::new(),
        }
    }};
}

fn report(label: &str, input: &str, set: &BTreeSet<String>) {
    println!("  {label:8} {input:24} → {} reading(s)", set.len());
    for (i, r) in set.iter().enumerate() {
        println!("        [{i}] {r}");
    }
}

// ── T0: the teeth. Run FIRST; every later negative depends on it. ──────────

#[test]
fn t0_teeth_the_reading_counter_can_see_a_planted_ambiguity() {
    mettail_runtime::clear_var_cache();
    let planted = readings!(x2teeth::Proc, "x!(Nil)[0]");
    report("TEETH", "x!(Nil)[0]", &planted);
    assert!(
        planted.len() >= 2,
        "TEETH FAILED — the counter cannot see a deliberately duplicated \
         production (`PIndex` has byte-identical surface to `PLookahead`). \
         Every 'exactly one reading' assertion in this file is therefore \
         untrustworthy. Got {} reading(s): {:?}",
        planted.len(),
        planted
    );
    assert!(
        planted.iter().any(|r| r.contains("PLookahead")),
        "teeth: expected a PLookahead reading among {planted:?}"
    );
    assert!(
        planted.iter().any(|r| r.contains("PIndex")),
        "teeth: expected a PIndex reading among {planted:?}"
    );
}

/// A second tooth, at the OTHER end: the counter must also be able to report
/// ZERO for a string the grammar genuinely rejects, so "1 reading" is not
/// simply what the harness always says.
#[test]
fn t0b_teeth_the_reading_counter_reports_zero_for_a_rejected_string() {
    mettail_runtime::clear_var_cache();
    let rejected = readings!(x2look::Proc, "x!(Nil)[");
    report("TEETH0", "x!(Nil)[", &rejected);
    assert_eq!(rejected.len(), 0, "an unterminated bracket must not parse; got {rejected:?}");
}

// ── T1: the whole corpus under the TREATMENT language ──────────────────────

const CORPUS: &[&str] = &[
    "x!(Nil)[*]",
    "x!(Nil)[0]",
    "x!(Nil) [0]",
    "x!(Nil)[*x]",
    "[1]",
    "[[1],[2]]",
    "[1][2]",
    "x!([1])[2]",
    "[*x]",
    "*x",
    "{[1]}",
    "x!(Nil)[*] | y!(Nil)[3]",
    // Rows beyond the specified corpus, added because they are the shapes a
    // reviewer would ask about next: a lookahead over a list, a CHAINED
    // lookahead, and `[*]` over a braced par.
    "[1][*]",
    "x!(Nil)[*][0]",
    "x!(Nil)[0][*]",
    "{[1]}[*]",
];

/// Strings the grammar must REJECT. A surface that accepts these would be
/// offering `[*]` where the design says there is nothing to attach it to.
const REJECTED: &[&str] = &[
    "[*]", // no preceding Proc — a bare `[*]` is not a list and not a lookahead
    "x!(Nil)[*",
    "x!(Nil)*]",
];

#[test]
fn t1_every_corpus_string_has_exactly_one_reading_under_the_new_productions() {
    mettail_runtime::clear_var_cache();
    println!("\n── X2 corpus under X2Look (treatment) ──");
    let mut failures: Vec<String> = Vec::with_capacity(CORPUS.len());
    for input in CORPUS {
        let set = readings!(x2look::Proc, input);
        report("LOOK", input, &set);
        if set.len() != 1 {
            failures.push(format!("{input:?} → {} reading(s): {set:?}", set.len()));
        }
    }
    assert!(
        failures.is_empty(),
        "X2 REFUTED — these corpus strings are not uniquely read:\n  {}",
        failures.join("\n  ")
    );
}

#[test]
fn t1b_the_rejected_corpus_is_rejected() {
    mettail_runtime::clear_var_cache();
    println!("\n── X2 rejected corpus under X2Look ──");
    let mut accepted: Vec<String> = Vec::new();
    for input in REJECTED {
        let set = readings!(x2look::Proc, input);
        report("REJECT", input, &set);
        if !set.is_empty() {
            accepted.push(format!("{input:?} → {set:?}"));
        }
    }
    assert!(
        accepted.is_empty(),
        "these strings must NOT parse:\n  {}",
        accepted.join("\n  ")
    );
}

/// The `Name` category is unaffected: `@Nil`, `@[1]` still read as Names, and
/// identically in the control and the treatment.
#[test]
fn t1c_the_name_category_is_unaffected() {
    mettail_runtime::clear_var_cache();
    for input in ["@Nil", "@[1]", "@(x!(Nil))"] {
        let base = readings!(x2base::Name, input);
        let look = readings!(x2look::Name, input);
        println!("  NAME     {input:24} base={} look={}", base.len(), look.len());
        assert_eq!(base, look, "`{input}` changed meaning in the Name category");
    }
}

// ── T2: the specific shape assertions ──────────────────────────────────────

#[test]
fn t2_bracket_star_is_plookaheadall_not_plookahead_of_a_deref() {
    mettail_runtime::clear_var_cache();
    let set = readings!(x2look::Proc, "x!(Nil)[*]");
    report("LOOK", "x!(Nil)[*]", &set);
    assert_eq!(set.len(), 1, "`x!(Nil)[*]` must have exactly one reading: {set:?}");
    let only = set.iter().next().expect("checked len == 1");
    assert!(
        only.contains("PLookaheadAll"),
        "`x!(Nil)[*]` must read as PLookaheadAll, got: {only}"
    );
    assert!(only.contains("POutput"), "`x!(Nil)[*]` must wrap the POutput, got: {only}");
    // ★ THE HAZARD: `PLookahead` with `n = *…` must NOT be offered. `PDrop`
    // needs a Name after `*`; there is none before `]`.
    assert!(
        !only.contains("PDrop"),
        "HAZARD REALIZED — `[*]` was read as a dereference: {only}"
    );
}

#[test]
fn t2b_bracket_star_ident_is_pookahead_of_a_deref_not_pookaheadall() {
    mettail_runtime::clear_var_cache();
    let set = readings!(x2look::Proc, "x!(Nil)[*x]");
    report("LOOK", "x!(Nil)[*x]", &set);
    assert_eq!(set.len(), 1, "`x!(Nil)[*x]` must have exactly one reading: {set:?}");
    let only = set.iter().next().expect("checked len == 1");
    assert!(
        only.contains("PLookahead(") && !only.contains("PLookaheadAll"),
        "`x!(Nil)[*x]` must read as PLookahead (not …All), got: {only}"
    );
    assert!(only.contains("PDrop"), "`[*x]` must carry the deref, got: {only}");
}

#[test]
fn t2c_a_bare_list_literal_is_still_a_list() {
    mettail_runtime::clear_var_cache();
    for input in ["[1]", "[[1],[2]]", "[*x]"] {
        let set = readings!(x2look::Proc, input);
        report("LOOK", input, &set);
        assert_eq!(set.len(), 1, "`{input}` must have exactly one reading: {set:?}");
        let only = set.iter().next().expect("checked len == 1");
        assert!(only.contains("CastList"), "`{input}` must still be a list literal, got: {only}");
        assert!(
            !only.contains("PLookahead"),
            "`{input}` must not be read as a lookahead, got: {only}"
        );
    }
}

// ── T3: the no-meaning-change gate against the CONTROL language ────────────

/// Every string the control language accepts must be read IDENTICALLY by the
/// treatment language. This is the "no previously-accepted string changes
/// meaning" clause, and it is the assertion the design most needs.
#[test]
fn t3_no_previously_accepted_string_changes_meaning() {
    mettail_runtime::clear_var_cache();
    // Strings that are legal WITHOUT the new productions.
    const LEGACY: &[&str] = &[
        "Nil",
        "*x",
        // `@Nil` is a `Name`, not a `Proc`, so it is dereferenced here to stay
        // in the category under comparison. (An earlier revision listed the bare
        // `@Nil`; `Proc::parse_via_wpda_all` correctly returned 0 readings for it
        // in BOTH languages, which the "must parse in the control" guard —
        // rightly — flagged as a vacuous row rather than as drift.)
        "*@Nil",
        "[1]",
        "[1,2]",
        "[[1],[2]]",
        "[*x]",
        "{[1]}",
        "x!(Nil)",
        "x!([1])",
        "x!(Nil) | y!(Nil)",
        "{[1] | [2]}",
    ];
    println!("\n── X2 legacy corpus: X2Base (control) vs X2Look (treatment) ──");
    let mut drift: Vec<String> = Vec::with_capacity(LEGACY.len());
    for input in LEGACY {
        let base = readings!(x2base::Proc, input);
        let look = readings!(x2look::Proc, input);
        println!("  LEGACY   {input:24} base={} look={}", base.len(), look.len());
        if base.is_empty() {
            drift.push(format!("{input:?} does not parse in the CONTROL language"));
            continue;
        }
        if base != look {
            drift.push(format!(
                "{input:?} CHANGED MEANING\n      base: {base:?}\n      look: {look:?}"
            ));
        }
    }
    assert!(
        drift.is_empty(),
        "X2 REFUTED — adding the two productions changed the meaning of \
         already-legal strings:\n  {}",
        drift.join("\n  ")
    );
}

// ── T4: the established claims, verified rather than re-derived ────────────

/// `[` / `]` are grammar terminals of the two new productions and of nothing
/// else; the list carrier reaches them through `open_parts` / `close_parts`.
/// This test pins the consequence that matters: a list literal and a lookahead
/// are distinguished by CONTEXT (a preceding complete `Proc`), which is exactly
/// what a GLR engine is able to decide and an LL(1) one is not.
#[test]
fn t4_a_leading_bracket_is_a_list_and_a_trailing_bracket_is_a_lookahead() {
    mettail_runtime::clear_var_cache();
    let leading = readings!(x2look::Proc, "[1]");
    let trailing = readings!(x2look::Proc, "[1][2]");
    report("LOOK", "[1]", &leading);
    report("LOOK", "[1][2]", &trailing);
    assert_eq!(leading.len(), 1, "`[1]` ambiguous: {leading:?}");
    assert_eq!(trailing.len(), 1, "`[1][2]` ambiguous: {trailing:?}");
    let t = trailing.iter().next().expect("checked len == 1");
    assert!(
        t.contains("PLookahead(") && t.contains("CastList"),
        "`[1][2]` must be a lookahead over a list literal, got: {t}"
    );
}
