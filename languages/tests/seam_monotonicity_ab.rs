//! ★ O3 — SEAM MONOTONICITY, generalised over every string facade and both seams.
//!
//! # The property, and the instance whose absence made it necessary
//!
//! Three string-level facades sit in front of the monolithic walker — the `@`-PROJECTION
//! isolator, the `.*sep` isolator and the binary-INFIX isolator. Each is a divide-and-conquer
//! shortcut, and each is supposed to be a REFINEMENT of the walker: it may answer FASTER, and it
//! may answer where the walker cannot (`ProjectionIsolation.v` `T13_fallthrough_is_not_completeness`
//! records that the walker is NOT complete), but it must never LOSE a reading the walker has.
//!
//! ```math
//! \forall s.\quad \mathrm{readings}_{\mathrm{ON}}(s) \;\supseteq\; \mathrm{readings}_{\mathrm{OFF}}(s)
//! ```
//!
//! and, for the single-winner seam, the elected reading must be one the walker also admits:
//!
//! ```math
//! \forall s.\quad \mathrm{elected}_{\mathrm{ON}}(s) \in \mathrm{readings}_{\mathrm{OFF}}(s)
//!   \;\;\lor\;\; \mathrm{readings}_{\mathrm{OFF}}(s) = \varnothing
//! ```
//!
//! The disjunct is not a weakening: it is the `T13` case, where the facade parses something the
//! walker rejects outright, and there is then no OFF reading to be a member of.
//!
//! ★ **Instance 4 of the 2026-07 half-rule family is exactly a violation of the first line.** The
//! `_all` seam's projection facade SHORT-CIRCUITED — it returned its own reading set and
//! discarded the walker's — so for a channel written as a parenthesized grouping (`@(a)!(0)`) it
//! produced only the WRAPPED readings while the walker additionally yields the unwrapped one. The
//! reading was gone before anyone could see it, and it was found by reading the code, not by a
//! test. Repaired 2026-07-25 (#28 / G3) by UNIONING instead of short-circuiting.
//!
//! There was no gate then because there was no SEAM: `PRATTAIL_NO_PROJ_ISOLATION` did not exist
//! until 2026-07-25, and the sep and infix facades had no kill switch AT ALL, so their ON/OFF
//! reading sets had never once been compared. An infix facade that lost a reading looked exactly
//! like a language that never had it.
//!
//! # What this file adds over `proj_iso_ab_soundness.rs`
//!
//! That file is the PROJ facade's A/B, and it asserts ACCEPTANCE monotonicity (`OFF accepts ⇒ ON
//! accepts`) plus a per-shape family of pins. This one generalises along the two axes it left
//! fixed:
//!
//! | axis | there | here |
//! |---|---|---|
//! | facade | proj only | proj, sep, infix — each with its own committed kill switch |
//! | property | OFF accepts ⇒ ON accepts | `readings(ON) ⊇ readings(OFF)` as SETS, plus `elected(ON) ∈ readings(OFF)` |
//! | seam | the ALL seam's count | both seams: the ALL set and the SINGLE election |
//!
//! The two new switches — `PRATTAIL_NO_SEP_ISOLATION` and `PRATTAIL_NO_INFIX_ISOLATION`
//! (`facade.rs`) — are committed, permanent, and read once per process exactly like the proj one,
//! so the OFF legs run in SUBPROCESSES. An in-process flip would serve `__PROJ_MEMO_<Cat>`
//! entries computed under the other setting.
//!
//! # ★ Reading identity — the key is `Display`, and that was a MEASURED correction
//!
//! The first cut of this gate keyed readings by their `Debug` rendering. It reported 3 "lost"
//! readings and 15 "fabricated" elections on the very first run, and **every one of them was an
//! artifact of the key**:
//!
//! ```text
//!   @Nil!(0)      ON elects POutputNil(0)              OFF has POutputShort(PZero, 0)
//!   *(@(1))       ON has  PDrop(NParen(NQuote(1)))     OFF has PDrop(NParen(NQuoteShort(1)))
//! ```
//!
//! Those pairs are the SAME READING written through a `fold` sugar and its target: `POutputShort`
//! re-wraps to `POutput(NQuote(p), q)` and `NQuoteShort` to `NQuote(p)`, in the grammar's own
//! action bodies. `semantic_hash` folds them, the realize-dedup collapses them, and
//! `proj_iso_ab_soundness.rs` records the same correction in its own header — *"That came from
//! counting DEBUG strings, and Debug is a STRUCTURAL key"*. A structural key does not measure
//! reading loss; it measures constructor choice.
//!
//! The key is therefore the reading's **canonical SURFACE** — `Display`. After the 2026-07-26
//! surface-synonymy work (`macros/src/gen/syntax/synonymy.rs`) that is exactly the right
//! granularity, and it is right by construction rather than by luck:
//!
//! | pair | `Debug` | `Display` | which is correct |
//! |---|---|---|---|
//! | `POutputNil(0)` vs `POutputShort(PZero, 0)` | differ | both `@Nil!(0)` | SAME reading — a sugar, not a loss |
//! | `NQuote(1)` vs `NQuoteShort(1)` | differ | both `@1` | SAME reading — a synonymy class |
//! | `PDrop(NParen(x))` vs `PDrop(x)` | differ | `*(@1)` vs `*@1` | DIFFERENT readings — the grouping is load-bearing (`rd_a1_budget`) |
//!
//! So the key identifies exactly what the language declares identical and separates exactly what
//! the ambiguity-preservation contracts require kept apart. The raw structural delta is still
//! PRINTED on every run, so a divergence the surface key cannot see is visible rather than
//! silently absent.

#![cfg(feature = "rhocalc")]

use std::collections::{BTreeMap, BTreeSet};

use mettail_languages::rhocalc::{ForRow, Proc};

/// Env var that makes this binary run as an OFF-leg child.
const CHILD_MARKER: &str = "SEAM_AB_CHILD";

/// The three facades, each with the committed kill switch that disables it. Mirrors
/// `facade.rs::{PROJ,SEP,INFIX}_ISO_KILL_SWITCH_ENV`.
const FACADES: [(&str, &str); 3] = [
    ("proj", "PRATTAIL_NO_PROJ_ISOLATION"),
    ("sep", "PRATTAIL_NO_SEP_ISOLATION"),
    ("infix", "PRATTAIL_NO_INFIX_ISOLATION"),
];

/// The A/B corpus. Every row is a whole-input `Proc` span, chosen so that each facade is ENGAGED
/// by at least several of them — a monotonicity gate over inputs no facade touches is vacuous.
///
/// * `proj-*` — σ-led frames the projection isolator frames, including the `(`-grouped channels
///   whose lost reading WAS instance 4.
/// * `sep-*` — depth-0 `.*sep` lists (the `for(…;…)` row separator and polyadic sends).
/// * `infix-*` — depth-0 binary operators, including the mixed-precedence and abutted spellings
///   the `__OPS` election has to root correctly.
/// * `mix-*` — inputs where two facades compete for the same span.
fn corpus() -> Vec<(&'static str, &'static str)> {
    vec![
        // ── proj ──
        ("proj-nil", "@Nil!(0)"),
        ("proj-short", "@a!(0)"),
        ("proj-grouped", "@(a)!(0)"),
        ("proj-grouped-poly", "@(a)!(0,1)"),
        ("proj-grouped-degenerate", "@(a)!(0,)"),
        ("proj-nested", "@Nil!(@(@Nil)!())"),
        ("proj-drop", "*@Nil"),
        ("proj-drop-grouped", "*(@(1))"),
        ("proj-persist", "@Nil!!(0)"),
        ("proj-empty", "@a!()"),
        // ── sep ── observed AT `ForRow`, the only category whose `.*sep` facade RhoCalc
        //    generates. A `Proc` span containing a `for(…)` does NOT engage it: the row list is
        //    reached through `ForRow`'s own string entry, so a corpus of `Proc` spans leaves the
        //    sep column of this gate inert — which is precisely what `every_kill_switch_is_effective`
        //    caught on the first run.
        ("forrow-join", "x <- c1 & y <- c2"),
        ("forrow-join-3", "x <- c1 & y <- c2 & z <- c3"),
        ("forrow-where", "x <- c where x > 1"),
        ("forrow-join-where", "x <- c1 & y <- c2 where y > 1"),
        ("forrow-single", "x <- c"),
        ("forrow-quoted", "@x <- @Nil"),
        ("forrow-polyadic", "x , y <- c"),
        ("forrow-persist-join", "x <= c1 & y <- c2"),
        ("forrow-join-5", "a <- c1 & b <- c2 & c <- c3 & d <- c4 & e <- c5"),
        ("forrow-join-quoted", "@a <- @Nil & @b <- @Nil"),
        ("forrow-join-poly", "a , b <- c1 & d , e <- c2"),
        ("forrow-join-where-op", "a <- c1 & b <- c2 where a > 1 and b > 2"),
        ("forrow-join-send-guard", "a <- c1 & b <- c2 where @Nil!(0) matches @Nil!(0)"),
        ("forrow-nested-at", "@(a!(0)) <- @Nil & b <- c"),
        ("sep-for-two-rows", "for(x <- c1 ; y <- c2){Nil}"),
        ("sep-for-join", "for(x <- c1 & y <- c2){Nil}"),
        ("sep-for-where", "for(x <- c where x > 1){Nil}"),
        ("sep-poly-send", "@Nil!(0,1,2)"),
        ("sep-list", "[0, 1, 2]"),
        // ── infix ──
        ("infix-add", "1 + 2"),
        ("infix-prec", "1 + 2 * 3"),
        ("infix-abutted-sub", "1-7"),
        ("infix-par", "Nil | Nil"),
        ("infix-par-3", "Nil | Nil | Nil"),
        ("infix-or-of-sends", "@Nil!(0) or @Nil!(0)"),
        ("infix-cmp", "1 < 2"),
        ("infix-neg-operand", "- 7 + 1"),
        ("infix-neg-abutted", "-7 + 1"),
        // ── mixed ──
        ("mix-send-par", "@Nil!(0) | @Nil!(1)"),
        ("mix-drop-add", "*(@(1)) + 2"),
        ("mix-for-par", "for(x <- c){Nil} | c!(0)"),
        ("mix-nested-poly", "@(a)!(0, @Nil!(1))"),
    ]
}

/// One row's observation on one leg.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Obs {
    /// The ALL-seam reading set, keyed by canonical SURFACE. `None` ⇒ the span did not parse.
    all: Option<BTreeSet<String>>,
    /// The SINGLE-seam elected reading, keyed by canonical SURFACE. `None` ⇒ did not parse.
    elected: Option<String>,
    /// The ALL-seam set keyed STRUCTURALLY (`Debug`, `UniqueId` normalised) — reported, never
    /// asserted on. It is finer than the language's own notion of "the same reading", so a
    /// difference here is information, not a defect. See the header's key table.
    all_structural: Option<BTreeSet<String>>,
}

/// Normalise the per-process `UniqueId` counter out of a `Debug` rendering: variable identity is
/// allocation-ordered, so the two legs assign different ids to the same variable.
fn canon(debug: &str) -> String {
    let mut out = String::with_capacity(debug.len());
    let mut rest = debug;
    while let Some(i) = rest.find("UniqueId(") {
        out.push_str(&rest[..i]);
        out.push_str("UniqueId(#)");
        let after = &rest[i + "UniqueId(".len()..];
        let end = after.find(')').map(|e| e + 1).unwrap_or(after.len());
        rest = &after[end..];
    }
    out.push_str(rest);
    out
}

/// Observe the whole corpus on THIS process's configuration.
///
/// Rows are observed at the category their `id` names: `forrow-*` rows enter through
/// `ForRow::parse_via_wpda*` (the ONLY category whose `.*sep` facade RhoCalc generates — without
/// them the `sep` column of this gate is inert, which the teeth test now proves), everything else
/// through `Proc`.
fn observe() -> BTreeMap<String, Obs> {
    let mut m = BTreeMap::new();
    for (id, src) in corpus() {
        let at_forrow = id.starts_with("forrow-");
        mettail_runtime::clear_var_cache();
        let (all, all_structural) = if at_forrow {
            match ForRow::parse_via_wpda_all(src) {
                Ok(v) => (
                    Some(
                        v.iter()
                            .map(|t| format!("{t}"))
                            .collect::<BTreeSet<String>>(),
                    ),
                    Some(
                        v.iter()
                            .map(|t| canon(&format!("{t:?}")))
                            .collect::<BTreeSet<String>>(),
                    ),
                ),
                Err(_) => (None, None),
            }
        } else {
            match Proc::parse_via_wpda_all(src) {
                Ok(v) => (
                    Some(
                        v.iter()
                            .map(|t| format!("{t}"))
                            .collect::<BTreeSet<String>>(),
                    ),
                    Some(
                        v.iter()
                            .map(|t| canon(&format!("{t:?}")))
                            .collect::<BTreeSet<String>>(),
                    ),
                ),
                Err(_) => (None, None),
            }
        };
        mettail_runtime::clear_var_cache();
        let elected = if at_forrow {
            ForRow::parse_via_wpda(src).ok().map(|t| format!("{t}"))
        } else {
            Proc::parse_via_wpda(src).ok().map(|t| format!("{t}"))
        };
        m.insert(id.to_string(), Obs { all, elected, all_structural });
    }
    m
}

/// Render an observation map as a tab-separated stream the parent can read off stdout.
fn render(m: &BTreeMap<String, Obs>) -> String {
    let mut out = String::new();
    for (id, o) in m {
        match &o.all {
            None => out.push_str(&format!("{id}\tALL\t<NOPARSE>\n")),
            Some(set) => {
                for r in set {
                    out.push_str(&format!("{id}\tALL\t{r}\n"));
                }
                if set.is_empty() {
                    out.push_str(&format!("{id}\tALL\t<EMPTY>\n"));
                }
            },
        }
        match &o.elected {
            None => out.push_str(&format!("{id}\tONE\t<NOPARSE>\n")),
            Some(e) => out.push_str(&format!("{id}\tONE\t{e}\n")),
        }
        match &o.all_structural {
            None => out.push_str(&format!("{id}\tSTR\t<NOPARSE>\n")),
            Some(set) if set.is_empty() => out.push_str(&format!("{id}\tSTR\t<EMPTY>\n")),
            Some(set) => {
                for r in set {
                    out.push_str(&format!("{id}\tSTR\t{r}\n"));
                }
            },
        }
    }
    out
}

fn parse_render(text: &str) -> BTreeMap<String, Obs> {
    let mut m: BTreeMap<String, Obs> = BTreeMap::new();
    for line in text.lines() {
        let mut it = line.splitn(3, '\t');
        let (Some(id), Some(kind), Some(payload)) = (it.next(), it.next(), it.next()) else {
            continue;
        };
        let e = m.entry(id.to_string()).or_insert(Obs {
            all: None,
            elected: None,
            all_structural: None,
        });
        match (kind, payload) {
            ("ALL", "<NOPARSE>") => e.all = None,
            ("ALL", "<EMPTY>") => e.all = Some(BTreeSet::new()),
            ("ALL", r) => {
                e.all
                    .get_or_insert_with(BTreeSet::new)
                    .insert(r.to_string());
            },
            ("ONE", "<NOPARSE>") => e.elected = None,
            ("ONE", r) => e.elected = Some(r.to_string()),
            ("STR", "<NOPARSE>") => e.all_structural = None,
            ("STR", "<EMPTY>") => e.all_structural = Some(BTreeSet::new()),
            ("STR", r) => {
                e.all_structural
                    .get_or_insert_with(BTreeSet::new)
                    .insert(r.to_string());
            },
            _ => {},
        }
    }
    m
}

/// The child entry point. Inert unless `SEAM_AB_CHILD` is set, so a normal run executes it as a
/// trivially-passing no-op.
#[test]
fn seam_ab_off_leg_child() {
    if std::env::var_os(CHILD_MARKER).is_none() {
        return;
    }
    println!("<<<AB-LEG-BEGIN>>>");
    print!("{}", render(&observe()));
    println!("<<<AB-LEG-END>>>");
}

/// Run this same binary as a child with `switch` set, and read its leg off stdout.
///
/// A SUBPROCESS is the only honest OFF leg: every switch is process-constant by design (read once
/// into a `OnceLock`, because the helpers are on the parse hot path and the `__PROJ_MEMO_<Cat>`
/// best-parse memo must not serve entries computed under the other setting).
fn off_leg(switch: &str) -> BTreeMap<String, Obs> {
    let exe = std::env::current_exe().expect("current_exe");
    let out = std::process::Command::new(exe)
        .arg("--exact")
        .arg("seam_ab_off_leg_child")
        .arg("--nocapture")
        .env(CHILD_MARKER, "1")
        .env(switch, "1")
        .env("RUST_MIN_STACK", "8388608")
        .output()
        .unwrap_or_else(|e| panic!("spawn OFF-leg child for {switch}: {e}"));
    assert!(
        out.status.success(),
        "OFF-leg child for {switch} failed: status={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let body = stdout
        .split_once("<<<AB-LEG-BEGIN>>>\n")
        .and_then(|(_, rest)| rest.split_once("<<<AB-LEG-END>>>"))
        .map(|(body, _)| body.to_string())
        .unwrap_or_else(|| panic!("OFF-leg child for {switch} produced no leg block:\n{stdout}"));
    parse_render(&body)
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  0 — TEETH. A monotonicity gate over facades that are never engaged asserts nothing.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// Every switch must be EFFECTIVE — turning it off must change SOMETHING observable on this
/// corpus — or the corresponding column of the gate is decoration.
///
/// ⚠ If this fails, do NOT relax it: either the switch stopped being wired into the emitted
/// helpers, or the corpus no longer contains a row that engages that facade. Fix the switch or
/// extend the corpus.
#[test]
fn every_kill_switch_is_effective() {
    let on = observe();
    let mut inert: Vec<&str> = Vec::new();
    for (name, switch) in FACADES {
        let off = off_leg(switch);
        if off == on {
            inert.push(name);
        }
    }
    assert!(
        inert.is_empty(),
        "★ the {inert:?} kill switch(es) changed NOTHING on this corpus. A facade whose ON and \
         OFF legs are indistinguishable is either unwired or unexercised — a gate that cannot \
         fail is not a gate."
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  1 — THE ALL SEAM: readings(ON) ⊇ readings(OFF), per facade.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ THE PROPERTY INSTANCE 4 VIOLATED. A facade may ADD readings (it parses shapes the walker
/// cannot) and may reorder them, but it may never REMOVE one: every reading the walker alone
/// produces must still be in the facade's set.
#[test]
fn no_facade_loses_a_reading_on_the_all_seam() {
    let on = observe();
    let mut failures: Vec<String> = Vec::new();
    for (name, switch) in FACADES {
        let off = off_leg(switch);
        for (id, off_obs) in &off {
            let Some(off_set) = &off_obs.all else {
                continue;
            };
            let on_obs = on.get(id).expect("the two legs share the corpus");
            let Some(on_set) = &on_obs.all else {
                if !off_set.is_empty() {
                    failures.push(format!(
                        "  [{name}/{id}] ON does not parse at all, OFF yields {} reading(s) — \
                         the facade did not merely lose a reading, it lost the input",
                        off_set.len()
                    ));
                }
                continue;
            };
            let lost: Vec<&String> = off_set.difference(on_set).collect();
            if !lost.is_empty() {
                failures.push(format!(
                    "  [{name}/{id}] `{}` — {} reading(s) present with the facade OFF are MISSING \
                     with it ON:\n{}",
                    corpus()
                        .iter()
                        .find(|(i, _)| i == id)
                        .map(|(_, s)| *s)
                        .unwrap_or("?"),
                    lost.len(),
                    lost.iter()
                        .map(|r| format!("        {r}"))
                        .collect::<Vec<_>>()
                        .join("\n"),
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "★ {} reading(s) are LOST by a string facade. A facade is a REFINEMENT of the walker: it \
         may answer faster, and it may answer where the walker cannot \
         (`ProjectionIsolation.v` T13), but a reading it removes is gone before any \
         disambiguation can see it — which is how the `@(a)!(0)` grouped-channel reading was \
         lost for weeks.\n{}",
        failures.len(),
        failures.join("\n"),
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  2 — THE SINGLE SEAM: elected(ON) ∈ readings(OFF).
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// The single-winner seam does not have to elect the SAME representative as the walker — the
/// facade composes per-operand single winners and the walker runs a k-best extraction, and both
/// are legitimate — but whatever it elects must be a reading the walker ADMITS.
///
/// The `readings(OFF) = ∅` escape is the `T13_fallthrough_is_not_completeness` case: the facade
/// parses a shape the walker rejects (the G2 family: a σ-led frame whose channel is a grouped
/// method frame containing a nested channel-first send). There is then no OFF set to be a member
/// of, and the facade is the only reason the input parses at all.
#[test]
fn the_elected_reading_is_one_the_walker_admits() {
    let on = observe();
    let mut failures: Vec<String> = Vec::new();
    let mut checked = 0usize;
    let mut t13_rows: Vec<String> = Vec::new();
    for (name, switch) in FACADES {
        let off = off_leg(switch);
        for (id, on_obs) in &on {
            let Some(elected) = &on_obs.elected else {
                continue;
            };
            let off_obs = off.get(id).expect("the two legs share the corpus");
            let Some(off_set) = &off_obs.all else {
                t13_rows.push(format!("{name}/{id}"));
                continue;
            };
            if off_set.is_empty() {
                t13_rows.push(format!("{name}/{id}"));
                continue;
            }
            checked += 1;
            if !off_set.contains(elected) {
                failures.push(format!(
                    "  [{name}/{id}] `{}`\n      elected(ON) : {elected}\n      readings(OFF): \
                     {}",
                    corpus()
                        .iter()
                        .find(|(i, _)| i == id)
                        .map(|(_, s)| *s)
                        .unwrap_or("?"),
                    off_set
                        .iter()
                        .map(|r| format!("\n        {r}"))
                        .collect::<String>(),
                ));
            }
        }
    }
    if !t13_rows.is_empty() {
        println!(
            "  T13 rows (the facade parses what the walker rejects, so there is no OFF set): {}",
            t13_rows.join(", ")
        );
    }
    assert!(
        failures.is_empty(),
        "★ {} elected reading(s) are NOT admitted by the walker. The facade may elect a different \
         representative than the walker's k-best extractor, but electing a reading the walker \
         does not have means the facade FABRICATED it — which no refinement may \
         do.\n{}",
        failures.len(),
        failures.join("\n"),
    );
    assert!(
        checked > 0,
        "no row had a non-empty OFF reading set, so this gate is vacuous — the corpus must \
         contain inputs the WALKER can parse"
    );
}
