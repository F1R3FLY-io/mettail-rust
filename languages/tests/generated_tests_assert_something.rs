//! **#150 — A GENERATED `#[test]` WITH NO ASSERTION IS A COVERAGE OVERCLAIM, and there were 421.**
//!
//! # The shape
//!
//! `macros/src/gen/test_gen/` owns two emitters that answer "I cannot test this construct" by
//! writing a **named, passing, empty `#[test]`**:
//!
//! | emitter | site | condition | what it emits |
//! |---|---|---|---|
//! | `rewrite_tests.rs` | the `is_congruence_rule()` branch | the rewrite is a congruence | `fn rewrite_<lang>_<rule>() { let _lang = X; }` + two prose comments |
//! | `equation_tests.rs` | the `has_complex_premises` branch | freshness / `ForAll` / guard / relation premise | `fn equation_<lang>_<eq>() { let _lang = X; }` + two prose comments |
//!
//! ★ This is strictly worse than a silent skip, and #150's own census — which enumerates eleven
//! mechanisms — **does not contain either of them**. A skipped rule that emits nothing leaves a
//! gap somebody can find by counting. A skipped rule that emits `#[test] fn rewrite_rholang_addcongl()
//! {}` reports itself as *covered*: the suite grows by one green test and the coverage number goes
//! UP. `rewrite_tests.rs`'s own module header already argues this case, forty lines above the
//! branch that violates it —
//!
//! > *"A test suppressed by an unsound oracle is strictly worse than a test that fails: the failure
//! > is a report, the suppression is a silence."*
//!
//! — and `equation_tests.rs`'s comment is a statement about a body it does not have: *"emit a
//! metadata-presence test only"*, above a body containing no metadata check.
//!
//! # The repair — the skip's own JUSTIFICATION becomes the assertion
//!
//! Neither branch is deleted; both are wrong to *try* to reduce the construct (a congruence needs
//! a triggering context; a freshness equation cannot be instantiated statically). What is wrong is
//! answering "I cannot reduce it" with *nothing*. So each branch now asserts what IS checkable,
//! which is exactly the FACT the skip rests on:
//!
//! * a congruence-rewrite test asserts `rw.premise.is_some()` — it IS a congruence, which is the
//!   whole reason it is not reduced here;
//! * a complex-premise equation test asserts `!eq.conditions.is_empty()` — it DOES carry the
//!   premises the skip names.
//!
//! ⇒ *a disposition is a value, not an absence*, applied to a generated test body: the skip now
//! says why **in a form that can fail**.
//!
//! # ⚠ THIS GATE'S OWN COVERAGE, stated in its own output — THREE clauses
//!
//! A gate whose advertised coverage exceeds its real coverage is worse than no gate, so every run
//! prints what it could and could not see, and refuses a verdict rather than narrowing one:
//!
//! 1. **What it parsed.** The scan brackets bodies by brace balance over generated Rust text, so
//!    it can miss a `#[test]` whose body it cannot close. It reports the `#[test]` attributes it
//!    counted lexically AND the bodies it bracketed, and fails when the second is not at least
//!    [`MIN_BRACKETING_RATIO`] of the first.
//! 2. **What it can vouch for.** `target/generated/` is a build ARTIFACT, and a language hosted
//!    in `languages/tests/definitions/` is only re-expanded when its own host test target builds
//!    — so a partial build leaves bytes from a previous emitter behind. Files older than the
//!    newest of [`EMITTERS`] are counted, NAMED, and excluded from the verdict; more than
//!    `MAX_STALE_VACUOUS` of them and the gate says "rebuild first" instead of "clean". This
//!    clause was added because the fix measured 421 → **5**, and all five were stale bytes: a
//!    gate without it would have reported five live defects that did not exist.
//! 3. **What "cannot fail" means.** Deliberately narrow — see [`body_can_fail`], whose first form
//!    over-reported by 162 rows.

#![cfg(feature = "rholang")]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Minimum fraction of lexically-counted `#[test]` attributes whose bodies the scan must
/// successfully bracket before its verdict means anything.
const MIN_BRACKETING_RATIO: f64 = 0.95;

/// The corpus must be this large or the walk has changed shape and the gate is reporting
/// success over something that is not the generated tree. 54 language directories exist as of
/// 2026-07-30; the floor is deliberately below that so ordinary growth does not trip it, and
/// deliberately above zero so an empty or misrooted walk cannot pass.
const MIN_GENERATED_LANGUAGES: usize = 40;

fn workspace_root() -> PathBuf {
    let mut dir = Path::new(env!("CARGO_MANIFEST_DIR")).to_path_buf();
    loop {
        if std::fs::read_to_string(dir.join("Cargo.toml"))
            .is_ok_and(|text| text.contains("[workspace]"))
        {
            return dir;
        }
        assert!(dir.pop(), "no ancestor of CARGO_MANIFEST_DIR declares [workspace]");
    }
}

/// One generated test whose body contains nothing that can fail.
#[derive(Debug)]
struct Vacuous {
    /// Path relative to `target/generated`.
    file: String,
    name: String,
}

struct Scan {
    /// `#[test]` attributes counted lexically — the DENOMINATOR of this gate's coverage.
    attributes_seen: usize,
    /// Test bodies the scan successfully bracketed — the NUMERATOR.
    bodies_bracketed: usize,
    /// Language directories walked.
    languages: usize,
    /// Vacuous bodies found in files the gate can VOUCH FOR (newer than their emitter).
    vacuous: Vec<Vacuous>,
    /// Files OLDER than the emitter that writes them. `target/generated/` is a build artifact
    /// and a language hosted in `languages/tests/definitions/` is only re-expanded when its host
    /// test target is built — so a partial build leaves stale bytes behind. These are counted and
    /// NAMED rather than judged: a verdict over bytes the gate cannot vouch for would be exactly
    /// the overclaim it exists to catch.
    stale: Vec<Vacuous>,
}

/// The emitters whose output this gate audits. A generated file older than the newest of these
/// predates the current emitter and is therefore unauditable.
const EMITTERS: [&str; 2] = [
    "macros/src/gen/test_gen/rewrite_tests.rs",
    "macros/src/gen/test_gen/equation_tests.rs",
];

/// Modification time of the newest auditing emitter, as seconds since the epoch.
fn emitter_mtime(root: &Path) -> std::time::SystemTime {
    EMITTERS
        .iter()
        .map(|relative| {
            let path = root.join(relative);
            std::fs::metadata(&path)
                .unwrap_or_else(|e| panic!("stat {}: {e}", path.display()))
                .modified()
                .expect("a filesystem that records mtime")
        })
        .max()
        .expect("EMITTERS is non-empty")
}

/// Split `body` off after the opening `{` of a function, by brace balance.
///
/// Returns `None` when the braces do not balance before end-of-input, which is the case this
/// gate must count rather than assume away.
fn bracket_body(text: &str, open_brace: usize) -> Option<&str> {
    let bytes = text.as_bytes();
    let mut depth = 0usize;
    let mut i = open_brace;
    while i < bytes.len() {
        match bytes[i] {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return text.get(open_brace + 1..i);
                }
            },
            _ => {},
        }
        i += 1;
    }
    None
}

/// Strip `//` line comments from `body`. Generated bodies never contain `/* */`.
fn strip_comments(body: &str) -> String {
    body.lines()
        .map(|line| match line.find("//") {
            Some(at) => &line[..at],
            None => line,
        })
        .collect::<Vec<_>>()
        .join("\n")
}
/// Whether `body` contains anything at all that can turn the test red.
///
/// ⚠ THE PREDICATE IS DELIBERATELY NARROW, and this is the second half of the coverage
/// statement in this file's header. A body "cannot fail" here only when, after comments are
/// stripped, it performs **no call and no macro invocation** — no `(`, no `!`. Anything that
/// calls code CAN panic, and a panic IS a failure, so it counts as capable of failing even with
/// no `assert`.
///
/// This narrowing was forced by a measurement. The first form of this predicate looked for
/// `assert` / `panic!` / `.expect(` and flagged **583** bodies — 162 more than the real defect —
/// because it swept in the generated `proptest!` rows
///
/// ```text
/// fn proc_display_does_not_panic(term in arb_proc(4)) { let _ = format!("{}", term); }
/// ```
///
/// whose entire purpose is to fail by panicking. Calling those an overclaim would have been an
/// overclaim of its own, in a gate written to catch overclaims.
fn body_can_fail(body: &str) -> bool {
    let code = strip_comments(body);
    code.contains('(') || code.contains('!')
}

fn scan() -> Scan {
    let root = workspace_root();
    let generated = root.join("target").join("generated");
    let newest_emitter = emitter_mtime(&root);
    let mut out = Scan {
        attributes_seen: 0,
        bodies_bracketed: 0,
        languages: 0,
        vacuous: Vec::new(),
        stale: Vec::new(),
    };

    let entries = std::fs::read_dir(&generated).unwrap_or_else(|e| {
        panic!(
            "cannot read {}: {e}\n\nThe subject of this gate IS that tree, so it must not \
             continue with a guess — an absent or misrooted walk would report success over \
             nothing. Build `-p languages` first.",
            generated.display()
        )
    });
    let mut dirs: Vec<PathBuf> = Vec::new();
    for entry in entries {
        let path = entry.expect("a readable dir entry").path();
        if path.is_dir() {
            out.languages += 1;
            dirs.push(path);
        }
    }
    dirs.sort();

    for dir in dirs {
        let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
            .map(|e| e.expect("a readable dir entry").path())
            .filter(|p| p.extension().is_some_and(|x| x == "rs"))
            .collect();
        files.sort();
        for path in files {
            let Ok(text) = std::fs::read_to_string(&path) else {
                continue;
            };
            let fresh = std::fs::metadata(&path)
                .and_then(|m| m.modified())
                .is_ok_and(|written| written >= newest_emitter);
            let relative = path
                .strip_prefix(&generated)
                .unwrap_or(&path)
                .to_string_lossy()
                .replace('\\', "/");
            for (offset, _) in text.match_indices("#[test]") {
                out.attributes_seen += 1;
                // The nearest `fn NAME(` at or after the attribute, then its body.
                let Some(rest) = text.get(offset..) else {
                    continue;
                };
                let Some(fn_at) = rest.find("fn ") else {
                    continue;
                };
                let after = &rest[fn_at + 3..];
                let Some(paren) = after.find('(') else {
                    continue;
                };
                let name = after[..paren].trim().to_owned();
                let Some(brace_rel) = after[paren..].find('{') else {
                    continue;
                };
                let Some(body) = bracket_body(rest, fn_at + 3 + paren + brace_rel) else {
                    continue;
                };
                out.bodies_bracketed += 1;
                if !body_can_fail(body) {
                    let row = Vacuous { file: relative.clone(), name };
                    if fresh {
                        out.vacuous.push(row);
                    } else {
                        out.stale.push(row);
                    }
                }
            }
        }
    }
    out
}

fn render(scan: &Scan) -> String {
    let ratio = if scan.attributes_seen == 0 {
        0.0
    } else {
        scan.bodies_bracketed as f64 / scan.attributes_seen as f64
    };
    let mut per_file: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for v in &scan.vacuous {
        per_file.entry(&v.file).or_default().push(&v.name);
    }
    let mut stale_files: BTreeMap<&str, usize> = BTreeMap::new();
    for s in &scan.stale {
        *stale_files.entry(&s.file).or_default() += 1;
    }
    let mut out = format!(
        "\n  ── this gate's OWN coverage ──────────────────────────────────────────────\n\
         \x20   language dirs walked          {}\n\
         \x20   `#[test]` attributes seen     {}\n\
         \x20   bodies successfully bracketed {} ({:.1}% — floor {:.0}%)\n\
         \x20   vacuous bodies in STALE files (NOT judged — older than the emitter): {}\n",
        scan.languages,
        scan.attributes_seen,
        scan.bodies_bracketed,
        100.0 * ratio,
        100.0 * MIN_BRACKETING_RATIO,
        scan.stale.len(),
    );
    for (file, count) in &stale_files {
        out.push_str(&format!("     {count:>5}  {file}  ⟵ rebuild its host test target\n"));
    }
    out.push_str(&format!(
        "  ── verdict (over FRESH files only) ───────────────────────────────────────\n\
         \x20   generated tests whose body CANNOT FAIL: {}\n",
        scan.vacuous.len()
    ));
    for (file, names) in per_file {
        out.push_str(&format!("     {:>5}  {file}\n", names.len()));
        for name in names.iter().take(4) {
            out.push_str(&format!("            e.g. {name}\n"));
        }
    }
    out
}

/// ★ THE GATE. Measured RED at `9e7004cc` with **421** vacuous generated tests — 415 congruence
/// rewrites and 6 complex-premise equations.
#[test]
fn no_generated_test_body_is_incapable_of_failing() {
    let scan = scan();
    let report = render(&scan);
    println!("{report}");

    // ── anti-vacuity floors, asserted BEFORE the verdict ────────────────────────────────
    assert!(
        scan.languages >= MIN_GENERATED_LANGUAGES,
        "only {} generated language dir(s) were walked, so the verdict below ranges over a \
         fraction of the corpus without saying so.{report}",
        scan.languages
    );
    assert!(
        scan.attributes_seen > 1_000,
        "only {} `#[test]` attribute(s) found across the generated tree. The corpus emits far \
         more, so the walk has narrowed and a clean verdict would be meaningless.{report}",
        scan.attributes_seen
    );
    let ratio = scan.bodies_bracketed as f64 / scan.attributes_seen as f64;
    assert!(
        ratio >= MIN_BRACKETING_RATIO,
        "this gate could only bracket {:.1}% of the `#[test]` bodies it found. It must not \
         render a verdict over a domain it cannot see — a gate whose advertised coverage \
         exceeds its real coverage is worse than no gate.{report}",
        100.0 * ratio
    );

    // ⚠ The third coverage clause: the gate must not render a verdict when most of the tree
    // predates the emitter. `MAX_STALE_VACUOUS` is a ceiling on how much unauditable output the
    // gate will tolerate before it says "rebuild first" instead of "clean". Five is the measured
    // steady state (appsubst · bicongdemo · ctxdemo, all hosted in `languages/tests/definitions/`
    // and only re-expanded when their own host test target builds), so the ceiling is set just
    // above it — high enough not to cry wolf on an ordinary partial build, low enough that a
    // wholesale stale tree cannot masquerade as a clean verdict.
    const MAX_STALE_VACUOUS: usize = 8;
    assert!(
        scan.stale.len() <= MAX_STALE_VACUOUS,
        "{} vacuous bodies sit in files OLDER than their emitter, which is more than this gate \
         will judge around. Build `-p languages --tests` so every language is re-expanded, then \
         re-run: a clean verdict over stale bytes is the overclaim this gate exists to \
         catch.{report}",
        scan.stale.len()
    );

    // ── the verdict ─────────────────────────────────────────────────────────────────────
    assert!(
        scan.vacuous.is_empty(),
        "{} generated `#[test]` function(s) have a body that cannot fail. A named, passing, \
         empty test is a COVERAGE OVERCLAIM: the suite grows by one green test and nothing is \
         checked. The emitter must assert the FACT its skip rests on instead of emitting prose \
         — see this file's header.{report}",
        scan.vacuous.len()
    );
}
