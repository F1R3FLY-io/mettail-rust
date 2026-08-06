//! # No test in this workspace may expect a panic
//!
//! ## The measurement this gate exists to prevent recurring
//!
//! This workspace compiles `dev`/`test` with the **cranelift** codegen backend
//! (root `Cargo.toml`, `[profile.dev] codegen-backend = "cranelift"`). Under cg_clif
//! a `panic!` does not unwind the way the LLVM-backed profiles do:
//!
//! * inside the proc macro, a panic **does not cross the `proc_macro` bridge**.
//!   `rustc` aborts with `fatal runtime error: Rust cannot catch foreign exceptions`
//!   and prints **nothing** — no span, no message, no test name;
//! * inside an ordinary crate, cg_clif emits no catch pads, so an unwind sails
//!   straight through any `std::panic::catch_unwind` monomorphised in that crate and
//!   reaches libtest's LLVM-compiled interceptor — or aborts outright with
//!   `fatal runtime error: failed to initiate panic, error 5` (SIGABRT).
//!
//! A test that *expects* a panic is therefore, in this tree, either **useless** (it
//! passes for a reason unrelated to what it claims) or **actively destructive** (it
//! aborts the build with no diagnostic and takes every other test in the binary with
//! it). Both were observed.
//!
//! ## The two constructs, and why they are not held to the same rule
//!
//! | construct | rule | why |
//! |---|---|---|
//! | `#[should_panic]` | **banned outright** | its only purpose is to expect a panic — there is no other use |
//! | `catch_unwind` | **allowlisted, with a reason per entry** | it has three distinct uses and only one is a test asserting a panic |
//!
//! The three uses of `catch_unwind`:
//!
//! 1. **a test asserting that something panics** — banned, and rewritten;
//! 2. **a harness** isolating a subject or capturing a message for a diagnostic — kept
//!    where it is genuinely not asserting a panic;
//! 3. **production code defending itself** — kept; it is not a test at all.
//!
//! ⚠ An allowlist without a per-entry reason is the same defect wearing a list. Every
//! entry in [`CATCH_UNWIND_ALLOWLIST`] therefore carries the argument for its own
//! existence, and the gate fails if an entry's occurrence count drifts — so a NEW
//! `catch_unwind` in an already-allowlisted file has to be argued rather than
//! inheriting the argument made for its neighbours.
//!
//! ## What replaces an expectation of a panic
//!
//! Three patterns, chosen per site:
//!
//! 1. **The condition is an internal invariant no input can violate** ⇒ assert the
//!    invariant holds, and prove by construction or by full corpus that the guard
//!    never fires. A *measured negative*, not a hope.
//! 2. **The condition IS reachable from input** ⇒ the panic is the defect. The code
//!    grows a `try_…` entry point returning `Result`/`Option`, the panicking form
//!    becomes a thin wrapper over it, and the test asserts the `Err`/`None`.
//! 3. **The abort is observable only out of process** — a real `SIGABRT`, a panic at
//!    an `extern "C"` frame, a stack overflow ⇒ run the subject in a **child
//!    process** and decide on its exit status and stderr. `catch_unwind` cannot
//!    intercept any of those anyway, so a site that tried was already broken.
//!
//! ## Scope
//!
//! Every `.rs` file `git` tracks, minus `scratch*/` — a wipeable snapshot directory,
//! not source. `git ls-files` rather than a directory walk so the gate's idea of
//! "source" is exactly the repository's, and a file that is merely present on disk
//! (build output, an editor backup, a sibling worktree) cannot make it red.
//!
//! ## Anti-vacuity
//!
//! A scanner that walked nothing, or that could not see the construct it bans, would
//! pass forever. Three separate cells prevent that:
//!
//! * [`the_walk_reaches_the_workspace`] — the walk really covers hundreds of files;
//! * [`the_scanner_finds_a_planted_attribute`] — the scanner, run on a synthetic
//!   buffer, reports the file and line of a planted attribute;
//! * [`the_scanner_ignores_comments_and_string_literals`] — and does NOT report one
//!   that is only *mentioned*, which is what lets this file describe the ban in
//!   prose and lets `doc_fence_justification.rs` keep an `"ignore,should_panic"`
//!   doctest info-string fixture.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

// ═══════════════════════════════════════════════════════════════════════════════
// The needles
// ═══════════════════════════════════════════════════════════════════════════════

// ★ Assembled from fragments so this file's own CODE text contains neither literal.
// The gate is therefore clean under its own rule with no path exclusion — nothing
// here has to be trusted to keep excluding itself after a rename.
const PANIC_EXPECTING_ATTRIBUTE: &str = concat!("should", "_panic");
const UNWIND_INTERCEPTOR: &str = concat!("catch", "_unwind");

// ═══════════════════════════════════════════════════════════════════════════════
// The allowlist
// ═══════════════════════════════════════════════════════════════════════════════

/// One allowlisted file: `(path, occurrences, why it is allowed to be there)`.
type Allowed = (&'static str, usize, &'static str);

/// Every file permitted to name the unwind interceptor, with the exact number of
/// occurrences and the argument for each.
///
/// ⚠ The count is part of the entry. A new occurrence in an already-listed file
/// fails this gate, because the reason recorded here was made about the occurrences
/// that existed when it was written — not about whatever is added later.
const CATCH_UNWIND_ALLOWLIST: &[Allowed] = &[
    // ── use 3: production code defending itself ──────────────────────────────
    (
        "runtime/src/visitor.rs",
        2,
        "PRODUCTION, NOT A TEST. `with_pool_or_fallback` / `with_two_pools_or_fallback` \
         borrow a thread-local `Vec` pool; the interceptor exists solely to RETURN the \
         borrowed buffer on an unwind and then `resume_unwind` the original payload. \
         Nothing is swallowed and no panic is asserted — removing it would leave the \
         pool wedged after any panicking visit.",
    ),
    (
        "simulation/src/runner.rs",
        3,
        "PRODUCTION, NOT A TEST. The property-test driver evaluates a USER-SUPPLIED \
         language; a panicking seed must be recorded as a `SimulationFailure` (and \
         kept in the regression file) rather than tearing down the campaign. It \
         asserts nothing about panicking — the same three call sites handle `Ok`, \
         `Err` and panic alike.",
    ),
    (
        "prattail/src/logict_smt.rs",
        1,
        "PRODUCTION, NOT A TEST. `z3_available()` probes whether a Z3 `Context` can be \
         constructed at all. A missing or ABI-incompatible libz3 must make the probe \
         answer `false` so the caller falls back, not abort the compiling macro.",
    ),
    (
        "rholang-runtime/src/bin/bench_sa_vs_naive_driver.rs",
        1,
        "PRODUCTION (a measurement binary), NOT A TEST. Per-rep guard: an interpreter \
         panic inside one rep becomes a `dnf` line in the protocol file, so the \
         remaining reps still run and the run is not lost. It asserts nothing.",
    ),
    (
        "rholang-runtime/src/bin/bench_e6a_pathmap_driver.rs",
        1,
        "PRODUCTION (a measurement binary), NOT A TEST. Same per-rep DNF guard as \
         `bench_sa_vs_naive_driver.rs`; kept identical so the two drivers' failure \
         accounting is comparable.",
    ),
    // ── use 2: a harness that does not assert a panic ────────────────────────
    (
        "macros/src/gen/test_gen/simulation_tests.rs",
        7,
        "GENERATOR of a harness — seven emitted call sites. The emitted simulation \
         tests SKIP inputs whose native evaluation panics (e.g. division by zero in \
         `![a / b]`) so that a language's normal-form-reachability RATE is computed \
         over the inputs that evaluate. No emitted assertion requires a panic — every \
         one of the seven sites treats a panic exactly as it treats a parse failure. \
         Rewriting them to demand success would assert a property about arbitrary \
         generated terms that no language promises.",
    ),
    (
        "macros/src/gen/test_gen/rewrite_tests.rs",
        1,
        "GENERATOR of a harness. The emitted per-rewrite-rule execution test asserts \
         `NormalForm` only when the run RETURNED; a native-eval panic is tolerated, as \
         the emitted comment says. It does not assert that any rule panics.",
    ),
];

// ═══════════════════════════════════════════════════════════════════════════════
// The scanner
// ═══════════════════════════════════════════════════════════════════════════════

/// One occurrence of a banned or allowlisted construct.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Occurrence {
    path: String,
    line: usize,
    text: String,
}

/// Strip line comments, block comments and — optionally — string literals from one
/// file's text, preserving line structure so line numbers stay exact.
///
/// Comments are always removed: this gate must be describable in prose, and every
/// rewritten site carries a comment explaining what it used to be.
///
/// `keep_strings` is the difference between the two needles:
///
/// * the panic-expecting **attribute** is looked for with strings REMOVED, so a
///   doctest info-string fixture such as `"ignore,should_panic"` (a real one lives in
///   `doc_fence_justification.rs`) is not mistaken for an attribute;
/// * the unwind interceptor is looked for with strings KEPT, because a proc macro
///   that EMITS one has committed to it exactly as much as a crate that writes one,
///   and the allowlist should have to argue for it either way.
///
/// ⚠ Known and deliberate limitation: string state is reset at each newline, so the
/// continuation lines of a multi-line string literal are scanned as code. That errs
/// toward REPORTING, which is the correct failure direction for a gate — a false
/// positive is loud and is answered by an allowlist entry, whereas carrying string
/// state across lines would let a stray quote silently blind the scanner for the rest
/// of a file.
fn strip(source: &str, keep_strings: bool) -> Vec<String> {
    let mut out = Vec::with_capacity(source.lines().count());
    let mut in_block_comment = false;
    for raw_line in source.lines() {
        let chars: Vec<char> = raw_line.chars().collect();
        let mut kept = String::with_capacity(raw_line.len());
        let mut i = 0;
        let mut in_string = false;
        // Raw strings are matched by hash count so `r##"…"##` closes correctly.
        let mut raw_hashes: Option<usize> = None;
        while i < chars.len() {
            if in_block_comment {
                if chars[i] == '*' && chars.get(i + 1) == Some(&'/') {
                    in_block_comment = false;
                    i += 2;
                } else {
                    i += 1;
                }
                continue;
            }
            if let Some(hashes) = raw_hashes {
                if chars[i] == '"'
                    && chars.len() >= i + 1 + hashes
                    && chars[i + 1..].iter().take(hashes).all(|c| *c == '#')
                {
                    raw_hashes = None;
                    i += 1 + hashes;
                    continue;
                }
                if keep_strings {
                    kept.push(chars[i]);
                }
                i += 1;
                continue;
            }
            if in_string {
                if chars[i] == '\\' {
                    if keep_strings {
                        kept.push(chars[i]);
                        if let Some(c) = chars.get(i + 1) {
                            kept.push(*c);
                        }
                    }
                    i += 2;
                    continue;
                }
                if chars[i] == '"' {
                    in_string = false;
                    i += 1;
                    continue;
                }
                if keep_strings {
                    kept.push(chars[i]);
                }
                i += 1;
                continue;
            }
            // Not in any comment or literal.
            if chars[i] == '/' && chars.get(i + 1) == Some(&'/') {
                break; // line comment (including `///` and `//!`)
            }
            if chars[i] == '/' && chars.get(i + 1) == Some(&'*') {
                in_block_comment = true;
                i += 2;
                continue;
            }
            // A CHAR LITERAL, so `'"'` cannot be mistaken for the start of a string.
            // A lifetime (`'static`, `'_`) is not a literal and falls through.
            if chars[i] == '\'' {
                let width = match chars.get(i + 1) {
                    Some('\\') => 4, // '\n' — quote, backslash, escapee, quote
                    Some(_) => 3,    // 'x'
                    None => 0,
                };
                if width > 0 && chars.get(i + width - 1) == Some(&'\'') {
                    i += width;
                    continue;
                }
            }
            if chars[i] == 'r' {
                // `r"…"` or `r#"…"#`
                let mut hashes = 0;
                let mut j = i + 1;
                while chars.get(j) == Some(&'#') {
                    hashes += 1;
                    j += 1;
                }
                if chars.get(j) == Some(&'"') {
                    raw_hashes = Some(hashes);
                    i = j + 1;
                    continue;
                }
            }
            if chars[i] == '"' {
                in_string = true;
                i += 1;
                continue;
            }
            kept.push(chars[i]);
            i += 1;
        }
        out.push(kept);
    }
    out
}

/// Every occurrence of `needle` in `source`'s code text, attributed to `path`.
fn scan_source(path: &str, source: &str, needle: &str, keep_strings: bool) -> Vec<Occurrence> {
    strip(source, keep_strings)
        .into_iter()
        .enumerate()
        .filter(|(_, code)| code.contains(needle))
        .map(|(index, code)| Occurrence {
            path: path.to_string(),
            line: index + 1,
            text: code.trim().to_string(),
        })
        .collect()
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the dovetail crate has a workspace parent")
        .to_path_buf()
}

/// Every `.rs` path `git` tracks, minus `scratch*/`.
fn tracked_rust_files() -> Vec<String> {
    let output = Command::new("git")
        .args(["-c", "core.fsmonitor=false", "ls-files", "-z", "--", "*.rs"])
        .current_dir(repo_root())
        .output()
        .expect("`git ls-files` runs in the workspace root");
    assert!(
        output.status.success(),
        "`git ls-files` failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout)
        .split('\0')
        .filter(|path| !path.is_empty() && !path.starts_with("scratch"))
        .map(str::to_string)
        .collect()
}

/// Scan the whole workspace for one needle.
fn scan_workspace(needle: &str, keep_strings: bool) -> (Vec<Occurrence>, usize) {
    let root = repo_root();
    let mut found = Vec::new();
    let mut walked = 0usize;
    for relative in tracked_rust_files() {
        let Ok(source) = fs::read_to_string(root.join(&relative)) else {
            // Tracked but not present (a partial checkout); the walk count below
            // is what proves this is not silently skipping the whole tree.
            continue;
        };
        walked += 1;
        found.extend(scan_source(&relative, &source, needle, keep_strings));
    }
    (found, walked)
}

// ═══════════════════════════════════════════════════════════════════════════════
// The gate
// ═══════════════════════════════════════════════════════════════════════════════

/// ★★★ No tracked source may carry a panic-expecting test attribute.
#[test]
fn no_tracked_source_expects_a_panic() {
    let (found, walked) = scan_workspace(PANIC_EXPECTING_ATTRIBUTE, false);
    assert!(
        found.is_empty(),
        "★★★ {} panic-expecting attribute(s) in tracked source, across {walked} files.\n\n\
         A test that expects a panic cannot survive this workspace's cranelift dev \
         profile — see this file's module documentation for the mechanism and for the \
         three patterns that replace one.\n\n{}",
        found.len(),
        found
            .iter()
            .map(|o| format!("  {}:{}: {}", o.path, o.line, o.text))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// ★★★ Every unwind interceptor is on the allowlist, at the recorded count.
#[test]
fn every_unwind_interceptor_is_allowlisted_with_a_reason() {
    let (found, walked) = scan_workspace(UNWIND_INTERCEPTOR, true);

    let mut observed: BTreeMap<&str, Vec<&Occurrence>> = BTreeMap::new();
    for occurrence in &found {
        observed
            .entry(occurrence.path.as_str())
            .or_default()
            .push(occurrence);
    }

    let allowed: BTreeMap<&str, (usize, &str)> = CATCH_UNWIND_ALLOWLIST
        .iter()
        .map(|(path, count, reason)| (*path, (*count, *reason)))
        .collect();

    // Every entry carries a reason substantial enough to BE one.
    for (path, count, reason) in CATCH_UNWIND_ALLOWLIST {
        assert!(
            reason.len() >= 80,
            "the allowlist entry for `{path}` has no real reason recorded (\"{reason}\"). \
             An allowlist without a per-entry reason is the same defect wearing a list."
        );
        assert!(*count > 0, "`{path}` is allowlisted for zero occurrences");
    }

    let mut problems: Vec<String> = Vec::new();

    for (path, occurrences) in &observed {
        match allowed.get(path) {
            None => problems.push(format!(
                "  ★ NOT ALLOWLISTED — {path} ({} occurrence(s)):\n{}",
                occurrences.len(),
                occurrences
                    .iter()
                    .map(|o| format!("      line {}: {}", o.line, o.text))
                    .collect::<Vec<_>>()
                    .join("\n")
            )),
            Some((expected, _)) if *expected != occurrences.len() => problems.push(format!(
                "  ★ COUNT DRIFTED — {path}: allowlisted for {expected}, found {}. The \
                 recorded reason was written about the occurrences that existed then; a \
                 new one must be argued, not inherited.\n{}",
                occurrences.len(),
                occurrences
                    .iter()
                    .map(|o| format!("      line {}: {}", o.line, o.text))
                    .collect::<Vec<_>>()
                    .join("\n")
            )),
            Some(_) => {},
        }
    }

    // A stale entry is as much a defect as a missing one: it means the allowlist is
    // no longer a description of the tree.
    for (path, _) in &allowed {
        if !observed.contains_key(path) {
            problems.push(format!(
                "  ★ STALE ENTRY — {path} is allowlisted but no longer contains the \
                 construct. Delete the entry so the list keeps describing the tree."
            ));
        }
    }

    assert!(
        problems.is_empty(),
        "★★★ the unwind-interceptor allowlist does not describe the tree (walked \
         {walked} files):\n\n{}\n\n\
         Each entry must state which of the three uses it is — a test asserting a \
         panic (which must be REWRITTEN, not listed), a harness that does not assert \
         one, or production code defending itself.",
        problems.join("\n\n")
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// Anti-vacuity — the gate must be able to go RED
// ═══════════════════════════════════════════════════════════════════════════════

/// The walk really covers the workspace.
///
/// A scanner whose `git ls-files` returned nothing would make both gates above pass
/// forever. The floor is a floor with a wide margin, not a fixture.
#[test]
fn the_walk_reaches_the_workspace() {
    let (_, walked) = scan_workspace(PANIC_EXPECTING_ATTRIBUTE, false);
    assert!(
        walked > 300,
        "expected to walk more than 300 tracked source files, walked {walked} — the \
         gate is scanning an empty or truncated tree and proves nothing"
    );
    // …and the crate this gate lives in is among them, so the walk is not scanning
    // some unrelated tree that merely happens to be large.
    let files = tracked_rust_files();
    assert!(
        files
            .iter()
            .any(|p| p == "dovetail/tests/panic_expectation_gate.rs"),
        "the walk did not reach this file, so its idea of `tracked source` is not this \
         repository's"
    );
}

/// ★ THE RED PROOF. Planted in a synthetic buffer, the attribute is reported — with
/// the file name and the line.
///
/// This is the executable form of "show it red". It cannot be done by planting a real
/// attribute in the tree, because the whole point of the gate is that one must not be
/// there; a synthetic buffer proves the same thing about the same scanner and stays
/// proven on every future run rather than once.
#[test]
fn the_scanner_finds_a_planted_attribute() {
    let planted = format!(
        "#[test]\n#[{}(expected = \"boom\")]\nfn plants_a_violation() {{ panic!(\"boom\") }}\n",
        PANIC_EXPECTING_ATTRIBUTE
    );
    let found =
        scan_source("synthetic/planted_violation.rs", &planted, PANIC_EXPECTING_ATTRIBUTE, false);
    assert_eq!(found.len(), 1, "the planted attribute was not reported: {found:?}");
    assert_eq!(found[0].path, "synthetic/planted_violation.rs");
    assert_eq!(found[0].line, 2, "the reported line must be the attribute's");

    // The same for a `cfg_attr`-conditional one, which is how the walker's
    // duplicate-occurrence tripwire used to spell it.
    let conditional = format!(
        "#[test]\n#[cfg_attr(debug_assertions, {}(expected = \"boom\"))]\nfn also() {{}}\n",
        PANIC_EXPECTING_ATTRIBUTE
    );
    let found =
        scan_source("synthetic/conditional.rs", &conditional, PANIC_EXPECTING_ATTRIBUTE, false);
    assert_eq!(found.len(), 1, "a cfg_attr-conditional attribute must be reported too");

    // …and the interceptor needle finds a planted interceptor.
    let interceptor = format!("fn f() {{ let _ = std::panic::{}(|| ()); }}\n", UNWIND_INTERCEPTOR);
    let found = scan_source("synthetic/interceptor.rs", &interceptor, UNWIND_INTERCEPTOR, true);
    assert_eq!(found.len(), 1, "the planted interceptor was not reported: {found:?}");
}

/// …and the scanner does NOT report a construct that is merely mentioned.
///
/// Without this the gate would be unusable: this very file explains the ban in prose,
/// every rewritten site records what it used to be, and `doc_fence_justification.rs`
/// keeps `"ignore,should_panic"` as a doctest info-string fixture. A scanner that
/// could not tell code from prose would force all three to be written in riddles.
#[test]
fn the_scanner_ignores_comments_and_string_literals() {
    let mentions = format!(
        "//! This module used to use `#[{attr}]`.\n\
         /// Formerly `#[{attr}(expected = \"x\")]`; see the gate.\n\
         // #[{attr}]\n\
         /* #[{attr}] */\n\
         fn f() {{ let _info = \"ignore,{attr}\"; }}\n",
        attr = PANIC_EXPECTING_ATTRIBUTE
    );
    let found = scan_source("synthetic/mentions.rs", &mentions, PANIC_EXPECTING_ATTRIBUTE, false);
    assert!(
        found.is_empty(),
        "the scanner reported a MENTION as a violation, which would make the ban \
         undocumentable: {found:?}"
    );

    // A multi-line block comment must not leak either.
    let block = format!(
        "/*\n  #[{attr}]\n  still a comment\n*/\nfn g() {{}}\n",
        attr = PANIC_EXPECTING_ATTRIBUTE
    );
    assert!(
        scan_source("synthetic/block.rs", &block, PANIC_EXPECTING_ATTRIBUTE, false).is_empty(),
        "a multi-line block comment leaked"
    );

    // A raw string must not leak when strings are stripped …
    let raw = format!("fn h() {{ let _ = r#\"#[{attr}]\"#; }}\n", attr = PANIC_EXPECTING_ATTRIBUTE);
    assert!(
        scan_source("synthetic/raw.rs", &raw, PANIC_EXPECTING_ATTRIBUTE, false).is_empty(),
        "a raw string leaked into attribute detection"
    );

    // ★ A CHAR LITERAL holding a quote must not put the scanner into string state for
    // the rest of the line — otherwise a violation after one would be invisible.
    let quoted_char = format!(
        "fn q(c: char) {{ if c == '\"' {{}} }}\n#[{attr}]\nfn after() {{}}\n",
        attr = PANIC_EXPECTING_ATTRIBUTE
    );
    assert_eq!(
        scan_source("synthetic/quoted_char.rs", &quoted_char, PANIC_EXPECTING_ATTRIBUTE, false)
            .len(),
        1,
        "a char literal containing a double quote blinded the scanner"
    );
    // … and MUST be seen when they are kept, which is what makes the generator
    // entries in the allowlist meaningful.
    let emitted =
        format!("fn e() {{ out.push_str(r#\"std::panic::{}\"#); }}\n", UNWIND_INTERCEPTOR);
    assert_eq!(
        scan_source("synthetic/emitted.rs", &emitted, UNWIND_INTERCEPTOR, true).len(),
        1,
        "an EMITTED interceptor must still be seen, or the generator allowlist entries \
         describe nothing"
    );
}
