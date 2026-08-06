//! Every recorded counterexample corpus sits on a path proptest will actually open.
//!
//! # The defect this exists to make loud
//!
//! A proptest corpus is a list of seeds for inputs that ONCE FALSIFIED A PROPERTY, with the
//! shrunk counterexample recorded beside each. It is not regenerable on demand: reproducing
//! one means re-running the random search that found it, which may take an unbounded number
//! of cases or may never recur at all once the surrounding code drifts.
//!
//! proptest computes the corpus path; nobody writes it down. So when the thing the path is
//! computed FROM moves, the corpus stays where it was and proptest looks somewhere else.
//! Nothing errors. The file keeps sitting in the directory listing, still carrying its seeds
//! and its `# shrinks to` text, still read by a human as "these cases are covered" — while
//! the seeds are not replayed and nothing says so. A stranded corpus is worse than a deleted
//! one, because a deleted one is visibly gone.
//!
//! This repository has now been bitten three times, by three different movements:
//!
//! | # | Corpus | What moved | Layout |
//! |---|---|---|---|
//! | 1 | `languages/tests/gen_rhocalc_prop.proptest-regressions` (52 seeds) | the LANGUAGE was renamed `RhoCalc` -> `Rholang`; the path is keyed on the language name | B |
//! | 2 | `prattail/proptest-regressions/automata/lex_weight.txt` (2 seeds) | the PROPERTIES moved crate, `prattail/src/automata/lex_weight.rs` -> `rigail/src/lex_weight.rs` | A |
//! | 3 | `prattail/proptest-regressions/decision_tree.txt` (1 seed) | the MODULE became a directory, `prattail/src/decision_tree.rs` -> `prattail/src/decision_tree/tests.rs` | A |
//!
//! Case 1 was made loud by `ast/tests/language_name_keyed_artifacts.rs`
//! (`every_prop_corpus_names_a_live_language`), which enumerates the language-name-keyed
//! artifacts. That guard is complete for what it covers and this file does not duplicate it —
//! but it covers layout B only, and cases 2 and 3 are layout A, where the key is not a
//! language name but a SOURCE FILE PATH. Case 2 was found by hand. Case 3 was found by this
//! file. Layout A had no strandedness check at all until now.
//!
//! # The two layouts
//!
//! **Layout B — `<proptest_corpus_dir>/gen_<lang>_prop.proptest-regressions`.** The pinned
//! `FileFailurePersistence::Direct` form emitted by
//! `macros/src/gen/test_gen/mod.rs::proptest_config_expr`. Keyed on the LANGUAGE NAME.
//!
//! **Layout A — `<crate>/proptest-regressions/<module path>.txt`.** proptest's DEFAULT
//! `FileFailurePersistence::SourceParallel` form, used by every hand-written `proptest!`
//! block. Keyed on the SOURCE FILE PATH. This is the layout this file governs.
//!
//! # How the layout-A path is inverted, and why the inversion is exact
//!
//! The check must be COMPUTED from the filesystem, not compared against a hand-written list —
//! a list is exactly the thing that goes stale on the next move. So this file re-derives, for
//! each corpus on disk, the source file proptest would have had to be looking at to name it.
//!
//! proptest 1.10.0, `src/test_runner/failure_persistence/file.rs`, the `SourceParallel` arm,
//! given `source` = the absolutized `file!()` of the declaring file and `sibling` =
//! `"proptest-regressions"`:
//!
//! ```text
//!   dir <- source
//!   while dir.pop():                       -- walk up
//!       if dir/lib.rs or dir/main.rs is a file: break     -- dir is now <crate>/src
//!   suffix <- source.strip_prefix(dir)      -- e.g. "decision_tree/tests.rs"
//!   result <- dir; result.pop()             -- <crate>
//!   result.push(sibling)                    -- <crate>/proptest-regressions
//!   result.push(suffix)                     -- <crate>/proptest-regressions/decision_tree/tests.rs
//!   result.set_extension("txt")             -- <crate>/proptest-regressions/decision_tree/tests.txt
//! ```
//!
//! Every step is a bijection on paths, so the inverse is total and unambiguous:
//!
//! ```text
//!   <crate>/proptest-regressions/<rest>.txt   <->   <crate>/src/<rest>.rs
//! ```
//!
//! ⚠ The inverse is `<crate>/src/<rest>.rs` and NEVER `<crate>/src/<rest>/mod.rs`. A property
//! declared in `<rest>/mod.rs` has `file!() = <crate>/src/<rest>/mod.rs`, so proptest names its
//! corpus `<rest>/mod.txt`, not `<rest>.txt`. Accepting `mod.rs` as a match would have made
//! this file pass over case 3 above, whose corpus is `decision_tree.txt` while the live module
//! is `decision_tree/mod.rs` — the exact defect, hidden by the exact leniency.
//!
//! The inversion has one premise — that the `dir` proptest stops at is `<crate>/src` — and
//! `the_layout_a_path_inversion_premise_holds` checks it rather than assuming it.
//!
//! # Retention, and the escape hatch that cannot swallow a seed
//!
//! A stranded corpus is never deleted: the seeds are not regenerable, so the record of where
//! they came from is worth keeping. The established repair is to RELOCATE the entries to the
//! live path and mark the original superseded, which is what
//! `prattail/proptest-regressions/automata/lex_weight.txt` and
//! `languages/tests/gen_rhocalc_prop.proptest-regressions` both do.
//!
//! That marker is an exemption, and an unchecked exemption is a hiding place. So
//! `no_superseded_corpus_loses_a_seed` requires every seed a superseded corpus records —
//! whether its `cc` line is active or commented out — to be present as an ACTIVE seed in some
//! corpus that is NOT superseded and IS on a live replay path. Marking a file superseded
//! therefore cannot make a counterexample disappear; it can only assert a move that the
//! filesystem confirms.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("`testkit` is a workspace member, so its manifest dir has a parent")
        .to_path_buf()
}

/// Directory names the sweep refuses to descend into.
///
/// `target` is build output; `scratch` and `scratchpad` are wipeable working areas that hold
/// COPIES of real source trees (`scratch/gate49/basefiles/prattail/src/...`), and counting a
/// copy would let a corpus look live because its double is.
const NOT_SOURCE: &[&str] = &["target", "scratch", "scratchpad"];

/// One corpus file on disk, with everything the checks below need to judge it.
#[derive(Debug)]
struct Corpus {
    /// Path relative to the repository root, for messages that a reader can act on.
    rel: String,
    /// Absolute path.
    path: PathBuf,
    /// `Some(source)` for layout A: the file proptest must be looking at to name this corpus.
    /// `None` for layout B, whose key is a language name (guarded in `ast/tests/`).
    declaring_source: Option<PathBuf>,
    /// Marked with a `SUPERSEDED` header — its seeds claim to live somewhere else now.
    superseded: bool,
    /// Seeds on an ACTIVE `cc` line: the ones proptest replays if it opens this file.
    active_seeds: Vec<String>,
    /// Seeds on a commented-out `# cc` line: retained for provenance, replayed by nothing.
    retired_seeds: Vec<String>,
}

impl Corpus {
    /// Every seed the file records, in either state.
    fn recorded_seeds(&self) -> impl Iterator<Item = &String> {
        self.active_seeds.iter().chain(self.retired_seeds.iter())
    }

    /// Layout A only: proptest will open this file iff the source it is named after exists and
    /// still declares at least one property.
    fn on_live_replay_path(&self) -> bool {
        match &self.declaring_source {
            // Layout B: liveness is a language-name question, answered in `ast/tests/`.
            None => !self.superseded,
            Some(src) => declares_a_property(src),
        }
    }
}

/// Does this source file declare at least one proptest property?
///
/// Both spellings that occur in this repository are accepted: the imported `proptest! {` and
/// the fully-qualified `proptest::proptest! {` (`prattail/src/wpda_walker.rs`).
fn declares_a_property(source: &Path) -> bool {
    fs::read_to_string(source)
        .map(|text| text.contains("proptest!"))
        .unwrap_or(false)
}

/// Is this corpus's FIRST LINE the `SUPERSEDED` ruling?
///
/// ⚠ ANCHORED TO LINE 1, and that is load-bearing. A first draft of this predicate accepted
/// the word anywhere in a leading comment, and it misclassified BOTH relocation TARGETS —
/// `rigail/proptest-regressions/lex_weight.txt` and
/// `prattail/proptest-regressions/decision_tree/tests.txt` — as superseded, because each
/// explains the move in prose ("the original is retained at its old path, marked SUPERSEDED").
/// A target wrongly marked superseded is excluded from the live set, and then
/// `no_superseded_corpus_loses_a_seed` reports the seeds it holds as lost: the check
/// contradicted the very repair it exists to certify. Being a file-level RULING rather than a
/// word in prose is what makes the marker mean something.
///
/// ⚠ Two spellings are in the tree and both are accepted deliberately, rather than a third
/// being invented: layout B writes `# SUPERSEDED:` (see
/// `ast/tests/language_name_keyed_artifacts.rs::SUPERSEDED_MARKER`) and layout A writes
/// `# ── SUPERSEDED (<tag>): RELOCATED to ...`. Tolerating the spelling is safe precisely
/// because `no_superseded_corpus_loses_a_seed` never trusts the marker on its own — it makes
/// the filesystem confirm every seed the marker claims to have moved.
fn is_superseded(text: &str) -> bool {
    let Some(first) = text.lines().next() else {
        return false;
    };
    if !first.starts_with('#') {
        return false;
    }
    first
        .trim_start_matches(|c: char| {
            c == '#' || c == '─' || c == '-' || c == '—' || c.is_whitespace()
        })
        .starts_with("SUPERSEDED")
}

/// The seed hash on a `cc <hash> # shrinks to ...` line, active or commented out.
fn seed_on(line: &str) -> Option<(bool, String)> {
    let trimmed = line.trim_start();
    let (active, body) = match trimmed.strip_prefix('#') {
        Some(rest) => (false, rest.trim_start()),
        None => (true, trimmed),
    };
    let rest = body.strip_prefix("cc ")?;
    let hash = rest.split_whitespace().next()?;
    // A seed hash is hex; anything else on a `cc `-prefixed line is prose, not a seed.
    if hash.len() < 16 || !hash.chars().all(|c| c.is_ascii_hexdigit()) {
        return None;
    }
    Some((active, hash.to_string()))
}

/// Every corpus in the repository, both layouts, computed from the filesystem.
fn corpora() -> Vec<Corpus> {
    let root = repo_root();
    let mut out = Vec::new();
    let mut pending = vec![root.clone()];

    while let Some(dir) = pending.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("dir entry").path();
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if path.is_dir() {
                if name.starts_with('.') || NOT_SOURCE.contains(&name) {
                    continue;
                }
                pending.push(path);
                continue;
            }

            // Layout A: `<crate>/proptest-regressions/<rest>.txt`.
            let layout_a = path.extension().and_then(|e| e.to_str()) == Some("txt")
                && path.ancestors().any(|a| {
                    a.file_name().and_then(|n| n.to_str()) == Some("proptest-regressions")
                });
            // Layout B: `<dir>/<name>.proptest-regressions`.
            let layout_b = name.ends_with(".proptest-regressions");
            if !layout_a && !layout_b {
                continue;
            }

            let declaring_source = layout_a.then(|| {
                let corpus_dir = path
                    .ancestors()
                    .find(|a| {
                        a.file_name().and_then(|n| n.to_str()) == Some("proptest-regressions")
                    })
                    .expect("`layout_a` is true only when such an ancestor exists");
                let crate_root = corpus_dir
                    .parent()
                    .expect("`<crate>/proptest-regressions` has `<crate>` as its parent");
                let rest = path
                    .strip_prefix(corpus_dir)
                    .expect("the corpus lives under the corpus directory it was found in");
                crate_root.join("src").join(rest).with_extension("rs")
            });

            let text = fs::read_to_string(&path).unwrap_or_default();
            let mut active_seeds = Vec::new();
            let mut retired_seeds = Vec::new();
            for line in text.lines() {
                match seed_on(line) {
                    Some((true, hash)) => active_seeds.push(hash),
                    Some((false, hash)) => retired_seeds.push(hash),
                    None => {},
                }
            }

            out.push(Corpus {
                rel: path
                    .strip_prefix(&root)
                    .unwrap_or(&path)
                    .display()
                    .to_string(),
                superseded: is_superseded(&text),
                declaring_source,
                active_seeds,
                retired_seeds,
                path,
            });
        }
    }
    out.sort_by(|a, b| a.rel.cmp(&b.rel));
    out
}

// ══════════════════════════════════════════════════════════════════════════════
// The premise of the inversion
// ══════════════════════════════════════════════════════════════════════════════

/// `<crate>/proptest-regressions/<rest>.txt` inverts to `<crate>/src/<rest>.rs` only because
/// the directory proptest stops its upward walk at is `<crate>/src`. It stops at the first
/// ancestor holding `lib.rs` or `main.rs`, so this is a claim about the crate's layout, and it
/// is checked rather than assumed: a crate that put its roots somewhere else would make every
/// verdict below meaningless while still passing.
#[test]
fn the_layout_a_path_inversion_premise_holds() {
    let all = corpora();
    let mut checked = 0usize;
    for c in all.iter().filter(|c| c.declaring_source.is_some()) {
        let src_dir = c
            .path
            .ancestors()
            .find(|a| a.file_name().and_then(|n| n.to_str()) == Some("proptest-regressions"))
            .and_then(Path::parent)
            .expect("a layout-A corpus has a crate root")
            .join("src");
        assert!(
            src_dir.join("lib.rs").is_file() || src_dir.join("main.rs").is_file(),
            "{} inverts to a source path under {}, but that directory holds neither `lib.rs` \
             nor `main.rs`. proptest's `SourceParallel` walk stops at the first ancestor that \
             does, so for this crate it would stop somewhere else and the inversion this file \
             performs would name the wrong source",
            c.rel,
            src_dir.display()
        );
        checked += 1;
    }
    assert!(
        checked >= 5,
        "only {checked} layout-A corpus/corpora were found; the sweep is not reaching \
         `<crate>/proptest-regressions/` and every check in this file would be measuring \
         nothing"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// The gate
// ══════════════════════════════════════════════════════════════════════════════

/// Every layout-A corpus names a source file that exists and still declares a property.
///
/// # Anti-vacuity
///
/// This test was RED when it was written, against an UNMUTATED tree:
/// `prattail/proptest-regressions/decision_tree.txt` was stranded, because
/// `prattail/src/decision_tree.rs` had become the directory `prattail/src/decision_tree/` and
/// the properties had moved to `tests.rs` inside it. Five live corpora passed in the same run.
/// That is the strongest evidence available that it discriminates: it failed on a real defect
/// nobody had reported, before any mutation was applied.
#[test]
fn every_layout_a_corpus_is_on_the_path_proptest_reads() {
    let all = corpora();
    let mut stranded: Vec<String> = Vec::new();
    let mut live = 0usize;

    for c in all.iter() {
        let Some(src) = &c.declaring_source else {
            continue; // layout B — `ast/tests/language_name_keyed_artifacts.rs` owns it
        };
        if declares_a_property(src) {
            live += 1;
        } else if c.superseded {
            // Its seeds claim to have moved. `no_superseded_corpus_loses_a_seed` makes the
            // filesystem confirm that claim, seed by seed.
            continue;
        } else {
            let why = if src.is_file() {
                "that file exists but declares no `proptest!` block, so nothing replays these \
                 seeds"
            } else {
                "that file does not exist"
            };
            stranded.push(format!("{} -> {} ({why})", c.rel, src.display()));
        }
    }

    assert!(
        stranded.is_empty(),
        "{} proptest corpus file(s) are named after a source file that no longer declares \
         them. proptest computes a layout-A corpus path from the `file!()` of the declaring \
         source (`FileFailurePersistence::SourceParallel`), so these files exist, hold \
         recorded counterexamples, and are never opened — the seeds are silently not \
         replayed:\n  {}\n\nRepair: RELOCATE the entries to the path the live source computes \
         (`<crate>/proptest-regressions/<path under src>.txt`) and mark the original with a \
         `SUPERSEDED` header recording where they went, as \
         `prattail/proptest-regressions/automata/lex_weight.txt` does. Do NOT delete the file \
         and do NOT delete the entries: a shrunk counterexample is not regenerable on demand.",
        stranded.len(),
        stranded.join("\n  ")
    );

    assert!(
        live >= 5,
        "only {live} layout-A corpus/corpora were seen on a live replay path; this test is not \
         reaching the repository and would pass over an empty set. Measured at the time of \
         writing: 5 (grammar_generality_prop, rigail/lex_weight, speculation/delivery, \
         wpda_walker, decision_tree/tests)"
    );
}

/// A `SUPERSEDED` header may relocate a seed. It may not lose one.
///
/// Covers BOTH layouts, because the exemption is available in both and the property — "the
/// counterexample is still replayed by something" — is the same one.
///
/// # Why this is what makes the exemption safe
///
/// `every_layout_a_corpus_is_on_the_path_proptest_reads` lets a superseded corpus off. On its
/// own that would be a hiding place: writing the header would silence the gate whether or not
/// the seeds went anywhere. Here the marker is never trusted. Every seed the superseded file
/// records must be found, by hash, as an ACTIVE seed in some corpus that is not itself
/// superseded and is on a live replay path.
#[test]
fn no_superseded_corpus_loses_a_seed() {
    let all = corpora();

    // Where a seed is actively replayed from, by hash.
    let mut replayed_by: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for c in all
        .iter()
        .filter(|c| !c.superseded && c.on_live_replay_path())
    {
        for seed in &c.active_seeds {
            replayed_by.entry(seed.as_str()).or_default().push(&c.rel);
        }
    }

    let superseded: Vec<&Corpus> = all.iter().filter(|c| c.superseded).collect();
    let mut lost: Vec<String> = Vec::new();
    let mut confirmed = 0usize;
    for c in &superseded {
        for seed in c.recorded_seeds() {
            match replayed_by.get(seed.as_str()) {
                Some(_) => confirmed += 1,
                None => lost.push(format!("{} records `cc {seed}`", c.rel)),
            }
        }
    }

    assert!(
        lost.is_empty(),
        "{} recorded counterexample(s) are held ONLY by a corpus marked `SUPERSEDED`, and no \
         live corpus replays them. A `SUPERSEDED` header asserts that the entries moved \
         somewhere proptest still reads; these did not:\n  {}\n\nEither add the seed to the \
         successor corpus (byte-identical, `# shrinks to` text preserved) or remove the \
         `SUPERSEDED` header so the strandedness gate reports the file honestly.",
        lost.len(),
        lost.join("\n  ")
    );

    assert!(
        confirmed >= 55,
        "only {confirmed} relocated seed(s) across {} superseded corpus/corpora were confirmed; \
         the sweep is not finding them and this test would pass over an empty set. Measured at \
         the time of writing: 55 = 52 (`gen_rhocalc_prop`) + 2 (`automata/lex_weight`) + 1 \
         (`decision_tree`). A DROP means a provenance file was deleted — which the repair \
         policy forbids, because a shrunk counterexample is not regenerable on demand.",
        superseded.len()
    );
}

/// The corpus population is what the campaign that closed #104 left behind, and a drop in it
/// is a coverage loss that should be argued for rather than noticed later.
///
/// This is a FLOOR, not an equality: adding a counterexample is how the suite gets stronger,
/// so growth passes and shrinkage fails.
#[test]
fn the_recorded_counterexample_population_does_not_shrink() {
    let all = corpora();
    let distinct: std::collections::BTreeSet<&String> = all
        .iter()
        .filter(|c| !c.superseded)
        .flat_map(|c| c.active_seeds.iter())
        .collect();

    // 111 = 101 across the thirteen live generated-language corpora (52 of them merged from
    // `gen_rhocalc_prop` into `gen_rholang_prop`) + 10 across the five live layout-A corpora.
    // Independently corroborated: `testkit/tests/ctor_engine.rs`'s census also counts 111
    // recorded counterexamples, reached by a different route (citation and exemption rather
    // than replay path), and the two agree.
    assert!(
        distinct.len() >= 111,
        "only {} distinct actively-replayed counterexample(s) were found; the campaign that \
         closed #104 left 111. A shrinking corpus means seeds stopped being replayed — which \
         is the defect this file exists to catch, arriving by a different route (entries \
         deleted rather than the file stranded).",
        distinct.len()
    );

    // The three historical strand sites, pinned by name so a regression that re-strands one is
    // reported as itself rather than as a number that drifted.
    for (rel, why) in [
        (
            "languages/tests/gen_rholang_prop.proptest-regressions",
            "the RhoCalc merge target",
        ),
        ("rigail/proptest-regressions/lex_weight.txt", "the lex_weight relocation target"),
        (
            "prattail/proptest-regressions/decision_tree/tests.txt",
            "the decision_tree relocation target",
        ),
    ] {
        let c = all
            .iter()
            .find(|c| c.rel == rel)
            .unwrap_or_else(|| panic!("{rel} ({why}) is missing from the repository"));
        assert!(
            !c.active_seeds.is_empty(),
            "{rel} ({why}) holds no active `cc` entry; the seeds it was created to replay are gone"
        );
        assert!(
            !c.superseded,
            "{rel} ({why}) is itself marked SUPERSEDED; the relocation target cannot be the \
             thing that was relocated away from"
        );
    }
}
