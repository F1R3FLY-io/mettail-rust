//! **A-6 — capability A touches ZERO lines under `macros/src/gen/term_ops/`.**
//!
//! # The property, and why it is worth a standing guard rather than a paragraph
//!
//! A token-text capture leaf carries TWO properties, and the whole safety argument for
//! capability A is that they are already separated — by a MODULE BOUNDARY, not by a
//! convention someone must respect:
//!
//! ```text
//!  ┌───────────────────────────────┬─────────────────────────────────┬────────────────────┐
//!  │ property                      │ emitted in                      │ keyed on           │
//!  ├───────────────────────────────┼─────────────────────────────────┼────────────────────┤
//!  │ INERTNESS                     │ macros/src/gen/term_ops/*.rs    │ FieldInfo::        │
//!  │  Eq · Hash · Ord · subst ·    │ + types/enums.rs                │   is_opaque_leaf() │
//!  │  normalize · semantic_hash ·  │                                 │                    │
//!  │  display · is_ground ·        │                                 │                    │
//!  │  term_depth · Drop ·          │                                 │                    │
//!  │  match_pattern                │                                 │                    │
//!  ├───────────────────────────────┼─────────────────────────────────┼────────────────────┤
//!  │ RECOVERABILITY in a fold body │ macros/src/gen/runtime/         │ FieldInfo::        │
//!  │                               │   dovetail_report/*.rs          │   is_opaque_leaf() │
//!  └───────────────────────────────┴─────────────────────────────────┴────────────────────┘
//! ```
//!
//! The two read the SAME flag at DISJOINT call sites: nothing under `term_ops/` consults the
//! Dovetail derivation, and nothing under `dovetail_report/` emits a term operation. So making
//! a token-text leaf recoverable cannot make it non-inert — *provided* the change stayed on
//! the recoverability side. This test is the standing evidence that it did, and it is a
//! stronger claim than "we read the code": it is a claim about a DIFF.
//!
//! # Why a diff rather than a source-content assertion
//!
//! A content assertion ("no file under `term_ops/` mentions `FieldTokenText`") is satisfiable
//! by a change that rewrites `term_ops/` in some *other* way — reordering a match, widening a
//! guard, adding a descent. Inertness is a property of the emitted operations, not of a token
//! spelling, so the guard has to be over the emitted-code SOURCE as a whole.
//!
//! # Anti-vacuity
//!
//! An "N == 0" assertion is worthless if the measurement always returns 0 — a mistyped path,
//! a `--` that swallowed its argument, a commit that was never found. So the SAME measurement
//! is run over `macros/src/gen/runtime/dovetail_report/`, where capability A did its work, and
//! is required to be NON-ZERO. If the plumbing is broken, that control fails first and says so.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The trailer capability A stamps into its commit message. Naming the commit by a marker
/// rather than by a hash keeps this test stable across every later commit by anyone: it
/// always inspects the SAME historical change, and later work under `term_ops/` (which is
/// legitimate) cannot make it fail.
const CAPABILITY_A_MARKER: &str = "Capability-A-Guard: term-ops-untouched";

/// The tree capability A must not have touched.
const FENCED_PATH: &str = "macros/src/gen/term_ops";

/// The tree capability A DID change — the anti-vacuity control.
const CHANGED_PATH: &str = "macros/src/gen/runtime/dovetail_report";

fn workspace_root() -> PathBuf {
    // `macros/` → the workspace root. `CARGO_MANIFEST_DIR` is the only path the harness
    // guarantees; deriving from it keeps the test independent of the invoking directory.
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the `macros` package must live inside the workspace root")
        .to_path_buf()
}

fn git(root: &Path, args: &[&str]) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-c")
        .arg("core.fsmonitor=false")
        .args(args)
        .current_dir(root)
        .output()
        .map_err(|e| format!("could not run `git {}`: {e}", args.join(" ")))?;
    if !output.status.success() {
        return Err(format!(
            "`git {}` failed ({}): {}",
            args.join(" "),
            output.status,
            String::from_utf8_lossy(&output.stderr).trim(),
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

/// The commit hash of capability A, located by its marker.
///
/// ⚠ A `None` here would be a SILENT PASS for the whole guard, so it is an error instead:
/// a measurement that cannot find its subject has measured nothing, and reporting 0 changed
/// lines for a commit that was never located is precisely the false zero this file exists to
/// prevent.
fn capability_a_commit(root: &Path) -> Result<String, String> {
    let hash = git(root, &["log", "--format=%H", "-1", "--grep", CAPABILITY_A_MARKER])?;
    if hash.is_empty() {
        return Err(format!(
            "no commit in this history carries the marker {CAPABILITY_A_MARKER:?}. This guard \
             inspects capability A's own commit, so it cannot run before that commit exists — \
             and it must not report a vacuous zero instead.",
        ));
    }
    Ok(hash)
}

/// Total lines added + removed by `commit` under `path`.
fn changed_lines(root: &Path, commit: &str, path: &str) -> Result<u64, String> {
    let numstat = git(
        root,
        &["diff", "--numstat", &format!("{commit}^"), commit, "--", path],
    )?;
    let mut total = 0u64;
    for line in numstat.lines() {
        let mut fields = line.split('\t');
        // A binary file renders as `-\t-\t<path>`; no file under either fenced tree is
        // binary, and counting such a line as 0 would understate the diff, so it is an error.
        let added = fields.next().unwrap_or("-");
        let removed = fields.next().unwrap_or("-");
        if added == "-" || removed == "-" {
            return Err(format!(
                "unexpected binary diff entry under {path:?} in {commit}: {line:?}",
            ));
        }
        total += added.parse::<u64>().map_err(|e| format!("bad numstat {line:?}: {e}"))?;
        total += removed.parse::<u64>().map_err(|e| format!("bad numstat {line:?}: {e}"))?;
    }
    Ok(total)
}

#[test]
fn capability_a_changed_no_line_under_term_ops() {
    let root = workspace_root();
    let commit = capability_a_commit(&root).expect("capability A's commit must be locatable");

    // ── ANTI-VACUITY CONTROL, asserted FIRST ─────────────────────────────────────────────
    // The same measurement, over the tree capability A did change. If this is 0, the
    // measurement is broken (wrong path, wrong commit, swallowed `--`) and the fenced-tree
    // zero below would be a false zero rather than evidence.
    let changed = changed_lines(&root, &commit, CHANGED_PATH)
        .expect("the control measurement must run");
    assert!(
        changed > 0,
        "ANTI-VACUITY: commit {commit} must show a NON-ZERO diff under {CHANGED_PATH}, \
         otherwise this measurement is not measuring anything and the fenced-tree assertion \
         below is vacuous",
    );

    // ── THE PROPERTY ─────────────────────────────────────────────────────────────────────
    let fenced =
        changed_lines(&root, &commit, FENCED_PATH).expect("the fenced measurement must run");
    assert_eq!(
        fenced, 0,
        "capability A must not change ANY line under {FENCED_PATH}: inertness \
         (Eq/Hash/Ord/subst/normalize/semantic_hash/display/is_ground/term_depth/Drop/\
         match_pattern) is emitted there and keyed on `FieldInfo::is_opaque_leaf()`, while \
         recoverability is emitted under {CHANGED_PATH} and keyed on the same flag at \
         DISJOINT call sites. Preserving inertness is a property of that separation, not of \
         an argument — {fenced} changed line(s) in {commit} break it.",
    );
}
