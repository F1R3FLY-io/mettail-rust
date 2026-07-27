//! Every ```` ```ignore ```` doc fence in the workspace must say WHY it is not compiled.
//!
//! ## The measurement this file exists to prevent recurring
//!
//! `cargo test --doc -p macros` once printed `10 tests, 0 passed, 0 failed, 10 ignored`.
//! Not one line of example code in that crate reached the compiler. Across nine
//! packages, 43 of 61 doctests were in that state. The examples were not wrong — 41
//! of the 43 compiled cleanly the moment they were switched on — but nothing kept
//! them true, and the two that had rotted (`BooleanWeight::reachable()`, which never
//! existed, and a `LexicographicWeight` literal missing two fields the struct gained
//! later) had been uncompilable for an unknown span of commits.
//!
//! `ignore` is not `no_run`. `no_run` compiles the block and skips execution;
//! `ignore` skips the compiler entirely. A fence that carries it makes an assertion —
//! "this is Rust I chose not to run" — and that assertion is unverifiable, so it must
//! be argued in writing at the point of use.
//!
//! ## The invariant
//!
//! For every doc-comment fence whose info string carries the `ignore` attribute, the
//! nearest preceding non-blank line must be
//!
//! ```text
//! // ignore-justification: <reason>
//! ```
//!
//! a plain `//` comment (never a doc comment, so it does not render) stating what
//! makes the block uncompilable. The four legitimate answers this codebase has found
//! are: the block is not Rust and should be ```` ```text ````; it names a GENERATED
//! language or category that no dependency edge can reach; it invokes a macro whose
//! expansion names crates this crate does not depend on; or it loads a file off disk
//! that a doctest has no way to provide.
//!
//! The check fails at the commit that introduces an unjustified fence, not at the next
//! audit. It reads only the source text, allocates its own buffers, and touches no
//! shared state, so it is deterministic and safe to run in parallel with anything else.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

/// The comment that discharges the obligation.
const JUSTIFICATION_MARKER: &str = "// ignore-justification:";

/// Paths that cannot carry a justification yet, each with the reason and the
/// condition that retires it.
///
/// This list is CHECKED FOR STALENESS below: the moment an entry stops being
/// necessary, this test fails and tells you to delete the entry. An exemption
/// therefore cannot outlive the situation that earned it, which is the failure mode
/// that makes allowlists rot.
const EXEMPT: &[(&str, &str)] = &[(
    "rholang-runtime/src/rhocalc_ast.rs",
    "Owned by concurrent task #47 and unsafe to edit from here. Its single fence holds \
     a commented-out previous body of `canonicalize_arity_pattern` — an all-comment \
     historical record, so the correct disposition is ```text rather than a \
     justification. Retire this entry by making that change.",
)];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("dovetail crate has a workspace parent")
        .to_path_buf()
}

fn repo_relative(path: &Path) -> String {
    path.strip_prefix(repo_root())
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

/// The `src/` tree of every workspace member, read from the root manifest.
///
/// Derived from `members = [...]` rather than hard-coded so a NEW crate is covered the
/// day it joins the workspace. A hard-coded list is the same defect shape as the CI
/// package enumeration this campaign had to widen: it silently omits whatever was
/// added after it was written.
fn workspace_member_src_roots() -> Vec<PathBuf> {
    let manifest = fs::read_to_string(repo_root().join("Cargo.toml"))
        .expect("the workspace root manifest is readable");
    let start = manifest
        .find("members")
        .and_then(|at| manifest[at..].find('[').map(|off| at + off + 1))
        .expect("the root manifest declares a `members` array");
    let len = manifest[start..]
        .find(']')
        .expect("the `members` array is closed");

    let mut roots: Vec<PathBuf> = manifest[start..start + len]
        .split(',')
        .filter_map(|entry| {
            let name = entry.trim().trim_matches('"').trim();
            (!name.is_empty()).then(|| repo_root().join(name).join("src"))
        })
        .filter(|root| root.exists())
        .collect();
    roots.sort();
    assert!(
        roots.len() >= 10,
        "expected the workspace to have at least 10 members with a src/ tree, parsed {}",
        roots.len(),
    );
    roots
}

fn discover_rust_files(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_path_buf()];
    let mut files = Vec::new();
    while let Some(path) = pending.pop() {
        let metadata =
            fs::metadata(&path).unwrap_or_else(|err| panic!("failed to stat {path:?}: {err}"));
        if metadata.is_dir() {
            // `generated` holds macro output, which nobody edits by hand.
            if path.file_name().and_then(|name| name.to_str()) == Some("generated") {
                continue;
            }
            for entry in fs::read_dir(&path)
                .unwrap_or_else(|err| panic!("failed to read directory {path:?}: {err}"))
            {
                pending.push(entry.expect("source directory entry").path());
            }
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
            files.push(path);
        }
    }
    files.sort();
    files
}

/// The text of a doc comment line, with its `///` or `//!` prefix removed.
///
/// Returns `None` for anything that is not a doc comment. Restricting the scan to doc
/// comments is what keeps a fence inside ordinary prose, a string literal, or a `//`
/// comment from being mistaken for a doctest — only doc comments become doctests.
fn doc_comment_body(line: &str) -> Option<&str> {
    let trimmed = line.trim_start();
    let rest = trimmed
        .strip_prefix("///")
        .or_else(|| trimmed.strip_prefix("//!"))?;
    Some(rest.trim_start())
}

/// The info string of a fence opener, or `None` if this line opens no fence.
///
/// A CLOSING fence has an empty info string, so it never carries `ignore` and is
/// filtered out by [`info_string_ignores`] rather than needing a separate pass.
fn fence_info_string(doc_body: &str) -> Option<&str> {
    doc_body.strip_prefix("```")
}

/// Whether a fence info string carries rustdoc's `ignore` attribute.
///
/// rustdoc separates attributes by commas and whitespace, so `ignore`,
/// `rust,ignore`, and `ignore,should_panic` all mean the same thing here. The
/// targeted form `ignore-<target>` counts too: it also skips compilation, on the
/// targets it names. A language tag that merely CONTAINS the substring — a
/// hypothetical `ignorelist` — deliberately does not match, which is why this
/// tokenizes instead of calling `contains`.
fn info_string_ignores(info: &str) -> bool {
    info.split([',', ' ', '\t'])
        .map(str::trim)
        .any(|attr| attr == "ignore" || attr.starts_with("ignore-"))
}

/// Whether the fence opening at `fence_line` carries its justification.
///
/// The marker must be the nearest preceding NON-BLANK line. Blank lines are stepped
/// over so the comment may be separated from the fence for readability, but a doc line
/// in between does not qualify — the comment has to sit with the fence it explains,
/// not drift up into unrelated prose.
fn is_justified(lines: &[&str], fence_line: usize) -> bool {
    lines[..fence_line]
        .iter()
        .rev()
        .find(|line| !line.trim().is_empty())
        .is_some_and(|line| line.trim_start().starts_with(JUSTIFICATION_MARKER))
}

/// One `ignore` fence that failed to argue for itself.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
struct UnjustifiedFence {
    path: String,
    line: usize,
    opener: String,
}

fn collect_unjustified() -> (Vec<UnjustifiedFence>, BTreeSet<String>) {
    let exempt: BTreeSet<&str> = EXEMPT.iter().map(|(path, _)| *path).collect();
    let mut offenders = Vec::new();
    let mut exempt_paths_that_offend = BTreeSet::new();

    for root in workspace_member_src_roots() {
        for file in discover_rust_files(&root) {
            let relative = repo_relative(&file);
            let source = fs::read_to_string(&file)
                .unwrap_or_else(|err| panic!("failed to read {file:?}: {err}"));
            let lines: Vec<&str> = source.lines().collect();

            for (index, line) in lines.iter().enumerate() {
                let Some(body) = doc_comment_body(line) else {
                    continue;
                };
                let Some(info) = fence_info_string(body) else {
                    continue;
                };
                if !info_string_ignores(info) || is_justified(&lines, index) {
                    continue;
                }
                // `exempt` matches the file itself or any file beneath a module
                // directory of the same name, so a split-up module stays covered.
                match exempt.iter().find(|prefix| {
                    relative == **prefix
                        || relative.starts_with(&format!("{}/", prefix.trim_end_matches(".rs")))
                }) {
                    Some(prefix) => {
                        exempt_paths_that_offend.insert((*prefix).to_string());
                    },
                    None => offenders.push(UnjustifiedFence {
                        path: relative.clone(),
                        line: index + 1,
                        opener: line.trim().to_string(),
                    }),
                }
            }
        }
    }

    offenders.sort();
    (offenders, exempt_paths_that_offend)
}

/// Every `ignore` fence states what makes it uncompilable.
#[test]
fn every_ignore_fence_carries_a_justification() {
    let (offenders, _) = collect_unjustified();
    assert!(
        offenders.is_empty(),
        "{} doc fence(s) carry `ignore` without a recorded reason.\n\n\
         `ignore` does not compile the block AT ALL (unlike `no_run`, which compiles it \
         and skips only execution), so nothing checks that the example is still valid \
         Rust. Either make it compile, or say why it cannot.\n\n\
         Fix, in order of preference:\n  \
         1. If the block is not Rust — a grammar-rule DSL, a `<Cat>` schematic, a \
         body-less signature, a bare match arm — change the fence to ```text.\n  \
         2. If it is Rust that needs context, supply the context on `#`-hidden lines \
         and drop `ignore`. Hidden lines do not render, so the reader still sees only \
         the illustrative code.\n  \
         3. If running it would have a side effect a test must not have, use `no_run` \
         — it still COMPILES, which is the whole point.\n  \
         4. Only if it genuinely cannot compile, keep `ignore` and put\n     \
         `{JUSTIFICATION_MARKER} <reason>`\n     on the line immediately above the \
         fence.\n\nOffenders:\n{}",
        offenders.len(),
        offenders
            .iter()
            .map(|f| format!("  {}:{}  {}", f.path, f.line, f.opener))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

/// No exemption outlives the situation that earned it.
///
/// An allowlist whose entries are never re-examined is how a temporary hole becomes a
/// permanent one. This asserts the converse of the check above: every exempt path must
/// STILL have an unjustified fence. When someone fixes one, this test goes red and
/// names the entry to delete.
#[test]
fn no_exemption_outlives_its_reason() {
    let (_, still_offending) = collect_unjustified();
    let stale: Vec<&(&str, &str)> = EXEMPT
        .iter()
        .filter(|(path, _)| !still_offending.contains(*path))
        .collect();

    assert!(
        stale.is_empty(),
        "{} exemption(s) in EXEMPT are no longer needed — the fence they cover now \
         compiles, carries a justification, or is gone. Delete them from `EXEMPT` in \
         {}:\n{}",
        stale.len(),
        file!(),
        stale
            .iter()
            .map(|(path, reason)| format!("  {path}\n    (was: {reason})"))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

/// The scanner recognises the fence spellings that actually occur, and only those.
///
/// Without this, the guard above could pass by finding nothing — the same
/// could-not-fail shape it exists to catch. Two of the checks this campaign examined
/// passed while executing nothing at all.
#[test]
fn scanner_recognises_ignore_spellings() {
    // Both spellings in use across the workspace, plus the targeted and combined forms.
    for info in ["ignore", "rust,ignore", "ignore,should_panic", "ignore-x86"] {
        assert!(info_string_ignores(info), "should have matched `{info}`");
    }
    // A closing fence, ordinary language tags, and a tag that merely contains the word.
    for info in ["", "text", "rust", "no_run", "rust,no_run", "ignorelist"] {
        assert!(!info_string_ignores(info), "should NOT have matched `{info}`");
    }

    assert_eq!(doc_comment_body("    /// ```ignore"), Some("```ignore"));
    assert_eq!(doc_comment_body("//! ```rust,ignore"), Some("```rust,ignore"));
    // A `//` comment is not a doc comment and never becomes a doctest.
    assert_eq!(doc_comment_body("// ```ignore"), None);
    assert_eq!(doc_comment_body("let s = \"```ignore\";"), None);

    assert_eq!(fence_info_string("```ignore"), Some("ignore"));
    assert_eq!(fence_info_string("```"), Some(""));
    assert_eq!(fence_info_string("not a fence"), None);

    let justified = ["// ignore-justification: because", "/// ```ignore"];
    assert!(is_justified(&justified, 1));
    let blank_between = ["// ignore-justification: because", "", "/// ```ignore"];
    assert!(is_justified(&blank_between, 2));
    // A doc line between the marker and the fence breaks the association.
    let drifted = ["// ignore-justification: because", "/// prose", "/// ```ignore"];
    assert!(!is_justified(&drifted, 2));
    let bare = ["/// # Example", "/// ```ignore"];
    assert!(!is_justified(&bare, 1));
}

/// The walk actually reaches the workspace, and finds the fences that are really there.
///
/// A scanner that silently walked an empty tree would make the guard vacuous, so this
/// pins the discovery end too: the member list must include known crates, and the
/// justified fences this campaign wrote must be visible to the scan.
#[test]
fn scan_reaches_the_workspace_and_sees_real_fences() {
    let roots = workspace_member_src_roots();
    let names: BTreeSet<String> = roots.iter().map(|root| repo_relative(root)).collect();
    for expected in ["ast/src", "macros/src", "prattail/src", "runtime/src", "testkit/src"] {
        assert!(names.contains(expected), "member scan missed {expected}: {names:?}");
    }

    let total_files: usize = roots.iter().map(|root| discover_rust_files(root).len()).sum();
    assert!(total_files > 100, "expected to walk >100 source files, walked {total_files}");

    // The fences deliberately kept as `ignore` are found AND read as justified, so the
    // guard is exercising the justification path rather than finding nothing at all.
    let justified_by_hand = [
        "ast/src/compose.rs",
        "ast/src/fragment.rs",
        "macros/src/gen/runtime/environment.rs",
        "macros/src/gen/term_gen/random.rs",
        "macros/src/gen/test_gen/mod.rs",
        "macros/src/lib.rs",
        "testkit/src/program.rs",
    ];
    for relative in justified_by_hand {
        let source = fs::read_to_string(repo_root().join(relative))
            .unwrap_or_else(|err| panic!("failed to read {relative}: {err}"));
        let lines: Vec<&str> = source.lines().collect();
        let fences: Vec<usize> = lines
            .iter()
            .enumerate()
            .filter(|(_, line)| {
                doc_comment_body(line)
                    .and_then(fence_info_string)
                    .is_some_and(info_string_ignores)
            })
            .map(|(index, _)| index)
            .collect();
        assert!(!fences.is_empty(), "{relative} should still hold an `ignore` fence");
        for fence in fences {
            assert!(
                is_justified(&lines, fence),
                "{relative}:{} lost its justification",
                fence + 1,
            );
        }
    }
}
