//! The ONE recursive walk that finds every file which may declare a `language!`.
//!
//! # The defect this exists to make impossible
//!
//! Four independent guards decided, each in its own hand-written loop, which files they
//! would look at for a `language!` declaration:
//!
//! | site | what it walked | outcome |
//! |---|---|---|
//! | `ast/tests/dovetail_language_inventory.rs::language_files` | manifest roots, recursive | ✅ total |
//! | `dovetail/tests/language_inventory.rs::discover_rust_files` | manifest roots, recursive | ✅ total |
//! | `ast/tests/language_name_keyed_artifacts.rs::language_files` | manifest roots, recursive | ✅ total |
//! | `ast/tests/language_name_keyed_artifacts.rs::definition_files_that_declare_a_language` | two hard-coded directories, **one level deep** | ❌ **narrow** |
//!
//! The first three were widened together in `c58d3845` when a definition in a top-level
//! `languages/tests/*.rs` turned out to be audited by nobody. The fourth was in the SAME
//! FILE as the third, 505 lines away, and was not touched — so it kept deciding the domain
//! of `BUNDLED_LANGUAGES` from a two-entry directory list that could not see
//! `languages/src/composition/` (four `language!` bodies, one subdirectory down) or any
//! top-level `languages/tests/*.rs` (six files, eight bodies).
//!
//! A walk written out `n` times is a walk that can be widened `n − 1` times. It is written
//! out ONCE here, and every audit reads it.
//!
//! ```text
//!            [package.metadata.mettail] language_roots   ← the single declaration
//!                             │
//!                     manifest::language_roots
//!                             │
//!                    language_scan::language_files        ← THIS MODULE (the WALK)
//!                             │
//!            ┌────────────────┼────────────────┬─────────────────────┐
//!            ▼                ▼                ▼                     ▼
//!    ast structural      dovetail textual   name-keyed          binder-congruence
//!    inventory audit     inventory audit    artifact audit      bundled subject
//!            │                │                │                     │
//!            └────────────────┴────────────────┴─────────────────────┘
//!                     each keeps its OWN declaration DECISION
//! ```
//!
//! # What is shared, and what is deliberately NOT
//!
//! ★ This module shares the **walk**. It never shares the **decision**. Whether a file
//! DECLARES a language is answered structurally by `ast`'s audits (`syn::parse_file`, then
//! item-level `language!` macros including inline `mod` bodies) and textually by
//! `dovetail`'s (`declarations_only` + `is_language_macro_source`). Having two independent
//! answers is the point of having two audits —
//! `ast/tests/dovetail_language_inventory.rs` states so directly — and collapsing them into
//! one shared predicate would leave a single point of failure where there are currently
//! two mutually-checking ones. Only [`mentions_language_invocation`] is shared, and it is
//! not a decision: it is a strict over-approximation whose only job is to spare the
//! expensive parse on files that provably cannot invoke the macro.
//!
//! # Why nothing here may reference anything outside `std`
//!
//! `dovetail` depends on exactly one workspace crate (`rigail`) by design, so its audit
//! pulls this file in with `#[path = "../../ast/src/language_scan.rs"]` — exactly as it
//! already does with [`crate::manifest`]. The file therefore has to compile standing on
//! its own: no `syn`, no `proc_macro2`, no `mettail-*`. The one intra-crate reference it
//! makes, `crate::manifest`, resolves in both hosts, because `manifest` is a root-level
//! module of `ast` AND a root-level `#[path]` module of the `dovetail` test crate.
//!
//! # Failure is loud, never silent
//!
//! [`language_files`] returns `Result`. A root that cannot be resolved, or a path that
//! cannot be stat'd, is an error naming what failed — never an empty list. An empty list
//! is the exact shape of a check that cannot fail: every consumer's assertion has the form
//! "everything the walk found satisfies P", which is vacuously true over nothing.
//!
//! The repository-wide sweep [`repository_rust_files`] is the one place that skips quietly,
//! and only for the two conditions that are not findings: a broken symlink (`metadata`
//! fails) and a directory the process cannot read. Its consumers pair it with their own
//! non-vacuity floor.

use std::fs;
use std::path::{Path, PathBuf};

/// Directories under a language root that hold no hand-written source.
///
/// `target` is build output and `generated` is macro output — the `language!` EXPANSION,
/// never a declaration. Nothing else is skipped. In particular `bin` is NOT skipped: a
/// `language!` written into `languages/src/bin/` is a declaration like any other, and a
/// `bin` skip that used to sit in two of these walks made that directory a place a
/// definition could be written and never audited.
pub const NON_SOURCE_DIRECTORIES: &[&str] = &["target", "generated"];

/// Whether the REPOSITORY-WIDE sweep declines to enter a directory.
///
/// `target` is build output; `scratchpad` is the documented wipeable campaign scratch area
/// (gitignored, never a build input, cleared by the harness), so a stale probe left in
/// either must not be able to fail a suite. DOT-directories are tooling state and never
/// hold hand-written source: `.git` is object storage, and `.formal-tmp` holds the formal
/// pipeline's `cargo expand` dumps — two 40 MB single-item files whose scan dominated
/// everything else the sweep does.
pub fn is_swept_over(directory_name: &str) -> bool {
    directory_name.starts_with('.') || matches!(directory_name, "target" | "scratchpad")
}

/// Every `.rs` file under `root`, recursively, skipping [`NON_SOURCE_DIRECTORIES`].
///
/// Sorted, so two consumers of the same root see the same order and a diff of their output
/// is a real difference rather than a `read_dir` accident.
pub fn rust_files_under(root: &Path) -> Result<Vec<PathBuf>, String> {
    let mut pending = vec![root.to_path_buf()];
    let mut files = Vec::new();

    while let Some(path) = pending.pop() {
        let metadata = fs::metadata(&path)
            .map_err(|err| format!("failed to stat {}: {err}", path.display()))?;
        if metadata.is_dir() {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if NON_SOURCE_DIRECTORIES.contains(&name) {
                continue;
            }
            let entries = fs::read_dir(&path)
                .map_err(|err| format!("failed to read directory {}: {err}", path.display()))?;
            for entry in entries {
                let entry = entry.map_err(|err| {
                    format!("failed to read an entry of {}: {err}", path.display())
                })?;
                pending.push(entry.path());
            }
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.push(path);
        }
    }

    files.sort();
    Ok(files)
}

/// Every `.rs` file under the manifest-declared language roots.
///
/// The roots come from `[package.metadata.mettail] language_roots` through
/// [`crate::manifest::language_roots`] — READ, never written out here, because a second
/// literal is a second thing to widen and the whole point of this module is that there is
/// one.
///
/// A declared root that does not exist on disk is skipped rather than failing: the audits'
/// own totality invariants (`language_declarations_cannot_hide_outside_the_scanned_roots`)
/// are what turn a stale root into a failure that NAMES the escaped declarations, which is
/// a far more useful report than "directory missing".
pub fn language_files(workspace_root: &Path) -> Result<Vec<PathBuf>, String> {
    let roots = crate::manifest::language_roots(workspace_root)?;
    let mut files = Vec::new();
    for root in roots.into_iter().filter(|root| root.exists()) {
        files.extend(rust_files_under(&root)?);
    }
    files.sort();
    Ok(files)
}

/// Every `.rs` file in the repository, for the totality sweeps that prove the language
/// roots are not hiding a declaration somewhere else.
///
/// Sorted. Skips [`is_swept_over`] directories, broken symlinks and unreadable
/// directories; everything else is returned and the caller decides what it is.
pub fn repository_rust_files(workspace_root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![workspace_root.to_path_buf()];
    let mut files = Vec::new();

    while let Some(path) = pending.pop() {
        let Ok(metadata) = fs::metadata(&path) else {
            continue; // a broken symlink is not a declaration
        };
        if metadata.is_dir() {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if is_swept_over(name) {
                continue;
            }
            let Ok(entries) = fs::read_dir(&path) else {
                continue;
            };
            for entry in entries {
                pending.push(entry.expect("repository directory entry").path());
            }
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.push(path);
        }
    }

    files.sort();
    files
}

/// Whether `source` could contain a `language!` INVOCATION.
///
/// A Rust macro invocation is `path`, `!`, then a delimiter, with only whitespace and
/// comments allowed in between — so a file that never spells `language!` followed by `(`,
/// `[` or `{` cannot invoke it, and this gate cannot hide a declaration from a sweep. It is
/// a strict over-approximation in the other direction (a doc comment showing
/// `language! { … }` passes), which is harmless because the caller's own decision then
/// runs.
///
/// The gate matters because the step behind it is the expensive one: the workspace holds
/// 179 files that merely NAME the macro, 7.2 MB in all, one of them 1.2 MB, and `syn` in a
/// debug test binary is slow enough on that to dominate a run. The gate admits 57 files
/// totalling 1.1 MB.
pub fn mentions_language_invocation(source: &str) -> bool {
    mentions_macro_invocation(source, "language!")
}

/// Whether `source` could contain either a complete `language!` declaration or
/// a reusable `language_fragment!` declaration.
///
/// Migration and module-composition inventories use this broader gate;
/// language-only audits retain [`mentions_language_invocation`]. Like the
/// language-only gate, this deliberately over-approximates before a structural
/// parser makes the actual declaration decision.
pub fn mentions_grammar_invocation(source: &str) -> bool {
    mentions_language_invocation(source) || mentions_macro_invocation(source, "language_fragment!")
}

fn mentions_macro_invocation(source: &str, spelling: &str) -> bool {
    let bytes = source.as_bytes();
    source.match_indices(spelling).any(|(at, needle)| {
        let mut index = at + needle.len();
        loop {
            match bytes.get(index) {
                Some(byte) if byte.is_ascii_whitespace() => index += 1,
                Some(b'/') if bytes.get(index + 1) == Some(&b'/') => {
                    index = source[index..]
                        .find('\n')
                        .map_or(bytes.len(), |end| index + end + 1);
                },
                Some(b'/') if bytes.get(index + 1) == Some(&b'*') => {
                    index = source[index + 2..]
                        .find("*/")
                        .map_or(bytes.len(), |end| index + 2 + end + 2);
                },
                Some(b'{' | b'(' | b'[') => return true,
                _ => return false,
            }
        }
    })
}

/// `path` written relative to `workspace_root`, with `/` separators.
///
/// Every audit that reports a finding reports it by repository-relative path, and every
/// audit had its own copy of this. It is also the STABLE half of the
/// `(path, language name)` key the bundled-language subject is keyed on: an absolute path
/// embeds the checkout location, so a table keyed on one could not be written down.
pub fn repo_relative(workspace_root: &Path, path: &Path) -> String {
    match path.strip_prefix(workspace_root) {
        Ok(relative) => relative
            .components()
            .map(|component| component.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/"),
        // A path OUTSIDE the root is returned whole. Re-joining its components would
        // double the leading separator (`RootDir` renders as `/`), and a silently
        // malformed path in a finding is worse than an absolute one.
        Err(_) => path.display().to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_bare_mention_is_not_an_invocation() {
        assert!(!mentions_language_invocation("the `language!` macro"));
        assert!(!mentions_language_invocation("language! is a macro"));
        assert!(!mentions_language_invocation("no macro here at all"));
    }

    #[test]
    fn an_invocation_is_recognised_through_whitespace_and_comments() {
        assert!(mentions_language_invocation("language! {"));
        assert!(mentions_language_invocation("language!(name: X)"));
        assert!(mentions_language_invocation("language![]"));
        assert!(mentions_language_invocation("language!\n    {"));
        assert!(mentions_language_invocation("language! // why\n{"));
        assert!(mentions_language_invocation("language! /* why */ {"));
    }

    #[test]
    fn the_grammar_gate_adds_fragments_without_widening_the_language_gate() {
        let source = "language_fragment! { name: Reusable }";
        assert!(mentions_grammar_invocation(source));
        assert!(!mentions_language_invocation(source));
    }

    /// The gate over-approximates ON PURPOSE: a doc comment that SHOWS an invocation
    /// passes, and the caller's structural decision then rejects it. Under-approximating
    /// would hide a declaration, which is the failure this whole module exists to prevent.
    #[test]
    fn the_gate_over_approximates_rather_than_hiding_a_declaration() {
        assert!(mentions_language_invocation("//! Write `language! { name: X }`."));
    }

    #[test]
    fn the_repository_sweep_declines_tooling_and_scratch_directories() {
        assert!(is_swept_over(".git"));
        assert!(is_swept_over(".formal-tmp"));
        assert!(is_swept_over("target"));
        assert!(is_swept_over("scratchpad"));
        assert!(!is_swept_over("languages"));
        assert!(!is_swept_over("bin"));
    }

    /// `bin` is walked. A `language!` in `languages/src/bin/` used to leave every audit
    /// silently, and the skip that caused it is the reason this list is written down once.
    #[test]
    fn only_build_and_macro_output_are_skipped_under_a_language_root() {
        assert_eq!(NON_SOURCE_DIRECTORIES, &["target", "generated"]);
    }

    #[test]
    fn repo_relative_uses_forward_slashes_and_drops_the_root() {
        let root = Path::new("/w/mettail-rust");
        assert_eq!(
            repo_relative(root, Path::new("/w/mettail-rust/languages/src/ambient.rs")),
            "languages/src/ambient.rs"
        );
        // A path outside the root is returned whole rather than silently truncated.
        assert_eq!(repo_relative(root, Path::new("/elsewhere/x.rs")), "/elsewhere/x.rs");
    }
}
