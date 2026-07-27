//! The workspace manifest keys that say WHERE specification-related files live.
//!
//! # Why these paths are declared, not hardcoded
//!
//! Two independent audits scan the repository for `language!` declarations
//! (`ast/tests/dovetail_language_inventory.rs` and `dovetail/tests/language_inventory.rs`),
//! and the `language!` macro itself must resolve one path outside `target/` — the
//! proptest counterexample corpus, which is an INPUT rather than a generated source.
//! Each of those three sites used to carry its own literal. Three literals that must
//! agree, edited by different people for different reasons, is a drift waiting to
//! happen: the day they disagree, a specification becomes invisible to one audit and
//! nothing says so.
//!
//! They are now declared ONCE, in the workspace manifest:
//!
//! ```toml
//! [package.metadata.mettail]
//! language_roots = ["languages"]
//! proptest_corpus_dir = "languages/tests"
//! ```
//!
//! `[package.metadata]` is the Cargo-sanctioned place for tool-specific configuration:
//! Cargo itself ignores the table, and every consumer reads the same bytes.
//!
//! # This module is the ONLY reader
//!
//! `ast` and (through it) `macros` use it as an ordinary module. `dovetail` does not
//! depend on `ast` — it deliberately has exactly one workspace dependency — so its audit
//! pulls this same file in with `#[path]`. That is why nothing here may reference
//! anything outside `std`: the file has to compile standing on its own.
//!
//! # Failure is loud, never silent
//!
//! Every accessor returns `Result` and every caller is expected to fail on `Err`. The
//! failure mode being designed against is a reader that returns an EMPTY root list when
//! the key is missing or reshaped, because an empty root list makes an audit pass by
//! scanning nothing — the exact shape of a check that cannot fail. A missing table, a
//! missing key, a value of the wrong TOML type, and an array this reader cannot parse
//! are therefore all hard errors that name what was expected and where.
//!
//! # The parsed subset, and why it is a subset
//!
//! This reader accepts precisely the shape the manifest declares: a `[package.metadata.mettail]`
//! table header, followed by `key = "string"` or `key = ["string", …]` on a single line.
//! It is not a TOML implementation and does not pretend to be one — it REJECTS anything it
//! does not fully understand rather than guessing, so the cost of the subset is a loud
//! error at build time, not a wrong answer. A general TOML parser was not worth a new
//! dependency in `ast` (which `macros` and therefore every language compilation link) for
//! two keys, and `dovetail`'s audit could not have used one without breaking that crate's
//! single-dependency rule.

use std::path::{Path, PathBuf};

/// The manifest table these keys live in.
const TABLE: &str = "[package.metadata.mettail]";

/// The key naming the directories that hold `language!` declarations.
const LANGUAGE_ROOTS_KEY: &str = "language_roots";

/// The key naming the directory that holds committed proptest counterexample corpora.
const PROPTEST_CORPUS_DIR_KEY: &str = "proptest_corpus_dir";

/// The body of the `[package.metadata.mettail]` table in `manifest_text`.
///
/// Returns the lines between the table header and the next table header, so a key from a
/// DIFFERENT table can never be mistaken for one of ours — the reason this is a real scan
/// and not a `lines().find(…)` over the whole file.
fn mettail_table_body(manifest_text: &str) -> Result<Vec<&str>, String> {
    let mut lines = manifest_text
        .lines()
        .skip_while(|line| line.trim() != TABLE);
    if lines.next().is_none() {
        return Err(format!(
            "the workspace manifest has no `{TABLE}` table. It is the single declaration \
             site for `{LANGUAGE_ROOTS_KEY}` and `{PROPTEST_CORPUS_DIR_KEY}`; without it \
             the specification audits would have nothing to scan and would pass vacuously."
        ));
    }
    Ok(lines
        .take_while(|line| !line.trim_start().starts_with('['))
        .collect())
}

/// The raw right-hand side of `key` inside the `[package.metadata.mettail]` table.
fn raw_value<'a>(manifest_text: &'a str, key: &str) -> Result<&'a str, String> {
    mettail_table_body(manifest_text)?
        .into_iter()
        .filter_map(|line| {
            let (name, value) = line.split_once('=')?;
            (name.trim() == key).then(|| value.trim())
        })
        .next()
        .ok_or_else(|| format!("`{TABLE}` does not declare `{key}`"))
}

/// The contents of a single-line TOML basic string, or an error naming what was found.
///
/// Escapes are rejected rather than interpreted: no path in this manifest needs one, and
/// silently mis-decoding `\t` into a tab would produce a directory that does not exist and
/// an audit that scans nothing.
fn parse_string(raw: &str, key: &str) -> Result<String, String> {
    let inner = raw
        .strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
        .ok_or_else(|| {
            format!("`{TABLE}` key `{key}` must be a double-quoted string; found `{raw}`")
        })?;
    if inner.contains('\\') {
        return Err(format!(
            "`{TABLE}` key `{key}` contains a backslash escape (`{inner}`), which this \
             reader deliberately does not interpret. Paths in this manifest are plain \
             relative paths; write one."
        ));
    }
    Ok(inner.to_owned())
}

/// The elements of a single-line TOML array of basic strings.
fn parse_string_array(raw: &str, key: &str) -> Result<Vec<String>, String> {
    let inner = raw
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
        .ok_or_else(|| {
            format!(
                "`{TABLE}` key `{key}` must be a single-line array of strings, e.g. \
                 `{key} = [\"languages\"]`; found `{raw}`. A multi-line array is not \
                 accepted — this reader rejects what it cannot fully parse rather than \
                 returning a short list that would silently narrow the audits."
            )
        })?;
    let trimmed = inner.trim();
    if trimmed.is_empty() {
        return Err(format!(
            "`{TABLE}` key `{key}` is an EMPTY array. An empty root list makes every \
             specification audit pass by scanning nothing; declare at least one path."
        ));
    }
    trimmed
        .split(',')
        .map(str::trim)
        .filter(|element| !element.is_empty()) // tolerate a trailing comma, nothing more
        .map(|element| parse_string(element, key))
        .collect()
}

/// The directories, relative to `workspace_root`, that hold `language!` declarations.
///
/// The returned paths are absolute. They are NOT required to exist: a root that has been
/// renamed should surface as an audit finding, not as a silently-skipped directory, and
/// the audits' own totality invariants
/// (`language_declarations_cannot_hide_outside_the_scanned_roots`) are what turn a stale
/// root into a failure that names the escaped declarations.
pub fn language_roots(workspace_root: &Path) -> Result<Vec<PathBuf>, String> {
    let manifest_text = read_workspace_manifest(workspace_root)?;
    let raw = raw_value(&manifest_text, LANGUAGE_ROOTS_KEY)?;
    Ok(parse_string_array(raw, LANGUAGE_ROOTS_KEY)?
        .into_iter()
        .map(|relative| workspace_root.join(relative))
        .collect())
}

/// The directory, relative to `workspace_root`, that holds proptest counterexample corpora.
///
/// This is the one path the `language!` macro resolves OUTSIDE `target/`, and deliberately
/// so: a corpus of previously-failing seeds is an INPUT to the generated property tests,
/// not a generated source. Under `target/` it would be erased by `cargo clean` and the
/// seeds would quietly stop being replayed — nothing would fail, coverage would just
/// evaporate. See `macros/src/gen/test_gen/mod.rs::proptest_config_expr`.
pub fn proptest_corpus_dir(workspace_root: &Path) -> Result<PathBuf, String> {
    let manifest_text = read_workspace_manifest(workspace_root)?;
    let raw = raw_value(&manifest_text, PROPTEST_CORPUS_DIR_KEY)?;
    Ok(workspace_root.join(parse_string(raw, PROPTEST_CORPUS_DIR_KEY)?))
}

fn read_workspace_manifest(workspace_root: &Path) -> Result<String, String> {
    let path = workspace_root.join("Cargo.toml");
    std::fs::read_to_string(&path)
        .map_err(|err| format!("failed to read the workspace manifest {}: {err}", path.display()))
}

/// Walk up from `start` to the directory whose `Cargo.toml` declares `[workspace]`.
///
/// Both the audits and the macro need the workspace root before they can read the
/// manifest, and both would otherwise reach it by counting `..` segments from their own
/// `CARGO_MANIFEST_DIR` — a hardcoded depth that breaks the moment a crate moves.
pub fn find_workspace_root(start: &Path) -> Option<PathBuf> {
    let mut current = Some(start);
    while let Some(directory) = current {
        if let Ok(contents) = std::fs::read_to_string(directory.join("Cargo.toml")) {
            if contents
                .lines()
                .any(|line| line.trim_start().starts_with("[workspace]"))
            {
                return Some(directory.to_path_buf());
            }
        }
        current = directory.parent();
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = "\
[workspace]
members = [\"ast\"]

[package.metadata.mettail]
language_roots = [\"languages\", \"extra/specs\"]
proptest_corpus_dir = \"languages/tests\"

[workspace.package]
language_roots = [\"decoy\"]
";

    #[test]
    fn reads_the_declared_roots_in_order() {
        let raw = raw_value(SAMPLE, LANGUAGE_ROOTS_KEY).expect("the key is declared");
        assert_eq!(
            parse_string_array(raw, LANGUAGE_ROOTS_KEY).expect("a single-line string array"),
            vec!["languages".to_owned(), "extra/specs".to_owned()]
        );
    }

    #[test]
    fn reads_the_declared_corpus_directory() {
        let raw = raw_value(SAMPLE, PROPTEST_CORPUS_DIR_KEY).expect("the key is declared");
        assert_eq!(
            parse_string(raw, PROPTEST_CORPUS_DIR_KEY).expect("a quoted string"),
            "languages/tests"
        );
    }

    /// The scan stops at the next table header, so an identically-named key in a
    /// different table cannot be picked up. `SAMPLE` plants exactly that decoy.
    #[test]
    fn a_key_in_another_table_is_not_read() {
        let body = mettail_table_body(SAMPLE).expect("the table exists");
        assert!(
            !body.iter().any(|line| line.contains("decoy")),
            "the table body must end at the next header; got {body:?}"
        );
    }

    #[test]
    fn a_missing_table_is_an_error_not_an_empty_list() {
        let error = mettail_table_body("[workspace]\nmembers = []\n")
            .expect_err("a manifest without the table must fail loudly");
        assert!(error.contains(TABLE), "the error must name the table: {error}");
    }

    #[test]
    fn a_missing_key_is_an_error() {
        let error = raw_value("[package.metadata.mettail]\nother = 1\n", LANGUAGE_ROOTS_KEY)
            .expect_err("a missing key must fail loudly");
        assert!(error.contains(LANGUAGE_ROOTS_KEY), "the error must name the key: {error}");
    }

    #[test]
    fn an_empty_root_array_is_rejected() {
        let error = parse_string_array("[]", LANGUAGE_ROOTS_KEY)
            .expect_err("an empty root list would make the audits vacuous");
        assert!(
            error.contains("EMPTY"),
            "the error must say why an empty list is refused: {error}"
        );
    }

    #[test]
    fn a_multi_line_array_is_rejected_rather_than_truncated() {
        let error = parse_string_array("[", LANGUAGE_ROOTS_KEY)
            .expect_err("an array this reader cannot parse must fail, not truncate");
        assert!(
            error.contains("single-line"),
            "the error must say what shape is accepted: {error}"
        );
    }

    #[test]
    fn a_non_string_value_is_rejected() {
        let error = parse_string("languages", PROPTEST_CORPUS_DIR_KEY)
            .expect_err("bare words are not TOML strings");
        assert!(
            error.contains("double-quoted"),
            "the error must say what shape is accepted: {error}"
        );
    }
}
