//! Doc-comment hazards that `cargo nextest` cannot see.
//!
//! Two of them, and they are SIBLINGS: both are ways for a doc comment to make an
//! assertion about Rust that nothing checks. `cargo nextest` does not run doctests, so
//! neither shows up in the suite everyone watches — the first surfaces as a silent
//! `0 passed`, the second as a red `cargo test --doc` in CI hours later.
//!
//! 1. [`every_ignore_fence_carries_a_justification`] — a fence that opts OUT of
//!    compilation without saying why.
//! 2. [`no_doc_comment_hides_an_indented_code_block`] — prose that opts IN by accident,
//!    because a blank line followed by a ≥4-space indent is an INDENTED CODE BLOCK in
//!    markdown, and rustdoc compiles an unannotated code block as Rust.
//!
//! They are kept in one file on purpose. Covering one spelling of a hazard while its
//! sibling recurs is a failure mode this codebase has now hit repeatedly: hazard 2 was
//! first fixed by hand in `macros/src/gen/runtime/wpda_codegen/prefix.rs`, whose comment
//! states the rule — *keep prose at the left margin, and use a real markdown list for
//! enumerations rather than hanging indentation* — and then recurred four commits later
//! in a `#[doc = …]` attribute a proc macro emits, where no `///` was there to remind
//! anyone. Whoever reads this file for one hazard now meets the other.
//!
//! ══════════════════════════════════════════════════════════════════════════════════
//! # Hazard 1 — unjustified `ignore` fences
//! ══════════════════════════════════════════════════════════════════════════════════
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
//!
//! ══════════════════════════════════════════════════════════════════════════════════
//! # Hazard 2 — prose rustdoc mistakes for Rust
//! ══════════════════════════════════════════════════════════════════════════════════
//!
//! ## The measurement
//!
//! One `format!` in `macros/src/gen/test_gen/simulation_binary.rs` built a `#[doc = …]`
//! whose continuation lines sat nine spaces in after a blank line. That is two indented
//! code blocks per expansion; the macro expands once per language, so eight languages
//! produced **sixteen** failing doctests, every one of them rustc trying to parse
//! English:
//!
//! ```text
//! error: unknown start of token: `
//! error: expected one of `!` or `::`, found `ONCE`
//! ```
//!
//! ## The rule, and why the blank line is part of it
//!
//! CommonMark ([§4.4 Indented code blocks](https://spec.commonmark.org/0.31.2/#indented-code-blocks))
//! defines an indented chunk as consecutive non-blank lines indented four or more
//! columns, and states that an indented code block **cannot interrupt a paragraph**.
//! Indentation directly under a line of prose is therefore harmless — a lazy
//! continuation of the same paragraph — and only indentation that *follows a blank
//! line* opens a code block. rustdoc then treats a code block with no info string as
//! Rust and compiles it. Hence the exact predicate this file checks:
//!
//! > a non-blank line, outside any fence, preceded by a blank line, indented four or
//! > more columns beyond its enclosing container.
//!
//! The container term is what keeps the check honest about markdown lists. Inside a
//! list item, four columns past the marker is the item's own content, not a code block
//! ([§5.2 List items](https://spec.commonmark.org/0.31.2/#list-items)), so the scanner
//! tracks open list markers and measures indentation relative to the innermost one. The
//! recommended repair for a flagged line is the one the `prefix.rs` comment gives:
//! unindent the prose, and if it was an enumeration, make it a real markdown list.
//!
//! ## Both spellings, or it is not a guard
//!
//! Doc text reaches rustdoc two ways, and the defect above used the one no `///`-only
//! scan can see:
//!
//! - `///` and `//!` line comments — read directly, with rustdoc's unindentation
//!   applied (the minimum indentation over the block's non-blank lines is stripped, so
//!   `/// text` renders at column 0 and `///     text` at column 4).
//! - `#[doc = <expr>]` attributes, including the `#[doc = #ident]` form a `quote!` emits
//!   — resolved back to the `let ident = format!("…")` that built the text, with `{…}`
//!   placeholders standing in as a single token. Substituting the placeholder is sound
//!   here because indentation is the only property read, and a placeholder never
//!   carries any.
//!
//! One item may use BOTH — `lit_boundary.rs` opens `__inert_skip`'s documentation with
//! `#[doc = #pattern_doc]` and continues in `///` — and rustdoc unindents such a block
//! with a one-column correction, crediting each raw fragment the cosmetic space that
//! `/// text` puts in front of every sugared line. [`unindent`] is a faithful port of
//! that rule rather than an approximation of it, and
//! [`the_mixed_spelling_block_is_rendered_as_rustdoc_renders_it`] pins the one real
//! block that exercises the correction.
//!
//! [`every_doc_attribute_resolves_to_its_text`] closes the obvious hole: a `#[doc]`
//! value the resolver cannot read would be skipped SILENTLY, so an unresolvable one is
//! a hard failure that names the site rather than a quiet gap in coverage.

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
    "rholang-runtime/src/rholang_ast.rs",
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

    let total_files: usize = roots
        .iter()
        .map(|root| discover_rust_files(root).len())
        .sum();
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
            assert!(is_justified(&lines, fence), "{relative}:{} lost its justification", fence + 1,);
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════
// Hazard 2 — a blank line plus a ≥4-space indent is a Rust code block
// ══════════════════════════════════════════════════════════════════════════════════════

/// Columns a hard tab advances to, for indentation purposes.
///
/// CommonMark expands tabs to the next multiple of four when measuring block structure.
/// Doc comments here are space-indented, so this only ever matters as a guarantee that a
/// tab cannot smuggle four columns past the check.
const TAB_WIDTH: usize = 4;

/// The indentation, in columns, that opens a code block.
const CODE_BLOCK_INDENT: usize = 4;

/// The body of one line doc comment, INDENTATION PRESERVED.
///
/// [`doc_comment_body`] trims the body, which is right for finding a fence opener and
/// fatal here — the whole hazard is the leading whitespace it discards. `////` is a
/// plain comment, not a doc comment, so four-or-more slashes are rejected.
fn doc_line_body_verbatim(line: &str) -> Option<&str> {
    let trimmed = line.trim_start();
    match trimmed.strip_prefix("////") {
        Some(_) => None,
        None => trimmed
            .strip_prefix("///")
            .or_else(|| trimmed.strip_prefix("//!")),
    }
}

/// The value expression of a `#[doc = <expr>]` attribute line, or `None`.
///
/// The `#[doc(hidden)]` form carries no text and is not a match.
fn doc_attr_value(line: &str) -> Option<&str> {
    let trimmed = line.trim();
    let inner = trimmed.strip_prefix("#[doc")?.strip_suffix(']')?;
    Some(inner.trim_start().strip_prefix('=')?.trim())
}

/// Decode the CONTENTS of a Rust string literal — the text between the quotes.
///
/// Only the escapes that alter line structure need to be exact: `\n`, and the
/// `\`-before-newline continuation, which swallows the newline AND the indentation that
/// follows it. That continuation is precisely what the defective `format!` omitted after
/// its `\n\n`, leaving nine source-indentation spaces inside the rendered text.
/// Everything else may decode to a placeholder character, because no other escape can
/// change whether a line is blank or how far it is indented.
fn unescape_string_literal(body: &str) -> String {
    let mut out = String::with_capacity(body.len());
    let mut chars = body.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            Some('0') => out.push('\0'),
            Some(escaped @ ('\\' | '"' | '\'')) => out.push(escaped),
            // Line continuation: the newline and the following indentation vanish.
            Some('\n') => {
                while chars.peek().is_some_and(|c| *c == ' ' || *c == '\t') {
                    chars.next();
                }
            },
            Some('u') => {
                for skipped in chars.by_ref() {
                    if skipped == '}' {
                        break;
                    }
                }
                out.push('\u{fffd}');
            },
            Some('x') => {
                chars.next();
                chars.next();
                out.push('\u{fffd}');
            },
            Some(other) => out.push(other),
            None => break,
        }
    }
    out
}

/// Replace every `format!` placeholder with a single token.
///
/// `{}`, `{0}` and `{name}` all become `X`; `{{` and `}}` become the literal braces they
/// escape. The substituted value cannot change the property under test — indentation —
/// because a placeholder sits inside a line, never at its start followed by spaces.
fn substitute_placeholders(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '{' if chars.peek() == Some(&'{') => {
                chars.next();
                out.push('{');
            },
            '}' if chars.peek() == Some(&'}') => {
                chars.next();
                out.push('}');
            },
            '{' => {
                for inner in chars.by_ref() {
                    if inner == '}' {
                        break;
                    }
                }
                out.push('X');
            },
            other => out.push(other),
        }
    }
    out
}

/// The first string literal at or after `from`, decoded, or `None` if there is none.
fn first_string_literal(source: &str, from: usize) -> Option<String> {
    let bytes = source.as_bytes();
    let open = (from..bytes.len()).find(|at| bytes[*at] == b'"')?;
    let mut at = open + 1;
    while at < bytes.len() {
        match bytes[at] {
            b'\\' => at += 2,
            b'"' => return Some(unescape_string_literal(&source[open + 1..at])),
            _ => at += 1,
        }
    }
    None
}

/// The text a `#[doc = #ident]` interpolation carries, recovered from its `let`.
///
/// Finds the NEAREST PRECEDING `let <ident> =` — the binding actually in scope at the
/// attribute — and reads the string literal that follows, skipping a `format!(` if one
/// is present. `before` is the byte offset of the attribute line.
fn resolve_bound_doc_text(source: &str, before: usize, ident: &str) -> Option<String> {
    let needle = format!("let {ident} =");
    let at = source[..before].rfind(&needle)?;
    let tail = source[at + needle.len()..].trim_start();
    // Only the two spellings the failure message names are accepted. A doc text built any
    // other way is reported UNRESOLVED rather than guessed at, so the guard never scans
    // some unrelated literal and calls the site covered.
    let body = match tail.strip_prefix("format!") {
        Some(rest) => rest.trim_start().strip_prefix(['(', '[', '{'])?,
        None if tail.starts_with('"') => tail,
        None => return None,
    };
    let literal_from = source.len() - body.len();
    first_string_literal(source, literal_from).map(|text| substitute_placeholders(&text))
}

/// Render a `format!` literal body exactly as [`doc_blocks`] renders a `#[doc]` fragment.
///
/// Unescape, substitute placeholders, split on newlines, unindent — the whole pipeline in
/// one call, so [`indented_block_scanner_recognises_the_hazard_and_only_the_hazard`] can
/// exercise it end to end on a literal written verbatim in the test.
fn render_doc_literal(literal_body: &str) -> Vec<String> {
    unindent(&[DocFragment {
        spelling: DocSpelling::Raw,
        lines: substitute_placeholders(&unescape_string_literal(literal_body))
            .split('\n')
            .map(str::to_string)
            .collect(),
    }])
}

/// Strip rustdoc's uniform leading indentation from a doc block.
///
/// rustdoc computes the minimum indentation over the block's non-blank lines and removes
/// it from every line, which is what turns `/// text` into `text` at column 0. A block
/// whose FIRST line starts at column 0 therefore has nothing stripped, and any deeper
/// line keeps its full indentation — the situation the defective `format!` was in.
fn unindent(fragments: &[DocFragment]) -> Vec<String> {
    // rustdoc's `add`: when a block MIXES the two spellings, the sugared fragments decide
    // the common indent, and the raw ones are credited one column for the cosmetic space
    // `/// text` puts in front of every sugared line and `#[doc = "text"]` does not.
    let mixed = fragments
        .windows(2)
        .any(|pair| pair[0].spelling != pair[1].spelling)
        && fragments
            .iter()
            .any(|fragment| fragment.spelling == DocSpelling::Sugared);
    let add = usize::from(mixed);

    let common = fragments
        .iter()
        .map(|fragment| {
            let credit = match fragment.spelling {
                DocSpelling::Sugared => 0,
                DocSpelling::Raw => add,
            };
            fragment
                .lines
                .iter()
                .filter(|line| !line.trim().is_empty())
                .map(|line| leading_whitespace(line) + credit)
                .min()
                .unwrap_or(usize::MAX)
        })
        .min()
        .unwrap_or(usize::MAX);

    let mut rendered = Vec::new();
    for fragment in fragments {
        let strip = match (common, fragment.spelling) {
            (usize::MAX, _) => 0,
            (_, DocSpelling::Raw) if common > 0 => common - add,
            _ => common,
        };
        for line in &fragment.lines {
            match line.trim().is_empty() {
                true => rendered.push(String::new()),
                false => rendered.push(line[strip.min(leading_whitespace(line))..].to_string()),
            }
        }
    }
    rendered
}

/// The leading whitespace of a line, in BYTES (spaces and tabs are one byte each).
fn leading_whitespace(line: &str) -> usize {
    line.len() - line.trim_start_matches([' ', '\t']).len()
}

/// How one doc FRAGMENT was spelled in the source.
///
/// The distinction is rustdoc's, not this file's: `unindent_doc_fragments` credits a raw
/// fragment one column in a mixed block, so a scanner that erased the spelling would
/// measure the wrong indentation for exactly the blocks that mix them. One such block
/// exists — `macros/src/gen/runtime/wpda_codegen/lit_boundary.rs` opens an item's docs
/// with `#[doc = #pattern_doc]` and continues in `///`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DocSpelling {
    /// A `///` or `//!` line.
    Sugared,
    /// A `#[doc = …]` attribute.
    Raw,
}

/// One doc fragment: the body of a single `///` line, or of one `#[doc = …]` attribute.
#[derive(Debug)]
struct DocFragment {
    spelling: DocSpelling,
    /// The fragment's own lines, VERBATIM — indentation is the property under test.
    lines: Vec<String>,
}

/// One contiguous doc block, rendered as rustdoc would see it.
#[derive(Debug)]
struct DocBlock {
    /// 1-based line of the block's first line in the source.
    line: usize,
    /// The spellings the block's fragments used, in order of first appearance.
    spellings: Vec<DocSpelling>,
    /// The block's markdown, unindented, one entry per rendered line.
    text: Vec<String>,
    /// `#[doc = …]` values the resolver could not read, as `(1-based line, value)`.
    unresolved: Vec<(usize, String)>,
}

impl DocBlock {
    /// How the block is named in a failure message.
    fn spelling_label(&self) -> &'static str {
        match (
            self.spellings.contains(&DocSpelling::Sugared),
            self.spellings.contains(&DocSpelling::Raw),
        ) {
            (true, true) => "/// + #[doc = …]",
            (_, true) => "#[doc = …]",
            _ => "/// or //!",
        }
    }
}

/// Every doc block in one file, in source order.
///
/// A block is a maximal run of doc lines and `#[doc]` attributes, and the run STEPS OVER
/// an intervening ordinary attribute — `/// a` `#[allow(…)]` `/// b` is one doc comment
/// to rustc, which collects an item's `#[doc]` attributes in order and ignores what sits
/// between them. The step-over is only taken when a doc line really does follow, so a
/// trailing `#[allow(…)]` before the item still ends the block.
fn doc_blocks(source: &str) -> Vec<DocBlock> {
    let lines: Vec<&str> = source.lines().collect();
    let mut line_offsets = Vec::with_capacity(lines.len());
    let mut offset = 0usize;
    for line in &lines {
        line_offsets.push(offset);
        offset += line.len() + 1;
    }

    /// The next index at which the run continues, stepping over ordinary attributes.
    fn resume_at(lines: &[&str], from: usize) -> Option<usize> {
        let mut at = from;
        while at < lines.len() {
            if doc_line_body_verbatim(lines[at]).is_some() || doc_attr_value(lines[at]).is_some() {
                return Some(at);
            }
            match lines[at].trim().starts_with("#[") {
                true => at += 1,
                false => return None,
            }
        }
        None
    }

    let mut blocks = Vec::new();
    let mut index = 0usize;
    while index < lines.len() {
        let starts_block = doc_line_body_verbatim(lines[index]).is_some()
            || doc_attr_value(lines[index]).is_some();
        if !starts_block {
            index += 1;
            continue;
        }

        let start = index;
        let mut fragments: Vec<DocFragment> = Vec::new();
        let mut spellings: Vec<DocSpelling> = Vec::new();
        let mut unresolved = Vec::new();
        while let Some(at) = resume_at(&lines, index) {
            index = at;
            if let Some(body) = doc_line_body_verbatim(lines[index]) {
                fragments.push(DocFragment {
                    spelling: DocSpelling::Sugared,
                    lines: vec![body.to_string()],
                });
            } else {
                let value = doc_attr_value(lines[index]).expect("resume_at found one of the two");
                let recovered = match value.strip_prefix('"').and_then(|v| v.strip_suffix('"')) {
                    Some(literal) => Some(unescape_string_literal(literal)),
                    None => match value.strip_prefix('#') {
                        Some(ident) => {
                            resolve_bound_doc_text(source, line_offsets[index], ident.trim())
                        },
                        None => None,
                    },
                };
                match recovered {
                    Some(text) => fragments.push(DocFragment {
                        spelling: DocSpelling::Raw,
                        lines: text.split('\n').map(str::to_string).collect(),
                    }),
                    None => unresolved.push((index + 1, value.to_string())),
                }
            }
            if let Some(&DocFragment { spelling, .. }) = fragments.last() {
                if !spellings.contains(&spelling) {
                    spellings.push(spelling);
                }
            }
            index += 1;
        }

        blocks.push(DocBlock {
            line: start + 1,
            spellings,
            text: unindent(&fragments),
            unresolved,
        });
    }
    blocks
}

/// The indentation of a line, in columns, with tabs expanded.
fn indent_columns(line: &str) -> usize {
    line.chars()
        .take_while(|c| *c == ' ' || *c == '\t')
        .map(|c| match c {
            '\t' => TAB_WIDTH,
            _ => 1,
        })
        .sum()
}

/// The content column a list item opens, if this line opens one.
///
/// `- `, `* `, `+ `, `1. ` and `1) ` are the markers CommonMark recognises; the content
/// column is where the text after the marker begins, and it is the baseline every
/// following line of that item is measured against.
fn list_item_content_column(line: &str) -> Option<usize> {
    let indent = indent_columns(line);
    let rest = line.trim_start_matches([' ', '\t']);
    let marker_len = match rest.chars().next()? {
        '-' | '*' | '+' => 1,
        '0'..='9' => {
            let digits = rest.chars().take_while(char::is_ascii_digit).count();
            match rest[digits..].chars().next() {
                Some('.' | ')') => digits + 1,
                _ => return None,
            }
        },
        _ => return None,
    };
    let spaces = rest[marker_len..]
        .chars()
        .take_while(|c| *c == ' ' || *c == '\t')
        .count();
    match spaces {
        0 => None,
        _ => Some(indent + marker_len + spaces),
    }
}

/// The fence indentation, if this line opens or closes a fenced code block.
fn fence_indent(line: &str) -> Option<usize> {
    let rest = line.trim_start_matches([' ', '\t']);
    match rest.starts_with("```") || rest.starts_with("~~~") {
        true => Some(indent_columns(line)),
        false => None,
    }
}

/// The 0-based indices of lines that open an INDENTED CODE BLOCK in this doc text.
///
/// The predicate is the one argued in the module header: a non-blank line, outside any
/// fence, preceded by a blank line, indented [`CODE_BLOCK_INDENT`] columns or more past
/// its enclosing list container.
fn indented_code_block_lines(text: &[String]) -> Vec<usize> {
    let mut offenders = Vec::new();
    let mut open_fence: Option<usize> = None;
    let mut list_columns: Vec<usize> = Vec::new();
    let mut previous_blank = false;

    for (index, line) in text.iter().enumerate() {
        if line.trim().is_empty() {
            previous_blank = true;
            continue;
        }
        let indent = indent_columns(line);
        let fence = fence_indent(line);
        if let Some(opened_at) = open_fence {
            // A closing fence may be indented up to three columns past the opener.
            if fence.is_some_and(|at| at <= opened_at + 3) {
                open_fence = None;
            }
            previous_blank = false;
            continue;
        }
        while list_columns.last().is_some_and(|column| indent < *column) {
            list_columns.pop();
        }
        let container = list_columns.last().copied().unwrap_or(0);
        if previous_blank && indent >= container + CODE_BLOCK_INDENT {
            offenders.push(index);
        }
        match list_item_content_column(line) {
            Some(column) if indent <= container + 3 => list_columns.push(column),
            _ => {
                if let Some(at) = fence {
                    open_fence = Some(at);
                }
            },
        }
        previous_blank = false;
    }
    offenders
}

/// One doc block that hides prose inside an indented code block.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
struct IndentedBlock {
    path: String,
    line: usize,
    spelling: &'static str,
    excerpt: String,
}

/// A `#[doc = …]` value the resolver could not read.
#[derive(Debug)]
struct UnreadDocAttribute {
    path: String,
    line: usize,
    value: String,
}

/// What one walk of the workspace found.
#[derive(Debug)]
struct IndentedBlockScan {
    offenders: Vec<IndentedBlock>,
    unread: Vec<UnreadDocAttribute>,
    /// Files walked and doc blocks read — the anti-vacuity counts.
    files_walked: usize,
    blocks_read: usize,
}

/// Walk every workspace `src/` tree, returning the offenders and the coverage counts.
///
/// Only `src/` is walked, and deliberately: cargo compiles doctests for LIBRARY targets,
/// so a doc comment under `tests/` or `benches/` never reaches rustdoc and cannot carry
/// this hazard. The returned counts exist so the guard can prove it walked something.
fn collect_indented_blocks() -> IndentedBlockScan {
    let mut scan = IndentedBlockScan {
        offenders: Vec::new(),
        unread: Vec::new(),
        files_walked: 0,
        blocks_read: 0,
    };

    for root in workspace_member_src_roots() {
        for file in discover_rust_files(&root) {
            scan.files_walked += 1;
            let relative = repo_relative(&file);
            let source = fs::read_to_string(&file)
                .unwrap_or_else(|err| panic!("failed to read {file:?}: {err}"));
            for block in doc_blocks(&source) {
                scan.blocks_read += 1;
                for (line, value) in &block.unresolved {
                    scan.unread.push(UnreadDocAttribute {
                        path: relative.clone(),
                        line: *line,
                        value: value.clone(),
                    });
                }
                for index in indented_code_block_lines(&block.text) {
                    scan.offenders.push(IndentedBlock {
                        path: relative.clone(),
                        line: block.line,
                        spelling: block.spelling_label(),
                        excerpt: block.text[index].chars().take(88).collect(),
                    });
                }
            }
        }
    }
    scan.offenders.sort();
    scan
}

/// No doc comment, hand-written or macro-emitted, hides prose in an indented code block.
#[test]
fn no_doc_comment_hides_an_indented_code_block() {
    let offenders = collect_indented_blocks().offenders;
    assert!(
        offenders.is_empty(),
        "{} doc block(s) contain a blank line followed by a ≥{CODE_BLOCK_INDENT}-space \
         indent, which markdown reads as an INDENTED CODE BLOCK and rustdoc compiles as \
         Rust.\n\n\
         `cargo nextest` does not run doctests, so this stays green while \
         `cargo test --doc` fails on prose that rustc cannot parse.\n\n\
         Fix: keep prose at the left margin. If the indentation was marking an \
         enumeration, use a real markdown list (`- item`) — its continuation lines are \
         allowed to be indented. If the block really is code, put it in a fence with an \
         info string.\n\nOffenders (block start, then the offending line):\n{}",
        offenders.len(),
        offenders
            .iter()
            .map(|o| format!("  {}:{}  [{}]  {:?}", o.path, o.line, o.spelling, o.excerpt))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

/// Every `#[doc = …]` value is readable, so none is skipped in silence.
///
/// A value the resolver cannot decode would be scanned as empty text — coverage lost
/// with no signal, which is the same could-not-fail shape
/// [`scanner_recognises_ignore_spellings`] exists to prevent for hazard 1.
#[test]
fn every_doc_attribute_resolves_to_its_text() {
    let unread = collect_indented_blocks().unread;
    assert!(
        unread.is_empty(),
        "{} `#[doc = …]` value(s) could not be resolved to their text, so they were NOT \
         scanned for hazard 2.\n\n\
         The resolver reads a string literal, or `#ident` bound by the nearest preceding \
         `let ident = format!(\"…\")` / `let ident = \"…\"` in the same file. Bind the doc \
         text that way, or teach `resolve_bound_doc_text` the new spelling — do not leave \
         the site unread.\n\nUnresolved:\n{}",
        unread.len(),
        unread
            .iter()
            .map(|entry| format!("  {}:{}  {}", entry.path, entry.line, entry.value))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

/// The one block in the workspace that MIXES the two spellings renders at column 0.
///
/// `lit_boundary.rs` opens `__inert_skip`'s documentation with `#[doc = #pattern_doc]`
/// and continues in `///`. Its raw fragment carries one leading space and so do its
/// sugared ones, so rustdoc's `add` correction is exactly what decides whether the raw
/// line lands at column 0 or column 1 — and a scanner that ignored the correction and
/// stripped the sugared amount from the raw fragment would be reading a DIFFERENT
/// document than rustdoc does.
///
/// Pinning it here means the mixed path is exercised by a real fixture rather than by a
/// constructed one, and that a future edit which drops the mixing makes this test say so
/// instead of leaving the correction untested.
#[test]
fn the_mixed_spelling_block_is_rendered_as_rustdoc_renders_it() {
    let path = repo_root().join("macros/src/gen/runtime/wpda_codegen/lit_boundary.rs");
    let source = fs::read_to_string(&path).expect("the inert-boundary generator is readable");
    let blocks = doc_blocks(&source);
    let mixed: Vec<&DocBlock> = blocks
        .iter()
        .filter(|block| block.spellings.len() > 1)
        .collect();
    assert_eq!(
        mixed.len(),
        1,
        "expected exactly one mixed-spelling block in lit_boundary.rs, found {}",
        mixed.len(),
    );
    let block = mixed[0];
    assert!(block.unresolved.is_empty(), "the mixed block's `#[doc]` value went unread");
    // ONE leading space, not zero: the sugared fragments set the minimum at one column
    // and the raw fragment is credited it, so the raw fragment strips nothing. One column
    // is below markdown's three-column tolerance, so it renders as ordinary prose.
    assert_eq!(
        block.text.first().map(String::as_str),
        Some(" Derived from X inert token pattern(s): X"),
        "the raw fragment was not rendered as rustdoc renders it: {:#?}",
        block.text,
    );
    assert!(
        block
            .text
            .iter()
            .any(|line| line.starts_with("Return the index just past the inert span")),
        "the sugared fragments did not land at column 0: {:#?}",
        block.text,
    );
    assert!(indented_code_block_lines(&block.text).is_empty());
}

/// The scanner fires on the hazard, in both spellings, and on nothing legitimate.
///
/// Without this the guard above could pass by finding nothing — and the two shapes at the
/// bottom, a markdown list continuation and an indent that does not follow a blank line,
/// are exactly the legal markdown a cruder rule flags by mistake.
#[test]
fn indented_block_scanner_recognises_the_hazard_and_only_the_hazard() {
    let text = |lines: &[&str]| -> Vec<String> { lines.iter().map(|l| l.to_string()).collect() };

    // ── the hazard, hand-written ──────────────────────────────────────────────
    let hand_written = text(&["Header prose.", "", "    Indented continuation."]);
    assert_eq!(indented_code_block_lines(&hand_written), vec![2]);

    // ── the hazard, as the macro emitted it ───────────────────────────────────
    //
    // RAW strings below, so what appears here is byte-for-byte the literal BODY the
    // generator holds — `\n` is two characters, and a trailing backslash is the Rust
    // line continuation. The defect is the `\n\n` with NO continuation after it: the
    // nine columns of source indentation that follow survive into the rendered text,
    // twice, which is the two failing doctests per language.
    let defective = render_doc_literal(
        r"Simulation CLI entry point for `{}`.\n\n         Invoke ONCE, passing \
         the path:\n\
         `{}_simulation_main!(…);` for a library-hosted one.\n\n         Expands to `fn main`.",
    );
    assert_eq!(indented_code_block_lines(&defective).len(), 2, "rendered: {defective:#?}");

    // ── the same text written correctly: a continuation after every `\n` ──────
    let repaired = render_doc_literal(
        r"Simulation CLI entry point for `{}`.\n\n\
         Invoke ONCE, passing the path:\n\
         - library-hosted: `{}_simulation_main!(…);`\n\n\
         Expands to `fn main`.",
    );
    assert!(indented_code_block_lines(&repaired).is_empty(), "rendered: {repaired:#?}");

    // ── legitimate: a fenced block may be indented however it likes ───────────
    let fenced = text(&["Example:", "", "```rust", "    let deeply = indented;", "```"]);
    assert!(indented_code_block_lines(&fenced).is_empty());

    // ── legitimate: a list item's own continuation paragraph ──────────────────
    let list = text(&["Two of them:", "", "- first item", "", "  continued here", "", "- second"]);
    assert!(indented_code_block_lines(&list).is_empty());
    let nested = text(&["- outer", "  - inner", "", "    inner's continuation"]);
    assert!(indented_code_block_lines(&nested).is_empty());

    // ── legitimate: an indent cannot interrupt a paragraph (no blank line) ────
    let lazy = text(&["Prose that wraps", "    onto an indented line."]);
    assert!(indented_code_block_lines(&lazy).is_empty());

    // ── a code block right after a list ENDS is still a code block ────────────
    let after_list = text(&["- item", "", "        eight columns, two past the item"]);
    assert_eq!(indented_code_block_lines(&after_list), vec![2]);

    // ── the readers, on the spellings that actually occur ─────────────────────
    assert_eq!(doc_line_body_verbatim("    ///     text"), Some("     text"));
    assert_eq!(doc_line_body_verbatim("//!  text"), Some("  text"));
    assert_eq!(doc_line_body_verbatim("//// not a doc comment"), None);
    assert_eq!(doc_line_body_verbatim("let s = \"/// inside a literal\";"), None);
    assert_eq!(doc_attr_value("        #[doc = #doc]"), Some("#doc"));
    assert_eq!(doc_attr_value("#[doc = \"literal\"]"), Some("\"literal\""));
    assert_eq!(doc_attr_value("#[doc(hidden)]"), None);
    assert_eq!(substitute_placeholders("a {} b {name} c {{d}}"), "a X b X c {d}");

    // ── the unindent, on each of the three fragment shapes ────────────────────
    let sugared = |lines: &[&str]| DocFragment {
        spelling: DocSpelling::Sugared,
        lines: text(lines),
    };
    let raw = |lines: &[&str]| DocFragment {
        spelling: DocSpelling::Raw,
        lines: text(lines),
    };
    // The three expectations below were MEASURED, not assumed: a scratch crate carrying
    // each shape was documented with `RUSTDOCFLAGS="-Z unstable-options --output-format
    // json" cargo +nightly doc`, and its `docs` fields read back. Reproduce it whenever
    // this port is in doubt — the rule is subtle enough that reasoning about it is how
    // one ends up with a scanner reading a different document than rustdoc.
    //
    // All-sugared: the minimum, one column, is stripped everywhere.
    assert_eq!(unindent(&[sugared(&[" a", "", "     b"])]), text(&["a", "", "    b"]));
    // All-raw: no correction, so the minimum is again stripped as-is.
    //   #[doc = " only raw, one space"] #[doc = " second raw fragment"]
    //     ⟼ "only raw, one space\nsecond raw fragment"
    assert_eq!(unindent(&[raw(&["  a", "", "      b"])]), text(&["a", "", "    b"]));
    // Mixed, the `lit_boundary.rs` shape: the SUGARED fragment decides the minimum (one
    // column), the raw fragment is credited that column and therefore strips NOTHING, so
    // its single leading space survives into the rendered markdown.
    //   /// sugared line  #[doc = " raw line"]  /// another sugared
    //     ⟼ "sugared line\n raw line\nanother sugared"
    assert_eq!(
        unindent(&[raw(&[" from the attribute"]), sugared(&[" from the line"])]),
        text(&[" from the attribute", "from the line"])
    );
    // The consequence that matters here: in a MIXED block a raw fragment keeps every
    // column it was written with, so the hazard can hide in one. Four columns survive.
    //   #[doc = "    raw four spaces"]  /// sugared
    //     ⟼ "    raw four spaces\nsugared"
    assert_eq!(
        unindent(&[raw(&["    four columns"]), sugared(&[" one column"])]),
        text(&["    four columns", "one column"])
    );

    // ── the `let`-resolver, against the real emission shape ───────────────────
    let source =
        "fn f() {\n    let doc = format!(\n        \"first\\n\\n    second {}\",\n        \
                  name,\n    );\n    quote! { #[doc = #doc] }\n}\n";
    let resolved = resolve_bound_doc_text(source, source.len(), "doc")
        .expect("the `let doc = format!(…)` binding is readable");
    assert_eq!(resolved, "first\n\n    second X");
}

/// The hazard-2 walk reaches the workspace and reads a substantial body of documentation.
///
/// The counts are floors with wide margins, not fixtures: they fail a scan that walked an
/// empty tree or one that stopped reading doc comments, and survive ordinary editing.
#[test]
fn indented_block_scan_reaches_the_workspace() {
    let scan = collect_indented_blocks();
    let (files_walked, blocks_read) = (scan.files_walked, scan.blocks_read);
    assert!(files_walked > 300, "expected to walk >300 source files, walked {files_walked}");
    assert!(blocks_read > 5_000, "expected to read >5000 doc blocks, read {blocks_read}");

    // The macro-emitted spelling is REACHED — the one a `///`-only scan cannot see.
    let emitting = repo_root().join("macros/src/gen/test_gen/simulation_binary.rs");
    let source =
        fs::read_to_string(&emitting).expect("the simulation-binary generator is readable");
    let blocks = doc_blocks(&source);
    let resolved: Vec<&DocBlock> = blocks
        .iter()
        .filter(|block| block.spellings.contains(&DocSpelling::Raw))
        .collect();
    assert_eq!(
        resolved.len(),
        1,
        "simulation_binary.rs should emit exactly one `#[doc = …]` run, saw {}",
        resolved.len(),
    );
    assert!(
        resolved[0].unresolved.is_empty()
            && resolved[0]
                .text
                .iter()
                .any(|line| line.contains("Invoke ONCE")),
        "the emitted doc text was not recovered: {:#?}",
        resolved[0],
    );
}
