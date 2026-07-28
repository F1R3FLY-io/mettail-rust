use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

/// The single reader for the workspace manifest keys that say where specifications live.
///
/// Pulled in by `#[path]` rather than as a dependency: `dovetail` has exactly one
/// workspace dependency (`rigail`) by design, and this audit must not be the thing that
/// breaks that. The file is `ast`'s module of the same name — one source, two consumers.
// `dead_code` is wrong HERE: this consumer needs only `language_roots`, while
// `proptest_corpus_dir` and `find_workspace_root` are live in the other consumer (`ast`),
// where the same file is a normal module and the lint still guards them.
#[allow(dead_code)]
#[path = "../../ast/src/manifest.rs"]
mod manifest;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Requirement {
    Equation,
    DirectionalRewrite,
    CongruencePremise,
    FoldNativeHandler,
    FreshnessPremise,
    EnvRelationPremise,
    BehavioralGuard,
    SyntheticInjectionGuard,
    CollectionPattern,
    MapPattern,
    ZipPattern,
    BinderPattern,
    SubstitutionPattern,
    RhoCommHandlerContract,
    RhoResourceGuardContract,
}

#[derive(Debug)]
struct DiscoveredLanguage {
    rocq_name: String,
    source_path: PathBuf,
    requirements: BTreeSet<Requirement>,
    /// `options { parse_only: true }` — a syntax/lex-only fixture excluded from
    /// the production LanguageDefInventory (see `declared_parse_only`).
    parse_only: bool,
    /// Whether the source declares any reduction semantics — the anti-loophole
    /// guard: a `parse_only` language must have none (see `has_reduction_semantics`).
    has_reduction: bool,
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("dovetail crate has workspace parent")
        .to_path_buf()
}

fn read_repo_file(relative: &str) -> String {
    let path = repo_root().join(relative);
    fs::read_to_string(&path).unwrap_or_else(|err| panic!("failed to read {path:?}: {err}"))
}

fn repo_relative(path: &Path) -> String {
    path.strip_prefix(repo_root())
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

// ══════════════════════════════════════════════════════════════════════════════
// Quotation vs. declaration
// ══════════════════════════════════════════════════════════════════════════════

/// `source` with every comment and string literal blanked out — the DECLARATIONS
/// only, with line and column structure preserved.
///
/// # Why this file cannot scan raw source
///
/// Every scanner below looks for a short needle. A needle is evidence of a
/// declaration only where a declaration can occur, and three places in a Rust file
/// look exactly like the DSL without being it:
///
/// | quotation | needle it hit | requirement wrongly reported |
/// |---|---|---|
/// | `//! # Clause-by-clause containment` (a markdown heading) | `"# "` | `ReqFreshnessPremise` |
/// | `//! \| omnibus clause \| our clause \|` (a markdown table row) | `"\| "` | `ReqCongruencePremise` |
/// | ``//! `rholang.rs` `POutput` idiom`` (prose quoting another language) | `"POutput"` | `ReqRhoCommHandlerContract` |
///
/// Those are not hypotheticals: they were measured on `json`, `monoid`, and `turing`,
/// which were each told they declare a freshness premise they do not have. The
/// direction is harmless for the coverage theorems — over-approximating the
/// requirement set cannot cause a requirement to be MISSED — but it is wrong as
/// documentation, and a reader has no way to tell a reported requirement from a
/// quoted one.
///
/// # What is removed
///
/// Line comments (`//`, `///`, `//!`) to end of line; block comments (`/* … */`,
/// nested as Rust allows); string literals including raw (`r"…"`, `r#"…"#`) and byte
/// (`b"…"`, `br#"…"#`) forms; and character literals. A `'` that does not open a
/// well-formed character literal is left alone, so lifetimes (`&'static str`) survive
/// intact rather than swallowing the rest of the file.
///
/// Removed text becomes spaces, and newlines are kept, so line-oriented scans see the
/// same line numbering as the file on disk.
fn declarations_only(source: &str) -> String {
    let chars: Vec<char> = source.chars().collect();
    let mut out = String::with_capacity(source.len());
    let mut index = 0usize;

    /// Blank one character, keeping newlines so line structure survives.
    fn blank(out: &mut String, ch: char) {
        out.push(if ch == '\n' { '\n' } else { ' ' });
    }

    /// The raw/byte string prefix at `start` (`r`, `b`, `br`) with its hash count,
    /// or `None` when this is an ordinary identifier rather than a literal prefix.
    fn raw_prefix(chars: &[char], start: usize) -> Option<(usize, usize)> {
        let mut at = start;
        let mut saw_raw = false;
        if chars.get(at) == Some(&'b') {
            at += 1;
        }
        if chars.get(at) == Some(&'r') {
            at += 1;
            saw_raw = true;
        }
        if !saw_raw {
            return None;
        }
        let hashes = chars[at..].iter().take_while(|ch| **ch == '#').count();
        (chars.get(at + hashes) == Some(&'"')).then_some((at + hashes + 1 - start, hashes))
    }

    while index < chars.len() {
        let ch = chars[index];
        let previous = index.checked_sub(1).map(|at| chars[at]);
        let continues_identifier = previous.is_some_and(|ch| ch.is_alphanumeric() || ch == '_');

        match ch {
            // ── line comment ──
            '/' if chars.get(index + 1) == Some(&'/') => {
                while index < chars.len() && chars[index] != '\n' {
                    blank(&mut out, chars[index]);
                    index += 1;
                }
            },
            // ── block comment (nested, as Rust allows) ──
            '/' if chars.get(index + 1) == Some(&'*') => {
                let mut depth = 1usize;
                out.push_str("  ");
                index += 2;
                while index < chars.len() && depth > 0 {
                    if chars[index] == '/' && chars.get(index + 1) == Some(&'*') {
                        depth += 1;
                        out.push_str("  ");
                        index += 2;
                    } else if chars[index] == '*' && chars.get(index + 1) == Some(&'/') {
                        depth -= 1;
                        out.push_str("  ");
                        index += 2;
                    } else {
                        blank(&mut out, chars[index]);
                        index += 1;
                    }
                }
            },
            // ── raw / byte string literal ──
            'r' | 'b' if !continues_identifier && raw_prefix(&chars, index).is_some() => {
                let (opener, hashes) = raw_prefix(&chars, index).expect("checked by the guard");
                for _ in 0..opener {
                    out.push(' ');
                }
                index += opener;
                loop {
                    let closes = chars.get(index) == Some(&'"')
                        && chars[index + 1..]
                            .iter()
                            .take(hashes)
                            .filter(|ch| **ch == '#')
                            .count()
                            == hashes;
                    if index >= chars.len() || closes {
                        break;
                    }
                    blank(&mut out, chars[index]);
                    index += 1;
                }
                for _ in 0..(hashes + 1).min(chars.len().saturating_sub(index)) {
                    out.push(' ');
                    index += 1;
                }
            },
            // ── ordinary (or byte) string literal ──
            'b' if !continues_identifier && chars.get(index + 1) == Some(&'"') => {
                out.push_str("  ");
                index += 2;
                index = blank_string_body(&mut out, &chars, index);
            },
            '"' => {
                out.push(' ');
                index += 1;
                index = blank_string_body(&mut out, &chars, index);
            },
            // ── character literal, but NOT a lifetime ──
            '\'' => match character_literal_len(&chars, index) {
                Some(len) => {
                    for _ in 0..len {
                        out.push(' ');
                    }
                    index += len;
                },
                None => {
                    out.push(ch);
                    index += 1;
                },
            },
            _ => {
                out.push(ch);
                index += 1;
            },
        }
    }

    out
}

/// Blank a string literal body starting at `index`, returning the index past its
/// closing quote. `\`-escapes are consumed as a unit so `"\""` does not end early.
fn blank_string_body(out: &mut String, chars: &[char], mut index: usize) -> usize {
    while index < chars.len() {
        match chars[index] {
            '\\' => {
                out.push_str("  ");
                index += 2;
            },
            '"' => {
                out.push(' ');
                index += 1;
                return index;
            },
            ch => {
                out.push(if ch == '\n' { '\n' } else { ' ' });
                index += 1;
            },
        }
    }
    index
}

/// The length of the character literal opening at `index`, or `None` when the quote
/// opens a lifetime (`'static`, `'a`) instead.
fn character_literal_len(chars: &[char], index: usize) -> Option<usize> {
    match chars.get(index + 1)? {
        '\\' => {
            // `'\n'`, `'\''`, `'\u{1F600}'` — scan to the closing quote.
            let close = chars[index + 2..]
                .iter()
                .take(12)
                .position(|ch| *ch == '\'')?;
            Some(index + 2 + close + 1 - index)
        },
        _ if chars.get(index + 2) == Some(&'\'') => Some(3),
        _ => None,
    }
}

fn is_language_macro_source(source: &str) -> bool {
    source
        .lines()
        .any(|line| line.trim_start().starts_with("language!"))
}

fn declared_language_names(source: &str) -> Vec<String> {
    let mut waiting_for_name = false;
    let mut names = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("language!") {
            waiting_for_name = true;
            continue;
        }
        if !waiting_for_name {
            continue;
        }
        let Some(rest) = trimmed.strip_prefix("name:") else {
            continue;
        };
        if let Some(name) = rest
            .trim()
            .trim_end_matches(',')
            .split(|ch: char| ch.is_whitespace() || ch == ',')
            .next()
            .filter(|name| !name.is_empty())
        {
            names.push(name.to_owned());
            waiting_for_name = false;
        }
    }
    names
}

/// Whether the `language!` source declares `options { parse_only: true }`.
fn declared_parse_only(source: &str) -> bool {
    source.lines().any(|line| {
        line.trim()
            .strip_prefix("parse_only:")
            .map(|rest| rest.trim().trim_end_matches(',').trim() == "true")
            .unwrap_or(false)
    })
}

/// Textual detection of reduction semantics — the dovetail-side mirror of the AST
/// test's structural guard. A `parse_only` language must have NONE: no non-empty
/// `equations`/`rewrites`/`logic`/`guards` block. Empty `equations {}`/`rewrites {}`
/// (which some thin smoke languages carry) do NOT count, matching the AST side's
/// `!def.equations.is_empty()`.
fn has_reduction_semantics(source: &str) -> bool {
    nonempty_block(source, "equations")
        || nonempty_block(source, "rewrites")
        || nonempty_block(source, "logic")
        || nonempty_block(source, "guards")
}

/// Whether `source` contains a `<name> { … }` block with any non-blank,
/// non-comment content between its braces (whitespace-tolerant).
fn nonempty_block(source: &str, name: &str) -> bool {
    let inline_open = format!("{name} {{");
    let inline_open_tight = format!("{name}{{");
    let mut lines = source.lines();
    while let Some(line) = lines.next() {
        let trimmed = line.trim();
        let is_open = trimmed == name
            || trimmed.starts_with(&inline_open)
            || trimmed.starts_with(&inline_open_tight);
        if !is_open {
            continue;
        }
        // Inline form: `equations { <maybe content> }` on one line (possibly with
        // a trailing comma). Content is strictly between the braces.
        if let Some(open_idx) = trimmed.find('{') {
            let after = &trimmed[open_idx + 1..];
            if let Some(close_idx) = after.find('}') {
                if after[..close_idx].trim().is_empty() {
                    continue; // inline empty block `{}`
                }
                return true; // inline non-empty block
            }
        }
        // Multi-line: the first meaningful line is not the closing brace.
        for next in lines.by_ref() {
            let nt = next.trim();
            if nt.is_empty() || nt.starts_with("//") {
                continue;
            }
            return !nt.starts_with('}');
        }
    }
    false
}

// `rocq_inventory_names` was removed with the name-level equality it served (task #69
// S5). It scraped `inventory_name := "…"` out of `LanguageDefInventory.v` so this audit
// could compare name SETS; the mechanical inventory is now generated into
// `LanguageDefInventoryGenerated.v` and checked by
// `generated_rocq_inventory_matches_the_discovered_sources`, and no other caller existed.

fn rocq_current_requirement_names(source: &str) -> BTreeSet<String> {
    let marker = "Definition current_mettail_rewrite_requirements";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("Rocq coverage file missing `{marker}`"));
    let list_source = &source[start..];
    let open = list_source
        .find('[')
        .unwrap_or_else(|| panic!("Rocq current requirement list has no opening `[`"));
    let close = list_source[open..]
        .find(']')
        .unwrap_or_else(|| panic!("Rocq current requirement list has no closing `]`"));

    list_source[open + 1..open + close]
        .split(|ch: char| ch == ';' || ch.is_whitespace())
        .filter(|token| token.starts_with("Req"))
        .map(ToOwned::to_owned)
        .collect()
}

/// Directories that hold no hand-written source and are never scanned.
///
/// `target` is build output; `generated` is macro output (the `language!` expansion,
/// not a declaration). Nothing else is skipped: every other directory under a root is
/// walked, so no `language!` can be placed out of reach of the audit. In particular
/// `bin` is NOT skipped any more — a definition dropped into `languages/src/bin/`
/// used to leave the scan silently, which is the same hole this file exists to close.
const NON_SOURCE_DIRECTORIES: &[&str] = &["target", "generated"];

fn discover_rust_files(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_path_buf()];
    let mut files = Vec::new();
    while let Some(path) = pending.pop() {
        let metadata =
            fs::metadata(&path).unwrap_or_else(|err| panic!("failed to stat {path:?}: {err}"));
        if metadata.is_dir() {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if NON_SOURCE_DIRECTORIES.contains(&name) {
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

/// Every directory that may hold a `language!` definition: the whole `languages`
/// package.
///
/// # Why the root is a package and not a list of sub-directories
///
/// This scan used to name two directories — `languages/src` (production, library
/// modules) and `languages/tests/definitions` (test definitions, declared
/// `options { hosted_in: … }`). Both were scanned deliberately, so that MOVING a file
/// between those two roles could not drop it from the formal inventory. But a
/// definition in a THIRD place — a top-level `languages/tests/*.rs` — was in neither
/// root, and that is not a hypothetical:
///
/// | declaration | where it lived | consequence |
/// |---|---|---|
/// | `Pi`, `Turing` | `languages/tests/omnibus_*.rs` | equations, rewrites, a freshness premise, a substituting COMM, a native fold, two transition rewrites — ALL outside formal coverage until `e1bfcd38` moved the files |
/// | `L9FltToy`, `L9ModalToy` | `languages/tests/l9_*_toy.rs` | a `step` rewrite and native `![…]` fold actions each, outside formal coverage until this scan was widened |
///
/// An enumeration of sub-directories makes PLACEMENT a coverage decision, and the
/// decision is invisible: writing a reduction language one directory to the left
/// removes it from the audit and no test says anything. The root is therefore the
/// package itself, and [`language_declarations_cannot_hide_outside_the_scanned_roots`]
/// proves the choice is total for the whole repository rather than just this package.
///
/// # Why the root is READ rather than written here
///
/// The same list is needed by `ast/tests/dovetail_language_inventory.rs`, which audits
/// the identical corpus through the real `LanguageDef` parser instead of a textual scan.
/// Two literals that must agree is a drift waiting to happen — widen one and a
/// specification becomes invisible to the other audit, silently. Both now read the single
/// declaration in the workspace manifest, `[package.metadata.mettail] language_roots`,
/// through [`manifest`] — which is itself ONE file, shared by `#[path]` because `dovetail`
/// deliberately depends on nothing but `rigail`.
fn language_definition_roots() -> Vec<std::path::PathBuf> {
    manifest::language_roots(&repo_root()).unwrap_or_else(|err| {
        panic!(
            "cannot determine the language definition roots: {err}\n\nThis audit scans \
             exactly those roots, so it must NOT continue with a guess: an empty or \
             narrowed root list would make it pass by scanning nothing."
        )
    })
}

/// Whether the REPOSITORY-WIDE sweep declines to enter a directory.
///
/// `target` is build output; `scratchpad` is the documented wipeable campaign scratch
/// area (gitignored, never a build input, cleared by the harness), so a stale probe
/// left in either must not be able to fail this suite. DOT-directories are tooling
/// state and never hold hand-written source: `.git` is object storage, and
/// `.formal-tmp` holds the formal pipeline's `cargo expand` dumps — two 40 MB
/// single-item files whose scan dominated everything else this test does.
fn is_swept_over(directory_name: &str) -> bool {
    directory_name.starts_with('.') || matches!(directory_name, "target" | "scratchpad")
}

/// Every file in the repository that DECLARES a `language!`, wherever it lives.
///
/// Quotation does not count: the text is stripped by [`declarations_only`] first, so
/// the many files that discuss the macro in documentation (`prattail/src/lib.rs`,
/// `macros/src/…`, `languages/tests/doc_comment_metadata.rs`, and this file) are not
/// mistaken for definitions.
fn repository_language_declarations() -> BTreeSet<PathBuf> {
    let mut pending = vec![repo_root()];
    let mut declaring = BTreeSet::new();

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
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
            let source = fs::read_to_string(&path).unwrap_or_default();
            // Cheap gate first: reading is unavoidable, stripping is not.
            if source.contains("language!") && is_language_macro_source(&declarations_only(&source))
            {
                declaring.insert(path);
            }
        }
    }

    declaring
}

fn discover_language_sources() -> Vec<DiscoveredLanguage> {
    language_definition_roots()
        .iter()
        .filter(|root| root.exists())
        .flat_map(|root| discover_rust_files(root))
        .collect::<Vec<_>>()
        .into_iter()
        .flat_map(|path| {
            let raw = fs::read_to_string(&path)
                .unwrap_or_else(|err| panic!("failed to read {path:?}: {err}"));
            // Every scan below reads DECLARATIONS, never quotations: a `language!`
            // named in prose is not a definition, a `parse_only: true` inside a
            // comment must not exclude a language from the inventory, and a needle
            // in a markdown table is not a premise.
            let source = declarations_only(&raw);
            if !is_language_macro_source(&source) {
                return Vec::new();
            }
            let display_names = declared_language_names(&source);
            assert!(
                !display_names.is_empty(),
                "{} contains a language! macro without a `name:` declaration",
                repo_relative(&path)
            );
            let requirements = classify_source(&source);
            let parse_only = declared_parse_only(&source);
            let has_reduction = has_reduction_semantics(&source);
            display_names
                .into_iter()
                .map(|display_name| DiscoveredLanguage {
                    rocq_name: display_name.to_ascii_lowercase(),
                    source_path: path.clone(),
                    requirements: requirements.clone(),
                    parse_only,
                    has_reduction,
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

/// The `.rs` files this audit actually reads.
fn audited_files() -> BTreeSet<PathBuf> {
    language_definition_roots()
        .iter()
        .filter(|root| root.exists())
        .flat_map(|root| discover_rust_files(root))
        .collect()
}

/// No `language!` in this repository lies outside the files this audit reads.
///
/// The roots above make the scan total for the `languages` package. This makes it
/// total for the REPOSITORY, which is the property that matters: it is what stops
/// placement from ever being a coverage decision again, and it is what makes the
/// duplicate root list in `ast/tests/dovetail_language_inventory.rs` harmless — that
/// side enforces the same invariant independently, so a definition can only be
/// invisible to one audit by being invisible to that audit's totality check too.
///
/// When this fails there are exactly two honest resolutions, and neither is to delete
/// the check: move the definition under a scanned root, or widen the roots to include
/// where it now lives. Both leave the language inventoried.
#[test]
fn language_declarations_cannot_hide_outside_the_scanned_roots() {
    let audited = audited_files();
    let declaring = repository_language_declarations();

    let escaped = declaring
        .difference(&audited)
        .map(|path| repo_relative(path))
        .collect::<Vec<_>>();
    assert!(
        escaped.is_empty(),
        "{} file(s) declare a `language!` that this audit never reads, so their \
         equations, rewrites, folds and premises carry NO formal requirements entry \
         and nothing would say so:\n{}\n\nFix by moving the definition under a scanned \
         root ({:?}), or by widening `language_definition_roots` to cover where it \
         lives. Placement must not decide formal coverage.",
        escaped.len(),
        escaped
            .iter()
            .map(|path| format!("  {path}"))
            .collect::<Vec<_>>()
            .join("\n"),
        language_definition_roots()
            .iter()
            .map(|root| repo_relative(root))
            .collect::<Vec<_>>(),
    );

    // The sweep reaches the repository and finds the declarations that are really
    // there — a walk that silently visited nothing would make the check vacuous.
    assert!(
        declaring.len() >= 40,
        "the repository-wide sweep found only {} declaring file(s); it is not reaching \
         the source tree",
        declaring.len()
    );

    // A definition in a TOP-LEVEL `languages/tests/*.rs` is seen. This is the case the
    // previous roots missed, and the canary exists so it stays covered even if every
    // other top-level declaration is one day relocated.
    let canary = repo_root().join("languages/tests/inventory_discovery_canary.rs");
    assert!(
        declaring.contains(&canary),
        "the discovery canary must be recognised as a declaration"
    );
    assert!(
        audited.contains(&canary),
        "the discovery canary must be inside the audited file set"
    );
}

/// Whether some rule declares a REWRITE PREMISE — `Label . | S ~> T |- …`.
///
/// The DSL puts a rule's premises between the label's `.` and the turnstile `|-`, so
/// a congruence premise is a `~>` on the premise side of a statement. The previous
/// test — "the file contains `| ` somewhere AND `~>` somewhere" — is satisfied by any
/// rewriting language that also contains a pipe for any reason, and two such reasons
/// occur in this corpus: a markdown table row in a doc comment, and a Rust closure
/// (`map_err(|_| ())`) inside a native action. Turing has both, no congruence rule,
/// and was reported with one.
///
/// Statements are `;`-separated. Splitting there cannot manufacture a premise: it can
/// only cut a statement into smaller pieces, and a piece claims a congruence premise
/// only if a `~>` and a following `|-` survive together inside it.
fn declares_congruence_premise(code: &str) -> bool {
    code.split(';').any(|statement| match statement.find("|-") {
        Some(turnstile) => statement[..turnstile].contains("~>"),
        None => false,
    })
}

/// Whether some rule declares a GUARD SLOT — `?<name>:Guard` in a term context.
///
/// The previous test also accepted the bare word `where` surrounded by spaces, which
/// matches English prose: five demo languages were reported with a behavioral guard
/// because their header comments contain the phrase "where the installed …". Worse,
/// it did not match the guard that `GuardOptSmoke` actually declares — `?g:Guard`,
/// whose slot name is not the literal `guard` — so that language's only route to its
/// REAL requirement was a doc comment. Matching the slot shape covers every spelling
/// of the name and reads no prose.
fn declares_guard_slot(code: &str) -> bool {
    code.match_indices('?').any(|(at, _)| {
        let rest = &code[at + 1..];
        let name = rest
            .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
            .unwrap_or(rest.len());
        if name == 0 {
            return false;
        }
        rest[name..]
            .trim_start()
            .strip_prefix(':')
            .is_some_and(|typed| typed.trim_start().starts_with("Guard"))
    })
}

/// Classify a `language!` source by the Dovetail rewrite requirements it declares.
///
/// `source` must already have been through [`declarations_only`]: every needle here
/// is evidence of a declaration, and none of them can tell prose from code by itself.
fn classify_source(source: &str) -> BTreeSet<Requirement> {
    let mut reqs = BTreeSet::new();
    if source
        .lines()
        .any(|line| line.contains("|-") && line.contains(" = "))
    {
        reqs.insert(Requirement::Equation);
    }
    if source.contains("~>") || source.contains("extends: [BaseMath]") {
        reqs.insert(Requirement::DirectionalRewrite);
    }
    if declares_congruence_premise(source) || source.contains("extends: [BaseMath]") {
        reqs.insert(Requirement::CongruencePremise);
    }
    if source.contains("] fold")
        || source.contains("] step")
        || source.contains("extends: [BaseMath]")
    {
        reqs.insert(Requirement::FoldNativeHandler);
    }
    if source.contains("# ") {
        reqs.insert(Requirement::FreshnessPremise);
    }
    if source.contains("logic {") || source.contains("relation ") || source.contains(" = { x:") {
        reqs.insert(Requirement::EnvRelationPremise);
    }
    if declares_guard_slot(source) || source.contains("guards {") {
        reqs.insert(Requirement::BehavioralGuard);
        reqs.insert(Requirement::SyntheticInjectionGuard);
    }
    if source.contains("HashBag(")
        || source.contains("Vec(")
        || source.contains("Vec<")
        || source.contains("...rest")
        || source.contains("*opt(")
        || source.contains(".*sep")
    {
        reqs.insert(Requirement::CollectionPattern);
    }
    if source.contains("HashMap<") || source.contains("HashMap(") || source.contains(":Map") {
        reqs.insert(Requirement::MapPattern);
    }
    if source.contains("*zip(") {
        reqs.insert(Requirement::ZipPattern);
    }
    if source.contains('^') && source.contains("->") {
        reqs.insert(Requirement::BinderPattern);
    }
    if source.contains("eval ") || source.contains("eval(") {
        reqs.insert(Requirement::SubstitutionPattern);
    }
    if source.contains("PInputs") || source.contains("POutput") || source.contains("PGuardedInput")
    {
        reqs.insert(Requirement::RhoCommHandlerContract);
    }
    if source.contains("guards {") {
        reqs.insert(Requirement::RhoResourceGuardContract);
    }
    reqs
}

// ══════════════════════════════════════════════════════════════════════════════
// Guards for the quotation/declaration boundary
// ══════════════════════════════════════════════════════════════════════════════

/// The classification pipeline as `discover_language_sources` runs it.
fn classify(raw: &str) -> BTreeSet<Requirement> {
    classify_source(&declarations_only(raw))
}

/// Every requirement of the taxonomy, DECLARED — so the scan cannot pass by seeing
/// nothing.
///
/// This is the half that matters most. Removing quotations narrows the classifier,
/// and a classifier that narrows too far drops formal coverage SILENTLY: the
/// inventory test only asserts that each production language classifies something and
/// that the aggregate is a subset of the Rocq requirement list, both of which a
/// too-small set satisfies. So every needle is exercised in the position the DSL
/// actually puts it.
const DECLARES_EVERY_REQUIREMENT: &str = r##"
language! {
    name: EveryRequirement,

    types {
        Proc
        Name
        ![Vec<Proc>] as List
        ![HashMap<Proc, Proc>] as Map
    },

    terms {
        PZero . |- "Nil" : Proc ;
        POutput . n:Name, p:Proc |- n "!" "(" p ")" : Proc ;
        PFor . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" p : Proc ;
        PPar . ps:HashBag(Proc) |- ps.*sep("|") : Proc ;
        PZip . ns:Vec(Name), xs:Vec(Proc) |- *zip(ns,xs) : Proc ;
        PMap . m:Map |- "{" m "}" : Proc ;
        PCheck . k:Proc, ?g:Guard |- "check" "(" k g ")" : Proc ;
        AddNum . a:Proc, b:Proc |- a "+" b : Proc ![a + b] fold ;
    },

    equations {
        ParUnit . |- (PPar {P, PZero}) = P ;
        ScopeExt . | x # ...rest |- (PNew ^x.P) = (PNew ^x.P) ;
    },

    rewrites {
        Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest})
             ~> (PPar {(eval cont Q), ...rest}) ;
        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
    },

    logic {
        relation ok(Proc);
    },

    guards {
        channels { PCheck(ch: Name) }
    },
}
"##;

/// The same needles, QUOTED — and nothing is reported.
///
/// Each line below is a real shape from this repository's language sources: markdown
/// headings and tables in module documentation, prose naming another language's rule
/// labels, a commented-out rewrite, and DSL terminals that happen to be pipes.
const QUOTES_EVERY_REQUIREMENT: &str = r##"
//! # Clause-by-clause containment
//!
//! | omnibus clause | our clause | delta |
//! | --- | --- | --- |
//! | `Mul . x:M, y:M \|- x "*" y : M ;` | identical | — |
//!
//! Follows the `rholang.rs` `POutput` / `PInputs` / `PGuardedInput` idiom, where the
//! carrier is a `Vec(T)` slot. The paper writes `x # ...rest` for freshness and
//! `S ~> T` for a step; substitution is spelled `eval`, e.g. `(eval cont Q)`, and a
//! `?g:Guard` slot would sit in the term context. See `logic { relation ok(Proc); }`
//! and `guards { channels }`, plus `*zip(ns,xs)`, `HashBag(Proc)`, `:Map`, `] fold`,
//! `^x.p:[Name -> Proc]`, and an equation `|- (Mul X Y) = (Mul Y X)`.
/*
    ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
    logic { relation ok(Proc); }
*/
language! {
    name: QuotesOnly,
    types { Sym Tape },
    terms {
        // A tape whose delimiters are pipes: terminals, not premise bars.
        Tp . h:Sym |- "<" "|" h "|" ">" : Tape ;
    },
}
"##;

/// Quoted needles are not declarations.
#[test]
fn quotation_declares_nothing() {
    let quoted = classify(QUOTES_EVERY_REQUIREMENT);
    assert!(
        quoted.is_empty(),
        "a file that only TALKS about these constructs declares none of them, got {:?}",
        quoted
            .iter()
            .map(|req| rocq_requirement_name(*req))
            .collect::<Vec<_>>()
    );

    // And the scan is not passing by reading an empty string: the same text with its
    // quoting removed is exactly what the declaring fixture reports.
    assert!(
        !classify(DECLARES_EVERY_REQUIREMENT).is_empty(),
        "the declaring fixture must be non-empty or this test proves nothing"
    );
}

/// Declared needles are reported — every one of them.
#[test]
fn declaration_reports_every_requirement() {
    let declared = classify(DECLARES_EVERY_REQUIREMENT);
    let missing = [
        Requirement::Equation,
        Requirement::DirectionalRewrite,
        Requirement::CongruencePremise,
        Requirement::FoldNativeHandler,
        Requirement::FreshnessPremise,
        Requirement::EnvRelationPremise,
        Requirement::BehavioralGuard,
        Requirement::SyntheticInjectionGuard,
        Requirement::CollectionPattern,
        Requirement::MapPattern,
        Requirement::ZipPattern,
        Requirement::BinderPattern,
        Requirement::SubstitutionPattern,
        Requirement::RhoCommHandlerContract,
        Requirement::RhoResourceGuardContract,
    ]
    .into_iter()
    .filter(|req| !declared.contains(req))
    .map(rocq_requirement_name)
    .collect::<Vec<_>>();

    assert!(
        missing.is_empty(),
        "the classifier stopped seeing declarations it must see: {missing:?}"
    );
}

/// The guard slot is matched by SHAPE, so every spelling of its name is seen.
#[test]
fn guard_slot_is_matched_by_shape_not_by_name() {
    assert!(
        declares_guard_slot("PCheck . k:Int, *opt(?g:Guard)"),
        "the corpus spells it `?g`"
    );
    assert!(declares_guard_slot("PGuardedInput . n:Name, ?guard:Guard, ^x.p:[Name -> Proc]"));
    assert!(declares_guard_slot("Wrapped . ?the_guard : Guard"), "whitespace-tolerant");
    // Prose, and a `?` that opens no slot.
    assert!(!declares_guard_slot("where the installed receiver binds it"));
    assert!(!declares_guard_slot("is it a guard? Guard is the type."));
    assert!(!declares_guard_slot("k:Int, ?g:Int"));
}

/// A congruence premise is a rewrite ON THE PREMISE SIDE of a rule.
#[test]
fn congruence_premise_is_matched_on_the_premise_side() {
    assert!(declares_congruence_premise("ParCong . | S ~> T |- (PPar {S}) ~> (PPar {T}) ;"));
    assert!(
        declares_congruence_premise("WrapCong . | S ~> T\n    |- (Wrap S) ~> (Wrap T) ;"),
        "the premise may sit on its own line"
    );
    // A rewrite with no premise: the `~>` is on the conclusion side only.
    assert!(!declares_congruence_premise("D_q0_0 . |- (Cf Q0 (Tp L Zero R)) ~> (Cf Q1 R) ;"));
    // A Rust closure inside a native action, next to an unrelated rewrite rule.
    assert!(!declares_congruence_premise(
        "eval: ![ { parse_int_lit(text).map_err(|_| ()) } ] ;\n D . |- (A) ~> (B) ;"
    ));
}

/// The stripper keeps declarations and drops quotations, with line structure intact.
#[test]
fn declarations_only_removes_exactly_the_quotations() {
    let stripped = declarations_only(
        "//! # heading\n\
         let s = \"# in a string\";\n\
         /* # in a block /* nested */ comment */\n\
         ScopeExt . | x # ...rest |- (PNew ^x.P) = (PNew ^x.P) ;\n\
         let c = '#';\n\
         fn f<'a>(x: &'a str) -> &'a str { x }\n",
    );

    assert_eq!(
        stripped.lines().count(),
        6,
        "line structure must survive so line-oriented scans keep their numbering"
    );
    assert!(stripped.contains("ScopeExt . | x # ...rest |-"), "the declaration survives");
    assert!(!stripped.contains("heading"), "doc comment removed");
    assert!(!stripped.contains("in a string"), "string literal removed");
    assert!(!stripped.contains("nested"), "nested block comment removed");
    assert_eq!(stripped.matches("# ").count(), 1, "one freshness premise, in code");
    assert!(
        stripped.contains("fn f<'a>(x: &'a str) -> &'a str"),
        "a lifetime is not a character literal and must not swallow the file"
    );

    // Raw and byte strings, which the corpus uses for token patterns.
    let raw = declarations_only("pattern: r\"(0b[01]|0o[0-7])\"; keep_me: 1");
    assert!(!raw.contains("0b[01]"), "raw string removed");
    assert!(raw.contains("keep_me: 1"), "code after a raw string survives");
    let hashed = declarations_only("p: r#\"a \"quoted\" b\"#; keep_me: 2");
    assert!(!hashed.contains("quoted"), "hashed raw string removed");
    assert!(hashed.contains("keep_me: 2"), "code after a hashed raw string survives");
    let bytes = declarations_only("b: b\"# bytes\"; keep_me: 3");
    assert!(!bytes.contains("bytes"), "byte string removed");
    assert!(bytes.contains("keep_me: 3"));
}

/// The measured false positives, pinned on the real corpus — with the true positives
/// they sat next to.
///
/// `json`, `monoid`, and `turing` were each reported with a freshness premise because
/// their headers open with markdown `#` headings; `turing` with a congruence premise
/// because its header renders a markdown table; `json` with a Rho COMM handler
/// contract because its header quotes another language's `POutput` idiom. `pi` was
/// reported with a freshness premise TOO — and that one is real (`| x # ...rest` in
/// its `ScopeExt` equation), which is why the fix cannot be "stop looking for `#`".
#[test]
fn requirements_are_not_inherited_from_prose() {
    let discovered = discover_language_sources();
    let requirements = |name: &str| {
        discovered
            .iter()
            .find(|language| language.rocq_name == name)
            .unwrap_or_else(|| panic!("`{name}` must be discovered by the inventory scan"))
            .requirements
            .clone()
    };

    for (name, absent) in [
        ("json", Requirement::FreshnessPremise),
        ("json", Requirement::RhoCommHandlerContract),
        ("json", Requirement::SubstitutionPattern),
        ("monoid", Requirement::FreshnessPremise),
        ("turing", Requirement::FreshnessPremise),
        ("turing", Requirement::CongruencePremise),
    ] {
        assert!(
            !requirements(name).contains(&absent),
            "`{name}` does not declare {} — it only mentions it in prose",
            rocq_requirement_name(absent)
        );
    }

    for (name, present) in [
        ("pi", Requirement::FreshnessPremise),
        ("pi", Requirement::CongruencePremise),
        ("turing", Requirement::DirectionalRewrite),
        ("turing", Requirement::FoldNativeHandler),
        ("json", Requirement::CollectionPattern),
        ("monoid", Requirement::Equation),
        ("guardoptsmoke", Requirement::BehavioralGuard),
    ] {
        assert!(
            requirements(name).contains(&present),
            "`{name}` DOES declare {} and must keep it",
            rocq_requirement_name(present)
        );
    }
}

// ── The generated-Datalog audit was REMOVED (task #69 S6) ────────────────────────
//
// `generated_datalog_relation_heads_are_requirement_classified` read
// `languages/src/generated/*-datalog.rs` and classified each declared relation head into
// the requirement taxonomy. Three independent things made it dead residue rather than
// coverage:
//
//   1. Its subject no longer exists. Datalog/Ascent was replaced by Dovetail/SFT/Rholang;
//      NO generator in this tree emits a `*-datalog.rs`. The files it read were stale
//      output of code deleted long before.
//   2. Its subject set depended on LOCAL BUILD HISTORY. It globbed a gitignored directory,
//      so what it audited was whichever languages happened to have been compiled in that
//      working tree — a different set on a clean checkout than on a developer's machine,
//      and empty on CI. A test whose extension is decided by build history asserts nothing
//      reproducible.
//   3. Its subject set had drifted into fiction. Of the ten `*-datalog.rs` files present,
//      `rhocalc` named a language that no longer exists anywhere in the repository (it was
//      renamed to `rholang`), and the wider directory also held `class2opt`,
//      `crosscatsubst`, `dovetailsmoke` and `fltprobe` — four more stems with no live
//      declaration. The audit was classifying relation heads of languages that are gone.
//
// The requirement coverage it nominally provided is unaffected: the same
// `⊆ current_mettail_rewrite_requirements` property is asserted from the real
// `language!` sources by `source_language_inventory_matches_rocq_inventory_and_taxonomy`,
// which reads declarations rather than build leftovers.
//
// Removed with it: `relation_head`, `declared_relation_head`, `declared_relation`,
// `RelationDecl`, `split_relation_params`, `is_generated_category_relation`,
// `category_relation_heads_from_datalog`, `generated_category_heads`,
// `classify_datalog_head`, and the unit test
// `generated_category_heads_are_derived_from_relation_signatures` — every one of which was
// reachable only from that audit (verified: zero references elsewhere in the workspace).

fn rocq_requirement_name(requirement: Requirement) -> &'static str {
    match requirement {
        Requirement::Equation => "ReqEquation",
        Requirement::DirectionalRewrite => "ReqDirectionalRewrite",
        Requirement::CongruencePremise => "ReqCongruencePremise",
        Requirement::FoldNativeHandler => "ReqFoldNativeHandler",
        Requirement::FreshnessPremise => "ReqFreshnessPremise",
        Requirement::EnvRelationPremise => "ReqEnvRelationPremise",
        Requirement::BehavioralGuard => "ReqBehavioralGuard",
        Requirement::SyntheticInjectionGuard => "ReqSyntheticInjectionGuard",
        Requirement::CollectionPattern => "ReqCollectionPattern",
        Requirement::MapPattern => "ReqMapPattern",
        Requirement::ZipPattern => "ReqZipPattern",
        Requirement::BinderPattern => "ReqBinderPattern",
        Requirement::SubstitutionPattern => "ReqSubstitutionPattern",
        Requirement::RhoCommHandlerContract => "ReqRhoCommHandlerContract",
        Requirement::RhoResourceGuardContract => "ReqRhoResourceGuardContract",
    }
}

/// **G3 — additive inertness.** Adding a `language!` whose requirements are already
/// covered changes no HAND-WRITTEN file outside its own.
///
/// # The two halves of the claim
///
/// 1. **Covered.** Every requirement `AdditiveInertnessCanary` declares is inside the
///    taxonomy `MeTTaILRewriteCoverage.v` proves covered, so no Rocq file needs a new
///    constructor, a new capability, or a new proof.
/// 2. **Inert.** The hand-written `LanguageDefInventory.v` does not name it. It used to
///    have to: both audits asserted name-set EQUALITY against that file, so a language
///    could not exist without a line being pasted into it. Nothing forces that now.
///
/// The one committed file outside the canary's own source that DOES mention it is
/// `LanguageDefInventoryGenerated.v` — which is derived, regenerated by
/// [`generated_rocq_inventory_matches_the_discovered_sources`] under `METTAIL_BLESS=1`,
/// and carries no proof. That is the whole of the residual cost of adding a language, and
/// it is mechanical. This test asserts the canary IS there, because a derived inventory
/// that had silently stopped including a discovered language would be the same defect in
/// the other direction.
///
/// # Anti-vacuity
///
/// Absence is trivially true of a language that does not exist, so the first thing
/// asserted is that the audit really discovers this canary. Without that, deleting the
/// canary file would leave this test green.
#[test]
fn adding_a_covered_language_is_inert() {
    const CANARY: &str = "additiveinertnesscanary";

    let discovered = discover_language_sources();
    let canary = discovered
        .iter()
        .find(|language| language.rocq_name == CANARY)
        .unwrap_or_else(|| {
            panic!(
                "the additive-inertness canary was not discovered by this audit. Absence \
                 from the other files is trivially true of a language that does not \
                 exist, so the rest of this test would be vacuous. Expected a `language! \
                 {{ name: AdditiveInertnessCanary }}` under a scanned root; see \
                 languages/tests/inventory_additive_inertness_canary.rs"
            )
        });
    assert!(
        !canary.parse_only,
        "the canary must be a production language, or it is excluded from the inventory \
         and proves nothing about adding one"
    );
    assert!(
        !canary.requirements.is_empty(),
        "the canary must classify to at least one requirement, or 'its requirements are \
         covered' holds emptily"
    );

    // ── Half 1: covered, so no Rocq proof has to change ──────────────────────────
    let formal_coverage =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v");
    let formal_requirements = rocq_current_requirement_names(&formal_coverage);
    let canary_requirements = canary
        .requirements
        .iter()
        .map(|requirement| rocq_requirement_name(*requirement).to_owned())
        .collect::<BTreeSet<_>>();
    assert!(
        canary_requirements.is_subset(&formal_requirements),
        "the canary declares requirements outside the covered taxonomy \
         ({canary_requirements:?} vs {formal_requirements:?}), so it is not an example of \
         an ALREADY-COVERED language and cannot witness inertness. Either simplify the \
         canary or extend MeTTaILRewriteCoverage.v."
    );

    // ── Half 2: no hand-written file was edited to accommodate it ────────────────
    let hand_written =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/LanguageDefInventory.v");
    assert!(
        !hand_written.contains(CANARY),
        "`LanguageDefInventory.v` names `{CANARY}`. That file is HAND-WRITTEN formal \
         content, and the point of the canary is that adding a covered language does not \
         require touching it. If a test made you add that line, the name-level coupling \
         has been reintroduced — remove the coupling, not the canary."
    );

    // ── The residual, mechanical cost: the DERIVED inventory does list it ────────
    let generated = read_repo_file(GENERATED_INVENTORY_PATH);
    assert!(
        generated.contains(&format!("(\"{CANARY}\"")),
        "the derived inventory does not list `{CANARY}` even though the audit discovers \
         it. Regenerate with `{BLESS_VARIABLE}=1 cargo test -p dovetail --test \
         language_inventory`; a derived inventory that silently omits a discovered \
         language is the same defect as one that goes stale."
    );
}

/// Where the mechanically-derived Rocq inventory lives.
const GENERATED_INVENTORY_PATH: &str =
    "dovetail/formal/rocq/theories/Requirements/LanguageDefInventoryGenerated.v";

/// The environment variable that switches this audit from CHECKING the generated Rocq
/// inventory to REWRITING it.
const BLESS_VARIABLE: &str = "METTAIL_BLESS";

/// Render the discovered inventory as the body of `LanguageDefInventoryGenerated.v`.
///
/// # Why this file is generated rather than maintained
///
/// `LanguageDefInventory.v` used to have to name every language, and both Rust audits
/// asserted their discovered name set EQUALLED the Rocq one. That coupling made adding a
/// language whose requirements were ALREADY covered fail a Rocq-facing test for a purely
/// clerical reason: the proofs below it did not depend on the name, only on the
/// requirements, so the failure carried no formal content. It taught the reflex that a
/// red inventory test is fixed by pasting a line into a `.v` file.
///
/// Splitting the mechanical part out keeps the loud failures and drops the clerical one.
/// A language whose requirements are already covered is INERT: this file changes, the
/// hand-written `.v` does not, and no proof is touched. A language carrying a NEW
/// requirement still fails, and fails in the strongest possible way — the emitted
/// constructor name does not exist, so `LanguageDefInventoryGenerated.v` does not COMPILE
/// until the taxonomy in `MeTTaILRewriteCoverage.v` is extended and the requirement is
/// given a covering capability.
fn render_generated_inventory(production: &[&DiscoveredLanguage]) -> String {
    let mut entries = production
        .iter()
        .map(|language| {
            let requirements = language
                .requirements
                .iter()
                .map(|requirement| rocq_requirement_name(*requirement))
                .collect::<Vec<_>>()
                .join("; ");
            format!("  (\"{}\", [{}])", language.rocq_name, requirements)
        })
        .collect::<Vec<_>>();
    entries.sort();

    format!(
        "(*\n\
         \x20* LanguageDefInventoryGenerated: the MECHANICALLY DERIVED half of the\n\
         \x20* LanguageDef inventory.\n\
         \x20*\n\
         \x20* AUTO-GENERATED — do not edit. Regenerate with:\n\
         \x20*\n\
         \x20*     {bless}=1 cargo test -p dovetail --test language_inventory\n\
         \x20*\n\
         \x20* Produced by `dovetail/tests/language_inventory.rs`, which scans the\n\
         \x20* `language!` declarations under the manifest-declared roots\n\
         \x20* ([package.metadata.mettail] language_roots) and classifies each one into the\n\
         \x20* Dovetail rewrite-requirement taxonomy.\n\
         \x20*\n\
         \x20* This file carries NO proof and NO hand-written judgement; it is data. The formal\n\
         \x20* content that consumes it — the inventory record, the requirement surfaces, and\n\
         \x20* the coverage theorems — stays in LanguageDefInventory.v, which imports this.\n\
         \x20*\n\
         \x20* Its COMPILATION is the load-bearing check: a language carrying a requirement the\n\
         \x20* taxonomy does not yet have emits a constructor name that does not exist, and this\n\
         \x20* file stops compiling until MeTTaILRewriteCoverage.v is extended.\n\
         \x20*\n\
         \x20* Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.\n\
         \x20*)\n\
         \n\
         From Stdlib Require Import List.\n\
         From Stdlib Require Import String.\n\
         \n\
         From Dovetail.Requirements Require Import MeTTaILRewriteCoverage.\n\
         \n\
         Import ListNotations.\n\
         Open Scope string_scope.\n\
         \n\
         (* One entry per production `language!` declaration: its inventory name paired with\n\
         \x20  the requirements classified from its source. Sorted by name, so the file is a\n\
         \x20  function of the declarations alone and never of scan order. *)\n\
         Definition generated_language_inventory : list (string * list RewriteRequirement) := [\n\
         {entries}\n\
         ].\n",
        bless = BLESS_VARIABLE,
        entries = entries.join(";\n"),
    )
}

/// The generated Rocq inventory is exactly what the scan derives.
///
/// Set `METTAIL_BLESS=1` to rewrite it instead of checking it.
#[test]
fn generated_rocq_inventory_matches_the_discovered_sources() {
    let discovered = discover_language_sources();
    let production = discovered
        .iter()
        .filter(|language| !language.parse_only)
        .collect::<Vec<_>>();
    assert!(
        !production.is_empty(),
        "no production language! sources discovered; a generated inventory rendered from \
         nothing would be blessed as empty and every downstream check would go quiet"
    );

    let rendered = render_generated_inventory(&production);
    let path = repo_root().join(GENERATED_INVENTORY_PATH);

    if std::env::var(BLESS_VARIABLE).is_ok() {
        fs::write(&path, &rendered)
            .unwrap_or_else(|err| panic!("failed to write {}: {err}", path.display()));
        return;
    }

    let committed = fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    assert_eq!(
        committed, rendered,
        "{GENERATED_INVENTORY_PATH} is stale. It is DERIVED from the `language!` \
         declarations, so do not hand-edit it — regenerate with\n\n    \
         {BLESS_VARIABLE}=1 cargo test -p dovetail --test language_inventory\n\n\
         and commit the result. If the regenerated file then fails to COMPILE, a language \
         declares a requirement the Rocq taxonomy does not have; extend \
         MeTTaILRewriteCoverage.v rather than editing the generated file."
    );
}

#[test]
fn source_language_inventory_matches_rocq_inventory_and_taxonomy() {
    let discovered_languages = discover_language_sources();
    assert!(
        !discovered_languages.is_empty(),
        "no in-repo language! macro sources discovered"
    );

    // Anti-loophole guard: a parse_only language must declare NO reduction
    // semantics, else fail loudly — a real reduction language cannot hide behind
    // the flag to escape the formal rewrite inventory.
    for language in &discovered_languages {
        if language.parse_only {
            assert!(
                !language.has_reduction,
                "{} is marked `parse_only: true` but declares reduction semantics \
                 (equations/rewrites/logic/guards); parse_only is for syntax-only fixtures",
                repo_relative(&language.source_path)
            );
        }
    }

    // Parse-only fixtures (syntax/lex demonstrations that declare
    // `options { parse_only: true }`, e.g. the keyword-reservation FortranModel/
    // ReservedModel) are excluded from the production LanguageDefInventory.
    // Fail-closed: a language is inventoried unless it explicitly opts out.
    let production = discovered_languages
        .iter()
        .filter(|language| !language.parse_only)
        .collect::<Vec<_>>();

    // ── NAME-LEVEL EQUALITY IS GONE (task #69 S5) ────────────────────────────────
    //
    // This used to assert `discovered_names == rocq_names` and, per language, that
    // `LanguageDefInventory.v` literally contained `inventory_name := "<name>"`. Adding a
    // language whose requirements were ALREADY covered therefore failed a Rocq-facing test
    // for a clerical reason — the proofs in that file depend on the REQUIREMENTS, never on
    // the names — and the fix was to paste a line into a `.v` file. That teaches exactly
    // the wrong reflex about a formal gate.
    //
    // The mechanical half now lives in `LanguageDefInventoryGenerated.v`, checked by
    // `generated_rocq_inventory_matches_the_discovered_sources` and regenerable with
    // `METTAIL_BLESS=1`. What remains here is the assertion that carries formal content:
    // the requirement CLOSURE of every production language is within the taxonomy Rocq
    // proves covered. Adding a language is inert; adding a REQUIREMENT still fails loudly,
    // here and again when the generated file refuses to compile.
    let mut aggregate = BTreeSet::new();

    for language in &production {
        assert!(
            !language.requirements.is_empty(),
            "{} did not classify any Dovetail rewrite requirement",
            repo_relative(&language.source_path)
        );
        aggregate.extend(language.requirements.iter().copied());
    }

    let formal_coverage =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v");
    let formal_requirements = rocq_current_requirement_names(&formal_coverage);
    let aggregate_requirements = aggregate
        .iter()
        .map(|requirement| rocq_requirement_name(*requirement).to_owned())
        .collect::<BTreeSet<_>>();
    assert!(
        aggregate_requirements.is_subset(&formal_requirements),
        "source-classified LanguageDef requirements are not covered by Rocq current_mettail_rewrite_requirements: source={aggregate_requirements:?}, formal={formal_requirements:?}"
    );
}
