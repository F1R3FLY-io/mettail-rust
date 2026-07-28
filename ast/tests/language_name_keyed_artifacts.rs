//! Every artifact keyed on a LANGUAGE NAME must name a language that still exists.
//!
//! # The defect this exists to make loud
//!
//! `RhoCalc` was renamed `Rholang`. Nothing broke. Nothing warned. But
//! `languages/tests/gen_rhocalc_prop.proptest-regressions` — fifty-two seeds for inputs
//! that had once falsified a property of that grammar — stopped being read, because the
//! corpus path is computed from the language name
//! (`macros/src/gen/test_gen/mod.rs::proptest_config_expr`, `gen_{lang_lower}_prop`) and
//! no longer matched any language. Fifty-two counterexamples became a file nobody
//! executed, and the only evidence was that a filename in a directory listing referred to
//! something that no longer existed.
//!
//! # Why this guard is a CLASS guard and not a corpus guard
//!
//! Adding a guard is not the same as enumerating siblings. The corpus is one member of a
//! family: every artifact whose PATH or KEY is derived from the language name strands the
//! same way and just as silently on a rename. This suite covers the whole class, one test
//! per member, each naming its producing site:
//!
//! | artifact                                    | producing site                                        | failure on rename |
//! |---------------------------------------------|-------------------------------------------------------|-------------------|
//! | `gen_{lang}_prop.proptest-regressions`      | `macros/src/gen/test_gen/mod.rs::proptest_config_expr` | ⚠ SILENT          |
//! | `docs/languages/{lang}.md`                  | hand-written prose                                     | ⚠ SILENT          |
//! | `target/generated/{lang}/`                  | `macros/src/logic/writer.rs::lang_generated_dir`       | ⚠ SILENT          |
//! | `{lang}-blocks.ts`, `{lang}-categories.ts`  | `macros/src/gen/blockly/writer.rs`                     | ⚠ SILENT          |
//! | `BUNDLED_LANGUAGES` string keys             | `macros/src/gen/runtime/binder_congruence.rs`          | ⚠ SILENT          |
//!
//! The rest of the name-keyed family fails LOUD — `gen_{lang}_{section}.rs` hosts,
//! `mettail_languages::{lang}`, `src/bin/simulate_{lang}.rs` — because each is a Rust path
//! that stops resolving. Those need no guard, and adding one would only add maintenance.
//!
//! # Where the language names come from
//!
//! The same authority the two specification audits use: the roots declared once in the
//! workspace manifest under `[package.metadata.mettail] language_roots`, read through
//! [`mettail_ast::manifest::language_roots`], walked, and parsed with the REAL
//! `LanguageDef` parser rather than by text match. A guard that derived its own root list
//! could narrow silently — which is the exact failure mode it exists to prevent.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use mettail_ast::language::LanguageDef;
use syn::{Item, ItemMacro};

// ══════════════════════════════════════════════════════════════════════════════
// The declared language set
// ══════════════════════════════════════════════════════════════════════════════

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("`ast` is a workspace member, so its manifest dir has a parent")
        .to_path_buf()
}

/// Directories that hold no hand-written source: build output and macro output.
///
/// Mirrors `dovetail_language_inventory.rs`. Deliberately does NOT skip `bin`: a
/// `language!` written into `languages/src/bin/` is a declaration like any other.
const NON_SOURCE_DIRECTORIES: &[&str] = &["target", "generated"];

/// Every `.rs` file under the manifest-declared language roots.
fn language_files() -> Vec<PathBuf> {
    let roots = mettail_ast::manifest::language_roots(&repo_root()).unwrap_or_else(|err| {
        panic!(
            "cannot determine the language definition roots: {err}\n\nThis guard decides \
             which language names are LIVE by scanning exactly those roots, so it must NOT \
             continue with a guess: an empty or narrowed root list would make every \
             name-keyed artifact look stranded, or (worse, after a later edit) make the \
             guard pass by comparing two empty sets."
        )
    });

    let mut pending: Vec<PathBuf> = roots.into_iter().filter(|root| root.exists()).collect();
    let mut files = Vec::new();

    while let Some(path) = pending.pop() {
        let metadata =
            fs::metadata(&path).unwrap_or_else(|e| panic!("stat {}: {e}", path.display()));
        if metadata.is_dir() {
            let name = path.file_name().and_then(|name| name.to_str()).unwrap_or("");
            if NON_SOURCE_DIRECTORIES.contains(&name) {
                continue;
            }
            for entry in
                fs::read_dir(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
            {
                pending.push(entry.expect("dir entry").path());
            }
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }

    files.sort();
    files
}

fn collect_language_names(items: &[Item], out: &mut BTreeSet<String>) {
    for item in items {
        match item {
            Item::Macro(item_macro) => collect_language_name(item_macro, out),
            Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    collect_language_names(nested, out);
                }
            },
            _ => {},
        }
    }
}

fn collect_language_name(item_macro: &ItemMacro, out: &mut BTreeSet<String>) {
    if item_macro.mac.path.is_ident("language") {
        let def: LanguageDef = syn::parse2(item_macro.mac.tokens.clone())
            .unwrap_or_else(|e| panic!("parse language! body: {e}"));
        out.insert(def.name.to_string().to_lowercase());
    }
}

/// The set of language names, lower-cased, that a `language!` declaration actually
/// defines somewhere under the declared roots.
///
/// This is the ONE referent every name-keyed artifact is checked against.
fn declared_language_names() -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for path in language_files() {
        let source =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        // A file that declares a `language!` necessarily contains that text, so this gate
        // cannot hide a declaration; it only spares `syn` the generated test hosts and
        // simulator binaries that the package-wide root also walks.
        if !source.contains("language!") {
            continue;
        }
        let parsed = syn::parse_file(&source)
            .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
        collect_language_names(&parsed.items, &mut names);
    }
    names
}

/// A floor on the declared set, so no test below can pass by comparing against nothing.
///
/// Every check in this file has the shape "artifact names ⊆ declared names". If
/// `declared_language_names()` ever returned the empty set the subset checks would all
/// fail, which is safe — but if a future edit inverted a check, an empty declared set
/// would make it vacuously true. This is the anti-vacuity floor for the whole file.
#[test]
fn the_declared_language_set_is_non_trivial() {
    let declared = declared_language_names();
    assert!(
        declared.len() >= 30,
        "the scan found only {} declared language name(s) ({:?}); it is not reaching the \
         source tree, and every subset check in this file would be measuring nothing",
        declared.len(),
        declared
    );
    // Named anchors: one library-hosted, one test-hosted. Both are checked so that a
    // regression which drops an entire hosting CLASS is caught, not just a shrunken count.
    for anchor in ["rholang", "calculator", "lambda", "ambient", "class2smoke", "guardedrho"] {
        assert!(
            declared.contains(anchor),
            "`{anchor}` is declared in the source tree but the scan did not find it; the \
             scan is not total and the guards below are measuring a subset"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Member 1 — the proptest counterexample corpora
// ══════════════════════════════════════════════════════════════════════════════

/// Every `gen_<x>_prop.proptest-regressions` under the manifest-declared corpus directory
/// names a language `<x>` that still exists.
///
/// # Why a stranded corpus is worse than a deleted one
///
/// A deleted corpus is visibly gone. A stranded one still sits in the directory listing,
/// still carries its seeds and its `# shrinks to` counterexamples, and is still read by a
/// human as "these cases are covered" — while proptest never opens it, because the path it
/// computes from the language name no longer matches. The seeds are not replayed and
/// nothing says so.
///
/// # Anti-vacuity
///
/// This test was RED when it was written, against an unmutated tree: thirteen corpora were
/// live and `gen_rhocalc_prop.proptest-regressions` was stranded by the `RhoCalc` →
/// `Rholang` rename. It passes only once that corpus's seeds have been merged into the
/// successor language's corpus and the stranded file has been marked superseded. That is
/// the strongest evidence available that it discriminates: it failed on the real defect
/// before any mutation was applied, and the twelve live corpora passed in the same run.
#[test]
fn every_prop_corpus_names_a_live_language() {
    let declared = declared_language_names();
    let corpus_dir = mettail_ast::manifest::proptest_corpus_dir(&repo_root())
        .expect("`[package.metadata.mettail] proptest_corpus_dir` must be declared");

    let mut stranded: Vec<(String, PathBuf)> = Vec::new();
    let mut live = 0usize;

    for entry in fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", corpus_dir.display()))
    {
        let path = entry.expect("dir entry").path();
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        let Some(lang) = name
            .strip_prefix("gen_")
            .and_then(|rest| rest.strip_suffix("_prop.proptest-regressions"))
        else {
            continue;
        };
        if declared.contains(lang) {
            live += 1;
        } else if is_superseded_corpus(&path) {
            // A corpus whose seeds have been MERGED into a successor keeps its file for
            // provenance and declares so in its header. It is not stranded: nothing is
            // waiting to be replayed out of it, because the successor's corpus replays it.
            continue;
        } else {
            stranded.push((lang.to_string(), path));
        }
    }

    assert!(
        stranded.is_empty(),
        "{} proptest corpus file(s) are keyed on a language name that no `language!` \
         declaration defines. proptest computes the corpus path from the LANGUAGE NAME \
         (`macros/src/gen/test_gen/mod.rs::proptest_config_expr`), so these files exist, \
         hold recorded counterexamples, and are never opened — the seeds are silently not \
         replayed:\n  {}\n\nEither (a) merge the seeds into the successor language's \
         corpus and add the `{}` header to the original, recording what it was merged \
         into, or (b) restore the language name. Do NOT delete the file: a shrunk \
         counterexample is not regenerable on demand.",
        stranded.len(),
        stranded
            .iter()
            .map(|(lang, path)| format!("{} (language `{lang}` is not declared)", path.display()))
            .collect::<Vec<_>>()
            .join("\n  "),
        SUPERSEDED_MARKER,
    );

    assert!(
        live >= 12,
        "only {live} live corpus file(s) were seen; this test is not reaching the corpus \
         directory {} and would pass over an empty set",
        corpus_dir.display()
    );
}

/// The header marker a corpus carries once its seeds have been merged into a successor.
const SUPERSEDED_MARKER: &str = "# SUPERSEDED:";

fn is_superseded_corpus(path: &Path) -> bool {
    fs::read_to_string(path)
        .map(|text| text.lines().any(|line| line.starts_with(SUPERSEDED_MARKER)))
        .unwrap_or(false)
}

// ══════════════════════════════════════════════════════════════════════════════
// Member 2 — the per-language documentation pages
// ══════════════════════════════════════════════════════════════════════════════

/// Every `docs/languages/<x>.md` names a language `<x>` that still exists.
///
/// A page for a language that was renamed keeps rendering, keeps being indexed, and keeps
/// being read — describing a grammar that is no longer reachable under that name.
#[test]
fn every_language_doc_page_names_a_live_language() {
    let declared = declared_language_names();
    let docs_dir = repo_root().join("docs/languages");

    // Pages that are not per-language: the index, and the tooling that lints the set.
    const NOT_A_LANGUAGE_PAGE: &[&str] = &["readme"];

    let mut stranded = Vec::new();
    let mut live = 0usize;

    for entry in
        fs::read_dir(&docs_dir).unwrap_or_else(|e| panic!("read {}: {e}", docs_dir.display()))
    {
        let path = entry.expect("dir entry").path();
        let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
            continue;
        };
        if path.extension().and_then(|e| e.to_str()) != Some("md") {
            continue;
        }
        let stem = stem.to_lowercase();
        if NOT_A_LANGUAGE_PAGE.contains(&stem.as_str()) {
            continue;
        }
        if declared.contains(&stem) {
            live += 1;
        } else {
            stranded.push(path);
        }
    }

    assert!(
        stranded.is_empty(),
        "{} language documentation page(s) name a language no `language!` declaration \
         defines:\n  {}\n\nRename the page to follow the language, or remove it if the \
         grammar is gone.",
        stranded.len(),
        stranded
            .iter()
            .map(|p| p.display().to_string())
            .collect::<Vec<_>>()
            .join("\n  "),
    );

    assert!(
        live >= 4,
        "only {live} live language page(s) were seen; this test is not reaching {} and \
         would pass over an empty set",
        docs_dir.display()
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Member 3+4 — the generated output directory and its Blockly siblings
// ══════════════════════════════════════════════════════════════════════════════

/// Every `target/generated/<x>/` names a language `<x>` that still exists, and every
/// `<x>-blocks.ts` / `<x>-categories.ts` inside it agrees with its own directory.
///
/// `macros/src/logic/writer.rs::lang_generated_dir` computes the directory from the
/// language name and NEVER removes an old one, so a rename leaves the previous name's
/// tree behind in full. That stale tree still compiles if anything `include!`s it, and it
/// is what a reader inspects when asking "what did the macro emit for this grammar?".
/// The Blockly emitters (`macros/src/gen/blockly/writer.rs`) key their FILE names on the
/// language name inside that directory, so a directory whose `.ts` files disagree with it
/// is the same defect one level down — and those `.ts` files are consumed by an entirely
/// separate front end, which strands without any Rust ever failing to compile.
///
/// # Vacuity, stated honestly
///
/// `target/generated/` exists only after a build. On a tree that has never compiled a
/// `language!` there is nothing to check and this test is vacuous BY CONSTRUCTION — no
/// artifact exists to be stranded. It says so rather than skipping silently, and the
/// assertion below fails if the directory exists but is empty, which would mean the walk
/// is broken rather than the tree clean.
#[test]
fn every_generated_language_directory_names_a_live_language() {
    let declared = declared_language_names();
    let generated = repo_root().join("target/generated");

    if !generated.exists() {
        eprintln!(
            "note: {} does not exist — no `language!` has been compiled in this tree, so \
             there is no generated artifact that could be stranded. This check is vacuous \
             by construction, not skipped.",
            generated.display()
        );
        return;
    }

    let mut stranded_dirs = Vec::new();
    let mut mismatched_blockly = Vec::new();
    let mut live = 0usize;

    for entry in
        fs::read_dir(&generated).unwrap_or_else(|e| panic!("read {}: {e}", generated.display()))
    {
        let path = entry.expect("dir entry").path();
        if !path.is_dir() {
            continue;
        }
        let Some(dir_name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !declared.contains(dir_name) {
            stranded_dirs.push(path.clone());
            continue;
        }
        live += 1;

        for inner in
            fs::read_dir(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
        {
            let inner = inner.expect("dir entry").path();
            let Some(file_name) = inner.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            for suffix in ["-blocks.ts", "-categories.ts"] {
                if let Some(stem) = file_name.strip_suffix(suffix) {
                    if stem != dir_name {
                        mismatched_blockly.push(inner.display().to_string());
                    }
                }
            }
        }
    }

    assert!(
        stranded_dirs.is_empty(),
        "{} generated output directory/ies name a language no `language!` declaration \
         defines. `macros/src/logic/writer.rs::lang_generated_dir` derives the directory \
         from the language name and never prunes an old one, so this tree is what a \
         rename left behind — stale emitted source that still reads as current:\n  \
         {}\n\nDelete the stale directory (it is pure build output and is regenerated on \
         the next compile).",
        stranded_dirs.len(),
        stranded_dirs
            .iter()
            .map(|p| p.display().to_string())
            .collect::<Vec<_>>()
            .join("\n  "),
    );

    assert!(
        mismatched_blockly.is_empty(),
        "{} Blockly artifact(s) are named for a different language than the directory \
         holding them. `macros/src/gen/blockly/writer.rs` keys the FILE name on the \
         language name, and the downstream editor front end loads them by that name, so a \
         mismatch strands a consumer that no Rust build can see:\n  {}",
        mismatched_blockly.len(),
        mismatched_blockly.join("\n  "),
    );

    assert!(
        live >= 12,
        "only {live} live generated directory/ies were seen under {}; the walk is not \
         reaching the tree and would pass over an empty set",
        generated.display()
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Member 5 — the `BUNDLED_LANGUAGES` string-keyed table
// ══════════════════════════════════════════════════════════════════════════════

/// `BUNDLED_LANGUAGES` is a hand-written mirror of two directory listings; this is the
/// `read_dir` completeness assertion its own comment asks for.
///
/// The table at `macros/src/gen/runtime/binder_congruence.rs` pairs a key with
/// `include_str!` of a definition file. A MOVE fails the `macros` build, since
/// `include_str!` stops resolving. An ADDITION does not: a definition never listed
/// compiles fine and is silently outside every guard the table feeds, so the table reports
/// success over a SHRINKING DOMAIN as the language set grows. That already happened once —
/// `json`, `monoid`, `pi` and `turing` sat outside it, including `pi`, whose generated
/// float handler carried an unsound replication arm (`!(νx.P) ⟶ νx.!P`) that a guard
/// reading this table structurally could not see.
///
/// # What the key actually is, measured
///
/// It is the definition FILE STEM, not the lower-cased language name. Those coincide for
/// most entries and DIVERGE for four: `fortran_model` / `FortranModel`, `guarded_rho` /
/// `GuardedRho`, `led_test` / `LedTest`, `reserved_model` / `ReservedModel`. Checking the
/// key against the declared NAME set would therefore report four false strandings and
/// train a reader to ignore this test. The key is checked against the file stem, which is
/// what it is, and the file's declared language is checked separately for liveness.
///
/// # Two directions, because each fails differently
///
/// - **key ⇒ declaration**: the file a key points at must still DECLARE a `language!`. If
///   it stops (grammar moved out, file repurposed), `include_str!` still resolves and the
///   table still compiles — this is the silent half.
/// - **declaration ⇒ key**: every definition file that declares a `language!` must have an
///   entry. This is the FAILS-OPEN direction the table's own comment describes, and it is
///   the one that had already recurred when this guard was written.
#[test]
fn bundled_languages_table_covers_every_definition_file() {
    let table_path = repo_root().join("macros/src/gen/runtime/binder_congruence.rs");
    let source = fs::read_to_string(&table_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", table_path.display()));

    let keys = bundled_language_keys(&source);
    assert!(
        keys.len() >= 30,
        "only {} `BUNDLED_LANGUAGES` key(s) were extracted from {}; the extraction is \
         broken and both comparisons below would be meaningless",
        keys.len(),
        table_path.display()
    );

    let declaring = definition_files_that_declare_a_language();
    assert!(
        declaring.len() >= 30,
        "only {} definition file(s) declaring a `language!` were found; the directory walk \
         is broken and the completeness check below would pass over nothing",
        declaring.len()
    );

    let declaring_stems: BTreeSet<String> = declaring.keys().cloned().collect();

    // ── key ⇒ declaration ─────────────────────────────────────────────────────────
    let dead_keys: Vec<&String> = keys.difference(&declaring_stems).collect();
    assert!(
        dead_keys.is_empty(),
        "`BUNDLED_LANGUAGES` in {} carries {} key(s) whose definition file no longer \
         declares a `language!`: {:?}\n\n`include_str!` still resolves, so the table still \
         compiles and the guards it feeds still report success — over a grammar that is no \
         longer there.",
        table_path.display(),
        dead_keys.len(),
        dead_keys,
    );

    // ── declaration ⇒ key (the FAILS-OPEN direction) ──────────────────────────────
    let missing: Vec<String> = declaring_stems
        .difference(&keys)
        .map(|stem| {
            let path = &declaring[stem];
            format!(
                "{stem}  (declares `{}`, at {})",
                declaring_language_name(path),
                path.display()
            )
        })
        .collect();
    assert!(
        missing.is_empty(),
        "{} definition file(s) declare a `language!` and have no `BUNDLED_LANGUAGES` entry \
         in {}:\n  {}\n\nThis is the FAILS-OPEN direction the table's own comment predicts: \
         an unlisted definition is outside every guard that reads this table — including \
         the float-handler soundness guards — and nothing about the build says so. Add \
         `(\"<stem>\", include_str!(\"../../../../languages/…/<stem>.rs\"))` for each.",
        missing.len(),
        table_path.display(),
        missing.join("\n  "),
    );
}

/// Extract the string keys of `BUNDLED_LANGUAGES` by reading the table's entries.
///
/// The table is a `const … &[(&str, &str)]` whose entries are `("stem", include_str!(…))`.
/// Reading it textually, rather than parsing the whole file with `syn`, keeps this guard
/// independent of the surrounding module compiling — which matters because the point of
/// the guard is to catch a state in which that module is nonetheless perfectly valid Rust.
fn bundled_language_keys(source: &str) -> BTreeSet<String> {
    let mut keys = BTreeSet::new();
    let Some(start) = source.find("const BUNDLED_LANGUAGES") else {
        panic!(
            "`const BUNDLED_LANGUAGES` was not found; this guard's extraction is stale and \
             would otherwise report an empty table as a clean one"
        );
    };
    // Anchor each key on the `include_str!` that follows it, so prose in the surrounding
    // doc comment (which quotes example entries) cannot be mistaken for a real one.
    let mut rest = &source[start..];
    while let Some(idx) = rest.find("include_str!(") {
        let before = &rest[..idx];
        if let Some(quote_end) = before.rfind("\",") {
            if let Some(quote_start) = before[..quote_end].rfind('"') {
                let key = &before[quote_start + 1..quote_end];
                if !key.is_empty() && key.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                    keys.insert(key.to_string());
                }
            }
        }
        rest = &rest[idx + "include_str!(".len()..];
    }
    keys
}

/// The two directories a `BUNDLED_LANGUAGES` entry may `include_str!` from, mapped from
/// file stem to path, restricted to files that actually declare a `language!`.
///
/// Library-hosted definitions live in `languages/src/`; test-hosted ones in
/// `languages/tests/definitions/`. Support modules in either directory (`lib.rs`,
/// `bench_common.rs`, the composition module) declare no grammar and are excluded by the
/// declaration test rather than by a hand-written skip list.
fn definition_files_that_declare_a_language() -> std::collections::BTreeMap<String, PathBuf> {
    let root = repo_root();
    let mut out = std::collections::BTreeMap::new();
    for dir in [root.join("languages/src"), root.join("languages/tests/definitions")] {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.extension().and_then(|e| e.to_str()) != Some("rs") {
                continue;
            }
            let Ok(source) = fs::read_to_string(&path) else {
                continue;
            };
            if !source.contains("language!") {
                continue;
            }
            let parsed = match syn::parse_file(&source) {
                Ok(parsed) => parsed,
                Err(e) => panic!("parse {}: {e}", path.display()),
            };
            let mut names = BTreeSet::new();
            collect_language_names(&parsed.items, &mut names);
            if names.is_empty() {
                continue;
            }
            let stem = path
                .file_stem()
                .and_then(|s| s.to_str())
                .expect("a `.rs` path has a stem")
                .to_string();
            out.insert(stem, path);
        }
    }
    out
}

fn declaring_language_name(path: &Path) -> String {
    let source =
        fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let parsed =
        syn::parse_file(&source).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    let mut names = BTreeSet::new();
    collect_language_names(&parsed.items, &mut names);
    names.into_iter().collect::<Vec<_>>().join(", ")
}
