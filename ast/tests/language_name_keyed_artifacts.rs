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
//! | the binder-congruence bundled SUBJECT       | `macros/src/gen/runtime/binder_congruence.rs`          | ⚠ SILENT → now DERIVED |
//!
//! The last row is the one that changed shape. It was a hand-written `const
//! BUNDLED_LANGUAGES` of `(stem, include_str!(…))` pairs, and it failed OPEN three times
//! in a row: a definition that was simply never listed compiled fine and sat outside every
//! guard the table fed. Member 5 below therefore no longer checks that a list is complete
//! — it checks that there is NO LIST, that the subject is derived from the same
//! manifest-declared roots this file walks, and that the one class the derivation cannot
//! reconstruct is exempted by an exactly-asserted table rather than by omission.
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

/// Every `.rs` file under the manifest-declared language roots.
///
/// ★ The walk itself lives in [`mettail_ast::language_scan`] — ONE walk, read by all four
/// audits that need it. It used to be written out here, and identically in
/// `ast/tests/dovetail_language_inventory.rs` and `dovetail/tests/language_inventory.rs`,
/// and a FOURTH time (narrowly, and wrongly) 500 lines below in this very file. A walk
/// written out `n` times is a walk that can be widened `n − 1` times, which is exactly what
/// happened: `c58d3845` widened three of the four.
fn language_files() -> Vec<PathBuf> {
    mettail_ast::language_scan::language_files(&repo_root()).unwrap_or_else(|err| {
        panic!(
            "cannot determine the language definition roots: {err}\n\nThis guard decides \
             which language names are LIVE by scanning exactly those roots, so it must NOT \
             continue with a guess: an empty or narrowed root list would make every \
             name-keyed artifact look stranded, or (worse, after a later edit) make the \
             guard pass by comparing two empty sets."
        )
    })
}

/// Every item-level `language!` body in `items`, in source order, INCLUDING the bodies
/// inside inline `mod { … }` blocks.
///
/// The inline-`mod` recursion is load-bearing and the non-inline case is equally so:
/// `languages/tests/x2_lookahead_bracket_probe.rs` declares THREE languages, one in each
/// of three inline `pub mod`s, and `languages/tests/doc_comment_metadata.rs` reaches its
/// grammar through `#[path = "definitions/optsmoke.rs"] mod optsmoke;` — a NON-inline
/// `mod`, whose `ItemMod::content` is `None`. The first file declares three languages
/// here; the second correctly declares none, because the declaration belongs to the file
/// that spells it and counting it twice would put one grammar in the corpus under two
/// paths.
fn collect_language_defs(items: &[Item], out: &mut Vec<LanguageDef>) {
    for item in items {
        match item {
            Item::Macro(item_macro) => collect_language_def(item_macro, out),
            Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    collect_language_defs(nested, out);
                }
            },
            _ => {},
        }
    }
}

fn collect_language_def(item_macro: &ItemMacro, out: &mut Vec<LanguageDef>) {
    if item_macro.mac.path.is_ident("language") {
        let def: LanguageDef = syn::parse2(item_macro.mac.tokens.clone())
            .unwrap_or_else(|e| panic!("parse language! body: {e}"));
        out.push(def);
    }
}

fn collect_language_names(items: &[Item], out: &mut BTreeSet<String>) {
    let mut defs = Vec::new();
    collect_language_defs(items, &mut defs);
    out.extend(
        defs.into_iter()
            .map(|def| def.name.to_string().to_lowercase()),
    );
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
        // A file that declares a `language!` necessarily spells it followed by a
        // delimiter, so this gate cannot hide a declaration; it only spares `syn` the
        // generated test hosts and simulator binaries that the package-wide root also
        // walks. The gate is the shared over-approximation, not a shared DECISION — the
        // decision below is this audit's own, structural one.
        if !mettail_ast::language_scan::mentions_language_invocation(&source) {
            continue;
        }
        let parsed =
            syn::parse_file(&source).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
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

    for entry in
        fs::read_dir(&corpus_dir).unwrap_or_else(|e| panic!("read {}: {e}", corpus_dir.display()))
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

        for inner in fs::read_dir(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
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
// Member 5 — the binder-congruence bundled SUBJECT
// ══════════════════════════════════════════════════════════════════════════════

/// One `language!` body, keyed the way a corpus-wide subject has to be keyed.
///
/// # Why `(path, name)` and not a file stem
///
/// The subject this member watches used to be keyed on the definition FILE STEM, and the
/// map that produced it did `out.insert(stem, path)`. A file declaring TWO languages
/// therefore yielded ONE entry — and the completeness check compared cardinalities that
/// had both been collapsed the same way, so it passed. That was latent only while the
/// scan could not reach a multi-declaration file;
/// `languages/tests/x2_lookahead_bracket_probe.rs` declares `X2Base`, `X2Look` and
/// `X2Teeth` in three inline `pub mod`s, and the moment the walk widened to reach it the
/// stem key would have silently addressed one of the three.
///
/// A `(repository-relative path, declared name)` pair is injective over the corpus by
/// construction: two bodies in one file differ in `name`, and two bodies with one name in
/// different files differ in `path` (and are separately rejected as duplicates by
/// `ast/tests/dovetail_language_inventory.rs`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct DeclaredBody {
    /// Repository-relative, `/`-separated — e.g. `languages/src/ambient.rs`. Absolute
    /// paths embed the checkout location and could not be written into an exemption table.
    path: String,
    /// The declared `name:`, verbatim (`Ambient`, `X2Base`), NOT lower-cased and NOT the
    /// file stem. The two diverge for `fortran_model` / `FortranModel`, `guarded_rho` /
    /// `GuardedRho`, `led_test` / `LedTest`, `reserved_model` / `ReservedModel`, and for
    /// every body in `x2_lookahead_bracket_probe.rs`.
    name: String,
    /// Whether the body declares `extends` / `includes` / `mixins` — i.e. whether it is a
    /// COMPOSED language, the one class that cannot be reconstructed outside the macro.
    composed: bool,
}

impl DeclaredBody {
    fn key(&self) -> (String, String) {
        (self.path.clone(), self.name.clone())
    }
}

/// Every `language!` body under the manifest-declared roots, keyed by `(path, name)`.
///
/// This is the WIDE scan — the same [`language_files`] walk every other member of this
/// suite uses. It replaces a second, narrower walk that lived 500 lines below the correct
/// one in this same file; see [`historic_narrow_scan`] for what that one could see, and
/// [`the_scan_is_wider_than_the_two_directory_listing_it_replaced`] for the standing proof
/// that the widening is real.
fn declared_bodies() -> Vec<DeclaredBody> {
    let root = repo_root();
    let mut bodies = Vec::new();
    for path in language_files() {
        let source =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        if !mettail_ast::language_scan::mentions_language_invocation(&source) {
            continue;
        }
        let parsed =
            syn::parse_file(&source).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
        let mut defs = Vec::new();
        collect_language_defs(&parsed.items, &mut defs);
        for def in defs {
            bodies.push(DeclaredBody {
                path: mettail_ast::language_scan::repo_relative(&root, &path),
                name: def.name.to_string(),
                composed: !def.extends_names.is_empty()
                    || !def.include_names.is_empty()
                    || !def.mixin_names.is_empty(),
            });
        }
    }
    bodies.sort();
    bodies
}

/// The scan this file used to run, RETAINED as the control of a mutation experiment.
///
/// It reads exactly two hard-coded directories, exactly one level deep — a `read_dir`
/// entry for a SUBDIRECTORY has no `.rs` extension, so `languages/src/composition/` was
/// dropped before anything in it was read, and `languages/tests/*.rs` was never a root at
/// all. Nothing calls it except [`the_scan_is_wider_than_the_two_directory_listing_it_replaced`],
/// which is the point: a narrowing that is deleted leaves no evidence it was ever there,
/// and the next person to write "the two definition directories" reintroduces it.
fn historic_narrow_scan() -> BTreeSet<(String, String)> {
    let root = repo_root();
    let mut out = BTreeSet::new();
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
            let mut defs = Vec::new();
            collect_language_defs(&parsed.items, &mut defs);
            for def in defs {
                out.insert((
                    mettail_ast::language_scan::repo_relative(&root, &path),
                    def.name.to_string(),
                ));
            }
        }
    }
    out
}

/// The `macros` module that derives the bundled subject.
fn binder_congruence_source() -> (PathBuf, String) {
    let path = repo_root().join("macros/src/gen/runtime/binder_congruence.rs");
    let source =
        fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    (path, source)
}

/// The `(path, name)` rows of `macros`' `RECONSTRUCTION_EXEMPT`, read textually.
///
/// Textually, not by parsing the module, for the same reason the old key extractor was
/// textual: the whole point of this guard is to catch a state in which that module is
/// nonetheless perfectly valid Rust, so it must not depend on the module compiling. The
/// slice starts AT the `const` item, so the prose above it — which quotes the row shape —
/// cannot be mistaken for a row.
fn reconstruction_exempt_rows(source: &str) -> BTreeSet<(String, String)> {
    let Some(start) = source.find("const RECONSTRUCTION_EXEMPT") else {
        panic!(
            "`const RECONSTRUCTION_EXEMPT` was not found in \
             macros/src/gen/runtime/binder_congruence.rs. The bundled subject is DERIVED \
             from the corpus, and the exemption table is the only place a language may be \
             left out of it — an extraction that silently found nothing would report an \
             empty exemption set as agreement."
        );
    };
    let body = &source[start..];
    let end = body
        .find("];")
        .unwrap_or_else(|| panic!("`RECONSTRUCTION_EXEMPT` has no closing `];`"));
    let body = &body[..end];

    let mut rows = BTreeSet::new();
    let mut rest = body;
    while let Some(at) = rest.find("path: \"") {
        let after_path = &rest[at + "path: \"".len()..];
        let Some(path_end) = after_path.find('"') else {
            break;
        };
        let path = &after_path[..path_end];
        let after = &after_path[path_end + 1..];
        let Some(name_at) = after.find("name: \"") else {
            break;
        };
        let after_name = &after[name_at + "name: \"".len()..];
        let Some(name_end) = after_name.find('"') else {
            break;
        };
        rows.insert((path.to_string(), after_name[..name_end].to_string()));
        rest = &after_name[name_end + 1..];
    }
    rows
}

/// ★ The bundled subject of the binder-congruence guards is DERIVED, and the only
/// languages left out of it are the composed ones — exactly those, named.
///
/// # What this replaced, and why completing a list was never the repair
///
/// `macros/src/gen/runtime/binder_congruence.rs` used to carry `const BUNDLED_LANGUAGES`,
/// a hand-written `&[(stem, include_str!(…))]` mirror of two directory listings. Its own
/// header called the residual risk out: `include_str!` catches a MOVE (the path stops
/// resolving) and never an ADDITION, so a definition that was simply never listed compiled
/// fine and sat outside every guard the table fed. The table therefore reported success
/// over a SHRINKING DOMAIN as the language set grew, and it did so three times:
///
/// | occurrence | omitted | consequence |
/// |---|---|---|
/// | 1st (`359220f3`) | `json`, `monoid`, `pi`, `turing` | `pi`'s generated float handler carried an UNSOUND replication arm (`!(νx.P) ⟶ νx.!P`) that a guard reading this table structurally could not see |
/// | 2nd | `binder_law_demo`, `congruence_lane_demo`, `typed_drop_demo` | two of the three BEAR the float handler, so the "exactly Ambient and Pi" guard again answered over a domain that did not contain the whole question |
/// | 3rd (`53199ac4`) | `token_text_leaf_demo` | red at committed `HEAD` when this member was rewritten — the previous form of this very test was failing on it |
///
/// The lesson the second occurrence taught, in the table's own words, is that *"complete
/// the list" is not a repair — DERIVING the list is*. So this member no longer checks a
/// list for completeness. It checks that there is **no list**:
///
/// 1. `const BUNDLED_LANGUAGES` does not exist. A hand-written subject cannot fail open if
///    there is no hand-written subject.
/// 2. The subject is derived through [`mettail_ast::language_scan`] — the same walk, from
///    the same manifest-declared roots, that every other member of this file uses. A
///    private walk in `macros` could narrow independently, which is the defect one level up.
/// 3. The ONE class the derivation provably cannot reconstruct is exempted by a typed
///    table, and that table is checked for EQUALITY against the composed languages this
///    file finds structurally. Equality, not containment: a row that stops being justified
///    must fail here, and a new composed language must be classified deliberately rather
///    than inherit an exemption.
///
/// Direction 1 of the old test (a key whose file no longer declares a `language!`) is
/// SUBSUMED rather than dropped: a derived subject cannot name a file that stopped
/// declaring, because it only ever names files it has just parsed a declaration out of.
#[test]
fn the_bundled_subject_is_derived_and_exempts_exactly_the_composed_languages() {
    let (table_path, source) = binder_congruence_source();

    // An ITEM, not a mention: the module's prose necessarily quotes the name of the thing
    // it replaced, and a substring search would make that documentation self-defeating.
    // A `const` item sits at item position, so its line begins with `const`; every
    // quotation of it lives inside a `///` or `//!` line.
    let table_is_back = source
        .lines()
        .any(|line| line.trim_start().starts_with("const BUNDLED_LANGUAGES"));
    assert!(
        !table_is_back,
        "`const BUNDLED_LANGUAGES` is back in {}. It was a hand-written mirror of two \
         directory listings and it failed OPEN three times — `json`/`monoid`/`pi`/`turing`, \
         then `binder_law_demo`/`congruence_lane_demo`/`typed_drop_demo`, then \
         `token_text_leaf_demo` — each time reporting success over a domain that had \
         quietly stopped containing the whole question. Derive the subject from \
         `mettail_ast::language_scan::language_files` instead; a list cannot enumerate a \
         directory, and the guards that read it are only as total as their subject.",
        table_path.display()
    );

    assert!(
        source.contains("language_scan::language_files"),
        "{} no longer derives its bundled subject from \
         `mettail_ast::language_scan::language_files`. That function is the ONE walk of the \
         manifest-declared roots; a private walk here could narrow on its own, which is \
         precisely how the scan this test used to call stayed two directories wide while \
         its three siblings were widened in `c58d3845`.",
        table_path.display()
    );

    // ── the exemption set, asserted EXACTLY ───────────────────────────────────────
    let bodies = declared_bodies();
    assert!(
        bodies.len() >= 50,
        "the structural scan found only {} `language!` bodie(s); it is not reaching the \
         source tree and the equality below would be comparing two nearly-empty sets",
        bodies.len()
    );

    let composed: BTreeSet<(String, String)> = bodies
        .iter()
        .filter(|body| body.composed)
        .map(DeclaredBody::key)
        .collect();
    let exempt = reconstruction_exempt_rows(&source);

    assert_eq!(
        exempt,
        composed,
        "the `RECONSTRUCTION_EXEMPT` table in {} and the composed languages this file finds \
         structurally have diverged.\n  exempt but NOT composed: {:?}\n  composed but NOT \
         exempt: {:?}\n\nA composed language declares `extends`/`includes`/`mixins`, which \
         `ast/src/auto_inject.rs` resolves through the MACRO-TIME registry; that registry \
         is empty at reconstruction time, so the composition FAILS and the definition \
         cannot be rebuilt outside the macro (`ast/src/auto_inject.rs:122-124` owns the \
         fix, and calls it a separate task). That is the ONLY sanctioned reason to leave a \
         declared language out of the bundled subject. If a row is exempt without being \
         composed, the exemption has outlived its argument; if a language is composed \
         without being exempt, the subject derivation is about to fail on it.",
        table_path.display(),
        exempt.difference(&composed).collect::<Vec<_>>(),
        composed.difference(&exempt).collect::<Vec<_>>(),
    );

    assert!(
        !composed.is_empty(),
        "no composed language was found at all, so the equality above just compared two \
         empty sets. `languages/src/composition/` holds `ExtMath`, `ImportedMath` and \
         `MixedMath`; if they are gone, delete the exemption vocabulary deliberately rather \
         than letting this check go quiet."
    );
}

/// ★ THE NARROWING, kept as a permanent control.
///
/// # The experiment
///
/// * **control** — [`historic_narrow_scan`], the two hard-coded directories read one level
///   deep, exactly as this file used to read them;
/// * **mutation** — [`declared_bodies`], the recursive walk of the manifest-declared roots;
/// * **effect** — the mutation must see STRICTLY MORE. The difference is enumerated in the
///   failure message, so a regression says which declarations went back out of reach.
///
/// # Why the delta is asserted NON-EMPTY and never as an exact list
///
/// `languages/tests/inventory_additive_inertness_canary.rs` is the standing witness that
/// adding a language whose requirements are already covered must be INERT — no hand edit
/// anywhere else. An exact delta here would break that: every new probe under
/// `languages/tests/` would turn this test red for a purely clerical reason, and the
/// remedy would be to paste a path into a list, which is exactly the habit the derived
/// subject exists to end. The EXACT assertion belongs where drift must be argued — the
/// exemption set, above — and this one asserts only that the mutation still applies.
///
/// # The second defect this pins
///
/// The narrow scan was also keyed by FILE STEM. The assertion below that stems are not
/// injective over the corpus is the standing witness that a stem cannot address this
/// subject: `languages/tests/x2_lookahead_bracket_probe.rs` alone holds three bodies.
#[test]
fn the_scan_is_wider_than_the_two_directory_listing_it_replaced() {
    let wide: BTreeSet<(String, String)> =
        declared_bodies().iter().map(DeclaredBody::key).collect();
    let narrow = historic_narrow_scan();

    assert!(
        !narrow.is_empty(),
        "the historic narrow scan found nothing, so the comparison below is not a \
         narrowing experiment — it is a broken control"
    );
    assert!(
        narrow.is_subset(&wide),
        "the recursive walk does not contain the two-directory listing it replaced, which \
         means it is not a widening but a DIFFERENT scan: {:?}",
        narrow.difference(&wide).collect::<Vec<_>>()
    );

    let gained: Vec<&(String, String)> = wide.difference(&narrow).collect();
    assert!(
        !gained.is_empty(),
        "the recursive, manifest-rooted walk sees exactly what two hard-coded directories \
         read one level deep saw, so the narrowing this test exists to prevent has been \
         reintroduced. Declarations in `languages/src/composition/` (one subdirectory down) \
         and in top-level `languages/tests/*.rs` (never a root at all) are what the narrow \
         scan could not reach."
    );
    eprintln!(
        "note: the recursive walk reaches {} declaration(s) the historic two-directory scan \
         could not:\n  {}",
        gained.len(),
        gained
            .iter()
            .map(|(path, name)| format!("{path} :: {name}"))
            .collect::<Vec<_>>()
            .join("\n  ")
    );

    // The stem key, refuted. Two bodies in one file collapse to one stem, which is how a
    // map keyed on stems could report a complete corpus while addressing part of it.
    let bodies = declared_bodies();
    let stems: BTreeSet<&str> = bodies
        .iter()
        .map(|body| {
            body.path
                .rsplit('/')
                .next()
                .and_then(|file| file.strip_suffix(".rs"))
                .expect("a `.rs` path has a stem")
        })
        .collect();
    assert!(
        stems.len() < bodies.len(),
        "every declaring file holds exactly one `language!` body, so a FILE STEM would be \
         an adequate key. It was not when this was written — \
         `languages/tests/x2_lookahead_bracket_probe.rs` held three — and the subject is \
         keyed on `(path, name)` because of it. If this is now genuinely true, say so \
         deliberately rather than letting the weaker key back in."
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// The totality invariant — ported from `ast/tests/dovetail_language_inventory.rs`
// ══════════════════════════════════════════════════════════════════════════════

/// Every file in the repository that DECLARES a `language!`, wherever it lives.
///
/// Membership is decided by PARSING: a file is a declaration site iff `syn` finds an
/// item-level `language!` macro in it. That is exact where a text search is not — the
/// macro is named in documentation across a dozen crates and emitted inside `quote!`
/// templates in `macros/`, none of which is a definition, and
/// `dovetail/tests/language_inventory.rs` carries two `r##"…"##` grammar FIXTURES that are
/// string literals rather than items.
///
/// A file that mentions `language!` but does not parse as Rust is reported rather than
/// skipped: silence there would be a hole of exactly the shape this sweep closes.
fn repository_language_declarations() -> BTreeSet<PathBuf> {
    let mut declaring = BTreeSet::new();
    let mut unparsable = Vec::new();

    for path in mettail_ast::language_scan::repository_rust_files(&repo_root()) {
        let source = fs::read_to_string(&path).unwrap_or_default();
        if !mettail_ast::language_scan::mentions_language_invocation(&source) {
            continue;
        }
        match syn::parse_file(&source) {
            Ok(file) => {
                let mut defs = Vec::new();
                collect_language_defs(&file.items, &mut defs);
                if !defs.is_empty() {
                    declaring.insert(path);
                }
            },
            Err(_) => {
                if source
                    .lines()
                    .any(|line| line.trim_start().starts_with("language!"))
                {
                    unparsable.push(path.display().to_string());
                }
            },
        }
    }

    assert!(
        unparsable.is_empty(),
        "file(s) look like they declare a `language!` but do not parse as Rust, so this \
         sweep cannot tell whether they are inside the scanned roots: {unparsable:#?}"
    );
    declaring
}

/// ★ No `language!` in this repository lies outside the files this suite scans.
///
/// # Why this guard is the durable half of the fix, and the widening only the visible half
///
/// Three files in this repository walk directories looking for `language!` declarations.
/// Two of them — `ast/tests/dovetail_language_inventory.rs:576` and
/// `dovetail/tests/language_inventory.rs:580` — have carried a guard of this exact name
/// for some time. This file did not, and that is not a coincidence: when `c58d3845`
/// widened the roots (*"a `language!` in a top-level `languages/tests/*.rs` was audited by
/// nobody"*), it widened both files that had a totality guard, because in both of them the
/// guard is what went red. The scan in THIS file had nothing that could go red, so it
/// stayed two directories wide through the very commit that fixed its siblings.
///
/// Widening a scan fixes today's corpus. A totality guard fixes the CLASS: from here on, a
/// declaration written anywhere the roots do not reach fails by name, in this suite, on
/// the next run.
///
/// When it fails there are exactly two honest resolutions, and neither is to delete the
/// check: move the definition under a scanned root, or widen
/// `[package.metadata.mettail] language_roots`. Both leave the language covered.
#[test]
fn language_declarations_cannot_hide_outside_the_scanned_roots() {
    let audited: BTreeSet<PathBuf> = language_files().into_iter().collect();
    let declaring = repository_language_declarations();

    let escaped = declaring
        .difference(&audited)
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>();
    assert!(
        escaped.is_empty(),
        "{} file(s) declare a `language!` that this suite never scans, so every name-keyed \
         artifact belonging to them looks stranded and the bundled binder-congruence \
         subject does not contain them:\n  {}\n\nMove the definition under a scanned root, \
         or widen `[package.metadata.mettail] language_roots`.",
        escaped.len(),
        escaped.join("\n  "),
    );

    assert!(
        declaring.len() >= 40,
        "the repository-wide sweep found only {} declaring file(s); it is not reaching the \
         source tree and the difference above would be empty for the wrong reason",
        declaring.len()
    );

    // The two cases the narrow scan in this file could not reach, named so that they stay
    // covered even if every other declaration outside the two historic directories moves.
    for canary in [
        "languages/tests/inventory_discovery_canary.rs",
        "languages/src/composition/base_lang.rs",
    ] {
        let path = repo_root().join(canary);
        assert!(
            declaring.contains(&path) && audited.contains(&path),
            "`{canary}` must be both recognised as a declaration and scanned by this suite"
        );
    }
}
