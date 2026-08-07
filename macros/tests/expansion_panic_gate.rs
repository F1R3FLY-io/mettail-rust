//! **#141 — an expansion-reachable refusal must be a TOKEN, not a mute abort.**
//!
//! # The defect this gate exists to prevent recurring
//!
//! This workspace compiles `dev` with the **cranelift** backend (root `Cargo.toml`,
//! `[profile.dev] codegen-backend = "cranelift"`). Inside the `language!` proc macro a
//! bare `panic!` **does not cross the `proc_macro` bridge**: `rustc` aborts with
//! `fatal runtime error: Rust cannot catch foreign exceptions` and prints **nothing** —
//! no span, no message, no rule name. A refusal written as a `panic!` on an
//! expansion-reachable path is therefore a refusal that cannot be read.
//!
//! `compile_error!` is immune, because it is a *token*: rustc renders it at the call
//! site and needs no unwinding at all. Task #141 converted the reachable refusals to
//! tokens or to `Result`s that reach the boundary. This file is the standing proof that
//! the conversion is not quietly undone.
//!
//! # ⚠ FEASIBILITY VERDICT — stated, not relitigated
//!
//! A whole-class ban is **not** feasible, and the reason is structural rather than
//! effortful: *"expansion-reachable" is a call-graph property, not a syntactic one.* A
//! module-level reachability approximation over-approximates (it pulls
//! `wpda_walker.rs` in through a type mention in emitted code) and a name-matched
//! function-level graph under-approximates (trait dispatch). Neither is sound enough to
//! gate a build. And a `(path, count, reason)` allowlist over the ~586 candidate sites
//! in ~97 files would be the exact defect
//! [`dovetail/tests/panic_expectation_gate.rs`] warns about — *"an allowlist without a
//! per-entry reason is the same defect wearing a list"* — at a scale at which no reason
//! would be written honestly.
//!
//! So the gate is **three tiers**, each as strong as its subject allows and no stronger:
//!
//! | tier | subject | instrument | strength |
//! |---|---|---|---|
//! | 1 | `macros/src` + `ast/src` — the only crates where a `syn` **span** exists | a TYPED exception table, asserted as **set equality** in both directions | strongest: every site is classified, and the classification carries its own obligation |
//! | 2 | `prattail/src` — span-free by construction | a **monotone ratchet**: one integer per directory, asserted `==` | weakest: a number, argued below |
//! | 3 | the scanner itself | planted-refusal cells + a floor on the walk | keeps 1 and 2 from passing vacuously |
//!
//! # ⚠ Tier 2 IS a number, and this file's neighbour argues against numbers
//!
//! [`macros/tests/generated_output_locality.rs`] asserts a **set is empty** and says why
//! that shape was chosen: *"A set-emptiness assertion cannot decay into a threshold that
//! someone later bumps; there is no number to adjust."* Tier 2 is a threshold that
//! someone can bump. That is a real departure and it is argued here rather than smuggled:
//!
//! 1. **Set-emptiness is unavailable, because the set is not empty and cannot be made
//!    empty today.** `prattail` holds ~421 refusal sites. Converting them is not one
//!    change; §7 of the #141 design stages them, and Stage 5 converted the ones on the
//!    live path. An empty-set assertion over a non-empty set is not a stricter gate, it
//!    is a *red* gate, which is the same as no gate.
//! 2. **The alternative to a number is a per-site reason, and that is the defect.** 421
//!    hand-written reasons would not be 421 arguments; they would be 421 shrugs. The
//!    honest instrument for a surface that cannot be individually argued *today* is one
//!    that refuses to let it GROW while saying plainly that it is not a per-site
//!    argument.
//! 3. **The number is monotone by construction and the failure message says so.** It may
//!    only be lowered, and lowering it requires deleting a site. Raising it is possible —
//!    that is the weakness — but it is a visible, reviewable edit to a file whose whole
//!    subject is that refusals must be readable.
//! 4. **The escape from the number is Tier 1, not a bigger number.** As `prattail` sites
//!    are converted the ratchet falls; when a directory reaches zero its row can be
//!    deleted. The number is a decreasing budget, not a licence.
//!
//! Where set-emptiness *is* available — Tier 1's `Converted`/`PreValidated` classes, and
//! Tier 3's planted controls — it is used.
//!
//! # The instrument: `syn::parse_file`, not a text scan
//!
//! ⚠ Three separate stripper bugs were hit building the #141 census by hand with regular
//! expressions: a `panic!` quoted inside a string was counted, a `panic!` inside a
//! `quote!{}` body (which is *emitted* code, not code that runs during expansion) was
//! counted, and a `#[cfg(test)]` module's contents were counted. This gate must not
//! inherit them, so it parses.
//!
//! `syn` is a first-class dependency of this crate (`Cargo.toml`, with
//! `features = ["full", "extra-traits", "visit-mut"]`), and `proc-macro2` carries
//! `span-locations`, so every site reports a real line number. Three discriminations
//! come for free from the AST:
//!
//! * **`quote!` bodies are invisible.** `syn::Macro` stores its body as an opaque
//!   `proc_macro2::TokenStream`; there is no `VisitMut` hook into it. A `panic!` written
//!   inside `quote!{}` is a token the macro *emits*, not a refusal that fires during
//!   expansion, and the AST cannot see it. ⚠ The same property is a **known bound in the
//!   other direction**: a refusal inside *any* macro body — a `matches!` arm, a local
//!   `macro_rules!` — is equally invisible. The gate therefore counts refusals in parsed
//!   expression, statement and item position, which is where all of them are written
//!   today, and [`the_scanner_does_not_see_inside_a_macro_body`] pins that limit
//!   explicitly so nobody mistakes it for coverage.
//! * **String literals and comments are invisible**, structurally: `syn` yields a
//!   `Macro` node for a call, never for text.
//! * **Test code is excluded by attribute**, not by filename: `#[cfg(test)]` and
//!   `#[test]` on a module or a function stop the walk at that node.
//!
//! # Why `visit_mut` for a read-only scan
//!
//! Only `visit-mut` is enabled on `syn` in this workspace; `visit` is not. Taking `&mut`
//! of a file this gate itself parsed and never writes back is the same pattern
//! `macros/src/gen/runtime/wpda_codegen/grammar_generality_prop.rs:527` already uses.
//! Enabling a second `syn` feature to get an immutable visitor would be a workspace-wide
//! dependency change made for a test's aesthetics.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use syn::visit_mut::VisitMut;

// ═══════════════════════════════════════════════════════════════════════════
// The refusal vocabulary
// ═══════════════════════════════════════════════════════════════════════════

/// The macros that abort with an authored message and no token.
///
/// These four are the ones the cranelift measurement condemns: each carries a message
/// its author wrote for a reader, and each delivers it by unwinding — which, inside this
/// workspace's proc macro, means it is never delivered.
///
/// ⚠ `assert!`/`debug_assert!` and `.expect(…)`/`.unwrap()` are deliberately **not**
/// here. They belong to a different repair: `assert!` families are far more numerous and
/// mostly encode invariants rather than user-facing refusals, and `.unwrap()` carries no
/// authored message at all, so there is nothing to convert per-site. Tier 2's ratchet
/// therefore measures the same four constructs as Tier 1, which is what makes the two
/// tiers commensurable — a site that moves from `prattail` to `macros` moves between two
/// rows of the same census, not between two different censuses.
const REFUSAL_MACROS: &[&str] = &["panic", "unreachable", "todo", "unimplemented"];

/// One refusal site, as the scan sees it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Site {
    /// Repository-relative path, `/`-separated.
    file: String,
    line: usize,
    /// The macro name without the `!`, e.g. `panic`.
    construct: String,
}

impl std::fmt::Display for Site {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}!", self.file, self.line, self.construct)
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// The scanner
// ═══════════════════════════════════════════════════════════════════════════

/// True when these attributes gate the item out of a non-test build.
///
/// Matches `#[test]`, `#[cfg(test)]`, and any `cfg` whose predicate mentions the `test`
/// ident at all — `cfg(all(test, feature = "x"))`, `cfg(any(test, doc))`. Erring toward
/// exclusion is the right direction here: a false *exclusion* loses a site the gate
/// would have counted (visible as a ratchet that is one too low, caught by Tier 1's
/// exact set equality), whereas a false *inclusion* puts test code into a production
/// census and makes the gate lie.
fn is_test_gated(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let path = attr.path();
        match path.is_ident("test") {
            true => true,
            false => match path.is_ident("cfg") {
                true => attr
                    .meta
                    .require_list()
                    .map(|list| {
                        list.tokens
                            .clone()
                            .into_iter()
                            .any(|tt| matches!(&tt, proc_macro2::TokenTree::Ident(i) if i == "test")
                                || matches!(&tt, proc_macro2::TokenTree::Group(g)
                                    if g.stream().into_iter().any(|inner|
                                        matches!(&inner, proc_macro2::TokenTree::Ident(i) if i == "test"))))
                    })
                    .unwrap_or(false),
                false => false,
            },
        }
    })
}

/// Collects refusal sites from one parsed file.
struct RefusalScan {
    file: String,
    sites: Vec<Site>,
}

impl VisitMut for RefusalScan {
    fn visit_item_mod_mut(&mut self, node: &mut syn::ItemMod) {
        match is_test_gated(&node.attrs) {
            true => {},
            false => syn::visit_mut::visit_item_mod_mut(self, node),
        }
    }

    fn visit_item_fn_mut(&mut self, node: &mut syn::ItemFn) {
        match is_test_gated(&node.attrs) {
            true => {},
            false => syn::visit_mut::visit_item_fn_mut(self, node),
        }
    }

    fn visit_impl_item_fn_mut(&mut self, node: &mut syn::ImplItemFn) {
        match is_test_gated(&node.attrs) {
            true => {},
            false => syn::visit_mut::visit_impl_item_fn_mut(self, node),
        }
    }

    fn visit_macro_mut(&mut self, node: &mut syn::Macro) {
        // `node.tokens` is an opaque `TokenStream` with no visitor hook, so a `quote!`
        // body is never descended into. That is the discrimination this instrument was
        // chosen for; see the module docs.
        if let Some(last) = node.path.segments.last() {
            let name = last.ident.to_string();
            if REFUSAL_MACROS.contains(&name.as_str()) {
                self.sites.push(Site {
                    file: self.file.clone(),
                    line: last.ident.span().start().line,
                    construct: name,
                });
            }
        }
        syn::visit_mut::visit_macro_mut(self, node);
    }
}

/// Scan one source buffer, attributing sites to `display_path`.
///
/// Returns `Err` when the buffer does not parse, so a scan that silently read nothing
/// cannot masquerade as a scan that found nothing.
fn scan_source(display_path: &str, source: &str) -> Result<Vec<Site>, syn::Error> {
    let mut file = syn::parse_file(source)?;
    let mut scan = RefusalScan {
        file: display_path.to_string(),
        sites: Vec::new(),
    };
    scan.visit_file_mut(&mut file);
    scan.sites.sort();
    Ok(scan.sites)
}

/// The workspace root — the directory holding the `[workspace]` `Cargo.toml`.
///
/// Derived by walking up from this crate's manifest directory, mirroring
/// `macros::logic::writer::lang_generated_dir` and
/// `languages/tests/operator_precedence_ladders.rs`, so the gate's idea of "the
/// workspace" is the same as the build's.
fn workspace_root() -> PathBuf {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        let manifest = dir.join("Cargo.toml");
        let declares_workspace = std::fs::read_to_string(&manifest)
            .map(|c| c.lines().any(|l| l.trim_start().starts_with("[workspace]")))
            .unwrap_or(false);
        match declares_workspace {
            true => return dir,
            false => {
                assert!(dir.pop(), "no [workspace] Cargo.toml above {}", env!("CARGO_MANIFEST_DIR"))
            },
        }
    }
}

/// Every `.rs` file under `root/relative`, repo-relative and `/`-separated, sorted.
fn rust_files_under(root: &Path, relative: &str) -> Vec<(String, PathBuf)> {
    let mut out = Vec::new();
    let mut stack = vec![root.join(relative)];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            match path.is_dir() {
                true => stack.push(path),
                false => {
                    if path.extension().and_then(|e| e.to_str()) != Some("rs") {
                        continue;
                    }
                    let rel = path
                        .strip_prefix(root)
                        .expect("walked path must sit under the workspace root")
                        .to_string_lossy()
                        .replace('\\', "/");
                    out.push((rel, path));
                },
            }
        }
    }
    out.sort();
    out
}

/// Resolve a `mod name;` declaration in `owner` to the file it names.
///
/// Rust looks for `<dir>/<name>.rs` then `<dir>/<name>/mod.rs`, where `<dir>` is the
/// owner's own module directory: the parent directory for `lib.rs`/`mod.rs`, and the
/// same-named subdirectory otherwise. A `#[path = "…"]` attribute overrides the search.
fn resolve_mod_file(
    root: &Path,
    owner_rel: &str,
    name: &str,
    path_attr: Option<&str>,
) -> Vec<String> {
    let owner = Path::new(owner_rel);
    let stem = owner.file_stem().and_then(|s| s.to_str()).unwrap_or("");
    let parent = owner.parent().unwrap_or(Path::new(""));
    let module_dir = match stem {
        "lib" | "main" | "mod" => parent.to_path_buf(),
        other => parent.join(other),
    };
    let candidates = match path_attr {
        Some(explicit) => vec![module_dir.join(explicit)],
        None => vec![module_dir.join(format!("{name}.rs")), module_dir.join(name).join("mod.rs")],
    };
    candidates
        .into_iter()
        .filter(|c| root.join(c).is_file())
        .map(|c| c.to_string_lossy().replace('\\', "/"))
        .collect()
}

/// The `mod` declarations in one file: `(is_test_gated, resolved_child_paths)`.
fn declared_modules(root: &Path, rel: &str, source: &str) -> Vec<(bool, Vec<String>)> {
    let Ok(parsed) = syn::parse_file(source) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for item in &parsed.items {
        let syn::Item::Mod(m) = item else { continue };
        // Only DECLARATIONS (`mod x;`) name another file; inline `mod x { … }` is
        // already handled by the visitor.
        if m.content.is_some() {
            continue;
        }
        let path_attr = m
            .attrs
            .iter()
            .find_map(|a| match a.path().is_ident("path") {
                true => match &a.meta {
                    syn::Meta::NameValue(nv) => match &nv.value {
                        syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. }) => {
                            Some(s.value())
                        },
                        _ => None,
                    },
                    _ => None,
                },
                false => None,
            });
        out.push((
            is_test_gated(&m.attrs),
            resolve_mod_file(root, rel, &m.ident.to_string(), path_attr.as_deref()),
        ));
    }
    out
}

/// Files that are TEST modules by virtue of how their parent declares them.
///
/// ⚠ This exists because the first run of the census counted four sites in
/// `prattail/src/decision_tree/tests.rs`. That file carries no `#[cfg(test)]` of its own —
/// the attribute is on `mod tests;` in `decision_tree/mod.rs`, one file away. A scanner
/// that looks only at the file in front of it therefore puts test code into a production
/// census, which is the third of the three stripper bugs the module docs name. The
/// exclusion is DERIVED from the `mod` graph, not from filenames: a test module called
/// something other than `tests` is caught, and a production module called `tests` is not
/// excluded.
///
/// Transitive: everything a test module itself declares is a test module too.
fn test_module_files(root: &Path, relative: &str) -> std::collections::BTreeSet<String> {
    let files = rust_files_under(root, relative);
    let mut sources: BTreeMap<String, String> = BTreeMap::new();
    for (rel, path) in &files {
        if let Ok(src) = std::fs::read_to_string(path) {
            sources.insert(rel.clone(), src);
        }
    }
    let mut excluded: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (rel, src) in &sources {
        for (gated, children) in declared_modules(root, rel, src) {
            if gated {
                excluded.extend(children);
            }
        }
    }
    // Transitive closure: a submodule of a test module is a test module.
    loop {
        let mut grew = false;
        let frontier: Vec<String> = excluded.iter().cloned().collect();
        for rel in frontier {
            let Some(src) = sources.get(&rel) else {
                continue;
            };
            for (_, children) in declared_modules(root, &rel, src) {
                for child in children {
                    grew |= excluded.insert(child);
                }
            }
        }
        if !grew {
            break;
        }
    }
    excluded
}

/// Scan a subtree, failing loudly on any file that does not parse.
///
/// Returns `(sites, files_scanned, files_excluded_as_test_modules)`.
fn scan_subtree(root: &Path, relative: &str) -> (Vec<Site>, usize, usize) {
    let excluded = test_module_files(root, relative);
    let mut sites = Vec::new();
    let mut files = 0usize;
    let mut skipped = 0usize;
    for (rel, path) in rust_files_under(root, relative) {
        if excluded.contains(&rel) {
            skipped += 1;
            continue;
        }
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
        files += 1;
        match scan_source(&rel, &source) {
            Ok(found) => sites.extend(found),
            Err(e) => panic!(
                "the gate could not parse {rel}: {e}. A scan that cannot read a file must \
                 not silently report zero sites for it."
            ),
        }
    }
    sites.sort();
    (sites, files, skipped)
}

// ═══════════════════════════════════════════════════════════════════════════
// TIER 1 — the typed exception table over `macros/src` + `ast/src`
// ═══════════════════════════════════════════════════════════════════════════

/// Why a refusal in `macros/src` or `ast/src` is allowed to remain a `panic!`.
///
/// Modelled on `languages/tests/literal_domain_agreement.rs:32-52`: **every row is TYPED,
/// so no row can be a shrug.** A variant is not a label — it carries an *obligation* that
/// [`every_declared_disposition_still_holds`] re-checks on every run. A row whose
/// obligation stops holding fails the gate even though its count is unchanged.
///
/// # Relation to the vocabulary #141 proposed
///
/// The design sketched four variants: `Converted`, `ProvenInert`, `InfallibleByType`,
/// `PreValidated`. Two of them are here under sharper names, and two are deliberately
/// **absent**:
///
/// * `ProvenInert` → [`Disposition::ConstructionInvariant`]. The sharpening matters: this
///   gate refuses to accept "no shipped grammar reaches it", which is a *measurement* that
///   the next grammar can overturn, and requires instead a statement about what the
///   producing code *can construct*. `ProvenInert` remains the right classification for
///   `prattail/src/automata/codegen.rs`'s eight `TokenKind::LexError` arms, and it is
///   asserted where it belongs — in that crate, by
///   `token_kind_lex_error_has_no_constructor_in_this_crate`, which checks the
///   zero-constructor claim against the source rather than trusting a comment.
/// * `PreValidated` → [`Disposition::LocallyFiltered`] and
///   [`Disposition::EarlierPassNormalised`], split because the two have different
///   obligations: one names a predicate a few lines up, the other names a whole pass.
/// * `Converted` is **not a variant**, because it cannot be one. This table's domain is
///   the set of *remaining* refusal macros; a site that now emits `compile_error!` is not
///   in the domain at all, so a `Converted` row could never be inhabited and would be
///   decoration rather than typing. (`literal_domain_agreement.rs` keeps its uninhabited
///   `NoSurface` variant because that one *became* uninhabited by being fixed and can
///   become inhabited again. This is not that case.) The converted sites are asserted by
///   the Stage-3 tests that accompany each conversion.
/// * `InfallibleByType` is likewise absent: its subject is `.expect(…)` on a `String`
///   write, which is not a refusal macro and not in this domain. It is argued once at
///   `prattail/src/automata/codegen.rs`'s `w!` and asserted by
///   `w_emits_the_same_bytes_as_write`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Disposition {
    /// A predicate in the **same function**, a few lines above, already narrowed the value
    /// so the refusing arm cannot be selected.
    ///
    /// Obligation: `filter` must appear within [`WITNESS_WINDOW`] lines *above* the
    /// refusal. If the filter is moved, renamed or deleted, the row stops holding.
    LocallyFiltered { filter: &'static str },

    /// An **earlier pass of the same expansion** normalises the shape away before this
    /// code runs.
    ///
    /// Obligation: `pass` must appear within [`WITNESS_WINDOW`] lines of the refusal —
    /// the site has to *say* which pass it is trusting, which is the difference between a
    /// justified refusal and an assumption.
    EarlierPassNormalised { pass: &'static str },

    /// The refused value cannot be built: the data structure's construction never
    /// produces it.
    ///
    /// Obligation: `invariant` must appear within [`WITNESS_WINDOW`] lines of the refusal.
    /// ⚠ This is the sharpened `ProvenInert`. It is still **an open defect, not a
    /// licence**: it says the value is unconstructible *today*, and the day the
    /// construction gains a case the refusal goes live and needs a real answer.
    ConstructionInvariant { invariant: &'static str },
}

/// How far from a refusal its witness token may sit and still be that refusal's witness.
///
/// Wide enough to cover the enclosing `match` and its leading comment; narrow enough that
/// an unrelated occurrence elsewhere in a 3,000-line file cannot satisfy the obligation.
const WITNESS_WINDOW: usize = 30;

/// One declared row: `count` refusals of `construct` in `file`, all with `disposition`.
///
/// ⚠ Keyed on `(file, construct)` and a COUNT, **never on a line number**. Nine other
/// agents edit this tree concurrently; a table keyed on lines would go red every time
/// somebody inserted a function above a site, and a gate that cries wolf gets its numbers
/// bumped rather than read.
struct Row {
    file: &'static str,
    construct: &'static str,
    count: usize,
    disposition: Disposition,
}

/// The complete, exact table. Every refusal macro remaining in `macros/src` + `ast/src`.
///
/// Asserted as **set equality in both directions**: a new site fails because it is
/// undeclared, and a *fixed* site fails because its row is now unmatched. It can neither
/// grow silently nor be quietly forgotten once repaired.
const TIER1_TABLE: &[Row] = &[
    Row {
        file: "macros/src/gen/capture.rs",
        construct: "unreachable",
        count: 1,
        // The `match param` two lines below a `find` whose predicate admits only
        // `TermParam::MultiAbstraction` and `TermParam::Abstraction`; the `_` arm is the
        // complement of a set the same function just selected.
        disposition: Disposition::LocallyFiltered { filter: "MultiAbstraction" },
    },
    Row {
        file: "macros/src/gen/runtime/wpda_codegen/factoring.rs",
        construct: "panic",
        count: 4,
        // S1-FACTORING F5-2. Two are the spine-coordinate walk refusing kind 1 ("the
        // spine never runs kind 1 because its marker never bumps"); two are a
        // `MemberCommit` shape refusing a discovery-kind drift. All four are statements
        // about what `SpineTree`/`MemberCommit` construction can yield.
        disposition: Disposition::ConstructionInvariant { invariant: "F5-2" },
    },
    Row {
        file: "macros/src/gen/syntax/display.rs",
        construct: "unreachable",
        count: 1,
        // `TermParam::Optional` is flattened by an earlier pass; the arm exists only
        // because the enum still has the variant.
        disposition: Disposition::EarlierPassNormalised { pass: "flattened" },
    },
];

/// The scanned domain of Tier 1, as `(file, construct) -> count`.
fn tier1_scanned(root: &Path) -> (BTreeMap<(String, String), usize>, Vec<Site>, usize) {
    let mut counts: BTreeMap<(String, String), usize> = BTreeMap::new();
    let mut all = Vec::new();
    let mut files = 0usize;
    for sub in ["macros/src", "ast/src"] {
        let (sites, scanned, _) = scan_subtree(root, sub);
        files += scanned;
        for site in sites {
            *counts
                .entry((site.file.clone(), site.construct.clone()))
                .or_default() += 1;
            all.push(site);
        }
    }
    all.sort();
    (counts, all, files)
}

/// ★ TIER 1 — every remaining refusal in `macros/src` + `ast/src` is classified, exactly.
///
/// Adding a `panic!` to either crate fails HERE until it is either converted to a
/// `compile_error!`/`Result` or given a typed row whose obligation holds.
#[test]
fn tier1_every_refusal_in_macros_and_ast_is_classified() {
    let root = workspace_root();
    let (scanned, sites, files) = tier1_scanned(&root);

    // Anti-vacuity: the walk must really have read both crates.
    assert!(
        files >= 100,
        "the Tier 1 walk read only {files} files across macros/src + ast/src — it is not \
         walking the crates it claims to walk"
    );

    let declared: BTreeMap<(String, String), usize> = TIER1_TABLE
        .iter()
        .map(|r| ((r.file.to_string(), r.construct.to_string()), r.count))
        .collect();
    assert_eq!(
        TIER1_TABLE.len(),
        declared.len(),
        "two rows of TIER1_TABLE share a (file, construct) key; merge them and sum the counts"
    );

    let undeclared: Vec<String> = scanned
        .iter()
        .filter(|(k, _)| !declared.contains_key(*k))
        .map(|((f, c), n)| format!("  {f}: {n} × {c}!"))
        .collect();
    let stale: Vec<String> = declared
        .iter()
        .filter(|(k, _)| !scanned.contains_key(*k))
        .map(|((f, c), n)| format!("  {f}: {n} × {c}! (declared, not found)"))
        .collect();
    let miscounted: Vec<String> = scanned
        .iter()
        .filter_map(|(k, found)| match declared.get(k) {
            Some(want) if want != found => {
                Some(format!("  {}: {found} × {}! declared {want}", k.0, k.1))
            },
            _ => None,
        })
        .collect();

    assert!(
        undeclared.is_empty() && stale.is_empty() && miscounted.is_empty(),
        "the refusal census for `macros/src` + `ast/src` no longer matches TIER1_TABLE.\n\
         \n\
         NEW, undeclared — a refusal reached one of the two crates where a `syn` span IS \
         available, so it should almost certainly become a spanned `compile_error!` \
         instead of a table row:\n{}\n\
         \n\
         DECLARED but not found — if the site was fixed, DELETE its row (that is how a \
         row is supposed to leave). If it merely moved to another file, move the row:\n{}\n\
         \n\
         COUNT drift:\n{}\n\
         \n\
         Full scanned census ({} sites):\n{}",
        match undeclared.is_empty() {
            true => "  (none)".to_string(),
            false => undeclared.join("\n"),
        },
        match stale.is_empty() {
            true => "  (none)".to_string(),
            false => stale.join("\n"),
        },
        match miscounted.is_empty() {
            true => "  (none)".to_string(),
            false => miscounted.join("\n"),
        },
        sites.len(),
        sites
            .iter()
            .map(|s| format!("  {s}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// ★ TIER 1's teeth — every row's OBLIGATION is re-checked, not just its count.
///
/// This is what stops a row from being a shrug. A `LocallyFiltered` row that names a
/// filter somebody has since deleted fails here while its count is still correct.
#[test]
fn every_declared_disposition_still_holds() {
    let root = workspace_root();
    let (_, sites, _) = tier1_scanned(&root);
    let mut failures: Vec<String> = Vec::new();

    for row in TIER1_TABLE {
        let source = std::fs::read_to_string(root.join(row.file)).unwrap_or_else(|e| {
            panic!("TIER1_TABLE names {} but it cannot be read: {e}", row.file)
        });
        let lines: Vec<&str> = source.lines().collect();
        let row_sites: Vec<&Site> = sites
            .iter()
            .filter(|s| s.file == row.file && s.construct == row.construct)
            .collect();

        match row.disposition {
            Disposition::LocallyFiltered { filter } => {
                for site in &row_sites {
                    let lo = site.line.saturating_sub(WITNESS_WINDOW).saturating_sub(1);
                    let hi = site.line.min(lines.len());
                    let window = lines[lo..hi].join("\n");
                    if !window.contains(filter) {
                        failures.push(format!(
                            "{site}: LocallyFiltered names the filter `{filter}`, but it does \
                             not appear in the {WITNESS_WINDOW} lines above the refusal. \
                             Either the filter was removed — in which case the refusal is \
                             now REACHABLE — or the row is stale."
                        ));
                    }
                }
            },
            Disposition::EarlierPassNormalised { pass }
            | Disposition::ConstructionInvariant { invariant: pass } => {
                for site in &row_sites {
                    let lo = site.line.saturating_sub(WITNESS_WINDOW).saturating_sub(1);
                    let hi = (site.line + WITNESS_WINDOW).min(lines.len());
                    let window = lines[lo..hi].join("\n");
                    if !window.contains(pass) {
                        failures.push(format!(
                            "{site}: the row names `{pass}` as the reason this refusal cannot \
                             fire, but the refusal does not mention it within \
                             {WITNESS_WINDOW} lines. A refusal that does not say what it is \
                             trusting is an assumption, not a justification."
                        ));
                    }
                }
            },
        }
    }

    assert!(
        failures.is_empty(),
        "declared dispositions no longer hold:\n{}",
        failures.join("\n")
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// TIER 2 — the monotone ratchet over `prattail/src`
// ═══════════════════════════════════════════════════════════════════════════

/// One integer per directory of `prattail/src` that still holds refusal macros.
///
/// ⚠ See the module docs for why this tier is a NUMBER at all, and why that is a departure
/// from `generated_output_locality.rs`'s "there is no number to adjust". The short form:
/// set-emptiness over a non-empty set is a red gate, and 45 hand-written reasons would be
/// 45 shrugs.
///
/// **Only non-zero directories appear.** That is what makes the key set derived rather
/// than hand-maintained: a refusal added to a directory currently at zero creates a key
/// that is not in this table, and the gate fails because the key is undeclared — not
/// because somebody remembered to add a zero row. Symmetrically, a directory that reaches
/// zero must have its row DELETED, because a declared key with no scanned sites also
/// fails.
///
/// `<root>` is the aggregate for `.rs` files directly under `prattail/src`. It is
/// deliberately one bucket rather than one row per file: those files are the parser
/// RUNTIME (`wpda_walker.rs`, `sppf_realize.rs`, `sppf.rs`, …), which the #141 design
/// classifies as out of scope because it runs at *parse* time under the LLVM-compiled
/// `languages` profile, not during expansion. Bucketing them keeps them counted — a new
/// refusal there still has to be noticed — without pretending they are expansion sites.
const TIER2_RATCHET: &[(&str, usize)] =
    &[("<root>", 28), ("automata", 6), ("pipeline", 1), ("weighted_mso", 10)];

/// Bucket a `prattail/src` site by its first path component below `src/`.
fn prattail_bucket(file: &str) -> String {
    let rest = file.trim_start_matches("prattail/src/");
    match rest.split_once('/') {
        Some((dir, _)) => dir.to_string(),
        None => "<root>".to_string(),
    }
}

/// ★ TIER 2 — the `prattail` refusal count may FALL but never rise.
#[test]
fn tier2_prattail_refusal_count_does_not_rise() {
    let root = workspace_root();
    let (sites, files, _) = scan_subtree(&root, "prattail/src");

    // Anti-vacuity: the walk must really have read the crate.
    assert!(
        files >= 140,
        "the Tier 2 walk read only {files} files under prattail/src — it is not walking the \
         crate it claims to walk"
    );
    assert!(
        !sites.is_empty(),
        "the Tier 2 walk found ZERO refusals in prattail/src. That is not plausible for a \
         45-site surface; the scanner has stopped seeing the construct it counts, and every \
         row below would pass vacuously."
    );

    let mut scanned: BTreeMap<String, usize> = BTreeMap::new();
    for site in &sites {
        *scanned.entry(prattail_bucket(&site.file)).or_default() += 1;
    }
    let declared: BTreeMap<String, usize> = TIER2_RATCHET
        .iter()
        .map(|(k, v)| (k.to_string(), *v))
        .collect();

    let mut report: Vec<String> = Vec::new();
    for (bucket, found) in &scanned {
        match declared.get(bucket) {
            None => report.push(format!(
                "  `{bucket}` holds {found} refusal(s) and is NOT in TIER2_RATCHET. A \
                 directory that was at zero has gained refusals — convert them, or add the \
                 row deliberately and say why in the commit."
            )),
            Some(want) if found > want => report.push(format!(
                "  `{bucket}`: {found} refusals, ratchet is {want}. ⚠ The ratchet is \
                 MONOTONE: it may only be lowered, and lowering it means DELETING a site. \
                 Raising it is not a fix — the sites below are the ones to look at."
            )),
            Some(want) if found < want => report.push(format!(
                "  `{bucket}`: {found} refusals, ratchet is still {want}. Good news — lower \
                 the ratchet to {found} in TIER2_RATCHET so the gain is locked in."
            )),
            Some(_) => {},
        }
    }
    for (bucket, want) in &declared {
        if !scanned.contains_key(bucket) {
            report.push(format!(
                "  `{bucket}`: ratchet is {want} but NO refusals were found. If the \
                 directory is clean, DELETE its row; if the directory was renamed, rename \
                 the row."
            ));
        }
    }

    assert!(
        report.is_empty(),
        "the prattail refusal ratchet has moved:\n{}\n\nCurrent census by bucket: \
         {scanned:?}\n\nSites:\n{}",
        report.join("\n"),
        sites
            .iter()
            .map(|s| format!("  {s}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// TIER 3 — non-vacuity: the scanner is known to work, and to work precisely
// ═══════════════════════════════════════════════════════════════════════════
//
// A scanner that matched nothing would make Tiers 1 and 2 pass forever. These cells run it
// on synthetic buffers where the right answer is known by construction, in BOTH
// directions: it must SEE a real refusal and must NOT see the four things that are not
// refusals. Each positive cell is paired with the negative that shares its shape, so a
// mutation that broke the discrimination cannot pass by accident.

/// The scanner sees a plain `panic!` and reports its file and line.
#[test]
fn the_scanner_finds_a_planted_refusal() {
    let source = "fn f(x: u8) -> u8 {\n    match x {\n        0 => 1,\n        _ => \
                  panic!(\"planted\"),\n    }\n}\n";
    let sites = scan_source("synthetic.rs", source).expect("the fixture must parse");
    assert_eq!(sites.len(), 1, "expected exactly one site, got {sites:?}");
    assert_eq!(sites[0].construct, "panic");
    assert_eq!(sites[0].file, "synthetic.rs");
    assert_eq!(sites[0].line, 4, "the reported line must be the refusal's own");
}

/// …and all four refusal spellings, so `REFUSAL_MACROS` is known to be wired.
#[test]
fn the_scanner_finds_every_refusal_spelling() {
    let source = "fn f() {\n    panic!(\"a\");\n    unreachable!(\"b\");\n    \
                  todo!();\n    unimplemented!();\n}\n";
    let sites = scan_source("synthetic.rs", source).expect("the fixture must parse");
    let mut found: Vec<&str> = sites.iter().map(|s| s.construct.as_str()).collect();
    found.sort_unstable();
    assert_eq!(found, ["panic", "todo", "unimplemented", "unreachable"]);
}

/// ⚠ CONTROL — a refusal inside `quote!{}` is a token the macro EMITS, not a refusal that
/// fires during expansion. The scanner must not see it.
///
/// This was the second of the three stripper bugs the hand-built census hit, and it is the
/// single reason this gate parses instead of grepping: `macros/src` is full of `quote!`
/// bodies containing `panic!`s destined for generated code.
#[test]
fn the_scanner_ignores_a_refusal_inside_quote() {
    let inside = "fn emit() -> proc_macro2::TokenStream {\n    quote::quote! {\n        \
                  fn generated() { panic!(\"this one is EMITTED\"); }\n    }\n}\n";
    let sites = scan_source("synthetic.rs", inside).expect("the fixture must parse");
    assert!(
        sites.is_empty(),
        "a `panic!` inside `quote!{{}}` must not be counted — it is emitted code: {sites:?}"
    );

    // The paired POSITIVE, differing only in whether the refusal sits inside the `quote!`.
    let outside = "fn emit() -> proc_macro2::TokenStream {\n    panic!(\"this one FIRES\");\n}\n";
    let sites = scan_source("synthetic.rs", outside).expect("the fixture must parse");
    assert_eq!(
        sites.len(),
        1,
        "the same refusal OUTSIDE the quote must be counted, or this cell proves nothing"
    );
}

/// ⚠ KNOWN BOUND, pinned so nobody mistakes it for coverage.
///
/// `syn::Macro` keeps its body as an opaque `TokenStream`, which is exactly what makes the
/// `quote!` discrimination free — and the same property means a refusal inside *any* macro
/// body is invisible. Every refusal in this workspace is written in parsed expression,
/// statement or item position, so the census is complete today; this cell states the limit
/// rather than leaving a reader to discover it.
#[test]
fn the_scanner_does_not_see_inside_a_macro_body() {
    let source = "fn f() {\n    let _ = vec![panic!(\"hidden by the macro body\")];\n}\n";
    let sites = scan_source("synthetic.rs", source).expect("the fixture must parse");
    assert!(
        sites.is_empty(),
        "this cell documents a LIMIT: refusals nested inside another macro's body are not \
         counted. If it now fails, `syn` gained a visitor hook into macro tokens and the \
         module docs' bound has changed — a welcome improvement, but the docs must be \
         updated: {sites:?}"
    );
}

/// ⚠ CONTROL — test code is not production code. Both spellings, and the paired positive.
#[test]
fn the_scanner_ignores_test_gated_code() {
    let gated = "#[cfg(test)]\nmod tests {\n    fn helper() { panic!(\"in a test mod\"); }\n}\n\
                 #[test]\nfn a_test() { panic!(\"in a test fn\"); }\n";
    let sites = scan_source("synthetic.rs", gated).expect("the fixture must parse");
    assert!(
        sites.is_empty(),
        "refusals under `#[cfg(test)]` / `#[test]` must not be counted: {sites:?}"
    );

    // The paired POSITIVE: the same two bodies without the attributes.
    let ungated = "mod helpers {\n    fn helper() { panic!(\"in a plain mod\"); }\n}\n\
                   fn a_fn() { panic!(\"in a plain fn\"); }\n";
    let sites = scan_source("synthetic.rs", ungated).expect("the fixture must parse");
    assert_eq!(
        sites.len(),
        2,
        "without the test attributes both refusals must be counted, or the exclusion above \
         proves nothing: {sites:?}"
    );
}

/// ⚠ CONTROL — a refusal that is only *mentioned* is not a refusal. This is what lets this
/// very file, and the modules it guards, describe the ban in prose and in string literals.
#[test]
fn the_scanner_ignores_strings_and_comments() {
    let source = "fn f() -> &'static str {\n    // panic!(\"in a line comment\")\n    \
                  /* panic!(\"in a block comment\") */\n    \
                  let quoted = \"panic!(\\\"in a string\\\")\";\n    quoted\n}\n";
    let sites = scan_source("synthetic.rs", source).expect("the fixture must parse");
    assert!(
        sites.is_empty(),
        "a refusal that is only quoted or commented must not be counted: {sites:?}"
    );
}

/// ⚠ The cross-file exclusion works, pinned to the file whose four sites it first caught.
///
/// `prattail/src/decision_tree/tests.rs` carries no `#[cfg(test)]` of its own — the
/// attribute is on `mod tests;` in `decision_tree/mod.rs`. The first run of this gate's
/// census counted its four refusals as production sites. A scanner that looked only at the
/// file in front of it would still be counting them.
#[test]
fn a_test_module_declared_by_its_parent_is_excluded() {
    let root = workspace_root();
    let excluded = test_module_files(&root, "prattail/src");

    assert!(
        excluded.contains("prattail/src/decision_tree/tests.rs"),
        "the cross-file `mod` resolution no longer excludes \
         prattail/src/decision_tree/tests.rs, whose `#[cfg(test)]` lives in its PARENT. \
         Its refusals are being counted as production sites. Excluded set: {excluded:?}"
    );
    assert!(
        excluded.len() >= 10,
        "only {} test modules were resolved across prattail/src, which is too few for a \
         crate with test modules in most directories — the `mod` resolution is broken",
        excluded.len()
    );
    // …and the exclusion is not indiscriminate: production modules stay in.
    assert!(
        !excluded.contains("prattail/src/automata/codegen.rs"),
        "a production module was excluded as a test module"
    );
}

/// ★ THE WALK REACHES THE WORKSPACE — a sweep that found nothing fails loudly.
///
/// Per `rholang-runtime/tests/rholang_query_bind.rs:441-490`: *"a hand-listed set is what
/// failed here"*. Both tiers above compare a scan against a table; if the scan were empty
/// both would pass with every row unmatched — which the set-equality direction catches for
/// Tier 1, but only because this cell guarantees the scan is real in the first place.
#[test]
fn the_walk_reaches_the_workspace() {
    let root = workspace_root();
    let (macros_sites, macros_files, macros_skipped) = scan_subtree(&root, "macros/src");
    let (ast_sites, ast_files, _) = scan_subtree(&root, "ast/src");
    let (prattail_sites, prattail_files, _) = scan_subtree(&root, "prattail/src");

    assert!(macros_files >= 90, "macros/src: only {macros_files} files walked");
    assert!(ast_files >= 18, "ast/src: only {ast_files} files walked");
    assert!(prattail_files >= 140, "prattail/src: only {prattail_files} files walked");

    // Test modules exist and are being found — if this were zero, the exclusion logic
    // would be inert and the censuses would be inflated by test code.
    assert!(
        macros_skipped > 0,
        "no test modules were excluded from macros/src; the exclusion logic is inert"
    );

    let total = macros_sites.len() + ast_sites.len() + prattail_sites.len();
    assert!(
        total > 0,
        "the whole sweep found ZERO refusals across macros/src + ast/src + prattail/src. \
         That cannot be true of this tree; the scanner has stopped recognising the \
         construct it counts and every assertion in this file is vacuous."
    );
}

/// A diagnostic, not an assertion: prints the census for whoever has to move a ratchet.
///
/// `cargo test -p macros --test expansion_panic_gate -- --ignored --nocapture census_report`
#[test]
#[ignore = "diagnostic; run with --ignored --nocapture to print the refusal census"]
fn census_report() {
    let root = workspace_root();
    for sub in ["macros/src", "ast/src", "prattail/src"] {
        let (sites, files, skipped) = scan_subtree(&root, sub);
        println!(
            "### {sub}: {} sites, {files} files, {skipped} test modules excluded",
            sites.len()
        );
        for site in &sites {
            println!("  {site}");
        }
        if sub == "prattail/src" {
            let mut by_bucket: BTreeMap<String, usize> = BTreeMap::new();
            for site in &sites {
                *by_bucket.entry(prattail_bucket(&site.file)).or_default() += 1;
            }
            println!("--- TIER2_RATCHET should read: {by_bucket:?}");
        }
    }
}
