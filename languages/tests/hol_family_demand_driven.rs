//! ★ Work item #98 — the auto-injected HOL family is emitted ON DEMAND, per language.
//!
//! # The subject
//!
//! `macros/src/gen/types/enums.rs` auto-injects a four-variant higher-order-logic family
//! into a category for each domain category the language declares:
//!
//! | variant | payload | role |
//! |---|---|---|
//! | `Lam{D}` | `Scope<Binder<String>, Arc<Cat>>` | abstraction over a `D`-typed name |
//! | `MLam{D}` | `Scope<Vec<Binder<String>>, Arc<Cat>>` | multi-binder abstraction |
//! | `Apply{D}` | `(Arc<Cat>, Arc<D>)` | application, β-reduced in `term_ops/normalize.rs` |
//! | `MApply{D}` | `(Arc<Cat>, Vec<D>)` | multi-application |
//!
//! For a language of `n` categories that is `4n²` variants, because the family is emitted
//! for the full (category × domain) cross-product.
//!
//! Until #98 it was emitted for EVERY language. Measured over the 54 declared languages,
//! that was 3212 of 3976 generated AST variants — **80.8%** — while **40 of the 54 declare
//! no binder at all** and therefore cannot construct a `Lam{D}`, cannot reach a β-redex,
//! and cannot reference any of it. The gate now reads
//! `mettail_ast::grammar_shapes::declares_binder`.
//!
//! # ★★ Why the family is not merely unused but UNREACHABLE without a binder
//!
//! `Lam{D}` is the family's only introduction form, and the only surface syntax that
//! builds one is the synthetic `^x.{body}` rule from
//! `macros/src/gen/runtime/wpda_codegen/synthetic.rs` — which has been gated on binder
//! declaration since the WPDS migration. So for a binderless language the parser could
//! never produce a `Lam{D}`, hence `Apply{D}` had nothing to reduce against. The variants
//! were inhabited only by construction from Rust, which nothing does.
//!
//! # ★ It had already produced a defect
//!
//! `macros/src/gen/runtime/wpda_codegen/collection.rs` records it: `classify_binder_in`
//! resolved `declared_delims` from a rule's RESULT category, so an auto-injected
//! `MApplyProc(Arc<Map>, Vec<Proc>)` — injected into `Map` purely because `Map` was a
//! declared category — inherited `Map`'s `kv_sep: ":"` even though its slot is a plain
//! argument list. 40 of 42 kv slots were wrong for that reason (fixed in `331a525c`).
//! Injecting a family into categories where it means nothing *creates* defect surface.
//!
//! # The two directions, and why BOTH are required
//!
//! | direction | guard | what it refuses |
//! |---|---|---|
//! | the 14 keep theirs | [`every_binder_declaring_language_emits_the_full_hol_family`] | a gate that over-fires and strips a language that needs the family |
//! | the 40 lose nothing | [`no_binderless_language_emits_any_hol_variant`] | a gate that under-fires and leaves dead weight |
//! | neither is vacuous | [`the_gate_ranges_over_both_kinds_of_language`] | a run that asserts nothing because it found nothing |
//!
//! ⚠ The second direction is the one that can break something silently, so it is
//! *measured*: if any binderless language turns out to reference an `M*` variant, then it
//! DOES need the family and the predicate is wrong. Measured at the time of the change:
//! **0** references across all 40 languages' declaring specs, their entire generated
//! trees, and their name-keyed goldens.
//!
//! # Why the subject is the GENERATED tree and not the decision function
//!
//! `compute_hol_domain_pairs` lives in a proc-macro crate and cannot be called from an
//! integration test; its own unit tests in `macros/src/logic/common.rs` cover the decision.
//! This file checks the thing that actually ships — the emitted enums — so a decision that
//! is right but wired to the wrong emitter still fails here. It reads
//! `target/generated/<language>/ast_enums.rs`, which by construction exists whenever this
//! test runs: it is a `languages` integration test, so the crate (and every `language!` in
//! it) has been expanded to get here.

use mettail_ast::binder_census::{binder_census, DeclaredLanguage};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// The workspace root: `languages/`'s parent.
fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("`languages` is a workspace member, so its manifest dir has a parent")
        .to_path_buf()
}

fn census() -> Vec<DeclaredLanguage> {
    binder_census(&repo_root()).unwrap_or_else(|err| {
        panic!(
            "cannot census the declared languages: {err}\n\nThis guard decides which \
             languages MUST receive the HOL family and which must NOT from that census, so \
             it cannot continue with a guess: a narrowed census would silently stop \
             checking whole languages."
        )
    })
}

/// One category's variant list, as emitted.
struct EmittedEnum {
    category: String,
    variants: Vec<String>,
}

/// Whether `variant` names a member of the auto-injected HOL family.
///
/// The family's four forms are `Lam{D}` / `MLam{D}` / `Apply{D}` / `MApply{D}`, where `{D}`
/// is a declared category name and therefore begins with an upper-case letter. Requiring
/// that upper-case letter is what keeps a user-declared constructor such as `Application`
/// or `Lambda` (both legal rule labels, neither an injected variant) out of the match.
fn is_hol_variant(variant: &str) -> bool {
    ["MApply", "MLam", "Apply", "Lam"]
        .iter()
        .filter_map(|prefix| variant.strip_prefix(prefix))
        .any(|domain| domain.starts_with(|c: char| c.is_ascii_uppercase()))
}

/// Parse `ast_enums.rs` into its per-category variant lists.
///
/// The file is macro output with a fixed shape — `pub enum <Category> {` followed by one
/// variant per line at brace depth 1 — so a depth-tracking line scan reads it exactly. A
/// variant is an upper-case identifier followed by `(`, `,` or `{`.
fn parse_emitted_enums(source: &str, path: &Path) -> Vec<EmittedEnum> {
    let mut enums: Vec<EmittedEnum> = Vec::new();
    let mut depth: i32 = 0;
    let mut current: Option<EmittedEnum> = None;

    for line in source.lines() {
        let trimmed = line.trim_start();
        if depth == 0 {
            if let Some(rest) = trimmed
                .strip_prefix("pub enum ")
                .or_else(|| trimmed.strip_prefix("enum "))
            {
                let category = rest
                    .split(|c: char| c == '{' || c == '<' || c.is_whitespace())
                    .next()
                    .unwrap_or_default()
                    .to_string();
                current = Some(EmittedEnum { category, variants: Vec::new() });
            }
        } else if depth == 1 {
            if let Some(enum_being_read) = current.as_mut() {
                if let Some(variant) = variant_name(trimmed) {
                    enum_being_read.variants.push(variant);
                }
            }
        }

        depth += line.matches('{').count() as i32;
        depth -= line.matches('}').count() as i32;
        assert!(
            depth >= 0,
            "unbalanced braces while reading {} — the generated-enum reader has lost sync \
             and would silently report an empty variant list",
            path.display()
        );
        if depth == 0 {
            if let Some(finished) = current.take() {
                enums.push(finished);
            }
        }
    }

    enums
}

/// `Ident` from a variant line (`Ident(..)`, `Ident,` or `Ident {`), else `None`.
fn variant_name(trimmed: &str) -> Option<String> {
    let ident: String = trimmed
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    let first = ident.chars().next()?;
    if !first.is_ascii_uppercase() {
        return None;
    }
    match trimmed[ident.len()..].trim_start().chars().next() {
        Some('(' | ',' | '{') => Some(ident),
        _ => None,
    }
}

/// The emitted enums for `language`, or `None` when the language has no generated tree.
fn emitted_enums(language: &DeclaredLanguage) -> Option<Vec<EmittedEnum>> {
    let path = repo_root()
        .join("target/generated")
        .join(&language.directory_name)
        .join("ast_enums.rs");
    let source = fs::read_to_string(&path).ok()?;
    Some(parse_emitted_enums(&source, &path))
}

/// HOL variants emitted for `language`, grouped by hosting category.
fn hol_variants_by_category(language: &DeclaredLanguage) -> Option<BTreeMap<String, Vec<String>>> {
    let enums = emitted_enums(language)?;
    let mut found: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for emitted in enums {
        let hol: Vec<String> = emitted
            .variants
            .iter()
            .filter(|variant| is_hol_variant(variant))
            .cloned()
            .collect();
        if !hol.is_empty() {
            found.insert(emitted.category, hol);
        }
    }
    Some(found)
}

// ══════════════════════════════════════════════════════════════════════════════
// Direction 1 — every binder-declaring language still receives the FULL family
// ══════════════════════════════════════════════════════════════════════════════

/// A language that declares a binder receives all four forms for every ordered
/// (category, domain) pair — `4n²` variants — and the assertion NAMES the language.
///
/// This is the direction that catches a gate which over-fires. Inverting the predicate
/// makes every one of these languages emit zero, and this test reports the first by name.
#[test]
fn every_binder_declaring_language_emits_the_full_hol_family() {
    let census = census();
    let mut verified = 0usize;
    let mut findings: Vec<String> = Vec::new();

    for language in census.iter().filter(|entry| entry.declares_binder) {
        let Some(by_category) = hol_variants_by_category(language) else {
            findings.push(format!(
                "{} ({}) declares a binder but has no generated `ast_enums.rs`, so this \
                 guard could not verify that it received the HOL family",
                language.name, language.source
            ));
            continue;
        };

        let emitted: usize = by_category.values().map(Vec::len).sum();
        let expected = language.expected_hol_variants();

        // `expected` is derived from the PRE-composition category count, so a composed
        // language legitimately emits more than the census can predict; for those the
        // check is "the family is present", not the closed form. See
        // `mettail_ast::binder_census`.
        match language.composes {
            true if emitted == 0 => findings.push(format!(
                "{} ({}) declares a binder but emitted NO HOL variant",
                language.name, language.source
            )),
            true => verified += 1,
            false if emitted != expected => findings.push(format!(
                "{} ({}) declares a binder and {} categories, so it must receive 4·{n}² = \
                 {expected} HOL variants, but {emitted} were emitted. Per category: {:?}",
                language.name,
                language.source,
                language.category_count,
                by_category
                    .iter()
                    .map(|(cat, variants)| (cat, variants.len()))
                    .collect::<Vec<_>>(),
                n = language.category_count,
            )),
            false => {
                // Every declared category must host the family, and each must host
                // exactly the four forms per domain. A count that is right in aggregate
                // but wrong per category would otherwise pass.
                assert_eq!(
                    by_category.len(),
                    language.category_count,
                    "{} declares {} categories but only {} host HOL variants: {:?}",
                    language.name,
                    language.category_count,
                    by_category.len(),
                    by_category.keys().collect::<Vec<_>>(),
                );
                for (category, variants) in &by_category {
                    assert_eq!(
                        variants.len(),
                        4 * language.category_count,
                        "{}::{} hosts {} HOL variants; with {} declared domains it must \
                         host 4·{} = {}. Emitted: {:?}",
                        language.name,
                        category,
                        variants.len(),
                        language.category_count,
                        language.category_count,
                        4 * language.category_count,
                        variants,
                    );
                }
                verified += 1;
            },
        }
    }

    assert!(
        findings.is_empty(),
        "the HOL demand gate withheld the family from {} language(s) that declare a \
         binder:\n  {}\n\nA language that binds a variable can build a `Lam{{D}}` and \
         therefore needs `Apply{{D}}` to reduce it. If the gate is meant to narrow \
         further, narrow it PER (category, domain) with a derivation, not by dropping a \
         whole language.",
        findings.len(),
        findings.join("\n  "),
    );

    // Non-vacuity: this direction must have had subjects.
    assert!(
        verified >= 10,
        "only {verified} binder-declaring language(s) were verified to receive the HOL \
         family. The corpus holds 14, so either the census narrowed or the generated trees \
         are missing — and this direction's assertions are vacuous over an empty subject."
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Direction 2 — a binderless language receives NONE of it
// ══════════════════════════════════════════════════════════════════════════════

/// A language that declares no binder emits no `Lam{D}` / `MLam{D}` / `Apply{D}` /
/// `MApply{D}` variant at all, and the assertion NAMES the language and the variants.
///
/// This is the direction that catches a gate which under-fires — i.e. the pre-#98
/// behavior. Forcing the predicate always-true makes all 40 emit their families again,
/// and this test reports them by name.
#[test]
fn no_binderless_language_emits_any_hol_variant() {
    let census = census();
    let mut verified = 0usize;
    let mut findings: Vec<String> = Vec::new();

    for language in census.iter().filter(|entry| !entry.declares_binder) {
        let Some(by_category) = hol_variants_by_category(language) else {
            // No generated tree: nothing was emitted, so nothing is dead weight. Not a
            // finding, but not a verification either — the floor below counts only real
            // verifications.
            continue;
        };

        match by_category.is_empty() {
            true => verified += 1,
            false => {
                let total: usize = by_category.values().map(Vec::len).sum();
                findings.push(format!(
                    "{} ({}) declares NO binder, yet {total} HOL variant(s) were emitted \
                     into {} category/categories: {:?}",
                    language.name,
                    language.source,
                    by_category.len(),
                    by_category
                        .iter()
                        .map(|(cat, variants)| format!("{cat}: {variants:?}"))
                        .collect::<Vec<_>>(),
                ));
            },
        }
    }

    assert!(
        findings.is_empty(),
        "the HOL demand gate emitted the family into {} language(s) that declare no \
         binder:\n  {}\n\nWithout a binder there is no `Lam{{D}}` introduction form, so \
         these variants are unreachable: the synthetic `^x.{{body}}` surface rule is \
         itself gated on binder declaration \
         (`macros/src/gen/runtime/wpda_codegen/synthetic.rs`), so the parser cannot build \
         one and `Apply{{D}}` has nothing to β-reduce. ⚠ If one of these languages really \
         does need the family, then the predicate \
         (`mettail_ast::grammar_shapes::declares_binder`) is what is wrong — fix the \
         predicate, do not add the language to an exception list.",
        findings.len(),
        findings.join("\n  "),
    );

    assert!(
        verified >= 30,
        "only {verified} binderless language(s) were verified to receive no HOL family. \
         The corpus holds 40, so either the census narrowed or the generated trees are \
         missing — and this direction's assertion is vacuous over an empty subject."
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// The anti-vacuity floor
// ══════════════════════════════════════════════════════════════════════════════

/// ★ Both directions above have the form "every language of kind K satisfies P". Over an
/// empty set of kind-K languages that is vacuously true, so the gate must prove it had
/// subjects of BOTH kinds and that families were actually emitted.
///
/// A run that finds no binder-declaring language, or no emitted family at all, FAILS here.
/// That is the failure mode a mistake in the predicate would otherwise hide: a predicate
/// stuck at `false` makes direction 1 range over nothing and direction 2 trivially pass.
#[test]
fn the_gate_ranges_over_both_kinds_of_language() {
    let census = census();

    assert!(
        census.len() >= 30,
        "the census reports only {} declared languages; the corpus holds far more, so the \
         walk has narrowed and both directions of this gate are near-vacuous.",
        census.len()
    );

    let binder_declaring: Vec<&str> = census
        .iter()
        .filter(|entry| entry.declares_binder)
        .map(|entry| entry.name.as_str())
        .collect();
    let binderless = census.len() - binder_declaring.len();

    assert!(
        !binder_declaring.is_empty(),
        "NO declared language binds a variable. The demand gate is then equivalent to \
         deleting the HOL family outright, and `every_binder_declaring_language_emits_\
         the_full_hol_family` ranges over nothing."
    );
    assert!(
        binderless > 0,
        "EVERY declared language binds a variable, so the demand gate never withholds the \
         family and `no_binderless_language_emits_any_hol_variant` ranges over nothing."
    );

    // ★ The emitter must actually be emitting. A gate that is correct about who deserves
    // the family is worthless if the emitter produces none for anybody.
    let total_emitted: usize = census
        .iter()
        .filter_map(hol_variants_by_category)
        .map(|by_category| by_category.values().map(Vec::len).sum::<usize>())
        .sum();
    assert!(
        total_emitted >= 100,
        "only {total_emitted} HOL variant(s) were emitted across the ENTIRE corpus. The \
         binder-declaring languages alone account for far more, so the emitter is broken \
         rather than merely gated — and `no_binderless_language_emits_any_hol_variant` \
         would pass trivially against an emitter that emits nothing at all."
    );

    // ★ And the variant recognizer must actually recognize. If `is_hol_variant` were
    // broken to always answer `false`, every count above would read zero and BOTH
    // directions would agree on nothing.
    assert!(
        is_hol_variant("MApplyProc")
            && is_hol_variant("ApplyName")
            && is_hol_variant("LamTerm")
            && is_hol_variant("MLamM"),
        "the HOL variant recognizer fails to recognize the family's own naming scheme, so \
         every count in this file would read zero."
    );
    assert!(
        !is_hol_variant("Lambda")
            && !is_hol_variant("Application")
            && !is_hol_variant("PApply")
            && !is_hol_variant("Lam"),
        "the HOL variant recognizer matches user-declared constructors, so it would report \
         a family where a grammar merely named a rule `Lambda` or `Application`."
    );
}
