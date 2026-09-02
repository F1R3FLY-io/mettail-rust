//! Shared category / HOL-domain helpers for the WPDA/Dovetail codegen path.
//!
//! (The Ascent Datalog generator that previously dominated this module was
//! retired in P6; only the HOL-domain utilities remain.)

use mettail_ast::language::LanguageDef;
use std::collections::BTreeSet;

/// Compute which `(category, domain)` pairs should get auto-generated
/// higher-order-logic variants `Lam{Domain}` / `MLam{Domain}` /
/// `Apply{Domain}` / `MApply{Domain}`.
///
/// **Demand-driven (work item #98).** A language that declares a binder gets the full
/// cross-product of (category × domain) over its declared object types. Closed
/// `data` categories are parser metasyntax and are excluded from both axes. A language that
/// declares none gets the EMPTY set, and therefore no HOL family at all.
///
/// The demand signal is [`mettail_ast::grammar_shapes::declares_binder`] — read there,
/// never restated here, so the WPDA surface-syntax emitter
/// (`gen/runtime/wpda_codegen/synthetic.rs`) and this variant emitter cannot disagree
/// about what a binder is. They *did* disagree until #98: `synthetic.rs` has gated its
/// synthetic `$dom(f, x)` / `^x.{p}` grammar rules on its own private copy of the
/// predicate since the WPDS migration, while this function returned the cross-product
/// unconditionally. The result was 1432 variants across the 40 binderless languages
/// that had no surface syntax, no reachable β-redex, and no way to be constructed.
///
/// ## Why this is safe NOW when the earlier "HOL-B" attempt was not
///
/// HOL-B tried to narrow the set PER PAIR, by (a) structural analysis of abstraction
/// params and (b) a name scan of user `rust_code` / logic blocks. It broke because
/// downstream emitters referenced the variants *unconditionally*, so a narrowed enum
/// left dangling references — 96+ compile errors across rholang/guardedrho. The comment
/// that recorded the failure prescribed the fix: *"teach every emitter to use the same
/// gated set"*.
///
/// ★ That fix has since landed, incrementally, and this function is now the ONE oracle.
/// Every site that spells a HOL variant's name derives it from this set:
///
/// | emitter | gate |
/// |---|---|
/// | `gen/types/enums.rs` (the enum itself) | `hol_pairs.contains` |
/// | `gen/syntax/display.rs` | `hol_pairs.contains` |
/// | `gen/syntax/var_inference.rs` | `hol_pairs.contains` |
/// | `gen/term_ops/normalize.rs` (β/η arms, incl. `lam_doms`) | `compute_hol_pairs_set` |
/// | `gen/term_ops/subst.rs` (incl. `collect_category_variants`) | `hol_pairs.contains` |
/// | `gen/runtime/language.rs` (two sites) | `hol_pairs.contains` |
/// | `gen/runtime/wpda_codegen/synthetic.rs` (surface syntax) | `declares_binder` |
///
/// `prattail/src/trampoline.rs`, the file the failure comment named as emitting
/// unconditionally, no longer exists. An empty set now propagates to every one of those
/// sites together, which is precisely the property HOL-B lacked.
///
/// ## The gate is per LANGUAGE, deliberately not per (category, domain)
///
/// Narrowing further is derivable — an abstraction's type `[D -> C]` names its domain
/// and its host category directly — but it would change the emitted variant set of the
/// binder-declaring languages, and those languages' term encodings are pinned
/// byte-for-byte by the consensus suites (`rholang-codegen/tests/a_s5_*`,
/// `runtime/tests/canonical_to_bytes.rs`). Per-language gating touches no
/// binder-declaring language at all, so it moves no pinned byte. See
/// `languages/tests/hol_family_demand_driven.rs` for the guard that holds both
/// directions.
pub fn compute_hol_domain_pairs(language: &LanguageDef) -> BTreeSet<(String, String)> {
    // ★ The demand gate. Without a binder the family is unreachable, not merely unused:
    // `Lam{D}` is the only constructor that introduces a binding, so nothing can build
    // one, and `Apply{D}` has nothing to β-reduce against.
    if !mettail_ast::grammar_shapes::declares_binder(language) {
        return BTreeSet::new();
    }

    let all_types: Vec<String> = language
        .types
        .iter()
        .filter(|t| !t.is_data())
        .map(|t| t.name.to_string())
        .collect();
    let mut pairs: BTreeSet<(String, String)> = BTreeSet::new();
    for cat in &all_types {
        for domain in &all_types {
            pairs.insert((cat.clone(), domain.clone()));
        }
    }
    pairs
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::binder_census::binder_census;
    use mettail_ast::grammar::GrammarItem;
    use std::path::{Path, PathBuf};

    fn parse(body: &str) -> LanguageDef {
        syn::parse_str::<LanguageDef>(body).expect("the test grammar must parse")
    }

    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("`macros` is a workspace member, so its manifest dir has a parent")
            .to_path_buf()
    }

    /// Two grammars over the SAME two categories, differing ONLY in whether one rule binds.
    ///
    /// `binding` spells `^x.body:[Name -> Proc]` (a `TermParam::Abstraction`); `inert`
    /// replaces it with a plain `n:Name` parameter. Everything else — the category set, the
    /// rule count, the surface syntax shape — is held fixed, so any difference in the
    /// emitted HOL set is attributable to binder declaration and to nothing else.
    fn minimal_pair() -> (LanguageDef, LanguageDef) {
        let binding = parse(
            r#"
                name: BindingTwin,
                types {
                    Proc
                    Name
                },
                terms {
                    Zero . |- "0" : Proc ;
                    Bind . ^x.body:[Name -> Proc] |- "for" x "." body : Proc ;
                    NLit . |- "n" : Name ;
                },
                equations {},
                rewrites {},
            "#,
        );
        let inert = parse(
            r#"
                name: InertTwin,
                types {
                    Proc
                    Name
                },
                terms {
                    Zero . |- "0" : Proc ;
                    Bind . n:Name, body:Proc |- "for" n "." body : Proc ;
                    NLit . |- "n" : Name ;
                },
                equations {},
                rewrites {},
            "#,
        );
        (binding, inert)
    }

    /// ★ The gate, on a minimal pair: the ONLY difference is one abstraction param.
    #[test]
    fn the_hol_set_is_the_cross_product_with_a_binder_and_empty_without_one() {
        let (binding, inert) = minimal_pair();

        assert!(
            mettail_ast::grammar_shapes::declares_binder(&binding),
            "the binding twin spells `^x.body:[Name -> Proc]`, which is a \
             `TermParam::Abstraction`; if the predicate cannot see it, the gate is reading \
             the wrong field."
        );
        assert!(
            !mettail_ast::grammar_shapes::declares_binder(&inert),
            "the inert twin has no abstraction param and no `GrammarItem::Binder`, so it \
             must not be treated as binding."
        );

        let with_binder = compute_hol_domain_pairs(&binding);
        let without = compute_hol_domain_pairs(&inert);

        // n = 2 categories ⇒ the full cross-product is n² = 4 pairs ⇒ 4·n² = 16 variants.
        assert_eq!(
            with_binder.len(),
            4,
            "a binder-declaring language of 2 categories must get the full 2² cross-product \
             of (category, domain) pairs, got {with_binder:?}"
        );
        for cat in ["Proc", "Name"] {
            for domain in ["Proc", "Name"] {
                assert!(
                    with_binder.contains(&(cat.to_string(), domain.to_string())),
                    "({cat}, {domain}) is missing from the cross-product: {with_binder:?}"
                );
            }
        }

        assert!(
            without.is_empty(),
            "a language that declares no binder must receive NO HOL pairs, got {without:?}. \
             Without a `Lam{{D}}` introduction form the family cannot be constructed and \
             `Apply{{D}}` has nothing to β-reduce."
        );
    }

    /// The legacy positional style spells binding in `items` as a `GrammarItem::Binder`
    /// rather than as a term-context param. Both styles are demand.
    #[test]
    fn a_legacy_positional_binder_is_also_demand() {
        let legacy = parse(
            r#"
                name: LegacyBinderTwin,
                types {
                    Proc
                    Name
                },
                terms {
                    Zero . |- "0" : Proc ;
                    NLit . |- "n" : Name ;
                },
                equations {},
                rewrites {},
            "#,
        );
        // Confirm the fixture is inert BEFORE the positional binder is attached, so the
        // assertion below cannot pass for some unrelated reason.
        assert!(
            compute_hol_domain_pairs(&legacy).is_empty(),
            "the fixture must start inert, or attaching a binder proves nothing"
        );

        let mut with_positional = legacy.clone();
        with_positional.terms[0].items.push(GrammarItem::Binder {
            category: syn::Ident::new("Name", proc_macro2::Span::call_site()),
        });
        assert_eq!(
            compute_hol_domain_pairs(&with_positional).len(),
            4,
            "a rule carrying a `GrammarItem::Binder` binds a variable just as an \
             abstraction param does, so the language must receive the full family."
        );
    }

    /// ★★ The corpus-wide correspondence: emptiness of the HOL set is exactly
    /// non-declaration of a binder, for every declared language.
    ///
    /// This is the decision-level half of the gate; the emission-level half lives in
    /// `languages/tests/hol_family_demand_driven.rs`, which checks the enums that actually
    /// ship. Both are needed: a right decision wired to the wrong emitter passes here and
    /// fails there.
    #[test]
    fn the_gate_agrees_with_the_binder_census_over_the_whole_corpus() {
        let census = binder_census(&repo_root()).expect("the language corpus must be walkable");

        // Anti-vacuity floor FIRST: the loop below asserts a property of what the census
        // reports, which is vacuously true over an empty census.
        assert!(
            census.len() >= 30,
            "the census reports only {} declared languages; the loop below would be \
             near-vacuous.",
            census.len()
        );
        let binding = census.iter().filter(|e| e.declares_binder).count();
        assert!(
            binding > 0 && binding < census.len(),
            "the census must report BOTH kinds for this correspondence to have content: \
             {binding} binding of {} total.",
            census.len()
        );

        let mut checked = 0usize;
        for entry in &census {
            // The census answers PRE-composition, and a composed language's `types` are
            // filled in by `merge::apply_*` at macro time. Re-deriving that here would
            // need the macro-time registry, which is empty in a test, so the composed
            // languages are covered by the emission guard instead — it reads output that
            // was produced WITH composition applied.
            if entry.composes {
                continue;
            }
            let path = repo_root().join(&entry.source);
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|err| panic!("read {}: {err}", path.display()));
            let file = syn::parse_file(&source)
                .unwrap_or_else(|err| panic!("parse {}: {err}", path.display()));

            for item in &file.items {
                let syn::Item::Macro(item_macro) = item else {
                    continue;
                };
                if !item_macro.mac.path.is_ident("language") {
                    continue;
                }
                let def: LanguageDef = syn::parse2(item_macro.mac.tokens.clone())
                    .unwrap_or_else(|err| panic!("parse a body in {}: {err}", entry.source));
                if def.name.to_string() != entry.name {
                    continue;
                }
                let pairs = compute_hol_domain_pairs(&def);
                assert_eq!(
                    pairs.is_empty(),
                    !entry.declares_binder,
                    "{}: the HOL pair set is {} while the census says declares_binder = {}. \
                     The gate and the predicate must be the same question — \
                     `compute_hol_domain_pairs` reads \
                     `grammar_shapes::declares_binder` and nothing else.",
                    entry.name,
                    match pairs.is_empty() {
                        true => "EMPTY".to_string(),
                        false => format!("{} pair(s)", pairs.len()),
                    },
                    entry.declares_binder,
                );
                if entry.declares_binder {
                    let open_category_count = def
                        .types
                        .iter()
                        .filter(|category| !category.is_data())
                        .count();
                    let closed_category_count = def.types.len() - open_category_count;
                    assert_eq!(
                        pairs.len(),
                        open_category_count * open_category_count,
                        "{} declares {} categories ({} open, {} closed data), so the HOL \
                         cross-product is {}² open-category pairs, but {} were produced.",
                        entry.name,
                        entry.category_count,
                        open_category_count,
                        closed_category_count,
                        open_category_count,
                        pairs.len(),
                    );
                }
                checked += 1;
            }
        }

        assert!(
            checked >= 30,
            "only {checked} language definition(s) were re-derived and compared against the \
             census; the correspondence is near-vacuous."
        );
    }
}
