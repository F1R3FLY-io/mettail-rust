//! The DERIVED census of which declared languages bind a variable.
//!
//! # What this is for
//!
//! The auto-injected higher-order-logic (HOL) variant family — `Lam{D}` / `MLam{D}` /
//! `Apply{D}` / `MApply{D}` — is emitted per language on demand (work item #98), and the
//! demand signal is [`crate::grammar_shapes::declares_binder`]. Anything that wants to
//! audit that gate needs the same question answered for *every* declared language, which
//! means a corpus walk, a parse, and the predicate. This module is where those three meet,
//! ONCE.
//!
//! ```text
//!    [package.metadata.mettail] language_roots
//!                   │
//!          language_scan::language_files          ← the ONE walk (std only)
//!                   │
//!            syn::parse_file + inline `mod`       ← the structural decision
//!                   │
//!         grammar_shapes::declares_binder         ← the ONE predicate
//!                   │
//!              binder_census (THIS MODULE)
//!                   │
//!        ┌──────────┴───────────┐
//!        ▼                      ▼
//!  decision guard          emission guard
//!  (macros/src/logic/      (languages/tests/
//!   common.rs tests)        hol_family_demand_driven.rs)
//! ```
//!
//! # ★ Why a census and not a list of names
//!
//! "The languages that declare binders" is a computable property of the corpus, and this
//! repository has repeatedly been bitten by hand-maintained mirrors of computable domains
//! — `const BUNDLED_LANGUAGES` failed OPEN three times before it was replaced by a walk
//! (`ast/tests/language_name_keyed_artifacts.rs`). A roster written down here would have to
//! be edited by whoever adds a binder to a grammar, and nothing would make them.
//!
//! # Composition is answered CONSERVATIVELY, and disagreement is a finding
//!
//! `extends` / `includes` / `mixins` merge a base's `terms` into the deriving language, so
//! a language that spells no abstraction of its own can inherit one. Resolving that needs
//! the macro-time registry (`crate::registry`), which is empty outside the proc-macro, so
//! this census reports the **pre-composition** answer and records the composition clauses
//! it did not follow ([`DeclaredLanguage::composes`]).
//!
//! That is deliberately the safe direction. A composed language that inherits a binder is
//! censused as `declares_binder == false` while the macro — which composes first — emits
//! the family. The emission guard compares the two and reports a MISMATCH, so the
//! conservative answer surfaces as a loud finding rather than a silent pass. Today all
//! three composed languages (`ExtMath`, `ImportedMath`, `MixedMath`) derive from binderless
//! bases, so the two answers agree.

use crate::grammar_shapes::declares_binder;
use crate::language::LanguageDef;
use crate::language_scan;
use std::fs;
use std::path::Path;
use syn::{Item, ItemMacro};

/// One `language!` declaration, with the binder question answered.
#[derive(Debug, Clone)]
pub struct DeclaredLanguage {
    /// The name exactly as declared, e.g. `Rholang`.
    pub name: String,
    /// The name lower-cased — the key `macros/src/logic/writer.rs::lang_generated_dir`
    /// uses for `target/generated/<directory_name>/`.
    pub directory_name: String,
    /// Repo-relative path of the file holding the declaration.
    pub source: String,
    /// ★ Whether the grammar declares a binder — the HOL demand signal.
    pub declares_binder: bool,
    /// Declared categories (`types { … }`), pre-composition.
    pub category_count: usize,
    /// Declared grammar rules (`terms { … }`), pre-composition.
    pub rule_count: usize,
    /// Whether the declaration carries `extends` / `includes` / `mixins`, i.e. whether
    /// [`Self::declares_binder`] is the conservative pre-composition answer. See the
    /// module docs.
    pub composes: bool,
}

impl DeclaredLanguage {
    /// The number of HOL variants this language receives: four forms (`Lam` / `MLam` /
    /// `Apply` / `MApply`) for every ordered (category, domain) pair, or none.
    ///
    /// This is `4n²` for a binder-declaring language of `n` categories, and `0` otherwise
    /// — the closed form the emission guard checks the generated enums against.
    pub fn expected_hol_variants(&self) -> usize {
        match self.declares_binder {
            true => 4 * self.category_count * self.category_count,
            false => 0,
        }
    }
}

/// Every `language!` body under the manifest-declared roots, censused.
///
/// Sorted by `(name, source)`, so two consumers see the same order.
///
/// # Errors
///
/// Propagates a walk failure from [`language_scan::language_files`], and fails on a file
/// that cannot be read or that holds a `language!` body which does not parse. Never
/// returns an empty census silently — an empty result means the roots hold no declaration,
/// and every caller pairs this with its own non-vacuity floor.
pub fn binder_census(workspace_root: &Path) -> Result<Vec<DeclaredLanguage>, String> {
    let mut census = Vec::new();

    for path in language_scan::language_files(workspace_root)? {
        let source = fs::read_to_string(&path)
            .map_err(|err| format!("failed to read {}: {err}", path.display()))?;
        // The shared over-approximation, not a shared decision: a file that declares a
        // `language!` necessarily spells it followed by a delimiter, so this cannot hide a
        // declaration. It only spares `syn` the generated test hosts the roots also walk.
        if !language_scan::mentions_language_invocation(&source) {
            continue;
        }
        let parsed = syn::parse_file(&source)
            .map_err(|err| format!("failed to parse {}: {err}", path.display()))?;

        let mut defs = Vec::new();
        collect_language_defs(&parsed.items, &mut defs)
            .map_err(|err| format!("in {}: {err}", path.display()))?;

        let relative = language_scan::repo_relative(workspace_root, &path);
        for def in defs {
            let name = def.name.to_string();
            census.push(DeclaredLanguage {
                directory_name: name.to_lowercase(),
                name,
                source: relative.clone(),
                declares_binder: declares_binder(&def),
                category_count: def.types.len(),
                rule_count: def.terms.len(),
                composes: !def.extends_names.is_empty()
                    || !def.include_names.is_empty()
                    || !def.mixin_names.is_empty(),
            });
        }
    }

    census.sort_by(|left, right| {
        (&left.name, &left.source).cmp(&(&right.name, &right.source))
    });
    Ok(census)
}

/// Every item-level `language!` body in `items`, INCLUDING bodies inside inline `mod { … }`.
///
/// The inline-`mod` recursion is load-bearing: `languages/tests/x2_lookahead_bracket_probe.rs`
/// declares three languages, one per inline `pub mod`. A NON-inline `mod` (whose
/// `ItemMod::content` is `None`) is correctly not followed — the declaration belongs to the
/// file that spells it, and following the `#[path]` would count one grammar twice.
fn collect_language_defs(items: &[Item], out: &mut Vec<LanguageDef>) -> Result<(), String> {
    for item in items {
        match item {
            Item::Macro(item_macro) => collect_language_def(item_macro, out)?,
            Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    collect_language_defs(nested, out)?;
                }
            },
            _ => {},
        }
    }
    Ok(())
}

fn collect_language_def(item_macro: &ItemMacro, out: &mut Vec<LanguageDef>) -> Result<(), String> {
    if item_macro.mac.path.is_ident("language") {
        let def: LanguageDef = syn::parse2(item_macro.mac.tokens.clone())
            .map_err(|err| format!("failed to parse a `language!` body: {err}"))?;
        out.push(def);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("`ast` is a workspace member, so its manifest dir has a parent")
            .to_path_buf()
    }

    /// The anti-vacuity floor for every consumer of the census.
    ///
    /// Both guards this module feeds have the shape "everything the census reports
    /// satisfies P". Over an empty census that is vacuously true, so an empty (or
    /// implausibly small) census must fail HERE, loudly, rather than let a downstream
    /// assertion pass by ranging over nothing.
    #[test]
    fn the_census_finds_both_kinds_of_language() {
        let census = binder_census(&repo_root()).expect("the language corpus must be walkable");

        assert!(
            census.len() >= 30,
            "the binder census found only {} declared languages. The corpus holds far more, \
             so the walk or the structural decision has narrowed. Every guard that reads \
             this census checks a property of the languages it reports, which is vacuously \
             true over a census that reports (almost) nothing.",
            census.len()
        );

        let binding: Vec<&str> = census
            .iter()
            .filter(|entry| entry.declares_binder)
            .map(|entry| entry.name.as_str())
            .collect();
        let non_binding = census.len() - binding.len();

        assert!(
            !binding.is_empty(),
            "no declared language binds a variable. The HOL demand gate would then be \
             equivalent to deleting the family outright, and the guard that asserts the \
             binder-declaring languages still receive it would range over nothing."
        );
        assert!(
            non_binding > 0,
            "every declared language binds a variable, so the demand gate never withholds \
             the HOL family and the guard that asserts binderless languages receive none \
             would range over nothing. {} languages, all binding.",
            census.len()
        );
    }

    /// A category count of zero means the census read a definition whose `types { … }` had
    /// not been composed yet. That is expected for a composed language and ONLY for one:
    /// `expected_hol_variants` is `4n²`, which silently becomes `0` at `n == 0` and would
    /// make the emission guard demand nothing of a language that emits plenty.
    #[test]
    fn only_a_composed_language_can_report_zero_categories() {
        let census = binder_census(&repo_root()).expect("the language corpus must be walkable");
        let hidden: Vec<(&str, bool)> = census
            .iter()
            .filter(|entry| entry.category_count == 0)
            .map(|entry| (entry.name.as_str(), entry.composes))
            .collect();
        for (name, composes) in &hidden {
            assert!(
                composes,
                "{name} declares no category and does NOT compose, so nothing will ever \
                 fill its `types`. `expected_hol_variants()` returns 4·0² = 0 for it, which \
                 makes the emission guard's count assertion vacuous for that language."
            );
        }
    }

    /// Every censused name must be able to address its generated directory. The census is
    /// keyed to `target/generated/<lower-cased name>/` by
    /// `macros/src/logic/writer.rs::lang_generated_dir`, and a name that does not
    /// round-trip through lower-casing would be censused under a key no artifact uses.
    #[test]
    fn the_directory_key_is_the_lower_cased_name() {
        let census = binder_census(&repo_root()).expect("the language corpus must be walkable");
        for entry in &census {
            assert_eq!(
                entry.directory_name,
                entry.name.to_lowercase(),
                "{} is censused under a directory key that is not its lower-cased name",
                entry.name
            );
            assert!(
                !entry.name.is_empty(),
                "a `language!` body in {} declared an empty name",
                entry.source
            );
        }
    }
}
