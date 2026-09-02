//! Exhaustive compile-time grammar to structural `language/3` round trip.
//!
//! This test lives beside the private macro bridge so it exercises the exact
//! `LanguageDef -> LanguageSpec -> GrammarCoreV1` projection used during macro
//! expansion. Inventory discovery is structural and manifest-rooted; no hand
//! list can silently omit a grammar.

use super::language_def_to_spec;
use mettail_ast::auto_inject::reconstruct_language_def_from_tokens;
use mettail_ast::ddl_migration_inventory::{discover_language_declarations, DeclarationKind};
use mettail_elab::canonical::value_to_language_core;
use mettail_elab::core_value::language_core_to_value;
use mettail_grammar_core::LanguageCoreV1;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("macros crate has a workspace parent")
        .to_path_buf()
}

#[test]
fn every_compile_time_grammar_has_a_lossless_structural_language3_value() {
    let declarations = discover_language_declarations(&workspace_root())
        .expect("the manifest-rooted language inventory must be total");
    assert!(!declarations.is_empty(), "the corpus cannot pass vacuously");

    // The proc macro registry stores raw definitions before composition. Build
    // exactly the same name environment, but only for names actually requested
    // by composition. Requiring one inventory owner per referenced name removes
    // filesystem and test-runner order from resolution.
    let referenced = declarations
        .iter()
        .flat_map(|declaration| {
            declaration
                .definition
                .extends_names
                .iter()
                .chain(declaration.definition.include_names.iter())
                .chain(declaration.definition.mixin_names.iter())
                .map(ToString::to_string)
        })
        .collect::<BTreeSet<_>>();
    for name in referenced {
        let candidates = declarations
            .iter()
            .filter(|declaration| declaration.name == name)
            .collect::<Vec<_>>();
        assert_eq!(
            candidates.len(),
            1,
            "composition name `{name}` must resolve to exactly one inventoried declaration",
        );
        let declaration = candidates[0];
        let result = match declaration.kind {
            DeclarationKind::Language => mettail_ast::registry::register_language(
                &declaration.name,
                &declaration.source_tokens,
            ),
            DeclarationKind::Fragment => mettail_ast::registry::register_fragment(
                &declaration.name,
                &declaration.source_tokens,
            ),
        };
        result.unwrap_or_else(|error| {
            panic!("{} cannot populate the composition registry: {error}", declaration.source_key)
        });
    }

    for declaration in declarations {
        let definition = match declaration.kind {
            DeclarationKind::Language => {
                reconstruct_language_def_from_tokens(declaration.source_tokens.clone())
                    .unwrap_or_else(|error| {
                        panic!("{} does not replay exactly: {error}", declaration.source_key)
                    })
            },
            DeclarationKind::Fragment => declaration.definition.clone(),
        };
        let specification = language_def_to_spec(&definition).unwrap_or_else(|error| {
            panic!("{} does not project to LanguageSpec: {error}", declaration.source_key)
        });
        let grammar = specification.to_grammar_core().unwrap_or_else(|error| {
            panic!("{} does not project to GrammarCoreV1: {error}", declaration.source_key)
        });
        let expected = LanguageCoreV1::structural(grammar);
        let value = language_core_to_value(&expected).unwrap_or_else(|error| {
            panic!("{} does not encode as structural language/3: {error}", declaration.source_key)
        });
        let actual = value_to_language_core(&value).unwrap_or_else(|error| {
            panic!("{} structural language/3 does not decode: {error:?}", declaration.source_key)
        });

        assert_eq!(
            actual, expected,
            "{} changed a LanguageCore field during canonical round trip",
            declaration.source_key,
        );
        assert_eq!(
            actual.grammar_fingerprint().unwrap(),
            expected.grammar_fingerprint().unwrap(),
            "{} changed its GrammarCore commitment",
            declaration.source_key,
        );
        assert_eq!(
            actual.fingerprint().unwrap(),
            expected.fingerprint().unwrap(),
            "{} changed its complete LanguageCore commitment",
            declaration.source_key,
        );
    }
}
