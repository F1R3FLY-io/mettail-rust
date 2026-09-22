//! Pre-relocation baselines for the original five-pass category census and indices.

use super::{collect_category_names_with_literals, infix};
use mettail_ast::grammar::rule_fixture;
use mettail_ast::language::{CategoryRole, CollectionCategory, LangType, LanguageDef, TokenDef};
use proc_macro2::Span;
use syn::Ident;

fn id(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn category(name: &str, native: bool, collection: bool) -> LangType {
    LangType {
        name: id(name),
        role: CategoryRole::Data,
        native_type: native.then(|| syn::parse_quote!(i32)),
        collection_kind: collection
            .then(|| CollectionCategory::List(CollectionCategory::list_defaults())),
    }
}

fn token(category: Option<&str>, from_literals: bool) -> TokenDef {
    TokenDef {
        name: id("Token"),
        pattern: "token".into(),
        category: category.map(id),
        rust_code: None,
        priority: None,
        push_mode: None,
        is_pop: false,
        stream: None,
        from_literals,
    }
}

#[test]
fn original_census_preserves_five_pass_priority_and_source_order() {
    let language = LanguageDef {
        name: id("CensusBaseline"),
        options: Default::default(),
        extends_names: vec![],
        include_names: vec![],
        mixin_names: vec![],
        // Deliberately not census order. Data categories are not filtered.
        types: vec![
            category("Reference", false, false),
            category("Native", true, false),
            category("Collection", true, true),
            category("LiteralZ", false, false),
            category("LiteralA", true, true),
            category("Reference", false, false),
            category("RuleZ", false, false),
        ],
        refinement_types: vec![],
        // Token order is not literal-category output order. Nonliteral and
        // unassigned tokens must not manufacture an early category slot.
        token_defs: vec![
            token(Some("Reference"), false),
            token(None, true),
            token(Some("LiteralA"), true),
            token(Some("MissingDeclaration"), true),
            token(Some("LiteralZ"), true),
        ],
        mode_defs: vec![],
        sync_constraints: vec![],
        tree_invariants: vec![],
        terms: vec![
            rule_fixture(id("First"), id("RuleZ")),
            rule_fixture(id("Second"), id("RuleA")),
            rule_fixture(id("Third"), id("RuleZ")),
        ],
        equations: vec![],
        rewrites: vec![],
        logic: None,
        guard_config: None,
    };
    assert_eq!(
        collect_category_names_with_literals(&language),
        ["RuleZ", "RuleA", "LiteralZ", "LiteralA", "Collection", "Native", "Reference"]
    );
}

#[test]
fn original_label_index_uses_bucket_owner_and_last_duplicate_coordinates() {
    let categories = vec!["Z".into(), "Empty".into(), "Z".into()];
    let per_cat = vec![
        vec![rule_fixture(id("Same"), id("NotTheBucket"))],
        vec![],
        vec![
            rule_fixture(id("Same"), id("AlsoNotTheBucket")),
            rule_fixture(id("Same"), id("Different")),
        ],
    ];
    let index = infix::build_label_index(&categories, &per_cat);
    assert_eq!(index.len(), 1);
    assert_eq!(index.get(&("Z".into(), "Same".into())), Some(&(2, 1)));
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn original_label_index_requires_a_category_even_for_an_empty_bucket() {
    let _ = infix::build_label_index(&[], &[vec![]]);
}
