//! Original collection-category observations before shared helper extraction.
//! Fixtures use the existing AST parser and public source helper; no alternate
//! native classifier or collection-element inference is implemented here.

use mettail_ast::grammar::{GrammarItem, GrammarRule};
use mettail_ast::language::{
    CategoryRole, CollectionCategory, CollectionDelimiters, LangType, LanguageDef,
};
use mettail_ast::types::CollectionType;
use quote::quote;

fn ident(name: &str) -> syn::Ident {
    syn::parse_str(name).expect("collection observation name must be an identifier")
}

fn language() -> LanguageDef {
    syn::parse2(quote! {
        name: CollectionObservations,
        types { Proc },
        terms { Seed . |- "seed" : Proc; }
    })
    .expect("minimal collection observation language must parse")
}

fn declaration(name: &str, native: Option<&str>, collection: bool) -> LangType {
    LangType {
        name: ident(name),
        role: CategoryRole::Object,
        native_type: native
            .map(|source| syn::parse_str(source).expect("native fixture must parse")),
        collection_kind: collection
            .then(|| CollectionCategory::List(CollectionCategory::list_defaults())),
    }
}

fn collection_item(element: &str) -> GrammarItem {
    GrammarItem::Collection {
        coll_type: CollectionType::HashMap,
        element_type: ident(element),
        separator: ";".into(),
        delimiters: Some(("[".into(), "]".into())),
    }
}

fn rule(label: &str, category: &str, items: Vec<GrammarItem>) -> GrammarRule {
    let mut source = language();
    let mut rule = source.terms.remove(0);
    rule.label = ident(label);
    rule.category = ident(category);
    rule.items = items;
    rule
}

fn element(language: &LanguageDef, category: &str) -> Option<String> {
    language
        .collection_element_type_for_category(&ident(category))
        .map(|name| name.to_string())
}

#[test]
fn original_collection_observation_first_declaration_wins() {
    let mut source = language();
    source.types = vec![
        declaration("Other", Some("Vec<Ignored>"), true),
        declaration("Seq", Some("Vec<First>"), true),
        declaration("Seq", Some("Vec<Second>"), true),
    ];
    assert_eq!(element(&source, "Seq"), Some("First".into()));
    source.types.swap(1, 2);
    assert_eq!(element(&source, "Seq"), Some("Second".into()));
    assert_eq!(element(&source, "seq"), None);
}

#[test]
fn original_collection_observation_declared_collection_none_suppresses_terms() {
    let mut source = language();
    source.terms = vec![rule("Available", "Seq", vec![collection_item("TermElement")])];
    for native in [None, Some("str"), Some("Vec<&Proc>")] {
        source.types =
            vec![declaration("Seq", native, true), declaration("Seq", Some("Vec<Later>"), true)];
        assert_eq!(element(&source, "Seq"), None, "native={native:?}");
    }
    source.types = vec![
        declaration("Seq", Some("Vec<NativeButUndeclared>"), false),
        declaration("Seq", Some("Vec<Later>"), true),
    ];
    assert_eq!(element(&source, "Seq"), Some("TermElement".into()));
}

#[test]
fn original_collection_observation_only_first_matching_term_is_searched() {
    let mut source = language();
    source.terms = vec![
        rule("Unrelated", "Other", vec![collection_item("WrongCategory")]),
        rule("First", "Seq", vec![GrammarItem::Terminal("plain".into())]),
        rule("Later", "Seq", vec![collection_item("TooLate")]),
    ];
    assert_eq!(element(&source, "Seq"), None);
    source.terms[1].items = vec![
        GrammarItem::Terminal("prefix".into()),
        GrammarItem::Binder { category: ident("IgnoredBinder") },
        GrammarItem::non_terminal(ident("IgnoredNonterminal")),
        collection_item("Chosen"),
        collection_item("LaterItem"),
    ];
    assert_eq!(element(&source, "Seq"), Some("Chosen".into()));
}

#[test]
fn original_collection_observation_native_first_argument_is_shallow() {
    let mut source = language();
    for (native, expected) in [
        ("Vec<Proc>", Some("Proc")),
        ("HashMap<Key, Value>", Some("Key")),
        ("AnyContainer<module::Elem, Other>", Some("Elem")),
        ("<T as Trait>::Container<module::Elem>", Some("Elem")),
        ("Vec<<T as Trait>::Element>", Some("Element")),
        ("Vec<Vec<Proc>>", Some("Vec")),
        ("Vec<Elem<Proc>>", Some("Elem")),
        ("Vec<'a, Proc>", None),
        ("Vec<3, Proc>", None),
        ("Vec<&Proc>", None),
        ("Vec<(Proc, Other)>", None),
        ("Vec", None),
        ("&Vec<Proc>", None),
        ("[Proc; 2]", None),
    ] {
        source.types = vec![declaration("Seq", Some(native), true)];
        assert_eq!(element(&source, "Seq").as_deref(), expected, "native={native}");
    }
    source.types[0].native_type = Some(syn::Type::Path(syn::TypePath {
        qself: None,
        path: syn::Path {
            leading_colon: None,
            segments: Default::default(),
        },
    }));
    assert_eq!(element(&source, "Seq"), None);
}

#[test]
fn original_collection_observation_all_five_default_records_and_kinds() {
    let rows = [
        (
            CollectionCategory::List(CollectionCategory::list_defaults()),
            "list(",
            None,
            CollectionType::Vec,
        ),
        (
            CollectionCategory::Bag(CollectionCategory::bag_defaults()),
            "bag(",
            None,
            CollectionType::HashBag,
        ),
        (
            CollectionCategory::Map(CollectionCategory::map_defaults()),
            "map(",
            Some(":"),
            CollectionType::HashMap,
        ),
        (
            CollectionCategory::Set(CollectionCategory::set_defaults()),
            "Set(",
            None,
            CollectionType::HashSet,
        ),
        (
            CollectionCategory::Pathmap(CollectionCategory::pathmap_defaults()),
            "pathmap(",
            Some(":"),
            CollectionType::PathMap,
        ),
    ];
    for (category, open, key_value, kind) in rows {
        assert_eq!(
            category.delimiters(),
            &CollectionDelimiters {
                open: open.into(),
                close: ")".into(),
                sep: ",".into(),
                key_val_sep: key_value.map(str::to_owned),
            }
        );
        assert_eq!(category.coll_type(), kind);
    }
}

#[test]
fn original_collection_observation_custom_fields_are_not_defaulted() {
    let custom = CollectionDelimiters {
        open: String::new(),
        close: "close-custom".into(),
        sep: String::new(),
        key_val_sep: None,
    };
    for category in [
        CollectionCategory::List(custom.clone()),
        CollectionCategory::Bag(custom.clone()),
        CollectionCategory::Map(custom.clone()),
        CollectionCategory::Set(custom.clone()),
        CollectionCategory::Pathmap(custom.clone()),
    ] {
        assert_eq!(category.delimiters(), &custom);
    }
    let source: LanguageDef = syn::parse2(quote! {
        name: CustomDelimiters,
        types {
            ![Payload] as Map ["", "end", ";"]
            ![Payload] as Pathmap { open_parts: ["{|"], close_parts: ["|}"], sep: ";" }
        },
        terms { }
    })
    .expect("original positional and dictionary delimiter forms parse");
    let map = source.types[0]
        .collection_kind
        .as_ref()
        .expect("Map retains collection declaration")
        .delimiters();
    assert_eq!(map.open, "");
    assert_eq!(map.close, "end");
    assert_eq!(map.sep, ";");
    assert_eq!(map.key_val_sep, None);
    let pathmap = source.types[1]
        .collection_kind
        .as_ref()
        .expect("Pathmap retains collection declaration")
        .delimiters();
    assert_eq!(pathmap.open, "{|");
    assert_eq!(pathmap.close, "|}");
    assert_eq!(pathmap.sep, ";");
    assert_eq!(pathmap.key_val_sep.as_deref(), Some(":"));
}
