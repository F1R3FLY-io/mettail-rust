//! Frozen against the original context-to-items converter before relocation.
//! Explicit output rosters assert order, separators and even partial-arrow
//! binding indices; no oracle reimplements or reparses the conversion.
use mettail_ast::grammar::{
    convert_term_context_to_items, GrammarItem, NonTerminalKind, TermParam,
};
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::Span;
use syn::Ident;

fn ident(value: &str) -> Ident {
    Ident::new(value, Span::call_site())
}
fn base(value: &str) -> TypeExpr {
    TypeExpr::Base(ident(value))
}
fn arrow(domain: TypeExpr, codomain: TypeExpr) -> TypeExpr {
    TypeExpr::Arrow {
        domain: Box::new(domain),
        codomain: Box::new(codomain),
    }
}
fn collection(kind: CollectionType, element: TypeExpr) -> TypeExpr {
    TypeExpr::Collection {
        coll_type: kind,
        element: Box::new(element),
    }
}
fn map(key: TypeExpr, value: TypeExpr) -> TypeExpr {
    TypeExpr::Map {
        key: Box::new(key),
        value: Box::new(value),
    }
}
fn simple(ty: TypeExpr) -> TermParam {
    TermParam::Simple { name: ident("unused"), ty }
}
fn abstraction(ty: TypeExpr) -> TermParam {
    TermParam::Abstraction {
        binder: ident("ignored_binder"),
        body: ident("ignored_body"),
        ty,
    }
}
fn multi(ty: TypeExpr) -> TermParam {
    TermParam::MultiAbstraction {
        binder: ident("ignored_binders"),
        body: ident("ignored_body"),
        ty,
    }
}
fn optional(params: Vec<TermParam>) -> TermParam {
    TermParam::Optional { params }
}
fn nt(value: &str) -> GrammarItem {
    GrammarItem::NonTerminal {
        ident: ident(value),
        kind: NonTerminalKind::classify(value),
    }
}
fn bind(value: &str) -> GrammarItem {
    GrammarItem::Binder { category: ident(value) }
}
fn coll(kind: CollectionType, element: &str, separator: &str) -> GrammarItem {
    GrammarItem::Collection {
        coll_type: kind,
        element_type: ident(element),
        separator: separator.into(),
        delimiters: None,
    }
}

#[test]
fn empty_guards_and_empty_optional_groups_emit_nothing() {
    assert_eq!(convert_term_context_to_items(&[]), (vec![], vec![]));
    let params = [
        TermParam::GuardBody { name: ident("g") },
        optional(vec![]),
        optional(vec![TermParam::GuardBody { name: ident("nested") }, optional(vec![])]),
    ];
    assert_eq!(convert_term_context_to_items(&params), (vec![], vec![]));
}

#[test]
fn simple_types_preserve_order_duplicates_kind_and_exact_collection_defaults() {
    let params = [
        simple(base("Ident")),
        simple(base("Expr")),
        simple(base("Expr")),
        simple(collection(CollectionType::Vec, base("V"))),
        simple(collection(CollectionType::HashBag, base("B"))),
        simple(collection(CollectionType::HashSet, base("S"))),
        simple(collection(CollectionType::PathMap, base("P"))),
        simple(map(base("M"), base("M"))),
    ];
    assert_eq!(
        convert_term_context_to_items(&params),
        (
            vec![
                nt("Ident"),
                nt("Expr"),
                nt("Expr"),
                coll(CollectionType::Vec, "V", "|"),
                coll(CollectionType::HashBag, "B", "|"),
                coll(CollectionType::HashSet, "S", "|"),
                coll(CollectionType::PathMap, "P", "|"),
                coll(CollectionType::HashMap, "M", ",")
            ],
            vec![]
        )
    );
}

#[test]
fn unsupported_nested_shapes_and_unequal_map_names_are_skipped_without_slots() {
    let params = [
        simple(collection(CollectionType::Vec, collection(CollectionType::Vec, base("E")))),
        simple(map(base("K"), base("V"))),
        simple(map(base("K"), arrow(base("K"), base("K")))),
        simple(map(arrow(base("K"), base("K")), base("K"))),
        simple(arrow(base("A"), base("B"))),
        simple(TypeExpr::MultiBinder(Box::new(base("A")))),
        simple(TypeExpr::Refined {
            var: ident("x"),
            base: Box::new(base("E")),
            predicate_repr: "ignored".into(),
        }),
        simple(base("Tail")),
    ];
    assert_eq!(convert_term_context_to_items(&params), (vec![nt("Tail")], vec![]));
}

#[test]
fn top_level_partial_arrows_keep_original_pre_and_post_domain_indices() {
    let nonbase = || collection(CollectionType::Vec, base("E"));
    let params = [
        simple(base("A")),
        abstraction(arrow(nonbase(), base("B"))),
        abstraction(arrow(base("N"), nonbase())),
        abstraction(arrow(nonbase(), nonbase())),
        abstraction(arrow(base("N"), base("C"))),
        abstraction(base("NotArrow")),
    ];
    assert_eq!(
        convert_term_context_to_items(&params),
        (
            vec![nt("A"), nt("B"), bind("N"), bind("N"), nt("C")],
            vec![(1, vec![1]), (2, vec![3]), (3, vec![3]), (3, vec![4])]
        )
    );
}

#[test]
fn multi_abstraction_requires_exact_multibinder_domain_but_always_records_arrow_binding() {
    let params = [
        multi(arrow(TypeExpr::MultiBinder(Box::new(base("Name"))), base("Proc"))),
        multi(arrow(base("Name"), base("Other"))),
        multi(arrow(
            TypeExpr::MultiBinder(Box::new(collection(CollectionType::Vec, base("Name")))),
            collection(CollectionType::Vec, base("Proc")),
        )),
        multi(base("NotArrow")),
    ];
    assert_eq!(
        convert_term_context_to_items(&params),
        (
            vec![bind("Name"), nt("Proc"), nt("Other")],
            vec![(0, vec![1]), (2, vec![2]), (3, vec![3])]
        )
    );
}

#[test]
fn nested_optional_preorder_emits_bodies_only_and_never_adds_bindings() {
    let params = [
        optional(vec![
            simple(base("A")),
            abstraction(arrow(base("Hidden"), base("B"))),
            optional(vec![
                multi(arrow(TypeExpr::MultiBinder(Box::new(base("Hidden"))), base("C"))),
                TermParam::GuardBody { name: ident("g") },
                optional(vec![
                    simple(collection(CollectionType::Vec, base("D"))),
                    simple(map(base("E"), base("E"))),
                ]),
            ]),
            abstraction(arrow(base("Hidden"), collection(CollectionType::Vec, base("Skipped")))),
        ]),
        abstraction(arrow(base("Name"), base("Tail"))),
    ];
    assert_eq!(
        convert_term_context_to_items(&params),
        (
            vec![
                nt("A"),
                nt("B"),
                nt("C"),
                coll(CollectionType::Vec, "D", "|"),
                coll(CollectionType::HashMap, "E", ","),
                bind("Name"),
                nt("Tail")
            ],
            vec![(5, vec![6])]
        )
    );
}

#[test]
fn original_name_equality_and_input_observations_are_retained() {
    let key = ident("Same");
    let params = [
        simple(TypeExpr::Map {
            key: Box::new(TypeExpr::Base(key.clone())),
            value: Box::new(TypeExpr::Base(key.clone())),
        }),
        optional(vec![simple(base("Same")), simple(base("Same"))]),
    ];
    let before = format!("{params:?}");
    assert_eq!(
        convert_term_context_to_items(&params),
        (vec![coll(CollectionType::HashMap, "Same", ","), nt("Same"), nt("Same")], vec![])
    );
    assert_eq!(format!("{params:?}"), before);
}

#[test]
fn original_optional_frame_loop_is_stack_safe_at_depth_four_thousand() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut param = simple(base("Leaf"));
            for _ in 0..4000 {
                param = optional(vec![param]);
            }
            assert_eq!(convert_term_context_to_items(&[param]), (vec![nt("Leaf")], vec![]));
        })
        .expect("small-stack original converter thread starts")
        .join()
        .expect("original optional frame loop stays on the heap");
}
