//! Original macro classifier baselines, recorded before classifier extraction.
//! These deliberately pin observable acceptance, refusal, payloads and order,
//! including asymmetries that a later shared implementation must preserve.

use super::{classify_binder_in, ActionArgKind, BinderPosition, BinderShape, CollectionSepInfo};
use mettail_ast::grammar::{
    rule_fixture, DelimitedRegionKind, GrammarRule, PatternOp, SyntaxExpr, TermParam,
};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::Span;
use syn::Ident;

#[path = "binder_numeric_admission.rs"]
mod numeric_admission;

#[path = "owned_binder_reuse.rs"]
mod owned_binder_reuse;

fn id(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn base(name: &str) -> TypeExpr {
    TypeExpr::Base(id(name))
}

fn simple(name: &str, ty: TypeExpr) -> TermParam {
    TermParam::Simple { name: id(name), ty }
}

fn collection(kind: CollectionType, cat: &str) -> TypeExpr {
    TypeExpr::Collection {
        coll_type: kind,
        element: Box::new(base(cat)),
    }
}

fn abstraction(multi: bool, binder: &str, body: &str, cat: &str) -> TermParam {
    let ty = TypeExpr::Arrow {
        domain: Box::new(base("Name")),
        codomain: Box::new(base(cat)),
    };
    if multi {
        TermParam::MultiAbstraction { binder: id(binder), body: id(body), ty }
    } else {
        TermParam::Abstraction { binder: id(binder), body: id(body), ty }
    }
}

fn literal(text: &str) -> SyntaxExpr {
    SyntaxExpr::Literal(text.to_string())
}

fn param(name: &str) -> SyntaxExpr {
    SyntaxExpr::Param(id(name))
}

fn sep(name: &str) -> SyntaxExpr {
    SyntaxExpr::Op(PatternOp::Sep {
        collection: id(name),
        separator: ",".to_string(),
        source: None,
    })
}

fn token(bind: Option<&str>) -> SyntaxExpr {
    SyntaxExpr::TokenKind { name: id("Word"), bind: bind.map(id) }
}

fn guest() -> SyntaxExpr {
    SyntaxExpr::GuestBody {
        open: id("Open"),
        close: id("Close"),
        bind: id("guest"),
        kind: DelimitedRegionKind::Flt,
    }
}

fn rule(params: Vec<TermParam>, syntax: Vec<SyntaxExpr>) -> GrammarRule {
    GrammarRule {
        term_context: Some(params),
        syntax_pattern: Some(syntax),
        ..rule_fixture(id("Projection"), id("Expr"))
    }
}

fn language() -> LanguageDef {
    LanguageDef {
        name: id("ProjectionLanguage"),
        options: Default::default(),
        extends_names: Vec::new(),
        include_names: Vec::new(),
        mixin_names: Vec::new(),
        types: Vec::new(),
        refinement_types: Vec::new(),
        token_defs: Vec::new(),
        mode_defs: Vec::new(),
        sync_constraints: Vec::new(),
        tree_invariants: Vec::new(),
        terms: Vec::new(),
        equations: Vec::new(),
        rewrites: Vec::new(),
        logic: None,
        guard_config: None,
    }
}

fn shape(positions: Vec<BinderPosition>, action_args: Vec<ActionArgKind>) -> BinderShape {
    BinderShape {
        label: "Projection".to_string(),
        result_cat: "Expr".to_string(),
        leading_category: None,
        leading_ident_capture: None,
        positions,
        is_multi: false,
        has_binder: false,
        action_arity: u8::try_from(action_args.len()).expect("small baseline action arity"),
        action_args,
        body_cat: None,
        param_cats: Vec::new(),
    }
}

fn assert_shape(rule: &GrammarRule, expected: BinderShape) {
    let actual =
        classify_binder_in(rule, &language()).expect("original classifier accepts fixture");
    // The descriptor has a stack-safe Debug implementation, but no PartialEq.
    // Compare complete descriptors: every field and nested sequence is pinned.
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    let owned = owned_binder_reuse::classify_owned(rule, &language())
        .expect("owned classifier accepts the same fixture");
    assert_eq!(format!("{owned:?}"), format!("{expected:?}"));
}

fn assert_refuses(rule: &GrammarRule) {
    assert!(classify_binder_in(rule, &language()).is_none());
    assert!(owned_binder_reuse::classify_owned(rule, &language()).is_none());
}

fn term(cat: &str) -> BinderPosition {
    BinderPosition::ParamParse { cat: cat.to_string(), collection: None }
}

fn collection_position(
    cat: &str,
    close: &str,
    slot_idx: u8,
    key_val: Option<&str>,
) -> BinderPosition {
    BinderPosition::ParamParse {
        cat: cat.to_string(),
        collection: Some(CollectionSepInfo {
            separator: ",".to_string(),
            close: close.to_string(),
            elem_cat: cat.to_string(),
            key_val_separator: key_val.map(str::to_string),
            slot_idx,
        }),
    }
}

fn drain(cat: &str, kind: CollectionType) -> ActionArgKind {
    ActionArgKind::CollectionDrain {
        elem_cat: cat.to_string(),
        coll_kind: kind,
    }
}

#[test]
fn original_projection_distinguishes_absent_and_empty_contexts() {
    let accepted = rule(Vec::new(), vec![token(None)]);
    assert_shape(
        &accepted,
        shape(
            Vec::new(),
            vec![ActionArgKind::TokenText { param_name: "__tok_Word".to_string() }],
        ),
    );
    let mut absent_terms = accepted.clone();
    absent_terms.term_context = None;
    assert_refuses(&absent_terms);
    let mut absent_syntax = accepted.clone();
    absent_syntax.syntax_pattern = None;
    assert_refuses(&absent_syntax);
    for syntax in [Vec::new(), vec![literal("only")], vec![literal("a"), literal("b")]] {
        assert_refuses(&rule(Vec::new(), syntax));
    }
}

#[test]
fn original_projection_class5_exclusion_only_sees_sole_top_level_collection() {
    for syntax in [
        vec![literal("["), sep("xs"), literal("]")],
        vec![literal("list"), literal("("), sep("xs"), literal(")")],
    ] {
        let declaration = simple("xs", collection(CollectionType::Vec, "Name"));
        assert!(
            classify_binder_in(&rule(vec![declaration.clone()], syntax.clone()), &language())
                .is_none()
        );
        let close = if syntax.len() == 3 { "]" } else { ")" };
        let mut positions = Vec::new();
        if syntax.len() == 4 {
            positions.push(BinderPosition::Literal("(".to_string()));
        }
        positions.push(collection_position("Name", close, 0, None));
        let mut expected = shape(positions, vec![drain("Name", CollectionType::Vec)]);
        expected.param_cats = vec!["Name".to_string()];
        assert_shape(
            &rule(vec![TermParam::Optional { params: vec![declaration] }], syntax),
            expected,
        );
    }
    // Map(K,V) is a separate AST variant and is not in the Class-5 exclusion.
    let map = TypeExpr::Map {
        key: Box::new(base("Name")),
        value: Box::new(base("Name")),
    };
    let mut expected = shape(
        vec![collection_position("Name", "]", 0, Some(":"))],
        vec![drain("Name", CollectionType::HashMap)],
    );
    expected.param_cats = vec!["Name".to_string()];
    assert_shape(
        &rule(vec![simple("xs", map)], vec![literal("["), sep("xs"), literal("]")]),
        expected,
    );
}

#[test]
fn original_projection_duplicate_declarations_use_last_role_and_last_body_category() {
    let fixture = rule(
        vec![
            simple("value", base("Before")),
            abstraction(true, "xs", "body", "OldBody"),
            TermParam::Optional {
                params: vec![
                    simple("value", base("After")),
                    abstraction(false, "x", "body", "NewBody"),
                ],
            },
            TermParam::GuardBody { name: id("value") },
        ],
        vec![
            literal("start"),
            param("body"),
            param("value"),
            param("x"),
            sep("xs"),
            literal("end"),
        ],
    );
    let mut expected = shape(
        vec![
            term("NewBody"),
            BinderPosition::GuardSlot,
            BinderPosition::BinderListLoop {
                separator: String::new(),
                close: String::new(),
                inner_positions: vec![BinderPosition::BinderIdent],
                collection_param_cat: None,
                allow_empty: false,
                allow_multi: false,
                slot_idx: 0,
            },
            BinderPosition::BinderListLoop {
                separator: ",".to_string(),
                close: "end".to_string(),
                inner_positions: vec![BinderPosition::BinderIdent],
                collection_param_cat: None,
                allow_empty: true,
                allow_multi: true,
                slot_idx: 0,
            },
        ],
        vec![
            ActionArgKind::Term("NewBody".to_string()),
            ActionArgKind::Predicate,
            ActionArgKind::BinderName,
            ActionArgKind::BinderList,
        ],
    );
    expected.param_cats = vec!["Before".to_string(), "After".to_string()];
    expected.body_cat = Some("NewBody".to_string());
    expected.has_binder = true;
    expected.is_multi = true;
    assert_shape(&fixture, expected);
}

#[test]
fn original_projection_leading_roles_and_capture_only_exceptions() {
    let mut ident_expected =
        shape(Vec::new(), vec![ActionArgKind::TokenText { param_name: "name".to_string() }]);
    ident_expected.leading_ident_capture = Some("name".to_string());
    ident_expected.param_cats = vec!["Ident".to_string()];
    assert_shape(&rule(vec![simple("name", base("Ident"))], vec![param("name")]), ident_expected);
    assert!(classify_binder_in(
        &rule(
            vec![abstraction(false, "x", "body", "Ident")],
            vec![param("body"), literal("end")]
        ),
        &language()
    )
    .is_none());

    let category_only = rule(vec![simple("value", base("Name"))], vec![param("value")]);
    assert!(classify_binder_in(&category_only, &language()).is_none());
    let mut category_then_literal = category_only;
    category_then_literal
        .syntax_pattern
        .as_mut()
        .expect("syntax")
        .push(literal("end"));
    let mut expected = shape(
        vec![BinderPosition::Literal("end".to_string())],
        vec![ActionArgKind::Term("Name".to_string())],
    );
    expected.leading_category = Some("Name".to_string());
    expected.param_cats = vec!["Name".to_string()];
    assert_shape(&category_then_literal, expected);
    assert_shape(
        &rule(Vec::new(), vec![token(Some("word"))]),
        shape(Vec::new(), vec![ActionArgKind::TokenText { param_name: "word".to_string() }]),
    );
    assert_shape(
        &rule(Vec::new(), vec![guest()]),
        shape(
            Vec::new(),
            vec![ActionArgKind::GuestBody {
                param_name: "guest".to_string(),
                kind: DelimitedRegionKind::Flt,
            }],
        ),
    );
}

#[test]
fn original_projection_rejects_unsupported_types_even_when_unused() {
    let arrow = || TypeExpr::Arrow {
        domain: Box::new(base("Name")),
        codomain: Box::new(base("Expr")),
    };
    for ty in [
        arrow(),
        TypeExpr::MultiBinder(Box::new(base("Name"))),
        TypeExpr::Refined {
            var: id("n"),
            base: Box::new(base("Name")),
            predicate_repr: "true".to_string(),
        },
        collection(CollectionType::PathMap, "Name"),
        TypeExpr::Collection {
            coll_type: CollectionType::Vec,
            element: Box::new(arrow()),
        },
        TypeExpr::Map {
            key: Box::new(base("Name")),
            value: Box::new(base("Expr")),
        },
        TypeExpr::Map {
            key: Box::new(arrow()),
            value: Box::new(arrow()),
        },
    ] {
        assert!(classify_binder_in(
            &rule(vec![simple("unused", ty)], vec![token(None)]),
            &language()
        )
        .is_none());
    }
    for multi in [false, true] {
        for ty in [
            base("Expr"),
            TypeExpr::Arrow {
                domain: Box::new(base("Name")),
                codomain: Box::new(collection(CollectionType::Vec, "Expr")),
            },
        ] {
            let declaration = if multi {
                TermParam::MultiAbstraction { binder: id("xs"), body: id("body"), ty }
            } else {
                TermParam::Abstraction { binder: id("x"), body: id("body"), ty }
            };
            assert!(classify_binder_in(&rule(vec![declaration], vec![token(None)]), &language())
                .is_none());
        }
    }
}

#[test]
fn original_projection_rejects_unsupported_operation_positions_and_param_roles() {
    let declarations = vec![
        simple("value", base("Name")),
        simple("names", collection(CollectionType::Vec, "Name")),
        abstraction(false, "x", "single_body", "Expr"),
        abstraction(true, "xs", "body", "Expr"),
        TermParam::GuardBody { name: id("guard") },
    ];
    for syntax in [
        vec![sep("names"), literal("end")],
        vec![SyntaxExpr::Op(PatternOp::Opt { inner: vec![token(None)] })],
        vec![literal("start"), SyntaxExpr::Op(PatternOp::Var(id("names")))],
        vec![
            literal("start"),
            SyntaxExpr::Op(PatternOp::Zip { left: id("names"), right: id("xs") }),
        ],
        vec![
            literal("start"),
            SyntaxExpr::Op(PatternOp::Map {
                source: Box::new(PatternOp::Var(id("names"))),
                params: vec![id("n")],
                body: vec![param("n")],
            }),
        ],
        vec![literal("start"), SyntaxExpr::Op(PatternOp::Opt { inner: Vec::new() })],
        vec![literal("start"), param("missing")],
        vec![param("missing"), literal("end")],
        vec![literal("start"), sep("xs")],
        vec![literal("start"), sep("xs"), token(None)],
    ] {
        assert!(classify_binder_in(&rule(declarations.clone(), syntax), &language()).is_none());
    }
    for name in ["names", "xs", "x", "guard"] {
        assert!(classify_binder_in(
            &rule(declarations.clone(), vec![param(name), literal("end")]),
            &language()
        )
        .is_none());
    }
    for name in ["names", "xs"] {
        assert!(classify_binder_in(
            &rule(declarations.clone(), vec![literal("start"), param(name)]),
            &language()
        )
        .is_none());
    }
    for name in ["value", "single_body", "x", "guard", "missing"] {
        assert!(classify_binder_in(
            &rule(declarations.clone(), vec![literal("start"), sep(name), literal("end")]),
            &language()
        )
        .is_none());
    }
}

#[test]
fn original_projection_main_collection_is_open_ended_but_optional_requires_literal_close() {
    let declarations = vec![
        simple("names", collection(CollectionType::Vec, "Name")),
        simple("body", base("Expr")),
    ];
    for tail in [Vec::new(), vec![param("body")], vec![literal("]"), param("body")]] {
        let mut syntax = vec![literal("start"), sep("names")];
        syntax.extend(tail.clone());
        let close = if matches!(tail.first(), Some(SyntaxExpr::Literal(_))) {
            "]"
        } else {
            ""
        };
        let mut positions = vec![collection_position("Name", close, 0, None)];
        let mut args = vec![drain("Name", CollectionType::Vec)];
        if !tail.is_empty() {
            positions.push(term("Expr"));
            args.push(ActionArgKind::Term("Expr".to_string()));
        }
        let mut expected = shape(positions, args);
        expected.param_cats = vec!["Name".to_string(), "Expr".to_string()];
        assert_shape(&rule(declarations.clone(), syntax), expected);
        let mut inner = vec![sep("names")];
        inner.extend(tail);
        let optional_rule = rule(
            declarations.clone(),
            vec![literal("start"), SyntaxExpr::Op(PatternOp::Opt { inner })],
        );
        if close.is_empty() {
            assert_refuses(&optional_rule);
        } else {
            let mut expected = shape(
                vec![BinderPosition::OptionalGroup {
                    positions: vec![collection_position("Name", "]", 0, None), term("Expr")],
                    group_idx: 0,
                    first_token_set: Vec::new(),
                }],
                vec![ActionArgKind::Optional(vec![
                    drain("Name", CollectionType::Vec),
                    ActionArgKind::Term("Expr".to_string()),
                ])],
            );
            expected.param_cats = vec!["Name".to_string(), "Expr".to_string()];
            assert_shape(&optional_rule, expected);
        }
    }
}

fn mapped_sep(left: &str, right: &str, aliases: &[&str], body: Vec<SyntaxExpr>) -> SyntaxExpr {
    SyntaxExpr::Op(PatternOp::Sep {
        collection: id("ignored"),
        separator: ",".to_string(),
        source: Some(Box::new(PatternOp::Map {
            source: Box::new(PatternOp::Zip { left: id(left), right: id(right) }),
            params: aliases.iter().map(|name| id(name)).collect(),
            body,
        })),
    })
}

#[test]
fn original_projection_zip_map_sep_preserves_slot_payloads_and_drain_order() {
    // Reverse binder/name syntax order and use a non-Vec declaration: the
    // original still emits the synthesized Vec drain before the binder list.
    let fixture = rule(
        vec![
            simple("prefix", collection(CollectionType::Vec, "Expr")),
            abstraction(true, "xs", "body", "Expr"),
            simple("names", collection(CollectionType::HashSet, "Name")),
        ],
        vec![
            literal("start"),
            sep("prefix"),
            literal(";"),
            mapped_sep("names", "xs", &["n", "x"], vec![param("x"), literal("?"), param("n")]),
            literal(")"),
            param("body"),
        ],
    );
    let mut expected = shape(
        vec![
            collection_position("Expr", ";", 0, None),
            BinderPosition::BinderListLoop {
                separator: ",".to_string(),
                close: ")".to_string(),
                inner_positions: vec![
                    BinderPosition::BinderIdent,
                    BinderPosition::Literal("?".to_string()),
                    collection_position("Name", ")", 0, None),
                ],
                collection_param_cat: Some("Name".to_string()),
                allow_empty: true,
                allow_multi: true,
                slot_idx: 1,
            },
            term("Expr"),
        ],
        vec![
            drain("Expr", CollectionType::Vec),
            drain("Name", CollectionType::Vec),
            ActionArgKind::BinderList,
            ActionArgKind::Term("Expr".to_string()),
        ],
    );
    expected.is_multi = true;
    expected.has_binder = true;
    expected.body_cat = Some("Expr".to_string());
    expected.param_cats = vec!["Expr".to_string(), "Name".to_string()];
    assert_shape(&fixture, expected);
}

#[test]
fn original_projection_zip_map_sep_refusal_gates() {
    let declarations = vec![
        simple("names", collection(CollectionType::Vec, "Name")),
        abstraction(true, "xs", "body", "Expr"),
        simple("plain", base("Name")),
    ];
    for (left, right, aliases, body) in [
        ("names", "xs", vec!["n"], vec![param("n")]),
        ("names", "xs", vec!["n", "x", "z"], vec![param("x")]),
        ("plain", "xs", vec!["n", "x"], vec![param("x")]),
        ("names", "plain", vec!["n", "x"], vec![param("x")]),
        ("xs", "names", vec!["n", "x"], vec![param("x")]),
        ("missing", "xs", vec!["n", "x"], vec![param("x")]),
        ("names", "missing", vec!["n", "x"], vec![param("x")]),
        ("names", "xs", vec!["n", "x"], Vec::new()),
        ("names", "xs", vec!["n", "x"], vec![literal("no_binder"), param("n")]),
        ("names", "xs", vec!["same", "same"], vec![param("same")]),
        ("names", "xs", vec!["n", "x"], vec![param("x"), param("unknown")]),
        ("names", "xs", vec!["n", "x"], vec![param("x"), token(None)]),
        ("names", "xs", vec!["n", "x"], vec![param("x"), guest()]),
        (
            "names",
            "xs",
            vec!["n", "x"],
            vec![param("x"), SyntaxExpr::Op(PatternOp::Opt { inner: vec![literal("opt")] })],
        ),
    ] {
        assert!(classify_binder_in(
            &rule(
                declarations.clone(),
                vec![literal("start"), mapped_sep(left, right, &aliases, body), literal(")")]
            ),
            &language()
        )
        .is_none());
    }
    for tail in [Vec::new(), vec![param("body")], vec![token(None)]] {
        let mut syntax =
            vec![literal("start"), mapped_sep("names", "xs", &["n", "x"], vec![param("x")])];
        syntax.extend(tail);
        assert!(classify_binder_in(&rule(declarations.clone(), syntax), &language()).is_none());
    }
    for source in [
        PatternOp::Var(id("names")),
        PatternOp::Zip { left: id("names"), right: id("xs") },
        PatternOp::Map {
            source: Box::new(PatternOp::Var(id("names"))),
            params: vec![id("n"), id("x")],
            body: vec![param("x")],
        },
    ] {
        let syntax = vec![
            literal("start"),
            SyntaxExpr::Op(PatternOp::Sep {
                collection: id("ignored"),
                separator: ",".to_string(),
                source: Some(Box::new(source)),
            }),
            literal(")"),
        ];
        assert!(classify_binder_in(&rule(declarations.clone(), syntax), &language()).is_none());
    }
    // The gate requires a binder occurrence, but does not require a name occurrence.
    let mut expected = shape(
        vec![BinderPosition::BinderListLoop {
            separator: ",".to_string(),
            close: ")".to_string(),
            inner_positions: vec![BinderPosition::BinderIdent],
            collection_param_cat: Some("Name".to_string()),
            allow_empty: true,
            allow_multi: true,
            slot_idx: 0,
        }],
        vec![drain("Name", CollectionType::Vec), ActionArgKind::BinderList],
    );
    expected.is_multi = true;
    expected.has_binder = true;
    expected.body_cat = Some("Expr".to_string());
    expected.param_cats = vec!["Name".to_string(), "Name".to_string()];
    assert_shape(
        &rule(
            declarations,
            vec![
                literal("start"),
                mapped_sep("names", "xs", &["n", "x"], vec![param("x")]),
                literal(")"),
            ],
        ),
        expected,
    );
}
