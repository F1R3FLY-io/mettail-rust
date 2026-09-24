use super::{
    build_traversal_marker_table, classify_binder_in, classify_optional_body,
    emit_binder_list_loop_body, emit_nested_optional_action, emit_optional_group_body,
    first_param_cat_from_positions, traversal_sites, ActionArgKind, BinderPosition, ParamKind,
    TraversalMarkerCoordinate, TraversalResume,
};
use mettail_ast::grammar::{rule_fixture, GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::{LangType, LanguageDef};
use mettail_ast::types::CollectionType;
use mettail_ast::types::TypeExpr;
use proc_macro2::Span;
use std::collections::{HashMap, HashSet};
use syn::Ident;

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

#[test]
fn binder_codegen_models_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("binder-model-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut position = BinderPosition::ParamParse {
                cat: "Expr".to_string(),
                collection: None,
            };
            let mut action = ActionArgKind::Term("Expr".to_string());
            for depth in 0..DEPTH {
                if depth % 2 == 0 {
                    position = BinderPosition::OptionalGroup {
                        positions: vec![position],
                        group_idx: 0,
                        first_token_set: vec!["x".to_string()],
                    };
                } else {
                    position = BinderPosition::BinderListLoop {
                        separator: ",".to_string(),
                        close: ")".to_string(),
                        inner_positions: vec![position],
                        collection_param_cat: None,
                        allow_empty: true,
                        allow_multi: true,
                        slot_idx: 0,
                    };
                }
                action = ActionArgKind::Optional(vec![action]);
            }

            let sites = traversal_sites(std::slice::from_ref(&position));
            assert_eq!(sites.binder_lists.len(), DEPTH / 2);
            assert_eq!(sites.optionals.len(), DEPTH / 2);
            assert_eq!(sites.binder_frame_indices.len(), DEPTH / 2);
            assert_eq!(sites.binder_lists.first().map(|site| site.frame_idx), Some(0));
            assert_eq!(
                sites.binder_lists.last().map(|site| site.frame_idx),
                Some((DEPTH / 2 - 1) as u32)
            );

            assert_eq!(
                first_param_cat_from_positions(std::slice::from_ref(&position)),
                Some("Expr")
            );
            let position_clone = position.clone();
            let action_clone = action.clone();
            assert_eq!(format!("{position:?}"), format!("{position_clone:?}"));
            assert_eq!(format!("{action:?}"), format!("{action_clone:?}"));

            drop(sites);
            drop(position_clone);
            drop(position);
            drop(action_clone);
            drop(action);
        })
        .expect("spawn binder-model small-stack gate")
        .join()
        .expect("binder-model small-stack gate panicked");
}

#[test]
fn nested_binder_and_optional_sites_preserve_typed_continuations() {
    let positions = vec![BinderPosition::OptionalGroup {
        positions: vec![BinderPosition::BinderListLoop {
            separator: ",".to_string(),
            close: ")".to_string(),
            inner_positions: vec![
                BinderPosition::OptionalGroup {
                    positions: vec![BinderPosition::BinderListLoop {
                        separator: ";".to_string(),
                        close: "]".to_string(),
                        inner_positions: vec![BinderPosition::BinderIdent],
                        collection_param_cat: None,
                        allow_empty: true,
                        allow_multi: true,
                        slot_idx: 0,
                    }],
                    group_idx: 1,
                    first_token_set: vec!["[".to_string()],
                },
                BinderPosition::BinderListLoop {
                    separator: "|".to_string(),
                    close: "}".to_string(),
                    inner_positions: vec![BinderPosition::BinderIdent],
                    collection_param_cat: Some("Name".to_string()),
                    allow_empty: true,
                    allow_multi: true,
                    slot_idx: 1,
                },
            ],
            collection_param_cat: Some("Name".to_string()),
            allow_empty: true,
            allow_multi: true,
            slot_idx: 0,
        }],
        group_idx: 0,
        first_token_set: vec!["(".to_string()],
    }];

    let sites = traversal_sites(&positions);
    assert_eq!(sites.optionals.len(), 2);
    assert_eq!(sites.binder_lists.len(), 3);
    assert_eq!(
        sites
            .binder_lists
            .iter()
            .map(|site| site.frame_idx)
            .collect::<Vec<_>>(),
        vec![0, 1, 2]
    );
    assert!(matches!(
        sites.binder_lists[0].resume,
        TraversalResume::Optional { group_idx: 0, next_sub_pos: 2 }
    ));
    assert!(matches!(
        sites.optionals[1].resume,
        TraversalResume::BinderList { frame_idx: 0, next_sub_pos: 2 }
    ));
    assert!(matches!(
        sites.binder_lists[1].resume,
        TraversalResume::Optional { group_idx: 1, next_sub_pos: 2 }
    ));
    assert!(matches!(
        sites.binder_lists[2].resume,
        TraversalResume::BinderList { frame_idx: 0, next_sub_pos: 0 }
    ));
}

#[test]
fn binder_codegen_model_debug_preserves_compact_contracts() {
    let position = BinderPosition::OptionalGroup {
        positions: vec![BinderPosition::BinderListLoop {
            separator: ",".to_string(),
            close: ")".to_string(),
            inner_positions: vec![BinderPosition::BinderIdent],
            collection_param_cat: Some("Name".to_string()),
            allow_empty: false,
            allow_multi: true,
            slot_idx: 2,
        }],
        group_idx: 3,
        first_token_set: vec!["new".to_string()],
    };
    assert_eq!(
        format!("{position:?}"),
        "OptionalGroup { positions: [BinderListLoop { separator: \",\", close: \")\", inner_positions: [BinderIdent], collection_param_cat: Some(\"Name\"), allow_empty: false, allow_multi: true, slot_idx: 2 }], group_idx: 3, first_token_set: [\"new\"] }"
    );

    let action = ActionArgKind::Optional(vec![
        ActionArgKind::TokenText { param_name: "name".to_string() },
        ActionArgKind::Optional(vec![ActionArgKind::Term("Expr".to_string())]),
    ]);
    assert_eq!(
        format!("{action:?}"),
        "Optional([TokenText { param_name: \"name\" }, Optional([Term(\"Expr\")])])"
    );
}

#[test]
fn nested_optional_action_codegen_is_flat_and_preserves_leaf_order() {
    let inner = vec![
        ActionArgKind::TokenText { param_name: "tag".to_string() },
        ActionArgKind::Optional(vec![
            ActionArgKind::Term("Expr".to_string()),
            ActionArgKind::CollectionDrain {
                elem_cat: "Expr".to_string(),
                coll_kind: CollectionType::Vec,
            },
        ]),
        ActionArgKind::Predicate,
    ];

    let emitted = emit_nested_optional_action(7, &inner);
    assert_eq!(emitted.fields.len(), 4);
    assert_eq!(emitted.collection_drains.len(), 1);
    assert!(emitted.collection_drains[0].optional);

    let tokens = emitted.extract.to_string();
    assert!(tokens.contains("opt_7"));
    assert!(tokens.contains("nested_opt_7_1"));
    assert!(tokens.contains("nested_7_2"));
    assert!(tokens.contains("nested_7_3_id"));
    assert!(!tokens.contains("let nested_7_1 : ()"));

    let fields: Vec<String> = emitted
        .fields
        .into_iter()
        .map(|field| field.to_string())
        .collect();
    assert_eq!(fields, ["nested_7_0", "nested_7_2", "nested_7_3", "nested_7_4"]);
}

#[test]
fn nested_optional_action_codegen_is_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("nested-optional-action-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut action = ActionArgKind::Term("Expr".to_string());
            for _ in 0..DEPTH {
                action = ActionArgKind::Optional(vec![action]);
            }

            let emitted = emit_nested_optional_action(0, std::slice::from_ref(&action));
            assert_eq!(emitted.fields.len(), 1);
            assert!(emitted.collection_drains.is_empty());

            drop(emitted);
            drop(action);
        })
        .expect("spawn nested optional action small-stack gate")
        .join()
        .expect("nested optional action small-stack gate panicked");
}

fn nested_optional_rule() -> GrammarRule {
    let a = Ident::new("a", Span::call_site());
    let b = Ident::new("b", Span::call_site());
    GrammarRule {
        term_context: Some(vec![TermParam::Optional {
            params: vec![
                TermParam::Simple {
                    name: a.clone(),
                    ty: TypeExpr::Base(Ident::new("Expr", Span::call_site())),
                },
                TermParam::Optional {
                    params: vec![TermParam::Simple {
                        name: b.clone(),
                        ty: TypeExpr::Base(Ident::new("Expr", Span::call_site())),
                    }],
                },
            ],
        }]),
        syntax_pattern: Some(vec![
            SyntaxExpr::Literal("nested".to_string()),
            SyntaxExpr::Op(PatternOp::Opt {
                inner: vec![
                    SyntaxExpr::Literal("a".to_string()),
                    SyntaxExpr::Param(a),
                    SyntaxExpr::Op(PatternOp::Opt {
                        inner: vec![SyntaxExpr::Literal("b".to_string()), SyntaxExpr::Param(b)],
                    }),
                ],
            }),
        ]),
        ..rule_fixture(
            Ident::new("Nested", Span::call_site()),
            Ident::new("Expr", Span::call_site()),
        )
    }
}

fn nested_optional_binder_rule() -> GrammarRule {
    let binders = Ident::new("xs", Span::call_site());
    let body = Ident::new("body", Span::call_site());
    GrammarRule {
        term_context: Some(vec![TermParam::Optional {
            params: vec![TermParam::MultiAbstraction {
                binder: binders.clone(),
                body: body.clone(),
                ty: TypeExpr::Arrow {
                    domain: Box::new(TypeExpr::Base(Ident::new("Expr", Span::call_site()))),
                    codomain: Box::new(TypeExpr::Base(Ident::new("Expr", Span::call_site()))),
                },
            }],
        }]),
        syntax_pattern: Some(vec![
            SyntaxExpr::Literal("maybe".to_string()),
            SyntaxExpr::Op(PatternOp::Opt {
                inner: vec![
                    SyntaxExpr::Literal("(".to_string()),
                    SyntaxExpr::Op(PatternOp::Sep {
                        collection: binders,
                        separator: ",".to_string(),
                        source: None,
                    }),
                    SyntaxExpr::Literal(")".to_string()),
                    SyntaxExpr::Literal(".".to_string()),
                    SyntaxExpr::Param(body),
                ],
            }),
        ]),
        ..rule_fixture(
            Ident::new("MaybeBind", Span::call_site()),
            Ident::new("Expr", Span::call_site()),
        )
    }
}

fn nested_optional_language(rule: GrammarRule) -> LanguageDef {
    LanguageDef {
        name: Ident::new("NestedOptional", Span::call_site()),
        options: Default::default(),
        extends_names: Vec::new(),
        include_names: Vec::new(),
        mixin_names: Vec::new(),
        types: vec![LangType {
            name: Ident::new("Expr", Span::call_site()),
            role: Default::default(),
            native_type: None,
            collection_kind: None,
        }],
        refinement_types: Vec::new(),
        token_defs: Vec::new(),
        mode_defs: Vec::new(),
        sync_constraints: Vec::new(),
        tree_invariants: Vec::new(),
        terms: vec![rule],
        equations: Vec::new(),
        rewrites: Vec::new(),
        logic: None,
        guard_config: None,
    }
}

#[test]
fn nested_optional_classifier_and_emitter_preserve_frame_identity() {
    let rule = nested_optional_rule();
    let language = nested_optional_language(rule.clone());
    let shape = classify_binder_in(&rule, &language).expect("nested optionals must classify");
    let BinderPosition::OptionalGroup { positions, group_idx, .. } = &shape.positions[0] else {
        panic!("outer optional group missing");
    };
    assert_eq!(*group_idx, 0);
    let BinderPosition::OptionalGroup { group_idx: nested_group_idx, .. } = &positions[2] else {
        panic!("nested optional group missing");
    };
    assert_eq!(*nested_group_idx, 1);
    assert!(matches!(
        &shape.action_args[0],
        ActionArgKind::Optional(inner)
            if matches!(&inner[1], ActionArgKind::Optional(nested) if nested.len() == 1)
    ));

    let per_cat = vec![vec![rule]];
    let markers = build_traversal_marker_table(&language, &per_cat);
    let tokens =
        emit_optional_group_body(&language, &["Expr".to_string()], &per_cat, &markers).to_string();
    assert!(tokens.contains("0u32 , 0u32"), "outer group entry arm missing");
    assert!(tokens.contains("1u32 , 0u32"), "nested group entry arm missing");
    assert!(tokens.contains("group_idx : 1u32"));
    assert!(tokens.contains("group_idx : 0u32"));
    assert!(tokens.contains("WpdaStepAction :: Advance"));
}

#[test]
fn binder_list_nested_in_optional_emits_shared_entry_and_loop_frames() {
    let rule = nested_optional_binder_rule();
    let language = nested_optional_language(rule.clone());
    let shape = classify_binder_in(&rule, &language).expect("nested binder list must classify");
    let BinderPosition::OptionalGroup { positions, group_idx, .. } = &shape.positions[0] else {
        panic!("outer optional group missing");
    };
    assert_eq!(*group_idx, 0);
    assert!(matches!(positions[1], BinderPosition::BinderListLoop { .. }));
    assert!(matches!(
        &shape.action_args[0],
        ActionArgKind::Optional(inner)
            if matches!(inner.as_slice(), [ActionArgKind::BinderList, ActionArgKind::Term(cat)] if cat == "Expr")
    ));

    let per_cat = vec![vec![rule]];
    let markers = build_traversal_marker_table(&language, &per_cat);
    let optional =
        emit_optional_group_body(&language, &["Expr".to_string()], &per_cat, &markers).to_string();
    assert!(optional.contains("frame_idx : 0u32"));
    assert!(optional.contains("group_idx : 0u32"));
    assert!(optional.contains("0u32 , 3u32"));

    let binder = emit_binder_list_loop_body(&language, &["Expr".to_string()], &per_cat, &markers)
        .to_string();
    assert!(binder.contains("0u32 , 0u32"));
    assert!(binder.contains("optional_group_at"));
    let optional_resume_id =
        markers.id(0, 0, TraversalMarkerCoordinate::Optional { group_idx: 0, sub_pos: 3 });
    assert!(
        binder.contains(&format!("optional_group_at ({optional_resume_id}u32")),
        "nested binder completion must carry the dense ID of optional group 0, subposition 3: \
         {binder}",
    );
}

#[test]
fn traversal_marker_ids_are_dense_unique_and_decode_to_their_coordinates() {
    let rule = nested_optional_binder_rule();
    let language = nested_optional_language(rule.clone());
    let per_cat = vec![vec![rule]];
    let table = build_traversal_marker_table(&language, &per_cat);
    let total = table.optional_metadata.len() + table.binder_metadata.len();

    assert!(total > 0, "fixture must produce traversal markers");
    assert_eq!(table.ids.len(), total, "every coordinate must have one marker ID");

    let mut seen = HashSet::with_capacity(total);
    for &(marker_id, result_src_idx, rule_idx, group_idx, sub_pos) in &table.optional_metadata {
        assert!(seen.insert(marker_id), "duplicate marker ID {marker_id}");
        assert_eq!(
            table.id(
                result_src_idx,
                rule_idx,
                TraversalMarkerCoordinate::Optional { group_idx, sub_pos },
            ),
            marker_id,
        );
    }
    for &(marker_id, result_src_idx, rule_idx, frame_idx, sub_pos) in &table.binder_metadata {
        assert!(seen.insert(marker_id), "duplicate marker ID {marker_id}");
        assert_eq!(
            table.id(
                result_src_idx,
                rule_idx,
                TraversalMarkerCoordinate::BinderList { frame_idx, sub_pos },
            ),
            marker_id,
        );
    }

    assert_eq!(seen.len(), total);
    assert!(
        (0..u32::try_from(total).expect("small fixture"))
            .all(|marker_id| seen.contains(&marker_id)),
        "marker IDs must form one dense range",
    );
}

#[test]
fn optional_classifier_is_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("optional-classifier-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let param = Ident::new("x", Span::call_site());
            let mut expression = SyntaxExpr::Param(param.clone());
            for _ in 0..DEPTH {
                expression = SyntaxExpr::Op(PatternOp::Opt { inner: vec![expression] });
            }
            let root = vec![expression];
            let language = nested_optional_language(nested_optional_rule());
            let mut params = HashMap::new();
            params.insert("x".to_string(), ParamKind::Simple { cat: "Expr".to_string() });
            let mut next_group_idx = 0;
            let mut collection_slots = 0;
            let (positions, args) = classify_optional_body(
                &root,
                &language,
                &params,
                None,
                &mut next_group_idx,
                &mut collection_slots,
            )
            .expect("20k optional syntax must classify");
            assert_eq!(next_group_idx as usize, DEPTH);
            assert_eq!(positions.len(), 1);
            assert_eq!(args.len(), 1);

            drop(positions);
            drop(args);
            drop(root);
        })
        .expect("spawn optional classifier small-stack gate")
        .join()
        .expect("optional classifier small-stack gate panicked");
}

#[test]
fn optional_projection_preserves_empty_and_refusal_counter_states() {
    let language = nested_optional_language(nested_optional_rule());
    let params = HashMap::new();
    let mut group = 17;
    let mut slot = 23;
    let empty = classify_optional_body(&[], &language, &params, None, &mut group, &mut slot)
        .expect("empty root sequence is accepted");
    assert!(empty.0.is_empty() && empty.1.is_empty());
    assert_eq!((group, slot), (17, 23));

    let empty_child = [SyntaxExpr::Op(PatternOp::Opt { inner: Vec::new() })];
    assert!(
        classify_optional_body(&empty_child, &language, &params, None, &mut group, &mut slot,)
            .is_none()
    );
    // The original classifier allocates the group identity before rejecting
    // the empty child; failure does not roll the caller's counter back.
    assert_eq!((group, slot), (18, 23));

    group = u32::MAX;
    assert!(
        classify_optional_body(&empty_child, &language, &params, None, &mut group, &mut slot,)
            .is_none()
    );
    assert_eq!((group, slot), (u32::MAX, 23));

    let unsupported = [
        SyntaxExpr::Op(PatternOp::Opt {
            inner: vec![SyntaxExpr::Literal("ready".to_string())],
        }),
        SyntaxExpr::Op(PatternOp::Var(Ident::new("unknown", Span::call_site()))),
    ];
    group = 41;
    assert!(
        classify_optional_body(&unsupported, &language, &params, None, &mut group, &mut slot,)
            .is_none()
    );
    assert_eq!((group, slot), (42, 23));
}

#[test]
fn optional_projection_preserves_capture_roles_and_order() {
    let language = nested_optional_language(nested_optional_rule());
    let mut params = HashMap::new();
    for (name, role) in [
        ("binder", ParamKind::Binder),
        ("ident", ParamKind::Simple { cat: "Ident".to_string() }),
        ("body_ident", ParamKind::Body { cat: "Ident".to_string() }),
        ("value", ParamKind::Simple { cat: "Expr".to_string() }),
        ("body", ParamKind::Body { cat: "Expr".to_string() }),
        ("guard", ParamKind::Guard),
    ] {
        params.insert(name.to_string(), role);
    }
    let ident = |name: &str| Ident::new(name, Span::call_site());
    let mut root = vec![
        SyntaxExpr::Literal("anchor".to_string()),
        SyntaxExpr::TokenKind { name: ident("Word"), bind: None },
        SyntaxExpr::TokenKind {
            name: ident("Word"),
            bind: Some(ident("named")),
        },
        SyntaxExpr::GuestBody {
            open: ident("Open"),
            close: ident("Close"),
            bind: ident("guest"),
            kind: mettail_ast::grammar::DelimitedRegionKind::Flt,
        },
    ];
    root.extend(
        ["binder", "ident", "body_ident", "value", "body", "guard"]
            .into_iter()
            .map(|name| SyntaxExpr::Param(ident(name))),
    );
    let mut group = 7;
    let mut slot = 9;
    let (positions, args) =
        classify_optional_body(&root, &language, &params, None, &mut group, &mut slot)
            .expect("all original supported capture roles");
    assert_eq!((group, slot), (7, 9));
    assert_eq!(positions.len(), 10);
    assert_eq!(args.len(), 9);
    assert!(matches!(&positions[0], BinderPosition::Literal(text) if text == "anchor"));
    assert!(
        matches!(&positions[1], BinderPosition::TokenKindCapture { kind_name, param_name }
        if kind_name == "Word" && param_name == "__tok_Word")
    );
    assert!(
        matches!(&positions[2], BinderPosition::TokenKindCapture { kind_name, param_name }
        if kind_name == "Word" && param_name == "named")
    );
    assert!(matches!(&positions[3], BinderPosition::GuestBodyCapture {
        open_kind, nested_open_kinds, close_kind, param_name
    } if open_kind == "Open" && nested_open_kinds.is_empty()
        && close_kind == "Close" && param_name == "guest"));
    assert!(matches!(&positions[4], BinderPosition::BinderListLoop {
        separator, close, inner_positions, collection_param_cat,
        allow_empty: false, allow_multi: false, slot_idx: 0
    } if separator.is_empty() && close.is_empty() && collection_param_cat.is_none()
        && matches!(inner_positions.as_slice(), [BinderPosition::BinderIdent])));
    assert!(matches!(&positions[5], BinderPosition::IdentTextCapture { param_name }
        if param_name == "ident"));
    assert!(matches!(&positions[6], BinderPosition::IdentTextCapture { param_name }
        if param_name == "body_ident"));
    for position in &positions[7..9] {
        assert!(matches!(position, BinderPosition::ParamParse { cat, collection: None }
            if cat == "Expr"));
    }
    assert!(matches!(&positions[9], BinderPosition::GuardSlot));
    assert_eq!(format!("{args:?}"),
        "[TokenText { param_name: \"__tok_Word\" }, TokenText { param_name: \"named\" }, GuestBody { param_name: \"guest\", kind: Flt }, BinderName, IdentText { param_name: \"ident\" }, IdentText { param_name: \"body_ident\" }, Term(\"Expr\"), Term(\"Expr\"), Predicate]");
}

#[test]
fn optional_projection_preserves_separator_gates_and_slot_failures() {
    let language = nested_optional_language(nested_optional_rule());
    let declared = mettail_ast::language::CollectionDelimiters {
        open: "[".to_string(),
        close: "]".to_string(),
        sep: ",".to_string(),
        key_val_sep: Some("=>".to_string()),
    };
    for kind in [
        CollectionType::Vec,
        CollectionType::HashBag,
        CollectionType::HashSet,
        CollectionType::HashMap,
        CollectionType::PathMap,
    ] {
        let mut params = HashMap::new();
        params.insert(
            "xs".to_string(),
            ParamKind::SimpleCollection {
                elem_cat: "Expr".to_string(),
                coll_kind: kind.clone(),
            },
        );
        let sep = || {
            SyntaxExpr::Op(PatternOp::Sep {
                collection: Ident::new("xs", Span::call_site()),
                separator: ",".to_string(),
                source: None,
            })
        };
        let root = [
            sep(),
            SyntaxExpr::Literal("]".to_string()),
            SyntaxExpr::Literal("after".to_string()),
        ];
        let mut group = 3;
        let mut slot = 11;
        let (positions, args) = classify_optional_body(
            &root,
            &language,
            &params,
            Some(&declared),
            &mut group,
            &mut slot,
        )
        .expect("separator and its immediate literal close");
        assert_eq!((group, slot), (3, 12));
        assert_eq!(positions.len(), 2);
        assert!(matches!(&positions[1], BinderPosition::Literal(text) if text == "after"));
        let BinderPosition::ParamParse { cat, collection: Some(info) } = &positions[0] else {
            panic!("collection parsing position");
        };
        assert_eq!(cat, "Expr");
        assert_eq!(info.elem_cat, "Expr");
        assert_eq!(info.separator, ",");
        assert_eq!(info.close, "]");
        assert_eq!(info.slot_idx, 11);
        let expected_pair = match kind {
            CollectionType::HashMap | CollectionType::PathMap => Some("=>"),
            _ => None,
        };
        assert_eq!(info.key_val_separator.as_deref(), expected_pair);
        assert!(
            matches!(args.as_slice(), [ActionArgKind::CollectionDrain { elem_cat, coll_kind }]
            if elem_cat == "Expr" && coll_kind == &kind)
        );

        slot = u8::MAX;
        assert!(classify_optional_body(
            &root,
            &language,
            &params,
            Some(&declared),
            &mut group,
            &mut slot,
        )
        .is_none());
        assert_eq!((group, slot), (3, u8::MAX));
        for invalid in [
            vec![sep()],
            vec![sep(), SyntaxExpr::Param(Ident::new("xs", Span::call_site()))],
            vec![SyntaxExpr::Param(Ident::new("xs", Span::call_site()))],
            vec![
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: Ident::new("xs", Span::call_site()),
                    separator: ",".to_string(),
                    source: Some(Box::new(PatternOp::Var(Ident::new("xs", Span::call_site())))),
                }),
                SyntaxExpr::Literal("]".to_string()),
            ],
        ] {
            slot = 11;
            assert!(classify_optional_body(
                &invalid,
                &language,
                &params,
                Some(&declared),
                &mut group,
                &mut slot,
            )
            .is_none());
            assert_eq!((group, slot), (3, 11));
        }
    }

    let mut params = HashMap::new();
    params.insert("xs".to_string(), ParamKind::BinderList);
    let root = [
        SyntaxExpr::Op(PatternOp::Sep {
            collection: Ident::new("xs", Span::call_site()),
            separator: ";".to_string(),
            source: None,
        }),
        SyntaxExpr::Literal("end".to_string()),
    ];
    let mut group = 3;
    let mut slot = u8::MAX;
    let (positions, args) =
        classify_optional_body(&root, &language, &params, None, &mut group, &mut slot)
            .expect("binder-list separators do not allocate collection slots");
    assert_eq!((group, slot), (3, u8::MAX));
    assert!(matches!(positions.as_slice(), [BinderPosition::BinderListLoop {
        separator, close, inner_positions, collection_param_cat,
        allow_empty: true, allow_multi: true, slot_idx: 0
    }] if separator == ";" && close == "end" && collection_param_cat.is_none()
        && matches!(inner_positions.as_slice(), [BinderPosition::BinderIdent])));
    assert!(matches!(args.as_slice(), [ActionArgKind::BinderList]));
}
