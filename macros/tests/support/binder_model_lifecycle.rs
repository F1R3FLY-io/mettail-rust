use super::{
    classify_binder_in, classify_optional_body, emit_binder_list_loop_body,
    emit_nested_optional_action, emit_optional_group_body, first_param_cat_from_positions,
    traversal_sites, ActionArgKind, BinderPosition, ParamKind, TraversalMarkerCoordinate,
    TraversalMarkerTable, TraversalResume,
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
    let markers = TraversalMarkerTable::build(&language, &per_cat);
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
    let markers = TraversalMarkerTable::build(&language, &per_cat);
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
    let table = TraversalMarkerTable::build(&language, &per_cat);
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
            let mut params = HashMap::new();
            params.insert("x".to_string(), ParamKind::Simple { cat: "Expr".to_string() });
            let mut next_group_idx = 0;
            let mut collection_slots = 0;
            let (positions, args) = classify_optional_body(
                &root,
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
