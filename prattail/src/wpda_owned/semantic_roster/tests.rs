use super::*;
use mettail_grammar_core as core;

fn intern_name(
    store: &mut AuthoredRuleStore,
    names: &mut BTreeMap<String, AuthoredNameId>,
    text: &str,
) -> AuthoredNameId {
    if let Some(&name) = names.get(text) {
        return name;
    }
    let name = AuthoredNameId(
        store
            .try_push(AuthoredNode::Name(core::AuthoredName {
                spelling: text.into(),
                equality_class: u32::try_from(names.len()).expect("fixture name count fits"),
            }))
            .expect("fixture name is valid"),
    );
    names.insert(text.into(), name);
    name
}

fn fixture() -> core::GrammarCoreV1 {
    let mut grammar = core::GrammarCoreV1::new("SemanticRoster");
    grammar.categories = vec![
        core::Category {
            id: CategoryId(0),
            name: "Expr".into(),
            carrier: core::Carrier::Dynamic,
            primary: true,
            admits_variables: true,
        },
        core::Category {
            id: CategoryId(1),
            name: "Text".into(),
            carrier: core::Carrier::Builtin(core::BuiltinCarrier::String),
            primary: false,
            admits_variables: false,
        },
    ];
    let mut store = AuthoredRuleStore::new();
    let mut names = BTreeMap::new();
    let expr = intern_name(&mut store, &mut names, "Expr");
    let text = intern_name(&mut store, &mut names, "Text");
    let expr_ty = core::AuthoredTypeId(
        store
            .try_push(AuthoredNode::Type(AuthoredType::Base(expr)))
            .expect("Expr type"),
    );
    let text_ty = core::AuthoredTypeId(
        store
            .try_push(AuthoredNode::Type(AuthoredType::Base(text)))
            .expect("Text type"),
    );
    let list_ty = core::AuthoredTypeId(
        store
            .try_push(AuthoredNode::Type(AuthoredType::Collection {
                kind: CollectionKind::List,
                element: text_ty,
            }))
            .expect("List(Text) type"),
    );
    for (index, (label, constructor, shape)) in
        [("Leaf", 70, 0), ("Project", 9, 1), ("Pair", 81, 2), ("Pieces", 4, 3)]
            .into_iter()
            .enumerate()
    {
        let label = intern_name(&mut store, &mut names, label);
        let inputs = match shape {
            0 => vec![],
            1 => vec![("text", text_ty, CategoryId(1), false)],
            2 => vec![
                ("left", expr_ty, CategoryId(0), false),
                ("right", text_ty, CategoryId(1), false),
            ],
            _ => vec![("pieces", list_ty, CategoryId(1), true)],
        };
        let mut params = Vec::new();
        let mut source_syntax = Vec::new();
        let mut syntax = Vec::new();
        for (slot, ty, category, list) in &inputs {
            let parameter = intern_name(&mut store, &mut names, slot);
            params.push(core::AuthoredParamId(
                store
                    .try_push(AuthoredNode::Param(AuthoredParam::Simple {
                        name: parameter,
                        ty: *ty,
                    }))
                    .expect("plain source parameter"),
            ));
            source_syntax.push(AuthoredSyntax::Param(parameter));
            syntax.push(if *list {
                SyntaxItem::Separated {
                    source: Box::new(SyntaxItem::Collection {
                        slot: (*slot).into(),
                        key: None,
                        element: *category,
                        separator: String::new(),
                        kind: CollectionKind::List,
                        key_value_separator: None,
                    }),
                    separator: "::".into(),
                }
            } else {
                SyntaxItem::Category {
                    category: *category,
                    slot: (*slot).into(),
                }
            });
        }
        if shape != 1 {
            source_syntax.insert(0, AuthoredSyntax::Literal("keyword".into()));
        }
        let params = core::AuthoredParamsId(
            store
                .try_push(AuthoredNode::Params(params))
                .expect("source context"),
        );
        let source_syntax = core::AuthoredSyntaxId(
            store
                .try_push(AuthoredNode::Syntax(source_syntax))
                .expect("source syntax"),
        );
        let authored = core::AuthoredRuleId(
            store
                .try_push(AuthoredNode::Rule(AuthoredRule {
                    label,
                    category: expr,
                    source_body_present: SourceObservation::Known(false),
                    explicit_fold: SourceObservation::Known(false),
                    term_context: Some(params),
                    syntax_pattern: Some(source_syntax),
                    items: Vec::new(),
                }))
                .expect("authored constructor"),
        );
        grammar.productions.push(core::Production {
            id: core::ProductionId(index as u32),
            constructor: ConstructorId(constructor),
            label: name(&store, label).expect("source label").into(),
            result: CategoryId(0),
            authored: Some(authored),
            syntax,
            precedence: core::Precedence::default(),
            classification: core::ProductionClass::default(),
            reduction: index as u32,
            provenance: None,
        });
        grammar.reductions.push(core::ReductionPlan {
            output_category: CategoryId(0),
            constructor: ConstructorId(constructor),
            input_arity: inputs.len() as u16,
            fields: (0..inputs.len())
                .map(|input| FieldSource::Input(input as u16))
                .collect(),
            evaluation: None,
            evaluation_mode: None,
            tier: None,
        });
    }
    grammar.authored = Some(
        store
            .with_declarations(core::AuthoredDeclarations {
                categories: [(expr, None), (text, Some(NativeKind::Str))]
                    .into_iter()
                    .map(|(name, native)| core::AuthoredCategoryDeclaration {
                        name,
                        native,
                        collection: None,
                        data_observation: SourceObservation::Known(false),
                        byte_observation: SourceObservation::Known(false),
                        literal_observation: SourceObservation::Known(native.map(|_| {
                            core::LiteralNativeObservation::ExactNativeType(core::NativeType::Str)
                        })),
                        element_observation: SourceObservation::Known(None),
                    })
                    .collect(),
                tokens: Vec::new(),
                global_tokens: Vec::new(),
                modes: Vec::new(),
            })
            .expect("retained source header"),
    );
    grammar.authored_bindings = Some(core::AuthoredDeclarationBindings {
        categories: vec![CategoryId(0), CategoryId(1)],
        tokens: Vec::new(),
        modes: Vec::new(),
    });
    grammar
}

#[test]
fn roster_uses_source_occurrence_order_not_constructor_ids_or_wpda_coordinates() {
    let grammar = fixture();
    let roster = derive_roster(&grammar, &[2, 0, 1, 3], &[CategoryId(1), CategoryId(0)])
        .expect("simple original constructor observations");
    for (constructor, tag) in [(81, 0), (70, 1), (9, 2), (4, 3)] {
        assert_eq!(
            roster.constructors[&(CategoryId(0), ConstructorId(constructor))].local_tag,
            tag
        );
    }
    let text = &roster.categories[0];
    assert_eq!(text.category, CategoryId(1));
    assert!(
        text.variable,
        "source non-data Var occupies its original AST slot even when Core variables are forbidden"
    );
    assert_eq!(text.literal_tag, Some(1));
    assert!(!grammar.categories[1].admits_variables);
    let project = &roster.constructors[&(CategoryId(0), ConstructorId(9))];
    assert!(project.transparent);
    assert_eq!(
        project.fields,
        [SemanticField {
            category: CategoryId(1),
            kind: SemanticFieldKind::Term
        }]
    );
    let pair = &roster.constructors[&(CategoryId(0), ConstructorId(81))];
    assert!(!pair.transparent);
    assert_eq!(
        pair.fields,
        [
            SemanticField {
                category: CategoryId(0),
                kind: SemanticFieldKind::Term
            },
            SemanticField {
                category: CategoryId(1),
                kind: SemanticFieldKind::Term
            }
        ]
    );
    assert_eq!(
        roster.constructors[&(CategoryId(0), ConstructorId(4))].fields,
        [SemanticField {
            category: CategoryId(1),
            kind: SemanticFieldKind::OrderedList
        }]
    );
}

#[test]
fn roster_refuses_nonidentity_plans_mismatched_slots_and_ranked_transparency() {
    let categories = [CategoryId(0), CategoryId(1)];
    let occurrences = [0, 1, 2, 3];
    let mut reordered = fixture();
    reordered.reductions[2].fields.swap(0, 1);
    assert!(derive_roster(&reordered, &occurrences, &categories).is_none());
    let mut wrong_category = fixture();
    let SyntaxItem::Category { category, .. } = &mut wrong_category.productions[2].syntax[1] else {
        panic!("fixture term field")
    };
    *category = CategoryId(0);
    assert!(derive_roster(&wrong_category, &occurrences, &categories).is_none());
    let mut ranked = fixture();
    ranked.productions[1].precedence.binding_power = Some(10);
    assert!(derive_roster(&ranked, &occurrences, &categories).is_none());
    let mut nested = fixture();
    let inner = nested.productions[3].syntax.remove(0);
    nested.productions[3].syntax.push(SyntaxItem::Separated {
        source: Box::new(inner),
        separator: ",".into(),
    });
    assert!(derive_roster(&nested, &occurrences, &categories).is_none());
}

#[test]
fn roster_refuses_overflow_instead_of_truncating_original_local_tags() {
    let grammar = fixture();
    // 255 authored occurrences plus implicit Var exceeds the original bound.
    assert!(derive_roster(&grammar, &vec![0; 255], &[CategoryId(0), CategoryId(1)]).is_none());
}

#[test]
fn cross_category_duplicate_label_disables_only_the_key_profile() {
    let mut grammar = fixture();
    assert!(derive_roster(&grammar, &[0, 1, 2, 3], &[CategoryId(0), CategoryId(1)]).is_some());
    let store = grammar.authored.as_mut().expect("fixture source store");
    let leaf = grammar.productions[0]
        .authored
        .expect("Leaf source identity");
    let projection = grammar.productions[1]
        .authored
        .expect("Project source identity");
    let AuthoredNode::Rule(mut other) = store.get(leaf.0).expect("Leaf rule").clone() else {
        panic!("Leaf is a source rule");
    };
    let AuthoredNode::Rule(project) = store.get(projection.0).expect("Project rule") else {
        panic!("Project is a source rule");
    };
    // A nullary Text constructor has the same source label as the transparent
    // Expr projection. The original global label set couples these two arms.
    other.label = project.label;
    other.category = store
        .declarations()
        .expect("source declarations")
        .categories[1]
        .name;
    let other = core::AuthoredRuleId(
        store
            .try_push(AuthoredNode::Rule(other))
            .expect("second category source rule"),
    );
    let mut production = grammar.productions[0].clone();
    production.id = core::ProductionId(4);
    production.constructor = ConstructorId(99);
    production.label = "Project".into();
    production.result = CategoryId(1);
    production.reduction = 4;
    production.authored = Some(other);
    grammar.productions.push(production);
    let mut plan = grammar.reductions[0].clone();
    plan.output_category = CategoryId(1);
    plan.constructor = ConstructorId(99);
    grammar.reductions.push(plan);
    let productions = grammar.productions.clone();
    let reductions = grammar.reductions.clone();
    let authored = grammar.authored.clone();
    assert!(derive_roster(&grammar, &[0, 1, 2, 3, 4], &[CategoryId(0), CategoryId(1)]).is_none());
    assert_eq!(grammar.productions, productions, "all parser rows remain available");
    assert_eq!(grammar.reductions, reductions);
    assert_eq!(grammar.authored, authored);
}
