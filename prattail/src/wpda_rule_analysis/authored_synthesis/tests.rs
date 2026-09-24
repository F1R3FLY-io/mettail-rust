use super::*;
use mettail_grammar_core::*;
use std::cell::RefCell;
use std::convert::Infallible;
use std::rc::Rc;

struct Fixture {
    core: GrammarCoreV1,
    store: AuthoredRuleStore,
    header: AuthoredDeclarations,
    category: AuthoredNameId,
}

impl Fixture {
    fn new(native: Option<NativeKind>, data: bool) -> Self {
        let mut core = GrammarCoreV1::new("owned-synthesis-fixture");
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Expr".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: !data,
        });
        let mut store = AuthoredRuleStore::new();
        let category = AuthoredNameId(
            store
                .try_push(AuthoredNode::Name(AuthoredName {
                    spelling: "Expr".into(),
                    equality_class: 0,
                }))
                .expect("fixture category"),
        );
        let header = AuthoredDeclarations {
            categories: vec![AuthoredCategoryDeclaration {
                name: category,
                native,
                collection: None,
                byte_observation: SourceObservation::Known(false),
                literal_observation: SourceObservation::Known(Some(
                    LiteralNativeObservation::ExactNativeType(NativeType::Int32),
                )),
                element_observation: SourceObservation::Known(None),
            }],
            tokens: vec![],
            global_tokens: vec![],
            modes: vec![],
        };
        Self { core, store, header, category }
    }

    fn rule(&mut self, items: Vec<AuthoredLegacyItem>) -> AuthoredRuleId {
        let label = AuthoredNameId(
            self.store
                .try_push(AuthoredNode::Name(AuthoredName {
                    spelling: "Original".into(),
                    equality_class: 1,
                }))
                .expect("fixture label"),
        );
        AuthoredRuleId(
            self.store
                .try_push(AuthoredNode::Rule(AuthoredRule {
                    label,
                    category: self.category,
                    term_context: None,
                    syntax_pattern: None,
                    items,
                }))
                .expect("fixture original rule"),
        )
    }

    fn production(&mut self, authored: Option<AuthoredRuleId>, label: &str) {
        let index = u32::try_from(self.core.productions.len()).expect("fixture small");
        self.core.reductions.push(ReductionPlan {
            output_category: CategoryId(0),
            constructor: ConstructorId(index),
            input_arity: 0,
            fields: vec![],
            evaluation: None,
            evaluation_mode: None,
            tier: None,
        });
        self.core.productions.push(Production {
            authored,
            id: ProductionId(index),
            constructor: ConstructorId(index),
            label: label.into(),
            result: CategoryId(0),
            syntax: vec![],
            precedence: Precedence::default(),
            classification: ProductionClass::default(),
            reduction: index,
            provenance: None,
        });
    }

    fn finish(mut self) -> GrammarCoreV1 {
        self.core.authored = Some(
            self.store
                .with_declarations(self.header)
                .expect("fixture declarations"),
        );
        self.core.authored_bindings = Some(AuthoredDeclarationBindings {
            categories: vec![CategoryId(0)],
            tokens: vec![],
            modes: vec![],
        });
        self.core.validate().expect("fixture core");
        self.core
    }
}

fn label(store: &AuthoredRuleStore, payload: &AuthoredRulePayload) -> String {
    let Some(AuthoredNode::Rule(rule)) = store.get(payload.rule.0) else {
        panic!("rule output")
    };
    let Some(AuthoredNode::Name(name)) = store.get(rule.label.0) else {
        panic!("label output")
    };
    name.spelling.clone()
}

#[test]
fn authored_synthesis_preserves_explicit_occurrences_duplicates_metadata_and_prefix() {
    let mut f = Fixture::new(None, true);
    let id = f.rule(vec![
        AuthoredLegacyItem::Terminal("original".into()),
        AuthoredLegacyItem::NonTerminal {
            ident: f.category,
            kind: NonTerminalKind::Category,
        },
    ]);
    f.production(Some(id), "Original");
    f.production(Some(id), "Original");
    f.production(None, "auxiliary");
    let core = f.finish();
    let output = derive_authored_rules(&core, &[1, 0, 1], |_| Ok::<_, Infallible>(()))
        .expect("original worker succeeds");
    assert_eq!(output.categories, ["Expr"]);
    let rows = &output.per_category[0];
    assert_eq!(
        rows.iter().map(|p| p.origin).collect::<Vec<_>>(),
        [
            AuthoredRuleOrigin::User { production_index: 1 },
            AuthoredRuleOrigin::User { production_index: 0 },
            AuthoredRuleOrigin::User { production_index: 1 },
        ]
    );
    assert!(rows.iter().all(|p| p.rule != id));
    assert_eq!(
        rows.iter()
            .map(|p| match p.origin {
                AuthoredRuleOrigin::User { production_index } =>
                    core.productions[production_index].constructor,
                AuthoredRuleOrigin::Synthetic => panic!("no synthetic data-category rule"),
            })
            .collect::<Vec<_>>(),
        [ConstructorId(1), ConstructorId(0), ConstructorId(1)]
    );
    let source = core.authored.as_ref().expect("source store");
    for index in 0..source.len() {
        assert_eq!(source.get(index as u32), output.store.get(index as u32));
    }
    assert_eq!(source.declarations(), output.store.declarations());
    assert!(matches!(
        derive_authored_rules(&core, &[2], |_| Ok::<_, Infallible>(())),
        Err(AuthoredSynthesisError::MissingAuthoredRule(2))
    ));
    assert!(matches!(
        derive_authored_rules(&core, &[3], |_| Ok::<_, Infallible>(())),
        Err(AuthoredSynthesisError::InvalidOccurrence(3))
    ));
}

#[test]
fn authored_synthesis_terminal_only_normalization_preserves_original_handle() {
    let mut f = Fixture::new(None, true);
    let id = f.rule(vec![AuthoredLegacyItem::Terminal("original".into())]);
    f.production(Some(id), "Original");
    let core = f.finish();
    let output = derive_authored_rules(&core, &[0], |_| Ok::<_, Infallible>(()))
        .expect("original no-op normalizer");
    assert_eq!(
        output.per_category,
        [vec![AuthoredRulePayload {
            rule: id,
            origin: AuthoredRuleOrigin::User { production_index: 0 },
        }]]
    );
    assert_eq!(&output.store, core.authored.as_ref().expect("source store"));
}

#[test]
fn authored_synthesis_empty_roster_keeps_declarations_and_synthetic_origins() {
    let core = Fixture::new(Some(NativeKind::Int32), false).finish();
    let output = derive_authored_rules(&core, &[], |_| Ok::<_, Infallible>(()))
        .expect("declaration only grammar");
    assert_eq!(output.categories, ["Expr"]);
    assert_eq!(
        output.per_category[0]
            .iter()
            .map(|row| label(&output.store, row))
            .collect::<Vec<_>>(),
        ["NumLit", "EVar"]
    );
    assert!(output.per_category[0]
        .iter()
        .all(|row| row.origin == AuthoredRuleOrigin::Synthetic));
}

#[test]
fn authored_synthesis_data_categories_skip_native_collection_and_variable_synthesis() {
    for collection in [false, true] {
        let mut f = Fixture::new(Some(NativeKind::Int32), true);
        f.header.categories[0].byte_observation = SourceObservation::Unavailable;
        f.header.categories[0].literal_observation = SourceObservation::Unavailable;
        f.header.categories[0].element_observation = SourceObservation::Unavailable;
        if collection {
            f.header.categories[0].collection = Some(AuthoredCollectionDeclaration {
                kind: CollectionKind::Set,
                open: None,
                close: None,
                separator: None,
                key_value_separator: None,
            });
        }
        let core = f.finish();
        let output = derive_authored_rules(&core, &[], |_| Ok::<_, Infallible>(()))
            .expect("data categories skip synthesis");
        assert_eq!(output.categories, ["Expr"]);
        assert!(output.per_category[0].is_empty());
    }
}

#[test]
fn authored_synthesis_byte_true_skips_unavailable_native_but_false_refuses() {
    let mut f = Fixture::new(Some(NativeKind::Other), false);
    f.header.categories[0].byte_observation = SourceObservation::Known(true);
    f.header.categories[0].literal_observation = SourceObservation::Unavailable;
    let core = f.finish();
    let mut probes = Vec::new();
    let output = derive_authored_rules(&core, &[], |event| {
        if let AuthoredSynthesisEvent::NativeProbe { probe, .. } = event {
            probes.push(probe);
        }
        Ok::<_, Infallible>(())
    })
    .expect("byte probe bypasses native metadata");
    assert_eq!(
        output.per_category[0]
            .iter()
            .map(|row| label(&output.store, row))
            .collect::<Vec<_>>(),
        ["BytesLit", "EVar"]
    );
    drop(output);
    assert_eq!(probes, [NativeProbe::ByteVector]);
    for observation in [SourceObservation::Unavailable, SourceObservation::Known(None)] {
        let mut f = Fixture::new(Some(NativeKind::Other), false);
        f.header.categories[0].literal_observation = observation.clone();
        let core = f.finish();
        let result = derive_authored_rules(&core, &[], |_| Ok::<_, Infallible>(()));
        match observation {
            SourceObservation::Unavailable => assert!(matches!(
                result,
                Err(AuthoredSynthesisError::UnavailableObservation {
                    probe: NativeProbe::Literal,
                    ..
                })
            )),
            SourceObservation::Known(None) => {
                assert!(matches!(result, Err(AuthoredSynthesisError::AbsentNativeObservation(0))))
            },
            _ => unreachable!(),
        }
    }
}

#[test]
fn authored_synthesis_collection_uses_original_defaults_and_known_none_fallback() {
    let mut f = Fixture::new(None, false);
    f.header.categories[0].collection = Some(AuthoredCollectionDeclaration {
        kind: CollectionKind::Set,
        open: None,
        close: Some(String::new()),
        separator: None,
        key_value_separator: None,
    });
    let core = f.finish();
    let output = derive_authored_rules(&core, &[], |_| Ok::<_, Infallible>(()))
        .expect("retained collection");
    assert_eq!(
        output.per_category[0]
            .iter()
            .map(|row| label(&output.store, row))
            .collect::<Vec<_>>(),
        ["SetLit", "EVar"]
    );
    let payload = &output.per_category[0][0];
    assert_eq!(label(&output.store, payload), "SetLit");
    let Some(AuthoredNode::Rule(rule)) = output.store.get(payload.rule.0) else {
        panic!("collection rule")
    };
    let Some(AuthoredNode::Syntax(syntax)) = output
        .store
        .get(rule.syntax_pattern.expect("collection syntax").0)
    else {
        panic!("syntax")
    };
    assert!(matches!(syntax.first(), Some(AuthoredSyntax::Literal(text)) if text == "Set"));
    assert!(matches!(syntax.last(), Some(AuthoredSyntax::Literal(text)) if text.is_empty()));
    let Some(AuthoredNode::Params(params)) = output
        .store
        .get(rule.term_context.expect("collection context").0)
    else {
        panic!("params")
    };
    let Some(AuthoredNode::Param(AuthoredParam::Simple { ty, .. })) = output.store.get(params[0].0)
    else {
        panic!("simple")
    };
    let Some(AuthoredNode::Type(AuthoredType::Collection { kind, element })) =
        output.store.get(ty.0)
    else {
        panic!("collection type")
    };
    assert_eq!(*kind, CollectionKind::Set);
    let Some(AuthoredNode::Type(AuthoredType::Base(name))) = output.store.get(element.0) else {
        panic!("element type")
    };
    let Some(AuthoredNode::Name(name)) = output.store.get(name.0) else {
        panic!("element name")
    };
    assert_eq!(name.spelling, "Expr");
}

fn event_tag(event: &AuthoredSynthesisEvent<'_>) -> &'static str {
    match event {
        AuthoredSynthesisEvent::Normalization(_) => "normalization",
        AuthoredSynthesisEvent::Binder(_) => "binder",
        AuthoredSynthesisEvent::Synthesis(_) => "synthesis",
        AuthoredSynthesisEvent::NativeProbe { .. } => "native",
        AuthoredSynthesisEvent::StoreCopy(_) => "copy",
        AuthoredSynthesisEvent::StringCopy(_) => "string",
        _ => "source",
    }
}

#[test]
fn authored_synthesis_one_policy_refuses_every_reached_site_without_suffix() {
    let mut f = Fixture::new(Some(NativeKind::Int32), false);
    let rule = f.rule(vec![
        AuthoredLegacyItem::Terminal("original".into()),
        AuthoredLegacyItem::NonTerminal {
            ident: f.category,
            kind: NonTerminalKind::Category,
        },
    ]);
    f.production(Some(rule), "Original");
    let core = f.finish();
    let expected = Rc::new(RefCell::new(Vec::new()));
    let recorder = Rc::clone(&expected);
    let output = derive_authored_rules(&core, &[0], move |event| {
        recorder.borrow_mut().push(event_tag(&event));
        Ok::<_, usize>(())
    })
    .expect("baseline succeeds");
    assert!(output.per_category[0].len() >= 3);
    drop(output);
    let expected = expected.borrow().clone();
    assert!(expected.contains(&"normalization"));
    assert!(expected.contains(&"binder"));
    for refusal in 0..expected.len() {
        let actual = Rc::new(RefCell::new(Vec::new()));
        let recorder = Rc::clone(&actual);
        let result = derive_authored_rules(&core, &[0], move |event| {
            let mut trace = recorder.borrow_mut();
            let index = trace.len();
            trace.push(event_tag(&event));
            if index == refusal {
                Err(index)
            } else {
                Ok(())
            }
        });
        assert!(result.is_err(), "site {refusal} must not publish output");
        assert_eq!(*actual.borrow(), expected[..=refusal], "site {refusal}");
    }
}
