use super::*;
use crate::runtime_backend::{compile_parser_image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI};
use crate::wpda_runtime::{ActionArg, ActionSignature, SemanticBuilder};
use mettail_grammar_core as core;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc, Mutex,
};

const SPAN: SourceSpan = SourceSpan { start: 0, end: 3 };

#[test]
fn native_variable_action_reuses_original_identity_and_argument_projection() {
    let name = "owned-native-variable";
    let expected = core::native_variable::get_or_create_var(name);
    let args = vec![ActionArg::Token {
        kind: crate::automata::TokenKind::Ident,
        text: name.into(),
        pos: 0,
        occurrence: None,
    }];
    let term = native_variable(7, CategoryId(3), args, SPAN);
    assert_eq!(term.category, 7);
    assert_eq!(term.production, None);
    assert_eq!(term.span, SPAN);
    assert_eq!(term.syntax, term.value);
    assert_eq!(
        term.value,
        DynamicValue::NativeVariable {
            category: CategoryId(3),
            variable: expected
        }
    );
    let fallback = native_variable(7, CategoryId(3), vec![], SPAN);
    assert_eq!(
        fallback.value,
        DynamicValue::NativeVariable {
            category: CategoryId(3),
            variable: core::native_variable::get_or_create_var(""),
        }
    );
}

#[test]
fn grouping_boundary_clears_only_production_top() {
    let original = OwnedTerm {
        category: 7,
        production: Some(core::ProductionId(12)),
        syntax: DynamicValue::Text("recognized syntax".into()),
        value: DynamicValue::Integer(42),
        span: SPAN,
    };
    let mut builder = SemanticBuilder::new();
    grouping_boundary(
        &mut builder,
        vec![ActionArg::Term {
            value: Arc::new(original.clone()),
            type_name: std::any::type_name::<OwnedTerm>(),
        }],
    )
    .expect("one grouping operand is valid");
    let grouped = builder
        .take_result::<OwnedTerm>()
        .expect("grouping publishes one owned term");
    let mut expected = original.clone();
    expected.production = None;
    assert_eq!(grouped, expected);
    assert_eq!(original.production, Some(core::ProductionId(12)), "shared inner remains ranked");
    assert!(matches!(
        grouping_boundary(&mut builder, Vec::new()),
        Err(ActionInvocationError::Arity { expected: 1, actual: 0 })
    ));
}

#[derive(Debug, PartialEq, Eq)]
enum Call {
    Decode(String),
    Evaluate(Vec<DynamicValue>, SourceSpan),
}

#[derive(Default)]
struct RecordingHost {
    calls: Mutex<Vec<Call>>,
    fail_native: bool,
    revoke_native: bool,
    changed: AtomicBool,
}

impl core::RuntimeHost for RecordingHost {
    fn capability_manifest(
        &self,
        key: &core::RuntimeCapabilityKey,
    ) -> Option<core::RuntimeCapabilityManifest> {
        Some(core::RuntimeCapabilityManifest {
            key: key.clone(),
            code_commitment: if self.changed.load(Ordering::SeqCst) {
                [2; 32]
            } else {
                [1; 32]
            },
            abi: "owned-action-test/1".into(),
            effects: [core::RuntimeEffect::Reduce].into_iter().collect(),
            cost: core::RuntimeLogicalCost {
                base: 1,
                per_input_byte: 1,
                per_value: 1,
                maximum: 1_024,
            },
        })
    }

    fn decode_token(&self, _: &str, text: &str) -> Result<DynamicValue, String> {
        self.calls.lock().unwrap().push(Call::Decode(text.into()));
        text.parse::<i128>()
            .map(DynamicValue::Integer)
            .map_err(|error| error.to_string())
    }

    fn evaluate(
        &self,
        _: &core::NativeEvaluation,
        inputs: &[DynamicValue],
        span: SourceSpan,
    ) -> Result<DynamicValue, String> {
        self.calls
            .lock()
            .unwrap()
            .push(Call::Evaluate(inputs.to_vec(), span));
        if self.revoke_native {
            self.changed.store(true, Ordering::SeqCst);
        }
        if self.fail_native {
            Err("native refused".into())
        } else {
            Ok(DynamicValue::Integer(987))
        }
    }
}

fn grammar() -> core::GrammarCoreV1 {
    let mut grammar = core::GrammarCoreV1::new("OwnedActions");
    grammar.categories.push(core::Category {
        id: CategoryId(0),
        name: "Expr".into(),
        carrier: core::Carrier::Dynamic,
        primary: true,
        admits_variables: true,
    });
    grammar.tokens.push(core::TokenDefinition {
        id: TokenId(0),
        name: "integer".into(),
        pattern: core::TokenPattern::Builtin(core::BuiltinToken::Integer),
        category: None,
        evaluation: None,
        priority: 1,
        mode: core::ModeId(0),
        channel: "main".into(),
        transition: core::ModeTransition::default(),
        decoder: core::TokenDecoder::Capability("owned/token".into()),
        reservation: core::Reservation::None,
    });
    grammar.modes[0].token_ids = vec![TokenId(0)];
    grammar.reductions.push(ReductionPlan {
        output_category: CategoryId(0),
        constructor: core::ConstructorId(0),
        input_arity: 1,
        fields: vec![core::FieldSource::Input(0)],
        evaluation: Some(core::NativeEvaluation::Handler("owned/native".into())),
        evaluation_mode: None,
        tier: None,
    });
    grammar.productions.push(core::Production {
        authored: None,
        id: core::ProductionId(0),
        constructor: core::ConstructorId(0),
        label: "Int".into(),
        result: CategoryId(0),
        syntax: vec![core::SyntaxItem::CaptureToken { token: TokenId(0), slot: "value".into() }],
        precedence: core::Precedence::default(),
        classification: core::ProductionClass::default(),
        reduction: 0,
        provenance: None,
    });
    grammar
        .capabilities
        .insert(core::Capability::TokenDecoder("owned/token".into()));
    grammar
        .capabilities
        .insert(core::Capability::NativeEvaluator("owned/native".into()));
    grammar
}

fn with_session<T>(
    host: &dyn core::RuntimeHost,
    run: impl FnOnce(&RuntimeLexicalSession<'_, '_, '_>, &ReductionPlan) -> T,
) -> T {
    let grammar = grammar();
    let image = compile_parser_image(&grammar).expect("compile fixture");
    let parser =
        core::RuntimeParser::new(&grammar, &image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI, host)
            .expect("admit fixture");
    let session = parser.lexical_session("123").expect("lex once");
    run(&session, &grammar.reductions[0])
}

fn action_arg(term: OwnedTerm) -> ActionArg {
    ActionArg::Term {
        value: Arc::new(term),
        type_name: "RealizedTerm",
    }
}

#[test]
fn token_decodes_once_and_category_comes_from_payload_not_debug_tag() {
    let host = RecordingHost::default();
    with_session(&host, |session, _| {
        let term = decode_token(session, 0, TokenId(0), "123", SPAN).expect("decode");
        assert_eq!(term.syntax, DynamicValue::Integer(123));
        assert_eq!(term.value, DynamicValue::Integer(123));
        assert_eq!(term.span, SPAN);
        let mut builder = SemanticBuilder::new();
        builder.push_term_arc(Arc::new(term));
        let (payload, tag) = builder.top_term().expect("term");
        assert_eq!(tag, "RealizedTerm");
        assert_eq!(term_category(payload), Some(0));
        assert_eq!(term_category(&DynamicValue::Integer(123)), None);
        assert_eq!(*host.calls.lock().unwrap(), vec![Call::Decode("123".into())]);
        assert_eq!(
            decode_token(session, 0, TokenId(u32::MAX), "123", SPAN),
            Err(ActionInvocationError::RuntimeSemantic(RuntimeError::InvalidToken(TokenId(
                u32::MAX
            )))),
        );
        assert_eq!(host.calls.lock().unwrap().len(), 1);
    });
}

#[test]
fn reduction_keeps_order_captures_span_and_distinct_syntax_after_native_evaluation() {
    let host = RecordingHost::default();
    with_session(&host, |session, original| {
        let mut plan = original.clone();
        plan.input_arity = 2;
        plan.fields = vec![
            core::FieldSource::Input(1),
            core::FieldSource::Input(0),
            core::FieldSource::Text(0),
        ];
        let inputs = [
            OwnedTerm {
                category: 0,
                production: None,
                syntax: DynamicValue::Text("left".into()),
                value: DynamicValue::Integer(7),
                span: SPAN,
            },
            OwnedTerm {
                category: 0,
                production: None,
                syntax: DynamicValue::Text("right".into()),
                value: DynamicValue::Integer(11),
                span: SPAN,
            },
        ];
        let result = reduce(session, 0, &plan, &inputs, &["capture".into()], SPAN).expect("reduce");
        assert_eq!(result.value, DynamicValue::Integer(987));
        let DynamicValue::Term(ref syntax) = result.syntax else {
            panic!("retained constructor")
        };
        assert_eq!(
            syntax.fields,
            vec![
                DynamicValue::Text("right".into()),
                DynamicValue::Text("left".into()),
                DynamicValue::Text("capture".into())
            ]
        );
        assert_eq!(syntax.span, SPAN);
        assert_eq!(result.span, SPAN);
        assert_eq!(
            *host.calls.lock().unwrap(),
            vec![Call::Evaluate(vec![DynamicValue::Integer(7), DynamicValue::Integer(11)], SPAN)],
        );
    });
}

#[test]
fn structural_hole_is_preserved_without_decoding_in_non_native_reduction() {
    let host = RecordingHost::default();
    with_session(&host, |session, original| {
        let hole = structural_hole(0, 17, CategoryId(0), SPAN);
        assert_eq!(hole.syntax, DynamicValue::TemplateHole { id: 17, category: CategoryId(0) });
        assert_eq!(hole.value, hole.syntax);
        let mut plan = original.clone();
        plan.evaluation = None;
        let result = reduce(session, 0, &plan, &[hole], &[], SPAN).expect("reduce");
        assert_eq!(result.syntax, result.value);
        let DynamicValue::Term(ref syntax) = result.syntax else {
            panic!("constructor")
        };
        assert_eq!(
            syntax.fields,
            vec![DynamicValue::TemplateHole { id: 17, category: CategoryId(0) }]
        );
        assert!(host.calls.lock().unwrap().is_empty());
    });
}

#[test]
fn reduction_apply_failure_skips_native_and_is_not_an_empty_action() {
    let host = RecordingHost::default();
    with_session(&host, |session, original| {
        let mut plan = original.clone();
        plan.fields = vec![core::FieldSource::Text(0)];
        let input = structural_hole(0, 0, CategoryId(0), SPAN);
        let result = SemanticBuilder::invoke_action_with(
            ActionSignature {
                arity: 1,
                expected_input_cats: &[0],
                output_cat: 0,
            },
            vec![action_arg(input)],
            vec![],
            |builder, args| {
                let inputs = args
                    .into_iter()
                    .map(|arg| arg.try_into_term::<OwnedTerm>().expect("carrier"))
                    .collect::<Vec<_>>();
                builder.push_term(reduce(session, 0, &plan, &inputs, &[], SPAN)?);
                Ok(())
            },
        );
        assert!(matches!(result,
            Err(ActionInvocationError::RuntimeSemantic(RuntimeError::Reduction(message)))
            if message == "MissingText(0)"
        ));
        assert!(host.calls.lock().unwrap().is_empty());
    });
}

#[test]
fn native_failure_and_revalidation_failure_survive_existing_invocation_boundary() {
    for revoke in [false, true] {
        let host = RecordingHost {
            fail_native: !revoke,
            revoke_native: revoke,
            ..Default::default()
        };
        with_session(&host, |session, plan| {
            let input = structural_hole(0, 0, CategoryId(0), SPAN);
            let result = SemanticBuilder::invoke_action_with(
                ActionSignature {
                    arity: 1,
                    expected_input_cats: &[0],
                    output_cat: 0,
                },
                vec![action_arg(input)],
                vec![],
                |builder, args| {
                    let inputs = args
                        .into_iter()
                        .map(|arg| arg.try_into_term::<OwnedTerm>().expect("carrier"))
                        .collect::<Vec<_>>();
                    builder.push_term(reduce(session, 0, plan, &inputs, &[], SPAN)?);
                    Ok(())
                },
            );
            if revoke {
                assert!(matches!(
                    result,
                    Err(ActionInvocationError::RuntimeSemantic(RuntimeError::Capability(
                        core::RuntimeCapabilityError::Changed(_)
                    )))
                ));
            } else {
                assert!(
                    matches!(result, Err(ActionInvocationError::RuntimeSemantic(RuntimeError::Reduction(message))) if message == "native refused")
                );
            }
            assert_eq!(
                *host.calls.lock().unwrap(),
                vec![Call::Evaluate(
                    vec![DynamicValue::TemplateHole { id: 0, category: CategoryId(0) }],
                    SPAN
                )]
            );
        });
    }
}

/// End-to-end instances of OwnedActionAdapter's explicit native failure and
/// RealizationFailureBoundary's failure publication: neither host failure nor
/// post-call authority revocation may become accepted roots or empty success.
#[test]
fn owned_walker_publishes_native_failure_and_capability_revocation_as_errors() {
    use crate::automata::TokenKind;
    use crate::wpda_owned::engine::{AbsorptionRows, OwnedWpdaEngine};
    use crate::wpda_owned::source::{OwnedTokenSource, SourceAdapterLimits};
    use crate::wpda_rule_analysis::authored_descriptors::{
        derive_authored_descriptors, DescriptorOptions,
    };
    use crate::wpda_rule_analysis::authored_synthesis::derive_authored_rules;
    use crate::wpda_runtime::{RealizationError, WpdaResolveResult};
    use crate::wpda_walker::WpdaWalker;
    use std::convert::Infallible;

    // Retain the existing host/plan fixture, making its source production the
    // nullary keyword `Int . |- "123" : Expr`. Keyword forwarding ignores the
    // captured terminal; only the declared native evaluator is invoked.
    let mut grammar = grammar();
    grammar.tokens[0].pattern = core::TokenPattern::Literal("123".into());
    grammar.productions[0].syntax = vec![core::SyntaxItem::Token(TokenId(0))];
    grammar.reductions[0].input_arity = 0;
    grammar.reductions[0].fields.clear();
    let mut store = core::AuthoredRuleStore::new();
    let category = core::AuthoredNameId(
        store
            .try_push(core::AuthoredNode::Name(core::AuthoredName {
                spelling: "Expr".into(),
                equality_class: 0,
            }))
            .expect("fixture category"),
    );
    let label = core::AuthoredNameId(
        store
            .try_push(core::AuthoredNode::Name(core::AuthoredName {
                spelling: "Int".into(),
                equality_class: 1,
            }))
            .expect("fixture label"),
    );
    grammar.productions[0].authored = Some(core::AuthoredRuleId(
        store
            .try_push(core::AuthoredNode::Rule(core::AuthoredRule {
                source_body_present: core::SourceObservation::Known(false),
                explicit_fold: core::SourceObservation::Known(false),
                label,
                category,
                term_context: None,
                syntax_pattern: None,
                items: vec![core::AuthoredLegacyItem::Terminal("123".into())],
            }))
            .expect("fixture authored rule"),
    ));
    grammar.authored = Some(
        store
            .with_declarations(core::AuthoredDeclarations {
                categories: vec![core::AuthoredCategoryDeclaration {
                    name: category,
                    data_observation: core::SourceObservation::Known(false),
                    native: None,
                    collection: None,
                    byte_observation: core::SourceObservation::Known(false),
                    literal_observation: core::SourceObservation::Known(None),
                    element_observation: core::SourceObservation::Known(None),
                }],
                tokens: vec![],
                global_tokens: vec![],
                modes: vec![],
            })
            .expect("fixture source declarations"),
    );
    grammar.authored_bindings = Some(core::AuthoredDeclarationBindings {
        categories: vec![CategoryId(0)],
        tokens: vec![],
        modes: vec![],
    });
    grammar.validate().expect("retained fixture source");
    let synthesis = derive_authored_rules(&grammar, &[0], |_| Ok::<_, Infallible>(()))
        .expect("original rule synthesis");
    let descriptors = derive_authored_descriptors(
        &grammar,
        &[0],
        synthesis,
        DescriptorOptions {
            crosscat_lex_compat_gate: true,
            prefix_factoring: false,
            mixfix_factoring: false,
            accept_continue: false,
            recovery_base: 0xFE00,
            max_mixfix_slice: usize::MAX,
        },
        |_, _, _, _| Ok::<_, Infallible>(()),
        |_, _| Ok::<_, Infallible>(false),
    )
    .expect("original descriptor workers");
    let image = compile_parser_image(&grammar).expect("fixture image");
    let absorption = AbsorptionRows::new();

    for revoke in [false, true] {
        let host = RecordingHost {
            fail_native: !revoke,
            revoke_native: revoke,
            ..Default::default()
        };
        let parser = core::RuntimeParser::new(
            &grammar,
            &image,
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            &host,
        )
        .expect("initial authority admitted");
        let session = parser.lexical_session("123").expect("lex once");
        let source = OwnedTokenSource::new(
            &session,
            SourceAdapterLimits { nodes: 16, edges: 16, text_bytes: 128 },
            |token, text| {
                assert_eq!(token, TokenId(0));
                assert_eq!(text, "123");
                Ok::<_, Infallible>(TokenKind::Fixed("123".into()))
            },
        )
        .expect("existing lexical lattice projection");
        let actions = OwnedActionProvider::new(&source, &descriptors, |_| Ok(()))
            .expect("actual owned action provider");
        let engine = OwnedWpdaEngine::new(&descriptors, &actions, 0, &[], &absorption, |_| Ok(()))
            .expect("actual owned engine");
        let mut walker = WpdaWalker::new_for_category(engine, 0, 0);
        walker
            .run_to_end_of_input(1_024, &source)
            .expect("bounded original walker run");
        let result = walker.resolve_at_end_of_input(&source);
        let WpdaResolveResult::RealizationFailed {
            error:
                RealizationError::Action {
                    cause: ActionInvocationError::RuntimeSemantic(error),
                    ..
                },
            ..
        } = result
        else {
            panic!("host failure must publish an error, not roots or no-match: {result:?}");
        };
        if revoke {
            assert!(matches!(
                error,
                RuntimeError::Capability(core::RuntimeCapabilityError::Changed(_))
            ));
        } else {
            assert!(
                matches!(error, RuntimeError::Reduction(message) if message == "native refused")
            );
        }
        assert_eq!(
            *host.calls.lock().expect("host callback trace lock"),
            vec![Call::Evaluate(vec![], SPAN)]
        );
    }
}
