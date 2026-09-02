use crate::automata::minimize::minimize_dfa;
use crate::automata::partition::compute_equivalence_classes;
use crate::automata::regex::compile_regex;
use crate::automata::semiring::TropicalWeight;
use crate::automata::subset::subset_construction;
use crate::automata::{CharClass, Nfa, NfaState, TokenKind, DEAD_STATE};
use mettail_grammar_core as core;

pub const RUNTIME_COMPILER_ABI: &str = "mettail-rtn/1";
pub const RUNTIME_UNICODE_ABI: &str = "unicode-regex-syntax-0.8";

#[derive(Debug)]
pub enum RuntimeCompileError {
    InvalidGrammar(Vec<core::ValidationError>),
    NonExactProfile,
    Regex {
        token: String,
        position: usize,
        message: String,
    },
    NullableToken(String),
    NativeSourceForbidden(String),
    EngineNormalization(core::EngineNormalizationError),
    Image(core::ImageError),
    Fingerprint(postcard::Error),
}

pub fn compile_parser_image(
    grammar: &core::GrammarCoreV1,
) -> Result<core::ParserImageV1, RuntimeCompileError> {
    grammar
        .validate()
        .map_err(RuntimeCompileError::InvalidGrammar)?;
    if !grammar.weight_profile.is_consensus_safe() {
        return Err(RuntimeCompileError::NonExactProfile);
    }
    reject_runtime_source_actions(grammar)?;
    let lexer = compile_lexer(grammar)?;
    let engine = core::normalize_runtime_engine(grammar)
        .map_err(RuntimeCompileError::EngineNormalization)?;
    let image = core::ParserImageV1 {
        magic: core::PARSER_IMAGE_MAGIC,
        abi: core::PARSER_IMAGE_ABI_V1,
        compiler_abi: RUNTIME_COMPILER_ABI.into(),
        unicode_version: RUNTIME_UNICODE_ABI.into(),
        core_fingerprint: grammar
            .fingerprint()
            .map_err(RuntimeCompileError::Fingerprint)?,
        kind: core::ParserImageKind::Executable,
        index_width: core::IndexWidth::for_max(
            grammar
                .categories
                .len()
                .max(grammar.tokens.len())
                .max(grammar.productions.len())
                .max(engine.nonterminal_count as usize),
        ),
        exact: true,
        lexer,
        reductions: grammar.reductions.clone(),
        engine,
        limits: grammar.limits,
    };
    image
        .verify_executable(grammar, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI)
        .map_err(RuntimeCompileError::Image)?;
    Ok(image)
}

fn reject_runtime_source_actions(grammar: &core::GrammarCoreV1) -> Result<(), RuntimeCompileError> {
    for token in &grammar.tokens {
        if matches!(token.evaluation, Some(core::NativeEvaluation::Source { .. })) {
            return Err(RuntimeCompileError::NativeSourceForbidden(format!(
                "token `{}`",
                token.name
            )));
        }
    }
    for (index, reduction) in grammar.reductions.iter().enumerate() {
        if matches!(reduction.evaluation, Some(core::NativeEvaluation::Source { .. })) {
            return Err(RuntimeCompileError::NativeSourceForbidden(format!("reduction {index}")));
        }
    }
    Ok(())
}

fn compile_lexer(grammar: &core::GrammarCoreV1) -> Result<core::LexerImage, RuntimeCompileError> {
    let mut image = core::LexerImage::default();
    for mode in &grammar.modes {
        let mut nfa = Nfa::new();
        let start = nfa.start;
        for token_id in &mode.token_ids {
            let token = &grammar.tokens[token_id.0 as usize];
            if matches!(token.pattern, core::TokenPattern::Builtin(core::BuiltinToken::EndOfInput))
            {
                continue;
            }
            let kind = TokenKind::Custom(token.id.0.to_string());
            let accept = match &token.pattern {
                core::TokenPattern::Literal(text) => {
                    let branch = nfa.add_state(NfaState::new());
                    nfa.add_epsilon(start, branch);
                    let mut current = branch;
                    for byte in text.as_bytes() {
                        let next = nfa.add_state(NfaState::new());
                        nfa.add_transition(current, next, CharClass::Single(*byte));
                        current = next;
                    }
                    if text.is_empty() {
                        return Err(RuntimeCompileError::Regex {
                            token: token.name.clone(),
                            position: 0,
                            message: "empty tokens are not permitted".into(),
                        });
                    }
                    nfa.states[current as usize].accept = Some(kind);
                    current
                },
                core::TokenPattern::Regex(pattern) => {
                    let fragment = compile_regex(pattern, &mut nfa, kind).map_err(|error| {
                        RuntimeCompileError::Regex {
                            token: token.name.clone(),
                            position: error.position,
                            message: error.message,
                        }
                    })?;
                    nfa.add_epsilon(start, fragment.start);
                    fragment.accept
                },
                core::TokenPattern::Builtin(builtin) => {
                    let pattern = core::builtin_token_pattern(*builtin)
                        .expect("end-of-input was handled before regex compilation");
                    let fragment = compile_regex(pattern, &mut nfa, kind).map_err(|error| {
                        RuntimeCompileError::Regex {
                            token: token.name.clone(),
                            position: error.position,
                            message: error.message,
                        }
                    })?;
                    nfa.add_epsilon(start, fragment.start);
                    fragment.accept
                },
            };
            nfa.states[accept as usize].weight =
                TropicalWeight::new(-(f64::from(token.priority) * 1_000_000.0) + token.id.0 as f64);
        }

        let partition = compute_equivalence_classes(&nfa);
        let dfa = minimize_dfa(&subset_construction(&nfa, &partition));
        if !dfa.states[dfa.start as usize].alt_accepts.is_empty()
            || dfa.states[dfa.start as usize].accept.is_some()
        {
            return Err(RuntimeCompileError::NullableToken(mode.name.clone()));
        }
        let state_base =
            u32::try_from(image.states.len()).map_err(|_| RuntimeCompileError::Regex {
                token: mode.name.clone(),
                position: 0,
                message: "lexer state index exceeds u32".into(),
            })?;
        image.mode_starts.push(state_base + dfa.start);
        for state in &dfa.states {
            let transition_start =
                u32::try_from(image.transitions.len()).map_err(|_| RuntimeCompileError::Regex {
                    token: mode.name.clone(),
                    position: 0,
                    message: "lexer transition index exceeds u32".into(),
                })?;
            let mut byte = 0u16;
            while byte <= u8::MAX as u16 {
                let first = byte as u8;
                let target = state.transitions[partition.classify(first) as usize];
                if target == DEAD_STATE {
                    byte += 1;
                    continue;
                }
                let mut end = first;
                while end < u8::MAX {
                    let next = end + 1;
                    let next_target = state.transitions[partition.classify(next) as usize];
                    if next_target != target {
                        break;
                    }
                    end = next;
                }
                image.transitions.push(core::LexerTransition {
                    start: first,
                    end,
                    target: state_base + target,
                });
                byte = u16::from(end) + 1;
            }
            let mut accept: Vec<core::TokenId> = if state.alt_accepts.is_empty() {
                state.accept.iter().filter_map(token_kind_id).collect()
            } else {
                state
                    .alt_accepts
                    .iter()
                    .filter_map(|(kind, _)| token_kind_id(kind))
                    .collect()
            };
            accept.sort_by_key(|id| {
                let token = &grammar.tokens[id.0 as usize];
                (std::cmp::Reverse(token.priority), token.id)
            });
            accept.dedup();
            let transition_len = u32::try_from(image.transitions.len())
                .ok()
                .and_then(|end| end.checked_sub(transition_start))
                .ok_or_else(|| RuntimeCompileError::Regex {
                    token: mode.name.clone(),
                    position: 0,
                    message: "lexer transition slice exceeds u32".into(),
                })?;
            image
                .states
                .push(core::LexerState { transition_start, transition_len, accept });
        }
    }
    Ok(image)
}

fn token_kind_id(kind: &TokenKind) -> Option<core::TokenId> {
    match kind {
        TokenKind::Custom(value) => value.parse().ok().map(core::TokenId),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn category(id: u32, name: &str, primary: bool) -> core::Category {
        core::Category {
            id: core::CategoryId(id),
            name: name.into(),
            carrier: core::Carrier::Dynamic,
            primary,
            admits_variables: false,
        }
    }

    fn token(
        id: u32,
        name: &str,
        pattern: core::TokenPattern,
        decoder: core::TokenDecoder,
    ) -> core::TokenDefinition {
        core::TokenDefinition {
            id: core::TokenId(id),
            name: name.into(),
            pattern,
            category: None,
            evaluation: None,
            priority: 1,
            mode: core::ModeId(0),
            channel: "main".into(),
            transition: core::ModeTransition::default(),
            decoder,
            reservation: core::Reservation::None,
        }
    }

    fn reduction(category: u32, constructor: u32, arity: u16) -> core::ReductionPlan {
        core::ReductionPlan {
            output_category: core::CategoryId(category),
            constructor: core::ConstructorId(constructor),
            input_arity: arity,
            fields: (0..arity).map(core::FieldSource::Input).collect(),
            evaluation: None,
            evaluation_mode: None,
            tier: None,
        }
    }

    fn repeated_integer_grammar(kind: core::CollectionKind) -> core::GrammarCoreV1 {
        let mut grammar = core::GrammarCoreV1::new("IntegerCollection");
        grammar.categories.push(category(0, "Root", true));
        grammar.tokens = vec![
            token(
                0,
                "integer",
                core::TokenPattern::Builtin(core::BuiltinToken::Integer),
                core::TokenDecoder::Integer { radix: None },
            ),
            token(1, "comma", core::TokenPattern::Literal(",".into()), core::TokenDecoder::Unit),
        ];
        grammar.modes[0].token_ids = vec![core::TokenId(0), core::TokenId(1)];
        grammar.reductions.push(reduction(0, 0, 1));
        grammar.productions.push(core::Production {
            id: core::ProductionId(0),
            constructor: core::ConstructorId(0),
            label: "Collection".into(),
            result: core::CategoryId(0),
            syntax: vec![core::SyntaxItem::Repeat {
                body: vec![core::SyntaxItem::CaptureToken {
                    token: core::TokenId(0),
                    slot: "value".into(),
                }],
                separator: ",".into(),
                kind,
            }],
            precedence: core::Precedence::default(),
            classification: core::ProductionClass::default(),
            reduction: 0,
            provenance: None,
        });
        grammar
    }

    fn integer_map_grammar() -> core::GrammarCoreV1 {
        let mut grammar = core::GrammarCoreV1::new("IntegerMap");
        grammar.categories = vec![category(0, "Root", true), category(1, "Atom", false)];
        grammar.tokens = vec![
            token(
                0,
                "integer",
                core::TokenPattern::Builtin(core::BuiltinToken::Integer),
                core::TokenDecoder::Integer { radix: None },
            ),
            token(1, "comma", core::TokenPattern::Literal(",".into()), core::TokenDecoder::Unit),
            token(2, "colon", core::TokenPattern::Literal(":".into()), core::TokenDecoder::Unit),
        ];
        grammar.modes[0].token_ids = vec![core::TokenId(0), core::TokenId(1), core::TokenId(2)];
        grammar.reductions = vec![reduction(0, 0, 1), reduction(1, 1, 1)];
        grammar.productions = vec![
            core::Production {
                id: core::ProductionId(0),
                constructor: core::ConstructorId(0),
                label: "Map".into(),
                result: core::CategoryId(0),
                syntax: vec![core::SyntaxItem::Collection {
                    slot: "entries".into(),
                    key: Some(core::CategoryId(1)),
                    element: core::CategoryId(1),
                    separator: ",".into(),
                    kind: core::CollectionKind::Map,
                    key_value_separator: Some(":".into()),
                }],
                precedence: core::Precedence::default(),
                classification: core::ProductionClass::default(),
                reduction: 0,
                provenance: None,
            },
            core::Production {
                id: core::ProductionId(1),
                constructor: core::ConstructorId(1),
                label: "Atom".into(),
                result: core::CategoryId(1),
                syntax: vec![core::SyntaxItem::CaptureToken {
                    token: core::TokenId(0),
                    slot: "value".into(),
                }],
                precedence: core::Precedence::default(),
                classification: core::ProductionClass::default(),
                reduction: 1,
                provenance: None,
            },
        ];
        grammar
    }

    fn zipped_integer_grammar() -> core::GrammarCoreV1 {
        let mut grammar = repeated_integer_grammar(core::CollectionKind::List);
        grammar.name = "IntegerZip".into();
        grammar.tokens.push(token(
            2,
            "colon",
            core::TokenPattern::Literal(":".into()),
            core::TokenDecoder::Unit,
        ));
        grammar.modes[0].token_ids.push(core::TokenId(2));
        grammar.reductions[0] = reduction(0, 0, 2);
        grammar.productions[0].syntax = vec![core::SyntaxItem::Separated {
            source: Box::new(core::SyntaxItem::Mapped {
                source: Box::new(core::SyntaxItem::Zip {
                    left_slot: "left".into(),
                    right_slot: "right".into(),
                    left_kind: core::CollectionKind::List,
                    right_kind: core::CollectionKind::List,
                    body: Vec::new(),
                }),
                bindings: vec!["left".into(), "right".into()],
                body: vec![
                    core::SyntaxItem::CaptureToken {
                        token: core::TokenId(0),
                        slot: "left".into(),
                    },
                    core::SyntaxItem::Token(core::TokenId(2)),
                    core::SyntaxItem::CaptureToken {
                        token: core::TokenId(0),
                        slot: "right".into(),
                    },
                ],
            }),
            separator: ",".into(),
        }];
        grammar
    }

    fn foreign_grammar() -> core::GrammarCoreV1 {
        let mut grammar = core::GrammarCoreV1::new("Foreign");
        grammar.categories.push(category(0, "Root", true));
        grammar.reductions.push(reduction(0, 0, 1));
        grammar.productions.push(core::Production {
            id: core::ProductionId(0),
            constructor: core::ConstructorId(0),
            label: "Guest".into(),
            result: core::CategoryId(0),
            syntax: vec![core::SyntaxItem::ForeignLanguage {
                slot: "guest".into(),
                open: "{{".into(),
                close: "}}".into(),
            }],
            precedence: core::Precedence::default(),
            classification: core::ProductionClass::default(),
            reduction: 0,
            provenance: None,
        });
        grammar
    }

    fn push_mode_grammar() -> core::GrammarCoreV1 {
        let mut grammar = core::GrammarCoreV1::new("Modes");
        grammar.categories.push(category(0, "Root", true));
        let mut enter =
            token(0, "enter", core::TokenPattern::Literal("<".into()), core::TokenDecoder::Unit);
        enter.transition.push = Some(core::ModeId(1));
        let mut nested =
            token(1, "nested", core::TokenPattern::Literal("<".into()), core::TokenDecoder::Unit);
        nested.mode = core::ModeId(1);
        nested.transition.push = Some(core::ModeId(1));
        let mut leave =
            token(2, "leave", core::TokenPattern::Literal(">".into()), core::TokenDecoder::Unit);
        leave.mode = core::ModeId(1);
        leave.transition.pop = true;
        grammar.tokens = vec![enter, nested, leave];
        grammar.modes = vec![
            core::LexerMode {
                id: core::ModeId(0),
                name: "default".into(),
                token_ids: vec![core::TokenId(0)],
                raw: false,
            },
            core::LexerMode {
                id: core::ModeId(1),
                name: "nested".into(),
                token_ids: vec![core::TokenId(1), core::TokenId(2)],
                raw: false,
            },
        ];
        grammar.reductions.push(reduction(0, 0, 0));
        grammar.productions.push(core::Production {
            id: core::ProductionId(0),
            constructor: core::ConstructorId(0),
            label: "Enter".into(),
            result: core::CategoryId(0),
            syntax: vec![core::SyntaxItem::Token(core::TokenId(0))],
            precedence: core::Precedence::default(),
            classification: core::ProductionClass::default(),
            reduction: 0,
            provenance: None,
        });
        grammar
    }

    fn parse(
        grammar: &core::GrammarCoreV1,
        source: &str,
    ) -> Result<Vec<core::WeightedParse>, core::RuntimeError> {
        let image = compile_parser_image(grammar).expect("compile");
        let host = core::DefaultRuntimeHost;
        core::RuntimeParser::new(grammar, &image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI, &host)
            .expect("admit")
            .parse(source)
    }

    #[test]
    fn compiler_emits_verified_lexer_and_recursive_network() {
        let mut grammar = core::GrammarCoreV1::new("Tiny");
        grammar.categories.push(core::Category {
            id: core::CategoryId(0),
            name: "Expr".into(),
            carrier: core::Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        grammar.tokens.push(core::TokenDefinition {
            id: core::TokenId(0),
            name: "integer".into(),
            pattern: core::TokenPattern::Builtin(core::BuiltinToken::Integer),
            category: Some(core::CategoryId(0)),
            evaluation: None,
            priority: 1,
            mode: core::ModeId(0),
            channel: "main".into(),
            transition: core::ModeTransition::default(),
            decoder: core::TokenDecoder::Integer { radix: None },
            reservation: core::Reservation::None,
        });
        grammar.modes[0].token_ids.push(core::TokenId(0));
        grammar.reductions.push(core::ReductionPlan {
            output_category: core::CategoryId(0),
            constructor: core::ConstructorId(0),
            input_arity: 1,
            fields: vec![core::FieldSource::Input(0)],
            evaluation: None,
            evaluation_mode: None,
            tier: None,
        });
        grammar.productions.push(core::Production {
            id: core::ProductionId(0),
            constructor: core::ConstructorId(0),
            label: "Int".into(),
            result: core::CategoryId(0),
            syntax: vec![core::SyntaxItem::CaptureToken {
                token: core::TokenId(0),
                slot: "value".into(),
            }],
            precedence: core::Precedence::default(),
            classification: core::ProductionClass::default(),
            reduction: 0,
            provenance: None,
        });
        let image = compile_parser_image(&grammar).expect("compile");
        assert_eq!(image.kind, core::ParserImageKind::Executable);
        assert_eq!(image.engine.runtime_rules.len(), 1);
        assert!(!image.lexer.states.is_empty());
    }

    #[test]
    fn separated_collection_is_linear_left_recursive_and_preserves_order() {
        let grammar = repeated_integer_grammar(core::CollectionKind::List);
        let image = compile_parser_image(&grammar).expect("compile");
        assert!(image.engine.runtime_rules.iter().any(|rule| matches!(
            rule.semantic,
            core::RuntimeRuleSemantic::AppendCollection { .. }
        )));
        assert!(image.engine.runtime_rules.iter().any(|rule| matches!(
            rule.semantic,
            core::RuntimeRuleSemantic::FinalizeCollection { .. }
        )));

        let parsed = parse(&grammar, "1,2,3").expect("parse");
        let core::DynamicValue::Term(term) = &parsed[0].value else {
            panic!("root term")
        };
        let core::DynamicValue::Collection { kind, entries } = &term.fields[0] else {
            panic!("collection field")
        };
        assert_eq!(*kind, core::CollectionKind::List);
        assert_eq!(
            entries,
            &vec![
                core::DynamicValue::Integer(1),
                core::DynamicValue::Integer(2),
                core::DynamicValue::Integer(3),
            ]
        );
        assert!(parse(&grammar, "").is_ok());
        assert!(matches!(parse(&grammar, ",1"), Err(core::RuntimeError::NoParse)));
        assert!(matches!(parse(&grammar, "1,"), Err(core::RuntimeError::NoParse)));
    }

    #[test]
    fn map_finalization_sorts_semantic_keys_and_rejects_duplicates() {
        let grammar = integer_map_grammar();
        let parsed = parse(&grammar, "2:3,1:4").expect("parse");
        let core::DynamicValue::Term(term) = &parsed[0].value else {
            panic!("root term")
        };
        let core::DynamicValue::Collection { entries, .. } = &term.fields[0] else {
            panic!("map field")
        };
        let keys: Vec<_> = entries
            .iter()
            .map(|entry| {
                let core::DynamicValue::Sequence(pair) = entry else {
                    panic!("map pair")
                };
                pair[0].semantic_key().unwrap()
            })
            .collect();
        assert!(keys.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(matches!(parse(&grammar, "1:2,1:3"), Err(core::RuntimeError::Reduction(_))));
    }

    #[test]
    fn compiler_rejects_nullable_tokens() {
        let mut grammar = repeated_integer_grammar(core::CollectionKind::List);
        grammar.tokens[0].pattern = core::TokenPattern::Regex("[0-9]*".into());
        assert!(matches!(
            compile_parser_image(&grammar),
            Err(RuntimeCompileError::NullableToken(_))
        ));
    }

    #[test]
    fn mapped_zip_realizes_parallel_collections_without_transposition() {
        let grammar = zipped_integer_grammar();
        let parsed = parse(&grammar, "1:2,3:4").expect("parse");
        let core::DynamicValue::Term(term) = &parsed[0].value else {
            panic!("root term")
        };
        assert_eq!(term.fields.len(), 2);
        let expected = [vec![1, 3], vec![2, 4]];
        for (field, expected) in term.fields.iter().zip(expected) {
            let core::DynamicValue::Collection { kind, entries } = field else {
                panic!("collection field")
            };
            assert_eq!(*kind, core::CollectionKind::List);
            assert_eq!(
                entries,
                &expected
                    .into_iter()
                    .map(core::DynamicValue::Integer)
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn canonical_normalizer_rejects_noncontracting_same_span_cycles() {
        let mut grammar = core::GrammarCoreV1::new("Cycle");
        grammar.categories.push(category(0, "Loop", true));
        grammar.reductions.push(reduction(0, 0, 1));
        grammar.productions.push(core::Production {
            id: core::ProductionId(0),
            constructor: core::ConstructorId(0),
            label: "Loop".into(),
            result: core::CategoryId(0),
            syntax: vec![core::SyntaxItem::Category {
                category: core::CategoryId(0),
                slot: "next".into(),
            }],
            precedence: core::Precedence::default(),
            classification: core::ProductionClass::default(),
            reduction: 0,
            provenance: None,
        });
        assert!(matches!(
            compile_parser_image(&grammar),
            Err(RuntimeCompileError::EngineNormalization(
                core::EngineNormalizationError::Analysis(
                    core::RuntimeAnalysisError::NonContractingCycle
                )
            ))
        ));
    }

    struct RecordingForeignHost;

    impl core::RuntimeHost for RecordingForeignHost {
        fn capability_manifest(
            &self,
            key: &core::RuntimeCapabilityKey,
        ) -> Option<core::RuntimeCapabilityManifest> {
            (key.kind == core::RuntimeCapabilityKind::ForeignBridge).then(|| {
                core::RuntimeCapabilityManifest {
                    key: key.clone(),
                    code_commitment: [9; 32],
                    abi: "recording-foreign-host/1".into(),
                    effects: [core::RuntimeEffect::Bridge].into_iter().collect(),
                    cost: core::RuntimeLogicalCost {
                        base: 1,
                        per_input_byte: 1,
                        per_value: 0,
                        maximum: 1_024,
                    },
                }
            })
        }

        fn parse_foreign(
            &self,
            open: &str,
            close: &str,
            source: &str,
            span: core::SourceSpan,
        ) -> Result<core::DynamicValue, String> {
            Ok(core::DynamicValue::Sequence(vec![
                core::DynamicValue::Text(open.into()),
                core::DynamicValue::Text(close.into()),
                core::DynamicValue::Text(source.into()),
                core::DynamicValue::Integer(i128::from(span.end - span.start)),
            ]))
        }
    }

    #[test]
    fn foreign_regions_are_bounded_and_delegated_to_the_host() {
        let grammar = foreign_grammar();
        let image = compile_parser_image(&grammar).expect("compile");
        let host = RecordingForeignHost;
        let parser = core::RuntimeParser::new(
            &grammar,
            &image,
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            &host,
        )
        .expect("admit");
        let parsed = parser.parse("{{a{{b}}c}}").expect("nested foreign parse");
        let core::DynamicValue::Term(term) = &parsed[0].value else {
            panic!("root term")
        };
        assert_eq!(
            term.fields[0],
            core::DynamicValue::Sequence(vec![
                core::DynamicValue::Text("{{".into()),
                core::DynamicValue::Text("}}".into()),
                core::DynamicValue::Text("a{{b}}c".into()),
                core::DynamicValue::Integer(11),
            ])
        );

        let limited = core::RuntimeParser::new_with_policy(
            &grammar,
            &image,
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            &host,
            core::RuntimePolicy {
                max_foreign_nesting: 1,
                ..core::RuntimePolicy::default()
            },
        )
        .expect("admit");
        assert!(matches!(
            limited.parse("{{a{{b}}c}}"),
            Err(core::RuntimeError::ForeignNestingLimit { .. })
        ));
        assert!(matches!(
            parser.parse("{{unterminated"),
            Err(core::RuntimeError::ForeignLanguage { .. })
        ));
    }

    #[test]
    fn lexer_mode_stack_is_bounded_and_must_close() {
        let grammar = push_mode_grammar();
        let image = compile_parser_image(&grammar).expect("compile");
        let host = core::DefaultRuntimeHost;
        let parser = core::RuntimeParser::new(
            &grammar,
            &image,
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            &host,
        )
        .expect("admit");
        assert!(matches!(parser.parse("<"), Err(core::RuntimeError::LexerModeUnclosed { .. })));

        let limited = core::RuntimeParser::new_with_policy(
            &grammar,
            &image,
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            &host,
            core::RuntimePolicy {
                max_lexer_mode_depth: 2,
                ..core::RuntimePolicy::default()
            },
        )
        .expect("admit");
        assert!(matches!(
            limited.parse("<<"),
            Err(core::RuntimeError::LexerModeDepthLimit { .. })
        ));
    }

    #[test]
    fn image_admission_rejects_engine_and_lexer_tampering() {
        let grammar = repeated_integer_grammar(core::CollectionKind::List);
        let image = compile_parser_image(&grammar).expect("compile");

        let mut engine_tamper = image.clone();
        let rule = engine_tamper
            .engine
            .runtime_rules
            .iter_mut()
            .find(|rule| rule.production.is_some())
            .expect("source production");
        rule.cost = core::ExactParseCost::from_ticks(1).expect("finite nonzero test cost");
        assert!(matches!(
            engine_tamper.verify_executable(&grammar, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI),
            Err(core::ImageError::NonCanonicalEngine)
        ));

        let mut lexer_tamper = image;
        let transition = lexer_tamper
            .lexer
            .transitions
            .iter_mut()
            .find(|transition| transition.start == b'0' && transition.end == b'9')
            .expect("decimal transition");
        transition.end = b'8';
        assert!(matches!(
            lexer_tamper.verify_executable(&grammar, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI),
            Err(core::ImageError::LexerLanguageMismatch(0))
        ));
    }

    #[test]
    fn host_resource_policy_tightens_grammar_limits() {
        let grammar = repeated_integer_grammar(core::CollectionKind::List);
        let image = compile_parser_image(&grammar).expect("compile");
        let host = core::DefaultRuntimeHost;
        let parser = core::RuntimeParser::new_with_policy(
            &grammar,
            &image,
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            &host,
            core::RuntimePolicy {
                max_input_bytes: 2,
                ..core::RuntimePolicy::default()
            },
        )
        .expect("admit");
        assert!(matches!(parser.parse("123"), Err(core::RuntimeError::InputTooLarge)));
    }

    #[test]
    fn repeated_template_hole_must_infer_one_category() {
        let mut grammar = core::GrammarCoreV1::new("TemplateCategories");
        grammar.categories = vec![
            category(0, "Root", true),
            category(1, "Left", false),
            category(2, "Right", false),
        ];
        grammar.categories[1].admits_variables = true;
        grammar.categories[2].admits_variables = true;
        grammar.tokens = vec![token(
            0,
            "comma",
            core::TokenPattern::Literal(",".into()),
            core::TokenDecoder::Unit,
        )];
        grammar.modes[0].token_ids = vec![core::TokenId(0)];
        grammar.reductions = vec![reduction(0, 0, 2), reduction(1, 1, 0), reduction(2, 2, 0)];
        grammar.productions = vec![
            core::Production {
                id: core::ProductionId(0),
                constructor: core::ConstructorId(0),
                label: "Pair".into(),
                result: core::CategoryId(0),
                syntax: vec![
                    core::SyntaxItem::Category {
                        category: core::CategoryId(1),
                        slot: "left".into(),
                    },
                    core::SyntaxItem::Token(core::TokenId(0)),
                    core::SyntaxItem::Category {
                        category: core::CategoryId(2),
                        slot: "right".into(),
                    },
                ],
                precedence: core::Precedence::default(),
                classification: core::ProductionClass::default(),
                reduction: 0,
                provenance: None,
            },
            core::Production {
                id: core::ProductionId(1),
                constructor: core::ConstructorId(1),
                label: "LeftUnit".into(),
                result: core::CategoryId(1),
                syntax: Vec::new(),
                precedence: core::Precedence::default(),
                classification: core::ProductionClass::default(),
                reduction: 1,
                provenance: None,
            },
            core::Production {
                id: core::ProductionId(2),
                constructor: core::ConstructorId(2),
                label: "RightUnit".into(),
                result: core::CategoryId(2),
                syntax: Vec::new(),
                precedence: core::Precedence::default(),
                classification: core::ProductionClass::default(),
                reduction: 2,
                provenance: None,
            },
        ];
        let image = compile_parser_image(&grammar).expect("compile");
        let host = core::DefaultRuntimeHost;
        let parser = core::RuntimeParser::new(
            &grammar,
            &image,
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            &host,
        )
        .expect("admit");
        let result = parser.parse_template(
            &[
                core::RuntimeTemplatePiece::Hole(0),
                core::RuntimeTemplatePiece::Text(",".into()),
                core::RuntimeTemplatePiece::Hole(0),
            ],
            &[core::RuntimeTemplateHole { id: 0, category: None }],
            Some(core::CategoryId(0)),
        );
        assert!(matches!(
            result,
            Err(core::RuntimeError::TemplateHoleCategoryConflict { id: 0 })
        ));
    }
}
