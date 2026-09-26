use super::*;
use crate::runtime_backend::{compile_parser_image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI};
use mettail_grammar_core as core;
use std::cell::Cell;

const LIMITS: SourceAdapterLimits =
    SourceAdapterLimits { nodes: 100, edges: 100, text_bytes: 1000 };

fn grammar() -> core::GrammarCoreV1 {
    let mut grammar = core::GrammarCoreV1::new("OwnedInput");
    grammar.categories.push(core::Category {
        id: core::CategoryId(0),
        name: "Expr".into(),
        carrier: core::Carrier::Dynamic,
        primary: true,
        admits_variables: true,
    });
    for (id, pattern, channel) in [
        (0, core::TokenPattern::Regex("[0-9]+".into()), "main"),
        (1, core::TokenPattern::Literal("12".into()), "main"),
        (2, core::TokenPattern::Regex("[ ]+".into()), "trivia"),
    ] {
        grammar.tokens.push(core::TokenDefinition {
            id: TokenId(id),
            name: format!("token{id}"),
            pattern,
            category: (id == 0).then_some(core::CategoryId(0)),
            evaluation: None,
            priority: 1,
            mode: core::ModeId(0),
            channel: channel.into(),
            transition: core::ModeTransition::default(),
            decoder: core::TokenDecoder::Text,
            reservation: core::Reservation::None,
        });
        grammar.modes[0].token_ids.push(TokenId(id));
    }
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
        authored: None,
        id: core::ProductionId(0),
        constructor: core::ConstructorId(0),
        label: "Number".into(),
        result: core::CategoryId(0),
        syntax: vec![core::SyntaxItem::CaptureToken { token: TokenId(0), slot: "value".into() }],
        precedence: core::Precedence::default(),
        classification: core::ProductionClass::default(),
        reduction: 0,
        provenance: None,
    });
    grammar
}

fn kind(id: TokenId, _: &str) -> Result<TokenKind, &'static str> {
    match id.0 {
        0 => Ok(TokenKind::Integer),
        1 => Ok(TokenKind::Fixed("12".into())),
        _ => Err("unexpected observer"),
    }
}

#[test]
fn source_reuses_ordered_edges_and_original_trivia_targets() {
    let grammar = grammar();
    let image = compile_parser_image(&grammar).expect("image");
    let host = core::DefaultRuntimeHost;
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("parser");
    let session = parser.lexical_session(" 123 ").expect("lex once");
    let source = OwnedTokenSource::new(&session, LIMITS, kind).expect("source");
    assert_eq!(source.position(0), Some(session.canonical_position(LexPosition::START)));
    assert_eq!(source.peek_text(0), Some("123"));
    assert!(source.is_ambiguous_at(0));
    for node_id in 0..source.len() {
        let position = source.position(node_id).expect("dense position");
        assert_eq!(source.node_id(position), Some(node_id));
        assert!(std::ptr::eq(
            source.evidence_at(node_id).expect("evidence"),
            session.node(position).expect("original")
        ));
        let expected: Vec<_> = session
            .node(position)
            .expect("node")
            .edges
            .iter()
            .filter_map(|e| match e {
                LexicalEdge::Accepted { token, target, alternative } => {
                    Some((*token, *target, *alternative))
                },
                LexicalEdge::Refuted { .. } => None,
            })
            .collect();
        for (alt, (token, target, ordinal)) in expected.iter().enumerate() {
            assert_eq!(WpdaTokenSource::token_occurrence(&source, node_id, alt), Some(alt as u32));
            assert_eq!(
                source.token_occurrence(node_id, alt),
                Some(TokenOccurrence {
                    token: *token,
                    end: *target,
                    alternative: *ordinal
                })
            );
            let next = source.next_pos(node_id, alt).expect("target");
            assert_eq!(source.position(next), Some(session.canonical_position(*target)));
            assert_eq!(source.end_byte(node_id, alt), Some(target.offset));
        }
        assert_eq!(source.token_occurrence(node_id, expected.len()), None);
        assert_eq!(WpdaTokenSource::token_occurrence(&source, node_id, expected.len()), None);
        assert_eq!(source.is_logical_eoi(node_id), session.is_logical_eoi(position));
    }
    assert!(!source.is_logical_eoi(usize::MAX));
    assert_eq!(source.peek_kind(usize::MAX), None);
}

#[test]
fn source_admission_precedes_observer_calls_and_retains_binding_failure() {
    let grammar = grammar();
    let image = compile_parser_image(&grammar).expect("image");
    let host = core::DefaultRuntimeHost;
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("parser");
    let session = parser.lexical_session("123").expect("lex");
    for (limits, expected) in [
        (SourceAdapterLimits { nodes: 0, ..LIMITS }, SourceAdapterError::NodeLimit),
        (SourceAdapterLimits { edges: 0, ..LIMITS }, SourceAdapterError::EdgeLimit),
        (SourceAdapterLimits { text_bytes: 0, ..LIMITS }, SourceAdapterError::TextLimit),
    ] {
        let calls = Cell::new(0);
        let result = OwnedTokenSource::new(&session, limits, |id, text| {
            calls.set(calls.get() + 1);
            kind(id, text)
        });
        assert_eq!(result.err(), Some(expected));
        assert_eq!(calls.get(), 0);
    }
    let failure =
        OwnedTokenSource::new(&session, LIMITS, |_, _| Err::<TokenKind, _>("retained failure"));
    assert_eq!(failure.err(), Some(SourceAdapterError::TokenBinding("retained failure")));
}

#[test]
fn structural_holes_remain_typed_and_are_never_tokenized() {
    let mut grammar = grammar();
    for (id, admits_variables) in [(1, true), (2, false)] {
        grammar.categories.push(core::Category {
            id: core::CategoryId(id),
            name: format!("Other{id}"),
            carrier: core::Carrier::Dynamic,
            primary: false,
            admits_variables,
        });
    }
    let image = compile_parser_image(&grammar).expect("image");
    let host = core::DefaultRuntimeHost;
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("parser");
    let pieces = [
        core::RuntimeTemplatePiece::Hole(0),
        core::RuntimeTemplatePiece::Text("123".into()),
    ];
    let holes = [core::RuntimeTemplateHole {
        id: 0,
        category: Some(core::CategoryId(0)),
    }];
    let session = parser
        .lexical_template_session(&pieces, &holes)
        .expect("structural input");
    let calls = Cell::new(0);
    let source = OwnedTokenSource::new(&session, LIMITS, |id, text| {
        calls.set(calls.get() + 1);
        kind(id, text)
    })
    .expect("source");
    let hole = source.hole_at(0).expect("typed hole");
    assert_eq!(hole.id, 0);
    assert_eq!(hole.category, Some(core::CategoryId(0)));
    assert_eq!(source.peek_kind(0), None);
    assert_eq!(source.peek_text(0), None);
    assert!(!source.is_logical_eoi(0));
    assert_eq!(source.token_occurrence(0, 0), None);
    let after = source.hole_target(0).expect("existing hole successor");
    let edge = source
        .structural_hole_edge(core::CategoryId(0), 0)
        .expect("admitted category edge");
    assert_eq!(source.position(after), Some(edge.end));
    assert_eq!(
        source.structural_hole_edge(core::CategoryId(1), 0),
        None,
        "typed category mismatch"
    );
    assert_eq!(
        source.structural_hole_edge(core::CategoryId(2), 0),
        None,
        "nonvariable category"
    );
    assert_eq!(source.structural_hole_edge(core::CategoryId(3), 0), None, "unknown category");
    assert_eq!(source.peek_text(after), Some("123"));
    let accepted = session
        .nodes()
        .flat_map(|(_, n)| &n.edges)
        .filter(|e| matches!(e, LexicalEdge::Accepted { .. }))
        .count();
    assert_eq!(calls.get(), accepted, "only original text edges invoke token observers");
}

#[test]
fn equal_offsets_keep_distinct_modes_and_refutation_evidence() {
    let mut grammar = grammar();
    grammar.tokens.clear();
    for (id, text, mode, push, pop) in [
        (0, "xy", 0, None, false),
        (1, "x", 0, Some(core::ModeId(1)), false),
        (2, "y", 1, None, false),
        (3, ")", 1, None, true),
        (4, ")", 0, None, false),
        (5, "z!", 0, None, false),
        (6, "z", 0, None, true),
    ] {
        grammar.tokens.push(core::TokenDefinition {
            id: TokenId(id),
            name: format!("mode{id}"),
            pattern: core::TokenPattern::Literal(text.into()),
            category: None,
            evaluation: None,
            priority: 10 - id as i16,
            mode: core::ModeId(mode),
            channel: "main".into(),
            transition: core::ModeTransition { push, pop },
            decoder: core::TokenDecoder::Text,
            reservation: core::Reservation::None,
        });
    }
    grammar.modes = vec![
        core::LexerMode {
            id: core::ModeId(0),
            name: "default".into(),
            token_ids: vec![TokenId(0), TokenId(1), TokenId(4), TokenId(5), TokenId(6)],
            raw: false,
        },
        core::LexerMode {
            id: core::ModeId(1),
            name: "nested".into(),
            token_ids: vec![TokenId(2), TokenId(3)],
            raw: false,
        },
    ];
    let image = compile_parser_image(&grammar).expect("mode image");
    let host = core::DefaultRuntimeHost;
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("parser");
    // Different token extents, not conflicting transitions on a coaccepting
    // token span, yield two valid contexts at the same later byte position.
    let session = parser.lexical_session("xy)").expect("mode lattice");
    let source = OwnedTokenSource::new(&session, LIMITS, |_, text| {
        Ok::<_, ()>(TokenKind::Fixed(text.into()))
    })
    .expect("source");
    let same_offset: Vec<_> = (0..source.len())
        .filter(|id| source.position(*id).expect("position").offset == 2)
        .collect();
    assert_eq!(same_offset.len(), 2, "two mode contexts share byte two");
    assert_ne!(source.position(same_offset[0]), source.position(same_offset[1]));
    assert_ne!(source.next_pos(0, 0), source.next_pos(0, 1));
    let pieces = [
        core::RuntimeTemplatePiece::Text("xy".into()),
        core::RuntimeTemplatePiece::Hole(0),
        core::RuntimeTemplatePiece::Text(")".into()),
    ];
    let holes = [core::RuntimeTemplateHole {
        id: 0,
        category: Some(core::CategoryId(0)),
    }];
    let template = parser
        .lexical_template_session(&pieces, &holes)
        .expect("context-carrying hole");
    let structural = OwnedTokenSource::new(&template, LIMITS, |_, text| {
        Ok::<_, ()>(TokenKind::Fixed(text.into()))
    })
    .expect("context source");
    let hole_nodes: Vec<_> = (0..structural.len())
        .filter(|node| structural.position(*node).expect("position").offset == 2)
        .collect();
    assert_eq!(hole_nodes.len(), 2);
    let edges: Vec<_> = hole_nodes
        .iter()
        .map(|node| {
            structural
                .structural_hole_edge(core::CategoryId(0), *node)
                .expect("hole in each context")
        })
        .collect();
    assert_ne!(edges[0].start, edges[1].start);
    assert_ne!(edges[0].end, edges[1].end, "same offsets do not erase mode contexts");
    for edge in edges {
        assert_eq!(edge.end, template.canonical_position(edge.start.at(3)));
        assert!(structural.node_id(edge.end).is_some());
    }
    let refuted_session = parser
        .lexical_session("z!")
        .expect("secondary pop is refuted");
    let source = OwnedTokenSource::new(&refuted_session, LIMITS, |_, text| {
        Ok::<_, ()>(TokenKind::Fixed(text.into()))
    })
    .expect("source retains original refutation");
    let mut refutations = 0;
    for node in 0..source.len() {
        let evidence = source.evidence_at(node).expect("original node");
        for edge in &evidence.edges {
            if let LexicalEdge::Refuted { reason, .. } = edge {
                assert!(matches!(reason, core::RuntimeError::LexerModeUnderflow { byte: 0 }));
                refutations += 1;
            }
        }
    }
    assert_eq!(refutations, 1);
    let total_edges: usize = refuted_session
        .nodes()
        .map(|(_, node)| node.edges.len())
        .sum();
    let calls = Cell::new(0);
    let too_small = OwnedTokenSource::new(
        &refuted_session,
        SourceAdapterLimits {
            edges: total_edges - refutations,
            ..LIMITS
        },
        |_, text| {
            calls.set(calls.get() + 1);
            Ok::<_, ()>(TokenKind::Fixed(text.into()))
        },
    );
    assert_eq!(too_small.err(), Some(SourceAdapterError::EdgeLimit));
    assert_eq!(calls.get(), 0, "refuted edges consume admission budget too");
}

fn retained_budget_grammar() -> core::GrammarCoreV1 {
    let mut grammar = grammar();
    grammar.wpda_token_observations = Some(vec![
        Some(core::WpdaTokenObservation::IntegerLit("Number".into())),
        Some(core::WpdaTokenObservation::Fixed("12".into())),
        None, // Trivia is not an Accepted token observation.
    ]);
    grammar
}

#[test]
fn admitted_factory_charges_primary_kind_payload_before_allocation() {
    let grammar = retained_budget_grammar();
    let image = compile_parser_image(&grammar).expect("compile payload budget fixture");
    let host = core::DefaultRuntimeHost;
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("admit payload budget fixture");
    let session = parser
        .lexical_session("7")
        .expect("single-edge lexical evidence");
    // One byte of source text plus six bytes of the retained typed-kind name.
    for budget in [1, 6] {
        assert_eq!(
            OwnedTokenSource::from_admitted_session(
                &session,
                SourceAdapterLimits { text_bytes: budget, ..LIMITS }
            )
            .err(),
            Some(SourceAdapterError::TextLimit),
            "budget {budget} must not omit the six kind bytes",
        );
    }
    let source = OwnedTokenSource::from_admitted_session(
        &session,
        SourceAdapterLimits { text_bytes: 7, ..LIMITS },
    )
    .expect("exact primary source and kind budget");
    assert_eq!(source.peek_kind(0), Some(TokenKind::IntegerLit("Number".into())));
    assert_eq!(source.peek_text(0), Some("7"));
    assert!(source.peek_alternatives(0).is_empty());
}

#[test]
fn admitted_factory_prepays_lazy_secondary_text_and_kind_copies() {
    let grammar = retained_budget_grammar();
    let image = compile_parser_image(&grammar).expect("compile lazy copy budget fixture");
    let host = core::DefaultRuntimeHost;
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("admit lazy copy budget fixture");
    let session = parser
        .lexical_session("12")
        .expect("ambiguous lexical evidence");
    let start = session.canonical_position(LexPosition::START);
    let ids: Vec<_> = session
        .node(start)
        .expect("original start node")
        .edges
        .iter()
        .filter_map(|edge| match edge {
            LexicalEdge::Accepted { token, .. } => Some(*token),
            LexicalEdge::Refuted { .. } => None,
        })
        .collect();
    assert_eq!(ids, vec![TokenId(0), TokenId(1)], "fixture retains original primary order");
    // Primary: source 2 + kind 6. Secondary: (source 2 + kind 2) twice,
    // once in LexDag and once in the existing lazy LexAlternative cache.
    for budget in [12, 15] {
        assert_eq!(
            OwnedTokenSource::from_admitted_session(
                &session,
                SourceAdapterLimits { text_bytes: budget, ..LIMITS }
            )
            .err(),
            Some(SourceAdapterError::TextLimit),
            "budget {budget} must prepay both lazy secondary payloads",
        );
    }
    let source = OwnedTokenSource::from_admitted_session(
        &session,
        SourceAdapterLimits { text_bytes: 16, ..LIMITS },
    )
    .expect("exact primary plus doubled secondary budget");
    assert_eq!(source.peek_kind(0), Some(TokenKind::IntegerLit("Number".into())));
    assert_eq!(
        source
            .token_occurrence(0, 1)
            .expect("secondary origin")
            .token,
        TokenId(1)
    );
    let alternatives = source.peek_alternatives(0);
    assert_eq!(alternatives.len(), 1, "only the secondary is materialized");
    assert_eq!(alternatives[0].kind, TokenKind::Fixed("12".into()));
    assert_eq!(alternatives[0].text, "12");
    assert!(
        std::ptr::eq(alternatives, source.peek_alternatives(0)),
        "repeated reads reuse the original lazy cache"
    );
}

#[test]
fn source_limits_accept_exact_census_and_reject_each_one_below_before_observation() {
    let grammar = retained_budget_grammar();
    let image = compile_parser_image(&grammar).expect("compile exact-census fixture");
    let host = core::DefaultRuntimeHost;
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("admit exact-census fixture");
    for input in ["7", "12", " 12 123 ", "123 12 7"] {
        let session = parser
            .lexical_session(input)
            .expect("original lexical evidence");
        let nodes = session.nodes().count();
        let edges = session.nodes().map(|(_, node)| node.edges.len()).sum();
        let mut accepted = 0;
        let mut text_bytes = 0;
        let mut kind_bytes = 0;
        for (position, node) in session.nodes() {
            let mut ordinal = 0;
            for edge in &node.edges {
                if let LexicalEdge::Accepted { token, target, .. } = edge {
                    let copies = if ordinal == 0 { 1 } else { 2 };
                    ordinal += 1;
                    accepted += 1;
                    text_bytes += copies * (target.offset - position.offset);
                    kind_bytes += copies
                        * match token.0 {
                            0 => "Number".len(),
                            1 => "12".len(),
                            _ => panic!("hidden trivia must not become an accepted token"),
                        };
                }
            }
        }
        let exact = SourceAdapterLimits { nodes, edges, text_bytes };
        let calls = Cell::new(0);
        let source = OwnedTokenSource::new(&session, exact, |token, text| {
            calls.set(calls.get() + 1);
            kind(token, text)
        })
        .expect("all three exact bounds admit the complete source");
        assert_eq!(source.len(), nodes);
        assert_eq!(calls.get(), accepted);
        for (limit, expected) in [
            (SourceAdapterLimits { nodes: nodes - 1, ..exact }, SourceAdapterError::NodeLimit),
            (SourceAdapterLimits { edges: edges - 1, ..exact }, SourceAdapterError::EdgeLimit),
            (
                SourceAdapterLimits { text_bytes: text_bytes - 1, ..exact },
                SourceAdapterError::TextLimit,
            ),
        ] {
            calls.set(0);
            let result = OwnedTokenSource::new(&session, limit, |token, text| {
                calls.set(calls.get() + 1);
                kind(token, text)
            });
            assert_eq!(result.err(), Some(expected), "input {input:?}");
            assert_eq!(calls.get(), 0, "whole-source admission precedes observation");
        }
        let retained = SourceAdapterLimits {
            text_bytes: text_bytes + kind_bytes,
            ..exact
        };
        let source = OwnedTokenSource::from_admitted_session(&session, retained)
            .expect("exact source plus kind storage budget");
        for node in 0..source.len() {
            // Materialize every secondary cache covered by the reservation.
            let _ = source.peek_alternatives(node);
        }
        assert_eq!(
            OwnedTokenSource::from_admitted_session(
                &session,
                SourceAdapterLimits {
                    text_bytes: retained.text_bytes - 1,
                    ..retained
                },
            )
            .err(),
            Some(SourceAdapterError::TextLimit),
            "a one-byte deficit must not be hidden by lazy materialization",
        );
    }
}
