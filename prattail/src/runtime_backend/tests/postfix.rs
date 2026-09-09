use super::*;

fn grammar(associativity: core::Associativity, power: Option<u16>) -> core::GrammarCoreV1 {
    let mut grammar = core::GrammarCoreV1::new("Postfix");
    grammar.categories = vec![category(0, "Expr", true), category(1, "Nat", false)];
    grammar.tokens = ["a", "*", "+", "?", "(", ")", "{", ",", "}"]
        .into_iter()
        .enumerate()
        .map(|(id, literal)| {
            token(
                id as u32,
                literal,
                core::TokenPattern::Literal(literal.into()),
                core::TokenDecoder::Unit,
            )
        })
        .collect();
    grammar.tokens.push(token(
        9,
        "integer",
        core::TokenPattern::Regex("[0-9]+".into()),
        core::TokenDecoder::Integer { radix: None },
    ));
    grammar.tokens[9].category = Some(core::CategoryId(1));
    grammar.modes[0].token_ids = (0..10).map(core::TokenId).collect();
    let terminal = |id| core::SyntaxItem::Token(core::TokenId(id));
    let operand = |id, name: &str| core::SyntaxItem::Category {
        category: core::CategoryId(id),
        slot: name.into(),
    };
    for (id, (label, syntax, postfix, arity)) in [
        ("Atom", vec![terminal(0)], false, 0),
        ("Star", vec![operand(0, "body"), terminal(1)], true, 1),
        ("Plus", vec![operand(0, "body"), terminal(2)], true, 1),
        ("Optional", vec![operand(0, "body"), terminal(3)], true, 1),
        ("Group", vec![terminal(4), operand(0, "body"), terminal(5)], false, 1),
        (
            "Repeat",
            vec![
                operand(0, "body"),
                terminal(6),
                operand(1, "lower"),
                terminal(7),
                operand(1, "upper"),
                terminal(8),
            ],
            true,
            3,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        grammar.reductions.push(reduction(0, id as u32, arity));
        grammar.productions.push(core::Production {
            id: core::ProductionId(id as u32),
            constructor: core::ConstructorId(id as u32),
            label: label.into(),
            result: core::CategoryId(0),
            syntax,
            precedence: if postfix {
                core::Precedence {
                    binding_power: power,
                    associativity,
                    shares_previous_level: false,
                }
            } else {
                core::Precedence::default()
            },
            classification: core::ProductionClass {
                postfix,
                ..core::ProductionClass::default()
            },
            reduction: id as u32,
            provenance: None,
        });
    }
    grammar
}

#[test]
fn postfix_admission_respects_declared_associativity_and_optional_power() {
    for power in [None, Some(0), Some(30), Some(u16::MAX)] {
        for assoc in [
            core::Associativity::Left,
            core::Associativity::Right,
            core::Associativity::NonAssociative,
        ] {
            let grammar = grammar(assoc, power);
            for input in ["a**", "a*+", "a?{2,3}", "a{2,3}+"] {
                let result = parse(&grammar, input);
                if assoc == core::Associativity::NonAssociative && power.is_some() {
                    assert!(
                        matches!(result, Err(core::RuntimeError::NoParse)),
                        "{assoc:?}/{power:?}/{input}: {result:?}"
                    );
                } else {
                    assert_eq!(result.expect("existing admission").len(), 1);
                }
            }
            for input in ["(a*)*", "(a*)+", "(a?){2,3}", "(a{2,3})+"] {
                assert_eq!(parse(&grammar, input).expect("unranked group").len(), 1);
            }
        }
    }
}

#[test]
fn postfix_strict_comparison_handles_ranked_atoms_and_maximum_without_increment() {
    for (parent, child, accepted) in [
        (0, None, true),
        (0, Some(0), false),
        (0, Some(1), true),
        (30, None, true),
        (30, Some(29), false),
        (30, Some(30), false),
        (30, Some(31), true),
        (u16::MAX, None, true),
        (u16::MAX, Some(u16::MAX - 1), false),
        (u16::MAX, Some(u16::MAX), false),
    ] {
        let mut grammar = grammar(core::Associativity::NonAssociative, Some(parent));
        grammar.productions[0].precedence.binding_power = child;
        let result = parse(&grammar, "a*");
        if accepted {
            assert_eq!(result.expect("strict or unranked atom").len(), 1);
        } else {
            assert!(matches!(result, Err(core::RuntimeError::NoParse)), "{parent}/{child:?}");
        }
    }
}

#[test]
fn postfix_filter_retains_independent_readings_with_exact_payload_cost_and_rank() {
    let mut before = grammar(core::Associativity::Left, Some(30));
    before.tokens.push(token(
        10,
        "double_star_atom",
        core::TokenPattern::Literal("a**".into()),
        core::TokenDecoder::Unit,
    ));
    before.modes[0].token_ids.push(core::TokenId(10));
    for id in [6, 7] {
        before.reductions.push(reduction(0, id, 0));
        before.productions.push(core::Production {
            id: core::ProductionId(id),
            constructor: core::ConstructorId(id),
            label: format!("Independent{id}"),
            result: core::CategoryId(0),
            syntax: vec![core::SyntaxItem::Token(core::TokenId(10))],
            precedence: core::Precedence::default(),
            classification: core::ProductionClass::default(),
            reduction: id,
            provenance: None,
        });
    }
    let original = parse(&before, "a**").expect("three supplied readings");
    assert_eq!(original.len(), 3);
    let expected: Vec<_> = original
        .into_iter()
        .filter(|candidate| candidate.production.is_some_and(|id| id.0 >= 6))
        .collect();
    assert_eq!(expected.len(), 2);
    let mut after = before.clone();
    after.productions[1].precedence.associativity = core::Associativity::NonAssociative;
    assert_eq!(parse(&after, "a**").expect("two independent readings survive"), expected);

    let image = compile_parser_image(&after).expect("compile");
    let host = core::DefaultRuntimeHost;
    let parser = core::RuntimeParser::new_with_policy(
        &after,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
        core::RuntimePolicy { max_parse_items: 0, ..Default::default() },
    )
    .expect("admitted bounded parser");
    assert!(matches!(parser.parse("a**"), Err(core::RuntimeError::ParseItemLimit)));
    let mut stale = image;
    stale.compiler_abi = "mettail-rtn/3".into();
    assert!(matches!(
        stale.verify_executable(&after, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI),
        Err(core::ImageError::CompilerAbiMismatch)
    ));
}
