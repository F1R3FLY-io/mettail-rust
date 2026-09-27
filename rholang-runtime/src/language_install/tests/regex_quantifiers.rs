use super::*;
use mettail_grammar_core::{DynamicTerm, DynamicValue, GrammarCoreV1, SourceSpan};

const SOURCE: &str = include_str!("../../../tests/fixtures/regex_gslt.rho");

/// Exercise the actual DDL producer, original owned adapter and installed
/// dispatch together. This library gate does not establish public-node cutover.
#[test]
fn practical_regex_ddl_drives_original_wpda_with_complete_owned_metadata() {
    use mettail_prattail::runtime_backend::{RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI};
    use mettail_prattail::wpda_owned::{
        absorption::derive_absorption_rows,
        actions::{OwnedActionProvider, OwnedTerm},
        engine::OwnedWpdaEngine,
        source::{OwnedTokenSource, SourceAdapterLimits},
    };
    use mettail_prattail::wpda_rule_analysis::{
        authored_descriptors::{derive_authored_descriptors, DescriptorOptions},
        authored_synthesis::derive_authored_rules,
    };
    use mettail_prattail::wpda_runtime::WpdaResolveResult;
    use mettail_prattail::wpda_walker::{RealizeRequestMode, WpdaWalker};
    use std::convert::Infallible;

    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("actual inline Regex DDL installs");
    let handle = runtime
        .resolve(&batch.exports[0].handle, LanguageRight::Parse)
        .expect("actual parse authority");
    let installed = runtime
        .service
        .table()
        .authorize(&handle, LanguageRight::Parse)
        .expect("installed Regex artifact");
    let core = installed.core();
    assert!(core.wpda_token_observations.is_some(),
        "DDL lowering must retain the original token-kind observations, not guess them at parse time");
    // The DDL lowerer's terms loop emits exactly one production per authored
    // source term, in that order. It does not append bridge helper productions.
    assert!(core
        .productions
        .iter()
        .all(|production| production.authored.is_some()));
    for label in ["PStar", "PPlus", "POptional", "PRepeat"] {
        let production = core
            .productions
            .iter()
            .find(|row| row.label == label)
            .expect("actual quantifier declaration");
        assert_eq!(
            production.precedence.associativity,
            mettail_grammar_core::Associativity::NonAssociative,
            "{label}"
        );
        assert_eq!(production.precedence.binding_power, Some(30), "{label}");
    }
    let receipt = core
        .wpda_original_occurrences
        .as_ref()
        .expect("actual DDL producer retains its exact original term roster");
    assert_eq!(receipt.len(), core.productions.len(), "this DDL producer appends no helpers");
    let occurrences: Vec<_> = receipt.iter().map(|id| id.0 as usize).collect();
    let synthesis = derive_authored_rules(core, &occurrences, |_| Ok::<_, Infallible>(()))
        .expect("complete actual Regex declaration uses original synthesis");
    let descriptors = derive_authored_descriptors(
        core,
        &occurrences,
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
    .expect("complete Regex descriptor domain");
    let primary_for = |category: &str| {
        u16::try_from(
            descriptors
                .synthesis
                .categories
                .iter()
                .position(|name| name == category)
                .expect("original category census"),
        )
        .expect("checked category index")
    };
    let parser = mettail_grammar_core::RuntimeParser::new(
        core,
        installed.parser_image().expect("installed runtime image"),
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        runtime.host.as_ref(),
    )
    .expect("actual host-authorized lexical and semantic workers");
    let absorption =
        derive_absorption_rows(core, &descriptors).expect("exact original absorption queries");
    let &(alt_result, alt_rule) = descriptors
        .label_index
        .get(&("Pattern".into(), "PAlt".into()))
        .expect("original PAlt coordinates");
    assert!(
        matches!(absorption.get(&(primary_for("Pattern"), alt_result, alt_rule)), Some(None)),
        "PAlt has an explicit original nonnative-atom refusal, not a missing receipt"
    );
    let collect = |source: &OwnedTokenSource<'_, '_, '_, '_>, primary, input: &str| {
        let actions = OwnedActionProvider::new(source, &descriptors, |_| Ok(()))
            .expect("all original Regex action rows admitted");
        let engine =
            OwnedWpdaEngine::new(&descriptors, &actions, primary, &[], &absorption, |_| Ok(()))
                .expect("all original Regex routing rows admitted");
        let mut walker = WpdaWalker::new_for_category(engine, primary, 0);
        walker
            .run_to_end_of_input(100_000, source)
            .expect("bounded original walker");
        let resolved = walker.resolve_at_end_of_input(source);
        let WpdaResolveResult::Accepted { roots, .. } = resolved else {
            return Err(resolved);
        };
        let mut actual = Vec::new();
        for root in roots {
            let readings = walker
                .realize_root_complete_with_weights(root, 256)
                .expect("complete bounded candidate extraction");
            assert!(readings.len() < 256, "{input:?}: reaching the cap is not exhaustive evidence");
            for (value, weight) in readings {
                actual.push((
                    value
                        .downcast_ref::<OwnedTerm>()
                        .expect("owned category carrier")
                        .clone(),
                    weight,
                ));
            }
        }
        eprintln!("{input:?}: retained {} weighted readings", actual.len());
        Ok(actual)
    };
    let assert_installed_family =
        |actual: &[(OwnedTerm, mettail_prattail::automata::lex_weight::LexicographicWeight)],
         installed: &[mettail_grammar_core::WeightedParse],
         input: &str| {
            assert_eq!(installed.len(), actual.len(), "installed complete family for {input:?}");
            for (term, weight) in actual {
                assert_eq!(
                    installed
                        .iter()
                        .filter(|candidate| {
                            candidate.syntax == term.syntax
                                && candidate.value == term.value
                                && candidate.production == term.production
                                && candidate.weight.shared_wpda() == Some(weight)
                        })
                        .count(),
                    1,
                    "unchanged original syntax/value/production/full weight for {input:?}"
                );
            }
        };
    let policy = mettail_grammar_core::RuntimePolicy {
        max_parse_items: 100_000,
        max_semantic_results: 256,
        ..Default::default()
    };
    // The old normalizer has neither implicit variable rules nor the original
    // constructor-free grouping branch. It witnesses the authored ground term,
    // not the complete shared WPDA family. Where parentheses also admit generic
    // grouping, explicitly supply that second exact ground term. The generated
    // consumer parity fixture independently checks both grouping interpretations.
    // This partition is test observation, never a parser/publication policy.
    let check_variable_free = |actual: &[(
        OwnedTerm,
        mettail_prattail::automata::lex_weight::LexicographicWeight,
    )],
                               expected: &[mettail_grammar_core::WeightedParse],
                               generic_grouping: Option<&DynamicValue>,
                               input: &str| {
        let ground: Vec<_> = actual
            .iter()
            .filter(|(term, _)| variable_free(&term.syntax))
            .collect();
        assert_eq!(ground.len(), expected.len() + usize::from(generic_grouping.is_some()),
            "variable-free candidate count for {input:?}; all readings: {actual:?}; expected: {expected:?}");
        assert_eq!(expected.len(), 1, "one variable-free contract result for {input:?}");
        for (syntax, value) in std::iter::once((&expected[0].syntax, &expected[0].value))
            .chain(generic_grouping.map(|term| (term, term)))
        {
            assert_eq!(
                ground
                    .iter()
                    .filter(|(term, _)| {
                        same_structure(&term.syntax, syntax) && same_structure(&term.value, value)
                    })
                    .count(),
                1,
                "each exact ground interpretation occurs once for {input:?}: {actual:?}"
            );
        }
    };
    for (category_name, input) in [
        ("Pattern", "(?!)"),
        ("Pattern", "()"),
        ("Pattern", "."),
        ("Pattern", "a"),
        ("Pattern", "ab*|c"),
        ("Pattern", "abc"),
        ("Pattern", "a|b|c"),
        ("Pattern", "(a*)?"),
        ("Pattern", "λ+"),
        ("Pattern", "a{2,3}"),
        ("Pattern", "(a*){2,3}"),
        ("Pattern", "(a{2,3})+"),
        ("Computation", "nullable(a{2,3})"),
        ("Computation", "nullable(a{0,0})"),
    ] {
        let category = resolve_required_category(core, category_name).expect("declared category");
        let expected = parser
            .parse_category(input, category)
            .expect("existing Regex contract");
        let session = parser
            .lexical_session(input)
            .expect("actual lexical session");
        let source = OwnedTokenSource::from_admitted_session(
            &session,
            SourceAdapterLimits {
                nodes: 4096,
                edges: 16384,
                text_bytes: 1_048_576,
            },
        )
        .expect("retained DDL token observations");
        let actual = collect(&source, primary_for(category_name), input)
            .expect("original walker accepts the complete Regex input");
        let installed_results = runtime
            .service
            .table()
            .parse(&handle, input, Some(category), runtime.host.as_ref(), policy)
            .expect("installed dispatch runs the shared original walker");
        assert_installed_family(&actual, &installed_results, input);
        if input == "a" {
            // Both implicit variable routes exist, but the original generated
            // semantic visitor gives PVar(a) and PLiteral(SVar(a)) the same
            // exact key. Keep one representative AND the distinct literal.
            // The generated-consumer parity fixture proves the key equality;
            // this is not permission to filter all variable interpretations.
            let variable = mettail_grammar_core::native_variable::get_or_create_var("a");
            let pattern = resolve_required_category(core, "Pattern").expect("Pattern");
            let scalar = resolve_required_category(core, "Scalar").expect("Scalar");
            let mut literal_variable = term(
                core,
                "PLiteral",
                vec![DynamicValue::NativeVariable {
                    category: scalar,
                    variable: variable.clone(),
                }],
            );
            if let DynamicValue::Term(term) = &mut literal_variable {
                term.span = SourceSpan { start: 0, end: 1 };
            }
            let variable_representatives =
                [DynamicValue::NativeVariable { category: pattern, variable }, literal_variable];
            assert_eq!(actual.len(), 2, "the two original semantic equivalence classes");
            assert_eq!(
                actual
                    .iter()
                    .filter(|(term, _)| {
                        variable_representatives
                            .iter()
                            .any(|expected| &term.syntax == expected && &term.value == expected)
                    })
                    .count(),
                1,
                "one native-variable representative with unchanged identity: {actual:?}"
            );
            assert_eq!(
                actual
                    .iter()
                    .filter(|(term, _)| {
                        term.syntax == expected[0].syntax && term.value == expected[0].value
                    })
                    .count(),
                1,
                "the literal class remains distinct from native variables: {actual:?}"
            );
        }
        let ungrouped = match input {
            "(a*)?" => Some(("*", "?")),
            "(a*){2,3}" => Some(("*", "{2,3}")),
            "(a{2,3})+" => Some(("{2,3}", "+")),
            _ => None,
        }
        .map(|(inner, outer)| {
            quantifier(
                core,
                outer,
                quantifier(
                    core,
                    inner,
                    term(core, "PLiteral", vec![DynamicValue::Text("a".into())]),
                ),
            )
        });
        check_variable_free(&actual, &expected, ungrouped.as_ref(), input);
    }

    let pattern = resolve_required_category(core, "Pattern").expect("Pattern");
    for inner in ["*", "+", "?", "{2,3}"] {
        for outer in ["*", "+", "?", "{2,3}"] {
            for (input, accepted) in
                [(format!("a{inner}{outer}"), false), (format!("(a{inner}){outer}"), true)]
            {
                let session = parser
                    .lexical_session(&input)
                    .expect("quantifier text lexes");
                let source = OwnedTokenSource::from_admitted_session(
                    &session,
                    SourceAdapterLimits {
                        nodes: 4096,
                        edges: 16384,
                        text_bytes: 1_048_576,
                    },
                )
                .expect("exact retained quantifier token observations");
                let result = collect(&source, primary_for("Pattern"), &input);
                if accepted {
                    let actual = result.expect("grouped quantifiers are accepted");
                    let installed_results = runtime
                        .service
                        .table()
                        .parse(&handle, &input, Some(pattern), runtime.host.as_ref(), policy)
                        .expect("installed grouped quantifier route");
                    assert_installed_family(&actual, &installed_results, &input);
                    let expected = parser
                        .parse_category(&input, pattern)
                        .expect("grouped contract");
                    let ungrouped = quantifier(
                        core,
                        outer,
                        quantifier(
                            core,
                            inner,
                            term(core, "PLiteral", vec![DynamicValue::Text("a".into())]),
                        ),
                    );
                    check_variable_free(&actual, &expected, Some(&ungrouped), &input);
                } else {
                    assert!(matches!(runtime.service.table()
                        .parse(&handle, &input, Some(pattern), runtime.host.as_ref(), policy),
                        Err(mettail_grammar_core::InstalledParseError::Parse(
                            mettail_grammar_core::RuntimeError::NoParse))),
                        "installed route must reject adjacent nonassociative quantifiers: {input:?}");
                    match result {
                        Ok(actual) => assert!(actual.is_empty(), "all readings must reject {input:?}: {actual:?}"),
                        Err(WpdaResolveResult::ParseError { .. } | WpdaResolveResult::AcceptedWithTrailing { .. }) => {},
                        Err(other) => panic!("resource/action failure is not quantifier rejection for {input:?}: {other:?}"),
                    }
                }
            }
        }
    }

    // Execute the declared List(Text) route with typed structural input. Text
    // holes stay holes; they are never rendered as guessed guest literals.
    let text = resolve_required_category(core, "Text").expect("declared Text category");
    let computation =
        resolve_required_category(core, "Computation").expect("declared Computation category");
    let pieces = [
        RuntimeTemplatePiece::Text("joinPieces([".into()),
        RuntimeTemplatePiece::Hole(0),
        RuntimeTemplatePiece::Text(",".into()),
        RuntimeTemplatePiece::Hole(1),
        RuntimeTemplatePiece::Text("])".into()),
    ];
    let holes = [
        mettail_grammar_core::RuntimeTemplateHole { id: 0, category: Some(text) },
        mettail_grammar_core::RuntimeTemplateHole { id: 1, category: Some(text) },
    ];
    let expected = parser
        .parse_template(&pieces, &holes, Some(computation))
        .expect("declared JoinPieces structural syntax");
    let session = parser
        .lexical_template_session(&pieces, &holes)
        .expect("actual structural lexer");
    let source = OwnedTokenSource::from_admitted_session(
        &session,
        SourceAdapterLimits {
            nodes: 4096,
            edges: 16384,
            text_bytes: 1_048_576,
        },
    )
    .expect("typed Text occurrences retain their source identity");
    let actual = collect(&source, primary_for("Computation"), "JoinPieces with two Text holes")
        .expect("structural collection is accepted");
    assert_eq!(actual.len(), expected.len(), "complete JoinPieces candidate count");
    assert_eq!(expected.len(), 1, "one declared JoinPieces structure");
    assert_structure(&actual[0].0.syntax, &expected[0].syntax, "JoinPieces syntax");
    assert_structure(&actual[0].0.value, &expected[0].value, "JoinPieces value");
    let installed_results = runtime
        .service
        .table()
        .parse_template(
            &handle,
            &pieces,
            &holes,
            Some(computation),
            runtime.host.as_ref(),
            policy,
            LanguageRight::Construct,
        )
        .expect("installed route preserves typed Text holes");
    assert_installed_family(&actual, &installed_results, "JoinPieces with two Text holes");

    for (restricted, expected) in [
        (
            mettail_grammar_core::RuntimePolicy { max_parse_items: 0, ..policy },
            mettail_grammar_core::RuntimeError::ParseItemLimit,
        ),
        (
            mettail_grammar_core::RuntimePolicy { max_forest_nodes: 0, ..policy },
            mettail_grammar_core::RuntimeError::ForestNodeLimit,
        ),
        (
            mettail_grammar_core::RuntimePolicy { max_semantic_results: 1, ..policy },
            mettail_grammar_core::RuntimeError::SemanticResultLimit,
        ),
    ] {
        match runtime.service.table().parse(
            &handle,
            "a",
            Some(pattern),
            runtime.host.as_ref(),
            restricted,
        ) {
            Err(mettail_grammar_core::InstalledParseError::Parse(error)) => {
                assert_eq!(error, expected)
            },
            other => panic!("installed exhaustion must not publish a partial family: {other:?}"),
        }
    }

    // The actual ambiguous input must exercise the owned persistent-key hook.
    // Exhaustion is a failed realization request, never an empty family or a
    // successfully published prefix of that request's results.
    let session = parser
        .lexical_session("a")
        .expect("literal/variable witness lexes");
    let source = OwnedTokenSource::from_admitted_session(
        &session,
        SourceAdapterLimits {
            nodes: 4096,
            edges: 16384,
            text_bytes: 1_048_576,
        },
    )
    .expect("actual ambiguity source");
    for entry_limit in [true, false] {
        let actions = OwnedActionProvider::new(&source, &descriptors, |_| Ok(()))
            .expect("complete owned actions");
        let primary = primary_for("Pattern");
        let engine =
            OwnedWpdaEngine::new(&descriptors, &actions, primary, &[], &absorption, |_| Ok(()))
                .expect("complete owned routing");
        let walker = WpdaWalker::new_for_category(engine, primary, 0);
        let mut walker = if entry_limit {
            walker.with_semantic_key_cache_entries(0)
        } else {
            walker.with_semantic_key_logical_bytes(0)
        };
        walker
            .run_to_end_of_input(100_000, &source)
            .expect("bounded recognition");
        let error = match walker.resolve_at_end_of_input(&source) {
            WpdaResolveResult::RealizationFailed { error, .. } => error,
            WpdaResolveResult::Accepted { roots, .. } => roots
                .into_iter()
                .find_map(|root| {
                    walker
                        .realize_root_to_terms_with_weights(
                            root,
                            Some(256),
                            RealizeRequestMode::BoundedEnumeration,
                        )
                        .err()
                })
                .expect("the ambiguous family must report key-resource exhaustion"),
            other => panic!("key exhaustion is not syntax rejection: {other:?}"),
        };
        use mettail_prattail::wpda_runtime::RealizationError;
        use mettail_runtime::exact_semantic_key::ContentKeyCacheError;
        match (entry_limit, error) {
            (
                true,
                RealizationError::SemanticKey(ContentKeyCacheError::ResourceExhausted {
                    limit: 0,
                    ..
                }),
            )
            | (
                false,
                RealizationError::SemanticKey(ContentKeyCacheError::KeyBytesExhausted {
                    limit: 0,
                    ..
                }),
            ) => {},
            (_, error) => panic!("retain the exact exhausted resource: {error:?}"),
        }
    }
}

fn variable_free(value: &DynamicValue) -> bool {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        match value {
            DynamicValue::NativeVariable { .. } => return false,
            DynamicValue::Term(term) => pending.extend(&term.fields),
            DynamicValue::Sequence(values) | DynamicValue::Collection { entries: values, .. } => {
                pending.extend(values)
            },
            DynamicValue::TemplateHole { .. }
            | DynamicValue::Text(_)
            | DynamicValue::Integer(_)
            | DynamicValue::Boolean(_)
            | DynamicValue::Bytes(_)
            | DynamicValue::Unit => {},
        }
    }
    true
}

fn term(core: &GrammarCoreV1, label: &str, fields: Vec<DynamicValue>) -> DynamicValue {
    let production = core
        .productions
        .iter()
        .find(|p| p.label == label)
        .expect("declared constructor");
    DynamicValue::Term(Box::new(DynamicTerm {
        category: production.result,
        constructor: production.constructor,
        fields,
        span: SourceSpan::default(),
    }))
}

fn quantifier(core: &GrammarCoreV1, suffix: &str, child: DynamicValue) -> DynamicValue {
    let (label, fields) = match suffix {
        "*" => ("PStar", vec![child]),
        "+" => ("PPlus", vec![child]),
        "?" => ("POptional", vec![child]),
        "{2,3}" => ("PRepeat", vec![child, DynamicValue::Integer(2), DynamicValue::Integer(3)]),
        _ => unreachable!("fixed quantifier matrix"),
    };
    term(core, label, fields)
}

fn assert_structure(actual: &DynamicValue, expected: &DynamicValue, source: &str) {
    assert!(
        same_structure(actual, expected),
        "{source}: actual {actual:?}; expected {expected:?}"
    );
}

fn same_structure(actual: &DynamicValue, expected: &DynamicValue) -> bool {
    // Source spans describe the spelling, not constructor structure. Check every
    // other field with an explicit worklist, including ordered native bounds.
    let mut pending = vec![(actual, expected)];
    while let Some((actual, expected)) = pending.pop() {
        match (actual, expected) {
            (DynamicValue::Term(actual), DynamicValue::Term(expected)) => {
                if actual.category != expected.category
                    || actual.constructor != expected.constructor
                    || actual.fields.len() != expected.fields.len()
                {
                    return false;
                }
                pending.extend(actual.fields.iter().zip(&expected.fields));
            },
            _ if actual != expected => return false,
            _ => {},
        }
    }
    true
}

#[test]
fn practical_regex_quantifiers_reject_adjacent_pairs_and_admit_grouping() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("actual inline Regex declaration installs");
    let token = &batch.exports[0].handle;
    let handle = runtime
        .resolve(token, LanguageRight::Parse)
        .expect("parse capability");
    let installed = runtime
        .service
        .table()
        .authorize(&handle, LanguageRight::Parse)
        .expect("installed language");
    let core = installed.core();
    let category = resolve_required_category(core, "Pattern").expect("Pattern category");
    let parse = |source: &str| {
        runtime
            .service
            .parse(&handle, source, Some(category), runtime.host.as_ref())
    };
    let literal = |text: &str| term(core, "PLiteral", vec![DynamicValue::Text(text.into())]);
    for inner in ["*", "+", "?", "{2,3}"] {
        for outer in ["*", "+", "?", "{2,3}"] {
            let adjacent = format!("a{inner}{outer}");
            assert!(
                matches!(parse(&adjacent), Err(InstalledParseError::Parse(RuntimeError::NoParse))),
                "{adjacent}: adjacent quantifiers must be rejected"
            );
            let grouped = format!("(a{inner}){outer}");
            let parses = parse(&grouped).unwrap_or_else(|error| panic!("{grouped}: {error:?}"));
            assert_eq!(parses.len(), 1, "{grouped}");
            let expected = quantifier(
                core,
                outer,
                term(core, "PGroup", vec![quantifier(core, inner, literal("a"))]),
            );
            assert_structure(&parses[0].syntax, &expected, &grouped);
            eprintln!("{adjacent}: rejected; {grouped}: exact constructor structure verified");
        }
    }
    for (source, expected) in [
        (
            "ab*|c",
            term(
                core,
                "PAlt",
                vec![
                    term(core, "PConcat", vec![literal("a"), quantifier(core, "*", literal("b"))]),
                    literal("c"),
                ],
            ),
        ),
        (
            "abc",
            term(
                core,
                "PConcat",
                vec![term(core, "PConcat", vec![literal("a"), literal("b")]), literal("c")],
            ),
        ),
        (
            "a|b|c",
            term(
                core,
                "PAlt",
                vec![term(core, "PAlt", vec![literal("a"), literal("b")]), literal("c")],
            ),
        ),
    ] {
        let parses = parse(source).unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(parses.len(), 1, "{source}");
        assert_structure(&parses[0].syntax, &expected, source);
    }
    assert_eq!(
        runtime
            .parse_source(token, "a*?", "Pattern")
            .expect("parse-only boundary"),
        LanguageParseOutcome::Rejected(LanguageParseRejection::NoParse)
    );
    assert_eq!(
        runtime
            .parse_source(token, "(a*)?", "Pattern")
            .expect("parse-only boundary"),
        LanguageParseOutcome::Accepted
    );
}
