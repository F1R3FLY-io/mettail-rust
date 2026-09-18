use super::*;

const SOURCE: &str = include_str!("../../../tests/fixtures/regex_gslt.rho");

#[test]
fn practical_regex_gslt_application_contains_the_checked_declaration_and_parses_once() {
    let application = include_str!("../../../tests/fixtures/regex_gslt_application.rho");
    assert_eq!(
        application.matches(SOURCE.trim()).count(),
        1,
        "the standalone application embeds exactly the service-tested declaration"
    );
    let _program = Proc::parse_via_wpda(application)
        .expect("one generated host parse includes the complete DDL and qualified FLT uses");
}

fn text_computation(
    runtime: &RholangLanguageRuntime,
    token: &Par,
    fragments: &[&str],
    text_values: &[&str],
) -> Par {
    assert_eq!(fragments.len(), text_values.len() + 1);
    let handle = runtime
        .resolve(token, LanguageRight::Construct)
        .expect("construct authority");
    let installed = runtime
        .service
        .table()
        .authorize(&handle, LanguageRight::Construct)
        .expect("installed language");
    let owner = grammar_fingerprint_label(handle.fingerprint());
    let mut pieces = Vec::with_capacity(fragments.len() + text_values.len());
    let mut holes = Vec::with_capacity(text_values.len());
    let mut fills = BTreeMap::new();
    for (index, fragment) in fragments.iter().enumerate() {
        pieces.push(RuntimeTemplatePiece::Text((*fragment).into()));
        if let Some(text) = text_values.get(index) {
            let id = u32::try_from(index).expect("small test hole index");
            let name = format!("text{index}");
            let ground = dynamic_syntax_to_ground_term(
                &mettail_grammar_core::DynamicValue::Text((*text).into()),
                installed.core(),
                &BTreeMap::new(),
            )
            .expect("native text reflection");
            fills.insert(
                name.clone(),
                mettail_rholang_codegen::reflect_ground_term_par(&ground, &owner),
            );
            holes.push(NamedRuntimeTemplateHole { id, name, category: Some("Text".into()) });
            pieces.push(RuntimeTemplatePiece::Hole(id));
        }
    }
    runtime
        .construct_template(token, &pieces, &holes, Some("Computation"), &fills)
        .expect("declared application computation with structural Text holes")
}

#[test]
fn practical_regex_guest_text_is_exact_and_native_text_holes_preserve_whitespace() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("the application's unchanged inline grammar installs");
    let token = &batch.exports[0].handle;
    let holes = [NamedRuntimeTemplateHole {
        id: 0,
        name: "text".into(),
        category: Some("Text".into()),
    }];
    let text = " \tλ\n${not_a_hole:Text}` ";
    let fills = BTreeMap::from([(
        "text".into(),
        new_gstring_par(text.into(), Vec::new(), false),
    )]);
    for prefix in ["fullMatch(a(b|c)+,", "search(λ+,"] {
        let pieces = [
            RuntimeTemplatePiece::Text(prefix.into()),
            RuntimeTemplatePiece::Hole(0),
            RuntimeTemplatePiece::Text(")".into()),
        ];
        let actual = runtime
            .construct_template(token, &pieces, &holes, Some("Computation"), &fills)
            .expect("declared guest syntax accepts structural native Text fills");
        let expected = text_computation(&runtime, token, &[prefix, ")"], &[text]);
        assert_eq!(actual.cmp(&expected), std::cmp::Ordering::Equal);
        let spaced = [
            RuntimeTemplatePiece::Text(format!("{prefix} ")),
            RuntimeTemplatePiece::Hole(0),
            RuntimeTemplatePiece::Text(")".into()),
        ];
        assert!(matches!(
            runtime.construct_template(token, &spaced, &holes, Some("Computation"), &fills),
            Err(LanguageFltConstructionError::Runtime(LanguageRuntimeError::Parse(
                InstalledParseError::Parse(mettail_grammar_core::RuntimeError::Lex { byte })
            ))) if byte == prefix.len()
        ));
    }
}

fn assert_regex_observation(
    runtime: &RholangLanguageRuntime,
    token: &Par,
    name: &str,
    input: &Par,
    expected: &Par,
) -> u64 {
    let report = runtime.execute_semantic(
        SemanticServiceRequest {
            handle: token,
            operation: SemanticOperation::Observe(name),
            input,
            limits: SemanticServiceLimits::default(),
        },
        || false,
    );
    let outputs = report.outcome.unwrap_or_else(|error| {
        panic!("{name}: {error:?}; work={}, kernel={:?}", report.work, report.kernel_work)
    });
    assert_eq!(outputs.len(), 1, "{name}: one complete deterministic observation");
    assert_eq!(
        outputs[0].term.cmp(expected),
        std::cmp::Ordering::Equal,
        "{name}: exact complete structural result including metadata"
    );
    report.work
}

#[test]
fn practical_regex_gslt_full_match_search_and_replacement_application_matrix() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("complete practical regex declaration installs");
    let token = &batch.exports[0].handle;
    for (pattern, text, matches) in [
        ("a(b|c)+", "abcb", true),
        ("a(b|c)+", "ax", false),
        ("a(b|c)+", "xab", false),
        (".", "\n", true),
        ("a{2,3}", "a", false),
        ("a{2,3}", "aaa", true),
        ("a{2,3}", "aaaa", false),
        ("a{3,2}", "aaa", false),
        ("()", "", true),
        ("a", "", false),
        ("()", "a", false),
        ("é", "e\u{301}", false),
        ("λ+", "λλ", true),
    ] {
        let prefix = format!("fullMatch({pattern},");
        let input = text_computation(&runtime, token, &[&prefix, ")"], &[text]);
        let expected = computation(
            &runtime,
            token,
            if matches {
                "doneBool(true)"
            } else {
                "doneBool(false)"
            },
        );
        let work = assert_regex_observation(&runtime, token, "FullMatch", &input, &expected);
        eprintln!("FullMatch({pattern:?},{text:?}) = {matches}; work={work}");
    }
    for (pattern, text, expected_span) in [
        ("a+", "xaaab", Some((1, 4, "aaa"))),
        ("a|aa", "aa", Some((0, 2, "aa"))),
        ("a+", "bc", None),
        ("λ+", "éλλx", Some((2, 6, "λλ"))),
        ("()", "ab", Some((0, 0, ""))),
        ("()", "", Some((0, 0, ""))),
    ] {
        let prefix = format!("search({pattern},");
        let input = text_computation(&runtime, token, &[&prefix, ")"], &[text]);
        let expected = match expected_span {
            Some((start, end, matched)) => {
                let prefix = format!("doneMatch(found({start},{end},");
                text_computation(&runtime, token, &[&prefix, "))"], &[matched])
            },
            None => computation(&runtime, token, "doneMatch(noMatch)"),
        };
        let work = assert_regex_observation(&runtime, token, "Search", &input, &expected);
        eprintln!("Search({pattern:?},{text:?}) = {expected_span:?}; work={work}");
    }
    for (name, operation, pattern, text, output) in [
        ("ReplaceFirst", "replaceFirst", "a+", "baac", "bxc"),
        ("ReplaceAll", "replaceAll", "a+", "aaba", "xbx"),
        ("ReplaceFirst", "replaceFirst", "a+", "bc", "bc"),
        ("ReplaceAll", "replaceAll", "()", "ab", "xaxbx"),
        ("ReplaceAll", "replaceAll", "()", "λ", "xλx"),
        ("ReplaceAll", "replaceAll", "a*", "a", "xx"),
        ("ReplaceAll", "replaceAll", "()", "", "x"),
    ] {
        let prefix = format!("{operation}({pattern},literal(");
        let input = text_computation(&runtime, token, &[&prefix, "),", ")"], &["x", text]);
        let expected = text_computation(&runtime, token, &["doneText(", ")"], &[output]);
        let work = assert_regex_observation(&runtime, token, name, &input, &expected);
        eprintln!("{name}({pattern:?},{text:?}) = {output:?}; work={work}");
    }
    let input = text_computation(
        &runtime,
        token,
        &["replaceFirst(a+,append(literal(", "),append(whole,literal(", "))),", ")"],
        &["[", "]", "baac"],
    );
    let expected = text_computation(&runtime, token, &["doneText(", ")"], &["b[aa]c"]);
    assert_regex_observation(&runtime, token, "ReplaceFirst", &input, &expected);
}

#[test]
fn practical_regex_gslt_full_match_result_is_controlled_by_the_declared_driver() {
    let original = "FullNullableDone : (FullNullable (NDone B)) ~> (DoneBool B);";
    let replacement = "FullNullableDone : (FullNullable (NDone B)) ~> (DoneBool (BFalse));";
    assert_eq!(SOURCE.matches(original).count(), 1);
    let changed = SOURCE.replace(original, replacement);
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let mut commitments = Vec::with_capacity(2);
    for (source, result) in [(SOURCE, "doneBool(true)"), (changed.as_str(), "doneBool(false)")] {
        let batch = runtime
            .install_all(rholang_ddl_candidate(source))
            .expect("independent inline application declaration");
        let token = &batch.exports[0].handle;
        commitments.push(
            runtime
                .resolve(token, LanguageRight::Observe)
                .expect("observation authority")
                .fingerprint(),
        );
        let input = text_computation(&runtime, token, &["fullMatch(a,", ")"], &["a"]);
        let expected = computation(&runtime, token, result);
        assert_regex_observation(&runtime, token, "FullMatch", &input, &expected);
    }
    assert_ne!(
        commitments[0], commitments[1],
        "changed declared semantics has a distinct full-language owner"
    );
}

#[test]
fn practical_regex_gslt_application_limits_refuse_without_partial_results() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("inline declaration");
    let token = &batch.exports[0].handle;
    for (name, fragments, texts, expected_fragments, expected_texts) in [
        (
            "FullMatch",
            vec!["fullMatch(a+,", ")"],
            vec!["aaa"],
            vec!["doneBool(true)"],
            vec![],
        ),
        (
            "Search",
            vec!["search(a|aa,", ")"],
            vec!["aa"],
            vec!["doneMatch(found(0,2,", "))"],
            vec!["aa"],
        ),
        (
            "ReplaceAll",
            vec!["replaceAll((),literal(", "),", ")"],
            vec!["x", "λ"],
            vec!["doneText(", ")"],
            vec!["xλx"],
        ),
    ] {
        let input = text_computation(&runtime, token, &fragments, &texts);
        let expected = text_computation(&runtime, token, &expected_fragments, &expected_texts);
        let work = assert_regex_observation(&runtime, token, name, &input, &expected);
        for (limit, succeeds) in [(0, false), (work - 1, false), (work, true)] {
            let mut limits = SemanticServiceLimits::default();
            limits.execution.work = limit;
            let report = runtime.execute_semantic(
                SemanticServiceRequest {
                    handle: token,
                    operation: SemanticOperation::Observe(name),
                    input: &input,
                    limits,
                },
                || false,
            );
            assert!(report.work <= limit, "{name}: shared work bound");
            if succeeds {
                let result = report.outcome.expect("exact measured work allowance");
                assert_eq!(result.len(), 1);
                assert_eq!(result[0].term.cmp(&expected), std::cmp::Ordering::Equal);
            } else {
                assert!(report.outcome.is_err(), "{name}: bounded refusal, no successful prefix");
            }
        }
        let cancelled = runtime.execute_semantic(
            SemanticServiceRequest {
                handle: token,
                operation: SemanticOperation::Observe(name),
                input: &input,
                limits: SemanticServiceLimits::default(),
            },
            || true,
        );
        assert!(cancelled.outcome.is_err(), "{name}: cancellation cannot commit a result");
    }
}

fn computation(runtime: &RholangLanguageRuntime, token: &Par, source: &str) -> Par {
    runtime
        .construct_template(
            token,
            &[RuntimeTemplatePiece::Text(source.into())],
            &[],
            Some("Computation"),
            &BTreeMap::new(),
        )
        .unwrap_or_else(|error| panic!("declared computation {source}: {error:?}"))
}

#[test]
fn practical_regex_gslt_executes_declared_rules_through_the_generated_rholang_entrypoint() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("practical regex declaration installs through the actual inline DDL path");
    assert_eq!(batch.exports.len(), 1);
    assert_eq!(batch.exports[0].name, "Regex");
    let token = &batch.exports[0].handle;
    for (source, action, expected) in [
        ("nullable((?!))", "nullable", "doneBool(false)"),
        ("nullable(())", "nullable", "doneBool(true)"),
        ("nullable(a)", "nullable", "doneBool(false)"),
        ("nullable(.)", "nullable", "doneBool(false)"),
        ("nullable((a))", "nullable", "doneBool(false)"),
        ("nullable(a|())", "nullable", "doneBool(true)"),
        ("nullable(a())", "nullable", "doneBool(false)"),
        ("nullable(a*)", "nullable", "doneBool(true)"),
        ("nullable(a+)", "nullable", "doneBool(false)"),
        ("nullable(a?)", "nullable", "doneBool(true)"),
        ("derivative(a,a+)", "derivative", "donePattern(a*)"),
        ("nullable(a{2,3})", "nullable", "doneBool(false)"),
        ("nullable(a{0,0})", "nullable", "doneBool(true)"),
        ("nullable(a{3,2})", "nullable", "doneBool(false)"),
        ("nullable(λ?)", "nullable", "doneBool(true)"),
        ("derivative(a,(?!))", "derivative", "donePattern((?!))"),
        ("derivative(a,())", "derivative", "donePattern((?!))"),
        ("derivative(a,a)", "derivative", "donePattern(())"),
        ("derivative(a,b)", "derivative", "donePattern((?!))"),
        ("derivative(λ,.)", "derivative", "donePattern(())"),
        ("derivative(λ,λ)", "derivative", "donePattern(())"),
        ("derivative(a,a|b)", "derivative", "donePattern(())"),
        ("derivative(a,ab)", "derivative", "donePattern(b)"),
        ("derivative(b,ab)", "derivative", "donePattern((?!))"),
        ("derivative(b,a?b)", "derivative", "donePattern(())"),
        ("derivative(a,a*)", "derivative", "donePattern(a*)"),
    ] {
        let input = runtime
            .construct_template(
                token,
                &[RuntimeTemplatePiece::Text(source.into())],
                &[],
                Some("Computation"),
                &BTreeMap::new(),
            )
            .unwrap_or_else(|error| panic!("declared request {source} must parse: {error:?}"));
        let expected = runtime
            .construct_template(
                token,
                &[RuntimeTemplatePiece::Text(expected.into())],
                &[],
                Some("Computation"),
                &BTreeMap::new(),
            )
            .expect("declared result syntax");
        let report = runtime.execute_semantic(
            SemanticServiceRequest {
                handle: token,
                operation: SemanticOperation::Reduce(action),
                input: &input,
                limits: SemanticServiceLimits::default(),
            },
            || false,
        );
        let outputs = report.outcome.unwrap_or_else(|error| {
            panic!(
                "{source}: {error:?}; total work={}, kernel work={:?}",
                report.work, report.kernel_work
            )
        });
        assert_eq!(outputs.len(), 1, "{source}: deterministic declared result");
        assert_eq!(outputs[0].term, expected, "{source}: complete structural result");
        eprintln!("{source}: exact result verified; work={}", report.work);
    }
}

#[test]
fn practical_regex_gslt_declared_rule_controls_observation() {
    let original = "NullableAny : (NEval (PAny) K) ~> (NReturn (BFalse) K);";
    let replacement = "NullableAny : (NEval (PAny) K) ~> (NReturn (BTrue) K);";
    assert_eq!(SOURCE.matches(original).count(), 1);
    // Separate application specifications, each parsed once through the host
    // entrypoint. This test mutation is not runtime source rewriting.
    let changed = SOURCE.replace(original, replacement);
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let mut commitments = Vec::with_capacity(2);
    for (source, expected) in [(SOURCE, "doneBool(false)"), (changed.as_str(), "doneBool(true)")] {
        let batch = runtime
            .install_all(rholang_ddl_candidate(source))
            .expect("inline declaration");
        let token = &batch.exports[0].handle;
        commitments.push(
            runtime
                .resolve(token, LanguageRight::Observe)
                .expect("observation authority")
                .fingerprint(),
        );
        let input = computation(&runtime, token, "nullable(.)");
        let expected = computation(&runtime, token, expected);
        let report = runtime.execute_semantic(
            SemanticServiceRequest {
                handle: token,
                operation: SemanticOperation::Observe("Nullable"),
                input: &input,
                limits: SemanticServiceLimits::default(),
            },
            || false,
        );
        let outputs = report.outcome.expect("declared observation completes");
        assert_eq!(outputs.len(), 1);
        assert_eq!(
            outputs[0].term.cmp(&expected),
            std::cmp::Ordering::Equal,
            "the declaration determines the complete answer, including metadata"
        );
    }
    assert_ne!(commitments[0], commitments[1], "semantic changes have distinct owners");
}

#[test]
fn practical_regex_gslt_scalar_holes_admit_singletons_and_refuse_other_text() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("inline declaration");
    let token = &batch.exports[0].handle;
    let handle = runtime
        .resolve(token, LanguageRight::Construct)
        .expect("construct authority");
    let installed = runtime
        .service
        .table()
        .authorize(&handle, LanguageRight::Construct)
        .expect("installed language");
    let owner = grammar_fingerprint_label(handle.fingerprint());
    for text in ["a", "λ", "€", "🙂", "", "ab", "λ🙂"] {
        let ground = dynamic_syntax_to_ground_term(
            &mettail_grammar_core::DynamicValue::Text(text.into()),
            installed.core(),
            &BTreeMap::new(),
        )
        .expect("native text reflection");
        let fill = mettail_rholang_codegen::reflect_ground_term_par(&ground, &owner);
        for (prefix, suffix, action) in
            [("nullable(", ")", "nullable"), ("derivative(", ",a)", "derivative")]
        {
            let input = runtime
                .construct_template(
                    token,
                    &[
                        RuntimeTemplatePiece::Text(prefix.into()),
                        RuntimeTemplatePiece::Hole(0),
                        RuntimeTemplatePiece::Text(suffix.into()),
                    ],
                    &[NamedRuntimeTemplateHole {
                        id: 0,
                        name: "scalar".into(),
                        category: Some("Scalar".into()),
                    }],
                    Some("Computation"),
                    &BTreeMap::from([("scalar".into(), fill.clone())]),
                )
                .expect("typed native text hole constructs without textual interpolation");
            let request = |limits| SemanticServiceRequest {
                handle: token,
                operation: SemanticOperation::Reduce(action),
                input: &input,
                limits,
            };
            let report =
                runtime.execute_semantic(request(SemanticServiceLimits::default()), || false);
            if text.chars().count() == 1 {
                let expected = match (action, text) {
                    ("nullable", _) => "doneBool(false)",
                    (_, "a") => "donePattern(())",
                    _ => "donePattern((?!))",
                };
                let outputs = report.outcome.expect("singleton scalar admission");
                assert_eq!(outputs.len(), 1);
                assert_eq!(outputs[0].term, computation(&runtime, token, expected));
                let mut zero = SemanticServiceLimits::default();
                zero.execution.work = 0;
                let refused = runtime.execute_semantic(request(zero), || false);
                assert!(matches!(
                    refused.outcome,
                    Err(InstalledSemanticError::Resource(
                        mettail_rholang_codegen::DynamicReflectionError::WorkLimit
                    ))
                ));
                assert_eq!(refused.work, 0);
            } else {
                assert!(
                    matches!(
                        report.outcome,
                        Err(InstalledSemanticError::Refuted(
                            mettail_dovetail_runtime::SemanticMatchRefutation::StuckNonterminal
                        ))
                    ),
                    "{action}({text:?}): {:?}",
                    report.outcome
                );
            }
            eprintln!("{action} scalar hole {text:?}: admission/refusal verified");
        }
    }
}

#[test]
fn practical_regex_gslt_structural_repeat_bounds_preserve_nat_hole_policy() {
    use mettail_grammar_core::{DynamicTerm, DynamicValue, SourceSpan};
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("inline declaration");
    let token = &batch.exports[0].handle;
    let handle = runtime
        .resolve(token, LanguageRight::Construct)
        .expect("construct authority");
    let installed = runtime
        .service
        .table()
        .authorize(&handle, LanguageRight::Construct)
        .expect("installed language");
    let core = installed.core();
    assert!(
        !core
            .categories
            .iter()
            .find(|category| category.name == "Nat")
            .expect("Nat category")
            .admits_variables
    );
    let term = |label: &str, fields| {
        let production = core
            .productions
            .iter()
            .find(|production| production.label == label)
            .expect("declared constructor");
        DynamicValue::Term(Box::new(DynamicTerm {
            category: production.result,
            constructor: production.constructor,
            fields,
            span: SourceSpan::default(),
        }))
    };
    let owner = grammar_fingerprint_label(handle.fingerprint());
    for (lower, upper, expected) in
        [(0, 2, Some(true)), (2, 2, Some(false)), (-1, 2, None), (0, -1, None)]
    {
        let pattern = term(
            "PRepeat",
            vec![
                term("PLiteral", vec![DynamicValue::Text("a".into())]),
                DynamicValue::Integer(lower),
                DynamicValue::Integer(upper),
            ],
        );
        let ground = dynamic_syntax_to_ground_term(&pattern, core, &BTreeMap::new())
            .expect("structural pattern reflection");
        let fill = mettail_rholang_codegen::reflect_ground_term_par(&ground, &owner);
        let input = runtime
            .construct_template(
                token,
                &[
                    RuntimeTemplatePiece::Text("nullable(".into()),
                    RuntimeTemplatePiece::Hole(0),
                    RuntimeTemplatePiece::Text(")".into()),
                ],
                &[NamedRuntimeTemplateHole {
                    id: 0,
                    name: "pattern".into(),
                    category: Some("Pattern".into()),
                }],
                Some("Computation"),
                &BTreeMap::from([("pattern".into(), fill)]),
            )
            .expect("whole Pattern hole is authorized; Nat holes remain forbidden");
        let report = runtime.execute_semantic(
            SemanticServiceRequest {
                handle: token,
                operation: SemanticOperation::Reduce("nullable"),
                input: &input,
                limits: SemanticServiceLimits::default(),
            },
            || false,
        );
        match expected {
            Some(value) => {
                let outputs = report.outcome.expect("nonnegative bounds complete");
                assert_eq!(outputs.len(), 1);
                assert_eq!(
                    outputs[0].term.cmp(&computation(
                        &runtime,
                        token,
                        if value {
                            "doneBool(true)"
                        } else {
                            "doneBool(false)"
                        }
                    )),
                    std::cmp::Ordering::Equal
                );
            },
            None => assert!(
                matches!(
                    report.outcome,
                    Err(InstalledSemanticError::Refuted(
                        mettail_dovetail_runtime::SemanticMatchRefutation::StuckNonterminal
                    ))
                ),
                "negative bounds must not fabricate a Boolean: {:?}",
                report.outcome
            ),
        }
        eprintln!("repeat bounds ({lower},{upper}): result/refusal verified");
    }
}
