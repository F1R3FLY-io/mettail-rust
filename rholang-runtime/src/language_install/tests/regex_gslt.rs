use super::*;

const SOURCE: &str = include_str!("../../../tests/fixtures/regex_gslt.rho");

#[test]
fn practical_regex_default_mode_tokens_have_original_wpda_observations() {
    let service = LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    );
    let batch = service
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("declared Regex theory installs");
    assert_eq!(
        batch.exports[0].receipt.requested_rights,
        LanguageRights::native_flt_default(),
        "omitting the redundant rights row keeps the exact requested-right set"
    );
    let installed = service
        .table()
        .authorize(&batch.exports[0].receipt.handle, LanguageRight::Parse)
        .expect("installed grammar");
    let core = installed.core();
    let observations = core
        .wpda_token_observations
        .as_ref()
        .expect("original token observations");
    for token in &core.tokens {
        if token.mode == mettail_grammar_core::ModeId(0) && token.channel == "main" {
            assert!(
                observations
                    .get(token.id.0 as usize)
                    .and_then(Option::as_ref)
                    .is_some(),
                "default-mode token {:?} {} {:?} lacks its original WPDA observation",
                token.id,
                token.name,
                token.pattern
            );
        }
    }
}

#[test]
fn practical_regex_full_match_input_has_canonical_closed_heads() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("complete practical regex declaration installs");
    let token = &batch.exports[0].handle;
    let handle = runtime
        .resolve(token, LanguageRight::Construct)
        .expect("construct right");
    let installed = runtime
        .service
        .table()
        .authorize(&handle, LanguageRight::Construct)
        .expect("installed grammar");
    let category = resolve_required_category(installed.core(), "Computation").expect("sort");
    let text_category = resolve_required_category(installed.core(), "Text").expect("hole sort");
    let pieces = [
        RuntimeTemplatePiece::Text("fullMatch(a(b|c)+,".into()),
        RuntimeTemplatePiece::Hole(0),
        RuntimeTemplatePiece::Text(")".into()),
    ];
    let parses = runtime
        .service
        .parse_template(
            &handle,
            &pieces,
            &[RuntimeTemplateHole { id: 0, category: Some(text_category) }],
            Some(category),
            LanguageRight::Construct,
            runtime.host.as_ref(),
        )
        .expect("complete template parse family");
    let distinct_syntax = parses
        .iter()
        .map(|parse| &parse.syntax)
        .collect::<std::collections::HashSet<_>>()
        .len();
    let distinct_values = parses
        .iter()
        .map(|parse| &parse.value)
        .collect::<std::collections::HashSet<_>>()
        .len();
    assert_eq!(distinct_syntax, 1, "grouping must have one structural meaning");
    assert_eq!(distinct_values, 1, "grouping must have one semantic value");
    let bool_category = resolve_required_category(installed.core(), "Bool").expect("sort");
    let bool_family = runtime
        .service
        .parse(&handle, "yes", Some(bool_category), runtime.host.as_ref())
        .expect("declared Boolean constructor parses");
    assert!(bool_family.iter().all(|parse| matches!(
        &parse.syntax,
        DynamicValue::Term(term) if installed.core().productions.iter().any(|production| {
            production.constructor == term.constructor && production.label == "BTrue"
        })
    )));
    let input = text_computation(&runtime, token, &["fullMatch(a(b|c)+,", ")"], &["abcb"]);
    let owner = grammar_fingerprint_label(handle.fingerprint());
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = mettail_rholang_codegen::ReflectedCodecBudget::new(
        &mut work,
        1_000_000,
        1_000_000,
        &mut cancel,
    );
    let context = mettail_rholang_codegen::ReflectedPositionalContext::new(&owner, &mut budget)
        .expect("canonical owner");
    let mut nodes = vec![(&input, 0usize)];
    while let Some((node, depth)) = nodes.pop() {
        let head = context
            .view(node, &mut budget)
            .expect("bounded view")
            .unwrap_or_else(|| {
                panic!(
                "noncanonical reflected node at depth {depth}; complete parses={}, expressions={}",
                parses.len(),
                node.exprs.len()
            )
            });
        nodes.extend(head.children().iter().map(|child| (child, depth + 1)));
    }
}

#[test]
fn practical_regex_search_alt_concat_template_parses() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("complete practical regex declaration installs");
    let token = &batch.exports[0].handle;
    let handle = runtime
        .resolve(token, LanguageRight::Construct)
        .expect("construct right");
    let installed = runtime
        .service
        .table()
        .authorize(&handle, LanguageRight::Construct)
        .expect("installed grammar");
    let pattern = resolve_required_category(installed.core(), "Pattern").expect("sort");
    let computation = resolve_required_category(installed.core(), "Computation").expect("sort");
    let text = resolve_required_category(installed.core(), "Text").expect("sort");
    let parser = mettail_grammar_core::RuntimeParser::new(
        installed.core(),
        installed.parser_image().expect("runtime parser image"),
        &installed.commitment().compiler_abi,
        &installed.commitment().unicode_abi,
        runtime.host.as_ref(),
    )
    .expect("admitted parser");
    let label = |constructor| {
        installed
            .core()
            .productions
            .iter()
            .find(|production| production.constructor == constructor)
            .map(|production| production.label.as_str())
    };
    for (source, concat_side, concat_span) in [
        ("a|aa", 1, mettail_grammar_core::SourceSpan { start: 2, end: 4 }),
        ("a|ab", 1, mettail_grammar_core::SourceSpan { start: 2, end: 4 }),
        ("aa|a", 0, mettail_grammar_core::SourceSpan { start: 0, end: 2 }),
    ] {
        let forest = parser
            .parse_category(source, pattern)
            .expect("original forest reference must recognize the same complete input");
        let family = runtime.service.parse(&handle, source, Some(pattern), runtime.host.as_ref())
            .unwrap_or_else(|error| panic!("{source}: shared WPDA failed while original forest returned {} complete readings: {error:?}", forest.len()));
        assert_eq!(family.len(), 1, "one complete shared reading for {source}");
        assert_eq!(forest.len(), 1, "one complete reference reading for {source}");
        assert_eq!(family[0].syntax, forest[0].syntax, "exact constructor family for {source}");
        assert_eq!(family[0].value, forest[0].value, "exact semantic result for {source}");
        let DynamicValue::Term(root) = &family[0].syntax else {
            panic!("alternation must retain its constructor root for {source}")
        };
        assert_eq!(label(root.constructor), Some("PAlt"), "{source}");
        assert_eq!(root.span, mettail_grammar_core::SourceSpan { start: 0, end: 4 });
        assert_eq!(root.fields.len(), 2, "alternation arity for {source}");
        let DynamicValue::Term(concat) = &root.fields[concat_side] else {
            panic!("alternation must retain its concatenation operand for {source}")
        };
        assert_eq!(label(concat.constructor), Some("PConcat"), "{source}");
        assert_eq!(concat.span, concat_span, "{source}");
        assert_eq!(concat.fields.len(), 2, "concatenation arity for {source}");
    }
    let holes = [RuntimeTemplateHole { id: 0, category: Some(text) }];
    for (name, before, after) in [
        ("search input", "search(a|aa,", ")"),
        ("search output", "doneMatch(found(0,2,", "))"),
    ] {
        let pieces = [
            RuntimeTemplatePiece::Text(before.into()),
            RuntimeTemplatePiece::Hole(0),
            RuntimeTemplatePiece::Text(after.into()),
        ];
        let family = runtime.service.parse_template(
            &handle,
            &pieces,
            &holes,
            Some(computation),
            LanguageRight::Construct,
            runtime.host.as_ref(),
        );
        assert!(family.is_ok(), "{name}: {family:?}");
    }
}

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

#[test]
fn authored_regex_limits_preserve_the_data_faithful_canonical_module() {
    const AUTHORED_TRAILER: &str = r#"        ]
      }
    })
    Options {
      Semantics {
        Limits {
          max_term_nodes = 16384;
          max_proof_nodes = 16384;
          max_frontier = 256;
          max_grade_bits = 128;
        }
      }
    }"#;
    const DATA_TRAILER: &str = r#"        ],
        "limits":{"max_term_nodes":16384,"max_proof_nodes":16384,"max_frontier":256,"max_steps":10000000,"max_grade_bits":128}
      }
    })"#;
    assert_eq!(SOURCE.matches(AUTHORED_TRAILER).count(), 1);
    let data_faithful = SOURCE.replacen(AUTHORED_TRAILER, DATA_TRAILER, 1);
    let service = LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    );
    let (_, host_profile) = service
        .builtin_host_profile_binding()
        .expect("compiled Rholang host profile is available");
    let host_signature = host_profile
        .raw_signature()
        .expect("compiled Rholang host signature is checked");

    let canonical = |source: &str| {
        let InstallCandidate::Ddl(ParsedDdl::Module(module)) = rholang_ddl_candidate(source) else {
            panic!("Regex fixture must lower to a module declaration")
        };
        mettail_elab::elaborate_module_ast_with_host(
            module,
            &mettail_elab::resolve::MemResolver::new(),
            &host_signature,
        )
        .expect("Regex module elaborates")
        .canonical_value
    };
    assert_eq!(canonical(SOURCE), canonical(&data_faithful));
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
    let fills = BTreeMap::from([("text".into(), new_gstring_par(text.into(), Vec::new(), false))]);
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
    if outputs[0].term.cmp(expected) != std::cmp::Ordering::Equal {
        eprintln!("{name}: actual={:?}", outputs[0].term);
        eprintln!("{name}: expected={expected:?}");
    }
    assert_eq!(
        outputs[0].term.cmp(expected),
        std::cmp::Ordering::Equal,
        "{name}: exact complete structural result including metadata"
    );
    report.work
}

#[test]
fn authored_regex_terminal_judgments_observe_all_result_categories_without_actions() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("complete Regex theory installs");
    let handle = &batch.exports[0].handle;
    let observe = |label: &str, terminal_judgment: &str, input: &Par, expected: &Par| {
        let report = runtime.execute_relation_observation(
            RelationObservationRequest {
                handle,
                relation_category: "Computation",
                terminal_judgment,
                terminal_projection: "TerminalVerdict",
                input,
                limits: SemanticServiceLimits::default(),
            },
            || false,
        );
        let results = report.outcome.unwrap_or_else(|error| {
            panic!("{label}: {error:?}; work={}; kernel={:?}", report.work, report.kernel_work)
        });
        assert_eq!(results.len(), 1, "{label}: one admitted complete normal form");
        assert_eq!(results[0].term.cmp(expected), std::cmp::Ordering::Equal, "{label}");
        assert!(!results[0].terminal_receipts.is_empty());
        assert!(!results[0].projection_receipts.is_empty());
    };
    for (text, expected_text) in [("abcb", "doneBool(yes)"), ("ax", "doneBool(no)")] {
        let input = text_computation(&runtime, handle, &["fullMatch(a(b|c)+,", ")"], &[text]);
        let expected = computation(&runtime, handle, expected_text);
        observe("full match", "CheckBooleanTerminal", &input, &expected);
    }
    observe(
        "nullable",
        "CheckBooleanTerminal",
        &computation(&runtime, handle, "nullable(())"),
        &computation(&runtime, handle, "doneBool(yes)"),
    );
    observe(
        "derivative",
        "CheckPatternTerminal",
        &computation(&runtime, handle, "derivative(a,a+)"),
        &computation(&runtime, handle, "donePattern(a*)"),
    );
    observe(
        "search",
        "CheckMatchTerminal",
        &text_computation(&runtime, handle, &["search(a+,", ")"], &["xaaab"]),
        &text_computation(&runtime, handle, &["doneMatch(found(1,4,", "))"], &["aaa"]),
    );
    for (operation, expected_text) in [("replaceFirst", "bxc"), ("replaceAll", "xbx")] {
        let input = text_computation(
            &runtime,
            handle,
            &[&format!("{operation}(a+,literal("), "),", ")"],
            &[
                "x",
                if operation == "replaceFirst" {
                    "baac"
                } else {
                    "aaba"
                },
            ],
        );
        let expected = text_computation(&runtime, handle, &["doneText(", ")"], &[expected_text]);
        observe(operation, "CheckTextTerminal", &input, &expected);
    }
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
                "doneBool(yes)"
            } else {
                "doneBool(no)"
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
    for (source, result) in [(SOURCE, "doneBool(yes)"), (changed.as_str(), "doneBool(no)")] {
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
            vec!["doneBool(yes)"],
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
        ("nullable((?!))", "nullable", "doneBool(no)"),
        ("nullable(())", "nullable", "doneBool(yes)"),
        ("nullable(a)", "nullable", "doneBool(no)"),
        ("nullable(.)", "nullable", "doneBool(no)"),
        ("nullable((a))", "nullable", "doneBool(no)"),
        ("nullable(a|())", "nullable", "doneBool(yes)"),
        ("nullable(a())", "nullable", "doneBool(no)"),
        ("nullable(a*)", "nullable", "doneBool(yes)"),
        ("nullable(a+)", "nullable", "doneBool(no)"),
        ("nullable(a?)", "nullable", "doneBool(yes)"),
        ("derivative(a,a+)", "derivative", "donePattern(a*)"),
        ("nullable(a{2,3})", "nullable", "doneBool(no)"),
        ("nullable(a{0,0})", "nullable", "doneBool(yes)"),
        ("nullable(a{3,2})", "nullable", "doneBool(no)"),
        ("nullable(λ?)", "nullable", "doneBool(yes)"),
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
    for (source, expected) in [(SOURCE, "doneBool(no)"), (changed.as_str(), "doneBool(yes)")] {
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
                .unwrap_or_else(|error| {
                    let parser = mettail_grammar_core::RuntimeParser::new(
                        installed.core(),
                        installed.parser_image().expect("runtime parser image"),
                        &installed.commitment().compiler_abi,
                        &installed.commitment().unicode_abi,
                        runtime.host.as_ref(),
                    )
                    .expect("admitted reference parser");
                    let reference = parser.parse_template(
                        &[
                            RuntimeTemplatePiece::Text(prefix.into()),
                            RuntimeTemplatePiece::Hole(0),
                            RuntimeTemplatePiece::Text(suffix.into()),
                        ],
                        &[RuntimeTemplateHole { id: 0, category: Some(resolve_required_category(installed.core(), "Scalar").expect("Scalar category")) }],
                        Some(resolve_required_category(installed.core(), "Computation").expect("Computation category")),
                    ).map(|family| family.len());
                    panic!("{action}({text:?}) shared template parse failed: {error:?}; original forest: {reference:?}");
                });
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
                    ("nullable", _) => "doneBool(no)",
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
fn practical_regex_gslt_structural_repeat_bounds_preserve_native_nat_variable_policy() {
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
            .expect("whole Pattern hole is authorized independently of guest variables");
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
                            "doneBool(yes)"
                        } else {
                            "doneBool(no)"
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
