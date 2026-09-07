use mettail_languages::rholang::{
    lex, lex_dag, DdlEquation, DdlImport, DdlImports, DdlModuleItem, DdlParam, DdlPath, DdlRewrite,
    DdlRuleAst, DdlTermRule, DdlTheoryExpr, Proc,
};
use mettail_prattail::automata::TokenKind;

fn run_ddl_sexp_action(
    items: Vec<mettail_prattail::wpda_runtime::ActionArg>,
) -> Result<Option<DdlRuleAst>, mettail_prattail::wpda_runtime::ActionInvocationError> {
    use mettail_languages::rholang::{RholangWpdaEngine, WPDA_CATEGORIES, WPDA_RULES};
    use mettail_prattail::wpda_runtime::{ActionArg, SelectedCollection, SemanticBuilder};
    use mettail_prattail::wpda_walker::WpdaEngine;

    let category = WPDA_CATEGORIES
        .iter()
        .position(|name| *name == "DdlRuleAst")
        .expect("DDL AST category is emitted");
    let rule = WPDA_RULES[category]
        .iter()
        .find_map(|(name, index)| (*name == "DdlRuleAstSExp").then_some(*index))
        .expect("DDL S-expression rule is emitted");
    let engine = RholangWpdaEngine;
    let action = engine
        .action_for(u16::try_from(category).expect("category fits the engine ABI"), rule)
        .expect("DDL S-expression construction action exists");
    let result = SemanticBuilder::invoke_selected_action(
        *action,
        vec![
            ActionArg::Token {
                kind: TokenKind::Ident,
                text: "PNode".into(),
                pos: 0,
            },
            ActionArg::SelectedCollection(
                SelectedCollection::new(items).expect("test inputs are terms"),
            ),
        ],
    )?;
    Ok(result.map(|term| {
        term.try_into_term::<DdlRuleAst>()
            .expect("generated action returns its declared category")
    }))
}

#[test]
fn generated_ddl_collection_action_rejects_mismatched_items_without_shortening() {
    use mettail_prattail::wpda_runtime::ActionArg;
    use std::sync::Arc;

    let child = DdlRuleAst::DdlRuleAstSExp("PFail".into(), Vec::new());
    let argument = || ActionArg::Term {
        value: Arc::new(child.clone()),
        type_name: std::any::type_name::<DdlRuleAst>(),
    };
    assert_eq!(
        run_ddl_sexp_action(vec![argument(), argument()]),
        Ok(Some(DdlRuleAst::DdlRuleAstSExp(
            "PNode".into(),
            vec![child.clone(), child.clone()]
        ))),
    );
    assert_eq!(
        run_ddl_sexp_action(Vec::new()),
        Ok(Some(DdlRuleAst::DdlRuleAstSExp("PNode".into(), Vec::new()))),
    );
    for position in 0..=2 {
        let mut items = vec![argument(), argument()];
        items.insert(
            position,
            ActionArg::Term {
                value: Arc::new(Proc::PZero),
                type_name: std::any::type_name::<Proc>(),
            },
        );
        assert_eq!(
            run_ddl_sexp_action(items),
            Ok(None),
            "wrong-category item at {position} must reject the entire constructor",
        );
    }
}

fn parse(source: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse(source).unwrap_or_else(|error| panic!("`{source}` must parse: {error:?}"))
}

fn assert_roundtrip(source: &str) -> Proc {
    let term = parse(source);
    let rendered = term.to_string();
    let reparsed = parse(&rendered);
    assert_eq!(reparsed, term, "round-trip failed for `{rendered}`");
    term
}

fn assert_theory_ref(expression: &DdlTheoryExpr, expected: &str) {
    let DdlTheoryExpr::DdlTheoryRef(path) = expression else {
        panic!("expected theory reference `{expected}`, got {expression:?}");
    };
    assert!(
        matches!(path.as_ref(), DdlPath::DdlPathName(name) if name == expected),
        "expected theory reference `{expected}`, got {path:?}",
    );
}

#[test]
fn theory_is_a_structural_proc_form() {
    let term = assert_roundtrip("Theory RhoCalc() { Empty }");
    match &term {
        Proc::DdlTheory(name, parameters, body) => {
            assert_eq!(name, "RhoCalc");
            assert!(parameters.is_empty());
            assert!(matches!(body.as_ref(), DdlTheoryExpr::DdlTheoryEmpty));
        },
        other => panic!("expected a structural DdlTheory, got {other:?}"),
    }
}

#[test]
fn exact_core_data_is_parsed_as_structural_ddl_by_the_application_entrypoint() {
    let core = mettail_grammar_core::LanguageCoreV1::structural(
        mettail_grammar_core::GrammarCoreV1::new("Exact"),
    );
    let fragment = mettail_elab::core_value::language_core_to_data_fragment(&core)
        .expect("minimal LanguageCore has an exact Data fragment");
    let literal = mettail_elab::rholang_literal::render_rholang_value_literal(&fragment)
        .expect("exact fragment has a canonical Rholang spelling");
    let source = format!("Theory Exact() {{ Data({literal}) }}");
    let term = Proc::parse_via_wpda(&source)
        .expect("the generated application-entry WPDA parses exact Data directly");

    let Proc::DdlTheory(name, parameters, body) = &term else {
        panic!("exact Data must remain a structural DDL theory")
    };
    assert_eq!(name, "Exact");
    assert!(parameters.is_empty());
    assert!(matches!(body.as_ref(), DdlTheoryExpr::DdlTheoryDataImplicit(_)));
}

#[test]
fn judgement_term_and_builder_chain_parse_structurally() {
    let term_rule = DdlTermRule::parse(r#"PZero . |- "0" : Proc;"#)
        .expect("a judgement-style term rule must parse independently");
    assert_eq!(DdlTermRule::parse(&term_rule.to_string()).unwrap(), term_rule);

    let contextual_label =
        DdlTermRule::parse(r#"PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;"#)
            .expect("a DDL label may share a spelling with a contextual Rholang keyword");
    assert_eq!(DdlTermRule::parse(&contextual_label.to_string()).unwrap(), contextual_label,);

    let theory = DdlTheoryExpr::parse(r#"Types { Proc; Name; } Terms { PZero . |- "0" : Proc; }"#)
        .expect("adjacent theory builder blocks must compose into one expression");
    assert_eq!(DdlTheoryExpr::parse(&theory.to_string()).unwrap(), theory);

    for source in ["P", "(NQuote P)", "(PDrop (NQuote P))"] {
        let ast = DdlRuleAst::parse(source)
            .unwrap_or_else(|error| panic!("rule AST `{source}` must parse: {error:?}"));
        assert_eq!(DdlRuleAst::parse(&ast.to_string()).unwrap(), ast);
    }

    for source in ["P == P;", "(NQuote P) == P;", "(PDrop (NQuote P)) == P;"] {
        let equation = DdlEquation::parse(source)
            .unwrap_or_else(|error| panic!("direct equation `{source}` must parse: {error:?}"));
        assert_eq!(DdlEquation::parse(&equation.to_string()).unwrap(), equation);
    }

    let rewrite = DdlRewrite::parse("RDrop : (PDrop (NQuote P)) ~> P;")
        .expect("a named direct rewrite must parse independently");
    assert_eq!(DdlRewrite::parse(&rewrite.to_string()).unwrap(), rewrite);

    let complete_builder = DdlTheoryExpr::parse(
        r#"
            Types { Proc; Name; }
            Terms {
                PZero . |- "0" : Proc;
                PDrop . n:Name |- "*" "(" n ")" : Proc;
                PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
            }
            Equations { (PDrop (NQuote P)) == P; }
            Rewrites { RDrop : (PDrop (NQuote P)) ~> P; }
        "#,
    )
    .expect("all judgement-style theory builder blocks must compose structurally");
    assert_eq!(DdlTheoryExpr::parse(&complete_builder.to_string()).unwrap(), complete_builder,);
}

#[test]
fn wpda_preserves_nullary_rule_constructors_in_recursive_positions() {
    use mettail_languages::rholang::{
        parse_DdlRuleAst_via_wpda_all_with_source, parse_DdlRuleAst_via_wpda_with_source,
    };
    use mettail_prattail::wpda_runtime::{LatticeTokenSource, WpdaTokenSource};

    let variable = DdlRuleAst::DdlRuleAstVar("PFail".to_string());
    let nullary = DdlRuleAst::DdlRuleAstSExp("PFail".to_string(), Vec::new());
    let variable_child = DdlRuleAst::DdlRuleAstSExp("PStar".to_string(), vec![variable.clone()]);
    let constructor_child = DdlRuleAst::DdlRuleAstSExp("PStar".to_string(), vec![nullary.clone()]);
    for (input, expected, alternatives) in [
        ("PFail", variable.clone(), vec![variable.clone()]),
        ("(PFail)", nullary.clone(), vec![nullary, variable]),
        ("(PStar PFail)", variable_child.clone(), vec![variable_child.clone()]),
        (
            "(PStar (PFail))",
            constructor_child.clone(),
            vec![variable_child, constructor_child],
        ),
    ] {
        let source = LatticeTokenSource::new(lex_dag(input).expect("DDL input lexes"));
        let mut position = 0;
        let (direct, _) = parse_DdlRuleAst_via_wpda_with_source(&source, &mut position, 0)
            .expect("direct generated WPDA parse");
        assert_eq!(direct, expected, "direct constructor shape for {input}");
        assert_eq!(position, source.eof_node());
        // Do not use parse()/Display round trips: their surface-selection
        // wrapper would hide a defect in the actual generated WPDA route.
        assert_eq!(DdlRuleAst::parse_via_wpda(input).expect("public WPDA parse"), expected);

        position = 0;
        let (all, _) = parse_DdlRuleAst_via_wpda_all_with_source(&source, &mut position, 0)
            .expect("bounded enumeration");
        assert_eq!(position, source.eof_node());
        for alternative in alternatives {
            assert!(
                all.contains(&alternative),
                "lost admissible reading {alternative:?} of {input}"
            );
        }
    }
}

#[test]
fn saturated_ddl_root_elects_constructor_without_pruning_grouping() {
    use mettail_languages::rholang::{RholangWpdaEngine, WPDA_CATEGORIES};
    use mettail_prattail::automata::lex_weight::LexicographicWeight;
    use mettail_prattail::wpda_runtime::{
        CursorBoundingMode, LatticeTokenSource, WpdaResolveResult,
    };
    use mettail_prattail::wpda_walker::{RealizeRequestMode, WpdaWalker};

    let source = LatticeTokenSource::new(lex_dag("(PStar (PFail))").expect("DDL input lexes"));
    let category = WPDA_CATEGORIES
        .iter()
        .position(|name| *name == "DdlRuleAst")
        .expect("DDL category");
    let mut walker = WpdaWalker::<LexicographicWeight, _>::new_for_category(
        RholangWpdaEngine,
        u16::try_from(category).expect("category fits"),
        0,
    );
    let mut recovery = mettail_prattail::recovery::RecoveryConfig::default();
    recovery.max_recovery_depth = 0;
    walker.set_recovery_config(recovery);
    walker.set_bounding_mode(CursorBoundingMode::Unbounded);
    walker
        .run_to_end_of_input(1_000_000, &source)
        .expect("small forest saturates");
    let WpdaResolveResult::Accepted { roots, .. } = walker.resolve_at_end_of_input(&source) else {
        panic!("saturated input must accept");
    };
    assert_eq!(roots.len(), 1, "this witness compares alternatives within the same root");
    let root = roots[0];
    let nullary = DdlRuleAst::DdlRuleAstSExp("PFail".to_string(), Vec::new());
    let expected = DdlRuleAst::DdlRuleAstSExp("PStar".to_string(), vec![nullary]);
    let grouped = DdlRuleAst::DdlRuleAstSExp(
        "PStar".to_string(),
        vec![DdlRuleAst::DdlRuleAstVar("PFail".to_string())],
    );
    let elected = walker
        .realize_root_to_terms_with_weights(root, Some(1), RealizeRequestMode::SingleResultElection)
        .expect("election");
    assert_eq!(elected.len(), 1);
    assert_eq!(elected[0].0.downcast_ref::<DdlRuleAst>(), Some(&expected));
    let alternatives = walker
        .realize_root_to_terms_with_weights(root, Some(8), RealizeRequestMode::BoundedEnumeration)
        .expect("enumeration");
    for reading in [&expected, &grouped] {
        assert!(
            alternatives
                .iter()
                .any(|(value, _)| value.downcast_ref::<DdlRuleAst>() == Some(reading)),
            "election must not delete the distinct reading {reading:?}"
        );
    }
}

#[test]
fn wpda_preserves_rule_constructors_in_complete_module() {
    let source = r#"Module M {
        Theory T() {
            Types { Pattern; }
            Terms {
                PFail . |- "f" : Pattern;
                PEpsilon . |- "e" : Pattern;
                PStar . p:Pattern |- p "*" : Pattern;
            }
            Equations { (PStar (PFail)) == (PEpsilon); }
        }
        theory T()
    }"#;
    let process = Proc::parse_via_wpda(source).expect("complete inline module parses");
    let Proc::DdlModule(name, items) = &process else {
        panic!("expected structural module, got {process:?}");
    };
    assert_eq!(name, "M");
    assert_eq!(items.len(), 2);
    let DdlModuleItem::DdlModuleProcItem(declaration) = &items[0] else {
        panic!("first item must remain the theory declaration");
    };
    let Proc::DdlTheory(name, parameters, body) = declaration.as_ref() else {
        panic!("expected a structural theory");
    };
    assert_eq!(name, "T");
    assert!(parameters.is_empty());
    let DdlTheoryExpr::DdlTheoryEquations(_, equations) = body.as_ref() else {
        panic!("equations must remain the outer builder, got {body:?}");
    };
    let expected = DdlEquation::DdlEquationDirect(
        std::sync::Arc::new(DdlRuleAst::DdlRuleAstSExp(
            "PStar".to_string(),
            vec![DdlRuleAst::DdlRuleAstSExp("PFail".to_string(), vec![])],
        )),
        std::sync::Arc::new(DdlRuleAst::DdlRuleAstSExp("PEpsilon".to_string(), vec![])),
    );
    assert_eq!(
        equations.as_slice(),
        &[expected],
        "module/theory/equation embedding must not erase nullary constructors"
    );
}

#[test]
fn wpda_preserves_nullary_constructor_on_equation_right_side() {
    assert_eq!(
        DdlRuleAst::parse_via_wpda("(PFail)").expect("standalone nullary constructor parses"),
        DdlRuleAst::DdlRuleAstSExp("PFail".to_string(), Vec::new()),
    );
    for source in [
        "P == (PFail);",
        "(PConcat (PFail) P) == (PFail);",
        "(PConcat P (PFail)) == (PFail);",
    ] {
        let equation = DdlEquation::parse_via_wpda(source).expect("equation parses");
        let DdlEquation::DdlEquationDirect(_, right) = &equation else {
            panic!("expected a direct equation");
        };
        assert_eq!(
            right.as_ref(),
            &DdlRuleAst::DdlRuleAstSExp("PFail".to_string(), Vec::new()),
            "right-side constructor in {source}",
        );
    }
}

#[test]
fn wpda_preserves_regex_fixture_equation_right_side() {
    let source = include_str!("../../rholang-runtime/tests/fixtures/regex_extension.rho");
    let process = Proc::parse_via_wpda(source).expect("the complete Regex fixture parses");
    let Proc::DdlModule(_, items) = &process else {
        panic!("expected the Regex module");
    };
    let body = items
        .iter()
        .find_map(|item| match item {
            DdlModuleItem::DdlModuleProcItem(process) => match process.as_ref() {
                Proc::DdlTheory(name, _, body) if name == "RegexSyntax" => Some(body.as_ref()),
                _ => None,
            },
            _ => None,
        })
        .expect("the RegexSyntax theory exists");
    let DdlTheoryExpr::DdlTheoryRewrites(base, _) = body else {
        panic!("the syntax theory ends with its rewrites");
    };
    let DdlTheoryExpr::DdlTheoryEquations(_, equations) = base.as_ref() else {
        panic!("the rewrites extend the equations");
    };
    assert_eq!(equations.len(), 9);
    for index in [3, 4] {
        let DdlEquation::DdlEquationDirect(_, right) = &equations[index] else {
            panic!("expected a direct equation");
        };
        assert_eq!(
            right.as_ref(),
            &DdlRuleAst::DdlRuleAstSExp("PFail".to_string(), Vec::new()),
            "Regex equation {index} retains its right-side constructor before lowering",
        );
    }
    let DdlEquation::DdlEquationDirect(_, right) = &equations[5] else {
        panic!("expected a direct equation");
    };
    assert_eq!(right.as_ref(), &DdlRuleAst::DdlRuleAstVar("P".to_string()));
}

#[test]
fn module_imports_and_items_are_structural() {
    let source = r#"
        import "rho:registry/a@1" as a
        import Monoid from "rho:registry/b@2"
        Module Rholang {
            Theory Local(x:a.Base) { x }
            theory Local(a.Base)
        }
    "#;
    let term = assert_roundtrip(source);
    let Proc::DdlModuleImported(imports, name, items) = &term else {
        panic!("expected imported module");
    };
    assert_eq!(name, "Rholang");
    assert_eq!(items.len(), 2);

    let DdlImports::DdlImportsNonEmpty(first, rest) = imports.as_ref();
    assert!(matches!(
        first.as_ref(),
        DdlImport::DdlImportModuleAs(raw, alias)
            if raw == "\"rho:registry/a@1\"" && alias == "a"
    ));
    assert!(matches!(
        rest.as_slice(),
        [second]
            if matches!(
                second,
        DdlImport::DdlImportFromModule(theory, raw)
            if theory == "Monoid" && raw == "\"rho:registry/b@2\""
            )
    ));

    let DdlModuleItem::DdlModuleProcItem(declaration) = &items[0] else {
        panic!("expected a nested Theory declaration");
    };
    let Proc::DdlTheory(local_name, parameters, body) = declaration.as_ref() else {
        panic!("expected a structural nested Theory declaration");
    };
    assert_eq!(local_name, "Local");
    assert!(matches!(
        parameters.as_slice(),
        [DdlParam::DdlParamDecl(parameter, path)]
            if parameter == "x"
                && matches!(
                    path.as_ref(),
                    DdlPath::DdlPathQualified(head, tail)
                        if head == "a"
                            && matches!(tail.as_ref(), DdlPath::DdlPathName(name) if name == "Base")
                )
    ));
    assert!(matches!(body.as_ref(), DdlTheoryExpr::DdlTheoryRef(_)));

    assert!(matches!(
        &items[1],
        DdlModuleItem::DdlModuleTheoryItem(expression)
            if matches!(expression.as_ref(), DdlTheoryExpr::DdlTheoryApply(_, _))
    ));
}

#[test]
fn module_item_projection_and_collection_compose() {
    for source in ["Local", "Local()", "Local(a.Base)"] {
        DdlTheoryExpr::parse(source)
            .unwrap_or_else(|error| panic!("theory expression `{source}` must parse: {error:?}"));
    }

    for source in [
        "Theory Local() { Empty }",
        "Theory Local(x:a.Base) { x }",
        "theory Local()",
        "theory Local(a.Base)",
    ] {
        DdlModuleItem::parse(source)
            .unwrap_or_else(|error| panic!("module item `{source}` must parse: {error:?}"));
    }

    for body in [
        "Theory Local() { Empty }",
        "Theory Local(x:a.Base) { x }",
        "theory Local()",
        "theory Local(a.Base)",
        "Theory Local() { Empty } theory Local()",
        "Theory Local(x:a.Base) { x } theory Local(a.Base)",
    ] {
        for prefix in [
            "",
            "import \"rho:registry/a@1\" as a ",
            concat!(
                "import \"rho:registry/a@1\" as a ",
                "import Monoid from \"rho:registry/b@2\" ",
            ),
        ] {
            let source = format!("{prefix}Module Rholang {{ {body} }}");
            let term = parse(&source);
            assert!(
                matches!(&term, Proc::DdlModule(name, _) if name == "Rholang")
                    || matches!(&term, Proc::DdlModuleImported(_, name, _) if name == "Rholang"),
                "expected a structural module for `{source}`, got {term:?}",
            );
        }
    }
}

#[test]
fn lowercase_theory_instantiation_is_an_exact_structural_module_item() {
    let item = DdlModuleItem::parse("theory Local()")
        .expect("the lowercase BNFC theory-instantiation production must parse exactly");
    assert!(matches!(item, DdlModuleItem::DdlModuleTheoryItem(_)));
}

#[test]
fn qualified_theory_entry_uses_the_structural_wpda_path() {
    let name = DdlPath::parse_via_wpda("b").expect("a one-component DDL path parses via WPDA");
    assert!(matches!(name, DdlPath::DdlPathName(_)));
    let path = DdlPath::parse_via_wpda("b.T").expect("a qualified DDL path parses via WPDA");
    assert!(matches!(path, DdlPath::DdlPathQualified(_, _)));

    let local_expression = DdlTheoryExpr::parse_via_wpda("T()")
        .expect("an unqualified theory application parses through the WPDA");
    assert!(matches!(local_expression, DdlTheoryExpr::DdlTheoryApply(_, _)));

    let expression = DdlTheoryExpr::parse_via_wpda("b.T()")
        .expect("a qualified theory application parses through the WPDA");
    assert!(matches!(expression, DdlTheoryExpr::DdlTheoryApply(_, _)));

    let module = Proc::parse_via_wpda(r#"import "rho:base" as b Module Main { theory b.T() }"#)
        .expect("an imported module parses through the application-entry WPDA");
    let Proc::DdlModuleImported(_, name, items) = &module else {
        panic!("expected a structural imported module")
    };
    assert_eq!(name, "Main");
    assert!(matches!(
        items.as_slice(),
        [DdlModuleItem::DdlModuleTheoryItem(expression)]
            if matches!(expression.as_ref(), DdlTheoryExpr::DdlTheoryApply(_, _))
    ));
}

#[test]
fn case_distinct_ddl_literals_have_distinct_lexer_tokens() {
    let upper = lex("Theory").expect("uppercase Theory must lex");
    let lower = lex("theory").expect("lowercase theory must lex");
    assert_ne!(format!("{:?}", upper[0].0), format!("{:?}", lower[0].0));

    let dag = lex_dag("theory Local()").expect("lowercase theory input must form a token DAG");
    let first_edges = &dag.nodes[0].edges;
    assert!(matches!(
        first_edges.first().map(|edge| &edge.kind),
        Some(TokenKind::Fixed(literal)) if literal == "theory"
    ));
    assert!(first_edges.iter().any(|edge| edge.kind == TokenKind::Ident));
}

#[test]
fn leading_contextual_builder_uses_its_fixed_token_wpda_branch() {
    let source = "Types { Expr; }";
    let dag = lex_dag(source).expect("a leading DDL builder must form a token DAG");
    let first_edges = &dag.nodes[0].edges;
    assert!(first_edges
        .iter()
        .any(|edge| matches!(&edge.kind, TokenKind::Fixed(literal) if literal == "Types")));
    assert!(first_edges.iter().any(|edge| edge.kind == TokenKind::Ident));

    let parsed = DdlTheoryExpr::parse_via_wpda(source).expect(
        "the complete fixed-token builder branch must outrank a trailing identifier prefix",
    );
    assert!(matches!(parsed, DdlTheoryExpr::DdlTheoryTypesImplicit(_)));
}

#[test]
fn full_judgement_style_theory_parses_and_roundtrips() {
    let source = r#"
        Theory RhoCalc() {
            Types { Proc; Name; }
            Terms {
                PZero . |- "0" : Proc;
                PDrop . n:Name |- "*" "(" n ")" : Proc;
                PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
            }
            Equations {
                (PDrop (NQuote P)) == P;
            }
            Rewrites {
                RDrop : (PDrop (NQuote P)) ~> P;
            }
        }
    "#;
    let term = assert_roundtrip(source);
    assert!(matches!(&term, Proc::DdlTheory(name, _, _) if name == "RhoCalc"));
}

#[test]
fn contextual_ddl_words_remain_rholang_identifiers_outside_declarations() {
    for source in ["Module", "Theory", "Types", "Equations"] {
        assert!(
            matches!(parse(source), Proc::PVar(_)),
            "`{source}` must retain its ordinary Rholang identifier reading",
        );
    }
}

#[test]
fn rejected_extender_module_surface_is_not_a_ddl_declaration() {
    for source in [
        "module M { export extender E() { empty } }",
        "module M { export language L = E() }",
        "module M { export space s: L }",
        r"module M { export extender Both(L, R) { L /\ R } }",
    ] {
        mettail_runtime::clear_var_cache();
        assert!(
            Proc::parse(source).is_err(),
            "the rejected prototype surface must not parse as nouveau Rholang DDL: `{source}`",
        );
    }
}

#[test]
fn one_process_can_define_multiple_theories() {
    let term = assert_roundtrip("Theory A() { Empty } | Theory B() { Empty }");
    assert!(matches!(
        &term,
        Proc::PParInfix(left, right)
            if matches!(left.as_ref(), Proc::DdlTheory(name, _, _) if name == "A")
                && matches!(right.as_ref(), Proc::DdlTheory(name, _, _) if name == "B")
    ));
}

#[test]
fn delimiter_free_import_repetition_stops_at_eof_and_follow_token() {
    for source in [
        "import \"rho:registry/a@1\" as a",
        "import \"rho:registry/a@1\" as a import Monoid from \"rho:registry/b@2\"",
    ] {
        let parsed = DdlImports::parse(source)
            .unwrap_or_else(|error| panic!("`{source}` must parse: {error:?}"));
        let rendered = parsed.to_string();
        assert_eq!(DdlImports::parse(&rendered).unwrap(), parsed);
    }

    for source in [
        "import \"rho:registry/a@1\" as a Module M {}",
        concat!(
            "import \"rho:registry/a@1\" as a ",
            "import Monoid from \"rho:registry/b@2\" ",
            "Module M {}",
        ),
    ] {
        let module = parse(source);
        assert!(matches!(&module, Proc::DdlModuleImported(_, name, _) if name == "M"));
    }
}

#[test]
fn normative_theory_expression_surface_is_exhaustive() {
    let cases = [
        "Empty",
        "free(base.Core)",
        "Base",
        "Base()",
        "Base(Empty, free(other.Core))",
        "let b = Base() in (b)",
        "{ Base() }",
        "(Base())",
        "Types { Expr; Name; }",
        "Exports { Expr; Name => Quoted; }",
        r#"Replacements { Old => New . x:Expr |- "new" x : Expr; }"#,
        r#"Terms { Zero . |- "0" : Expr; }"#,
        "Equations { (Quote (Drop N)) == N; }",
        "Rewrites { Step : (Before X) ~> (After X); }",
        r#"Data({"types": ["Expr"]})"#,
        r#"Base Types { Expr; } Exports { Expr; } Terms { Zero . |- "0" : Expr; }"#,
        "Left /\\ Right",
        "Left \\/ Right",
        "Left \\ Right",
        "Left /\\ Middle \\/ Right \\ Removed",
    ];

    for source in cases {
        let parsed = DdlTheoryExpr::parse_via_wpda(source)
            .unwrap_or_else(|error| panic!("normative theory expression `{source}`: {error:?}"));
        let rendered = parsed.to_string();
        let reparsed = DdlTheoryExpr::parse_via_wpda(&rendered).unwrap_or_else(|error| {
            panic!("normative theory expression `{source}` rendered as `{rendered}`: {error:?}")
        });
        assert_eq!(reparsed, parsed, "WPDA round-trip failed for `{source}` as `{rendered}`");
    }
}

#[test]
fn theory_precedence_scope_and_postfix_order_have_exact_structural_asts() {
    let algebra = DdlTheoryExpr::parse_via_wpda("Left /\\ Middle \\/ Right \\ Removed")
        .expect("Greg's theory-algebra precedence example must parse");
    let DdlTheoryExpr::DdlTheoryDiff(join, removed) = &algebra else {
        panic!("difference must be the outermost constructor: {algebra:?}");
    };
    assert_theory_ref(removed.as_ref(), "Removed");
    let DdlTheoryExpr::DdlTheoryJoin(meet, right) = join.as_ref() else {
        panic!("join must bind more tightly than difference: {join:?}");
    };
    assert_theory_ref(right.as_ref(), "Right");
    let DdlTheoryExpr::DdlTheoryMeet(left, middle) = meet.as_ref() else {
        panic!("meet must bind more tightly than join: {meet:?}");
    };
    assert_theory_ref(left.as_ref(), "Left");
    assert_theory_ref(middle.as_ref(), "Middle");

    let builders = DdlTheoryExpr::parse_via_wpda(
        r#"Base Types { Expr; } Exports { Expr; } Terms { Zero . |- "0" : Expr; }"#,
    )
    .expect("postfix builders must parse in source order");
    let DdlTheoryExpr::DdlTheoryTerms(exports, terms) = &builders else {
        panic!("Terms must be the outermost postfix builder: {builders:?}");
    };
    assert_eq!(terms.len(), 1);
    let DdlTheoryExpr::DdlTheoryExports(types, exports) = exports.as_ref() else {
        panic!("Exports must retain the preceding Types result: {exports:?}");
    };
    assert_eq!(exports.len(), 1);
    let DdlTheoryExpr::DdlTheoryTypes(base, categories) = types.as_ref() else {
        panic!("Types must retain its explicit Base input: {types:?}");
    };
    assert_eq!(categories.len(), 1);
    assert_theory_ref(base.as_ref(), "Base");

    let scoped = DdlTheoryExpr::parse_via_wpda("let x = Left in (x \\/ Right)")
        .expect("a lexical theory binding must parse structurally");
    let DdlTheoryExpr::DdlTheoryLet(name, bound, body) = &scoped else {
        panic!("expected the exact lexical-let AST: {scoped:?}");
    };
    assert_eq!(name, "x");
    assert_theory_ref(bound.as_ref(), "Left");
    let DdlTheoryExpr::DdlTheoryJoin(local, right) = body.as_ref() else {
        panic!("the parenthesized let body must retain its complete join: {body:?}");
    };
    assert_theory_ref(local.as_ref(), "x");
    assert_theory_ref(right.as_ref(), "Right");
}

#[test]
fn theory_closed_primaries_resume_their_infix_continuation() {
    for source in [
        "(Left) /\\ Right",
        "{ Left } /\\ Right",
        "(let local = Base() in (local)) /\\ local",
    ] {
        let parsed = DdlTheoryExpr::parse_via_wpda(source).unwrap_or_else(|error| {
            panic!("closed theory primary must resume its enclosing infix continuation for `{source}`: {error:?}")
        });
        assert!(
            matches!(parsed, DdlTheoryExpr::DdlTheoryMeet(_, _)),
            "meet must remain the outermost constructor for `{source}`: {parsed:?}",
        );
    }
}

#[test]
fn theory_closed_primaries_preserve_infixes_when_embedded_in_proc() {
    for body in [
        "Left /\\ Right",
        "(Left) /\\ Right",
        "{ Left } /\\ Right",
        "(let local = Base() in (local)) /\\ local",
    ] {
        let source = format!("Module M {{ Theory T() {{ {body} }} theory T() }}");
        let parsed = Proc::parse_via_wpda(&source).unwrap_or_else(|error| {
            panic!("embedded theory expression must preserve its infix continuation for `{body}`: {error:?}")
        });
        assert!(
            matches!(parsed, Proc::DdlModule(ref name, _) if name == "M"),
            "module must remain the complete Proc root for `{body}`: {parsed:?}",
        );
    }

    let cases = [
        ("empty then simple meet", "Theory Base() { Empty }", "Left /\\ Right"),
        ("empty then parenthesized meet", "Theory Base() { Empty }", "(Left) /\\ Right"),
        (
            "empty then lexical let",
            "Theory Base() { Empty }",
            "let local = Base() in (local)",
        ),
        (
            "empty then parenthesized let meet",
            "Theory Base() { Empty }",
            "(let local = Base() in (local)) /\\ local",
        ),
        (
            "structured base then simple meet",
            r#"Theory Base() { Types { Expr; } Terms { X . |- "x" : Expr; } }"#,
            "Left /\\ Right",
        ),
        (
            "structured base then parenthesized let meet",
            r#"Theory Base() { Types { Expr; } Terms { X . |- "x" : Expr; } }"#,
            "(let local = Base() in (local)) /\\ local",
        ),
    ];
    let mut failures = Vec::new();
    for (label, preceding, body) in cases {
        let source = format!("Module M {{ {preceding} Theory T() {{ {body} }} theory T() }}",);
        match Proc::parse_via_wpda(&source) {
            Ok(Proc::DdlModule(ref name, _)) if name == "M" => {},
            result => failures.push(format!("{label}: {result:?}")),
        }
    }
    let compact = r#"Module Leaking { Theory Base() { Types { Expr; } Terms { X . |- "x" : Expr; } } Theory Bad() { (let local = Base() in (local)) /\ local } theory Bad() }"#;
    match Proc::parse_via_wpda(compact) {
        Ok(Proc::DdlModule(ref name, _)) if name == "Leaking" => {},
        result => failures.push(format!("compact exact: {result:?}")),
    }
    let multiline = r#"Module Leaking {
        Theory Base() { Types { Expr; } Terms { X . |- "x" : Expr; } }
        Theory Bad() { (let local = Base() in (local)) /\ local }
        theory Bad()
    }"#;
    let compact_dag = lex_dag(compact).expect("compact module must lex");
    let multiline_dag = lex_dag(multiline).expect("multiline module must lex");
    let compact_shape: Vec<_> = compact_dag
        .nodes
        .iter()
        .map(|node| {
            node.edges
                .iter()
                .map(|edge| {
                    (
                        edge.kind.clone(),
                        edge.text.clone(),
                        edge.target_node,
                        edge.alt_idx,
                        format!("{:?}", edge.weight),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect();
    let multiline_shape: Vec<_> = multiline_dag
        .nodes
        .iter()
        .map(|node| {
            node.edges
                .iter()
                .map(|edge| {
                    (
                        edge.kind.clone(),
                        edge.text.clone(),
                        edge.target_node,
                        edge.alt_idx,
                        format!("{:?}", edge.weight),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(compact_dag.eof_node, multiline_dag.eof_node);
    assert_eq!(
        compact_shape, multiline_shape,
        "whitespace must not change the token DAG topology"
    );
    match Proc::parse_via_wpda(multiline) {
        Ok(Proc::DdlModule(ref name, _)) if name == "Leaking" => {},
        result => failures.push(format!("multiline exact: {result:?}")),
    }
    let malformed_double_backslash = r#"Module Leaking {
        Theory Base() { Empty }
        Theory Bad() { (let local = Base() in (local)) /\\ local }
        theory Bad()
    }"#;
    assert!(
        Proc::parse_via_wpda(malformed_double_backslash).is_err(),
        "a doubled backslash is not Greg's single-backslash meet token",
    );
    assert!(
        failures.is_empty(),
        "multi-item module composition lost complete Proc roots:\n{}",
        failures.join("\n"),
    );
}

#[test]
fn normative_judgement_and_rule_ast_surface_is_exhaustive() {
    for rewrite in [
        "Direct : (Before X) ~> (After X);",
        concat!(
            "Conditional : if S ~> T then if U ~> V then ",
            "(Bag {(Pair S U), ...rest}) ~> (Bag {(Pair T V), ...rest});",
        ),
        "Substitute : (Apply ^x.p Q) ~> (subst ^x.p Q);",
        "EmptyBag : (Bag {}) ~> (Bag {...rest});",
    ] {
        DdlRewrite::parse_via_wpda(rewrite)
            .unwrap_or_else(|error| panic!("normative DDL rewrite `{rewrite}`: {error:?}"));
    }

    for fragment in [
        r#"Types { Expr; Name; }"#,
        r#"
        Terms {
            Empty . |- "empty" : Expr;
            Plain . x:Expr |- "plain" x : Expr;
            Bag . xs:HashBag(Expr) |- "{" xs.*sep(",") "}" : Expr;
            SetTerm . xs:Set(Expr) |- "Set" "(" xs.*sep(",") ")" : Expr;
            ListTerm . xs:List(Expr) |- "[" xs.*sep(",") "]" : Expr;
            Binder . ^x.p:[Name -> Expr] |- "bind" x "." p : Expr;
        }
        "#,
        r#"
        Equations {
            (Drop (Quote X)) == X;
            if x # P then if y # Q then (Fresh x y) == (Fresh y x);
        }
        "#,
        r#"
        Rewrites {
            Direct : (Before X) ~> (After X);
            Conditional : if S ~> T then if U ~> V then
              (Bag {(Pair S U), ...rest}) ~> (Bag {(Pair T V), ...rest});
            Substitute : (Apply ^x.p Q) ~> (subst ^x.p Q);
            EmptyBag : (Bag {}) ~> (Bag {...rest});
        }
        "#,
    ] {
        DdlTheoryExpr::parse_via_wpda(fragment)
            .unwrap_or_else(|error| panic!("normative DDL fragment `{fragment}`: {error:?}"));
    }

    let theory = DdlTheoryExpr::parse_via_wpda(
        r#"
        Types { Expr; Name; }
        Terms {
            Empty . |- "empty" : Expr;
            Plain . x:Expr |- "plain" x : Expr;
            Bag . xs:HashBag(Expr) |- "{" xs.*sep(",") "}" : Expr;
            SetTerm . xs:Set(Expr) |- "Set" "(" xs.*sep(",") ")" : Expr;
            ListTerm . xs:List(Expr) |- "[" xs.*sep(",") "]" : Expr;
            Binder . ^x.p:[Name -> Expr] |- "bind" x "." p : Expr;
        }
        Equations {
            (Drop (Quote X)) == X;
            if x # P then if y # Q then (Fresh x y) == (Fresh y x);
        }
        Rewrites {
            Direct : (Before X) ~> (After X);
            Conditional : if S ~> T then if U ~> V then
              (Bag {(Pair S U), ...rest}) ~> (Bag {(Pair T V), ...rest});
            Substitute : (Apply ^x.p Q) ~> (subst ^x.p Q);
            EmptyBag : (Bag {}) ~> (Bag {...rest});
        }
        "#,
    )
    .expect("every closed judgement-style DDL constructor must parse through the WPDA");

    let rendered = theory.to_string();
    let reparsed = DdlTheoryExpr::parse_via_wpda(&rendered)
        .unwrap_or_else(|error| panic!("combined theory rendered as `{rendered}`: {error:?}"));
    assert_eq!(reparsed, theory, "combined theory round-trip changed structure");
}

#[test]
fn malformed_greg_mike_forms_fail_as_complete_rholang_inputs() {
    for source in [
        "Module M {",
        "Module M { theory T( }",
        "Theory T( { Empty }",
        "Theory T() { free(.) }",
        "Theory T() { Types { Expr } }",
        r#"Theory T() { Terms { Bad . x:Expr "x" : Expr; } }"#,
        "Theory T() { Equations { X = Y; } }",
        "Theory T() { Rewrites { X ~> Y; } }",
        r#"import "rho:registry/base@1" Module M {}"#,
        "Space S() { }",
        "Presentation Exports { Expr; } Terms { Zero . Expr ::= \"0\"; }",
        r#"Theory T() { Empty Terms { Zero . Expr ::= "0"; } }"#,
    ] {
        mettail_runtime::clear_var_cache();
        assert!(
            Proc::parse_via_wpda(source).is_err(),
            "malformed DDL must not be accepted as a complete Rholang process: `{source}`",
        );
    }
}

#[test]
fn ddl_comments_strings_and_flt_guest_text_keep_their_lexer_domains() {
    let source = r#"
        // This comment is retained on the COMMENTS token channel.
        Theory T() {
            /* The generated Rholang parser consumes this comment once. */
            Types { Expr; }
            Terms { Slash . |- "// is literal DDL terminal text" : Expr; }
        }
        |
        lam:Proc`// and /* */ are literal guest text`
    "#;
    let parsed = Proc::parse_via_wpda(source)
        .expect("comments, DDL string terminals, and FLT guest text have disjoint lexer domains");
    assert!(matches!(
        &parsed,
        Proc::PParInfix(left, right)
            if matches!(left.as_ref(), Proc::DdlTheory(name, _, _) if name == "T")
                && matches!(right.as_ref(), Proc::PFlt(_))
    ));
}
