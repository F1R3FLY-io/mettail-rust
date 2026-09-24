mod owned_infix_reuse {
    use super::*;
    use mettail_grammar_core::{Associativity as CoreAssociativity, AuthoredRuleId};
    use mettail_prattail::wpda_rule_analysis::authored::AuthoredRuleReader;
    use mettail_prattail::wpda_rule_analysis::authored_synthesis::{
        derive_authored_rules, AuthoredRuleOrigin,
    };
    use mettail_prattail::wpda_rule_analysis::infix_projection::{
        try_project_infix_rule_in, InfixProjectionError,
    };
    use std::convert::Infallible;

    pub(super) fn assert_owned_projection(rule: &GrammarRule) {
        let captured = crate::gen::runtime::wpda_codegen::authored_capture::capture_rules(
            std::slice::from_ref(rule),
        )
        .expect("capture original source observations");
        let reader = AuthoredRuleReader::new(&captured.store).expect("owned shallow reader");
        let owned = try_project_infix_rule_in(
            &reader,
            AuthoredRuleId(captured.roots[0]),
            if rule.is_right_assoc {
                CoreAssociativity::Right
            } else {
                CoreAssociativity::Left
            },
            rule.shares_level_with_previous,
            |_, _| Ok::<_, Infallible>(()),
        )
        .expect("retained source view");
        assert_eq!(owned, project_infix_rule(rule));
    }

    #[test]
    fn owned_infix_projection_preserves_absence_other_positions_and_immediate_types() {
        for context in [None, Some(Vec::new())] {
            for pattern in [None, Some(Vec::new())] {
                let mut rule = infix_rule("Empty", "Int", "Int", "+");
                rule.term_context = context.clone();
                rule.syntax_pattern = pattern;
                assert_owned_projection(&rule);
            }
        }
        let mut rule = infix_rule("Unsupported", "Int", "Int", "+");
        rule.term_context
            .as_mut()
            .unwrap()
            .insert(1, TermParam::Optional { params: vec![simple("nested", "Int")] });
        rule.syntax_pattern
            .as_mut()
            .unwrap()
            .insert(1, SyntaxExpr::Op(PatternOp::Opt { inner: vec![lit("ignored")] }));
        assert_owned_projection(&rule);
        assert!(classify_rule(&rule).is_none());

        let base = TypeExpr::Base(Ident::new("Int", Span::call_site()));
        for ty in [
            base.clone(),
            TypeExpr::Collection {
                coll_type: mettail_ast::types::CollectionType::Vec,
                element: Box::new(base.clone()),
            },
            TypeExpr::Collection {
                coll_type: mettail_ast::types::CollectionType::Vec,
                element: Box::new(TypeExpr::Collection {
                    coll_type: mettail_ast::types::CollectionType::Vec,
                    element: Box::new(base.clone()),
                }),
            },
            TypeExpr::Arrow {
                domain: Box::new(base.clone()),
                codomain: Box::new(base.clone()),
            },
            TypeExpr::Map {
                key: Box::new(base.clone()),
                value: Box::new(base),
            },
        ] {
            let mut rule = postfix_rule("Shallow", "Int", "Int", "!");
            rule.term_context = Some(vec![TermParam::Simple {
                name: Ident::new_raw("type", Span::call_site()),
                ty,
            }]);
            rule.syntax_pattern = Some(vec![
                SyntaxExpr::Param(Ident::new_raw("type", Span::mixed_site())),
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: Ident::new("δ", Span::call_site()),
                    separator: ";".into(),
                    source: Some(Box::new(PatternOp::Zip {
                        left: Ident::new("left", Span::call_site()),
                        right: Ident::new("right", Span::call_site()),
                    })),
                }),
            ]);
            assert_owned_projection(&rule);
        }
    }

    #[test]
    fn owned_infix_projection_keeps_admission_and_unrepresentable_flags_explicit() {
        let rule = infix_rule("Denied", "Int", "Int", "+");
        let captured = crate::gen::runtime::wpda_codegen::authored_capture::capture_rules(&[rule])
            .expect("capture fixture");
        let reader = AuthoredRuleReader::new(&captured.store).unwrap();
        let root = AuthoredRuleId(captured.roots[0]);
        assert_eq!(
            try_project_infix_rule_in(&reader, root, CoreAssociativity::Left, false, |_, _| Err(7)),
            Err(InfixProjectionError::Admission(7))
        );
        assert_eq!(
            try_project_infix_rule_in(
                &reader,
                root,
                CoreAssociativity::NonAssociative,
                false,
                |_, _| Ok::<_, Infallible>(())
            ),
            Err(InfixProjectionError::UnsupportedNonAssociativity)
        );
    }

    #[test]
    fn owned_infix_source_order_crosses_result_buckets_and_preserves_duplicate_receipts() {
        let mut language = crate::gen::empty_language_for_tests();
        for name in ["Int", "Bool"] {
            language.types.push(mettail_ast::language::LangType {
                name: Ident::new(name, Span::call_site()),
                role: Default::default(),
                native_type: None,
                collection_kind: None,
            });
        }
        let mut eq = infix_rule("Eq", "Bool", "Int", "==");
        eq.is_right_assoc = true;
        eq.shares_level_with_previous = true;
        language.terms =
            vec![infix_rule("Add", "Int", "Int", "+"), eq, infix_rule("Mul", "Int", "Int", "*")];
        let core = crate::gen::syntax::parser::prattail_bridge::language_def_to_spec(&language)
            .unwrap()
            .to_grammar_core()
            .unwrap();
        for occurrences in [vec![0, 1, 2], vec![2, 0, 2]] {
            let output =
                derive_authored_rules(&core, &occurrences, |_| Ok::<_, Infallible>(())).unwrap();
            let reader = AuthoredRuleReader::new(&output.store).unwrap();
            assert_eq!(output.source_order.len(), occurrences.len());
            let mut infos = Vec::new();
            let mut expected_infos = Vec::new();
            for (ordinal, (payload, &production)) in
                output.source_order.iter().zip(&occurrences).enumerate()
            {
                assert_eq!(
                    payload.origin,
                    AuthoredRuleOrigin::User {
                        roster_index: ordinal,
                        production_index: production,
                    }
                );
                let metadata = core.productions[production].precedence;
                let view = try_project_infix_rule_in(
                    &reader,
                    payload.rule,
                    metadata.associativity,
                    metadata.shares_previous_level,
                    |_, _| Ok::<_, Infallible>(()),
                )
                .unwrap();
                let mut original = language.terms[production].clone();
                mettail_ast::grammar::convert_items_to_term_context(&mut original);
                assert_eq!(view, project_infix_rule(&original));
                infos.extend(mettail_prattail::wpda_rule_analysis::classify_rule(&view));
                expected_infos.extend(classify_rule(&original));
            }
            assert_eq!(format!("{infos:?}"), format!("{expected_infos:?}"));
            let table = mettail_prattail::binding_power::try_analyze_binding_powers(&infos, |_| {
                Ok::<_, Infallible>(())
            })
            .unwrap();
            let expected = analyze_binding_powers(&expected_infos);
            assert_eq!(format!("{:?}", table.operators), format!("{:?}", expected.operators));
            let pairs: Vec<_> = table
                .operators
                .iter()
                .map(|op| (op.left_bp, op.right_bp))
                .collect();
            assert_eq!(
                pairs,
                if occurrences == [0, 1, 2] {
                    vec![(2, 3), (3, 2), (4, 5)]
                } else {
                    vec![(2, 3), (4, 5), (6, 7)]
                }
            );
        }
    }
}
