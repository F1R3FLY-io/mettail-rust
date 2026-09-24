mod owned_atomic_reuse {
    use super::*;
    use crate::gen::runtime::wpda_codegen::authored_capture::{capture_language, capture_rules};
    use mettail_grammar_core::{Associativity, AuthoredLegacyItem, AuthoredNode, AuthoredRuleId};
    use mettail_prattail::wpda_rule_analysis::atomic::AtomicDescriptor;
    use mettail_prattail::wpda_rule_analysis::authored::AuthoredRuleReader;
    use mettail_prattail::wpda_rule_analysis::authored_atomic::derive_authored_atomic;
    use mettail_prattail::wpda_rule_analysis::infix_projection::InfixProjectionError;
    use std::convert::Infallible;

    pub(super) fn assert_owned_parity(rule: &GrammarRule, language: &LanguageDef) {
        let expected = classify_atomic_descriptor(rule, language);
        let mut source = language.clone();
        source.terms = vec![rule.clone()];
        let captured =
            capture_language(&source).expect("capture the same source rule and language");
        let root = AuthoredRuleId(captured.roots[0]);
        let reader = AuthoredRuleReader::new(&captured.store).expect("validated captured reader");
        let actual = derive_authored_atomic(
            &reader,
            root,
            if rule.is_right_assoc {
                Associativity::Right
            } else {
                Associativity::Left
            },
            rule.shares_level_with_previous,
            |_, _| Ok::<_, Infallible>(()),
            |name| {
                let Some(AuthoredNode::Rule(retained)) = captured.store.get(root.0) else {
                    panic!("captured root must be a rule");
                };
                let [AuthoredLegacyItem::NonTerminal {
                    ident: retained_name,
                    kind: NonTerminalKind::Category,
                }] = retained.items.as_slice()
                else {
                    panic!("literal resolution requires singleton Category");
                };
                assert_eq!(name, *retained_name);
                let [GrammarItem::NonTerminal { ident, kind: NonTerminalKind::Category }] =
                    rule.items.as_slice()
                else {
                    panic!("retained singleton must correspond to original singleton");
                };
                let Some(AuthoredNode::Name(retained)) = captured.store.get(name.0) else {
                    panic!("literal callback must receive the retained name handle");
                };
                assert_eq!(retained.spelling, ident.to_string());
                classify_literal_patterned(ident, language)
            },
        )
        .expect("owned atomic descriptor");
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn owned_atomic_preserves_unsupported_legacy_positions() {
        let language = empty_lang();
        for other in [
            GrammarItem::Binder {
                category: Ident::new("Name", Span::call_site()),
            },
            GrammarItem::Collection {
                coll_type: mettail_ast::types::CollectionType::Vec,
                element_type: Ident::new("Int", Span::call_site()),
                separator: ",".into(),
                delimiters: Some(("[".into(), "]".into())),
            },
        ] {
            for items in [
                vec![other.clone()],
                vec![other.clone(), GrammarItem::Terminal("keyword".into())],
                vec![GrammarItem::Terminal("keyword".into()), other.clone()],
            ] {
                let mut rule = terminal_rule("Other", "Int", "keyword");
                rule.items = items;
                assert_atomic_projection_baseline(&rule, &language, AtomicShape::NonAtomic);
            }
        }
    }

    #[test]
    fn owned_atomic_unary_keeps_optional_and_nested_types_unsupported() {
        use mettail_ast::types::CollectionType;

        let language = empty_lang();
        let base = TypeExpr::Base(Ident::new("Int", Span::call_site()));
        let collection = TypeExpr::Collection {
            coll_type: CollectionType::Vec,
            element: Box::new(base.clone()),
        };
        let fixture = judgement_rule(
            "Neg",
            "Int",
            &[("value", "Int")],
            vec![
                SyntaxExpr::Literal("-".into()),
                SyntaxExpr::Param(Ident::new("value", Span::call_site())),
            ],
        );
        for ty in [
            collection.clone(),
            TypeExpr::Collection {
                coll_type: CollectionType::Vec,
                element: Box::new(collection),
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
            let mut rule = fixture.clone();
            rule.term_context = Some(vec![TermParam::Simple {
                name: Ident::new("value", Span::call_site()),
                ty,
            }]);
            assert!(mettail_ast::grammar_shapes::classify_unary_prefix_shape(&rule).is_none());
            assert_atomic_projection_baseline(&rule, &language, AtomicShape::NonAtomic);
        }
        let mut optional = fixture.clone();
        optional.term_context = Some(vec![TermParam::Optional {
            params: optional.term_context.take().expect("fixture context"),
        }]);
        assert_atomic_projection_baseline(&optional, &language, AtomicShape::NonAtomic);
        let mut syntax_optional = fixture;
        syntax_optional.syntax_pattern = Some(vec![
            SyntaxExpr::Literal("-".into()),
            SyntaxExpr::Op(mettail_ast::grammar::PatternOp::Opt {
                inner: vec![SyntaxExpr::Param(Ident::new("value", Span::call_site()))],
            }),
        ]);
        assert_atomic_projection_baseline(&syntax_optional, &language, AtomicShape::NonAtomic);
    }

    #[test]
    fn owned_atomic_unary_preserves_raw_spelling() {
        let language = empty_lang();
        let mut rule = judgement_rule("Raw", "Int", &[], Vec::new());
        rule.category = Ident::new_raw("Int", Span::call_site());
        rule.term_context = Some(vec![TermParam::Simple {
            name: Ident::new_raw("value", Span::call_site()),
            ty: TypeExpr::Base(Ident::new_raw("Int", Span::mixed_site())),
        }]);
        rule.syntax_pattern = Some(vec![
            SyntaxExpr::Literal("-".into()),
            SyntaxExpr::Param(Ident::new_raw("value", Span::mixed_site())),
        ]);
        assert_atomic_projection_baseline(
            &rule,
            &language,
            AtomicShape::PrefixOperator {
                trigger: "-".into(),
                operand_cat_name: "r#Int".into(),
            },
        );
        rule.syntax_pattern.as_mut().expect("fixture syntax")[1] =
            SyntaxExpr::Param(Ident::new("value", Span::call_site()));
        assert_atomic_projection_baseline(&rule, &language, AtomicShape::NonAtomic);
    }

    #[test]
    fn owned_atomic_admission_precedes_observation_and_needs_no_header() {
        let rule = terminal_rule("Keyword", "Int", "keyword");
        let captured = capture_rules(&[rule]).expect("header-free fixture");
        assert!(captured.store.declarations().is_none());
        let reader = AuthoredRuleReader::new(&captured.store).expect("captured reader");
        let mut calls = 0;
        let denied = derive_authored_atomic(
            &reader,
            AuthoredRuleId(u32::MAX),
            Associativity::Left,
            false,
            |observed, rule| {
                calls += 1;
                assert!(std::ptr::eq(observed, &reader));
                assert_eq!(rule, AuthoredRuleId(u32::MAX));
                Err(7)
            },
            |_| -> Option<()> { panic!("admission denial must precede literal callback") },
        );
        assert_eq!(denied, Err(InfixProjectionError::Admission(7)));
        assert_eq!(calls, 1);

        let root = AuthoredRuleId(captured.roots[0]);
        let accepted = derive_authored_atomic(
            &reader,
            root,
            Associativity::Left,
            false,
            |_, _| Ok::<_, Infallible>(()),
            |_| -> Option<()> { panic!("terminal must not invoke literal callback") },
        )
        .expect("atomic derivation needs no declaration header");
        assert_eq!(
            accepted,
            AtomicDescriptor::TerminalKeyword {
                terminal_text: "keyword".into(),
                wrapper_variant: "Keyword".into(),
            }
        );
        let unsupported = derive_authored_atomic(
            &reader,
            root,
            Associativity::NonAssociative,
            false,
            |_, _| Ok::<_, Infallible>(()),
            |_| -> Option<()> { panic!("unsupported flags precede literal callback") },
        );
        assert_eq!(unsupported, Err(InfixProjectionError::UnsupportedNonAssociativity));
    }
}
