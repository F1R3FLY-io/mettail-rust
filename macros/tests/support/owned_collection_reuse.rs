mod owned_collection_reuse {
    use super::*;
    use mettail_prattail::wpda_rule_analysis::authored::AuthoredRuleReader;
    use mettail_prattail::wpda_rule_analysis::authored_collection::derive_authored_collection;
    use mettail_prattail::wpda_rule_analysis::collection_projection::try_project_collection_rule_in;
    use std::convert::Infallible;

    pub(super) fn assert_parity(
        rule: &GrammarRule,
        language: &mettail_ast::language::LanguageDef,
    ) -> Option<CollectionShape> {
        let expected = classify_collection(rule, language);
        let mut source = language.clone();
        source.terms = vec![rule.clone()];
        let captured =
            crate::gen::runtime::wpda_codegen::authored_capture::capture_language(&source)
                .expect("existing source capture accepts the fixture");
        let reader = AuthoredRuleReader::new(&captured.store).expect("captured reader");
        let projected = try_project_collection_rule_in(
            &reader,
            mettail_grammar_core::AuthoredRuleId(captured.roots[0]),
            |_, _| Ok::<_, Infallible>(()),
        )
        .expect("shallow collection projection");
        assert_eq!(
            projected.term_context.as_ref().map(Vec::len),
            rule.term_context.as_ref().map(Vec::len)
        );
        assert_eq!(
            projected.syntax_pattern.as_ref().map(Vec::len),
            rule.syntax_pattern.as_ref().map(Vec::len)
        );
        let actual = derive_authored_collection(
            &reader,
            mettail_grammar_core::AuthoredRuleId(captured.roots[0]),
            |_, _, _| Ok::<_, Infallible>(()),
        )
        .expect("owned collection derivation");
        match (&expected, &actual) {
            (None, None) => {},
            (Some(expected), Some(actual)) => {
                assert_eq!(actual.open_token, expected.open_token);
                assert_eq!(actual.has_synth_paren, expected.has_synth_paren);
                assert_eq!(actual.close, expected.close);
                assert_eq!(actual.separator, expected.separator);
                assert_eq!(actual.pair_separator, expected.pair_separator);
                assert_eq!(actual.element_cat, expected.element_cat);
                assert_eq!(actual.coll_kind, expected.coll_kind);
                assert_eq!(actual.label, expected.label);
            },
            _ => panic!("collection classification differs: {expected:?} vs {actual:?}"),
        }
        expected
    }

    #[test]
    fn optional_collection_parameter_is_not_flattened() {
        let mut rule = collection_baseline_rule(CollectionType::Vec, false);
        let params = rule.term_context.take().expect("fixture context");
        rule.term_context = Some(vec![TermParam::Optional { params }]);
        assert!(assert_parity(&rule, &empty_lang()).is_none());
    }

    #[test]
    fn empty_declared_pair_separator_is_not_defaulted() {
        let mut language = empty_lang();
        let mut delimiters = CollectionCategory::map_defaults();
        delimiters.key_val_sep = Some(String::new());
        language.types.push(mettail_ast::language::LangType {
            name: Ident::new("Home", Span::call_site()),
            role: Default::default(),
            native_type: None,
            collection_kind: Some(CollectionCategory::Map(delimiters)),
        });
        let shape = assert_parity(&collection_baseline_rule(CollectionType::Vec, false), &language)
            .expect("vector-shaped rule uses its result declaration");
        assert_eq!(shape.pair_separator.as_deref(), Some(""));
    }
}
