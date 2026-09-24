mod owned_cast_reuse {
    use super::owned_prefix_reuse::{core, mixed_language};
    use super::*;
    use crate::gen::runtime::numeric_cast_adapter as source;
    use crate::gen::runtime::wpda_codegen as original;
    use mettail_ast::types::EvalMode;
    use mettail_grammar_core::{
        AuthoredNode, AuthoredRule, AuthoredRuleId, AuthoredRuleStore, GrammarCoreV1,
        SourceObservation,
    };
    use mettail_prattail::wpda_rule_analysis::authored::AuthoredRuleReader;
    use mettail_prattail::wpda_rule_analysis::authored_cast::{
        try_authored_cast_participates, AuthoredCastError,
    };
    use mettail_prattail::wpda_rule_analysis::authored_synthesis::derive_authored_rules;
    use std::convert::Infallible;

    fn source_rules(core: &GrammarCoreV1, count: usize) -> Vec<AuthoredRuleId> {
        core.productions[..count]
            .iter()
            .map(|production| {
                production
                    .authored
                    .expect("captured original production has a rule handle")
            })
            .collect()
    }

    fn assert_facts(store: &AuthoredRuleStore, handle: AuthoredRuleId, source: &GrammarRule) {
        let Some(AuthoredNode::Rule(rule)) = store.get(handle.0) else {
            panic!("valid rule handle must point to retained authored source");
        };
        assert_eq!(
            rule.source_body_present,
            SourceObservation::Known(source.rust_code.is_some()),
            "body presence for {}",
            source.label
        );
        assert_eq!(
            rule.explicit_fold,
            SourceObservation::Known(source.eval_mode == Some(EvalMode::Fold)),
            "explicit source Fold for {}",
            source.label
        );
    }

    fn change_rule(
        store: &AuthoredRuleStore,
        handle: AuthoredRuleId,
        mut change: impl FnMut(&mut AuthoredRule),
    ) -> AuthoredRuleStore {
        let mut result = AuthoredRuleStore::new();
        for index in 0..store.len() {
            let index = u32::try_from(index).expect("bounded captured fixture arena");
            let mut node = store.get(index).expect("existing captured node").clone();
            if index == handle.0 {
                let AuthoredNode::Rule(rule) = &mut node else {
                    panic!("mutation must target exact rule handle");
                };
                change(rule);
            }
            assert_eq!(result.try_push(node).expect("retain original arena order"), index);
        }
        result
            .with_declarations(store.declarations().expect("captured header").clone())
            .expect("unavailable metadata is structurally valid, not known absence")
    }

    #[test]
    fn owned_cast_flags_and_results_match_original_raw_and_normalized_rules() {
        for fixture in [source::NATIVE_CAST_GRAMMAR, source::OBJECT_CAST_GRAMMAR] {
            let language: LanguageDef = syn::parse_str(fixture).expect("existing cast fixture");
            let core = core(&language);
            let handles = source_rules(&core, language.terms.len());
            let store = core.authored.as_ref().expect("captured authored source");
            let reader = AuthoredRuleReader::new(store).expect("validated original source");
            for (&handle, rule) in handles.iter().zip(&language.terms) {
                assert_facts(store, handle, rule);
                assert_eq!(
                    try_authored_cast_participates(
                        &reader,
                        handle,
                        handles.iter().copied(),
                        |spelling| Ok::<_, Infallible>(source::original_trigger_kind_for_test(
                            &language, spelling
                        ))
                    ),
                    Ok(source::cast_machinery_participates(&language, rule)),
                    "raw cast source rule {}",
                    rule.label
                );
            }

            let occurrences: Vec<_> = (0..language.terms.len()).collect();
            let synthesis = derive_authored_rules(&core, &occurrences, |_| Ok::<_, Infallible>(()))
                .expect("reuse original normalization and synthetic constructors");
            let categories = original::collect_category_names_with_literals(&language);
            let per_cat = original::synthetic::build_per_category_rules(&language, &categories);
            assert_eq!(synthesis.categories, categories);
            assert_eq!(synthesis.per_category.len(), per_cat.len());
            let reader =
                AuthoredRuleReader::new(&synthesis.store).expect("validated normalized source");
            for (owned, original) in synthesis.per_category.iter().zip(&per_cat) {
                assert_eq!(owned.len(), original.len());
                for (payload, rule) in owned.iter().zip(original) {
                    assert_facts(&synthesis.store, payload.rule, rule);
                    assert_eq!(
                        try_authored_cast_participates(
                            &reader,
                            payload.rule,
                            handles.iter().copied(),
                            |spelling| Ok::<_, Infallible>(source::original_trigger_kind_for_test(
                                &language, spelling
                            ))
                        ),
                        Ok(source::cast_machinery_participates(&language, rule)),
                        "normalized or synthetic rule {}",
                        rule.label
                    );
                }
            }
        }
    }

    #[test]
    fn unavailable_body_and_explicit_fold_are_not_semantic_nonmatches() {
        let language: LanguageDef =
            syn::parse_str(source::OBJECT_CAST_GRAMMAR).expect("existing object cast fixture");
        let core = core(&language);
        let handles = source_rules(&core, language.terms.len());
        let wrapper = language
            .terms
            .iter()
            .position(|rule| rule.label == "CastInt")
            .expect("existing fixture wrapper");
        let fold = language
            .terms
            .iter()
            .position(|rule| rule.label == "IntBinProc")
            .expect("existing fixture explicit Fold");
        let store = core.authored.as_ref().expect("captured source");
        let missing_body = change_rule(store, handles[wrapper], |rule| {
            rule.source_body_present = SourceObservation::Unavailable;
        });
        let reader =
            AuthoredRuleReader::new(&missing_body).expect("structurally valid unknown body");
        assert_eq!(
            try_authored_cast_participates(
                &reader,
                handles[wrapper],
                handles.iter().copied(),
                |spelling| Ok::<_, Infallible>(source::original_trigger_kind_for_test(
                    &language, spelling
                ))
            ),
            Err(AuthoredCastError::SourceBodyUnavailable(handles[wrapper]))
        );

        let missing_fold = change_rule(store, handles[fold], |rule| {
            rule.explicit_fold = SourceObservation::Unavailable;
        });
        let reader =
            AuthoredRuleReader::new(&missing_fold).expect("structurally valid unknown Fold");
        assert_eq!(
            try_authored_cast_participates(
                &reader,
                handles[fold],
                handles.iter().copied(),
                |spelling| Ok::<_, Infallible>(source::original_trigger_kind_for_test(
                    &language, spelling
                ))
            ),
            Err(AuthoredCastError::ExplicitFoldUnavailable(handles[fold]))
        );
    }

    #[test]
    fn original_trigger_lookup_precedes_and_can_skip_unavailable_later_flags() {
        let language = mixed_language();
        let core = core(&language);
        let handles = source_rules(&core, language.terms.len());
        let target = language
            .terms
            .iter()
            .position(|rule| rule.label == "UnaryCross")
            .expect("existing numeric trigger wrapper fixture");
        assert!(source::cast_machinery_participates(&language, &language.terms[target]));
        let changed = change_rule(
            core.authored.as_ref().expect("captured source"),
            handles[target],
            |rule| {
                rule.source_body_present = SourceObservation::Unavailable;
                rule.explicit_fold = SourceObservation::Unavailable;
            },
        );
        let reader = AuthoredRuleReader::new(&changed).expect("structurally valid unknown flags");
        let mut trigger_queries = Vec::new();
        assert_eq!(
            try_authored_cast_participates(
                &reader,
                handles[target],
                handles.iter().copied(),
                |spelling| {
                    trigger_queries.push(spelling.to_string());
                    Ok::<_, Infallible>(source::original_trigger_kind_for_test(&language, spelling))
                }
            ),
            Ok(true)
        );
        assert_eq!(trigger_queries, vec!["Int"]);
        assert_eq!(
            try_authored_cast_participates(
                &reader,
                handles[target],
                handles.iter().copied(),
                |_| Err("rendered source lookup unavailable")
            ),
            Err(AuthoredCastError::RenderedTrigger("rendered source lookup unavailable"))
        );
    }

    #[test]
    fn ambiguous_original_wrapper_election_is_refused_without_guessing_a_winner() {
        let mut language: LanguageDef =
            syn::parse_str(source::OBJECT_CAST_GRAMMAR).expect("existing object cast fixture");
        let mut other = language
            .types
            .iter()
            .find(|ty| ty.name == "Proc")
            .expect("original object category")
            .clone();
        other.name = Ident::new("OtherProc", Span::call_site());
        language.types.push(other);
        let mut other_wrapper = language
            .terms
            .iter()
            .find(|rule| rule.label == "CastInt")
            .expect("existing numeric wrapper")
            .clone();
        other_wrapper.label = Ident::new("OtherWrapper", Span::call_site());
        other_wrapper.category = Ident::new("OtherProc", Span::call_site());
        language.terms.push(other_wrapper);
        let core = core(&language);
        let handles = source_rules(&core, language.terms.len());
        let target = language
            .terms
            .iter()
            .position(|rule| rule.label == "IntBinProc")
            .expect("existing object Fold target");
        let wrapper = language
            .terms
            .iter()
            .position(|rule| rule.label == "CastInt")
            .expect("existing Proc wrapper");
        let reader = AuthoredRuleReader::new(core.authored.as_ref().expect("captured source"))
            .expect("validated tie fixture source");
        assert_eq!(
            try_authored_cast_participates(
                &reader,
                handles[target],
                handles.iter().copied(),
                |spelling| Ok::<_, Infallible>(source::original_trigger_kind_for_test(
                    &language, spelling
                ))
            ),
            Err(AuthoredCastError::AmbiguousObjectCategory)
        );

        // Explicit duplicate occurrences contribute to the original census.
        // A unique maximum is then independent of HashMap iteration order.
        let mut unique_roster = handles.clone();
        unique_roster.push(handles[wrapper]);
        let mut selected = language.clone();
        selected.terms.push(language.terms[wrapper].clone());
        let expected = source::cast_machinery_participates(&selected, &language.terms[target]);
        assert!(expected, "duplicate Proc wrapper produces the unique correct object election");
        assert_eq!(
            try_authored_cast_participates(
                &reader,
                handles[target],
                unique_roster,
                |spelling| Ok::<_, Infallible>(source::original_trigger_kind_for_test(
                    &selected, spelling
                ))
            ),
            Ok(expected)
        );
    }
}
