mod owned_descriptor_reuse {
    use super::owned_prefix_reuse::{core, guest_language, observations, original_quote};
    use super::*;
    use crate::gen::runtime::numeric_cast_adapter::cast_machinery_participates;
    use crate::gen::runtime::wpda_codegen as original;
    use mettail_ast::language::{CollectionCategory, CollectionDelimiters};
    use mettail_prattail::wpda_rule_analysis::authored_descriptors::{
        derive_authored_descriptors, AuthoredDescriptorsError, DescriptorOptions,
    };
    use mettail_prattail::wpda_rule_analysis::authored_synthesis::derive_authored_rules;
    use mettail_prattail::wpda_rule_analysis::binder::rule::BinderRuleReader;
    use mettail_prattail::wpda_rule_analysis::parikh::build_parikh_descriptors;
    use mettail_prattail::wpda_rule_analysis::prefix_bucket::derive_prefix_buckets;
    use std::cell::Cell;
    use std::convert::Infallible;

    fn options(factoring: bool) -> DescriptorOptions {
        DescriptorOptions {
            crosscat_lex_compat_gate: original::forks::CROSSCAT_LEX_COMPAT_GATE,
            prefix_factoring: factoring,
            mixfix_factoring: factoring && original::forks::S1F5_MIXFIX_COHORTS,
            accept_continue: original::forks::S1F5_ACCEPT_CONTINUE,
            recovery_base: original::forks::RECOVERY_BASE,
            max_mixfix_slice: original::infix::GEN1_MAX_SLICE,
        }
    }

    fn id(text: &str) -> Ident {
        Ident::new(text, Span::call_site())
    }
    fn literal(text: &str) -> SyntaxExpr {
        SyntaxExpr::Literal(text.into())
    }
    fn param(text: &str) -> SyntaxExpr {
        SyntaxExpr::Param(id(text))
    }

    fn language() -> LanguageDef {
        let mut language = guest_language();
        language.types.push(LangType {
            name: id("IntList"),
            role: CategoryRole::Object,
            native_type: Some(syn::parse_quote!(Vec<Int>)),
            collection_kind: Some(CollectionCategory::List(CollectionDelimiters {
                open: "[".into(),
                close: "]".into(),
                sep: ",".into(),
                key_val_sep: None,
            })),
        });
        language.terms.push(judgement_rule(
            "WrappedTwin",
            "Expr",
            &[("body", "Expr")],
            vec![literal("x"), param("body"), literal("]")],
        ));
        for (label, ending) in [("MethodA", "a"), ("MethodB", "b")] {
            language.terms.push(judgement_rule(
                label,
                "Expr",
                &[("left", "Expr"), ("arg", "Expr")],
                vec![
                    param("left"),
                    literal("."),
                    literal("("),
                    param("arg"),
                    literal(")"),
                    literal(ending),
                ],
            ));
        }
        language
    }

    fn selected(language: &LanguageDef, occurrences: &[usize]) -> LanguageDef {
        let mut selected = language.clone();
        selected.terms = occurrences
            .iter()
            .map(|&i| language.terms[i].clone())
            .collect();
        selected
    }

    fn assert_complete_parity(language: &LanguageDef, occurrences: &[usize], enabled: bool) {
        let core = core(language);
        let selected = selected(language, occurrences);
        let categories = original::collect_category_names_with_literals(&selected);
        let per_cat = original::synthetic::build_per_category_rules(&selected, &categories);
        let synthesis = derive_authored_rules(&core, occurrences, |_| Ok::<_, Infallible>(()))
            .expect("captured grammar must synthesize through original worker");
        assert_eq!(synthesis.categories, categories);
        let mut correspondence = Vec::new();
        for (owned, source) in synthesis.per_category.iter().zip(&per_cat) {
            assert_eq!(owned.len(), source.len());
            correspondence.extend(owned.iter().copied().zip(source));
        }
        assert_eq!(synthesis.per_category.len(), per_cat.len());
        let cast_calls = Cell::new(0usize);
        let mut actual = derive_authored_descriptors(
            &core,
            occurrences,
            synthesis,
            options(enabled),
            |_, _, _, _| Ok::<_, Infallible>(()),
            |reader, occurrence| {
                cast_calls.set(cast_calls.get() + 1);
                let (_, source) = correspondence
                    .iter()
                    .find(|(payload, _)| *payload == occurrence)
                    .expect("cast query must identify its exact normalized local occurrence");
                assert_eq!(reader.label(occurrence.rule).to_string(), source.label.to_string());
                assert_eq!(
                    reader.category(occurrence.rule).to_string(),
                    source.category.to_string()
                );
                Ok(cast_machinery_participates(&selected, source))
            },
        )
        .expect("complete original descriptor assembly must succeed");
        assert_eq!(actual.original_occurrences, occurrences);
        assert_eq!(actual.synthesis.categories, categories);
        assert_eq!(actual.synthesis.source_order.len(), occurrences.len());
        assert_eq!(actual.structural_delimiters,
            original::collection::collect_structural_delimiters(&selected, &per_cat));
        for (category, first) in categories.iter().zip(&actual.first_sets) {
            let expected = original::prefix::first_set_of_category(category, &selected);
            assert_eq!(
                first.iter().map(|row| (original_quote(&row.pattern).to_string(), row.extra_guard.as_ref().map(|guard| original_quote(guard).to_string()), row.leading_literal.clone(), row.is_var_contribution)).collect::<Vec<_>>(),
                expected.iter().map(|row| (row.pattern.to_string(), row.extra_guard.as_ref().map(ToString::to_string), row.leading_literal.clone(), row.is_var_contribution)).collect::<Vec<_>>(),
                "collection FIRST predicate retains original rows/order for {category}",
            );
        }
        // Independent original kind_dispatch census, retained here as the
        // source oracle after production forwards to the shared reader body.
        let mut projections = Vec::new();
        for (to, rules) in per_cat.iter().enumerate() {
            for (rule_idx, rule) in rules.iter().enumerate() {
                let Some(tc) = rule.term_context.as_ref() else { continue };
                if tc.len() != 1 { continue; }
                let mettail_ast::grammar::TermParam::Simple { name, ty } = &tc[0] else { continue };
                let mettail_ast::types::TypeExpr::Base(source) = ty else { continue };
                let source_name = source.to_string();
                if source_name == rule.category.to_string() { continue; }
                let Some(sp) = rule.syntax_pattern.as_ref() else { continue };
                if !(sp.len() == 1 && matches!(sp.first(), Some(SyntaxExpr::Param(syn_name)) if syn_name == name)) { continue; }
                let Some(from) = categories.iter().position(|category| category == &source_name) else { continue };
                projections.push((from as u16, to as u16, rule_idx as u16));
            }
        }
        assert_eq!(actual.transparent_projections, projections);
        let mut coercions: std::collections::BTreeMap<_, Vec<_>> = std::collections::BTreeMap::new();
        for &(from, to, rule) in &projections {
            if !mettail_ast::grammar::NonTerminalKind::classify(&categories[usize::from(from)]).is_builtin() {
                coercions.entry((from, to)).or_default().push((to, rule));
            }
        }
        assert_eq!(actual.single_hop_coercions, coercions);
        let mut direct = std::collections::BTreeSet::new();
        for rule in &selected.terms {
            if let Some(info) = original::infix::classify_rule_public(rule) {
                if info.is_cross_category && info.category != info.result_category {
                    if let (Some(from), Some(to)) = (
                        categories.iter().position(|cat| cat == &info.category),
                        categories.iter().position(|cat| cat == &info.result_category),
                    ) {
                        if from != to { direct.insert((from as u16, to as u16)); }
                    }
                }
            }
        }
        for &(from, to, _) in &projections {
            if from != to { direct.insert((from, to)); }
        }
        let mut reach = direct.clone();
        loop {
            let mut added = false;
            let snapshot: Vec<_> = reach.iter().copied().collect();
            for &(a, b) in &snapshot {
                for &(c, d) in &snapshot {
                    if b == c && a != d && reach.insert((a, d)) { added = true; }
                }
            }
            if !added { break; }
        }
        assert!(direct.iter().all(|edge| reach.contains(edge)));
        assert_eq!(actual.category_reachability, reach.into_iter().filter(|(a,b)| a != b).collect::<Vec<_>>());
        let ident_var_only: Vec<_> = categories.iter().enumerate().filter_map(|(index, category)| {
            let fs = original::prefix::first_set_of_category(category, &selected);
            (fs.iter().any(|ft| ft.pattern.to_string().contains("Ident") && ft.extra_guard.is_none())
                && original::prefix::source_ident_first_is_var_only(category, &selected)).then_some(index as u16)
        }).collect();
        assert_eq!(actual.projection_ident_var_only_sources, ident_var_only);

        let bp = original::infix::build_bp_table(&selected);
        // These Debug implementations expose every field in ordered vectors;
        // unlike maps, the rendered order is part of the descriptor contract.
        assert_eq!(format!("{:?}", actual.binding_powers), format!("{bp:?}"));
        assert_eq!(actual.label_index, original::infix::build_label_index(&categories, &per_cat));
        assert_eq!(
            actual.prefix_binding_powers,
            original::binder::build_prefix_bp_map(&selected, &per_cat)
        );

        assert_eq!(actual.prefixes.len(), categories.len());
        for (category, actual_bucket) in
            std::mem::take(&mut actual.prefixes).into_iter().enumerate()
        {
            let indexed: Vec<_> = per_cat[category]
                .iter()
                .enumerate()
                .map(|(i, rule)| (u16::try_from(i).expect("bounded rule fixture"), rule))
                .collect();
            let expected = derive_prefix_buckets(
                &original::binder::MacroBinderSyntaxReader,
                &mut MacroFirstSetContext { language: &selected },
                u16::try_from(category).expect("bounded category fixture"),
                &categories[category],
                &indexed,
                options(enabled).crosscat_lex_compat_gate,
            );
            assert_eq!(
                observations(
                    actual_bucket,
                    |p| original_quote(p).to_string(),
                    |p| original_quote(p).to_string()
                ),
                observations(expected, ToString::to_string, Clone::clone),
                "complete prefix bucket category {category}"
            );
        }
        assert_eq!(
            actual.grouping_sources,
            (0..categories.len())
                .map(|category| grouping_source_categories_for_result(
                    &categories,
                    &selected,
                    &per_cat,
                    category
                ))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            actual.traversal_markers,
            original::binder::build_traversal_marker_table(&selected, &per_cat)
        );
        assert!(
            !actual.traversal_markers.optional_metadata.is_empty(),
            "fixture must exercise optional continuation markers"
        );
        assert_eq!(
            actual.collections,
            original::collection::original_collection_descriptors_for_test(
                &selected,
                &categories,
                &per_cat
            )
        );
        assert!(!actual.collections.is_empty(), "fixture must exercise collection slots");

        let prefix = original::factoring::original_prefix_partition_for_test(
            &selected,
            &categories,
            &per_cat,
            enabled,
        );
        let mixfix = if options(enabled).mixfix_factoring {
            original::factoring::build_mixfix_factoring(&selected, &categories, &per_cat, &prefix)
        } else {
            original::factoring::mixfix_identity_partition(&selected, &categories, &per_cat)
        };
        // Full structural Debug traverses all ordered trees and member fields;
        // no group, singleton, refusal, coordinate or weight owner is filtered.
        assert_eq!(format!("{:?}", actual.prefix_partition), format!("{prefix:?}"));
        assert_eq!(format!("{:?}", actual.mixfix_partition), format!("{mixfix:?}"));
        let emission = original::factoring::build_spine_emission_from_parts(
            &prefix,
            &mixfix,
            &selected,
            &categories,
            &per_cat,
        );
        assert_eq!(actual.factoring_emission.dispositions, emission.dispositions);
        assert_eq!(actual.factoring_emission.group_members, emission.group_members);
        assert_eq!(actual.factoring_emission.lex_alt, emission.lex_alt);
        assert_eq!(actual.factoring_emission.mixfix_groups, emission.mixfix_groups);
        assert!(emission.refusals.is_empty(), "valid fixture must not hide emitter refusal");
        if enabled {
            assert!(
                cast_calls.get() > 0,
                "enabled factoring must consult actual source cast helper"
            );
            assert!(
                prefix
                    .iter()
                    .flat_map(|category| &category.buckets)
                    .any(|bucket| !bucket.groups.is_empty()),
                "fixture must exercise prefix factoring"
            );
            assert!(
                mixfix
                    .iter()
                    .flat_map(|category| &category.buckets)
                    .any(|bucket| !bucket.groups.is_empty()),
                "fixture must exercise mixfix factoring"
            );
        } else {
            assert_eq!(cast_calls.get(), 0, "disabled original partitions do not call cast helper");
        }

        let parikh = build_parikh_descriptors(
            &original::binder::MacroBinderSyntaxReader,
            &selected.terms,
            &categories,
            &per_cat,
            original::infix::classify_rule_public,
        );
        assert_eq!(actual.parikh.alphabet.trigger_bit, parikh.alphabet.trigger_bit);
        assert_eq!(actual.parikh.alphabet.coarse_bit, parikh.alphabet.coarse_bit);
        assert_eq!(actual.parikh.must_entries, parikh.must_entries);
    }

    #[test]
    fn complete_owned_descriptor_artifact_matches_original_macro_workers() {
        let language = language();
        let occurrences: Vec<_> = (0..language.terms.len()).collect();
        for enabled in [false, original::forks::S1_FACTORING] {
            assert_complete_parity(&language, &occurrences, enabled);
        }
    }

    #[test]
    fn complete_owned_descriptor_artifact_preserves_reordered_duplicate_occurrences() {
        let language = language();
        let mut occurrences: Vec<_> = (0..language.terms.len()).rev().collect();
        occurrences.insert(3, 0);
        for enabled in [false, original::forks::S1_FACTORING] {
            assert_complete_parity(&language, &occurrences, enabled);
        }
    }

    #[test]
    fn complete_descriptor_admission_and_cast_refusals_never_publish_artifacts() {
        let language = language();
        let core = core(&language);
        let occurrences: Vec<_> = (0..language.terms.len()).collect();
        let synthesis = derive_authored_rules(&core, &occurrences, |_| Ok::<_, Infallible>(()))
            .expect("valid synthesis for admission refusal");
        let cast_calls = Cell::new(0);
        let denied = derive_authored_descriptors(
            &core,
            &[usize::MAX],
            synthesis,
            options(true),
            |_, _, _, _| Err("admission"),
            |_, _| {
                cast_calls.set(cast_calls.get() + 1);
                panic!("admission refusal must precede every cast observation")
            },
        );
        assert!(matches!(denied, Err(AuthoredDescriptorsError::Admission("admission"))));
        assert_eq!(cast_calls.get(), 0);

        let synthesis = derive_authored_rules(&core, &occurrences, |_| Ok::<_, Infallible>(()))
            .expect("valid synthesis for cast refusal");
        let categories = original::collect_category_names_with_literals(&language);
        let per_cat = original::synthetic::build_per_category_rules(&language, &categories);
        let correspondence: Vec<_> = synthesis
            .per_category
            .iter()
            .zip(&per_cat)
            .flat_map(|(owned, source)| owned.iter().copied().zip(source))
            .collect();
        let refused = derive_authored_descriptors(
            &core,
            &occurrences,
            synthesis,
            options(true),
            |_, _, _, _| Ok(()),
            |_, occurrence| {
                cast_calls.set(cast_calls.get() + 1);
                let (_, source) = correspondence
                    .iter()
                    .find(|(payload, _)| *payload == occurrence)
                    .expect("exact normalized cast occurrence");
                let _source_result = cast_machinery_participates(&language, source);
                Err("source cast evidence refused")
            },
        );
        assert!(matches!(
            refused,
            Err(AuthoredDescriptorsError::Cast("source cast evidence refused"))
        ));
        assert_eq!(cast_calls.get(), 1, "no cast query after first refusal");
    }

    #[test]
    fn complete_descriptor_position_bound_fails_before_cast_callbacks() {
        let mut language = guest_language();
        language.terms.push(judgement_rule(
            "WideLiteralRun",
            "Expr",
            &[],
            (0..257).map(|_| literal("wide")).collect(),
        ));
        let core = core(&language);
        let occurrences: Vec<_> = (0..language.terms.len()).collect();
        let synthesis = derive_authored_rules(&core, &occurrences, |_| Ok::<_, Infallible>(()))
            .expect("position-width admission belongs to descriptor consumer");
        let result = derive_authored_descriptors(
            &core,
            &occurrences,
            synthesis,
            options(false),
            |_, _, _, _| Ok::<_, Infallible>(()),
            |_, _| panic!("position admission must precede cast observation"),
        );
        assert!(matches!(
            result,
            Err(AuthoredDescriptorsError::PositionIndexOverflow { positions: 257, .. })
        ));
    }
}
