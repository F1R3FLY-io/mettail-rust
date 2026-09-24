mod owned_synthesis_reuse {
    use super::*;
    use mettail_grammar_core::{AuthoredNode, AuthoredRuleStore};
    use mettail_prattail::wpda_rule_analysis::authored_synthesis::{
        derive_authored_rules, AuthoredRuleOrigin,
    };
    use std::collections::{BTreeMap, BTreeSet};
    use std::convert::Infallible;

    // Compare complete retained shapes through the existing immediate-field
    // mapper. Arena indices may differ; source name equivalence must remain
    // bijective across every compared rule. The test walker is iterative and
    // memoizes node pairs only, never parser candidates or production rows.
    fn assert_same_shape(
        expected: &AuthoredRuleStore,
        expected_root: u32,
        actual: &AuthoredRuleStore,
        actual_root: u32,
        classes: &mut (BTreeMap<u32, u32>, BTreeMap<u32, u32>),
    ) {
        let mut work = vec![(expected_root, actual_root)];
        let mut seen = BTreeSet::new();
        while let Some((left_id, right_id)) = work.pop() {
            if !seen.insert((left_id, right_id)) {
                continue;
            }
            let left = expected.get(left_id).expect("captured static node");
            let right = actual.get(right_id).expect("derived owned node");
            if let (AuthoredNode::Name(left), AuthoredNode::Name(right)) = (left, right) {
                for (map, key, value) in [
                    (&mut classes.0, left.equality_class, right.equality_class),
                    (&mut classes.1, right.equality_class, left.equality_class),
                ] {
                    if let Some(previous) = map.insert(key, value) {
                        assert_eq!(previous, value, "source name equivalence changed");
                    }
                }
            }
            let mut left_edges = Vec::new();
            let mut right_edges = Vec::new();
            let erase = |node: &AuthoredNode, edges: &mut Vec<_>| {
                node.clone()
                    .try_map_observations(
                        |tag, id| {
                            edges.push((tag, id));
                            Ok::<_, Infallible>(0u32)
                        },
                        |_| Ok(0u32),
                    )
                    .expect("test field mapping is infallible")
            };
            assert_eq!(erase(left, &mut left_edges), erase(right, &mut right_edges));
            assert_eq!(left_edges.len(), right_edges.len());
            for ((left_tag, left), (right_tag, right)) in
                left_edges.into_iter().zip(right_edges).rev()
            {
                assert_eq!(left_tag, right_tag);
                work.push((left, right));
            }
        }
    }

    fn assert_original_and_owned(language: &LanguageDef) {
        let core = crate::gen::syntax::parser::prattail_bridge::language_def_to_spec(language)
            .expect("existing static bridge accepts source fixture")
            .to_grammar_core()
            .expect("existing bridge produces valid grammar core");
        // The bridge retains source terms first and then appends auxiliary
        // collection productions. Select the actual source roster explicitly;
        // do not infer it by filtering missing authored handles.
        let occurrences: Vec<_> = (0..language.terms.len()).collect();
        let output = derive_authored_rules(&core, &occurrences, |_| Ok::<_, Infallible>(()))
            .expect("original owned synthesis succeeds");
        if core.productions.len() > occurrences.len() {
            let including_auxiliaries: Vec<_> = (0..core.productions.len()).collect();
            assert!(
                derive_authored_rules(&core, &including_auxiliaries, |_| Ok::<_, Infallible>(()))
                    .is_err(),
                "auxiliary productions without authored rules must not be silently filtered"
            );
        }
        let categories =
            crate::gen::runtime::wpda_codegen::collect_category_names_with_literals(language);
        assert_eq!(output.categories, categories);
        let original = build_per_category_rules(language, &categories);
        assert_eq!(output.per_category.len(), original.len());
        let flat: Vec<_> = original.iter().flatten().cloned().collect();
        let captured = crate::gen::runtime::wpda_codegen::authored_capture::capture_rules(&flat)
            .expect("capture original macro-derived rules without reconstruction");
        let mut expected_roots = captured.roots.into_iter();
        let mut classes = (BTreeMap::new(), BTreeMap::new());
        for (category, (expected_rows, actual_rows)) in
            original.iter().zip(&output.per_category).enumerate()
        {
            assert_eq!(actual_rows.len(), expected_rows.len(), "{}", categories[category]);
            let source_positions: Vec<_> = language
                .terms
                .iter()
                .enumerate()
                .filter(|(_, rule)| rule.category.to_string() == categories[category])
                .map(|(index, _)| index)
                .collect();
            for (local, payload) in actual_rows.iter().enumerate() {
                assert_same_shape(
                    &captured.store,
                    expected_roots.next().expect("one captured root per rule"),
                    &output.store,
                    payload.rule.0,
                    &mut classes,
                );
                let expected_origin = source_positions
                    .get(local)
                    .map_or(AuthoredRuleOrigin::Synthetic, |index| AuthoredRuleOrigin::User {
                        production_index: *index,
                    });
                assert_eq!(
                    payload.origin, expected_origin,
                    "source occurrence is not a local rule index"
                );
            }
        }
        assert!(expected_roots.next().is_none());
        let source = core
            .authored
            .as_ref()
            .expect("bridge retained source arena");
        for index in 0..source.len() {
            let index = u32::try_from(index).expect("fixture index fits");
            assert_eq!(source.get(index), output.store.get(index), "original arena prefix changed");
        }
        assert_eq!(source.declarations(), output.store.declarations());
    }

    #[test]
    fn owned_synthesis_matches_original_native_and_collection_rules() {
        let mut language = lang_with_int_and_bool_literals();
        assert_original_and_owned(&language);
        language.types.push(synthesis_baseline_collection("seq("));
        language.terms = vec![
            synthesis_baseline_user("BoolFirst", "Bool"),
            synthesis_baseline_user("IntFirst", "Int"),
            synthesis_baseline_user("SeqFirst", "Seq"),
            synthesis_baseline_user("IntSecond", "Int"),
        ];
        assert_original_and_owned(&language);
        language.token_defs.clear();
        assert_original_and_owned(&language);
    }

    #[test]
    fn owned_synthesis_matches_original_cross_category_binder_families() {
        let mut language = synthesis_baseline_binder_language();
        assert_original_and_owned(&language);
        language.types.push(synthesis_baseline_collection("["));
        assert_original_and_owned(&language);
        language.types[1].role = CategoryRole::Data;
        assert_original_and_owned(&language);
    }

    #[test]
    fn owned_synthesis_matches_original_five_collection_kinds() {
        for kind in 0..5 {
            let mut language = lang_with_int_and_bool_literals();
            let mut collection = synthesis_baseline_collection("[");
            let delimiters = CollectionDelimiters {
                open: "[".into(),
                close: "]".into(),
                sep: ";".into(),
                key_val_sep: Some(":".into()),
            };
            let (native, declared) = match kind {
                0 => (parse_quote!(Vec<Int>), CollectionCategory::List(delimiters)),
                1 => (parse_quote!(HashBag<Int>), CollectionCategory::Bag(delimiters)),
                2 => (parse_quote!(HashMap<Int, Bool>), CollectionCategory::Map(delimiters)),
                3 => (parse_quote!(HashSetLit<Int>), CollectionCategory::Set(delimiters)),
                _ => (parse_quote!(PathMapLit<Int, Bool>), CollectionCategory::Pathmap(delimiters)),
            };
            collection.native_type = Some(native);
            collection.collection_kind = Some(declared);
            language.types.push(collection);
            assert_original_and_owned(&language);
        }
    }

    #[test]
    fn owned_synthesis_matches_original_explicit_var_suppression() {
        let mut language = lang_with_int_and_bool_literals();
        language.terms.push(GrammarRule {
            items: vec![GrammarItem::NonTerminal {
                ident: synthesis_baseline_ident("Int"),
                kind: NonTerminalKind::Var,
            }],
            ..rule_fixture(synthesis_baseline_ident("ExplicitVar"), synthesis_baseline_ident("Int"))
        });
        assert_original_and_owned(&language);
    }
}
