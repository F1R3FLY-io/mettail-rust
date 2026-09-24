mod owned_prefix_reuse {
    use super::*;
    use mettail_ast::grammar::PatternOp;
    use mettail_prattail::wpda_rule_analysis::atomic_prefix::UnifiedDescriptor as D;
    use mettail_prattail::wpda_rule_analysis::authored_prefix::{
        derive_authored_prefix_buckets, AuthoredPrefixError,
    };
    use mettail_prattail::wpda_rule_analysis::authored_synthesis::derive_authored_rules;
    use mettail_prattail::wpda_rule_analysis::native_first::{
        NativeFirstConstructors, NativePatternSite,
    };
    use mettail_prattail::wpda_rule_analysis::prefix::FirstPredicate as F;
    use mettail_prattail::wpda_rule_analysis::prefix_bucket::{
        derive_prefix_buckets, PrefixBuckets,
    };
    use mettail_prattail::wpda_rule_analysis::prefix_pattern::NeutralPattern as N;
    use std::convert::Infallible;

    // Test-only association to the ORIGINAL constructors. This does not parse
    // generated tokens or introduce quotation into the owned implementation.
    pub(super) fn original_quote(pattern: &N) -> TokenStream {
        match pattern {
            N::Empty => TokenStream::new(),
            N::FixedKeyword => first_predicate_parts(F::Fixed("")).0,
            N::Ident => first_predicate_parts(F::Ident).0,
            N::Integer => first_predicate_parts(F::Integer).0,
            N::BooleanAlternative => first_predicate_parts(F::Boolean).0,
            N::StringLiteral => first_predicate_parts(F::String).0,
            N::Float => first_predicate_parts(F::Float).0,
            N::Capture => first_predicate_parts(F::CaptureName("")).0,
            N::GuestCustomRef => first_predicate_parts(F::GuestOpen("")).0,
            N::IntegerTyped => {
                MacroNativeFirstConstructors.pattern(NativePatternSite::IntegerTyped)
            },
            N::CustomTyped => MacroNativeFirstConstructors.pattern(NativePatternSite::CustomTyped),
            N::RationalTyped => {
                MacroNativeFirstConstructors.pattern(NativePatternSite::RationalTyped)
            },
            N::FixedPointTyped => {
                MacroNativeFirstConstructors.pattern(NativePatternSite::FixedPointTyped)
            },
            N::FixedText(text) => first_predicate_parts(F::Fixed(text))
                .1
                .expect("fixed quotation has a guard"),
            N::CaptureName(text) => first_predicate_parts(F::CaptureName(text))
                .1
                .expect("capture quotation has a guard"),
            N::GuestName(text) => first_predicate_parts(F::GuestOpen(text))
                .1
                .expect("guest quotation has a guard"),
            N::CategoryName(text) => MacroNativeFirstConstructors.category_guard(text),
        }
    }

    #[derive(Debug, PartialEq, Eq)]
    pub(super) enum Descriptor {
        CrossLhs(u16, bool),
        Atomic(String, Option<String>, u16, u16),
        Binder(u16, u16),
        LeadingCategory(u16, u16),
        Capture(u16, u16, String),
        Guest(u16, u16, String, Vec<String>, String),
        Unary(u16, u16, u8),
        Projection(u16, u16),
        Nullary(u16),
    }

    fn descriptor<P>(value: D<P>, render: &impl Fn(&P) -> String) -> Descriptor {
        match value {
            D::CrossCatLhs { source_src_idx, sigil_leads_result_rule } => {
                Descriptor::CrossLhs(source_src_idx, sigil_leads_result_rule)
            },
            D::Atomic(row) => Descriptor::Atomic(
                render(&row.pattern),
                row.extra_guard.as_ref().map(render),
                row.rule_idx,
                row.category_src_idx,
            ),
            D::BinderPrefix { rule_idx, body_src_idx } => {
                Descriptor::Binder(rule_idx, body_src_idx)
            },
            D::LeadingCategory { rule_idx, source_src_idx } => {
                Descriptor::LeadingCategory(rule_idx, source_src_idx)
            },
            D::LeadingTokenKindCapture { rule_idx, body_src_idx, kind_name } => {
                Descriptor::Capture(rule_idx, body_src_idx, kind_name)
            },
            D::LeadingGuestBody {
                rule_idx,
                body_src_idx,
                open_kind,
                nested_open_kinds,
                close_kind,
            } => {
                Descriptor::Guest(rule_idx, body_src_idx, open_kind, nested_open_kinds, close_kind)
            },
            D::CrossCatPrefixUnary { rule_idx, source_src_idx, operand_bp } => {
                Descriptor::Unary(rule_idx, source_src_idx, operand_bp)
            },
            D::CrossCatProjection { rule_idx, source_src_idx } => {
                Descriptor::Projection(rule_idx, source_src_idx)
            },
            D::NullaryLiteralRun { rule_idx } => Descriptor::Nullary(rule_idx),
        }
    }

    pub(super) type Bucket = ((String, String), String, Option<String>, Vec<Descriptor>);

    pub(super) fn observations<P, K: Ord>(
        (mut buckets, order): PrefixBuckets<P, K>,
        render: impl Fn(&P) -> String,
        key: impl Fn(&K) -> String,
    ) -> Vec<Bucket> {
        let result = order
            .into_iter()
            .map(|row_key| {
                let row = buckets
                    .remove(&row_key)
                    .expect("one bucket per insertion-order entry");
                (
                    (key(&row_key.0), key(&row_key.1)),
                    render(&row.pat),
                    row.extra_guard.as_ref().map(&render),
                    row.descs
                        .into_iter()
                        .map(|value| descriptor(value, &render))
                        .collect(),
                )
            })
            .collect();
        assert!(buckets.is_empty(), "no bucket may be missing from insertion order");
        result
    }

    pub(super) fn core(language: &LanguageDef) -> mettail_grammar_core::GrammarCoreV1 {
        crate::gen::syntax::parser::prattail_bridge::language_def_to_spec(language)
            .expect("original macro bridge accepts fixture")
            .to_grammar_core()
            .expect("capture through the existing Core bridge")
    }

    fn assert_parity(language: &LanguageDef, occurrences: &[usize]) -> Vec<Bucket> {
        let core = core(language);
        let synthesis = derive_authored_rules(&core, occurrences, |_| Ok::<_, Infallible>(()))
            .expect("reuse original owned synthesis");
        let mut selected = language.clone();
        selected.terms = occurrences
            .iter()
            .map(|&index| language.terms[index].clone())
            .collect();
        let categories =
            crate::gen::runtime::wpda_codegen::collect_category_names_with_literals(&selected);
        assert_eq!(synthesis.categories, categories);
        let per_category = crate::gen::runtime::wpda_codegen::synthetic::build_per_category_rules(
            &selected,
            &categories,
        );
        let mut complete = Vec::new();
        for gate in [false, true] {
            for (category, rules) in per_category.iter().enumerate() {
                let indexed: Vec<_> = rules
                    .iter()
                    .enumerate()
                    .map(|(index, rule)| {
                        (u16::try_from(index).expect("fixture rule index fits u16"), rule)
                    })
                    .collect();
                let expected = derive_prefix_buckets(
                    &crate::gen::runtime::wpda_codegen::binder::MacroBinderSyntaxReader,
                    &mut MacroFirstSetContext { language: &selected },
                    u16::try_from(category).expect("fixture category fits u16"),
                    &categories[category],
                    &indexed,
                    gate,
                );
                let actual = derive_authored_prefix_buckets(
                    &core,
                    occurrences,
                    &synthesis,
                    u16::try_from(category).expect("fixture category fits u16"),
                    gate,
                    |_, _, _, _| Ok::<_, Infallible>(()),
                )
                .expect("owned context produces complete buckets");
                let expected = observations(expected, ToString::to_string, Clone::clone);
                let actual = observations(
                    actual,
                    |p| original_quote(p).to_string(),
                    |p| original_quote(p).to_string(),
                );
                assert_eq!(
                    actual, expected,
                    "category {}, lexical gate {gate}",
                    categories[category]
                );
                complete.extend(actual);
            }
        }
        complete
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

    pub(super) fn mixed_language() -> LanguageDef {
        let mut language = lang_with_int_literal();
        language.types.push(LangType {
            name: id("Expr"),
            role: CategoryRole::Object,
            native_type: None,
            collection_kind: None,
        });
        let mut add = judgement_rule(
            "Add",
            "Int",
            &[("left", "Int"), ("right", "Int")],
            vec![param("left"), literal("+"), param("right")],
        );
        add.is_right_assoc = true;
        let mut mul = judgement_rule(
            "Mul",
            "Int",
            &[("left", "Int"), ("right", "Int")],
            vec![param("left"), literal("*"), param("right")],
        );
        mul.shares_level_with_previous = true;
        language.terms = vec![
            terminal_rule("HomeX", "Expr", "x"),
            terminal_rule("IntX", "Int", "x"),
            judgement_rule(
                "Cross",
                "Expr",
                &[("left", "Int"), ("right", "Int")],
                vec![param("left"), literal("<"), param("right")],
            ),
            add,
            judgement_rule(
                "Wrapped",
                "Expr",
                &[("body", "Expr")],
                vec![literal("x"), param("body"), literal(")")],
            ),
            mul,
            judgement_rule("Project", "Expr", &[("body", "Int")], vec![param("body")]),
            judgement_rule(
                "UnaryCross",
                "Expr",
                &[("body", "Int")],
                vec![literal("int"), param("body")],
            ),
            judgement_rule("Nullary", "Expr", &[], vec![literal("done"), literal("now")]),
        ];
        language
    }

    #[test]
    fn owned_prefix_complete_mixed_native_crosscategory_buckets_match_original() {
        let language = mixed_language();
        let rows = assert_parity(&language, &(0..language.terms.len()).collect::<Vec<_>>());
        let descriptors: Vec<_> = rows.iter().flat_map(|row| &row.3).collect();
        assert!(descriptors
            .iter()
            .any(|d| matches!(d, Descriptor::CrossLhs(..))));
        assert!(descriptors
            .iter()
            .any(|d| matches!(d, Descriptor::Binder(..))));
        assert!(descriptors
            .iter()
            .any(|d| matches!(d, Descriptor::Atomic(..))));
        assert!(descriptors
            .iter()
            .any(|d| matches!(d, Descriptor::Projection(..))));
        assert!(descriptors
            .iter()
            .any(|d| matches!(d, Descriptor::Unary(..))));
        assert!(descriptors
            .iter()
            .any(|d| matches!(d, Descriptor::Nullary(..))));
    }

    #[test]
    fn owned_prefix_explicit_reordered_duplicate_occurrences_match_original() {
        let language = mixed_language();
        // Reuse one source production twice; global ordinal, production identity
        // and local synthesized index must not be conflated.
        assert_parity(&language, &[6, 1, 0, 3, 4, 5, 2, 0, 7, 8]);
    }

    pub(super) fn guest_language() -> LanguageDef {
        use crate::gen::runtime::wpda_codegen::guest_mode_descriptor_baselines as guests;
        let mut language = mixed_language();
        let mut open = guests::token("GuestOpen", Some("Guest"));
        open.pattern = "`".into();
        let mut close = guests::token("GuestClose", None);
        close.pattern = "`".into();
        close.is_pop = true;
        let mut nested_z = guests::token("NestedZ", Some("Guest"));
        nested_z.pattern = "z".into();
        let mut nested_a = guests::token("NestedA", Some("Guest"));
        nested_a.pattern = "a".into();
        language.token_defs.push(open);
        language
            .mode_defs
            .push(guests::mode("Guest", vec![nested_z, nested_a, close]));
        language.terms.push(judgement_rule(
            "GuestRegion",
            "Expr",
            &[],
            vec![SyntaxExpr::GuestBody {
                open: id("GuestOpen"),
                close: id("GuestClose"),
                bind: id("guest"),
                kind: DelimitedRegionKind::Flt,
            }],
        ));
        language.terms.push(judgement_rule(
            "Capture",
            "Expr",
            &[],
            vec![SyntaxExpr::TokenKind {
                name: id("Ident"),
                bind: Some(id("name")),
            }],
        ));
        let mut optional = judgement_rule(
            "Optional",
            "Expr",
            &[],
            vec![
                literal("opt"),
                SyntaxExpr::Op(PatternOp::Opt {
                    inner: vec![literal("with"), param("body")],
                }),
                literal("end"),
            ],
        );
        optional.term_context = Some(vec![TermParam::Optional {
            params: vec![TermParam::Simple {
                name: id("body"),
                ty: TypeExpr::Base(id("Expr")),
            }],
        }]);
        language.terms.push(optional);
        language
    }

    #[test]
    fn owned_prefix_guest_capture_and_optional_shapes_match_original() {
        let language = guest_language();
        let rows = assert_parity(&language, &(0..language.terms.len()).collect::<Vec<_>>());
        assert!(rows.iter().flat_map(|row| &row.3).any(|d| matches!(d, Descriptor::Guest(_, _, open, nested, close) if open == "GuestOpen" && nested == &vec!["NestedZ".to_string(), "NestedA".to_string()] && close == "GuestClose")));
        assert!(rows
            .iter()
            .flat_map(|row| &row.3)
            .any(|d| matches!(d, Descriptor::Capture(_, _, name) if name == "Ident")));
    }

    #[test]
    fn owned_prefix_admission_and_roster_errors_do_not_publish_buckets() {
        let language = mixed_language();
        let core = core(&language);
        let occurrences: Vec<_> = (0..language.terms.len()).collect();
        let mut synthesis = derive_authored_rules(&core, &occurrences, |_| Ok::<_, Infallible>(()))
            .expect("synthesize valid source before corruption");
        let calls = std::cell::Cell::new(0);
        let result = derive_authored_prefix_buckets(
            &core,
            &[usize::MAX],
            &synthesis,
            u16::MAX,
            false,
            |_, _, _, _| {
                calls.set(calls.get() + 1);
                Err("denied")
            },
        );
        assert!(matches!(result, Err(AuthoredPrefixError::Admission("denied"))));
        assert_eq!(calls.get(), 1);
        synthesis.source_order.swap(0, 1);
        assert!(matches!(
            derive_authored_prefix_buckets(
                &core,
                &occurrences,
                &synthesis,
                0,
                false,
                |_, _, _, _| Ok::<_, Infallible>(())
            ),
            Err(AuthoredPrefixError::SourceRosterMismatch(0))
        ));
        synthesis.source_order.swap(0, 1);
        synthesis.categories.push("NotInOriginalCensus".into());
        synthesis.per_category.push(Vec::new());
        assert!(matches!(
            derive_authored_prefix_buckets(
                &core,
                &occurrences,
                &synthesis,
                0,
                false,
                |_, _, _, _| Ok::<_, Infallible>(())
            ),
            Err(AuthoredPrefixError::CategoryRosterMismatch)
        ));
    }

    #[test]
    fn owned_prefix_out_of_range_explicit_binding_power_is_not_nonatomic() {
        let language = mixed_language();
        let mut core = core(&language);
        let occurrences: Vec<_> = (0..language.terms.len()).collect();
        core.productions[7].precedence.binding_power = Some(256);
        let synthesis = derive_authored_rules(&core, &occurrences, |_| Ok::<_, Infallible>(()))
            .expect("synthesis does not consume prefix binding power");
        let category = u16::try_from(
            synthesis
                .categories
                .iter()
                .position(|name| name == "Expr")
                .expect("fixture declares Expr"),
        )
        .expect("Expr category fits u16");
        assert!(matches!(
            derive_authored_prefix_buckets(
                &core,
                &occurrences,
                &synthesis,
                category,
                false,
                |_, _, _, _| Ok::<_, Infallible>(())
            ),
            Err(AuthoredPrefixError::PrefixBindingPowerOverflow(256))
        ));
    }

    #[test]
    fn owned_prefix_missing_literal_observation_remains_a_typed_error() {
        use mettail_grammar_core::{AuthoredRuleStore, SourceObservation};
        use mettail_prattail::wpda_rule_analysis::authored_atomic::AuthoredAtomicError;
        use mettail_prattail::wpda_rule_analysis::authored_prefix::LiteralError;

        fn without_byte_observation(store: &AuthoredRuleStore) -> AuthoredRuleStore {
            let mut changed = AuthoredRuleStore::new();
            for index in 0..store.len() {
                let index = u32::try_from(index).expect("validated arena index fits u32");
                assert_eq!(
                    changed
                        .try_push(store.get(index).expect("existing source node").clone())
                        .expect("preserve validated node order"),
                    index
                );
            }
            let mut header = store
                .declarations()
                .expect("captured declaration header")
                .clone();
            header.categories[0].byte_observation = SourceObservation::Unavailable;
            changed
                .with_declarations(header)
                .expect("missing observation remains structurally valid")
        }

        let language = mixed_language();
        let mut core = core(&language);
        let occurrences: Vec<_> = (0..language.terms.len()).collect();
        let mut synthesis = derive_authored_rules(&core, &occurrences, |_| Ok::<_, Infallible>(()))
            .expect("synthesize before removing literal observation");
        // Change both matching stores only AFTER original synthesis. This
        // exercises prefix literal resolution, not synthesis label admission,
        // and leaves the entrypoint's exact source-store checks enabled.
        core.authored =
            Some(without_byte_observation(core.authored.as_ref().expect("captured source store")));
        synthesis.store = without_byte_observation(&synthesis.store);
        let category = u16::try_from(
            synthesis
                .categories
                .iter()
                .position(|name| name == "Int")
                .expect("fixture declares Int"),
        )
        .expect("Int category fits u16");
        assert!(matches!(
            derive_authored_prefix_buckets(
                &core,
                &occurrences,
                &synthesis,
                category,
                false,
                |_, _, _, _| Ok::<_, Infallible>(())
            ),
            Err(AuthoredPrefixError::Atomic(AuthoredAtomicError::Literal(
                LiteralError::UnavailableByteObservation
            )))
        ));
    }
}
