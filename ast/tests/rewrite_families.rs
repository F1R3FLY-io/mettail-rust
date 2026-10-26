use mettail_ast::grammar::{GrammarItem, NonTerminalKind, TermParam};
use mettail_ast::identity::{language_definition_fingerprint, premises_identity, rewrite_identity};
use mettail_ast::language::{
    parse_rewrite_fragment, BehavioralPred, FreshnessCondition, FreshnessTarget, LanguageDef,
    PredArg, Premise, Quantifier, RuleContextType,
};
use mettail_ast::rewrite_family::normalize_rewrite_families;
use proptest::prelude::*;

fn ident(name: &str) -> syn::Ident {
    syn::parse_str(name).unwrap()
}

fn language(types: &str, terms: &str, rewrites: &str) -> LanguageDef {
    let source = format!(
        "name: FamilyTest, types {{ {types} }}, terms {{ {terms} }}, rewrites {{ {rewrites} }}"
    );
    syn::parse_str(&source)
        .unwrap_or_else(|failure| panic!("{failure} at {:?}\n{source}", failure.span()))
}

const TERMS: &str = "
    Zero . |- \"zero\" : Proc;
    New . ^x.p:[Name -> Proc] |- \"new\" x \"in\" p : Proc;
    Many . ^[xs].p:[Name* -> Proc] |- \"many\" xs \"in\" p : Proc;
    Pair . a:Proc, b:Proc |- a \"|\" b : Proc;
    Wrap . p:Proc |- \"wrap\" p : Proc;
";

fn basic(rewrites: &str) -> LanguageDef {
    language("Name; Proc", TERMS, rewrites)
}

fn ordinary(source: &str) -> String {
    rewrite_identity(&parse_rewrite_fragment(source).unwrap().remove(0))
}

fn assert_refuses_atomically(mut source: LanguageDef, diagnostic: &str) {
    let before = language_definition_fingerprint(&source);
    let failure = normalize_rewrite_families(&mut source)
        .unwrap_err()
        .to_string();
    assert!(failure.contains(diagnostic), "{failure}");
    assert_eq!(language_definition_fingerprint(&source), before);
}

#[test]
fn binder_family_matches_the_existing_ordinary_transition_rule() {
    let mut source =
        basic("Body . f:[Name -> Rewrite(Proc)] |- (New ^x.(s (f x))) ~> (New ^x.(t (f x)));");
    normalize_rewrite_families(&mut source).unwrap();
    assert_eq!(rewrite_identity(&source.rewrites[0]), ordinary("Body . __mettail_rewrite_0:Proc, | __mettail_rewrite_0 ~> __mettail_rewrite_1 |- (New ^x.__mettail_rewrite_0) ~> (New ^x.__mettail_rewrite_1);"));
    let once = language_definition_fingerprint(&source);
    normalize_rewrite_families(&mut source).unwrap();
    assert_eq!(language_definition_fingerprint(&source), once);
}

proptest! {
    #[test]
    fn arbitrary_categories_and_nested_contexts_retain_exact_semantics(
        tag in 0u16..1000, depth in 0usize..16, reserved in 0usize..12,
    ) {
        let category = format!("Term{tag}");
        let constructor = format!("Context{tag}");
        let mut terms = format!("{constructor} . body:{category} |- \"context\" body : {category};");
        for index in 0..reserved {
            terms.push_str(&format!("__mettail_rewrite_{index} . |- \"r{index}\" : {category};"));
        }
        let mut left = "(s f)".to_owned();
        let mut right = "(t f)".to_owned();
        let mut expected_left = format!("__mettail_rewrite_{reserved}");
        let mut expected_right = format!("__mettail_rewrite_{}", reserved + 1);
        for _ in 0..depth {
            left = format!("({constructor} {left})");
            right = format!("({constructor} {right})");
            expected_left = format!("({constructor} {expected_left})");
            expected_right = format!("({constructor} {expected_right})");
        }
        let mut source = language(&category, &terms, &format!("Step . f:Rewrite({category}) |- {left} ~> {right};"));
        normalize_rewrite_families(&mut source).unwrap();
        let expected = ordinary(&format!("Step . __mettail_rewrite_{reserved}:{category}, | __mettail_rewrite_{reserved} ~> __mettail_rewrite_{} |- {expected_left} ~> {expected_right};", reserved + 1));
        prop_assert_eq!(rewrite_identity(&source.rewrites[0]), expected);
    }

    #[test]
    fn declaration_order_and_original_occurrence_numbers_survive_projection_erasure(count in 1usize..20) {
        let params = (0..count).map(|i| format!("p{i}:Proc")).collect::<Vec<_>>().join(",");
        let syntax = (0..count).map(|i| format!("p{i}")).collect::<Vec<_>>().join(" ");
        let terms = format!("Wide . {params} |- {syntax} : Proc;");
        let declarations = (0..count).map(|i| format!("f{i}:Rewrite(Proc)")).collect::<Vec<_>>().join(",");
        let left = (0..count).rev().map(|i| format!("(s f{i})")).collect::<Vec<_>>().join(" ");
        let right = (0..count).rev().map(|i| format!("(t f{i})")).collect::<Vec<_>>().join(" ");
        let mut source = language("Proc", &terms, &format!("Step . {declarations} |- (Wide {left}) ~> (Wide {right});"));
        normalize_rewrite_families(&mut source).unwrap();
        let inputs = (0..count).map(|i| format!("__mettail_rewrite_{}:Proc", 2*i)).collect::<Vec<_>>().join(",");
        let premises = (0..count).map(|i| format!("__mettail_rewrite_{} ~> __mettail_rewrite_{}", 2*i, 2*i+1)).collect::<Vec<_>>().join(",");
        let left = (0..count).rev().map(|i| format!("__mettail_rewrite_{}", 2*i)).collect::<Vec<_>>().join(" ");
        let right = (0..count).rev().map(|i| format!("__mettail_rewrite_{}", 2*i+1)).collect::<Vec<_>>().join(" ");
        prop_assert_eq!(rewrite_identity(&source.rewrites[0]), ordinary(&format!("Step . {inputs}, | {premises} |- (Wide {left}) ~> (Wide {right});")));
    }

    #[test]
    fn every_introduced_binder_is_preserved_in_nested_contexts(depth in 1usize..16) {
        let mut family = "Rewrite(Proc)".to_owned();
        for _ in 0..depth { family = format!("[Name -> {family}]"); }
        let args = (0..depth).map(|i| format!("x{i}")).collect::<Vec<_>>().join(" ");
        let mut left = format!("(s (f {args}))");
        let mut right = format!("(t (f {args}))");
        let mut expected_left = "__mettail_rewrite_0".to_owned();
        let mut expected_right = "__mettail_rewrite_1".to_owned();
        for i in (0..depth).rev() {
            left = format!("(New ^x{i}.{left})");
            right = format!("(New ^x{i}.{right})");
            expected_left = format!("(New ^x{i}.{expected_left})");
            expected_right = format!("(New ^x{i}.{expected_right})");
        }
        let mut source = basic(&format!("Step . f:{family} |- {left} ~> {right};"));
        normalize_rewrite_families(&mut source).unwrap();
        prop_assert_eq!(rewrite_identity(&source.rewrites[0]), ordinary(&format!("Step . __mettail_rewrite_0:Proc, | __mettail_rewrite_0 ~> __mettail_rewrite_1 |- {expected_left} ~> {expected_right};")));
    }
}

#[test]
fn semantic_parameter_order_does_not_follow_concrete_syntax_order() {
    let mut source = language(
        "Name; Proc",
        "Order . p:Proc, n:Name |- n \"then\" p : Proc;",
        "Step . f:Rewrite(Proc), n:Name |- (Order (s f) n) ~> (Order (t f) n);",
    );
    normalize_rewrite_families(&mut source).unwrap();
    assert_eq!(rewrite_identity(&source.rewrites[0]), ordinary("Step . n:Name, __mettail_rewrite_0:Proc, | __mettail_rewrite_0 ~> __mettail_rewrite_1 |- (Order __mettail_rewrite_0 n) ~> (Order __mettail_rewrite_1 n);"));
}

#[test]
fn complete_collection_and_function_types_remain_distinct() {
    for ty in [
        "Vec(Proc)",
        "HashBag(Proc)",
        "HashSet(Proc)",
        "HashMap(Name, Proc)",
        "[Name -> Proc]",
    ] {
        let terms = format!("Carry . p:{ty} |- \"carry\" p : Proc;");
        let mut source = language(
            "Name; Proc",
            &terms,
            &format!("Step . f:Rewrite({ty}) |- (Carry (s f)) ~> (Carry (t f));"),
        );
        normalize_rewrite_families(&mut source).unwrap();
        assert_eq!(rewrite_identity(&source.rewrites[0]), ordinary(&format!("Step . __mettail_rewrite_0:{ty}, | __mettail_rewrite_0 ~> __mettail_rewrite_1 |- (Carry __mettail_rewrite_0) ~> (Carry __mettail_rewrite_1);")));
        assert_refuses_atomically(
            language(
                "Name; Proc",
                &terms,
                "Step . f:Rewrite(Proc) |- (Carry (s f)) ~> (Carry (t f));",
            ),
            "EndpointSort",
        );
    }
}

#[test]
fn collection_elements_use_their_full_declared_type() {
    let mut source = language(
        "Name; Proc",
        "Carry . p:Vec([Name -> Proc]) |- \"carry\" p : Proc;",
        "Step . f:Rewrite([Name -> Proc]) |- (Carry {(s f)}) ~> (Carry {(t f)});",
    );
    normalize_rewrite_families(&mut source).unwrap();
    assert_eq!(rewrite_identity(&source.rewrites[0]), ordinary("Step . __mettail_rewrite_0:[Name -> Proc], | __mettail_rewrite_0 ~> __mettail_rewrite_1 |- (Carry {__mettail_rewrite_0}) ~> (Carry {__mettail_rewrite_1});"));
    assert_refuses_atomically(
        language(
            "Name; Proc",
            "Carry . p:HashMap(Name, Proc) |- \"carry\" p : Proc;",
            "Step . f:Rewrite(Proc) |- (Carry {(s f)}) ~> (Carry {(t f)});",
        ),
        "ProjectionOutsideTypedContext",
    );
}

#[test]
fn multiple_binders_keep_all_declared_domains() {
    let mut source = basic("Step . f:[Name -> [Name -> Rewrite(Proc)]] |- (Many ^[x,y].(s (f x y))) ~> (Many ^[x,y].(t (f x y)));");
    normalize_rewrite_families(&mut source).unwrap();
    assert_eq!(rewrite_identity(&source.rewrites[0]), ordinary("Step . __mettail_rewrite_0:Proc, | __mettail_rewrite_0 ~> __mettail_rewrite_1 |- (Many ^[x,y].__mettail_rewrite_0) ~> (Many ^[x,y].__mettail_rewrite_1);"));
    assert_refuses_atomically(basic("Step . f:[Name -> Rewrite(Proc)] |- (Many ^[x,y].(s (f x))) ~> (Many ^[x,y].(t (f x)));"), "MissingDependency");
}

#[test]
fn repeated_sibling_binders_receive_distinct_names_before_family_endpoints() {
    let mut source = basic("Step . f:[Name -> Rewrite(Proc)], g:[Name -> Rewrite(Proc)] |- (Pair (New ^x.(s (f x))) (New ^x.(s (g x)))) ~> (Pair (New ^x.(t (f x))) (New ^x.(t (g x))));");
    normalize_rewrite_families(&mut source).unwrap();
    assert_eq!(rewrite_identity(&source.rewrites[0]), ordinary("Step . __mettail_rewrite_2:Proc, __mettail_rewrite_4:Proc, | __mettail_rewrite_2 ~> __mettail_rewrite_3, __mettail_rewrite_4 ~> __mettail_rewrite_5 |- (Pair (New ^__mettail_rewrite_0.__mettail_rewrite_2) (New ^__mettail_rewrite_1.__mettail_rewrite_4)) ~> (Pair (New ^__mettail_rewrite_0.__mettail_rewrite_3) (New ^__mettail_rewrite_1.__mettail_rewrite_5));"));
}

#[test]
fn optional_and_guard_parameters_disable_only_their_own_subtree() {
    for opaque in [
        TermParam::Optional {
            params: vec![TermParam::Simple {
                name: ident("opaque"),
                ty: syn::parse_str("Proc").unwrap(),
            }],
        },
        TermParam::GuardBody { name: ident("opaque") },
    ] {
        let mut source = basic(
            "Step . f:Rewrite(Proc) |- (Pair (Wrap Zero) (s f)) ~> (Pair (Wrap Zero) (t f));",
        );
        source
            .terms
            .iter_mut()
            .find(|rule| rule.label == "Pair")
            .unwrap()
            .term_context
            .as_mut()
            .unwrap()[0] = opaque.clone();
        normalize_rewrite_families(&mut source).unwrap();
        let mut forbidden = basic(
            "Step . f:Rewrite(Proc) |- (Pair (Wrap (s f)) Zero) ~> (Pair (Wrap (t f)) Zero);",
        );
        forbidden
            .terms
            .iter_mut()
            .find(|rule| rule.label == "Pair")
            .unwrap()
            .term_context
            .as_mut()
            .unwrap()[0] = opaque;
        assert_refuses_atomically(forbidden, "ProjectionOutsideTypedContext");
    }
}

fn census_premises(name: &str) -> Vec<Premise> {
    let n = || ident(name);
    let other = || ident("other");
    vec![
        Premise::Freshness(FreshnessCondition {
            var: n(),
            term: FreshnessTarget::Var(other()),
        }),
        Premise::Freshness(FreshnessCondition {
            var: other(),
            term: FreshnessTarget::Var(n()),
        }),
        Premise::Freshness(FreshnessCondition {
            var: other(),
            term: FreshnessTarget::CollectionRest(n()),
        }),
        Premise::Congruence { source: n(), target: other() },
        Premise::Congruence { source: other(), target: n() },
        Premise::CongruenceWithheld { source: n(), target: other() },
        Premise::CongruenceWithheld { source: other(), target: n() },
        Premise::RelationQuery {
            relation: other(),
            args: vec![other(), n()],
        },
        Premise::ForAll {
            collection: n(),
            param: other(),
            body: Box::new(Premise::BehavioralGuard(BehavioralPred::Top)),
        },
        Premise::ForAll {
            collection: other(),
            param: n(),
            body: Box::new(Premise::BehavioralGuard(BehavioralPred::Top)),
        },
        Premise::ForAll {
            collection: other(),
            param: other(),
            body: Box::new(Premise::RelationQuery { relation: other(), args: vec![n()] }),
        },
        Premise::BehavioralGuard(BehavioralPred::RelationQuery {
            relation_name: other(),
            args: vec![PredArg::Constant(other()), PredArg::Var(n())],
            negated: true,
        }),
        Premise::BehavioralGuard(BehavioralPred::Quantified {
            quantifier: Quantifier::Exists,
            var: n(),
            domain: Some(other()),
            bound: Some(4),
            body: Box::new(BehavioralPred::Top),
        }),
        Premise::BehavioralGuard(BehavioralPred::And(
            Box::new(BehavioralPred::Top),
            Box::new(BehavioralPred::Or(
                Box::new(BehavioralPred::Top),
                Box::new(BehavioralPred::Not(Box::new(BehavioralPred::Implies(
                    Box::new(BehavioralPred::Top),
                    Box::new(BehavioralPred::RelationQuery {
                        relation_name: other(),
                        args: vec![PredArg::Var(n())],
                        negated: false,
                    }),
                )))),
            )),
        )),
        Premise::BehavioralGuard(BehavioralPred::AcMatch {
            bag: n(),
            elements: vec![],
            rest: None,
        }),
        Premise::BehavioralGuard(BehavioralPred::AcMatch {
            bag: other(),
            elements: vec![other(), n()],
            rest: None,
        }),
        Premise::BehavioralGuard(BehavioralPred::AcMatch {
            bag: other(),
            elements: vec![],
            rest: Some(n()),
        }),
        Premise::SyntheticInjGuard {
            inner_var: n(),
            source_category: ident("Proc"),
            excluded_variants: vec![ident("Zero")],
        },
    ]
}

#[test]
fn every_structured_premise_read_and_declaration_prevents_name_capture() {
    for (index, premise) in census_premises("__mettail_rewrite_0")
        .into_iter()
        .enumerate()
    {
        let mut source = basic("Step . f:Rewrite(Proc) |- (s f) ~> (t f);");
        source.rewrites[0].premises.push(premise);
        let authored = premises_identity(&source.rewrites[0].premises);
        normalize_rewrite_families(&mut source).unwrap();
        assert_eq!(
            source.rewrites[0].type_context[0].name, "__mettail_rewrite_1",
            "premise {index}"
        );
        assert_eq!(premises_identity(&source.rewrites[0].premises[..1]), authored);
    }
}

#[test]
fn every_structured_premise_reference_refuses_ambiguous_binder_aliases() {
    for premise in census_premises("x") {
        let mut source = basic("Step . f:[Name -> Rewrite(Proc)], g:[Name -> Rewrite(Proc)] |- (Pair (New ^x.(s (f x))) (New ^x.(s (g x)))) ~> (Pair (New ^x.(t (f x))) (New ^x.(t (g x))));");
        source.rewrites[0].premises.push(premise);
        assert_refuses_atomically(source, "AmbiguousBinderReference");
    }
}

#[test]
fn raw_identifiers_retain_the_destination_compilers_exact_equality() {
    let mut source = basic("Step . r#f:Rewrite(Proc) |- (s r#f) ~> (t r#f);");
    normalize_rewrite_families(&mut source).unwrap();
    let mut raw = basic("Step . f:Rewrite(Proc) |- (s f) ~> (t f);");
    raw.terms[0].label = ident("r#__mettail_rewrite_0");
    normalize_rewrite_families(&mut raw).unwrap();
    assert_eq!(raw.rewrites[0].type_context[0].name, "__mettail_rewrite_0");
}

#[test]
fn unchanged_ordinary_rules_keep_their_identity_without_new_validation() {
    let mut source = basic("Old . |- (Unregistered missing) ~> another;");
    let before = language_definition_fingerprint(&source);
    normalize_rewrite_families(&mut source).unwrap();
    assert_eq!(language_definition_fingerprint(&source), before);
}

#[test]
fn later_failure_does_not_publish_an_earlier_normalized_rule() {
    assert_refuses_atomically(basic("Good . f:Rewrite(Proc) |- (s f) ~> (t f); Bad . f:[Name -> Rewrite(Proc)] |- (New ^x.(s (f x))) ~> (New ^x.(t (f absent)));"), "EscapedArgument");
}

#[test]
fn equations_refuse_family_contexts_before_any_rewrite_changes() {
    let mut source = basic("Step . f:Rewrite(Proc) |- (s f) ~> (t f);");
    let equation = syn::parse_str::<LanguageDef>("name: EquationTest, types {Proc}, terms {Zero . |- \"zero\" : Proc;}, equations { Eq . f:Rewrite(Proc) |- (s f) = (t f); }").unwrap();
    source.equations = equation.equations;
    assert_refuses_atomically(source, "not an equation");
}

#[test]
fn legacy_signatures_reuse_existing_normalization_and_refusal() {
    let mut source = basic("Step . f:Rewrite(Proc) |- (Wrap (s f)) ~> (Wrap (t f));");
    let wrapper = source
        .terms
        .iter_mut()
        .find(|rule| rule.label == "Wrap")
        .unwrap();
    wrapper.term_context = None;
    wrapper.syntax_pattern = None;
    wrapper.items =
        vec![GrammarItem::Terminal("wrap".into()), GrammarItem::non_terminal(ident("Proc"))];
    let mut invalid = source.clone();
    let wrapper = invalid
        .terms
        .iter_mut()
        .find(|rule| rule.label == "Wrap")
        .unwrap();
    wrapper.items = vec![GrammarItem::NonTerminal {
        ident: ident("Proc"),
        kind: NonTerminalKind::Var,
    }];
    normalize_rewrite_families(&mut source).unwrap();
    assert!(matches!(source.rewrites[0].type_context[0].ty, RuleContextType::Ordinary(_)));
    assert_refuses_atomically(invalid, "ProjectionOutsideTypedContext");
}

#[test]
fn native_collection_elements_require_complete_category_references() {
    use mettail_ast::language::CollectionCategory;
    for (native, result, accepted) in [
        ("Vec<Proc>", "Proc", true),
        ("Vec<module::Proc>", "Proc", true),
        ("Vec<Vec<Proc>>", "Vec", false),
        ("Vec<module::Vec<Proc>>", "Vec", false),
        ("Vec<<Proc as Trait>::Vec>", "Vec", false),
        ("Vec<&Proc>", "Proc", false),
    ] {
        let mut source = language(
            "Proc; Vec; Seq",
            "Carry . p:Seq |- \"carry\" p : Proc;",
            &format!("Step . f:Rewrite({result}) |- (Carry {{(s f)}}) ~> (Carry {{(t f)}});"),
        );
        let sequence = source.types.iter_mut().find(|ty| ty.name == "Seq").unwrap();
        sequence.collection_kind =
            Some(CollectionCategory::List(CollectionCategory::list_defaults()));
        sequence.native_type = Some(syn::parse_str(native).unwrap());
        if accepted {
            normalize_rewrite_families(&mut source).unwrap();
        } else {
            assert_refuses_atomically(source, "ProjectionOutsideTypedContext");
        }
    }
}

#[test]
fn reconstruction_uses_the_same_normalized_rules_as_the_direct_adapter() {
    let input = format!("name: ReconstructionFamily, types {{Name; Proc}}, terms {{{TERMS}}}, rewrites {{ Body . f:[Name -> Rewrite(Proc)] |- (New ^x.(s (f x))) ~> (New ^x.(t (f x))); }}");
    let reconstructed = mettail_ast::auto_inject::reconstruct_language_def_from_tokens(
        syn::parse_str(&input).unwrap(),
    )
    .unwrap();
    let mut expected: LanguageDef = syn::parse_str(&input).unwrap();
    normalize_rewrite_families(&mut expected).unwrap();
    let additions = mettail_ast::auto_inject::emit_auto_injection_rules(&expected);
    expected.terms.extend(additions.terms);
    expected.rewrites.extend(additions.rewrites);
    assert_eq!(
        language_definition_fingerprint(&reconstructed),
        language_definition_fingerprint(&expected)
    );
}

proptest! {
    #[test]
    fn ambiguous_multibinder_diagnostic_identifies_the_exact_nonzero_index(index in 1usize..12) {
        let mut family = "Rewrite(Proc)".to_owned();
        for _ in 0..=index { family = format!("[Name -> {family}]"); }
        let left_names = (0..index).map(|i| format!("a{i}")).chain(["shared".to_owned()]).collect::<Vec<_>>();
        let right_names = (0..index).map(|i| format!("b{i}")).chain(["shared".to_owned()]).collect::<Vec<_>>();
        let left_binders = left_names.join(",");
        let right_binders = right_names.join(",");
        let left_args = left_names.join(" ");
        let right_args = right_names.join(" ");
        let mut source = basic(&format!("Step . f:{family}, g:{family} |- (Pair (Many ^[{left_binders}].(s (f {left_args}))) (Many ^[{right_binders}].(s (g {right_args})))) ~> (Pair (Many ^[{left_binders}].(t (f {left_args}))) (Many ^[{right_binders}].(t (g {right_args}))));"));
        source.rewrites[0].premises.push(Premise::RelationQuery { relation:ident("predicate"), args:vec![ident("shared")] });
        let before = language_definition_fingerprint(&source);
        let failure = normalize_rewrite_families(&mut source).unwrap_err().to_string();
        prop_assert!(failure.contains("binder `shared`"), "{}", failure);
        prop_assert!(failure.contains(&format!("index {index}.")), "{}", failure);
        prop_assert!(failure.contains("path [0, 0]"), "{}", failure);
        prop_assert!(failure.contains("External(0)"), "{}", failure);
        prop_assert_eq!(language_definition_fingerprint(&source), before);
    }
}

#[test]
fn hidden_pattern_variables_participate_in_the_complete_name_census() {
    use mettail_ast::pattern::{Pattern, PatternTerm};
    let zero = || Box::new(Pattern::Term(PatternTerm::Var(ident("Zero"))));
    let reserved = || ident("__mettail_rewrite_0");
    let patterns = vec![
        Pattern::Term(PatternTerm::Subst {
            term: zero(),
            var: reserved(),
            replacement: zero(),
        }),
        Pattern::Collection {
            coll_type: None,
            elements: vec![],
            rest: Some(reserved()),
        },
        Pattern::Map {
            collection: zero(),
            params: vec![reserved()],
            body: zero(),
        },
        Pattern::IndexedVec {
            collection: reserved(),
            index: ident("index"),
            element: zero(),
        },
        Pattern::IndexedVec {
            collection: ident("values"),
            index: reserved(),
            element: zero(),
        },
    ];
    for pattern in patterns {
        let mut source = basic("Step . f:Rewrite(Proc) |- (Pair Zero (s f)) ~> (Pair Zero (t f));");
        let rule = &mut source.rewrites[0];
        for side in [&mut rule.left, &mut rule.right] {
            let Pattern::Term(PatternTerm::Apply { args, .. }) = side else {
                panic!()
            };
            args[0] = pattern.clone();
        }
        normalize_rewrite_families(&mut source).unwrap();
        assert_eq!(source.rewrites[0].type_context[0].name, "__mettail_rewrite_1");
    }
}

#[test]
fn every_computation_context_refuses_family_holes() {
    use mettail_ast::pattern::{Pattern, PatternTerm};
    let zero = || Box::new(Pattern::Term(PatternTerm::Var(ident("Zero"))));
    for variant in 0..5 {
        let mut source = basic("Step . f:Rewrite(Proc) |- (s f) ~> (t f);");
        let rule = &mut source.rewrites[0];
        for side in [&mut rule.left, &mut rule.right] {
            let projection = Box::new(side.clone());
            *side = match variant {
                0 => Pattern::Term(PatternTerm::Subst {
                    term: projection,
                    var: ident("x"),
                    replacement: zero(),
                }),
                1 => Pattern::Term(PatternTerm::MultiSubst {
                    scope: projection,
                    replacements: vec![],
                }),
                2 => Pattern::Map {
                    collection: zero(),
                    params: vec![ident("x")],
                    body: projection,
                },
                3 => Pattern::Zip { first: zero(), second: projection },
                4 => Pattern::IndexedVec {
                    collection: ident("values"),
                    index: ident("i"),
                    element: projection,
                },
                _ => unreachable!(),
            };
        }
        assert_refuses_atomically(source, "ProjectionOutsideTypedContext");
    }
}

#[test]
fn deep_normalization_uses_bounded_call_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            use mettail_ast::pattern::{Pattern, PatternTerm};
            let mut source = basic("Step . f:Rewrite(Proc) |- (s f) ~> (t f);");
            let rule = &mut source.rewrites[0];
            for side in [&mut rule.left, &mut rule.right] {
                let mut pattern =
                    std::mem::replace(side, Pattern::Term(PatternTerm::Var(ident("Zero"))));
                for _ in 0..4096 {
                    pattern = Pattern::Term(PatternTerm::Apply {
                        constructor: ident("Wrap"),
                        args: vec![pattern],
                    });
                }
                *side = pattern;
            }
            normalize_rewrite_families(&mut source).unwrap();
            for (pattern, expected) in [
                (&source.rewrites[0].left, "__mettail_rewrite_0"),
                (&source.rewrites[0].right, "__mettail_rewrite_1"),
            ] {
                let mut node = pattern;
                for _ in 0..4096 {
                    let Pattern::Term(PatternTerm::Apply { constructor, args }) = node else {
                        panic!()
                    };
                    assert_eq!(constructor, "Wrap");
                    assert_eq!(args.len(), 1);
                    node = &args[0];
                }
                let Pattern::Term(PatternTerm::Var(name)) = node else {
                    panic!()
                };
                assert_eq!(name, expected);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
