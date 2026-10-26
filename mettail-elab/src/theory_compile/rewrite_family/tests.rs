use super::*;
use proptest::prelude::*;

fn text(value: impl Into<String>) -> RhoValue {
    RhoValue::String(value.into())
}
fn list(values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
    RhoValue::List(values.into_iter().collect())
}
fn node(tag: &str, values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
    list(std::iter::once(text(tag)).chain(values))
}
fn typed(name: &str, sort: RhoValue) -> RhoValue {
    node("typed", [text(name), sort])
}
fn projection(side: &str, name: &str, arguments: &[String]) -> RhoValue {
    node(side, [node(name, arguments.iter().map(text))])
}
fn family(name: &str, domains: &[String], result: &str) -> RhoValue {
    typed(
        name,
        domains
            .iter()
            .rev()
            .fold(node("rewrite", [text(result)]), |value, domain| {
                node("arrow", [text(domain), value])
            }),
    )
}
fn rule(
    context: Vec<RhoValue>,
    left: RhoValue,
    right: RhoValue,
    premises: Vec<RhoValue>,
) -> RhoValue {
    RhoValue::Map(BTreeMap::from([
        ("name".into(), text("Under")),
        ("context".into(), list(context)),
        ("left".into(), left),
        ("right".into(), right),
        ("premises".into(), list(premises)),
    ]))
}
fn syntax(name: &str) -> core::TheorySortV1 {
    core::TheorySortV1 {
        name: name.into(),
        kind: core::TheorySortKindV1::Syntax { literal: None },
    }
}
fn constructor(name: &str, domain: Vec<String>, result: &str) -> core::TheoryConstructorV1 {
    core::TheoryConstructorV1 {
        name: name.into(),
        domain,
        codomain: result.into(),
    }
}
fn signature(
    sorts: Vec<core::TheorySortV1>,
    constructors: Vec<core::TheoryConstructorV1>,
) -> Signature {
    let mut theory = core::TheoryCoreV1::structural();
    theory.profile = core::TheoryProfileV1::Oslf;
    theory.sorts = sorts;
    theory.constructors = constructors;
    Signature::from_theory(&theory)
}
fn limits() -> core::TheoryLimitsV1 {
    core::TheoryCoreV1::structural().limits
}
fn compile(
    value: &RhoValue,
    signature: &Signature,
) -> Result<core::TheoryRewriteV1, ValueDecodeError> {
    compile_rewrite(value, "$.rule", signature, limits())
}
fn without_names(mut rule: core::TheoryRewriteV1) -> core::TheoryRewriteV1 {
    for variable in &mut rule.arena.variables {
        variable.name = format!("slot{}", variable.id.0);
    }
    rule
}
fn equivalent(family: &RhoValue, ordinary: &RhoValue, signature: &Signature) {
    let before = family.clone();
    let actual = compile(family, signature).expect("explicit family compiles");
    let expected = compile(ordinary, signature).expect("ordinary premise control compiles");
    assert_eq!(without_names(actual), without_names(expected));
    assert_eq!(family, &before);
    let normalized = normalize(family, "$.rule", signature, limits())
        .unwrap()
        .unwrap();
    assert!(normalize(&normalized, "$.rule", signature, limits())
        .unwrap()
        .is_none());
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    #[test]
    fn ordered_constructor_and_product_fields_match_ordinary_rules(
        salt in any::<u16>(), count in 1usize..7, selected in 0usize..7, product in any::<bool>(),
    ) {
        let selected = selected % count;
        let names = (0..count).map(|index| format!("S{salt}_{index}")).collect::<Vec<_>>();
        let mut sorts = names.iter().map(|name| syntax(name)).collect::<Vec<_>>();
        sorts.push(syntax("Output"));
        let constructors = if product {
            sorts.push(core::TheorySortV1 { name: "Tuple".into(), kind: core::TheorySortKindV1::Product { factors: names.clone() } });
            vec![constructor("Outer", vec!["Tuple".into()], "Output")]
        } else { vec![constructor("Outer", names.clone(), "Output")] };
        let signature = signature(sorts, constructors);
        let fields = |endpoint: RhoValue| (0..count).map(|index| if index == selected { endpoint.clone() } else { text(format!("v{index}")) }).collect::<Vec<_>>();
        let wrap = |endpoint| {
            let fields = fields(endpoint);
            if product { node("Outer", [node("product", fields)]) } else { node("Outer", fields) }
        };
        let ordinary_context = (0..count).filter(|index| *index != selected).map(|index| typed(&format!("v{index}"), text(&names[index]))).collect::<Vec<_>>();
        let mut explicit_context = ordinary_context.clone();
        explicit_context.push(family("f", &[], &names[selected]));
        let explicit = rule(explicit_context, wrap(projection("s", "f", &[])), wrap(projection("t", "f", &[])), vec![]);
        let mut ordinary_context = ordinary_context;
        ordinary_context.push(typed("source", text(&names[selected])));
        let ordinary = rule(ordinary_context, wrap(text("source")), wrap(text("target")), vec![node("~>", [text("source"), text("target")])]);
        equivalent(&explicit, &ordinary, &signature);
        let wrong = rule(vec![family("f", &[], "Output")], wrap(projection("s", "f", &[])), wrap(projection("t", "f", &[])), vec![]);
        prop_assert!(compile(&wrong, &signature).is_err());
        for extra in [false, true] {
            let mut invalid = explicit.clone();
            let RhoValue::Map(values) = &mut invalid else { unreachable!() };
            for side in ["left", "right"] {
                let RhoValue::List(outer) = values.get_mut(side).unwrap() else { unreachable!() };
                let fields = if product {
                    let RhoValue::List(fields) = &mut outer[1] else { unreachable!() };
                    fields
                } else { outer };
                if extra { fields.push(text("extra")); } else { fields.pop(); }
            }
            let error = normalize(&invalid, "$.rule", &signature, limits()).unwrap_err();
            prop_assert!(error.message.contains(if product { "product arity" } else { "incompatible arity" }), "{error}");
        }
    }

    #[test]
    fn nested_unary_binders_use_registered_domains_and_preserve_slots(depth in 1usize..7, salt in any::<u16>()) {
        let endpoint = format!("Result{salt}");
        let domains = (0..depth).map(|index| format!("Domain{salt}_{index}")).collect::<Vec<_>>();
        let mut sorts = vec![syntax(&endpoint)];
        sorts.extend(domains.iter().map(|name| syntax(name)));
        for index in 0..depth {
            sorts.push(core::TheorySortV1 {
                name: format!("Function{index}"),
                kind: core::TheorySortKindV1::Function {
                    domain: domains[index].clone(),
                    codomain: if index + 1 == depth { endpoint.clone() } else { format!("Function{}", index + 1) },
                    multiple: false,
                },
            });
        }
        let signature = signature(sorts, vec![constructor("Under", vec!["Function0".into()], &endpoint)]);
        let binders = (0..depth).map(|index| format!("x{index}")).collect::<Vec<_>>();
        let wrap = |body| node("Under", [binders.iter().rev().fold(body, |body, name| node("^", [text(name), body]))]);
        let explicit = rule(vec![family("f", &domains, &endpoint)], wrap(projection("s", "f", &binders)), wrap(projection("t", "f", &binders)), vec![]);
        let ordinary = rule(vec![typed("source", text(&endpoint))], wrap(text("source")), wrap(text("target")), vec![node("~>", [text("source"), text("target")])]);
        equivalent(&explicit, &ordinary, &signature);
        let bad_arguments = vec![binders[0].clone(); depth + 1];
        let bad = rule(vec![family("f", &domains, &endpoint)], wrap(projection("s", "f", &bad_arguments)), wrap(projection("t", "f", &bad_arguments)), vec![]);
        prop_assert!(compile(&bad, &signature).is_err());
    }

    #[test]
    fn collection_fields_use_each_registered_kind_and_pathmap_mode(which in 0usize..6, typed_elements in any::<bool>(), salt in any::<u16>()) {
        let key = format!("Key{salt}");
        let value = format!("Value{salt}");
        let pair = format!("Pair{salt}");
        let kinds = [core::CollectionKind::List, core::CollectionKind::Bag, core::CollectionKind::Set, core::CollectionKind::Map, core::CollectionKind::PathMap, core::CollectionKind::PathMap];
        let kind = kinds[which];
        let keyed = matches!(kind, core::CollectionKind::Map | core::CollectionKind::PathMap);
        let element = if keyed { &pair } else { &value };
        let selected = if which == 4 { &key } else { element };
        let mode = match which { 4 => Some("set"), 5 => Some("map"), _ => None };
        let signature = signature(vec![
            syntax(&key), syntax(&value),
            core::TheorySortV1 { name: pair.clone(), kind: core::TheorySortKindV1::Product { factors: vec![key.clone(), value.clone()] } },
            core::TheorySortV1 { name: "Values".into(), kind: core::TheorySortKindV1::Collection { kind, key: keyed.then(|| key.clone()), element: element.clone() } },
        ], vec![constructor("Outer", vec!["Values".into()], &value)]);
        let wrap = |endpoint| {
            let mut fields = Vec::new();
            if typed_elements { fields.push(text(selected)); }
            fields.extend([list([endpoint]), RhoValue::Nil]);
            if let Some(mode) = mode { fields.push(text(mode)); }
            node("Outer", [node(if typed_elements { "coll_typed" } else { "coll" }, fields)])
        };
        let explicit = rule(vec![family("f", &[], selected)], wrap(projection("s", "f", &[])), wrap(projection("t", "f", &[])), vec![]);
        let ordinary = rule(vec![typed("source", text(selected))], wrap(text("source")), wrap(text("target")), vec![node("~>", [text("source"), text("target")])]);
        equivalent(&explicit, &ordinary, &signature);
        if kind != core::CollectionKind::PathMap {
            let mut invalid = explicit.clone();
            let RhoValue::Map(values) = &mut invalid else { unreachable!() };
            for side in ["left", "right"] {
                let RhoValue::List(outer) = values.get_mut(side).unwrap() else { unreachable!() };
                let RhoValue::List(collection) = &mut outer[1] else { unreachable!() };
                collection.push(text("set"));
            }
            let error = normalize(&invalid, "$.rule", &signature, limits()).unwrap_err();
            prop_assert!(error.message.contains("only a PathMap"), "{error}");
        } else if which == 4 {
            let mut invalid_signature = signature.clone();
            let index = invalid_signature.sort_indices["Values"];
            let core::TheorySortKindV1::Collection { key, .. } = &mut invalid_signature.sorts[index].kind else { unreachable!() };
            *key = None;
            let error = normalize(&explicit, "$.rule", &invalid_signature, limits()).unwrap_err();
            prop_assert!(error.message.contains("no declared key sort"), "{error}");
        }
    }
}

#[test]
fn family_order_and_existing_premises_survive_normalization() {
    let mut signature = signature(
        vec![syntax("P")],
        vec![constructor("Pair", vec!["P".into(), "P".into(), "P".into()], "P")],
    );
    signature.judgments.insert("J".into(), vec!["P".into()]);
    let wrap = |f, g| node("Pair", [f, text("x"), g]);
    let premises = vec![node("rel", [text("J"), list([text("x")])])];
    let explicit = rule(
        vec![typed("x", text("P")), family("g", &[], "P"), family("f", &[], "P")],
        wrap(projection("s", "f", &[]), projection("s", "g", &[])),
        wrap(projection("t", "f", &[]), projection("t", "g", &[])),
        premises.clone(),
    );
    let mut ordinary_premises = premises;
    ordinary_premises
        .extend([node("~>", [text("gs"), text("gt")]), node("~>", [text("fs"), text("ft")])]);
    let ordinary = rule(
        vec![typed("x", text("P")), typed("gs", text("P")), typed("fs", text("P"))],
        wrap(text("fs"), text("gs")),
        wrap(text("ft"), text("gt")),
        ordinary_premises,
    );
    equivalent(&explicit, &ordinary, &signature);
}

#[test]
fn canonical_strings_remain_variables_even_when_a_constructor_has_that_name() {
    let signature = signature(vec![syntax("P")], vec![constructor("x", vec![], "P")]);
    let explicit = rule(
        vec![typed("x", text("P")), family("f", &["P".into()], "P")],
        projection("s", "f", &["x".into()]),
        projection("t", "f", &["x".into()]),
        vec![],
    );
    let ordinary = rule(
        vec![typed("x", text("P")), typed("source", text("P"))],
        text("source"),
        text("target"),
        vec![node("~>", [text("source"), text("target")])],
    );
    equivalent(&explicit, &ordinary, &signature);
}

#[test]
fn root_collection_inference_preserves_existing_selection_and_refusal() {
    let collection = |name: &str| core::TheorySortV1 {
        name: name.into(),
        kind: core::TheorySortKindV1::Collection {
            kind: core::CollectionKind::List,
            key: None,
            element: "P".into(),
        },
    };
    let wrap = |body| node("coll", [list([body]), RhoValue::Nil]);
    let explicit = rule(
        vec![family("f", &[], "P")],
        wrap(projection("s", "f", &[])),
        wrap(projection("t", "f", &[])),
        vec![],
    );
    let ordinary = rule(
        vec![typed("source", text("P"))],
        wrap(text("source")),
        wrap(text("target")),
        vec![node("~>", [text("source"), text("target")])],
    );
    equivalent(
        &explicit,
        &ordinary,
        &signature(vec![syntax("P"), collection("Values")], vec![]),
    );
    for sorts in [vec![syntax("P")], vec![syntax("P"), collection("First"), collection("Second")]] {
        let signature = signature(sorts, vec![]);
        assert!(compile(&explicit, &signature).is_err());
        assert!(compile(&ordinary, &signature).is_err());
    }
}

#[test]
fn computation_paths_refuse_family_holes_and_keep_names_visible() {
    let signature = signature(vec![syntax("P")], vec![constructor("Known", vec!["P".into()], "P")]);
    for tag in ["eval", "pmap", "pzip"] {
        let wrap = |body| match tag {
            "pmap" => {
                node(tag, [text("collection"), list([text("parameter")]), node("Known", [body])])
            },
            _ => node(tag, [node("Known", [body]), text("argument")]),
        };
        let explicit = rule(
            vec![family("f", &[], "P")],
            wrap(projection("s", "f", &[])),
            wrap(projection("t", "f", &[])),
            vec![],
        );
        let failure = normalize(&explicit, "$.rule", &signature, limits()).unwrap_err();
        assert!(
            failure
                .to_string()
                .contains("ProjectionOutsideTypedContext"),
            "{failure}"
        );
    }
}

#[test]
fn complete_premise_name_census_excludes_constant_and_relation_labels() {
    let guard = node(
        "guard",
        [node(
            "and",
            [list([
                node(
                    "call",
                    [
                        text("relation"),
                        list([node("var", [text("argument")]), node("const", [text("constant")])]),
                    ],
                ),
                node(
                    "quant",
                    [
                        text("forall"),
                        text("quantified"),
                        text("Category"),
                        RhoValue::Nil,
                        node("not", [node("true", [])]),
                    ],
                ),
                node(
                    "implies",
                    [
                        node("true", []),
                        node("ac_match", [text("bag"), list([text("element")]), text("rest")]),
                    ],
                ),
            ])],
        )],
    );
    let premises = list([
        node("fresh", [text("fresh"), text("term")]),
        node(
            "forall",
            [
                text("collection"),
                text("parameter"),
                node("rel", [text("judgment"), list([text("parameter")])]),
            ],
        ),
        guard,
    ]);
    assert_eq!(
        premise_names(Some(&premises), "$.premises").unwrap(),
        vec![
            "fresh",
            "term",
            "collection",
            "parameter",
            "parameter",
            "argument",
            "quantified",
            "bag",
            "element",
            "rest"
        ]
    );
}

#[test]
fn ordinary_rules_return_unchanged_without_context_normalization() {
    let signature = signature(vec![syntax("P")], vec![constructor("Wrap", vec!["P".into()], "P")]);
    let ordinary = rule(vec![typed("x", text("P"))], node("Wrap", [text("x")]), text("x"), vec![]);
    assert!(normalize(&ordinary, "$.rule", &signature, limits())
        .unwrap()
        .is_none());
    compile(&ordinary, &signature).unwrap();
}

#[test]
fn registered_endpoints_and_structural_refusals_match_descriptor_contracts() {
    let sorts = vec![
        syntax("P"),
        core::TheorySortV1 {
            name: "Opaque".into(),
            kind: core::TheorySortKindV1::Opaque { abi: "test:opaque/1".into() },
        },
    ];
    for name in ["P", "Opaque"] {
        let signature =
            signature(sorts.clone(), vec![constructor("Outer", vec![name.into()], "P")]);
        let explicit = rule(
            vec![family("f", &[], name)],
            projection("s", "f", &[]),
            projection("t", "f", &[]),
            vec![],
        );
        let ordinary = rule(
            vec![typed("source", text(name))],
            text("source"),
            text("target"),
            vec![node("~>", [text("source"), text("target")])],
        );
        equivalent(&explicit, &ordinary, &signature);
        for shape in ["^", "product", "coll"] {
            let wrap = |body| {
                node(
                    "Outer",
                    [match shape {
                        "^" => node("^", [text("x"), body]),
                        "product" => node("product", [body]),
                        _ => node("coll", [list([body]), RhoValue::Nil]),
                    }],
                )
            };
            let invalid = rule(
                vec![family("f", &[], name)],
                wrap(projection("s", "f", &[])),
                wrap(projection("t", "f", &[])),
                vec![],
            );
            assert!(compile(&invalid, &signature).is_err());
        }
    }
    let signature = signature(sorts, vec![]);
    let missing = rule(
        vec![family("f", &[], "Missing")],
        projection("s", "f", &[]),
        projection("t", "f", &[]),
        vec![],
    );
    assert!(compile(&missing, &signature)
        .unwrap_err()
        .to_string()
        .contains("UnknownSort"));
}

#[test]
fn sibling_binder_shadowing_has_distinct_slots_and_ambiguous_references_are_diagnostic() {
    let mut signature = signature(
        vec![
            syntax("P"),
            core::TheorySortV1 {
                name: "Fn".into(),
                kind: core::TheorySortKindV1::Function {
                    domain: "P".into(),
                    codomain: "P".into(),
                    multiple: false,
                },
            },
        ],
        vec![constructor("Pair", vec!["Fn".into(), "Fn".into()], "P")],
    );
    let wrap = |a, b, first: &str, second: &str| {
        node("Pair", [node("^", [text(first), a]), node("^", [text(second), b])])
    };
    let explicit = rule(
        vec![family("f", &["P".into()], "P"), family("g", &["P".into()], "P")],
        wrap(
            projection("s", "f", &["x".into()]),
            projection("s", "g", &["x".into()]),
            "x",
            "x",
        ),
        wrap(
            projection("t", "f", &["x".into()]),
            projection("t", "g", &["x".into()]),
            "x",
            "x",
        ),
        vec![],
    );
    let ordinary = rule(
        vec![typed("fs", text("P")), typed("gs", text("P"))],
        wrap(text("fs"), text("gs"), "first", "second"),
        wrap(text("ft"), text("gt"), "first", "second"),
        vec![node("~>", [text("fs"), text("ft")]), node("~>", [text("gs"), text("gt")])],
    );
    equivalent(&explicit, &ordinary, &signature);
    signature.judgments.insert("J".into(), vec!["P".into()]);
    let mut ambiguous = explicit;
    let RhoValue::Map(values) = &mut ambiguous else {
        unreachable!()
    };
    values.insert("premises".into(), list([node("rel", [text("J"), list([text("x")])])]));
    let failure = compile(&ambiguous, &signature).unwrap_err().to_string();
    assert!(failure.contains("AmbiguousBinderReference: binder `x`"), "{failure}");
    assert!(failure.contains("Conflicting reference at Some(External(0))"), "{failure}");
}

#[test]
fn multiple_functions_keep_endpoint_support_and_unary_abstraction_refusal() {
    let signature = signature(
        vec![
            syntax("P"),
            core::TheorySortV1 {
                name: "Many".into(),
                kind: core::TheorySortKindV1::Function {
                    domain: "P".into(),
                    codomain: "P".into(),
                    multiple: true,
                },
            },
        ],
        vec![constructor("Outer", vec!["Many".into()], "P")],
    );
    let endpoint = rule(
        vec![family("f", &[], "Many")],
        projection("s", "f", &[]),
        projection("t", "f", &[]),
        vec![],
    );
    compile(&endpoint, &signature).unwrap();
    for tag in ["^", "^*"] {
        let wrap = |body| {
            node(
                "Outer",
                [node(
                    tag,
                    [
                        if tag == "^" {
                            text("x")
                        } else {
                            list([text("x")])
                        },
                        body,
                    ],
                )],
            )
        };
        let invalid = rule(
            vec![family("f", &["P".into()], "P")],
            wrap(projection("s", "f", &["x".into()])),
            wrap(projection("t", "f", &["x".into()])),
            vec![],
        );
        assert!(compile(&invalid, &signature).is_err());
    }
    let invalid = rule(
        vec![typed("xs", node("multi", [text("P")])), family("f", &[], "P")],
        projection("s", "f", &[]),
        projection("t", "f", &[]),
        vec![],
    );
    assert!(compile(&invalid, &signature)
        .unwrap_err()
        .to_string()
        .contains("multi"));
}

fn canonical_language(ty: RhoValue, rewrite: RhoValue) -> RhoValue {
    let term = RhoValue::Map(BTreeMap::from([
        ("label".into(), text("Outer")),
        ("category".into(), text("P")),
        ("context".into(), list([node("param", [text("body"), ty])])),
        ("syntax".into(), list([node("lit", [text("outer")]), text("body")])),
    ]));
    RhoValue::Map(BTreeMap::from([
        ("mettail".into(), text("language/3")),
        ("name".into(), text("Families")),
        ("types".into(), list([text("P"), text("Q")])),
        ("terms".into(), list([term])),
        ("rewrites".into(), list([rewrite])),
        ("oslf".into(), RhoValue::Map(BTreeMap::new())),
    ]))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn public_language_lowering_preserves_family_and_ordinary_rule_correspondence(which in 0usize..5, salt in any::<u16>()) {
        let family_name = format!("family{salt}");
        let (ty, endpoint, domains, arguments, wrapper): (_, _, Vec<String>, Vec<String>, _) = match which {
            0 => (text("P"), text("P"), vec![], vec![], "plain"),
            1 => (node("arrow", [text("Q"), text("P")]), text("P"), vec!["Q".into()], vec!["x".into()], "^"),
            2 => (node("vec", [text("P")]), text("P"), vec![], vec![], "coll"),
            3 => (node("pathmap", [text("P"), text("Q")]), text("P"), vec![], vec![], "set"),
            _ => (node("map", [text("P"), text("Q")]), text("Q"), vec![], vec![], "map"),
        };
        let wrap = |body| node("Outer", [match wrapper {
            "plain" => body,
            "^" => node("^", [text("x"), body]),
            "map" => node("coll", [list([node("product", [text("key"), body])]), RhoValue::Nil]),
            "set" => node("coll", [list([body]), RhoValue::Nil, text("set")]),
            _ => node("coll", [list([body]), RhoValue::Nil]),
        }]);
        let ordinary_context = if wrapper == "map" { vec![typed("key", text("P"))] } else { vec![] };
        let mut explicit_context = ordinary_context.clone();
        let RhoValue::String(endpoint_name) = &endpoint else { unreachable!() };
        explicit_context.push(family(&family_name, &domains, endpoint_name));
        let explicit = rule(explicit_context, wrap(projection("s", &family_name, &arguments)), wrap(projection("t", &family_name, &arguments)), vec![]);
        let mut ordinary_context = ordinary_context;
        ordinary_context.push(typed("source", endpoint));
        let ordinary = rule(ordinary_context, wrap(text("source")), wrap(text("target")), vec![node("~>", [text("source"), text("target")])]);
        let explicit_value = canonical_language(ty.clone(), explicit);
        let actual = crate::canonical::value_to_language_core(&explicit_value).unwrap();
        let expected = crate::canonical::value_to_language_core(&canonical_language(ty, ordinary)).unwrap();
        prop_assert_eq!(actual.grammar, expected.grammar);
        prop_assert_eq!(actual.theory.sorts, expected.theory.sorts);
        prop_assert_eq!(without_names(actual.theory.rewrites[0].clone()), without_names(expected.theory.rewrites[0].clone()));
    }
}

#[test]
fn public_lowering_refuses_duplicate_unknown_and_invalid_pathmap_descriptors_without_mutation() {
    let wrap = |body, mode| {
        node(
            "Outer",
            [node(
                "coll",
                [list([node("product", [body, text("value")])]), RhoValue::Nil, mode],
            )],
        )
    };
    for mode in [RhoValue::Nil, text("neutral-empty")] {
        let explicit = rule(
            vec![typed("value", text("Q")), family("f", &[], "P")],
            wrap(projection("s", "f", &[]), mode.clone()),
            wrap(projection("t", "f", &[]), mode),
            vec![],
        );
        let value = canonical_language(node("pathmap", [text("P"), text("Q")]), explicit);
        let before = value.clone();
        let failure = crate::canonical::value_to_language_core(&value).unwrap_err();
        assert!(
            matches!(
                &failure,
                crate::canonical::ValueToCoreError::Decode(error)
                    if error.path == "$.oslf" && error.message.starts_with("invalid LanguageCore:")
            ),
            "{failure:?}"
        );
        assert_eq!(value, before);
    }
    for mode in [RhoValue::Nil, text("neutral-empty")] {
        let remainder_only = matches!(mode, RhoValue::Nil);
        let context = if remainder_only {
            vec![typed("rest", node("pathmap", [text("P"), text("Q")]))]
        } else {
            vec![]
        };
        let body = node(
            "Outer",
            [node(
                "coll",
                [
                    list([]),
                    if remainder_only {
                        text("rest")
                    } else {
                        RhoValue::Nil
                    },
                    mode,
                ],
            )],
        );
        let ordinary = rule(context, body.clone(), body, vec![]);
        crate::canonical::value_to_language_core(&canonical_language(
            node("pathmap", [text("P"), text("Q")]),
            ordinary,
        ))
        .unwrap();
    }
    let explicit = rule(
        vec![family("f", &[], "P")],
        node("Outer", [projection("s", "f", &[])]),
        node("Outer", [projection("t", "f", &[])]),
        vec![],
    );
    let valid = canonical_language(text("P"), explicit);
    crate::canonical::value_to_language_core(&valid).unwrap();
    let mut duplicates = valid.clone();
    let RhoValue::Map(values) = &mut duplicates else {
        unreachable!()
    };
    values.insert("types".into(), list([text("P"), text("P"), text("Q")]));
    assert!(crate::canonical::value_to_language_core(&duplicates).is_err());
    let mut unknown = valid;
    let RhoValue::Map(values) = &mut unknown else {
        unreachable!()
    };
    values.insert(
        "rewrites".into(),
        list([rule(
            vec![family("f", &[], "Absent")],
            projection("s", "f", &[]),
            projection("t", "f", &[]),
            vec![],
        )]),
    );
    assert!(crate::canonical::value_to_language_core(&unknown).is_err());
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn premise_census_preserves_intrinsic_and_nested_predicate_names(salt in any::<u16>()) {
        let names = (0..9).map(|i| format!("name{salt}_{i}")).collect::<Vec<_>>();
        let premises = list([
            node("fresh_rest", [text(&names[0]), text(&names[1])]),
            node("~>", [text(&names[2]), text(&names[3])]),
            node("intrinsic", [RhoValue::Map(BTreeMap::from([
                ("op".into(), text("utf8_scalar_at")),
                ("inputs".into(), list([text(&names[4]), text(&names[5])])),
                ("outputs".into(), list([typed(&names[6], text("Text")), typed(&names[7], text("Int"))])),
            ]))]),
            node("guard", [node("or", [list([
                node("ncall", [text("relation_label"), list([node("const", [text("opaque_constant")]), node("var", [text(&names[8])])])]),
                node("ac_match", [text(&names[0]), list([]), RhoValue::Nil]),
            ])])]),
        ]);
        let mut expected = names.iter().map(String::as_str).collect::<Vec<_>>();
        expected.push(names[0].as_str());
        prop_assert_eq!(premise_names(Some(&premises), "$.premises").unwrap(), expected);
    }

    #[test]
    fn public_rule_batch_refuses_a_later_invalid_family_atomically(salt in any::<u16>()) {
        let name = format!("family{salt}");
        let make = |result| rule(vec![family(&name, &[], result)], node("Outer", [projection("s", &name, &[])]), node("Outer", [projection("t", &name, &[])]), vec![]);
        let good = make("P");
        let valid = canonical_language(text("P"), good.clone());
        crate::canonical::value_to_language_core(&valid).unwrap();
        let mut bad = make("Missing");
        let RhoValue::Map(fields) = &mut bad else { unreachable!() };
        fields.insert("name".into(), text("Later"));
        let mut input = valid;
        let RhoValue::Map(fields) = &mut input else { unreachable!() };
        fields.insert("rewrites".into(), list([good, bad]));
        let before = input.clone();
        let error = crate::canonical::value_to_language_core(&input).unwrap_err();
        prop_assert!(matches!(&error, crate::canonical::ValueToCoreError::Decode(error) if error.message.contains("UnknownSort")), "{error:?}");
        prop_assert_eq!(input, before);
    }
}

#[test]
fn canonical_normalization_and_cleanup_use_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let signature =
                signature(vec![syntax("P")], vec![constructor("Wrap", vec!["P".into()], "P")]);
            let depth = 2048;
            let wrap = |endpoint| (0..depth).fold(endpoint, |body, _| node("Wrap", [body]));
            let value = rule(
                vec![family("f", &[], "P")],
                wrap(projection("s", "f", &[])),
                wrap(projection("t", "f", &[])),
                vec![],
            );
            let normalized = normalize(&value, "$.rule", &signature, limits())
                .unwrap()
                .unwrap();
            let RhoValue::Map(fields) = &normalized else {
                unreachable!()
            };
            let RhoValue::List(premises) = &fields["premises"] else {
                unreachable!()
            };
            let RhoValue::List(premise) = &premises[0] else {
                unreachable!()
            };
            for (side, endpoint) in [("left", &premise[1]), ("right", &premise[2])] {
                let mut current = &fields[side];
                for _ in 0..depth {
                    let RhoValue::List(children) = current else {
                        panic!("wrapper lost")
                    };
                    assert_eq!(children[0], text("Wrap"));
                    assert_eq!(children.len(), 2);
                    current = &children[1];
                }
                assert_eq!(current, endpoint);
            }
            assert!(normalize(&normalized, "$.rule", &signature, limits())
                .unwrap()
                .is_none());
            drop(normalized);
            drop(value);
        })
        .unwrap()
        .join()
        .unwrap();
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    #[test]
    fn typed_slot_allocation_preserves_prefix_capacity_and_roles(
        prefix in prop::collection::vec((0usize..5, any::<bool>()), 0..12),
        adoption in 0usize..5, salt in any::<u16>(),
    ) {
        let signature = signature(vec![syntax("P"), syntax("Q")], vec![]);
        let roles = [core::TheoryVariableRoleV1::Input, core::TheoryVariableRoleV1::Binder, core::TheoryVariableRoleV1::Derived, core::TheoryVariableRoleV1::Remainder, core::TheoryVariableRoleV1::Quantified];
        let mut bounds = limits();
        bounds.max_rule_variables = prefix.len() as u32 + 1;
        let mut compiler = RuleCompiler::new(&signature, bounds, "Slots");
        let mut expected = Vec::new();
        for (index, (role, alternate)) in prefix.iter().copied().chain(std::iter::once((0, false))).enumerate() {
            let name = format!("slot{salt}_{index}");
            let sort = if alternate { "Q" } else { "P" };
            let id = core::TheoryVariableId(index as u32);
            prop_assert_eq!(compiler.add_variable(&name, sort, roles[role], "$.slots").unwrap(), id);
            expected.push(core::TheoryVariableV1 { id, name, sort: sort.into(), role: roles[role] });
            prop_assert_eq!(&compiler.variables, &expected);
        }
        let before_ids = compiler.variable_ids.clone();
        let before_names = compiler.variable_names.clone();
        let error = compiler.add_variable("overflow", "P", roles[adoption], "$.slots").unwrap_err();
        prop_assert!(error.message.contains("rule-variable limit exceeded"));
        prop_assert_eq!(&compiler.variables, &expected);
        prop_assert_eq!(&compiler.variable_ids, &before_ids);
        prop_assert_eq!(&compiler.variable_names, &before_names);
        let source = &expected[0].name;
        let target = &expected.last().unwrap().name;
        let transition = node("~>", [text(source), text(target)]);
        let error = compiler.compile_premise(&transition, true, "$.premise").unwrap_err();
        prop_assert_eq!(error.path, "$.premise[2]");
        prop_assert_eq!(error.message, format!("transition target `{target}` is already bound"));
        prop_assert_eq!(&compiler.variables, &expected);
        prop_assert_eq!(&compiler.variable_ids, &before_ids);
        prop_assert_eq!(&compiler.variable_names, &before_names);
        prop_assert!(compiler.premises.is_empty());
        for slot in &expected {
            prop_assert_eq!(compiler.require_variable(&slot.name, &slot.sort, "$.slots").unwrap(), slot.id);
        }
        prop_assert!(compiler.require_variable("absent", "P", "$.slots").is_err());
        let pivot = expected.last_mut().unwrap();
        prop_assert_eq!(compiler.add_or_constrain_input(&pivot.name, "P", roles[adoption], "$.slots").unwrap(), pivot.id);
        pivot.role = roles[adoption];
        let pivot_name = pivot.name.clone();
        prop_assert_eq!(&compiler.variables, &expected);
        prop_assert!(compiler.add_or_constrain_input(&pivot_name, "Q", roles[adoption], "$.slots").is_err());
        prop_assert!(compiler.require_variable(&pivot_name, "Q", "$.slots").is_err());
        prop_assert_eq!(&compiler.variables, &expected);
        prop_assert_eq!(compiler.variable_ids, before_ids);
        prop_assert_eq!(compiler.variable_names, before_names);
        let mut binder_limits = limits();
        binder_limits.max_rule_variables = 1;
        let mut binder = RuleCompiler::new(&signature, binder_limits, "Binder");
        let id = binder.add_variable("bound", "P", core::TheoryVariableRoleV1::Binder, "$.binder").unwrap();
        let before = binder.variables.clone();
        prop_assert_eq!(binder.add_or_constrain_input("bound", "P", core::TheoryVariableRoleV1::Input, "$.binder").unwrap(), id);
        prop_assert_eq!(binder.variables, before);
    }
}
