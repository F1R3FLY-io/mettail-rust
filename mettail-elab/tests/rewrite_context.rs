use mettail_elab::ast::{
    Ast, Builder, RewriteContextBinding, RewriteDecl, RewriteEntry, TheoryDecl, TheoryExpr,
};
use mettail_elab::canonical::{presentation_to_value, value_to_presentation, RhoValue};
use mettail_elab::diag::DiagKind;
use mettail_elab::lex::Span;
use mettail_elab::parse::{parse_theory, MAX_DDL_STRUCTURAL_DEPTH};
use mettail_elab::pres::{ElemId, Presentation, RwEntry};
use mettail_elab::wire::{decode_ddl_value, ParsedDdl, DDL_AST_ENVELOPE_V2};
use proptest::prelude::*;

fn text(value: &str) -> RhoValue {
    RhoValue::String(value.into())
}

fn node(tag: &str, values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
    RhoValue::List(std::iter::once(text(tag)).chain(values).collect())
}

fn ordinary_types() -> BoxedStrategy<RhoValue> {
    prop_oneof![
        any::<u16>().prop_map(|n| text(&format!("T{n}"))),
        prop::sample::select(vec![
            "A",
            "B",
            "Rewrite",
            "Map",
            "PathMap",
            "HashBag",
            "Set",
            "List",
            "Module",
            "Theory",
            "theory",
            "import",
            "from",
            "Empty",
            "free",
            "then",
            "subst",
            "Types",
            "Exports",
            "Replacements",
            "Terms",
            "Equations",
            "Rewrites",
            "Data",
            "Nil",
        ])
        .prop_map(text),
    ]
    .prop_recursive(5, 64, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| node("arrow", [a, b])),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| node("map", [a, b])),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| node("pathmap", [a, b])),
            (prop::sample::select(vec!["multi", "bag", "set", "vec"]), inner)
                .prop_map(|(tag, value)| node(tag, [value])),
        ]
    })
    .boxed()
}

fn context_types() -> BoxedStrategy<RhoValue> {
    let ordinary = ordinary_types();
    prop_oneof![
        ordinary.clone(),
        (prop::collection::vec(ordinary.clone(), 0..4), ordinary).prop_map(|(domains, result)| {
            domains
                .into_iter()
                .rev()
                .fold(node("rewrite", [result]), |result, domain| node("arrow", [domain, result]))
        }),
    ]
    .boxed()
}

fn binding(index: usize, sort: RhoValue) -> RewriteContextBinding {
    RewriteContextBinding::try_new(format!("v{index}"), sort).unwrap()
}

fn presentation(sorts: &[RhoValue]) -> Presentation {
    let span = Span { line: 1, col: 1 };
    let mut result = Presentation::empty();
    result.rewrites.push(RwEntry {
        id: ElemId(1),
        rw: RewriteDecl {
            name: "Step".into(),
            context: sorts
                .iter()
                .cloned()
                .enumerate()
                .map(|(index, sort)| binding(index, sort))
                .collect(),
            premises: Vec::new(),
            lhs: Ast::Var("x".into(), span),
            rhs: Ast::Var("y".into(), span),
            span,
        },
    });
    result
}

fn source(sorts: &[RhoValue]) -> String {
    let bindings = sorts
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, sort)| format!("v{index}:{}", binding(index, sort).render_sort()))
        .collect::<Vec<_>>()
        .join(", ");
    format!("Theory Context() {{ Empty Rewrites {{ Step({bindings}): x ~> y; }} }}")
}

fn theory_rule(theory: &TheoryDecl) -> &RewriteDecl {
    let TheoryExpr::Build { builder: Builder::Rewrites(entries), .. } = &theory.body else {
        panic!("expected actual rewrite builder");
    };
    assert_eq!(entries.len(), 1);
    let RewriteEntry::Ordinary(rule) = &entries[0] else {
        panic!("expected ordinary rewrite");
    };
    rule
}

fn assert_context(rule: &RewriteDecl, sorts: &[RhoValue]) {
    assert_eq!(rule.context.len(), sorts.len());
    for (index, (actual, expected)) in rule.context.iter().zip(sorts).enumerate() {
        assert_eq!(actual.name, format!("v{index}"));
        assert_eq!(actual.sort(), expected);
    }
}

fn wire(sorts: &[RhoValue], premises: Vec<RhoValue>) -> RhoValue {
    node(
        DDL_AST_ENVELOPE_V2,
        [node(
            "theory",
            [
                text("Context"),
                node("sequence", []),
                node(
                    "build",
                    [
                        node("empty", []),
                        node(
                            "rewrites",
                            [node(
                                "sequence",
                                [node(
                                    "rewrite-typed",
                                    [
                                        text("Step"),
                                        node(
                                            "sequence",
                                            sorts.iter().cloned().enumerate().map(
                                                |(index, sort)| {
                                                    node(
                                                        "rewrite-binding",
                                                        [text(&format!("v{index}")), sort],
                                                    )
                                                },
                                            ),
                                        ),
                                        node("sequence", premises),
                                        node("ast-var", [text("x")]),
                                        node("ast-var", [text("y")]),
                                    ],
                                )],
                            )],
                        ),
                    ],
                ),
            ],
        )],
    )
}

fn wire_theory(sorts: &[RhoValue]) -> TheoryDecl {
    let ParsedDdl::Theory(theory) = decode_ddl_value(wire(sorts, Vec::new())).unwrap() else {
        panic!("expected theory");
    };
    theory
}

fn type_at_depth(depth: usize, branch: u8, family: bool) -> RhoValue {
    assert!(depth > usize::from(family));
    let mut value = text("A");
    for _ in 1..depth - usize::from(family) {
        value = match branch {
            0 => node("multi", [value]),
            1 => node("vec", [value]),
            2 => node("arrow", [value, text("B")]),
            3 => node("arrow", [text("B"), value]),
            4 => node("map", [value, text("B")]),
            _ => node("pathmap", [text("B"), value]),
        };
    }
    if family {
        node("rewrite", [value])
    } else {
        value
    }
}

proptest! {
    #[test]
    fn source_names_follow_canonical_validation_without_accepting_quoted_names(
        name in "[A-Za-z_][A-Za-z0-9_]{0,16}",
    ) {
        let expected = RewriteContextBinding::try_new("f".into(), text(&name));
        let input = format!("Theory Context() {{ Empty Rewrites {{ Step(v0:{name}): x ~> y; }} }}");
        let parsed = parse_theory(&input);
        prop_assert_eq!(parsed.is_ok(), expected.is_ok());
        if let Ok(theory) = parsed {
            assert_context(theory_rule(&theory), &[text(&name)]);
        }
        let quoted = format!("Theory Context() {{ Empty Rewrites {{ Step(v0:{name:?}): x ~> y; }} }}");
        prop_assert!(parse_theory(&quoted).is_err());
    }

    #[test]
    fn canonical_context_round_trip_preserves_complete_types_and_order(
        sorts in prop::collection::vec(context_types(), 1..5),
    ) {
        let original = presentation_to_value("Context", &presentation(&sorts)).unwrap();
        let (name, decoded) = value_to_presentation(&original).unwrap();
        prop_assert_eq!(&name, "Context");
        prop_assert_eq!(decoded.rewrites.len(), 1);
        assert_context(&decoded.rewrites[0].rw, &sorts);
        prop_assert_eq!(presentation_to_value(&name, &decoded).unwrap(), original);
    }

    #[test]
    fn rendered_types_parse_without_erasing_wrappers_or_changing_order(
        sorts in prop::collection::vec(context_types(), 1..5),
    ) {
        let parsed = parse_theory(&source(&sorts)).unwrap();
        assert_context(theory_rule(&parsed), &sorts);
    }

    #[test]
    fn wire_contexts_preserve_complete_types_and_order(
        sorts in prop::collection::vec(context_types(), 1..5),
    ) {
        let theory = wire_theory(&sorts);
        assert_context(theory_rule(&theory), &sorts);
    }

    #[test]
    fn source_and_wire_admit_the_same_type_depth(
        depth in 240usize..270,
        branch in 0u8..6,
        family in any::<bool>(),
    ) {
        let sorts = vec![type_at_depth(depth, branch, family)];
        let source_result = parse_theory(&source(&sorts));
        let wire_result = decode_ddl_value(wire(&sorts, Vec::new()));
        prop_assert_eq!(source_result.is_ok(), depth <= MAX_DDL_STRUCTURAL_DEPTH);
        prop_assert_eq!(wire_result.is_ok(), depth <= MAX_DDL_STRUCTURAL_DEPTH);
        if let Err(error) = source_result {
            prop_assert_eq!(error.kind, DiagKind::ResourceLimit);
        }
        if let Err(error) = wire_result {
            prop_assert!(error.path.contains(".context[0].sort"));
            prop_assert!(error.message.contains("nesting exceeds"));
        }
    }

    #[test]
    fn nested_family_markers_are_refused_by_source_and_wire(
        ordinary in ordinary_types(),
        tag in prop::sample::select(vec!["multi", "bag", "set", "vec", "rewrite"]),
    ) {
        let rendered = binding(0, ordinary.clone()).render_sort();
        let invalid = node(tag, [node("rewrite", [ordinary])]);
        prop_assert!(RewriteContextBinding::try_new("f".into(), invalid.clone()).is_err());
        prop_assert!(decode_ddl_value(wire(&[invalid], Vec::new())).is_err());
        let syntax = match tag {
            "multi" => format!("Rewrite({rendered})*"),
            "bag" => format!("HashBag(Rewrite({rendered}))"),
            "set" => format!("Set(Rewrite({rendered}))"),
            "vec" => format!("List(Rewrite({rendered}))"),
            _ => format!("Rewrite(Rewrite({rendered}))"),
        };
        let rejected_source = format!(
            "Theory Context() {{ Empty Rewrites {{ Step(f:{syntax}): x ~> y; }} }}"
        );
        prop_assert!(parse_theory(&rejected_source).is_err());
    }
}

#[test]
fn legacy_wire_contexts_preserve_exact_canonical_payloads() {
    let expected = vec![
        text("A"),
        node("bag", [text("B")]),
        node("set", [text("A")]),
        node("vec", [text("B")]),
        text("A"),
    ];
    let legacy = vec![
        node("sort-category", [text("A")]),
        node("sort-bag", [text("B")]),
        node("sort-set", [text("A")]),
        node("sort-list", [text("B")]),
        node("sort-category", [text("A")]),
    ];
    let theory = wire_theory(&legacy);
    let rule = theory_rule(&theory);
    assert_context(rule, &expected);
    let mut actual = Presentation::empty();
    actual
        .rewrites
        .push(RwEntry { id: ElemId(1), rw: rule.clone() });
    assert_eq!(
        presentation_to_value("Context", &actual).unwrap(),
        presentation_to_value("Context", &presentation(&expected)).unwrap(),
    );
}

#[test]
fn keyword_category_names_and_constructor_names_remain_distinct() {
    for name in [
        "Module",
        "Theory",
        "theory",
        "import",
        "from",
        "Empty",
        "free",
        "then",
        "subst",
        "Types",
        "Exports",
        "Replacements",
        "Terms",
        "Equations",
        "Rewrites",
        "Data",
        "Nil",
        "Rewrite",
        "HashBag",
        "Set",
        "List",
        "Map",
        "PathMap",
    ] {
        let sorts = vec![text(name), node("rewrite", [text(name)])];
        let parsed = parse_theory(&source(&sorts)).unwrap();
        assert_context(theory_rule(&parsed), &sorts);
    }
    for invalid in [
        "\"A\"",
        "as",
        "if",
        "in",
        "let",
        "true",
        "false",
        "Unknown(A)",
        "0",
        "-1",
        "1.5",
        "(",
        ")",
        "{",
        "}",
        ",",
        ";",
        ":",
        ".",
        "*",
        "#",
        "^",
        "|-",
        "=>",
        "~>",
        "<~",
        "<~>",
        "::",
        "->",
        "==",
        "...",
        "=",
        "",
    ] {
        assert!(parse_theory(&format!(
            "Theory Context() {{ Empty Rewrites {{ Step(f:{invalid}): x ~> y; }} }}"
        ))
        .is_err());
    }
}

#[test]
fn postfix_placement_and_binary_argument_order_are_exact() {
    let sorts = vec![
        node("multi", [node("arrow", [text("A"), text("B")])]),
        node("arrow", [text("A"), node("multi", [text("B")])]),
        node("multi", [node("multi", [text("A")])]),
        node("map", [node("set", [text("A")]), node("pathmap", [text("B"), text("C")])]),
    ];
    assert_eq!(binding(0, sorts[0].clone()).render_sort(), "[A -> B]*");
    assert_eq!(binding(1, sorts[1].clone()).render_sort(), "[A -> B*]");
    assert_eq!(binding(2, sorts[2].clone()).render_sort(), "A**");
    let theory = parse_theory(&source(&sorts)).unwrap();
    assert_context(theory_rule(&theory), &sorts);
    assert_context(theory_rule(&wire_theory(&sorts)), &sorts);
}

#[test]
fn exact_source_and_wire_boundaries_cover_every_type_branch() {
    for family in [false, true] {
        for branch in 0..6 {
            for depth in [MAX_DDL_STRUCTURAL_DEPTH, MAX_DDL_STRUCTURAL_DEPTH + 1] {
                let sorts = vec![type_at_depth(depth, branch, family)];
                assert_eq!(
                    parse_theory(&source(&sorts)).is_ok(),
                    depth == MAX_DDL_STRUCTURAL_DEPTH
                );
                assert_eq!(
                    decode_ddl_value(wire(&sorts, Vec::new())).is_ok(),
                    depth == MAX_DDL_STRUCTURAL_DEPTH
                );
                assert_eq!(binding(0, sorts[0].clone()).sort(), &sorts[0]);
            }
        }
    }
}

#[test]
fn intrinsic_outputs_keep_the_existing_ordinary_sort_contract() {
    let intrinsic = |sort| {
        node(
            "premise-intrinsic",
            [
                text("utf8_at_end"),
                node("sequence", [text("x"), text("y")]),
                node("sequence", [node("rewrite-binding", [text("result"), sort])]),
            ],
        )
    };
    assert!(
        decode_ddl_value(wire(&[], vec![intrinsic(node("sort-category", [text("Flag")]))])).is_ok()
    );
    for sort in [node("rewrite", [text("Flag")]), node("arrow", [text("A"), text("B")])] {
        let error = decode_ddl_value(wire(&[], vec![intrinsic(sort)])).unwrap_err();
        assert!(error.path.contains(".outputs[0].sort"));
    }
}

#[test]
fn lexed_literal_kinds_cannot_become_context_type_names() {
    for literal in [
        r#""A""#,
        r#"b"00abFF""#,
        "0",
        "-1",
        "1.5",
        "9223372036854775808n",
        "-3r/4r",
        "1.25p2",
    ] {
        let tokens = mettail_elab::lex::lex(literal).unwrap();
        assert_eq!(tokens.len(), 2, "{literal}");
        let input =
            format!("Theory Context() {{ Empty Rewrites {{ Step(v0:{literal}): x ~> y; }} }}");
        assert!(parse_theory(&input).is_err(), "{literal}");
    }
}

#[test]
fn validated_context_rendering_and_cleanup_are_stack_safe() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let value = type_at_depth(2048, 3, true);
            let context = binding(0, value.clone());
            let rendered = context.render_sort();
            assert!(rendered.starts_with("Rewrite([B -> "));
            assert!(rendered.ends_with(')'));
            assert_eq!(context.sort(), &value);
            assert_eq!(context.clone().sort(), &value);
            assert!(decode_ddl_value(wire(&[value], Vec::new())).is_err());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn wire_depth_admission_precedes_type_validation() {
    for depth in [1, 20, MAX_DDL_STRUCTURAL_DEPTH + 1, 1024] {
        let mut malformed = RhoValue::List(Vec::new());
        for _ in 1..depth {
            malformed = node("vec", [malformed]);
        }
        let error = decode_ddl_value(wire(&[malformed], Vec::new())).unwrap_err();
        assert_eq!(error.message.contains("nesting exceeds"), depth > MAX_DDL_STRUCTURAL_DEPTH);
        assert!(error.path.contains(".context[0].sort"));
    }
}
