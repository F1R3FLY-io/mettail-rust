use super::*;
use crate::rholang_ast::constructed_value::ConstructedValue;
use mettail_elab::ast::{Builder, RewriteEntry, TheoryDecl, TheoryExpr};
use mettail_elab::canonical::RhoValue;
use mettail_elab::wire::{decode_ddl_value, ParsedDdl};
use mettail_languages::rholang::{lex_dag, DdlRewriteContextType};
use mettail_prattail::automata::TokenKind;
use proptest::prelude::*;
use prost::Message;
use std::sync::Arc;

fn text(value: &str) -> RhoValue {
    RhoValue::String(value.into())
}

fn node(tag: &str, children: impl IntoIterator<Item = RhoValue>) -> RhoValue {
    RhoValue::List(std::iter::once(text(tag)).chain(children).collect())
}

fn body_source(types: &[String]) -> String {
    let context = types
        .iter()
        .enumerate()
        .map(|(index, ty)| format!("v{index}:{ty}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!("Empty Rewrites {{ Step({context}): x ~> y; }}")
}

fn plan_for(body: &DdlTheoryExpr) -> DdlLowerPlan<'_> {
    DdlLowerPlan::build(DdlRoot::Theory { name: "Context", parameters: &[], body })
}

fn wire_for(body: &DdlTheoryExpr) -> RhoValue {
    plan_for(body)
        .try_finish_with(Vec::new(), &mut |_, _| Ok(()))
        .unwrap()
}

fn context(theory: &TheoryDecl) -> Vec<(String, RhoValue)> {
    let TheoryExpr::Build { builder: Builder::Rewrites(entries), .. } = &theory.body else {
        panic!("expected rewrite builder");
    };
    assert_eq!(entries.len(), 1);
    let RewriteEntry::Ordinary(rule) = &entries[0] else {
        panic!("expected ordinary rewrite");
    };
    rule.context
        .iter()
        .map(|entry| (entry.name.clone(), entry.sort().clone()))
        .collect()
}

fn decoded(wire: RhoValue) -> TheoryDecl {
    let ParsedDdl::Theory(theory) = decode_ddl_value(wire).unwrap() else {
        panic!("expected theory wire");
    };
    theory
}

fn verify_types(types: &[(String, RhoValue)]) {
    let source = body_source(
        &types
            .iter()
            .map(|(source, _)| source.clone())
            .collect::<Vec<_>>(),
    );
    let body = DdlTheoryExpr::parse_via_wpda(&source)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert_eq!(DdlTheoryExpr::parse_via_wpda(&body.to_string()).unwrap(), body);
    let expected: Vec<_> = types
        .iter()
        .enumerate()
        .map(|(index, (_, value))| (format!("v{index}"), value.clone()))
        .collect();
    assert_eq!(context(&decoded(wire_for(&body))), expected);
    let standalone =
        mettail_elab::parse::parse_theory(&format!("Theory Context() {{ {source} }}")).unwrap();
    assert_eq!(context(&standalone), expected);
    let original = plan_for(&body).finish(Vec::new()).unwrap();
    let measured: ConstructedValue = plan_for(&body)
        .try_finish_with(Vec::new(), &mut |_, _| Ok(()))
        .unwrap();
    assert_eq!(measured.par.encode_to_vec(), original.encode_to_vec());
    assert!(measured.par.locally_free.is_empty());
    assert!(!measured.par.connective_used);
    assert_eq!(measured.receipt.outer_metadata_bytes, 0);
}

fn ordinary_types() -> BoxedStrategy<(String, RhoValue)> {
    prop_oneof![
        "Context[A-Za-z0-9_]{0,10}".prop_map(|name| (name.clone(), text(&name))),
        prop::sample::select(vec![
            "Map", "Nil", "new", "contract", "HashBag", "Set", "List", "PathMap", "Rewrite",
            "Types", "then"
        ])
        .prop_map(|name| (name.to_string(), text(name))),
    ]
    .prop_recursive(3, 12, 2, |inner| {
        prop_oneof![
            (
                prop::sample::select(vec![("HashBag", "bag"), ("Set", "set"), ("List", "vec")]),
                inner.clone()
            )
                .prop_map(|((name, tag), (source, value))| (
                    format!("{name}({source})"),
                    node(tag, [value])
                )),
            inner
                .clone()
                .prop_map(|(source, value)| (format!("{source}*"), node("multi", [value]))),
            (inner.clone(), inner.clone()).prop_map(|((left, a), (right, b))| (
                format!("[{left} -> {right}]"),
                node("arrow", [a, b])
            )),
            (
                prop::sample::select(vec![("Map", "map"), ("PathMap", "pathmap")]),
                inner.clone(),
                inner
            )
                .prop_map(|((name, tag), (left, a), (right, b))| (
                    format!("{name}({left}, {right})"),
                    node(tag, [a, b])
                )),
        ]
    })
    .boxed()
}

fn context_types() -> BoxedStrategy<(String, RhoValue)> {
    let ordinary = ordinary_types();
    prop_oneof![
        ordinary.clone(),
        (prop::collection::vec(ordinary.clone(), 0..3), ordinary).prop_map(
            |(domains, (source, value))| {
                domains.into_iter().rev().fold(
                    (format!("Rewrite({source})"), node("rewrite", [value])),
                    |(codomain, result), (domain, input)| {
                        (format!("[{domain} -> {codomain}]"), node("arrow", [input, result]))
                    },
                )
            }
        )
    ]
    .boxed()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn generated_context_transport_preserves_complete_ordered_types(types in prop::collection::vec(context_types(), 1..3)) {
        verify_types(&types);
    }

    #[test]
    fn named_type_capture_preserves_complete_spelling(name in "Context[A-Za-z0-9_]{0,20}") {
        let parsed = DdlRewriteContextType::parse_via_wpda(&name).unwrap();
        prop_assert!(matches!(&parsed, DdlRewriteContextType::DdlRewriteContextCategory(actual) if actual == &name));
        let dag = lex_dag(&name).unwrap();
        prop_assert_eq!(&dag.nodes[0].edges[0].kind, &TokenKind::Ident);
        prop_assert!(dag.nodes[0].edges.iter().any(|edge| edge.kind == TokenKind::Custom("DdlContextName".into())));
    }
}

#[test]
fn all_context_constructor_words_keep_bare_and_applied_readings() {
    for (word, tag, binary) in [
        ("HashBag", "bag", false),
        ("Set", "set", false),
        ("List", "vec", false),
        ("Map", "map", true),
        ("PathMap", "pathmap", true),
        ("Rewrite", "rewrite", false),
    ] {
        verify_types(&[(word.to_string(), text(word))]);
        let (source, value) = if binary {
            (format!("{word}(A, B)"), node(tag, [text("A"), text("B")]))
        } else {
            (format!("{word}(A)"), node(tag, [text("A")]))
        };
        verify_types(&[(source, value)]);
        let dag = lex_dag(word).unwrap();
        let custom: Vec<_> = dag.nodes[0]
            .edges
            .iter()
            .filter_map(|edge| match &edge.kind {
                TokenKind::Custom(name) => Some(name.as_str()),
                _ => None,
            })
            .collect();
        let mut expected = vec!["DdlContextName".to_string(), format!("DdlContext{word}")];
        expected.sort();
        assert_eq!(custom, expected);
        let mut all_expected = match word {
            "Map" => vec![TokenKind::Fixed(word.into())],
            "PathMap" | "Rewrite" => vec![TokenKind::Ident],
            _ => vec![TokenKind::Fixed(word.into()), TokenKind::Ident],
        };
        all_expected.extend(expected.into_iter().map(TokenKind::Custom));
        let actual: Vec<_> = dag.nodes[0]
            .edges
            .iter()
            .map(|edge| edge.kind.clone())
            .collect();
        assert_eq!(actual, all_expected);
    }
}

#[test]
fn context_tokens_preserve_existing_host_primary_and_reservation() {
    for name in ["Map", "Nil", "new"] {
        let dag = lex_dag(name).unwrap();
        assert_eq!(dag.nodes[0].edges[0].kind, TokenKind::Fixed(name.into()));
        assert!(!dag.nodes[0]
            .edges
            .iter()
            .any(|edge| edge.kind == TokenKind::Ident));
        assert!(dag.nodes[0]
            .edges
            .iter()
            .any(|edge| edge.kind == TokenKind::Custom("DdlContextName".into())));
        verify_types(&[(name.to_string(), text(name))]);
    }
    for name in ["Rewrite", "PathMap", "MapValue_12", "A_0", "contract"] {
        let dag = lex_dag(name).unwrap();
        assert_eq!(dag.nodes[0].edges[0].kind, TokenKind::Ident);
        assert!(dag.nodes[0]
            .edges
            .iter()
            .any(|edge| edge.kind == TokenKind::Custom("DdlContextName".into())));
        verify_types(&[(name.to_string(), text(name))]);
        assert!(matches!(Proc::parse_via_wpda(name).unwrap(), Proc::PVar(_)));
    }
    assert!(matches!(Proc::parse_via_wpda("Nil").unwrap(), Proc::PZero));
    for source in ["Map()", "Pathmap()", "new x in { x }"] {
        assert!(Proc::parse_via_wpda(source).is_ok(), "{source}");
    }
    for source in ["Map", "new"] {
        assert!(Proc::parse_via_wpda(source).is_err(), "{source}");
    }
}

#[test]
fn context_postfix_and_binary_positions_remain_distinct() {
    verify_types(&[
        ("A**".into(), node("multi", [node("multi", [text("A")])])),
        ("[A -> B]*".into(), node("multi", [node("arrow", [text("A"), text("B")])])),
        ("[A -> B*]".into(), node("arrow", [text("A"), node("multi", [text("B")])])),
        (
            "[Map(A, B) -> Rewrite(PathMap(B, A))]".into(),
            node(
                "arrow",
                [
                    node("map", [text("A"), text("B")]),
                    node("rewrite", [node("pathmap", [text("B"), text("A")])]),
                ],
            ),
        ),
    ]);
}

fn expected_wire(sorts: impl IntoIterator<Item = RhoValue>) -> RhoValue {
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
                                            sorts.into_iter().enumerate().map(|(index, sort)| {
                                                node(
                                                    "rewrite-binding",
                                                    [text(&format!("v{index}")), sort],
                                                )
                                            }),
                                        ),
                                        node("sequence", []),
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

#[test]
fn generated_context_wire_keeps_exact_legacy_payloads() {
    let source = body_source(&["A".into(), "HashBag(B)".into(), "Set(C)".into(), "List(D)".into()]);
    let body = DdlTheoryExpr::parse_via_wpda(&source).unwrap();
    let sorts = [
        node("sort-category", [text("A")]),
        node("sort-bag", [text("B")]),
        node("sort-set", [text("C")]),
        node("sort-list", [text("D")]),
    ];
    let expected = expected_wire(sorts);
    assert_eq!(wire_for(&body), expected);
}

#[test]
fn generated_context_wire_keeps_existing_validation_boundaries() {
    for sort in [
        "[Rewrite(A) -> B]",
        "List(Rewrite(A))",
        "Rewrite(Rewrite(A))",
        "Rewrite(A)*",
        "Map(A, Rewrite(B))",
        "fn",
        "Self",
    ] {
        let source = body_source(&[sort.into()]);
        let body = DdlTheoryExpr::parse_via_wpda(&source).unwrap();
        assert!(decode_ddl_value(wire_for(&body)).is_err(), "{sort}");
    }
    for sort in ["\"A\"", "42", "A-B", "Map(A)", "List(A, B)"] {
        assert!(DdlRewriteContextType::parse_via_wpda(sort).is_err(), "{sort}");
    }
    for output in ["Rewrite(A)", "[A -> B]", "Map(A, B)"] {
        let source = format!("Step: if intrinsic op(x) => (y:{output}) then x ~> y;");
        assert!(DdlRewrite::parse_via_wpda(&source).is_err(), "{output}");
    }
}

fn body_with_type(sort: DdlRewriteContextType) -> DdlTheoryExpr {
    DdlTheoryExpr::DdlTheoryRewrites(
        Arc::new(DdlTheoryExpr::DdlTheoryEmpty),
        vec![DdlRewrite::DdlRewriteTypedDirect(
            "Step".into(),
            vec![DdlRewriteContextBinding::DdlRewriteContextBinding("v0".into(), Arc::new(sort))],
            Arc::new(DdlRuleAst::DdlRuleAstVar("x".into())),
            Arc::new(DdlRuleAst::DdlRuleAstVar("y".into())),
        )],
    )
}

#[test]
fn generated_context_lowering_keeps_wire_depth_admission() {
    for depth in [256, 257] {
        let mut sort = DdlRewriteContextType::DdlRewriteContextCategory("A".into());
        for _ in 1..depth {
            sort = DdlRewriteContextType::DdlRewriteContextList("List".into(), Arc::new(sort));
        }
        let body = body_with_type(sort);
        assert_eq!(decode_ddl_value(wire_for(&body)).is_ok(), depth == 256);
    }
}

#[test]
fn context_build_and_finish_refuse_at_every_paid_cut() {
    for source in ["HashBag(A)", "HashBag(List(A))", "[Map(A, B) -> Rewrite(PathMap(B, A))]"] {
        let body = DdlTheoryExpr::parse_via_wpda(&body_source(&[source.into()])).unwrap();
        let mut trace = Vec::new();
        let root = || DdlRoot::Theory {
            name: "Context",
            parameters: &[],
            body: &body,
        };
        let plan = DdlLowerPlan::try_build(root(), &mut |w, u| {
            trace.push((w, u));
            Ok(())
        })
        .unwrap();
        let _: ConstructedValue = plan
            .try_finish_with(Vec::new(), &mut |w, u| {
                trace.push((w, u));
                Ok(())
            })
            .unwrap();
        for cut in 0..trace.len() {
            let mut seen = Vec::new();
            let mut reserve = |w, u| {
                seen.push((w, u));
                if seen.len() == cut + 1 {
                    Err(RholangAstLowerError::PreparationSizeOverflow)
                } else {
                    Ok(())
                }
            };
            let result = DdlLowerPlan::try_build(root(), &mut reserve).and_then(|plan| {
                plan.try_finish_with::<ConstructedValue>(Vec::new(), &mut reserve)
            });
            assert_eq!(result.err(), Some(RholangAstLowerError::PreparationSizeOverflow));
            assert_eq!(seen, trace[..=cut]);
        }
    }
}

#[test]
fn nested_legacy_context_tags_are_refused_in_every_canonical_child_position() {
    for legacy_tag in ["sort-category", "sort-bag", "sort-set", "sort-list"] {
        let legacy = node(legacy_tag, [text("A")]);
        for tag in ["multi", "bag", "set", "vec", "rewrite"] {
            let wire = expected_wire([node(tag, [legacy.clone()])]);
            assert!(decode_ddl_value(wire).is_err(), "{tag}: {legacy_tag}");
        }
        for tag in ["arrow", "map", "pathmap"] {
            for children in [[legacy.clone(), text("B")], [text("B"), legacy.clone()]] {
                let wire = expected_wire([node(tag, children)]);
                assert!(decode_ddl_value(wire).is_err(), "{tag}: {legacy_tag}");
            }
        }
    }
}
