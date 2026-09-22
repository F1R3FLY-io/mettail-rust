//! Actual grammar-rule baselines for the original prefix discovery boundary.

use super::*;
use mettail_ast::grammar::{convert_term_context_to_items, rule_fixture, TermParam};
use mettail_ast::language::LangType;
use mettail_ast::types::TypeExpr;
use proc_macro2::Span;
use std::collections::{BTreeMap, HashMap};
use syn::Ident;

fn id(text: &str) -> Ident {
    Ident::new(text, Span::call_site())
}

fn simple(name: &str, cat: &str) -> TermParam {
    TermParam::Simple {
        name: id(name),
        ty: TypeExpr::Base(id(cat)),
    }
}

fn param(name: &str) -> SyntaxExpr {
    SyntaxExpr::Param(id(name))
}

fn lit(text: &str) -> SyntaxExpr {
    SyntaxExpr::Literal(text.into())
}

fn rule(label: &str, cat: &str, params: Vec<TermParam>, syntax: Vec<SyntaxExpr>) -> GrammarRule {
    let (items, bindings) = convert_term_context_to_items(&params);
    GrammarRule {
        items,
        bindings,
        term_context: Some(params),
        syntax_pattern: Some(syntax),
        ..rule_fixture(id(label), id(cat))
    }
}

fn language(terms: Vec<GrammarRule>) -> LanguageDef {
    LanguageDef {
        name: id("PrefixDiscoveryBaseline"),
        options: Default::default(),
        extends_names: vec![],
        include_names: vec![],
        mixin_names: vec![],
        types: ["Other", "Expr"]
            .into_iter()
            .map(|name| LangType {
                name: id(name),
                role: Default::default(),
                native_type: None,
                collection_kind: None,
            })
            .collect(),
        refinement_types: vec![],
        token_defs: vec![],
        mode_defs: vec![],
        sync_constraints: vec![],
        tree_invariants: vec![],
        terms,
        equations: vec![],
        rewrites: vec![],
        logic: None,
        guard_config: None,
    }
}

fn literal_item(text: &str, required_top_cat: Option<u16>) -> SpineItem {
    SpineItem::Literal { text: text.into(), required_top_cat }
}

fn candidate(
    kind: MemberKind,
    rule_idx: u16,
    items: Vec<SpineItem>,
    truncated: bool,
    total_positions: usize,
    body_src_idx: Option<u16>,
) -> CandidateMember {
    CandidateMember {
        kind,
        rule_idx,
        items,
        truncated,
        total_positions,
        body_src_idx,
        mixfix_coords: vec![],
    }
}

#[test]
fn original_prefix_discovery_preserves_atomic_priority_rule_order_and_complete_members() {
    let mut unary = rule("Unary", "Expr", vec![simple("x", "Expr")], vec![lit("~"), param("x")]);
    unary.prefix_bp = Some(17);
    let mut absent = rule("Absent", "Expr", vec![], vec![lit("absent")]);
    absent.term_context = None;
    let mut multi = rule(
        "Call",
        "Expr",
        vec![simple("arg", "Other"), simple("local", "Expr")],
        vec![lit("call"), lit("("), param("arg"), lit(","), param("local"), lit(")")],
    );
    multi.prefix_bp = Some(230);
    let rules = vec![
        rule("ParenUnit", "Expr", vec![], vec![lit("("), lit("unit"), lit(")")]),
        rule(
            "CrossPrefix",
            "Expr",
            vec![simple("x", "Other")],
            vec![lit("cross"), param("x")],
        ),
        unary,
        rule(
            "ParenBinder",
            "Expr",
            vec![simple("x", "Expr")],
            vec![lit("("), param("x"), lit(")")],
        ),
        absent,
        rule(
            "TokenBinder",
            "Expr",
            vec![],
            vec![SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("word")) }],
        ),
        rule("TailKeyword", "Expr", vec![], vec![lit("z"), lit("tail")]),
        rule(
            "Tagged",
            "Expr",
            vec![simple("name", "Ident")],
            vec![lit("tag"), lit("["), param("name"), lit("]")],
        ),
        multi,
        rule("Projection", "Expr", vec![simple("x", "Other")], vec![param("x")]),
    ];
    let language = language(rules.clone());
    assert!(
        matches!(classify_atomic(&rules[0], &language), AtomicShape::NullaryLiteralRun { trigger, .. } if trigger == "(")
    );
    assert!(matches!(
        classify_atomic(&rules[1], &language),
        AtomicShape::CrossCatPrefixUnary { .. }
    ));
    assert!(classify_binder_in(&rules[3], &language).is_some());
    assert!(classify_binder_in(&rules[4], &language).is_none());
    assert!(classify_binder_in(&rules[5], &language).is_some());
    assert!(matches!(
        classify_atomic(&rules[9], &language),
        AtomicShape::CrossCatProjection { .. }
    ));
    let categories = vec!["Other".into(), "Expr".into()];
    let per_cat = vec![vec![], rules];
    let bp = build_prefix_bp_map(&language, &per_cat);
    assert_eq!(bp, HashMap::from([((1, 2), 17)]));
    let actual = discover_members(&language, &categories, 1, &per_cat[1], &bp);
    let expected = vec![
        (
            "(".to_owned(),
            candidate(
                MemberKind::Nullary,
                0,
                vec![literal_item("unit", None), literal_item(")", None)],
                false,
                2,
                None,
            ),
        ),
        (
            "~".to_owned(),
            candidate(
                MemberKind::Binder,
                2,
                vec![SpineItem::ParamParse { cat_src_idx: 1, cur_bp: 17 }],
                false,
                1,
                Some(1),
            ),
        ),
        (
            "z".to_owned(),
            candidate(MemberKind::Nullary, 6, vec![literal_item("tail", None)], false, 1, None),
        ),
        (
            "tag".to_owned(),
            candidate(MemberKind::Binder, 7, vec![literal_item("[", None)], true, 3, Some(1)),
        ),
        (
            "call".to_owned(),
            candidate(
                MemberKind::Binder,
                8,
                vec![
                    literal_item("(", None),
                    SpineItem::ParamParse { cat_src_idx: 0, cur_bp: 0 },
                    literal_item(",", Some(0)),
                    SpineItem::ParamParse { cat_src_idx: 1, cur_bp: 0 },
                    literal_item(")", Some(1)),
                ],
                false,
                5,
                Some(0),
            ),
        ),
    ];
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
}

fn unary(label: &str, cat: &str, explicit: Option<u8>) -> GrammarRule {
    let mut rule = rule(label, cat, vec![simple("x", cat)], vec![lit(label), param("x")]);
    rule.prefix_bp = explicit;
    rule
}

fn infix(label: &str, cat: &str, terminal: &str) -> GrammarRule {
    rule(
        label,
        cat,
        vec![simple("left", cat), simple("right", cat)],
        vec![param("left"), lit(terminal), param("right")],
    )
}

#[test]
fn original_prefix_bp_map_uses_actual_infix_table_shape_eligibility_and_owner_coordinates() {
    let mut cross =
        rule("Cross", "Other", vec![simple("x", "Expr")], vec![lit("cross"), param("x")]);
    cross.prefix_bp = Some(90);
    let mut abstraction = rule(
        "Lambda",
        "Expr",
        vec![TermParam::Abstraction {
            binder: id("x"),
            body: id("body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(id("Other"))),
                codomain: Box::new(TypeExpr::Base(id("Expr"))),
            },
        }],
        vec![lit("lambda"), param("x"), lit("."), param("body")],
    );
    abstraction.prefix_bp = Some(220);
    let mut wrong_name = rule(
        "WrongName",
        "Expr",
        vec![simple("x", "Expr")],
        vec![lit("bad"), param("undeclared")],
    );
    wrong_name.prefix_bp = Some(91);
    let per_cat = vec![
        vec![
            rule("OtherKeyword", "Other", vec![], vec![lit("other")]),
            unary("OtherUnary", "Other", None),
            cross,
        ],
        vec![
            unary("Explicit", "Expr", Some(11)),
            unary("Default", "Expr", None),
            abstraction,
            wrong_name,
        ],
    ];
    let mut terms = per_cat.iter().flatten().cloned().collect::<Vec<_>>();
    terms.extend([
        infix("Add", "Expr", "+"),
        infix("Mul", "Expr", "*"),
        infix("OtherOp", "Other", "&"),
    ]);
    let language = language(terms);
    let table = super::super::infix::build_bp_table(&language);
    let infix_powers: BTreeMap<_, _> = table
        .operators
        .iter()
        .map(|op| (op.label.as_str(), (op.left_bp, op.right_bp)))
        .collect();
    assert_eq!(
        infix_powers,
        BTreeMap::from([("Add", (2, 3)), ("Mul", (4, 5)), ("OtherOp", (2, 3))])
    );
    assert!(classify_binder_in(&per_cat[1][2], &language).is_some());
    assert_eq!(
        build_prefix_bp_map(&language, &per_cat),
        HashMap::from([((0, 1), 5), ((1, 0), 11), ((1, 1), 7),])
    );
}
