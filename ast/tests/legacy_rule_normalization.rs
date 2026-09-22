//! Baselines for the original legacy-rule normalizer, captured before extraction.
//! Fixtures use authored AST constructors; expected outputs are explicit, never
//! obtained by parsing or by reproducing the conversion algorithm.

use mettail_ast::grammar::{
    convert_items_to_term_context, rule_fixture, GrammarItem, GrammarRule, NonTerminalKind,
    PatternOp, SyntaxExpr, TermParam, TierDirective, TierRequest,
};
use mettail_ast::types::{CollectionType, EvalMode, RustCodeBlock, TypeExpr};
use proc_macro2::Span;
use syn::Ident;

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn nonterminal(name: &str) -> GrammarItem {
    GrammarItem::NonTerminal {
        ident: ident(name),
        kind: NonTerminalKind::Category,
    }
}

fn binder(category: &str) -> GrammarItem {
    GrammarItem::Binder { category: ident(category) }
}

fn collection(kind: CollectionType, element: &str, separator: &str) -> GrammarItem {
    GrammarItem::Collection {
        coll_type: kind,
        element_type: ident(element),
        separator: separator.into(),
        delimiters: Some(("[".into(), "]".into())),
    }
}

fn rule(items: Vec<GrammarItem>) -> GrammarRule {
    GrammarRule {
        items,
        bindings: vec![(7, vec![9, 9, 2]), (0, vec![])],
        rust_code: Some(RustCodeBlock {
            code: syn::parse_quote!(captured_value + 1),
        }),
        eval_mode: Some(EvalMode::Step),
        is_right_assoc: true,
        shares_level_with_previous: true,
        prefix_bp: Some(37),
        tier_directive: Some(TierDirective {
            tier: TierRequest::T3,
            bound: Some(17),
            force: true,
        }),
        is_auto_injected: true,
        doc_comment: Some("retained\nmetadata".into()),
        is_canonical_synonym: true,
        ..rule_fixture(ident("LegacyFixture"), ident("Result"))
    }
}

fn assert_retained_fields(actual: &GrammarRule, before: &GrammarRule) {
    assert_eq!(actual.label, before.label);
    assert_eq!(actual.category, before.category);
    assert_eq!(actual.items, before.items);
    assert_eq!(actual.bindings, before.bindings);
    assert_eq!(
        actual.rust_code.as_ref().map(|block| &block.code),
        before.rust_code.as_ref().map(|block| &block.code),
    );
    assert_eq!(actual.eval_mode, before.eval_mode);
    assert_eq!(actual.is_right_assoc, before.is_right_assoc);
    assert_eq!(actual.shares_level_with_previous, before.shares_level_with_previous);
    assert_eq!(actual.prefix_bp, before.prefix_bp);
    assert_eq!(actual.tier_directive, before.tier_directive);
    assert_eq!(actual.is_auto_injected, before.is_auto_injected);
    assert_eq!(actual.doc_comment, before.doc_comment);
    assert_eq!(actual.is_canonical_synonym, before.is_canonical_synonym);
}

fn assert_unchanged(mut rule: GrammarRule) {
    let before = rule.clone();
    let context_allocation = rule.term_context.as_ref().map(|params| params.as_ptr());
    let syntax_allocation = rule.syntax_pattern.as_ref().map(|items| items.as_ptr());
    convert_items_to_term_context(&mut rule);
    assert_retained_fields(&rule, &before);
    // Debug exposes each variant and field of these otherwise non-Eq AST types.
    assert_eq!(format!("{:?}", rule.term_context), format!("{:?}", before.term_context));
    assert_eq!(format!("{:?}", rule.syntax_pattern), format!("{:?}", before.syntax_pattern));
    assert_eq!(rule.term_context.as_ref().map(|params| params.as_ptr()), context_allocation);
    assert_eq!(rule.syntax_pattern.as_ref().map(|items| items.as_ptr()), syntax_allocation);
}

fn normalize(mut rule: GrammarRule) -> GrammarRule {
    let before = rule.clone();
    convert_items_to_term_context(&mut rule);
    assert_retained_fields(&rule, &before);
    assert!(rule.term_context.is_some());
    assert!(rule.syntax_pattern.is_some());
    rule
}

fn assert_base(ty: &TypeExpr, expected: &str) {
    assert!(matches!(ty, TypeExpr::Base(name) if name == expected), "{ty:?}");
}

fn assert_simple(param: &TermParam, expected_name: &str, expected_category: &str) {
    let TermParam::Simple { name, ty } = param else {
        panic!("expected Simple, got {param:?}");
    };
    assert_eq!(name, expected_name);
    assert_base(ty, expected_category);
}

fn assert_abstraction(param: &TermParam, binder: &str, body: &str, from: &str, to: &str) {
    let TermParam::Abstraction {
        binder: actual_binder,
        body: actual_body,
        ty,
    } = param
    else {
        panic!("expected Abstraction, got {param:?}");
    };
    assert_eq!(actual_binder, binder);
    assert_eq!(actual_body, body);
    let TypeExpr::Arrow { domain, codomain } = ty else {
        panic!("expected Arrow, got {ty:?}");
    };
    assert_base(domain, from);
    assert_base(codomain, to);
}

fn assert_collection(param: &TermParam, expected_kind: &CollectionType, expected_element: &str) {
    let TermParam::Simple { name, ty } = param else {
        panic!("expected Simple collection, got {param:?}");
    };
    assert_eq!(name, "elems");
    let TypeExpr::Collection { coll_type, element } = ty else {
        panic!("expected Collection, got {ty:?}");
    };
    assert_eq!(coll_type, expected_kind);
    assert_base(element, expected_element);
}

fn literal(text: &str) -> SyntaxExpr {
    SyntaxExpr::Literal(text.into())
}

fn param(name: &str) -> SyntaxExpr {
    SyntaxExpr::Param(ident(name))
}

fn sep(separator: &str) -> SyntaxExpr {
    SyntaxExpr::Op(PatternOp::Sep {
        collection: ident("elems"),
        separator: separator.into(),
        source: None,
    })
}

fn assert_pattern(rule: &GrammarRule, expected: &[SyntaxExpr]) {
    let actual = rule
        .syntax_pattern
        .as_ref()
        .expect("normalized syntax exists");
    assert_eq!(actual.len(), expected.len());
    for (actual, expected) in actual.iter().zip(expected) {
        match (actual, expected) {
            (SyntaxExpr::Literal(actual), SyntaxExpr::Literal(expected)) => {
                assert_eq!(actual, expected);
            },
            (SyntaxExpr::Param(actual), SyntaxExpr::Param(expected)) => {
                assert_eq!(actual, expected);
            },
            (
                SyntaxExpr::Op(PatternOp::Sep { collection, separator, source }),
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: expected_collection,
                    separator: expected_separator,
                    source: None,
                }),
            ) => {
                assert_eq!(collection, expected_collection);
                assert_eq!(separator, expected_separator);
                assert!(source.is_none());
            },
            _ => panic!("unexpected normalized syntax: {actual:?}; expected {expected:?}"),
        }
    }
}

#[test]
fn either_judgement_field_blocks_conversion_even_when_empty() {
    for context_case in 0..3 {
        for syntax_case in 0..3 {
            if context_case == 0 && syntax_case == 0 {
                continue;
            }
            let mut fixture = rule(vec![nonterminal("WouldConvert")]);
            fixture.term_context = match context_case {
                0 => None,
                1 => Some(vec![]),
                _ => Some(vec![TermParam::GuardBody { name: ident("original_guard") }]),
            };
            fixture.syntax_pattern = match syntax_case {
                0 => None,
                1 => Some(vec![]),
                _ => Some(vec![SyntaxExpr::TokenKind {
                    name: ident("OriginalToken"),
                    bind: Some(ident("original_binding")),
                }]),
            };
            assert_unchanged(fixture);
        }
    }
}

#[test]
fn every_noncategory_kind_refuses_before_committing_any_prefix() {
    for kind in [
        NonTerminalKind::Var,
        NonTerminalKind::Integer,
        NonTerminalKind::Boolean,
        NonTerminalKind::StringLiteral,
        NonTerminalKind::FloatLiteral,
        NonTerminalKind::Ident,
    ] {
        for position in 0..=3 {
            let mut items = vec![nonterminal("First"), binder("Name"), nonterminal("Body")];
            // The explicit kind, not the identifier's spelling, controls refusal.
            items.insert(
                position,
                GrammarItem::NonTerminal { ident: ident("LooksLikeCategory"), kind },
            );
            assert_unchanged(rule(items));
        }
    }
}

#[test]
fn category_discriminants_and_fresh_names_preserve_order_and_duplicates() {
    let normalized = normalize(rule(vec![
        GrammarItem::Terminal("begin".into()),
        nonterminal("Var"),
        nonterminal("Var"),
        binder("Name"),
        nonterminal("Body"),
        nonterminal("Tail"),
        GrammarItem::Terminal("end".into()),
    ]));
    let context = normalized
        .term_context
        .as_ref()
        .expect("normalized context");
    assert_eq!(context.len(), 4);
    assert_simple(&context[0], "p0", "Var");
    assert_simple(&context[1], "p1", "Var");
    assert_abstraction(&context[2], "p2", "p3", "Name", "Body");
    assert_simple(&context[3], "p4", "Tail");
    assert_pattern(
        &normalized,
        &[
            literal("begin"),
            param("p0"),
            param("p1"),
            param("p2"),
            param("p3"),
            param("p4"),
            literal("end"),
        ],
    );
}

#[test]
fn pending_binder_is_last_wins_and_survives_literals_and_collections() {
    let normalized = normalize(rule(vec![
        binder("Discarded"),
        GrammarItem::Terminal("before".into()),
        binder("Retained"),
        GrammarItem::Terminal("between".into()),
        collection(CollectionType::HashBag, "Element", "|"),
        GrammarItem::Terminal("after".into()),
        nonterminal("Body"),
        nonterminal("Tail"),
    ]));
    let context = normalized
        .term_context
        .as_ref()
        .expect("normalized context");
    assert_eq!(context.len(), 3);
    assert_collection(&context[0], &CollectionType::HashBag, "Element");
    assert_abstraction(&context[1], "p0", "p1", "Retained", "Body");
    assert_simple(&context[2], "p2", "Tail");
    assert_pattern(
        &normalized,
        &[
            literal("before"),
            literal("between"),
            literal("["),
            sep("|"),
            literal("]"),
            literal("after"),
            param("p0"),
            param("p1"),
            param("p2"),
        ],
    );
}

#[test]
fn every_collection_kind_keeps_duplicate_elems_without_advancing_fresh_counter() {
    for kind in [
        CollectionType::HashBag,
        CollectionType::HashSet,
        CollectionType::Vec,
        CollectionType::HashMap,
        CollectionType::PathMap,
    ] {
        let normalized = normalize(rule(vec![
            nonterminal("Head"),
            collection(kind.clone(), "FirstElement", ";"),
            nonterminal("Middle"),
            collection(kind.clone(), "SecondElement", ""),
            nonterminal("Tail"),
        ]));
        let context = normalized
            .term_context
            .as_ref()
            .expect("normalized context");
        assert_eq!(context.len(), 5);
        assert_simple(&context[0], "p0", "Head");
        assert_collection(&context[1], &kind, "FirstElement");
        assert_simple(&context[2], "p1", "Middle");
        assert_collection(&context[3], &kind, "SecondElement");
        assert_simple(&context[4], "p2", "Tail");
        assert_pattern(
            &normalized,
            &[
                param("p0"),
                literal("["),
                sep(";"),
                literal("]"),
                param("p1"),
                literal("["),
                sep(""),
                literal("]"),
                param("p2"),
            ],
        );
    }
}

#[test]
fn refusal_after_a_convertible_prefix_leaves_the_entire_rule_unchanged() {
    let undelimited = GrammarItem::Collection {
        coll_type: CollectionType::Vec,
        element_type: ident("Element"),
        separator: ",".into(),
        delimiters: None,
    };
    for suffix in [
        vec![undelimited, nonterminal("AfterMissingDelimiters")],
        vec![binder("Trailing")],
        vec![binder("Trailing"), GrammarItem::Terminal("end".into())],
        vec![binder("Trailing"), collection(CollectionType::Vec, "Element", ",")],
    ] {
        let mut items = vec![nonterminal("AlreadyBuilt"), GrammarItem::Terminal("prefix".into())];
        items.extend(suffix);
        assert_unchanged(rule(items));
    }
}

#[test]
fn empty_pure_literal_and_binder_only_rules_remain_legacy() {
    for items in [
        vec![],
        vec![GrammarItem::Terminal("keyword".into())],
        vec![GrammarItem::Terminal("(".into()), GrammarItem::Terminal(")".into())],
        vec![binder("Name")],
    ] {
        assert_unchanged(rule(items));
    }
}

#[test]
fn collection_without_nonterminals_commits_both_judgement_fields() {
    let normalized = normalize(rule(vec![GrammarItem::Collection {
        coll_type: CollectionType::PathMap,
        element_type: ident("Entry"),
        separator: "::".into(),
        delimiters: Some(("pathmap(".into(), "END".into())),
    }]));
    let context = normalized
        .term_context
        .as_ref()
        .expect("normalized context");
    assert_eq!(context.len(), 1);
    assert_collection(&context[0], &CollectionType::PathMap, "Entry");
    assert_pattern(&normalized, &[literal("pathmap("), sep("::"), literal("END")]);
}
