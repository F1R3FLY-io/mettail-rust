//! Original home-variable and identifier-summary snapshots before relocation.
//! These freeze the current predicates, including conservative asymmetries;
//! they do not establish that every authored grammar is valid or FIRST-complete.

use super::*;
use mettail_ast::grammar::{rule_fixture, SyntaxExpr};
use mettail_ast::language::{CategoryRole, LangType};
use proc_macro2::Span;

fn ident(text: &str) -> Ident {
    Ident::new(text, Span::call_site())
}

fn category(name: &str, role: CategoryRole) -> LangType {
    LangType {
        name: ident(name),
        role,
        native_type: None,
        collection_kind: None,
    }
}

fn nonterminal(name: &str, kind: NonTerminalKind) -> GrammarItem {
    GrammarItem::NonTerminal { ident: ident(name), kind }
}

fn rule(label: &str, category: &str, items: Vec<GrammarItem>) -> GrammarRule {
    GrammarRule {
        items,
        ..rule_fixture(ident(label), ident(category))
    }
}

#[test]
fn ident_summary_baseline_home_var_requires_first_declaration_and_any_first_var() {
    let mut language = crate::gen::empty_language_for_tests();
    language.terms = vec![rule(
        "OddVar",
        "A",
        vec![
            nonterminal("Different", NonTerminalKind::Var),
            GrammarItem::Terminal("tail".into()),
        ],
    )];
    assert!(
        !result_has_home_var_reading("A", &language),
        "undeclared category refuses before rule scan"
    );
    language.types.push(category("A", CategoryRole::Data));
    assert!(
        result_has_home_var_reading("A", &language),
        "any first legacy Var contributes to this predicate"
    );
    assert!(
        !ident_first_categories(&language).contains("A"),
        "the separate atomic classifier rejects this non-singleton Var rule"
    );
    language.terms.clear();
    language.types.push(category("A", CategoryRole::Object));
    assert!(!result_has_home_var_reading("A", &language), "first declaration wins");
    language.types.swap(0, 1);
    assert!(result_has_home_var_reading("A", &language));
}

#[test]
fn ident_summary_baseline_nonatomic_edge_needs_param_then_legacy_category() {
    let mut language = crate::gen::empty_language_for_tests();
    language.types =
        vec![category("Source", CategoryRole::Object), category("Target", CategoryRole::Data)];
    for syntax in [
        None,
        Some(Vec::new()),
        Some(vec![SyntaxExpr::Literal("x".into())]),
        Some(vec![SyntaxExpr::Param(ident("p"))]),
    ] {
        let should_reach = matches!(syntax.as_deref(), Some([SyntaxExpr::Param(_)]));
        let mut candidate =
            rule("Edge", "Target", vec![nonterminal("Source", NonTerminalKind::Category)]);
        candidate.syntax_pattern = syntax;
        assert!(matches!(classify_atomic(&candidate, &language), AtomicShape::NonAtomic));
        language.terms = vec![candidate];
        let reached = ident_first_categories(&language);
        assert!(reached.contains("Source"));
        assert_eq!(reached.contains("Target"), should_reach);
    }
    language.terms[0].items.clear();
    assert!(
        !ident_first_categories(&language).contains("Target"),
        "binder context is not a replacement for the original legacy edge test"
    );
    language.terms[0].items = vec![nonterminal("Source", NonTerminalKind::Ident)];
    assert!(!ident_first_categories(&language).contains("Target"));
}

#[test]
fn ident_summary_baseline_explicit_var_can_seed_an_undeclared_category() {
    let mut language = crate::gen::empty_language_for_tests();
    language.terms =
        vec![rule("FreeVar", "Undeclared", vec![nonterminal("Name", NonTerminalKind::Var)])];
    assert!(
        !ident_first_categories(&language).contains("Undeclared"),
        "the atomic Var classifier requires the legacy name to match the rule category"
    );
    language.terms[0].items = vec![nonterminal("Undeclared", NonTerminalKind::Var)];
    assert!(ident_first_categories(&language).contains("Undeclared"));
    assert!(!result_has_home_var_reading("Undeclared", &language));
    assert!(source_ident_first_is_var_only("Undeclared", &language));
}

#[test]
fn ident_summary_baseline_var_terminal_and_same_category_skip_entire_suffix() {
    let mut language = crate::gen::empty_language_for_tests();
    language.types =
        vec![category("A", CategoryRole::Data), category("Source", CategoryRole::Object)];
    for first in [
        nonterminal("Other", NonTerminalKind::Var),
        GrammarItem::Terminal("literal".into()),
        nonterminal("A", NonTerminalKind::Category),
    ] {
        language.terms =
            vec![rule("Skip", "A", vec![first, nonterminal("Source", NonTerminalKind::Category)])];
        assert!(source_ident_first_is_var_only("A", &language));
    }
}

#[test]
fn ident_summary_baseline_pure_cycles_and_structural_tails_have_distinct_results() {
    let mut language = crate::gen::empty_language_for_tests();
    language.types = vec![
        category("A", CategoryRole::Data),
        category("B", CategoryRole::Data),
        category("Source", CategoryRole::Object),
    ];
    language.terms = vec![
        rule("AB", "A", vec![nonterminal("B", NonTerminalKind::Category)]),
        rule("BA", "B", vec![nonterminal("A", NonTerminalKind::Category)]),
        rule("BS", "B", vec![nonterminal("Source", NonTerminalKind::Category)]),
    ];
    // These are legacy projection observations, with explicit Param syntax so
    // the original identifier closure includes their reverse edges.
    for candidate in &mut language.terms {
        candidate.syntax_pattern = Some(vec![SyntaxExpr::Param(ident("p"))]);
    }
    assert!(source_ident_first_is_var_only("A", &language));
    language.terms[2]
        .items
        .push(GrammarItem::Terminal("!".into()));
    assert!(!source_ident_first_is_var_only("A", &language));
    language.terms[2].items[1] = nonterminal("Integer", NonTerminalKind::Integer);
    assert!(!source_ident_first_is_var_only("A", &language));
    language.types[2].role = CategoryRole::Data;
    assert!(
        source_ident_first_is_var_only("A", &language),
        "a non-Ident source does not reject even a structural tail"
    );
}

#[test]
fn ident_summary_baseline_conservative_fallback_accepts_only_present_first_literal() {
    let mut language = crate::gen::empty_language_for_tests();
    language.types = vec![category("A", CategoryRole::Data)];
    for syntax in [
        None,
        Some(Vec::new()),
        Some(vec![SyntaxExpr::Param(ident("p"))]),
        Some(vec![SyntaxExpr::Literal("x".into())]),
    ] {
        let expected = matches!(syntax.as_deref(), Some([SyntaxExpr::Literal(_)]));
        let mut candidate =
            rule("Fallback", "A", vec![nonterminal("Integer", NonTerminalKind::Integer)]);
        candidate.syntax_pattern = syntax;
        language.terms = vec![candidate];
        assert_eq!(source_ident_first_is_var_only("A", &language), expected);
    }
}
