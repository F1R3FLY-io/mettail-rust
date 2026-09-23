//! Frozen observations of the original bucket driver's pass schedule.
//! These call the original emitter; they do not implement another classifier.

use super::*;
use mettail_ast::grammar::{rule_fixture, GrammarItem, SyntaxExpr, TermParam};
use mettail_ast::types::TypeExpr;
use proc_macro2::Span;

fn name(text: &str) -> Ident {
    Ident::new(text, Span::call_site())
}

fn language(terms: Vec<GrammarRule>) -> LanguageDef {
    LanguageDef {
        name: name("BucketDriverBaseline"),
        options: Default::default(),
        extends_names: Vec::new(),
        include_names: Vec::new(),
        mixin_names: Vec::new(),
        types: Vec::new(),
        refinement_types: Vec::new(),
        token_defs: Vec::new(),
        mode_defs: Vec::new(),
        sync_constraints: Vec::new(),
        tree_invariants: Vec::new(),
        terms,
        equations: Vec::new(),
        rewrites: Vec::new(),
        logic: None,
        guard_config: None,
    }
}

fn terminal(label: &str, category: &str, text: &str) -> GrammarRule {
    GrammarRule {
        items: vec![GrammarItem::Terminal(text.into())],
        ..rule_fixture(name(label), name(category))
    }
}

fn judgement(
    label: &str,
    category: &str,
    params: &[(&str, &str)],
    syntax: Vec<SyntaxExpr>,
) -> GrammarRule {
    GrammarRule {
        term_context: Some(
            params
                .iter()
                .map(|(param, ty)| TermParam::Simple {
                    name: name(param),
                    ty: TypeExpr::Base(name(ty)),
                })
                .collect(),
        ),
        syntax_pattern: Some(syntax),
        ..rule_fixture(name(label), name(category))
    }
}

fn literal(text: &str) -> SyntaxExpr {
    SyntaxExpr::Literal(text.into())
}

fn param(text: &str) -> SyntaxExpr {
    SyntaxExpr::Param(name(text))
}

fn emit(
    lang: &LanguageDef,
    owner: u16,
    rules: &[(u16, &GrammarRule)],
) -> (
    Vec<TokenStream>,
    TokenStream,
    super::super::fork_emission::ForkEmissionOrdinalModel,
) {
    let mut rows = super::super::fork_emission::ForkEmissionOrdinalModel::new();
    let (arms, helpers) = emit_prefix_arms_for_category(
        lang,
        owner,
        "Expr",
        rules,
        &std::collections::HashMap::new(),
        &std::collections::HashMap::new(),
        &mut rows,
    );
    (arms, helpers, rows)
}

#[test]
fn prefix_bucket_baseline_cross_lhs_binder_atomic_projection_order() {
    let source = terminal("SourceAtom", "Source", "x");
    let infix = judgement(
        "CrossInfix",
        "Expr",
        &[("left", "Source"), ("right", "Source")],
        vec![param("left"), literal("+"), param("right")],
    );
    let atom = terminal("HomeAtom", "Expr", "x");
    let binder = judgement(
        "Wrapped",
        "Expr",
        &[("body", "Expr")],
        vec![literal("x"), param("body"), literal(")")],
    );
    let projection = judgement("Project", "Expr", &[("source", "Source")], vec![param("source")]);
    let lang = language(vec![source, infix, atom.clone(), binder.clone(), projection.clone()]);
    let (arms, helpers, rows) = emit(&lang, 1, &[(0, &atom), (1, &binder), (2, &projection)]);
    assert_eq!(arms.len(), 1, "all four alternatives share the original Fixed(x) key");
    assert_eq!(rows.site2_ordinal(1, 1), Some(1), "global cross-LHS occupies slot zero");
    assert_eq!(rows.site2_ordinal(1, 0), Some(2), "atomic rows flush after binder rows");
    assert_eq!(rows.site2_ordinal(1, 2), Some(3), "projection rows belong to pass two");
    assert!(helpers.to_string().contains("WpdaStepAction :: Fork"));
}

#[test]
fn prefix_bucket_baseline_indexed_roster_and_first_insertion_order() {
    let first = terminal("First", "Expr", "z");
    let second = terminal("Second", "Expr", "a");
    let lang = language(Vec::new());
    let (arms, _, rows) = emit(&lang, 7, &[(31, &first), (4, &second)]);
    assert_eq!(arms.len(), 2, "indexed rules are not replaced with the empty global roster");
    assert!(arms[0].to_string().contains("__kw == \"z\""));
    assert!(arms[1].to_string().contains("__kw == \"a\""));
    assert_eq!(rows.site2_ordinal(7, 31), Some(0));
    assert_eq!(rows.site2_ordinal(7, 4), Some(0));
}

#[test]
fn prefix_bucket_baseline_duplicate_indexed_rules_remain_distinct_branches() {
    let atom = terminal("Repeated", "Expr", "x");
    let (arms, helpers, rows) = emit(&language(Vec::new()), 0, &[(7, &atom), (7, &atom)]);
    assert_eq!(arms.len(), 1);
    assert!(helpers.to_string().contains("WpdaStepAction :: Fork"));
    assert!(
        rows.is_ambiguous_multi_bucket(0, 7),
        "the existing accumulator observes the two different static positions",
    );
    assert_eq!(rows.site2_ordinal(0, 7), None);
}

#[test]
fn prefix_bucket_baseline_parenthesis_exclusion_is_only_for_binders() {
    let nullary = judgement("Empty", "Expr", &[], vec![literal("("), literal(")")]);
    let grouping = judgement(
        "Grouped",
        "Expr",
        &[("body", "Expr")],
        vec![literal("("), param("body"), literal(")")],
    );
    let (arms, _, rows) = emit(&language(Vec::new()), 8, &[(0, &grouping), (1, &nullary)]);
    assert_eq!(arms.len(), 1);
    assert!(arms[0].to_string().contains("__kw == \"(\""));
    assert_eq!(rows.site2_ordinal(8, 0), None);
    assert_eq!(rows.site2_ordinal(8, 1), Some(0));
}

#[test]
fn prefix_bucket_baseline_missing_category_falls_back_or_skips_at_original_sites() {
    let prefix = judgement(
        "CrossPrefix",
        "Expr",
        &[("value", "Missing")],
        vec![literal("prefix"), param("value")],
    );
    let leading = judgement(
        "Leading",
        "Expr",
        &[("left", "Missing"), ("right", "Expr")],
        vec![param("left"), literal(":"), param("right"), literal(";")],
    );
    let (arms, helpers, rows) = emit(&language(Vec::new()), 9, &[(0, &prefix), (1, &leading)]);
    assert_eq!(
        arms.len(),
        1,
        "unresolved leading-category branch must skip rather than fallback"
    );
    assert!(helpers.to_string().contains("source_src_idx : 9u16"));
    assert_eq!(rows.site2_ordinal(9, 0), Some(0));
    assert_eq!(rows.site2_ordinal(9, 1), None);
}
