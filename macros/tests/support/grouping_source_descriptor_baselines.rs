//! Snapshots of the original bounded grouping-source helper, before relocation.
//! These deliberately preserve its actual two-level schedule, not the older
//! transitive-closure prose, and make no parser-completeness assertion.

use super::*;
use mettail_ast::grammar::{rule_fixture, SyntaxExpr, TermParam};
use mettail_ast::types::TypeExpr;
use proc_macro2::Span;

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn language(terms: Vec<GrammarRule>) -> LanguageDef {
    LanguageDef {
        name: ident("GroupingBaseline"),
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

fn categories(names: &[&str]) -> Vec<String> {
    names.iter().map(|name| (*name).to_owned()).collect()
}

fn projection(result: &str, source: &str) -> GrammarRule {
    GrammarRule {
        term_context: Some(vec![TermParam::Simple {
            name: ident("x"),
            ty: TypeExpr::Base(ident(source)),
        }]),
        syntax_pattern: Some(vec![SyntaxExpr::Param(ident("x"))]),
        ..rule_fixture(ident("Projection"), ident(result))
    }
}

fn infix(result: &str, source: &str) -> GrammarRule {
    GrammarRule {
        term_context: Some(vec![
            TermParam::Simple {
                name: ident("left"),
                ty: TypeExpr::Base(ident(source)),
            },
            TermParam::Simple {
                name: ident("right"),
                ty: TypeExpr::Base(ident(source)),
            },
        ]),
        syntax_pattern: Some(vec![
            SyntaxExpr::Param(ident("left")),
            SyntaxExpr::Literal("+".into()),
            SyntaxExpr::Param(ident("right")),
        ]),
        ..rule_fixture(ident("Operator"), ident(result))
    }
}

#[test]
fn original_grouping_sources_expand_only_projection_then_one_infix() {
    let cats = categories(&["R", "P", "Q", "D", "E", "F", "U"]);
    let language =
        language(vec![infix("R", "D"), infix("D", "E"), infix("P", "Q"), infix("Q", "F")]);
    let per_cat = vec![vec![projection("R", "P")], vec![projection("P", "U")]];
    assert_eq!(
        grouping_source_categories_for_result(&cats, &language, &per_cat, 0),
        vec![0, 1, 2, 3]
    );
    // E (infix->infix), F (projection->infix->infix), and U
    // (projection->projection) are intentionally NOT followed.
}

#[test]
fn original_grouping_sources_threshold_counts_distinct_cast_indices() {
    let cats = categories(&["R", "P", "Q", "S", "T", "U"]);
    let language = language(vec![infix("P", "U")]);
    let mut row = vec![projection("R", "P"), projection("R", "Q"), projection("R", "S")];
    row.extend((0..5).map(|_| projection("R", "P")));
    assert_eq!(
        grouping_source_categories_for_result(&cats, &language, &[row.clone()], 0),
        vec![0, 1, 2, 3, 5]
    );
    row.push(projection("R", "T"));
    assert_eq!(
        grouping_source_categories_for_result(&cats, &language, &[row], 0),
        vec![0, 1, 2, 3, 4]
    );
}

#[test]
fn original_grouping_sources_keep_result_first_sorted_tail_and_first_name_position() {
    let cats = categories(&["A", "P", "X", "R", "P"]);
    let language = language(vec![infix("R", "X"), infix("R", "Missing"), infix("R", "R")]);
    let per_cat = vec![vec![], vec![], vec![], vec![projection("R", "P"), projection("R", "P")]];
    assert_eq!(
        grouping_source_categories_for_result(&cats, &language, &per_cat, 3),
        vec![3, 1, 2]
    );
    let mut tail = std::collections::BTreeSet::from([9]);
    grouping_source_infix_hop(&cats, &language, 3, &mut tail);
    assert_eq!(tail.into_iter().collect::<Vec<_>>(), vec![2, 9], "hop extends the existing set");
}

#[test]
fn original_grouping_sources_cycle_can_repeat_the_primary_result() {
    let cats = categories(&["R", "P"]);
    let language = language(vec![infix("P", "R")]);
    let per_cat = vec![vec![projection("R", "P")]];
    assert_eq!(
        grouping_source_categories_for_result(&cats, &language, &per_cat, 0),
        vec![0, 0, 1],
        "the write-only visited set does not suppress a returned primary index"
    );
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn original_grouping_sources_preserve_bnf_normalization_and_missing_row_boundary() {
    let cats = categories(&["R", "P"]);
    let legacy = GrammarRule {
        items: vec![
            GrammarItem::NonTerminal {
                ident: ident("P"),
                kind: NonTerminalKind::Category,
            },
            GrammarItem::Terminal("+".into()),
            GrammarItem::NonTerminal {
                ident: ident("P"),
                kind: NonTerminalKind::Category,
            },
        ],
        ..rule_fixture(ident("LegacyOperator"), ident("R"))
    };
    let language = language(vec![legacy]);
    assert_eq!(grouping_source_categories_for_result(&cats, &language, &[], 0), vec![0, 1]);
    let mut unchanged = std::collections::BTreeSet::from([7]);
    grouping_source_projection_hop(&language, &[], &cats, usize::MAX, &mut unchanged);
    assert_eq!(
        unchanged.into_iter().collect::<Vec<_>>(),
        vec![7],
        "missing row does not index categories"
    );
    grouping_source_categories_for_result(&cats, &language, &[], cats.len());
}

#[test]
fn original_grouping_sources_cast_before_ordering_and_second_hop_lookup() {
    let mut cats = vec![String::new(); usize::from(u16::MAX) + 2];
    cats[0] = "R".into();
    cats[1] = "Q".into();
    cats[usize::from(u16::MAX) + 1] = "P".into();
    let language = language(vec![infix("P", "Q")]);
    let per_cat = vec![vec![projection("R", "P")]];
    assert_eq!(
        grouping_source_categories_for_result(&cats, &language, &per_cat, 0),
        vec![0, 0],
        "65536 casts to zero; the second hop therefore reads R, not P, and does not add Q"
    );
}

#[test]
fn shared_grouping_sources_preserve_original_classifier_callbacks_and_order() {
    use mettail_prattail::wpda_rule_analysis::grouping;
    use std::cell::RefCell;

    let cats = categories(&["R", "P", "Q", "D"]);
    let mut direct = infix("R", "D");
    direct.label = ident("Direct");
    let mut via = infix("P", "Q");
    via.label = ident("Via");
    let mut other = infix("Other", "Q");
    other.label = ident("Other");
    let language = language(vec![direct, via, other]);
    // The original projection hop trusts its row; it does not add the infix
    // hop's rule-category filter. Preserve that distinction in the adapter.
    let mut projected = projection("Other", "P");
    projected.label = ident("Projected");
    let keyword = GrammarRule {
        term_context: Some(vec![]),
        syntax_pattern: Some(vec![SyntaxExpr::Literal("word".into())]),
        ..rule_fixture(ident("Keyword"), ident("R"))
    };
    let mut missing = projection("R", "Missing");
    missing.label = ident("Missing");
    let mut same = projection("R", "R");
    same.label = ident("Same");
    let per_cat = vec![vec![projected, keyword, missing, same]];
    let original_projection_observations: Vec<_> = per_cat[0]
        .iter()
        .map(|rule| match classify_atomic(rule, &language) {
            AtomicShape::CrossCatProjection { source_cat_name, .. } => Some(source_cat_name),
            _ => None,
        })
        .collect();
    assert_eq!(
        original_projection_observations,
        vec![Some("P".into()), None, Some("Missing".into()), None]
    );

    let trace = RefCell::new(Vec::new());
    let actual = grouping::grouping_source_categories_for_result(
        &cats,
        &language.terms,
        &per_cat,
        0,
        |rule| {
            trace.borrow_mut().push(format!("category:{}", rule.label));
            rule.category.to_string()
        },
        |rule| {
            trace.borrow_mut().push(format!("infix:{}", rule.label));
            super::super::infix::classify_rule_public(rule)
        },
        |rule| {
            trace.borrow_mut().push(format!("atomic:{}", rule.label));
            match classify_atomic(rule, &language) {
                AtomicShape::CrossCatProjection { source_cat_name, .. } => Some(source_cat_name),
                _ => None,
            }
        },
    );
    assert_eq!(actual, vec![0, 1, 2, 3]);
    assert_eq!(actual, grouping_source_categories_for_result(&cats, &language, &per_cat, 0));
    assert_eq!(
        trace.into_inner(),
        [
            "category:Direct",
            "infix:Direct",
            "category:Via",
            "category:Other",
            "atomic:Projected",
            "atomic:Keyword",
            "atomic:Missing",
            "atomic:Same",
            "atomic:Projected",
            "atomic:Keyword",
            "atomic:Missing",
            "atomic:Same",
            "category:Direct",
            "category:Via",
            "infix:Via",
            "category:Other",
        ]
    );
}

#[test]
fn shared_grouping_sources_accept_neutral_handles_to_the_same_original_classifiers() {
    use mettail_prattail::wpda_rule_analysis::grouping;

    let cats = categories(&["R", "P", "Q", "D"]);
    let bank = [infix("R", "D"), infix("P", "Q"), projection("R", "P")];
    let language = language(vec![bank[0].clone(), bank[1].clone()]);
    let per_cat = vec![vec![bank[2].clone()]];
    let original = grouping_source_categories_for_result(&cats, &language, &per_cat, 0);
    let handles = [0usize, 1];
    let rows = vec![vec![2usize]];
    let shared = grouping::grouping_source_categories_for_result(
        &cats,
        &handles,
        &rows,
        0,
        |handle| bank[*handle].category.to_string(),
        |handle| super::super::infix::classify_rule_public(&bank[*handle]),
        |handle| match classify_atomic(&bank[*handle], &language) {
            AtomicShape::CrossCatProjection { source_cat_name, .. } => Some(source_cat_name),
            _ => None,
        },
    );
    assert_eq!(shared, original);
    assert_eq!(shared, vec![0, 1, 2, 3]);
}
