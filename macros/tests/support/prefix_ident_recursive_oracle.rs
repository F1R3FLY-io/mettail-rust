use super::*;
use mettail_ast::grammar::{rule_fixture, GrammarItem, NonTerminalKind};
use mettail_ast::language::LangType;
use proc_macro2::Span;
use syn::Ident;

fn recursive_var_only(
    category: &str,
    language: &LanguageDef,
    visited: &mut std::collections::HashSet<String>,
) -> bool {
    if !visited.insert(category.to_string()) {
        return true;
    }
    for rule in &language.terms {
        if rule.category != category {
            continue;
        }
        if matches!(
            rule.items.first(),
            Some(GrammarItem::NonTerminal { kind: NonTerminalKind::Var, .. })
        ) {
            continue;
        }
        match rule.items.first() {
            Some(GrammarItem::Terminal(_)) => continue,
            Some(GrammarItem::NonTerminal { ident, kind: NonTerminalKind::Category }) => {
                let next = ident.to_string();
                if next == category {
                    continue;
                }
                let structural_items = rule
                    .items
                    .iter()
                    .filter(|item| !matches!(item, GrammarItem::Terminal(_)))
                    .count();
                let pure_projection = structural_items == 1
                    && rule.items.iter().all(|item| {
                        matches!(
                            item,
                            GrammarItem::NonTerminal { kind: NonTerminalKind::Category, .. }
                                | GrammarItem::Terminal(_)
                        )
                    })
                    && rule
                        .items
                        .iter()
                        .all(|item| !matches!(item, GrammarItem::Terminal(_)));
                let next_has_ident = first_set_of_category(&next, language).iter().any(|token| {
                    token.pattern.to_string().contains("Ident") && token.extra_guard.is_none()
                });
                if next_has_ident
                    && !(pure_projection && recursive_var_only(&next, language, visited))
                {
                    return false;
                }
            },
            Some(GrammarItem::NonTerminal { kind: NonTerminalKind::Var, .. }) => {},
            _ => {
                if !matches!(
                    rule.syntax_pattern
                        .as_ref()
                        .and_then(|pattern| pattern.first()),
                    Some(mettail_ast::grammar::SyntaxExpr::Literal(_))
                ) {
                    return false;
                }
            },
        }
    }
    true
}

#[test]
fn iterative_var_only_analysis_matches_recursive_equation_and_first_sets_on_corpus() {
    for bundled in crate::gen::capture::bundled_corpus::bundled_languages() {
        let language = &bundled.def;
        let ident_first = ident_first_categories(language);
        for ty in &language.types {
            let category = ty.name.to_string();
            let expected_first = first_set_of_category(&category, language)
                .iter()
                .any(|token| {
                    token.pattern.to_string().contains("Ident") && token.extra_guard.is_none()
                });
            assert_eq!(
                ident_first.contains(&category),
                expected_first,
                "boolean FIRST projection moved for {}::{category}",
                bundled.tag
            );

            let mut visited = std::collections::HashSet::new();
            assert_eq!(
                source_ident_first_is_var_only(&category, language),
                recursive_var_only(&category, language, &mut visited),
                "var-only classification moved for {}::{category}",
                bundled.tag
            );
        }
    }
}

#[test]
fn iterative_var_only_analysis_handles_20k_projection_depth_on_a_256k_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut language = crate::gen::empty_language_for_tests();
            language.name = Ident::new("DeepProjection", Span::call_site());
            for depth in 0..20_000 {
                let category = Ident::new(&format!("C{depth}"), Span::call_site());
                language.types.push(LangType {
                    name: category.clone(),
                    role: Default::default(),
                    native_type: None,
                    collection_kind: None,
                });
                if depth + 1 < 20_000 {
                    let next = Ident::new(&format!("C{}", depth + 1), Span::call_site());
                    language.terms.push(mettail_ast::grammar::GrammarRule {
                        items: vec![GrammarItem::NonTerminal {
                            ident: next,
                            kind: NonTerminalKind::Category,
                        }],
                        ..rule_fixture(
                            Ident::new(&format!("Cast{depth}"), Span::call_site()),
                            category,
                        )
                    });
                }
            }
            assert!(source_ident_first_is_var_only("C0", &language));
        })
        .expect("spawn low-stack var-only FIRST-analysis gate")
        .join()
        .expect("var-only FIRST analysis must not consume category-depth native stack");
}
