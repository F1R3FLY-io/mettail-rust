//! A-RT01: Hash-consing applicability analysis.
//!
//! Analyzes a language definition to determine which categories have recursive
//! fields (Box<Self> or Box<OtherCat>) and would benefit from hash-consing.
//! This analysis feeds into the ART01 gate in cost_benefit.rs and emits
//! diagnostic notes when enabled.

#![allow(dead_code)]

use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use crate::ast::language::LanguageDef;
use crate::ast::types::TypeExpr;
use std::collections::{HashMap, HashSet};

/// Analysis result for a single category's hash-consing applicability.
#[derive(Debug, Clone)]
pub struct CategoryRecursion {
    /// Category name.
    pub name: String,
    /// Number of variants with recursive fields (referencing language categories).
    pub recursive_variant_count: usize,
    /// Total number of user-defined variants (excludes auto-generated Var/Lam/Apply).
    pub total_variant_count: usize,
    /// Set of categories referenced recursively (including self).
    pub recursive_refs: HashSet<String>,
}

/// Full hash-consing analysis for a language.
#[derive(Debug, Clone)]
pub struct HashConsingReport {
    /// Per-category recursion analysis.
    pub categories: Vec<CategoryRecursion>,
    /// Categories that are part of mutually-recursive cycles.
    pub mutual_recursion_groups: Vec<Vec<String>>,
    /// Overall recommendation: true if any category benefits from hash-consing.
    pub recommended: bool,
}

/// Analyze a language definition for hash-consing applicability.
///
/// Examines each category's grammar rules to find recursive fields
/// (parameters whose types reference other categories in the language).
/// Categories with recursive variants benefit from hash-consing because:
/// - Subterms are frequently shared (e.g., `PPar(a, a)`)
/// - Equality checks are O(1) with pointer comparison vs O(depth) structural
pub fn analyze_hash_consing(language: &LanguageDef) -> HashConsingReport {
    let all_categories: HashSet<String> = language
        .types
        .iter()
        .map(|t| t.name.to_string())
        .collect();

    // Group rules by category
    let mut rules_by_cat: HashMap<String, Vec<&GrammarRule>> = HashMap::new();
    for rule in &language.terms {
        let cat = rule.category.to_string();
        rules_by_cat.entry(cat).or_default().push(rule);
    }

    let mut categories = Vec::new();
    let mut ref_graph: HashMap<String, HashSet<String>> = HashMap::new();

    for lang_type in &language.types {
        let cat_name = lang_type.name.to_string();
        let rules = rules_by_cat.get(&cat_name).map(|v| v.as_slice()).unwrap_or(&[]);

        let mut recursive_refs = HashSet::new();
        let mut recursive_variant_count = 0;

        for rule in rules {
            let refs = collect_category_refs(rule, &all_categories);
            if !refs.is_empty() {
                recursive_variant_count += 1;
                recursive_refs.extend(refs);
            }
        }

        ref_graph.insert(cat_name.clone(), recursive_refs.clone());

        categories.push(CategoryRecursion {
            name: cat_name,
            recursive_variant_count,
            total_variant_count: rules.len(),
            recursive_refs,
        });
    }

    // Find mutually-recursive groups via SCC (Kosaraju's algorithm)
    let mutual_recursion_groups = find_mutual_recursion(&ref_graph);

    let recommended = categories.iter().any(|c| c.recursive_variant_count > 0);

    HashConsingReport {
        categories,
        mutual_recursion_groups,
        recommended,
    }
}

/// Collect all category references from a grammar rule's items or term context.
fn collect_category_refs(rule: &GrammarRule, categories: &HashSet<String>) -> HashSet<String> {
    let mut refs = HashSet::new();

    // Check new-syntax (term_context)
    if let Some(term_context) = &rule.term_context {
        for param in term_context {
            match param {
                TermParam::Simple { ty, .. } => {
                    collect_type_category_refs(ty, categories, &mut refs);
                }
                TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
                    collect_type_category_refs(ty, categories, &mut refs);
                }
                TermParam::GuardBody { .. } => {
                    // Guard bodies carry no category references.
                }
            }
        }
    }

    // Check old-syntax (items)
    for item in &rule.items {
        match item {
            GrammarItem::NonTerminal(nt) => {
                let name = nt.to_string();
                if categories.contains(&name) {
                    refs.insert(name);
                }
            }
            GrammarItem::Collection { element_type, .. } => {
                let name = element_type.to_string();
                if categories.contains(&name) {
                    refs.insert(name);
                }
            }
            GrammarItem::Binder { category } => {
                let name = category.to_string();
                if categories.contains(&name) {
                    refs.insert(name);
                }
            }
            GrammarItem::Terminal(_) => {}
        }
    }

    refs
}

/// Collect category references from a type expression.
fn collect_type_category_refs(
    ty: &TypeExpr,
    categories: &HashSet<String>,
    refs: &mut HashSet<String>,
) {
    match ty {
        TypeExpr::Base(ident) => {
            let name = ident.to_string();
            if categories.contains(&name) {
                refs.insert(name);
            }
        }
        TypeExpr::Arrow { domain, codomain } => {
            collect_type_category_refs(domain, categories, refs);
            collect_type_category_refs(codomain, categories, refs);
        }
        TypeExpr::MultiBinder(inner) => {
            collect_type_category_refs(inner, categories, refs);
        }
        TypeExpr::Collection { element, .. } => {
            collect_type_category_refs(element, categories, refs);
        }
        TypeExpr::Refined { base, .. } => {
            collect_type_category_refs(base, categories, refs);
        }
    }
}

/// Find mutually-recursive groups (strongly connected components) in the
/// category reference graph using Kosaraju's algorithm.
fn find_mutual_recursion(graph: &HashMap<String, HashSet<String>>) -> Vec<Vec<String>> {
    let nodes: Vec<&String> = graph.keys().collect();
    let mut visited = HashSet::new();
    let mut order = Vec::new();

    // Pass 1: DFS to compute finish order
    for node in &nodes {
        if !visited.contains(*node) {
            dfs_forward(node, graph, &mut visited, &mut order);
        }
    }

    // Build reverse graph
    let mut rev_graph: HashMap<String, HashSet<String>> = HashMap::new();
    for (from, tos) in graph {
        for to in tos {
            rev_graph.entry(to.clone()).or_default().insert(from.clone());
        }
        rev_graph.entry(from.clone()).or_default();
    }

    // Pass 2: DFS on reverse graph in reverse finish order
    visited.clear();
    let mut groups = Vec::new();
    for node in order.iter().rev() {
        if !visited.contains(node) {
            let mut component = Vec::new();
            dfs_reverse(node, &rev_graph, &mut visited, &mut component);
            // Only report groups with mutual recursion (size > 1 or self-referencing)
            if component.len() > 1
                || graph
                    .get(&component[0])
                    .is_some_and(|refs| refs.contains(&component[0]))
            {
                component.sort();
                groups.push(component);
            }
        }
    }

    groups
}

fn dfs_forward(
    node: &str,
    graph: &HashMap<String, HashSet<String>>,
    visited: &mut HashSet<String>,
    order: &mut Vec<String>,
) {
    if !visited.insert(node.to_string()) {
        return;
    }
    if let Some(neighbors) = graph.get(node) {
        for neighbor in neighbors {
            dfs_forward(neighbor, graph, visited, order);
        }
    }
    order.push(node.to_string());
}

fn dfs_reverse(
    node: &str,
    graph: &HashMap<String, HashSet<String>>,
    visited: &mut HashSet<String>,
    component: &mut Vec<String>,
) {
    if !visited.insert(node.to_string()) {
        return;
    }
    component.push(node.to_string());
    if let Some(neighbors) = graph.get(node) {
        for neighbor in neighbors {
            dfs_reverse(neighbor, graph, visited, component);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_mutual_recursion_self_ref() {
        let mut graph = HashMap::new();
        let mut proc_refs = HashSet::new();
        proc_refs.insert("Proc".to_string());
        proc_refs.insert("Name".to_string());
        graph.insert("Proc".to_string(), proc_refs);

        let mut name_refs = HashSet::new();
        name_refs.insert("Proc".to_string());
        graph.insert("Name".to_string(), name_refs);

        graph.insert("Int".to_string(), HashSet::new());

        let groups = find_mutual_recursion(&graph);
        // Proc and Name are mutually recursive, Int is not
        assert_eq!(groups.len(), 1);
        assert!(groups[0].contains(&"Proc".to_string()));
        assert!(groups[0].contains(&"Name".to_string()));
    }

    #[test]
    fn test_find_mutual_recursion_none() {
        let mut graph = HashMap::new();
        graph.insert("Int".to_string(), HashSet::new());
        graph.insert("Bool".to_string(), HashSet::new());

        let groups = find_mutual_recursion(&graph);
        assert!(groups.is_empty());
    }

    #[test]
    fn test_find_mutual_recursion_self_only() {
        let mut graph = HashMap::new();
        let mut proc_refs = HashSet::new();
        proc_refs.insert("Proc".to_string());
        graph.insert("Proc".to_string(), proc_refs);
        graph.insert("Int".to_string(), HashSet::new());

        let groups = find_mutual_recursion(&graph);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0], vec!["Proc".to_string()]);
    }

    #[test]
    fn test_category_recursion_report() {
        let report = HashConsingReport {
            categories: vec![
                CategoryRecursion {
                    name: "Proc".to_string(),
                    recursive_variant_count: 5,
                    total_variant_count: 12,
                    recursive_refs: {
                        let mut s = HashSet::new();
                        s.insert("Proc".to_string());
                        s.insert("Name".to_string());
                        s
                    },
                },
                CategoryRecursion {
                    name: "Int".to_string(),
                    recursive_variant_count: 0,
                    total_variant_count: 3,
                    recursive_refs: HashSet::new(),
                },
            ],
            mutual_recursion_groups: vec![vec!["Name".to_string(), "Proc".to_string()]],
            recommended: true,
        };

        assert!(report.recommended);
        assert_eq!(report.categories[0].recursive_variant_count, 5);
        assert_eq!(report.categories[1].recursive_variant_count, 0);
        assert_eq!(report.mutual_recursion_groups.len(), 1);
    }
}
