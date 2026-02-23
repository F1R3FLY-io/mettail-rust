//! Shared helpers for Ascent Datalog code generation.
//!
//! This module provides common utilities used across multiple logic
//! generation modules, reducing duplication and ensuring consistency.

use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use crate::ast::language::LanguageDef;
use crate::ast::types::TypeExpr;
use crate::gen::{generate_literal_label, is_literal_rule};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{BTreeMap, BTreeSet};
use syn::Ident;

/// Pre-computed relation names for a category.
///
/// Avoids repeated `format_ident!("{}", category.to_string().to_lowercase())` calls
/// throughout the codebase.
pub struct RelationNames {
    /// Category type (e.g., `Int`)
    pub cat: Ident,
    /// Lowercase category relation (e.g., `int`)
    pub cat_lower: Ident,
    /// Rewrite relation (e.g., `rw_int`)
    pub rw_rel: Ident,
    /// Equality relation (e.g., `eq_int`)
    pub eq_rel: Ident,
    /// Fold relation (e.g., `fold_int`)
    pub fold_rel: Ident,
}

/// Compute all relation names for a category identifier.
pub fn relation_names(category: &Ident) -> RelationNames {
    let lower = category.to_string().to_lowercase();
    RelationNames {
        cat: category.clone(),
        cat_lower: format_ident!("{}", lower),
        rw_rel: format_ident!("rw_{}", lower),
        eq_rel: format_ident!("eq_{}", lower),
        fold_rel: format_ident!("fold_{}", lower),
    }
}

/// Find the literal label for a category (e.g., `NumLit` for `Int`, `BoolLit` for `Bool`).
///
/// Returns `None` if the category has no native type or no literal rule.
pub fn literal_label_for(language: &LanguageDef, category: &Ident) -> Option<Ident> {
    let lang_type = language.types.iter().find(|t| t.name == *category)?;
    let native_type = lang_type.native_type.as_ref()?;
    let label = language
        .terms
        .iter()
        .find(|r| r.category == *category && is_literal_rule(r))
        .map(|r| r.label.clone())
        .unwrap_or_else(|| generate_literal_label(native_type));
    Some(label)
}

/// Count the number of AST fields (nonterminals + collections) in a grammar rule.
///
/// Accounts for:
/// - New syntax (term_context): each param = 1 field
/// - Old syntax with bindings: Binder + body NonTerminal = 1 Scope field
/// - Regular rules: count NonTerminals and Collections
pub fn count_nonterminals(rule: &GrammarRule) -> usize {
    // New syntax uses term_context
    if let Some(ref term_context) = rule.term_context {
        return term_context.len();
    }

    // Old syntax with explicit bindings - binder and body combine into one Scope
    if !rule.bindings.is_empty() {
        let (binder_idx, body_indices) = &rule.bindings[0];
        let body_idx = body_indices[0];

        let mut count = 0;
        for (i, item) in rule.items.iter().enumerate() {
            if i == *binder_idx {
                continue; // Skip binder - it's part of the Scope
            }
            if i == body_idx {
                count += 1; // Body becomes Scope field
            } else {
                match item {
                    GrammarItem::NonTerminal(_) | GrammarItem::Collection { .. } => {
                        count += 1;
                    },
                    _ => {},
                }
            }
        }
        return count;
    }

    // Regular rule - count non-terminals and collections
    rule.items
        .iter()
        .filter(|item| matches!(item, GrammarItem::NonTerminal(_) | GrammarItem::Collection { .. }))
        .count()
}

/// Check if a constructor has a collection field.
pub fn has_collection_field(rule: &GrammarRule) -> bool {
    rule.items
        .iter()
        .any(|item| matches!(item, GrammarItem::Collection { .. }))
}

/// Check if a constructor is a multi-binder (has MultiAbstraction in term_context).
pub fn is_multi_binder(rule: &GrammarRule) -> bool {
    rule.term_context.as_ref().is_some_and(|ctx| {
        ctx.iter()
            .any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
    })
}

/// Get the native type for a category, if it has one.
pub fn native_type_for<'a>(language: &'a LanguageDef, category: &Ident) -> Option<&'a syn::Type> {
    language
        .types
        .iter()
        .find(|t| t.name == *category)
        .and_then(|t| t.native_type.as_ref())
}

/// Collect non-terminal fields from a grammar rule's items.
///
/// Returns a vector of (field_index, category_ident) pairs.
pub fn collect_nonterminal_fields(rule: &GrammarRule) -> Vec<(usize, &Ident)> {
    rule.items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| {
            if let GrammarItem::NonTerminal(ident) = item {
                Some((i, ident))
            } else {
                None
            }
        })
        .collect()
}

/// Simple param names from term_context (order matches constructor fields).
/// Used so fold rules bind lv, rv to the names expected by rust_code (e.g. a, b).
pub fn fold_param_names(rule: &GrammarRule) -> Vec<Ident> {
    rule.term_context
        .as_ref()
        .map(|ctx| {
            ctx.iter()
                .filter_map(|p| match p {
                    TermParam::Simple { name, .. } => Some(name.clone()),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Check whether all Simple params in a rule have the same type as the given category.
/// Used to filter out cross-category rules (e.g., Len(Str)->Int) from fold generation.
pub fn fold_params_all_same_category(rule: &GrammarRule, category: &Ident) -> bool {
    let cat_str = category.to_string();
    if let Some(ref ctx) = rule.term_context {
        ctx.iter().all(|p| match p {
            TermParam::Simple { ty, .. } => {
                if let TypeExpr::Base(t) = ty {
                    *t == cat_str
                } else {
                    false
                }
            }
            _ => true, // Binders etc. are OK
        })
    } else {
        // Old-style: check NonTerminal items
        rule.items.iter().all(|item| match item {
            GrammarItem::NonTerminal(nt) => *nt == cat_str,
            _ => true, // Terminals are OK
        })
    }
}

/// Number of constructor fields (for identity fold pattern).
pub fn fold_field_count(rule: &GrammarRule) -> usize {
    if let Some(ref ctx) = rule.term_context {
        return ctx.len();
    }
    rule.items
        .iter()
        .filter(|i| matches!(i, GrammarItem::NonTerminal(_) | GrammarItem::Collection { .. }))
        .count()
}

// =============================================================================
// Category Reachability Analysis
// =============================================================================

/// Compute the set of reachable (src, tgt) category pairs from user-defined constructors.
///
/// Builds a directed graph from user-defined constructor field types, computes the
/// transitive closure, and returns the set of reachable (src, tgt) pairs.
///
/// This is used to prune dead cross-category rules. For example, if Float has no
/// user-defined constructors with fields of type Proc, then the rule
/// `proc(sub) <-- float(t), for sub in ...` will never produce facts and can be skipped.
///
/// The reachability includes:
/// - Direct edges: if category A has a constructor with a field of type B, A→B
/// - Transitive: if A→B and B→C, then A→C (B can extract subterms of type C)
/// - Self-loops: every category reaches itself (identity)
///
/// Auto-generated variants (Apply/MApply/Lam/MLam) are NOT included in the base graph.
/// They create edges between all category pairs, which is exactly what we want to prune.
/// Only if user constructors create a path src→tgt will auto-variant rules for that pair fire.
pub fn compute_category_reachability(language: &LanguageDef) -> BTreeSet<(String, String)> {
    let categories: Vec<String> = language.types.iter().map(|t| t.name.to_string()).collect();

    // Build adjacency list from user-defined constructors
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for cat in &categories {
        edges.entry(cat.clone()).or_default();
    }

    for rule in &language.terms {
        let src = rule.category.to_string();

        // Extract field types from new-syntax term_context
        if let Some(ref term_context) = rule.term_context {
            for param in term_context {
                match param {
                    TermParam::Simple { ty, .. } => {
                        collect_type_refs(&src, ty, &categories, &mut edges);
                    }
                    TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
                        collect_type_refs(&src, ty, &categories, &mut edges);
                    }
                }
            }
        } else {
            // Old-syntax: inspect items
            for item in &rule.items {
                match item {
                    GrammarItem::NonTerminal(cat) => {
                        let tgt = cat.to_string();
                        if categories.contains(&tgt) && tgt != "Var" && tgt != "Integer" {
                            edges.entry(src.clone()).or_default().insert(tgt);
                        }
                    }
                    GrammarItem::Collection { element_type, .. } => {
                        let tgt = element_type.to_string();
                        if categories.contains(&tgt) {
                            edges.entry(src.clone()).or_default().insert(tgt);
                        }
                    }
                    GrammarItem::Binder { category: binder_domain } => {
                        let tgt = binder_domain.to_string();
                        if categories.contains(&tgt) {
                            edges.entry(src.clone()).or_default().insert(tgt);
                        }
                    }
                    GrammarItem::Terminal(_) => {}
                }
            }
        }
    }

    // Compute transitive closure using Floyd-Warshall
    let mut reachable = BTreeSet::new();

    // Add self-loops and direct edges
    for cat in &categories {
        reachable.insert((cat.clone(), cat.clone()));
        if let Some(targets) = edges.get(cat) {
            for tgt in targets {
                reachable.insert((cat.clone(), tgt.clone()));
            }
        }
    }

    // Transitive closure: iterate until no new pairs found
    loop {
        let mut changed = false;
        let current: Vec<(String, String)> = reachable.iter().cloned().collect();
        for (a, b) in &current {
            for (c, d) in &current {
                if b == c && !reachable.contains(&(a.clone(), d.clone())) {
                    reachable.insert((a.clone(), d.clone()));
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    reachable
}

/// Helper: extract category references from a TypeExpr
fn collect_type_refs(
    src: &str,
    ty: &TypeExpr,
    categories: &[String],
    edges: &mut BTreeMap<String, BTreeSet<String>>,
) {
    match ty {
        TypeExpr::Base(ident) => {
            let tgt = ident.to_string();
            if categories.contains(&tgt) && tgt != "Var" && tgt != "Integer" {
                edges.entry(src.to_string()).or_default().insert(tgt);
            }
        }
        TypeExpr::Collection { element, .. } => {
            collect_type_refs(src, element, categories, edges);
        }
        TypeExpr::Arrow { domain, codomain } => {
            collect_type_refs(src, domain, categories, edges);
            collect_type_refs(src, codomain, categories, edges);
        }
        TypeExpr::MultiBinder(inner) => {
            collect_type_refs(src, inner, categories, edges);
        }
    }
}

/// Type alias for an optional category filter set.
///
/// When `Some(set)`, only categories whose names appear in the set are processed.
/// When `None`, all categories are processed (no filtering).
pub type CategoryFilter<'a> = Option<&'a BTreeSet<String>>;

/// Check if a category passes the filter.
///
/// Returns `true` if either:
/// - No filter is set (`None`) — all categories pass
/// - The category's name is in the filter set
pub fn in_cat_filter(cat: &Ident, filter: CategoryFilter) -> bool {
    filter.is_none_or(|f| f.contains(&cat.to_string()))
}

/// Compute the set of "core" categories for SCC splitting.
///
/// Core categories are those that are bidirectionally reachable from the primary
/// category (first declared) through user-defined constructors. For example, in
/// RhoCalc: Proc→Name (via PDrop/POutput) and Name→Proc (via NQuote), so
/// Core = {Proc, Name}. Categories like Int/Float/Bool/Str are one-way sinks
/// (only reachable FROM Proc via Cast, with no path back).
///
/// The core set is used to generate a smaller Ascent struct with fewer rules
/// for inputs that only use core categories. This reduces SCC iteration cost
/// by skipping rules for categories whose relations will be empty.
///
/// Returns `None` if:
/// - The language has ≤ 1 type (no splitting benefit)
/// - All categories are core (core == full, no splitting benefit)
pub fn compute_core_categories(language: &LanguageDef) -> Option<BTreeSet<String>> {
    if language.types.len() <= 1 {
        return None; // Single-category language — no splitting benefit
    }

    let reachable = compute_category_reachability(language);
    let all_cats: Vec<String> = language.types.iter().map(|t| t.name.to_string()).collect();
    let primary = match all_cats.first() {
        Some(p) => p.clone(),
        None => return None,
    };

    let mut core = BTreeSet::new();
    core.insert(primary.clone());

    // Add categories bidirectionally reachable with the primary
    for cat in &all_cats {
        if *cat == primary {
            continue;
        }
        // Both primary→cat AND cat→primary must exist in user constructors
        if reachable.contains(&(primary.clone(), cat.clone()))
            && reachable.contains(&(cat.clone(), primary.clone()))
        {
            core.insert(cat.clone());
        }
    }

    // No benefit if core == all categories
    if core.len() == all_cats.len() {
        return None;
    }

    Some(core)
}

// =============================================================================
// TLS Vec Pool Pattern for Zero-Allocation Iteration
// =============================================================================

/// Information about a single match arm for the TLS pool pattern.
///
/// Each arm specifies a pattern and the push operations to perform
/// when that pattern matches.
pub struct PoolArm {
    /// The match pattern (e.g., `Cat::Foo(f0, f1)`)
    pub pattern: TokenStream,
    /// The push operations inside the arm body (e.g., `buf.push(f0.as_ref().clone());`)
    pub pushes: Vec<TokenStream>,
}

/// Generate an inline block expression that uses a thread-local Vec pool
/// for zero-allocation iteration in steady state.
///
/// Replaces the pattern:
/// ```text
/// (match t {
///     Cat::A(f0, f1) => vec![f0.as_ref().clone(), f1.as_ref().clone()],
///     Cat::B(f0) => vec![f0.as_ref().clone()],
///     _ => vec![],
/// }).into_iter()
/// ```
///
/// With a TLS-pooled version that avoids heap allocation after the first call:
/// ```text
/// {
///     thread_local! { static POOL: std::cell::Cell<Vec<Cat>> = const { std::cell::Cell::new(Vec::new()) }; }
///     let mut buf = POOL.with(|p| p.take());
///     buf.clear();
///     match t {
///         Cat::A(f0, f1) => { buf.push(f0.as_ref().clone()); buf.push(f1.as_ref().clone()); },
///         Cat::B(f0) => { buf.push(f0.as_ref().clone()); },
///         _ => {},
///     }
///     let iter_buf = std::mem::take(&mut buf);
///     POOL.with(|p| p.set(buf));
///     iter_buf
/// }.into_iter()
/// ```
///
/// # Parameters
/// - `pool_name`: Unique identifier for the thread_local static (e.g., `POOL_PROC_PROC_SUB`)
/// - `element_type`: The type stored in the Vec (e.g., `Proc`)
/// - `match_expr`: The expression being matched (e.g., `t`)
/// - `arms`: The match arms with their push operations
///
/// # Notes
/// - Uses `Cell<Vec<T>>` (not RefCell) to avoid re-entrancy panics
/// - The empty fallthrough (`_ => {}`) does zero work
/// - After the first iteration, the buffer is pre-sized and never allocates
/// - Uses `const { ... }` initializer for zero-cost TLS init (nightly feature)
pub fn generate_tls_pool_iter(
    pool_name: &Ident,
    element_type: &TokenStream,
    match_expr: &TokenStream,
    arms: &[PoolArm],
) -> TokenStream {
    let match_arms: Vec<TokenStream> = arms
        .iter()
        .map(|arm| {
            let pattern = &arm.pattern;
            let pushes = &arm.pushes;
            quote! {
                #pattern => { #(#pushes)* },
            }
        })
        .collect();

    quote! {
        {
            std::thread_local! {
                static #pool_name: std::cell::Cell<Vec<#element_type>> =
                    const { std::cell::Cell::new(Vec::new()) };
            }
            let mut buf = #pool_name.with(|p| p.take());
            buf.clear();
            match #match_expr {
                #(#match_arms)*
                _ => {},
            }
            let iter_buf = std::mem::take(&mut buf);
            #pool_name.with(|p| p.set(buf));
            iter_buf
        }.into_iter()
    }
}
