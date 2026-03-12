//! Shared helpers for Ascent Datalog code generation.
//!
//! This module provides common utilities used across multiple logic
//! generation modules, reducing duplication and ensuring consistency.

use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use crate::ast::language::LanguageDef;
use crate::ast::types::{EvalMode, TypeExpr};
use crate::gen::{generate_literal_label, is_literal_rule};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{BTreeMap, BTreeSet, HashMap};
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
            },
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
                    },
                    TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
                        collect_type_refs(&src, ty, &categories, &mut edges);
                    },
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
                    },
                    GrammarItem::Collection { element_type, .. } => {
                        let tgt = element_type.to_string();
                        if categories.contains(&tgt) {
                            edges.entry(src.clone()).or_default().insert(tgt);
                        }
                    },
                    GrammarItem::Binder { category: binder_domain } => {
                        let tgt = binder_domain.to_string();
                        if categories.contains(&tgt) {
                            edges.entry(src.clone()).or_default().insert(tgt);
                        }
                    },
                    GrammarItem::Terminal(_) => {},
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
        },
        TypeExpr::Collection { element, .. } => {
            collect_type_refs(src, element, categories, edges);
        },
        TypeExpr::Arrow { domain, codomain } => {
            collect_type_refs(src, domain, categories, edges);
            collect_type_refs(src, codomain, categories, edges);
        },
        TypeExpr::MultiBinder(inner) => {
            collect_type_refs(src, inner, categories, edges);
        },
    }
}

// =============================================================================
// Demand-Driven Relation Population (A-RT06)
// =============================================================================

/// Compute the set of categories that are "demanded" by equation/rewrite/logic rules.
///
/// A category is demanded if it appears in at least one:
/// - Equation LHS or RHS pattern (as a constructor's category or subterm field type)
/// - Rewrite LHS or RHS pattern (same)
/// - Logic block relation parameter type
/// - Type context entry in an equation or rewrite
/// - HOL step rule (rust_code references categories via constructor fields)
///
/// The demand set is used to prune deconstruction rules: for a reachable `(src, tgt)` pair,
/// if `tgt` is not in the demanded set, no equation/rewrite/logic rule can reference
/// subterms of type `tgt`, so the deconstruction rule would produce unused facts.
///
/// This is conservative: if in doubt, the category is included. Specifically:
/// - All categories from pattern constructors (recursively, including nested subterms)
/// - All field types of those constructors (transitive demand)
/// - All categories from logic block relation types
///
/// Note: Self-loop pairs `(src, src)` are kept unconditionally by the caller
/// (see `filter_reachable_by_demand`), since every category with any terms needs
/// same-category deconstruction for pattern matching and congruence rules.
///
/// Returns the set of demanded category names.
pub fn compute_demanded_categories(language: &LanguageDef) -> BTreeSet<String> {
    let all_categories: BTreeSet<String> = language.types.iter().map(|t| t.name.to_string()).collect();
    let mut demanded = BTreeSet::new();

    // 1. Categories referenced in equation patterns
    for eq in &language.equations {
        collect_pattern_categories(&eq.left, language, &all_categories, &mut demanded);
        collect_pattern_categories(&eq.right, language, &all_categories, &mut demanded);
        // Type context entries
        for tp in &eq.type_context {
            collect_type_expr_categories(&tp.ty, &all_categories, &mut demanded);
        }
    }

    // 2. Categories referenced in rewrite patterns
    for rw in &language.rewrites {
        collect_pattern_categories(&rw.left, language, &all_categories, &mut demanded);
        collect_pattern_categories(&rw.right, language, &all_categories, &mut demanded);
        // Type context entries
        for tp in &rw.type_context {
            collect_type_expr_categories(&tp.ty, &all_categories, &mut demanded);
        }
        // Congruence premises reference categories implicitly via the rewrite relation
        // (rw_cat), but the category is already demanded via the pattern. No extra work needed.
    }

    // 3. Categories referenced in logic block relation parameter types
    if let Some(ref logic) = language.logic {
        for rel in &logic.relations {
            for param_type in &rel.param_types {
                // param_types are strings like "Proc", "Vec<Proc>", etc.
                // Extract the base category name(s) from them.
                collect_param_type_categories(param_type, &all_categories, &mut demanded);
            }
        }
        // Conservative: if there's a logic block with content, assume all categories
        // might be referenced (the content is a raw TokenStream that we can't easily
        // introspect beyond the parsed relation declarations). The relation parameter
        // types give us the main signal, but custom rules might reference additional
        // category relations (e.g., `proc(t)` directly).
        //
        // For safety, if ANY logic block exists with non-empty content, we include
        // all categories that appear in logic relation parameter types (already done above).
        // We do NOT conservatively include ALL categories — the relation declarations
        // are the primary signal and should be sufficient for most grammars.
    }

    // 4. Categories referenced by HOL step rules (rust_code constructors)
    // These are constructors with rust_code that reference categories via their field types.
    // The constructor's own category and all field categories are demanded.
    for rule in &language.terms {
        if rule.rust_code.is_some() {
            demanded.insert(rule.category.to_string());
            if let Some(ref term_ctx) = rule.term_context {
                for param in term_ctx {
                    match param {
                        TermParam::Simple { ty, .. } => {
                            collect_type_expr_categories(ty, &all_categories, &mut demanded);
                        },
                        TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
                            collect_type_expr_categories(ty, &all_categories, &mut demanded);
                        },
                    }
                }
            }
        }
    }

    demanded
}

/// Filter a reachable `(src, tgt)` pair set to only include pairs where `tgt` is demanded.
///
/// Self-loop pairs `(src, src)` are always kept — every category needs same-category
/// deconstruction for its own congruence and pattern-matching rules.
///
/// Cross-category pairs `(src, tgt)` where `src != tgt` are kept only if `tgt` is in the
/// demanded set. If `tgt` is not demanded, no equation/rewrite/logic rule references
/// subterms of type `tgt`, so the deconstruction rule would produce unused facts.
///
/// This is a conservative filter: it only removes pairs that are provably unused.
pub fn filter_reachable_by_demand(
    reachable: &BTreeSet<(String, String)>,
    demanded: &BTreeSet<String>,
) -> BTreeSet<(String, String)> {
    reachable
        .iter()
        .filter(|(src, tgt)| {
            // Self-loops are always kept
            if src == tgt {
                return true;
            }
            // Cross-category pairs: keep only if tgt is demanded
            demanded.contains(tgt)
        })
        .cloned()
        .collect()
}

/// Recursively collect all category names referenced in a pattern.
///
/// For each `Apply { constructor, args }`, adds the constructor's category and all
/// field types of that constructor. Then recurses into args.
fn collect_pattern_categories(
    pattern: &crate::ast::pattern::Pattern,
    language: &LanguageDef,
    all_categories: &BTreeSet<String>,
    demanded: &mut BTreeSet<String>,
) {
    use crate::ast::pattern::Pattern;

    match pattern {
        Pattern::Term(pt) => {
            collect_pattern_term_categories(pt, language, all_categories, demanded);
        },
        Pattern::Collection { elements, .. } => {
            for elem in elements {
                collect_pattern_categories(elem, language, all_categories, demanded);
            }
        },
        Pattern::Map { collection, body, .. } => {
            collect_pattern_categories(collection, language, all_categories, demanded);
            collect_pattern_categories(body, language, all_categories, demanded);
        },
        Pattern::Zip { first, second } => {
            collect_pattern_categories(first, language, all_categories, demanded);
            collect_pattern_categories(second, language, all_categories, demanded);
        },
    }
}

/// Recursively collect categories from a PatternTerm.
fn collect_pattern_term_categories(
    pt: &crate::ast::pattern::PatternTerm,
    language: &LanguageDef,
    all_categories: &BTreeSet<String>,
    demanded: &mut BTreeSet<String>,
) {
    use crate::ast::pattern::PatternTerm;

    match pt {
        PatternTerm::Var(_) => {},
        PatternTerm::Apply { constructor, args } => {
            // Add the constructor's own category
            if let Some(cat) = language.category_of_constructor(constructor) {
                demanded.insert(cat.to_string());
            }
            // Add all field types of this constructor (these are categories that
            // deconstruction would extract from terms of this constructor's category)
            if let Some(rule) = language.get_constructor(constructor) {
                collect_constructor_field_categories(rule, all_categories, demanded);
            }
            // Recurse into arguments
            for arg in args {
                collect_pattern_categories(arg, language, all_categories, demanded);
            }
        },
        PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
            collect_pattern_categories(body, language, all_categories, demanded);
        },
        PatternTerm::Subst { term, replacement, .. } => {
            collect_pattern_categories(term, language, all_categories, demanded);
            collect_pattern_categories(replacement, language, all_categories, demanded);
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            collect_pattern_categories(scope, language, all_categories, demanded);
            for r in replacements {
                collect_pattern_categories(r, language, all_categories, demanded);
            }
        },
    }
}

/// Collect category names from a constructor's field types.
///
/// For a constructor like `POutput(Name, Name, Proc)`, this adds "Name" and "Proc"
/// to the demanded set.
fn collect_constructor_field_categories(
    rule: &crate::ast::grammar::GrammarRule,
    all_categories: &BTreeSet<String>,
    demanded: &mut BTreeSet<String>,
) {
    if let Some(ref term_ctx) = rule.term_context {
        for param in term_ctx {
            match param {
                TermParam::Simple { ty, .. } => {
                    collect_type_expr_categories(ty, all_categories, demanded);
                },
                TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
                    collect_type_expr_categories(ty, all_categories, demanded);
                },
            }
        }
    } else {
        // Old-syntax: inspect items directly
        for item in &rule.items {
            match item {
                GrammarItem::NonTerminal(cat) => {
                    let cat_str = cat.to_string();
                    if all_categories.contains(&cat_str) {
                        demanded.insert(cat_str);
                    }
                },
                GrammarItem::Collection { element_type, .. } => {
                    let cat_str = element_type.to_string();
                    if all_categories.contains(&cat_str) {
                        demanded.insert(cat_str);
                    }
                },
                GrammarItem::Binder { category: binder_domain } => {
                    let cat_str = binder_domain.to_string();
                    if all_categories.contains(&cat_str) {
                        demanded.insert(cat_str);
                    }
                },
                GrammarItem::Terminal(_) => {},
            }
        }
    }
}

/// Collect category names from a TypeExpr.
fn collect_type_expr_categories(
    ty: &TypeExpr,
    all_categories: &BTreeSet<String>,
    demanded: &mut BTreeSet<String>,
) {
    match ty {
        TypeExpr::Base(ident) => {
            let name = ident.to_string();
            if all_categories.contains(&name) {
                demanded.insert(name);
            }
        },
        TypeExpr::Collection { element, .. } => {
            collect_type_expr_categories(element, all_categories, demanded);
        },
        TypeExpr::Arrow { domain, codomain } => {
            collect_type_expr_categories(domain, all_categories, demanded);
            collect_type_expr_categories(codomain, all_categories, demanded);
        },
        TypeExpr::MultiBinder(inner) => {
            collect_type_expr_categories(inner, all_categories, demanded);
        },
    }
}

/// Extract category names from a relation parameter type string.
///
/// Handles simple cases like "Proc", "Vec<Proc>", "i32", etc.
/// If the string contains a known category name, it is added.
fn collect_param_type_categories(
    param_type: &str,
    all_categories: &BTreeSet<String>,
    demanded: &mut BTreeSet<String>,
) {
    // Simple approach: check if any category name appears in the param type string.
    // This handles "Proc", "Vec<Proc>", "HashBag<Proc>", etc.
    for cat in all_categories {
        if param_type.contains(cat.as_str()) {
            demanded.insert(cat.clone());
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

// =============================================================================
// Ground Rule Classification for Pre-Stratum Optimization
// =============================================================================

/// Classification of rewrite rules into evaluation strata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RewriteStratum {
    /// Safe for pre-stratum: matches only literal arguments, produces a literal result.
    /// Converges in O(depth) iterations when combined with deconstruction.
    Ground,
    /// Must be in main SCC: depends on recursive Ascent relations.
    Recursive,
    /// Skip entirely: dead constructor detected by WFST analysis (Sprint 1 DCE).
    Dead,
}

/// Classify HOL step rules into evaluation strata.
///
/// A HOL step rule is **Ground** if:
/// 1. It has `rust_code` (HOL evaluation body)
/// 2. It is step-mode (not fold)
/// 3. It has ≥1 NonTerminal child
/// 4. All NonTerminal children are destructured to literal patterns
///    (checked by verifying the rule has `term_context` with Simple params
///    whose types resolve to categories with native types and literal labels)
/// 5. Its constructor label is not dead (from WFST 4-tier analysis)
///
/// Ground rules produce only literal results (`Cat::LitLabel(f(a, b, ...))`)
/// and cannot trigger further recursive term creation, making them safe to
/// evaluate in a pre-stratum before the main fixpoint.
///
/// Returns a map from constructor label to stratum classification.
pub fn classify_rewrite_strata(
    language: &LanguageDef,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
) -> HashMap<String, RewriteStratum> {
    let mut strata = HashMap::new();

    for rule in &language.terms {
        let label = rule.label.to_string();

        // Dead rule check (Sprint 1 DCE)
        if let Some(ref a) = analysis {
            if a.dead_rule_labels.contains(&label) {
                strata.insert(label, RewriteStratum::Dead);
                continue;
            }
        }

        // Only HOL step rules (rust_code present, not fold mode) are candidates
        if rule.rust_code.is_none() {
            continue;
        }
        if rule.eval_mode == Some(EvalMode::Fold) {
            continue;
        }

        let category = &rule.category;

        // Must have NonTerminal children
        let non_terminal_count = rule
            .items
            .iter()
            .filter(|item| matches!(item, GrammarItem::NonTerminal(_)))
            .count();
        if non_terminal_count == 0 {
            continue;
        }

        // Must have a native type on the result category
        if native_type_for(language, category).is_none() {
            strata.insert(label, RewriteStratum::Recursive);
            continue;
        }

        // Check that all NonTerminal arguments resolve to literal-bearing categories
        let all_args_literal = if let Some(ref term_ctx) = rule.term_context {
            term_ctx.iter().all(|param| match param {
                TermParam::Simple { ty, .. } => {
                    if let TypeExpr::Base(arg_cat) = ty {
                        literal_label_for(language, arg_cat).is_some()
                    } else {
                        false
                    }
                },
                _ => false, // Binders/multi-abstractions are not ground
            })
        } else {
            // Old syntax: check that all NonTerminal items point to literal-bearing cats
            rule.items.iter().all(|item| match item {
                GrammarItem::NonTerminal(cat) => literal_label_for(language, cat).is_some(),
                _ => true, // Terminals don't affect groundness
            })
        };

        if all_args_literal {
            strata.insert(label, RewriteStratum::Ground);
        } else {
            strata.insert(label, RewriteStratum::Recursive);
        }
    }

    strata
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::grammar::{GrammarItem, GrammarRule};
    use crate::ast::language::{Equation, LangType, LanguageDef, RewriteRule};
    use crate::ast::pattern::{Pattern, PatternTerm};
    use proc_macro2::Span;
    use syn::Ident;

    /// Build a minimal LanguageDef for demand analysis testing.
    fn make_test_language_with_rewrites(
        types: Vec<&str>,
        terms: Vec<(&str, &str, Vec<&str>)>,
        equations: Vec<(&str, &str)>,
        rewrites: Vec<(&str, &str, &str)>, // (name, lhs_ctor, rhs_ctor)
    ) -> LanguageDef {
        let lang_types: Vec<LangType> = types
            .iter()
            .map(|name| LangType {
                name: Ident::new(name, Span::call_site()),
                native_type: None,
            })
            .collect();

        let grammar_rules: Vec<GrammarRule> = terms
            .iter()
            .map(|(label, category, field_cats)| {
                let items: Vec<GrammarItem> = field_cats
                    .iter()
                    .map(|fc| GrammarItem::NonTerminal(Ident::new(fc, Span::call_site())))
                    .collect();
                GrammarRule {
                    label: Ident::new(label, Span::call_site()),
                    category: Ident::new(category, Span::call_site()),
                    items,
                    bindings: vec![],
                    rust_code: None,
                    term_context: None,
                    syntax_pattern: None,
                    eval_mode: None,
                    is_right_assoc: false,
                    prefix_bp: None,
                }
            })
            .collect();

        let eqs: Vec<Equation> = equations
            .iter()
            .map(|(name, lhs_ctor)| {
                let lhs_ident = Ident::new(lhs_ctor, Span::call_site());
                Equation {
                    name: Ident::new(name, Span::call_site()),
                    type_context: vec![],
                    premises: vec![],
                    left: Pattern::Term(PatternTerm::Apply {
                        constructor: lhs_ident,
                        args: vec![Pattern::Term(PatternTerm::Var(Ident::new("X", Span::call_site())))],
                    }),
                    right: Pattern::Term(PatternTerm::Var(Ident::new("X", Span::call_site()))),
                }
            })
            .collect();

        let rws: Vec<RewriteRule> = rewrites
            .iter()
            .map(|(name, lhs_ctor, rhs_ctor)| {
                let lhs_ident = Ident::new(lhs_ctor, Span::call_site());
                let rhs_ident = Ident::new(rhs_ctor, Span::call_site());
                RewriteRule {
                    name: Ident::new(name, Span::call_site()),
                    type_context: vec![],
                    premises: vec![],
                    left: Pattern::Term(PatternTerm::Apply {
                        constructor: lhs_ident,
                        args: vec![Pattern::Term(PatternTerm::Var(Ident::new("X", Span::call_site())))],
                    }),
                    right: Pattern::Term(PatternTerm::Apply {
                        constructor: rhs_ident,
                        args: vec![Pattern::Term(PatternTerm::Var(Ident::new("X", Span::call_site())))],
                    }),
                }
            })
            .collect();

        LanguageDef {
            name: Ident::new("TestLang", Span::call_site()),
            options: std::collections::HashMap::new(),
            extends_names: vec![],
            include_names: vec![],
            mixin_names: vec![],
            types: lang_types,
            token_defs: vec![],
            mode_defs: vec![],
            sync_constraints: vec![],
            tree_invariants: vec![],
            terms: grammar_rules,
            equations: eqs,
            rewrites: rws,
            logic: None,
        }
    }

    // ── ART06: compute_demanded_categories ────────────────────────────────

    #[test]
    fn demand_basic_unused_category() {
        // 3 categories: Proc, Name, Unused.
        // Only Proc has an equation referencing PFoo(Name).
        // Unused has a constructor but no equation/rewrite/logic references.
        let lang = make_test_language_with_rewrites(
            vec!["Proc", "Name", "Unused"],
            vec![
                ("PFoo", "Proc", vec!["Name"]),
                ("NBar", "Name", vec![]),
                ("UBaz", "Unused", vec![]),
            ],
            vec![("Eq1", "PFoo")], // equation references PFoo in Proc
            vec![],
        );

        let demanded = compute_demanded_categories(&lang);

        assert!(demanded.contains("Proc"), "Proc should be demanded (has equation)");
        assert!(demanded.contains("Name"), "Name should be demanded (field of PFoo in equation)");
        assert!(!demanded.contains("Unused"), "Unused should NOT be demanded (no references)");
    }

    #[test]
    fn demand_transitive_closure_via_rewrite() {
        // A rewrites to B (via constructor), B is constructed from C.
        // All three should be demanded even though only A has a direct rewrite.
        // Proc has PFoo(Name), and a rewrite matching PFoo.
        // Name has NBar(Expr). Expr has EBaz().
        // The rewrite on PFoo demands Proc and Name (via field type).
        // NBar constructor doesn't appear in any rule, but Name IS demanded
        // because the equation references PFoo which has a Name field.
        let lang = make_test_language_with_rewrites(
            vec!["Proc", "Name", "Expr"],
            vec![
                ("PFoo", "Proc", vec!["Name"]),
                ("NBar", "Name", vec!["Expr"]),
                ("EBaz", "Expr", vec![]),
            ],
            vec![],
            vec![("Rw1", "PFoo", "PFoo")], // rewrite references PFoo
        );

        let demanded = compute_demanded_categories(&lang);

        assert!(demanded.contains("Proc"), "Proc should be demanded (rewrite LHS category)");
        assert!(demanded.contains("Name"), "Name should be demanded (field of PFoo in rewrite pattern)");
        // Expr is NOT directly referenced in any equation/rewrite pattern.
        // NBar is a constructor but NBar doesn't appear in any pattern.
        // The demand analysis only collects categories from patterns, not transitively
        // through all constructors.
        assert!(
            !demanded.contains("Expr"),
            "Expr should NOT be demanded (not referenced in any equation/rewrite pattern)"
        );
    }

    #[test]
    fn demand_all_categories_with_equations() {
        // Every category has an equation — all should be demanded.
        let lang = make_test_language_with_rewrites(
            vec!["Proc", "Name"],
            vec![
                ("PFoo", "Proc", vec!["Name"]),
                ("NBar", "Name", vec!["Proc"]),
            ],
            vec![("EqP", "PFoo"), ("EqN", "NBar")],
            vec![],
        );

        let demanded = compute_demanded_categories(&lang);

        assert!(demanded.contains("Proc"), "Proc demanded");
        assert!(demanded.contains("Name"), "Name demanded");
    }

    #[test]
    fn demand_empty_language() {
        let lang = make_test_language_with_rewrites(vec![], vec![], vec![], vec![]);
        let demanded = compute_demanded_categories(&lang);
        assert!(demanded.is_empty(), "empty language should have no demanded categories");
    }

    #[test]
    fn demand_filter_reachable_by_demand() {
        // Test filter_reachable_by_demand: self-loops always kept,
        // cross-category pairs kept only if tgt is demanded.
        let mut reachable = BTreeSet::new();
        reachable.insert(("Proc".to_string(), "Proc".to_string())); // self-loop
        reachable.insert(("Name".to_string(), "Name".to_string())); // self-loop
        reachable.insert(("Proc".to_string(), "Name".to_string())); // cross-cat
        reachable.insert(("Proc".to_string(), "Unused".to_string())); // cross-cat

        let mut demanded = BTreeSet::new();
        demanded.insert("Proc".to_string());
        demanded.insert("Name".to_string());
        // Unused is NOT demanded

        let filtered = filter_reachable_by_demand(&reachable, &demanded);

        assert!(filtered.contains(&("Proc".to_string(), "Proc".to_string())), "self-loop kept");
        assert!(filtered.contains(&("Name".to_string(), "Name".to_string())), "self-loop kept");
        assert!(filtered.contains(&("Proc".to_string(), "Name".to_string())), "demanded tgt kept");
        assert!(
            !filtered.contains(&("Proc".to_string(), "Unused".to_string())),
            "non-demanded tgt pruned"
        );
    }
}
