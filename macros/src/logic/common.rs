//! Shared helpers for Ascent Datalog code generation.
//!
//! This module provides common utilities used across multiple logic
//! generation modules, reducing duplication and ensuring consistency.

use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use crate::ast::language::LanguageDef;
use crate::ast::types::TypeExpr;
use crate::gen::{generate_literal_label, is_literal_rule};
use quote::format_ident;
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
