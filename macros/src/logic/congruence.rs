//! Unified congruence rule generation.
//!
//! This module handles EXPLICIT congruence rules declared in languages:
//!   `if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest})`
//!
//! Note: Rewrite congruences are NOT auto-generated. Users explicitly control
//! where rewrites propagate (e.g., rewrites through PPar but not POutput).
//!
//! Equality congruences ARE auto-generated (in equations.rs), since
//! `eq(x,y) => eq(f(x), f(y))` for all constructors is always sound.

use super::common::{
    count_nonterminals, generate_tls_pool_iter, in_cat_filter, relation_names, CategoryFilter,
    PoolArm,
};
use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use crate::ast::language::{LanguageDef, RewriteRule};
use crate::ast::pattern::{Pattern, PatternTerm};
use crate::ast::types::TypeExpr;
use crate::gen::native::{is_list_literal_rule, is_vec_native_type, vec_element_ident};
use crate::gen::generate_literal_label;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::BTreeMap;
use syn::Ident;

/// Entry for a simple congruence rule to be consolidated.
struct SimpleCongruenceEntry {
    constructor: Ident,
    field_idx: usize,
    n_fields: usize,
    is_boxed: bool,
}

/// Generate all explicit congruence rules.
///
/// When `cat_filter` is `Some`, only generates rules for categories in the filter set.
pub fn generate_all_explicit_congruences(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    // Group simple congruences by (source_cat, field_cat) for consolidation.
    // BTreeMap gives deterministic ordering for reproducible code generation.
    let mut simple_groups: BTreeMap<(String, String), Vec<SimpleCongruenceEntry>> = BTreeMap::new();

    for rewrite in &language.rewrites {
        if !rewrite.is_congruence_rule() {
            continue;
        }

        // Determine category and skip if not in filter
        let category = rewrite
            .left
            .category(language)
            .or_else(|| rewrite.right.category(language));
        if let Some(cat) = category {
            if !in_cat_filter(cat, cat_filter) {
                continue;
            }
        }

        if let Some(rule) = classify_and_generate_congruence(rewrite, language, &mut simple_groups)
        {
            rules.push(rule);
        }
    }

    // Generate consolidated rules for each simple congruence group
    for ((src_str, fld_str), entries) in &simple_groups {
        let source_cat = format_ident!("{}", src_str);
        let field_cat = format_ident!("{}", fld_str);
        if let Some(rule) =
            generate_consolidated_simple_congruence(&source_cat, &field_cat, entries)
        {
            rules.push(rule);
        }
    }

    // Auto-generate List (Vec-backed) element congruence: rewrites propagate into list elements by index
    for lang_type in &language.types {
        let category = &lang_type.name;
        if !in_cat_filter(category, cat_filter) {
            continue;
        }
        let Some(ref native_type) = lang_type.native_type else { continue };
        if !is_vec_native_type(native_type) {
            continue;
        }
        let Some(element_cat) = vec_element_ident(native_type) else { continue };
        if let Some(rule) = generate_list_native_congruence(category, &element_cat, native_type) {
            rules.push(rule);
        }
    }

    rules
}

/// Classify a congruence rewrite rule and either generate it immediately
/// (Collection/Binding) or collect it for consolidation (Simple).
///
/// Returns `Some(TokenStream)` for Collection/Binding rules, `None` for Simple
/// (which is added to simple_groups for later consolidation).
fn classify_and_generate_congruence(
    rewrite: &RewriteRule,
    language: &LanguageDef,
    simple_groups: &mut BTreeMap<(String, String), Vec<SimpleCongruenceEntry>>,
) -> Option<TokenStream> {
    let (source_var, _target_var) = rewrite.congruence_premise()?;
    let context = find_rewrite_context(&rewrite.left, source_var, language)?;

    match context {
        RewriteContext::Collection {
            category,
            constructor,
            element_category,
            has_rest,
        } => generate_collection_congruence(
            &category,
            &constructor,
            &element_category,
            has_rest,
            language,
        ),
        RewriteContext::Binding {
            category,
            constructor,
            field_idx,
            body_category,
        } => generate_binding_congruence(
            &category,
            &constructor,
            field_idx,
            &body_category,
            language,
        ),
        RewriteContext::Simple {
            category,
            constructor,
            field_idx,
            field_category,
        } => {
            // Collect for consolidation instead of generating immediately
            let grammar_rule = language.get_constructor(&constructor)?;
            // List literal: single field is Vec<elem>, not Box<cat>; skip simple congruence
            if is_list_literal_rule(grammar_rule, language) {
                return None;
            }
            let n = count_nonterminals(grammar_rule);
            let is_boxed = field_is_boxed_in_ast(grammar_rule, field_idx);

            let key = (category.to_string(), field_category.to_string());
            simple_groups
                .entry(key)
                .or_default()
                .push(SimpleCongruenceEntry {
                    constructor,
                    field_idx,
                    n_fields: n,
                    is_boxed,
                });
            None // Will be generated later in consolidated form
        },
    }
}

/// Context where a rewrite variable appears
enum RewriteContext {
    /// Variable appears in a collection element position
    /// e.g., `(PPar {S, ...rest})`
    Collection {
        category: Ident,
        constructor: Ident,
        element_category: Ident,
        has_rest: bool,
    },
    /// Variable appears in a binder body position
    /// e.g., `(PNew x S)`
    Binding {
        category: Ident,
        constructor: Ident,
        field_idx: usize,
        body_category: Ident,
    },
    /// Variable appears in a simple field position
    /// e.g., `(PAmb N S)`
    Simple {
        category: Ident,
        constructor: Ident,
        field_idx: usize,
        field_category: Ident,
    },
}

/// Find where the rewrite variable appears in the pattern
fn find_rewrite_context(
    pattern: &Pattern,
    source_var: &Ident,
    language: &LanguageDef,
) -> Option<RewriteContext> {
    match pattern {
        // Collections no longer have constructors - they're always inside an Apply
        // that provides the context. Top-level Collection patterns can't determine context.
        Pattern::Collection { .. } => None,
        Pattern::Term(pt) => find_rewrite_context_in_term(pt, source_var, language),
        _ => None,
    }
}

/// Find rewrite context in a PatternTerm
fn find_rewrite_context_in_term(
    pt: &PatternTerm,
    source_var: &Ident,
    language: &LanguageDef,
) -> Option<RewriteContext> {
    match pt {
        PatternTerm::Apply { constructor, args } => {
            let rule = language.get_constructor(constructor)?;
            let category = rule.category.clone();

            // Check each argument for the source variable
            let mut field_idx = 0;
            for item in rule.items.iter() {
                match item {
                    GrammarItem::NonTerminal(field_cat) => {
                        if let Some(arg) = args.get(field_idx) {
                            if let Pattern::Term(PatternTerm::Var(v)) = arg {
                                if v == source_var {
                                    return Some(RewriteContext::Simple {
                                        category,
                                        constructor: constructor.clone(),
                                        field_idx,
                                        field_category: field_cat.clone(),
                                    });
                                }
                            }
                            // Check nested patterns
                            if let Some(ctx) = find_rewrite_context(arg, source_var, language) {
                                return Some(ctx);
                            }
                        }
                        field_idx += 1;
                    },
                    GrammarItem::Collection { element_type, .. } => {
                        if let Some(Pattern::Collection { elements, rest, .. }) =
                            args.get(field_idx)
                        {
                            // Check if this is a collection pattern containing source_var
                            for elem in elements {
                                if let Pattern::Term(PatternTerm::Var(v)) = elem {
                                    if v == source_var {
                                        return Some(RewriteContext::Collection {
                                            category,
                                            constructor: constructor.clone(),
                                            element_category: element_type.clone(),
                                            has_rest: rest.is_some(),
                                        });
                                    }
                                }
                            }
                        }
                        field_idx += 1;
                    },
                    GrammarItem::Binder { category: _binder_domain } => {
                        // Note: _binder_domain is the domain type (e.g., Name)
                        // We need the codomain type (e.g., Proc) for the body
                        let actual_body_category = get_binder_body_category(rule, field_idx)
                            .unwrap_or_else(|| rule.category.clone());

                        if let Some(arg) = args.get(field_idx) {
                            // Check if body contains source_var
                            if let Pattern::Term(PatternTerm::Lambda { body, .. }) = arg {
                                if pattern_contains_var(body, source_var) {
                                    return Some(RewriteContext::Binding {
                                        category,
                                        constructor: constructor.clone(),
                                        field_idx,
                                        body_category: actual_body_category,
                                    });
                                }
                            } else if let Pattern::Term(PatternTerm::Var(v)) = arg {
                                if v == source_var {
                                    return Some(RewriteContext::Binding {
                                        category,
                                        constructor: constructor.clone(),
                                        field_idx,
                                        body_category: actual_body_category,
                                    });
                                }
                            }
                        }
                        field_idx += 1;
                    },
                    GrammarItem::Terminal(_) => {
                        // Skip terminals
                    },
                }
            }
            None
        },
        PatternTerm::Lambda { body, .. } => find_rewrite_context(body, source_var, language),
        _ => None,
    }
}

/// Check if a pattern contains a variable
fn pattern_contains_var(pattern: &Pattern, var: &Ident) -> bool {
    match pattern {
        Pattern::Term(PatternTerm::Var(v)) => v == var,
        Pattern::Term(PatternTerm::Apply { args, .. }) => {
            args.iter().any(|a| pattern_contains_var(a, var))
        },
        Pattern::Term(PatternTerm::Lambda { body, .. }) => pattern_contains_var(body, var),
        Pattern::Collection { elements, .. } => {
            elements.iter().any(|e| pattern_contains_var(e, var))
        },
        _ => false,
    }
}

// =============================================================================
// Congruence Generators
// =============================================================================

/// Generate collection congruence: if element rewrites, collection rewrites
///
/// Example: `if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest})`
/// Generates:
/// ```text
/// rw_proc(parent, result) <--
///     proc(parent),
///     if let Proc::PPar(ref bag) = parent,
///     for (elem, _count) in bag.iter(),
///     rw_proc(elem.clone(), elem_rewritten),
///     let result = Proc::PPar({
///         let mut new_bag = bag.clone();
///         new_bag.remove(elem);
///         Proc::insert_into_ppar(&mut new_bag, elem_rewritten);
///         new_bag
///     });
/// ```
fn generate_collection_congruence(
    category: &Ident,
    constructor: &Ident,
    element_category: &Ident,
    _has_rest: bool,
    _language: &LanguageDef,
) -> Option<TokenStream> {
    let rn = relation_names(category);
    let cat_lower = &rn.cat_lower;
    let rw_rel = &rn.rw_rel;
    let elem_rn = relation_names(element_category);
    let elem_rw_rel = &elem_rn.rw_rel;
    let insert_helper = format_ident!("insert_into_{}", constructor.to_string().to_lowercase());

    Some(quote! {
        #rw_rel(<#category as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*parent)), result) <--
            #cat_lower(parent),
            if let #category::#constructor(ref bag) = parent,
            for (elem, _count) in bag.iter(),
            #elem_rw_rel(elem.clone(), elem_rewritten),
            let result = #category::#constructor({
                let mut new_bag = bag.clone();
                new_bag.remove(elem);
                #category::#insert_helper(&mut new_bag, elem_rewritten.clone());
                new_bag
            });
    })
}

/// Generate List (Vec-backed) element congruence: rewrites propagate into list elements by index.
///
/// Generates one rule per index: if the element at that index rewrites, the whole list rewrites
/// with that element replaced. Uses the literal variant (e.g. `List::Lit`) for the list type.
pub fn generate_list_native_congruence(
    category: &Ident,
    element_cat: &Ident,
    native_type: &syn::Type,
) -> Option<TokenStream> {
    let rn = relation_names(category);
    let cat_lower = &rn.cat_lower;
    let rw_rel = &rn.rw_rel;
    let elem_rn = relation_names(element_cat);
    let elem_rw_rel = &elem_rn.rw_rel;
    let literal_label = generate_literal_label(native_type);

    Some(quote! {
        #rw_rel(<#category as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lhs)), result) <--
            #cat_lower(lhs),
            if let #category::#literal_label(ref vec) = lhs,
            for (idx, elem) in vec.iter().enumerate(),
            #elem_rw_rel(elem.clone(), elem_rewritten),
            let result = #category::#literal_label({
                let mut v = vec.clone();
                v[idx] = elem_rewritten.clone();
                v
            });
    })
}

/// Generate binding congruence: if body under binder rewrites, term rewrites
///
/// Example: `if S => T then (PNew x S) => (PNew x T)`
/// Generates:
/// ```text
/// rw_proc(lhs, rhs) <--
///     proc(lhs),
///     if let Proc::PNew(ref scope) = lhs,
///     let (binder, body) = scope.clone().unbind(),
///     rw_proc((*body).clone(), body_rewritten),
///     let rhs = Proc::PNew(Scope::new(binder, Box::new(body_rewritten)));
/// ```
fn generate_binding_congruence(
    category: &Ident,
    constructor: &Ident,
    field_idx: usize,
    body_category: &Ident,
    language: &LanguageDef,
) -> Option<TokenStream> {
    let rn = relation_names(category);
    let cat_lower = &rn.cat_lower;
    let rw_rel = &rn.rw_rel;
    let body_rn = relation_names(body_category);
    let body_rw_rel = &body_rn.rw_rel;

    let rule = language.get_constructor(constructor)?;
    let n = count_nonterminals(rule);

    if n == 1 {
        // Simple case: just the scope (like PNew)
        // Use unsafe accessors to preserve binder identity (prevents infinite loops)
        Some(quote! {
            #rw_rel(<#category as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lhs)), rhs) <--
                #cat_lower(lhs),
                if let #category::#constructor(ref scope) = lhs,
                let binder = scope.unsafe_pattern().clone(),
                let body = scope.unsafe_body(),
                #body_rw_rel((**body).clone(), body_rewritten),
                let rhs = #category::#constructor(
                    mettail_runtime::Scope::from_parts_unsafe(binder.clone(), Box::new(body_rewritten.clone()))
                );
        })
    } else {
        // Multiple fields - need to handle position
        // Use unsafe accessors to preserve binder identity
        let vars: Vec<Ident> = (0..n).map(|i| format_ident!("x{}", i)).collect();
        let scope_var = &vars[field_idx];

        let recon_args: Vec<TokenStream> = vars.iter().enumerate()
            .map(|(i, v)| {
                if i == field_idx {
                    quote! { mettail_runtime::Scope::from_parts_unsafe(binder.clone(), Box::new(body_rewritten.clone())) }
                } else {
                    quote! { #v.clone() }
                }
            })
            .collect();

        Some(quote! {
            #rw_rel(<#category as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lhs)), rhs) <--
                #cat_lower(lhs),
                if let #category::#constructor(#(ref #vars),*) = lhs,
                let binder = #scope_var.unsafe_pattern().clone(),
                let body = #scope_var.unsafe_body(),
                #body_rw_rel((**body).clone(), body_rewritten),
                let rhs = #category::#constructor(#(#recon_args),*);
        })
    }
}

/// Generate a single consolidated rule for a group of simple congruence entries
/// that share the same (source_cat, field_cat).
///
/// Groups constructors with the same rewrite target field category into one rule
/// using inline match expressions for extraction and rebuild.
///
/// Uses thread-local Vec pools for zero-allocation iteration.
///
/// Before: N rules (one per constructor×field position)
/// After: 1 rule with N match arms
fn generate_consolidated_simple_congruence(
    source_cat: &Ident,
    field_cat: &Ident,
    entries: &[SimpleCongruenceEntry],
) -> Option<TokenStream> {
    if entries.is_empty() {
        return None;
    }

    let rn = relation_names(source_cat);
    let cat_lower = &rn.cat_lower;
    let rw_rel = &rn.rw_rel;
    let field_rn = relation_names(field_cat);
    let field_rw_rel = &field_rn.rw_rel;

    // Assign variant indices sequentially within this group
    // Group entries by constructor for extraction (one match arm per constructor)
    let mut by_constructor: BTreeMap<String, Vec<(usize, &SimpleCongruenceEntry)>> =
        BTreeMap::new();
    for (vi, entry) in entries.iter().enumerate() {
        by_constructor
            .entry(entry.constructor.to_string())
            .or_default()
            .push((vi, entry));
    }

    // === Extraction pool arms (one per constructor) ===
    let mut pool_arms = Vec::new();
    for ctor_entries in by_constructor.values() {
        let first = ctor_entries[0].1;
        let ctor = &first.constructor;
        let n = first.n_fields;

        // Determine which fields to bind (those being extracted)
        let extracted_indices: Vec<usize> = ctor_entries.iter().map(|(_, e)| e.field_idx).collect();

        let pattern_fields: Vec<TokenStream> = (0..n)
            .map(|i| {
                if extracted_indices.contains(&i) {
                    let xi = format_ident!("x{}", i);
                    quote! { ref #xi }
                } else {
                    quote! { _ }
                }
            })
            .collect();

        // Build push operations: one (field_val, vi) per entry (clone referent for non-Copy)
        let pushes: Vec<TokenStream> = ctor_entries
            .iter()
            .map(|(vi, e)| {
                let xi = format_ident!("x{}", e.field_idx);
                let vi_lit = *vi;
                if e.is_boxed {
                    quote! { buf.push((<#field_cat as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*#xi)), #vi_lit)); }
                } else {
                    quote! { buf.push((<#field_cat as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*#xi)), #vi_lit)); }
                }
            })
            .collect();

        pool_arms.push(PoolArm {
            pattern: quote! { #source_cat::#ctor(#(#pattern_fields),*) },
            pushes,
        });
    }

    // === Rebuild match arms (one per entry) ===
    let mut rebuild_arms = Vec::new();
    for (vi, entry) in entries.iter().enumerate() {
        let ctor = &entry.constructor;
        let n = entry.n_fields;
        let vi_lit = vi;

        // Pattern: bind all fields by ref except the replaced one
        let pattern_fields: Vec<TokenStream> = (0..n)
            .map(|i| {
                if i == entry.field_idx {
                    quote! { _ }
                } else {
                    let xi = format_ident!("x{}", i);
                    quote! { ref #xi }
                }
            })
            .collect();

        // Reconstruction: clone all fields (ref bindings so we don't move), replace the rewritten one
        let recon_args: Vec<TokenStream> = (0..n)
            .map(|i| {
                if i == entry.field_idx {
                    if entry.is_boxed {
                        quote! { Box::new(t.clone()) }
                    } else {
                        quote! { t.clone() }
                    }
                } else {
                    let xi = format_ident!("x{}", i);
                    quote! { #xi.clone() }
                }
            })
            .collect();

        rebuild_arms.push(quote! {
            (#source_cat::#ctor(#(#pattern_fields),*), #vi_lit) =>
                #source_cat::#ctor(#(#recon_args),*),
        });
    }

    // TLS pool for the (field_val, vi) pairs
    let pool_name = format_ident!(
        "POOL_{}_SCONG_{}",
        source_cat.to_string().to_uppercase(),
        field_cat.to_string().to_uppercase()
    );
    let elem_type = quote! { (#field_cat, usize) };
    let match_expr = quote! { lhs };
    let for_iter = generate_tls_pool_iter(&pool_name, &elem_type, &match_expr, &pool_arms);

    Some(quote! {
        #rw_rel(<#source_cat as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lhs)), match (lhs, vi) {
            #(#rebuild_arms)*
            _ => unreachable!(),
        }) <--
            #cat_lower(lhs),
            for (field_val, vi) in #for_iter,
            #field_rw_rel(field_val, t);
    })
}

// =============================================================================
// Helpers
// =============================================================================

// `count_nonterminal_fields` moved to `common::count_nonterminals`

/// Check if the AST stores this field as Box<T> (so reconstruction must use Box::new).
///
/// For term_context rules, Simple params with Base type become Box<ident>.
/// For old syntax, NonTerminal items become Box<cat>. Collections/Scope are not simple Box.
fn field_is_boxed_in_ast(rule: &GrammarRule, field_idx: usize) -> bool {
    if let Some(ref term_context) = rule.term_context {
        if let Some(TermParam::Simple { ty: TypeExpr::Base(_), .. }) = term_context.get(field_idx) {
            return true;
        }
        // Abstraction/MultiAbstraction => Scope (not a single Box for the param)
        // Collection => Vec/HashBag/etc.
        return false;
    }
    // Old syntax: NonTerminal and Collection count as fields; NonTerminal => Box<cat>
    let mut idx = 0;
    for item in &rule.items {
        match item {
            GrammarItem::NonTerminal(_) => {
                if idx == field_idx {
                    return true;
                }
                idx += 1;
            },
            GrammarItem::Collection { .. } | GrammarItem::Binder { .. } => {
                if idx == field_idx {
                    return false;
                }
                idx += 1;
            },
            GrammarItem::Terminal(_) => {},
        }
    }
    false
}

/// Get the body category for a binder at the given field index
///
/// For new syntax (term_context): extracts codomain from Arrow type
/// For old syntax: looks at the next NonTerminal after the Binder
fn get_binder_body_category(rule: &GrammarRule, field_idx: usize) -> Option<Ident> {
    // New syntax uses term_context
    if let Some(ref term_context) = rule.term_context {
        if let Some(TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. }) =
            term_context.get(field_idx)
        {
            if let TypeExpr::Arrow { codomain, .. } = ty {
                if let TypeExpr::Base(body_type) = codomain.as_ref() {
                    return Some(body_type.clone());
                }
            }
        }
        return None;
    }

    // Old syntax - find the NonTerminal that the binder binds into
    if !rule.bindings.is_empty() {
        for (binder_idx, body_indices) in &rule.bindings {
            // Check if this is the field we're looking for
            let mut idx = 0;
            for (i, item) in rule.items.iter().enumerate() {
                if i == *binder_idx {
                    if idx == field_idx {
                        // Found the binder - get the body type
                        if let Some(&body_item_idx) = body_indices.first() {
                            if let Some(GrammarItem::NonTerminal(body_cat)) =
                                rule.items.get(body_item_idx)
                            {
                                return Some(body_cat.clone());
                            }
                        }
                    }
                    idx += 1;
                } else if matches!(
                    item,
                    GrammarItem::NonTerminal(_) | GrammarItem::Collection { .. }
                ) {
                    idx += 1;
                }
            }
        }
    }

    None
}
