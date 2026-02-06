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

use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use crate::ast::language::{LanguageDef, RewriteRule};
use crate::ast::pattern::{Pattern, PatternTerm};
use crate::ast::types::TypeExpr;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

pub fn generate_all_explicit_congruences(language: &LanguageDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for rewrite in &language.rewrites {
        // Only process rules with congruence premise
        if rewrite.is_congruence_rule() {
            if let Some(rule) = generate_explicit_congruence(rewrite, language) {
                rules.push(rule);
            }
        }
    }

    rules
}

/// Process an explicit congruence rule: `| S ~> T |- LHS ~> RHS`
///
/// This is the main entry point that replaces the scattered code in
/// analysis.rs, binding.rs, collection.rs, regular.rs, projections.rs.
pub fn generate_explicit_congruence(
    rule: &RewriteRule,
    language: &LanguageDef,
) -> Option<TokenStream> {
    // Must have a congruence premise (S ~> T)
    let (source_var, _target_var) = rule.congruence_premise()?;

    // Analyze LHS to find where source_var appears and in what context
    let context = find_rewrite_context(&rule.left, source_var, language)?;

    // Generate appropriate congruence based on context
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
        } => generate_simple_congruence(
            &category,
            &constructor,
            field_idx,
            &field_category,
            language,
        ),
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
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let rw_rel = format_ident!("rw_{}", category.to_string().to_lowercase());
    let elem_rw_rel = format_ident!("rw_{}", element_category.to_string().to_lowercase());
    let insert_helper = format_ident!("insert_into_{}", constructor.to_string().to_lowercase());

    Some(quote! {
        #rw_rel(parent.clone(), result) <--
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
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let rw_rel = format_ident!("rw_{}", category.to_string().to_lowercase());
    let body_rw_rel = format_ident!("rw_{}", body_category.to_string().to_lowercase());

    let rule = language.get_constructor(constructor)?;
    let n = count_nonterminal_fields(rule);

    if n == 1 {
        // Simple case: just the scope (like PNew)
        // Use unsafe accessors to preserve binder identity (prevents infinite loops)
        Some(quote! {
            #rw_rel(lhs.clone(), rhs) <--
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
            #rw_rel(lhs.clone(), rhs) <--
                #cat_lower(lhs),
                if let #category::#constructor(#(ref #vars),*) = lhs,
                let binder = #scope_var.unsafe_pattern().clone(),
                let body = #scope_var.unsafe_body(),
                #body_rw_rel((**body).clone(), body_rewritten),
                let rhs = #category::#constructor(#(#recon_args),*);
        })
    }
}

/// Generate simple congruence: if field rewrites, term rewrites
///
/// Example: `if S => T then (PAmb N S) => (PAmb N T)`
/// Generates:
/// ```text
/// rw_proc(lhs, rhs) <--
///     proc(lhs),
///     if let Proc::PAmb(ref x0, ref x1) = lhs,
///     rw_proc((*x1).clone(), t),
///     let rhs = Proc::PAmb(x0.clone(), Box::new(t));
/// ```
fn generate_simple_congruence(
    category: &Ident,
    constructor: &Ident,
    field_idx: usize,
    field_category: &Ident,
    language: &LanguageDef,
) -> Option<TokenStream> {
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let rw_rel = format_ident!("rw_{}", category.to_string().to_lowercase());
    let field_rw_rel = format_ident!("rw_{}", field_category.to_string().to_lowercase());

    let rule = language.get_constructor(constructor)?;
    let n = count_nonterminal_fields(rule);
    let vars: Vec<Ident> = (0..n).map(|i| format_ident!("x{}", i)).collect();

    let s_var = &vars[field_idx];
    let t_var = format_ident!("t");

    // Determine if field is stored as Box in the AST (recursive or cross-category both use Box)
    let needs_box = is_recursive_field(rule, field_idx);
    let rewritten_field_is_boxed = field_is_boxed_in_ast(rule, field_idx);

    // Source expression: pass the inner value to the rewrite relation (rw_cat expects the term type, not Box)
    let s_expr = if needs_box || rewritten_field_is_boxed {
        quote! { (**#s_var).clone() }
    } else {
        quote! { (*#s_var).clone() }
    };

    // Reconstruction: vars from the pattern are already &Box<T>, so clone() gives Box<T>.
    // Only the rewritten field (t_var) is a bare value and must be wrapped in Box::new when the AST expects Box.
    let recon_args: Vec<TokenStream> = vars
        .iter()
        .enumerate()
        .map(|(i, v)| {
            if i == field_idx {
                if rewritten_field_is_boxed {
                    quote! { Box::new(#t_var.clone()) }
                } else {
                    quote! { #t_var.clone() }
                }
            } else {
                quote! { #v.clone() }
            }
        })
        .collect();

    Some(quote! {
        #rw_rel(lhs.clone(), rhs) <--
            #cat_lower(lhs),
            if let #category::#constructor(#(ref #vars),*) = lhs,
            #field_rw_rel(#s_expr, #t_var),
            let rhs = #category::#constructor(#(#recon_args),*);
    })
}

// =============================================================================
// Helpers
// =============================================================================

/// Count actual AST fields in a grammar rule
///
/// This accounts for the fact that:
/// - New syntax (term_context): Abstraction = 1 Scope field
/// - Old syntax with bindings: Binder + body NonTerminal = 1 Scope field
fn count_nonterminal_fields(rule: &GrammarRule) -> usize {
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

/// Check if a field is recursive (same category as constructor result)
fn is_recursive_field(rule: &GrammarRule, field_idx: usize) -> bool {
    let mut idx = 0;
    for item in &rule.items {
        match item {
            GrammarItem::NonTerminal(cat) => {
                if idx == field_idx {
                    return cat == &rule.category;
                }
                idx += 1;
            },
            GrammarItem::Collection { .. } | GrammarItem::Binder { .. } => {
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
