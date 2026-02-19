//! Helper function code generation for Ascent rule consolidation.
//!
//! Generates normal Rust helper functions that replace many per-constructor
//! Ascent rules with a single rule using `for` iteration.
//!
//! ## Strategy
//!
//! Instead of N separate Ascent rules like:
//! ```text
//! cat(f0.as_ref().clone()) <-- cat(t), if let Cat::A(f0) = t;
//! cat(f0.as_ref().clone()), cat(f1.as_ref().clone()) <-- cat(t), if let Cat::B(f0, f1) = t;
//! ```
//!
//! We generate one helper function + one rule:
//! ```text
//! fn all_subterms_cat_cat(t: &Cat) -> Vec<Cat> { match t { ... } }
//! cat(sub.clone()) <-- cat(t), for sub in all_subterms_cat_cat(t).into_iter();
//! ```

use super::common::{
    collect_nonterminal_fields, count_nonterminals, has_collection_field, is_multi_binder,
    relation_names,
};
use crate::ast::grammar::{GrammarItem, GrammarRule};
use crate::ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

/// Generate all helper functions for subterm extraction (Area 1).
///
/// Returns an empty TokenStream - all logic is now inline in Ascent rules.
/// This function exists for forward compatibility with Areas 2-6.
pub fn generate_helper_functions(_language: &LanguageDef) -> TokenStream {
    // Helper functions are now generated inline within Ascent rules
    // (see generate_consolidated_deconstruction_rules)
    quote! {}
}

/// Generate consolidated Ascent rules with inline match expressions.
///
/// Returns rules that replace the per-constructor deconstruction rules.
/// Each rule uses an inline match expression in a `for` clause to iterate
/// over subterms, replacing many individual rules with one per (src, tgt) pair.
pub fn generate_consolidated_deconstruction_rules(
    language: &LanguageDef,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for src_type in &language.types {
        let src = &src_type.name;
        let src_rn = relation_names(src);
        let src_lower = &src_rn.cat_lower;

        for tgt_type in &language.types {
            let tgt = &tgt_type.name;
            let tgt_rn = relation_names(tgt);
            let tgt_lower = &tgt_rn.cat_lower;

            // Collect match arms for this (src, tgt) pair
            let arms = generate_subterm_arms(language, src, tgt);

            if arms.is_empty() {
                continue; // No subterms to extract — skip the rule
            }

            // One rule per (src, tgt) pair with inline match:
            // tgt(sub.clone()) <-- src(t), for sub in { match t { ...arms..., _ => vec![] } }.into_iter();
            rules.push(quote! {
                #tgt_lower(sub.clone()) <--
                    #src_lower(t),
                    for sub in (match t {
                        #(#arms)*
                        _ => vec![],
                    }).into_iter();
            });
        }
    }

    rules
}

// =============================================================================
// Area 1: Subterm extraction helper generation
// =============================================================================

/// Generate match arms for the subterm extraction of a (src, tgt) pair.
///
/// Returns the match arms (without the surrounding match/function).
fn generate_subterm_arms(language: &LanguageDef, src: &Ident, tgt: &Ident) -> Vec<TokenStream> {
    let mut arms = Vec::new();

    // 1. User-defined constructors
    for rule in language.terms.iter().filter(|r| r.category == *src) {
        // Skip collection-only and multi-binder constructors (they have special rules)
        if has_collection_field(rule) {
            continue;
        }
        if is_multi_binder(rule) {
            continue;
        }

        if let Some(arm) = generate_user_constructor_arm(rule, src, tgt) {
            arms.push(arm);
        }
    }

    // 2. Auto-generated variants (Apply, MApply, Lam, MLam) for each domain
    for domain_type in &language.types {
        let domain = &domain_type.name;
        let auto = generate_auto_variant_arms(src, tgt, domain);
        arms.extend(auto);
    }

    arms
}

/// Generate match arm for a user-defined constructor.
fn generate_user_constructor_arm(
    rule: &GrammarRule,
    src: &Ident,
    tgt: &Ident,
) -> Option<TokenStream> {
    if !rule.bindings.is_empty() {
        generate_binding_constructor_arm(rule, src, tgt)
    } else {
        generate_regular_constructor_arm(rule, src, tgt)
    }
}

/// Generate match arm for a regular (non-binding, non-collection) constructor.
///
/// Extracts all fields whose type matches `tgt`, skipping Var and Integer fields.
fn generate_regular_constructor_arm(
    rule: &GrammarRule,
    src: &Ident,
    tgt: &Ident,
) -> Option<TokenStream> {
    let label = &rule.label;
    let fields = collect_nonterminal_fields(rule);

    if fields.is_empty() {
        return None; // No fields to extract (nullary constructor)
    }

    // Find indices of fields matching the target category
    let matching_indices: Vec<usize> = fields
        .iter()
        .enumerate()
        .filter(|(_, (_, field_type))| {
            let ft_str = field_type.to_string();
            // Skip Var and Integer — they are built-in types, not exported categories
            ft_str != "Var" && ft_str != "Integer" && **field_type == *tgt
        })
        .map(|(i, _)| i)
        .collect();

    if matching_indices.is_empty() {
        return None;
    }

    let total = fields.len();
    let field_bindings: Vec<TokenStream> = (0..total)
        .map(|i| {
            if matching_indices.contains(&i) {
                let name = format_ident!("f{}", i);
                quote! { #name }
            } else {
                quote! { _ }
            }
        })
        .collect();

    let extractions: Vec<TokenStream> = matching_indices
        .iter()
        .map(|&i| {
            let name = format_ident!("f{}", i);
            quote! { #name.as_ref().clone() }
        })
        .collect();

    Some(quote! {
        #src::#label(#(#field_bindings),*) => vec![#(#extractions),*],
    })
}

/// Generate match arm for a binding constructor (e.g., PNew).
///
/// Extracts body from scope if body_cat matches tgt, plus any other
/// non-binder non-body fields that match tgt.
fn generate_binding_constructor_arm(
    rule: &GrammarRule,
    src: &Ident,
    tgt: &Ident,
) -> Option<TokenStream> {
    let label = &rule.label;
    let (_binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Get body category
    let body_cat = match &rule.items[body_idx] {
        GrammarItem::NonTerminal(cat) => cat,
        _ => return None,
    };

    let n = count_nonterminals(rule);

    // Collect what to extract
    let body_matches = *body_cat == *tgt;

    if n == 1 {
        // Single field: just the scope
        if !body_matches {
            return None;
        }
        Some(quote! {
            #src::#label(scope) => vec![scope.inner().unsafe_body.as_ref().clone()],
        })
    } else {
        // Multiple fields: scope + other fields
        // Build pattern and extraction
        let mut field_bindings = Vec::with_capacity(n);
        let mut extractions = Vec::new();
        let mut ast_field_idx = 0usize;

        for (i, item) in rule.items.iter().enumerate() {
            if i == *_binder_idx {
                continue; // Skip binder
            } else if i == body_idx {
                let scope_name = format_ident!("scope_f");
                field_bindings.push(quote! { #scope_name });
                if body_matches {
                    extractions.push(quote! { #scope_name.inner().unsafe_body.as_ref().clone() });
                }
            } else if let GrammarItem::NonTerminal(cat) = item {
                let name = format_ident!("f{}", ast_field_idx);
                let cat_str = cat.to_string();
                if cat_str != "Var" && cat_str != "Integer" && *cat == *tgt {
                    field_bindings.push(quote! { #name });
                    extractions.push(quote! { #name.as_ref().clone() });
                } else {
                    field_bindings.push(quote! { _ });
                }
                ast_field_idx += 1;
            }
        }

        if extractions.is_empty() {
            return None;
        }

        Some(quote! {
            #src::#label(#(#field_bindings),*) => vec![#(#extractions),*],
        })
    }
}

// =============================================================================
// Area 2: Auto-variant congruence consolidation
// =============================================================================

/// Generate consolidated auto-variant congruence rules for a source category.
///
/// Consolidates Apply and MApply lam congruence across all domains into ONE rule,
/// and generates one arg congruence rule per domain.
///
/// Before: 3C rules per category (Apply-lam, Apply-arg, MApply-lam × C domains)
/// After: 1 + C rules per category (1 lam rule + C arg rules)
/// Savings: (2C-1) per category, (2C-1)×C total
pub fn generate_consolidated_congruence_rules(
    category: &Ident,
    language: &LanguageDef,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    let rn = relation_names(category);
    let cat_lower = &rn.cat_lower;
    let rw_cat = &rn.rw_rel;

    let domains: Vec<&Ident> = language.types.iter().map(|t| &t.name).collect();

    // === Lam congruence: ONE rule per source category ===
    // Merges Apply{Dom}-lam and MApply{Dom}-lam across all domains.
    // The lam field is always Box<Cat> regardless of domain.
    let mut lam_extract_arms = Vec::new();
    let mut lam_rebuild_arms = Vec::new();

    for domain in &domains {
        let apply_variant = format_ident!("Apply{}", domain);
        let mapply_variant = format_ident!("MApply{}", domain);

        // Extract lam from Apply{Dom} and MApply{Dom}
        lam_extract_arms.push(quote! {
            #category::#apply_variant(lam, _) => vec![lam.as_ref().clone()],
        });
        lam_extract_arms.push(quote! {
            #category::#mapply_variant(lam, _) => vec![lam.as_ref().clone()],
        });

        // Rebuild with new lam
        lam_rebuild_arms.push(quote! {
            #category::#apply_variant(_, arg) =>
                #category::#apply_variant(Box::new(new_lam.clone()), arg.clone()),
        });
        lam_rebuild_arms.push(quote! {
            #category::#mapply_variant(_, args) =>
                #category::#mapply_variant(Box::new(new_lam.clone()), args.clone()),
        });
    }

    if !lam_extract_arms.is_empty() {
        rules.push(quote! {
            #rw_cat(t.clone(), match t {
                #(#lam_rebuild_arms)*
                _ => unreachable!(),
            }) <--
                #cat_lower(t),
                for lam in (match t {
                    #(#lam_extract_arms)*
                    _ => vec![],
                }).into_iter(),
                #rw_cat(lam, new_lam);
        });
    }

    // === Arg congruence: one rule per (cat, domain) pair ===
    // Only for Apply{Dom} (not MApply, which has Vec<Dom> args).
    for domain in &domains {
        let dom_rn = relation_names(domain);
        let rw_domain = &dom_rn.rw_rel;
        let apply_variant = format_ident!("Apply{}", domain);

        rules.push(quote! {
            #rw_cat(t.clone(), match t {
                #category::#apply_variant(lam, _) =>
                    #category::#apply_variant(lam.clone(), Box::new(new_arg.clone())),
                _ => unreachable!(),
            }) <--
                #cat_lower(t),
                for arg in (match t {
                    #category::#apply_variant(_, arg) => vec![arg.as_ref().clone()],
                    _ => vec![],
                }).into_iter(),
                #rw_domain(arg, new_arg);
        });
    }

    rules
}

/// Generate match arms for auto-generated variants (Apply, MApply, Lam, MLam)
/// for a specific domain category.
fn generate_auto_variant_arms(src: &Ident, tgt: &Ident, domain: &Ident) -> Vec<TokenStream> {
    let mut arms = Vec::new();
    let src_is_tgt = *src == *tgt;
    let domain_is_tgt = *domain == *tgt;
    let domain_is_src = *domain == *src;

    let apply_variant = format_ident!("Apply{}", domain);
    let mapply_variant = format_ident!("MApply{}", domain);
    let lam_variant = format_ident!("Lam{}", domain);
    let mlam_variant = format_ident!("MLam{}", domain);

    // For Apply{domain}(lam, arg):
    //   - lam: Box<src> → contributes to (src, src) helper
    //   - arg: Box<domain> → contributes to (src, domain) helper
    if src_is_tgt && domain_is_src {
        // Same-category Apply: both lam and arg are src
        arms.push(quote! {
            #src::#apply_variant(lam, arg) => vec![lam.as_ref().clone(), arg.as_ref().clone()],
        });
    } else if src_is_tgt {
        // Cross-category Apply: only lam is src
        arms.push(quote! {
            #src::#apply_variant(lam, _) => vec![lam.as_ref().clone()],
        });
    } else if domain_is_tgt {
        // Cross-category Apply: only arg is domain (== tgt)
        arms.push(quote! {
            #src::#apply_variant(_, arg) => vec![arg.as_ref().clone()],
        });
    }

    // For MApply{domain}(lam, args):
    //   - lam: Box<src> → contributes to (src, src) helper
    //   - args: Vec<domain> → contributes to (src, domain) helper
    if src_is_tgt && domain_is_src {
        // Same-category MApply: lam + all args are src
        arms.push(quote! {
            #src::#mapply_variant(lam, args) => {
                let mut v = Vec::with_capacity(1 + args.len());
                v.push(lam.as_ref().clone());
                v.extend(args.iter().cloned());
                v
            },
        });
    } else if src_is_tgt {
        // Cross-category MApply: only lam is src
        arms.push(quote! {
            #src::#mapply_variant(lam, _) => vec![lam.as_ref().clone()],
        });
    } else if domain_is_tgt {
        // Cross-category MApply: only args are domain (== tgt)
        arms.push(quote! {
            #src::#mapply_variant(_, args) => args.iter().cloned().collect(),
        });
    }

    // For Lam{domain}(scope) and MLam{domain}(scope):
    //   - body: src → contributes to (src, src) helper only
    if src_is_tgt {
        arms.push(quote! {
            #src::#lam_variant(scope) => vec![scope.inner().unsafe_body.as_ref().clone()],
        });
        arms.push(quote! {
            #src::#mlam_variant(scope) => vec![scope.inner().unsafe_body.as_ref().clone()],
        });
    }

    arms
}
