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
    collect_nonterminal_fields, count_nonterminals, generate_tls_pool_iter, has_collection_field,
    is_multi_binder, relation_names, PoolArm,
};
use crate::gen::native::is_list_literal_rule;
use crate::ast::grammar::{GrammarItem, GrammarRule};
use crate::ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::BTreeSet;
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
///
/// Uses thread-local Vec pools to avoid heap allocation in steady state.
/// The empty fallthrough (`_ => {}`) does zero work.
///
/// Prunes dead cross-category rules using compile-time reachability analysis.
/// Only generates rules for (src, tgt) pairs reachable through user-defined constructors.
pub fn generate_consolidated_deconstruction_rules(
    language: &LanguageDef,
    reachable: &BTreeSet<(String, String)>,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for src_type in &language.types {
        let src = &src_type.name;
        let src_rn = relation_names(src);
        let src_lower = &src_rn.cat_lower;

        for tgt_type in &language.types {
            let tgt = &tgt_type.name;

            // Skip unreachable (src, tgt) pairs — their rules would iterate empty relations
            if !reachable.contains(&(src.to_string(), tgt.to_string())) {
                continue;
            }

            let tgt_rn = relation_names(tgt);
            let tgt_lower = &tgt_rn.cat_lower;

            // Collect match arms for this (src, tgt) pair
            let pool_arms = generate_subterm_pool_arms(language, src, tgt);

            if pool_arms.is_empty() {
                continue; // No subterms to extract — skip the rule
            }

            // Unique pool name per (src, tgt) pair
            let pool_name = format_ident!(
                "POOL_{}_{}",
                src.to_string().to_uppercase(),
                tgt.to_string().to_uppercase()
            );
            let tgt_type_ts = quote! { #tgt };
            let match_expr = quote! { t };

            let for_iter =
                generate_tls_pool_iter(&pool_name, &tgt_type_ts, &match_expr, &pool_arms);

            // One rule per (src, tgt) pair with TLS-pooled iteration:
            // tgt(sub.clone()) <-- src(t), for sub in { ...tls pool... }.into_iter();
            rules.push(quote! {
                #tgt_lower(sub.clone()) <--
                    #src_lower(t),
                    for sub in #for_iter;
            });
        }
    }

    rules
}

// =============================================================================
// Area 1: Subterm extraction helper generation
// =============================================================================

/// Generate PoolArm entries for the subterm extraction of a (src, tgt) pair.
///
/// Returns PoolArm values for use with `generate_tls_pool_iter`.
fn generate_subterm_pool_arms(language: &LanguageDef, src: &Ident, tgt: &Ident) -> Vec<PoolArm> {
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
        // List literal (and similar): single field is Vec<elem>, not same-category subterms
        if is_list_literal_rule(rule, language) && src == tgt {
            continue;
        }

        if let Some(arm) = generate_user_constructor_pool_arm(rule, src, tgt) {
            arms.push(arm);
        }
    }

    // 2. Auto-generated variants (Apply, MApply, Lam, MLam) for each domain
    for domain_type in &language.types {
        let domain = &domain_type.name;
        let auto = generate_auto_variant_pool_arms(src, tgt, domain);
        arms.extend(auto);
    }

    arms
}

/// Generate a PoolArm for a user-defined constructor.
fn generate_user_constructor_pool_arm(
    rule: &GrammarRule,
    src: &Ident,
    tgt: &Ident,
) -> Option<PoolArm> {
    if !rule.bindings.is_empty() {
        generate_binding_constructor_pool_arm(rule, src, tgt)
    } else {
        generate_regular_constructor_pool_arm(rule, src, tgt)
    }
}

/// Generate a PoolArm for a regular (non-binding, non-collection) constructor.
///
/// Extracts all fields whose type matches `tgt`, skipping Var and Integer fields.
fn generate_regular_constructor_pool_arm(
    rule: &GrammarRule,
    src: &Ident,
    tgt: &Ident,
) -> Option<PoolArm> {
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
                quote! { ref #name }
            } else {
                quote! { _ }
            }
        })
        .collect();

    let pushes: Vec<TokenStream> = matching_indices
        .iter()
        .map(|&i| {
            let name = format_ident!("f{}", i);
            quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*#name))); }
        })
        .collect();

    Some(PoolArm {
        pattern: quote! { #src::#label(#(#field_bindings),*) },
        pushes,
    })
}

/// Generate a PoolArm for a binding constructor (e.g., PNew).
///
/// Extracts body from scope if body_cat matches tgt, plus any other
/// non-binder non-body fields that match tgt.
fn generate_binding_constructor_pool_arm(
    rule: &GrammarRule,
    src: &Ident,
    tgt: &Ident,
) -> Option<PoolArm> {
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
        Some(PoolArm {
            pattern: quote! { #src::#label(ref scope) },
            pushes: vec![quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*scope.inner().unsafe_body))); }],
        })
    } else {
        // Multiple fields: scope + other fields
        // Build pattern and extraction
        let mut field_bindings = Vec::with_capacity(n);
        let mut pushes = Vec::new();
        let mut ast_field_idx = 0usize;

        for (i, item) in rule.items.iter().enumerate() {
            if i == *_binder_idx {
                continue; // Skip binder
            } else if i == body_idx {
                let scope_name = format_ident!("scope_f");
                field_bindings.push(quote! { ref #scope_name });
                if body_matches {
                    pushes.push(
                        quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*#scope_name.inner().unsafe_body))); },
                    );
                }
            } else if let GrammarItem::NonTerminal(cat) = item {
                let name = format_ident!("f{}", ast_field_idx);
                let cat_str = cat.to_string();
                if cat_str != "Var" && cat_str != "Integer" && *cat == *tgt {
                    field_bindings.push(quote! { ref #name });
                    pushes.push(quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*#name))); });
                } else {
                    field_bindings.push(quote! { _ });
                }
                ast_field_idx += 1;
            }
        }

        if pushes.is_empty() {
            return None;
        }

        Some(PoolArm {
            pattern: quote! { #src::#label(#(#field_bindings),*) },
            pushes,
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
    reachable: &BTreeSet<(String, String)>,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    let rn = relation_names(category);
    let cat_lower = &rn.cat_lower;
    let rw_cat = &rn.rw_rel;
    let cat_upper = category.to_string().to_uppercase();
    let cat_str = category.to_string();

    // Only include domains reachable from this category
    let domains: Vec<&Ident> = language
        .types
        .iter()
        .filter(|t| reachable.contains(&(cat_str.clone(), t.name.to_string())))
        .map(|t| &t.name)
        .collect();

    // === Lam congruence: ONE rule per source category ===
    // Merges Apply{Dom}-lam and MApply{Dom}-lam across all domains.
    // The lam field is always Box<Cat> regardless of domain.
    let mut lam_pool_arms = Vec::new();
    let mut lam_rebuild_arms = Vec::new();

    for domain in &domains {
        let apply_variant = format_ident!("Apply{}", domain);
        let mapply_variant = format_ident!("MApply{}", domain);

        // Extract lam from Apply{Dom} and MApply{Dom} (clone referent for non-Copy categories)
        lam_pool_arms.push(PoolArm {
            pattern: quote! { #category::#apply_variant(ref lam, _) },
            pushes: vec![quote! { buf.push(<#category as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lam))); }],
        });
        lam_pool_arms.push(PoolArm {
            pattern: quote! { #category::#mapply_variant(ref lam, _) },
            pushes: vec![quote! { buf.push(<#category as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lam))); }],
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

    if !lam_pool_arms.is_empty() {
        let pool_name = format_ident!("POOL_{}_CONG_LAM", cat_upper);
        let elem_type = quote! { #category };
        let match_expr = quote! { t };
        let for_iter = generate_tls_pool_iter(&pool_name, &elem_type, &match_expr, &lam_pool_arms);

        rules.push(quote! {
            #rw_cat(
                <#category as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*t)),
                match t {
                    #(#lam_rebuild_arms)*
                    _ => unreachable!(),
                },
            ) <--
                #cat_lower(t),
                for lam in #for_iter,
                #rw_cat(lam, new_lam);
        });
    }

    // === Arg congruence: one rule per (cat, domain) pair ===
    // Only for Apply{Dom} (not MApply, which has Vec<Dom> args).
    for domain in &domains {
        let dom_rn = relation_names(domain);
        let rw_domain = &dom_rn.rw_rel;
        let apply_variant = format_ident!("Apply{}", domain);
        let dom_upper = domain.to_string().to_uppercase();

        let pool_name = format_ident!("POOL_{}_CONG_ARG_{}", cat_upper, dom_upper);
        let elem_type = quote! { #domain };
        let match_expr = quote! { t };
        let pool_arms = vec![PoolArm {
            pattern: quote! { #category::#apply_variant(_, ref arg) },
            pushes: vec![quote! { buf.push(<#domain as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*arg))); }],
        }];
        let for_iter = generate_tls_pool_iter(&pool_name, &elem_type, &match_expr, &pool_arms);

        rules.push(quote! {
            #rw_cat(
                <#category as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*t)),
                match t {
                    #category::#apply_variant(lam, _) =>
                        #category::#apply_variant(lam.clone(), Box::new(new_arg.clone())),
                    _ => unreachable!(),
                },
            ) <--
                #cat_lower(t),
                for arg in #for_iter,
                #rw_domain(arg, new_arg);
        });
    }

    rules
}

/// Generate PoolArm entries for auto-generated variants (Apply, MApply, Lam, MLam)
/// for a specific domain category.
fn generate_auto_variant_pool_arms(src: &Ident, tgt: &Ident, domain: &Ident) -> Vec<PoolArm> {
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
        arms.push(PoolArm {
            pattern: quote! { #src::#apply_variant(ref lam, ref arg) },
            pushes: vec![
                quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lam))); },
                quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*arg))); },
            ],
        });
    } else if src_is_tgt {
        // Cross-category Apply: only lam is src
        arms.push(PoolArm {
            pattern: quote! { #src::#apply_variant(ref lam, _) },
            pushes: vec![quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lam))); }],
        });
    } else if domain_is_tgt {
        // Cross-category Apply: only arg is domain (== tgt)
        arms.push(PoolArm {
            pattern: quote! { #src::#apply_variant(_, ref arg) },
            pushes: vec![quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*arg))); }],
        });
    }

    // For MApply{domain}(lam, args):
    //   - lam: Box<src> → contributes to (src, src) helper
    //   - args: Vec<domain> → contributes to (src, domain) helper
    if src_is_tgt && domain_is_src {
        // Same-category MApply: lam + all args are src
        arms.push(PoolArm {
            pattern: quote! { #src::#mapply_variant(ref lam, ref args) },
            pushes: vec![
                quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lam))); },
                quote! { buf.extend(args.iter().cloned()); },
            ],
        });
    } else if src_is_tgt {
        // Cross-category MApply: only lam is src
        arms.push(PoolArm {
            pattern: quote! { #src::#mapply_variant(ref lam, _) },
            pushes: vec![quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*lam))); }],
        });
    } else if domain_is_tgt {
        // Cross-category MApply: only args are domain (== tgt)
        arms.push(PoolArm {
            pattern: quote! { #src::#mapply_variant(_, ref args) },
            pushes: vec![quote! { buf.extend(args.iter().cloned()); }],
        });
    }

    // For Lam{domain}(scope) and MLam{domain}(scope):
    //   - body: src → contributes to (src, src) helper only
    if src_is_tgt {
        arms.push(PoolArm {
            pattern: quote! { #src::#lam_variant(ref scope) },
            pushes: vec![quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*scope.inner().unsafe_body))); }],
        });
        arms.push(PoolArm {
            pattern: quote! { #src::#mlam_variant(ref scope) },
            pushes: vec![quote! { buf.push(<#tgt as std::clone::Clone>::clone(std::borrow::Borrow::borrow(&*scope.inner().unsafe_body))); }],
        });
    }

    arms
}
