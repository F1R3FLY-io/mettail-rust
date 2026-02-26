// Pretty-printing generation for MeTTaIL languages
//
// This module generates Display trait implementations for AST types,
// allowing them to be pretty-printed back to source syntax.

#![allow(clippy::cmp_owned)]

use crate::ast::{
    grammar::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam},
    language::LanguageDef,
    types::TypeExpr,
};
use crate::gen::native::{has_native_type, native_type_to_string};
use crate::gen::{generate_literal_label, generate_var_label, is_literal_rule, is_var_rule};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

/// Generate Display implementations for all exported categories
pub fn generate_display(language: &LanguageDef) -> TokenStream {
    // Group rules by category
    let mut rules_by_cat: HashMap<String, Vec<&GrammarRule>> = HashMap::new();

    for rule in &language.terms {
        let cat_name = rule.category.to_string();
        rules_by_cat.entry(cat_name).or_default().push(rule);
    }

    // Generate Display impl for each exported category
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let cat_name = &lang_type.name;

            let rules = rules_by_cat
                .get(&cat_name.to_string())
                .map(|v| v.as_slice())
                .unwrap_or(&[]);

            generate_display_impl(cat_name, rules, language)
        })
        .collect();

    quote! {
        #(#impls)*
    }
}

/// Generate Display impl for a single category
fn generate_display_impl(
    category: &syn::Ident,
    rules: &[&GrammarRule],
    language: &LanguageDef,
) -> TokenStream {
    let mut match_arms: Vec<TokenStream> = rules
        .iter()
        .map(|rule| generate_display_arm(rule, language))
        .collect();

    // Check if Var variant was auto-generated (include List/Bag LVar/BVar for at(x,0), etc.)
    let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));
    if !has_var_rule {
        let var_arm = generate_auto_var_display_arm(category);
        match_arms.push(var_arm);
    }

    // Display for List/Bag literal variants (ListLit, BagLit)
    if let Some(ref ck) = language.get_type(category).and_then(|t| t.collection_kind.clone()) {
        use crate::ast::language::CollectionCategory;
        use proc_macro2::Span;
        use syn::LitStr;
        match ck {
            CollectionCategory::List(d) => {
                let open = LitStr::new(&d.open, Span::call_site());
                let close = LitStr::new(&d.close, Span::call_site());
                let sep = LitStr::new(&d.sep, Span::call_site());
                let lit_label = syn::Ident::new("ListLit", Span::call_site());
                match_arms.push(quote! {
                    #category::#lit_label(ref list) => {
                        let parts: Vec<_> = list.iter().map(|e| e.to_string()).collect();
                        write!(f, "{}", #open)?;
                        for (i, p) in parts.iter().enumerate() {
                            if i > 0 { write!(f, "{}", #sep)?; }
                            write!(f, "{}", p)?;
                        }
                        write!(f, "{}", #close)
                    }
                });
            },
            CollectionCategory::Bag(d) => {
                let open = LitStr::new(&d.open, Span::call_site());
                let close = LitStr::new(&d.close, Span::call_site());
                let sep = LitStr::new(&d.sep, Span::call_site());
                let lit_label = syn::Ident::new("BagLit", Span::call_site());
                match_arms.push(quote! {
                    #category::#lit_label(ref bag) => {
                        let parts: Vec<_> = bag
                            .iter()
                            .flat_map(|(elem, count)| std::iter::repeat(elem.to_string()).take(count))
                            .collect::<Vec<_>>();
                        write!(f, "{}", #open)?;
                        for (i, p) in parts.iter().enumerate() {
                            if i > 0 { write!(f, "{}", #sep)?; }
                            write!(f, "{}", p)?;
                        }
                        write!(f, "{}", #close)
                    }
                });
            },
        }
    }

    // Check if NumLit variant was auto-generated (for native types).
    // Skip for collection categories (List/Bag) — they already have ListLit/BagLit display arms above.
    let has_literal_rule = rules.iter().any(|rule| is_literal_rule(rule));
    let is_collection_category = language.get_type(category).and_then(|t| t.collection_kind.as_ref()).is_some();
    if let Some(native_type) = has_native_type(category, language) {
        if !has_literal_rule && !is_collection_category {
            let literal_arm = generate_auto_literal_display_arm(category, native_type);
            match_arms.push(literal_arm);
        }
    }

    // Generate display arms for auto-generated lambda variants (skip for collection categories)
    if language.get_type(category).and_then(|t| t.collection_kind.as_ref()).is_none() {
    for domain_lang_type in &language.types {
        let domain_name = &domain_lang_type.name;

        // Single-binder lambda: Lam{Domain}
        let lam_variant =
            syn::Ident::new(&format!("Lam{}", domain_name), proc_macro2::Span::call_site());
        match_arms.push(quote! {
            #category::#lam_variant(scope) => {
                let (binder, body) = scope.clone().unbind();
                let var_name = binder.0.pretty_name.as_deref().unwrap_or("?");
                write!(f, "^{}.{{{}}}", var_name, body)
            }
        });

        // Multi-binder lambda: MLam{Domain}
        let mlam_variant =
            syn::Ident::new(&format!("MLam{}", domain_name), proc_macro2::Span::call_site());
        match_arms.push(quote! {
            #category::#mlam_variant(scope) => {
                let (binders, body) = scope.clone().unbind();
                let names: Vec<_> = binders.iter()
                    .map(|b| b.0.pretty_name.as_deref().unwrap_or("?").to_string())
                    .collect();
                write!(f, "^[{}].{{{}}}", names.join(","), body)
            }
        });

        // Application: Apply{Domain} - display as $domain(lam, arg)
        let apply_variant =
            syn::Ident::new(&format!("Apply{}", domain_name), proc_macro2::Span::call_site());
        let domain_lower = domain_name.to_string().to_lowercase();
        match_arms.push(quote! {
            #category::#apply_variant(lam, arg) => {
                write!(f, "${}({}, {})", #domain_lower, lam, arg)
            }
        });

        // Multi-application: MApply{Domain} - display as $$domain(lam, args...)
        let mapply_variant =
            syn::Ident::new(&format!("MApply{}", domain_name), proc_macro2::Span::call_site());
        match_arms.push(quote! {
            #category::#mapply_variant(lam, args) => {
                let arg_strs: Vec<_> = args.iter().map(|a| a.to_string()).collect();
                write!(f, "$${}({}, {})", #domain_lower, lam, arg_strs.join(", "))
            }
        });
    }
    }

    quote! {
        impl std::fmt::Display for #category {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    #(#match_arms),*
                }
            }
        }
    }
}

/// Generate a match arm for displaying a single constructor
fn generate_display_arm(rule: &GrammarRule, language: &LanguageDef) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    // Check if this uses new syntax_pattern - generate display from pattern
    if let (Some(syntax_pattern), Some(term_context)) = (&rule.syntax_pattern, &rule.term_context) {
        return generate_syntax_pattern_display_arm(rule, syntax_pattern, term_context);
    }

    // Check if this has binders (old syntax)
    if !rule.bindings.is_empty() {
        return generate_binder_display_arm(rule, language);
    }

    // Collect field names and their types
    let fields: Vec<(String, Option<&syn::Ident>)> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| match item {
            GrammarItem::NonTerminal(ident) => Some((format!("f{}", i), Some(ident))),
            GrammarItem::Collection { .. } => Some((format!("f{}", i), None)), // Collection field
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        // Unit variant - just print terminals
        let output = format_terminals(rule);
        quote! {
            #category::#label => write!(f, #output)
        }
    } else {
        // Tuple variant - pattern match fields
        let field_names: Vec<syn::Ident> = fields
            .iter()
            .map(|(name, _)| syn::Ident::new(name, proc_macro2::Span::call_site()))
            .collect();

        // Check if any fields are Var - they need special handling
        let has_var = fields.iter().any(|(_, nt_opt)| {
            if let Some(nt) = nt_opt {
                nt.to_string() == "Var"
            } else {
                false
            }
        });

        if has_var {
            // Generate code that extracts names from Vars
            let mut format_parts = Vec::new();
            let mut format_args_tokens = Vec::new();
            let mut part_str = String::new();
            let mut field_iter = fields.iter().zip(field_names.iter());

            for item in &rule.items {
                match item {
                    GrammarItem::Terminal(term) => {
                        let escaped = term.replace("{", "{{").replace("}", "}}");
                        part_str.push_str(&escaped);
                    },
                    GrammarItem::NonTerminal(nt) if nt.to_string() == "Var" => {
                        if !part_str.is_empty() {
                            format_parts.push(part_str.clone());
                            part_str.clear();
                        }
                        if let Some((_, field_name)) = field_iter.next() {
                            format_parts.push("{}".to_string());
                            // Var fields are always OrdVar, need to extract the variable name
                            format_args_tokens.push(quote! {
                                match &(#field_name).0 {
                                    mettail_runtime::Var::Free(fv) => fv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_"),
                                    mettail_runtime::Var::Bound(bv) => bv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_"),
                                }
                            });
                        }
                    },
                    GrammarItem::NonTerminal(_) => {
                        if !part_str.is_empty() {
                            format_parts.push(part_str.clone());
                            part_str.clear();
                        }
                        if let Some((_, field_name)) = field_iter.next() {
                            format_parts.push("{}".to_string());
                            format_args_tokens.push(quote! { #field_name });
                        }
                    },
                    _ => {},
                }
            }

            if !part_str.is_empty() {
                format_parts.push(part_str);
            }

            let format_str = format_parts.join("");

            quote! {
                #category::#label(#(#field_names),*) => write!(f, #format_str, #(#format_args_tokens),*)
            }
        } else {
            // No Var fields - use simple approach
            let (format_str, format_args) = build_format_string(rule, &fields);

            quote! {
                #category::#label(#(#field_names),*) => write!(f, #format_str, #(#format_args),*)
            }
        }
    }
}

/// Generate display for a constructor using new syntax_pattern
fn generate_syntax_pattern_display_arm(
    rule: &GrammarRule,
    syntax_pattern: &[SyntaxExpr],
    term_context: &[TermParam],
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    // Build maps from parameter names to their info
    let mut param_names: Vec<String> = Vec::new();
    let mut collection_params: Vec<(String, String)> = Vec::new(); // (name, separator)
    let mut has_abstraction = false;
    let mut is_multi_binder = false;
    let mut abstraction_binder: Option<String> = None;
    let mut abstraction_body: Option<String> = None;

    for param in term_context {
        match param {
            TermParam::Simple { name, ty } => {
                if matches!(ty, TypeExpr::Collection { .. }) {
                    // Collection params need special handling - separator will be found in syntax pattern
                    param_names.push(name.to_string());
                } else {
                    param_names.push(name.to_string());
                }
            },
            TermParam::Abstraction { binder, body, .. } => {
                has_abstraction = true;
                abstraction_binder = Some(binder.to_string());
                abstraction_body = Some(body.to_string());
            },
            TermParam::MultiAbstraction { binder, body, .. } => {
                has_abstraction = true;
                is_multi_binder = true;
                abstraction_binder = Some(binder.to_string());
                abstraction_body = Some(body.to_string());
            },
        }
    }

    // Scan syntax pattern for #sep operations to find separators
    for expr in syntax_pattern {
        if let SyntaxExpr::Op(PatternOp::Sep { collection, separator, .. }) = expr {
            collection_params.push((collection.to_string(), separator.clone()));
        }
    }

    // Check if we have collection parameters with separators
    let has_collection = !collection_params.is_empty();

    // Use positional field names (f0, f1, ...) so we never shadow the formatter "f"
    let param_index: std::collections::HashMap<String, usize> = param_names
        .iter()
        .enumerate()
        .map(|(i, n)| (n.clone(), i))
        .collect();

    // Build format string and args from syntax pattern
    let mut format_parts: Vec<TokenStream> = Vec::new();

    for (i, expr) in syntax_pattern.iter().enumerate() {
        match expr {
            SyntaxExpr::Literal(s) => {
                let next_param = syntax_pattern
                    .get(i + 1)
                    .map(|e| matches!(e, SyntaxExpr::Param(_)));
                let prev_param =
                    i > 0 && matches!(syntax_pattern.get(i - 1), Some(SyntaxExpr::Param(_)));
                let is_word = s.chars().all(|c| c.is_alphabetic());
                let (prefix, suffix) = if prev_param && next_param.unwrap_or(false) {
                    (" ", " ") // infix op: spaces around (e.g. " && ")
                } else if next_param == Some(true) && is_word {
                    ("", " ") // word then param: trailing space (e.g. "not ")
                } else {
                    ("", "")
                };
                let raw = format!("{}{}{}", prefix, s, suffix);
                let escaped = raw.replace('{', "{{").replace('}', "}}");
                format_parts.push(quote! { write!(f, #escaped)?; });
            },
            SyntaxExpr::Param(id) => {
                let name = id.to_string();

                // Check if this is the binder from an abstraction
                if Some(&name) == abstraction_binder.as_ref() {
                    format_parts.push(quote! { write!(f, "{}", binder_name)?; });
                }
                // Check if this is the body from an abstraction
                else if Some(&name) == abstraction_body.as_ref() {
                    format_parts.push(quote! { write!(f, "{}", body)?; });
                }
                // Simple parameter: use positional ident (f0, f1) to avoid shadowing formatter "f"; use .as_ref() for Box<OtherCat>
                else {
                    let idx = param_index.get(&name).copied().unwrap_or(0);
                    let field_ident = syn::Ident::new(&format!("f{}", idx), proc_macro2::Span::call_site());
                    let param_ty = term_context.iter().find_map(|p| {
                        if let TermParam::Simple { name: n, ty } = p {
                            if n.to_string() == name { Some(ty) } else { None }
                        } else { None }
                    });
                    let use_deref = param_ty.map(|ty| {
                        if let TypeExpr::Base(ref cat) = ty { cat != category } else { false }
                    }).unwrap_or(false);
                    // List/Bag implement Display (ListLit/BagLit produce [] and {}), use {} for round-trip
                    if use_deref {
                        format_parts.push(quote! { write!(f, "{}", #field_ident.as_ref())?; });
                    } else {
                        format_parts.push(quote! { write!(f, "{}", #field_ident)?; });
                    }
                }
            },
            SyntaxExpr::Op(op) => {
                let op_code =
                    generate_pattern_op_display(op, &abstraction_binder, &abstraction_body, &param_index);
                format_parts.push(op_code);
            },
        }
    }

    // Generate field pattern for match arm (f0, f1, ... to avoid shadowing formatter "f")
    let mut field_idents: Vec<syn::Ident> = (0..param_names.len())
        .map(|i| syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site()))
        .collect();

    if has_abstraction {
        field_idents.push(syn::Ident::new("scope", proc_macro2::Span::call_site()));

        if is_multi_binder {
            // Multi-binder: scope.unbind() returns (Vec<Binder>, body)
            // For display with #zip().#map().#sep(), handled by generate_chained_sep_display
            quote! {
                #category::#label(#(#field_idents),*) => {
                    let (binders, body) = scope.clone().unbind();
                    let binder_names: Vec<String> = binders.iter()
                        .map(|b| b.0.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string()))
                        .collect();
                    #(#format_parts)*
                    Ok(())
                }
            }
        } else if has_collection {
            // Both single abstraction and collection
            quote! {
                #category::#label(#(#field_idents),*) => {
                    let (binder, body) = scope.clone().unbind();
                    let binder_name = binder.0.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
                    #(#format_parts)*
                    Ok(())
                }
            }
        } else {
            // Single abstraction without collection
            quote! {
                #category::#label(#(#field_idents),*) => {
                    let (binder, body) = scope.clone().unbind();
                    let binder_name = binder.0.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
                    #(#format_parts)*
                    Ok(())
                }
            }
        }
    } else if field_idents.is_empty() {
        // Nullary constructor - unit variant pattern
        quote! {
            #category::#label => {
                #(#format_parts)*
                Ok(())
            }
        }
    } else if has_collection {
        // Collection without abstraction
        quote! {
            #category::#label(#(#field_idents),*) => {
                #(#format_parts)*
                Ok(())
            }
        }
    } else {
        // Simple tuple variant pattern
        quote! {
            #category::#label(#(#field_idents),*) => {
                #(#format_parts)*
                Ok(())
            }
        }
    }
}

/// Generate display code for a pattern operation
fn generate_pattern_op_display(
    op: &PatternOp,
    _abstraction_binder: &Option<String>,
    _abstraction_body: &Option<String>,
    param_index: &std::collections::HashMap<String, usize>,
) -> TokenStream {
    match op {
        PatternOp::Sep { collection, separator, source } => {
            // Handle chained #zip().#map().#sep() for multi-binder display
            if let Some(chain_source) = source {
                return generate_chained_sep_display_code(chain_source, separator, param_index, &collection.to_string());
            }
            // Use positional ident (f0, f1) so we don't shadow formatter "f" or reference missing param names
            let idx = param_index.get(&collection.to_string()).copied().unwrap_or(0);
            let coll_ident =
                syn::Ident::new(&format!("f{}", idx), proc_macro2::Span::call_site());
            let sep_with_spaces = format!(" {} ", separator);
            quote! {
                {
                    let mut first = true;
                    for (item, count) in #coll_ident.iter() {
                        for _ in 0..count {
                            if !first { write!(f, #sep_with_spaces)?; }
                            first = false;
                            write!(f, "{}", item)?;
                        }
                    }
                }
            }
        },
        PatternOp::Var(id) => {
            // Use positional ident to avoid shadowing formatter "f"
            let idx = param_index.get(&id.to_string()).copied().unwrap_or(0);
            let ident = syn::Ident::new(&format!("f{}", idx), proc_macro2::Span::call_site());
            quote! { write!(f, "{}", #ident)?; }
        },
        PatternOp::Opt { inner } => {
            // For optional, we'd need to know if the value is present
            // This requires more context - for now, just display the inner if non-empty
            let inner_parts: Vec<TokenStream> = inner
                .iter()
                .map(|expr| match expr {
                    SyntaxExpr::Literal(s) => {
                        let escaped = s.replace('{', "{{").replace('}', "}}");
                        quote! { write!(f, #escaped)?; }
                    },
                    SyntaxExpr::Param(id) => {
                        let idx = param_index.get(&id.to_string()).copied().unwrap_or(0);
                        let ident = syn::Ident::new(&format!("f{}", idx), proc_macro2::Span::call_site());
                        quote! { write!(f, "{}", #ident)?; }
                    },
                    SyntaxExpr::Op(op) => generate_pattern_op_display(op, &None, &None, param_index),
                })
                .collect();
            quote! { #(#inner_parts)* }
        },
        PatternOp::Zip { .. } | PatternOp::Map { .. } => {
            // Zip and Map are typically chained with Sep, not standalone
            quote! { /* zip/map should be chained with #sep */ }
        },
    }
}

/// Generate display code for chained #zip().#map().#sep() pattern.
/// Uses positional ident (f0, f1, ...) for the collection so we don't reference param names like `ns`.
fn generate_chained_sep_display_code(
    source: &PatternOp,
    separator: &str,
    param_index: &std::collections::HashMap<String, usize>,
    collection_name: &str,
) -> TokenStream {
    // Extract Map and Zip info from the chain
    if let PatternOp::Map { source: map_source, params, body } = source {
        if let PatternOp::Zip { left, .. } = map_source.as_ref() {
            // We have #zip(left, right).#map(|params...| body).#sep(separator)
            // Use positional ident for the collection (e.g. f0) so we don't use param name "ns"
            let idx = param_index.get(collection_name).or_else(|| param_index.get(&left.to_string())).copied().unwrap_or(0);
            let coll_ident = syn::Ident::new(&format!("f{}", idx), proc_macro2::Span::call_site());

            // Generate format code for each pair based on the body
            let format_code = generate_map_body_format(params, body);

            let sep_str = format!("{} ", separator);

            return quote! {
                {
                    let mut first = true;
                    for (i, item) in #coll_ident.iter().enumerate() {
                        if !first { write!(f, #sep_str)?; }
                        first = false;
                        let binder_name = binder_names.get(i).map(|s| s.as_str()).unwrap_or("_");
                        #format_code
                    }
                }
            };
        }
    }

    // Fallback
    quote! { /* unhandled chained pattern */ }
}

/// Generate format code from map body
fn generate_map_body_format(params: &[syn::Ident], body: &[SyntaxExpr]) -> TokenStream {
    // params typically are [n, x] for #map(|n, x| ...)
    // body contains the format like [Param(x), Literal("<-"), Param(n)]
    // We map:
    //   - first param (n) -> item (from the collection)
    //   - second param (x) -> binder_name (from binder_names)

    let mut format_parts: Vec<TokenStream> = Vec::new();

    for expr in body {
        match expr {
            SyntaxExpr::Literal(s) => {
                format_parts.push(quote! { write!(f, #s)?; });
            },
            SyntaxExpr::Param(id) => {
                let id_str = id.to_string();
                // Check which param this corresponds to
                if params.len() >= 2 {
                    let first_param = params[0].to_string();
                    let second_param = params[1].to_string();

                    if id_str == first_param {
                        // First param maps to the collection item
                        format_parts.push(quote! { write!(f, "{}", item)?; });
                    } else if id_str == second_param {
                        // Second param maps to the binder name
                        format_parts.push(quote! { write!(f, "{}", binder_name)?; });
                    } else {
                        // Unknown param
                        let ident = syn::Ident::new(&id_str, proc_macro2::Span::call_site());
                        format_parts.push(quote! { write!(f, "{}", #ident)?; });
                    }
                } else if params.len() == 1 && id.to_string() == params[0].to_string() {
                    format_parts.push(quote! { write!(f, "{}", item)?; });
                } else {
                    let ident = syn::Ident::new(&id_str, proc_macro2::Span::call_site());
                    format_parts.push(quote! { write!(f, "{}", #ident)?; });
                }
            },
            SyntaxExpr::Op(_) => {
                // Nested ops not expected in map body
            },
        }
    }

    quote! { #(#format_parts)* }
}

/// Generate display for a constructor with binders (old syntax)
fn generate_binder_display_arm(rule: &GrammarRule, _language: &LanguageDef) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Collect regular fields (not binder, not body)
    let mut regular_fields = Vec::new();
    let mut has_scope = false;
    let mut field_idx = 0;

    for (i, item) in rule.items.iter().enumerate() {
        match item {
            GrammarItem::NonTerminal(_) if i == body_idx => {
                has_scope = true;
            },
            GrammarItem::NonTerminal(_) => {
                regular_fields.push(format!("f{}", field_idx));
                field_idx += 1;
            },
            GrammarItem::Binder { .. } if i == *binder_idx => {
                // Skip - it's in the scope
            },
            _ => {},
        }
    }

    // Build pattern: regular fields + scope
    let mut all_fields = regular_fields.clone();
    if has_scope {
        all_fields.push("scope".to_string());
    }

    let field_idents: Vec<syn::Ident> = all_fields
        .iter()
        .map(|name| syn::Ident::new(name, proc_macro2::Span::call_site()))
        .collect();

    // Build format string with placeholders for all parts
    let format_str = build_binder_format_string_simple(rule);

    // Build format args: regular fields, then binder name, then body
    let regular_field_idents: Vec<syn::Ident> = regular_fields
        .iter()
        .map(|name| syn::Ident::new(name, proc_macro2::Span::call_site()))
        .collect();

    quote! {
        #category::#label(#(#field_idents),*) => {
            // Use unbind() to get fresh variables with proper names for display
            let (binder, body) = scope.clone().unbind();
            let binder_name = binder.0.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
            write!(f, #format_str, #(#regular_field_idents,)* binder_name, body)
        }
    }
}

/// Build format string and args for a rule (no Var fields)
fn build_format_string(
    rule: &GrammarRule,
    fields: &[(String, Option<&syn::Ident>)],
) -> (String, Vec<TokenStream>) {
    let mut format_str = String::new();
    let mut format_args = Vec::new();
    let mut field_iter = fields.iter();

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(term) => {
                // Escape braces in format strings
                let escaped = term.replace("{", "{{").replace("}", "}}");
                format_str.push_str(&escaped);
            },
            GrammarItem::NonTerminal(_ty) => {
                // List/Bag implement Display (ListLit/BagLit produce [] and {}), so use {} for round-trip parsing
                if let Some((name, _)) = field_iter.next() {
                    format_str.push_str("{}");
                    let field_ident = syn::Ident::new(name, proc_macro2::Span::call_site());
                    format_args.push(quote! { #field_ident });
                }
            },
            GrammarItem::Collection { separator, delimiters, .. } => {
                // Collection field - format with custom separator
                if let Some((name, _)) = field_iter.next() {
                    format_str.push_str("{}");
                    let field_ident = syn::Ident::new(name, proc_macro2::Span::call_site());

                    // Generate custom formatting for collection with separator
                    let sep = separator.clone();
                    if let Some((open, close)) = delimiters {
                        // With delimiters: {elem1 | elem2 | elem3}
                        format_args.push(quote! {
                            {
                                let mut s = String::from(#open);
                                let items: Vec<String> = #field_ident.iter().map(|(elem, count)| {
                                    // For multisets, repeat element by count
                                    (0..count).map(|_| elem.to_string()).collect::<Vec<_>>().join(&format!(" {} ", #sep))
                                }).collect();
                                if !items.is_empty() {
                                    s.push_str(&items.join(&format!(" {} ", #sep)));
                                }
                                s.push_str(#close);
                                s
                            }
                        });
                    } else {
                        // Without delimiters
                        format_args.push(quote! {
                            {
                                let items: Vec<String> = #field_ident.iter().map(|(elem, count)| {
                                    (0..count).map(|_| elem.to_string()).collect::<Vec<_>>().join(&format!(" {} ", #sep))
                                }).collect();
                                items.join(&format!(" {} ", #sep))
                            }
                        });
                    }
                }
            },
            GrammarItem::Binder { .. } => {
                // Binders are handled separately in binder rules
            },
        }
    }

    (format_str, format_args)
}

/// Build format string for a rule with binders (simplified)
fn build_binder_format_string_simple(rule: &GrammarRule) -> String {
    let mut format_str = String::new();

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    let mut prev_was_nonterminal = false;

    for (i, item) in rule.items.iter().enumerate() {
        match item {
            GrammarItem::Terminal(term) => {
                // Escape braces in format strings
                let escaped = term.replace("{", "{{").replace("}", "}}");
                format_str.push_str(&escaped);
                prev_was_nonterminal = false;
            },
            GrammarItem::NonTerminal(_) if i == body_idx => {
                // Body - will be provided from scope.unbind()
                if prev_was_nonterminal {
                    format_str.push(' ');
                }
                format_str.push_str("{}");
                prev_was_nonterminal = true;
            },
            GrammarItem::NonTerminal(_) => {
                // Regular field
                if prev_was_nonterminal {
                    format_str.push(' ');
                }
                format_str.push_str("{}");
                prev_was_nonterminal = true;
            },
            GrammarItem::Collection { .. } => {
                // Collection field
                if prev_was_nonterminal {
                    format_str.push(' ');
                }
                format_str.push_str("{}");
                prev_was_nonterminal = true;
            },
            GrammarItem::Binder { .. } if i == *binder_idx => {
                // Binder - will be provided from scope.unbind()
                if prev_was_nonterminal {
                    format_str.push(' ');
                }
                format_str.push_str("{}");
                prev_was_nonterminal = true;
            },
            GrammarItem::Binder { .. } => {},
        }
    }

    format_str
}

/// Format just the terminals for a unit variant
fn format_terminals(rule: &GrammarRule) -> String {
    rule.items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::Terminal(term) => Some(term.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("")
}

/// Generate display match arm for an auto-generated Var variant
fn generate_auto_var_display_arm(category: &syn::Ident) -> TokenStream {
    // Generate Var label: first letter + "Var"
    let var_label = generate_var_label(category);

    quote! {
        #category::#var_label(var) => {
            match &var.0 {
                mettail_runtime::Var::Free(fv) => {
                    let name = fv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
                    write!(f, "{}", name)
                }
                mettail_runtime::Var::Bound(bv) => {
                    let name = bv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
                    write!(f, "{}", name)
                }
            }
        }
    }
}

/// Generate display match arm for an auto-generated literal variant (NumLit, etc.)
/// For str/String we output quoted form so pre-substitution produces a re-parseable string literal (e.g. |y| with y="abc" -> |"abc"|).
fn generate_auto_literal_display_arm(
    category: &syn::Ident,
    native_type: &syn::Type,
) -> TokenStream {
    let literal_label = generate_literal_label(native_type);
    let type_str = native_type_to_string(native_type);

    if type_str == "str" || type_str == "String" {
        quote! {
            #category::#literal_label(v) => write!(f, "\"{}\"", v.replace('\"', "\\\""))
        }
    } else {
        // f32/f64 payload is canonical wrapper; it implements Display, so write!(f, "{}", v) is correct
        quote! {
            #category::#literal_label(v) => write!(f, "{}", v)
        }
    }
}
