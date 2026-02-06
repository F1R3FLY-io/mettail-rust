//! Metadata generation for REPL introspection
//!
//! This module generates static metadata about a language's types, terms,
//! equations, and rewrites. The REPL uses this to display the `info` command.

use crate::ast::{
    grammar::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam},
    language::{Equation, FreshnessTarget, LanguageDef, Premise, RewriteRule},
    pattern::{Pattern, PatternTerm},
    types::{CollectionType, TypeExpr},
};
use crate::gen::is_literal_nonterminal;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::LitStr;

/// Generate metadata struct and impl for a language
pub fn generate_metadata(language: &LanguageDef) -> TokenStream {
    let name = &language.name;
    let name_str = name.to_string();
    let name_lit = LitStr::new(&name_str, name.span());
    let metadata_name = format_ident!("{}Metadata", name);

    // Generate type definitions
    let type_defs = generate_type_defs(language);

    // Generate term definitions
    let term_defs = generate_term_defs(language);

    // Generate equation definitions
    let equation_defs = generate_equation_defs(language);

    // Generate rewrite definitions
    let rewrite_defs = generate_rewrite_defs(language);

    // Generate logic relation and rule definitions
    let logic_relation_defs = generate_logic_relation_defs(language);
    let logic_rule_defs = generate_logic_rule_defs(language);

    quote! {
        /// Static metadata for the #name language
        pub struct #metadata_name;

        impl mettail_runtime::LanguageMetadata for #metadata_name {
            fn name(&self) -> &'static str { #name_lit }

            fn types(&self) -> &'static [mettail_runtime::TypeDef] {
                #type_defs
            }

            fn terms(&self) -> &'static [mettail_runtime::TermDef] {
                #term_defs
            }

            fn equations(&self) -> &'static [mettail_runtime::EquationDef] {
                #equation_defs
            }

            fn rewrites(&self) -> &'static [mettail_runtime::RewriteDef] {
                #rewrite_defs
            }
            
            fn logic_relations(&self) -> &'static [mettail_runtime::LogicRelationDef] {
                #logic_relation_defs
            }
            
            fn logic_rules(&self) -> &'static [mettail_runtime::LogicRuleDef] {
                #logic_rule_defs
            }
        }
    }
}

/// Generate TypeDef array from language types
fn generate_type_defs(language: &LanguageDef) -> TokenStream {
    let defs: Vec<TokenStream> = language
        .types
        .iter()
        .enumerate()
        .map(|(i, ty)| {
            let name = ty.name.to_string();
            let name_lit = LitStr::new(&name, ty.name.span());
            let is_primary = i == 0;
            let native_type = match &ty.native_type {
                Some(t) => {
                    let t_str = quote!(#t).to_string();
                    let t_lit = LitStr::new(&t_str, Span::call_site());
                    quote! { Some(#t_lit) }
                },
                None => quote! { None },
            };

            quote! {
                mettail_runtime::TypeDef {
                    name: #name_lit,
                    native_type: #native_type,
                    is_primary: #is_primary,
                }
            }
        })
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

/// Generate TermDef array from language terms
fn generate_term_defs(language: &LanguageDef) -> TokenStream {
    let defs: Vec<TokenStream> = language
        .terms
        .iter()
        .map(|rule| generate_term_def(rule, language))
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

/// Generate a single TermDef
fn generate_term_def(rule: &GrammarRule, language: &LanguageDef) -> TokenStream {
    let name = rule.label.to_string();
    let type_name = rule.category.to_string();

    // Generate user syntax
    let syntax = term_to_user_syntax(rule, language);

    // Use LitStr for static string fields to avoid moving String in generated code
    let name_lit = LitStr::new(&name, rule.label.span());
    let type_name_lit = LitStr::new(&type_name, rule.category.span());
    let syntax_lit = LitStr::new(&syntax, rule.label.span());

    // Generate field definitions
    let fields = generate_field_defs(rule);

    // TODO: Extract description from doc comments
    let description = quote! { None };

    quote! {
        mettail_runtime::TermDef {
            name: #name_lit,
            type_name: #type_name_lit,
            syntax: #syntax_lit,
            description: #description,
            fields: #fields,
        }
    }
}

/// Generate user syntax string for a term
fn term_to_user_syntax(rule: &GrammarRule, _language: &LanguageDef) -> String {
    // If there's a syntax_pattern, use it
    if let Some(syntax_pattern) = &rule.syntax_pattern {
        return syntax_pattern_to_string(syntax_pattern, rule.term_context.as_ref());
    }

    // Otherwise, build from grammar items
    let mut parts = Vec::new();

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(t) => {
                parts.push(t.clone());
            },
            GrammarItem::NonTerminal(nt) => {
                let name = nt.to_string().to_lowercase();
                parts.push(name);
            },
            GrammarItem::Collection { element_type, separator, delimiters, .. } => {
                let elem = element_type.to_string().to_lowercase();
                if let Some((open, close)) = delimiters {
                    parts.push(format!("{} {} ... {}", open, elem, close));
                } else {
                    parts.push(format!("{} {} ...", elem, separator));
                }
            },
            GrammarItem::Binder { category } => {
                // Use lowercase category name as placeholder
                parts.push(category.to_string().to_lowercase());
            },
        }
    }

    parts.join("")
}

/// Convert syntax pattern to user-readable string
fn syntax_pattern_to_string(pattern: &[SyntaxExpr], term_ctx: Option<&Vec<TermParam>>) -> String {
    let mut result = String::new();

    for expr in pattern {
        match expr {
            SyntaxExpr::Literal(s) => result.push_str(s),
            SyntaxExpr::Param(id) => result.push_str(&id.to_string()),
            SyntaxExpr::Op(op) => result.push_str(&pattern_op_to_string(op, term_ctx)),
        }
    }

    result
}

/// Convert pattern operation to string
fn pattern_op_to_string(op: &PatternOp, term_ctx: Option<&Vec<TermParam>>) -> String {
    match op {
        PatternOp::Sep { collection, separator, source } => {
            // Check if there's a chained source (zip.map.sep pattern)
            if let Some(chain_source) = source {
                // Extract the pattern from the chain
                let element_pattern =
                    extract_chained_element_pattern(chain_source.as_ref(), term_ctx);
                format!("{}, ...", element_pattern)
            } else {
                // Simple collection separator
                format!("{} {} ...", collection, separator)
            }
        },
        PatternOp::Var(id) => id.to_string(),
        PatternOp::Opt { inner } => {
            format!("[{}]", syntax_pattern_to_string(inner, term_ctx))
        },
        PatternOp::Zip { left, right, .. } => {
            format!("({}, {})", left, right)
        },
        PatternOp::Map { params, body, .. } => {
            let body_str = syntax_pattern_to_string(body, term_ctx);
            let params_str: Vec<_> = params.iter().map(|p| p.to_string()).collect();
            if params_str.len() > 1 {
                body_str
            } else {
                format!("|{}| {}", params_str.join(", "), body_str)
            }
        },
    }
}

/// Extract the element pattern from a chained zip.map pattern
fn extract_chained_element_pattern(op: &PatternOp, term_ctx: Option<&Vec<TermParam>>) -> String {
    match op {
        PatternOp::Map { body, .. } => {
            // The body contains the pattern for each element
            syntax_pattern_to_string(body, term_ctx)
        },
        _ => "...".to_string(),
    }
}

/// Generate FieldDef array for a term
fn generate_field_defs(rule: &GrammarRule) -> TokenStream {
    // Use term_context if available (new syntax)
    if let Some(ctx) = &rule.term_context {
        let defs: Vec<TokenStream> = ctx
            .iter()
            .map(|param| match param {
                TermParam::Simple { name, ty } => {
                    let name_str = name.to_string();
                    let ty_str = type_expr_to_string(ty);
                    let name_lit = LitStr::new(&name_str, name.span());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: false,
                        }
                    }
                },
                TermParam::Abstraction { binder, body, ty } => {
                    let name_str = format!("^{}.{}", binder, body);
                    let ty_str = type_expr_to_string(ty);
                    let name_lit = LitStr::new(&name_str, binder.span());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: true,
                        }
                    }
                },
                TermParam::MultiAbstraction { binder, body, ty } => {
                    let name_str = format!("^[{}].{}", binder, body);
                    let ty_str = type_expr_to_string(ty);
                    let name_lit = LitStr::new(&name_str, binder.span());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: true,
                        }
                    }
                },
            })
            .collect();

        return quote! { &[#(#defs),*] };
    }

    // Old syntax - build from items
    let defs: Vec<TokenStream> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| {
            match item {
                GrammarItem::NonTerminal(nt)
                    if nt.to_string() != "Var" && !is_literal_nonterminal(&nt.to_string()) =>
                {
                    let name_str = format!("f{}", i);
                    let ty_str = nt.to_string();
                    let name_lit = LitStr::new(&name_str, Span::call_site());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    Some(quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: false,
                        }
                    })
                },
                GrammarItem::Collection { element_type, coll_type, .. } => {
                    let name_str = format!("f{}", i);
                    let ty_str = format!(
                        "{}({})",
                        match coll_type {
                            CollectionType::HashBag => "HashBag",
                            CollectionType::HashSet => "HashSet",
                            CollectionType::Vec => "Vec",
                        },
                        element_type
                    );
                    let name_lit = LitStr::new(&name_str, Span::call_site());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    Some(quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: false,
                        }
                    })
                },
                GrammarItem::Binder { category } => {
                    // Use lowercase category as placeholder name
                    let name_str = category.to_string().to_lowercase();
                    let ty_str = category.to_string();
                    let name_lit = LitStr::new(&name_str, category.span());
                    let ty_lit = LitStr::new(&ty_str, category.span());
                    Some(quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: true,
                        }
                    })
                },
                _ => None,
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

/// Convert TypeExpr to string
fn type_expr_to_string(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Base(id) => id.to_string(),
        TypeExpr::Collection { coll_type, element } => {
            let coll_name = match coll_type {
                CollectionType::HashBag => "HashBag",
                CollectionType::HashSet => "HashSet",
                CollectionType::Vec => "Vec",
            };
            format!("{}({})", coll_name, type_expr_to_string(element))
        },
        TypeExpr::Arrow { domain, codomain } => {
            format!("[{} -> {}]", type_expr_to_string(domain), type_expr_to_string(codomain))
        },
        TypeExpr::MultiBinder(inner) => {
            format!("{}*", type_expr_to_string(inner))
        },
    }
}

/// Generate EquationDef array
fn generate_equation_defs(language: &LanguageDef) -> TokenStream {
    let defs: Vec<TokenStream> = language
        .equations
        .iter()
        .map(|eq| generate_equation_def(eq, language))
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

/// Generate a single EquationDef
fn generate_equation_def(eq: &Equation, language: &LanguageDef) -> TokenStream {
    // Convert conditions to strings
    let conditions: Vec<String> = eq
        .premises
        .iter()
        .map(|c| match c {
            Premise::Freshness(fc) => {
                let target = match &fc.term {
                    FreshnessTarget::Var(v) => v.to_string(),
                    FreshnessTarget::CollectionRest(v) => format!("...{}", v),
                };
                format!("{} # {}", fc.var, target)
            },
            Premise::RelationQuery { relation, args } => {
                let args_str: Vec<_> = args.iter().map(|a| a.to_string()).collect();
                format!("{}({})", relation, args_str.join(", "))
            },
            Premise::Congruence { source, target } => {
                format!("{} ~> {}", source, target)
            },
        })
        .collect();

    let conditions_tokens: Vec<TokenStream> = conditions
        .iter()
        .map(|s| {
            let lit = LitStr::new(s, Span::call_site());
            quote! { #lit }
        })
        .collect();

    // Convert patterns to user syntax (use LitStr for static str fields)
    let lhs = pattern_to_user_syntax(&eq.left, language);
    let rhs = pattern_to_user_syntax(&eq.right, language);
    let lhs_lit = LitStr::new(&lhs, Span::call_site());
    let rhs_lit = LitStr::new(&rhs, Span::call_site());

    quote! {
        mettail_runtime::EquationDef {
            conditions: &[#(#conditions_tokens),*],
            lhs: #lhs_lit,
            rhs: #rhs_lit,
        }
    }
}

/// Generate RewriteDef array
fn generate_rewrite_defs(language: &LanguageDef) -> TokenStream {
    let defs: Vec<TokenStream> = language
        .rewrites
        .iter()
        .enumerate()
        .map(|(i, rw)| generate_rewrite_def(rw, i, language))
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

/// Generate a single RewriteDef
fn generate_rewrite_def(rw: &RewriteRule, _index: usize, language: &LanguageDef) -> TokenStream {
    // For now, no names
    let name = quote! { None };

    // Convert conditions to strings
    let conditions: Vec<String> = rw
        .premises
        .iter()
        .map(|c| match c {
            Premise::Freshness(fc) => format!("{} # {}", fc.var, fc.term),
            Premise::RelationQuery { relation, args } => format!(
                "{}({})",
                relation,
                args.iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Premise::Congruence { source, target } => format!("{} ~> {}", source, target),
        })
        .collect();

    let conditions_tokens: Vec<TokenStream> = conditions
        .iter()
        .map(|s| {
            let lit = LitStr::new(s, Span::call_site());
            quote! { #lit }
        })
        .collect();

    // Convert premise if present (use LitStr for static str)
    let premise = rw
        .premises
        .iter()
        .find_map(|p| {
            if let Premise::Congruence { source, target } = p {
                let source_str = source.to_string();
                let target_str = target.to_string();
                let source_lit = LitStr::new(&source_str, source.span());
                let target_lit = LitStr::new(&target_str, target.span());
                Some(quote! { Some((#source_lit, #target_lit)) })
            } else {
                None
            }
        })
        .unwrap_or(quote! { None });

    // Convert patterns to user syntax (use LitStr for static str fields)
    let lhs = pattern_to_user_syntax(&rw.left, language);
    let rhs = pattern_to_user_syntax(&rw.right, language);
    let lhs_lit = LitStr::new(&lhs, Span::call_site());
    let rhs_lit = LitStr::new(&rhs, Span::call_site());

    quote! {
        mettail_runtime::RewriteDef {
            name: #name,
            conditions: &[#(#conditions_tokens),*],
            premise: #premise,
            lhs: #lhs_lit,
            rhs: #rhs_lit,
        }
    }
}

/// Convert a Pattern to user syntax string
fn pattern_to_user_syntax(pattern: &Pattern, language: &LanguageDef) -> String {
    match pattern {
        Pattern::Term(pt) => pattern_term_to_syntax(pt, language),
        Pattern::Collection { elements, rest, .. } => {
            let mut parts: Vec<String> = elements
                .iter()
                .map(|e| pattern_to_user_syntax(e, language))
                .collect();

            if let Some(r) = rest {
                parts.push(format!("...{}", r));
            }

            format!("{{{}}}", parts.join(" | "))
        },
        Pattern::Map { collection, params, body } => {
            let coll = pattern_to_user_syntax(collection, language);
            let params_str: Vec<_> = params.iter().map(|p| p.to_string()).collect();
            let body_str = pattern_to_user_syntax(body, language);
            format!("{}.*map(|{}| {})", coll, params_str.join(", "), body_str)
        },
        Pattern::Zip { first, second } => {
            let first_str = pattern_to_user_syntax(first, language);
            let second_str = pattern_to_user_syntax(second, language);
            format!("*zip({}, {})", first_str, second_str)
        },
    }
}

/// Convert a PatternTerm to user syntax string
fn pattern_term_to_syntax(pt: &PatternTerm, language: &LanguageDef) -> String {
    match pt {
        PatternTerm::Var(v) => v.to_string(),

        PatternTerm::Apply { constructor, args } => {
            // Try to find the grammar rule for this constructor
            if let Some(rule) = language.terms.iter().find(|r| &r.label == constructor) {
                // Use syntax_pattern if available
                if let Some(syntax_pattern) = &rule.syntax_pattern {
                    return apply_args_to_syntax(syntax_pattern, args, language);
                }

                // Otherwise build from grammar items
                return build_syntax_from_grammar(rule, args, language);
            }

            // Fallback: constructor(args...)
            if args.is_empty() {
                constructor.to_string()
            } else {
                let args_str: Vec<_> = args
                    .iter()
                    .map(|a| pattern_to_user_syntax(a, language))
                    .collect();
                format!(
                    "({}{})",
                    constructor,
                    if args_str.is_empty() {
                        String::new()
                    } else {
                        format!(" {}", args_str.join(" "))
                    }
                )
            }
        },

        PatternTerm::Lambda { binder, body } => {
            let body_str = pattern_to_user_syntax(body, language);
            format!("^{}.{{{}}}", binder, body_str)
        },

        PatternTerm::MultiLambda { binders, body } => {
            let binders_str: Vec<_> = binders.iter().map(|b| b.to_string()).collect();
            let body_str = pattern_to_user_syntax(body, language);
            format!("^[{}].{{{}}}", binders_str.join(", "), body_str)
        },

        PatternTerm::Subst { term, var, replacement } => {
            let term_str = pattern_to_user_syntax(term, language);
            let repl_str = pattern_to_user_syntax(replacement, language);
            format!("{}[{}/{}]", term_str, repl_str, var)
        },

        PatternTerm::MultiSubst { scope, replacements } => {
            let scope_str = pattern_to_user_syntax(scope, language);
            let repls: Vec<_> = replacements
                .iter()
                .map(|r| pattern_to_user_syntax(r, language))
                .collect();
            format!("{}[{}]", scope_str, repls.join(", "))
        },
    }
}

/// Apply arguments to a syntax pattern
fn apply_args_to_syntax(
    syntax_pattern: &[SyntaxExpr],
    args: &[Pattern],
    language: &LanguageDef,
) -> String {
    let mut result = String::new();
    let mut arg_iter = args.iter().peekable();

    // Track if we're currently inside a lambda argument (for binder/body extraction)
    let mut current_lambda: Option<&Pattern> = None;

    for expr in syntax_pattern {
        match expr {
            SyntaxExpr::Literal(s) => result.push_str(s),
            SyntaxExpr::Param(id) => {
                let id_str = id.to_string();

                // Check if this param is from a lambda (binder or body)
                if let Some(Pattern::Term(PatternTerm::Lambda { binder, body })) = current_lambda {
                    if id_str == binder.to_string() {
                        // This is the binder variable
                        result.push_str(&id_str);
                        continue;
                    } else {
                        // This is the body - render it without extra braces
                        result.push_str(&pattern_to_user_syntax(body, language));
                        current_lambda = None;
                        continue;
                    }
                }

                // Get next argument
                if let Some(arg) = arg_iter.next() {
                    // Check if this argument is a Lambda - if so, we need special handling
                    if let Pattern::Term(PatternTerm::Lambda { .. }) = arg {
                        // Store the lambda for subsequent binder/body params
                        current_lambda = Some(arg);
                        // The current param is the binder
                        if let Pattern::Term(PatternTerm::Lambda { binder, .. }) = arg {
                            result.push_str(&binder.to_string());
                        }
                    } else {
                        result.push_str(&pattern_to_user_syntax(arg, language));
                    }
                }
            },
            SyntaxExpr::Op(op) => {
                // For Sep operations referencing a parameter, use the next argument
                if let PatternOp::Sep { separator, source, .. } = op {
                    if let Some(arg) = arg_iter.next() {
                        // Check if there's a chained source (zip.map.sep)
                        if source.is_some() {
                            result.push_str(&pattern_op_to_string(op, None));
                        } else {
                            // Render the collection argument with the separator
                            result.push_str(&render_collection_with_sep(arg, separator, language));
                        }
                    } else {
                        result.push_str(&pattern_op_to_string(op, None));
                    }
                } else {
                    result.push_str(&pattern_op_to_string(op, None));
                }
            },
        }
    }

    result
}

/// Render a collection pattern with a separator
fn render_collection_with_sep(
    pattern: &Pattern,
    separator: &str,
    language: &LanguageDef,
) -> String {
    match pattern {
        Pattern::Collection { elements, rest, .. } => {
            let mut parts: Vec<String> = elements
                .iter()
                .map(|e| pattern_to_user_syntax(e, language))
                .collect();

            if let Some(r) = rest {
                parts.push(format!("...{}", r));
            }

            parts.join(&format!(" {} ", separator))
        },
        _ => pattern_to_user_syntax(pattern, language),
    }
}

/// Build user syntax from grammar items
fn build_syntax_from_grammar(
    rule: &GrammarRule,
    args: &[Pattern],
    language: &LanguageDef,
) -> String {
    let mut result = String::new();
    let mut arg_iter = args.iter();

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(t) => {
                result.push_str(t);
            },
            GrammarItem::NonTerminal(_) => {
                if let Some(arg) = arg_iter.next() {
                    result.push_str(&pattern_to_user_syntax(arg, language));
                }
            },
            GrammarItem::Collection { delimiters, .. } => {
                if let Some(arg) = arg_iter.next() {
                    let inner = pattern_to_user_syntax(arg, language);
                    if let Some((open, close)) = delimiters {
                        result.push_str(&format!("{}{}{}", open, inner, close));
                    } else {
                        result.push_str(&inner);
                    }
                }
            },
            GrammarItem::Binder { category } => {
                // Use lowercase category as placeholder
                result.push_str(&category.to_string().to_lowercase());
            },
        }
    }

    result
}

/// Generate LogicRelationDef array from logic block
fn generate_logic_relation_defs(language: &LanguageDef) -> TokenStream {
    let logic = match &language.logic {
        Some(l) => l,
        None => return quote! { &[] },
    };
    
    if logic.relations.is_empty() {
        return quote! { &[] };
    }
    
    let defs: Vec<TokenStream> = logic.relations
        .iter()
        .map(|rel| {
            let name = rel.name.to_string();
            let param_types: Vec<String> = rel.param_types.iter()
                .map(|t| t.to_string())
                .collect();
            
            quote! {
                mettail_runtime::LogicRelationDef {
                    name: #name,
                    param_types: &[#(#param_types),*],
                    description: None,
                }
            }
        })
        .collect();
    
    quote! {
        &[#(#defs),*]
    }
}

/// Generate LogicRuleDef array from logic block
/// 
/// This extracts rules (non-relation declarations) from the logic content.
fn generate_logic_rule_defs(language: &LanguageDef) -> TokenStream {
    let logic = match &language.logic {
        Some(l) => l,
        None => return quote! { &[] },
    };
    
    // Extract rules from the token stream by splitting on semicolons
    // and filtering out relation declarations
    let content_str = logic.content.to_string();
    let rules: Vec<String> = content_str
        .split(';')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .filter(|s| !s.starts_with("relation "))
        .map(|s| normalize_rule_whitespace(s))
        .collect();
    
    if rules.is_empty() {
        return quote! { &[] };
    }
    
    let defs: Vec<TokenStream> = rules
        .iter()
        .map(|rule| {
            quote! {
                mettail_runtime::LogicRuleDef {
                    rule: #rule,
                }
            }
        })
        .collect();
    
    quote! {
        &[#(#defs),*]
    }
}

/// Normalize whitespace in a rule string for display
fn normalize_rule_whitespace(s: &str) -> String {
    // Replace multiple whitespace with single space
    let normalized: String = s.split_whitespace().collect::<Vec<_>>().join(" ");
    // Clean up spacing around operators
    normalized
        .replace(" . ", ".")
        .replace(". ", ".")
        .replace(" .", ".")
        .replace("< - -", "<--")
        .replace("< --", "<--")
        .replace("< -", "<-")
}
