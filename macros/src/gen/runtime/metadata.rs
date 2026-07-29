//! Metadata generation for REPL introspection
//!
//! This module generates static metadata about a language's types, terms,
//! equations, and rewrites. The REPL uses this to display the `info` command.

use mettail_ast::{
    grammar::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam},
    language::{
        BehavioralPred, Equation, FreshnessTarget, LanguageDef, PredArg, Premise, Quantifier,
        RewriteRule,
    },
    pattern::{Pattern, PatternTerm},
    types::{CollectionType, TypeExpr},
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::LitStr;

fn collection_type_name(coll_type: &CollectionType) -> &'static str {
    match coll_type {
        CollectionType::HashBag => "HashBag",
        CollectionType::HashSet => "HashSet",
        CollectionType::Vec => "Vec",
        CollectionType::HashMap => "HashMap",
        CollectionType::PathMap => "PathMap",
    }
}

/// Generate metadata struct and impl for a language
///
/// `definition_source` is the verbatim `language!` body text (captured in
/// `macros/src/lib.rs` before parsing). It is emitted via
/// `LanguageMetadata::definition_source` so a generated language's exact
/// augmented `LanguageDef` can be reconstructed at runtime
/// (`mettail_ast::auto_inject::reconstruct_language_def`), reproducing the same
/// `definition_fingerprint`.
///
/// `lowering_dispositions` is the language's LOWERING-DISPOSITION INVENTORY
/// (`dovetail_report::lowering_disposition_inventory`) — one entry per declared
/// equation orientation, rewrite, and fold, saying whether the runtime lowering
/// delivered it, delegated it to a named lane, suppressed it by decision, or
/// declined it outright. It is emitted here rather than recomputed at each use
/// so there is exactly ONE derivation of what became of a language's declared
/// semantics, reachable from a running program through
/// `LanguageMetadata::lowering_dispositions`.
pub fn generate_metadata(
    language: &LanguageDef,
    definition_source: &str,
    lowering_dispositions: &[crate::gen::runtime::disposition::LoweringDisposition],
) -> TokenStream {
    let name = &language.name;
    let name_str = name.to_string();
    let name_lit = LitStr::new(&name_str, name.span());
    let fingerprint = mettail_ast::identity::language_definition_fingerprint(language);
    let fingerprint_lit = LitStr::new(&fingerprint, name.span());
    let source_lit = LitStr::new(definition_source, Span::call_site());
    let metadata_name = format_ident!("{}Metadata", name);

    // Generate type definitions
    let type_defs = generate_type_defs(language);

    // Generate term definitions
    let term_defs = generate_term_defs(language);

    // Generate equation definitions
    let equation_defs = generate_equation_defs(language);

    // Generate rewrite definitions
    let rewrite_defs = generate_rewrite_defs(language);

    // Raw generated languages are substrate-neutral: they do not advertise a
    // production runtime backend by default. The generated Ascent runner remains
    // available only through explicit reference-oracle calls. Dovetail/Rho
    // defaults are installed by checked runtime wrappers.
    let runtime_backend_defs = generate_runtime_backend_defs();

    // Generate logic relation and rule definitions
    let logic_relation_defs = generate_logic_relation_defs(language);
    let logic_rule_defs = generate_logic_rule_defs(language);

    // Sim-B: Generate guard configuration metadata arrays from the
    // language's `guards { }` block. When the block is absent, all
    // five generators emit `&[]`, producing the same output as the
    // default-empty trait methods on `LanguageMetadata`.
    let builtin_predicate_defs = generate_builtin_predicate_defs(language);
    let theory_defs = generate_theory_defs(language);
    let channel_defs = generate_channel_defs(language);
    let join_pattern_defs = generate_join_pattern_defs(language);
    let connective_defs = generate_connective_defs(language);

    // Task #94: the lowering-disposition inventory, emitted verbatim from the one
    // derivation every lowering consumer shares.
    let lowering_disposition_defs =
        crate::gen::runtime::disposition::emit_disposition_defs(lowering_dispositions);

    quote! {
        /// Static metadata for the #name language
        pub struct #metadata_name;

        impl mettail_runtime::LanguageMetadata for #metadata_name {
            fn name(&self) -> &'static str { #name_lit }

            fn definition_fingerprint(&self) -> Option<&'static str> {
                Some(#fingerprint_lit)
            }

            fn definition_source(&self) -> Option<&'static str> {
                Some(#source_lit)
            }

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

            fn runtime_backends(&self) -> &'static [mettail_runtime::BackendCapabilityDef] {
                #runtime_backend_defs
            }

            fn logic_relations(&self) -> &'static [mettail_runtime::LogicRelationDef] {
                #logic_relation_defs
            }

            fn logic_rules(&self) -> &'static [mettail_runtime::LogicRuleDef] {
                #logic_rule_defs
            }

            fn builtin_predicates(&self) -> &'static [mettail_runtime::BuiltinPredicateDef] {
                #builtin_predicate_defs
            }

            fn theories(&self) -> &'static [mettail_runtime::TheoryDef] {
                #theory_defs
            }

            fn channels(&self) -> &'static [mettail_runtime::ChannelDef] {
                #channel_defs
            }

            fn join_patterns(&self) -> &'static [mettail_runtime::JoinPatternDef] {
                #join_pattern_defs
            }

            fn connectives(&self) -> &'static [mettail_runtime::ConnectiveDef] {
                #connective_defs
            }

            fn lowering_dispositions(&self)
                -> &'static [mettail_runtime::LoweringDispositionDef]
            {
                #lowering_disposition_defs
            }
        }
    }
}

fn generate_runtime_backend_defs() -> TokenStream {
    quote! {
        mettail_runtime::NO_RUNTIME_BACKEND_CAPABILITIES
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

    // Stage 3.27a (2026-05-04): emit description from doc-comment text
    // captured by `parse_doc_comment` (ast/src/grammar.rs). The text is
    // wrapped via `LitStr::new` which handles all Rust string escaping
    // automatically, so multi-line and special-character doc comments
    // round-trip safely through `quote!` interpolation.
    let description = match &rule.doc_comment {
        Some(text) => {
            let lit = LitStr::new(text, rule.label.span());
            quote! { Some(#lit) }
        },
        None => quote! { None },
    };

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
            GrammarItem::NonTerminal { ident: nt, .. } => {
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
                // Use lowercase category name as a synthetic binder label.
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
            SyntaxExpr::TokenKind { name, bind } => {
                if let Some(b) = bind {
                    result.push_str(&b.to_string());
                    result.push('@');
                }
                result.push_str(&name.to_string());
            },
            SyntaxExpr::GuestBody { open, close, bind } => {
                result.push_str(&format!("*flt({},{},{})", bind, open, close));
            },
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
        fn one_param(param: &TermParam) -> Vec<TokenStream> {
            match param {
                TermParam::Simple { name, ty } => {
                    let name_str = name.to_string();
                    let ty_str = type_expr_to_string(ty);
                    let name_lit = LitStr::new(&name_str, name.span());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    vec![quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: false,
                        }
                    }]
                },
                TermParam::Abstraction { binder, body, ty } => {
                    let name_str = format!("^{}.{}", binder, body);
                    let ty_str = type_expr_to_string(ty);
                    let name_lit = LitStr::new(&name_str, binder.span());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    vec![quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: true,
                        }
                    }]
                },
                TermParam::MultiAbstraction { binder, body, ty } => {
                    let name_str = format!("^[{}].{}", binder, body);
                    let ty_str = type_expr_to_string(ty);
                    let name_lit = LitStr::new(&name_str, binder.span());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    vec![quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: true,
                        }
                    }]
                },
                TermParam::GuardBody { name, .. } => {
                    let name_str = format!("?{}", name);
                    let name_lit = LitStr::new(&name_str, name.span());
                    vec![quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: "Guard",
                            is_binder: false,
                        }
                    }]
                },
                TermParam::Optional { params: inner } => {
                    // Opt-Group: each inner param becomes an Option<>-wrapped
                    // FieldDef whose `ty` field is wrapped as `Option<T>`
                    // and whose `name` is suffixed with `?` so diagnostic
                    // consumers (debug print, equality, hash-cons key
                    // builder) know the field may be absent.
                    fn one_optional(param: &TermParam) -> Vec<TokenStream> {
                        match param {
                            TermParam::Simple { name, ty } => {
                                let name_str = format!("{}?", name);
                                let ty_str = format!("Option<{}>", type_expr_to_string(ty));
                                let name_lit = LitStr::new(&name_str, name.span());
                                let ty_lit = LitStr::new(&ty_str, Span::call_site());
                                vec![quote! {
                                    mettail_runtime::FieldDef {
                                        name: #name_lit,
                                        ty: #ty_lit,
                                        is_binder: false,
                                    }
                                }]
                            },
                            TermParam::Abstraction { binder, body, ty } => {
                                let name_str = format!("^{}.{}?", binder, body);
                                let ty_str = format!("Option<{}>", type_expr_to_string(ty));
                                let name_lit = LitStr::new(&name_str, binder.span());
                                let ty_lit = LitStr::new(&ty_str, Span::call_site());
                                vec![quote! {
                                    mettail_runtime::FieldDef {
                                        name: #name_lit,
                                        ty: #ty_lit,
                                        is_binder: true,
                                    }
                                }]
                            },
                            TermParam::MultiAbstraction { binder, body, ty } => {
                                let name_str = format!("^[{}].{}?", binder, body);
                                let ty_str = format!("Option<{}>", type_expr_to_string(ty));
                                let name_lit = LitStr::new(&name_str, binder.span());
                                let ty_lit = LitStr::new(&ty_str, Span::call_site());
                                vec![quote! {
                                    mettail_runtime::FieldDef {
                                        name: #name_lit,
                                        ty: #ty_lit,
                                        is_binder: true,
                                    }
                                }]
                            },
                            TermParam::GuardBody { name } => {
                                let name_str = format!("?{}?", name);
                                let name_lit = LitStr::new(&name_str, name.span());
                                vec![quote! {
                                    mettail_runtime::FieldDef {
                                        name: #name_lit,
                                        ty: "Option<Guard>",
                                        is_binder: false,
                                    }
                                }]
                            },
                            TermParam::Optional { params: nested } => {
                                // Nested Optional: flatten — Option<Option<T>>
                                // collapses to Option<T> at the outer level
                                // (the WPDS engine never produces Some(Some(...)),
                                // only Some(...) or None).
                                nested.iter().flat_map(one_optional).collect()
                            },
                        }
                    }
                    inner.iter().flat_map(one_optional).collect()
                },
            }
        }
        let defs: Vec<TokenStream> = ctx.iter().flat_map(one_param).collect();
        return quote! { &[#(#defs),*] };
    }

    // Old syntax - build from items
    let defs: Vec<TokenStream> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| {
            match item {
                GrammarItem::NonTerminal { ident: nt, kind } if !kind.is_builtin() => {
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
                    let ty_str = format!("{}({})", collection_type_name(coll_type), element_type);
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
                    // Use lowercase category as a synthetic field name.
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
            let coll_name = collection_type_name(coll_type);
            format!("{}({})", coll_name, type_expr_to_string(element))
        },
        TypeExpr::Map { key, value } => {
            format!("HashMap({}, {})", type_expr_to_string(key), type_expr_to_string(value))
        },
        TypeExpr::Arrow { domain, codomain } => {
            format!("[{} -> {}]", type_expr_to_string(domain), type_expr_to_string(codomain))
        },
        TypeExpr::MultiBinder(inner) => {
            format!("{}*", type_expr_to_string(inner))
        },
        TypeExpr::Refined { base, .. } => type_expr_to_string(base),
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

fn premise_to_display_string(p: &Premise) -> String {
    match p {
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
        Premise::ForAll { collection, param, body } => {
            format!("{}.*map(|{}| {})", collection, param, premise_to_display_string(body))
        },
        Premise::BehavioralGuard(pred) => {
            // Lint-D cleanup: proper unicode-formatted display instead of
            // `{:?}` Debug output. Uses the same display function as the
            // simulator metadata bridge.
            format!("guard({})", behavioral_pred_to_display(pred))
        },
        Premise::SyntheticInjGuard {
            inner_var,
            source_category,
            excluded_variants,
        } => {
            // Phase A (2026-05-16): synthetic-injection guard display.
            let variants: Vec<_> = excluded_variants.iter().map(|v| v.to_string()).collect();
            format!(
                "synthetic_inj_guard({}, {}, [{}])",
                inner_var,
                source_category,
                variants.join(", "),
            )
        },
    }
}

/// Render a `BehavioralPred` as a unicode-formatted user-facing string
/// suitable for inclusion in `EquationDef::conditions` and
/// `RewriteDef::conditions` slices visible via `LanguageMetadata`.
///
/// The rendering uses the same unicode connectives as the design doc
/// §2A surface syntax:
///
/// | Variant | Rendering |
/// |---------|-----------|
/// | `RelationQuery { name, args, negated: false }` | `name(a, b)` |
/// | `RelationQuery { negated: true }` | `¬name(a, b)` |
/// | `And(a, b)` | `a ∧ b` |
/// | `Or(a, b)`  | `a ∨ b` |
/// | `Not(inner)` | `¬inner` |
/// | `Implies(a, b)` | `a ⟹ b` |
/// | `Quantified { ForAll, var, body }` | `∀var. body` (with optional domain/bound) |
/// | `Quantified { Exists, var, body }` | `∃var. body` |
/// | `AcMatch { bag, elements, rest }` | `ac_match(bag, {e1, e2, ...rest})` |
///
/// Parentheses are added conservatively around sub-expressions to avoid
/// ambiguity: any `And`/`Or`/`Implies` operand that is itself a binary
/// combinator of lower-or-equal precedence gets wrapped.
fn behavioral_pred_to_display(pred: &BehavioralPred) -> String {
    match pred {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            let args_str: Vec<String> = args
                .iter()
                .map(|a| match a {
                    PredArg::Var(v) => v.to_string(),
                    PredArg::Constant(c) => c.to_string(),
                })
                .collect();
            let call = format!("{}({})", relation_name, args_str.join(", "));
            if *negated {
                format!("¬{}", call)
            } else {
                call
            }
        },
        BehavioralPred::And(a, b) => {
            format!("{} ∧ {}", wrap_if_binary(a), wrap_if_binary(b),)
        },
        BehavioralPred::Or(a, b) => {
            format!("{} ∨ {}", wrap_if_binary(a), wrap_if_binary(b),)
        },
        BehavioralPred::Not(inner) => {
            format!("¬{}", wrap_if_binary(inner))
        },
        BehavioralPred::Implies(a, b) => {
            format!("{} ⟹ {}", wrap_if_binary(a), wrap_if_binary(b),)
        },
        BehavioralPred::Quantified { quantifier, var, domain, bound, body } => {
            let q = match quantifier {
                Quantifier::ForAll => "∀",
                Quantifier::Exists => "∃",
            };
            let domain_str = match (domain, bound) {
                (Some(d), Some(k)) => format!(" ∈ {}_{{k={}}}", d, k),
                (Some(d), None) => format!(" ∈ {}", d),
                (None, Some(k)) => format!(" _{{k={}}}", k),
                (None, None) => String::new(),
            };
            format!("{}{}{}. {}", q, var, domain_str, behavioral_pred_to_display(body),)
        },
        BehavioralPred::AcMatch { bag, elements, rest } => {
            let mut elems: Vec<String> = elements.iter().map(|e| e.to_string()).collect();
            if let Some(r) = rest {
                elems.push(format!("...{}", r));
            }
            format!("ac_match({}, {{{}}})", bag, elems.join(", "))
        },
        BehavioralPred::Top => "⊤".to_string(),
    }
}

/// Wrap a sub-expression in parentheses when it is a binary combinator
/// (And, Or, Implies). Leaf predicates and Not/Quantified/AcMatch pass
/// through unparenthesized because they are unambiguous at any nesting
/// depth in the rendered output.
fn wrap_if_binary(pred: &BehavioralPred) -> String {
    match pred {
        BehavioralPred::And(_, _) | BehavioralPred::Or(_, _) | BehavioralPred::Implies(_, _) => {
            format!("({})", behavioral_pred_to_display(pred))
        },
        _ => behavioral_pred_to_display(pred),
    }
}

/// Generate a single EquationDef
fn generate_equation_def(eq: &Equation, language: &LanguageDef) -> TokenStream {
    // Convert conditions to strings
    let conditions: Vec<String> = eq.premises.iter().map(premise_to_display_string).collect();

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

    // Sim-B: detect BehavioralGuard premises on equations too.
    let is_guarded = eq
        .premises
        .iter()
        .any(|p| matches!(p, Premise::BehavioralGuard(_)));

    // ★ #97 item 4. Every equation in the grammar is NAMED, and the reflection
    // could not say which equation it was reflecting. It is the only thing that
    // identifies a rule whose two rendered surfaces legitimately coincide.
    let name_lit = LitStr::new(&eq.name.to_string(), eq.name.span());

    quote! {
        mettail_runtime::EquationDef {
            name: #name_lit,
            conditions: &[#(#conditions_tokens),*],
            lhs: #lhs_lit,
            rhs: #rhs_lit,
            is_guarded: #is_guarded,
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
    // Extract the rewrite rule name from the AST
    let name = {
        let name_str = rw.name.to_string();
        let name_lit = LitStr::new(&name_str, rw.name.span());
        quote! { Some(#name_lit) }
    };

    // Convert conditions to strings
    let conditions: Vec<String> = rw.premises.iter().map(premise_to_display_string).collect();

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

    // Detect whether any premise guards rewrite applicability. Behavioral
    // guards are user-authored; SyntheticInjGuard is generated for NormCast
    // rewrites to bound auto-injection cascades.
    let is_guarded = rw
        .premises
        .iter()
        .any(|p| matches!(p, Premise::BehavioralGuard(_) | Premise::SyntheticInjGuard { .. }));

    quote! {
        mettail_runtime::RewriteDef {
            name: #name,
            conditions: &[#(#conditions_tokens),*],
            premise: #premise,
            lhs: #lhs_lit,
            rhs: #rhs_lit,
            is_guarded: #is_guarded,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Task #97 — THE REFLECTION RENDERER'S PRECEDENCE MODEL
// ═══════════════════════════════════════════════════════════════════════════
//
// # The defect
//
// The renderer below turns an equation's or rewrite's `Pattern` back into the
// surface syntax a user would write. Until this repair it spliced each child
// into its parent's syntax pattern with NO context argument — no `min_bp`, no
// parent label — and therefore never emitted a parenthesis. So
//
//     Mul(Mul(X, Y), Z)  ⟼  "X" + "*" + "Y"   then + "*" + "Z"  =  X*Y*Z
//     Mul(X, Mul(Y, Z))  ⟼  "X" + "*" + "Y*Z"                   =  X*Y*Z
//
// and Monoid's associativity axiom — the one law whose entire content IS the
// bracketing — reflected as the tautology `X*Y*Z = X*Y*Z`.
//
// # The model is BORROWED, never re-derived
//
// A precedence-aware renderer already exists in the same build: the generated
// `Display` impl, whose operator arms emit `let needs_parens = <own_left_bp> <
// min_bp;` and push their left and right operands at `left_bp` / `right_bp`.
// Its table is [`BpLookup`], built once by
// `gen::syntax::display::build_bp_lookup` from
// `prattail::binding_power::analyze_binding_powers`. This renderer reads THAT
// table. Two precedence models — one for `Display`, one for the reflected
// theory — could disagree about the very brackets an associativity law is
// about, which is the failure this repair exists to remove, not to duplicate.
//
// # Consequence: the bracketing is MINIMAL, and that is correct
//
// `Mul` is left-associative (`left_bp = 2`, `right_bp = 3`), so the LEFT-nested
// side needs no bracket — `X*Y*Z` already means `(X*Y)*Z` — while the
// RIGHT-nested side does: `2 < 3`, so it renders `X*(Y*Z)`. The axiom therefore
// reflects as `X*Y*Z = X*(Y*Z)`: two different strings, each of which reparses
// to the side it came from. A renderer that bracketed both sides would be a
// SECOND model, disagreeing with `Display` about a string neither needs.

/// Everything the reflection renderer needs that is not the pattern itself.
#[derive(Clone, Copy)]
struct RenderCtx<'a> {
    language: &'a LanguageDef,
    /// The ONE binding-power table, shared with `Display` codegen.
    bp: &'a crate::gen::syntax::display::BpLookup,
}

/// A constructor's precedence: what it takes to bracket IT, and the threshold
/// each of its operands inherits.
///
/// `None` from [`rule_bp`] means the constructor is not Pratt-registered — a
/// delimited, atomic or binder rule. Such a rule brackets its own operands with
/// its own literals, so it never needs parentheses and its children inherit `0`.
/// This mirrors the `else` arm of `display.rs`'s arm generator exactly.
struct RuleBp {
    /// The rule's own left binding power — the operand strength it competes at.
    /// Bracket the rendering when this is BELOW the inherited threshold.
    own_left_bp: u8,
    /// The `min_bp` each argument slot inherits, by slot index.
    child_min_bps: Vec<u8>,
}

/// Read `label`'s precedence out of the shared table, in the same case order
/// `display.rs` uses: postfix, then mixfix, then regular infix, then unary
/// prefix, then "not an operator".
fn rule_bp(label: &str, arg_slots: usize, bp: &crate::gen::syntax::display::BpLookup) -> Option<RuleBp> {
    if let Some(info) = bp.infix.get(label) {
        let child_min_bps: Vec<u8> = if info.is_postfix {
            // Postfix: the single operand carries the operator's left power.
            vec![info.left_bp; arg_slots]
        } else if info.is_mixfix {
            // Mixfix: first operand = left_bp, last = right_bp, interior = 0
            // (an interior slot is fenced by the operator's own literals).
            (0..arg_slots)
                .map(|i| {
                    if i == 0 {
                        info.left_bp
                    } else if i + 1 == arg_slots {
                        info.right_bp
                    } else {
                        0
                    }
                })
                .collect()
        } else {
            // Regular infix: left operand = left_bp, everything after = right_bp.
            (0..arg_slots)
                .map(|i| if i == 0 { info.left_bp } else { info.right_bp })
                .collect()
        };
        return Some(RuleBp { own_left_bp: info.left_bp, child_min_bps });
    }
    if let Some(prefix) = bp.prefix.get(label) {
        return Some(RuleBp {
            own_left_bp: prefix.prefix_bp,
            child_min_bps: vec![prefix.prefix_bp; arg_slots],
        });
    }
    None
}

/// The `min_bp` for argument slot `index`, or `0` when the rule is not
/// precedence-governed.
fn child_min_bp(bp: Option<&RuleBp>, index: usize) -> u8 {
    bp.and_then(|b| b.child_min_bps.get(index).copied()).unwrap_or(0)
}

/// The surface of `name` when it denotes a NULLARY constructor, else `None`.
///
/// ★ #97 item 2. A bare identifier in a pattern is parsed as
/// [`PatternTerm::Var`] whether the author meant a metavariable or a nullary
/// constructor; the rest of the system already decides between the two by
/// LOOKING THE NAME UP (`PatternTerm::is_ground_pattern` calls
/// `LanguageDef::get_constructor` for exactly this reason, and the Dovetail
/// lowering resolves the same node as a constructor leaf). The renderer used to
/// be the one place that did not, so Monoid's `Unit` — declared
/// `Unit . M ::= "e" ;` — reflected as the bare word `Unit`, which is the
/// constructor's LABEL and not anything a user can write.
///
/// "Nullary" is structural: the rule consumes no argument slot, in either
/// grammar form. A constructor that takes arguments is not what a bare
/// identifier denotes, so its label passes through unresolved.
fn nullary_constructor_surface(name: &syn::Ident, ctx: RenderCtx<'_>) -> Option<String> {
    let rule = ctx.language.get_constructor(name)?;
    let takes_arguments = match (&rule.term_context, &rule.syntax_pattern) {
        (Some(term_context), _) => !term_context.is_empty(),
        (None, _) => rule.items.iter().any(|item| {
            matches!(
                item,
                GrammarItem::NonTerminal { .. }
                    | GrammarItem::Collection { .. }
                    | GrammarItem::Binder { .. }
            )
        }),
    };
    if takes_arguments {
        return None;
    }
    Some(match &rule.syntax_pattern {
        Some(syntax_pattern) => apply_args_to_syntax(syntax_pattern, &[], ctx, None),
        None => build_syntax_from_grammar(rule, &[], ctx, None),
    })
}

/// Convert a Pattern to user syntax string, at the top level (nothing outside
/// it, so nothing can require a bracket).
fn pattern_to_user_syntax(pattern: &Pattern, language: &LanguageDef) -> String {
    let bp = match crate::gen::syntax::display::build_bp_lookup(language) {
        Ok(bp) => bp,
        // The bridge refuses only on an `options` value it cannot decode, which
        // makes `Display` codegen refuse for the same language in the same
        // expansion. Rendering without precedence would silently reproduce the
        // tautology this repair removes, so the reflection renders bracket-free
        // ONLY when there are no operators to bracket.
        Err(_) => crate::gen::syntax::display::BpLookup::empty(),
    };
    render_pattern(pattern, RenderCtx { language, bp: &bp }, 0)
}

/// Convert a Pattern to user syntax at an inherited precedence threshold.
fn render_pattern(pattern: &Pattern, ctx: RenderCtx<'_>, min_bp: u8) -> String {
    match pattern {
        Pattern::Term(pt) => render_pattern_term(pt, ctx, min_bp),
        // Every arm below is DELIMITED: its own braces / `*map(…)` / `*zip(…)` /
        // `[… := …]` fence its children, so no child can bind loosely enough to
        // need a bracket and each is rendered at `0`. This is the same rule the
        // generated `Display` collection twin follows.
        Pattern::Collection { elements, rest, .. } => {
            let mut parts: Vec<String> = elements
                .iter()
                .map(|e| render_pattern(e, ctx, 0))
                .collect();

            if let Some(r) = rest {
                parts.push(format!("...{}", r));
            }

            format!("{{{}}}", parts.join(" | "))
        },
        Pattern::Map { collection, params, body } => {
            let coll = render_pattern(collection, ctx, 0);
            let params_str: Vec<_> = params.iter().map(|p| p.to_string()).collect();
            let body_str = render_pattern(body, ctx, 0);
            format!("{}.*map(|{}| {})", coll, params_str.join(", "), body_str)
        },
        Pattern::Zip { first, second } => {
            let first_str = render_pattern(first, ctx, 0);
            let second_str = render_pattern(second, ctx, 0);
            format!("*zip({}, {})", first_str, second_str)
        },
        // Renders back as the surface syntax the user wrote.
        Pattern::IndexedVec { collection, index, element } => {
            format!("{}[{} := {}]", collection, index, render_pattern(element, ctx, 0))
        },
    }
}

/// Convert a PatternTerm to user syntax string, at an inherited precedence
/// threshold.
fn render_pattern_term(pt: &PatternTerm, ctx: RenderCtx<'_>, min_bp: u8) -> String {
    match pt {
        // A bare identifier is a METAVARIABLE unless it names a nullary
        // constructor, in which case it denotes that constructor and renders as
        // its surface — see [`nullary_constructor_surface`]. A nullary
        // constructor's surface is a literal, so no threshold can bracket it.
        PatternTerm::Var(v) => {
            nullary_constructor_surface(v, ctx).unwrap_or_else(|| v.to_string())
        },

        PatternTerm::Apply { constructor, args } => {
            // Try to find the grammar rule for this constructor
            if let Some(rule) = ctx.language.terms.iter().find(|r| &r.label == constructor) {
                let bp = rule_bp(&constructor.to_string(), args.len(), ctx.bp);
                // Use syntax_pattern if available; otherwise build from grammar items.
                let rendered = match &rule.syntax_pattern {
                    Some(syntax_pattern) => {
                        apply_args_to_syntax(syntax_pattern, args, ctx, bp.as_ref())
                    },
                    None => build_syntax_from_grammar(rule, args, ctx, bp.as_ref()),
                };
                // The one bracketing decision, in the same form the generated
                // `Display` arm emits it: `own_left_bp < min_bp`.
                return match &bp {
                    Some(b) if b.own_left_bp < min_bp => format!("({rendered})"),
                    _ => rendered,
                };
            }

            // Fallback: the constructor has no grammar rule, so there is no
            // surface for it and the prefix form is written out. It is already
            // delimited, so it needs no threshold of its own and its arguments
            // inherit none.
            if args.is_empty() {
                constructor.to_string()
            } else {
                let args_str: Vec<_> = args.iter().map(|a| render_pattern(a, ctx, 0)).collect();
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

        // The remaining forms all write their own delimiters — `^x.{…}`,
        // `^[xs].{…}`, `t[r/x]`, `s[…]` — so each child is rendered bare.
        PatternTerm::Lambda { binder, body } => {
            let body_str = render_pattern(body, ctx, 0);
            format!("^{}.{{{}}}", binder, body_str)
        },

        PatternTerm::MultiLambda { binders, body } => {
            let binders_str: Vec<_> = binders.iter().map(|b| b.to_string()).collect();
            let body_str = render_pattern(body, ctx, 0);
            format!("^[{}].{{{}}}", binders_str.join(", "), body_str)
        },

        PatternTerm::Subst { term, var, replacement } => {
            let term_str = render_pattern(term, ctx, 0);
            let repl_str = render_pattern(replacement, ctx, 0);
            format!("{}[{}/{}]", term_str, repl_str, var)
        },

        PatternTerm::MultiSubst { scope, replacements } => {
            let scope_str = render_pattern(scope, ctx, 0);
            let repls: Vec<_> = replacements
                .iter()
                .map(|r| render_pattern(r, ctx, 0))
                .collect();
            format!("{}[{}]", scope_str, repls.join(", "))
        },
    }
}

/// Apply arguments to a syntax pattern.
///
/// `bp` is the enclosing constructor's precedence, or `None` when it is not
/// Pratt-registered. Each argument slot is rendered at the threshold that
/// precedence gives it: for a regular infix rule the FIRST slot inherits
/// `left_bp` and the rest `right_bp`, which is what makes a right-nested
/// left-associative operand bracket itself and a left-nested one not.
fn apply_args_to_syntax(
    syntax_pattern: &[SyntaxExpr],
    args: &[Pattern],
    ctx: RenderCtx<'_>,
    bp: Option<&RuleBp>,
) -> String {
    let mut result = String::new();
    let mut arg_iter = args.iter().peekable();
    // Which argument slot the next consumed argument occupies. Indexes
    // `bp.child_min_bps`, so it counts CONSUMED ARGUMENTS and not syntax
    // elements — a literal is not a slot.
    let mut slot: usize = 0;

    // Track if we're currently inside a lambda argument (for binder/body extraction)
    let mut current_lambda: Option<&Pattern> = None;

    for expr in syntax_pattern {
        match expr {
            SyntaxExpr::Literal(s) => result.push_str(s),
            SyntaxExpr::TokenKind { name, .. } => result.push_str(&name.to_string()),
            SyntaxExpr::GuestBody { open, .. } => result.push_str(&open.to_string()),
            SyntaxExpr::Param(id) => {
                let id_str = id.to_string();

                // Check if this param is from a lambda (binder or body)
                if let Some(Pattern::Term(PatternTerm::Lambda { binder, body })) = current_lambda {
                    if id_str == binder.to_string() {
                        // This is the binder variable
                        result.push_str(&id_str);
                        continue;
                    } else {
                        // This is the body — rendered bare: a binder body sits
                        // inside the rule's own delimiters, exactly as the
                        // generated `Display` pushes it at `min_bp == 0`.
                        result.push_str(&render_pattern(body, ctx, 0));
                        current_lambda = None;
                        continue;
                    }
                }

                // Get next argument
                if let Some(arg) = arg_iter.next() {
                    let inherited = child_min_bp(bp, slot);
                    slot += 1;
                    // Check if this argument is a Lambda - if so, we need special handling
                    if let Pattern::Term(PatternTerm::Lambda { .. }) = arg {
                        // Store the lambda for subsequent binder/body params
                        current_lambda = Some(arg);
                        // The current param is the binder
                        if let Pattern::Term(PatternTerm::Lambda { binder, .. }) = arg {
                            result.push_str(&binder.to_string());
                        }
                    } else {
                        result.push_str(&render_pattern(arg, ctx, inherited));
                    }
                }
            },
            SyntaxExpr::Op(op) => {
                // For Sep operations referencing a parameter, use the next argument
                if let PatternOp::Sep { separator, source, .. } = op {
                    if let Some(arg) = arg_iter.next() {
                        slot += 1;
                        // Check if there's a chained source (zip.map.sep)
                        if source.is_some() {
                            result.push_str(&pattern_op_to_string(op, None));
                        } else {
                            // Render the collection argument with the separator
                            result.push_str(&render_collection_with_sep(arg, separator, ctx));
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

/// Render a collection pattern with a separator.
///
/// Elements are rendered bare: a collection slot is fenced by the rule's own
/// open/close literals, so no element can bind loosely enough to need a bracket.
fn render_collection_with_sep(
    pattern: &Pattern,
    separator: &str,
    ctx: RenderCtx<'_>,
) -> String {
    match pattern {
        Pattern::Collection { elements, rest, .. } => {
            let mut parts: Vec<String> = elements
                .iter()
                .map(|e| render_pattern(e, ctx, 0))
                .collect();

            if let Some(r) = rest {
                parts.push(format!("...{}", r));
            }

            parts.join(&format!(" {} ", separator))
        },
        _ => render_pattern(pattern, ctx, 0),
    }
}

/// Build user syntax from grammar items (the BNFC item form).
///
/// The precedence contract is identical to [`apply_args_to_syntax`]'s: a
/// non-terminal item is an argument slot and inherits its threshold from the
/// enclosing rule's `bp`; a collection item writes its own delimiters, so its
/// contents are bare.
fn build_syntax_from_grammar(
    rule: &GrammarRule,
    args: &[Pattern],
    ctx: RenderCtx<'_>,
    bp: Option<&RuleBp>,
) -> String {
    let mut result = String::new();
    let mut arg_iter = args.iter();
    let mut slot: usize = 0;

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(t) => {
                result.push_str(t);
            },
            GrammarItem::NonTerminal { .. } => {
                if let Some(arg) = arg_iter.next() {
                    let inherited = child_min_bp(bp, slot);
                    slot += 1;
                    result.push_str(&render_pattern(arg, ctx, inherited));
                }
            },
            GrammarItem::Collection { delimiters, .. } => {
                if let Some(arg) = arg_iter.next() {
                    slot += 1;
                    let inner = render_pattern(arg, ctx, 0);
                    if let Some((open, close)) = delimiters {
                        result.push_str(&format!("{}{}{}", open, inner, close));
                    } else {
                        result.push_str(&inner);
                    }
                }
            },
            GrammarItem::Binder { category } => {
                // Use lowercase category as a synthetic binder label.
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

    let defs: Vec<TokenStream> = logic
        .relations
        .iter()
        .map(|rel| {
            let name = rel.name.to_string();
            let param_types = &rel.param_types;

            // Stage 3.27a (2026-05-04): emit description from RelationDecl
            // doc-comment when present. ascent_syntax_export currently does
            // not surface relation-level doc comments, so all paths route
            // through the `None` arm — but the wiring is in place for
            // when that gets extended.
            let description = match &rel.doc_comment {
                Some(text) => {
                    let lit = LitStr::new(text, rel.name.span());
                    quote! { Some(#lit) }
                },
                None => quote! { None },
            };

            quote! {
                mettail_runtime::LogicRelationDef {
                    name: #name,
                    param_types: &[#(#param_types),*],
                    description: #description,
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
        .map(normalize_rule_whitespace)
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

// ═════════════════════════════════════════════════════════════════════════════
// Sim-B: Guard configuration metadata generators
// ═════════════════════════════════════════════════════════════════════════════
//
// Each generator reads from `language.guard_config` and emits an `&[…]`
// literal suitable for the corresponding `LanguageMetadata` trait method.
// When the `guards { }` block is absent (or the relevant sub-block is
// omitted), the generator emits `&[]`.

/// Generate the `BuiltinPredicateDef` array from direct predicate items
/// in `guards { }`.
fn generate_builtin_predicate_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    let Some(preds) = gc.builtin_predicates.as_ref() else {
        return quote! { &[] };
    };

    let defs: Vec<TokenStream> = preds
        .iter()
        .map(|p| {
            let name_str = p.name.to_string();
            let name_lit = LitStr::new(&name_str, p.name.span());

            // Render the first syntax form (if any) using the existing
            // syntax-expression printer. When a predicate declares
            // alternative forms via `|`, we pick the first — this is a
            // best-effort summary, not a round-trippable rendering.
            let syntax_str = p
                .syntax_forms
                .first()
                .map(|form| {
                    form.iter()
                        .map(|expr| syntax_expr_to_display(expr))
                        .collect::<Vec<_>>()
                        .join(" ")
                })
                .unwrap_or_default();
            let syntax_lit = LitStr::new(&syntax_str, Span::call_site());

            let selectivity = match p.annotations.selectivity {
                Some(s) => quote! { Some(#s) },
                None => quote! { None },
            };
            let cost = match p.annotations.cost {
                Some(c) => quote! { Some(#c) },
                None => quote! { None },
            };

            quote! {
                mettail_runtime::BuiltinPredicateDef {
                    name: #name_lit,
                    syntax: #syntax_lit,
                    selectivity: #selectivity,
                    cost: #cost,
                }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

/// Render a syntax expression as a plain string for the
/// `BuiltinPredicateDef.syntax` field.
fn syntax_expr_to_display(expr: &SyntaxExpr) -> String {
    match expr {
        SyntaxExpr::Literal(s) => format!("\"{}\"", s),
        SyntaxExpr::Param(id) => id.to_string(),
        SyntaxExpr::Op(_) => "#op".to_string(),
        SyntaxExpr::TokenKind { name, bind } => match bind {
            Some(b) => format!("{}@{}", b, name),
            None => name.to_string(),
        },
        SyntaxExpr::GuestBody { open, close, bind } => {
            format!("*flt({},{},{})", bind, open, close)
        },
    }
}

/// Generate the `TheoryDef` array from `guards { theories { } }`.
fn generate_theory_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    if gc.theories.is_empty() {
        return quote! { &[] };
    }

    let defs: Vec<TokenStream> = gc
        .theories
        .iter()
        .map(|t| {
            let name_str = t.name.to_string();
            let name_lit = LitStr::new(&name_str, t.name.span());

            let theory_type_str = {
                let ty = &t.theory_type;
                quote!(#ty).to_string()
            };
            let theory_type_lit = LitStr::new(&theory_type_str, Span::call_site());

            let handled_tokens: Vec<TokenStream> = match &t.handled_types {
                Some(cats) => cats
                    .iter()
                    .map(|c| {
                        let c_str = c.to_string();
                        let c_lit = LitStr::new(&c_str, c.span());
                        quote! { #c_lit }
                    })
                    .collect(),
                None => Vec::new(),
            };

            quote! {
                mettail_runtime::TheoryDef {
                    name: #name_lit,
                    theory_type: #theory_type_lit,
                    handled_types: &[#(#handled_tokens),*],
                }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

/// Generate the `ChannelDef` array from `guards { channels { channel … } }`.
fn generate_channel_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    let Some(channels) = gc.channels.as_ref() else {
        return quote! { &[] };
    };

    let defs: Vec<TokenStream> = channels
        .channel_categories
        .iter()
        .map(|c| {
            let cat_str = c.category.to_string();
            let cat_lit = LitStr::new(&cat_str, c.category.span());
            quote! {
                mettail_runtime::ChannelDef { category: #cat_lit }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

/// Generate the `JoinPatternDef` array from `guards { channels { join … } }`.
fn generate_join_pattern_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    let Some(channels) = gc.channels.as_ref() else {
        return quote! { &[] };
    };

    let defs: Vec<TokenStream> = channels
        .join_patterns
        .iter()
        .map(|jp| {
            let label_str = jp.label.to_string();
            let label_lit = LitStr::new(&label_str, jp.label.span());

            let cat_tokens: Vec<TokenStream> = jp
                .channel_params
                .iter()
                .map(|cp| {
                    let cat_str = cp.category.to_string();
                    let cat_lit = LitStr::new(&cat_str, cp.category.span());
                    quote! { #cat_lit }
                })
                .collect();

            quote! {
                mettail_runtime::JoinPatternDef {
                    label: #label_lit,
                    channel_categories: &[#(#cat_tokens),*],
                }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

/// Generate the `ConnectiveDef` array from `guards { connectives { } }`.
fn generate_connective_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    let Some(decls) = gc.connectives.as_ref() else {
        return quote! { &[] };
    };

    let defs: Vec<TokenStream> = decls
        .iter()
        .map(|decl| {
            let role_str = decl.role.as_str();
            let role_lit = LitStr::new(role_str, Span::call_site());

            let kw_tokens: Vec<TokenStream> = decl
                .keywords
                .iter()
                .map(|kw| {
                    let kw_lit = LitStr::new(kw, Span::call_site());
                    quote! { #kw_lit }
                })
                .collect();

            quote! {
                mettail_runtime::ConnectiveDef {
                    role: #role_lit,
                    keywords: &[#(#kw_tokens),*],
                }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::Span;

    #[test]
    fn collection_type_name_distinguishes_hashmap_from_hashbag() {
        assert_eq!(collection_type_name(&CollectionType::HashBag), "HashBag");
        assert_eq!(collection_type_name(&CollectionType::HashMap), "HashMap");
    }

    #[test]
    fn type_expr_to_string_renders_hashmap_collection() {
        let elem = syn::Ident::new("Proc", Span::call_site());
        let ty = TypeExpr::Collection {
            coll_type: CollectionType::HashMap,
            element: Box::new(TypeExpr::Base(elem)),
        };
        assert_eq!(type_expr_to_string(&ty), "HashMap(Proc)");
    }

    #[test]
    fn rewrite_metadata_marks_synthetic_injection_guard_as_guarded() {
        let proc = syn::Ident::new("Proc", Span::call_site());
        let p = syn::Ident::new("P", Span::call_site());
        let rw = RewriteRule {
            name: syn::Ident::new("NormCastProcToProcInProc", Span::call_site()),
            type_context: Vec::new(),
            premises: vec![Premise::SyntheticInjGuard {
                inner_var: p.clone(),
                source_category: proc.clone(),
                excluded_variants: vec![syn::Ident::new("PWrap", Span::call_site())],
            }],
            left: Pattern::Term(PatternTerm::Var(p.clone())),
            right: Pattern::Term(PatternTerm::Var(p)),
            is_auto_injected: true,
        };
        let language = LanguageDef {
            name: syn::Ident::new("TestLang", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        };

        let rendered = generate_rewrite_def(&rw, 0, &language).to_string();
        assert!(
            rendered.contains("is_guarded : true"),
            "synthetic injection guards must be visible in metadata: {}",
            rendered
        );
        assert!(
            rendered.contains("synthetic_inj_guard"),
            "metadata should retain the synthetic guard condition display: {}",
            rendered
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Task #97 RED — the reflected equational theory can express BRACKETING
    // ═══════════════════════════════════════════════════════════════════════
    //
    // Monoid's associativity axiom is `(X*Y)*Z = X*(Y*Z)`. Its entire content is
    // where the brackets go, so a renderer with no precedence model reflects it
    // as `X*Y*Z = X*Y*Z` — a tautology, and the one rule in the corpus for which
    // being uninformative is indistinguishable from being wrong.
    //
    // The cells below assert over the SHIPPED spec (`languages/src/monoid.rs`,
    // read through the derived corpus) rather than a hand-built replica, so a
    // cell cannot pass against a grammar the repository does not contain.

    /// Monoid's three equations, rendered by the reflection renderer, keyed by
    /// the equation's declared name.
    fn monoid_equation_renderings() -> std::collections::HashMap<String, (String, String)> {
        let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid");
        monoid
            .def
            .equations
            .iter()
            .map(|eq| {
                (
                    eq.name.to_string(),
                    (
                        pattern_to_user_syntax(&eq.left, &monoid.def),
                        pattern_to_user_syntax(&eq.right, &monoid.def),
                    ),
                )
            })
            .collect()
    }

    /// ★ THE MUTATION CELL. `Assoc`'s right-nested side brackets its operand, so
    /// the axiom no longer reflects as a tautology.
    ///
    /// ⚠ The assertion is pinned to the SUBSTRING `(Y*Z)`, never to
    /// `assert_ne!(lhs, rhs)` on whole strings: a whole-string `assert_ne!`
    /// passes on any incidental difference and is the vacuity mode that has
    /// already bitten this campaign.
    #[test]
    fn the_associativity_axiom_reflects_its_bracketing() {
        let renderings = monoid_equation_renderings();
        let (lhs, rhs) = renderings
            .get("Assoc")
            .expect("`languages/src/monoid.rs` declares an equation named `Assoc`");

        assert!(
            rhs.contains("(Y*Z)"),
            "the RIGHT-nested side must bracket its operand: `Mul` is left-associative \
             (left_bp 2, right_bp 3), so a `Mul` sitting in a right operand meets a \
             threshold above its own power and parenthesizes. Got rhs = {rhs}",
        );

        // ★ And the LEFT-nested side must NOT bracket. `X*Y*Z` already means
        // `(X*Y)*Z` for a left-associative `*`; bracketing it would be a SECOND
        // precedence model, disagreeing with the generated `Display` about a
        // string that needs no bracket. This half of the cell is what keeps the
        // repair from over-parenthesising its way to a passing `lhs != rhs`.
        assert_eq!(
            lhs, "X*Y*Z",
            "the LEFT-nested side of a left-associative operator needs no bracket. \
             Got lhs = {lhs}",
        );

        assert_ne!(
            lhs, rhs,
            "and therefore the axiom is no longer a tautology: {lhs} = {rhs}",
        );
    }

    /// ANTI-VACUITY for the cell above: the two sides really are DIFFERENT
    /// patterns. If `Assoc` were declared with two identical sides, the cell
    /// above would be asserting something the repair did not cause.
    #[test]
    fn the_associativity_axiom_really_does_nest_its_two_sides_differently() {
        let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid");
        let assoc = monoid
            .def
            .equations
            .iter()
            .find(|eq| eq.name == "Assoc")
            .expect("`languages/src/monoid.rs` declares `Assoc`");

        // LHS is `(Mul (Mul X Y) Z)`: its FIRST argument is an application.
        // RHS is `(Mul X (Mul Y Z))`: its SECOND is.
        fn nested_arg_index(pattern: &Pattern) -> Option<usize> {
            let Pattern::Term(PatternTerm::Apply { args, .. }) = pattern else {
                return None;
            };
            args.iter().position(|a| {
                matches!(a, Pattern::Term(PatternTerm::Apply { .. }))
            })
        }
        assert_eq!(
            nested_arg_index(&assoc.left),
            Some(0),
            "`Assoc`'s left side must be LEFT-nested",
        );
        assert_eq!(
            nested_arg_index(&assoc.right),
            Some(1),
            "`Assoc`'s right side must be RIGHT-nested",
        );
    }

    /// CONTROL for the precedence repair — a flat, single-level term gains NO
    /// parenthesis. An over-parenthesising renderer would reach `lhs != rhs` for
    /// `Assoc` and turn this cell red at the same time, which is exactly what a
    /// control is for.
    #[test]
    fn a_flat_term_gains_no_parenthesis() {
        let renderings = monoid_equation_renderings();
        for name in ["UnitL", "UnitR"] {
            let (lhs, rhs) = renderings
                .get(name)
                .unwrap_or_else(|| panic!("`languages/src/monoid.rs` declares `{name}`"));
            assert!(
                !lhs.contains('(') && !lhs.contains(')'),
                "`{name}`'s left side is a single `Mul` at the top level; nothing encloses \
                 it, so nothing can require a bracket. Got: {lhs}",
            );
            assert_eq!(
                rhs, "X",
                "`{name}`'s right side is the bare metavariable `X`, which neither \
                 precedence nor constructor resolution can touch. Got: {rhs}",
            );
        }
    }

    /// ★ THE SECOND MUTATION CELL (#97 item 2) — a bare identifier that names a
    /// NULLARY CONSTRUCTOR reflects as that constructor's SURFACE, not as its
    /// label.
    ///
    /// Monoid declares `Unit . M ::= "e" ;`, so `(Mul Unit X)` is written `e*X`.
    /// The renderer used to emit the label `Unit`, which is not a string any user
    /// can write, while the rest of the system already resolved the same node by
    /// name (`PatternTerm::is_ground_pattern` → `LanguageDef::get_constructor`).
    #[test]
    fn a_nullary_constructor_reflects_as_its_surface_not_its_label() {
        let renderings = monoid_equation_renderings();
        let (lhs, _) = renderings.get("UnitL").expect("Monoid declares `UnitL`");
        assert_eq!(
            lhs, "e*X",
            "`Unit` is declared `Unit . M ::= \"e\" ;`, so it reflects as `e`. Got: {lhs}",
        );
    }

    /// CONTROL for the constructor-resolution repair — a side whose leaves are
    /// all METAVARIABLES must be untouched by it. `Assoc` names `X`, `Y`, `Z`,
    /// none of which is a constructor, so its left side is byte-identical before
    /// and after.
    #[test]
    fn metavariables_are_not_resolved_against_the_constructor_table() {
        let renderings = monoid_equation_renderings();
        let (lhs, _) = renderings.get("Assoc").expect("Monoid declares `Assoc`");
        assert_eq!(
            lhs, "X*Y*Z",
            "`X`, `Y` and `Z` name no constructor, so constructor resolution must leave \
             them alone. Got: {lhs}",
        );
    }

    /// The reflected equation can now say WHICH equation it is (#97 item 4).
    #[test]
    fn the_reflected_equation_carries_its_name() {
        let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid");
        let assoc = monoid
            .def
            .equations
            .iter()
            .find(|eq| eq.name == "Assoc")
            .expect("Monoid declares `Assoc`");
        let rendered = generate_equation_def(assoc, &monoid.def).to_string();
        assert!(
            rendered.contains("name : \"Assoc\""),
            "an `EquationDef` must carry the equation's declared name, as `RewriteDef` \
             always has. Got: {rendered}",
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // THE CORPUS GATE — no reflected rule is vacuous without a REASON
    // ═══════════════════════════════════════════════════════════════════════

    /// Whether `rule` renders as exactly its single argument and nothing else.
    ///
    /// Such a constructor is DISPLAY-TRANSPARENT: `CastInt(x)` and `x` are written
    /// identically, by design — the injection exists to retype a value, not to
    /// add notation. The generated `Display` is transparent for the same node.
    fn is_display_transparent(rule: &GrammarRule) -> bool {
        match &rule.syntax_pattern {
            Some(syntax_pattern) => {
                syntax_pattern.len() == 1 && matches!(syntax_pattern[0], SyntaxExpr::Param(_))
            },
            None => {
                rule.items.len() == 1
                    && matches!(rule.items[0], GrammarItem::NonTerminal { .. })
            },
        }
    }

    /// Strip every display-transparent wrapper from a pattern.
    fn erase_transparent<'a>(pattern: &'a Pattern, language: &LanguageDef) -> &'a Pattern {
        let mut current = pattern;
        loop {
            let Pattern::Term(PatternTerm::Apply { constructor, args }) = current else {
                return current;
            };
            if args.len() != 1 {
                return current;
            }
            let Some(rule) = language.get_constructor(constructor) else {
                return current;
            };
            if !is_display_transparent(rule) {
                return current;
            }
            current = &args[0];
        }
    }

    /// Structural equality of two patterns AFTER erasing display-transparent
    /// wrappers.
    ///
    /// This is the exemption predicate for the gate below: when it holds, the two
    /// sides really do have the same SURFACE, and rendering them identically is
    /// faithful rather than lossy.
    fn equal_modulo_transparent(a: &Pattern, b: &Pattern, language: &LanguageDef) -> bool {
        let (a, b) = (erase_transparent(a, language), erase_transparent(b, language));
        match (a, b) {
            (Pattern::Term(x), Pattern::Term(y)) => match (x, y) {
                (PatternTerm::Var(u), PatternTerm::Var(v)) => u == v,
                (
                    PatternTerm::Apply { constructor: cx, args: ax },
                    PatternTerm::Apply { constructor: cy, args: ay },
                ) => {
                    cx == cy
                        && ax.len() == ay.len()
                        && ax
                            .iter()
                            .zip(ay.iter())
                            .all(|(p, q)| equal_modulo_transparent(p, q, language))
                },
                _ => false,
            },
            _ => false,
        }
    }

    /// ★ THE ANTI-VACUITY GATE over the whole corpus: no reflected equation or
    /// rewrite renders its two sides identically UNLESS the two sides genuinely
    /// have the same surface.
    ///
    /// # The declared exemption, and why it is a reason rather than a skip
    ///
    /// Thirteen auto-injected `NormCast<S>To<T>In<R>` rewrites render
    /// `lhs: "v", rhs: "v"`. Their shape is
    /// `(Cast<S> v) ~> (Cast<T> (<S>To<T> v))`, and every constructor in it is
    /// DISPLAY-TRANSPARENT: an injection adds no notation, so the surface really
    /// is `v` on both sides. Rendering a constructor there would invent a
    /// notation nobody can write and would contradict the generated `Display`,
    /// which is transparent for the same node. What such a rule is identified by
    /// is its NAME — `RewriteDef::name` has always carried one, and `EquationDef`
    /// now does too — so the reflection does say which retagging it is.
    ///
    /// The exemption is therefore not a list of thirteen labels but the
    /// structural property [`equal_modulo_transparent`]: two sides may render
    /// identically exactly when they ARE identical once transparent wrappers are
    /// erased. Monoid's `Assoc` does not satisfy it — its two sides differ in
    /// nesting, not in wrappers — so this gate was RED on `Assoc` before the
    /// precedence repair and is green after it.
    #[test]
    fn no_reflected_rule_is_vacuous_without_a_structural_reason() {
        let mut rules_checked = 0usize;
        let mut exempt = 0usize;
        let mut vacuous: Vec<String> = Vec::new();

        for language in crate::gen::capture::bundled_corpus::bundled_languages() {
            let def = &language.def;
            let sides: Vec<(String, &Pattern, &Pattern)> = def
                .equations
                .iter()
                .map(|eq| (format!("equation `{}`", eq.name), &eq.left, &eq.right))
                .chain(
                    def.rewrites
                        .iter()
                        .map(|rw| (format!("rewrite `{}`", rw.name), &rw.left, &rw.right)),
                )
                .collect();

            for (what, left, right) in sides {
                rules_checked += 1;
                let lhs = pattern_to_user_syntax(left, def);
                let rhs = pattern_to_user_syntax(right, def);
                if lhs != rhs {
                    continue;
                }
                if equal_modulo_transparent(left, right, def) {
                    exempt += 1;
                    continue;
                }
                vacuous.push(format!(
                    "{}: {what} reflects as `{lhs}` = `{rhs}` — identical surfaces that are \
                     NOT the same pattern once display-transparent wrappers are erased, so \
                     the reflection has lost the rule's content",
                    language.tag,
                ));
            }
        }

        // Non-vacuity floor: "for every reflected rule, P" is satisfied by no
        // rules at all.
        assert!(
            rules_checked >= 300,
            "only {rules_checked} reflected rule(s) reached the gate; the corpus reflects \
             several hundred across its equations and rewrites, so the subject has \
             collapsed and this assertion would be reporting success over almost nothing",
        );
        // And the exemption is REACHED: if it were not, the structural predicate
        // would be untested and could silently stop matching the class it exists
        // to describe.
        assert!(
            exempt > 0,
            "the display-transparent exemption matched NOTHING. The auto-injected \
             `NormCast*` family is supposed to reach it, so either the family stopped \
             being generated or `equal_modulo_transparent` stopped recognising it — in \
             which case the exemption is an untested branch",
        );
        assert!(
            vacuous.is_empty(),
            "{} of {rules_checked} reflected rule(s) are vacuous with no structural \
             reason:\n\n{}",
            vacuous.len(),
            vacuous.join("\n"),
        );
    }

}
