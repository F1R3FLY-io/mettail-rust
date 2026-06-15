//! Dovetail report helper generation.
//!
//! This concern emits AST-first lowering from macro-expanded `LanguageDef`
//! data into the runtime Dovetail API. It never reconstructs a language from
//! rendered syntax strings: constructor labels, categories, rules, and
//! patterns come directly from the parsed language definition.

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::{Equation, LanguageDef, Premise, RewriteRule};
use mettail_ast::pattern::{Pattern as AstPattern, PatternTerm};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Ident, LitStr};

use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};

fn to_snake(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    for (i, ch) in s.chars().enumerate() {
        if ch.is_ascii_uppercase() {
            if i > 0 {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

fn lit(value: &str) -> LitStr {
    LitStr::new(value, Span::call_site())
}

fn constructor_label(language: &LanguageDef, constructor: &Ident) -> Result<String, String> {
    let category = language
        .category_of_constructor(constructor)
        .ok_or_else(|| format!("constructor `{constructor}` has no category"))?;
    Ok(format!("{}::{}::{}", language.name, category, constructor))
}

fn category_lowering_fn(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_add_{}", to_snake(&category.to_string()))
}

fn opaque_leaf_expr(label: TokenStream, payload: TokenStream) -> TokenStream {
    quote! {
        eg.add(::dovetail::egraph::ENode::leaf(format!("{}::{:?}", #label, #payload)))
    }
}

fn field_child_expr(
    owner_label: &str,
    field_index: usize,
    field: &FieldInfo,
    field_var: &Ident,
) -> TokenStream {
    let none_label = lit(&format!("{owner_label}::field{field_index}::None"));
    let opaque_label = lit(&format!("{owner_label}::field{field_index}::opaque"));
    let collection_label = lit(&format!("{owner_label}::field{field_index}::collection"));
    let child_fn = category_lowering_fn(&field.category);
    let field_kind = NonTerminalKind::classify(&field.category.to_string());
    if field_kind.is_builtin() {
        let leaf = opaque_leaf_expr(quote! { #opaque_label }, quote! { #field_var });
        return quote! { #leaf };
    }

    if field.is_optional {
        if field.is_predicate {
            let leaf = opaque_leaf_expr(quote! { #opaque_label }, quote! { __pred });
            return quote! {
                match #field_var.as_ref() {
                    Some(__pred) => #leaf,
                    None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
                }
            };
        }
        if field.is_collection {
            let leaf = opaque_leaf_expr(quote! { #collection_label }, quote! { __values });
            return quote! {
                match #field_var.as_ref() {
                    Some(__values) => #leaf,
                    None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
                }
            };
        }
        return quote! {
            match #field_var.as_ref() {
                Some(__inner) => #child_fn(eg, __inner.as_ref()),
                None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
            }
        };
    }

    if field.is_predicate {
        let leaf = opaque_leaf_expr(quote! { #opaque_label }, quote! { #field_var });
        return quote! { #leaf };
    }

    if field.is_collection {
        let leaf = opaque_leaf_expr(quote! { #collection_label }, quote! { #field_var });
        return quote! { #leaf };
    }

    quote! { #child_fn(eg, #field_var.as_ref()) }
}

fn regular_arm(
    language: &LanguageDef,
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
) -> TokenStream {
    let owner = format!("{}::{}::{}", language.name, category, label);
    let owner_lit = lit(&owner);
    let field_vars: Vec<Ident> = (0..fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let child_exprs: Vec<TokenStream> = fields
        .iter()
        .zip(field_vars.iter())
        .enumerate()
        .map(|(i, (field, var))| field_child_expr(&owner, i, field, var))
        .collect();
    quote! {
        #category::#label(#(#field_vars),*) => {
            let __children = vec![#(#child_exprs),*];
            eg.add(::dovetail::egraph::ENode::new(#owner_lit.to_string(), __children))
        }
    }
}

fn binder_arm(
    language: &LanguageDef,
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    multi: bool,
) -> TokenStream {
    let owner = format!("{}::{}::{}", language.name, category, label);
    let owner_lit = lit(&owner);
    let binder_label = lit(&format!("{owner}::binder"));
    let pre_vars: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let scope_var = format_ident!("scope");
    let pre_child_exprs: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(pre_vars.iter())
        .enumerate()
        .map(|(i, (field, var))| field_child_expr(&owner, i, field, var))
        .collect();
    let body_fn = category_lowering_fn(category);
    let binder_child = if multi {
        quote! {{
            let mut __binders = Vec::new();
            for __binder in #scope_var.unsafe_pattern().iter() {
                __binders.push(eg.add(::dovetail::egraph::ENode::leaf(format!(
                    "{}::{:?}",
                    #binder_label,
                    __binder
                ))));
            }
            eg.add(::dovetail::egraph::ENode::new(#binder_label.to_string(), __binders))
        }}
    } else {
        quote! {
            eg.add(::dovetail::egraph::ENode::leaf(format!(
                "{}::{:?}",
                #binder_label,
                #scope_var.unsafe_pattern()
            )))
        }
    };

    quote! {
        #category::#label(#(#pre_vars,)* #scope_var) => {
            let __binder = #binder_child;
            let __body = #body_fn(eg, #scope_var.unsafe_body().as_ref());
            let __children = vec![#(#pre_child_exprs,)* __binder, __body];
            eg.add(::dovetail::egraph::ENode::new(#owner_lit.to_string(), __children))
        }
    }
}

fn category_lowering(language: &LanguageDef, category: &Ident) -> TokenStream {
    let fn_name = category_lowering_fn(category);
    let arms: Vec<TokenStream> = collect_category_variants(category, language)
        .into_iter()
        .map(|variant| match variant {
            VariantKind::Var { label } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label(value) => {
                        eg.add(::dovetail::egraph::ENode::leaf(format!("{}::{:?}", #owner, value)))
                    }
                }
            },
            VariantKind::Literal { label } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label(value) => {
                        eg.add(::dovetail::egraph::ENode::leaf(format!("{}::{:?}", #owner, value)))
                    }
                }
            },
            VariantKind::Nullary { label } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label => {
                        eg.add(::dovetail::egraph::ENode::leaf(#owner.to_string()))
                    }
                }
            },
            VariantKind::Regular { label, fields } => {
                regular_arm(language, category, &label, &fields)
            },
            VariantKind::Collection { label, .. } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label(values) => {
                        eg.add(::dovetail::egraph::ENode::leaf(format!(
                            "{}::{:?}",
                            #owner,
                            values,
                        )))
                    }
                }
            },
            VariantKind::Binder { label, pre_scope_fields, .. } => {
                binder_arm(language, category, &label, &pre_scope_fields, false)
            },
            VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
                binder_arm(language, category, &label, &pre_scope_fields, true)
            },
        })
        .collect();

    quote! {
        fn #fn_name(
            eg: &mut ::dovetail::egraph::EGraph<String>,
            term: &#category,
        ) -> ::dovetail::egraph::EClassId {
            match term {
                #(#arms),*
            }
        }
    }
}

fn pattern_to_dovetail(
    language: &LanguageDef,
    pattern: &AstPattern,
) -> Result<TokenStream, String> {
    match pattern {
        AstPattern::Term(term) => pattern_term_to_dovetail(language, term),
        AstPattern::Collection { .. } => {
            Err("collection metapatterns require AC/collection lowering".into())
        },
        AstPattern::Map { .. } => {
            Err("map metapatterns require collection-comprehension lowering".into())
        },
        AstPattern::Zip { .. } => {
            Err("zip metapatterns require collection-comprehension lowering".into())
        },
    }
}

fn pattern_term_to_dovetail(
    language: &LanguageDef,
    term: &PatternTerm,
) -> Result<TokenStream, String> {
    match term {
        PatternTerm::Var(var) => {
            if let Some(rule) = language.get_constructor(var) {
                let label = constructor_label(language, &rule.label)?;
                let label = lit(&label);
                Ok(quote! { ::dovetail::rules::Pattern::leaf(#label.to_string()) })
            } else {
                let name = lit(&var.to_string());
                Ok(quote! { ::dovetail::rules::Pattern::var(#name) })
            }
        },
        PatternTerm::Apply { constructor, args } => {
            let label = constructor_label(language, constructor)?;
            let label = lit(&label);
            let args = args
                .iter()
                .map(|arg| pattern_to_dovetail(language, arg))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(quote! {
                ::dovetail::rules::Pattern::app(#label.to_string(), vec![#(#args),*])
            })
        },
        PatternTerm::Lambda { .. } => Err("lambda patterns require binder lowering".into()),
        PatternTerm::MultiLambda { .. } => {
            Err("multi-lambda patterns require binder lowering".into())
        },
        PatternTerm::Subst { .. } => {
            Err("substitution patterns require generated substitution lowering".into())
        },
        PatternTerm::MultiSubst { .. } => {
            Err("multi-substitution patterns require generated substitution lowering".into())
        },
    }
}

fn premise_supported(premise: &Premise) -> bool {
    match premise {
        Premise::Congruence { .. } => true,
        _ => false,
    }
}

fn lower_equation(language: &LanguageDef, eq: &Equation) -> (Vec<TokenStream>, Vec<String>) {
    let mut out = Vec::new();
    let mut unsupported = Vec::new();
    if !eq.premises.iter().all(premise_supported) {
        unsupported.push(format!("equation `{}` has side conditions", eq.name));
        return (out, unsupported);
    }

    match pattern_to_dovetail(language, &eq.left) {
        Ok(left) if !eq.left.is_just_variable() => match pattern_to_dovetail(language, &eq.right) {
            Ok(right) => {
                let label = lit(&format!("{}::equation::{}::forward", language.name, eq.name));
                out.push(quote! {
                    ::dovetail::rules::RewriteRule {
                        lhs: #left,
                        rhs: #right,
                        label: Some(#label.to_string()),
                    }
                });
            },
            Err(reason) => unsupported.push(format!("equation `{}` RHS: {reason}", eq.name)),
        },
        Ok(_) => {},
        Err(reason) => unsupported.push(format!("equation `{}` LHS: {reason}", eq.name)),
    }

    match pattern_to_dovetail(language, &eq.right) {
        Ok(right) if !eq.right.is_just_variable() => {
            match pattern_to_dovetail(language, &eq.left) {
                Ok(left) => {
                    let label = lit(&format!("{}::equation::{}::reverse", language.name, eq.name));
                    out.push(quote! {
                        ::dovetail::rules::RewriteRule {
                            lhs: #right,
                            rhs: #left,
                            label: Some(#label.to_string()),
                        }
                    });
                },
                Err(reason) => {
                    unsupported.push(format!("equation `{}` reverse RHS: {reason}", eq.name))
                },
            }
        },
        Ok(_) => {},
        Err(reason) => unsupported.push(format!("equation `{}` reverse LHS: {reason}", eq.name)),
    }

    (out, unsupported)
}

fn lower_rewrite(language: &LanguageDef, rw: &RewriteRule) -> (Vec<TokenStream>, Vec<String>) {
    if !rw.premises.iter().all(premise_supported) {
        return (Vec::new(), vec![format!("rewrite `{}` has side conditions", rw.name)]);
    }
    if rw.is_congruence_rule() {
        // The e-graph congruence closure supplies context closure after the
        // premise-free kernel rewrite has merged the child e-class, so explicit
        // generated congruence rules are not emitted as separate Dovetail data.
        return (Vec::new(), Vec::new());
    }

    match (
        pattern_to_dovetail(language, &rw.left),
        pattern_to_dovetail(language, &rw.right),
    ) {
        (Ok(lhs), Ok(rhs)) => {
            let label = lit(&format!("{}::rewrite::{}", language.name, rw.name));
            (
                vec![quote! {
                    ::dovetail::rules::RewriteRule {
                        lhs: #lhs,
                        rhs: #rhs,
                        label: Some(#label.to_string()),
                    }
                }],
                Vec::new(),
            )
        },
        (Err(reason), _) => (Vec::new(), vec![format!("rewrite `{}` LHS: {reason}", rw.name)]),
        (_, Err(reason)) => (Vec::new(), vec![format!("rewrite `{}` RHS: {reason}", rw.name)]),
    }
}

fn rule_block(language: &LanguageDef) -> (TokenStream, Vec<String>) {
    let mut rules = Vec::new();
    let mut unsupported = Vec::new();
    for eq in &language.equations {
        let (lowered, rejected) = lower_equation(language, eq);
        rules.extend(lowered);
        unsupported.extend(rejected);
    }
    for rw in &language.rewrites {
        let (lowered, rejected) = lower_rewrite(language, rw);
        rules.extend(lowered);
        unsupported.extend(rejected);
    }

    (quote! { vec![#(#rules),*] }, unsupported)
}

/// Generate feature-gated helpers that compile generated typed AST terms into
/// checked `RuntimeDovetailRunReport` values.
pub fn generate_dovetail_report(language: &LanguageDef) -> TokenStream {
    let name = &language.name;
    let language_struct = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let language_lit = lit(&name.to_string());
    let category_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| category_lowering(language, &ty.name))
        .collect();
    let (rules, unsupported) = rule_block(language);
    let unsupported_lits: Vec<LitStr> = unsupported.iter().map(|s| lit(s)).collect();
    let primary_type = language
        .types
        .first()
        .map(|ty| ty.name.clone())
        .expect("language has at least one type");
    let primary_add = category_lowering_fn(&primary_type);

    let root_block = if language.types.len() > 1 {
        let inner_enum = format_ident!("{}TermInner", name);
        let mut arms = Vec::new();
        for ty in &language.types {
            let cat = &ty.name;
            let add_fn = category_lowering_fn(cat);
            arms.push(quote! {
                #inner_enum::#cat(value) => {
                    __roots.push(#add_fn(&mut eg, value));
                }
            });
        }
        quote! {
            for __alt in typed_term.0.all_alts() {
                match __alt {
                    #(#arms)*
                    #inner_enum::Ambiguous(_) => unreachable!(
                        "all_alts() returns flat alternatives, not nested Ambiguous"
                    ),
                }
            }
        }
    } else {
        quote! {
            __roots.push(#primary_add(&mut eg, &typed_term.0));
        }
    };

    quote! {
        #[cfg(feature = "dovetail-codegen")]
        impl #language_struct {
            /// Compile this language's generated typed AST into a checked
            /// runtime Dovetail report.
            ///
            /// The compiler is derived from the same macro-expanded
            /// `LanguageDef` as the AST constructors. Rholang-looking or
            /// source-language text is not parsed or reverse-engineered here.
            ///
            /// Formal models:
            /// - `dovetail/formal/rocq/theories/Lowering/GeneratedReportCompiler.v`
            /// - `dovetail/formal/rocq/theories/Refinement/RustModelBridge.v`
            /// - `dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v`
            pub fn dovetail_report_for(
                term: &dyn mettail_runtime::Term,
                max_iters: usize,
                max_nodes: usize,
            ) -> Result<mettail_runtime::RuntimeDovetailRunReport, String> {
                if let Ok(report) =
                    ::mettail_dovetail_runtime::complete_native_dovetail_report_for_language(
                        &#language_struct,
                        term,
                    )
                {
                    return Ok(report);
                }

                let unsupported: &[&str] = &[#(#unsupported_lits),*];
                if !unsupported.is_empty() {
                    return Err(format!(
                        "generated Dovetail compiler for language {} needs specialized lowering before structural saturation can be complete: {}",
                        #language_lit,
                        unsupported.join("; "),
                    ));
                }

                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("expected {}Term, got {:?}", #language_lit, term))?;

                let mut eg = ::dovetail::egraph::EGraph::<String>::with_config(
                    ::dovetail::egraph::EGraphConfig { max_nodes },
                );
                #(#category_fns)*

                let mut __roots = Vec::new();
                #root_block
                __roots.sort_unstable();
                __roots.dedup();
                if __roots.is_empty() {
                    return Err(format!(
                        "generated Dovetail compiler for language {} produced no roots",
                        #language_lit,
                    ));
                }

                let rules = #rules;
                let sat = eg.saturate(&rules, max_iters);
                if sat.outcome != ::dovetail::rules::SaturationOutcome::Converged {
                    return Err(format!(
                        "generated Dovetail saturation for language {} stopped before convergence: {:?}",
                        #language_lit,
                        sat.outcome,
                    ));
                }

                let mut extractor =
                    ::dovetail::extract::Extractor::new(&eg, |_| ::rigail::TropicalWeight(0.0));
                let mut __derivations = Vec::new();
                let mut __completeness = ::dovetail::extract::ExtractionCompleteness::Complete;
                for __root in __roots {
                    let __extracted = extractor.derivations(eg.find(__root)).collect_checked();
                    if __extracted.completeness
                        == ::dovetail::extract::ExtractionCompleteness::BoundedByCycleCut
                    {
                        __completeness =
                            ::dovetail::extract::ExtractionCompleteness::BoundedByCycleCut;
                    }
                    __derivations.extend(__extracted.value);
                }

                let report = ::dovetail::report::report_from_extraction(
                    ::dovetail::extract::Extraction {
                        value: __derivations,
                        completeness: __completeness,
                    },
                );
                let runtime_report = ::mettail_dovetail_runtime::project_dovetail_report(&report);
                runtime_report
                    .validate_shape()
                    .map_err(|err| format!("generated Dovetail report for language {} is malformed: {err}", #language_lit))?;
                Ok(runtime_report)
            }

            /// Installable Dovetail compiler stage for this generated language.
            pub fn dovetail_compiler_stage(
            ) -> ::mettail_dovetail_runtime::DovetailCompilerStage<
                fn(&dyn mettail_runtime::Term) -> Result<mettail_runtime::RuntimeDovetailRunReport, String>,
            > {
                fn __runner(
                    term: &dyn mettail_runtime::Term,
                ) -> Result<mettail_runtime::RuntimeDovetailRunReport, String> {
                    #language_struct::dovetail_report_for(term, 64, 1_000_000)
                }

                ::mettail_dovetail_runtime::DovetailCompilerStage::new(
                    <#language_struct as mettail_runtime::Language>::metadata(&#language_struct)
                        .definition_fingerprint()
                        .unwrap_or_default(),
                    __runner as fn(&dyn mettail_runtime::Term) -> Result<mettail_runtime::RuntimeDovetailRunReport, String>,
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(fragment: &str) -> LanguageDef {
        syn::parse_str(fragment).expect("test language fragment must parse")
    }

    #[test]
    fn generated_report_uses_structured_constructor_rules() {
        let language = parse(
            r#"
                name: DovetailSmoke,
                types { Expr }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                    Wrap . x:Expr |- "wrap" "(" x ")" : Expr ;
                }
                equations {}
                rewrites {
                    AToB . |- A ~> B ;
                }
            "#,
        );

        let tokens = generate_dovetail_report(&language).to_string();
        let (_, unsupported) = rule_block(&language);
        assert!(tokens.contains("dovetail_report_for"));
        assert!(tokens.contains("DovetailSmoke"));
        assert!(tokens.contains("AToB"));
        assert!(unsupported.is_empty(), "unexpected unsupported rules: {unsupported:?}");
    }

    #[test]
    fn generated_report_fails_closed_for_binder_metapatterns() {
        let language = parse(
            r#"
                name: DovetailBinder,
                types { Expr Name }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                    Lam . ^x.p:[Name -> Expr] |- "lam" x "." p : Expr ;
                }
                equations {}
                rewrites {
                    BadBeta . |- (Lam ^x.A) ~> B ;
                }
            "#,
        );

        let tokens = generate_dovetail_report(&language).to_string();
        assert!(tokens.contains("dovetail_report_for"));
        assert!(tokens.contains("lambda patterns require binder lowering"));
    }
}
