//! E3 — per-language Rho **dataflow** invocation emitter.
//!
//! Generalizes the single-op emitter [`crate::gen::runtime::rho_invocation`] from "lower ONE scalar
//! rule with ground-literal operands" to "lower a NESTED scalar expression tree to a Rholang
//! dataflow of contract calls." Like the single-op emitter it is behind the expansion-site
//! `rho-codegen` feature, downcasts the generated typed AST, and reuses the same scalar plan
//! ([`mettail_rholang_codegen::plan_scalar_invocations`]) — but instead of extracting each operand
//! as a ground literal, it RECURSES into operands: a leaf scalar literal becomes a
//! [`RhoDataflowChild::Leaf`], a nested scalar op becomes a [`RhoDataflowChild::Node`] (post-order),
//! and the accumulated node list is assembled into a closed `call` `Par` by the runtime-free
//! [`mettail_rholang_codegen::build_dataflow_call_par`].
//!
//! ## Defer and semantic-predicate gates
//! A term returns [`RhoFoldDataflowDisposition::Defer`] when its shape is not fully Rho-lowerable (a
//! non-scalar op / free variable / a literal of the wrong kind: the recursive collector returns
//! `None`). A structurally lowerable term whose generated `try_eval()` returns `None` (integer
//! overflow, `÷0`, `%0`) returns [`RhoFoldDataflowDisposition::BlockedBySemanticPredicate`].
//! Splitting these cases lets runtime planning keep true semantic predicates separate from shape
//! rejection while still avoiding unguarded Rho expressions that would hard-error inside the
//! reducer.

use std::collections::{BTreeMap, BTreeSet};

use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{
    lower_language_def, plan_scalar_invocations, RhoScalarInvocationPlan, RhoScalarType,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Ident, LitStr};

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn lit(value: &str) -> LitStr {
    LitStr::new(value, Span::call_site())
}

fn collect_fn_ident(category: &str) -> Ident {
    format_ident!("__mettail_rho_dataflow_collect_{}", to_snake(category))
}

fn root_fn_ident(category: &str) -> Ident {
    format_ident!("__mettail_rho_dataflow_root_{}", to_snake(category))
}

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

fn scalar_type_expr(scalar_type: RhoScalarType) -> TokenStream {
    match scalar_type {
        RhoScalarType::Int => quote! { ::mettail_rholang_codegen::RhoScalarType::Int },
        RhoScalarType::Bool => quote! { ::mettail_rholang_codegen::RhoScalarType::Bool },
        RhoScalarType::Str => quote! { ::mettail_rholang_codegen::RhoScalarType::Str },
    }
}

/// The `RhoAstLiteral` constructor for a scalar leaf of the given type, applied to the matched
/// `value` binding (mirrors `rho_invocation::literal_extractor`).
fn leaf_literal_token(scalar_type: RhoScalarType) -> TokenStream {
    match scalar_type {
        RhoScalarType::Int => {
            quote! { ::mettail_rholang_codegen::RhoAstLiteral::Int(i64::from(*value)) }
        },
        RhoScalarType::Bool => quote! { ::mettail_rholang_codegen::RhoAstLiteral::Bool(*value) },
        RhoScalarType::Str => {
            quote! { ::mettail_rholang_codegen::RhoAstLiteral::String(value.clone()) }
        },
    }
}

fn compile_error_tokens(message: String) -> TokenStream {
    let message = lit(&message);
    quote! {
        #[cfg(feature = "rho-codegen")]
        compile_error!(#message);
    }
}

/// The recursive collector for one scalar category: matches each op variant producing the category
/// (recursing each operand), the category's scalar literal variant (a [`RhoDataflowChild::Leaf`]),
/// else `None` (a non-lowerable variant ⇒ Defer).
fn collector_fn(
    language: &LanguageDef,
    category: &str,
    scalar_type: RhoScalarType,
    op_plans: &[&RhoScalarInvocationPlan],
) -> Result<TokenStream, String> {
    let category_ident = ident(category);
    let fn_name = collect_fn_ident(category);

    let mut op_arms = Vec::with_capacity(op_plans.len());
    for plan in op_plans {
        let label_ident = ident(&plan.rule_label);
        let label_lit = lit(&plan.rule_label);
        let fields: Vec<Ident> = (0..plan.operands.len())
            .map(|i| format_ident!("field_{i}"))
            .collect();
        let op_idents: Vec<Ident> = (0..plan.operands.len())
            .map(|i| format_ident!("__op_{i}"))
            .collect();
        let recurse: Vec<TokenStream> = plan
            .operands
            .iter()
            .zip(fields.iter())
            .zip(op_idents.iter())
            .map(|((operand, field), op_ident)| {
                let operand_collect = collect_fn_ident(&operand.category);
                quote! { let #op_ident = #operand_collect(#field.as_ref(), nodes)?; }
            })
            .collect();
        op_arms.push(quote! {
            #category_ident::#label_ident(#(#fields),*) => {
                #(#recurse)*
                let __idx = nodes.len();
                nodes.push(::mettail_rholang_codegen::RhoDataflowNode {
                    label: #label_lit.to_string(),
                    operands: ::std::vec![#(#op_idents),*],
                });
                ::core::option::Option::Some(::mettail_rholang_codegen::RhoDataflowChild::Node(__idx))
            },
        });
    }

    // Scalar literal arm: the category's ground literal variant becomes a Leaf.
    let lit_variant = crate::gen::runtime::rho_invocation::scalar_literal_variant(
        language,
        category,
        scalar_type,
    )?;
    let leaf = leaf_literal_token(scalar_type);

    Ok(quote! {
        fn #fn_name(
            node: &#category_ident,
            nodes: &mut ::std::vec::Vec<::mettail_rholang_codegen::RhoDataflowNode>,
        ) -> ::core::option::Option<::mettail_rholang_codegen::RhoDataflowChild> {
            match node {
                #(#op_arms)*
                #category_ident::#lit_variant(value) => {
                    ::core::option::Option::Some(::mettail_rholang_codegen::RhoDataflowChild::Leaf(#leaf))
                },
                _ => ::core::option::Option::None,
            }
        }
    })
}

/// The per-scalar-category root entry: collect the dataflow off `node`, gate on `try_eval`
/// (safe-evaluability ⇒ parity with Dovetail), and assemble the closed `call` `Par`.
fn root_fn(category: &str, scalar_type: RhoScalarType) -> TokenStream {
    let category_ident = ident(category);
    let fn_name = root_fn_ident(category);
    let collect = collect_fn_ident(category);
    let result_type = scalar_type_expr(scalar_type);
    quote! {
        fn #fn_name(
            node: &#category_ident,
            out_channel: &str,
        ) -> ::core::result::Result<::mettail_rholang_codegen::RhoFoldDataflowDisposition, ::std::string::String> {
            let mut nodes = ::std::vec::Vec::new();
            let __root = match #collect(node, &mut nodes) {
                ::core::option::Option::Some(child) => child,
                // Not fully Rho-lowerable (non-scalar op / free var / wrong literal) ⇒ rejected by
                // the Rho-default runtime wrapper rather than routed through Dovetail execution.
                ::core::option::Option::None => {
                    return ::core::result::Result::Ok(
                        ::mettail_rholang_codegen::RhoFoldDataflowDisposition::Defer,
                    );
                },
            };
            // A structurally Rho-lowerable term can still be blocked by a semantic predicate:
            // overflow / ÷0 / %0 would hard-error in the unguarded Rho expression, while the
            // generated safe evaluator declines it.
            if node.try_eval().is_none() {
                return ::core::result::Result::Ok(
                    ::mettail_rholang_codegen::RhoFoldDataflowDisposition::BlockedBySemanticPredicate(
                        ::mettail_rholang_codegen::RhoFoldDataflowPredicateBlock::SafeEvaluationDeclined,
                    ),
                );
            }
            let call = ::mettail_rholang_codegen::build_dataflow_call_par(&nodes, &__root, out_channel)
                .map_err(|err| ::std::format!("E3 dataflow assembly failed: {err}"))?;
            ::core::result::Result::Ok(::mettail_rholang_codegen::RhoFoldDataflowDisposition::Run(
                ::mettail_rholang_codegen::RhoFoldDataflowInvocation {
                    call,
                    out_channel: out_channel.to_string(),
                    result_type: #result_type,
                },
            ))
        }
    }
}

/// Generate the opt-in `rho_fold_dataflow_invocation_to` / `_from_dovetail_to` helpers that lower a
/// generated typed AST scalar expression tree to a Rholang dataflow invocation (or Defer).
pub fn generate_rho_fold_dataflow(language: &LanguageDef) -> TokenStream {
    let lowering = lower_language_def(language);
    let plans = match plan_scalar_invocations(language, &lowering) {
        Ok(plans) => plans,
        Err(err) => {
            return compile_error_tokens(format!(
                "failed to derive generated Rho fold-dataflow plan: {err:?}"
            ));
        },
    };

    let name = &language.name;
    let language_struct = format_ident!("{}Language", name);
    let language_name = name.to_string();
    let language_lit = lit(&language_name);
    let term_name = format_ident!("{}Term", name);

    // Empty plan inventory (no Rho-lowerable scalar rule): the helper exists but always Defers.
    if plans.is_empty() {
        return quote! {
            #[cfg(feature = "rho-codegen")]
            impl #language_struct {
                pub fn rho_fold_dataflow_invocation_to(
                    term: &dyn mettail_runtime::Term,
                    out_channel: impl AsRef<str>,
                ) -> ::core::result::Result<::mettail_rholang_codegen::RhoFoldDataflowDisposition, ::std::string::String> {
                    let _ = (term, out_channel);
                    ::core::result::Result::Ok(::mettail_rholang_codegen::RhoFoldDataflowDisposition::Defer)
                }

                pub fn rho_fold_dataflow_invocation_from_dovetail_to(
                    term: &dyn mettail_runtime::Term,
                    report: &mettail_runtime::RuntimeDovetailRunReport,
                    out_channel: impl AsRef<str>,
                ) -> ::core::result::Result<::mettail_rholang_codegen::RhoFoldDataflowDisposition, ::std::string::String> {
                    report.assert_complete().map_err(|status| {
                        ::std::format!(
                            "Rho fold dataflow for language {} requires a complete Dovetail report, got {}",
                            #language_lit, status,
                        )
                    })?;
                    Self::rho_fold_dataflow_invocation_to(term, out_channel)
                }
            }
        };
    }

    // Per-category scalar type + op-plan grouping; the union of result and operand categories needs
    // a collector (operands may be a leaf-only scalar category with no ops of its own).
    let mut category_scalar: BTreeMap<String, RhoScalarType> = BTreeMap::new();
    let mut op_plans_by_cat: BTreeMap<String, Vec<&RhoScalarInvocationPlan>> = BTreeMap::new();
    for plan in &plans {
        category_scalar.insert(plan.result_category.clone(), plan.result_scalar_type);
        op_plans_by_cat
            .entry(plan.result_category.clone())
            .or_default()
            .push(plan);
        for operand in &plan.operands {
            category_scalar.insert(operand.category.clone(), operand.scalar_type);
        }
    }

    // Collectors for every category that can appear as a result or operand.
    let mut collectors = Vec::with_capacity(category_scalar.len());
    for (category, scalar_type) in &category_scalar {
        let empty: Vec<&RhoScalarInvocationPlan> = Vec::new();
        let op_plans = op_plans_by_cat.get(category).unwrap_or(&empty);
        match collector_fn(language, category, *scalar_type, op_plans) {
            Ok(tokens) => collectors.push(tokens),
            Err(err) => return compile_error_tokens(err),
        }
    }

    // A root entry per scalar category (any scalar category may be the whole term's top operand —
    // including a bare literal like `exec 5`).
    let roots: Vec<TokenStream> = category_scalar
        .iter()
        .map(|(category, scalar_type)| root_fn(category, *scalar_type))
        .collect();

    // Dispatch on the term's root category. Multi-type languages match the `TermInner` enum (with an
    // `Ambiguous` find-first-Run arm); a single-type language's `.0` IS the category.
    let root_categories: BTreeSet<&str> = category_scalar.keys().map(|s| s.as_str()).collect();
    let dispatch_body = if language.types.len() > 1 {
        let inner_enum = format_ident!("{}TermInner", name);
        let inner_arms: Vec<TokenStream> = root_categories
            .iter()
            .map(|category| {
                let category_ident = ident(category);
                let root = root_fn_ident(category);
                quote! { #inner_enum::#category_ident(value) => #root(value, out_channel), }
            })
            .collect();
        let all_declared_types_covered = language.types.iter().all(|ty| {
            let ty_name = ty.name.to_string();
            root_categories.contains(ty_name.as_str())
        });
        let fallback_arm = if all_declared_types_covered {
            quote! {}
        } else {
            quote! {
                _ => ::core::result::Result::Ok(::mettail_rholang_codegen::RhoFoldDataflowDisposition::Defer),
            }
        };
        quote! {
            fn __mettail_rho_dataflow_dispatch(
                inner: &#inner_enum,
                out_channel: &str,
            ) -> ::core::result::Result<::mettail_rholang_codegen::RhoFoldDataflowDisposition, ::std::string::String> {
                match inner {
                    #(#inner_arms)*
                    #inner_enum::Ambiguous(alternatives) => {
                        let mut __mettail_semantic_predicate_block = ::core::option::Option::None;
                        for alternative in alternatives {
                            match __mettail_rho_dataflow_dispatch(alternative, out_channel)? {
                                ::mettail_rholang_codegen::RhoFoldDataflowDisposition::Run(invocation) => {
                                    return ::core::result::Result::Ok(
                                        ::mettail_rholang_codegen::RhoFoldDataflowDisposition::Run(invocation),
                                    );
                                },
                                ::mettail_rholang_codegen::RhoFoldDataflowDisposition::BlockedBySemanticPredicate(reason) => {
                                    if __mettail_semantic_predicate_block.is_none() {
                                        __mettail_semantic_predicate_block = ::core::option::Option::Some(reason);
                                    }
                                },
                                ::mettail_rholang_codegen::RhoFoldDataflowDisposition::Defer => {},
                            }
                        }
                        match __mettail_semantic_predicate_block {
                            ::core::option::Option::Some(reason) => {
                                ::core::result::Result::Ok(
                                    ::mettail_rholang_codegen::RhoFoldDataflowDisposition::BlockedBySemanticPredicate(reason),
                                )
                            },
                            ::core::option::Option::None => {
                                ::core::result::Result::Ok(::mettail_rholang_codegen::RhoFoldDataflowDisposition::Defer)
                            },
                        }
                    },
                    #fallback_arm
                }
            }

            let typed_term = term
                .as_any()
                .downcast_ref::<#term_name>()
                .ok_or_else(|| ::std::format!("expected {}Term, got {:?}", #language_lit, term))?;
            __mettail_rho_dataflow_dispatch(&typed_term.0, out_channel.as_ref())
        }
    } else {
        // Single-category language: `.0` is the one category. Dispatch to its root if it is scalar.
        let only = language
            .types
            .first()
            .expect("a language has at least one type");
        let only_name = only.name.to_string();
        if root_categories.contains(only_name.as_str()) {
            let root = root_fn_ident(&only_name);
            quote! {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| ::std::format!("expected {}Term, got {:?}", #language_lit, term))?;
                #root(&typed_term.0, out_channel.as_ref())
            }
        } else {
            quote! {
                let _ = (term, out_channel);
                ::core::result::Result::Ok(::mettail_rholang_codegen::RhoFoldDataflowDisposition::Defer)
            }
        }
    };

    quote! {
        #[cfg(feature = "rho-codegen")]
        impl #language_struct {
            /// Lower this language's generated typed AST scalar expression tree into a Rholang
            /// dataflow invocation (one contract call per node, wired through intermediate channels),
            /// [`RhoFoldDataflowDisposition::Defer`] for a non-lowerable term, or
            /// [`RhoFoldDataflowDisposition::BlockedBySemanticPredicate`] for a lowerable term
            /// blocked by a semantic predicate such as safe arithmetic.
            ///
            /// Generalizes [`Self::rho_scalar_contract_invocation_to`] (one node) to a nested tree.
            pub fn rho_fold_dataflow_invocation_to(
                term: &dyn mettail_runtime::Term,
                out_channel: impl AsRef<str>,
            ) -> ::core::result::Result<::mettail_rholang_codegen::RhoFoldDataflowDisposition, ::std::string::String> {
                #(#collectors)*
                #(#roots)*
                #dispatch_body
            }

            /// As [`Self::rho_fold_dataflow_invocation_to`], after asserting the Dovetail report is
            /// complete (the F-stage precondition; semantic-predicate deferral can carry that
            /// checked report as evidence).
            pub fn rho_fold_dataflow_invocation_from_dovetail_to(
                term: &dyn mettail_runtime::Term,
                report: &mettail_runtime::RuntimeDovetailRunReport,
                out_channel: impl AsRef<str>,
            ) -> ::core::result::Result<::mettail_rholang_codegen::RhoFoldDataflowDisposition, ::std::string::String> {
                report.assert_complete().map_err(|status| {
                    ::std::format!(
                        "Rho fold dataflow for language {} requires a complete Dovetail report, got {}",
                        #language_lit, status,
                    )
                })?;
                Self::rho_fold_dataflow_invocation_to(term, out_channel)
            }
        }
    }
}
