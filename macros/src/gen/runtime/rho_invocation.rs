//! Rho scalar invocation helper generation.
//!
//! Generated language crates stay substrate-neutral by default. The items this
//! module emits are behind the expansion-site `rho-codegen` feature and return
//! codegen-owned scalar invocation payloads. Runtime-facing crates normalize
//! those payloads through `mettail-rho-runtime`.

use std::collections::{BTreeMap, BTreeSet};

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{
    lower_language_def, plan_scalar_invocations, RhoScalarContractShape, RhoScalarInvocationPlan,
    RhoScalarType,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Ident, LitStr};

use crate::gen::{generate_literal_label, literal_rule_nonterminal};

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

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn lit(value: &str) -> LitStr {
    LitStr::new(value, Span::call_site())
}

fn scalar_type_expr(scalar_type: RhoScalarType) -> TokenStream {
    match scalar_type {
        RhoScalarType::Int => quote! { ::mettail_rholang_codegen::RhoScalarType::Int },
        RhoScalarType::Bool => quote! { ::mettail_rholang_codegen::RhoScalarType::Bool },
        RhoScalarType::Str => quote! { ::mettail_rholang_codegen::RhoScalarType::Str },
    }
}

fn abi_expr(plan: &RhoScalarInvocationPlan) -> TokenStream {
    let rule_label = lit(&plan.abi.rule_label);
    let shape = match plan.abi.shape {
        RhoScalarContractShape::UnaryPrefix { argument, result } => {
            let argument = scalar_type_expr(argument);
            let result = scalar_type_expr(result);
            quote! {
                ::mettail_rholang_codegen::RhoScalarContractShape::UnaryPrefix {
                    argument: #argument,
                    result: #result,
                }
            }
        },
        RhoScalarContractShape::BinaryInfix { left, right, result } => {
            let left = scalar_type_expr(left);
            let right = scalar_type_expr(right);
            let result = scalar_type_expr(result);
            quote! {
                ::mettail_rholang_codegen::RhoScalarContractShape::BinaryInfix {
                    left: #left,
                    right: #right,
                    result: #result,
                }
            }
        },
    };

    quote! {
        ::mettail_rholang_codegen::RhoScalarContractAbi {
            rule_label: #rule_label.to_string(),
            shape: #shape,
        }
    }
}

fn literal_kind_matches(kind: NonTerminalKind, scalar_type: RhoScalarType) -> bool {
    matches!(
        (kind, scalar_type),
        (NonTerminalKind::Integer, RhoScalarType::Int)
            | (NonTerminalKind::Boolean, RhoScalarType::Bool)
            | (NonTerminalKind::StringLiteral, RhoScalarType::Str)
    )
}

pub(crate) fn scalar_literal_variant(
    language: &LanguageDef,
    category: &str,
    scalar_type: RhoScalarType,
) -> Result<Ident, String> {
    for rule in language
        .terms
        .iter()
        .filter(|rule| rule.category == ident(category))
    {
        if literal_rule_nonterminal(rule)
            .is_some_and(|kind| literal_kind_matches(kind, scalar_type))
        {
            return Ok(rule.label.clone());
        }
    }

    let category_ident = ident(category);
    let lang_type = language.get_type(&category_ident).ok_or_else(|| {
        format!("Rho scalar invocation planning referenced missing category {category}")
    })?;
    let native_type = lang_type.native_type.as_ref().ok_or_else(|| {
        format!("Rho scalar invocation planning referenced non-native category {category}")
    })?;
    Ok(generate_literal_label(native_type))
}

fn literal_extractor_name(category: &str) -> Ident {
    format_ident!("__mettail_rho_literal_{}", to_snake(category))
}

fn literal_extractor(
    language: &LanguageDef,
    category: &str,
    scalar_type: RhoScalarType,
) -> Result<TokenStream, String> {
    let category_ident = ident(category);
    let variant = scalar_literal_variant(language, category, scalar_type)?;
    let function_name = literal_extractor_name(category);
    let category_lit = lit(category);
    let scalar_lit = lit(match scalar_type {
        RhoScalarType::Int => "integer",
        RhoScalarType::Bool => "boolean",
        RhoScalarType::Str => "string",
    });
    let body = match scalar_type {
        RhoScalarType::Int => quote! {
            #category_ident::#variant(value) => {
                Ok(::mettail_rholang_codegen::RhoAstLiteral::Int(i64::from(*value)))
            }
        },
        RhoScalarType::Bool => quote! {
            #category_ident::#variant(value) => {
                Ok(::mettail_rholang_codegen::RhoAstLiteral::Bool(*value))
            }
        },
        RhoScalarType::Str => quote! {
            #category_ident::#variant(value) => {
                Ok(::mettail_rholang_codegen::RhoAstLiteral::String(value.clone()))
            }
        },
    };

    Ok(quote! {
        fn #function_name(
            term: &#category_ident,
        ) -> Result<::mettail_rholang_codegen::RhoAstLiteral, String> {
            match term {
                #body,
                other => Err(format!(
                    "Rho scalar invocation for category {} needs a ground {} literal, got {:?}",
                    #category_lit,
                    #scalar_lit,
                    other,
                )),
            }
        }
    })
}

fn build_invocation_expr(plan: &RhoScalarInvocationPlan) -> TokenStream {
    let abi = abi_expr(plan);
    let mut argument_exprs = Vec::with_capacity(plan.operands.len());
    for operand in &plan.operands {
        let field = format_ident!("field_{}", operand.field_position);
        let extractor = literal_extractor_name(&operand.category);
        argument_exprs.push(quote! { #extractor(#field.as_ref())? });
    }

    quote! {
        (|| -> Result<::mettail_rholang_codegen::RhoScalarContractInvocation, String> {
            let __mettail_rho_abi = #abi;
            let __mettail_rho_arguments = vec![#(#argument_exprs),*];
            Ok(::mettail_rholang_codegen::RhoScalarContractInvocation::new(
                __mettail_rho_abi,
                __mettail_rho_arguments,
                out_channel.to_string(),
            ))
        })()
    }
}

fn plan_arm_result(plan: &RhoScalarInvocationPlan) -> TokenStream {
    let category = ident(&plan.result_category);
    let label = ident(&plan.rule_label);
    let fields: Vec<Ident> = (0..plan.operands.len())
        .map(|index| format_ident!("field_{index}"))
        .collect();
    let invocation = build_invocation_expr(plan);

    quote! {
        #category::#label(#(#fields),*) => {
            return #invocation;
        }
    }
}

fn plan_arm_option(plan: &RhoScalarInvocationPlan) -> TokenStream {
    let category = ident(&plan.result_category);
    let label = ident(&plan.rule_label);
    let fields: Vec<Ident> = (0..plan.operands.len())
        .map(|index| format_ident!("field_{index}"))
        .collect();
    let invocation = build_invocation_expr(plan);

    quote! {
        #category::#label(#(#fields),*) => {
            Some(#invocation)
        }
    }
}

fn category_match_arms(plans: &[RhoScalarInvocationPlan]) -> BTreeMap<String, Vec<TokenStream>> {
    let mut out: BTreeMap<String, Vec<TokenStream>> = BTreeMap::new();
    for plan in plans {
        out.entry(plan.result_category.clone())
            .or_default()
            .push(plan_arm_option(plan));
    }
    out
}

fn no_match_expr(language_name: &str) -> TokenStream {
    let language_lit = lit(language_name);
    quote! {
        Err(format!(
            "Rho scalar invocation planner for language {} has no ground scalar contract for {:?}",
            #language_lit,
            typed_term,
        ))
    }
}

fn multi_category_try_fn(language: &LanguageDef, plans: &[RhoScalarInvocationPlan]) -> TokenStream {
    let name = &language.name;
    let inner_enum = format_ident!("{}TermInner", name);
    let root_categories: BTreeSet<&str> = plans
        .iter()
        .map(|plan| plan.result_category.as_str())
        .collect();
    let all_declared_types_covered = language.types.iter().all(|ty| {
        let ty_name = ty.name.to_string();
        root_categories.contains(ty_name.as_str())
    });
    let fallback_arm = if all_declared_types_covered {
        quote! {}
    } else {
        quote! { _ => None, }
    };
    let mut inner_arms = Vec::new();
    for (category, arms) in category_match_arms(plans) {
        let category_ident = ident(&category);
        inner_arms.push(quote! {
            #inner_enum::#category_ident(value) => {
                match value {
                    #(#arms)*
                    _ => None,
                }
            }
        });
    }

    quote! {
        fn __mettail_rho_try_scalar_inner(
            inner: &#inner_enum,
            out_channel: &str,
        ) -> Option<Result<::mettail_rholang_codegen::RhoScalarContractInvocation, String>> {
            match inner {
                #(#inner_arms)*
                #inner_enum::Ambiguous(alternatives) => {
                    alternatives
                        .iter()
                        .find_map(|alternative| {
                            __mettail_rho_try_scalar_inner(alternative, out_channel)
                        })
                },
                #fallback_arm
            }
        }
    }
}

fn invocation_body(language: &LanguageDef, plans: &[RhoScalarInvocationPlan]) -> TokenStream {
    let name = &language.name;
    let language_name = name.to_string();
    let term_name = format_ident!("{}Term", name);
    let no_match = no_match_expr(&language_name);

    if language.types.len() > 1 {
        let try_fn = multi_category_try_fn(language, plans);
        quote! {
            #try_fn

            let typed_term = term
                .as_any()
                .downcast_ref::<#term_name>()
                .ok_or_else(|| format!("expected {}Term, got {:?}", #language_name, term))?;
            let out_channel = out_channel.as_ref();
            match __mettail_rho_try_scalar_inner(&typed_term.0, out_channel) {
                Some(result) => result,
                None => #no_match,
            }
        }
    } else {
        let arms: Vec<TokenStream> = plans.iter().map(plan_arm_result).collect();
        quote! {
            let typed_term = term
                .as_any()
                .downcast_ref::<#term_name>()
                .ok_or_else(|| format!("expected {}Term, got {:?}", #language_name, term))?;
            let out_channel = out_channel.as_ref();
            match &typed_term.0 {
                #(#arms)*
                _ => #no_match,
            }
        }
    }
}

fn compile_error_tokens(message: String) -> TokenStream {
    let message = lit(&message);
    quote! {
        #[cfg(feature = "rho-codegen")]
        compile_error!(#message);
    }
}

/// Generate opt-in helpers that turn generated typed AST constructors into
/// checked Rho scalar contract invocations.
pub fn generate_rho_scalar_invocation(language: &LanguageDef) -> TokenStream {
    let lowering = lower_language_def(language);
    let plans = match plan_scalar_invocations(language, &lowering) {
        Ok(plans) => plans,
        Err(err) => {
            return compile_error_tokens(format!(
                "failed to derive generated Rho scalar invocation plan: {err:?}"
            ));
        },
    };

    let name = &language.name;
    let language_struct = format_ident!("{}Language", name);
    let language_name = name.to_string();
    let language_lit = lit(&language_name);

    let mut literal_categories = BTreeMap::<String, RhoScalarType>::new();
    for plan in &plans {
        for operand in &plan.operands {
            match literal_categories.get(&operand.category) {
                Some(existing) if *existing != operand.scalar_type => {
                    return compile_error_tokens(format!(
                        "category {} is used as both {:?} and {:?} in Rho scalar invocation plans",
                        operand.category, existing, operand.scalar_type
                    ));
                },
                _ => {
                    literal_categories.insert(operand.category.clone(), operand.scalar_type);
                },
            }
        }
    }

    let literal_extractors = match literal_categories
        .iter()
        .map(|(category, scalar_type)| literal_extractor(language, category, *scalar_type))
        .collect::<Result<Vec<_>, _>>()
    {
        Ok(extractors) => extractors,
        Err(err) => return compile_error_tokens(err),
    };

    let body = if plans.is_empty() {
        quote! {
            let _ = (term, out_channel);
            Err(format!(
                "language {} has no lowered Rho scalar contract invocation plan",
                #language_lit,
            ))
        }
    } else {
        invocation_body(language, &plans)
    };

    let plan_labels: BTreeSet<&str> = plans.iter().map(|plan| plan.rule_label.as_str()).collect();
    let plan_label_list = plan_labels.into_iter().collect::<Vec<_>>().join(", ");
    let plan_label_lit = lit(&plan_label_list);

    quote! {
        #[cfg(feature = "rho-codegen")]
        impl #language_struct {
            /// Compile this language's generated typed AST into an ABI-checked
            /// Rho scalar-contract invocation.
            ///
            /// The emitted Rholang-looking contract names are annotations only:
            /// execution carries normalized `rhoapi::Par` through
            /// `mettail_rholang_runtime::build_scalar_contract_invocation_from_contract`.
            ///
            /// Formal model: `formal/rocq/rho_bridge/theories/RhoScalarOperatorTyping.v`.
            pub fn rho_scalar_contract_invocation_to(
                term: &dyn mettail_runtime::Term,
                out_channel: impl AsRef<str>,
            ) -> Result<::mettail_rholang_codegen::RhoScalarContractInvocation, String> {
                #(#literal_extractors)*
                #body
            }

            /// Compile a scalar invocation after the Dovetail stage has already
            /// produced a complete, shape-validated report.
            pub fn rho_scalar_contract_invocation_from_dovetail_to(
                term: &dyn mettail_runtime::Term,
                report: &mettail_runtime::RuntimeDovetailRunReport,
                out_channel: impl AsRef<str>,
            ) -> Result<::mettail_rholang_codegen::RhoScalarContractInvocation, String> {
                report.assert_complete().map_err(|status| {
                    format!(
                        "Rho scalar invocation for language {} requires a complete Dovetail report, got {}",
                        #language_lit,
                        status,
                    )
                })?;
                Self::rho_scalar_contract_invocation_to(term, out_channel)
            }

            /// Rule labels accepted by the generated scalar invocation mapper.
            pub fn rho_scalar_invocation_rule_labels() -> &'static str {
                #plan_label_lit
            }
        }
    }
}

/// Generate the opt-in `rho_net_invocation_from_dovetail_to` helper: the Rho-net
/// σ-injection F-function.
///
/// It reads a rewrite firing's justification from an already complete Dovetail
/// report (whose σ constructor labels the report producer bare-ified to their
/// source form), matches the fired rule to a base-rewrite σ-receiver
/// [injection site](mettail_rholang_codegen::RhoNetInjectionSite), reorders the σ
/// into the receiver's first-occurrence LHS variable order, reflects each matched
/// sub-term to a ground `Par`, and assembles the σ-injection
/// [`RhoNetInjectionInvocation`](mettail_rholang_codegen::RhoNetInjectionInvocation)
/// the runtime runs against the installed σ-receiver program. This mirrors
/// [`generate_rho_fold_dataflow`](crate::gen::runtime::rho_dataflow::generate_rho_fold_dataflow):
/// codegen-typed output, no `mettail-rholang-runtime` dependency.
pub fn generate_rho_net_invocation(language: &LanguageDef) -> TokenStream {
    let name = &language.name;
    let language_struct = format_ident!("{}Language", name);
    let language_name = name.to_string();
    let language_lit = lit(&language_name);

    let sites = mettail_rholang_codegen::rho_net_injection_sites(language);

    let body = if sites.is_empty() {
        // No base-rewrite σ-receiver: the helper exists for a uniform surface but
        // always fails closed (there is nothing to inject).
        quote! {
            report.assert_complete().map_err(|status| {
                ::std::format!(
                    "Rho-net injection for language {} requires a complete Dovetail report, got {}",
                    #language_lit, status,
                )
            })?;
            let _ = (term, out_channel, firing_index);
            ::core::result::Result::Err(::std::format!(
                "language {} has no Rho-net σ-receiver injection sites",
                #language_lit,
            ))
        }
    } else {
        let site_arms: Vec<TokenStream> = sites
            .iter()
            .map(|site| {
                let label = lit(&site.rule_label);
                let channel = lit(&site.channel);
                let vars: Vec<LitStr> = site.lhs_var_order.iter().map(|var| lit(var)).collect();
                quote! {
                    #label => (#channel, &[#(#vars),*][..]),
                }
            })
            .collect();

        quote! {
            report.assert_complete().map_err(|status| {
                ::std::format!(
                    "Rho-net injection for language {} requires a complete Dovetail report, got {}",
                    #language_lit, status,
                )
            })?;
            let _ = term;
            let out_channel = out_channel.as_ref();

            // Rebuild a runtime-neutral σ sub-term into a codegen ground term (same
            // `{ constructor, children }` shape). The report producer already
            // bare-ified each constructor to its source label, so reflection tags it
            // identically to the σ-receiver's compiled RHS constructors.
            fn __mettail_rho_net_to_ground(
                subterm: &mettail_runtime::RuntimeReflectedSubterm,
            ) -> ::mettail_rholang_codegen::GroundTerm {
                ::mettail_rholang_codegen::GroundTerm::new(
                    subterm.constructor.clone(),
                    subterm.children.iter().map(__mettail_rho_net_to_ground).collect(),
                )
            }

            // The reflection fingerprint MUST equal the one the installed σ-receiver
            // was compiled with. The install boundary requires
            // `metadata().definition_fingerprint() == plan.definition_fingerprint()`,
            // and the σ-receiver reflects its RHS constructors with that plan
            // fingerprint, so reading it from metadata here cannot drift.
            let __fingerprint = <#language_struct as mettail_runtime::Language>::metadata(
                &#language_struct,
            )
            .definition_fingerprint()
            .ok_or_else(|| {
                ::std::format!(
                    "language {} has no definition fingerprint for Rho-net σ reflection",
                    #language_lit,
                )
            })?;

            // The rewrite firing at `firing_index` in the report's ordered
            // justification list. Stage 0 multi-firing: the replay driver fires
            // each firing as its own atomic COMM (distinct out channel per firing).
            // An out-of-range index has nothing to inject there.
            let __justification = report
                .rewrite_justifications
                .get(firing_index)
                .ok_or_else(|| {
                    ::std::format!(
                        "Rho-net injection for language {} has no rewrite justification at firing index {}",
                        #language_lit, firing_index,
                    )
                })?;

            let (__channel, __var_order): (&str, &[&str]) =
                match __justification.rule_label.as_str() {
                    #(#site_arms)*
                    __other => {
                        return ::core::result::Result::Err(::std::format!(
                            "Rho-net injection for language {} has no σ-receiver for fired rule {}",
                            #language_lit, __other,
                        ));
                    },
                };

            // Reorder the report's (name-sorted) σ into the σ-receiver's
            // first-occurrence LHS variable order and reflect each sub-term.
            let mut __args = ::std::vec::Vec::with_capacity(__var_order.len());
            for __var in __var_order {
                let __subterm = __justification
                    .sigma
                    .iter()
                    .find(|(__name, _)| __name.as_str() == *__var)
                    .map(|(_, __subterm)| __subterm)
                    .ok_or_else(|| {
                        ::std::format!(
                            "Rho-net injection for language {} is missing σ binding for LHS variable {}",
                            #language_lit, __var,
                        )
                    })?;
                let __ground = __mettail_rho_net_to_ground(__subterm);
                __args.push(::mettail_rholang_codegen::reflect_ground_term_par(
                    &__ground,
                    __fingerprint,
                ));
            }

            let __call =
                ::mettail_rholang_codegen::term_contract_call(__channel, __args, out_channel);
            ::core::result::Result::Ok(::mettail_rholang_codegen::RhoNetInjectionInvocation {
                call: __call,
                out_channel: out_channel.to_string(),
            })
        }
    };

    quote! {
        #[cfg(feature = "rho-codegen")]
        impl #language_struct {
            /// Build a Rho-net σ-injection for the rewrite firing at `firing_index`
            /// in an already complete, shape-validated Dovetail report: read that
            /// firing's justification, reorder its σ into the fired σ-receiver's
            /// first-occurrence LHS variable order, reflect each matched sub-term to
            /// a ground `Par`, and assemble the injection `call` the runtime runs
            /// against the installed σ-receiver program
            /// (`installed_rho_net_program_par() ∥ call`).
            ///
            /// Stage 0 multi-firing surface: the replay driver
            /// (`run_rho_net_replay_report`) calls this once per firing in
            /// `report.rewrite_justifications`, each with its own out channel, so a
            /// multi-redex term replays every firing as its own atomic COMM. The
            /// single-firing [`Self::rho_net_invocation_from_dovetail_to`] delegates
            /// here with `firing_index = 0`. Returns codegen types
            /// (`RhoNetInjectionInvocation`) so the language crate takes no Rho
            /// runtime dependency.
            pub fn rho_net_invocation_from_dovetail_to_firing(
                term: &dyn mettail_runtime::Term,
                report: &mettail_runtime::RuntimeDovetailRunReport,
                out_channel: impl ::core::convert::AsRef<str>,
                firing_index: usize,
            ) -> ::core::result::Result<
                ::mettail_rholang_codegen::RhoNetInjectionInvocation,
                ::std::string::String,
            > {
                #body
            }

            /// Build a Rho-net σ-injection from the FIRST rewrite firing of an
            /// already complete, shape-validated Dovetail report — convenience over
            /// [`Self::rho_net_invocation_from_dovetail_to_firing`] with
            /// `firing_index = 0`. Rho-net analogue of
            /// [`Self::rho_fold_dataflow_invocation_from_dovetail_to`].
            pub fn rho_net_invocation_from_dovetail_to(
                term: &dyn mettail_runtime::Term,
                report: &mettail_runtime::RuntimeDovetailRunReport,
                out_channel: impl ::core::convert::AsRef<str>,
            ) -> ::core::result::Result<
                ::mettail_rholang_codegen::RhoNetInjectionInvocation,
                ::std::string::String,
            > {
                Self::rho_net_invocation_from_dovetail_to_firing(term, report, out_channel, 0)
            }

            /// Build the FULL multi-firing σ-injection sequence from an already
            /// complete, shape-validated Dovetail report: one
            /// [`RhoNetInjectionInvocation`](mettail_rholang_codegen::RhoNetInjectionInvocation)
            /// per rewrite firing in `report.rewrite_justifications`, each on a
            /// distinct out channel `{out_channel_prefix}{i}`.
            ///
            /// The Stage 0 replay driver
            /// (`PlannedRhoBackend::run_rho_net_replay_and_observe_runtime_values`)
            /// fires each of these as its own atomic COMM against the installed
            /// σ-receiver program, so a multi-redex reduction replays every rewrite
            /// as a `c(ℓ)` COMM. An EMPTY result is a valid, non-error state: the
            /// term is already a normal form (no redex fired). If a firing exists
            /// but the language has no σ-receiver for its rule, this fails closed
            /// (via `rho_net_invocation_from_dovetail_to_firing`).
            pub fn rho_net_replay_invocation_from_dovetail_to(
                term: &dyn mettail_runtime::Term,
                report: &mettail_runtime::RuntimeDovetailRunReport,
                out_channel_prefix: impl ::core::convert::AsRef<str>,
            ) -> ::core::result::Result<
                ::std::vec::Vec<::mettail_rholang_codegen::RhoNetInjectionInvocation>,
                ::std::string::String,
            > {
                report.assert_complete().map_err(|status| {
                    ::std::format!(
                        "Rho-net replay for language {} requires a complete Dovetail report, got {}",
                        #language_lit, status,
                    )
                })?;
                let __prefix = out_channel_prefix.as_ref();
                let mut __invocations =
                    ::std::vec::Vec::with_capacity(report.rewrite_justifications.len());
                for __i in 0..report.rewrite_justifications.len() {
                    let __out = ::std::format!("{}{}", __prefix, __i);
                    __invocations.push(Self::rho_net_invocation_from_dovetail_to_firing(
                        term, report, __out, __i,
                    )?);
                }
                ::core::result::Result::Ok(__invocations)
            }

            /// The RhoNet planning artifact for this generated language — its
            /// planned channels, rule identities, RHS-template fingerprints, and
            /// semantic-predicate obligations
            /// ([`RhoNetProgram`](mettail_rholang_codegen::RhoNetProgram)).
            ///
            /// Derived from the generated `definition_source` exactly as the
            /// production installer does (`reconstruct_language_def` →
            /// `lower_language_def` → `RhoNetProgram::from_language_def`), so a
            /// caller reads a generated language's RhoNet metadata directly
            /// without hand-reconstructing its `LanguageDef` (item #2030).
            pub fn rho_net_program() -> ::core::result::Result<
                ::mettail_rholang_codegen::RhoNetProgram,
                ::std::string::String,
            > {
                let __source = <#language_struct as mettail_runtime::Language>::metadata(
                    &#language_struct,
                )
                .definition_source()
                .ok_or_else(|| ::std::format!(
                    "language {} has no definition source for its RhoNet program",
                    #language_lit,
                ))?;
                let __def = ::mettail_rholang_codegen::reconstruct_language_def(__source)
                    .map_err(|__err| ::std::format!(
                        "language {} definition source did not reconstruct: {}",
                        #language_lit, __err,
                    ))?;
                let __lowering = ::mettail_rholang_codegen::lower_language_def(&__def);
                ::core::result::Result::Ok(
                    ::mettail_rholang_codegen::RhoNetProgram::from_language_def(
                        &__def, &__lowering,
                    ),
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
    fn generated_mapper_uses_ast_constructors_and_checked_runtime_boundary() {
        let language = parse(
            r#"
                name: CalcRhoMapper,
                types {
                    Proc
                    ![i64] as Int
                    ![bool] as Bool
                    ![str] as Text
                }
                terms {
                    AddInt . a:Int, b:Int |- a "+" b : Int ;
                    EqText . a:Text, b:Text |- a "==" b : Bool ;
                }
            "#,
        );

        let tokens = generate_rho_scalar_invocation(&language).to_string();
        assert!(tokens.contains("rho_scalar_contract_invocation_to"));
        assert!(tokens.contains("RhoScalarContractInvocation :: new"));
        assert!(tokens.contains("CalcRhoMapperTermInner :: Int"));
        assert!(tokens.contains("Int :: AddInt"));
        assert!(tokens.contains("Bool :: EqText"));
        assert!(tokens.contains("RhoAstLiteral :: Int"));
        assert!(tokens.contains("RhoAstLiteral :: String"));
    }

    #[test]
    fn generated_mapper_rejects_structural_scalar_named_categories() {
        let language = parse(
            r#"
                name: StructuralScalarNames,
                types {
                    Int
                    Bool
                    Str
                }
                terms {
                    AddInt . a:Int, b:Int |- a "+" b : Int ;
                    EqStr . a:Str, b:Str |- a "==" b : Bool ;
                }
            "#,
        );

        let tokens = generate_rho_scalar_invocation(&language).to_string();
        assert!(tokens.contains("has no lowered Rho scalar contract invocation plan"));
        assert!(!tokens.contains("Int :: AddInt"));
        assert!(!tokens.contains("Str :: EqStr"));
    }

    #[test]
    fn generated_rho_net_invocation_emits_site_match_and_reflection() {
        let language = parse(
            r#"
                name: SwapNetGen,
                types { Proc }
                terms {
                    A . |- "A" : Proc ;
                    B . |- "B" : Proc ;
                    Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
                    Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
                }
                equations {}
                rewrites {
                    SwapStep . |- (Swap x y) ~> (Pair y x) ;
                }
            "#,
        );
        let tokens = generate_rho_net_invocation(&language).to_string();
        assert!(tokens.contains("rho_net_invocation_from_dovetail_to"));
        assert!(tokens.contains("RhoNetInjectionInvocation"));
        assert!(tokens.contains("term_contract_call"));
        assert!(tokens.contains("reflect_ground_term_par"));
        // The fired rule's bare label keys the σ-receiver channel + var-order lookup.
        assert!(tokens.contains("\"SwapStep\""));
        // The out-of-scope fallback fails closed (no silent no-op).
        assert!(tokens.contains("for fired rule"));
    }

    #[test]
    fn generated_rho_net_invocation_without_base_rewrites_fails_closed() {
        let language = parse(
            r#"
                name: ScalarNetGen,
                types {
                    ![i32] as Int
                }
                terms {
                    AddInt . a:Int, b:Int |- a "+" b : Int ;
                }
            "#,
        );
        let tokens = generate_rho_net_invocation(&language).to_string();
        assert!(tokens.contains("rho_net_invocation_from_dovetail_to"));
        assert!(tokens.contains("injection sites"));
        assert!(!tokens.contains("term_contract_call"));
    }

    /// The Swap→Pair fixture reused by the #2030/#2033 codegen-surface tests.
    fn swap_net_fixture() -> LanguageDef {
        parse(
            r#"
                name: SwapSurfaceGen,
                types { Proc }
                terms {
                    A . |- "A" : Proc ;
                    B . |- "B" : Proc ;
                    Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
                    Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
                }
                equations {}
                rewrites { SwapStep . |- (Swap x y) ~> (Pair y x) ; }
            "#,
        )
    }

    #[test]
    fn generated_rho_net_invocation_exposes_rho_net_program_accessor() {
        // #2030: every generated language exposes its RhoNet planning artifact
        // (planned channels, rule identities, RHS templates, semantic predicates)
        // directly via `rho_net_program()`, derived from the definition source.
        let tokens = generate_rho_net_invocation(&swap_net_fixture()).to_string();
        assert!(tokens.contains("fn rho_net_program"));
        assert!(tokens.contains("RhoNetProgram"));
        assert!(tokens.contains("from_language_def"));
        assert!(tokens.contains("reconstruct_language_def"));
    }

    #[test]
    fn generated_rho_codegen_surface_is_deterministic() {
        // #2033: regenerating the same language definition yields byte-identical
        // generated code (reproducible builds; guards against map-iteration or
        // other nondeterministic emission in the injection-site derivation).
        let language = swap_net_fixture();
        assert_eq!(
            generate_rho_net_invocation(&language).to_string(),
            generate_rho_net_invocation(&language).to_string(),
            "generated Rho-net invocation surface must be deterministic"
        );
        assert_eq!(
            generate_rho_scalar_invocation(&language).to_string(),
            generate_rho_scalar_invocation(&language).to_string(),
            "generated Rho scalar invocation surface must be deterministic"
        );
    }

    /// Whether a token stream USES `name` as a path/ident anywhere (recursing into
    /// groups). A doc comment that merely NAMES the crate in prose is a string
    /// literal, not an `Ident`, so it is correctly ignored — only real code use is
    /// flagged.
    fn token_stream_uses_ident(tokens: &proc_macro2::TokenStream, name: &str) -> bool {
        tokens.clone().into_iter().any(|tree| match tree {
            proc_macro2::TokenTree::Ident(ident) => ident == name,
            proc_macro2::TokenTree::Group(group) => token_stream_uses_ident(&group.stream(), name),
            _ => false,
        })
    }

    #[test]
    fn generated_rho_codegen_surface_takes_no_runtime_dependency() {
        // #2031/#2033: generated language code USES the codegen crate
        // (`mettail_rholang_codegen`) and the runtime-neutral `mettail_runtime`,
        // but NEVER the Rho runtime crate — so a generated language crate takes no
        // `mettail-rholang-runtime` dependency (Cargo enforces the boundary
        // structurally; this guards the generated-token level). Checks Ident USE,
        // not prose — the scalar helper's doc cross-reference to the runtime adapter
        // that consumes its output is legitimate and must not trip the gate.
        let language = swap_net_fixture();
        for tokens in [
            generate_rho_net_invocation(&language),
            generate_rho_scalar_invocation(&language),
        ] {
            assert!(
                !token_stream_uses_ident(&tokens, "mettail_rholang_runtime"),
                "generated code must not USE the Rho runtime crate as a path"
            );
        }
    }
}
