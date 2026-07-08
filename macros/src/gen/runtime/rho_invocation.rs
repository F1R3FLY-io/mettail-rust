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

use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
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

/// The per-category `Term → GroundTerm` reflection fn name (`__mettail_rho_net_reflect_<cat>`).
fn reflect_fn_name(category: &Ident) -> Ident {
    format_ident!("__mettail_rho_net_reflect_{}", to_snake(&category.to_string()))
}

/// Whether a constructor field is a PLAIN structural category subterm the M-reflect walk can
/// recurse into (`Box`/`Arc<Cat>`, `.as_ref()` → `&Cat`): a non-collection, non-optional,
/// non-predicate field whose category is a language non-terminal (not a builtin like `i32`).
/// Every other field (builtin / optional / predicate / collection) has no positional ground
/// image, so its host variant fails the reflection closed (routing that firing to σ-replay).
fn is_structural_category_field(field: &FieldInfo) -> bool {
    !field.is_collection
        && !field.is_optional
        && !field.is_predicate
        && !NonTerminalKind::classify(&field.category.to_string()).is_builtin()
}

/// Generate the per-category structural `Term → GroundTerm` reflection fn — the M-reflect
/// greenfield hinge. It mirrors the Dovetail report's `category_lowering` term walk
/// (`macros/src/gen/runtime/dovetail_report.rs`) but produces a codegen
/// [`GroundTerm`](mettail_rholang_codegen::GroundTerm) DIRECTLY from the runtime subject term
/// (NOT from the report's σ), tagging each node with its BARE constructor label — the exact
/// input `spread_term_par` / `reflect_tag` expect, so the reflected subject is coherent with the
/// automaton's compiled tags. It is TOTAL over the category's variants: a Nullary or an
/// all-structural Regular constructor reflects; a Var / Literal / Collection / Binder / an
/// Regular with a non-structural field fails CLOSED with a typed reason (the firing then falls
/// back to the σ-replay driver). The `k` reflection fns (one per category) are mutually
/// recursive nested fns, so cross-category structural fields resolve without a trait surface.
fn reflect_category_fn(language: &LanguageDef, category: &Ident) -> TokenStream {
    let fn_name = reflect_fn_name(category);
    let ground = quote!(::mettail_rholang_codegen::GroundTerm);
    let arms: Vec<TokenStream> = collect_category_variants(category, language)
        .into_iter()
        .map(|variant| match variant {
            VariantKind::Nullary { label } => {
                let label_lit = lit(&label.to_string());
                quote! {
                    #category::#label => ::core::result::Result::Ok(
                        #ground::new(#label_lit, ::std::vec::Vec::new())
                    )
                }
            },
            VariantKind::Regular { label, fields } if fields.iter().all(is_structural_category_field) => {
                let label_lit = lit(&label.to_string());
                let field_vars: Vec<Ident> =
                    (0..fields.len()).map(|i| format_ident!("__field_{i}")).collect();
                let child_calls: Vec<TokenStream> = fields
                    .iter()
                    .zip(field_vars.iter())
                    .map(|(field, var)| {
                        let child_fn = reflect_fn_name(&field.category);
                        quote! { #child_fn(#var.as_ref())? }
                    })
                    .collect();
                quote! {
                    #category::#label(#(#field_vars),*) => ::core::result::Result::Ok(
                        #ground::new(#label_lit, ::std::vec![#(#child_calls),*])
                    )
                }
            },
            VariantKind::Regular { label, .. } => {
                let msg = lit(&format!(
                    "in-Rho match reflection: constructor {label} has a non-structural field with no positional ground image"
                ));
                quote! {
                    #category::#label(..) =>
                        ::core::result::Result::Err(::std::string::String::from(#msg))
                }
            },
            VariantKind::Var { label } | VariantKind::Literal { label } => {
                let msg = lit(&format!(
                    "in-Rho match reflection: {label} is a variable/literal leaf with no structural ground image"
                ));
                quote! {
                    #category::#label(..) =>
                        ::core::result::Result::Err(::std::string::String::from(#msg))
                }
            },
            VariantKind::Collection { label, .. } => {
                let msg = lit(&format!(
                    "in-Rho match reflection: {label} is an AC/collection node (matched via the AC path, not the base automaton)"
                ));
                quote! {
                    #category::#label(..) =>
                        ::core::result::Result::Err(::std::string::String::from(#msg))
                }
            },
            VariantKind::Binder { label, .. } | VariantKind::MultiBinder { label, .. } => {
                let msg = lit(&format!(
                    "in-Rho match reflection: {label} is a binder node with no positional ground image"
                ));
                quote! {
                    #category::#label(..) =>
                        ::core::result::Result::Err(::std::string::String::from(#msg))
                }
            },
        })
        .collect();
    quote! {
        fn #fn_name(
            __term: &#category,
        ) -> ::core::result::Result<#ground, ::std::string::String> {
            match __term {
                #(#arms),*
            }
        }
    }
}

/// The M-reflect subject binding for `match_body`: the `k` per-category reflection fns plus the
/// `let __subject = …;` that reflects the runtime subject term `typed_term.0` into a
/// `GroundTerm` — WITHOUT reading `report.rewrite_justifications` (no host σ). For a
/// single-category language `typed_term.0` IS the primary category; for a multi-category one it
/// is the `…TermInner` cross-category enum, whose first structurally-reflectable alternative is
/// taken (fail-closed otherwise). The subject is then spread and LOCATED by the automaton.
fn reflect_subject_binding(language: &LanguageDef) -> TokenStream {
    let name = &language.name;
    let language_lit = lit(&name.to_string());
    let term_name = format_ident!("{}Term", name);
    let reflect_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| reflect_category_fn(language, &ty.name))
        .collect();
    let primary = language
        .types
        .first()
        .map(|ty| ty.name.clone())
        .expect("a language declares at least one category");

    let subject_expr = if language.types.len() > 1 {
        let inner_enum = format_ident!("{}TermInner", name);
        let arms: Vec<TokenStream> = language
            .types
            .iter()
            .map(|ty| {
                let cat = &ty.name;
                let reflect = reflect_fn_name(cat);
                quote! { #inner_enum::#cat(__value) => #reflect(__value), }
            })
            .collect();
        quote! {
            let __subject = {
                let mut __reflected: ::core::result::Result<
                    ::mettail_rholang_codegen::GroundTerm,
                    ::std::string::String,
                > = ::core::result::Result::Err(::std::format!(
                    "in-Rho match for language {} has no structurally reflectable subject alternative",
                    #language_lit,
                ));
                for __alt in __typed_term.0.all_alts() {
                    __reflected = match __alt {
                        #(#arms)*
                        #inner_enum::Ambiguous(_) => ::core::result::Result::Err(
                            ::std::string::String::from(
                                "in-Rho match reflection: an Ambiguous subject alternative has no ground image",
                            ),
                        ),
                    };
                    if __reflected.is_ok() {
                        break;
                    }
                }
                __reflected?
            };
        }
    } else {
        let reflect_primary = reflect_fn_name(&primary);
        quote! {
            let __subject = #reflect_primary(&__typed_term.0)?;
        }
    };

    quote! {
        #(#reflect_fns)*

        let __typed_term = term
            .as_any()
            .downcast_ref::<#term_name>()
            .ok_or_else(|| {
                ::std::format!(
                    "in-Rho match for language {} could not reflect the subject: expected {}Term, got {:?}",
                    #language_lit, #language_lit, term,
                )
            })?;
        #subject_expr
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
    // Stage AC-U3: the AC firing sites — an un-skipped linear with-rest HashBag AC rewrite
    // (`RhoNetLoweredRule::AcRewrite`) fires by reconstructing the WHOLE operand bag from σ and
    // sending its process-soup carrier on the AC trace channel (the installed AC receiver re-does
    // the order-independent match), rather than the flat base-rewrite σ-tuple.
    let ac_sites = mettail_rholang_codegen::rho_net_ac_injection_sites(language);
    // Stage 3c: the binder/β-substitution firing sites — a substitution rewrite
    // (`RhoNetLoweredRule::SubstRewrite`) fires by reflecting the firing's CONTRACTUM (the
    // host-computed reduct `RHS[σ]`) at the scope variable's σ slot and the raw σ at every
    // other LHS slot, then sending the σ tuple on the receiver channel (the installed
    // SubstRewrite σ-receiver forwards the scope slot on `@out`).
    let subst_sites = mettail_rholang_codegen::rho_net_subst_injection_sites(language);
    // Stage 3e: the native-system-process firing sites — a `fold` native process
    // (`RhoNetLoweredRule::NativeSystemProcessRewrite`) fires by reflecting the firing's CONTRACTUM
    // (the WHOLE native value the host's trusted handler computed — there is no structural RHS)
    // and sending it on the dispatch channel (the installed NativeSystemProcessRewrite receiver
    // forwards that single slot on `@out`).
    let native_sites = mettail_rholang_codegen::rho_net_native_injection_sites(language);
    // Stage 3f: the native-SCALAR-FOLD firing sites — a `fold` native scalar arithmetic
    // (`RhoNetLoweredRule::NativeFold`, e.g. `AddInt`) fires by reflecting the firing's CONTRACTUM
    // (the WHOLE reduced value the host computed via its trusted `fold` handler — there is no
    // structural RHS) and sending it on the dispatch channel (the installed `NativeFold` receiver
    // forwards that single slot on `@out`). The scalar-fold analogue of the Stage 3e native arm —
    // the SAME contractum lane.
    let native_fold_sites = mettail_rholang_codegen::rho_net_native_fold_injection_sites(language);
    // Stage 3b / A-4: the COMM firing sites — a canonical single-receive Rholang communication
    // rewrite (`RhoNetLoweredRule::CommRewrite`) fires by reconstructing the WHOLE operand bag from
    // σ (its structured elements ⊎ the `rest` children) and passing the host-computed reduct
    // `cont[Q/y]` — recovered from the firing's CONTRACTUM (the communicated bag) minus `rest` — to
    // `comm_contract_call`, which sends `channel!(⟦bag⟧, ⟦reduct⟧, @out)`. This is the AUTOMATED
    // drive that removes the hand-built-σ `comm_contract_call` deviation.
    let comm_sites = mettail_rholang_codegen::rho_net_comm_injection_sites(language);
    // Stage 3d: the STRUCTURAL-AC firing sites — a structural non-linear AC rewrite (Ambient
    // `OpenRule`, `RhoNetLoweredRule::StructuralAcRewrite`) fires by reconstructing the WHOLE operand
    // bag from σ (its structured elements ⊎ the `rest` children) and recovering each STRUCTURAL reduct
    // element `r_j` DIRECTLY from σ (an LHS-element arg — no host-computed contractum), then passing
    // them to `structural_ac_contract_call`, which sends `channel!(⟦bag⟧, ⟦r0⟧, …, @out)`.
    let structural_ac_sites =
        mettail_rholang_codegen::rho_net_structural_ac_injection_sites(language);

    let body = if sites.is_empty()
        && ac_sites.is_empty()
        && subst_sites.is_empty()
        && native_sites.is_empty()
        && native_fold_sites.is_empty()
        && comm_sites.is_empty()
        && structural_ac_sites.is_empty()
    {
        // No σ-receiver (base OR AC OR subst OR native): the helper exists for a uniform surface
        // but always fails closed (there is nothing to inject).
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
        // Base-rewrite arms: reflect the flat σ tuple (first-occurrence LHS order) and send it on
        // the trace channel — the existing byte-identical path, now one dispatch arm.
        let base_site_arms: Vec<TokenStream> = sites
            .iter()
            .map(|site| {
                let label = lit(&site.rule_label);
                let channel = lit(&site.channel);
                let vars: Vec<LitStr> = site.lhs_var_order.iter().map(|var| lit(var)).collect();
                quote! {
                    #label => {
                        // Reorder the report's (name-sorted) σ into the σ-receiver's
                        // first-occurrence LHS variable order and reflect each sub-term.
                        let __var_order: &[&str] = &[#(#vars),*][..];
                        let mut __args = ::std::vec::Vec::with_capacity(__var_order.len());
                        for __var in __var_order {
                            let __subterm = __mettail_rho_net_find_sigma(__justification, __var)?;
                            __args.push(::mettail_rholang_codegen::reflect_ground_term_par(
                                &__mettail_rho_net_to_ground(__subterm),
                                __fingerprint,
                            ));
                        }
                        ::mettail_rholang_codegen::term_contract_call(#channel, __args, out_channel)
                    },
                }
            })
            .collect();

        // AC-rewrite arms: reconstruct the WHOLE operand bag from σ — the k matched element
        // sub-terms (`element_var_order`) followed by the CHILDREN of the `rest` sub-term (the
        // canonical `op` node over the multiset complement, whose `children` are the residual bag
        // elements) — and send its reflected process-soup carrier on the AC trace channel.
        let ac_site_arms: Vec<TokenStream> = ac_sites
            .iter()
            .map(|site| {
                let label = lit(&site.rule_label);
                let channel = lit(&site.channel);
                let op = lit(&site.op);
                let element_vars: Vec<LitStr> =
                    site.element_var_order.iter().map(|var| lit(var)).collect();
                let element_count = site.element_var_order.len();
                let rest_var = lit(&site.rest_var);
                quote! {
                    #label => {
                        // The k matched element σ sub-terms (first-occurrence order), plus the
                        // residual `rest.children` spliced in below.
                        let mut __elements = ::std::vec::Vec::with_capacity(#element_count);
                        #(
                            __elements.push(__mettail_rho_net_to_ground(
                                __mettail_rho_net_find_sigma(__justification, #element_vars)?,
                            ));
                        )*
                        // `rest` binds to the canonical bag over the multiset complement: its
                        // `{ constructor: op, children: [complement…] }` sub-term reconstructs to a
                        // positional ground term whose CHILDREN are the residual elements. Splice
                        // them so `whole_bag = elements ⊎ rest.children` is the full operand bag.
                        let __rest = __mettail_rho_net_to_ground(
                            __mettail_rho_net_find_sigma(__justification, #rest_var)?,
                        );
                        __elements.extend(__rest.children.iter().cloned());
                        let __whole_bag = ::mettail_rholang_codegen::GroundTerm::collection(
                            ::mettail_rholang_codegen::CollectionType::HashBag,
                            #op,
                            __elements,
                        );
                        ::mettail_rholang_codegen::ac_contract_call(
                            #channel, &__whole_bag, __fingerprint, out_channel,
                        )
                    },
                }
            })
            .collect();

        // Subst-rewrite arms (Stage 3c): reflect the firing's CONTRACTUM (the host-computed
        // reduct) at the scope variable's slot, and the raw σ at every other LHS slot, then send
        // the σ tuple on the receiver channel via `term_contract_call` (the same flat send the
        // base arm uses — the SubstRewrite receiver is a plain σ-receiver that forwards the scope
        // slot). The host does the matching AND the capture-avoiding substitution (model-b); the
        // reduced term reflects to that ground σ slot.
        let subst_site_arms: Vec<TokenStream> = subst_sites
            .iter()
            .map(|site| {
                let label = lit(&site.rule_label);
                let channel = lit(&site.channel);
                let vars: Vec<LitStr> = site.lhs_var_order.iter().map(|var| lit(var)).collect();
                let scope_var = lit(&site.scope_var);
                quote! {
                    #label => {
                        // The reduced term the host produced (`RHS[σ]` after capture-avoiding
                        // substitution) is the firing's contractum; it fills the scope slot.
                        let __contractum = __justification.contractum.as_ref().ok_or_else(|| {
                            ::std::format!(
                                "Rho-net subst injection for language {} has no contractum for fired rule {}",
                                #language_lit, #label,
                            )
                        })?;
                        let __var_order: &[&str] = &[#(#vars),*][..];
                        let mut __args = ::std::vec::Vec::with_capacity(__var_order.len());
                        for __var in __var_order {
                            // The scope slot carries the host-computed reduct; every other LHS
                            // slot carries its raw matched sub-term (bound by the receiver but
                            // not emitted — the body forwards only the scope slot).
                            let __ground = if *__var == #scope_var {
                                __mettail_rho_net_to_ground(__contractum)
                            } else {
                                __mettail_rho_net_to_ground(
                                    __mettail_rho_net_find_sigma(__justification, __var)?,
                                )
                            };
                            __args.push(::mettail_rholang_codegen::reflect_ground_term_par(
                                &__ground, __fingerprint,
                            ));
                        }
                        ::mettail_rholang_codegen::term_contract_call(#channel, __args, out_channel)
                    },
                }
            })
            .collect();

        // Native-system-process arms (Stage 3e): a `fold` native process has NO structural RHS —
        // the WHOLE reduct is the host's trusted-handler value, carried as the firing's contractum.
        // Reflect that contractum and send it (as the single dispatch argument) on the dispatch
        // channel via `term_contract_call`; the installed `NativeSystemProcessRewrite` receiver is
        // the flat one-slot receiver `for (result, out <- c) { out!(result) }` that forwards it on
        // `@out`. The host matched AND computed the native value (model-b) via its `![…] fold` HOL
        // body; only the payload is delegated — the encoder reflects it, never fabricates it.
        let native_site_arms: Vec<TokenStream> = native_sites
            .iter()
            .map(|site| {
                let label = lit(&site.rule_label);
                let channel = lit(&site.channel);
                quote! {
                    #label => {
                        let __contractum = __justification.contractum.as_ref().ok_or_else(|| {
                            ::std::format!(
                                "Rho-net native injection for language {} has no contractum for fired rule {}",
                                #language_lit, #label,
                            )
                        })?;
                        let __arg = ::mettail_rholang_codegen::reflect_ground_term_par(
                            &__mettail_rho_net_to_ground(__contractum), __fingerprint,
                        );
                        ::mettail_rholang_codegen::term_contract_call(
                            #channel, ::std::vec![__arg], out_channel,
                        )
                    },
                }
            })
            .collect();

        // Native-scalar-fold arms (Stage 3f): a `fold` native scalar arithmetic (`AddInt`) has NO
        // structural RHS — the WHOLE reduct is the host's trusted-handler value `a op b`, carried as
        // the firing's contractum. IDENTICAL to the Stage 3e native (system-process) arm: reflect
        // that contractum and send it (as the single dispatch argument) on the dispatch channel via
        // `term_contract_call`; the installed `NativeFold` receiver is the flat one-slot receiver
        // `for (result, out <- c) { out!(result) }` that forwards it on `@out`. By D3 a computing
        // fold is directed motion, so it fires as a COMM (a lossless cast would be congruence).
        let native_fold_site_arms: Vec<TokenStream> = native_fold_sites
            .iter()
            .map(|site| {
                let label = lit(&site.rule_label);
                let channel = lit(&site.channel);
                quote! {
                    #label => {
                        let __contractum = __justification.contractum.as_ref().ok_or_else(|| {
                            ::std::format!(
                                "Rho-net native-fold injection for language {} has no contractum for fired rule {}",
                                #language_lit, #label,
                            )
                        })?;
                        let __arg = ::mettail_rholang_codegen::reflect_ground_term_par(
                            &__mettail_rho_net_to_ground(__contractum), __fingerprint,
                        );
                        ::mettail_rholang_codegen::term_contract_call(
                            #channel, ::std::vec![__arg], out_channel,
                        )
                    },
                }
            })
            .collect();

        // Comm-rewrite arms (Stage 3b / A-4): COMPOSE the AC-site whole-bag reconstruction with the
        // subst-site contractum read. Reconstruct the operand bag from σ — each structured element
        // `C(σ[a_0], …)` (from `element_constructors` ∥ `element_arg_vars`) followed by the `rest`
        // sub-term's children — and pass the host-computed reduct `cont[Q/y]` (recovered from the
        // firing's CONTRACTUM, the communicated bag, minus the residual `rest`) to
        // `comm_contract_call`, which sends `channel!(⟦bag⟧, ⟦reduct⟧, @out)` for the installed Comm
        // receiver (which re-does the non-linear AC match `N ≡ N` and splices `reduct | rest`).
        let comm_site_arms: Vec<TokenStream> = comm_sites
            .iter()
            .map(|site| {
                let label = lit(&site.rule_label);
                let channel = lit(&site.channel);
                let op = lit(&site.op);
                let rest_var = lit(&site.rest_var);
                let element_count = site.element_constructors.len();
                let element_builds: Vec<TokenStream> = site
                    .element_constructors
                    .iter()
                    .zip(site.element_arg_vars.iter())
                    .map(|(constructor, arg_vars)| {
                        let ctor = lit(constructor);
                        let arg_lits: Vec<LitStr> = arg_vars.iter().map(|arg| lit(arg)).collect();
                        let arg_count = arg_vars.len();
                        quote! {
                            {
                                let mut __elem_children =
                                    ::std::vec::Vec::with_capacity(#arg_count);
                                #(
                                    __elem_children.push(__mettail_rho_net_to_ground(
                                        __mettail_rho_net_find_sigma(__justification, #arg_lits)?,
                                    ));
                                )*
                                ::mettail_rholang_codegen::GroundTerm::new(#ctor, __elem_children)
                            }
                        }
                    })
                    .collect();
                quote! {
                    #label => {
                        // Reconstruct the operand bag: the k structured elements ⊎ the residual bag.
                        let mut __elements = ::std::vec::Vec::with_capacity(#element_count);
                        #( __elements.push(#element_builds); )*
                        let __rest = __mettail_rho_net_to_ground(
                            __mettail_rho_net_find_sigma(__justification, #rest_var)?,
                        );
                        __elements.extend(__rest.children.iter().cloned());
                        let __whole_bag = ::mettail_rholang_codegen::GroundTerm::collection(
                            ::mettail_rholang_codegen::CollectionType::HashBag,
                            #op,
                            __elements,
                        );
                        // The reduct `cont[Q/y]` = the communicated bag (the firing's CONTRACTUM)
                        // minus the residual `rest` (multiset difference — exactly one element left).
                        let __contractum = __justification.contractum.as_ref().ok_or_else(|| {
                            ::std::format!(
                                "Rho-net Comm injection for language {} has no contractum for fired rule {}",
                                #language_lit, #label,
                            )
                        })?;
                        let __reduct = __mettail_rho_net_comm_reduct(
                            &__mettail_rho_net_to_ground(__contractum),
                            &__rest.children,
                        )
                        .ok_or_else(|| {
                            ::std::format!(
                                "Rho-net Comm injection for language {} could not recover the reduct for fired rule {}",
                                #language_lit, #label,
                            )
                        })?;
                        ::mettail_rholang_codegen::comm_contract_call(
                            #channel, &__whole_bag, &__reduct, __fingerprint, out_channel,
                        )
                    },
                }
            })
            .collect();

        // Structural-AC-rewrite arms (Stage 3d): reconstruct the operand bag from σ EXACTLY like the
        // Comm arm (each structured element `C(σ[a_0], …)` from `element_constructors` ∥
        // `element_arg_vars`, ⊎ the `rest` sub-term's children), then recover each STRUCTURAL reduct
        // element `r_j` DIRECTLY from σ (each `reduct_var` is a bare LHS-element arg the AC match
        // bound — no contractum, no substitution), and pass them to `structural_ac_contract_call`,
        // which sends `channel!(⟦bag⟧, ⟦r0⟧, …, ⟦r_{m-1}⟧, @out)` for the installed structural-AC
        // receiver (which re-does the non-linear AC match `N ≡ N` and splices `r0 | … | rest`).
        let structural_ac_site_arms: Vec<TokenStream> = structural_ac_sites
            .iter()
            .map(|site| {
                let label = lit(&site.rule_label);
                let channel = lit(&site.channel);
                let op = lit(&site.op);
                let rest_var = lit(&site.rest_var);
                let element_count = site.element_constructors.len();
                let element_builds: Vec<TokenStream> = site
                    .element_constructors
                    .iter()
                    .zip(site.element_arg_vars.iter())
                    .map(|(constructor, arg_vars)| {
                        let ctor = lit(constructor);
                        let arg_lits: Vec<LitStr> = arg_vars.iter().map(|arg| lit(arg)).collect();
                        let arg_count = arg_vars.len();
                        quote! {
                            {
                                let mut __elem_children =
                                    ::std::vec::Vec::with_capacity(#arg_count);
                                #(
                                    __elem_children.push(__mettail_rho_net_to_ground(
                                        __mettail_rho_net_find_sigma(__justification, #arg_lits)?,
                                    ));
                                )*
                                ::mettail_rholang_codegen::GroundTerm::new(#ctor, __elem_children)
                            }
                        }
                    })
                    .collect();
                let reduct_lits: Vec<LitStr> =
                    site.reduct_vars.iter().map(|var| lit(var)).collect();
                let reduct_count = site.reduct_vars.len();
                quote! {
                    #label => {
                        // Reconstruct the operand bag: the k structured elements ⊎ the residual bag.
                        let mut __elements = ::std::vec::Vec::with_capacity(#element_count);
                        #( __elements.push(#element_builds); )*
                        let __rest = __mettail_rho_net_to_ground(
                            __mettail_rho_net_find_sigma(__justification, #rest_var)?,
                        );
                        __elements.extend(__rest.children.iter().cloned());
                        let __whole_bag = ::mettail_rholang_codegen::GroundTerm::collection(
                            ::mettail_rholang_codegen::CollectionType::HashBag,
                            #op,
                            __elements,
                        );
                        // The m STRUCTURAL reduct elements — recovered DIRECTLY from σ (each an
                        // LHS-element arg the AC match bound). No contractum: the reduct is a pure
                        // rearrangement, so σ already carries every element.
                        let mut __reducts = ::std::vec::Vec::with_capacity(#reduct_count);
                        #(
                            __reducts.push(__mettail_rho_net_to_ground(
                                __mettail_rho_net_find_sigma(__justification, #reduct_lits)?,
                            ));
                        )*
                        ::mettail_rholang_codegen::structural_ac_contract_call(
                            #channel, &__whole_bag, &__reducts, __fingerprint, out_channel,
                        )
                    },
                }
            })
            .collect();

        // The multiset-difference reduct recovery, emitted only for a language with a Comm site (so
        // a non-Comm language surfaces no dead helper).
        let comm_reduct_helper: TokenStream = if comm_sites.is_empty() {
            quote! {}
        } else {
            quote! {
                // The firing's CONTRACTUM is the communicated bag `op{ cont[Q/y], ...rest }`. Remove
                // ONE occurrence of each residual `rest` child (multiset difference); the single
                // remaining element is the reduct `cont[Q/y]` the Comm receiver splices back with
                // `rest`. `None` when the shape is unexpected (fail-closed).
                fn __mettail_rho_net_comm_reduct(
                    __contractum: &::mettail_rholang_codegen::GroundTerm,
                    __rest_children: &[::mettail_rholang_codegen::GroundTerm],
                ) -> ::core::option::Option<::mettail_rholang_codegen::GroundTerm> {
                    let mut __remaining: ::std::vec::Vec<::mettail_rholang_codegen::GroundTerm> =
                        __contractum.children.clone();
                    for __r in __rest_children {
                        if let ::core::option::Option::Some(__pos) =
                            __remaining.iter().position(|__c| __c == __r)
                        {
                            __remaining.remove(__pos);
                        }
                    }
                    match __remaining.as_slice() {
                        [__reduct] => ::core::option::Option::Some(__reduct.clone()),
                        _ => ::core::option::Option::None,
                    }
                }
            }
        };

        quote! {
            report.assert_complete().map_err(|status| {
                ::std::format!(
                    "Rho-net injection for language {} requires a complete Dovetail report, got {}",
                    #language_lit, status,
                )
            })?;
            let _ = term;
            let out_channel = out_channel.as_ref();

            #comm_reduct_helper

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

            // Look up a σ binding by LHS variable name (the report's σ is name-sorted, not in LHS
            // order). Shared by the base and AC arms so the two σ reorderings are one routine.
            fn __mettail_rho_net_find_sigma<'a>(
                __justification: &'a mettail_runtime::RuntimeRewriteJustification,
                __name: &str,
            ) -> ::core::result::Result<
                &'a mettail_runtime::RuntimeReflectedSubterm,
                ::std::string::String,
            > {
                __justification
                    .sigma
                    .iter()
                    .find(|(__n, _)| __n.as_str() == __name)
                    .map(|(_, __subterm)| __subterm)
                    .ok_or_else(|| {
                        ::std::format!(
                            "Rho-net injection for language {} is missing σ binding for LHS variable {}",
                            #language_lit, __name,
                        )
                    })
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

            // Dispatch the fired rule to its σ-receiver family: base rewrites send a flat σ tuple
            // (`term_contract_call`); un-skipped HashBag AC rewrites send the whole-bag carrier
            // (`ac_contract_call`). Both assemble the SAME `RhoNetInjectionInvocation` — one atomic
            // `c(ℓ)` COMM the runtime runs against the installed σ-receiver program.
            let __call = match __justification.rule_label.as_str() {
                #(#base_site_arms)*
                #(#ac_site_arms)*
                #(#subst_site_arms)*
                #(#native_site_arms)*
                #(#native_fold_site_arms)*
                #(#comm_site_arms)*
                #(#structural_ac_site_arms)*
                __other => {
                    return ::core::result::Result::Err(::std::format!(
                        "Rho-net injection for language {} has no σ-receiver for fired rule {}",
                        #language_lit, __other,
                    ));
                },
            };
            ::core::result::Result::Ok(::mettail_rholang_codegen::RhoNetInjectionInvocation {
                call: __call,
                out_channel: out_channel.to_string(),
            })
        }
    };

    // Stage 3 piece 5: the in-Rho MATCH body. Unlike `#body` (host-computes σ and injects
    // it), this compiles the language's in-Rho matching ruleset, GATES on it, rebuilds the
    // ground subject `LHS[σ]`, and assembles the `network ‖ spread` call so the automaton
    // re-does the MATCHING on the interpreter and fires the σ-receiver.
    // M-reflect (Stage 4): the per-category `Term → GroundTerm` reflection fns + the
    // `let __subject = …;` that structurally reflects the runtime subject term — the greenfield
    // hinge that retires the report-σ redex reconstruction from the MATCH path.
    let reflect_subject = reflect_subject_binding(language);
    let match_body = quote! {
        report.assert_complete().map_err(|status| {
            ::std::format!(
                "in-Rho match for language {} requires a complete Dovetail report, got {}",
                #language_lit, status,
            )
        })?;
        // M-reflect (Stage 4): the subject is the WHOLE input `term`, reflected STRUCTURALLY to a
        // `GroundTerm` (`__subject`) — NOT rebuilt from `report.rewrite_justifications` σ. The
        // `sa:` automaton then LOCATES the redex in the spread and EMITS σ, so the host Dovetail
        // no longer computes σ (nor locates the redex) for the MATCH path; the report survives
        // only to GATE (which rules fired) and to drive the σ-replay FALLBACK.
        let out_channel = out_channel.as_ref();
        #reflect_subject

        // Reconstruct the def exactly as `rho_net_program()` does, so the ruleset's
        // fingerprint + accept channels are the ones the installed σ-receivers were
        // compiled with (one def, one fingerprint, no separate metadata read → no drift).
        let __source = <#language_struct as mettail_runtime::Language>::metadata(
            &#language_struct,
        )
        .definition_source()
        .ok_or_else(|| {
            ::std::format!(
                "language {} has no definition source for in-Rho matching",
                #language_lit,
            )
        })?;
        let __def = ::mettail_rholang_codegen::reconstruct_language_def(__source).map_err(|__err| {
            ::std::format!(
                "language {} definition source did not reconstruct for in-Rho matching: {}",
                #language_lit, __err,
            )
        })?;

        let __ruleset = ::mettail_rholang_codegen::compile_in_rho_matching_ruleset(&__def);

        // Capability gate (FV ix `install_admits`): fail closed BEFORE any Rho reduction
        // if any FIRED rule is skipped from in-Rho matching.
        let __fired: ::std::vec::Vec<&str> = report
            .rewrite_justifications
            .iter()
            .map(|__justification| __justification.rule_label.as_str())
            .collect();
        if let ::core::option::Option::Some(__skipped) =
            ::mettail_rholang_codegen::in_rho_match_gate_reject(&__ruleset.deferred, &__fired)
        {
            return ::core::result::Result::Err(::std::format!(
                "in-Rho match gate for language {} rejects: fired rule {} is not matchable in Rho ({:?})",
                #language_lit, __skipped.rule_label, __skipped.reason,
            ));
        }

        // Stage 3 scope: exactly one root-rooted redex (0 = normal form, >1 = Stage-4
        // multi-redex — both fail closed so the repl falls back to the σ-replay driver).
        let __justification = match report.rewrite_justifications.as_slice() {
            [__only] => __only,
            __other => {
                return ::core::result::Result::Err(::std::format!(
                    "in-Rho match for language {} handles a single root-rooted redex (Stage 3); the report fired {} rules",
                    #language_lit, __other.len(),
                ));
            },
        };

        // Root-rooted scope: the automaton LOCATES the redex at the spread ROOT, so the whole
        // reflected subject must BE the redex — its root constructor equals the fired rule's LHS
        // root constructor. A NESTED redex (subject root ≠ rule root; the whole term is a context
        // AROUND the redex) is not locatable by the root Match, so it fails closed to the
        // σ-replay driver, which openly uses σ to locate + inject nested redexes.
        let __lhs_root = ::mettail_rholang_codegen::rule_lhs_root_constructor(
            &__def,
            &__justification.rule_label,
        )?;
        if __subject.constructor != __lhs_root {
            return ::core::result::Result::Err(::std::format!(
                "in-Rho match for language {}: the fired redex is not root-rooted (subject root `{}` \u{2260} rule `{}` LHS root `{}`); the \u{3c3}-replay driver handles nested redexes",
                #language_lit, __subject.constructor, __justification.rule_label, __lhs_root,
            ));
        }

        // Assemble the in-Rho match call (network ‖ spread) — the SAME driver target as
        // the σ-injection path (`RhoNetInjectionInvocation`).
        let __call = ::mettail_rholang_codegen::in_rho_match_call_par(
            &__ruleset,
            &__subject,
            "site0",
            out_channel,
        )
        .map_err(|__err| {
            ::std::format!(
                "in-Rho match for language {} could not serialize the match call: {:?}",
                #language_lit, __err,
            )
        })?;

        ::core::result::Result::Ok(::mettail_rholang_codegen::RhoNetInjectionInvocation {
            call: __call,
            out_channel: out_channel.to_string(),
        })
    };

    // Stage 3a: the CONTEXTUAL injection body — the third arm of the σ-injection F-function
    // family (base | AC | contextual). Unlike the base/AC arms (keyed on the fired rule's
    // OWN σ-receiver), a congruence rule fires no explicit Dovetail rule (the e-graph
    // congruence closure closes the context implicitly), so its atomic JOIN is driven by the
    // PREMISE firing: reconstruct the reduced hole `T = RHS_premise[σ]` and deliver it on the
    // join's premise channel, where the installed `contextual_join_receiver_par` binds it and
    // emits `⟦K'⟧` on `@out`. Stage 3a scope = a single UNARY congruence rule closed by a
    // single root-rooted premise firing; 0/≥2 congruence rules, a non-unary context, or a
    // multi-redex report fail closed (a later multi-premise stage).
    let contextual_body = quote! {
        report.assert_complete().map_err(|status| {
            ::std::format!(
                "contextual injection for language {} requires a complete Dovetail report, got {}",
                #language_lit, status,
            )
        })?;
        let _ = term;
        let out_channel = out_channel.as_ref();

        // Reconstruct the def exactly as `rho_net_program()` does, so the contextual join's
        // premise channels + fingerprint are the ones the installed join was compiled with
        // (one def, one fingerprint, no separate metadata read → no drift).
        let __source = <#language_struct as mettail_runtime::Language>::metadata(
            &#language_struct,
        )
        .definition_source()
        .ok_or_else(|| {
            ::std::format!(
                "language {} has no definition source for contextual injection",
                #language_lit,
            )
        })?;
        let __def = ::mettail_rholang_codegen::reconstruct_language_def(__source).map_err(|__err| {
            ::std::format!(
                "language {} definition source did not reconstruct for contextual injection: {}",
                #language_lit, __err,
            )
        })?;

        // Stage 3a scope: exactly ONE congruence rule (one context to close). 0 (no join) or
        // ≥2 (multi-congruence) fail closed.
        let __sites = ::mettail_rholang_codegen::rho_net_contextual_injection_sites(&__def);
        let __site = match __sites.as_slice() {
            [__only] => __only,
            __other => {
                return ::core::result::Result::Err(::std::format!(
                    "contextual injection for language {} handles a single congruence rule (Stage 3a); found {}",
                    #language_lit, __other.len(),
                ));
            },
        };
        // Stage 3a scope: a UNARY context (one premise hole). A wider n-ary join is a later
        // multi-premise stage.
        let __premise_channel = match __site.premise_channels.as_slice() {
            [__only] => __only,
            __other => {
                return ::core::result::Result::Err(::std::format!(
                    "contextual injection for language {} handles a unary congruence (one premise); rule {} has {} premises",
                    #language_lit, __site.rule_label, __other.len(),
                ));
            },
        };

        // The premise firing whose contractum fills the hole. Stage 3a scope: exactly one
        // root-rooted premise firing (0 = normal form, ≥2 = multi-redex — both fail closed).
        let __justification = match report.rewrite_justifications.as_slice() {
            [__only] => __only,
            __other => {
                return ::core::result::Result::Err(::std::format!(
                    "contextual injection for language {} handles a single premise firing (Stage 3a); the report fired {} rules",
                    #language_lit, __other.len(),
                ));
            },
        };

        // Rebuild the premise firing's σ, then reconstruct the reduced hole
        // `T = RHS_premise[σ]` — the contractum the join plugs into its context `K'`.
        fn __mettail_rho_net_to_ground(
            subterm: &mettail_runtime::RuntimeReflectedSubterm,
        ) -> ::mettail_rholang_codegen::GroundTerm {
            ::mettail_rholang_codegen::GroundTerm::new(
                subterm.constructor.clone(),
                subterm.children.iter().map(__mettail_rho_net_to_ground).collect(),
            )
        }
        let __sigma: ::std::vec::Vec<(
            ::std::string::String,
            ::mettail_rholang_codegen::GroundTerm,
        )> = __justification
            .sigma
            .iter()
            .map(|(__name, __subterm)| (__name.clone(), __mettail_rho_net_to_ground(__subterm)))
            .collect();
        let __hole = ::mettail_rholang_codegen::reconstruct_contractum(
            &__def,
            &__justification.rule_label,
            &__sigma,
        )?;

        // Reflect the reduced hole with the SAME fingerprint the installed join reflects its
        // context constructors with (the install boundary requires
        // `metadata().definition_fingerprint() == plan.definition_fingerprint()`).
        let __fingerprint = <#language_struct as mettail_runtime::Language>::metadata(
            &#language_struct,
        )
        .definition_fingerprint()
        .ok_or_else(|| {
            ::std::format!(
                "language {} has no definition fingerprint for contextual σ reflection",
                #language_lit,
            )
        })?;
        let __reflected_hole =
            ::mettail_rholang_codegen::reflect_ground_term_par(&__hole, __fingerprint);

        // Deliver the reduced hole on the premise channel; the installed contextual join
        // binds it and emits `⟦K'⟧` on `@out` — one atomic JOIN COMM (INV-6).
        let __call = ::mettail_rholang_codegen::contextual_contract_call(
            &[__premise_channel.as_str()],
            ::std::vec![__reflected_hole],
            out_channel,
        );
        ::core::result::Result::Ok(::mettail_rholang_codegen::RhoNetInjectionInvocation {
            call: __call,
            out_channel: out_channel.to_string(),
        })
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

            /// Build the in-Rho set-automaton MATCH call for the single, root-rooted
            /// rewrite firing of an already complete Dovetail report (Stage 3 piece 5):
            /// compile the language's in-Rho matching ruleset, GATE (fail closed if any
            /// fired rule is not matchable in Rho — FV (ix) `install_admits`), rebuild the
            /// ground subject `LHS[σ]`, and assemble the `network ‖ spread` call the runtime
            /// runs against the installed σ-receiver program. Unlike
            /// [`Self::rho_net_invocation_from_dovetail_to`] (which host-computes σ and
            /// injects it), here the automaton re-does the MATCHING on the interpreter (the
            /// `$\tau$` `sa:` COMMs) and fires the σ-receiver — the campaign endpoint for a
            /// base rewrite. The default backend (`swapdemo_backed`) calls this, falling
            /// back to the σ-replay driver on a gate/scope rejection.
            pub fn rho_net_match_invocation_from_dovetail_to(
                term: &dyn mettail_runtime::Term,
                report: &mettail_runtime::RuntimeDovetailRunReport,
                out_channel: impl ::core::convert::AsRef<str>,
            ) -> ::core::result::Result<
                ::mettail_rholang_codegen::RhoNetInjectionInvocation,
                ::std::string::String,
            > {
                #match_body
            }

            /// Build the CONTEXTUAL (congruence) JOIN injection for a single, root-rooted
            /// premise firing of an already complete Dovetail report (Stage 3a) — the third
            /// arm of the σ-injection F-function family (base | AC | contextual).
            ///
            /// A congruence rewrite `⟦ S ~> T |- K(S) ~> K'(T) ⟧` fires no explicit Dovetail
            /// rule (the e-graph congruence closure closes the context implicitly), so unlike
            /// [`Self::rho_net_invocation_from_dovetail_to`] (which dispatches on the fired
            /// rule's OWN σ-receiver) this is driven by the PREMISE firing: reconstruct the
            /// reduced hole `T = RHS_premise[σ]`
            /// ([`reconstruct_contractum`](mettail_rholang_codegen::reconstruct_contractum)),
            /// reflect it, and deliver it on the join's premise location channel via
            /// [`contextual_contract_call`](mettail_rholang_codegen::contextual_contract_call),
            /// where the installed [`contextual_join_receiver_par`](mettail_rholang_codegen::contextual_join_receiver_par)
            /// binds it and emits `⟦K'⟧` on `@out` — one atomic JOIN COMM on the reducer
            /// (INV-6). Returns codegen types (`RhoNetInjectionInvocation`) so the language
            /// crate takes no Rho runtime dependency.
            ///
            /// Stage 3a scope: exactly one UNARY congruence rule closed by a single
            /// root-rooted premise firing; 0/≥2 congruence rules, a non-unary context, or a
            /// multi-redex report fail closed (a later multi-premise stage).
            pub fn rho_net_contextual_invocation_from_dovetail_to(
                term: &dyn mettail_runtime::Term,
                report: &mettail_runtime::RuntimeDovetailRunReport,
                out_channel: impl ::core::convert::AsRef<str>,
            ) -> ::core::result::Result<
                ::mettail_rholang_codegen::RhoNetInjectionInvocation,
                ::std::string::String,
            > {
                #contextual_body
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
    fn generated_rho_net_invocation_emits_the_ac_firing_arm() {
        // Stage AC-U3: a linear with-rest HashBag AC rewrite emits an AC firing arm that
        // reconstructs the WHOLE operand bag from σ (the matched elements ⊎ the `rest`
        // sub-term's children) and sends its process-soup carrier via `ac_contract_call` —
        // NOT the flat base-rewrite `term_contract_call`.
        let language = parse(
            r##"
                name: AcNetGen,
                types {
                    Proc
                    ![mettail_runtime::HashBag<Proc>] as Bag {
                        open_parts: ["#{"],
                        close_parts: ["}#"],
                        sep: "|",
                    }
                }
                terms {
                    A . |- "A" : Proc ;
                    Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
                    PPar . ps:HashBag(Proc) |- "#{" ps.*sep("|") "}#" : Proc ;
                }
                equations {}
                rewrites {
                    AcStep . |- (PPar {x, ...rest}) ~> (Wrap x) ;
                }
            "##,
        );
        let tokens = generate_rho_net_invocation(&language).to_string();
        assert!(tokens.contains("rho_net_invocation_from_dovetail_to"));
        // The AC arm reconstructs the whole bag and sends it via the AC injection builder.
        assert!(tokens.contains("ac_contract_call"));
        assert!(tokens.contains("GroundTerm :: collection"));
        assert!(tokens.contains("CollectionType :: HashBag"));
        // The `rest` sub-term's children are spliced into the whole bag.
        assert!(tokens.contains("__rest . children"));
        // The fired AC rule's bare label keys the AC firing arm.
        assert!(tokens.contains("\"AcStep\""));
        // A pure-AC language surfaces no flat base-rewrite site, so no `term_contract_call`.
        assert!(!tokens.contains("term_contract_call"));
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
    fn generated_rho_net_invocation_emits_the_contextual_join_arm() {
        // Stage 3a: a UNARY congruence rewrite `| S ~> T |- Wrap(S) ~> Wrap(T)` (plus a base
        // rewrite `Flip` to fire the premise) emits the contextual injection method, which
        // reconstructs the reduced hole from the premise firing and delivers it via
        // `contextual_contract_call` — the third arm (base | AC | contextual) of the F-fn.
        let language = parse(
            r#"
                name: CtxNetGen,
                types { Proc }
                terms {
                    A . |- "A" : Proc ;
                    B . |- "B" : Proc ;
                    Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
                    Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
                    Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
                }
                equations {}
                rewrites {
                    Flip . |- (Swap x y) ~> (Pair y x) ;
                    WrapCong . | S ~> T |- (Wrap S) ~> (Wrap T) ;
                }
            "#,
        );
        let tokens = generate_rho_net_invocation(&language).to_string();
        // The contextual injection method + its distinctive helpers.
        assert!(tokens.contains("rho_net_contextual_invocation_from_dovetail_to"));
        assert!(tokens.contains("rho_net_contextual_injection_sites"));
        assert!(tokens.contains("reconstruct_contractum"));
        assert!(tokens.contains("contextual_contract_call"));
        // The base arm still fires for the `Flip` premise rewrite (base | AC | contextual).
        assert!(tokens.contains("term_contract_call"));
        assert!(tokens.contains("\"Flip\"") || tokens.contains("Flip"));
    }

    #[test]
    fn generated_rho_net_invocation_emits_the_in_rho_match_method() {
        // Stage 4 M-reflect: the emitted impl carries the in-Rho MATCH invocation — compile the
        // ruleset, GATE on it, STRUCTURALLY reflect the whole subject term (NOT the report σ),
        // check the redex is root-rooted, and assemble the network‖spread call (the automaton
        // LOCATES the redex + emits σ ON the interpreter).
        let tokens = generate_rho_net_invocation(&swap_net_fixture()).to_string();
        assert!(tokens.contains("rho_net_match_invocation_from_dovetail_to"));
        assert!(tokens.contains("compile_in_rho_matching_ruleset"));
        assert!(tokens.contains("in_rho_match_gate_reject"));
        assert!(tokens.contains("in_rho_match_call_par"));
        // M-reflect: the MATCH path structurally reflects `term` (the greenfield hinge) and
        // checks the redex is root-rooted — instead of rebuilding LHS[σ] from the report σ.
        assert!(
            tokens.contains("__mettail_rho_net_reflect_proc"),
            "per-category Term→GroundTerm"
        );
        assert!(tokens.contains("rule_lhs_root_constructor"), "root-rooted redex check");
        // Retirement proof (by construction): the MATCH path no longer reconstructs LHS[σ] from
        // the host report σ — `reconstruct_redex_subject` is gone from the emitted MATCH method,
        // so the σ the σ-receiver fires on is produced by the `sa:` accept, never the report.
        // (The σ-injection `body` above is a DIFFERENT method and legitimately keeps its σ read;
        // the match method uniquely names the reflection fns, asserted present above.)
        assert!(
            !tokens.contains("reconstruct_redex_subject"),
            "the MATCH path must not rebuild the redex from the report σ (M-reflect retirement)"
        );
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
