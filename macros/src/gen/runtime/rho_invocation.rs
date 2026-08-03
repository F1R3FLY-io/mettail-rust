//! Rho scalar invocation helper generation.
//!
//! Generated language crates stay substrate-neutral by default. The items this
//! module emits are behind the expansion-site `rho-codegen` feature and return
//! codegen-owned scalar invocation payloads. Runtime-facing crates normalize
//! those payloads through `mettail-rho-runtime`.

use std::collections::{BTreeMap, BTreeSet};

use mettail_ast::grammar::{NonTerminalKind, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::{EvalMode, TypeExpr};
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

/// Emit a codegen-owned `AcReconstructTemplate` VALUE (a constructor-call expression) for a nested
/// structural-AC operand / reduct template, so the generated σ-injection F-function can materialize it
/// at runtime and walk it with the firing's σ (`instantiate_ac_reconstruct_template`) to rebuild the
/// ground operand / reduct. Recurses through the template's `Node` children / `Bag` elements.
fn ac_template_tokens(template: &mettail_rholang_codegen::AcReconstructTemplate) -> TokenStream {
    use mettail_rholang_codegen::AcReconstructTemplate as T;
    match template {
        T::Var(name) => {
            let name = lit(name);
            quote! { ::mettail_rholang_codegen::AcReconstructTemplate::Var(#name.to_string()) }
        },
        T::Node { constructor, children } => {
            let constructor = lit(constructor);
            let children: Vec<TokenStream> = children.iter().map(ac_template_tokens).collect();
            quote! {
                ::mettail_rholang_codegen::AcReconstructTemplate::Node {
                    constructor: #constructor.to_string(),
                    children: ::std::vec![#(#children),*],
                }
            }
        },
        T::Bag { op, elements, rest } => {
            let op = lit(op);
            let elements: Vec<TokenStream> = elements.iter().map(ac_template_tokens).collect();
            let rest = match rest {
                Some(rest) => {
                    let rest = lit(rest);
                    quote! { ::core::option::Option::Some(#rest.to_string()) }
                },
                None => quote! { ::core::option::Option::None },
            };
            quote! {
                ::mettail_rholang_codegen::AcReconstructTemplate::Bag {
                    op: #op.to_string(),
                    elements: ::std::vec![#(#elements),*],
                    rest: #rest,
                }
            }
        },
        // A-S5.8 (F8-AM-1b): the RHS-introduced binder scope. Totality arm only — a
        // binder-templated rule takes the NO-MATCH-ENTRY lowering disposition and surfaces
        // in NO injection site, so these tokens are never emitted for a bundled language;
        // the arm keeps this tokenizer total over the extended template enum.
        T::Binder { body } => {
            let body = ac_template_tokens(body);
            quote! {
                ::mettail_rholang_codegen::AcReconstructTemplate::Binder {
                    body: ::std::boxed::Box::new(#body),
                }
            }
        },
    }
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
    let mut inner_arms = Vec::new();
    let mut covered: std::collections::HashSet<String> = std::collections::HashSet::new();
    for (category, arms) in category_match_arms(plans) {
        covered.insert(category.clone());
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
    // The outer `_ => None` fallback is reachable only when some inner category lacks a scalar
    // arm. When every category is covered, the per-category arms plus the explicit `Ambiguous`
    // arm exhaust `#inner_enum`, so the wildcard would be an unreachable pattern (MixedMath).
    let all_covered = language
        .types
        .iter()
        .all(|t| covered.contains(&t.name.to_string()));
    let outer_default = if all_covered {
        quote! {}
    } else {
        quote! { _ => None, }
    };

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
                #outer_default
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
///
/// ⚠ RECURSION, NOT ADMISSION. Since (A4) this predicate answers only "can the walk RECURSE
/// here?"; whether a field is admissible at all is [`classify_reflect_field`]. A token-text
/// leaf is not recursible (it is atomic data, not a subterm) yet IS reflectable, as a nullary
/// node — so the two questions had to stop being the same question.
fn is_structural_category_field(field: &FieldInfo) -> bool {
    !field.is_collection
        && !field.is_optional
        && !field.is_predicate
        // L9-3: a token-text capture (`String`) is not a recursible subterm — it has no
        // `__mettail_rho_net_reflect_<cat>` to call (branch on the flag BEFORE reading
        // `category`, whose placeholder is `String`). Its NULLARY image is emitted by
        // `ReflectField::IdentText` instead.
        && !field.is_opaque_leaf()
        && !NonTerminalKind::classify(&field.category.to_string()).is_builtin()
}

/// (A4) How a constructor field reflects into a [`GroundTerm`] child. TOTAL over `FieldInfo`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReflectField {
    /// A recursible category subterm — `__mettail_rho_net_reflect_<cat>(field.as_ref())?`.
    Structural,
    /// An [`OpaqueLeafKind::TokenText`] capture (`m:Ident`, `v@Tok`): a NULLARY ground leaf
    /// whose tag BAKES the text — `^ident("nth")`. Atomic data, so nothing to recurse into;
    /// distinct texts give structurally distinct ground terms, which is what lets the in-Rho
    /// set automaton LOCATE a named constructor instead of falling back to σ-replay.
    IdentText,
    /// No positional ground image at all — the host variant fails reflection CLOSED and the
    /// firing routes to σ-replay. Covers builtin/optional/predicate/collection fields and
    /// [`OpaqueLeafKind::GuestBody`] (an `Arc<FltNode>` is an opaque foreign payload with no
    /// ground image, and inventing a `{:?}` tag for it would make σ-replay silently
    /// unnecessary-looking without making the match correct).
    NotReflectable,
}

/// Classify a field for the M-reflect walk. Branches on the leaf FLAG before reading
/// `category`, whose value is a placeholder (`String`/`FltNode`) for leaf fields.
fn classify_reflect_field(field: &FieldInfo) -> ReflectField {
    if is_structural_category_field(field) {
        return ReflectField::Structural;
    }
    match field.opaque_leaf {
        Some(crate::gen::term_ops::subst::OpaqueLeafKind::TokenText)
            if !field.is_optional && !field.is_collection =>
        {
            ReflectField::IdentText
        },
        _ => ReflectField::NotReflectable,
    }
}

/// Generate the per-category structural `Term → GroundTerm` reflection fn — the M-reflect
/// greenfield hinge. It mirrors the Dovetail report's `category_lowering` term walk
/// (`macros/src/gen/runtime/dovetail_report.rs`) but produces a codegen
/// [`GroundTerm`](mettail_rholang_codegen::GroundTerm) DIRECTLY from the runtime subject term
/// (NOT from the report's σ), tagging each node with its BARE constructor label — the exact
/// input `spread_term_par` / `reflect_tag` expect, so the reflected subject is coherent with the
/// automaton's compiled tags. It is TOTAL over the category's variants: a Nullary or a Regular
/// constructor all of whose fields are reflectable ([`classify_reflect_field`]) reflects; a Var
/// / Literal / Collection / Binder / a Regular with a NON-reflectable field fails CLOSED with a
/// typed reason (the firing then falls back to the σ-replay driver). The `k` reflection fns
/// (one per category) are mutually recursive nested fns, so cross-category structural fields
/// resolve without a trait surface.
///
/// ★ (A4) "Reflectable" is strictly wider than "recursible". A token-text field
/// (`OpaqueLeafKind::TokenText`) is atomic data with no child to recurse into, yet has a
/// perfectly good NULLARY image — `^ident("nth")` — so its host constructor now reflects
/// STRUCTURALLY instead of failing closed. A guest-body field (`OpaqueLeafKind::GuestBody`)
/// still fails closed: an `Arc<FltNode>` is an opaque foreign payload, and a `{:?}` tag over
/// it would make the reflection LOOK total while giving the automaton nothing it can match on.
#[cfg(test)]
#[allow(dead_code)]
fn reflect_category_fn(language: &LanguageDef, category: &Ident) -> TokenStream {
    let fn_name = reflect_fn_name(category);
    let ground = quote!(::mettail_rholang_codegen::GroundTerm);
    let arms: Vec<TokenStream> = collect_category_variants(category, language)
        .into_iter()
        .map(|variant| match variant {
            // ★ #141 G5 — see `VariantKind::Refused`.
            VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
            VariantKind::Nullary { label } => {
                let label_lit = lit(&label.to_string());
                quote! {
                    #category::#label => ::core::result::Result::Ok(
                        #ground::new(#label_lit, ::std::vec::Vec::new())
                    )
                }
            },
            VariantKind::Regular { label, fields }
                if fields
                    .iter()
                    .all(|f| classify_reflect_field(f) != ReflectField::NotReflectable) =>
            {
                let label_lit = lit(&label.to_string());
                let ident_label_lit = lit(mettail_rholang_codegen::IDENT_TEXT_REFLECT_LABEL);
                let field_vars: Vec<Ident> =
                    (0..fields.len()).map(|i| format_ident!("__field_{i}")).collect();
                let child_calls: Vec<TokenStream> = fields
                    .iter()
                    .zip(field_vars.iter())
                    .map(|(field, var)| match classify_reflect_field(field) {
                        ReflectField::Structural => {
                            let child_fn = reflect_fn_name(&field.category);
                            quote! { #child_fn(#var.as_ref())? }
                        },
                        // (A4) A token-text field reflects to a NULLARY ground leaf whose tag
                        // bakes the text — `^ident("nth")`. This is the SAME shape the
                        // `Literal` arm below emits for a native-scalar leaf
                        // (`format!("{}({:?})", label, value)`), which is already the accepted
                        // structural image of atomic data; the only difference is that the tag
                        // is `^`-prefixed and therefore unforgeable versus any user `Ident`.
                        // `#var` is a `&String` here, so `{:?}` renders the quoted text.
                        ReflectField::IdentText => quote! {
                            #ground::new(
                                ::std::format!("{}({:?})", #ident_label_lit, #var),
                                ::std::vec::Vec::new(),
                            )
                        },
                        // ★ #141 G9. "The arm guard rejects it" is a claim about a
                        // guard twenty lines up staying in step with this classifier;
                        // nothing checks it, and an `unreachable!` here is mute (a
                        // proc-macro panic prints nothing under this workspace's
                        // cranelift dev backend — #141 RED-0). The closure yields the
                        // child's tokens, so the refusal simply IS the child.
                        ReflectField::NotReflectable => {
                            let message = format!(
                                "mettail internal error: the in-Rho reflection of \
                                 constructor `{label}` reached a field with no positional \
                                 ground image, which the arm guard is supposed to have \
                                 rejected. The guard and the field classifier have drifted \
                                 apart. This is a macro bug, not a grammar bug — please \
                                 report it."
                            );
                            quote! { compile_error!(#message) }
                        },
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
            // A native-scalar LITERAL leaf (`Int::NumLit(8)`, a `![i64]`-category value) reflects to
            // a NULLARY `GroundTerm` whose tag bakes the literal value — `"NumLit(8)"` — the SAME
            // bare form the Dovetail report bare-ifies a literal op-enum leaf to. This is the exact
            // structural image of a literal (a ground nullary node), and it lets a native process
            // `NativeProc(a₀..a_{k-1})` over literal args reflect STRUCTURALLY, so the automaton can
            // LOCATE its App head + CAPTURE the args in Rho (Stage 4 S-native). The captured args
            // only GATE the located native dispatch; the native VALUE stays the trusted handler's
            // payload (the firing's contractum), so an internally-consistent tag suffices — a Var
            // leaf still matches it. The tag format matters only for the spread's own coherence.
            // Stage 0 identity — STAYS (spread leaf tagging; the tag format
            // matters only for the spread's own coherence).
            VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
                let label_lit = lit(&label.to_string());
                quote! {
                    #category::#label(__value) => ::core::result::Result::Ok(
                        #ground::new(
                            ::std::format!("{}({:?})", #label_lit, __value),
                            ::std::vec::Vec::new(),
                        )
                    )
                }
            },
            // Stage 4 (S-binder): a VARIABLE leaf (`Term::TVar(OrdVar)`) reflects DE-BRUIJN. The
            // runtime is already de-Bruijn (moniker), so a BOUND occurrence
            // `Var::Bound{scope, binder}` reflects to a `^bound(peano(scope))` leaf — the reserved
            // `^bound` tag over a Peano numeral `S(S(…(Z)))` of the scope offset — and a genuinely
            // FREE occurrence to a `^free(name)` leaf. This is what lets a binder body (reflected
            // under the `^lambda` arm below) carry its bound occurrences as structural ground nodes,
            // so the set-automaton can LOCATE + CAPTURE an `App(^lambda(body), arg)` β-redex in Rho
            // (the reduct — the capture-avoiding substitution — is deferred to the S-binder slice-2
            // in-Rho TRS; this slice only MATCHES + captures `(body, arg)`). The `^`-prefixed tags
            // are unforgeable vs any user `Ident`; `Z`/`S` are only meaningful UNDER `^bound`.
            VariantKind::Var { label } => {
                let bound_lit = lit(mettail_rholang_codegen::BOUND_VAR_REFLECT_LABEL);
                let free_lit = lit(mettail_rholang_codegen::FREE_VAR_REFLECT_LABEL);
                let zero_lit = lit(mettail_rholang_codegen::PEANO_ZERO_REFLECT_LABEL);
                let succ_lit = lit(mettail_rholang_codegen::PEANO_SUCC_REFLECT_LABEL);
                quote! {
                    #category::#label(__ordvar) => match &__ordvar.0 {
                        mettail_runtime::Var::Bound(__bv) => {
                            let mut __peano = #ground::new(#zero_lit, ::std::vec::Vec::new());
                            for _ in 0..__bv.scope.0 {
                                __peano = #ground::new(#succ_lit, ::std::vec![__peano]);
                            }
                            ::core::result::Result::Ok(#ground::new(#bound_lit, ::std::vec![__peano]))
                        },
                        mettail_runtime::Var::Free(__fv) => ::core::result::Result::Ok(
                            #ground::new(
                                #free_lit,
                                ::std::vec![#ground::new(
                                    ::std::format!("{:?}", __fv),
                                    ::std::vec::Vec::new(),
                                )],
                            )
                        ),
                    }
                }
            },
            // An AC operand COLLECTION `op(HashBag<E>)` / `op(HashSet<E>)` (Stage 4 S-AC / AC4)
            // reflects to a `GroundTerm::collection(kind, op, children)` whose `children` are the
            // reflected elements (order-independent; a `HashBag` is multiplicity-preserving, a
            // `HashSet` uniqueness-preserving). This is the structural image of the operand collection
            // DIRECTLY from the runtime subject term — NOT the report σ — so the in-Rho AC matcher (a
            // co-installed `ac_sigma_receiver_par` over the SPREAD of this collection) picks k-of-n +
            // binds `rest` ON the interpreter: a genuine in-Rho replacement, not a σ-replay duplicate.
            // A `HashBag` rides the process-soup carrier; a `HashSet` the native `ESet` carrier (its
            // field is `std::collections::HashSet<E>`, iterated by `.iter()`). A `HashMap` has no
            // element_cat-shaped image here (its entries are `key => value` pairs — its reflection is
            // reached through the runtime-value path, not this constructor arm) and fails CLOSED,
            // routing that firing to the σ-replay driver.
            VariantKind::Collection { label, element_cat, coll_type } => match coll_type {
                mettail_ast::types::CollectionType::HashBag => {
                    let label_lit = lit(&label.to_string());
                    let element_reflect = reflect_fn_name(&element_cat);
                    quote! {
                        #category::#label(__bag) => {
                            let mut __children =
                                ::std::vec::Vec::with_capacity(__bag.len());
                            for __elem in __bag.iter_elements() {
                                __children.push(#element_reflect(__elem)?);
                            }
                            ::core::result::Result::Ok(
                                ::mettail_rholang_codegen::GroundTerm::collection(
                                    ::mettail_rholang_codegen::CollectionType::HashBag,
                                    #label_lit,
                                    __children,
                                )
                            )
                        }
                    }
                },
                // A `HashSet` collection FIELD rides `HashSetLit` (see
                // `macros/src/gen/types/enums.rs`), a deterministic, orderable, hashable set wrapper
                // iterated by `.iter()` (yielding `&E`, no multiplicity). The reflected `GroundTerm`
                // is tagged `HashSet`, so it rides the native `ESet` carrier (`reflect_ac_set_par`) —
                // which `ParSet` sorts + dedupes, so SET uniqueness holds through the reflect.
                mettail_ast::types::CollectionType::HashSet => {
                    let label_lit = lit(&label.to_string());
                    let element_reflect = reflect_fn_name(&element_cat);
                    quote! {
                        #category::#label(__set) => {
                            let mut __children =
                                ::std::vec::Vec::with_capacity(__set.len());
                            for __elem in __set.iter() {
                                __children.push(#element_reflect(__elem)?);
                            }
                            ::core::result::Result::Ok(
                                ::mettail_rholang_codegen::GroundTerm::collection(
                                    ::mettail_rholang_codegen::CollectionType::HashSet,
                                    #label_lit,
                                    __children,
                                )
                            )
                        }
                    }
                },
                _ => {
                    let msg = lit(&format!(
                        "in-Rho match reflection: {label} is a non-bare-var ({coll_type:?}) collection with no in-Rho AC carrier via this arm"
                    ));
                    quote! {
                        #category::#label(..) =>
                            ::core::result::Result::Err(::std::string::String::from(#msg))
                    }
                },
            },
            // Stage 4 (S-binder): a single BINDER node (`Term::Lam(Scope<Binder, Arc<Body>>)`)
            // reflects to `^lambda([⟦body⟧])` — the reserved `^lambda` tag over the reflected scope
            // BODY (read via `unsafe_body()`, which preserves the de-Bruijn coordinates: a bound
            // occurrence in the body reflects to `^bound(peano(n))` under the `Var` arm, NOT a fresh
            // free var). The bound variable is de-Bruijn-IMPLICIT (no named binder leaf), so the node
            // has exactly ONE child — the shape an `App(^lambda(body), arg)` automaton entry matches.
            // A MultiBinder reflects to `^multilambda([⟦body⟧])` identically. A binder WITH
            // pre-scope fields (e.g. `PInput(chan, ^x.body)`) has no single-child `^lambda` image in
            // this slice and fails CLOSED (routing that firing to the σ-replay driver).
            VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
                if pre_scope_fields.is_empty() =>
            {
                let lambda_lit = lit(mettail_rholang_codegen::LAMBDA_REFLECT_LABEL);
                let body_fn = reflect_fn_name(&body_cat);
                quote! {
                    #category::#label(__scope) => {
                        let __body = #body_fn(__scope.unsafe_body().as_ref())?;
                        ::core::result::Result::Ok(#ground::new(#lambda_lit, ::std::vec![__body]))
                    }
                }
            },
            VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. }
                if pre_scope_fields.is_empty() =>
            {
                let multilambda_lit = lit(mettail_rholang_codegen::MULTILAMBDA_REFLECT_LABEL);
                let body_fn = reflect_fn_name(&body_cat);
                quote! {
                    #category::#label(__scope) => {
                        let __body = #body_fn(__scope.unsafe_body().as_ref())?;
                        ::core::result::Result::Ok(#ground::new(#multilambda_lit, ::std::vec![__body]))
                    }
                }
            },
            VariantKind::Binder { label, .. } | VariantKind::MultiBinder { label, .. } => {
                let msg = lit(&format!(
                    "in-Rho match reflection: {label} is a binder node with pre-scope fields — no single-child ^lambda ground image in this slice"
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

/// Handler name for one category in the shared stack-safe reflection PDA.
fn reflect_handler_name(category: &Ident) -> Ident {
    format_ident!("__mettail_rho_net_reflect_handle_{}", to_snake(&category.to_string()))
}

/// Task variant for one category in the shared stack-safe reflection PDA.
fn reflect_task_variant(category: &Ident) -> Ident {
    format_ident!("Visit{}", category)
}

/// Generate the task algebra, reusable allocation pools, and single dispatch engine used by all
/// category reflectors in one language. Raw pointers make the task type lifetime-free so its
/// allocation can be retained between calls; every pointer is derived from the wrapper's live
/// input borrow and consumed synchronously before that wrapper returns.
fn reflect_pda_support(language: &LanguageDef) -> TokenStream {
    let task_variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
            let variant = reflect_task_variant(category);
            quote! { #variant(*const #category) }
        })
        .collect();
    let dispatch: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
            let variant = reflect_task_variant(category);
            let handler = reflect_handler_name(category);
            quote! {
                __MettailReflectTask::#variant(__ptr) => {
                    // SAFETY: the wrapper creates this pointer from its borrowed input and the
                    // synchronous engine drains every task before the borrow can end.
                    #handler(unsafe { &*__ptr }, &mut __tasks, &mut __values)?;
                }
            }
        })
        .collect();
    let ident_label_lit = lit(mettail_rholang_codegen::IDENT_TEXT_REFLECT_LABEL);

    quote! {
        #[allow(dead_code)]
        enum __MettailReflectTask {
            #(#task_variants,)*
            IdentText(*const ::std::string::String),
            Assemble {
                constructor: &'static str,
                coll_type: ::core::option::Option<
                    ::mettail_rholang_codegen::CollectionType,
                >,
                child_count: usize,
            },
        }

        ::std::thread_local! {
            static __METTAIL_REFLECT_TASK_POOL:
                ::std::cell::Cell<::std::vec::Vec<__MettailReflectTask>> =
                    const { ::std::cell::Cell::new(::std::vec::Vec::new()) };
            static __METTAIL_REFLECT_VALUE_POOL:
                ::std::cell::Cell<
                    ::std::vec::Vec<::mettail_rholang_codegen::GroundTerm>,
                > = const { ::std::cell::Cell::new(::std::vec::Vec::new()) };
        }

        fn __mettail_rho_net_reflect_run(
            __seed: __MettailReflectTask,
        ) -> ::core::result::Result<
            ::mettail_rholang_codegen::GroundTerm,
            ::std::string::String,
        > {
            let mut __tasks = __METTAIL_REFLECT_TASK_POOL.with(|__pool| __pool.take());
            let mut __values = __METTAIL_REFLECT_VALUE_POOL.with(|__pool| __pool.take());
            __tasks.clear();
            __values.clear();
            __tasks.push(__seed);

            let __result = (|| {
                while let ::core::option::Option::Some(__task) = __tasks.pop() {
                    match __task {
                        #(#dispatch)*
                        __MettailReflectTask::IdentText(__ptr) => {
                            // SAFETY: identical lifetime argument to category task pointers.
                            let __text = unsafe { &*__ptr };
                            __values.push(::mettail_rholang_codegen::GroundTerm::new(
                                ::std::format!("{}({:?})", #ident_label_lit, __text),
                                ::std::vec::Vec::new(),
                            ));
                        },
                        __MettailReflectTask::Assemble {
                            constructor,
                            coll_type,
                            child_count,
                        } => {
                            let __first_child = __values.len().checked_sub(child_count)
                                .ok_or_else(|| ::std::string::String::from(
                                    "generated reflection PDA lost a child result",
                                ))?;
                            let __children = __values.split_off(__first_child);
                            __values.push(::mettail_rholang_codegen::GroundTerm {
                                constructor: ::std::string::String::from(constructor),
                                children: __children,
                                coll_type,
                            });
                        },
                    }
                }

                if __values.len() != 1 {
                    return ::core::result::Result::Err(::std::format!(
                        "generated reflection PDA produced {} root results",
                        __values.len(),
                    ));
                }
                ::core::result::Result::Ok(__values.pop().expect(
                    "generated reflection PDA checked its root-result count",
                ))
            })();

            // The returned root has been moved out. On error, stack-safe GroundTerm::drop makes
            // clearing partially assembled results safe at arbitrary input depth.
            __tasks.clear();
            __values.clear();
            __METTAIL_REFLECT_TASK_POOL.with(|__pool| __pool.set(__tasks));
            __METTAIL_REFLECT_VALUE_POOL.with(|__pool| __pool.set(__values));
            __result
        }
    }
}

/// Generate one category handler and its thin wrapper for the shared reflection PDA.
fn reflect_category_pda_fn(language: &LanguageDef, category: &Ident) -> TokenStream {
    let fn_name = reflect_fn_name(category);
    let handler_name = reflect_handler_name(category);
    let seed_variant = reflect_task_variant(category);
    let ground = quote!(::mettail_rholang_codegen::GroundTerm);
    let arms: Vec<TokenStream> = collect_category_variants(category, language)
        .into_iter()
        .map(|variant| match variant {
            VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
            VariantKind::Nullary { label } => {
                let label_lit = lit(&label.to_string());
                quote! {
                    #category::#label => {
                        __values.push(#ground::new(#label_lit, ::std::vec::Vec::new()));
                        ::core::result::Result::Ok(())
                    }
                }
            },
            VariantKind::Regular { label, fields }
                if fields
                    .iter()
                    .all(|field| classify_reflect_field(field) != ReflectField::NotReflectable) =>
            {
                let label_lit = lit(&label.to_string());
                let field_vars: Vec<Ident> =
                    (0..fields.len()).map(|index| format_ident!("__field_{index}")).collect();
                let child_pushes: Vec<TokenStream> = fields
                    .iter()
                    .zip(field_vars.iter())
                    .rev()
                    .map(|(field, var)| match classify_reflect_field(field) {
                        ReflectField::Structural => {
                            let child_variant = reflect_task_variant(&field.category);
                            quote! {
                                __tasks.push(__MettailReflectTask::#child_variant(
                                    #var.as_ref() as *const _,
                                ));
                            }
                        },
                        ReflectField::IdentText => quote! {
                            __tasks.push(__MettailReflectTask::IdentText(#var as *const _));
                        },
                        ReflectField::NotReflectable => {
                            let message = format!(
                                "mettail internal error: reflection PDA admission and field classifier drifted for constructor `{label}`"
                            );
                            quote! { compile_error!(#message); }
                        },
                    })
                    .collect();
                let child_count = fields.len();
                quote! {
                    #category::#label(#(#field_vars),*) => {
                        __tasks.push(__MettailReflectTask::Assemble {
                            constructor: #label_lit,
                            coll_type: ::core::option::Option::None,
                            child_count: #child_count,
                        });
                        #(#child_pushes)*
                        ::core::result::Result::Ok(())
                    }
                }
            },
            VariantKind::Regular { label, .. } => {
                let message = lit(&format!(
                    "in-Rho match reflection: constructor {label} has a non-structural field with no positional ground image"
                ));
                quote! {
                    #category::#label(..) => ::core::result::Result::Err(
                        ::std::string::String::from(#message),
                    )
                }
            },
            VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
                let label_lit = lit(&label.to_string());
                quote! {
                    #category::#label(__value) => {
                        __values.push(#ground::new(
                            ::std::format!("{}({:?})", #label_lit, __value),
                            ::std::vec::Vec::new(),
                        ));
                        ::core::result::Result::Ok(())
                    }
                }
            },
            VariantKind::Var { label } => {
                let bound_lit = lit(mettail_rholang_codegen::BOUND_VAR_REFLECT_LABEL);
                let free_lit = lit(mettail_rholang_codegen::FREE_VAR_REFLECT_LABEL);
                let zero_lit = lit(mettail_rholang_codegen::PEANO_ZERO_REFLECT_LABEL);
                let succ_lit = lit(mettail_rholang_codegen::PEANO_SUCC_REFLECT_LABEL);
                quote! {
                    #category::#label(__ordvar) => {
                        let __reflected = match &__ordvar.0 {
                            mettail_runtime::Var::Bound(__bv) => {
                                let mut __peano = #ground::new(
                                    #zero_lit,
                                    ::std::vec::Vec::new(),
                                );
                                for _ in 0..__bv.scope.0 {
                                    __peano = #ground::new(#succ_lit, ::std::vec![__peano]);
                                }
                                #ground::new(#bound_lit, ::std::vec![__peano])
                            },
                            mettail_runtime::Var::Free(__fv) => #ground::new(
                                #free_lit,
                                ::std::vec![#ground::new(
                                    ::std::format!("{:?}", __fv),
                                    ::std::vec::Vec::new(),
                                )],
                            ),
                        };
                        __values.push(__reflected);
                        ::core::result::Result::Ok(())
                    }
                }
            },
            VariantKind::Collection { label, element_cat, coll_type } => match coll_type {
                mettail_ast::types::CollectionType::HashBag => {
                    let label_lit = lit(&label.to_string());
                    let child_variant = reflect_task_variant(&element_cat);
                    quote! {
                        #category::#label(__bag) => {
                            __tasks.push(__MettailReflectTask::Assemble {
                                constructor: #label_lit,
                                coll_type: ::core::option::Option::Some(
                                    ::mettail_rholang_codegen::CollectionType::HashBag,
                                ),
                                child_count: __bag.len(),
                            });
                            let __first_child_task = __tasks.len();
                            for __element in __bag.iter_elements() {
                                __tasks.push(__MettailReflectTask::#child_variant(
                                    __element as *const _,
                                ));
                            }
                            __tasks[__first_child_task..].reverse();
                            ::core::result::Result::Ok(())
                        }
                    }
                },
                mettail_ast::types::CollectionType::HashSet => {
                    let label_lit = lit(&label.to_string());
                    let child_variant = reflect_task_variant(&element_cat);
                    quote! {
                        #category::#label(__set) => {
                            __tasks.push(__MettailReflectTask::Assemble {
                                constructor: #label_lit,
                                coll_type: ::core::option::Option::Some(
                                    ::mettail_rholang_codegen::CollectionType::HashSet,
                                ),
                                child_count: __set.len(),
                            });
                            let __first_child_task = __tasks.len();
                            for __element in __set.iter() {
                                __tasks.push(__MettailReflectTask::#child_variant(
                                    __element as *const _,
                                ));
                            }
                            __tasks[__first_child_task..].reverse();
                            ::core::result::Result::Ok(())
                        }
                    }
                },
                _ => {
                    let message = lit(&format!(
                        "in-Rho match reflection: {label} is a non-bare-var ({coll_type:?}) collection with no in-Rho AC carrier via this arm"
                    ));
                    quote! {
                        #category::#label(..) => ::core::result::Result::Err(
                            ::std::string::String::from(#message),
                        )
                    }
                },
            },
            VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
                if pre_scope_fields.is_empty() =>
            {
                let lambda_lit = lit(mettail_rholang_codegen::LAMBDA_REFLECT_LABEL);
                let body_variant = reflect_task_variant(&body_cat);
                quote! {
                    #category::#label(__scope) => {
                        __tasks.push(__MettailReflectTask::Assemble {
                            constructor: #lambda_lit,
                            coll_type: ::core::option::Option::None,
                            child_count: 1,
                        });
                        __tasks.push(__MettailReflectTask::#body_variant(
                            __scope.unsafe_body().as_ref() as *const _,
                        ));
                        ::core::result::Result::Ok(())
                    }
                }
            },
            VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. }
                if pre_scope_fields.is_empty() =>
            {
                let lambda_lit = lit(mettail_rholang_codegen::MULTILAMBDA_REFLECT_LABEL);
                let body_variant = reflect_task_variant(&body_cat);
                quote! {
                    #category::#label(__scope) => {
                        __tasks.push(__MettailReflectTask::Assemble {
                            constructor: #lambda_lit,
                            coll_type: ::core::option::Option::None,
                            child_count: 1,
                        });
                        __tasks.push(__MettailReflectTask::#body_variant(
                            __scope.unsafe_body().as_ref() as *const _,
                        ));
                        ::core::result::Result::Ok(())
                    }
                }
            },
            VariantKind::Binder { label, .. } | VariantKind::MultiBinder { label, .. } => {
                let message = lit(&format!(
                    "in-Rho match reflection: {label} is a binder node with pre-scope fields — no single-child ^lambda ground image in this slice"
                ));
                quote! {
                    #category::#label(..) => ::core::result::Result::Err(
                        ::std::string::String::from(#message),
                    )
                }
            },
        })
        .collect();

    quote! {
        fn #handler_name(
            __term: &#category,
            __tasks: &mut ::std::vec::Vec<__MettailReflectTask>,
            __values: &mut ::std::vec::Vec<#ground>,
        ) -> ::core::result::Result<(), ::std::string::String> {
            match __term {
                #(#arms),*
            }
        }

        fn #fn_name(
            __term: &#category,
        ) -> ::core::result::Result<#ground, ::std::string::String> {
            __mettail_rho_net_reflect_run(__MettailReflectTask::#seed_variant(
                __term as *const _,
            ))
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
    reflect_subject_binding_inner(language, false)
}

/// A-S5.4b (design v2 §3.2): the M-reflect subject binding for the REPORT-FREE bodies
/// (`rho_net_match_invocation_to` / `rho_net_drive_invocation_to`) — for a FLOAT-BEARING language
/// (one the macros side generates the binder-congruence handler for,
/// `should_emit_binder_congruence`), the subject is BOUNDARY-CANONICALIZED through the
/// unconditional unbind-first float BEFORE M-reflect:
/// `binder_congruence_nf_term().unwrap_or_else(original)` (the F17 `Some`-iff-progress contract,
/// per the `dovetail_report.rs` source-binding precedent). The canonicalized subject is
/// float-canonical — every binder outermost, every bag flat — so every redex modulo the declared
/// binder-float equational theory is SYNTACTICALLY present for the automaton/receivers
/// (`equations_boundary_canonicalizable`'s admission rests on exactly this; FV:
/// `BinderFloatCanonicalization.v`). For every other language this is BYTE-IDENTICAL to
/// [`reflect_subject_binding`] (the report-carrying bodies keep the uncanonicalized binding
/// unconditionally — they gate on the Dovetail report, whose producer already floats).
fn reflect_subject_binding_boundary_canonicalized(language: &LanguageDef) -> TokenStream {
    reflect_subject_binding_inner(
        language,
        crate::gen::runtime::binder_congruence::should_emit_binder_congruence(language),
    )
}

fn reflect_subject_binding_inner(language: &LanguageDef, canonicalize: bool) -> TokenStream {
    let name = &language.name;
    let language_lit = lit(&name.to_string());
    let term_name = format_ident!("{}Term", name);
    let reflect_pda = reflect_pda_support(language);
    let reflect_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| reflect_category_pda_fn(language, &ty.name))
        .collect();
    let primary = language
        .types
        .first()
        .map(|ty| ty.name.clone())
        .expect("a language declares at least one category");

    // A-S5.4b: the report-free bodies of a float-bearing language canonicalize the subject
    // through the unconditional binder float BEFORE M-reflect; every other emission reads the
    // downcast term directly (byte-identical tokens to pre-A-S5.4b).
    let subject_source = if canonicalize {
        quote! { __canonical }
    } else {
        quote! { __typed_term.0 }
    };
    let canonical_binding = if canonicalize {
        quote! {
            // A-S5.4b boundary canonicalization (design v2 §3.2, F17): float-canonicalize the
            // subject through the generated UNCONDITIONAL unbind-first binder float before
            // M-reflect. `binder_congruence_nf_term` returns `Some` iff observable progress;
            // an already-canonical subject reflects unchanged (the
            // `dovetail_report.rs` source-binding precedent). The float NF has every binder
            // outermost and every bag flat, so every redex modulo the declared binder-float
            // equations is SYNTACTICALLY present in the reflected subject — the discharge the
            // `equations_boundary_canonicalizable` admission (rho_net_lower) rests on.
            let __canonical = __typed_term
                .0
                .binder_congruence_nf_term()
                .unwrap_or_else(|| __typed_term.0.clone());
        }
    } else {
        quote! {}
    };

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
                for __alt in #subject_source.all_alts() {
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
            let __subject = #reflect_primary(&#subject_source)?;
        }
    };

    quote! {
        #reflect_pda
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
        #canonical_binding
        #subject_expr
    }
}

/// Generate the per-guest [`FltReflect`](mettail_rholang_codegen::FltReflect) impl (feature
/// `rho-codegen`) — the Stage-4 public FLT reflection hinge that lets a resolver reflect a guest
/// FLT template `` L`…` `` body into the [`GroundTerm`](mettail_rholang_codegen::GroundTerm) the
/// public FLT reflectors consume.
///
/// It is deliberately THIN and ADDITIVE: it REUSES [`reflect_subject_binding`] VERBATIM — the exact
/// `Term → GroundTerm` reflection the in-Rho match/drive invocation bodies emit (so an FLT template
/// reflects byte-identically to how the same term reflects for driving, `coll_type` and
/// `^bound(peano)` binder leaves included) — and applies the pure
/// [`flt_normalize_hole_names`](mettail_rholang_codegen::flt_normalize_hole_names) post-pass so a
/// hole `${f}` reflects to the STABLE `^free(f)` leaf (the moniker `pretty_name`) rather than the
/// reflector's unstable `format!("{:?}", fv)` debug string. Existing reflection/lowering codegen is
/// untouched.
pub fn generate_flt_reflect(language: &LanguageDef) -> TokenStream {
    let name = &language.name;
    let language_struct = format_ident!("{}Language", name);
    // The SAME reflect-fn group + `let __subject = …;` binding the match/drive invocation bodies
    // use (reads the `term: &dyn Term` local; produces `__subject: GroundTerm`). No boundary
    // canonicalization — an FLT template reflects exactly as written.
    let reflect_subject = reflect_subject_binding(language);
    quote! {
        #[cfg(feature = "rho-codegen")]
        impl ::mettail_rholang_codegen::FltReflect for #language_struct {
            fn reflect_flt_term(
                &self,
                term: &dyn mettail_runtime::Term,
            ) -> ::core::result::Result<
                ::mettail_rholang_codegen::GroundTerm,
                ::std::string::String,
            > {
                #reflect_subject
                ::core::result::Result::Ok(
                    ::mettail_rholang_codegen::flt_normalize_hole_names(__subject),
                )
            }

            fn parse_and_reflect_flt(
                &self,
                body: &str,
            ) -> ::core::result::Result<
                ::mettail_rholang_codegen::GroundTerm,
                ::std::string::String,
            > {
                // Parse the guest body in the guest's own surface (holes are ordinary guest free
                // variables); `parse_term_for_env` does NOT clear the var cache, so the caller's
                // interning is undisturbed when a lowering pass reflects several FLTs in a row.
                let __parsed = mettail_runtime::Language::parse_term_for_env(self, body)?;
                self.reflect_flt_term(__parsed.as_ref())
            }
        }
    }
}

/// A-S3: the native-scalar types whose LITERAL-LEAF ground tags (`"{Lit}({:?})"`, the
/// generated reflection PDA's literal-arm format) parse back FAITHFULLY via `FromStr` — the
/// registrability whitelist for machine-side native handlers. For each of these,
/// `parse ∘ debug-format = identity` on every value the leaf tag can carry (integers, IEEE
/// floats including `NaN`/`inf`/`-0.0`, booleans), and the generated ground-eval leaf arm
/// RE-CHECKS the identity at runtime (`format!("{:?}", parsed) == inner`), so an unfaithful
/// parse can only DEFER (the fold does not fire), never mis-evaluate. `String` is deliberately
/// absent (its `{:?}` tag is quoted/escaped — `FromStr` would keep the quotes), as is every
/// non-`FromStr` native type (e.g. `rug` big integers): a native rule over such a type gets NO
/// registered handler and the report-free match DEFERS it with a typed reason — exactly the
/// A-S2 behavior, never a silent wrong value.
const NATIVE_GROUND_PARSEABLE_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128", "f32", "f64", "bool",
];

/// Whether `ty` is a whitelisted ground-parseable native scalar type (token-string compare —
/// the `![…]` native type of a `types { … }` entry is a bare primitive path when whitelisted).
fn native_ground_parseable_type(ty: &syn::Type) -> bool {
    let rendered = quote!(#ty).to_string();
    NATIVE_GROUND_PARSEABLE_TYPES.contains(&rendered.as_str())
}

/// The RUNTIME VALUE type of a whitelisted native scalar category — the generated literal
/// variant's payload type (`macros/src/gen/types/enums.rs`): `f64`/`f32` ride the canonical
/// wrappers (`CanonicalFloat64`/`CanonicalFloat32`, Debug-transparent, canonicalized `Eq`), so
/// the fold bodies (written against the wrapper — `.get()`) and the safeified/lifted closures
/// (which return the wrapper) type-check identically to the D-stage dispatcher's bindings;
/// integers and `bool` are their declared primitives.
fn native_runtime_value_type(native: &syn::Type) -> TokenStream {
    match crate::gen::native::NativeType::from_syn_type(native) {
        crate::gen::native::NativeType::Float64 => quote! { mettail_runtime::CanonicalFloat64 },
        crate::gen::native::NativeType::Float32 => quote! { mettail_runtime::CanonicalFloat32 },
        _ => quote! { #native },
    }
}

/// The literal-leaf PARSE binding for a whitelisted native scalar category: bind
/// `__value: <runtime value type>` from the tag's inner string `__inner`, deferring (`None`) on
/// any parse failure. Floats parse the RAW primitive via `FromStr` and wrap through the
/// canonical constructor (`From<f64>`/`From<f32>` — the same canonicalization the literal
/// variant's payload was constructed with, so the faithfulness guard's re-format compares
/// canonical-to-canonical); integers and `bool` parse directly.
fn native_leaf_parse_binding(native: &syn::Type) -> TokenStream {
    match crate::gen::native::NativeType::from_syn_type(native) {
        crate::gen::native::NativeType::Float64 => quote! {
            let __raw: f64 = ::core::str::FromStr::from_str(__inner).ok()?;
            let __value: mettail_runtime::CanonicalFloat64 = ::core::convert::From::from(__raw);
        },
        crate::gen::native::NativeType::Float32 => quote! {
            let __raw: f32 = ::core::str::FromStr::from_str(__inner).ok()?;
            let __value: mettail_runtime::CanonicalFloat32 = ::core::convert::From::from(__raw);
        },
        _ => quote! {
            let __value: #native = ::core::str::FromStr::from_str(__inner).ok()?;
        },
    }
}

/// A category usable in A-S3 machine-side ground evaluation: a NON-collection native-scalar
/// category whose native type is ground-parseable. Returns the native type when so.
fn native_eval_category<'a>(language: &'a LanguageDef, category: &Ident) -> Option<&'a syn::Type> {
    let lang_type = language.get_type(category)?;
    if lang_type.collection_kind.is_some() {
        return None;
    }
    let native = lang_type.native_type.as_ref()?;
    native_ground_parseable_type(native).then_some(native)
}

/// One `fold` rule participating in A-S3 machine-side ground evaluation: every parameter a
/// `Simple`/`Base` typed param of a [`native_eval_category`], with a `![…]` fold body — the
/// ground-eval mirror of `typed_report.rs`'s `is_pure_native_arith` fold collection, restricted
/// to the ground-parseable whitelist. `registrable` additionally requires the OUTPUT category to
/// be a native-eval category (the handler must produce a literal-leaf ground value).
struct NativeEvalRule<'a> {
    /// `"{Category}_{Label}"` — the Dovetail firing label (`NativeDispatch::fired_rule_label`).
    fired_rule_label: String,
    /// The bare constructor label (`"PowInt"`) — the ground-eval match arm's tag.
    bare_label: String,
    /// The rule's typed params `(name, category)` in declaration order.
    params: Vec<(Ident, Ident)>,
    /// The `![…]` fold body (safeified at generation: overflow / ÷0 / NaN → defer).
    body: &'a syn::Expr,
    /// The output category (the arm's own category; the handler's literal-leaf wrapper).
    output_cat: Ident,
}

/// Collect the language's native-eval `fold` rules, grouped by OUTPUT category, plus the
/// registrable subset's fired labels. Mirrors `collect_fold_rules` (typed_report.rs) restricted
/// to the ground-parseable whitelist: `eval_mode == Fold`, a `![…]` body, all params
/// `Simple`/`Base` of native-eval categories. A rule outside the whitelist is simply ABSENT —
/// its located sites then defer with a typed reason (the fail-closed boundary), never a wrong
/// arm.
fn collect_native_eval_rules(language: &LanguageDef) -> Vec<NativeEvalRule<'_>> {
    let mut out = Vec::new();
    for rule in &language.terms {
        if rule.eval_mode != Some(EvalMode::Fold) {
            continue;
        }
        let Some(body) = rule.rust_code.as_ref().map(|rc| &rc.code) else {
            continue;
        };
        let Some(ctx) = rule.term_context.as_ref() else {
            continue;
        };
        if ctx.is_empty() {
            continue;
        }
        let mut params = Vec::with_capacity(ctx.len());
        let mut all_native_eval = true;
        for param in ctx {
            match param {
                TermParam::Simple { name, ty: TypeExpr::Base(category) }
                    if native_eval_category(language, category).is_some() =>
                {
                    params.push((name.clone(), category.clone()));
                },
                _ => {
                    all_native_eval = false;
                    break;
                },
            }
        }
        if !all_native_eval {
            continue;
        }
        // The output category must itself be ground-evaluable (the arm returns its native
        // value; the handler wraps it as the category's literal leaf).
        if native_eval_category(language, &rule.category).is_none() {
            continue;
        }
        out.push(NativeEvalRule {
            fired_rule_label: format!("{}_{}", rule.category, rule.label),
            bare_label: rule.label.to_string(),
            params,
            body,
            output_cat: rule.category.clone(),
        });
    }
    out
}

/// The per-category A-S3 ground-eval fn name (`__mettail_native_ground_eval_<Category>`). The
/// category name rides VERBATIM (collision-free: category names are unique idents; a snake-case
/// mangle of underscore-joined names could collide and would trip `non_snake_case` on the `__`
/// seams) — the generated fn carries `#[allow(non_snake_case)]`.
fn native_ground_eval_fn_name(category: &Ident) -> Ident {
    format_ident!("__mettail_native_ground_eval_{}", category)
}

/// The per-rule A-S3 handler fn name (`__mettail_native_handler_<Category>_<Label>`). The fired
/// label rides VERBATIM (unique per rule); the generated fn carries `#[allow(non_snake_case)]`.
fn native_handler_fn_name(fired_rule_label: &str) -> Ident {
    format_ident!("__mettail_native_handler_{}", fired_rule_label)
}

/// Generate the A-S3 machine-side NATIVE HANDLER TABLE for the report-free match body:
///
/// * one GROUND-EVAL fn per reachable native-eval category —
///   `__mettail_native_ground_eval_<cat>(g: &GroundTerm) -> Option<N>` — evaluating a reflected
///   ground subtree to its native value: a fold-rule arm per native-eval `fold` rule of that
///   output category (recursively evaluating the children per their param categories, then
///   running the rule's OWN safeified `![…]` body — the same `safeify_and_wrap` the D-stage
///   dispatcher runs, so overflow/÷0/NaN DEFERS instead of panicking), and a literal-leaf
///   fallback arm that parses the category's `"{Lit}({:?})"` tag with the
///   `parse ∘ format = identity` faithfulness guard. Every other constructor — a variable leaf
///   (`^free`/`^bound`), a foreign head, a collection — evaluates to `None`: the fold DEFERS,
///   mirroring the D-stage `try_eval()?` / `__class_is_fold_value` gate;
///
/// * one HANDLER fn per REGISTRABLE native rule —
///   `__mettail_native_handler_<rule>(args) -> Option<GroundTerm>` — evaluating the located σ
///   operands and wrapping the reduced value as the output category's literal-leaf ground term
///   (`"{Lit}({:?})"`, byte-identical to the reflection's literal arm and to the D-stage
///   contractum's bare form);
///
/// * the LOOKUP `__mettail_native_handler_for(fired_rule_label)` the report-free match body
///   keys `NativeDispatch` entries on. `None` = the rule has no registrable machine-side
///   handler → the located term DEFERS with a typed reason.
///
/// These are the SAME trusted evaluators the D-stage used — the `![…] fold` bodies compiled
/// against natively-bound operands (`typed_report.rs` binds `try_eval()` values and runs the
/// same safeified body) — now run by the MACHINE's dispatch COMM instead of ahead of it.
fn native_handler_table(language: &LanguageDef) -> TokenStream {
    let rules = collect_native_eval_rules(language);

    // Reachable native-eval categories: registrable-rule param/output categories, closed under
    // "params of native-eval fold rules of a reachable output category" (the eval fns are
    // mutually recursive through cross-category folds, e.g. casts).
    let mut reachable: BTreeSet<String> = BTreeSet::new();
    let mut frontier: Vec<Ident> = Vec::new();
    for rule in &rules {
        for (_, category) in &rule.params {
            if reachable.insert(category.to_string()) {
                frontier.push(category.clone());
            }
        }
        if reachable.insert(rule.output_cat.to_string()) {
            frontier.push(rule.output_cat.clone());
        }
    }
    while let Some(category) = frontier.pop() {
        for rule in &rules {
            if rule.output_cat != category {
                continue;
            }
            for (_, param_cat) in &rule.params {
                if reachable.insert(param_cat.to_string()) {
                    frontier.push(param_cat.clone());
                }
            }
        }
    }

    // One ground-eval fn per reachable category (BTreeSet order: deterministic emission).
    let eval_fns: Vec<TokenStream> = reachable
        .iter()
        .map(|category_name| {
            let category = ident(category_name);
            let fn_name = native_ground_eval_fn_name(&category);
            let native_ty = native_eval_category(language, &category)
                .expect("reachable categories are native-eval categories by construction");
            let value_ty = native_runtime_value_type(native_ty);
            let leaf_parse = native_leaf_parse_binding(native_ty);
            let lit_label = generate_literal_label(native_ty);
            let lit_prefix = lit(&format!("{lit_label}("));
            let fold_arms: Vec<TokenStream> = rules
                .iter()
                .filter(|rule| rule.output_cat == category)
                .map(|rule| {
                    let bare = lit(&rule.bare_label);
                    let child_idents: Vec<Ident> = (0..rule.params.len())
                        .map(|i| format_ident!("__mettail_native_child_{i}"))
                        .collect();
                    let binds: Vec<TokenStream> = rule
                        .params
                        .iter()
                        .zip(child_idents.iter())
                        .map(|((name, category), child)| {
                            let child_eval = native_ground_eval_fn_name(category);
                            quote! { let #name = #child_eval(#child)?; }
                        })
                        .collect();
                    // The rule's OWN fold body, safeified exactly as the D-stage dispatcher
                    // safeifies it (arith → SafeArith, Option-returning closure): a decline
                    // (`None`) defers the fold.
                    let safeified =
                        crate::gen::native::rust_code_rewrite::safeify_and_wrap(rule.body);
                    quote! {
                        #bare => {
                            let [#(#child_idents),*] = __g.children.as_slice() else {
                                return ::core::option::Option::None;
                            };
                            #(#binds)*
                            let __value: #value_ty = (#safeified)?;
                            ::core::option::Option::Some(__value)
                        },
                    }
                })
                .collect();
            quote! {
                #[allow(non_snake_case)]
                fn #fn_name(
                    __g: &::mettail_rholang_codegen::GroundTerm,
                ) -> ::core::option::Option<#value_ty> {
                    // A collection has no scalar ground value; a fold over one defers.
                    if __g.coll_type.is_some() {
                        return ::core::option::Option::None;
                    }
                    match __g.constructor.as_str() {
                        #(#fold_arms)*
                        __other => {
                            // The literal-leaf fallback: parse the category's
                            // `"{Lit}({:?})"` tag with the faithfulness guard
                            // (`parse ∘ format = identity`); anything else — a variable
                            // leaf, a foreign head — DEFERS (`None`), never guesses.
                            if !__g.children.is_empty() {
                                return ::core::option::Option::None;
                            }
                            let __inner =
                                __other.strip_prefix(#lit_prefix)?.strip_suffix(')')?;
                            #leaf_parse
                            if ::std::format!("{:?}", __value) == __inner {
                                ::core::option::Option::Some(__value)
                            } else {
                                ::core::option::Option::None
                            }
                        },
                    }
                }
            }
        })
        .collect();

    // One handler fn per registrable rule + the label-keyed lookup.
    let handler_fns: Vec<TokenStream> = rules
        .iter()
        .map(|rule| {
            let fn_name = native_handler_fn_name(&rule.fired_rule_label);
            let arg_idents: Vec<Ident> = (0..rule.params.len())
                .map(|i| format_ident!("__mettail_native_arg_{i}"))
                .collect();
            let binds: Vec<TokenStream> = rule
                .params
                .iter()
                .zip(arg_idents.iter())
                .map(|((name, category), arg)| {
                    let arg_eval = native_ground_eval_fn_name(category);
                    quote! { let #name = #arg_eval(#arg)?; }
                })
                .collect();
            let native_out_ty = native_eval_category(language, &rule.output_cat)
                .expect("registrable rules have native-eval output categories by construction");
            let out_value_ty = native_runtime_value_type(native_out_ty);
            let out_lit_label = lit(&generate_literal_label(native_out_ty).to_string());
            let safeified = crate::gen::native::rust_code_rewrite::safeify_and_wrap(rule.body);
            quote! {
                #[allow(non_snake_case)]
                fn #fn_name(
                    __args: &[::mettail_rholang_codegen::GroundTerm],
                ) -> ::core::option::Option<::mettail_rholang_codegen::GroundTerm> {
                    let [#(#arg_idents),*] = __args else {
                        return ::core::option::Option::None;
                    };
                    #(#binds)*
                    let __value: #out_value_ty = (#safeified)?;
                    // The output category's literal-leaf ground form — byte-identical to the
                    // subject reflection's literal arm (`"{Lit}({:?})"`) and to the D-stage
                    // contractum's bare form, so the emitted value decodes exactly as the
                    // report path's did.
                    ::core::option::Option::Some(::mettail_rholang_codegen::GroundTerm::new(
                        ::std::format!("{}({:?})", #out_lit_label, __value),
                        ::std::vec::Vec::new(),
                    ))
                }
            }
        })
        .collect();

    let lookup_arms: Vec<TokenStream> = rules
        .iter()
        .map(|rule| {
            let fired = lit(&rule.fired_rule_label);
            let fn_name = native_handler_fn_name(&rule.fired_rule_label);
            quote! { #fired => ::core::option::Option::Some(#fn_name), }
        })
        .collect();

    quote! {
        #(#eval_fns)*
        #(#handler_fns)*

        /// A-S3: the registrable machine-side handler for a native rule's Dovetail firing
        /// label, or `None` when the rule has no ground-parseable pure-native-scalar shape —
        /// the located term then DEFERS to the lazy-report path with a typed reason.
        fn __mettail_native_handler_for(
            __label: &str,
        ) -> ::core::option::Option<
            fn(
                &[::mettail_rholang_codegen::GroundTerm],
            ) -> ::core::option::Option<::mettail_rholang_codegen::GroundTerm>,
        > {
            match __label {
                #(#lookup_arms)*
                _ => ::core::option::Option::None,
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
    // Stage 4: the DEPTH-2 NESTED structural-AC firing sites — a nested non-linear AC rewrite (Ambient
    // `InRule`/`OutRule`, `RhoNetLoweredRule::NestedStructuralAcRewrite`) fires by rebuilding the WHOLE
    // nested operand `⟦{ n[{in(m,P),...q}], m[R], ...s }⟧` (or the `out` wrapper) from σ by walking its
    // OPERAND template, and each NESTED reduct element (a host-computed restructuring) from σ by
    // walking its REDUCT template, then passing them to `structural_ac_contract_call`, which sends
    // `channel!(⟦operand⟧, ⟦r0⟧, …, @out)` — the SAME firing seam as the flat structural-AC path.
    let nested_structural_ac_sites =
        mettail_rholang_codegen::rho_net_nested_structural_ac_injection_sites(language);

    let body = if sites.is_empty()
        && ac_sites.is_empty()
        && subst_sites.is_empty()
        && native_sites.is_empty()
        && native_fold_sites.is_empty()
        && comm_sites.is_empty()
        && structural_ac_sites.is_empty()
        && nested_structural_ac_sites.is_empty()
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

        // RETIRED for the in-Rho β (Stage 4 S-binder SLICE 2a): the Stage-3c host-CONTRACTUM subst
        // injection arms.
        //
        // These reflected the firing's CONTRACTUM (the host-computed reduct `RHS[σ]` after the
        // capture-avoiding substitution) at the scope slot, so the (then-forward-only) SubstRewrite
        // σ-receiver emitted the ALREADY-REDUCED term. The in-Rho β now COMPUTES the reduct with the
        // generated de-Bruijn TRS: the SubstRewrite σ-receiver is the β SEED
        // (`subst_seed_receiver_par`), which SENDS `^subst(⟦Z⟧, a, b, out)` with the RAW captured body
        // `b`; feeding it the host CONTRACTUM instead would double-substitute. So the in-Rho β fires
        // via the MATCH path (`rho_net_match_invocation_from_dovetail_to` → the automaton captures the
        // RAW body + arg → the seed), and a `Beta` firing routed to THIS host-σ dispatch body has no
        // arm and errors (`__other =>`), naming the rule. The arms are kept (commented) for reference
        // / a future σ-replay fallback, which would need a SEED-compatible RAW-σ injection (the raw
        // matched body, NOT the contractum). `subst_sites` still gates the `#body` shape (above).
        //
        // let subst_site_arms: Vec<TokenStream> = subst_sites
        //     .iter()
        //     .map(|site| {
        //         let label = lit(&site.rule_label);
        //         let channel = lit(&site.channel);
        //         let vars: Vec<LitStr> = site.lhs_var_order.iter().map(|var| lit(var)).collect();
        //         let scope_var = lit(&site.scope_var);
        //         quote! {
        //             #label => {
        //                 let __contractum = __justification.contractum.as_ref().ok_or_else(|| {
        //                     ::std::format!(
        //                         "Rho-net subst injection for language {} has no contractum for fired rule {}",
        //                         #language_lit, #label,
        //                     )
        //                 })?;
        //                 let __var_order: &[&str] = &[#(#vars),*][..];
        //                 let mut __args = ::std::vec::Vec::with_capacity(__var_order.len());
        //                 for __var in __var_order {
        //                     let __ground = if *__var == #scope_var {
        //                         __mettail_rho_net_to_ground(__contractum)
        //                     } else {
        //                         __mettail_rho_net_to_ground(
        //                             __mettail_rho_net_find_sigma(__justification, __var)?,
        //                         )
        //                     };
        //                     __args.push(::mettail_rholang_codegen::reflect_ground_term_par(
        //                         &__ground, __fingerprint,
        //                     ));
        //                 }
        //                 ::mettail_rholang_codegen::term_contract_call(#channel, __args, out_channel)
        //             },
        //         }
        //     })
        //     .collect();

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
        // sub-term's children — and pass the `m` reduct elements to `comm_contract_call`, which
        // sends `channel!(⟦bag⟧, ⟦r_0⟧, …, ⟦r_{m-1}⟧, @out)` for the installed Comm receiver (which
        // re-does the non-linear AC match `N ≡ N` and splices `r_0 | … | rest`).
        //
        // (D10) `reduct_slots` says where each element comes from, in RHS order: `Some(var)` is a
        // σ-DELIVERED LHS-element argument (read straight out of σ, exactly as the structural-AC
        // arm); `None` is the ONE HOST-COMPUTED substitution `cont[Q/y]`, recovered from the
        // firing's CONTRACTUM (the communicated bag) minus the residual `rest` AND minus the
        // σ-delivered elements — a multiset difference that leaves exactly the substitution. For the
        // ASYNCHRONOUS `m = 1` shape there are no σ-delivered elements, so the subtraction and the
        // emitted call are byte-identical to the pre-generalization form.
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
                let reduct_count = site.reduct_slots.len();
                // The σ-delivered slots, bound BEFORE the contractum subtraction (which must remove
                // them along with `rest` to isolate the host-computed substitution).
                let sigma_reduct_lits: Vec<LitStr> = site
                    .reduct_slots
                    .iter()
                    .flatten()
                    .map(|var| lit(var))
                    .collect();
                let sigma_reduct_count = sigma_reduct_lits.len();
                // One push per reduct slot, in RHS order.
                let mut sigma_cursor = 0usize;
                let reduct_pushes: Vec<TokenStream> = site
                    .reduct_slots
                    .iter()
                    .map(|slot| match slot {
                        ::core::option::Option::None => quote! {
                            __reducts.push(__subst_reduct.clone());
                        },
                        ::core::option::Option::Some(_) => {
                            let index = sigma_cursor;
                            sigma_cursor += 1;
                            quote! {
                                __reducts.push(__sigma_reducts[#index].clone());
                            }
                        },
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
                        // The σ-DELIVERED reduct elements (RHS order among themselves).
                        let mut __sigma_reducts =
                            ::std::vec::Vec::with_capacity(#sigma_reduct_count);
                        #(
                            __sigma_reducts.push(__mettail_rho_net_to_ground(
                                __mettail_rho_net_find_sigma(__justification, #sigma_reduct_lits)?,
                            ));
                        )*
                        // The HOST-COMPUTED substitution `cont[Q/y]` = the communicated bag (the
                        // firing's CONTRACTUM) minus the residual `rest` and minus the σ-delivered
                        // elements (multiset difference — exactly one element left).
                        let __contractum = __justification.contractum.as_ref().ok_or_else(|| {
                            ::std::format!(
                                "Rho-net Comm injection for language {} has no contractum for fired rule {}",
                                #language_lit, #label,
                            )
                        })?;
                        let __subst_reduct = __mettail_rho_net_comm_reduct(
                            &__mettail_rho_net_to_ground(__contractum),
                            &__rest.children,
                            &__sigma_reducts,
                        )
                        .ok_or_else(|| {
                            ::std::format!(
                                "Rho-net Comm injection for language {} could not recover the reduct for fired rule {}",
                                #language_lit, #label,
                            )
                        })?;
                        // The m reduct values, in RHS order.
                        let mut __reducts = ::std::vec::Vec::with_capacity(#reduct_count);
                        #(#reduct_pushes)*
                        ::mettail_rholang_codegen::comm_contract_call(
                            #channel, &__whole_bag, &__reducts, __fingerprint, out_channel,
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

        // Nested-structural-AC-rewrite arms (Stage 4, Ambient `InRule`/`OutRule`): rebuild the WHOLE
        // DEPTH-2 nested operand `⟦{ n[{in(m,P),...q}], m[R], ...s }⟧` (or the `out` wrapper) from σ by
        // walking its OPERAND template, and each NESTED reduct element (the host-computed
        // restructuring) from σ by walking its REDUCT template, then send
        // `channel!(⟦operand⟧, ⟦r0⟧, …, @out)` via the SAME `structural_ac_contract_call` seam. The
        // installed nested σ-receiver re-does the DEPTH-2 match + the cross-level `M ≡ M` guard and
        // splices `⟦r0⟧ | … | ...s`.
        let nested_structural_ac_site_arms: Vec<TokenStream> = nested_structural_ac_sites
            .iter()
            .map(|site| {
                let label = lit(&site.rule_label);
                let channel = lit(&site.channel);
                let operand_tokens = ac_template_tokens(&site.operand_template);
                let reduct_count = site.reduct_templates.len();
                let reduct_tokens: Vec<TokenStream> =
                    site.reduct_templates.iter().map(ac_template_tokens).collect();
                quote! {
                    #label => {
                        // σ → ground reconstruction closure (a missing σ variable fails closed).
                        let __find = |__name: &str|
                            -> ::core::option::Option<::mettail_rholang_codegen::GroundTerm> {
                            __mettail_rho_net_find_sigma(__justification, __name)
                                .ok()
                                .map(__mettail_rho_net_to_ground)
                        };
                        // The WHOLE nested operand, rebuilt from σ by walking the operand template.
                        let __operand_template = #operand_tokens;
                        let __operand =
                            ::mettail_rholang_codegen::instantiate_ac_reconstruct_template(
                                &__operand_template, &__find,
                            )
                            .ok_or_else(|| ::std::format!(
                                "Rho-net injection for language {} could not reconstruct the {} operand from σ",
                                #language_lit, #label,
                            ))?;
                        // The m NESTED reduct elements — each the host-computed restructuring rebuilt
                        // from σ by walking its reduct template.
                        let mut __reducts = ::std::vec::Vec::with_capacity(#reduct_count);
                        #(
                            {
                                let __reduct_template = #reduct_tokens;
                                __reducts.push(
                                    ::mettail_rholang_codegen::instantiate_ac_reconstruct_template(
                                        &__reduct_template, &__find,
                                    )
                                    .ok_or_else(|| ::std::format!(
                                        "Rho-net injection for language {} could not reconstruct a {} reduct from σ",
                                        #language_lit, #label,
                                    ))?,
                                );
                            }
                        )*
                        ::mettail_rholang_codegen::structural_ac_contract_call(
                            #channel, &__operand, &__reducts, __fingerprint, out_channel,
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
                // The firing's CONTRACTUM is the communicated bag
                // `op{ cont[Q/y], r_1, …, r_{m-1}, ...rest }`. Remove ONE occurrence of each
                // residual `rest` child AND of each σ-DELIVERED reduct element (multiset
                // difference); the single remaining element is the HOST-COMPUTED substitution
                // `cont[Q/y]` the Comm receiver splices back with the others and `rest`. `None` when
                // the shape is unexpected (fail-closed).
                //
                // (D10) `__sigma_reducts` is EMPTY for the asynchronous arity-1 reduct, so the
                // recovery reduces exactly to the original "contractum minus rest" difference.
                fn __mettail_rho_net_comm_reduct(
                    __contractum: &::mettail_rholang_codegen::GroundTerm,
                    __rest_children: &[::mettail_rholang_codegen::GroundTerm],
                    __sigma_reducts: &[::mettail_rholang_codegen::GroundTerm],
                ) -> ::core::option::Option<::mettail_rholang_codegen::GroundTerm> {
                    let mut __remaining: ::std::vec::Vec<::mettail_rholang_codegen::GroundTerm> =
                        __contractum.children.clone();
                    for __r in __rest_children.iter().chain(__sigma_reducts.iter()) {
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
                // RETIRED (Stage 4 S-binder SLICE 2a): the host-contractum subst dispatch arm — a
                // `Beta` firing now fires the in-Rho β via the MATCH path + the TRS SEED, so this
                // host-σ injection body has no `Beta` arm (it falls to `__other`). See the commented
                // `subst_site_arms` builder above.
                // #(#subst_site_arms)*
                #(#native_site_arms)*
                #(#native_fold_site_arms)*
                #(#comm_site_arms)*
                #(#structural_ac_site_arms)*
                #(#nested_structural_ac_site_arms)*
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

        // A-S2: the def + matching ruleset come from the per-source MEMOIZED artifacts
        // (`cached_in_rho_artifacts`) — the SAME derivation as before (`reconstruct_language_def`
        // → `compile_in_rho_matching_ruleset`, exactly as `rho_net_program()` does), computed once
        // per definition source instead of per invocation. E-3 T-LAZY: the ruleset is a
        // demand-forced cell now — `__artifacts.ruleset()` forces exactly the artifact this
        // path consumes (the unconsumed installed-par emission stays unforced, EM-1). The
        // ruleset's fingerprint + accept
        // channels are therefore STILL the ones the installed σ-receivers were compiled with (one
        // def, one fingerprint, no separate metadata read → no drift).
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
        let __artifacts = ::mettail_rholang_codegen::cached_in_rho_artifacts(__source)
            .map_err(|__err| {
                ::std::format!(
                    "language {} definition source did not reconstruct for in-Rho matching: {}",
                    #language_lit, __err,
                )
            })?;
        let __ruleset = __artifacts.ruleset();

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

        // Stage 4 (locate-all + multi-firing): the automaton LOCATES every redex — at ANY
        // position in the spread subject, and multiple simultaneously (P1 Thm 6.12 / P2 Thm 2) —
        // NOT just the root. `in_rho_match_all_sites_call_par` spreads the whole reflected
        // subject ONCE and co-installs a positional network at every position whose head is a
        // rule LHS root (the ν-free `⌜(ρ,ℓ)⌝` site paths), each accept firing the σ-receiver on
        // `out_channel`. So a NESTED redex (the redex is a sub-term, not the whole subject) and
        // MULTIPLE redexes both match + fire IN RHO — the root-rooted + single-redex fallback is
        // retired. Only a NESTED-App-entry ruleset with ≥2 located redexes (whose descents could
        // contend across co-installed sites) fails closed to the σ-replay driver; a flat-only
        // ruleset (SwapDemo) locates ALL redexes in Rho, and a single nested-pattern redex still
        // matches. A normal form locates 0 sites (the bare spread, a no-op).
        let (mut __call, _sites) = ::mettail_rholang_codegen::in_rho_match_all_sites_call_par(
            __ruleset,
            &__subject,
            "site0",
            out_channel,
        )
        .map_err(|__err| {
            ::std::format!(
                "in-Rho match for language {} could not serialize the locate-all match call: {:?}",
                #language_lit, __err,
            )
        })?;

        // Stage 4 (S-native): co-install a value-carrying bridge per LOCATED native firing. The
        // automaton has already MATCHED the native `NativeProc` head + CAPTURED its structural args
        // in Rho (the located accept routes to the entry's trigger channel — the STRUCTURAL DISPATCH
        // moved in Rho); the bridge binds those captures (they only GATE the delivery) and forwards
        // the trusted host handler's VALUE — the firing's CONTRACTUM, NOT the report σ — on the
        // dispatch channel, where the installed dispatch receiver emits it on `@out`. So the redex
        // LOCATION is the automaton's; only the native VALUE stays host-supplied (the inherent
        // `NativeSystemProcessBoundary` — BigInt / pow / factorial is outside Rho's arithmetic).
        if !__ruleset.native_dispatch.is_empty() {
            fn __mettail_rho_net_to_ground(
                __subterm: &mettail_runtime::RuntimeReflectedSubterm,
            ) -> ::mettail_rholang_codegen::GroundTerm {
                ::mettail_rholang_codegen::GroundTerm::new(
                    __subterm.constructor.clone(),
                    __subterm.children.iter().map(__mettail_rho_net_to_ground).collect(),
                )
            }
            // The reflection fingerprint the installed dispatch receiver was compiled with (the
            // install boundary requires `metadata().definition_fingerprint() ==
            // plan.definition_fingerprint()`), so the forwarded value decodes coherently.
            let __native_fingerprint = <#language_struct as mettail_runtime::Language>::metadata(
                &#language_struct,
            )
            .definition_fingerprint()
            .ok_or_else(|| {
                ::std::format!(
                    "language {} has no definition fingerprint for in-Rho native value reflection",
                    #language_lit,
                )
            })?;

            let mut __native_firings = 0usize;
            for __justification in &report.rewrite_justifications {
                let ::core::option::Option::Some(__dispatch) = __ruleset
                    .native_dispatch
                    .iter()
                    .find(|__d| __d.fired_rule_label == __justification.rule_label)
                else {
                    continue;
                };
                // A single located native firing delivers a single host value on one trigger; ≥2
                // native firings share the per-rule trigger channel, so their value bridges would
                // cross-talk — fail closed to the host-matched σ-replay driver, which replays each
                // firing as its own atomic COMM (correct, exactly the nested-multi-site fallback).
                __native_firings += 1;
                if __native_firings > 1 {
                    return ::core::result::Result::Err(::std::format!(
                        "in-Rho native match for language {} handles a single native firing per call; \
                         the report fired {} native rewrites (deferring to σ-replay)",
                        #language_lit, __native_firings,
                    ));
                }
                let __contractum = __justification.contractum.as_ref().ok_or_else(|| {
                    ::std::format!(
                        "in-Rho native match for language {}: fired native rule {} has no contractum",
                        #language_lit, __justification.rule_label,
                    )
                })?;
                let __value = ::mettail_rholang_codegen::reflect_ground_term_par(
                    &__mettail_rho_net_to_ground(__contractum),
                    __native_fingerprint,
                );
                let __bridge = ::mettail_rholang_codegen::native_locate_bridge_par(
                    &__dispatch.trigger_channel,
                    __dispatch.arity,
                    &__dispatch.dispatch_channel,
                    __value,
                );
                __call = __call.append(__bridge);
            }
        }

        ::core::result::Result::Ok(::mettail_rholang_codegen::RhoNetInjectionInvocation {
            call: __call,
            out_channel: out_channel.to_string(),
        })
    };

    // A-S2 (D-stage demotion) + A-S3 (native dispatch boundary tightening): the REPORT-FREE
    // match body — `match_body` minus every report read. No `assert_complete` (there is no
    // report), no fired-rule gate (the STATIC gate `in_rho_static_gate` decides admission
    // term-independently: every FIREABLE rewrite must be matchable in Rho, congruence-premise
    // rewrites exempt — they never fire). Native site counts still come from LOCATED sites over
    // the reflected subject (never report firings), but A-S3 ADMITS them: the body registers
    // one machine-side handler contract per located native rule (the trusted evaluator = the
    // rule's own `![…] fold` body, run by the MACHINE's dispatch COMM at COMM time — no
    // host-pre-computed contractum rides the call `Par`) and co-installs one contract-call
    // bridge per located site; only a native rule with NO registrable handler still defers,
    // with its typed reason. Everything else — the M-reflect subject reflection, the memoized
    // ruleset, and the locate-all `∏ network_ℓ ‖ spread` call — is the `match_body` code.
    let native_handlers = native_handler_table(language);
    // A-S5.4b: the REPORT-FREE bodies (this match-free body + the drive body below) reflect the
    // BOUNDARY-CANONICALIZED subject for a float-bearing language; byte-identical for every other
    // language (`reflect_subject_binding_boundary_canonicalized`).
    let reflect_subject_report_free = reflect_subject_binding_boundary_canonicalized(language);
    let match_free_body = quote! {
        // M-reflect: the subject is the WHOLE input `term`, reflected STRUCTURALLY to a
        // `GroundTerm` (`__subject`) — never a report σ (this path has no report at all).
        let out_channel = out_channel.as_ref();
        #reflect_subject_report_free

        // A-S3: the machine-side native handler table — the per-category ground evaluators,
        // the per-rule trusted handlers (the same `![…] fold` bodies the D-stage dispatcher
        // runs), and the label-keyed lookup the native admission block below uses.
        #native_handlers

        // The per-source MEMOIZED artifacts (same derivation + coherence argument as the
        // report-carrying match body above).
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
        let __artifacts = ::mettail_rholang_codegen::cached_in_rho_artifacts(__source)
            .map_err(|__err| {
                ::std::format!(
                    "language {} definition source did not reconstruct for in-Rho matching: {}",
                    #language_lit, __err,
                )
            })?;
        let __ruleset = __artifacts.ruleset();

        // A-S2 STATIC capability gate (the term-independent strengthening of FV ix
        // `install_admits`): fail closed BEFORE any Rho reduction if ANY fireable rewrite is
        // skipped from in-Rho matching — no report needed to know the located redexes are all
        // matchable.
        if let ::core::result::Result::Err(__deferred) =
            ::mettail_rholang_codegen::in_rho_static_gate(__ruleset, &__artifacts.def)
        {
            let __labels: ::std::vec::Vec<::std::string::String> = __deferred
                .iter()
                .map(|__entry| ::std::format!("{} ({:?})", __entry.rule_label, __entry.reason))
                .collect();
            return ::core::result::Result::Err(::std::format!(
                "in-Rho static gate for language {} rejects: fireable rule(s) not matchable in Rho: {}",
                #language_lit, __labels.join(", "),
            ));
        }

        // The SAME locate-all `∏ network_ℓ ‖ spread` call as the report-carrying match body: the
        // automaton LOCATES every redex (nested + multiple) and each accept fires the σ-receiver
        // on `out_channel`. A normal form locates 0 sites (the bare spread, a no-op). A nested
        // ruleset with ≥2 located sites fails closed here (`NestedEntryMultiSite` → the
        // lazy-report σ-replay), identical to the report-carrying path.
        let (mut __call, _sites) = ::mettail_rholang_codegen::in_rho_match_all_sites_call_par(
            __ruleset,
            &__subject,
            "site0",
            out_channel,
        )
        .map_err(|__err| {
            ::std::format!(
                "in-Rho match for language {} could not serialize the locate-all match call: {:?}",
                #language_lit, __err,
            )
        })?;

        // A-S3 (native dispatch boundary tightening): located native sites ADMIT. Native site
        // counts still come from LOCATED sites over the reflected subject (never report firings
        // — `located_native_site_count_for`, the per-rule refinement of A-S2's
        // `located_native_site_count`), but a located site now REGISTERS the rule's machine-side
        // handler contract and co-installs a CONTRACT-CALL bridge instead of deferring:
        //
        //  * one `NativeHandlerSpec` per located native RULE — the trusted evaluator (the
        //    rule's own `![…] fold` body, `__mettail_native_handler_for`) plus the reserved
        //    contract channel `[0xF1, rule_index]`. The runtime's invocation-compiler bracket
        //    drains the specs into system-process `Definition`s injected via
        //    `extra_system_processes` (the Tier-3 held-fold trampoline seam), so the MACHINE's
        //    dispatch COMM invokes the evaluator at COMM time;
        //  * one value-free `native_locate_contract_bridge_par` per located SITE — the accept's
        //    captured σ operands forward to the contract channel, and the handler `produce`s
        //    `[value, out]` on the rule's dispatch channel, where the installed σ-receiver
        //    consumes the RETURNED value. The bridges are identical pure forwarders (no
        //    per-site value), so — unlike the report path's single-native-firing value bridge —
        //    ≥2 located sites CANNOT cross-talk: each accept drives its own handler invocation.
        //
        // No host-pre-computed contractum rides the call `Par` (`NativeSystemProcessBoundary.v`
        // section 4). FAIL-CLOSED residue: a native rule with NO registrable machine-side
        // handler (a non-scalar or non-ground-parseable native shape) still DEFERS to the
        // lazy-report path with its typed reason, where the report-carrying value bridge (or
        // the σ-replay driver) handles it exactly as before.
        let mut __native_specs: ::std::vec::Vec<::mettail_rholang_codegen::NativeHandlerSpec> =
            ::std::vec::Vec::new();
        for (__native_index, __dispatch) in __ruleset.native_dispatch.iter().enumerate() {
            let __site_count = ::mettail_rholang_codegen::located_native_site_count_for(
                __ruleset,
                &__subject,
                &__dispatch.bare_label,
            );
            if __site_count == 0 {
                continue;
            }
            let ::core::option::Option::Some(__evaluator) =
                __mettail_native_handler_for(&__dispatch.fired_rule_label)
            else {
                return ::core::result::Result::Err(::std::format!(
                    "in-Rho report-free match for language {} located {} native site(s) for rule \
                     {} with no registrable machine-side handler (a non-scalar or \
                     non-ground-parseable native shape); the native value requires the host \
                     D-stage handler (deferring to the report path)",
                    #language_lit, __site_count, __dispatch.fired_rule_label,
                ));
            };
            let ::core::result::Result::Ok(__rule_index) = u8::try_from(__native_index) else {
                return ::core::result::Result::Err(::std::format!(
                    "in-Rho report-free match for language {} has native rule index {} beyond \
                     the reserved contract band (max {}); deferring to the report path",
                    #language_lit, __native_index, u8::MAX,
                ));
            };
            // ★ #36 S4: the contract channel is FINGERPRINT-SCOPED. `__rule_index` alone made
            // two co-installed native-bearing languages share `[0xF1, 0]`, and f1r3node's
            // dispatch table silently keeps whichever installed last.
            let __native_channel = ::mettail_rholang_codegen::native_contract_channel(
                __rule_index,
                &__ruleset.language_fingerprint,
            );
            for _ in 0..__site_count {
                __call = __call.append(
                    ::mettail_rholang_codegen::native_locate_contract_bridge_par(
                        &__dispatch.trigger_channel,
                        __dispatch.arity,
                        __native_channel.clone(),
                    ),
                );
            }
            __native_specs.push(::mettail_rholang_codegen::NativeHandlerSpec {
                urn: ::mettail_rholang_codegen::native_handler_urn(
                    &__ruleset.language_fingerprint,
                    &__dispatch.fired_rule_label,
                ),
                fired_rule_label: __dispatch.fired_rule_label.clone(),
                bare_label: __dispatch.bare_label.clone(),
                arity: __dispatch.arity,
                fingerprint: __ruleset.language_fingerprint.clone(),
                rule_index: __rule_index,
                dispatch_channel: __dispatch.dispatch_channel.clone(),
                evaluator: ::std::sync::Arc::new(__evaluator),
            });
        }
        // Record ONLY after every fallible step: a deferral return above records nothing (and
        // the runtime bracket would discard a stray record anyway).
        if !__native_specs.is_empty() {
            ::mettail_rholang_codegen::record_pending_native_handler_specs(__native_specs);
        }

        ::core::result::Result::Ok(::mettail_rholang_codegen::RhoNetInjectionInvocation {
            call: __call,
            out_channel: out_channel.to_string(),
        })
    };

    // Stage 4 (S-contextual): the CONTEXTUAL injection body — the third arm of the σ-injection
    // F-function family (base | AC | contextual), now MATCHING IN RHO. Unlike the base/AC arms (keyed
    // on the fired rule's OWN σ-receiver), a congruence rule fires no explicit Dovetail rule (the
    // e-graph congruence closure closes the outer context `K` implicitly), so its atomic JOIN is fed
    // by the PREMISE redex — but that premise redex is now MATCHED + REDUCED IN RHO: the base
    // automaton LOCATES the hole's premise redex from the ONE spread of the structurally reflected
    // subject (M-reflect, the nested-App descent through `K`'s spine) and fires its σ-receiver, and
    // the hole bridge routes that IN-RHO reduced hole `T` to the join's premise channel, where the
    // installed `contextual_join_receiver_par` reassembles `⟦K'⟧` on `@out`. The reduced hole is the
    // automaton's NESTED FIRING, NOT `reconstruct_contractum` from the report σ (which is retired
    // from this path — the report survives only to GATE which rules fired). Sub-slice 1 scope = a
    // single UNARY congruence rule closed by a single located hole redex; 0/≥2 congruence rules, a
    // non-unary context, or a differing hole count fail closed (the n-ary hole routing is the next
    // sub-slice). Host residue: a premise SEMANTIC-PREDICATE guard stays off-machine (INV-14) — the
    // premise's STRUCTURAL reduction is in Rho, only its value-predicate guard is host.
    let contextual_body = quote! {
        report.assert_complete().map_err(|status| {
            ::std::format!(
                "contextual match for language {} requires a complete Dovetail report, got {}",
                #language_lit, status,
            )
        })?;
        // M-reflect (Stage 4, S-contextual): the outer context spine `K` IS the whole input `term`,
        // reflected STRUCTURALLY to a `GroundTerm` (`__subject`) with the hole position(s) — NOT
        // rebuilt from the report σ. The base automaton then LOCATES the hole's premise redex in the
        // spread + EMITS its reduced value, so the host no longer reconstructs the reduced hole for
        // the contextual MATCH path.
        let out_channel = out_channel.as_ref();
        #reflect_subject

        // A-S2: the def + matching ruleset come from the per-source MEMOIZED artifacts
        // (`cached_in_rho_artifacts`) — the SAME derivation as before, computed once per
        // definition source instead of per invocation (E-3 T-LAZY: `__artifacts.ruleset()`
        // demand-forces exactly this path's artifact) — so the contextual join's premise
        // channels + the ruleset's fingerprint/accept channels are the ones the installed join +
        // σ-receivers were compiled with (one def, one fingerprint, no separate metadata read →
        // no drift).
        let __source = <#language_struct as mettail_runtime::Language>::metadata(
            &#language_struct,
        )
        .definition_source()
        .ok_or_else(|| {
            ::std::format!(
                "language {} has no definition source for contextual match",
                #language_lit,
            )
        })?;
        let __artifacts = ::mettail_rholang_codegen::cached_in_rho_artifacts(__source)
            .map_err(|__err| {
                ::std::format!(
                    "language {} definition source did not reconstruct for contextual match: {}",
                    #language_lit, __err,
                )
            })?;
        let __ruleset = __artifacts.ruleset();

        // Capability gate (FV ix `install_admits`): fail closed BEFORE any Rho reduction if any
        // FIRED rule (the premise firing that closes the context) is skipped from in-Rho matching —
        // a contextual rule's hole is reduced by its PREMISE's σ-receiver, so the premise rule must
        // be matchable in Rho for the hole to fire on the reducer.
        let __fired: ::std::vec::Vec<&str> = report
            .rewrite_justifications
            .iter()
            .map(|__justification| __justification.rule_label.as_str())
            .collect();
        if let ::core::option::Option::Some(__skipped) =
            ::mettail_rholang_codegen::in_rho_match_gate_reject(&__ruleset.deferred, &__fired)
        {
            return ::core::result::Result::Err(::std::format!(
                "contextual match gate for language {} rejects: fired rule {} is not matchable in Rho ({:?})",
                #language_lit, __skipped.rule_label, __skipped.reason,
            ));
        }

        // Build the contextual match call: the base automaton LOCATES the hole's premise redex in
        // the ONE spread (the nested-App descent through `K`'s spine) and fires its σ-receiver; the
        // hole bridge routes the IN-RHO reduced hole to the join's premise channel, where the
        // installed `contextual_join_receiver_par` reassembles `⟦K'⟧` on `@out` — one atomic JOIN
        // COMM (INV-6). The reduced hole is the automaton's nested firing, NOT `reconstruct_
        // contractum` from the report σ.
        let __call = ::mettail_rholang_codegen::contextual_match_call_par(
            __ruleset,
            &__subject,
            "site0",
            out_channel,
        )
        .map_err(|__err| {
            ::std::format!(
                "contextual match for language {} could not serialize the contextual match call: {:?}",
                #language_lit, __err,
            )
        })?;

        ::core::result::Result::Ok(::mettail_rholang_codegen::RhoNetInjectionInvocation {
            call: __call,
            out_channel: out_channel.to_string(),
        })
    };

    // A-S5.2 (plan v2 §4.4 / F9, amendment AM-4): the in-Rho QUIESCENCE-DRIVER seed
    // invocation — emitted ONLY for languages opted into the driver via the
    // codegen-visible `DRIVE_OPT_IN` const (consulted HERE, at expansion time, exactly as
    // AM-4 mandates), so a non-opted-in language's generated module is BYTE-IDENTICAL to
    // pre-A-S5.2 (the SwapDemo pin below) and `rho_net_match_invocation_to` is untouched
    // for every language. The generated body re-checks the FULL `drive_admissible`
    // predicate per exec against the memoized artifacts (fail-closed: an opted-in but
    // not-yet-supported language errors typed instead of seeding a channel with no
    // installed receivers; A-S5.5 flipped Ambient's predicate to Admitted — the AC
    // carrier arms — with NO change to this emission, exactly the AM-4 design).
    let drive_opted_in = mettail_rholang_codegen::DRIVE_OPT_IN.contains(&language_name.as_str());
    // A-S5.8 (decision Q-SEED = S2): a FLOAT-BEARING language's drive fn assembles the
    // FLOAT-ROUTED seed (`rho_net_drive_float_invocation` — `new rf { ⌜^float⌝!(⟦t⟧, rf)
    // | for(@cf <- rf){ ⌜^drive⌝!(cf, fuel, @out) } }`) so the installed `^float`
    // dispatcher canonicalizes the subject IN-RHO before the first drive frame; the host
    // boundary float above is RETAINED (defense-in-depth + the ONLY place the NewComm
    // display ordering exists — load-bearing for the run-order-sensitive α goldens,
    // F8-AM-5b; under S2 the in-Rho seed float is an identity pass on the already-
    // canonical subject). The expansion-time condition is the SAME gate the float family
    // installs under (`language_is_float_bearing` = the macros-side
    // `should_emit_binder_congruence` restatement ∧ `equations_boundary_canonicalizable`;
    // drive admission is re-checked in the body), so a float-routed seed always has its
    // `^float` receivers. A NON-float language's drive fn is BYTE-IDENTICAL to pre-A-S5.8
    // (the F8-AM-5c Lambda fn-item pin).
    let drive_float_seeded = drive_opted_in
        && crate::gen::runtime::binder_congruence::should_emit_binder_congruence(language)
        && mettail_rholang_codegen::equations_boundary_canonicalizable(language);
    let drive_invocation_assembler = if drive_float_seeded {
        quote! { ::mettail_rholang_codegen::rho_net_drive_float_invocation }
    } else {
        quote! { ::mettail_rholang_codegen::rho_net_drive_invocation }
    };
    let drive_fn = if drive_opted_in {
        quote! {
            /// A-S5.2: seed the in-Rho QUIESCENCE DRIVER for the whole subject `term` —
            /// the report-free, locate-all-free execution surface for driver-admitted
            /// languages. Reflects the subject structurally (M-reflect), gates admission
            /// (the A-S2 static gate PLUS the full
            /// [`drive_admissible`](mettail_rholang_codegen::drive_admissible) predicate,
            /// both against the per-source memoized artifacts), and assembles the seed
            /// `⌜^drive⌝!(⟦term⟧, fuel₀, @out)` plus the fingerprint-derived observation
            /// channel names. The installed program's persistent `^drive` receiver family
            /// then matches, fires (through the existing σ ABI), re-drives every
            /// contractum, and rests the quiescent term on `out` — the resting-term /
            /// ledger / typed-error / fuel channels are read back with
            /// `DriveObservationChannels` (rholang-runtime).
            pub fn rho_net_drive_invocation_to(
                term: &dyn mettail_runtime::Term,
                out_channel: impl ::core::convert::AsRef<str>,
            ) -> ::core::result::Result<
                ::mettail_rholang_codegen::RhoNetDriveInvocation,
                ::std::string::String,
            > {
                let out_channel = out_channel.as_ref();
                #reflect_subject_report_free

                let __source = <#language_struct as mettail_runtime::Language>::metadata(
                    &#language_struct,
                )
                .definition_source()
                .ok_or_else(|| {
                    ::std::format!(
                        "language {} has no definition source for the in-Rho drive",
                        #language_lit,
                    )
                })?;
                let __artifacts = ::mettail_rholang_codegen::cached_in_rho_artifacts(__source)
                    .map_err(|__err| {
                        ::std::format!(
                            "language {} definition source did not reconstruct for the \
                             in-Rho drive: {}",
                            #language_lit, __err,
                        )
                    })?;
                let __ruleset = __artifacts.ruleset();

                // The A-S2 STATIC capability gate (term-independent), exactly as the
                // report-free match body runs it: fail closed BEFORE any Rho reduction.
                if let ::core::result::Result::Err(__deferred) =
                    ::mettail_rholang_codegen::in_rho_static_gate(__ruleset, &__artifacts.def)
                {
                    let __labels: ::std::vec::Vec<::std::string::String> = __deferred
                        .iter()
                        .map(|__entry| {
                            ::std::format!("{} ({:?})", __entry.rule_label, __entry.reason)
                        })
                        .collect();
                    return ::core::result::Result::Err(::std::format!(
                        "in-Rho drive for language {} rejects: fireable rule(s) not \
                         matchable in Rho: {}",
                        #language_lit, __labels.join(", "),
                    ));
                }

                // The FULL driver-admission predicate (plan v2 §4.4) — a pure function of
                // the memoized `(def, ruleset)`, so this per-exec re-check costs a cache
                // hit and can never drift from the install-time recorded disposition.
                match ::mettail_rholang_codegen::drive_admissible(
                    &__artifacts.def,
                    __ruleset,
                ) {
                    ::mettail_rholang_codegen::DriveAdmission::Admitted => {},
                    ::mettail_rholang_codegen::DriveAdmission::NotRequested => {
                        return ::core::result::Result::Err(::std::format!(
                            "language {} is not opted into the in-Rho quiescence driver",
                            #language_lit,
                        ));
                    },
                    ::mettail_rholang_codegen::DriveAdmission::Unsupported {
                        reason: __reason,
                    } => {
                        return ::core::result::Result::Err(::std::format!(
                            "in-Rho drive for language {} is not admitted: {}",
                            #language_lit, __reason,
                        ));
                    },
                }

                let __subject_par = ::mettail_rholang_codegen::reflect_ground_term_par(
                    &__subject,
                    &__ruleset.language_fingerprint,
                );
                ::core::result::Result::Ok(#drive_invocation_assembler(
                    &__ruleset.language_fingerprint,
                    __subject_par,
                    out_channel,
                ))
            }
        }
    } else {
        quote! {}
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

            /// Build the in-Rho set-automaton MATCH call that LOCATES EVERY redex of an
            /// already complete Dovetail report — at ANY position in the subject term, and
            /// multiple simultaneously (Stage 4, P1 Thm 6.12 / P2 Thm 2): compile the
            /// language's in-Rho matching ruleset, GATE (fail closed if any fired rule is not
            /// matchable in Rho — FV (ix) `install_admits`), STRUCTURALLY reflect the whole
            /// subject `term` (M-reflect, NOT the report σ), and assemble ONE
            /// `∏ network_ℓ ‖ spread` call — a positional network co-installed at every redex
            /// position `ℓ` over one spread — the runtime runs against the installed
            /// σ-receiver program. Unlike [`Self::rho_net_invocation_from_dovetail_to`] (which
            /// host-computes σ and injects it), the automaton re-does the MATCHING +
            /// LOCATION on the interpreter (the `$\tau$` `sa:` COMMs) and each located site's
            /// accept fires the σ-receiver — so a NESTED redex and MULTIPLE redexes all fire
            /// IN RHO, the observed channel collecting every located redex's contractum. The
            /// default backend (`swapdemo_backed`) calls this, falling back to the σ-replay
            /// driver ONLY when the gate rejects (a fired rule is off-machine: AC / contextual
            /// / binder / native) or the ruleset has a nested-App entry (co-install
            /// contention) — never for a flat-rule language's nested/multiple redexes.
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

            /// A-S2 (D-stage demotion) + A-S3 (native dispatch boundary tightening): the
            /// REPORT-FREE in-Rho set-automaton MATCH call —
            /// [`Self::rho_net_match_invocation_from_dovetail_to`] with every Dovetail-report
            /// read removed, so the admitted path runs with ZERO Dovetail work.
            ///
            /// Differences from the report-carrying body (and nothing else):
            /// - no `assert_complete` — there is no report;
            /// - the fired-rule gate is replaced by the STATIC gate
            ///   (`in_rho_static_gate`): term-independent admission — every FIREABLE rewrite
            ///   must be matchable in Rho (congruence-premise rewrites are exempt: they never
            ///   appear as fired rules, the e-graph closes contexts implicitly);
            /// - native sites are counted from LOCATED positions
            ///   (`located_native_site_count_for` over the structurally reflected subject)
            ///   instead of report firings, and — A-S3 — a located native site ADMITS: the
            ///   body registers the rule's machine-side handler contract (a
            ///   `NativeHandlerSpec` the runtime's invocation-compiler bracket drains into an
            ///   `extra_system_processes` `Definition` — the Tier-3 held-fold trampoline
            ///   seam) and co-installs one value-free contract-call bridge
            ///   (`native_locate_contract_bridge_par`) per located site, so the MACHINE's
            ///   dispatch COMM invokes the trusted evaluator (the rule's own `![…] fold`
            ///   body) on the automaton-captured σ AT COMM TIME and the rule's σ-receiver
            ///   consumes the RETURNED value. No host-pre-computed contractum rides the call
            ///   `Par`, and ≥2 located native sites admit (each site drives its own handler
            ///   invocation — the identical bridges cannot cross-talk). Only a native rule
            ///   with NO registrable machine-side handler (a non-scalar or
            ///   non-ground-parseable native shape) still fails closed, with its typed
            ///   reason.
            ///
            /// Every `Err` is a DEFERRAL to the lazy-report path: the runtime wrapper then
            /// LAZILY builds the checked Dovetail report and takes today's report-carrying
            /// paths (the value-bridged match, the σ-replay driver, or the semantic-predicate
            /// payload), so no input loses its existing behavior — the admitted subset simply
            /// stops paying for the D-stage. The def + ruleset come from the per-source
            /// memoized artifacts (`cached_in_rho_artifacts`), so repeated execs also stop
            /// paying reconstruct+compile.
            pub fn rho_net_match_invocation_to(
                term: &dyn mettail_runtime::Term,
                out_channel: impl ::core::convert::AsRef<str>,
            ) -> ::core::result::Result<
                ::mettail_rholang_codegen::RhoNetInjectionInvocation,
                ::std::string::String,
            > {
                #match_free_body
            }

            #drive_fn

            /// Build the CONTEXTUAL (congruence) JOIN injection that MATCHES IN RHO for an already
            /// complete Dovetail report (Stage 4, S-contextual) — the third arm of the σ-injection
            /// F-function family (base | AC | contextual).
            ///
            /// A congruence rewrite `⟦ S ~> T |- K(S) ~> K'(T) ⟧` fires no explicit Dovetail rule
            /// (the e-graph congruence closure closes the outer context `K` implicitly), so unlike
            /// [`Self::rho_net_invocation_from_dovetail_to`] (which dispatches on the fired rule's OWN
            /// σ-receiver) its atomic JOIN is fed by the PREMISE redex — but that premise redex is now
            /// MATCHED + REDUCED IN RHO, not host-reconstructed. This STRUCTURALLY reflects the whole
            /// subject `term` (M-reflect, the outer context spine `K` with its hole positions, NOT the
            /// report σ), compiles + GATES the in-Rho matching ruleset, and assembles the contextual
            /// match call: the base automaton LOCATES the hole's premise redex from the ONE spread
            /// (the nested-App descent through `K`'s spine) and fires its σ-receiver, and the hole
            /// bridge routes that IN-RHO reduced hole to the join's premise channel, where the
            /// installed
            /// [`contextual_join_receiver_par`](mettail_rholang_codegen::contextual_join_receiver_par)
            /// binds it and emits `⟦K'⟧` on `@out` — one atomic JOIN COMM on the reducer (INV-6). So
            /// the reduced hole is the automaton's NESTED FIRING, never the report σ. Returns codegen
            /// types (`RhoNetInjectionInvocation`) so the language crate takes no Rho runtime
            /// dependency.
            ///
            /// Sub-slice 1 scope: exactly one UNARY congruence rule closed by a single located hole
            /// redex; 0/≥2 congruence rules, a non-unary context, or a differing located-hole count
            /// fail closed (the n-ary hole routing is the next sub-slice). Host residue: a premise
            /// SEMANTIC-PREDICATE guard stays off-machine (INV-14) — the premise's STRUCTURAL
            /// reduction runs in Rho, only its value-predicate guard is host.
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

    /// Render the production reflection engine, not the retained recursive reference emitter.
    /// Keeping generator tests on this helper prevents the two implementations from drifting
    /// while the reference remains available for differential-equivalence work.
    fn reflect_pda_tokens(language: &LanguageDef, category: &Ident) -> String {
        let support = reflect_pda_support(language);
        let category = reflect_category_pda_fn(language, category);
        quote! { #support #category }.to_string()
    }

    /// **A-7.** A constructor carrying an `m:Ident` token-text field REFLECTS — it emits an
    /// `Ok(GroundTerm)` arm whose token-text position is the reserved nullary leaf
    /// `^ident("…")` — while a constructor carrying a `*flt(…)` guest-body field still fails
    /// reflection CLOSED with the typed reason (routing that firing to σ-replay).
    ///
    /// ★ MUTATION IT REJECTS: restoring `is_structural_category_field` as the admission test
    /// (i.e. deleting the `ReflectField::IdentText` arm) puts `Named`/`Call` back on the
    /// fail-closed arm, and `named_reflect`'s `Ok` assertion goes red.
    ///
    /// ★ CONTROL, so it cannot pass by admitting everything: the SAME reflection walk, on the
    /// SAME language, must still refuse `Guest`. An `Arc<FltNode>` is an opaque foreign
    /// payload with no ground image; inventing a `{:?}` tag for it would make the reflection
    /// look total while giving the in-Rho automaton nothing it can match on.
    ///
    /// ⚠ The expected tag is DERIVED from the ABI constant, never re-spelled — a test that
    /// re-spells a reserved tag is a second, unversioned copy of the ABI (the exact defect
    /// that made the Peano assertion in this module test for a user constructor named `Z`).
    #[test]
    fn token_text_field_reflects_while_guest_body_still_fails_closed() {
        let language = parse(
            r#"
                name: IdentReflectGen,
                types { Proc }
                tokens {
                    FltOpenBacktick = "[a-z]+`" push(flt_body) ;
                    raw mode flt_body {
                        FltCloseBacktick = "`" pop ;
                        GuestChunk = "[^`]+" ;
                    }
                }
                terms {
                    Nil . |- "0" : Proc ;
                    Named . m:Ident |- "tag" m : Proc ;
                    Call . recv:Proc, m:Ident |- recv "." m : Proc ;
                    Guest . |- *flt(node, FltOpenBacktick, FltCloseBacktick) : Proc ;
                }
                equations {}
                rewrites { Drop . |- (Named m) ~> (Nil) ; }
            "#,
        );
        let reflect = reflect_pda_tokens(&language, &format_ident!("Proc"));
        let ident_tag = format!("{:?}", mettail_rholang_codegen::IDENT_TEXT_REFLECT_LABEL);

        // The token-text positions reflect, through the reserved `^ident` tag.
        assert!(
            reflect.contains(&ident_tag),
            "a token-text field must reflect to the reserved {ident_tag} leaf; got:\n{reflect}",
        );
        // `Call`'s category child still RECURSES — the mixed variant reflects both shapes,
        // so admitting the text position did not turn the whole variant into a leaf.
        assert!(
            reflect.contains("__MettailReflectTask :: VisitProc"),
            "the mixed variant's category child must enqueue a structural visit; got:\n{reflect}",
        );
        // CONTROL: the guest-body constructor keeps the fail-closed arm.
        assert!(
            reflect.contains("constructor Guest has a non-structural field"),
            "a guest-body field must still fail reflection CLOSED (σ-replay); got:\n{reflect}",
        );
        // ANTI-VACUITY: the fail-closed message must NOT name the token-text constructors.
        for refused in ["constructor Named has a", "constructor Call has a"] {
            assert!(
                !reflect.contains(refused),
                "a token-text constructor must not be on the fail-closed arm ({refused}); \
                 got:\n{reflect}",
            );
        }
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

    /// Extract one `pub fn <name>` item substring from an expansion's token string — from
    /// the fn's `pub fn <name>` head through its final closing brace (the slice to the
    /// NEXT `pub fn ` also captures the FOLLOWING item's leading `#[doc]` attributes, so
    /// the item boundary is the last `}` before it). Token-level (the
    /// `TokenStream::to_string` spacing), sufficient for the AM-4 byte-identity pins.
    fn extract_fn_item<'a>(tokens: &'a str, fn_name: &str) -> &'a str {
        let head = format!("pub fn {fn_name}");
        let start = tokens
            .find(&head)
            .unwrap_or_else(|| panic!("expansion must contain `{head}`"));
        let rest = &tokens[start + head.len()..];
        let end = rest
            .find("pub fn ")
            .map_or(tokens.len(), |offset| start + head.len() + offset);
        let slice = &tokens[start..end];
        let brace = slice
            .rfind('}')
            .expect("a fn item ends with a closing brace");
        &slice[..=brace]
    }

    /// The production-Lambda-shaped grammar under a configurable name (the AM-4 pin
    /// subject: name `Lambda` IS in `DRIVE_OPT_IN`; any other name is not).
    fn lambda_shaped_fragment(name: &str) -> LanguageDef {
        parse(&format!(
            r#"
                name: {name},
                types {{ Term }},
                terms {{
                    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
                }},
                equations {{}},
                rewrites {{
                    Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ;
                    AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N) ;
                    AppCongR . | N0 ~> N1 |- (App M N0) ~> (App M N1) ;
                    LamCong . | S ~> T |- (Lam ^x.S) ~> (Lam ^x.T) ;
                }},
            "#
        ))
    }

    /// ★ AM-4 pin (A-S5.2), non-opted-in half: a language whose name is NOT in
    /// `DRIVE_OPT_IN` receives NO generated drive fn — the emitted module carries no
    /// drive token at all, so the WHOLE generated module is byte-identical to the
    /// pre-A-S5.2 emission (the drive stage's only insertion point is the conditional
    /// `#drive_fn`, and it is empty here).
    #[test]
    fn generated_rho_net_invocation_omits_the_drive_fn_for_non_opted_in_languages() {
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
        assert!(
            !tokens.contains("rho_net_drive_invocation_to"),
            "a non-opted-in language must not receive the generated drive fn (AM-4)"
        );
        assert!(
            !tokens.contains("drive_admissible") && !tokens.contains("RhoNetDriveInvocation"),
            "no drive machinery leaks into a non-opted-in module (AM-4 byte-identity)"
        );
        // The report-free match fn item is present and drive-free.
        let match_item = extract_fn_item(&tokens, "rho_net_match_invocation_to");
        assert!(
            !match_item.contains("drive"),
            "rho_net_match_invocation_to is untouched by the drive stage"
        );
    }

    /// ★ AM-4 pin (A-S5.2), opted-in half + the cross-toggle byte-identity of
    /// `rho_net_match_invocation_to`: the SAME grammar expanded under the opted-in name
    /// `Lambda` and under a non-opted-in twin name emits (a) the drive fn ONLY for
    /// `Lambda`, with the full fail-closed admission chain, and (b) a
    /// `rho_net_match_invocation_to` fn item that is BYTE-IDENTICAL across the toggle
    /// after normalizing the name-derived identifiers — the executable form of "the
    /// match fn item is byte-identical for all languages".
    #[test]
    fn generated_rho_net_invocation_emits_the_drive_fn_for_opted_in_lambda_only() {
        let opted = generate_rho_net_invocation(&lambda_shaped_fragment("Lambda")).to_string();
        let twin =
            generate_rho_net_invocation(&lambda_shaped_fragment("LambdaDrivePinTwin")).to_string();

        // (a) presence + the fail-closed admission chain for the opted-in expansion…
        assert!(opted.contains("rho_net_drive_invocation_to"));
        assert!(opted.contains("drive_admissible"));
        assert!(opted.contains("rho_net_drive_invocation"));
        assert!(opted.contains("in_rho_static_gate"));
        assert!(opted.contains("is not opted into the in-Rho quiescence driver"));
        assert!(opted.contains("is not admitted"));
        // …and absence for the twin.
        assert!(!twin.contains("rho_net_drive_invocation_to"));

        // (b) the match fn item is byte-identical across the opt-in toggle (modulo the
        // name-derived identifiers, normalized by the rename).
        let opted_match = extract_fn_item(&opted, "rho_net_match_invocation_to").to_string();
        let twin_match = extract_fn_item(&twin, "rho_net_match_invocation_to")
            .replace("LambdaDrivePinTwin", "Lambda");
        assert_eq!(
            opted_match, twin_match,
            "rho_net_match_invocation_to must be byte-identical whether or not the \
             language is drive-opted-in (AM-4)"
        );
        assert!(!opted_match.contains("drive"), "the match fn item carries no drive reference");
    }

    /// ★ F8-AM-5c (A-S5.8): the Lambda `rho_net_drive_invocation_to` fn-item BYTE PIN —
    /// the S2 seed switch edits exactly this emission for FLOAT-BEARING languages, so the
    /// non-float branch must stay byte-identical: (a) the (length, `DefaultHasher`)
    /// fingerprint of the extracted fn item is pinned (captured pre-S2 at `3530df05` —
    /// re-capture only with an explained diff); (b) the item calls the LEGACY
    /// `rho_net_drive_invocation` assembler and carries NO float token.
    ///
    /// RE-CAPTURED (E-3 T-LAZY, 2026-07-20) — explained diff: the drive fn's artifact
    /// preamble switched from the eager field read `let __ruleset = &__artifacts.ruleset;`
    /// to the demand-forcing accessor `let __ruleset = __artifacts.ruleset();`
    /// (`CompiledInRhoArtifacts`' lazy cells, EM-1: the unconsumed installed-par emission
    /// is deferred; exec paths force exactly the ruleset). Token delta: `&` dropped,
    /// `()` appended — +1 byte on the rendered item (5027 → 5028) and a new hash. No
    /// other token changed; the S2 float-branch invariants (legacy seed path, no float
    /// token) are unaffected and still asserted above the pin.
    ///
    /// RE-CAPTURED (#36 S3, 2026-07-25) — explained diff: the Peano reflect labels moved
    /// into the reserved `^` namespace (`Z`/`S` → `^Z`/`^S`), and this fn item interpolates
    /// both as string literals (`lit(PEANO_ZERO_REFLECT_LABEL)` /
    /// `lit(PEANO_SUCC_REFLECT_LABEL)`). Exactly two literals gain exactly one `^` each:
    /// **+2 bytes on the rendered item (5028 → 5030)** and a new hash. The byte delta being
    /// exactly 2 is itself the proof that no other token moved — a single extra token, or a
    /// changed path, or a re-ordered field would not land on +2. The S2 float-branch
    /// invariants (legacy seed path, no float token) are unaffected and still asserted
    /// above the pin.
    ///
    /// RE-CAPTURED (campaign root 4131, 2026-07-31) — explained diff: the embedded mutually
    /// recursive `__mettail_rho_net_reflect_*` helpers were replaced by the generated shared
    /// PDA: one task algebra, pooled task/value stacks, per-category handlers, and thin seed
    /// wrappers. This intentionally changes the complete function-item fingerprint
    /// (5030 → 8610 rendered bytes); the assertions immediately below continue to pin the
    /// unchanged non-float seed route and absence of float machinery. Production-PDA token
    /// tests separately pin child ordering, collection tagging/reversal, binders, identifiers,
    /// and fail-closed fields.
    #[test]
    fn lambda_drive_fn_item_is_byte_identical_across_the_s2_seed_switch() {
        use std::hash::{Hash, Hasher};
        let tokens = generate_rho_net_invocation(&lambda_shaped_fragment("Lambda")).to_string();
        let item = extract_fn_item(&tokens, "rho_net_drive_invocation_to");
        assert!(
            item.contains("rho_net_drive_invocation ("),
            "Lambda's drive fn assembles through the LEGACY seed"
        );
        assert!(
            !item.contains("float"),
            "no float token leaks into a non-float language's drive fn (F8-AM-5c)"
        );
        let mut hasher = std::hash::DefaultHasher::new();
        item.hash(&mut hasher);
        assert_eq!(
            (item.len(), hasher.finish()),
            (8610, 0x6b3b3a697c484929),
            "the Lambda drive fn item must be byte-identical to the E-3 T-LAZY emission \
             (the S2 switch's non-float branch interpolates the SAME \
             `::mettail_rholang_codegen::rho_net_drive_invocation` path tokens the \
             pre-A-S5.8 quote! wrote literally — identical token stream by construction; \
             captured at the A-S5.8 leg-1 tree and recaptured only for the explained \
             changes documented above)"
        );
    }

    /// ★ A-S5.8 (decision Q-SEED = S2): a FLOAT-BEARING drive-opted language's drive fn
    /// assembles the FLOAT-ROUTED seed (`rho_net_drive_float_invocation`), while the rest
    /// of the fn body — admission chain, boundary canonicalization, reflection — is the
    /// shared emission.
    #[test]
    fn float_bearing_drive_fn_assembles_the_float_routed_seed() {
        let tokens = generate_rho_net_invocation(&ambient_shaped_fragment()).to_string();
        let item = extract_fn_item(&tokens, "rho_net_drive_invocation_to");
        assert!(
            item.contains("rho_net_drive_float_invocation"),
            "the float-bearing drive fn routes the seed through ^float (S2)"
        );
        assert!(
            item.contains("binder_congruence_nf_term"),
            "the HOST boundary float is RETAINED above the S2 seed (defense-in-depth + \
             the NewComm display ordering — F8-AM-5b)"
        );
    }

    /// The mini Ambient-shaped fragment (corrected A-S5.4b declarations): equations + the single
    /// `PNew` surface binder + no `RhoNativeJoin` obligation, under the drive-opted-in name
    /// `Ambient` — the float-bearing boundary-canonicalization subject.
    fn ambient_shaped_fragment() -> LanguageDef {
        parse(
            r#"
                name: Ambient,
                types {
                    Proc
                    Name
                },
                terms {
                    PZero . |- "0" : Proc ;
                    PIn . n:Name, p:Proc |- "in" "(" n "," p ")" : Proc ;
                    PAmb . n:Name, p:Proc |- n "[" p "]" : Proc ;
                    PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc ;
                    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
                },
                equations {
                    NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));
                    ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
                    InNew . | x # N |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));
                    AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
                },
                rewrites {}
            "#,
        )
    }

    /// ★ A-S5.4b boundary-canonicalization pin, float-bearing half: a float-bearing language's
    /// REPORT-FREE bodies (`rho_net_match_invocation_to` + `rho_net_drive_invocation_to`)
    /// canonicalize the subject through `binder_congruence_nf_term().unwrap_or_else(original)`
    /// BEFORE M-reflect (F17: `Some` iff progress), while the REPORT-CARRYING bodies
    /// (`rho_net_match_invocation_from_dovetail_to`, the contextual body) stay uncanonicalized —
    /// design v2 §3.3 leaves the typed-path gates and the report-carrying paths as-is.
    #[test]
    fn report_free_bodies_canonicalize_for_a_float_bearing_language() {
        let language = ambient_shaped_fragment();
        assert!(
            crate::gen::runtime::binder_congruence::should_emit_binder_congruence(&language),
            "the fragment is float-bearing (equations + single binder + no RhoNativeJoin)"
        );
        let tokens = generate_rho_net_invocation(&language).to_string();

        let match_free = extract_fn_item(&tokens, "rho_net_match_invocation_to");
        assert!(
            match_free.contains("binder_congruence_nf_term"),
            "the report-free match body canonicalizes before M-reflect"
        );
        assert!(
            match_free.contains("unwrap_or_else"),
            "the canonicalization keeps the F17 Some-iff-progress contract (original on None)"
        );

        let drive = extract_fn_item(&tokens, "rho_net_drive_invocation_to");
        assert!(
            drive.contains("binder_congruence_nf_term"),
            "the drive body canonicalizes before M-reflect"
        );

        let report_carrying = extract_fn_item(&tokens, "rho_net_match_invocation_from_dovetail_to");
        assert!(
            !report_carrying.contains("binder_congruence_nf_term"),
            "the report-carrying match body stays uncanonicalized (design v2 §3.3)"
        );
    }

    /// ★ A-S5.4b boundary-canonicalization pin, non-float half: a language WITHOUT the float
    /// handler (empty equations — SwapDemo-shaped AND the production-Lambda shape) emits NO
    /// canonicalization tokens anywhere — the generated module is byte-identical to the
    /// pre-A-S5.4b emission (the only insertion point is the conditional canonical binding,
    /// empty here).
    #[test]
    fn report_free_bodies_stay_uncanonicalized_for_non_float_languages() {
        for language in [lambda_shaped_fragment("Lambda"), lambda_shaped_fragment("SwapNetShape")] {
            assert!(
                !crate::gen::runtime::binder_congruence::should_emit_binder_congruence(&language),
                "an equations-free language generates no float handler"
            );
            let tokens = generate_rho_net_invocation(&language).to_string();
            assert!(
                !tokens.contains("binder_congruence_nf_term"),
                "a non-float language's generated module carries NO boundary canonicalization"
            );
        }
    }

    #[test]
    fn generated_rho_net_reflection_emits_the_hashset_arm() {
        // Stage 4 S-AC (AC4): a `HashSet` collection FIELD reflects to a
        // `GroundTerm::collection(HashSet, …)` via the `VariantKind::Collection` `HashSet` arm — the
        // subject side of the native `ESet` carrier. The reflect fn iterates the set by `.iter()`
        // (the `HashSetLit`/`std::collections::HashSet` API, no multiplicity), so the reflected
        // collection is tagged `HashSet` and rides `reflect_ac_set_par`. (The generated-language
        // HashSet FIELD does not yet compile end-to-end — the base collection-field codegen is
        // HashBag-shaped, a separate GROUP-B item — but the reflection codegen branch itself is
        // exercised here at the token level.)
        let language = parse(
            r##"
                name: SetNetGen,
                types {
                    Proc
                }
                terms {
                    A . |- "A" : Proc ;
                    Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
                    SetOp . ps:HashSet(Proc) |- "#s{" ps.*sep("|") "}s#" : Proc ;
                }
                equations {}
                rewrites {}
            "##,
        );
        let reflect = reflect_pda_tokens(&language, &format_ident!("Proc"));
        // The production PDA emits the `HashSet` collection arm (native `ESet` carrier), iterating
        // by `.iter()`, enqueueing element visits, and tagging the assembled `GroundTerm`.
        assert!(reflect.contains("CollectionType :: HashSet"));
        assert!(reflect.contains("__MettailReflectTask :: VisitProc"));
        assert!(reflect.contains("__MettailReflectTask :: Assemble"));
        assert!(reflect.contains(". iter ()"));
        assert!(reflect.contains(". reverse ()"));
    }

    /// Stage 4 S-binder SLICE 3a (Ambient OpenRule structural-AC under a `new`): the PNew binder
    /// constructor (`^x.p:[Name -> Proc]`, EMPTY pre-scope fields) reflects to the reserved
    /// `^lambda([⟦body⟧])` tag over the reflected scope body, and a bound NAME occurrence reflects to
    /// `^bound(peano(depth))` (the `^bound`/`Z`/`S` De-Bruijn leaf). This is the ALREADY-generic
    /// reflection the structural-AC spread matcher rides: `structural_ac_match_install_at` descends
    /// the single `^lambda` child into the operand bag (see the `rho_net_lower` companion test
    /// `structural_ac_match_call_descends_through_lambda_to_the_bag`), so an OpenRule redex under
    /// `new(x, {open(x,A) | x[B]})` is LOCATED in Rho with NO new reflection code.
    #[test]
    fn generated_rho_net_reflection_emits_the_lambda_arm_for_pnew() {
        let language = parse(
            r#"
                name: AmbNewReflect,
                types { Proc Name }
                terms {
                    PA . |- "A" : Proc ;
                    Na . |- "na" : Name ;
                    POpen . n:Name, p:Proc |- "open" "(" n "," p ")" : Proc ;
                    PAmb . n:Name, p:Proc |- n "[" p "]" : Proc ;
                    PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc ;
                    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
                }
                equations {}
                rewrites {
                    OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
                        ~> (PPar {P, Q, ...rest}) ;
                }
            "#,
        );
        // The `Proc` reflection emits the PNew binder arm: a single-child `^lambda` over the reflected
        // scope body (read via `unsafe_body`, preserving the de-Bruijn coordinates). PNew has EMPTY
        // pre-scope fields, so it takes the single-child `^lambda` arm (not the fail-closed arm).
        let proc_reflect = reflect_pda_tokens(&language, &format_ident!("Proc"));
        assert!(proc_reflect.contains("\"^lambda\""), "PNew reflects to the ^lambda tag");
        assert!(proc_reflect.contains("unsafe_body"), "the ^lambda arm reads the scope body");
        // The `Name` reflection emits the de-Bruijn Var arm: a BOUND occurrence → `^bound(peano)`, a
        // FREE occurrence → `^free`. A bound `new`-scoped ambient name rides `^bound(peano(depth))`,
        // so the non-linear guard `N ≡ N` compares the two occurrences' de-Bruijn depths.
        let name_reflect = reflect_pda_tokens(&language, &format_ident!("Name"));
        assert!(
            name_reflect.contains("\"^bound\""),
            "a bound Name occurrence reflects to ^bound"
        );
        assert!(name_reflect.contains("\"^free\""), "a free Name occurrence reflects to ^free");
        // ★ #36 S3: the expected token spelling is DERIVED from the ABI constants, never
        // re-spelled. This assertion previously hardcoded `"\"Z\""` / `"\"S\""`; when the
        // Peano labels moved into the `^` namespace the literals stopped naming the
        // machinery and the assertion started testing for a user constructor named `Z`.
        // A test that re-spells an ABI tag is a second, unversioned copy of the ABI —
        // exactly the defect that made this test fail rather than the emitter.
        let peano_zero = format!("{:?}", mettail_rholang_codegen::PEANO_ZERO_REFLECT_LABEL);
        let peano_succ = format!("{:?}", mettail_rholang_codegen::PEANO_SUCC_REFLECT_LABEL);
        assert!(
            name_reflect.contains(&peano_zero) && name_reflect.contains(&peano_succ),
            "the ^bound depth is a Peano numeral {peano_zero}/{peano_succ}(…)"
        );
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
        // Stage 4 (S-contextual): a UNARY congruence rewrite `| S ~> T |- Wrap(S) ~> Wrap(T)` (plus a
        // base rewrite `Flip` to reduce the hole) emits the contextual injection method, which now
        // MATCHES IN RHO — it compiles the ruleset, GATES on it, STRUCTURALLY reflects the whole
        // subject (M-reflect, NOT the report σ), and assembles the contextual match call (the base
        // automaton LOCATES the hole's premise redex + the hole bridge routes its IN-RHO reduced hole
        // to the join). This is the third arm (base | AC | contextual) of the F-fn.
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
        // The contextual injection method + its distinctive in-Rho MATCH helpers. A-S2: the
        // def + ruleset come from the per-source memoized artifacts, not a per-invocation
        // reconstruct+compile.
        assert!(tokens.contains("rho_net_contextual_invocation_from_dovetail_to"));
        assert!(tokens.contains("cached_in_rho_artifacts"));
        assert!(tokens.contains("in_rho_match_gate_reject"));
        assert!(tokens.contains("contextual_match_call_par"), "the contextual match call");
        // M-reflect: the contextual path structurally reflects `term` (the greenfield hinge)
        // instead of reconstructing the reduced hole `T = RHS_premise[σ]` from the report σ.
        assert!(
            tokens.contains("__mettail_rho_net_reflect_proc"),
            "per-category Term→GroundTerm (M-reflect)"
        );
        // Retirement proof (by construction): the contextual MATCH path no longer reconstructs the
        // reduced hole from the report σ (`reconstruct_contractum`) nor host-delivers it
        // (`contextual_contract_call`) — the hole comes from the automaton's IN-RHO nested firing.
        assert!(
            !tokens.contains("reconstruct_contractum"),
            "the contextual MATCH path must not reconstruct the hole from the report σ"
        );
        assert!(
            !tokens.contains("contextual_contract_call"),
            "the contextual MATCH path must not host-deliver the reduced hole (in-Rho routing)"
        );
        // The base arm still fires for the `Flip` premise rewrite (base | AC | contextual).
        assert!(tokens.contains("term_contract_call"));
        assert!(tokens.contains("\"Flip\"") || tokens.contains("Flip"));
    }

    #[test]
    fn generated_rho_net_invocation_emits_the_in_rho_match_method() {
        // Stage 4 (M-reflect + locate-all): the emitted impl carries the in-Rho MATCH invocation
        // — compile the ruleset, GATE on it, STRUCTURALLY reflect the whole subject term (NOT the
        // report σ), and assemble the LOCATE-ALL ∏ network_ℓ ‖ spread call (the automaton LOCATES
        // every redex at any position + emits σ ON the interpreter).
        let tokens = generate_rho_net_invocation(&swap_net_fixture()).to_string();
        assert!(tokens.contains("rho_net_match_invocation_from_dovetail_to"));
        // A-S2: the def + ruleset come from the per-source memoized artifacts
        // (`cached_in_rho_artifacts` — which performs the same reconstruct+compile once), not a
        // per-invocation `reconstruct_language_def` + `compile_in_rho_matching_ruleset`.
        assert!(tokens.contains("cached_in_rho_artifacts"));
        assert!(
            !tokens.contains("compile_in_rho_matching_ruleset"),
            "the generated bodies must not re-compile the ruleset per invocation (memoized; \
             `rho_net_program()` keeps its own reconstruct+lower accessor path)"
        );
        assert!(tokens.contains("in_rho_match_gate_reject"));
        // Locate-all: the MATCH path co-installs a positional network at EVERY located redex
        // position (nested + multiple), retiring the single-root `in_rho_match_call_par` +
        // `rule_lhs_root_constructor` root-rooted restriction.
        assert!(tokens.contains("in_rho_match_all_sites_call_par"), "locate-all multi-site call");
        // M-reflect: the MATCH path structurally reflects `term` (the greenfield hinge) instead
        // of rebuilding LHS[σ] from the report σ.
        assert!(
            tokens.contains("__mettail_rho_net_reflect_proc"),
            "per-category Term→GroundTerm"
        );
        // Retirement proof (by construction): the MATCH path no longer restricts to a single
        // root-rooted redex (`rule_lhs_root_constructor`) nor rebuilds LHS[σ] from the host
        // report σ (`reconstruct_redex_subject`) — every redex is LOCATED + fired by the `sa:`
        // accept, so σ is produced by the automaton, never the report.
        assert!(
            !tokens.contains("rule_lhs_root_constructor"),
            "the MATCH path must not gate on a single root-rooted redex (locate-all retirement)"
        );
        assert!(
            !tokens.contains("reconstruct_redex_subject"),
            "the MATCH path must not rebuild the redex from the report σ (M-reflect retirement)"
        );
    }

    #[test]
    fn generated_rho_net_invocation_emits_the_report_free_match_method() {
        // A-S2 (D-stage demotion) + A-S3 (native dispatch boundary tightening): the emitted
        // impl carries the REPORT-FREE match invocation —
        // `rho_net_match_invocation_to(term, out_channel)` — which admits via the STATIC gate
        // (`in_rho_static_gate`, term-independent), counts native sites from LOCATED positions
        // (`located_native_site_count_for`, never report firings), reads the memoized artifacts
        // (`cached_in_rho_artifacts`), and assembles the SAME locate-all call
        // (`in_rho_match_all_sites_call_par`) as the report-carrying body.
        let tokens = generate_rho_net_invocation(&swap_net_fixture()).to_string();
        assert!(tokens.contains("rho_net_match_invocation_to"), "the report-free method exists");
        assert!(tokens.contains("in_rho_static_gate"), "the STATIC gate replaces the fired gate");
        assert!(
            tokens.contains("located_native_site_count_for"),
            "native sites are counted from located positions, per rule"
        );
        assert!(tokens.contains("cached_in_rho_artifacts"), "artifacts are memoized per source");
        assert!(
            tokens.contains("in_rho_match_all_sites_call_par"),
            "the report-free path assembles the same locate-all call"
        );
        // A-S3: a located native site ADMITS — the body registers the machine-side handler
        // contract specs (drained by the runtime bracket into `extra_system_processes`
        // Definitions) and co-installs the per-site CONTRACT-CALL bridge; the host-value
        // deferral is gone from the report-free path (only unregistrable handlers defer).
        assert!(
            tokens.contains("record_pending_native_handler_specs"),
            "the report-free path registers machine-side native handler specs"
        );
        assert!(
            tokens.contains("native_locate_contract_bridge_par"),
            "the report-free path co-installs the per-site contract-call bridge"
        );
        assert!(
            tokens.contains("__mettail_native_handler_for"),
            "the machine-side handler lookup gates native admission"
        );
        // The report-carrying value bridge stays byte-identical on ITS path (the deferral
        // path): the host-contractum `native_locate_bridge_par` still appears there.
        assert!(
            tokens.contains("native_locate_bridge_par"),
            "the report-carrying value bridge is retained on the deferral path"
        );
        // The report-free method has NO report parameter: the report-carrying signature
        // (`RuntimeDovetailRunReport`) appears only in the `_from_dovetail_to*` fallbacks, which
        // this stage keeps behaviorally intact for the lazy-report deferral path.
        assert!(
            tokens.contains("rho_net_match_invocation_from_dovetail_to"),
            "the report-carrying fallback method is retained"
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
