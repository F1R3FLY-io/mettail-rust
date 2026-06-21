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

fn scalar_literal_variant(
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
                _ => None,
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
}
