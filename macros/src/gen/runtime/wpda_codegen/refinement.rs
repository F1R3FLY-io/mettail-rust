//! Refinement-type predicate codegen.
//!
//! For each `RefinementTypeDef { name, var, base_type, predicate }` in
//! `language.refinement_types`, emit:
//!
//! 1. A registration call in the language's `register_refinements()` function
//!    that wraps the predicate body as a closure and calls
//!    `mettail_runtime::register_refinement_predicate`. The closure takes
//!    `value: &dyn Any`, downcasts to the base type's native Rust type, and
//!    evaluates the lowered predicate body against the bound variable.
//!
//! 2. Generated rule actions for any rule whose result category matches a
//!    refinement type wrap construction with
//!    `evaluate_refinement_predicate(name, &candidate)`. On `false`, skip
//!    the push (RT01 diagnostic emission is the responsibility of the action
//!    site — currently the action body just refrains from pushing, which
//!    surfaces as `WpdaParseError::EmptyResult`).
//!
//! ## Lowering model
//!
//! The closure body has shape:
//! ```text
//! |value: &dyn Any| -> bool {
//!     if let Some(__v) = value.downcast_ref::<NativeTy>() {
//!         <body>
//!     } else { false }
//! }
//! ```
//! where `<body>` is built recursively by [`lower_refinement_body`] using the
//! bound variable name (e.g., `x`) bound to a local `__refinement_x` reference.
//! The bound var appears in `Linear` term coefficients and `TermEq`/`TermNeq`
//! arms; compound nodes (`And`/`Or`/`Not`/`Implies`) thread the same env.
//!
//! ## Unsupported variants
//!
//! These emit `compile_error!` rather than silently producing a wrong result:
//! - **Multi-variable Linear**: `3*x + 2*y > 7` — Presburger across multiple
//!   bound vars needs a constraint solver, not a closure.
//! - **Quantified without explicit bound**: `forall x. body` — undecidable in
//!   general; finite-domain enumeration requires `bound: Some(k)`.
//! - **TermEq/Neq with two free variables**: only `var op constant` form
//!   supported.
//!
//! ## No shipped grammar exercises this today
//!
//! Calculator/RhoCalc/etc. don't declare `refinement_types`. The synthetic
//! test grammar in `languages/tests/refinement_smoke.rs` covers the path.

use mettail_ast::language::{
    LangType, LanguageDef, LinearRelation, PredArg, Quantifier, RefinementPredicate,
    RefinementTypeDef,
};
use mettail_ast::types::TypeExpr;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Ident, Type};

/// Emit `register_refinements()` — a function that registers every
/// `RefinementTypeDef` in `language.refinement_types` with the runtime
/// predicate registry. Called by tests / language init before parsing
/// inputs that should observe the refinements.
///
/// Returns an empty `TokenStream` when no refinements are declared.
pub(crate) fn emit_refinement_registrations(language: &LanguageDef) -> TokenStream {
    if language.refinement_types.is_empty() {
        return quote! {};
    }
    let mut calls = Vec::new();
    for ref_ty in &language.refinement_types {
        let name_str = ref_ty.name.to_string();
        let native_ty = match resolve_base_native_type(language, &ref_ty.base_type) {
            Some(ty) => ty,
            None => {
                let msg = format!(
                    "refinement type `{}` base type `{}` has no native Rust type — declare via `![T] as {}`",
                    ref_ty.name,
                    type_expr_display(&ref_ty.base_type),
                    type_expr_display(&ref_ty.base_type),
                );
                calls.push(quote! { compile_error!(#msg); });
                continue;
            },
        };
        let body = lower_refinement_predicate(&ref_ty.predicate, &ref_ty.var, &native_ty);
        calls.push(quote! {
            mettail_runtime::register_refinement_predicate(
                #name_str,
                std::sync::Arc::new(|value: &dyn std::any::Any| -> bool {
                    #body
                }),
            );
        });
    }
    quote! {
        /// Refinement-type predicate registration. Tests / language init
        /// call this once before any parsing that should exercise the
        /// declared refinements.
        pub fn register_refinements() {
            #(#calls)*
        }
    }
}

/// Look up the native Rust type for a refinement's base type.
///
/// Only `TypeExpr::Base(Ident)` is supported — the base type names a
/// declared category whose `LangType.native_type` carries the underlying
/// Rust type (e.g., `i32` for `![i32] as Int`). Other shapes (`Arrow`,
/// `Collection`, `Refined`) cannot serve as a refinement base directly.
fn resolve_base_native_type(language: &LanguageDef, base: &TypeExpr) -> Option<Type> {
    let TypeExpr::Base(ref name) = base else {
        return None;
    };
    let lt: &LangType = language.types.iter().find(|t| &t.name == name)?;
    lt.native_type.clone()
}

/// One-line display of a `TypeExpr` for error messages.
fn type_expr_display(ty: &TypeExpr) -> String {
    format!("{}", ty)
}

/// Emit the closure body for a refinement predicate. The outer closure has
/// signature `Fn(&dyn Any) -> bool`; this body downcasts to `native_ty` and
/// evaluates the predicate against the bound variable.
fn lower_refinement_predicate(
    pred: &RefinementPredicate,
    var: &Ident,
    native_ty: &Type,
) -> TokenStream {
    let bound = bound_local_ident(var);
    let body = lower_refinement_body(pred, var, &bound);
    quote! {
        if let Some(#bound) = value.downcast_ref::<#native_ty>() {
            #body
        } else {
            false
        }
    }
}

/// Local Rust ident the closure body uses for the bound variable.
/// We don't reuse the user's `var` name directly so that user-chosen names
/// like `value`, `self`, `Box` don't collide with the closure scope.
fn bound_local_ident(var: &Ident) -> Ident {
    format_ident!("__refinement_{}", var)
}

/// Recursively lower a `RefinementPredicate` to a `bool` expression. The
/// caller has already opened a scope in which `bound` is bound to a
/// `&NativeTy` reference; references to the user's `var` lower to `*bound`
/// (deref to the underlying value) wherever a value is needed.
fn lower_refinement_body(pred: &RefinementPredicate, var: &Ident, bound: &Ident) -> TokenStream {
    match pred {
        RefinementPredicate::Linear { terms, relation, rhs } => {
            lower_linear(terms, relation, *rhs, var, bound)
        },
        RefinementPredicate::And(a, b) => {
            let ae = lower_refinement_body(a, var, bound);
            let be = lower_refinement_body(b, var, bound);
            quote! { ((#ae) && (#be)) }
        },
        RefinementPredicate::Or(a, b) => {
            let ae = lower_refinement_body(a, var, bound);
            let be = lower_refinement_body(b, var, bound);
            quote! { ((#ae) || (#be)) }
        },
        RefinementPredicate::Not(inner) => {
            let ie = lower_refinement_body(inner, var, bound);
            quote! { (!(#ie)) }
        },
        RefinementPredicate::Implies(a, b) => {
            let ae = lower_refinement_body(a, var, bound);
            let be = lower_refinement_body(b, var, bound);
            quote! { ((!(#ae)) || (#be)) }
        },
        RefinementPredicate::TermEq(a, b) => lower_term_cmp(a, b, var, bound, true),
        RefinementPredicate::TermNeq(a, b) => lower_term_cmp(a, b, var, bound, false),
        RefinementPredicate::Relation { name, args, negated } => {
            lower_relation(name, args, *negated, var, bound)
        },
        RefinementPredicate::Quantified {
            quantifier,
            var: qvar,
            domain,
            bound: k,
            body,
        } => lower_quantified(quantifier.clone(), qvar, domain.as_ref(), *k, body, var, bound),
    }
}

/// Lower `Linear { terms, relation, rhs }`. Only single-bound-var form is
/// supported; multi-variable Presburger emits `compile_error!`.
fn lower_linear(
    terms: &[(Ident, i64)],
    relation: &LinearRelation,
    rhs: i64,
    var: &Ident,
    bound: &Ident,
) -> TokenStream {
    if terms.len() != 1 || terms[0].0 != *var {
        let msg = format!(
            "multi-variable Presburger refinements not supported: predicate must use only the bound variable `{}` (got {} terms)",
            var,
            terms.len(),
        );
        return quote! { { compile_error!(#msg); false } };
    }
    let coeff = terms[0].1;
    // Widen via `as i128` so coefficient * value can't overflow i64 for
    // realistic refinement constants. The native type is some integer
    // family (Linear is an integer-arithmetic predicate); `*bound as i128`
    // is well-defined for every supported integer family.
    let lhs = if coeff == 1 {
        quote! { (*#bound as i128) }
    } else if coeff == -1 {
        quote! { (-(*#bound as i128)) }
    } else {
        quote! { ((#coeff as i128) * (*#bound as i128)) }
    };
    let rhs_lit = rhs as i128;
    let cmp = match relation {
        LinearRelation::Le => quote! { <= },
        LinearRelation::Lt => quote! { < },
        LinearRelation::Ge => quote! { >= },
        LinearRelation::Gt => quote! { > },
        LinearRelation::Eq => quote! { == },
        LinearRelation::Neq => quote! { != },
    };
    quote! { #lhs #cmp (#rhs_lit as i128) }
}

/// Lower `TermEq` / `TermNeq`. Only `var op constant` and `constant op var`
/// shapes are supported; two free variables emit `compile_error!`.
fn lower_term_cmp(
    a: &PredArg,
    b: &PredArg,
    var: &Ident,
    bound: &Ident,
    is_eq: bool,
) -> TokenStream {
    let cmp = if is_eq {
        quote! { == }
    } else {
        quote! { != }
    };
    match (a, b) {
        (PredArg::Var(v), PredArg::Constant(c)) | (PredArg::Constant(c), PredArg::Var(v)) => {
            if v != var {
                let msg = format!(
                    "refinement TermEq/Neq references unbound variable `{}` — only the bound variable `{}` is in scope",
                    v, var,
                );
                return quote! { { compile_error!(#msg); false } };
            }
            let c_str = c.to_string();
            quote! {
                {
                    let __rhs: i128 = #c_str.parse::<i128>().unwrap_or(0);
                    ((*#bound as i128) #cmp __rhs)
                }
            }
        },
        (PredArg::Constant(a), PredArg::Constant(b)) => {
            // Constant-vs-constant: evaluate at compile time. Both args are
            // identifiers (the parser uses `Ident` for numeric constants
            // too); parse to i128 and fold.
            let a_str = a.to_string();
            let b_str = b.to_string();
            quote! {
                {
                    let __l: i128 = #a_str.parse::<i128>().unwrap_or(0);
                    let __r: i128 = #b_str.parse::<i128>().unwrap_or(0);
                    (__l #cmp __r)
                }
            }
        },
        (PredArg::Var(_), PredArg::Var(_)) => {
            let msg = "refinement TermEq/Neq with two variables not supported (only the bound variable is in scope)";
            quote! { { compile_error!(#msg); false } }
        },
    }
}

/// Lower `Relation { name, args, negated }`. Delegates to the runtime
/// `evaluate_pred_with_bindings` against the thread-local fact snapshot.
/// The bound variable's value is supplied as a string-rendered binding; free
/// variables in `args` other than the bound var emit `compile_error!`.
fn lower_relation(
    name: &Ident,
    args: &[PredArg],
    negated: bool,
    var: &Ident,
    bound: &Ident,
) -> TokenStream {
    let name_str = name.to_string();
    let var_str = var.to_string();
    // Validate that every Var arg is the bound variable.
    for arg in args {
        if let PredArg::Var(v) = arg {
            if v != var {
                let msg = format!(
                    "refinement Relation arg `{}` is not the bound variable `{}` — refinement closures only see the bound var",
                    v, var,
                );
                return quote! { { compile_error!(#msg); false } };
            }
        }
    }
    let arg_exprs: Vec<TokenStream> = args
        .iter()
        .map(|a| match a {
            PredArg::Var(_) => {
                let var_string = var_str.clone();
                quote! {
                    mettail_runtime::PredArg::Var(#var_string.to_string())
                }
            },
            PredArg::Constant(c) => {
                let c_str = c.to_string();
                // The runtime PredArg distinguishes IntLit vs StringLit;
                // attempt to parse as i64, fall back to StringLit.
                quote! {
                    {
                        if let Ok(__n) = #c_str.parse::<i64>() {
                            mettail_runtime::PredArg::IntLit(__n)
                        } else {
                            mettail_runtime::PredArg::StringLit(#c_str.to_string())
                        }
                    }
                }
            },
        })
        .collect();
    let pred_expr = quote! {
        mettail_runtime::BehavioralPred::RelationQuery {
            relation_name: #name_str.to_string(),
            args: vec![#(#arg_exprs),*],
            negated: #negated,
        }
    };
    quote! {
        {
            let __pred = #pred_expr;
            let __bindings = vec![(
                #var_str.to_string(),
                format!("{}", *#bound),
            )];
            mettail_runtime::evaluate_pred_with_bindings(&__pred, &__bindings)
        }
    }
}

/// Lower `Quantified { quantifier, var, domain, bound, body }`. The bound
/// `k` must be `Some(_)` — unbounded quantification emits `compile_error!`.
/// A `domain` is also required (an `Ident` naming the relation to enumerate);
/// without one we have no domain to iterate.
///
/// Delegates to `mettail_prattail::logict::evaluate_quantified` with the
/// outer-bound variable's value supplied as part of the env. Domain
/// enumeration / relation-query callbacks return empty by default — a
/// language with refinement types and behavioral relations would supply
/// real callbacks via a different surface (e.g., a refinement evaluator
/// hook), but the synthetic test grammars don't exercise this path yet.
fn lower_quantified(
    quantifier: Quantifier,
    qvar: &Ident,
    domain: Option<&Ident>,
    k: Option<usize>,
    body: &RefinementPredicate,
    outer_var: &Ident,
    outer_bound: &Ident,
) -> TokenStream {
    let Some(k_lit) = k else {
        let msg = format!(
            "unbounded quantified refinement predicate over `{}` requires explicit `_{{k=N}}` bound — undecidable in general",
            qvar,
        );
        return quote! { { compile_error!(#msg); false } };
    };
    let Some(d) = domain else {
        let msg = format!(
            "quantified refinement predicate over `{}` requires explicit `in <domain>` clause — bare quantifiers have no enumeration source",
            qvar,
        );
        return quote! { { compile_error!(#msg); false } };
    };
    let qvar_str = qvar.to_string();
    let outer_var_str = outer_var.to_string();
    let d_str = d.to_string();
    let body_formula = refinement_pred_to_quantified_formula(body);
    let q_ctor = match quantifier {
        Quantifier::ForAll => quote! { mettail_prattail::logict::QuantifiedFormula::forall },
        Quantifier::Exists => quote! { mettail_prattail::logict::QuantifiedFormula::exists },
    };
    quote! {
        {
            let __body = #body_formula;
            let __formula = #q_ctor(
                #qvar_str.to_string(),
                mettail_prattail::logict::QuantifiedDomain::Bounded {
                    relation: #d_str.to_string(),
                    limit: #k_lit,
                },
                __body,
            );
            let mut __env = ::std::collections::HashMap::new();
            __env.insert(
                #outer_var_str.to_string(),
                format!("{}", *#outer_bound),
            );
            let __relation_query = |_rel: &str, _args: &[String]| -> bool { false };
            let __domain_enumerate = |_dom: &str| -> Vec<Vec<String>> { Vec::new() };
            mettail_prattail::logict::evaluate_quantified(
                &__formula,
                &__env,
                &__relation_query,
                &__domain_enumerate,
                #k_lit,
            )
        }
    }
}

/// Convert a `RefinementPredicate` body to a `QuantifiedFormula` construction
/// expression for use inside a `lower_quantified` body.
///
/// Each `PredArg::Var(v)` becomes `QuantifiedArg::Var(v)`; each
/// `PredArg::Constant(c)` becomes `QuantifiedArg::Constant(c)`. Linear /
/// TermEq / TermNeq leaves inside a quantifier body encode as a named atom
/// with a serialized form (the relation_query callback decides truth).
fn refinement_pred_to_quantified_formula(pred: &RefinementPredicate) -> TokenStream {
    match pred {
        RefinementPredicate::Relation { name, args, negated } => {
            let name_str = name.to_string();
            let arg_exprs: Vec<TokenStream> = args
                .iter()
                .map(|a| match a {
                    PredArg::Var(v) => {
                        let v_str = v.to_string();
                        quote! {
                            mettail_prattail::logict::QuantifiedArg::Var(#v_str.to_string())
                        }
                    },
                    PredArg::Constant(c) => {
                        let c_str = c.to_string();
                        quote! {
                            mettail_prattail::logict::QuantifiedArg::Constant(#c_str.to_string())
                        }
                    },
                })
                .collect();
            let atom = quote! {
                mettail_prattail::logict::QuantifiedFormula::atom(
                    #name_str.to_string(),
                    vec![#(#arg_exprs),*],
                )
            };
            if *negated {
                quote! { mettail_prattail::logict::QuantifiedFormula::not(#atom) }
            } else {
                atom
            }
        },
        RefinementPredicate::Quantified { quantifier, var, domain, bound, body } => {
            let body_expr = refinement_pred_to_quantified_formula(body);
            let var_str = var.to_string();
            let Some(d) = domain else {
                let msg = format!(
                    "nested quantifier over `{}` requires explicit `in <domain>` clause",
                    var,
                );
                return quote! { { compile_error!(#msg); mettail_prattail::logict::QuantifiedFormula::atom(String::new(), vec![]) } };
            };
            let d_str = d.to_string();
            let domain_expr = match bound {
                Some(b) => quote! {
                    mettail_prattail::logict::QuantifiedDomain::Bounded {
                        relation: #d_str.to_string(),
                        limit: #b,
                    }
                },
                None => quote! {
                    mettail_prattail::logict::QuantifiedDomain::Relation(#d_str.to_string())
                },
            };
            let ctor = match quantifier {
                Quantifier::ForAll => {
                    quote! { mettail_prattail::logict::QuantifiedFormula::forall }
                },
                Quantifier::Exists => {
                    quote! { mettail_prattail::logict::QuantifiedFormula::exists }
                },
            };
            quote! {
                #ctor(
                    #var_str.to_string(),
                    #domain_expr,
                    #body_expr,
                )
            }
        },
        RefinementPredicate::And(a, b) => {
            let ae = refinement_pred_to_quantified_formula(a);
            let be = refinement_pred_to_quantified_formula(b);
            quote! { mettail_prattail::logict::QuantifiedFormula::and(#ae, #be) }
        },
        RefinementPredicate::Or(a, b) => {
            let ae = refinement_pred_to_quantified_formula(a);
            let be = refinement_pred_to_quantified_formula(b);
            quote! { mettail_prattail::logict::QuantifiedFormula::or(#ae, #be) }
        },
        RefinementPredicate::Not(inner) => {
            let ie = refinement_pred_to_quantified_formula(inner);
            quote! { mettail_prattail::logict::QuantifiedFormula::not(#ie) }
        },
        RefinementPredicate::Implies(a, b) => {
            let ae = refinement_pred_to_quantified_formula(a);
            let be = refinement_pred_to_quantified_formula(b);
            quote! { mettail_prattail::logict::QuantifiedFormula::implies(#ae, #be) }
        },
        RefinementPredicate::Linear { terms, relation, rhs } => {
            // Linear inside a quantifier body: encode as a named atom whose
            // relation_query callback decides truth. Quantified refinements
            // with linear leaves are an unusual combination — a richer
            // surface would require a custom evaluation hook.
            let repr = format!(
                "{}{}{}",
                terms
                    .iter()
                    .map(|(v, c)| format!("{}*{}", c, v))
                    .collect::<Vec<_>>()
                    .join("+"),
                relation,
                rhs,
            );
            quote! {
                mettail_prattail::logict::QuantifiedFormula::atom(
                    #repr.to_string(),
                    vec![],
                )
            }
        },
        RefinementPredicate::TermEq(a, b) | RefinementPredicate::TermNeq(a, b) => {
            let a_str = match a {
                PredArg::Var(v) => v.to_string(),
                PredArg::Constant(c) => c.to_string(),
            };
            let b_str = match b {
                PredArg::Var(v) => v.to_string(),
                PredArg::Constant(c) => c.to_string(),
            };
            let op = if matches!(pred, RefinementPredicate::TermEq(_, _)) {
                "=="
            } else {
                "!="
            };
            let repr = format!("{}{}{}", a_str, op, b_str);
            quote! {
                mettail_prattail::logict::QuantifiedFormula::atom(
                    #repr.to_string(),
                    vec![],
                )
            }
        },
    }
}

/// Look up a `RefinementTypeDef` by category name. Used by action emitters
/// to wrap `push_term` with `evaluate_refinement_predicate`.
pub(crate) fn lookup_refinement_type<'a>(
    language: &'a LanguageDef,
    cat_name: &str,
) -> Option<&'a RefinementTypeDef> {
    language
        .refinement_types
        .iter()
        .find(|r| r.name.to_string() == cat_name)
}

/// Whether a category is refined. Convenience over `lookup_refinement_type`
/// for callers that only need the bool.
// dead_code: exercised only by the same-file `#[cfg(test)] mod tests`; dead in the non-test lib build.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn category_is_refined(language: &LanguageDef, cat_name: &str) -> bool {
    lookup_refinement_type(language, cat_name).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::{LangType, LinearRelation};
    use mettail_ast::types::TypeExpr;
    use proc_macro2::Span;
    use syn::{parse_str, Type};

    fn empty_lang() -> LanguageDef {
        LanguageDef {
            name: Ident::new("Test", Span::call_site()),
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
        }
    }

    fn lang_with_int_native() -> LanguageDef {
        let mut lang = empty_lang();
        let i32_ty: Type = parse_str("i32").expect("parse i32");
        lang.types.push(LangType {
            name: Ident::new("Int", Span::call_site()),
            native_type: Some(i32_ty),
            collection_kind: None,
        });
        lang
    }

    #[test]
    fn empty_refinement_emits_nothing() {
        let lang = empty_lang();
        let ts = emit_refinement_registrations(&lang);
        assert!(ts.to_string().trim().is_empty());
    }

    #[test]
    fn category_is_refined_returns_false_for_unknown() {
        let lang = empty_lang();
        assert!(!category_is_refined(&lang, "Anything"));
    }

    #[test]
    fn linear_single_var_lowers() {
        // x > 0
        let var = Ident::new("x", Span::call_site());
        let bound = bound_local_ident(&var);
        let pred = RefinementPredicate::Linear {
            terms: vec![(var.clone(), 1)],
            relation: LinearRelation::Gt,
            rhs: 0,
        };
        let ts = lower_refinement_body(&pred, &var, &bound);
        let s = ts.to_string();
        assert!(s.contains("__refinement_x"), "body should reference bound: {}", s);
        assert!(s.contains(">") && !s.contains(">="), "should emit > comparison: {}", s);
    }

    #[test]
    fn linear_multi_var_emits_compile_error() {
        // 3*x + 2*y > 7 — compile_error!
        let x = Ident::new("x", Span::call_site());
        let y = Ident::new("y", Span::call_site());
        let bound = bound_local_ident(&x);
        let pred = RefinementPredicate::Linear {
            terms: vec![(x.clone(), 3), (y, 2)],
            relation: LinearRelation::Gt,
            rhs: 7,
        };
        let ts = lower_refinement_body(&pred, &x, &bound);
        let s = ts.to_string();
        assert!(s.contains("compile_error"), "multi-var must compile_error: {}", s);
    }

    #[test]
    fn and_or_not_compose() {
        let var = Ident::new("x", Span::call_site());
        let bound = bound_local_ident(&var);
        let p1 = RefinementPredicate::Linear {
            terms: vec![(var.clone(), 1)],
            relation: LinearRelation::Gt,
            rhs: 0,
        };
        let p2 = RefinementPredicate::Linear {
            terms: vec![(var.clone(), 1)],
            relation: LinearRelation::Lt,
            rhs: 100,
        };
        let conj = RefinementPredicate::And(Box::new(p1.clone()), Box::new(p2.clone()));
        let ts = lower_refinement_body(&conj, &var, &bound);
        let s = ts.to_string();
        assert!(s.contains("&&"), "And should emit &&: {}", s);

        let not = RefinementPredicate::Not(Box::new(p1));
        let ts = lower_refinement_body(&not, &var, &bound);
        let s = ts.to_string();
        assert!(s.contains("!"), "Not should emit !: {}", s);
    }

    #[test]
    fn term_eq_var_constant_lowers() {
        let var = Ident::new("x", Span::call_site());
        let bound = bound_local_ident(&var);
        // Constants in TermEq must be uppercase-starting Idents per the
        // refinement-predicate parser — `x == MAX` is the canonical shape.
        // Numeric literal RHS like `x == 0` is parsed as `Linear { Eq, 0 }`,
        // not TermEq, so this test exercises the named-constant path.
        let max = Ident::new("MAX", Span::call_site());
        let pred = RefinementPredicate::TermEq(PredArg::Var(var.clone()), PredArg::Constant(max));
        let ts = lower_refinement_body(&pred, &var, &bound);
        let s = ts.to_string();
        assert!(
            s.contains("__refinement_x") && s.contains("=="),
            "TermEq should emit comparison: {}",
            s
        );
    }

    #[test]
    fn quantified_unbounded_emits_compile_error() {
        let outer = Ident::new("p", Span::call_site());
        let bound = bound_local_ident(&outer);
        let qvar = Ident::new("y", Span::call_site());
        let body = RefinementPredicate::Linear {
            terms: vec![(outer.clone(), 1)],
            relation: LinearRelation::Gt,
            rhs: 0,
        };
        let pred = RefinementPredicate::Quantified {
            quantifier: Quantifier::ForAll,
            var: qvar,
            domain: None,
            bound: None, // unbounded → compile_error!
            body: Box::new(body),
        };
        let ts = lower_refinement_body(&pred, &outer, &bound);
        let s = ts.to_string();
        assert!(s.contains("compile_error"), "unbounded forall must compile_error: {}", s);
    }

    #[test]
    fn registration_emits_register_call() {
        let mut lang = lang_with_int_native();
        let var = Ident::new("x", Span::call_site());
        lang.refinement_types.push(RefinementTypeDef {
            name: Ident::new("PosInt", Span::call_site()),
            var: var.clone(),
            base_type: TypeExpr::Base(Ident::new("Int", Span::call_site())),
            predicate: RefinementPredicate::Linear {
                terms: vec![(var, 1)],
                relation: LinearRelation::Gt,
                rhs: 0,
            },
        });
        let ts = emit_refinement_registrations(&lang);
        let s = ts.to_string();
        assert!(s.contains("register_refinements"), "should emit fn name: {}", s);
        assert!(s.contains("register_refinement_predicate"), "should call registry: {}", s,);
        assert!(s.contains("PosInt"), "should pass refinement name: {}", s);
        assert!(s.contains("i32"), "should downcast to i32: {}", s);
    }

    #[test]
    fn missing_native_type_emits_compile_error() {
        let mut lang = empty_lang();
        // Declare PosInt against base Int, but Int has no native_type.
        lang.types.push(LangType {
            name: Ident::new("Int", Span::call_site()),
            native_type: None,
            collection_kind: None,
        });
        let var = Ident::new("x", Span::call_site());
        lang.refinement_types.push(RefinementTypeDef {
            name: Ident::new("PosInt", Span::call_site()),
            var: var.clone(),
            base_type: TypeExpr::Base(Ident::new("Int", Span::call_site())),
            predicate: RefinementPredicate::Linear {
                terms: vec![(var, 1)],
                relation: LinearRelation::Gt,
                rhs: 0,
            },
        });
        let ts = emit_refinement_registrations(&lang);
        let s = ts.to_string();
        assert!(s.contains("compile_error"), "missing native_type must compile_error: {}", s);
    }
}
