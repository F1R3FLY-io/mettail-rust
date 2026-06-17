//! Steps E + F of the Dovetail native-fold reduction work (Increment 3): the typed-`L`
//! `dovetail_report_for` for fold-bearing languages.
//!
//! This is the alternate report body the `generate_dovetail_report` early-return dispatches to
//! when [`super::needs_typed_fold_path`] holds. It emits the typed op-enum
//! ([`super::op_enum`]), the typed lowering ([`super::typed_lowering`]), the reconstruction
//! ([`super::reconstruct`]), and — the new pieces here — the native-fold **dispatcher** (Step E:
//! `APPLY-NATIVE-FOLD`, the fold-readiness guard, the progress weight) wired into
//! `EGraph::<L>::saturate_with_native`, with the three-way gate (Step F: non-fatal residual
//! `unsupported`, no native-eval short-circuit) and depth-scaled `max_iters`.
//!
//! The `EGraph<String>` path for every non-fold language is untouched (this function is reached
//! only for fold-bearing languages).

use mettail_ast::grammar::TermParam;
use mettail_ast::language::LanguageDef;
use mettail_ast::types::{EvalMode, TypeExpr};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::op_enum::{self, op_enum_ident, op_variant_ident};
use super::reconstruct::{self, build_fn};
use super::{category_lowering_fn, lit, rule_block, typed_lowering};
use crate::gen::term_ops::subst::{collect_category_variants, VariantKind};

/// A fold rule lowered to a native rewrite + dispatcher arm.
struct FoldRule<'a> {
    op_id: u32,
    output_cat: Ident,
    op_variant: Ident,
    params: Vec<FoldParam>,
    body: &'a syn::Expr,
}

/// How a fold body wants its input bound.
enum BindKind {
    /// Scalar native (`Int`/`Float`/…): reconstruct then `.try_eval()` to the native value
    /// (`i64`, …). No fold-readiness gate — `try_eval` recurses through unfolded subterms.
    Scalar,
    /// Collection native (`List`/`Bag`/`Map`): reconstruct, then extract the inner native
    /// collection (`Vec`/`HashBag`/`HashMapLit`) from the literal variant — the body operates
    /// on it (`.extend`/`.union`/…). Gated on fold-readiness (a collection arg may be a redex).
    Collection(Ident),
    /// Object (`Proc`, …): reconstruct to the typed AST `&Cat`. Gated on fold-readiness.
    Object,
}

/// A fold rule's typed input parameter.
struct FoldParam {
    name: Ident,
    category: Ident,
    bind: BindKind,
}

/// The folds lowered as native rules: `eval_mode == Fold`, every param a `Simple`/`Base` typed
/// parameter, and at least one OBJECT (non-native) param (so a child must be reconstructed —
/// pure-native folds keep the existing `try_eval` path). Stable `op_id` = declaration index.
fn collect_fold_rules(language: &LanguageDef) -> Vec<FoldRule<'_>> {
    let mut out = Vec::new();
    let mut op_id = 0u32;
    for rule in &language.terms {
        if rule.eval_mode != Some(EvalMode::Fold) {
            continue;
        }
        let Some(body) = rule.rust_code.as_ref().map(|rc| &rc.code) else { continue };
        let Some(ctx) = rule.term_context.as_ref() else { continue };
        let mut params = Vec::new();
        let mut all_simple = true;
        for p in ctx {
            match p {
                TermParam::Simple { name, ty: TypeExpr::Base(category) } => {
                    let lt = language.get_type(category);
                    let native_type = lt.and_then(|t| t.native_type.as_ref());
                    let is_collection = lt.and_then(|t| t.collection_kind.as_ref()).is_some();
                    let bind = match (native_type, is_collection) {
                        (Some(nt), true) => BindKind::Collection(crate::gen::generate_literal_label(nt)),
                        (Some(_), false) => BindKind::Scalar,
                        (None, _) => BindKind::Object,
                    };
                    params.push(FoldParam { name: name.clone(), category: category.clone(), bind });
                },
                _ => {
                    all_simple = false;
                    break;
                },
            }
        }
        // Lower a fold iff at least one param needs reconstruction (object or collection) —
        // pure-scalar folds (`-a : Int`) keep the existing `try_eval` path.
        if !all_simple || !params.iter().any(|p| !matches!(p.bind, BindKind::Scalar)) {
            continue;
        }
        out.push(FoldRule {
            op_id,
            output_cat: rule.category.clone(),
            op_variant: op_variant_ident(&rule.category, &rule.label),
            params,
            body,
        });
        op_id += 1;
    }
    out
}

/// The `mettail_runtime` native-output numeric-cast reductions (generated cast fold bodies
/// call these). They return `Option<scalar>` — a `None` defers — but carry no `try` segment,
/// so they are recognized by name in [`body_returns_option`]. Their object-output siblings
/// (`proc_int_bin`, …) return a `Proc` (not an `Option`) and MUST NOT appear here.
const NATIVE_NUMERIC_CAST_FNS: &[&str] = &[
    "numeric_int_bin_i32",
    "numeric_int_bin_i64",
    "numeric_uint_bin_u32",
    "numeric_float_bin",
    "numeric_fixed_bin",
    "numeric_bigint_unary",
    "numeric_bigrat_unary",
];

/// Whether a fold body's outermost form returns an `Option` that the dispatcher must `?`-unwrap
/// (a `None` defers the fold). Precise for the fold-body conventions: a `try_*(..)` call or
/// method, or a bare `Some(..)`/`None`, or a `mettail_runtime` native numeric-cast reduction
/// ([`NATIVE_NUMERIC_CAST_FNS`]), recursing through a block's tail expression. A body that
/// `.expect()`s/`.unwrap()`s an inner `Option`, or returns a raw value (`(-a)`, `a.union(&b)`,
/// `{ … o }`, `proc_int_bin(..)`), is NOT an `Option` at the outermost position.
fn body_returns_option(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Block(b) => match b.block.stmts.last() {
            Some(syn::Stmt::Expr(e, None)) => body_returns_option(e),
            _ => false,
        },
        syn::Expr::Call(c) => match c.func.as_ref() {
            syn::Expr::Path(p) => p.path.segments.last().is_some_and(|s| {
                let n = s.ident.to_string();
                // The fallible-fold convention is any fn whose name has a `try` segment (a
                // `<lang>_try_<op>` or bare `try_*`); match `try` as a `_`-delimited segment.
                // The macro-generated numeric-cast adapters instead call the `mettail_runtime`
                // native-output reductions, which return `Option<scalar>` but carry no `try`
                // segment, so recognize them by name. Their object-output siblings (`proc_*`)
                // return a `Proc`, NOT an `Option`, and are deliberately EXCLUDED here.
                n.split('_').any(|seg| seg == "try")
                    || n == "Some"
                    || n == "None"
                    || NATIVE_NUMERIC_CAST_FNS.contains(&n.as_str())
            }),
            _ => false,
        },
        syn::Expr::MethodCall(m) => {
            let n = m.method.to_string();
            n.split('_').any(|seg| seg == "try")
        },
        syn::Expr::Paren(p) => body_returns_option(&p.expr),
        _ => false,
    }
}

/// `__is_fold_redex` / `__is_value_op` / `__weigh` / `__class_is_fold_value` — the fold-readiness
/// guard and the progress weight, keyed off the generated op-enum.
fn generate_helpers(language: &LanguageDef, folds: &[FoldRule<'_>]) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fold_heads: Vec<TokenStream> = folds
        .iter()
        .map(|f| {
            let v = &f.op_variant;
            quote! { #enum_id::#v }
        })
        .collect();
    let var_pats: Vec<TokenStream> = language
        .types
        .iter()
        .flat_map(|ty| {
            let cat = ty.name.clone();
            let enum_id = enum_id.clone();
            collect_category_variants(&cat, language)
                .into_iter()
                .filter_map(move |variant| match variant {
                    VariantKind::Var { label } => {
                        let v = op_variant_ident(&cat, &label);
                        Some(quote! { #enum_id::#v(..) })
                    },
                    _ => None,
                })
        })
        .collect();

    let is_fold_redex_body = if fold_heads.is_empty() {
        quote! { false }
    } else {
        quote! { ::core::matches!(__op, #(#fold_heads)|*) }
    };
    let is_var_body = if var_pats.is_empty() {
        quote! { false }
    } else {
        quote! { ::core::matches!(__op, #(#var_pats)|*) }
    };

    quote! {
        fn __is_fold_redex(__op: &#enum_id) -> bool { #is_fold_redex_body }
        fn __is_var_op(__op: &#enum_id) -> bool { #is_var_body }
        // A value op is a fold input that is fully reduced: not a fold redex and not a free
        // variable (a var defers — matches `int(x, 8)` staying unchanged). `Cast*` literals,
        // `Err`, and structural non-fold constructors are values.
        fn __is_value_op(__op: &#enum_id) -> bool {
            !__is_fold_redex(__op) && !__is_var_op(__op)
        }
        // Progress weight: a fold redex is strictly more expensive than its reduced value, so
        // funded 1-best extraction surfaces the normal form once the fold has fired.
        fn __weigh(__n: &::dovetail::egraph::ENode<#enum_id>) -> ::rigail::TropicalWeight {
            ::rigail::TropicalWeight(if __is_fold_redex(&__n.op) { 100.0 } else { 1.0 })
        }
        // Fold-readiness (no extraction): a class is value-ready iff some e-node in it is a
        // value op. After a fold fires (redex == value merged), the value node is present, so
        // the __weigh-weighted 1-best reconstructs the value.
        fn __class_is_fold_value(
            __eg: &::dovetail::egraph::EGraph<#enum_id>,
            __cls: ::dovetail::egraph::EClassId,
        ) -> bool {
            __eg.nodes(__cls).iter().any(|__n| __is_value_op(&__n.op))
        }
    }
}

/// The `vec![NativeRule { .. }]` expression and the dispatcher closure.
fn generate_native_rules_and_dispatch(
    language: &LanguageDef,
    folds: &[FoldRule<'_>],
) -> (TokenStream, TokenStream) {
    let enum_id = op_enum_ident(language);

    let native_rules: Vec<TokenStream> = folds
        .iter()
        .map(|f| {
            let op_variant = &f.op_variant;
            let op_id = f.op_id;
            let label = lit(&format!("{}::fold::{}", language.name, f.op_variant));
            let var_pats: Vec<TokenStream> = f
                .params
                .iter()
                .map(|p| {
                    let n = p.name.to_string();
                    quote! { ::dovetail::rules::Pattern::var(#n) }
                })
                .collect();
            quote! {
                ::dovetail::rules::NativeRule {
                    lhs: ::dovetail::rules::Pattern::app(#enum_id::#op_variant, vec![#(#var_pats),*]),
                    op: #op_id,
                    label: ::core::option::Option::Some(#label.to_string()),
                }
            }
        })
        .collect();

    let dispatch_arms: Vec<TokenStream> = folds
        .iter()
        .map(|f| {
            let op_id = f.op_id;
            let out_add = category_lowering_fn(&f.output_cat);
            let body = f.body;

            let cls_vars: Vec<Ident> =
                f.params.iter().map(|p| format_ident!("__cls_{}", p.name)).collect();
            let d_vars: Vec<Ident> =
                f.params.iter().map(|p| format_ident!("__d_{}", p.name)).collect();

            // 1. bind each param's class + gate object params on fold-readiness.
            let class_bindings: Vec<TokenStream> = f
                .params
                .iter()
                .zip(cls_vars.iter())
                .map(|(p, cls)| {
                    let nstr = p.name.to_string();
                    let gate = if matches!(p.bind, BindKind::Scalar) {
                        quote! {}
                    } else {
                        quote! {
                            if !__class_is_fold_value(__eg, #cls) {
                                return ::core::option::Option::None;
                            }
                        }
                    };
                    quote! {
                        let #cls = *__subst.get(#nstr)?;
                        #gate
                    }
                })
                .collect();

            // 2. extract all funded 1-best child derivations in ONE Extractor scope that drops
            //    before the mutable `__add` (A4 borrow discipline).
            let extract = quote! {
                let ( #(#d_vars),* ) = {
                    let mut __ex = ::dovetail::extract::Extractor::new(&*__eg, __weigh);
                    ( #( __ex.kth(__eg.find(#cls_vars), 0).value? ),* )
                };
            };

            // 3. bind each param BY NAME (the body references them): object → typed AST,
            //    native → `.try_eval()` to the native value.
            let param_binds: Vec<TokenStream> = f
                .params
                .iter()
                .zip(d_vars.iter())
                .map(|(p, dv)| {
                    let pname = &p.name;
                    let pcat = &p.category;
                    let bfn = build_fn(&p.category);
                    match &p.bind {
                        // Scalar (`Int`/…) and object (`Proc`) params bind a REFERENCE to the
                        // reconstructed category (`&Cat`, temporary-lifetime-extended). The fold
                        // body either pattern-matches it (`match a { Proc::… }` / `match &i {…}`
                        // via ref-ergonomics — no move out of the `Drop`-implementing category)
                        // or passes it on (`f(&a, w)` deref-coerces `&&Cat → &Cat`; the category
                        // impls `CastWidth`). Scalars are NOT `try_eval`'d and NOT gated —
                        // scalar arithmetic is native-output, never folds in-engine, so gating
                        // would defer forever; the body/`CastWidth` evaluates an unfolded arg.
                        BindKind::Scalar | BindKind::Object => {
                            quote! { let #pname = &#bfn(&#dv)?; }
                        },
                        // Collection params bind a reference to the inner native collection
                        // (`&Vec`/`&HashBag`/`&HashMapLit`) the body operates on (`.extend`/
                        // `.union`/…); `match &owned` avoids moving out of the `Drop` category.
                        BindKind::Collection(lit) => {
                            let owned = format_ident!("__owned_{}", pname);
                            quote! {
                                let #owned = #bfn(&#dv)?;
                                let #pname = match &#owned {
                                    #pcat::#lit(__v) => __v,
                                    _ => return ::core::option::Option::None,
                                };
                            }
                        },
                    }
                })
                .collect();

            // Native output (scalar `count(..) : Int` → `i64`, or collection `concat(..) : List`
            // → `Vec<Proc>`): the body returns the native value, so wrap it in the category's
            // literal constructor (`Int::NumLit` / `List::ListLit`) before lowering. Object
            // output (`Proc`): the body returns the category value directly.
            let out_type = language.get_type(&f.output_cat);
            let out_native = out_type.map(|t| t.native_type.is_some()).unwrap_or(false);
            let out_cat = &f.output_cat;
            // Some fold bodies are fallible (`try_*` returning `Option`, e.g. a Calculator cast
            // that may not be representable); `?` unwraps them — a `None` defers the fold (the
            // redex stays unreduced) rather than fabricating a value.
            let body_value = if body_returns_option(body) {
                quote! { ({ #body })? }
            } else {
                quote! { { #body } }
            };
            let result_handling = if out_native {
                let native_type = out_type
                    .and_then(|t| t.native_type.as_ref())
                    .expect("native output has a native type");
                let lit_label = crate::gen::generate_literal_label(native_type);
                quote! {
                    let __result = #out_cat::#lit_label(#body_value);
                    ::core::option::Option::Some(#out_add(__eg, &__result))
                }
            } else {
                quote! {
                    let __result = #body_value;
                    ::core::option::Option::Some(#out_add(__eg, &__result))
                }
            };

            quote! {
                #op_id => {
                    #(#class_bindings)*
                    #extract
                    #(#param_binds)*
                    #result_handling
                }
            }
        })
        .collect();

    let dispatch = quote! {
        |__op: ::dovetail::rules::NativeOpId,
         __eg: &mut ::dovetail::egraph::EGraph<#enum_id>,
         __subst: &::dovetail::rules::Subst|
         -> ::core::option::Option<::dovetail::egraph::EClassId> {
            match __op {
                #(#dispatch_arms)*
                _ => ::core::option::Option::None,
            }
        }
    };

    (quote! { vec![#(#native_rules),*] }, dispatch)
}

/// Generate the full typed `impl <Lang>Language { dovetail_report_for, dovetail_compiler_stage }`
/// + the op-enum, for a fold-bearing language.
pub(crate) fn generate_typed_dovetail_report(language: &LanguageDef) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let op_enum_decl = op_enum::generate_dovetail_op_enum(language);
    let language_struct = format_ident!("{}Language", language.name);
    let term_name = format_ident!("{}Term", language.name);
    let language_lit = lit(&language.name.to_string());

    let typed_category_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| typed_lowering::category_lowering_typed(language, &ty.name))
        .collect();
    let reconstruct_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| reconstruct::category_reconstruct(language, &ty.name))
        .collect();

    let folds = collect_fold_rules(language);
    let helpers = generate_helpers(language, &folds);
    let (native_rules_expr, dispatch) = generate_native_rules_and_dispatch(language, &folds);
    // Typed structural rules (congruence is automatic; host-routed Comm/Extrude land in the
    // dropped `unsupported` — NON-FATAL on the fold path).
    let (rules_expr, _unsupported) = rule_block(language, Some(&enum_id));

    let primary_cat = &language.types.first().expect("language has a type").name;
    let primary_add = category_lowering_fn(primary_cat);

    let root_block = if language.types.len() > 1 {
        let inner_enum = format_ident!("{}TermInner", language.name);
        let arms: Vec<TokenStream> = language
            .types
            .iter()
            .map(|ty| {
                let cat = &ty.name;
                let add_fn = category_lowering_fn(cat);
                quote! {
                    #inner_enum::#cat(value) => {
                        __max_depth = __max_depth.max(value.term_depth());
                        __roots.push(#add_fn(&mut eg, value));
                    }
                }
            })
            .collect();
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
            __max_depth = typed_term.0.term_depth();
            __roots.push(#primary_add(&mut eg, &typed_term.0));
        }
    };

    // A sound (generous) upper bound on the saturation passes a depth-`d` nested fold needs:
    // syntactic depth (no fold body synthesizes a new fold operator, so congruence cannot
    // deepen the chain) + a structural-rule slack + 1. `max_iters` (the caller's floor) is
    // taken as a lower bound. An over-estimate is harmless — saturation returns `Converged`
    // early on a zero-merge pass.
    let struct_slack = language.equations.len() * 2 + language.rewrites.len() + 8;

    quote! {
        // `op_enum_decl` carries `#[cfg(feature = "dovetail-codegen")]` on each of its items.
        #op_enum_decl

        #[cfg(feature = "dovetail-codegen")]
        impl #language_struct {
            /// Compile this language's generated typed AST into a checked runtime Dovetail
            /// report, reducing `fold` rules in-engine via native rewrites (Increment 2/3).
            pub fn dovetail_report_for(
                term: &dyn mettail_runtime::Term,
                max_iters: usize,
                max_nodes: usize,
            ) -> Result<mettail_runtime::RuntimeDovetailRunReport, String> {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("expected {}Term, got {:?}", #language_lit, term))?;

                #(#typed_category_fns)*
                #(#reconstruct_fns)*
                #helpers

                let mut eg = ::dovetail::egraph::EGraph::<#enum_id>::with_config(
                    ::dovetail::egraph::EGraphConfig { max_nodes },
                );

                let mut __roots = Vec::new();
                let mut __max_depth: u32 = 0;
                #root_block
                __roots.sort_unstable();
                __roots.dedup();
                if __roots.is_empty() {
                    return Err(format!(
                        "generated Dovetail compiler for language {} produced no roots",
                        #language_lit,
                    ));
                }

                let __iters = ((__max_depth as usize) + #struct_slack).max(max_iters);
                let rules = #rules_expr;
                let __native_rules = #native_rules_expr;
                let __dispatch = #dispatch;
                let sat = eg.saturate_with_native(&rules, &__native_rules, &__dispatch, __iters);
                if sat.outcome != ::dovetail::rules::SaturationOutcome::Converged {
                    return Err(format!(
                        "generated Dovetail saturation for language {} stopped before convergence: {:?}",
                        #language_lit,
                        sat.outcome,
                    ));
                }

                let mut extractor = ::dovetail::extract::Extractor::new(&eg, __weigh);
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
    use super::body_returns_option;

    #[test]
    fn native_numeric_cast_fns_classify_as_option() {
        // The generated native-output cast bodies (Calculator) call these; they return
        // `Option<scalar>`, so the dispatcher must `?`-unwrap (a `None` defers).
        for body in [
            quote::quote!(mettail_runtime::numeric_int_bin_i32(&a, w)),
            quote::quote!(mettail_runtime::numeric_int_bin_i64(&a, w)),
            quote::quote!(mettail_runtime::numeric_uint_bin_u32(&a, w)),
            quote::quote!(mettail_runtime::numeric_float_bin(&a, w)),
            quote::quote!(mettail_runtime::numeric_fixed_bin(&a, w)),
            quote::quote!(mettail_runtime::numeric_bigint_unary(&a)),
            quote::quote!(mettail_runtime::numeric_bigrat_unary(&a)),
            quote::quote!({ mettail_runtime::numeric_float_bin(&a, w) }),
        ] {
            let e: syn::Expr = syn::parse2(body).expect("parse fold body");
            assert!(body_returns_option(&e), "native numeric cast must be Option-returning");
        }
    }

    #[test]
    fn object_output_cast_fns_do_not_classify_as_option() {
        // The generated object-output cast bodies (RhoCalc) call these; they return a `Proc`
        // directly (`Proc::Err` on failure), so they MUST NOT be `?`-unwrapped.
        for body in [
            quote::quote!(mettail_runtime::proc_int_bin(&a, w)),
            quote::quote!(mettail_runtime::proc_float_bin(&a, w)),
            quote::quote!(mettail_runtime::proc_bigint_unary(&a)),
            quote::quote!({ mettail_runtime::proc_int_bin(&a, w) }),
        ] {
            let e: syn::Expr = syn::parse2(body).expect("parse fold body");
            assert!(!body_returns_option(&e), "object-output cast must not be Option-returning");
        }
    }

    #[test]
    fn try_convention_classifies_as_option() {
        // Any fold body calling a `try_*`-segment fn is Option-returning (a `None` defers) — a
        // general Rust idiom, independent of which language wrote the body.
        let e: syn::Expr = syn::parse2(quote::quote!(try_widen(&a, w))).expect("parse fold body");
        assert!(body_returns_option(&e));
    }
}
