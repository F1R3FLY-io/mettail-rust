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
use super::{
    category_lowering_fn, is_substitution_rewrite, lit, rule_block, subst_rewrite_native_lhs,
    to_snake, typed_lowering, SubstRewrite,
};
use crate::gen::term_ops::subst::{collect_category_variants, VariantKind};

/// A fold rule lowered to a native rewrite + dispatcher arm.
struct FoldRule<'a> {
    op_id: u32,
    output_cat: Ident,
    op_variant: Ident,
    params: Vec<FoldParam>,
    body: &'a syn::Expr,
    /// True when every param is native-scalar AND the output is native-scalar (e.g.
    /// `AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;`). The body is written
    /// against the native values, so the dispatcher binds operands via `try_eval()`
    /// (not `&Cat`) and `safeify`s the body (overflow / div-by-zero → `None` → defer).
    is_pure_native_arith: bool,
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
        let Some(body) = rule.rust_code.as_ref().map(|rc| &rc.code) else {
            continue;
        };
        let Some(ctx) = rule.term_context.as_ref() else {
            continue;
        };
        let mut params = Vec::new();
        let mut all_simple = true;
        for p in ctx {
            match p {
                TermParam::Simple { name, ty: TypeExpr::Base(category) } => {
                    let lt = language.get_type(category);
                    let native_type = lt.and_then(|t| t.native_type.as_ref());
                    let is_collection = lt.and_then(|t| t.collection_kind.as_ref()).is_some();
                    let bind = match (native_type, is_collection) {
                        (Some(nt), true) => {
                            BindKind::Collection(crate::gen::generate_literal_label(nt))
                        },
                        (Some(_), false) => BindKind::Scalar,
                        (None, _) => BindKind::Object,
                    };
                    params.push(FoldParam {
                        name: name.clone(),
                        category: category.clone(),
                        bind,
                    });
                },
                _ => {
                    all_simple = false;
                    break;
                },
            }
        }
        // Lower every fold whose params are all `Simple`/`Base` typed parameters. Post-P6
        // (Ascent retired), native-OUTPUT folds — including PURE-SCALAR arithmetic like
        // `AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;` — must reduce on the Dovetail
        // path too: their `![..]` bodies previously ran only in the retired Ascent backend, so
        // they evaluated nowhere after P6. (The old gate required at least one non-scalar param,
        // which skipped exactly these arithmetic folds.) A fold whose params are ALL native-scalar
        // with native-scalar output is `is_pure_native_arith`; the dispatcher binds its operands
        // via `try_eval()` and `safeify`s the body. Mixed / object / collection folds keep the
        // existing `&Cat` + `body_returns_option` path unchanged.
        if !all_simple || params.is_empty() {
            continue;
        }
        let out_lt = language.get_type(&rule.category);
        let is_pure_native_arith = params.iter().all(|p| matches!(p.bind, BindKind::Scalar))
            && out_lt.map_or(false, |t| t.native_type.is_some() && t.collection_kind.is_none());
        out.push(FoldRule {
            op_id,
            output_cat: rule.category.clone(),
            op_variant: op_variant_ident(&rule.category, &rule.label),
            params,
            body,
            is_pure_native_arith,
        });
        op_id += 1;
    }
    out
}

/// (E1.3) A substitution rewrite ([`SubstRewrite`]) lowered to a native rule + dispatcher arm,
/// carrying its assigned `op_id`. The `op_id` counter is SHARED with the folds (substitution
/// op-ids start at `folds.len()`), so every native rule across folds ∪ substitution rules has a
/// distinct id and its own dispatch arm.
struct SubstRule {
    op_id: u32,
    rewrite: SubstRewrite,
}

/// Collect the language's substitution rewrites ([`is_substitution_rewrite`]) as native rules,
/// assigning each an `op_id` STARTING AT `fold_count` (MF2: a shared counter across folds ∪
/// substitution rules). Source order is preserved (stable ids).
fn collect_substitution_rules(language: &LanguageDef, fold_count: usize) -> Vec<SubstRule> {
    let mut out = Vec::new();
    let mut op_id = fold_count as u32;
    for rw in &language.rewrites {
        if let Some(sr) = is_substitution_rewrite(language, rw) {
            out.push(SubstRule { op_id, rewrite: sr });
            op_id += 1;
        }
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

/// `__is_redex` / `__is_var_op` / `__is_value_op` / `__weigh` / `__class_is_fold_value` /
/// `__class_has_normal_form` — the fold/β-readiness guards and the progress weight, keyed off the
/// generated op-enum.
///
/// (E1.5 — MF1) The redex-head set is **folds ∪ substitution-rewrite LHS head ops**: a fold
/// redex (`f.op_variant`) OR the outermost constructor of a substitution rewrite's LHS
/// (`op_variant_ident(head_cat, head_label)`, e.g. `App` → `Term_App`). `__is_value_op` therefore
/// excludes a β-redex head, `__weigh` gives it 100.0, and `__class_is_fold_value` no longer treats
/// an un-reduced redex (an `App` whose function is still a `Lam`) as a value — so funded 1-best
/// extraction prefers the contractum once β has fired (without this, β fires in the e-graph but
/// extraction keeps selecting the redex and the whole extension silently fails).
fn generate_helpers(
    language: &LanguageDef,
    folds: &[FoldRule<'_>],
    substs: &[SubstRule],
) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let mut redex_heads: Vec<TokenStream> = folds
        .iter()
        .map(|f| {
            let v = &f.op_variant;
            quote! { #enum_id::#v }
        })
        .collect();
    // (MF1) Substitution-rewrite LHS head ops join the redex-head set so an un-reduced redex
    // (e.g. `App(Lam.., ..)`) is heavier than its contractum.
    for s in substs {
        let v = op_variant_ident(&s.rewrite.head_cat, &s.rewrite.head_label);
        redex_heads.push(quote! { #enum_id::#v });
    }
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

    let is_redex_body = if redex_heads.is_empty() {
        quote! { false }
    } else {
        quote! { ::core::matches!(__op, #(#redex_heads)|*) }
    };
    let is_var_body = if var_pats.is_empty() {
        quote! { false }
    } else {
        quote! { ::core::matches!(__op, #(#var_pats)|*) }
    };

    quote! {
        // (MF1) A REDEX head: a fold redex OR a substitution-rewrite LHS head (e.g. `App`). The
        // name is kept as `__is_fold_redex` for call-site stability; its set now also covers
        // β-redex heads (E1.5). An un-reduced `App(Lam.., ..)` therefore counts as a redex.
        fn __is_fold_redex(__op: &#enum_id) -> bool { #is_redex_body }
        fn __is_var_op(__op: &#enum_id) -> bool { #is_var_body }
        // A value op is fully reduced: not a redex (fold or β) and not a free variable (a var
        // defers a FOLD — `int(x, 8)` stays unchanged). `Cast*` literals, `Err`, structural
        // non-fold/non-redex constructors are values.
        fn __is_value_op(__op: &#enum_id) -> bool {
            !__is_fold_redex(__op) && !__is_var_op(__op)
        }
        // Progress weight: a redex (fold or β) is strictly more expensive than its reduced
        // result, so funded 1-best extraction surfaces the normal form once the redex has fired.
        fn __weigh(__n: &::dovetail::egraph::ENode<#enum_id>) -> ::rigail::TropicalWeight {
            ::rigail::TropicalWeight(if __is_fold_redex(&__n.op) { 100.0 } else { 1.0 })
        }
        // Fold-readiness (no extraction): a class is value-ready iff some e-node in it is a
        // value op. After a fold/β fires (redex == result merged), the value node is present, so
        // the __weigh-weighted 1-best reconstructs the value. Used to gate a fold's object
        // operands AND a substitution's SCOPE (a binder is a value op; an un-reduced redex is
        // not — so a substitution defers until its scope reduces to a binder).
        fn __class_is_fold_value(
            __eg: &::dovetail::egraph::EGraph<#enum_id>,
            __cls: ::dovetail::egraph::EClassId,
        ) -> bool {
            __eg.nodes(__cls).iter().any(|__n| __is_value_op(&__n.op))
        }
        // (E1.4) Normal-form readiness for a SUBSTITUTION REPLACEMENT operand: a class is ready
        // iff some e-node in it is NOT a redex — i.e. it contains a normal form. This ADMITS a
        // bare variable (a free variable IS a normal form — `(lam x. x, y)` must substitute the
        // free `y`), unlike `__class_is_fold_value` which excludes vars (a var defers a fold).
        // It still defers on an un-reduced redex argument, preserving the bottom-up saturation
        // MF1 relies on. (Unused-allow because a fold-only language has no substitution rules.)
        #[allow(dead_code)]
        fn __class_has_normal_form(
            __eg: &::dovetail::egraph::EGraph<#enum_id>,
            __cls: ::dovetail::egraph::EClassId,
        ) -> bool {
            __eg.nodes(__cls).iter().any(|__n| !__is_fold_redex(&__n.op))
        }
    }
}

/// The `vec![NativeRule { .. }]` expression and the dispatcher closure for BOTH the fold native
/// rules (`folds`) and the substitution native rules (`substs`, E1.4). Their `op_id`s are
/// disjoint (substitution ids start at `folds.len()`), so the dispatch match has one arm per
/// rule across both kinds.
fn generate_native_rules_and_dispatch(
    language: &LanguageDef,
    folds: &[FoldRule<'_>],
    substs: &[SubstRule],
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

            let cls_vars: Vec<Ident> = f
                .params
                .iter()
                .map(|p| format_ident!("__cls_{}", p.name))
                .collect();
            let d_vars: Vec<Ident> = f
                .params
                .iter()
                .map(|p| format_ident!("__d_{}", p.name))
                .collect();

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
                    // Pure-native-arith fold: bind the NATIVE value the body needs (`a + b` on
                    // `i32`/…). `try_eval()` recurses through unfolded subterms (so a single root
                    // fold computes nested arithmetic); the trailing `?` defers the fold if a
                    // child is not yet reducible to a value. Mirrors the interpreter eval binding.
                    if f.is_pure_native_arith {
                        return quote! { let #pname = #bfn(&#dv)?.try_eval()?; };
                    }
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
            // Pure-native-arith bodies are `safeify`d: arithmetic operators become
            // `SafeArith::safe_*(..)?` and the whole body is wrapped in an `Option`-returning
            // closure, so overflow / div-by-zero / NaN yields `None` → the fold defers (the redex
            // is left unreduced, the report stays Complete) instead of panicking inside the engine
            // closure. This matches the interpreter's `safeify_and_wrap` body handling. Other
            // folds keep the raw / `try_*` body convention.
            let body_value = if f.is_pure_native_arith {
                let safeified = crate::gen::native::rust_code_rewrite::safeify_and_wrap(body);
                quote! { (#safeified)? }
            } else if body_returns_option(body) {
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

    // (E1.4) Substitution native rules + dispatch arms.
    let subst_native_rules: Vec<TokenStream> = substs
        .iter()
        .map(|s| subst_native_rule(language, s, &enum_id))
        .collect::<Result<Vec<_>, _>>()
        .unwrap_or_else(|reason| {
            // A substitution rewrite that passed `is_substitution_rewrite` but whose LHS does not
            // lower (e.g. an unsupported metapattern slipped through) is a generator bug, surfaced
            // as a build error rather than a silently-missing rule.
            vec![quote! { compile_error!(#reason); }]
        });
    let subst_dispatch_arms: Vec<TokenStream> =
        substs.iter().map(|s| subst_dispatch_arm(s)).collect();

    let dispatch = quote! {
        |__op: ::dovetail::rules::NativeOpId,
         __eg: &mut ::dovetail::egraph::EGraph<#enum_id>,
         __subst: &::dovetail::rules::Subst|
         -> ::core::option::Option<::dovetail::egraph::EClassId> {
            match __op {
                #(#dispatch_arms)*
                #(#subst_dispatch_arms)*
                _ => ::core::option::Option::None,
            }
        }
    };

    (quote! { vec![#(#native_rules,)* #(#subst_native_rules),*] }, dispatch)
}

/// (E1.4) The `NativeRule` for a substitution rewrite. Its LHS binds the redex (`App(var fun,
/// var arg)`) — the binder sub-pattern collapsed to bind the WHOLE binder e-class (see
/// [`subst_rewrite_native_lhs`]); its op is the substitution `op_id` (≥ `folds.len()`); its
/// label is the rewrite's `<Lang>::rewrite::<name>`.
fn subst_native_rule(
    language: &LanguageDef,
    s: &SubstRule,
    enum_id: &Ident,
) -> Result<TokenStream, String> {
    let op_id = s.op_id;
    let label = lit(&s.rewrite.label);
    let lhs = subst_rewrite_native_lhs(language, &s.rewrite, enum_id)?;
    Ok(quote! {
        ::dovetail::rules::NativeRule {
            lhs: #lhs,
            op: #op_id,
            label: ::core::option::Option::Some(#label.to_string()),
        }
    })
}

/// (E1.4 — the dropped-`Extractor`-scope-then-mutate discipline) The dispatch arm for a
/// substitution rewrite. Mirrors the fold dispatch arm structure (gate operand classes, extract
/// child derivations in ONE dropped `Extractor` scope, reconstruct, mutate via `__add`), but the
/// "body" is the generated `substitute_<binder_var_cat>` / `multi_substitute_<binder_var_cat>`:
///
///  1. bind the scope class + each replacement class from `__subst`; gate the scope on
///     `__class_is_fold_value` (it must reduce to a binder VALUE, not an un-reduced redex) and
///     each replacement on `__class_has_normal_form` (admits a bare variable — a free variable is
///     a normal form — while still deferring an un-reduced redex argument);
///  2. `kth(.., 0)`-extract all child derivations in ONE `Extractor` scope that DROPS before the
///     mutable `__add` (A4 borrow discipline);
///  3. reconstruct the scope via `build_<binder_cat>_d` and each replacement via
///     `build_<binder_var_cat>_d`; `let binder_cat::binder_label(scope) = … else return None`;
///  4. `scope.unbind()` → `(binder, body)` (single) / `(binders, body)` (multi); run
///     `(*body).substitute_<binder_var_cat>(&binder.0, &arg)` (single) or, with an ARITY ASSERT,
///     `multi_substitute_<binder_var_cat>(&vars, &args)` (multi);
///  5. re-add the resulting `body_cat` via `__mettail_dovetail_add_<body_cat>` and return its
///     e-class — the contractum the engine merges with the redex's class.
fn subst_dispatch_arm(s: &SubstRule) -> TokenStream {
    let op_id = s.op_id;
    let sr = &s.rewrite;
    let scope_var = sr.scope_var.to_string();
    let binder_cat = &sr.binder_cat;
    let binder_label = &sr.binder_label;
    let body_cat = &sr.body_cat;
    let body_add = category_lowering_fn(body_cat);
    let binder_build = build_fn(binder_cat);

    // Replacement category build fns + class/derivation idents.
    let repl_cls: Vec<Ident> = (0..sr.repl_vars.len())
        .map(|i| format_ident!("__rcls_{i}"))
        .collect();
    let repl_d: Vec<Ident> = (0..sr.repl_vars.len())
        .map(|i| format_ident!("__rd_{i}"))
        .collect();
    let repl_build = build_fn(&sr.binder_var_cat);

    // 1. class bindings + gates.
    let scope_cls_binding = quote! {
        let __scls = *__subst.get(#scope_var)?;
        if !__class_is_fold_value(__eg, __scls) {
            return ::core::option::Option::None;
        }
    };
    let repl_cls_bindings: Vec<TokenStream> = sr
        .repl_vars
        .iter()
        .zip(repl_cls.iter())
        .map(|(rv, cls)| {
            let nstr = rv.to_string();
            quote! {
                let #cls = *__subst.get(#nstr)?;
                if !__class_has_normal_form(__eg, #cls) {
                    return ::core::option::Option::None;
                }
            }
        })
        .collect();

    // 2. extract all funded 1-best child derivations in ONE Extractor scope (drops before __add).
    let extract = quote! {
        let (__sd, #(#repl_d),*) = {
            let mut __ex = ::dovetail::extract::Extractor::new(&*__eg, __weigh);
            (
                __ex.kth(__eg.find(__scls), 0).value?,
                #( __ex.kth(__eg.find(#repl_cls), 0).value? ),*
            )
        };
    };

    // 3. reconstruct scope (must be the binder) + replacements. The reconstructed `body_cat`
    //    impls `Drop`, so we match the binder variant BY REFERENCE and clone the inner `Scope`
    //    (which `unbind` consumes by value) — mirroring the normalize.rs β assemble arm, which
    //    likewise ref-matches to avoid moving out of a `Drop` category.
    let scope_reconstruct = quote! {
        let __scope_term = #binder_build(&__sd)?;
        let __scope = match &__scope_term {
            #binder_cat::#binder_label(__s) => __s.clone(),
            _ => return ::core::option::Option::None,
        };
    };
    let repl_reconstruct: Vec<TokenStream> = repl_d
        .iter()
        .enumerate()
        .map(|(i, dv)| {
            let arg = format_ident!("__arg_{i}");
            quote! { let #arg = #repl_build(&#dv)?; }
        })
        .collect();
    let arg_idents: Vec<Ident> = (0..sr.repl_vars.len())
        .map(|i| format_ident!("__arg_{i}"))
        .collect();

    // 4. unbind + substitute (single vs multi).
    let subst_body = if sr.multi {
        let multi_subst = format_ident!("multi_substitute_{}", to_snake(&sr.binder_var_cat.to_string()));
        let arity = sr.repl_vars.len();
        quote! {
            let (__binders, __body) = __scope.unbind();
            // (MF5/arity) A multi-binder substitution is well-typed only when the binder arity
            // matches the replacement count; a mismatch defers (returns None) rather than
            // panicking inside the engine closure.
            if __binders.len() != #arity {
                return ::core::option::Option::None;
            }
            let __vars: ::std::vec::Vec<&::mettail_runtime::FreeVar<String>> =
                __binders.iter().map(|__b| &__b.0).collect();
            let __args = vec![#(#arg_idents),*];
            let __result = (*__body).#multi_subst(&__vars, &__args);
        }
    } else {
        let single_subst = format_ident!("substitute_{}", to_snake(&sr.binder_var_cat.to_string()));
        let arg0 = &arg_idents[0];
        quote! {
            let (__binder, __body) = __scope.unbind();
            let __result = (*__body).#single_subst(&__binder.0, &#arg0);
        }
    };

    // 5. re-add the substituted body and return its e-class.
    quote! {
        #op_id => {
            #scope_cls_binding
            #(#repl_cls_bindings)*
            #extract
            #scope_reconstruct
            #(#repl_reconstruct)*
            #subst_body
            ::core::option::Option::Some(#body_add(__eg, &__result))
        }
    }
}

/// (E2.2) Generate the `dovetail_normal_term` method body for a fold-bearing language.
///
/// `dovetail_normal_term(term, max_iters, max_nodes) -> Result<Box<dyn Term>, String>` reuses
/// the `dovetail_report_for` saturation prologue VERBATIM (downcast → lower roots →
/// `saturate_with_native` weighted by `__weigh`), then — instead of projecting a runtime report
/// — extracts each root's funded 1-best derivation and reconstructs it back into a typed AST term
/// via the generated `__mettail_dovetail_build_<cat>_d`, wrapping it in `<Lang>Term`.
///
/// Fail-closed: returns `Err` if saturation does not `Converge`, if any root extraction is
/// `BoundedByCycleCut`, or if reconstruction returns `None` (a stuck term the inverse cannot
/// recover — e.g. an opaque/`Vec`/`HashSet`/`HashMap` field). Multi-type languages reconstruct
/// each `all_alts()` alternative under its own category and reassemble the distinct results into
/// `<Lang>TermInner::Ambiguous` (deduplicated by semantic key), mirroring
/// `rholang-runtime/src/rhocalc_ast.rs`'s `lower_proc_alternatives`.
fn generate_dovetail_normal_term(language: &LanguageDef, struct_slack: usize) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let term_name = format_ident!("{}Term", language.name);
    let inner_enum = format_ident!("{}TermInner", language.name);
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
    // (E1.3) Substitution rules share the native op-id counter with the folds (ids start at
    // `folds.len()`), so the helpers (redex-head set) and the native-rule/dispatcher generator
    // both see folds ∪ substitution rules.
    let substs = collect_substitution_rules(language, folds.len());
    let helpers = generate_helpers(language, &folds, &substs);
    let (native_rules_expr, dispatch) =
        generate_native_rules_and_dispatch(language, &folds, &substs);
    let (rules_expr, _unsupported) = rule_block(language, Some(&enum_id));

    let primary_cat = &language.types.first().expect("language has a type").name;
    let primary_add = category_lowering_fn(primary_cat);
    let primary_build = build_fn(primary_cat);

    // Per-language root lowering + reconstruction. For a single-type language the root IS the
    // primary category (so `<Lang>Term(rebuilt)` wraps it directly). For a multi-type language
    // each `all_alts()` alternative is lowered under its own category, the category index is
    // tracked alongside the root e-class, and after extraction the per-category
    // `build_<cat>_d` reconstructs it and re-wraps it into `<Lang>TermInner::<cat>`.
    let multi = language.types.len() > 1;
    let (lower_roots, reconstruct_wrap) = if multi {
        let lower_arms: Vec<TokenStream> = language
            .types
            .iter()
            .enumerate()
            .map(|(idx, ty)| {
                let cat = &ty.name;
                let add_fn = category_lowering_fn(cat);
                let idx = idx as u32;
                quote! {
                    #inner_enum::#cat(value) => {
                        __max_depth = __max_depth.max(value.term_depth());
                        __roots.push((#add_fn(&mut eg, value), #idx));
                    }
                }
            })
            .collect();
        let rebuild_arms: Vec<TokenStream> = language
            .types
            .iter()
            .enumerate()
            .map(|(idx, ty)| {
                let cat = &ty.name;
                let build = build_fn(cat);
                let idx = idx as u32;
                quote! {
                    #idx => {
                        let __rebuilt = #build(&__derivation).ok_or_else(|| format!(
                            "generated Dovetail normal-form reconstruction for language {} failed (stuck term)",
                            #language_lit,
                        ))?;
                        #inner_enum::#cat(__rebuilt)
                    }
                }
            })
            .collect();
        let lower = quote! {
            // (root e-class, category index) per parse alternative.
            let mut __roots: Vec<(::dovetail::egraph::EClassId, u32)> = Vec::new();
            let mut __max_depth: u32 = 0;
            for __alt in typed_term.0.all_alts() {
                match __alt {
                    #(#lower_arms)*
                    #inner_enum::Ambiguous(_) => unreachable!(
                        "all_alts() returns flat alternatives, not nested Ambiguous"
                    ),
                }
            }
        };
        let reconstruct = quote! {
            // Reconstruct each root under its own category, dedup distinct alternatives by
            // semantic key, and reassemble into a single `<Lang>TermInner` (a bare inner for a
            // singleton, `Ambiguous` for 2+). Mirrors `lower_proc_alternatives`.
            let mut __seen: ::std::collections::BTreeSet<Vec<u8>> = ::std::collections::BTreeSet::new();
            let mut __alts: Vec<#inner_enum> = Vec::new();
            for (__root, __cat_idx) in __roots {
                let __extracted = {
                    let mut __extractor = ::dovetail::extract::Extractor::new(&eg, __weigh);
                    __extractor.funded_best(eg.find(__root))
                };
                if __extracted.completeness
                    == ::dovetail::extract::ExtractionCompleteness::BoundedByCycleCut
                {
                    return Err(format!(
                        "generated Dovetail normal-form extraction for language {} hit a cycle cut",
                        #language_lit,
                    ));
                }
                let __derivation = __extracted.value.ok_or_else(|| format!(
                    "generated Dovetail normal-form extraction for language {} produced no derivation",
                    #language_lit,
                ))?;
                let __inner = match __cat_idx {
                    #(#rebuild_arms)*
                    _ => unreachable!("category index out of range"),
                };
                let mut __hasher = ::mettail_runtime::FramedSemanticKeyHasher::default();
                __inner.semantic_hash(&mut __hasher);
                if __seen.insert(__hasher.into_key()) {
                    __alts.push(__inner);
                }
            }
            let __result_inner = match __alts.len() {
                0 => return Err(format!(
                    "generated Dovetail normal form for language {} produced no alternatives",
                    #language_lit,
                )),
                1 => __alts.pop().expect("checked len == 1"),
                _ => #inner_enum::Ambiguous(__alts),
            };
            Ok(Box::new(#term_name(__result_inner)) as Box<dyn mettail_runtime::Term>)
        };
        (lower, reconstruct)
    } else {
        // Single-type: the root is the primary category; `<Lang>Term` wraps it directly.
        let lower = quote! {
            let mut __roots: Vec<::dovetail::egraph::EClassId> = Vec::new();
            let mut __max_depth: u32 = typed_term.0.term_depth();
            __roots.push(#primary_add(&mut eg, &typed_term.0));
        };
        let reconstruct = quote! {
            let mut __seen: ::std::collections::BTreeSet<Vec<u8>> = ::std::collections::BTreeSet::new();
            let mut __results: Vec<#primary_cat> = Vec::new();
            for __root in __roots {
                let __extracted = {
                    let mut __extractor = ::dovetail::extract::Extractor::new(&eg, __weigh);
                    __extractor.funded_best(eg.find(__root))
                };
                if __extracted.completeness
                    == ::dovetail::extract::ExtractionCompleteness::BoundedByCycleCut
                {
                    return Err(format!(
                        "generated Dovetail normal-form extraction for language {} hit a cycle cut",
                        #language_lit,
                    ));
                }
                let __derivation = __extracted.value.ok_or_else(|| format!(
                    "generated Dovetail normal-form extraction for language {} produced no derivation",
                    #language_lit,
                ))?;
                let __rebuilt = #primary_build(&__derivation).ok_or_else(|| format!(
                    "generated Dovetail normal-form reconstruction for language {} failed (stuck term)",
                    #language_lit,
                ))?;
                use ::std::hash::Hash as _;
                let mut __hasher = ::mettail_runtime::FramedSemanticKeyHasher::default();
                __rebuilt.hash(&mut __hasher);
                if __seen.insert(__hasher.into_key()) {
                    __results.push(__rebuilt);
                }
            }
            let __result = match __results.len() {
                0 => return Err(format!(
                    "generated Dovetail normal form for language {} produced no result",
                    #language_lit,
                )),
                _ => __results.pop().expect("at least one result"),
            };
            Ok(Box::new(#term_name(__result)) as Box<dyn mettail_runtime::Term>)
        };
        (lower, reconstruct)
    };

    // `__roots` element type differs (tuple vs bare) between the multi/single arms, so the
    // empty-check is shared but uses the appropriate iterator emptiness.
    quote! {
        /// (E2.2) Reduce `term` to a typed Dovetail normal form and reconstruct it as a typed
        /// AST term. Same saturation as `dovetail_report_for`, but returns the reduced
        /// `<Lang>Term` (boxed) instead of a runtime report. Fail-closed: `Err` on
        /// non-convergence, a cycle cut, or a stuck (non-invertible) reconstruction.
        pub fn dovetail_normal_term(
            term: &dyn mettail_runtime::Term,
            max_iters: usize,
            max_nodes: usize,
        ) -> Result<Box<dyn mettail_runtime::Term>, String> {
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

            #lower_roots
            if __roots.is_empty() {
                return Err(format!(
                    "generated Dovetail normal form for language {} produced no roots",
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

            #reconstruct_wrap
        }
    }
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
    // (E1.3) Substitution rules share the native op-id counter with the folds (ids start at
    // `folds.len()`), so the helpers (redex-head set) and the native-rule/dispatcher generator
    // both see folds ∪ substitution rules.
    let substs = collect_substitution_rules(language, folds.len());
    let helpers = generate_helpers(language, &folds, &substs);
    let (native_rules_expr, dispatch) =
        generate_native_rules_and_dispatch(language, &folds, &substs);
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

    // (E2.2) The optional `dovetail_normal_term` method, emitted only when the MF7 gate
    // (`super::needs_normal_term`) holds. It reuses the saturation prologue and per-category
    // reconstruction verbatim, but returns the reduced term as a typed `Box<dyn Term>`
    // (wrapped `<Lang>Term`) instead of a `RuntimeDovetailRunReport`.
    let normal_term_method = if super::needs_normal_term(language) {
        generate_dovetail_normal_term(language, struct_slack)
    } else {
        TokenStream::new()
    };

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

                let mut __derivations = Vec::new();
                let mut __completeness = ::dovetail::extract::ExtractionCompleteness::Complete;
                for __root in __roots {
                    let mut extractor = ::dovetail::extract::Extractor::new(&eg, __weigh);
                    let __extracted = extractor.funded_best(eg.find(__root));
                    if __extracted.completeness
                        == ::dovetail::extract::ExtractionCompleteness::BoundedByCycleCut
                    {
                        __completeness =
                            ::dovetail::extract::ExtractionCompleteness::BoundedByCycleCut;
                    }
                    if let ::core::option::Option::Some(__derivation) = __extracted.value {
                        __derivations.push(__derivation);
                    }
                }

                let report = ::dovetail::report::report_from_extraction_with_rule_firings(
                    ::dovetail::extract::Extraction {
                        value: __derivations,
                        completeness: __completeness,
                    },
                    sat.rule_firings,
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

            #normal_term_method
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
