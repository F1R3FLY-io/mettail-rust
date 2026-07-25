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
    category_lowering_fn, is_comm_rewrite, is_nested_structural_ac_rewrite,
    is_structural_ac_rewrite, is_substitution_rewrite, lit, pattern_to_dovetail, rule_block,
    subst_rewrite_native_lhs, to_snake, typed_lowering, CommElementInfo, CommReductElement,
    CommRewrite, NestedStructuralAcRewrite, StructuralAcRewrite, SubstRewrite,
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

/// (A-3) A Comm rewrite ([`CommRewrite`]) lowered to a typed native rule + dispatch arm, carrying
/// its assigned `op_id`. The `op_id` counter is SHARED with the folds ∪ substitution rules (Comm
/// op-ids start at `folds.len() + substs.len()`), so every native rule across all three kinds has a
/// distinct id and its own dispatch arm.
struct CommRule {
    op_id: u32,
    rewrite: CommRewrite,
}

/// Collect the language's Comm rewrites ([`is_comm_rewrite`]) as typed native rules, assigning each
/// an `op_id` STARTING AT `start_op_id` (the shared counter after folds ∪ substitution rules).
/// Source order is preserved (stable ids).
fn collect_comm_rules(language: &LanguageDef, start_op_id: usize) -> Vec<CommRule> {
    let mut out = Vec::new();
    let mut op_id = start_op_id as u32;
    for rw in &language.rewrites {
        if let Some(cr) = is_comm_rewrite(language, rw) {
            out.push(CommRule { op_id, rewrite: cr });
            op_id += 1;
        }
    }
    out
}

/// (Stage 3d) A structural non-linear AC rewrite ([`StructuralAcRewrite`], Ambient `OpenRule`)
/// lowered to a typed native rule + dispatch arm, carrying its assigned `op_id`. The `op_id` counter
/// is SHARED with the folds ∪ substitution ∪ Comm rules (structural-AC op-ids start after them), so
/// every native rule across all kinds has a distinct id and its own dispatch arm.
struct StructuralAcRule {
    op_id: u32,
    rewrite: StructuralAcRewrite,
}

/// Collect the language's structural non-linear AC rewrites ([`is_structural_ac_rewrite`]) as typed
/// native rules, assigning each an `op_id` STARTING AT `start_op_id` (the shared counter after folds
/// ∪ substitution ∪ Comm rules). Source order is preserved (stable ids).
fn collect_structural_ac_rules(language: &LanguageDef, start_op_id: usize) -> Vec<StructuralAcRule> {
    let mut out = Vec::new();
    let mut op_id = start_op_id as u32;
    for rw in &language.rewrites {
        if let Some(sr) = is_structural_ac_rewrite(language, rw) {
            out.push(StructuralAcRule { op_id, rewrite: sr });
            op_id += 1;
        }
    }
    out
}

/// (Stage 4) A DEPTH-2 NESTED structural non-linear AC rewrite ([`NestedStructuralAcRewrite`], Ambient
/// `InRule`/`OutRule`) lowered to a typed native rule + dispatch arm, carrying its assigned `op_id`.
/// The `op_id` counter is SHARED with the folds ∪ substitution ∪ Comm ∪ flat-structural-AC rules
/// (nested op-ids start after them), so every native rule across all kinds has a distinct id.
struct NestedStructuralAcRule {
    op_id: u32,
    rewrite: NestedStructuralAcRewrite,
}

/// Collect the language's DEPTH-2 nested structural non-linear AC rewrites
/// ([`is_nested_structural_ac_rewrite`]) as typed native rules, assigning each an `op_id` STARTING AT
/// `start_op_id` (the shared counter after folds ∪ substitution ∪ Comm ∪ flat structural-AC rules).
/// Source order is preserved (stable ids).
fn collect_nested_structural_ac_rules(
    language: &LanguageDef,
    start_op_id: usize,
) -> Vec<NestedStructuralAcRule> {
    let mut out = Vec::new();
    let mut op_id = start_op_id as u32;
    for rw in &language.rewrites {
        if let Some(nr) = is_nested_structural_ac_rewrite(language, rw) {
            out.push(NestedStructuralAcRule { op_id, rewrite: nr });
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

/// Peel redundant single-tail-expression `{ … }` block wrappers off a fold body so the report
/// emitters below supply bracing exactly once. A body written as `![{ e }]` — or a macro-
/// synthesized `{ mettail_runtime::numeric_int_bin_i32(a, w) }` — is a `syn::Expr::Block`; splicing
/// it under an extra `{ · }` / `({ · })?` / `#ctor( · )` yields the `{ { e } }` / `({ { e } })?` /
/// `#ctor({ e })` shapes that `unused_braces` flags. Unwrapping a block whose sole content is a
/// trailing expression (no `let`s, no trailing `;`, no label/attrs) is exactly the semantics-
/// preserving rewrite the lint certifies (`{ e }` ≡ `e` in expression position when `e` binds
/// nothing); every other body is returned unchanged (its braces are load-bearing).
fn unwrap_fold_body_block(body: &syn::Expr) -> &syn::Expr {
    let mut current = body;
    loop {
        match current {
            syn::Expr::Block(b)
                if b.attrs.is_empty() && b.label.is_none() && b.block.stmts.len() == 1 =>
            {
                match &b.block.stmts[0] {
                    syn::Stmt::Expr(inner, None) => current = inner,
                    _ => return current,
                }
            },
            _ => return current,
        }
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
    comms: &[CommRule],
    structural_acs: &[StructuralAcRule],
    nested_structural_acs: &[NestedStructuralAcRule],
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
    // (A-3 / MF1) The Comm BINDER (receive) element head — present in the redex bag, CONSUMED by
    // the COMM (`(PFor N cont)` is gone from `op{ cont[Q/y], ...rest }`) — joins the redex-head
    // set. So a bag carrying the un-communicated receive is strictly heavier than the communicated
    // bag, and funded 1-best extraction reports the reduced bag `op{ cont[Q/y], ...rest }` as the
    // firing's contractum (`resolve_rewrite_justifications` roots the contractum at the firing's
    // ROOT class), from which the Comm σ-injection recovers `cont[Q/y]`.
    for c in comms {
        let element = &c.rewrite.elements[c.rewrite.binder_element_index];
        let v = op_variant_ident(&element.category, &element.constructor);
        redex_heads.push(quote! { #enum_id::#v });
    }
    // (Stage 3d / MF1) EVERY structured element head of a structural-AC rewrite is CONSUMED by the
    // firing (Ambient's `{(open N P), N[Q], ...rest}` becomes `{P, Q, ...rest}` — neither `open` nor
    // `amb` survives), so ALL of them join the redex-head set. A bag carrying an un-opened element is
    // then strictly heavier than the restructured bag, so funded 1-best extraction reports the
    // restructured bag `op{ r0, …, ...rest }` as the firing's contractum.
    for s in structural_acs {
        for element in &s.rewrite.elements {
            let v = op_variant_ident(&element.category, &element.constructor);
            redex_heads.push(quote! { #enum_id::#v });
        }
    }
    // (Stage 4 / MF1) For a DEPTH-2 nested structural-AC rewrite the RESTRUCTURED contractum PRESERVES
    // the ambient/par heads (`PAmb`/`PPar` appear in BOTH sides) but DISSOLVES the capability
    // (`PIn`/`POut` appears in the redex, gone from the contractum). So ONLY the CONSUMED heads
    // (`consumed_heads` = LHS heads \ RHS heads) join the redex-head set — a bag still carrying the
    // un-consumed capability is then strictly heavier than the restructured bag, so funded 1-best
    // extraction reports the restructured operand as the firing's contractum. (Adding the persisting
    // `PAmb` would wrongly weight the contractum too, so it is EXCLUDED — the set difference is exact.)
    for s in nested_structural_acs {
        for (category, constructor) in &s.rewrite.consumed_heads {
            let v = op_variant_ident(category, constructor);
            redex_heads.push(quote! { #enum_id::#v });
        }
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
    comms: &[CommRule],
    structural_acs: &[StructuralAcRule],
    nested_structural_acs: &[NestedStructuralAcRule],
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
            // A single binding needs no wrapping tuple: `let (x) = { (e) }` trips `unused_parens`
            // on both the pattern and the block return value. Emit the bare form. Two-or-more
            // bindings are a genuine tuple `(a, b, …)` (parens load-bearing); zero bindings give
            // the unit pattern `let () = { () }` — neither is flagged — so both keep the template.
            let extract = if d_vars.len() == 1 {
                let d = &d_vars[0];
                let cls = &cls_vars[0];
                quote! {
                    let #d = {
                        let mut __ex = ::dovetail::extract::Extractor::new(&*__eg, __weigh);
                        __ex.kth(__eg.find(#cls), 0).value?
                    };
                }
            } else {
                quote! {
                    let ( #(#d_vars),* ) = {
                        let mut __ex = ::dovetail::extract::Extractor::new(&*__eg, __weigh);
                        ( #( __ex.kth(__eg.find(#cls_vars), 0).value? ),* )
                    };
                }
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
            // Peel a redundant `{ … }` off the body so the wrappers below don't double-brace
            // (`({ { e } })?` / `{ { e } }` / `#ctor({ e })`). See `unwrap_fold_body_block`.
            let body_inner = unwrap_fold_body_block(body);
            let body_value = if f.is_pure_native_arith {
                let safeified = crate::gen::native::rust_code_rewrite::safeify_and_wrap(body);
                quote! { (#safeified)? }
            } else if body_returns_option(body_inner) {
                quote! { (#body_inner)? }
            } else {
                quote! { #body_inner }
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

    // (A-3) Comm native rules + dispatch arms. Their `op_id`s are disjoint from the folds and
    // substitution rules (Comm ids start at `folds.len() + substs.len()`), so the dispatch match
    // has one arm per rule across all three native kinds.
    let comm_native_rules: Vec<TokenStream> = comms
        .iter()
        .map(|c| comm_native_rule(c, &enum_id))
        .collect::<Result<Vec<_>, _>>()
        .unwrap_or_else(|reason| {
            // A Comm rewrite that passed `is_comm_rewrite` but whose LHS does not lower is a
            // generator bug, surfaced as a build error rather than a silently-missing rule.
            vec![quote! { compile_error!(#reason); }]
        });
    let comm_dispatch_arms: Vec<TokenStream> =
        comms.iter().map(|c| comm_dispatch_arm(c, &enum_id)).collect();

    // (Stage 3d) Structural-AC native rules + dispatch arms. Their `op_id`s are disjoint from folds ∪
    // substitution ∪ Comm rules, so the dispatch match has one arm per rule across all four kinds.
    let structural_ac_native_rules: Vec<TokenStream> = structural_acs
        .iter()
        .map(|s| structural_ac_native_rule(s, &enum_id))
        .collect::<Result<Vec<_>, _>>()
        .unwrap_or_else(|reason| {
            // A structural-AC rewrite that passed `is_structural_ac_rewrite` but whose LHS does not
            // lower is a generator bug, surfaced as a build error rather than a silently-missing rule.
            vec![quote! { compile_error!(#reason); }]
        });
    let structural_ac_dispatch_arms: Vec<TokenStream> = structural_acs
        .iter()
        .map(|s| structural_ac_dispatch_arm(s, &enum_id))
        .collect();

    // (Stage 4) Nested structural-AC native rules + dispatch arms (Ambient `InRule`/`OutRule`). Their
    // `op_id`s are disjoint from every prior kind, so the dispatch match has one arm per rule.
    let nested_structural_ac_native_rules: Vec<TokenStream> = nested_structural_acs
        .iter()
        .map(|s| nested_structural_ac_native_rule(language, s, &enum_id))
        .collect::<Result<Vec<_>, _>>()
        .unwrap_or_else(|reason| {
            // A nested structural-AC rewrite that passed `is_nested_structural_ac_rewrite` but whose
            // LHS does not lower is a generator bug, surfaced as a build error rather than a
            // silently-missing rule.
            vec![quote! { compile_error!(#reason); }]
        });
    let nested_structural_ac_dispatch_arms: Vec<TokenStream> = nested_structural_acs
        .iter()
        .map(|s| nested_structural_ac_dispatch_arm(language, s, &enum_id))
        .collect::<Result<Vec<_>, _>>()
        .unwrap_or_else(|reason| vec![quote! { compile_error!(#reason); }]);

    let dispatch = quote! {
        |__op: ::dovetail::rules::NativeOpId,
         __eg: &mut ::dovetail::egraph::EGraph<#enum_id>,
         __subst: &::dovetail::rules::Subst|
         -> ::core::option::Option<::dovetail::egraph::EClassId> {
            match __op {
                #(#dispatch_arms)*
                #(#subst_dispatch_arms)*
                #(#comm_dispatch_arms)*
                #(#structural_ac_dispatch_arms)*
                #(#nested_structural_ac_dispatch_arms)*
                _ => ::core::option::Option::None,
            }
        }
    };

    (
        quote! {
            vec![
                #(#native_rules,)*
                #(#subst_native_rules,)*
                #(#comm_native_rules,)*
                #(#structural_ac_native_rules,)*
                #(#nested_structural_ac_native_rules),*
            ]
        },
        dispatch,
    )
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
        let multi_subst =
            format_ident!("multi_substitute_{}", to_snake(&sr.binder_var_cat.to_string()));
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

/// (A-3) The typed AcApp element pattern for one structured Comm element. A BINDER (receive)
/// element `(Recv pre… scope)` lowers to `[pre-scope children…, BinderArity(1), body]`, so its
/// pattern binds each pre-scope arg, matches the FIX-A arity marker EXACTLY (single binder ⇒ arity
/// 1 — `is_comm_rewrite` accepts only single `Binder`s), and binds `scope` (the LAST arg, the
/// continuation `cont`) to the BODY class. A non-binder (send) element `(Send v_0 …)` binds each
/// arg positionally. The shared non-linear channel var occurs in BOTH element patterns, so the AC
/// matcher's `Var` re-bind check enforces `N ≡ N` by e-class equality (A-2).
fn comm_element_pattern(element: &CommElementInfo, enum_id: &Ident) -> TokenStream {
    let elem_op = op_variant_ident(&element.category, &element.constructor);
    if element.is_binder {
        let (pre, scope) = element
            .args
            .split_last()
            .map(|(scope, pre)| (pre, scope))
            .expect("a binder element has at least the scope arg");
        let pre_pats: Vec<TokenStream> = pre
            .iter()
            .map(|arg| {
                let name = lit(&arg.to_string());
                quote! { ::dovetail::rules::Pattern::var(#name) }
            })
            .collect();
        let scope_lit = lit(&scope.to_string());
        quote! {
            ::dovetail::rules::Pattern::app(
                #enum_id::#elem_op,
                vec![
                    #(#pre_pats,)*
                    ::dovetail::rules::Pattern::leaf(#enum_id::BinderArity(1u32)),
                    ::dovetail::rules::Pattern::var(#scope_lit),
                ],
            )
        }
    } else {
        let arg_pats: Vec<TokenStream> = element
            .args
            .iter()
            .map(|arg| {
                let name = lit(&arg.to_string());
                quote! { ::dovetail::rules::Pattern::var(#name) }
            })
            .collect();
        quote! {
            ::dovetail::rules::Pattern::app(#enum_id::#elem_op, vec![#(#arg_pats),*])
        }
    }
}

/// (A-3) The typed `NativeRule` for a Comm rewrite: its LHS is the AcApp `op{ E0, E1, ...rest }`
/// with binder-aware element patterns ([`comm_element_pattern`]); its op is the Comm `op_id`
/// (≥ `folds.len() + substs.len()`); its label is the rewrite's `<Lang>::rewrite::<name>` (matching
/// the installed Comm σ-receiver's label).
fn comm_native_rule(c: &CommRule, enum_id: &Ident) -> Result<TokenStream, String> {
    let op_id = c.op_id;
    let cr = &c.rewrite;
    let label = lit(&cr.label);
    let op_variant = op_variant_ident(&cr.op_cat, &cr.op_label);
    let fixed: Vec<TokenStream> =
        cr.elements.iter().map(|e| comm_element_pattern(e, enum_id)).collect();
    let rest_lit = lit(&cr.rest_var.to_string());
    Ok(quote! {
        ::dovetail::rules::NativeRule {
            lhs: ::dovetail::rules::Pattern::ac(
                #enum_id::#op_variant,
                vec![#(#fixed),*],
                ::core::option::Option::Some(#rest_lit.to_string()),
            ),
            op: #op_id,
            label: ::core::option::Option::Some(#label.to_string()),
        }
    })
}

/// (A-3 — the dropped-`Extractor`-scope-then-mutate discipline) The dispatch arm for a Comm
/// rewrite. It mirrors the fold/subst arm structure (gate operand classes, extract child
/// derivations in ONE dropped `Extractor` scope, reconstruct, mutate via the typed lowering), but
/// realizes the communication reduct + AC splice:
///
///  1. bind the continuation `cont` (the binder BODY class — the AcApp pattern binds it via the
///     3-child binder shape), the sent name `Q`, and (from the AC match) the residual `rest`; gate
///     `cont` on `__class_is_fold_value` and `Q` on `__class_has_normal_form`;
///  2. `kth(.., 0)`-extract the `cont`/`Q` child derivations in ONE `Extractor` scope that DROPS
///     before the mutable `instantiate` (A4 borrow discipline);
///  3. reconstruct the body, rebuild its binder `Scope` with a FRESH binder (`reconstruct.rs`'s
///     `Binder` arm — α-equivalent), `unbind` to freshen the bound variable, and reconstruct `Q`;
///  4. `cont[Q/y]` = `body.substitute_<binder_var_cat>(&binder.0, &Q)` — the host-computed
///     capture-avoiding substitution (model-b, exactly the Stage 3c binder reduct);
///  5. lower the reduct and splice `op{ r_0, …, r_{m-1}, ...rest }` into ONE flat canonical bag via
///     `instantiate` (whose `AcApp` RHS handling flattens the `rest` bag into the parallel), and
///     return the reduced bag's e-class — the contractum the engine merges with the redex bag, from
///     which `resolve_rewrite_justifications` reports the communicated bag and the Comm σ-injection
///     recovers `cont[Q/y]`.
///
/// (D10) Step 5 is arity-general: the reduct bag carries the `m ≥ 1` fixed elements
/// [`CommRewrite::reduct_elements`] describes, in RHS order — the host-computed substitution at the
/// reserved `__comm_reduct` σ slot, and every other element re-referenced DIRECTLY from `__subst`
/// (a bare LHS-element argument the AC match already bound), exactly as
/// [`structural_ac_dispatch_arm`] splices its σ-delivered reducts. For the asynchronous `m = 1`
/// shape this emits the byte-identical single-element `vec![Pattern::var("__comm_reduct")]`; for the
/// omnibus π synchronous `m = 2` shape it emits `vec![var("__comm_reduct"), var("q")]`, i.e. the
/// parallel composition `p[m/x] | q` the rule's AC operator denotes.
fn comm_dispatch_arm(c: &CommRule, enum_id: &Ident) -> TokenStream {
    let op_id = c.op_id;
    let cr = &c.rewrite;
    let scope_var = lit(&cr.scope_var.to_string());
    let arg_var = lit(&cr.arg_var.to_string());
    let rest_var = lit(&cr.rest_var.to_string());
    let body_build = build_fn(&cr.body_cat);
    let arg_build = build_fn(&cr.binder_var_cat);
    let body_add = category_lowering_fn(&cr.body_cat);
    let single_subst = format_ident!("substitute_{}", to_snake(&cr.binder_var_cat.to_string()));
    let op_variant = op_variant_ident(&cr.op_cat, &cr.op_label);
    // (D10) The `m ≥ 1` reduct element patterns, in RHS order: the reserved `__comm_reduct` slot for
    // the host-computed substitution, a plain σ variable for every other element.
    let reduct_pats: Vec<TokenStream> = cr
        .reduct_elements
        .iter()
        .map(|element| match element {
            CommReductElement::Substitution => {
                quote! { ::dovetail::rules::Pattern::var("__comm_reduct") }
            },
            CommReductElement::Var(var) => {
                let name = lit(&var.to_string());
                quote! { ::dovetail::rules::Pattern::var(#name) }
            },
        })
        .collect();
    quote! {
        #op_id => {
            // 1. Bind + gate the operand classes.
            let __ccls = *__subst.get(#scope_var)?;
            if !__class_is_fold_value(__eg, __ccls) {
                return ::core::option::Option::None;
            }
            let __qcls = *__subst.get(#arg_var)?;
            if !__class_has_normal_form(__eg, __qcls) {
                return ::core::option::Option::None;
            }
            // 2. Extract the funded 1-best child derivations in ONE dropped `Extractor` scope.
            let (__cont_d, __q_d) = {
                let mut __ex = ::dovetail::extract::Extractor::new(&*__eg, __weigh);
                (
                    __ex.kth(__eg.find(__ccls), 0).value?,
                    __ex.kth(__eg.find(__qcls), 0).value?,
                )
            };
            // 3. Reconstruct the body, rebuild its binder scope (FRESH binder), unbind, reconstruct Q.
            let __body = #body_build(&__cont_d)?;
            let __binder = ::mettail_runtime::Binder(::mettail_runtime::FreeVar::fresh_unnamed());
            let __scope = ::mettail_runtime::Scope::from_parts_unsafe(
                __binder,
                ::std::sync::Arc::new(__body),
            );
            let (__b, __open_body) = __scope.unbind();
            let __arg = #arg_build(&__q_d)?;
            // 4. cont[Q/y] — host-computed capture-avoiding substitution (model-b).
            let __reduct = (*__open_body).#single_subst(&__b.0, &__arg);
            // 5. Splice op{ r_0, …, r_{m-1}, ...rest } into one flat canonical bag and return its
            //    class. The substitution slot is `__comm_reduct`; every other element comes from σ.
            let __reduct_class = #body_add(__eg, &__reduct);
            let mut __rhs_subst = __subst.clone();
            __rhs_subst.insert(::std::string::String::from("__comm_reduct"), __reduct_class);
            let __rhs_pat = ::dovetail::rules::Pattern::ac(
                #enum_id::#op_variant,
                ::std::vec![#(#reduct_pats),*],
                ::core::option::Option::Some(#rest_var.to_string()),
            );
            __eg.instantiate(&__rhs_pat, &__rhs_subst)
        }
    }
}

/// (Stage 3d) The typed `NativeRule` for a structural non-linear AC rewrite (Ambient `OpenRule`): its
/// LHS is the AcApp `op{ E0, …, ...rest }` with the SAME tag-routed, non-linear-guarded element
/// patterns the Comm rule uses (each element a plain constructor over bare vars — the shared channel
/// `N` occurs in BOTH, so the AC matcher's `Var` re-bind check enforces `N ≡ N` by e-class equality);
/// its op is the structural-AC `op_id`; its label is `<Lang>::rewrite::<name>` (matching the installed
/// structural-AC σ-receiver's label). Every element is non-binder, so [`comm_element_pattern`]'s
/// non-binder branch applies.
fn structural_ac_native_rule(s: &StructuralAcRule, enum_id: &Ident) -> Result<TokenStream, String> {
    let op_id = s.op_id;
    let sr = &s.rewrite;
    let label = lit(&sr.label);
    let op_variant = op_variant_ident(&sr.op_cat, &sr.op_label);
    let fixed: Vec<TokenStream> =
        sr.elements.iter().map(|e| comm_element_pattern(e, enum_id)).collect();
    let rest_lit = lit(&sr.rest_var.to_string());
    Ok(quote! {
        ::dovetail::rules::NativeRule {
            lhs: ::dovetail::rules::Pattern::ac(
                #enum_id::#op_variant,
                vec![#(#fixed),*],
                ::core::option::Option::Some(#rest_lit.to_string()),
            ),
            op: #op_id,
            label: ::core::option::Option::Some(#label.to_string()),
        }
    })
}

/// (Stage 3d) The dispatch arm for a structural non-linear AC rewrite. UNLIKE the Comm arm there is
/// no binder reconstruction and no substitution: the reduct is a PURE structural restructuring, so
/// each RHS element `r_j` — a bare LHS-element argument bound by the AC match — is re-referenced
/// DIRECTLY from `__subst`. The arm splices `op{ σ[r0], …, σ[r_{m-1}], ...rest }` into ONE flat
/// canonical bag via `instantiate` (whose `AcApp` RHS handling flattens the `rest` bag into the
/// parallel) and returns the restructured bag's e-class — the contractum the engine merges with the
/// redex bag, from which `resolve_rewrite_justifications` reports the restructured bag and the
/// structural-AC σ-injection recovers each `r_j` from σ. The non-linear guard `N ≡ N` was already
/// enforced at the AC matcher (a mismatched-channel soup produces no match ⇒ no firing), so the arm
/// needs no re-check.
fn structural_ac_dispatch_arm(s: &StructuralAcRule, enum_id: &Ident) -> TokenStream {
    let op_id = s.op_id;
    let sr = &s.rewrite;
    let op_variant = op_variant_ident(&sr.op_cat, &sr.op_label);
    let rest_var = lit(&sr.rest_var.to_string());
    let reduct_pats: Vec<TokenStream> = sr
        .reduct_vars
        .iter()
        .map(|v| {
            let name = lit(&v.to_string());
            quote! { ::dovetail::rules::Pattern::var(#name) }
        })
        .collect();
    quote! {
        #op_id => {
            // Splice op{ σ[r0], …, σ[r_{m-1}], ...rest } from the AC-matched σ (every reduct var is a
            // bound LHS-element arg — no substitution, no reconstruction) into one flat canonical bag.
            let __rhs_pat = ::dovetail::rules::Pattern::ac(
                #enum_id::#op_variant,
                ::std::vec![#(#reduct_pats),*],
                ::core::option::Option::Some(#rest_var.to_string()),
            );
            __eg.instantiate(&__rhs_pat, __subst)
        }
    }
}

/// (Stage 4) The typed `NativeRule` for a DEPTH-2 NESTED structural non-linear AC rewrite (Ambient
/// `InRule`/`OutRule`): its LHS is the WHOLE nested LHS lowered through the ordinary
/// [`pattern_to_dovetail`] — which builds the nested `AcApp{ … , App(PAmb, [Var, AcApp{ … }]) , … }`
/// (`InRule`, bag-rooted) or `App(PAmb, [Var, AcApp{ … }])` (`OutRule`, wrapper-rooted) the native AC
/// matcher matches ORDER-INDEPENDENTLY at every depth, binding every LHS variable (`N`, `M`, `P`, the
/// remainders, `R`) — the shared cross-level `M` occurs in BOTH the inner capability AND the outer
/// level, so the matcher's `Var` re-bind check enforces `M ≡ M` by e-class equality. Its op is the
/// nested `op_id`; its label matches the installed nested structural-AC σ-receiver's.
fn nested_structural_ac_native_rule(
    language: &LanguageDef,
    s: &NestedStructuralAcRule,
    enum_id: &Ident,
) -> Result<TokenStream, String> {
    let op_id = s.op_id;
    let label = lit(&s.rewrite.label);
    let lhs = pattern_to_dovetail(language, &s.rewrite.left, Some(enum_id))?;
    Ok(quote! {
        ::dovetail::rules::NativeRule {
            lhs: #lhs,
            op: #op_id,
            label: ::core::option::Option::Some(#label.to_string()),
        }
    })
}

/// (Stage 4) The dispatch arm for a DEPTH-2 nested structural non-linear AC rewrite. UNLIKE the flat
/// structural-AC arm (whose RHS elements are bare LHS-element args spliced directly), the In/Out
/// reduct is a NESTED re-assembly, so the arm INSTANTIATES the WHOLE nested RHS pattern (lowered via
/// [`pattern_to_dovetail`], which threads the same nested `AcApp`/`App` structure) with the AC-matched
/// σ and returns the restructured bag's e-class — the contractum the engine merges with the redex bag,
/// from which `resolve_rewrite_justifications` reports the restructured operand and the nested
/// structural-AC σ-injection reconstructs `⟦operand⟧` + `⟦reduct⟧` from σ. The cross-level guard
/// `M ≡ M` was already enforced at the AC matcher (a mismatched-channel soup produces no match ⇒ no
/// firing), so the arm needs no re-check.
fn nested_structural_ac_dispatch_arm(
    language: &LanguageDef,
    s: &NestedStructuralAcRule,
    enum_id: &Ident,
) -> Result<TokenStream, String> {
    let op_id = s.op_id;
    let rhs = pattern_to_dovetail(language, &s.rewrite.right, Some(enum_id))?;
    Ok(quote! {
        #op_id => {
            // Instantiate the whole NESTED restructured RHS `op{ m[{ n[{P,...q}], R }], ...s }` (or
            // the `out` dual) from the AC-matched σ into one canonical bag — the firing's contractum.
            let __rhs_pat = #rhs;
            __eg.instantiate(&__rhs_pat, __subst)
        }
    })
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
    // (A-3) Comm rewrites share the native op-id counter with the folds ∪ substitution rules (ids
    // start at `folds.len() + substs.len()`), so the helpers (redex-head set) and the
    // native-rule/dispatcher generator both see folds ∪ substitution rules ∪ Comm rules.
    let comms = collect_comm_rules(language, folds.len() + substs.len());
    // (Stage 3d) Structural-AC rewrites (Ambient `OpenRule`) share the native op-id counter, starting
    // after folds ∪ substitution ∪ Comm rules, so the helpers (redex-head set) and the
    // native-rule/dispatcher generator see all four native kinds.
    let structural_acs =
        collect_structural_ac_rules(language, folds.len() + substs.len() + comms.len());
    // (Stage 4) DEPTH-2 nested structural-AC rewrites (Ambient `InRule`/`OutRule`) share the native
    // op-id counter, starting after folds ∪ substitution ∪ Comm ∪ flat-structural-AC rules.
    let nested_structural_acs = collect_nested_structural_ac_rules(
        language,
        folds.len() + substs.len() + comms.len() + structural_acs.len(),
    );
    let helpers = generate_helpers(
        language,
        &folds,
        &substs,
        &comms,
        &structural_acs,
        &nested_structural_acs,
    );
    let (native_rules_expr, dispatch) = generate_native_rules_and_dispatch(
        language,
        &folds,
        &substs,
        &comms,
        &structural_acs,
        &nested_structural_acs,
    );
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
            // One extractor reused across all category-alternative roots (same rationale as the
            // main report path): the O(classes) inside weights are computed once and memoized,
            // not re-run per root. This is the alternatives path where cross-category numeric
            // ambiguity yields the most roots, so the per-root inside recompute hurt most here.
            let mut __extractor = ::dovetail::extract::Extractor::new(&eg, __weigh);
            for (__root, __cat_idx) in __roots {
                let __extracted = __extractor.funded_best(eg.find(__root));
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
            // One extractor reused across all roots (same rationale as the main report path):
            // `funded_best` computes the O(classes) inside weights once and memoizes, rather than
            // re-running them per root with a discarded memo. Behaviorally identical here — the
            // loop returns `Err` on the first cycle-cut root under either the per-root or the
            // cumulative completeness.
            let mut __extractor = ::dovetail::extract::Extractor::new(&eg, __weigh);
            for __root in __roots {
                let __extracted = __extractor.funded_best(eg.find(__root));
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
            let __dispatch = #dispatch;
            static __DOVETAIL_COMPILED_RULES: ::std::sync::OnceLock<
                ::dovetail::rules::CompiledRuleSet<#enum_id>,
            > = ::std::sync::OnceLock::new();
            let __compiled_rules = __DOVETAIL_COMPILED_RULES.get_or_init(|| {
                ::dovetail::rules::CompiledRuleSet::new(#rules_expr, #native_rules_expr)
            });
            let sat = eg.saturate_compiled_with_native(__compiled_rules, &__dispatch, __iters);
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

/// (Increment 4) Generate `dovetail_step_graph` — the REPL `step` command's navigable, one-step
/// REWRITE-step graph producer.
///
/// Our Dovetail e-graph is congruence CLOSURE: it merges equal terms and retains NO term→term
/// rewrite relation (the retired Ascent engine had one). So a navigable rewrite graph cannot be
/// read off a saturation; it is RECONSTRUCTED step-only by a lazy small-step enumerator that, given
/// a program state `T`, lowers `T` into a FRESH unsaturated e-graph, extracts its funded-best
/// derivation `D_T`, then for every redex match of every structural [`RewriteRule`] AND every
/// fold/substitution [`NativeRule`] builds the rule's RHS class on that same fresh graph
/// (`instantiate` for structural, the native `dispatch` for native), extracts the RHS derivation,
/// and SPLICES it into `D_T` at every subtree whose canonical e-class equals the matched redex's
/// (per-class, faithful to the e-graph). Each spliced tree reconstructs (via the generated
/// `__mettail_dovetail_build_<cat>_d`) to a whole successor program state; deduped by rendered
/// source these are `T`'s one-step successors. A bounded BFS over successors yields the whole
/// navigable graph; a state with no successor is a normal form.
///
/// Splicing reads only `op`/`children` through the reconstructor, so the spliced nodes' `key`/
/// `weight` are irrelevant (carried forward verbatim). `search`/`instantiate`/`dispatch`/`rebuild`
/// add nodes and canonicalize but NEVER merge (merging happens only inside `saturate_with_native`),
/// so `D_T` stays the pristine current state and a matched class's canonical id is stable across the
/// enumeration loop.
///
/// This path is reached ONLY from the REPL `step` routing (via `Language::run_step_backend_report`
/// → the wrapper's `step_compiler`); production `exec` (`dovetail_report_for`) never calls it, so it
/// costs `exec` nothing and the exec report is byte-identical.
fn generate_step_graph(language: &LanguageDef) -> TokenStream {
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
    let substs = collect_substitution_rules(language, folds.len());
    // (A-3) Comm rewrites share the native op-id counter with the folds ∪ substitution rules (ids
    // start at `folds.len() + substs.len()`), so the helpers (redex-head set) and the
    // native-rule/dispatcher generator both see folds ∪ substitution rules ∪ Comm rules.
    let comms = collect_comm_rules(language, folds.len() + substs.len());
    // (Stage 3d) Structural-AC rewrites (Ambient `OpenRule`) share the native op-id counter, starting
    // after folds ∪ substitution ∪ Comm rules, so the helpers (redex-head set) and the
    // native-rule/dispatcher generator see all four native kinds.
    let structural_acs =
        collect_structural_ac_rules(language, folds.len() + substs.len() + comms.len());
    // (Stage 4) DEPTH-2 nested structural-AC rewrites (Ambient `InRule`/`OutRule`) share the native
    // op-id counter, starting after folds ∪ substitution ∪ Comm ∪ flat-structural-AC rules.
    let nested_structural_acs = collect_nested_structural_ac_rules(
        language,
        folds.len() + substs.len() + comms.len() + structural_acs.len(),
    );
    let helpers = generate_helpers(
        language,
        &folds,
        &substs,
        &comms,
        &structural_acs,
        &nested_structural_acs,
    );
    let (native_rules_expr, dispatch) = generate_native_rules_and_dispatch(
        language,
        &folds,
        &substs,
        &comms,
        &structural_acs,
        &nested_structural_acs,
    );
    let (rules_expr, _unsupported) = rule_block(language, Some(&enum_id));

    let primary_cat = &language.types.first().expect("language has a type").name;
    let primary_add = category_lowering_fn(primary_cat);
    let primary_build = build_fn(primary_cat);

    let multi = language.types.len() > 1;

    // Per-category lowering arms (inner-enum alt → its category's e-class root) and reconstruction
    // arms (category index → `build_<cat>_d` then re-wrap into the inner enum). For a single-type
    // language `<Lang>Term` wraps the primary category directly (no inner enum), so the alt loop and
    // category dispatch collapse to the one primary category.
    let (
        // Returns `Vec<(typed_alt_for_lowering, cat_idx)>` for the input term.
        alts_expr,
        // `fn __step_lower(eg, alt, cat_idx) -> EClassId`
        lower_fn,
        // `fn __step_build(cat_idx, &Rc<Derivation>) -> Option<TypedTermForKeying>`
        build_fn_def,
        // `fn __step_render(&TypedTermForKeying) -> String`
        render_fn,
        // the Rust type the BFS frontier/successors carry (`<Lang>TermInner` or `<primary>`)
        node_ty,
    ) = if multi {
        let lower_arms: Vec<TokenStream> = language
            .types
            .iter()
            .enumerate()
            .map(|(idx, ty)| {
                let cat = &ty.name;
                let add_fn = category_lowering_fn(cat);
                let idx = idx as u32;
                quote! {
                    (#idx, #inner_enum::#cat(__v)) => #add_fn(__eg, __v),
                }
            })
            .collect();
        let build_arms: Vec<TokenStream> = language
            .types
            .iter()
            .enumerate()
            .map(|(idx, ty)| {
                let cat = &ty.name;
                let build = build_fn(cat);
                let idx = idx as u32;
                quote! {
                    #idx => #build(__d).map(#inner_enum::#cat),
                }
            })
            .collect();
        // Map each inner-enum alternative to its declared category index (so `__step_lower` /
        // `__step_build` can route it). `Ambiguous` is impossible here — `all_alts()` returns flat
        // alternatives, never a nested `Ambiguous`.
        let idx_arms: Vec<TokenStream> = language
            .types
            .iter()
            .enumerate()
            .map(|(idx, ty)| {
                let cat = &ty.name;
                let idx = idx as u32;
                quote! { #inner_enum::#cat(_) => #idx, }
            })
            .collect();
        let alts = quote! {
            {
                let mut __out: Vec<(#inner_enum, u32)> = Vec::new();
                for __alt in __input.all_alts() {
                    let __idx: u32 = match __alt {
                        #(#idx_arms)*
                        #inner_enum::Ambiguous(_) => unreachable!(
                            "all_alts() returns flat alternatives, not nested Ambiguous"
                        ),
                    };
                    __out.push((::core::clone::Clone::clone(__alt), __idx));
                }
                __out
            }
        };
        let lower = quote! {
            fn __step_lower(
                __eg: &mut ::dovetail::egraph::EGraph<#enum_id>,
                __alt: &#inner_enum,
                __cat_idx: u32,
            ) -> ::dovetail::egraph::EClassId {
                match (__cat_idx, __alt) {
                    #(#lower_arms)*
                    _ => unreachable!("category index does not match the alternative"),
                }
            }
        };
        let build = quote! {
            fn __step_build(
                __cat_idx: u32,
                __d: &::std::rc::Rc<::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>>,
            ) -> ::core::option::Option<#inner_enum> {
                match __cat_idx {
                    #(#build_arms)*
                    _ => ::core::option::Option::None,
                }
            }
        };
        let render = quote! {
            fn __step_render(__n: &#inner_enum) -> String {
                format!("{}", #term_name(__n.clone()))
            }
        };
        (alts, lower, build, render, quote! { #inner_enum })
    } else {
        // Single-type: one category, index 0; `<Lang>Term` wraps the primary category directly.
        // Spliced as the tail of `let __alts = { let __input = __state; #alts };`; the outer block
        // already delimits, so an inner `{ … }` is a redundant block-return-value wrapper.
        let alts = quote! {
            vec![(::core::clone::Clone::clone(__input), 0u32)]
        };
        let lower = quote! {
            fn __step_lower(
                __eg: &mut ::dovetail::egraph::EGraph<#enum_id>,
                __alt: &#primary_cat,
                _cat_idx: u32,
            ) -> ::dovetail::egraph::EClassId {
                #primary_add(__eg, __alt)
            }
        };
        let build = quote! {
            fn __step_build(
                _cat_idx: u32,
                __d: &::std::rc::Rc<::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>>,
            ) -> ::core::option::Option<#primary_cat> {
                #primary_build(__d)
            }
        };
        let render = quote! {
            fn __step_render(__n: &#primary_cat) -> String {
                format!("{}", #term_name(::core::clone::Clone::clone(__n)))
            }
        };
        (alts, lower, build, render, quote! { #primary_cat })
    };

    quote! {
        /// (Increment 4) Build the navigable one-step REWRITE-step graph for `term` and project it
        /// as a [`RuntimeDovetailRunReport`] whose `graph_kind` is
        /// [`RuntimeDovetailGraphKind::Rewrite`]. Each term record is a whole program STATE rendered
        /// in source syntax (`source_display`); each edge is a one-step rewrite successor
        /// (`parent → child`). The single entry state is the report root; a state with no outgoing
        /// edge is a normal form. Step-only — production `exec` never reaches it.
        pub fn dovetail_step_graph(
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

            #lower_fn
            #build_fn_def
            #render_fn

            // Per-class splice: replace every subtree of `__d` whose canonical e-class is `__target`
            // with `__repl`. `key`/`weight` of rebuilt interior nodes are carried forward verbatim —
            // the reconstructor reads only `op`/`children`, so they are irrelevant to the result.
            fn __step_splice(
                __d: &::std::rc::Rc<::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>>,
                __target: ::dovetail::egraph::EClassId,
                __repl: &::std::rc::Rc<::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>>,
                __eg: &::dovetail::egraph::EGraph<#enum_id>,
            ) -> ::std::rc::Rc<::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>> {
                if __eg.find(__d.class) == __target {
                    return ::std::rc::Rc::clone(__repl);
                }
                ::std::rc::Rc::new(::dovetail::extract::Derivation {
                    op: ::core::clone::Clone::clone(&__d.op),
                    class: __d.class,
                    children: __d
                        .children
                        .iter()
                        .map(|__c| __step_splice(__c, __target, __repl, __eg))
                        .collect(),
                    weight: ::core::clone::Clone::clone(&__d.weight),
                    key: ::core::clone::Clone::clone(&__d.key),
                })
            }

            // The whole-state one-step successors of `__alt` (a single typed alternative under
            // category `__cat_idx`): lower it into a FRESH unsaturated e-graph, extract `D_T`, and
            // for every redex match of every rule splice the rule's RHS derivation into `D_T`, then
            // reconstruct the whole spliced state. Returns `(rule label, successor state)` pairs.
            let __successors_of_alt = |__alt: &#node_ty, __cat_idx: u32, __max_nodes: usize|
              -> Vec<(::core::option::Option<String>, #node_ty)> {
                let mut __succ: Vec<(::core::option::Option<String>, #node_ty)> = Vec::new();
                let mut __eg = ::dovetail::egraph::EGraph::<#enum_id>::with_config(
                    ::dovetail::egraph::EGraphConfig { max_nodes: __max_nodes },
                );
                let __r0 = __step_lower(&mut __eg, __alt, __cat_idx);
                __eg.rebuild();
                let __d_t = {
                    let mut __ex = ::dovetail::extract::Extractor::new(&__eg, __weigh);
                    __ex.funded_best(__eg.find(__r0)).value
                };
                let ::core::option::Option::Some(__d_t) = __d_t else {
                    return __succ;
                };

                let __push_succ = |
                    __succ: &mut Vec<(::core::option::Option<String>, #node_ty)>,
                    __eg: &::dovetail::egraph::EGraph<#enum_id>,
                    __redex: ::dovetail::egraph::EClassId,
                    __rhs_id: ::dovetail::egraph::EClassId,
                    __label: ::core::option::Option<String>,
                | {
                    let __d_rhs = {
                        let mut __ex = ::dovetail::extract::Extractor::new(__eg, __weigh);
                        __ex.funded_best(__eg.find(__rhs_id)).value
                    };
                    let ::core::option::Option::Some(__d_rhs) = __d_rhs else {
                        return;
                    };
                    let __spliced =
                        __step_splice(&__d_t, __eg.find(__redex), &__d_rhs, __eg);
                    if let ::core::option::Option::Some(__state) = __step_build(__cat_idx, &__spliced) {
                        // A successor identical to the source under rendering is not a step (e.g. a
                        // rule that re-derives the same term); drop it so a fixpoint is a real
                        // normal form rather than a self-loop.
                        if __step_render(&__state) != __step_render(__alt) {
                            __succ.push((__label, __state));
                        }
                    }
                };

                // Structural rewrite rules: instantiate the RHS pattern on the fresh graph. The
                // explicit type lets `vec![]` (a language with no structural rewrites, e.g. Lambda)
                // infer; with rules the element type already matches.
                static __DOVETAIL_COMPILED_RULES: ::std::sync::OnceLock<
                    ::dovetail::rules::CompiledRuleSet<#enum_id>,
                > = ::std::sync::OnceLock::new();
                let __compiled_rules = __DOVETAIL_COMPILED_RULES.get_or_init(|| {
                    ::dovetail::rules::CompiledRuleSet::new(#rules_expr, #native_rules_expr)
                });
                for __rule in __compiled_rules.rewrite_rules() {
                    for (__c, __subst) in __eg.search(&__rule.lhs) {
                        if let ::core::option::Option::Some(__rhs_id) =
                            __eg.instantiate(&__rule.rhs, &__subst)
                        {
                            __eg.rebuild();
                            __push_succ(&mut __succ, &__eg, __c, __rhs_id, __rule.label.clone());
                        }
                    }
                }

                // Native (fold / substitution) rules: the generated dispatcher computes the RHS
                // class from the matched substitution (the same computation saturation uses).
                let __dispatch = #dispatch;
                for __nrule in __compiled_rules.native_rules() {
                    for (__c, __subst) in __eg.search(&__nrule.lhs) {
                        if let ::core::option::Option::Some(__rhs_id) =
                            __dispatch(__nrule.op, &mut __eg, &__subst)
                        {
                            __eg.rebuild();
                            __push_succ(&mut __succ, &__eg, __c, __rhs_id, __nrule.label.clone());
                        }
                    }
                }

                __succ
            };

            // The one-step successors of a whole program STATE: union the successors over each of its
            // parse alternatives, deduped by rendered source (a node is its source string).
            let __successors_of_state = |__state: &#node_ty, __max_nodes: usize|
              -> Vec<(::core::option::Option<String>, #node_ty)> {
                let mut __out: Vec<(::core::option::Option<String>, #node_ty)> = Vec::new();
                let mut __seen: ::std::collections::HashSet<String> =
                    ::std::collections::HashSet::new();
                let __alts: Vec<(#node_ty, u32)> = {
                    let __input = __state;
                    #alts_expr
                };
                for (__alt, __cat_idx) in &__alts {
                    for (__label, __next) in __successors_of_alt(__alt, *__cat_idx, __max_nodes) {
                        if __seen.insert(__step_render(&__next)) {
                            __out.push((__label, __next));
                        }
                    }
                }
                __out
            };

            // Bounded BFS over states, keyed by rendered source. `__nodes` preserves discovery order
            // (entry first) so ordinals are stable; `__edges` are (from-source, to-source, label).
            const MAX_STEP_NODES: usize = 256;
            const MAX_STEP_DEPTH: usize = 64;
            // `max_iters` is a per-term saturation floor for the report/normal-form paths; the
            // small-step BFS is bounded by `MAX_STEP_NODES`/`MAX_STEP_DEPTH` instead, so it is unused
            // here (kept in the signature for a uniform stepper API across languages).
            let _ = max_iters;

            let __entry: #node_ty = {
                let __input = &typed_term.0;
                ::core::clone::Clone::clone(__input)
            };
            let __entry_src = __step_render(&__entry);

            let mut __order: Vec<String> = Vec::new();
            let mut __states: ::std::collections::HashMap<String, #node_ty> =
                ::std::collections::HashMap::new();
            let mut __depth: ::std::collections::HashMap<String, usize> =
                ::std::collections::HashMap::new();
            let mut __edges: Vec<(String, String, ::core::option::Option<String>)> = Vec::new();
            let mut __edge_seen: ::std::collections::HashSet<(String, String)> =
                ::std::collections::HashSet::new();
            let mut __queue: ::std::collections::VecDeque<String> =
                ::std::collections::VecDeque::new();

            __order.push(__entry_src.clone());
            __states.insert(__entry_src.clone(), __entry);
            __depth.insert(__entry_src.clone(), 0);
            __queue.push_back(__entry_src.clone());

            while let ::core::option::Option::Some(__cur_src) = __queue.pop_front() {
                let __cur_depth = *__depth.get(&__cur_src).unwrap_or(&0);
                if __cur_depth >= MAX_STEP_DEPTH {
                    continue;
                }
                let __cur_state = match __states.get(&__cur_src) {
                    ::core::option::Option::Some(__s) => ::core::clone::Clone::clone(__s),
                    ::core::option::Option::None => continue,
                };
                for (__label, __next) in __successors_of_state(&__cur_state, max_nodes) {
                    let __next_src = __step_render(&__next);
                    if !__states.contains_key(&__next_src) {
                        if __order.len() >= MAX_STEP_NODES {
                            // Node budget hit: record no further new states (and so no edges into
                            // them), keeping the graph bounded. Existing edges remain valid.
                            continue;
                        }
                        __order.push(__next_src.clone());
                        __states.insert(__next_src.clone(), __next);
                        __depth.insert(__next_src.clone(), __cur_depth + 1);
                        __queue.push_back(__next_src.clone());
                    }
                    if __edge_seen.insert((__cur_src.clone(), __next_src.clone())) {
                        __edges.push((__cur_src.clone(), __next_src.clone(), __label));
                    }
                }
            }

            // Project the BFS into a `RuntimeDovetailRunReport`. Each distinct state is one term
            // record (ordinal = discovery order, key = its source bytes — unique because states are
            // keyed by source); the entry state is the single root (`is_root` only on it, so
            // `validate_shape` holds — normal-form-ness is recovered in the REPL from the absence of
            // outgoing edges). `op_display` = `source_display` = the rendered source.
            let mut __key_of: ::std::collections::HashMap<String, Vec<u8>> =
                ::std::collections::HashMap::with_capacity(__order.len());
            let mut __ordinal_of: ::std::collections::HashMap<String, usize> =
                ::std::collections::HashMap::with_capacity(__order.len());
            let mut __terms: Vec<mettail_runtime::RuntimeDovetailTermRecord> =
                Vec::with_capacity(__order.len());
            for (__ordinal, __src) in __order.iter().enumerate() {
                let __key = __src.clone().into_bytes();
                __key_of.insert(__src.clone(), __key.clone());
                __ordinal_of.insert(__src.clone(), __ordinal);
                __terms.push(mettail_runtime::RuntimeDovetailTermRecord {
                    ordinal: __ordinal,
                    class_id: __ordinal as u32,
                    key: __key,
                    op_display: __src.clone(),
                    weight_display: String::new(),
                    is_root: __ordinal == 0,
                    source_display: ::core::option::Option::Some(__src.clone()),
                });
            }

            let __entry_key = __key_of
                .get(&__entry_src)
                .cloned()
                .ok_or_else(|| format!(
                    "generated Dovetail step graph for language {} lost its entry state",
                    #language_lit,
                ))?;

            let mut __derivation_edges: Vec<mettail_runtime::RuntimeDovetailDerivationEdge> =
                Vec::with_capacity(__edges.len());
            for (__ordinal, (__from, __to, _label)) in __edges.iter().enumerate() {
                let (::core::option::Option::Some(__parent_key), ::core::option::Option::Some(__child_key)) =
                    (__key_of.get(__from), __key_of.get(__to))
                else {
                    continue;
                };
                // `child_index` = the successor's ordinal among the parent's outgoing edges (a stable
                // per-edge index for the navigable menu).
                let __child_index = __derivation_edges
                    .iter()
                    .filter(|__e| &__e.parent_key == __parent_key)
                    .count();
                __derivation_edges.push(mettail_runtime::RuntimeDovetailDerivationEdge {
                    ordinal: __ordinal,
                    parent_key: __parent_key.clone(),
                    child_key: __child_key.clone(),
                    child_index: __child_index,
                });
            }

            let __report = mettail_runtime::RuntimeDovetailRunReport {
                roots: vec![__entry_key],
                root_ordinals: vec![0],
                terms: __terms,
                derivation_edges: __derivation_edges,
                rule_firings: Vec::new(),
                rewrite_justifications: Vec::new(),
                completeness: mettail_runtime::RuntimeDovetailCompleteness::Complete,
                graph_kind: mettail_runtime::RuntimeDovetailGraphKind::Rewrite,
            };
            __report.validate_shape().map_err(|err| format!(
                "generated Dovetail step graph for language {} is malformed: {err}",
                #language_lit,
            ))?;
            Ok(__report)
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
    // (A-3) Comm rewrites share the native op-id counter with the folds ∪ substitution rules (ids
    // start at `folds.len() + substs.len()`), so the helpers (redex-head set) and the
    // native-rule/dispatcher generator both see folds ∪ substitution rules ∪ Comm rules.
    let comms = collect_comm_rules(language, folds.len() + substs.len());
    // (Stage 3d) Structural-AC rewrites (Ambient `OpenRule`) share the native op-id counter, starting
    // after folds ∪ substitution ∪ Comm rules, so the helpers (redex-head set) and the
    // native-rule/dispatcher generator see all four native kinds.
    let structural_acs =
        collect_structural_ac_rules(language, folds.len() + substs.len() + comms.len());
    // (Stage 4) DEPTH-2 nested structural-AC rewrites (Ambient `InRule`/`OutRule`) share the native
    // op-id counter, starting after folds ∪ substitution ∪ Comm ∪ flat-structural-AC rules.
    let nested_structural_acs = collect_nested_structural_ac_rules(
        language,
        folds.len() + substs.len() + comms.len() + structural_acs.len(),
    );
    let helpers = generate_helpers(
        language,
        &folds,
        &substs,
        &comms,
        &structural_acs,
        &nested_structural_acs,
    );
    let (native_rules_expr, dispatch) = generate_native_rules_and_dispatch(
        language,
        &folds,
        &substs,
        &comms,
        &structural_acs,
        &nested_structural_acs,
    );
    // Typed structural rules (congruence is automatic; Comm/Extrude rules that belong to the
    // RhoNativeJoin boundary land in the dropped `unsupported` — NON-FATAL on the fold path).
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

    // Step-only source reconstruction (powers `source_display` on the step report). `__source_of`
    // tries each category's `build_<cat>_d` reconstructor (each self-filters by `__d.op`, so the
    // matching category returns `Some`) and renders the typed term via its source-syntax `Display`.
    // `__collect_sources` walks a derivation tree, recording one source string per exact
    // `ContentKey`. Emitted into the report impl; only invoked when `record_source`.
    let source_attempts: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| {
            let bf = reconstruct::build_fn(&ty.name);
            quote! {
                if let ::core::option::Option::Some(__t) = #bf(__d) {
                    return ::core::option::Option::Some(format!("{}", __t));
                }
            }
        })
        .collect();
    let source_helpers = quote! {
        fn __source_of(
            __d: &::std::rc::Rc<::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>>,
        ) -> ::core::option::Option<String> {
            #(#source_attempts)*
            ::core::option::Option::None
        }
        fn __collect_sources(
            __d: &::std::rc::Rc<::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>>,
            __map: &mut ::std::collections::HashMap<Vec<u8>, String>,
        ) {
            let __k = __d.key.as_bytes().to_vec();
            if !__map.contains_key(&__k) {
                if let ::core::option::Option::Some(__s) = __source_of(__d) {
                    __map.insert(__k, __s);
                }
            }
            for __c in &__d.children {
                __collect_sources(__c, __map);
            }
        }
    };

    // (E2.2) The optional `dovetail_normal_term` method, emitted only when the MF7 gate
    // (`super::needs_normal_term`) holds. It reuses the saturation prologue and per-category
    // reconstruction verbatim, but returns the reduced term as a typed `Box<dyn Term>`
    // (wrapped `<Lang>Term`) instead of a `RuntimeDovetailRunReport`.
    let normal_term_method = if super::needs_normal_term(language) {
        generate_dovetail_normal_term(language, struct_slack)
    } else {
        TokenStream::new()
    };

    // (Increment 4) The REPL `step` navigable one-step rewrite-graph producer. Emitted for every
    // fold-bearing language (its only caller is the REPL `step` path); production `exec` never
    // reaches it.
    let step_graph_method = generate_step_graph(language);

    // Stage 3c (typed path): a language whose rewrites lower to a σ-receiver (base / AC /
    // contextual / SubstRewrite) carries the resolved σ provenance a runtime Rho σ-injection
    // reads. The BINDER family (`rho_net_subst_injection_sites`) matters HERE: a λ-calculus
    // reduces on the TYPED fold path (a binder `[Term -> Term]` + substitution), so its report is
    // produced by THIS body — the non-typed `report_projection` gate never runs for it. Without
    // this, β fires in the e-graph but the report carries no `rewrite_justifications`, so the subst
    // σ-injection F-fn has no firing (and no contractum) to read. The gate mirrors the non-typed
    // path exactly; a language with no σ-receiver keeps `rewrite_justifications` empty and stays
    // byte-identical.
    //
    // Stage 3e: the NATIVE-SYSTEM-PROCESS family (`rho_net_native_injection_sites`) matters HERE
    // too, and CRUCIALLY: a `fold` native process (BigInt/large-int arithmetic, `PowInt`,
    // factorial) reduces to its host-computed value on THIS typed fold path (the native rule + op
    // enum), so its report is produced by this body — the non-typed gate never runs for it. Without
    // this, the native fold fires in the e-graph but the report carries no `rewrite_justifications`,
    // so the native σ-injection F-fn has no firing (and no contractum) to read.
    // Stage 3b / A-3: the COMM family (`rho_net_comm_injection_sites`) matters HERE — a canonical
    // single-receive Rholang communication rewrite (a non-linear AC over a binder element with a
    // nested-substitution RHS) reduces on THIS typed native lane, so its report is produced by this
    // body. Without carrying its resolved σ + contractum, the runtime Comm σ-injection F-fn would
    // have no firing to read (the hand-built-σ deviation this campaign removes).
    // Stage 3d: the STRUCTURAL-AC family (`rho_net_structural_ac_injection_sites`) matters HERE — a
    // structural non-linear AC rewrite (Ambient `OpenRule`) reduces on THIS typed native lane, so its
    // report is produced by this body. Without carrying its resolved σ, the runtime structural-AC
    // σ-injection F-fn would have no firing to read.
    // Stage 3f: the NATIVE-SCALAR-FOLD family (`rho_net_native_fold_injection_sites`) matters HERE —
    // a `fold` native scalar arithmetic (`AddInt`) reduces to its host-computed value on THIS typed
    // fold path (the native rule + op enum), so its report is produced by this body. Without
    // carrying its resolved σ + contractum, the runtime native-fold σ-injection F-fn would have no
    // firing (and no contractum) to read — empirically the pure scalar fold records `#justifications
    // = 0` on the untyped String path.
    let populate_rewrite_justifications =
        !mettail_rholang_codegen::rho_net_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_ac_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_contextual_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_subst_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_native_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_native_fold_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_comm_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_structural_ac_injection_sites(language).is_empty()
            // Stage 4: a DEPTH-2 nested structural-AC rewrite (Ambient `InRule`/`OutRule`) reduces on
            // THIS typed native lane, so its report is produced by this body. Without carrying its
            // resolved σ + contractum, the runtime nested structural-AC σ-injection F-fn would have no
            // firing to reconstruct `⟦operand⟧` + `⟦reduct⟧` from.
            || !mettail_rholang_codegen::rho_net_nested_structural_ac_injection_sites(language)
                .is_empty();
    // The report `let` binding (mut only when we populate σ), the σ-resolution statement (resolves
    // σ + the firing CONTRACTUM under the SAME `__weigh` cost model the roots use, so the
    // contractum is the reduct the extractor reports — model-b: the host computed the
    // substitution), and the runtime bare-ification (source-identity op labels for the Rho
    // reflector, incl. the contractum).
    let (report_let, resolve_justifications, bareify_justifications) =
        if populate_rewrite_justifications {
            (
                quote! { let mut report },
                quote! {
                    // Resolve σ + contractum while the e-graph is still live, under the SAME
                    // `__weigh` the roots were extracted with (so the contractum is the extractor's
                    // funded-best reduct for the firing's root class).
                    report.rewrite_justifications =
                        ::dovetail::report::resolve_rewrite_justifications(
                            &eg,
                            &sat.rewrite_justifications,
                            __weigh,
                        );
                },
                quote! {
                    fn __mettail_bareify_label(__label: &str) -> String {
                        __label.split("::").nth(2).unwrap_or(__label).to_string()
                    }
                    fn __mettail_bareify_subterm(
                        __subterm: &mut mettail_runtime::RuntimeReflectedSubterm,
                    ) {
                        __subterm.constructor = __mettail_bareify_label(&__subterm.constructor);
                        for __child in &mut __subterm.children {
                            __mettail_bareify_subterm(__child);
                        }
                    }
                    fn __mettail_bareify_rewrite_justifications(
                        __justifications: &mut Vec<mettail_runtime::RuntimeRewriteJustification>,
                    ) {
                        for __justification in __justifications.iter_mut() {
                            __justification.rule_label =
                                __mettail_bareify_label(&__justification.rule_label);
                            for (_, __subterm) in __justification.sigma.iter_mut() {
                                __mettail_bareify_subterm(__subterm);
                            }
                            if let ::core::option::Option::Some(__contractum) =
                                __justification.contractum.as_mut()
                            {
                                __mettail_bareify_subterm(__contractum);
                            }
                        }
                    }
                    __mettail_bareify_rewrite_justifications(
                        &mut runtime_report.rewrite_justifications,
                    );
                },
            )
        } else {
            (quote! { let report }, quote! {}, quote! {})
        };

    quote! {
        // `op_enum_decl` carries `#[cfg(feature = "dovetail-codegen")]` on each of its items.
        #op_enum_decl

        #[cfg(feature = "dovetail-codegen")]
        impl #language_struct {
            /// Shared report builder. `record_source = false` is the production `exec` path —
            /// byte-identical to the pre-step-feature build: no source reconstruction runs and every
            /// `source_display` stays `None`. `record_source = true` is the step-only path, which
            /// additionally reconstructs each derivation node's source syntax. The flag gates ALL the
            /// extra work, so `exec` pays nothing for the stepper feature.
            fn __dovetail_report_impl(
                term: &dyn mettail_runtime::Term,
                max_iters: usize,
                max_nodes: usize,
                record_source: bool,
            ) -> Result<mettail_runtime::RuntimeDovetailRunReport, String> {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("expected {}Term, got {:?}", #language_lit, term))?;

                #(#typed_category_fns)*
                #(#reconstruct_fns)*
                #helpers
                #source_helpers

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
                let __dispatch = #dispatch;
                static __DOVETAIL_COMPILED_RULES: ::std::sync::OnceLock<
                    ::dovetail::rules::CompiledRuleSet<#enum_id>,
                > = ::std::sync::OnceLock::new();
                let __compiled_rules = __DOVETAIL_COMPILED_RULES.get_or_init(|| {
                    ::dovetail::rules::CompiledRuleSet::new(#rules_expr, #native_rules_expr)
                });
                let sat = eg.saturate_compiled_with_native(__compiled_rules, &__dispatch, __iters);
                if sat.outcome != ::dovetail::rules::SaturationOutcome::Converged {
                    return Err(format!(
                        "generated Dovetail saturation for language {} stopped before convergence: {:?}",
                        #language_lit,
                        sat.outcome,
                    ));
                }

                let mut __derivations = Vec::new();
                let mut __completeness = ::dovetail::extract::ExtractionCompleteness::Complete;
                // One extractor reused across ALL roots. `funded_best` lazily computes the
                // per-class inside weights (`wta::compute_inside_closed` = acyclic fixpoint +
                // Tarjan SCC + Newton closure) ONCE into `self.inside` and memoizes the per-class
                // best derivation; a fresh extractor per root re-ran that whole O(classes)
                // computation `roots` times, discarding the memo — the dominant report-path cost
                // when cross-category numeric ambiguity yields many equivalent roots. Correctness
                // is preserved: the inside weights are a property of the immutable, post-saturation
                // e-graph (identical for every root), `funded_best(root)` still returns THAT root's
                // own funded-best derivation, and the cumulative cycle-cut completeness aggregates
                // to the same final verdict the per-root `BoundedByCycleCut` check produced.
                let mut extractor = ::dovetail::extract::Extractor::new(&eg, __weigh);
                for __root in __roots {
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

                // Step-only: reconstruct each derivation node's source syntax, keyed by exact
                // `ContentKey`. Skipped entirely when `record_source` is false ⇒ `exec` pays nothing.
                let mut __source_map: ::std::collections::HashMap<Vec<u8>, String> =
                    ::std::collections::HashMap::new();
                if record_source {
                    for __d in &__derivations {
                        __collect_sources(__d, &mut __source_map);
                    }
                }

                #report_let = ::dovetail::report::report_from_extraction_with_rule_firings(
                    ::dovetail::extract::Extraction {
                        value: __derivations,
                        completeness: __completeness,
                    },
                    sat.rule_firings,
                );
                #resolve_justifications
                let mut runtime_report =
                    ::mettail_dovetail_runtime::project_dovetail_report(&report);
                #bareify_justifications
                if record_source {
                    for __term in &mut runtime_report.terms {
                        __term.source_display = __source_map.get(&__term.key).cloned();
                    }
                }
                runtime_report
                    .validate_shape()
                    .map_err(|err| format!("generated Dovetail report for language {} is malformed: {err}", #language_lit))?;
                Ok(runtime_report)
            }

            /// Compile this language's generated typed AST into a checked runtime Dovetail
            /// report, reducing `fold` rules in-engine via native rewrites (Increment 2/3). This is
            /// the production `exec` path — byte-identical (`record_source = false`).
            pub fn dovetail_report_for(
                term: &dyn mettail_runtime::Term,
                max_iters: usize,
                max_nodes: usize,
            ) -> Result<mettail_runtime::RuntimeDovetailRunReport, String> {
                Self::__dovetail_report_impl(term, max_iters, max_nodes, false)
            }

            /// Step-only report: same saturation/extraction as `dovetail_report_for`, but each term
            /// record carries its reconstructed source syntax (`source_display`) for comprehensible
            /// `step` display. Never reached on the `exec` path.
            pub fn dovetail_step_report(
                term: &dyn mettail_runtime::Term,
                max_iters: usize,
                max_nodes: usize,
            ) -> Result<mettail_runtime::RuntimeDovetailRunReport, String> {
                Self::__dovetail_report_impl(term, max_iters, max_nodes, true)
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

            #step_graph_method
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
