use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Generate eval() method for native types
use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind, TermParam};
use mettail_ast::language::{LanguageDef, NativeKind};
use mettail_ast::types::TypeExpr;
use crate::gen::native::lossless_coercion::build_lossless_coercion;
use crate::gen::native::{native_type_to_string, NativeType};
use crate::gen::runtime::wpda_codegen::builtin_metadata::classify_simple_projection_shape;
use crate::gen::{
    generate_literal_label, generate_var_label, is_literal_rule, literal_rule_nonterminal,
};

/// Classify a HOL rule for PDA purposes: determine whether we can generate the
/// work-stack form (PDA), or whether we must fall back to the recursive match.
///
/// The PDA form is generated only when every param is `TermParam::Simple` with
/// a `TypeExpr::Base(_)` type. Rules with abstractions, multi-abstractions,
/// guard bodies, or complex type shapes fall back to the recursive form — those
/// traversal modes are inherently non-linear and don't fit the work-stack
/// pattern cleanly, but their trees are bounded in depth by their structure
/// (binder scoping) and so don't pose a realistic stack-overflow risk.
///
/// Returns a `Vec<(name, TypeExpr, is_same_category)>` for rules that qualify,
/// or `None` if the rule has any param that can't be classified for PDA use.
fn classify_hol_rule_for_pda<'a>(
    rule: &'a GrammarRule,
    category: &syn::Ident,
) -> Option<Vec<(syn::Ident, &'a syn::Ident, bool, bool)>> {
    // Zero-ary rules (no term_context) are PDA-compatible: they have no
    // children to recurse into. Returning `Some(Vec::new())` rather than
    // `None` is the critical difference: `None` disables PDA for the WHOLE
    // category, while an empty vec just means this particular rule has no
    // same-cat children.
    //
    // Opt-Group: a TermParam::Optional with inner Simple/Base params is
    // PDA-compatible — each inner becomes a tuple entry with
    // `is_optional: true`. Inner non-Simple/non-Base params still fall
    // back to recursive eval.
    let Some(ctx) = rule.term_context.as_ref() else {
        return Some(Vec::new());
    };
    fn collect<'a>(
        params: &'a [TermParam],
        category: &syn::Ident,
        in_opt: bool,
        out: &mut Vec<(syn::Ident, &'a syn::Ident, bool, bool)>,
    ) -> Option<()> {
        for p in params {
            match p {
                TermParam::Simple { name, ty } => {
                    let base = match ty {
                        TypeExpr::Base(id) => id,
                        _ => return None,
                    };
                    let same_cat = base == category;
                    out.push((name.clone(), base, same_cat, in_opt));
                }
                TermParam::Optional { params: inner } => {
                    collect(inner, category, true, out)?;
                }
                _ => return None,
            }
        }
        Some(())
    }
    let mut out = Vec::with_capacity(ctx.len());
    collect(ctx, category, false, &mut out)?;
    Some(out)
}

/// Extract parameter names from term_context in the same order as generated variant fields.
/// Used for rust_code eval arms: param names match constructor field names.
fn term_context_param_names(term_context: &[TermParam]) -> Vec<syn::Ident> {
    let mut names = Vec::new();
    fn collect(params: &[TermParam], names: &mut Vec<syn::Ident>) {
        for p in params {
            match p {
                TermParam::Simple { name, .. } => names.push(name.clone()),
                TermParam::Abstraction { binder, body, .. } => {
                    names.push(binder.clone());
                    names.push(body.clone());
                },
                TermParam::MultiAbstraction { binder, body, .. } => {
                    names.push(binder.clone());
                    names.push(body.clone());
                },
                TermParam::GuardBody { name, .. } => {
                    let _ = name;
                },
                TermParam::Optional { params: inner } => {
                    collect(inner, names);
                },
            }
        }
    }
    collect(term_context, &mut names);
    names
}

/// True if the type is a category with `native_type` (e.g. `Int`, `Float`).
/// False for collection categories (`List`, `Bag`) and non-native types
/// — the param binding for those must use `.clone()` rather than `.eval()`.
fn type_has_native_eval(ty: &TypeExpr, language: &LanguageDef) -> bool {
    let cat = match ty {
        TypeExpr::Base(ident) => ident,
        _ => return false,
    };
    language
        .get_type(cat)
        .and_then(|t| t.native_type.as_ref())
        .is_some()
}

/// Extract parameter names AND whether each should bind via `.eval()` (true)
/// or `.clone()` (false). Categories without a native type (collections,
/// `Proc`, etc.) cannot be `.eval()`'d, so the cross-category bindings have
/// to clone — matching main's `term_context_params_with_eval`.
fn term_context_params_with_eval(
    term_context: &[TermParam],
    language: &LanguageDef,
) -> Vec<(syn::Ident, bool, bool)> {
    let mut out = Vec::new();
    fn collect(
        params: &[TermParam],
        language: &LanguageDef,
        in_opt: bool,
        out: &mut Vec<(syn::Ident, bool, bool)>,
    ) {
        for p in params {
            match p {
                TermParam::Simple { name, ty } => {
                    let use_eval = type_has_native_eval(ty, language);
                    out.push((name.clone(), use_eval, in_opt));
                },
                TermParam::Abstraction { binder, body, .. } => {
                    out.push((binder.clone(), false, in_opt));
                    out.push((body.clone(), false, in_opt));
                },
                TermParam::MultiAbstraction { binder, body, .. } => {
                    out.push((binder.clone(), false, in_opt));
                    out.push((body.clone(), false, in_opt));
                },
                TermParam::GuardBody { name, .. } => {
                    let _ = name;
                },
                TermParam::Optional { params: inner } => {
                    // Inner params are tagged `in_opt: true` so the
                    // emitter wraps their bindings in `Option<T>` map.
                    collect(inner, language, true, out);
                },
            }
        }
    }
    collect(term_context, language, false, &mut out);
    out
}

/// Phase D Layer 2 (2026-05-17, per
/// `~/.claude/plans/principled-fold-root-cause.md`): structural detector
/// replacing four string-vocabulary helpers
/// (`hol_bigrat_fraction_try_from_nd_option`, `hol_numeric_cast_option`,
/// `hol_int_fact_option`, `hol_bigrat_div_zero_guard`).
///
/// Returns `true` if the user's `rust_code` expression's outermost form is
/// structurally an `Option<_>` producer. The eval-method codegen then
/// wraps the arm with `.expect(...)` to unwrap; `try_eval` short-circuits
/// via `?` through the existing `safeify_and_wrap` pipeline.
///
/// Recognized syntactic shapes:
/// - **Function call to a `try_*`-prefixed function**: e.g.
///   `crate::numeric_dispatch::calc_try_int_bin(&a, w)`. The `try_*`
///   convention is the established Rust idiom for fallible constructors
///   (cf. `i32::try_from`, `String::try_into`, `num_rational::Ratio::try_from_nd`).
/// - **Explicit `Some(...)` / `None` literals at the outermost position**:
///   if the user wrote `if cond { Some(x) } else { None }`, the if's
///   value type is `Option<_>`.
/// - **`match` expression whose arms are `Some(...)` / `None`** (e.g. an
///   exhaustive `match` returning `Option`).
/// - **Method call to `try_*`-prefixed method**: e.g. `x.try_into()`.
/// - **Block expression whose final statement is one of the above**:
///   `{ let __r = try_compute(); __r }`.
///
/// The detector walks the `syn::Expr` AST recursively at the outermost
/// shape — NO string comparisons on rule labels, NO `(category, label)`
/// tuple matching. The user's code is the only legitimate authority on
/// what type their code returns.
fn rust_code_returns_option(code: &syn::Expr) -> bool {
    use syn::Expr;
    match code {
        // Direct `Some(...)` / `None` literal at outermost position.
        Expr::Call(call) => {
            if let Expr::Path(path) = call.func.as_ref() {
                if let Some(last) = path.path.segments.last() {
                    let name = last.ident.to_string();
                    if name == "Some" || name == "None" {
                        return true;
                    }
                    // `crate::module::try_xxx(...)` or just `try_xxx(...)`.
                    if name.starts_with("try_") {
                        return true;
                    }
                }
            }
            false
        }
        // `x.try_xxx(...)` — method call.
        Expr::MethodCall(mc) => mc.method.to_string().starts_with("try_"),
        // Bare path that resolves to `None`.
        Expr::Path(path) => path
            .path
            .segments
            .last()
            .map(|s| s.ident == "None")
            .unwrap_or(false),
        // `if cond { ... } else { ... }` — recurse into arms.
        Expr::If(expr_if) => {
            // Then-branch is a block; check its tail expression.
            let then_returns = expr_if
                .then_branch
                .stmts
                .last()
                .and_then(|stmt| match stmt {
                    syn::Stmt::Expr(e, _) => Some(rust_code_returns_option(e)),
                    _ => None,
                })
                .unwrap_or(false);
            // Else-branch: recurse on the else expression if present.
            let else_returns = expr_if
                .else_branch
                .as_ref()
                .map(|(_, e)| rust_code_returns_option(e))
                .unwrap_or(false);
            then_returns || else_returns
        }
        // `match scrutinee { Some(_) => ..., None => ... }` — check arms.
        Expr::Match(expr_match) => {
            expr_match.arms.iter().any(|arm| {
                rust_code_returns_option(&arm.body)
            }) || expr_match.arms.iter().all(|arm| {
                // Pattern matches `Some(...)` or `None`.
                match &arm.pat {
                    syn::Pat::TupleStruct(ts) => ts
                        .path
                        .segments
                        .last()
                        .map(|s| s.ident == "Some")
                        .unwrap_or(false),
                    syn::Pat::Path(p) => p
                        .path
                        .segments
                        .last()
                        .map(|s| s.ident == "None")
                        .unwrap_or(false),
                    syn::Pat::Ident(i) => i.ident == "None",
                    _ => false,
                }
            })
        }
        // `{ ... ; final_expr }` — check the tail expression.
        Expr::Block(b) => b
            .block
            .stmts
            .last()
            .and_then(|stmt| match stmt {
                syn::Stmt::Expr(e, _) => Some(rust_code_returns_option(e)),
                _ => None,
            })
            .unwrap_or(false),
        // Parenthesized expression — recurse.
        Expr::Paren(p) => rust_code_returns_option(&p.expr),
        _ => false,
    }
}

pub fn generate_eval_method(language: &LanguageDef) -> TokenStream {
    let mut impls = Vec::new();

    for lang_type in &language.types {
        let category = &lang_type.name;

        // Only generate for native types
        let native_type = match lang_type.native_type.as_ref() {
            Some(ty) => ty,
            None => continue,
        };

        // Find all rules for this category (may be empty for native types that only
        // get literal/Var from the grammar, e.g. Int with no explicit term rules)
        let rules: Vec<&GrammarRule> = language
            .terms
            .iter()
            .filter(|r| r.category == *category)
            .collect();

        // Literal label for try_fold_to_literal (resolve once)
        let has_literal_rule = rules.iter().any(|rule| is_literal_rule(rule));
        let literal_label = if has_literal_rule {
            rules
                .iter()
                .find(|r| is_literal_rule(r))
                .map(|r| r.label.clone())
                .unwrap_or_else(|| generate_literal_label(native_type))
        } else {
            generate_literal_label(native_type)
        };

        // Collection categories (List/Bag/Map): `.eval()` only unwraps the
        // literal variant (`ListLit`, `BagLit`, `MapLit`). Per-rule fold
        // bodies are consumed by Ascent rules, not by `.eval()` — trying to
        // compile the user's `![{ … match &i { Int::NumLit(n) => … } }]`
        // here would fail because eval-time params are native types, but
        // the user wrote patterns against enum variants. This matches main's
        // behaviour: collection eval returns the payload if already folded,
        // otherwise panics with "apply fold rules first".
        let is_collection_for_eval = lang_type.collection_kind.is_some();

        // Generate match arms for eval()
        let mut match_arms = Vec::new();

        // Add arm for auto-generated literal if no explicit literal rule
        if !has_literal_rule {
            let nt = NativeType::from_syn_type(native_type);
            let literal_arm = if nt.is_string() {
                quote! { #category::#literal_label(n) => n.clone(), }
            } else if is_collection_for_eval {
                quote! { #category::#literal_label(n) => n.clone(), }
            } else {
                quote! { #category::#literal_label(n) => *n, }
            };
            match_arms.push(literal_arm);
        }

        // Add arm for auto-generated Var variant if no explicit Var rule
        let var_label = generate_var_label(category);
        let panic_msg = format!(
            "Cannot evaluate {} - variables must be substituted via rewrites first",
            var_label
        );
        match_arms.push(quote! {
            #category::#var_label(_) => loop { panic!(#panic_msg) },
        });

        // Match arms for try_eval() -> Option<T> (Var and catch-all => None, rest => Some(...))
        let mut try_eval_arms: Vec<TokenStream> = Vec::new();

        // ─── PDA work-stack state ──────────────────────────────────────────
        // In parallel with the recursive `try_eval_arms`, we also build arms
        // for a work-stack-based `try_eval` so that deep same-category trees
        // (e.g. 10k-node `AddNum(AddNum(AddNum(…, Lit), Lit), Lit)`) do not
        // blow Rust's call stack. For rules whose params are all
        // `TermParam::Simple` with base types, we emit PDA Visit + Reduce
        // arms; for everything else we fall back to the recursive path.
        //
        // `pda_supported` becomes false as soon as we encounter a rule we
        // can't PDA-ify — at that point we drop the PDA variant and emit only
        // the recursive form. This is conservative: it sacrifices stack
        // safety for rules with abstractions in exchange for simpler codegen.
        // `pda_supported` stays true throughout — unclassifiable rules abort via
        // `compile_error!` in the `None` arm below rather than flipping the flag.
        let pda_supported = true;
        // Frame enum variants (one per HOL rule that has any same-category child):
        let mut pda_frame_variants: Vec<TokenStream> = Vec::new();
        // Arms inside `match node { ... }` of the Visit case:
        let mut pda_visit_arms: Vec<TokenStream> = Vec::new();
        // Arms inside `match frame { ... }` for non-Visit frames:
        let mut pda_reduce_arms: Vec<TokenStream> = Vec::new();

        // PDA literal arm
        if !has_literal_rule {
            let nt = NativeType::from_syn_type(native_type);
            let try_literal_arm = if nt.is_string() {
                quote! { #category::#literal_label(n) => Some(n.clone()), }
            } else if is_collection_for_eval {
                quote! { #category::#literal_label(n) => Some(n.clone()), }
            } else {
                quote! { #category::#literal_label(n) => Some(*n), }
            };
            try_eval_arms.push(try_literal_arm);

            let pda_literal_arm = if nt.is_string() {
                quote! { #category::#literal_label(n) => values.push(n.clone()), }
            } else if is_collection_for_eval {
                quote! { #category::#literal_label(n) => values.push(n.clone()), }
            } else {
                quote! { #category::#literal_label(n) => values.push(*n), }
            };
            pda_visit_arms.push(pda_literal_arm);
        }
        try_eval_arms.push(quote! {
            #category::#var_label(_) => None,
        });
        // PDA Var arm: eagerly bail via `return None`.
        pda_visit_arms.push(quote! {
            #category::#var_label(_) => return None,
        });

        // Collection categories delegate all per-rule evaluation to the Ascent
        // fold pipeline, which runs with different param types than `.eval()`
        // would use. Skip the per-rule arm generation entirely for them —
        // `.eval()` falls through to the catch-all panic arm when the term
        // has not yet been folded to its literal variant.
        if is_collection_for_eval {
            // Keep only the literal and Var arms already pushed above.
        } else {
        for rule in &rules {
            let label = &rule.label;

            // Literal rule: copy or clone depending on nonterminal (StringLiteral => clone)
            if is_literal_rule(rule) {
                let use_clone = literal_rule_nonterminal(rule) == Some(NonTerminalKind::StringLiteral);
                if use_clone {
                    match_arms.push(quote! {
                        #category::#label(n) => n.clone(),
                    });
                    try_eval_arms.push(quote! {
                        #category::#label(n) => Some(n.clone()),
                    });
                    pda_visit_arms.push(quote! {
                        #category::#label(n) => values.push(n.clone()),
                    });
                } else {
                    match_arms.push(quote! {
                        #category::#label(n) => *n,
                    });
                    try_eval_arms.push(quote! {
                        #category::#label(n) => Some(*n),
                    });
                    pda_visit_arms.push(quote! {
                        #category::#label(n) => values.push(*n),
                    });
                }
            }
            // Stage 3.12.9 β-2 (2026-05-04): synthetic auto-injection wrapper.
            //
            // Stage 3.13's auto_inject.rs::make_injection_rule emits
            // `<Source>To<Target> . v:Source |- v : Target ;` constructors
            // with `is_auto_injected = true`. Pre-Stage-3.12.9 these
            // synthetic variants fell through `try_eval`'s catch-all
            // `_ => None` arm, which made `eval()` panic when the rewrite
            // pipeline didn't collapse the wrapper before evaluation —
            // surfacing as the 7 `cross_cat_rhocalc_castop_*` failures.
            //
            // β-2 closes the gap: detect the synthetic rule via
            // `classify_simple_projection_shape`, look up source/target
            // NativeKinds, and (if the lattice declares the edge as
            // lossless) emit a `try_eval` arm that recursively evaluates
            // the inner term and applies the lossless coercion.
            //
            // Cross-category recursion: same idiom as calc's existing
            // `BigRat::Fraction(a, b)` arm at
            // `target/generated/calculator/eval.rs:1002-1009`. Bounded by
            // lossless-lattice depth (≤ 4 hops in practice).
            else if rule.is_auto_injected
                && classify_simple_projection_shape(rule).is_some()
            {
                let shape = classify_simple_projection_shape(rule)
                    .expect("just checked classify_simple_projection_shape");
                let source_native_kind = language
                    .types
                    .iter()
                    .find(|t| t.name.to_string() == shape.source_category)
                    .and_then(|t| t.native_type.as_ref())
                    .map(NativeKind::from_syn_type);
                let target_native_kind = NativeKind::from_syn_type(native_type);

                // Coercion only emits for declared lossless edges. Lossy
                // auto-injection (gated behind `auto_inject_lossy`) and
                // edges with no Rust-level coercion fall through to the
                // existing catch-all `_ => None`.
                let coercion = source_native_kind.and_then(|src| {
                    let v_ident = format_ident!("__v");
                    let v_expr = quote! { #v_ident };
                    build_lossless_coercion(src, target_native_kind, &v_expr)
                });

                if let Some(coercion_expr) = coercion {
                    let v_ident = format_ident!("__v");
                    // match_arms is the gate that decides whether
                    // `eval()` / `try_eval()` impls are emitted (line
                    // ~837: `if !match_arms.is_empty()`). The body here
                    // is unused — `eval()` delegates to `try_eval()` —
                    // but the gate needs at least one arm, so we push a
                    // placeholder that mirrors the try_eval semantics.
                    match_arms.push(quote! {
                        #category::#label(__v_box) => {
                            let #v_ident = __v_box.as_ref().eval();
                            (#coercion_expr)
                        },
                    });

                    // try_eval arm (recursive form): bubbles `None` on
                    // either inner failure (e.g., source contains a Var)
                    // or fallible coercion (NaN→Float→BigRat).
                    try_eval_arms.push(quote! {
                        #category::#label(__v_box) => {
                            let #v_ident = __v_box.as_ref().try_eval()?;
                            Some(#coercion_expr)
                        }
                    });

                    // PDA Visit arm: cross-category recursion via the
                    // inner type's `try_eval`. Bounded by lossless-lattice
                    // depth (≤ 4-hop chain like Int → BigInt → BigRat).
                    pda_visit_arms.push(quote! {
                        #category::#label(__v_box) => {
                            let #v_ident = __v_box.as_ref().try_eval()?;
                            values.push(#coercion_expr);
                        }
                    });
                }
            }
            // HOL syntax: rule with Rust code block - generate eval from rust_code
            else if let Some(ref rust_code_block) = rule.rust_code {
                // Resolve `(name, use_eval)` per param: native-typed categories
                // bind via `.eval()`; collection / non-native categories bind
                // via `.clone()` (cannot be `.eval()`'d).
                let params_with_eval = rule
                    .term_context
                    .as_ref()
                    .map(|ctx| term_context_params_with_eval(ctx, language))
                    .unwrap_or_default();
                let param_names: Vec<syn::Ident> =
                    params_with_eval.iter().map(|(n, _, _)| n.clone()).collect();
                let param_count = param_names.len();
                // Opt-Group: when `is_optional`, the variant field is
                // `Option<Box<Cat>>` (not `Box<Cat>`). The user's eval
                // code expects the param bound to `Option<NativeT>`
                // (when use_eval) or `Option<&Cat>` (when !use_eval).
                // Map each binding accordingly.
                let param_bindings: Vec<_> = params_with_eval
                    .iter()
                    .map(|(name, use_eval, is_optional)| {
                        if *is_optional {
                            if *use_eval {
                                quote! { let #name = #name.as_ref().map(|__b| __b.as_ref().eval()); }
                            } else {
                                quote! { let #name = #name.as_ref().map(|__b| __b.as_ref()); }
                            }
                        } else if *use_eval {
                            quote! { let #name = #name.as_ref().eval(); }
                        } else {
                            // Non-native categories (Proc, List, Bag, Map) must
                            // bind by reference — user eval code typically
                            // `match`es on these and Rust prohibits moving out
                            // of `Drop` types in a by-value match. `.as_ref()`
                            // on `Box<Category>` yields `&Category`, which
                            // matches without moving.
                            quote! { let #name = #name.as_ref(); }
                        }
                    })
                    .collect();
                let try_param_bindings: Vec<_> = params_with_eval
                    .iter()
                    .map(|(name, use_eval, is_optional)| {
                        if *is_optional {
                            if *use_eval {
                                quote! {
                                    let #name: Option<_> = match #name.as_ref() {
                                        Some(__b) => Some(__b.as_ref().try_eval()?),
                                        None => None,
                                    };
                                }
                            } else {
                                quote! { let #name = #name.as_ref().map(|__b| __b.as_ref()); }
                            }
                        } else if *use_eval {
                            quote! { let #name = #name.as_ref().try_eval()?; }
                        } else {
                            quote! { let #name = #name.as_ref(); }
                        }
                    })
                    .collect();
                let rust_code = &rust_code_block.code;
                // Phase D Layer 2 (2026-05-17, per
                // `~/.claude/plans/principled-fold-root-cause.md`): replace
                // FOUR string-vocabulary helpers (each matching specific
                // (category, label) tuples for `Fraction`/`*Bin`/`*Cast`/
                // `Fact`/`DivBigRat`) with ONE structural detector
                // (`rust_code_returns_option`) that walks the user's
                // `syn::Expr` to determine whether the code returns
                // `Option<T>` natively.
                //
                // The unified Option-returning arm replaces three of the
                // four previous special cases (the three `_option`
                // helpers). The fourth (`hol_bigrat_div_zero_guard`) was
                // a pre-condition guard for `DivBigRat` that pre-checks
                // divisor-zero before invoking num-rational's reduce.
                // Layer 2 removes the pre-check: divisor-zero is now the
                // grammar author's responsibility — declare a rewrite
                // `(div_bigrat a b) ~> error` premised on `b == 0` in the
                // `rewrites { }` block. num-rational's natural panic on
                // divisor-zero serves as the "should have been rewritten
                // first" failure-mode indicator.
                let returns_option = rust_code_returns_option(rust_code);
                let match_arm = if returns_option && param_count > 0 {
                    quote! {
                        #category::#label(#(#param_names),*) => {
                            #(#param_bindings)*
                            (#rust_code).expect(
                                "evaluation reached unreachable Option::None sentinel; \
                                 user grammar must normalize via rewrite rules \
                                 (e.g., (cast_op a) ~> cast_error) before eval()",
                            )
                        },
                    }
                } else if param_count == 0 {
                    quote! {
                        #category::#label => (#rust_code),
                    }
                } else {
                    quote! {
                        #category::#label(#(#param_names),*) => {
                            #(#param_bindings)*
                            (#rust_code)
                        },
                    }
                };
                match_arms.push(match_arm);
                // `try_eval` treats each evaluation step as a trampoline frame: if
                // the step's arithmetic overflows (e.g., i32 factorial) or produces
                // `NaN` (e.g., `0.0 / 0.0`), the frame yields `None` rather than
                // panicking. We achieve this by rewriting the user's `#rust_code`
                // through `rust_code_rewrite::safeify` — every `+`, `-`, `*`, `/`,
                // `%`, unary `-`, `.pow(…)`, `.product::<_>()`, `.sqrt()`, etc. is
                // replaced with its `SafeArith` / `SafeFloat` counterpart, and the
                // whole expression is wrapped in a closure returning `Option<_>`.
                // No panic is ever raised, so there is no unwind path for
                // proptest's panic hook to race with under nextest.
                //
                // The rewritten expression parses as a `syn::Expr`. For the
                // parameter-less arm (where the user's code is embedded as a
                // statement-or-expression block), we parse and re-rewrite.
                let rust_code_expr: syn::Expr = syn::parse_quote!({ #rust_code });
                let safe_closure_call = crate::gen::native::rust_code_rewrite::safeify_and_wrap(&rust_code_expr);
                let try_arm = if param_count == 0 {
                    quote! {
                        #category::#label => {
                            #safe_closure_call
                        }
                    }
                } else {
                    quote! {
                        #category::#label(#(#param_names),*) => {
                            #(#try_param_bindings)*
                            #safe_closure_call
                        },
                    }
                };
                try_eval_arms.push(try_arm);

                // Also build PDA Visit/Reduce arms for this rule if possible.
                // If the rule has any non-Simple param (e.g. Abstraction), we
                // leave the PDA path un-built for the whole category — the
                // recursive fallback still handles this rule correctly.
                if pda_supported {
                    match classify_hol_rule_for_pda(rule, category) {
                        Some(classified) => {
                            let reduce_variant = format_ident!("Reduce{}", label);
                            // For each cross-category param, decide how it's
                            // captured in the Reduce frame:
                            //   - CrossKind::Native(storage_ty): evaluate to a
                            //     native value at Visit time and store it.
                            //   - CrossKind::Borrow(cat): the param's category
                            //     has no native_type (e.g. Proc in calculator).
                            //     We store an owned clone of the child term
                            //     (`Box<Cat>`) in the frame and bind `&Cat` to
                            //     the user's rust_code at Reduce time — the
                            //     recursive fallback does exactly the same
                            //     via `let #n = #n.as_ref();`.
                            // Opt-Group: `Optional(storage_ty, use_eval)` represents
                            // an `Option<storage_ty>` field; visit emits
                            // `Option::map` over `try_eval()` (Native) or
                            // `Option::clone()` (Borrow). Optional same-cat
                            // children are routed through cross_kinds (not the
                            // same-cat Visit-push path) because the `Some(_)`/
                            // `None` branching doesn't fit the unconditional
                            // Visit-frame push.
                            enum CrossKind {
                                Native(TokenStream),
                                Borrow(TokenStream),
                                OptionalNative(TokenStream),
                                OptionalBorrow(TokenStream),
                            }
                            let mut cross_kinds: Vec<(syn::Ident, CrossKind)> = Vec::new();
                            for (name, ty_id, same, is_optional) in &classified {
                                if *same && !*is_optional { continue; }
                                let target_native = language
                                    .types
                                    .iter()
                                    .find(|t| t.name == **ty_id)
                                    .and_then(|t| t.native_type.as_ref());
                                let storage_ty: TokenStream = match target_native {
                                    Some(nt) => match NativeType::from_syn_type(nt) {
                                        NativeType::Str => quote! { std::string::String },
                                        NativeType::Float32 => quote! { ::mettail_runtime::CanonicalFloat32 },
                                        NativeType::Float64 => quote! { ::mettail_runtime::CanonicalFloat64 },
                                        _ => quote! { #nt },
                                    },
                                    None => {
                                        // ARC refactor (2026-05-28): AST children are
                                        // `Arc<Cat>`, and the eval frame receives the
                                        // shared Arc extracted from the AST field — so
                                        // the frame's storage type must be `Arc<Cat>`
                                        // (was `Box<Cat>`). The user's rust_code binds
                                        // `&Cat` via deref, which works identically for
                                        // Arc.
                                        let ty_ident = *ty_id;
                                        quote! { ::std::sync::Arc<#ty_ident> }
                                    }
                                };
                                let kind = match (target_native.is_some(), *is_optional) {
                                    (true, false) => CrossKind::Native(storage_ty),
                                    (false, false) => CrossKind::Borrow(storage_ty),
                                    (true, true) => CrossKind::OptionalNative(storage_ty),
                                    (false, true) => CrossKind::OptionalBorrow(storage_ty),
                                };
                                cross_kinds.push((name.clone(), kind));
                            }

                            let cross_fields: Vec<TokenStream> = cross_kinds
                                .iter()
                                .map(|(n, k)| match k {
                                    CrossKind::Native(ty) | CrossKind::Borrow(ty) => {
                                        quote! { #n: #ty }
                                    }
                                    CrossKind::OptionalNative(ty) | CrossKind::OptionalBorrow(ty) => {
                                        quote! { #n: ::std::option::Option<#ty> }
                                    }
                                })
                                .collect();
                            let cross_field_names: Vec<syn::Ident> = cross_kinds
                                .iter()
                                .map(|(n, _)| n.clone())
                                .collect();

                            // Emit Frame variant.
                            if cross_fields.is_empty() {
                                pda_frame_variants.push(quote! { #reduce_variant, });
                            } else {
                                pda_frame_variants.push(quote! {
                                    #reduce_variant { #(#cross_fields),* },
                                });
                            }

                            // Emit Visit arm for this constructor.
                            // Pattern: #category::#label(p0, p1, ...).
                            let param_pat: Vec<_> = classified
                                .iter()
                                .map(|(n, _, _, _)| quote! { #n })
                                .collect();
                            let eager_cross_evals: Vec<TokenStream> = cross_kinds
                                .iter()
                                .map(|(n, k)| match k {
                                    CrossKind::Native(_) => quote! {
                                        // Native cross-cat: evaluate now. Cross-category
                                        // tree depth is bounded in practice.
                                        let #n = #n.as_ref().try_eval()?;
                                    },
                                    CrossKind::Borrow(_) => quote! {
                                        // Non-native cross-cat (e.g. Proc): clone the
                                        // child box so the frame owns it. `rust_code`
                                        // receives `&Cat` after deref at Reduce time.
                                        let #n = #n.clone();
                                    },
                                    CrossKind::OptionalNative(_) => quote! {
                                        // Opt-Group: Option<Box<Cat>> with native eval.
                                        // Map over Some, propagating `?` for try_eval failure.
                                        let #n: ::std::option::Option<_> = match #n.as_ref() {
                                            ::std::option::Option::Some(__b) => {
                                                ::std::option::Option::Some(__b.as_ref().try_eval()?)
                                            }
                                            ::std::option::Option::None => ::std::option::Option::None,
                                        };
                                    },
                                    CrossKind::OptionalBorrow(_) => quote! {
                                        // Opt-Group: Option<Box<Cat>> with borrow.
                                        // Clone the inner Box if Some.
                                        let #n: ::std::option::Option<_> = #n.clone();
                                    },
                                })
                                .collect();
                            let reduce_push = if cross_field_names.is_empty() {
                                quote! { work.push(__EvalFrame::#reduce_variant); }
                            } else {
                                quote! {
                                    work.push(__EvalFrame::#reduce_variant {
                                        #(#cross_field_names),*
                                    });
                                }
                            };
                            // Same-category children: push in REVERSE so the left-
                            // most child is processed first (LIFO stack).
                            // Opt-Group: Optional same-cat children are routed
                            // through cross_kinds (with OptionalBorrow), NOT
                            // through this Visit-push path — they're captured
                            // unconditionally and unwrapped at Reduce time.
                            let same_cat_pushes: Vec<TokenStream> = classified
                                .iter()
                                .rev()
                                .filter(|(_, _, same, is_opt)| *same && !*is_opt)
                                .map(|(n, _, _, _)| quote! {
                                    work.push(__EvalFrame::Visit(#n.as_ref()));
                                })
                                .collect();

                            // For zero-ary rules (classified empty), match pattern
                            // has no parens: `Int::Err` not `Int::Err()`.
                            let visit_pat = if param_pat.is_empty() {
                                quote! { #category::#label }
                            } else {
                                quote! { #category::#label(#(#param_pat),*) }
                            };
                            pda_visit_arms.push(quote! {
                                #visit_pat => {
                                    #(#eager_cross_evals)*
                                    #reduce_push
                                    #(#same_cat_pushes)*
                                }
                            });

                            // Emit Reduce arm: pop same-cat values (in reverse
                            // param order = pop order), then run the safeified
                            // rust_code with all params in scope. Non-native
                            // cross-cat params bind as `&Cat` (deref the Box
                            // stored in the frame) so user rust_code sees the
                            // same borrow as the recursive fallback.
                            let frame_pat = if cross_field_names.is_empty() {
                                quote! { __EvalFrame::#reduce_variant }
                            } else {
                                quote! {
                                    __EvalFrame::#reduce_variant { #(#cross_field_names),* }
                                }
                            };
                            // Opt-Group: Optional same-cat children are NOT
                            // popped from values (they were captured into the
                            // frame as `Option<Box<Cat>>`); only pure-same-cat
                            // children are pushed/popped via Visit frames.
                            let pops: Vec<TokenStream> = classified
                                .iter()
                                .rev()
                                .filter(|(_, _, same, is_opt)| *same && !*is_opt)
                                .map(|(n, _, _, _)| quote! {
                                    // Pops are in reverse param order; since we
                                    // push in reverse earlier (so leftmost is
                                    // visited first = processed first = pushed to
                                    // value stack first), popping in reverse gives
                                    // us rightmost-first which matches the name
                                    // binding order below.
                                    let #n = values.pop().expect("PDA same-cat value");
                                })
                                .collect();
                            let borrow_rebinds: Vec<TokenStream> = cross_kinds
                                .iter()
                                .filter_map(|(n, k)| match k {
                                    CrossKind::Borrow(_) => Some(quote! {
                                        // Frame owns a Box<Cat>; give user
                                        // `&Cat` via explicit deref-and-reborrow.
                                        let #n = &*#n;
                                    }),
                                    CrossKind::Native(_) => None,
                                    CrossKind::OptionalBorrow(_) => Some(quote! {
                                        // Opt-Group: Frame owns Option<Box<Cat>>.
                                        // Give user `Option<&Cat>` via map deref.
                                        let #n: ::std::option::Option<&_> = #n.as_ref().map(|__b| &**__b);
                                    }),
                                    CrossKind::OptionalNative(_) => None,
                                })
                                .collect();
                            pda_reduce_arms.push(quote! {
                                #frame_pat => {
                                    #(#pops)*
                                    #(#borrow_rebinds)*
                                    match #safe_closure_call {
                                        Some(__v) => values.push(__v),
                                        None => return None,
                                    }
                                }
                            });
                        }
                        None => {
                            // Silent recursive fallback is no longer permitted:
                            // the classifier refusing a rule would push us back
                            // onto the stack-consuming `match self { … }` path,
                            // which is exactly what the WFST-architecture PDA
                            // refactor ruled out. If this fires, the classifier
                            // needs a new case (report upstream with the rule
                            // syntax that triggered it).
                            let msg = format!(
                                "mettail: cannot emit stack-safe `try_eval` frame for \
                                 rule `{}::{}` — `classify_hol_rule_for_pda` returned \
                                 `None`. Silent recursive fallback is not permitted. \
                                 Report this as a macro bug, including the rule's \
                                 syntax.",
                                category, rule.label,
                            );
                            return quote::quote_spanned!(rule.label.span()=> compile_error!(#msg););
                        }
                    }
                }
            }
            // Handle rules with recursive self-reference and Var (like Assign . Int ::= Var "=" Int)
            // These evaluate to the value of the recursive argument
            else {
                // Find non-terminals in the rule
                let non_terminals: Vec<_> = rule
                    .items
                    .iter()
                    .filter_map(|item| match item {
                        GrammarItem::NonTerminal { ident, kind } => Some((ident.to_string(), *kind)),
                        _ => None,
                    })
                    .collect();

                // Check if this has Var and a recursive reference
                let has_var = non_terminals.iter().any(|(_, kind)| *kind == NonTerminalKind::Var);
                let has_recursive = non_terminals.iter().any(|(name, _)| *name == category.to_string());

                if has_var && has_recursive {
                    match_arms.push(quote! {
                        #category::#label(_, expr) => expr.as_ref().eval(),
                    });
                    try_eval_arms.push(quote! {
                        #category::#label(_, expr) => expr.as_ref().try_eval(),
                    });
                    // PDA: forward to child via Visit frame (no Reduce needed).
                    pda_visit_arms.push(quote! {
                        #category::#label(_, expr) => {
                            work.push(__EvalFrame::Visit(expr.as_ref()));
                        }
                    });
                }
            }
        }
        } // end: `else` of `if is_collection_for_eval`

        if !match_arms.is_empty() {
            let nt = NativeType::from_syn_type(native_type);
            let return_type = match nt {
                NativeType::Str => quote! { std::string::String },
                NativeType::Float32 => quote! { mettail_runtime::CanonicalFloat32 },
                NativeType::Float64 => quote! { mettail_runtime::CanonicalFloat64 },
                _ => quote! { #native_type },
            };
            try_eval_arms.push(quote! { _ => None, });

            // If every HOL rule in this category classified cleanly for PDA,
            // emit the work-stack form. Otherwise fall back to the recursive
            // match on `self`. Either form has the same external signature.
            let try_eval_body = if pda_supported && !pda_reduce_arms.is_empty() {
                // Work-stack PDA: iterative traversal of the term tree. The
                // value stack holds intermediate native values; the work stack
                // holds `__EvalFrame::Visit(node)` for nodes yet to visit and
                // `Frame::ReduceXxx { ... }` for pending reductions. Stack
                // depth is O(1) with respect to same-category tree depth;
                // only cross-category subterms introduce bounded recursion.
                //
                // The Frame enum is local to this method so it doesn't
                // conflict with other categories' PDAs.
                quote! {
                    {
                        #[allow(non_camel_case_types)]
                        enum __EvalFrame<'a> {
                            Visit(&'a #category),
                            #(#pda_frame_variants)*
                        }
                        let mut work: ::std::vec::Vec<__EvalFrame<'_>> =
                            ::std::vec![__EvalFrame::Visit(self)];
                        let mut values: ::std::vec::Vec<#return_type> =
                            ::std::vec::Vec::new();
                        while let Some(__frame) = work.pop() {
                            match __frame {
                                __EvalFrame::Visit(__node) => match __node {
                                    #(#pda_visit_arms)*
                                    _ => return None,
                                },
                                #(#pda_reduce_arms)*
                            }
                        }
                        values.pop()
                    }
                }
            } else {
                quote! {
                    match self {
                        #(#try_eval_arms)*
                    }
                }
            };

            // `eval()` delegates to the PDA-based `try_eval()` and unwraps:
            // any None (Var, overflow) becomes a panic with the same message
            // semantics as the previous recursive `match self` arm. This avoids
            // a parallel recursive code path and guarantees identical stack
            // safety to `try_eval`. Note: overflow now panics uniformly in
            // debug and release (previously wrapped in release); this matches
            // the stated contract "fully evaluable or panic".
            let impl_block = quote! {
                impl #category {
                    /// Evaluate the expression to its native type value.
                    /// Variables must be substituted via rewrites before evaluation.
                    pub fn eval(&self) -> #return_type {
                        self.try_eval().expect(
                            "Cannot evaluate expression - contains unevaluated terms or arithmetic overflowed. Apply rewrites first."
                        )
                    }
                    /// Like eval but returns None for unevaluable terms (e.g. Var) instead of panicking.
                    pub fn try_eval(&self) -> std::option::Option<#return_type> {
                        #try_eval_body
                    }
                    /// If this term is fully evaluable, return its value as a literal; otherwise None.
                    pub fn try_fold_to_literal(&self) -> std::option::Option<Self> {
                        self.try_eval().map(|v| #category::#literal_label(v))
                    }
                }
            };
            impls.push(impl_block);

            // Implement arithmetic ops for numeric native types so rust_code in other categories
            // (e.g. Proc::Add with CastInt(a), CastInt(b) => a + b) can use +, -, etc. on term types.
            let type_str = native_type_to_string(native_type);
            let is_numeric = matches!(
                type_str.as_str(),
                "i32" | "i64" | "u32" | "u64" | "isize" | "usize" | "f32" | "f64"
            );
            if is_numeric {
                // These `std::ops::*` impls exist so user `![...]` code that has
                // *not* been routed through `rust_code_rewrite::safeify` (e.g. a
                // direct `a + b` written by a manual caller that bypassed the
                // rewrite pass) still compiles. The bodies delegate to the
                // `SafeArith` impl below — which uses `try_eval` + stdlib
                // `checked_*` — and swap a `None` result for the literal's
                // `Default` value rather than panicking. Silent saturation is
                // wrong for a hot path, but every hot path in generated code
                // *is* safeified; this path is a fallback for unknown callers
                // and must never abort (see #radiant-pondering-kahan plan).
                let ops_impl = quote! {
                    impl std::ops::Add for #category {
                        type Output = #category;
                        fn add(self, rhs: #category) -> #category {
                            <Self as ::mettail_runtime::SafeArith>::safe_add(self, rhs)
                                .unwrap_or_else(|| #category::#literal_label(Default::default()))
                        }
                    }
                    impl std::ops::Sub for #category {
                        type Output = #category;
                        fn sub(self, rhs: #category) -> #category {
                            <Self as ::mettail_runtime::SafeArith>::safe_sub(self, rhs)
                                .unwrap_or_else(|| #category::#literal_label(Default::default()))
                        }
                    }
                    impl std::ops::Mul for #category {
                        type Output = #category;
                        fn mul(self, rhs: #category) -> #category {
                            <Self as ::mettail_runtime::SafeArith>::safe_mul(self, rhs)
                                .unwrap_or_else(|| #category::#literal_label(Default::default()))
                        }
                    }
                    impl std::ops::Div for #category {
                        type Output = #category;
                        fn div(self, rhs: #category) -> #category {
                            <Self as ::mettail_runtime::SafeArith>::safe_div(self, rhs)
                                .unwrap_or_else(|| #category::#literal_label(Default::default()))
                        }
                    }
                    impl std::ops::Rem for #category {
                        type Output = #category;
                        fn rem(self, rhs: #category) -> #category {
                            <Self as ::mettail_runtime::SafeArith>::safe_rem(self, rhs)
                                .unwrap_or_else(|| #category::#literal_label(Default::default()))
                        }
                    }
                };
                impls.push(ops_impl);

                // `SafeArith` for the category wrapper: delegates to `try_eval` to
                // get the underlying native value, then delegates to the native
                // `SafeArith` impl, and re-wraps the result as a literal. This is
                // what the `rust_code_rewrite` pass emits when a user's `![...]`
                // block contains `a + b` where `a` / `b` are typed as the category
                // (e.g., rhocalc's `Proc::CastInt(Box::new(*a.clone() + *b.clone()))`
                // with `a, b: &Box<Int>` — after `*a.clone()` they are `Int`).
                //
                // Returning `None` from any of the three steps (unevaluable operand,
                // arithmetic failure, or invalid literal) causes the enclosing
                // rewrite to not fire, matching the overall policy.
                let safe_arith_impl = quote! {
                    impl ::mettail_runtime::SafeArith for #category {
                        type Output = Self;
                        fn safe_add(self, rhs: Self) -> Option<Self> {
                            let a = self.try_eval()?;
                            let b = rhs.try_eval()?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_add(a, b)?;
                            Some(#category::#literal_label(r))
                        }
                        fn safe_sub(self, rhs: Self) -> Option<Self> {
                            let a = self.try_eval()?;
                            let b = rhs.try_eval()?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_sub(a, b)?;
                            Some(#category::#literal_label(r))
                        }
                        fn safe_mul(self, rhs: Self) -> Option<Self> {
                            let a = self.try_eval()?;
                            let b = rhs.try_eval()?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_mul(a, b)?;
                            Some(#category::#literal_label(r))
                        }
                        fn safe_div(self, rhs: Self) -> Option<Self> {
                            let a = self.try_eval()?;
                            let b = rhs.try_eval()?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_div(a, b)?;
                            Some(#category::#literal_label(r))
                        }
                        fn safe_rem(self, rhs: Self) -> Option<Self> {
                            let a = self.try_eval()?;
                            let b = rhs.try_eval()?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_rem(a, b)?;
                            Some(#category::#literal_label(r))
                        }
                        fn safe_neg(self) -> Option<Self> {
                            let a = self.try_eval()?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_neg(a)?;
                            Some(#category::#literal_label(r))
                        }
                        fn safe_not(self) -> Option<Self> {
                            let a = self.try_eval()?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_not(a)?;
                            Some(#category::#literal_label(r))
                        }
                        fn safe_pow(self, exp: i32) -> Option<Self> {
                            let a = self.try_eval()?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_pow(a, exp)?;
                            Some(#category::#literal_label(r))
                        }
                    }
                };
                impls.push(safe_arith_impl);
            }
        }
    }

    quote! {
        #(#impls)*
    }
}
