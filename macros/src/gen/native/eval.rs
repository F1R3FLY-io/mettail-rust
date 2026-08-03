use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::gen::capture::{capture_layout, CaptureFieldKind};
use crate::gen::native::lossless_coercion::build_lossless_coercion;
use crate::gen::native::{native_type_to_string, NativeType};
use crate::gen::runtime::wpda_codegen::builtin_metadata::classify_simple_projection_shape;
use crate::gen::{
    generate_literal_label, generate_var_label, is_literal_rule, literal_rule_nonterminal,
};
/// Generate eval() method for native types
use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind, TermParam};
use mettail_ast::language::{LanguageDef, NativeKind};
use mettail_ast::types::TypeExpr;

/// The FIRST generic argument of a declared collection native type — the
/// collection's ELEMENT type.
///
/// #74: rholang declares `![mettail_runtime::PathMapLit<Proc, Proc>] as Pathmap`,
/// and both parameters are the same generated element type. Set/map optionality
/// is stored once in `PathMapLit`'s mode. This extracts `E` so `eval()`'s return type is rebuilt the same
/// way `crate::gen::types::enums` builds the enum variant's payload. Keeping the
/// two derivations textually parallel is deliberate: if they diverge the
/// generated code does not compile, which is the failure mode we want.
fn pathmap_element_type(native_type: &syn::Type) -> Option<TokenStream> {
    let syn::Type::Path(type_path) = native_type else {
        return None;
    };
    let seg = type_path.path.segments.last()?;
    let syn::PathArguments::AngleBracketed(args) = &seg.arguments else {
        return None;
    };
    match args.args.first()? {
        syn::GenericArgument::Type(elem) => Some(quote! { #elem }),
        _ => None,
    }
}

/// Per-field PDA classification of a HOL rule's term context — one entry per
/// generated variant field, in declaration order.
///
/// Task #14 (Option<Guard>): predicates are OPAQUE to evaluation. A `Guard`
/// entry occupies a constructor position (every match pattern over the
/// variant MUST cover it or the arm's arity is wrong), but it is never
/// evaluated, captured into the Reduce frame, pushed as a Visit, or popped
/// from the value stack.
enum PdaParam<'a> {
    /// `TermParam::Simple` with a `TypeExpr::Base(_)` type — the only shape
    /// the PDA visits/reduces.
    Term {
        name: syn::Ident,
        ty: &'a syn::Ident,
        same_cat: bool,
        is_optional: bool,
    },
    /// A `?g:Guard` predicate slot (top-level or inside `#opt(...)`). The
    /// name is used only to render an underscore-prefixed pattern binder.
    Guard { name: syn::Ident },
}

/// Classify a HOL rule for PDA purposes: determine whether we can generate
/// the work-stack form (PDA).
///
/// The PDA form is generated when every param is `TermParam::Simple` with a
/// `TypeExpr::Base(_)` type (optionally nested in `#opt(...)`) or a
/// `TermParam::GuardBody` (any nesting). There is NO recursive fallback:
/// rules with abstractions, multi-abstractions, or complex type shapes
/// return `None`, which the caller turns into a `compile_error!` (silent
/// recursive fallback was abolished by the WFST-architecture PDA refactor —
/// see the `None` arm at the sole call site).
///
/// Returns one [`PdaParam`] per variant field for rules that qualify, or
/// `None` if the rule has any param that can't be classified for PDA use.
fn classify_hol_rule_for_pda<'a>(
    rule: &'a GrammarRule,
    category: &syn::Ident,
) -> Option<Vec<PdaParam<'a>>> {
    // Zero-ary rules (no term_context) are PDA-compatible: they have no
    // children to recurse into. Returning `Some(Vec::new())` rather than
    // `None` is the critical difference: `None` aborts the WHOLE category
    // via compile_error!, while an empty vec just means this particular
    // rule has no same-cat children.
    let Some(ctx) = rule.term_context.as_ref() else {
        return Some(Vec::new());
    };
    classify_term_params_for_pda(ctx, category)
}

/// The recursive body of [`classify_hol_rule_for_pda`], hoisted so unit
/// tests can exercise the classification over a bare `&[TermParam]`.
///
/// Opt-Group: a `TermParam::Optional` with inner Simple/Base params is
/// PDA-compatible — each inner becomes a [`PdaParam::Term`] with
/// `is_optional: true`. A `TermParam::GuardBody` (top-level or
/// Optional-nested) becomes [`PdaParam::Guard`]. Inner non-Simple/non-Base
/// params abort classification.
fn classify_term_params_for_pda<'a>(
    params: &'a [TermParam],
    category: &syn::Ident,
) -> Option<Vec<PdaParam<'a>>> {
    fn collect<'a>(
        params: &'a [TermParam],
        category: &syn::Ident,
        in_opt: bool,
        out: &mut Vec<PdaParam<'a>>,
    ) -> Option<()> {
        for p in params {
            match p {
                TermParam::Simple { name, ty } => {
                    let base = match ty {
                        TypeExpr::Base(id) => id,
                        _ => return None,
                    };
                    let same_cat = base == category;
                    out.push(PdaParam::Term {
                        name: name.clone(),
                        ty: base,
                        same_cat,
                        is_optional: in_opt,
                    });
                },
                TermParam::GuardBody { name } => {
                    out.push(PdaParam::Guard { name: name.clone() });
                },
                TermParam::Optional { params: inner } => {
                    collect(inner, category, true, out)?;
                },
                _ => return None,
            }
        }
        Some(())
    }
    let mut out = Vec::with_capacity(params.len());
    collect(params, category, false, &mut out)?;
    Some(out)
}

/// Would a CAPTURE rule's `Term` field recurse into the category that owns the rule?
///
/// ★ The discriminator behind the refusal in the capture branch of
/// [`generate_eval_method`]. It is a separate function so it can be tested in both
/// directions without standing up a whole `LanguageDef`; what the tests prove is that
/// the PREDICATE fires on a same-category base type and stays quiet otherwise. That the
/// emitter consults it is checked by the workspace build, which compiles every
/// `language!` in the tree — including the grammars whose generated output is not
/// present in `target/generated/` and which an artifact census therefore cannot see.
fn capture_term_field_is_same_category(ty: &TypeExpr, category: &syn::Ident) -> bool {
    matches!(ty, TypeExpr::Base(base) if base == category)
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

/// Per-field eval-arm parameter — one entry per generated variant field, in
/// declaration order (the recursive `eval`/`try_eval` match patterns
/// destructure ALL of them, so the entry count must equal the variant's
/// field arity).
enum EvalParam {
    /// A term-valued field: binds via `.eval()` (native categories) or
    /// `.as_ref()`/`.clone()` (non-native), Option-mapped when optional.
    Term {
        name: syn::Ident,
        use_eval: bool,
        is_optional: bool,
    },
    /// Task #14 (Option<Guard>): a `?g:Guard` predicate slot (top-level or
    /// inside `#opt(...)`). It occupies a constructor position — the match
    /// pattern MUST bind it (underscore-prefixed) or the arm's arity is
    /// wrong (E0023) — but it contributes no `let` binding: guards are
    /// opaque to evaluation and unreadable from user `![...]` code.
    Guard { name: syn::Ident },
}

/// Extract parameter entries: names AND whether each should bind via
/// `.eval()` (true) or `.clone()` (false). Categories without a native type
/// (collections, `Proc`, etc.) cannot be `.eval()`'d, so the cross-category
/// bindings have to clone — matching main's `term_context_params_with_eval`.
/// Guard slots yield [`EvalParam::Guard`] entries (previously they were
/// silently DROPPED, which desynchronized the match-pattern arity from the
/// variant's field count the moment a guard-bearing rule classified for the
/// PDA).
fn term_context_params_with_eval(
    term_context: &[TermParam],
    language: &LanguageDef,
) -> Vec<EvalParam> {
    let mut out = Vec::new();
    fn collect(
        params: &[TermParam],
        language: &LanguageDef,
        in_opt: bool,
        out: &mut Vec<EvalParam>,
    ) {
        for p in params {
            match p {
                TermParam::Simple { name, ty } => {
                    let use_eval = type_has_native_eval(ty, language);
                    out.push(EvalParam::Term {
                        name: name.clone(),
                        use_eval,
                        is_optional: in_opt,
                    });
                },
                TermParam::Abstraction { binder, body, .. } => {
                    out.push(EvalParam::Term {
                        name: binder.clone(),
                        use_eval: false,
                        is_optional: in_opt,
                    });
                    out.push(EvalParam::Term {
                        name: body.clone(),
                        use_eval: false,
                        is_optional: in_opt,
                    });
                },
                TermParam::MultiAbstraction { binder, body, .. } => {
                    out.push(EvalParam::Term {
                        name: binder.clone(),
                        use_eval: false,
                        is_optional: in_opt,
                    });
                    out.push(EvalParam::Term {
                        name: body.clone(),
                        use_eval: false,
                        is_optional: in_opt,
                    });
                },
                TermParam::GuardBody { name } => {
                    out.push(EvalParam::Guard { name: name.clone() });
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
/// - **Function call to a `try_*`-prefixed function**: e.g. a user fold body
///   `try_widen(&a, w)`. The `try_*` convention is the established Rust idiom
///   for fallible constructors (cf. `i32::try_from`, `String::try_into`,
///   `num_rational::Ratio::try_from_nd`).
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
        },
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
        },
        // `match scrutinee { Some(_) => ..., None => ... }` — check arms.
        Expr::Match(expr_match) => {
            expr_match
                .arms
                .iter()
                .any(|arm| rust_code_returns_option(&arm.body))
                || expr_match.arms.iter().all(|arm| {
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
        },
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

        // PDA literal arm. `n` is bound by reference, so the payload is cloned
        // out. `n.clone()` resolves to the payload type's `Clone` and is correct
        // for every native type — Copy primitives (compiled to a bitwise copy),
        // string/collection wrappers, and non-Copy structs (e.g. the
        // `Arc<…ZipperLit>` payloads of Rholang's ReadZipper/WriteZipper) alike.
        if !has_literal_rule {
            try_eval_arms.push(quote! {
                #category::#literal_label(n) => Some(n.clone()),
            });
            pda_visit_arms.push(quote! {
                #category::#literal_label(n) => values.push(n.clone()),
            });
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
        // remains unfolded instead of already being a literal variant.
        if is_collection_for_eval {
            // Keep only the literal and Var arms already pushed above.
        } else {
            for rule in &rules {
                let label = &rule.label;

                // Literal rule: copy or clone depending on nonterminal (StringLiteral => clone)
                if is_literal_rule(rule) {
                    let use_clone =
                        literal_rule_nonterminal(rule) == Some(NonTerminalKind::StringLiteral);
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
                // surfacing as the 7 `cross_cat_rholang_castop_*` failures.
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
                else if rule.is_auto_injected && classify_simple_projection_shape(rule).is_some()
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
                        // gate arm that mirrors the try_eval semantics.
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
                    // L9-3: a capture-bearing rule binds its capture `String`
                    // fields (and any interleaved simple params) in
                    // `capture_layout` order — captures bind as `&String`,
                    // directly usable in the `![...]` body (e.g. `w.len()`).
                    // Such rules are not PDA-eligible (a token's text is a leaf
                    // with no same-category recursion), so we emit only the
                    // recursive `match_arm` + `try_eval` arm and skip the PDA
                    // frame build below.
                    if let Some(layout) = capture_layout(
                        rule.term_context.as_deref().unwrap_or(&[]),
                        rule.syntax_pattern.as_deref().unwrap_or(&[]),
                    ) {
                        let rust_code = &rust_code_block.code;
                        let mut pats: Vec<TokenStream> = Vec::new();
                        let mut bindings: Vec<TokenStream> = Vec::new();
                        let mut try_bindings: Vec<TokenStream> = Vec::new();
                        for f in &layout.non_scope {
                            match &f.kind {
                                CaptureFieldKind::TokenText
                                | CaptureFieldKind::GuestBody { .. } => {
                                    // Opaque capture leaf (`&String` / `&Arc<FltNode>`)
                                    // — bound directly, usable in `![…]` (no eval).
                                    let name = format_ident!("{}", f.name);
                                    pats.push(quote! { #name });
                                },
                                CaptureFieldKind::Term(ty) => {
                                    let name = format_ident!("{}", f.name);
                                    pats.push(quote! { #name });
                                    // ★★ THE REFUSAL — the sibling of the `OptionalSameCat`
                                    // defect, made UNSPELLABLE instead of left to be found.
                                    //
                                    // The comment below this branch asserts *"A capture rule
                                    // is a LEAF value producer (its `String` fields are not
                                    // same-category children, so it needs no Reduce frame)"*.
                                    // That is true of its `String` fields and says nothing
                                    // about its `Term` fields, which this very arm binds
                                    // through `try_eval()?` — on the HOST STACK, in both the
                                    // recursive form and the PDA Visit arm, because the
                                    // branch `continue`s before any Reduce frame is built.
                                    // A capture rule with a same-category `Term` field would
                                    // therefore be Θ(depth) inside a "converted" driver, the
                                    // same shape `#opt(e:Int)` had.
                                    //
                                    // MEASURED: no grammar in the workspace instantiates it
                                    // (the census of all 54 generated `eval.rs` files finds
                                    // zero non-cast `try_eval()` sites in the two capture
                                    // languages, `l9flttoy` and `l9modaltoy`). So this is a
                                    // REFUSAL rather than a conversion: the shape has no
                                    // user, and a build failure naming the rule is a better
                                    // answer than emitting a silent recursion for the first
                                    // grammar that writes one.
                                    //
                                    // ⚠ The DISCRIMINATOR below is unit-tested for
                                    // non-vacuity by
                                    // `capture_term_field_same_category_discriminator_is_non_vacuous`
                                    // (this file, in `mod tests`). ★ Be precise about what
                                    // that test establishes: it proves the discriminator
                                    // ANSWERS CORRECTLY on both polarities. It does NOT
                                    // prove the emitter consults it — that is proven by the
                                    // workspace build, because a rule of this shape fails to
                                    // compile without the refusal.
                                    //
                                    // ⚠ This comment previously named
                                    // `capture_rule_with_same_category_term_field_is_refused`,
                                    // which does not exist and never did: a repo-wide search
                                    // returns exactly one hit — this line. A test name in a
                                    // comment is a claim about the suite that nothing checks,
                                    // so it is worth stating what the real test does and does
                                    // not cover rather than swapping one bare name for another.
                                    if capture_term_field_is_same_category(ty, category) {
                                        let msg = format!(
                                            "mettail: rule `{}::{}` is a CAPTURE rule (its \
                                             syntax pattern binds token text) and it also \
                                             takes a same-category term parameter `{}: {}`. \
                                             `try_eval` cannot be emitted stack-safely for \
                                             that shape: the capture branch produces a leaf \
                                             value with no Reduce frame, so the same-category \
                                             child would be evaluated by HOST RECURSION and a \
                                             term nested through `{}` would be Θ(depth) in \
                                             stack. Split the rule — put the same-category \
                                             child on a non-capture rule, which gets a work-\
                                             stack frame — or open a work item to give the \
                                             capture branch its own Reduce frame.",
                                            category, label, f.name, category, f.name,
                                        );
                                        return quote::quote_spanned!(
                                            label.span()=> compile_error!(#msg);
                                        );
                                    }
                                    if type_has_native_eval(ty, language) {
                                        bindings
                                            .push(quote! { let #name = #name.as_ref().eval(); });
                                        try_bindings.push(
                                            quote! { let #name = #name.as_ref().try_eval()?; },
                                        );
                                    } else {
                                        let b = quote! { let #name = #name.as_ref(); };
                                        bindings.push(b.clone());
                                        try_bindings.push(b);
                                    }
                                },
                                CaptureFieldKind::Predicate => {
                                    // Guards are opaque to eval — bind under an
                                    // underscore for arity, no `let`.
                                    let uname = format_ident!("_{}", f.name);
                                    pats.push(quote! { #uname });
                                },
                            }
                        }
                        if layout.scope.is_some() {
                            pats.push(quote! { _scope });
                        }
                        match_arms.push(quote! {
                            #category::#label(#(#pats),*) => {
                                #(#bindings)*
                                #rust_code
                            },
                        });
                        let rust_code_expr: syn::Expr = syn::parse_quote!({ #rust_code });
                        let safe_closure_call =
                            crate::gen::native::rust_code_rewrite::safeify_and_wrap(
                                &rust_code_expr,
                            );
                        try_eval_arms.push(quote! {
                            #category::#label(#(#pats),*) => {
                                #(#try_bindings)*
                                #safe_closure_call
                            },
                        });
                        // The PRODUCTION `try_eval` is the stack-safe PDA
                        // trampoline; the recursive arm above is only used when
                        // the category is not PDA-supported. A capture rule is a
                        // LEAF value producer (its `String` fields are not
                        // same-category children, so it needs no Reduce frame):
                        // its PDA Visit arm computes the value from the captures
                        // and pushes it, exactly like the literal arm
                        // (`Num::NumLit(n) => values.push(n)`).
                        pda_visit_arms.push(quote! {
                            #category::#label(#(#pats),*) => {
                                #(#try_bindings)*
                                match #safe_closure_call {
                                    ::std::option::Option::Some(__v) => values.push(__v),
                                    ::std::option::Option::None => return None,
                                }
                            }
                        });
                        continue;
                    }
                    // Resolve `(name, use_eval)` per param: native-typed categories
                    // bind via `.eval()`; collection / non-native categories bind
                    // via `.clone()` (cannot be `.eval()`'d).
                    let params_with_eval = rule
                        .term_context
                        .as_ref()
                        .map(|ctx| term_context_params_with_eval(ctx, language))
                        .unwrap_or_default();
                    let param_names: Vec<syn::Ident> = params_with_eval
                        .iter()
                        .map(|p| match p {
                            EvalParam::Term { name, .. } => name.clone(),
                            // Task #14 (Option<Guard>): underscore-prefixed
                            // binder — the pattern must cover the guard
                            // position (arity) without a usable binding.
                            EvalParam::Guard { name } => format_ident!("_{}", name),
                        })
                        .collect();
                    let param_count = param_names.len();
                    // Opt-Group: when `is_optional`, the variant field is
                    // `Option<Box<Cat>>` (not `Box<Cat>`). The user's eval
                    // code expects the param bound to `Option<NativeT>`
                    // (when use_eval) or `Option<&Cat>` (when !use_eval).
                    // Map each binding accordingly.
                    let param_bindings: Vec<_> = params_with_eval
                    .iter()
                    .map(|p| {
                        let (name, use_eval, is_optional) = match p {
                            EvalParam::Term { name, use_eval, is_optional } => {
                                (name, use_eval, is_optional)
                            },
                            // Guards get NO `let` binding — opaque to eval.
                            EvalParam::Guard { .. } => return quote! {},
                        };
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
                        .map(|p| {
                            let (name, use_eval, is_optional) = match p {
                                EvalParam::Term { name, use_eval, is_optional } => {
                                    (name, use_eval, is_optional)
                                },
                                // Guards get NO `let` binding — opaque to eval.
                                EvalParam::Guard { .. } => return quote! {},
                            };
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
                                let __mettail_eval_option = #rust_code;
                                __mettail_eval_option.expect(
                                    "evaluation reached unreachable Option::None sentinel; \
                                     user grammar must normalize via rewrite rules \
                                     (e.g., (cast_op a) ~> cast_error) before eval()",
                                )
                            },
                        }
                    } else if param_count == 0 {
                        quote! {
                            #category::#label => #rust_code,
                        }
                    } else {
                        quote! {
                            #category::#label(#(#param_names),*) => {
                                #(#param_bindings)*
                                #rust_code
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
                    let safe_closure_call =
                        crate::gen::native::rust_code_rewrite::safeify_and_wrap(&rust_code_expr);
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
                                // `Option::clone()` (Borrow).
                                //
                                // ★★ `OptionalSameCat` — #189-residual, THE ONE PLACE THE
                                // WORK STACK WAS STILL ESCAPED, and it is the #162 lesson
                                // repeating one level down: *a work-stack driver can only
                                // replace recursion for work its TASK ENUM can represent.*
                                //
                                // This arm used to read: *"Optional same-cat children are
                                // routed through cross_kinds (not the same-cat Visit-push
                                // path) because the `Some(_)`/`None` branching doesn't fit
                                // the unconditional Visit-frame push."* The premise is
                                // true — the push IS unconditional — and the conclusion
                                // does not follow. What the branching does not fit is the
                                // FRAME, which had no way to say "the child was absent";
                                // routing the child to `try_eval()?` instead just moved
                                // the descent onto the host stack, where a chain nested
                                // through the optional position is Θ(depth).
                                //
                                // MEASURED over the artifact: the workspace's 54 generated
                                // `eval.rs` files contain exactly ONE instance —
                                // `optsmoke::Int::IfElse`'s `#opt(e:Int)`, whose `t` branch
                                // went on the work stack and whose `e` branch did not. It
                                // is the ONLY same-category host recursion in any
                                // generated `try_eval` anywhere.
                                //
                                // The repair is to give the frame the missing word: the
                                // field becomes a PRESENCE FLAG (`bool`), the child is
                                // Visit-pushed when present, and the Reduce arm rebuilds
                                // the `Option<NativeT>` the user's `![…]` body expects by
                                // popping conditionally. A same-category optional child is
                                // always `Native` here, because `generate_eval_method`
                                // returns early for a category with no `native_type`.
                                enum CrossKind {
                                    Native(TokenStream),
                                    Borrow(TokenStream),
                                    OptionalNative(TokenStream),
                                    OptionalBorrow(TokenStream),
                                    OptionalSameCat,
                                }
                                let mut cross_kinds: Vec<(syn::Ident, CrossKind)> = Vec::new();
                                for entry in &classified {
                                    let (name, ty_id, same, is_optional) = match entry {
                                        PdaParam::Term { name, ty, same_cat, is_optional } => {
                                            (name, ty, same_cat, is_optional)
                                        },
                                        // Task #14 (Option<Guard>): guards are
                                        // never captured into the Reduce frame.
                                        PdaParam::Guard { .. } => continue,
                                    };
                                    if *same && !*is_optional {
                                        continue;
                                    }
                                    // ★ The same-category OPTIONAL child: no storage type,
                                    // because nothing is stored — the frame carries a
                                    // presence flag and the value comes off the value
                                    // stack, exactly as the non-optional same-cat child's
                                    // does. See `CrossKind::OptionalSameCat`.
                                    if *same {
                                        cross_kinds
                                            .push((name.clone(), CrossKind::OptionalSameCat));
                                        continue;
                                    }
                                    let target_native = language
                                        .types
                                        .iter()
                                        .find(|t| t.name == **ty_id)
                                        .and_then(|t| t.native_type.as_ref());
                                    let storage_ty: TokenStream = match target_native {
                                        Some(nt) => match NativeType::from_syn_type(nt) {
                                            NativeType::Str => quote! { std::string::String },
                                            NativeType::Float32 => {
                                                quote! { ::mettail_runtime::CanonicalFloat32 }
                                            },
                                            NativeType::Float64 => {
                                                quote! { ::mettail_runtime::CanonicalFloat64 }
                                            },
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
                                        },
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
                                        },
                                        CrossKind::OptionalNative(ty)
                                        | CrossKind::OptionalBorrow(ty) => {
                                            quote! { #n: ::std::option::Option<#ty> }
                                        },
                                        // ★ The presence flag — the word the frame was
                                        // missing. See `CrossKind::OptionalSameCat`.
                                        CrossKind::OptionalSameCat => quote! { #n: bool },
                                    })
                                    .collect();
                                let cross_field_names: Vec<syn::Ident> =
                                    cross_kinds.iter().map(|(n, _)| n.clone()).collect();
                                // ★ Field INITIALISERS, not just names. Every other kind
                                // binds a local already named after its field and uses
                                // struct-init shorthand; `OptionalSameCat` has no local to
                                // shorthand from — its field is computed from the still-
                                // unshadowed `Option<Arc<Cat>>` binder at the push site,
                                // because the same binder is needed one line later by the
                                // conditional Visit push.
                                let cross_field_inits: Vec<TokenStream> = cross_kinds
                                    .iter()
                                    .map(|(n, k)| match k {
                                        CrossKind::OptionalSameCat => {
                                            quote! { #n: #n.is_some() }
                                        },
                                        _ => quote! { #n },
                                    })
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
                                    .map(|entry| match entry {
                                        PdaParam::Term { name, .. } => quote! { #name },
                                        // Task #14 (Option<Guard>): the guard
                                        // position must be covered for arity;
                                        // underscore-prefixed = never read.
                                        PdaParam::Guard { name } => {
                                            let silent = format_ident!("_{}", name);
                                            quote! { #silent }
                                        },
                                    })
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
                                    // ★ NOTHING is evaluated eagerly for a same-category
                                    // optional child — that eager `try_eval()?` WAS the
                                    // defect. It must also not shadow `#n`, which the
                                    // conditional Visit push below still needs.
                                    CrossKind::OptionalSameCat => quote! {},
                                })
                                .collect();
                                let reduce_push = if cross_field_names.is_empty() {
                                    quote! { work.push(__EvalFrame::#reduce_variant); }
                                } else {
                                    quote! {
                                        work.push(__EvalFrame::#reduce_variant {
                                            #(#cross_field_inits),*
                                        });
                                    }
                                };
                                // Same-category children: push in REVERSE so the left-
                                // most child is processed first (LIFO stack), which is
                                // what makes the value stack read in declaration order
                                // and the reverse-order pops below correct.
                                //
                                // ★ Optional same-category children go through THIS path
                                // now, conditionally. The interleaving still works: an
                                // absent child pushes no Visit and its Reduce pop is
                                // likewise skipped (the frame's presence flag decides
                                // both), so the two sequences stay in lockstep whatever
                                // the mix of present and absent children is.
                                let same_cat_pushes: Vec<TokenStream> = classified
                                    .iter()
                                    .rev()
                                    .filter_map(|entry| match entry {
                                        // Task #14 (Option<Guard>): Term-only —
                                        // guards are never Visit-pushed.
                                        PdaParam::Term {
                                            name,
                                            same_cat: true,
                                            is_optional: false,
                                            ..
                                        } => Some(quote! {
                                            work.push(__EvalFrame::Visit(#name.as_ref()));
                                        }),
                                        PdaParam::Term {
                                            name,
                                            same_cat: true,
                                            is_optional: true,
                                            ..
                                        } => Some(quote! {
                                            if let ::std::option::Option::Some(__opt_child) =
                                                #name.as_ref()
                                            {
                                                work.push(
                                                    __EvalFrame::Visit(__opt_child.as_ref()),
                                                );
                                            }
                                        }),
                                        _ => None,
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
                                // ★ Optional same-cat children ARE popped now, conditionally
                                // — the mirror image of the conditional Visit push above.
                                // The `bool` destructured out of the frame is shadowed by
                                // the `Option<NativeT>` the user's `![…]` body expects, so
                                // the body sees exactly what the recursive form gave it.
                                let pops: Vec<TokenStream> = classified
                                    .iter()
                                    .rev()
                                    .filter_map(|entry| match entry {
                                        // Task #14 (Option<Guard>): Term-only —
                                        // guards were never pushed, so they are
                                        // never popped.
                                        PdaParam::Term {
                                            name,
                                            same_cat: true,
                                            is_optional: false,
                                            ..
                                        } => Some(quote! {
                                            // Pops are in reverse param order; since we
                                            // push in reverse earlier (so leftmost is
                                            // visited first = processed first = pushed to
                                            // value stack first), popping in reverse gives
                                            // us rightmost-first which matches the name
                                            // binding order below.
                                            let #name = values.pop().expect("PDA same-cat value");
                                        }),
                                        PdaParam::Term {
                                            name,
                                            same_cat: true,
                                            is_optional: true,
                                            ..
                                        } => Some(quote! {
                                            let #name = match #name {
                                                true => ::std::option::Option::Some(
                                                    values
                                                        .pop()
                                                        .expect("PDA optional same-cat value"),
                                                ),
                                                false => ::std::option::Option::None,
                                            };
                                        }),
                                        _ => None,
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
                                    // Already rebuilt by its `pops` entry.
                                    CrossKind::OptionalSameCat => None,
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
                            },
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
                            },
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
                            GrammarItem::NonTerminal { ident, kind } => {
                                Some((ident.to_string(), *kind))
                            },
                            _ => None,
                        })
                        .collect();

                    // Check if this has Var and a recursive reference
                    let has_var = non_terminals
                        .iter()
                        .any(|(_, kind)| *kind == NonTerminalKind::Var);
                    let has_recursive = non_terminals
                        .iter()
                        .any(|(name, _)| *name == category.to_string());

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
            let return_type = if matches!(
                lang_type.collection_kind,
                Some(mettail_ast::language::CollectionCategory::Pathmap(_))
            ) {
                // A pathmap's literal payload is homogeneous `PathMapLit<E,E>`;
                // its set/map mode records whether values exist.
                let elem =
                    pathmap_element_type(native_type).unwrap_or_else(|| quote! { #native_type });
                quote! {
                    mettail_runtime::PathMapLit<#elem, #elem>
                }
            } else {
                match nt {
                    NativeType::Str => quote! { std::string::String },
                    NativeType::Float32 => quote! { mettail_runtime::CanonicalFloat32 },
                    NativeType::Float64 => quote! { mettail_runtime::CanonicalFloat64 },
                    _ => quote! { #native_type },
                }
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
                // ── NO `std::ops::{Add,Sub,Mul,Div,Rem}` IMPLS ARE EMITTED ──────────────
                //
                // Until 2026-07-25 this block emitted `impl std::ops::Add for #category`
                // (and the four siblings) whose body was
                //
                //     <Self as SafeArith>::safe_add(self, rhs)
                //         .unwrap_or_else(|| #category::#literal_label(Default::default()))
                //
                // i.e. a *checked* operation whose failure path FABRICATED the category's
                // `Default` value. Measured consequences in Rholang (whose `Add`/`Div`/`Mod`
                // fold bodies are object-output, hence NOT routed through
                // `rust_code_rewrite::safeify`, hence reaching these impls):
                //
                //   `int(i64::MAX, 64) + int(1, 64)`  folded to  `0`   (overflow)
                //   `int(1, 64) / int(0, 64)`         folded to  `0`   (division by zero)
                //   `1e308f64 * 1e308f64` → Inf, and `Inf - Inf` → NaN → `0.0`
                //
                // A silent wrong VALUE is strictly worse than a stuck term or an error term:
                // it is indistinguishable from a correct answer downstream.
                //
                // The operator signature `fn add(self, rhs: Self) -> Self` cannot report
                // failure — for a category over `i64` there is no `Int` value that means
                // "not representable". Three dispositions were considered:
                //
                //   * panic — rejected: a panic raised inside a Dovetail fold body cannot be
                //     contained in this workspace (unwinding across the Cranelift-compiled
                //     frames of `[profile.dev] codegen-backend = "cranelift"` dies with
                //     `fatal runtime error: failed to initiate panic, error 5, aborting`,
                //     documented in `rholang-runtime/tests/rho_rholang_conformance.rs`
                //     divergence C). A process abort is worse than a wrong value.
                //   * `type Output = Option<Self>` — rejected: it leaves TWO spellings of the
                //     same fallible operation (`a + b` and `SafeArith::safe_add(a, b)`), and
                //     `safeify` already rewrites every in-body `+` to the latter, so the
                //     operator spelling would be dead syntax that only invites the mistake.
                //   * NOT EMITTING THE OPERATOR — chosen. Fabrication becomes unrepresentable
                //     because the fabricating operation no longer exists: `a + b` on a
                //     category value is a COMPILE error, and every call site must consume the
                //     `Result` returned by the `SafeArith` impl below and map its `Err` onto
                //     the language's own failure disposition (for Rholang: `Proc::Err`, the
                //     `error` term — see `languages/src/rholang.rs` `Add`/`Sub`/`Mul`/`Div`/
                //     `Mod`, whose `UInt32`/`BigInt`/`BigRat`/`Fixed` arms already answered
                //     `Proc::Err` on ÷0 before this change; the `Int`/`Float` arms were the
                //     only fabricating ones).
                //
                // The `SafeArith` impl immediately below is therefore the SOLE arithmetic
                // surface on a category value, and its `Err(Partiality)` is its sole failure
                // report: "blocked by semantic predicate / defer to the machine", the same
                // meaning it carries in `macros/src/gen/runtime/rho_dataflow.rs`'s
                // `RhoFoldDataflowPredicateBlock::SafeEvaluationDeclined` gate — except that
                // it now NAMES which partiality occurred.

                // `SafeArith` for the category wrapper: delegates to `try_eval` to
                // get the underlying native value, then delegates to the native
                // `SafeArith` impl, and re-wraps the result as a literal. This is
                // what the `rust_code_rewrite` pass emits when a user's `![...]`
                // block contains `a + b` where `a` / `b` are typed as the category
                // (e.g., rholang's `Proc::CastInt(Box::new(*a.clone() + *b.clone()))`
                // with `a, b: &Box<Int>` — after `*a.clone()` they are `Int`).
                //
                // ★ The two failure sources are reported DIFFERENTLY, and the difference is
                // the whole partition:
                //
                //   * an operand that will not `try_eval` is STRUCTURAL — a Var-bearing or
                //     unreduced child — so it becomes `Partiality::NotReduced` and DEFERS,
                //     recording nothing;
                //   * the arithmetic's own decline is SEMANTIC and carries the native impl's
                //     reason (`DivisionByZero`, `NotRepresentable{carrier}`, …) unchanged.
                let safe_arith_impl = quote! {
                    impl ::mettail_runtime::SafeArith for #category {
                        type Output = Self;
                        fn safe_add(self, rhs: Self) -> ::core::result::Result<Self, ::mettail_runtime::Partiality> {
                            let a = ::mettail_runtime::partiality::not_reduced(self.try_eval())?;
                            let b = ::mettail_runtime::partiality::not_reduced(rhs.try_eval())?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_add(a, b)?;
                            ::core::result::Result::Ok(#category::#literal_label(r))
                        }
                        fn safe_sub(self, rhs: Self) -> ::core::result::Result<Self, ::mettail_runtime::Partiality> {
                            let a = ::mettail_runtime::partiality::not_reduced(self.try_eval())?;
                            let b = ::mettail_runtime::partiality::not_reduced(rhs.try_eval())?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_sub(a, b)?;
                            ::core::result::Result::Ok(#category::#literal_label(r))
                        }
                        fn safe_mul(self, rhs: Self) -> ::core::result::Result<Self, ::mettail_runtime::Partiality> {
                            let a = ::mettail_runtime::partiality::not_reduced(self.try_eval())?;
                            let b = ::mettail_runtime::partiality::not_reduced(rhs.try_eval())?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_mul(a, b)?;
                            ::core::result::Result::Ok(#category::#literal_label(r))
                        }
                        fn safe_div(self, rhs: Self) -> ::core::result::Result<Self, ::mettail_runtime::Partiality> {
                            let a = ::mettail_runtime::partiality::not_reduced(self.try_eval())?;
                            let b = ::mettail_runtime::partiality::not_reduced(rhs.try_eval())?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_div(a, b)?;
                            ::core::result::Result::Ok(#category::#literal_label(r))
                        }
                        fn safe_rem(self, rhs: Self) -> ::core::result::Result<Self, ::mettail_runtime::Partiality> {
                            let a = ::mettail_runtime::partiality::not_reduced(self.try_eval())?;
                            let b = ::mettail_runtime::partiality::not_reduced(rhs.try_eval())?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_rem(a, b)?;
                            ::core::result::Result::Ok(#category::#literal_label(r))
                        }
                        fn safe_neg(self) -> ::core::result::Result<Self, ::mettail_runtime::Partiality> {
                            let a = ::mettail_runtime::partiality::not_reduced(self.try_eval())?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_neg(a)?;
                            ::core::result::Result::Ok(#category::#literal_label(r))
                        }
                        fn safe_not(self) -> ::core::result::Result<Self, ::mettail_runtime::Partiality> {
                            let a = ::mettail_runtime::partiality::not_reduced(self.try_eval())?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_not(a)?;
                            ::core::result::Result::Ok(#category::#literal_label(r))
                        }
                        fn safe_pow(self, exp: i32) -> ::core::result::Result<Self, ::mettail_runtime::Partiality> {
                            let a = ::mettail_runtime::partiality::not_reduced(self.try_eval())?;
                            let r = <_ as ::mettail_runtime::SafeArith>::safe_pow(a, exp)?;
                            ::core::result::Result::Ok(#category::#literal_label(r))
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

#[cfg(test)]
mod tests {
    use super::*;
    use quote::format_ident;

    fn simple(name: &str, cat: &str) -> TermParam {
        TermParam::Simple {
            name: format_ident!("{}", name),
            ty: TypeExpr::Base(format_ident!("{}", cat)),
        }
    }

    /// ★ Non-vacuity for the capture-rule refusal, in BOTH directions.
    ///
    /// ⚠ What this proves and what it does not, stated so the next reader does not
    /// over-read it: it proves the DISCRIMINATOR answers correctly. It does not prove
    /// the emitter consults it — that is proven by the workspace build, which expands
    /// every `language!` in the tree. The distinction matters here because the
    /// evidence that no grammar instantiates the shape came from a census of
    /// `target/generated/`, which holds 54 languages while the source declares more:
    /// an artifact census cannot see a grammar that was not compiled into it.
    #[test]
    fn capture_term_field_same_category_discriminator_is_non_vacuous() {
        let category = format_ident!("Int");
        assert!(
            capture_term_field_is_same_category(&TypeExpr::Base(format_ident!("Int")), &category),
            "a capture rule's `Term(Int)` field inside category `Int` IS the \
             same-category recursion the refusal exists for"
        );
        assert!(
            !capture_term_field_is_same_category(&TypeExpr::Base(format_ident!("Bool")), &category),
            "a capture rule's `Term(Bool)` field inside category `Int` is a CROSS-category \
             hop, bounded by the cast lattice's height — refusing it would be wrong"
        );
    }

    #[test]
    fn classify_guard_free_rule_unchanged() {
        // Task #14 gate-1: the tuple→enum refactor must classify guard-free
        // rules exactly as before — same entry count, same (name, ty,
        // same_cat, is_optional) content, in declaration order. (The
        // emitted-token byte-identity across the 22 default languages is
        // enforced by probe P5's sha compare.)
        let category = format_ident!("Int");
        let ctx = vec![simple("a", "Int"), simple("b", "Proc")];
        let classified = classify_term_params_for_pda(&ctx, &category)
            .expect("guard-free Simple/Base params must classify");
        assert_eq!(classified.len(), 2);
        match &classified[0] {
            PdaParam::Term { name, ty, same_cat, is_optional } => {
                assert_eq!(name.to_string(), "a");
                assert_eq!(ty.to_string(), "Int");
                assert!(*same_cat);
                assert!(!*is_optional);
            },
            PdaParam::Guard { .. } => panic!("`a:Int` must classify as Term"),
        }
        match &classified[1] {
            PdaParam::Term { name, ty, same_cat, is_optional } => {
                assert_eq!(name.to_string(), "b");
                assert_eq!(ty.to_string(), "Proc");
                assert!(!*same_cat);
                assert!(!*is_optional);
            },
            PdaParam::Guard { .. } => panic!("`b:Proc` must classify as Term"),
        }
    }

    #[test]
    fn classify_optional_guard_yields_guard_entry() {
        // The guardoptsmoke PCheck shape: `k:Int, *opt(?g:Guard)`.
        // Pre-#14 this returned None → compile_error!.
        let category = format_ident!("Int");
        let ctx = vec![
            simple("k", "Int"),
            TermParam::Optional {
                params: vec![TermParam::GuardBody { name: format_ident!("g") }],
            },
        ];
        let classified = classify_term_params_for_pda(&ctx, &category)
            .expect("Optional{GuardBody} must classify for the PDA");
        assert_eq!(classified.len(), 2, "one Term + one Guard entry");
        assert!(
            matches!(&classified[0], PdaParam::Term { same_cat: true, is_optional: false, .. }),
            "`k:Int` stays a mandatory same-cat Term",
        );
        assert!(
            matches!(&classified[1], PdaParam::Guard { name } if name == "g"),
            "`?g:Guard` inside #opt must classify as Guard",
        );
    }

    #[test]
    fn classify_top_level_guard_yields_guard_entry() {
        let category = format_ident!("Proc");
        let ctx = vec![simple("p", "Proc"), TermParam::GuardBody { name: format_ident!("guard") }];
        let classified = classify_term_params_for_pda(&ctx, &category)
            .expect("top-level GuardBody must classify for the PDA");
        assert!(matches!(&classified[1], PdaParam::Guard { name } if name == "guard"));
    }

    #[test]
    fn classify_abstraction_still_aborts() {
        // Non-Simple/non-Guard params must still return None (the caller
        // turns that into compile_error! — no silent recursive fallback).
        let category = format_ident!("Proc");
        let ctx = vec![TermParam::Abstraction {
            binder: format_ident!("x"),
            body: format_ident!("p"),
            ty: TypeExpr::Base(format_ident!("Proc")),
        }];
        assert!(classify_term_params_for_pda(&ctx, &category).is_none());
    }

    #[test]
    fn eval_params_count_guard_positions() {
        // Task #14 gate-1 (the MASKED layer): `term_context_params_with_eval`
        // must yield one entry per variant field INCLUDING guards, so the
        // recursive/try_eval match patterns cover the guard position (the
        // pre-#14 drop desynchronized arity → E0023 once classify passed).
        let language = crate::gen::empty_language_for_tests();
        let ctx = vec![
            simple("k", "Int"),
            TermParam::Optional {
                params: vec![TermParam::GuardBody { name: format_ident!("g") }],
            },
        ];
        let params = term_context_params_with_eval(&ctx, &language);
        assert_eq!(params.len(), 2, "guard positions must be counted");
        match &params[0] {
            EvalParam::Term { name, is_optional, .. } => {
                assert_eq!(name.to_string(), "k");
                assert!(!*is_optional);
            },
            EvalParam::Guard { .. } => panic!("`k:Int` must be a Term entry"),
        }
        assert!(
            matches!(&params[1], EvalParam::Guard { name } if name == "g"),
            "the guard slot must be an EvalParam::Guard entry",
        );
    }
}
