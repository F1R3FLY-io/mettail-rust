use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::gen::capture::{capture_layout, CaptureFieldKind};
use crate::gen::native::lossless_coercion::build_lossless_coercion;
use crate::gen::native::{native_type_to_string, NativeType};
use crate::gen::runtime::wpda_codegen::builtin_metadata::classify_simple_projection_shape;
use crate::gen::term_param_walk::TermParamLeaves;
use crate::gen::{
    generate_literal_label, generate_var_label, is_literal_rule, literal_rule_nonterminal,
};
/// Generate eval() method for native types
use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind, TermParam};
use mettail_ast::language::{LangType, LanguageDef, NativeKind};
use mettail_ast::types::TypeExpr;
use std::collections::HashMap;

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

/// The concrete value carried by a native category's evaluator result.
///
/// This is deliberately derived once and reused by both the heterogeneous
/// evaluator value enum and the public `try_eval` method.  Before the shared
/// evaluator PDA, each category recomputed the type inside its private work
/// loop; keeping two copies would make a PathMap category especially easy to
/// mis-model as its declared wrapper rather than its homogeneous literal.
fn eval_return_type(lang_type: &LangType) -> TokenStream {
    let native_type = lang_type
        .native_type
        .as_ref()
        .expect("eval_return_type is called only for native categories");
    if matches!(
        lang_type.collection_kind,
        Some(mettail_ast::language::CollectionCategory::Pathmap(_))
    ) {
        let elem = pathmap_element_type(native_type).unwrap_or_else(|| quote! { #native_type });
        return quote! { mettail_runtime::PathMapLit<#elem, #elem> };
    }

    match NativeType::from_syn_type(native_type) {
        NativeType::Str => quote! { std::string::String },
        NativeType::Float32 => quote! { mettail_runtime::CanonicalFloat32 },
        NativeType::Float64 => quote! { mettail_runtime::CanonicalFloat64 },
        _ => quote! { #native_type },
    }
}

/// Iterative Kosaraju decomposition.  The graph is the generated evaluator's
/// category-dependency graph, so its SCCs are exactly the category sets that
/// can rebuild unbounded host recursion by alternating constructors.
///
/// The implementation itself is iterative: a large user language must not
/// move the stack-safety defect from generated runtime code into macro
/// expansion.
fn strongly_connected_components(edges: &[Vec<usize>]) -> (Vec<usize>, Vec<Vec<usize>>) {
    let mut seen = vec![false; edges.len()];
    let mut finish = Vec::with_capacity(edges.len());
    for root in 0..edges.len() {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut work = vec![(root, 0usize)];
        while let Some((node, next)) = work.pop() {
            if let Some(&child) = edges[node].get(next) {
                work.push((node, next + 1));
                if !seen[child] {
                    seen[child] = true;
                    work.push((child, 0));
                }
            } else {
                finish.push(node);
            }
        }
    }

    let mut reverse = vec![Vec::new(); edges.len()];
    for (source, targets) in edges.iter().enumerate() {
        for &target in targets {
            reverse[target].push(source);
        }
    }

    let mut raw_components = Vec::new();
    let mut assigned = vec![false; edges.len()];
    while let Some(root) = finish.pop() {
        if assigned[root] {
            continue;
        }
        assigned[root] = true;
        let mut component = Vec::new();
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            component.push(node);
            for &parent in &reverse[node] {
                if !assigned[parent] {
                    assigned[parent] = true;
                    work.push(parent);
                }
            }
        }
        component.sort_unstable();
        raw_components.push(component);
    }
    raw_components.sort_by_key(|component| component[0]);

    let mut component_of = vec![usize::MAX; edges.len()];
    for (component_id, component) in raw_components.iter().enumerate() {
        for &node in component {
            component_of[node] = component_id;
        }
    }
    (component_of, raw_components)
}

fn collect_native_dependencies(
    params: &[TermParam],
    native_index: &HashMap<String, usize>,
    out: &mut Vec<usize>,
) {
    for leaf in TermParamLeaves::new(params, false) {
        match leaf.param {
            TermParam::Simple { ty: TypeExpr::Base(target), .. } => {
                if let Some(&index) = native_index.get(&target.to_string()) {
                    out.push(index);
                }
            },
            _ => {},
        }
    }
}

/// Derive one component id per native category, in `language.types` native-only
/// order.  Duplicate edges are removed so generated shape and macro work are
/// stable under repeated term parameters.
fn evaluator_component_ids(language: &LanguageDef) -> (Vec<usize>, Vec<Vec<usize>>) {
    let native_names: Vec<String> = language
        .types
        .iter()
        .filter(|lang_type| lang_type.native_type.is_some())
        .map(|lang_type| lang_type.name.to_string())
        .collect();
    let native_index: HashMap<String, usize> = native_names
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), index))
        .collect();
    let mut edges = vec![Vec::new(); native_names.len()];
    for rule in &language.terms {
        let Some(&source) = native_index.get(&rule.category.to_string()) else {
            continue;
        };
        if let Some(params) = rule.term_context.as_deref() {
            collect_native_dependencies(params, &native_index, &mut edges[source]);
        }
    }
    for targets in &mut edges {
        targets.sort_unstable();
        targets.dedup();
    }
    strongly_connected_components(&edges)
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
fn classify_hol_rule_for_pda(rule: &GrammarRule) -> Option<Vec<PdaParam<'_>>> {
    // Zero-ary rules (no term_context) are PDA-compatible: they have no
    // children to recurse into. Returning `Some(Vec::new())` rather than
    // `None` is the critical difference: `None` aborts the WHOLE category
    // via compile_error!, while an empty vec just means this particular
    // rule has no same-cat children.
    let Some(ctx) = rule.term_context.as_ref() else {
        return Some(Vec::new());
    };
    classify_term_params_for_pda(ctx)
}

/// The leaf-classification body of [`classify_hol_rule_for_pda`], hoisted so
/// unit tests can exercise the classification over a bare `&[TermParam]`.
///
/// Opt-Group: a `TermParam::Optional` with inner Simple/Base params is
/// PDA-compatible — each inner becomes a [`PdaParam::Term`] with
/// `is_optional: true`. A `TermParam::GuardBody` (top-level or
/// Optional-nested) becomes [`PdaParam::Guard`]. Inner non-Simple/non-Base
/// params abort classification.
fn classify_term_params_for_pda(params: &[TermParam]) -> Option<Vec<PdaParam<'_>>> {
    let mut out = Vec::with_capacity(params.len());
    for leaf in TermParamLeaves::new(params, false) {
        match leaf.param {
            TermParam::Simple { name, ty } => {
                let TypeExpr::Base(base) = ty else {
                    return None;
                };
                out.push(PdaParam::Term {
                    name: name.clone(),
                    ty: base,
                    is_optional: leaf.is_optional,
                });
            },
            TermParam::GuardBody { name } => {
                out.push(PdaParam::Guard { name: name.clone() });
            },
            TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. } => return None,
            TermParam::Optional { .. } => unreachable!("TermParamLeaves omits grouping nodes"),
        }
    }
    Some(out)
}

pub fn generate_eval_method(language: &LanguageDef) -> TokenStream {
    let mut impls = Vec::new();

    // One compact machine per dependency SCC.  A category-local `Vec<Frame>`
    // cannot represent `Int -> Bool -> Int`, while one language-wide mega-enum
    // makes rustc pay for every unrelated category in every match.  SCCs are
    // the exact middle ground: every potentially unbounded category cycle is
    // one heterogeneous PDA, and condensation-DAG edges remain bounded calls.
    let native_categories: Vec<&LangType> = language
        .types
        .iter()
        .filter(|lang_type| lang_type.native_type.is_some())
        .collect();
    if native_categories.is_empty() {
        return TokenStream::new();
    }
    let (component_of, components) = evaluator_component_ids(language);
    debug_assert_eq!(component_of.len(), native_categories.len());

    struct ComponentMachine {
        frame: syn::Ident,
        value: syn::Ident,
        function: syn::Ident,
        visit_variants: Vec<TokenStream>,
        value_variants: Vec<TokenStream>,
        frame_variants: Vec<TokenStream>,
        arms: Vec<TokenStream>,
    }
    let mut machines: Vec<ComponentMachine> = components
        .iter()
        .enumerate()
        .map(|(component, _)| ComponentMachine {
            frame: format_ident!("__EvalFrameC{}", component),
            value: format_ident!("__EvalValueC{}", component),
            function: format_ident!("__mettail_try_eval_c{}", component),
            visit_variants: Vec::new(),
            value_variants: Vec::new(),
            frame_variants: Vec::new(),
            arms: Vec::new(),
        })
        .collect();
    let mut native_component = HashMap::new();
    for (native_index, lang_type) in native_categories.iter().enumerate() {
        let component = component_of[native_index];
        native_component.insert(lang_type.name.to_string(), component);
        let category = &lang_type.name;
        let visit = format_ident!("Visit{}", category);
        let value = format_ident!("{}", category);
        let return_type = eval_return_type(lang_type);
        machines[component]
            .visit_variants
            .push(quote! { #visit(&'a #category), });
        machines[component]
            .value_variants
            .push(quote! { #value(#return_type), });
    }

    for lang_type in &language.types {
        let category = &lang_type.name;

        // Only generate for native types
        let native_type = match lang_type.native_type.as_ref() {
            Some(ty) => ty,
            None => continue,
        };
        let return_type = eval_return_type(lang_type);
        let visit_variant = format_ident!("Visit{}", category);
        let value_variant = format_ident!("{}", category);
        let component = native_component[&category.to_string()];
        let component_is_singleton = components[component].len() == 1;
        let frame_type = machines[component].frame.clone();
        let value_type = machines[component].value.clone();
        let machine_function = machines[component].function.clone();

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

        let var_label = generate_var_label(category);

        // ─── PDA work-stack state ──────────────────────────────────────────
        // Every evaluable constructor gets a Visit/Reduce interpretation. There
        // is deliberately no recursive fallback: an unclassifiable rule is a
        // macro error rather than a latent input-depth-dependent stack path.
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
            pda_visit_arms.push(quote! {
                #category::#literal_label(n) => {
                    values.push(#value_type::#value_variant(n.clone()))
                },
            });
        }
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
                        pda_visit_arms.push(quote! {
                            #category::#label(n) => {
                                values.push(#value_type::#value_variant(n.clone()))
                            },
                        });
                    } else {
                        pda_visit_arms.push(quote! {
                            #category::#label(n) => {
                                values.push(#value_type::#value_variant(*n))
                            },
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
                // lossless) emit a PDA projection step.
                else if rule.is_auto_injected && classify_simple_projection_shape(rule).is_some()
                {
                    let shape = classify_simple_projection_shape(rule)
                        .expect("just checked classify_simple_projection_shape");
                    let source_type = language
                        .types
                        .iter()
                        .find(|t| t.name.to_string() == shape.source_category);
                    let source_native_kind = source_type
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
                        let source_category = source_type
                            .map(|t| t.name.clone())
                            .expect("a coercible projection source is a declared native category");
                        let source_visit = format_ident!("Visit{}", source_category);
                        let source_value = format_ident!("{}", source_category);
                        let reduce_variant = format_ident!("Reduce{}{}Projection", category, label);
                        let source_component = native_component[&source_category.to_string()];
                        if source_component == component {
                            pda_frame_variants.push(quote! { #reduce_variant, });
                            pda_visit_arms.push(quote! {
                                #category::#label(__v_box) => {
                                    work.push(#frame_type::#reduce_variant);
                                    work.push(#frame_type::#source_visit(__v_box.as_ref()));
                                }
                            });
                            pda_reduce_arms.push(quote! {
                                #frame_type::#reduce_variant => {
                                    let #v_ident = match values.pop() {
                                        ::std::option::Option::Some(
                                            #value_type::#source_value(__value)
                                        ) => __value,
                                        _ => unreachable!(
                                            "evaluator PDA projection value/category mismatch"
                                        ),
                                    };
                                    values.push(#value_type::#value_variant(#coercion_expr));
                                }
                            });
                        } else {
                            // A condensation-DAG edge cannot participate in a
                            // category cycle, so one bounded call keeps both SCC
                            // alphabets compact.
                            pda_visit_arms.push(quote! {
                                #category::#label(__v_box) => {
                                    let #v_ident = __v_box.as_ref().try_eval()?;
                                    values.push(#value_type::#value_variant(#coercion_expr));
                                }
                            });
                        }
                    }
                }
                // HOL syntax: rule with Rust code block - generate eval from rust_code
                else if let Some(ref rust_code_block) = rule.rust_code {
                    // Capture fields follow syntax-pattern order. Opaque text and
                    // guest-body values are retained in the Reduce frame, while
                    // native term fields use the same SCC-aware Visit policy as
                    // ordinary HOL parameters.
                    if let Some(layout) = capture_layout(
                        rule.term_context.as_deref().unwrap_or(&[]),
                        rule.syntax_pattern.as_deref().unwrap_or(&[]),
                    ) {
                        let rust_code = &rust_code_block.code;
                        let rust_code_expr: syn::Expr = syn::parse_quote!({ #rust_code });
                        let safe_closure_call =
                            crate::gen::native::rust_code_rewrite::safeify_and_wrap(
                                &rust_code_expr,
                            );
                        let reduce_variant = format_ident!("Reduce{}{}Capture", category, label);

                        enum CapturePdaKind {
                            Opaque {
                                storage: TokenStream,
                                optional: bool,
                            },
                            Native {
                                visit: syn::Ident,
                                value: syn::Ident,
                                optional: bool,
                            },
                            ExternalNative {
                                storage: TokenStream,
                                optional: bool,
                            },
                            Borrow {
                                storage: TokenStream,
                                optional: bool,
                            },
                            Predicate,
                        }

                        let mut pats: Vec<TokenStream> = Vec::new();
                        let mut fields: Vec<(syn::Ident, CapturePdaKind)> = Vec::new();
                        for f in &layout.non_scope {
                            let name = format_ident!("{}", f.name);
                            match &f.kind {
                                CaptureFieldKind::TokenText => {
                                    pats.push(quote! { #name });
                                    fields.push((
                                        name,
                                        CapturePdaKind::Opaque {
                                            storage: quote! { ::std::string::String },
                                            optional: f.optional,
                                        },
                                    ));
                                },
                                CaptureFieldKind::GuestBody { .. } => {
                                    pats.push(quote! { #name });
                                    fields.push((
                                        name,
                                        CapturePdaKind::Opaque {
                                            storage: quote! {
                                                ::std::sync::Arc<::mettail_runtime::FltNode>
                                            },
                                            optional: f.optional,
                                        },
                                    ));
                                },
                                CaptureFieldKind::Term(ty) => {
                                    pats.push(quote! { #name });
                                    let TypeExpr::Base(target_name) = ty else {
                                        let msg = format!(
                                            "mettail: cannot emit a stack-safe evaluator frame \
                                             for capture rule `{}::{}` because term field `{}` \
                                             has non-base type `{ty:?}`",
                                            category, label, f.name,
                                        );
                                        return quote::quote_spanned!(
                                            label.span()=> compile_error!(#msg);
                                        );
                                    };
                                    let target_type =
                                        language.types.iter().find(|t| t.name == *target_name);
                                    let kind = match target_type {
                                        Some(target) if target.native_type.is_some() => {
                                            let target_component =
                                                native_component[&target.name.to_string()];
                                            if target_component == component {
                                                CapturePdaKind::Native {
                                                    visit: format_ident!("Visit{}", target_name),
                                                    value: format_ident!("{}", target_name),
                                                    optional: f.optional,
                                                }
                                            } else {
                                                CapturePdaKind::ExternalNative {
                                                    storage: eval_return_type(target),
                                                    optional: f.optional,
                                                }
                                            }
                                        },
                                        Some(target) => {
                                            let target = &target.name;
                                            CapturePdaKind::Borrow {
                                                storage: quote! { ::std::sync::Arc<#target> },
                                                optional: f.optional,
                                            }
                                        },
                                        None => {
                                            let msg = format!(
                                                "mettail: capture rule `{}::{}` references \
                                                 undeclared category `{}`",
                                                category, label, target_name,
                                            );
                                            return quote::quote_spanned!(
                                                label.span()=> compile_error!(#msg);
                                            );
                                        },
                                    };
                                    fields.push((name, kind));
                                },
                                CaptureFieldKind::Predicate => {
                                    let uname = format_ident!("_{}", f.name);
                                    pats.push(quote! { #uname });
                                    fields.push((name, CapturePdaKind::Predicate));
                                },
                            }
                        }
                        if layout.scope.is_some() {
                            pats.push(quote! { _scope });
                        }

                        let frame_fields: Vec<TokenStream> = fields
                            .iter()
                            .filter_map(|(name, kind)| match kind {
                                CapturePdaKind::Native { optional: false, .. }
                                | CapturePdaKind::Predicate => None,
                                CapturePdaKind::Native { optional: true, .. } => {
                                    Some(quote! { #name: bool })
                                },
                                CapturePdaKind::Opaque { storage, optional: false }
                                | CapturePdaKind::ExternalNative { storage, optional: false }
                                | CapturePdaKind::Borrow { storage, optional: false } => {
                                    Some(quote! { #name: #storage })
                                },
                                CapturePdaKind::Opaque { storage, optional: true }
                                | CapturePdaKind::ExternalNative { storage, optional: true }
                                | CapturePdaKind::Borrow { storage, optional: true } => {
                                    Some(quote! { #name: ::std::option::Option<#storage> })
                                },
                            })
                            .collect();
                        let frame_field_names: Vec<syn::Ident> = fields
                            .iter()
                            .filter_map(|(name, kind)| match kind {
                                CapturePdaKind::Native { optional: false, .. }
                                | CapturePdaKind::Predicate => None,
                                _ => Some(name.clone()),
                            })
                            .collect();
                        let eager_values: Vec<TokenStream> = fields
                            .iter()
                            .filter_map(|(name, kind)| match kind {
                                CapturePdaKind::ExternalNative { optional: false, .. } => {
                                    Some(quote! { let #name = #name.as_ref().try_eval()?; })
                                },
                                CapturePdaKind::ExternalNative { optional: true, .. } => {
                                    Some(quote! {
                                        let #name = match #name.as_ref() {
                                            ::std::option::Option::Some(__child) => {
                                                ::std::option::Option::Some(
                                                    __child.as_ref().try_eval()?
                                                )
                                            },
                                            ::std::option::Option::None => {
                                                ::std::option::Option::None
                                            },
                                        };
                                    })
                                },
                                _ => None,
                            })
                            .collect();
                        let frame_field_inits: Vec<TokenStream> = fields
                            .iter()
                            .filter_map(|(name, kind)| match kind {
                                CapturePdaKind::Native { optional: false, .. }
                                | CapturePdaKind::Predicate => None,
                                CapturePdaKind::Native { optional: true, .. } => {
                                    Some(quote! { #name: #name.is_some() })
                                },
                                CapturePdaKind::ExternalNative { .. } => Some(quote! { #name }),
                                CapturePdaKind::Opaque { .. } | CapturePdaKind::Borrow { .. } => {
                                    Some(quote! { #name: #name.clone() })
                                },
                            })
                            .collect();
                        if frame_fields.is_empty() {
                            pda_frame_variants.push(quote! { #reduce_variant, });
                        } else {
                            pda_frame_variants.push(quote! {
                                #reduce_variant { #(#frame_fields),* },
                            });
                        }
                        let reduce_push = if frame_field_names.is_empty() {
                            quote! { work.push(#frame_type::#reduce_variant); }
                        } else {
                            quote! {
                                work.push(#frame_type::#reduce_variant {
                                    #(#frame_field_inits),*
                                });
                            }
                        };
                        let native_pushes: Vec<TokenStream> = fields
                            .iter()
                            .rev()
                            .filter_map(|(name, kind)| match kind {
                                CapturePdaKind::Native { visit, optional: false, .. } => {
                                    Some(quote! {
                                        work.push(#frame_type::#visit(#name.as_ref()));
                                    })
                                },
                                CapturePdaKind::Native { visit, optional: true, .. } => {
                                    Some(quote! {
                                        if let ::std::option::Option::Some(__child) = #name.as_ref() {
                                            work.push(#frame_type::#visit(__child.as_ref()));
                                        }
                                    })
                                },
                                _ => None,
                            })
                            .collect();
                        pda_visit_arms.push(quote! {
                            #category::#label(#(#pats),*) => {
                                #(#eager_values)*
                                #reduce_push
                                #(#native_pushes)*
                            }
                        });

                        let frame_pat = if frame_field_names.is_empty() {
                            quote! { #frame_type::#reduce_variant }
                        } else {
                            quote! {
                                #frame_type::#reduce_variant { #(#frame_field_names),* }
                            }
                        };
                        let native_pops: Vec<TokenStream> = fields
                            .iter()
                            .rev()
                            .filter_map(|(name, kind)| match kind {
                                CapturePdaKind::Native {
                                    value,
                                    optional: false,
                                    ..
                                } => Some(quote! {
                                    let #name = match values.pop() {
                                        ::std::option::Option::Some(
                                            #value_type::#value(__value)
                                        ) => __value,
                                        _ => unreachable!(
                                            "capture evaluator PDA value/category mismatch"
                                        ),
                                    };
                                }),
                                CapturePdaKind::Native {
                                    value,
                                    optional: true,
                                    ..
                                } => Some(quote! {
                                    let #name = match #name {
                                        true => match values.pop() {
                                            ::std::option::Option::Some(
                                                #value_type::#value(__value)
                                            ) => ::std::option::Option::Some(__value),
                                            _ => unreachable!(
                                                "capture evaluator PDA optional value/category mismatch"
                                            ),
                                        },
                                        false => ::std::option::Option::None,
                                    };
                                }),
                                _ => None,
                            })
                            .collect();
                        let rebinds: Vec<TokenStream> = fields
                            .iter()
                            .filter_map(|(name, kind)| match kind {
                                CapturePdaKind::Opaque { .. } => {
                                    Some(quote! { let #name = &#name; })
                                },
                                CapturePdaKind::Borrow { optional: false, .. } => {
                                    Some(quote! { let #name = &*#name; })
                                },
                                CapturePdaKind::Borrow { optional: true, .. } => Some(quote! {
                                    let #name = #name.as_ref().map(|__child| &**__child);
                                }),
                                CapturePdaKind::Native { .. }
                                | CapturePdaKind::ExternalNative { .. }
                                | CapturePdaKind::Predicate => None,
                            })
                            .collect();
                        pda_reduce_arms.push(quote! {
                            #frame_pat => {
                                #(#native_pops)*
                                #(#rebinds)*
                                match #safe_closure_call {
                                    ::std::option::Option::Some(__value) => {
                                        values.push(#value_type::#value_variant(__value))
                                    },
                                    ::std::option::Option::None => return None,
                                }
                            }
                        });
                        continue;
                    }
                    let rust_code = &rust_code_block.code;
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
                    let rust_code_expr: syn::Expr = syn::parse_quote!({ #rust_code });
                    let safe_closure_call =
                        crate::gen::native::rust_code_rewrite::safeify_and_wrap(&rust_code_expr);
                    match classify_hol_rule_for_pda(rule) {
                        Some(classified) => {
                            let reduce_variant = format_ident!("Reduce{}{}", category, label);
                            // Every native child in this dependency SCC — whether same-
                            // category or cross-category — is represented by a Visit task
                            // and a typed value-enum arm. The old category-local machine
                            // could only spell `Visit(&Cat)`, so a cycle such as Int ⇄ Bool
                            // rebuilt the host stack at every edge. Native children in a
                            // different SCC use one direct call: by construction that edge
                            // lies in the acyclic condensation graph and therefore cannot
                            // repeat with input depth.
                            //
                            // Non-native children (for example `Proc` in Calculator) are
                            // opaque to native evaluation.  They remain owned in the
                            // Reduce frame and are reborrowed for the user's Rust body.
                            enum ParamKind {
                                /// Native child in this SCC: Visit/pop through this PDA.
                                Native {
                                    visit: syn::Ident,
                                    value: syn::Ident,
                                    optional: bool,
                                },
                                /// Native child in another SCC: the condensation graph is
                                /// acyclic, so evaluate once and store the concrete result.
                                ExternalNative {
                                    storage: TokenStream,
                                    optional: bool,
                                },
                                Borrow {
                                    storage: TokenStream,
                                    optional: bool,
                                },
                            }
                            let mut param_kinds: Vec<(syn::Ident, ParamKind)> = Vec::new();
                            for entry in &classified {
                                let (name, ty_id, is_optional) = match entry {
                                    PdaParam::Term { name, ty, is_optional, .. } => {
                                        (name, ty, is_optional)
                                    },
                                    // Task #14 (Option<Guard>): guards are
                                    // never captured into the Reduce frame.
                                    PdaParam::Guard { .. } => continue,
                                };
                                let target_type = language.types.iter().find(|t| t.name == **ty_id);
                                let kind = match target_type {
                                    Some(target) if target.native_type.is_some() => {
                                        let target_component =
                                            native_component[&target.name.to_string()];
                                        if target_component == component {
                                            ParamKind::Native {
                                                visit: format_ident!("Visit{}", ty_id),
                                                value: format_ident!("{}", ty_id),
                                                optional: *is_optional,
                                            }
                                        } else {
                                            ParamKind::ExternalNative {
                                                storage: eval_return_type(target),
                                                optional: *is_optional,
                                            }
                                        }
                                    },
                                    _ => ParamKind::Borrow {
                                        storage: {
                                            let ty_ident = *ty_id;
                                            quote! { ::std::sync::Arc<#ty_ident> }
                                        },
                                        optional: *is_optional,
                                    },
                                };
                                param_kinds.push((name.clone(), kind));
                            }

                            let frame_fields: Vec<TokenStream> = param_kinds
                                .iter()
                                .map(|(n, k)| match k {
                                    ParamKind::Native { optional: false, .. } => quote! {},
                                    ParamKind::Native { optional: true, .. } => {
                                        quote! { #n: bool }
                                    },
                                    ParamKind::ExternalNative { storage, optional: false } => {
                                        quote! { #n: #storage }
                                    },
                                    ParamKind::ExternalNative { storage, optional: true } => {
                                        quote! { #n: ::std::option::Option<#storage> }
                                    },
                                    ParamKind::Borrow { storage, optional: false } => {
                                        quote! { #n: #storage }
                                    },
                                    ParamKind::Borrow { storage, optional: true } => {
                                        quote! { #n: ::std::option::Option<#storage> }
                                    },
                                })
                                .filter(|field| !field.is_empty())
                                .collect();
                            let frame_field_names: Vec<syn::Ident> = param_kinds
                                .iter()
                                .filter_map(|(n, k)| match k {
                                    ParamKind::Native { optional: false, .. } => None,
                                    _ => Some(n.clone()),
                                })
                                .collect();
                            let frame_field_inits: Vec<TokenStream> = param_kinds
                                .iter()
                                .filter_map(|(n, k)| match k {
                                    ParamKind::Native { optional: false, .. } => None,
                                    ParamKind::Native { optional: true, .. } => {
                                        Some(quote! { #n: #n.is_some() })
                                    },
                                    ParamKind::ExternalNative { .. } => Some(quote! { #n }),
                                    ParamKind::Borrow { .. } => Some(quote! { #n }),
                                })
                                .collect();

                            // Emit Frame variant.
                            if frame_fields.is_empty() {
                                pda_frame_variants.push(quote! { #reduce_variant, });
                            } else {
                                pda_frame_variants.push(quote! {
                                    #reduce_variant { #(#frame_fields),* },
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
                            let eager_external_values: Vec<TokenStream> = param_kinds
                                .iter()
                                .filter_map(|(n, k)| match k {
                                    ParamKind::Native { .. } => None,
                                    ParamKind::ExternalNative { optional: false, .. } => {
                                        Some(quote! {
                                            let #n = #n.as_ref().try_eval()?;
                                        })
                                    },
                                    ParamKind::ExternalNative { optional: true, .. } => {
                                        Some(quote! {
                                            let #n: ::std::option::Option<_> = match #n.as_ref() {
                                                ::std::option::Option::Some(__child) => {
                                                    ::std::option::Option::Some(
                                                        __child.as_ref().try_eval()?
                                                    )
                                                },
                                                ::std::option::Option::None => {
                                                    ::std::option::Option::None
                                                },
                                            };
                                        })
                                    },
                                    ParamKind::Borrow { optional: false, .. } => Some(quote! {
                                        // Non-native cross-cat (e.g. Proc): clone the
                                        // child Arc so the frame owns it. `rust_code`
                                        // receives `&Cat` after deref at Reduce time.
                                        let #n = #n.clone();
                                    }),
                                    ParamKind::Borrow { optional: true, .. } => Some(quote! {
                                        // Opt-Group: clone the optional Arc into the frame.
                                        let #n: ::std::option::Option<_> = #n.clone();
                                    }),
                                })
                                .collect();
                            let reduce_push = if frame_field_names.is_empty() {
                                quote! { work.push(#frame_type::#reduce_variant); }
                            } else {
                                quote! {
                                    work.push(#frame_type::#reduce_variant {
                                        #(#frame_field_inits),*
                                    });
                                }
                            };
                            // Native children of every category are Visit-pushed in
                            // reverse declaration order so the leftmost child runs first.
                            // Optional presence is recorded in the Reduce frame and controls
                            // both the Visit push and the matching value pop.
                            let native_pushes: Vec<TokenStream> = param_kinds
                                .iter()
                                .rev()
                                .filter_map(|(name, kind)| match kind {
                                    ParamKind::Native { visit, optional: false, .. } => {
                                        Some(quote! {
                                            work.push(#frame_type::#visit(#name.as_ref()));
                                        })
                                    },
                                    ParamKind::Native { visit, optional: true, .. } => {
                                        Some(quote! {
                                            if let ::std::option::Option::Some(__opt_child) =
                                                #name.as_ref()
                                            {
                                                work.push(
                                                    #frame_type::#visit(__opt_child.as_ref()),
                                                );
                                            }
                                        })
                                    },
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
                                    #(#eager_external_values)*
                                    #reduce_push
                                    #(#native_pushes)*
                                }
                            });

                            // Emit Reduce arm: pop same-SCC native values (in reverse
                            // param order = pop order), then run the safeified
                            // rust_code with all params in scope. Non-native
                            // cross-cat params bind as `&Cat` (deref the Box
                            // stored in the frame) so user rust_code sees the
                            // same borrow as the previous recursive implementation.
                            let frame_pat = if frame_field_names.is_empty() {
                                quote! { #frame_type::#reduce_variant }
                            } else {
                                quote! {
                                    #frame_type::#reduce_variant { #(#frame_field_names),* }
                                }
                            };
                            let pops: Vec<TokenStream> = param_kinds
                                    .iter()
                                    .rev()
                                    .filter_map(|(name, kind)| match kind {
                                        ParamKind::Native {
                                            value,
                                            optional: false,
                                            ..
                                        } => Some(quote! {
                                            let #name = match values.pop() {
                                                ::std::option::Option::Some(
                                                    #value_type::#value(__value)
                                                ) => __value,
                                                _ => unreachable!(
                                                    "evaluator PDA value/category mismatch"
                                                ),
                                            };
                                        }),
                                        ParamKind::Native {
                                            value,
                                            optional: true,
                                            ..
                                        } => Some(quote! {
                                            let #name = match #name {
                                                true => match values.pop() {
                                                    ::std::option::Option::Some(
                                                        #value_type::#value(__value)
                                                    ) => ::std::option::Option::Some(__value),
                                                    _ => unreachable!(
                                                        "evaluator PDA optional value/category mismatch"
                                                    ),
                                                },
                                                false => ::std::option::Option::None,
                                            };
                                        }),
                                        _ => None,
                                    })
                                    .collect();
                            let borrow_rebinds: Vec<TokenStream> = param_kinds
                                .iter()
                                .filter_map(|(n, k)| match k {
                                    ParamKind::Borrow { optional: false, .. } => Some(quote! {
                                        // Frame owns an Arc<Cat>; give user
                                        // `&Cat` via explicit deref-and-reborrow.
                                        let #n = &*#n;
                                    }),
                                    ParamKind::Borrow { optional: true, .. } => Some(quote! {
                                        // Opt-Group: Frame owns Option<Arc<Cat>>.
                                        // Give user `Option<&Cat>` via map deref.
                                        let #n: ::std::option::Option<&_> = #n.as_ref().map(|__b| &**__b);
                                    }),
                                    ParamKind::ExternalNative { .. } => None,
                                    ParamKind::Native { .. } => None,
                                })
                                .collect();
                            pda_reduce_arms.push(quote! {
                                #frame_pat => {
                                    #(#pops)*
                                    #(#borrow_rebinds)*
                                    match #safe_closure_call {
                                        Some(__v) => {
                                            values.push(#value_type::#value_variant(__v))
                                        },
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
                        // PDA: forward to child via Visit frame (no Reduce needed).
                        pda_visit_arms.push(quote! {
                            #category::#label(_, expr) => {
                                work.push(#frame_type::#visit_variant(expr.as_ref()));
                            }
                        });
                    }
                }
            }
        } // end: `else` of `if is_collection_for_eval`

        machines[component]
            .frame_variants
            .extend(pda_frame_variants);
        machines[component].arms.push(quote! {
            #frame_type::#visit_variant(__node) => match __node {
                #(#pda_visit_arms)*
                _ => return ::std::option::Option::None,
            },
        });
        machines[component].arms.extend(pda_reduce_arms);

        let try_eval_body = if component_is_singleton {
            quote! {
                let #value_type::#value_variant(__value) =
                    #machine_function(#frame_type::#visit_variant(self))?;
                ::std::option::Option::Some(__value)
            }
        } else {
            quote! {
                match #machine_function(#frame_type::#visit_variant(self))? {
                    #value_type::#value_variant(__value) => {
                        ::std::option::Option::Some(__value)
                    },
                    _ => unreachable!("evaluator PDA root value/category mismatch"),
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

    let machine_defs: Vec<TokenStream> = machines
        .into_iter()
        .map(|machine| {
            let ComponentMachine {
                frame,
                value,
                function,
                visit_variants,
                value_variants,
                frame_variants,
                arms,
            } = machine;
            quote! {
                #[allow(non_camel_case_types)]
                enum #frame<'a> {
                    #(#visit_variants)*
                    #(#frame_variants)*
                }

                #[allow(non_camel_case_types)]
                enum #value {
                    #(#value_variants)*
                }

                #[allow(unreachable_patterns)]
                fn #function(__root: #frame<'_>) -> ::std::option::Option<#value> {
                    let mut work = ::std::vec![__root];
                    let mut values: ::std::vec::Vec<#value> = ::std::vec::Vec::new();
                    while let ::std::option::Option::Some(__frame) = work.pop() {
                        match __frame {
                            #(#arms)*
                        }
                    }
                    let __result = values.pop()?;
                    debug_assert!(values.is_empty(), "evaluator PDA left surplus values");
                    ::std::option::Option::Some(__result)
                }
            }
        })
        .collect();

    quote! {
        #(#machine_defs)*

        #(#impls)*
    }
}

#[cfg(test)]
#[path = "../../../tests/support/native_eval_recursive_oracle.rs"]
mod recursive_oracle;

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

    fn pda_param_shapes(params: &[PdaParam<'_>]) -> Vec<(String, String, bool)> {
        params
            .iter()
            .map(|param| match param {
                PdaParam::Term { name, ty, is_optional } => {
                    (format!("term:{name}"), ty.to_string(), *is_optional)
                },
                PdaParam::Guard { name } => (format!("guard:{name}"), String::new(), false),
            })
            .collect()
    }

    #[test]
    fn iterative_term_param_consumers_match_recursive_oracles() {
        let params = vec![
            simple("head", "Int"),
            TermParam::Optional {
                params: vec![
                    TermParam::GuardBody { name: format_ident!("guard") },
                    TermParam::Optional { params: vec![simple("nested", "Bool")] },
                ],
            },
            simple("external", "Proc"),
        ];
        let native_index = HashMap::from([("Int".to_string(), 4), ("Bool".to_string(), 7)]);

        let mut actual_dependencies = Vec::new();
        collect_native_dependencies(&params, &native_index, &mut actual_dependencies);
        let mut expected_dependencies = Vec::new();
        recursive_oracle::collect_native_dependencies(
            &params,
            &native_index,
            &mut expected_dependencies,
        );
        assert_eq!(actual_dependencies, expected_dependencies);
        assert_eq!(actual_dependencies, vec![4, 7]);

        let actual = classify_term_params_for_pda(&params).expect("fixture is PDA-compatible");
        let expected = recursive_oracle::classify_term_params_for_pda(&params)
            .expect("recursive fixture is PDA-compatible");
        assert_eq!(pda_param_shapes(&actual), pda_param_shapes(&expected));

        let unsupported = vec![TermParam::MultiAbstraction {
            binder: format_ident!("xs"),
            body: format_ident!("body"),
            ty: TypeExpr::Base(format_ident!("Proc")),
        }];
        assert_eq!(
            classify_term_params_for_pda(&unsupported).is_some(),
            recursive_oracle::classify_term_params_for_pda(&unsupported).is_some(),
        );
    }

    #[test]
    fn native_term_param_consumers_handle_20k_nesting_on_a_256k_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut nested = simple("leaf", "Int");
                for _ in 0..20_000 {
                    nested = TermParam::Optional { params: vec![nested] };
                }
                let params = vec![nested];
                let native_index = HashMap::from([("Int".to_string(), 11)]);

                let mut dependencies = Vec::new();
                collect_native_dependencies(&params, &native_index, &mut dependencies);
                assert_eq!(dependencies, vec![11]);

                let classified =
                    classify_term_params_for_pda(&params).expect("deep leaf remains compatible");
                assert_eq!(classified.len(), 1);
                assert!(matches!(
                    &classified[0],
                    PdaParam::Term { name, ty, is_optional: true }
                        if name == "leaf" && *ty == "Int"
                ));
            })
            .expect("spawn low-stack native term-param gate")
            .join()
            .expect("native term-param consumers must not use nesting-proportional call stack");
    }

    #[test]
    fn scc_partition_coalesces_cycles_but_not_dag_edges() {
        // 0 ⇄ 1 is the evaluator cycle; 1 → 2 is a condensation-DAG edge.
        let (component_of, components) =
            strongly_connected_components(&[vec![1], vec![0, 2], vec![]]);
        assert_eq!(components, vec![vec![0, 1], vec![2]]);
        assert_eq!(component_of[0], component_of[1]);
        assert_ne!(component_of[1], component_of[2]);
    }

    #[test]
    fn scc_partition_itself_is_stack_safe_on_a_deep_dependency_dag() {
        let node_count = 20_000;
        let mut edges = vec![Vec::new(); node_count];
        for (index, targets) in edges.iter_mut().enumerate().take(node_count - 1) {
            targets.push(index + 1);
        }
        let (component_of, components) = strongly_connected_components(&edges);
        assert_eq!(component_of.len(), node_count);
        assert_eq!(components.len(), node_count);
    }

    #[test]
    fn classify_guard_free_rule_unchanged() {
        // Task #14 gate-1: the tuple→enum refactor must classify guard-free
        // rules exactly as before — same entry count and (name, ty,
        // is_optional) content, in declaration order. (The
        // emitted-token byte-identity across the 22 default languages is
        // enforced by probe P5's sha compare.)
        let ctx = vec![simple("a", "Int"), simple("b", "Proc")];
        let classified = classify_term_params_for_pda(&ctx)
            .expect("guard-free Simple/Base params must classify");
        assert_eq!(classified.len(), 2);
        match &classified[0] {
            PdaParam::Term { name, ty, is_optional } => {
                assert_eq!(name.to_string(), "a");
                assert_eq!(ty.to_string(), "Int");
                assert!(!*is_optional);
            },
            PdaParam::Guard { .. } => panic!("`a:Int` must classify as Term"),
        }
        match &classified[1] {
            PdaParam::Term { name, ty, is_optional } => {
                assert_eq!(name.to_string(), "b");
                assert_eq!(ty.to_string(), "Proc");
                assert!(!*is_optional);
            },
            PdaParam::Guard { .. } => panic!("`b:Proc` must classify as Term"),
        }
    }

    #[test]
    fn classify_optional_guard_yields_guard_entry() {
        // The guardoptsmoke PCheck shape: `k:Int, *opt(?g:Guard)`.
        // Pre-#14 this returned None → compile_error!.
        let ctx = vec![
            simple("k", "Int"),
            TermParam::Optional {
                params: vec![TermParam::GuardBody { name: format_ident!("g") }],
            },
        ];
        let classified = classify_term_params_for_pda(&ctx)
            .expect("Optional{GuardBody} must classify for the PDA");
        assert_eq!(classified.len(), 2, "one Term + one Guard entry");
        assert!(
            matches!(&classified[0], PdaParam::Term { is_optional: false, .. }),
            "`k:Int` stays a mandatory Term",
        );
        assert!(
            matches!(&classified[1], PdaParam::Guard { name } if name == "g"),
            "`?g:Guard` inside #opt must classify as Guard",
        );
    }

    #[test]
    fn classify_top_level_guard_yields_guard_entry() {
        let ctx = vec![simple("p", "Proc"), TermParam::GuardBody { name: format_ident!("guard") }];
        let classified = classify_term_params_for_pda(&ctx)
            .expect("top-level GuardBody must classify for the PDA");
        assert!(matches!(&classified[1], PdaParam::Guard { name } if name == "guard"));
    }

    #[test]
    fn classify_abstraction_still_aborts() {
        // Non-Simple/non-Guard params must still return None (the caller
        // turns that into compile_error! — no silent recursive fallback).
        let ctx = vec![TermParam::Abstraction {
            binder: format_ident!("x"),
            body: format_ident!("p"),
            ty: TypeExpr::Base(format_ident!("Proc")),
        }];
        assert!(classify_term_params_for_pda(&ctx).is_none());
    }
}
