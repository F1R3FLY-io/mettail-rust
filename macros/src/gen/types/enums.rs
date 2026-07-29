#![allow(clippy::single_match)]

use crate::gen::capture::{field_layout, FieldSlotSource};
use crate::gen::native::NativeType;
use crate::gen::{generate_literal_label, generate_var_label, is_literal_rule, is_var_rule};
use mettail_ast::{
    grammar::{GrammarItem, GrammarRule, NonTerminalKind, SyntaxExpr, TermParam},
    language::LanguageDef,
    types::{CollectionType, TypeExpr},
};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

/// Generate just the AST enums (without parser)
pub fn generate_ast_enums(language: &LanguageDef) -> TokenStream {
    // Group rules by category
    let mut rules_by_cat: HashMap<String, Vec<&GrammarRule>> = HashMap::new();

    for rule in &language.terms {
        let cat_name = rule.category.to_string();
        rules_by_cat.entry(cat_name).or_default().push(rule);
    }

    // Generate enum for each exported category
    let enums: Vec<TokenStream> = language.types.iter().map(|lang_type| {
        let cat_name = &lang_type.name;

        let rules = rules_by_cat
            .get(&cat_name.to_string())
            .map(|v| v.as_slice())
            .unwrap_or(&[]);

        let has_literal_rule = rules.iter().any(|rule| is_literal_rule(rule));
        let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));

        let mut variants: Vec<TokenStream> = rules.iter().map(|rule| {
            generate_variant(rule, language)
        }).collect();

        // Auto-generate literal variant for native types without explicit literal rule.
        // Skip for collection categories (List/Bag/Map) — they get ListLit/BagLit/MapLit below instead.
        let is_collection_category = lang_type.collection_kind.is_some();
        if let Some(native_type) = &lang_type.native_type {
            if !has_literal_rule && !is_collection_category {
                let literal_label = generate_literal_label(native_type);
                let nt = NativeType::from_syn_type(native_type);
                // str is unsized; use String. f32/f64 use canonical wrapper for Eq/Hash/Ord.
                let payload_type = match nt {
                    NativeType::Str => quote! { std::string::String },
                    NativeType::Float64 => quote! { mettail_runtime::CanonicalFloat64 },
                    NativeType::Float32 => quote! { mettail_runtime::CanonicalFloat32 },
                    _ => quote! { #native_type },
                };
                variants.push(quote! {
                    #literal_label(#payload_type)
                });
            }
        }

        // Auto-generate ListLit/BagLit/MapLit literal variant for collection categories
        // whose delimiters are declared in `types { ... }` (List/Bag/Map kinds).
        // Payload:
        //   - `![T] as List`  → `T` from native_type
        //   - bare `List`     → `Vec<Proc>` (Proc is the primary category)
        //   - similarly for Bag (`HashBag<Proc>`) and Map (`HashMapLit<Proc, Proc>`)
        {
            use mettail_ast::language::CollectionCategory;
            let elem_type = language
                .types
                .iter()
                .find(|t| t.name.to_string() == "Proc")
                .map(|t| &t.name)
                .or_else(|| language.types.first().map(|t| &t.name));
            if let Some(ref collection_kind) = lang_type.collection_kind.as_ref() {
                let payload_opt: Option<TokenStream> = if let Some(ref native_type) = lang_type.native_type {
                    // `![HashMap] as Map` (implicit params) parses as a bare `HashMap`;
                    // use the runtime wrapper so derived Hash/Ord/Eq apply.
                    let nt = NativeType::from_syn_type(native_type);
                    if matches!(collection_kind, CollectionCategory::Map(_))
                        && matches!(nt, NativeType::Other(ref s) if s == "HashMap")
                    {
                        elem_type.map(|elem_type| {
                            quote! { mettail_runtime::HashMapLit<#elem_type, #elem_type> }
                        })
                    } else {
                        Some(quote! { #native_type })
                    }
                } else {
                    elem_type.map(|elem_type| match collection_kind {
                        CollectionCategory::List(_) => quote! { Vec<#elem_type> },
                        CollectionCategory::Bag(_) => {
                            quote! { mettail_runtime::HashBag<#elem_type> }
                        }
                        CollectionCategory::Map(_) => {
                            quote! { mettail_runtime::HashMapLit<#elem_type, #elem_type> }
                        }
                        CollectionCategory::Set(_) => {
                            quote! { mettail_runtime::HashSetLit<#elem_type> }
                        }
                        CollectionCategory::Pathmap(_) => {
                            quote! { mettail_runtime::PathMapLit<#elem_type, #elem_type> }
                        }
                    })
                };
                if let (Some(payload_type), false) = (payload_opt, has_literal_rule) {
                    let literal_label = match collection_kind {
                        CollectionCategory::List(_) => quote::format_ident!("ListLit"),
                        CollectionCategory::Bag(_) => quote::format_ident!("BagLit"),
                        CollectionCategory::Map(_) => quote::format_ident!("MapLit"),
                        CollectionCategory::Set(_) => quote::format_ident!("SetLit"),
                        CollectionCategory::Pathmap(_) => quote::format_ident!("PathmapLit"),
                    };
                    variants.push(quote! {
                        #literal_label(#payload_type)
                    });
                }
            }
        }

        // Auto-generate Var variant if no explicit Var rule exists
        if !has_var_rule {
            let var_label = generate_var_label(cat_name);
            variants.push(quote! {
                #var_label(mettail_runtime::OrdVar)
            });
        }

        // Auto-generate lambda variants for domain categories that this
        // category uses. Pre-HOL-B: every (cat, domain) pair — O(categories²).
        // Post-HOL-B: only pairs flagged by `compute_hol_domain_pairs`:
        // either structurally implied by an `Abstraction` /
        // `MultiAbstraction` grammar param, or appearing by name in a
        // `rust_code` body / logic block. This is the primary cut: the
        // enum definition is what every downstream emitter keys off of.
        let hol_pairs = crate::logic::common::compute_hol_domain_pairs(language);
        let cat_str = cat_name.to_string();
        for domain_lang_type in &language.types {
            let domain_name = &domain_lang_type.name;
            let domain_str = domain_name.to_string();

            if !hol_pairs.contains(&(cat_str.clone(), domain_str)) {
                continue;
            }

            // Single-binder lambda: Lam{Domain}
            let lam_variant = syn::Ident::new(
                &format!("Lam{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #lam_variant(mettail_runtime::Scope<mettail_runtime::Binder<String>, std::sync::Arc<#cat_name>>)
            });

            // Multi-binder lambda: MLam{Domain}
            let mlam_variant = syn::Ident::new(
                &format!("MLam{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #mlam_variant(mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, std::sync::Arc<#cat_name>>)
            });

            // Application variant: Apply{Domain}
            // Represents unevaluated application of a lambda to an argument
            let apply_variant = syn::Ident::new(
                &format!("Apply{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #apply_variant(std::sync::Arc<#cat_name>, std::sync::Arc<#domain_name>)
            });

            // Multi-application variant: MApply{Domain}
            let mapply_variant = syn::Ident::new(
                &format!("MApply{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #mapply_variant(std::sync::Arc<#cat_name>, Vec<#domain_name>)
            });
        }

        // Float categories use canonical wrapper payload (Eq/Hash/Ord).
        // NOTE: Debug is NOT derived — it is manually implemented via an iterative work-stack
        // in gen/syntax/debug.rs to avoid stack overflow on deeply nested terms.
        // NOTE: Clone IS derived (ARC refactor, 2026-05-28). Recursive AST
        // children are now `std::sync::Arc<Cat>` (was `Box<Cat>`), so derived
        // `Clone` is `Arc::clone` per child — O(1) and NON-recursive (it stops
        // at the Arc boundary, never descending the subtree). This collapses
        // the former O(N²) deep-clone (`into_term` cloned the whole accumulated
        // subtree at every chain step; heaptrack: 96% of peak heap at
        // chain_1000) to O(N) sharing. The old iterative work-stack clone
        // (gen/term_ops/iterative_clone.rs) existed solely to avoid stack
        // overflow on deep `Box` chains — obsolete now that Arc::clone does not
        // recurse; that module was removed (2026-06-22).
        // NOTE: PartialEq, Eq, PartialOrd, Ord, Hash are NOT derived — they are manually
        // implemented via iterative work-stacks in gen/term_ops/iterative_cmp.rs and
        // gen/term_ops/iterative_hash.rs to avoid stack overflow on deeply nested terms
        // (these still traverse the full tree, so iterative stack-safety is retained).
        let derives = quote! { #[derive(Clone, mettail_runtime::BoundTerm)] };
        quote! {
            #derives
            pub enum #cat_name {
                #(#variants),*
            }
        }
    }).collect();

    quote! {
        #(#enums)*
    }
}

/// Rust type for a literal rule's single field (Integer, Boolean, StringLiteral, FloatLiteral).
fn literal_payload_type(
    kind: NonTerminalKind,
    category: &syn::Ident,
    language: &LanguageDef,
) -> TokenStream {
    let native_type_for_category = || {
        language
            .types
            .iter()
            .find(|t| t.name == *category)
            .and_then(|t| t.native_type.as_ref())
    };
    match kind {
        NonTerminalKind::Integer => {
            if let Some(native_type) = native_type_for_category() {
                quote! { #native_type }
            } else {
                quote! { i32 }
            }
        },
        NonTerminalKind::Boolean => quote! { bool },
        NonTerminalKind::StringLiteral => quote! { std::string::String },
        NonTerminalKind::FloatLiteral => {
            if let Some(native_type) = native_type_for_category() {
                match NativeType::from_syn_type(native_type) {
                    NativeType::Float32 => quote! { mettail_runtime::CanonicalFloat32 },
                    _ => quote! { mettail_runtime::CanonicalFloat64 },
                }
            } else {
                quote! { mettail_runtime::CanonicalFloat64 }
            }
        },
        _ => quote! { std::string::String }, // fallback for str/other
    }
}

/// The exact variant tokens this module writes for `rule` into the generated
/// `ast_enums.rs`.
///
/// ★ #139: exists so the positional gate's cells
/// (`gen/runtime/wpda_codegen/binder.rs`) can assert the DEFINITION against the
/// CONSTRUCTION on the same rule, at the generator, on token streams — with no
/// build of the generated crate. It is the same entry point the enum emitter
/// uses, not a re-derivation of it, so a cell cannot pass against a variant that
/// is never written.
pub(crate) fn variant_tokens_for_rule(rule: &GrammarRule, language: &LanguageDef) -> TokenStream {
    generate_variant(rule, language)
}

fn generate_variant(rule: &GrammarRule, language: &LanguageDef) -> TokenStream {
    let label = &rule.label;

    // Check if this rule uses new syntax (term_context)
    if let Some(ref term_context) = rule.term_context {
        return generate_variant_from_term_context(
            label,
            term_context,
            rule.syntax_pattern.as_deref(),
            language,
            &rule.category,
        );
    }

    // Check if this rule has bindings (old syntax)
    if !rule.bindings.is_empty() {
        // This constructor has binders - generate Scope type
        return generate_binder_variant(rule);
    }

    // Count non-terminal and collection items (these become fields)
    #[derive(Clone)]
    enum FieldType {
        NonTerminal(syn::Ident, NonTerminalKind),
        Collection {
            coll_type: CollectionType,
            element_type: syn::Ident,
        },
    }

    let fields: Vec<FieldType> = rule
        .items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal { ident, kind } => {
                Some(FieldType::NonTerminal(ident.clone(), *kind))
            },
            GrammarItem::Collection { coll_type, element_type, .. } => {
                Some(FieldType::Collection {
                    coll_type: coll_type.clone(),
                    element_type: element_type.clone(),
                })
            },
            GrammarItem::Binder { .. } => None, // Handled above
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        // Unit variant
        quote! { #label }
    } else if fields.len() == 1 {
        match &fields[0] {
            FieldType::NonTerminal(_, kind) if kind.is_literal() => {
                // Literal rule: payload type from nonterminal kind (Integer, Boolean, StringLiteral, FloatLiteral)
                let payload_type = literal_payload_type(*kind, &rule.category, language);
                quote! { #label(#payload_type) }
            },
            FieldType::NonTerminal(_, NonTerminalKind::Var) => {
                // Special case: Var field - always use OrdVar
                quote! { #label(mettail_runtime::OrdVar) }
            },
            FieldType::NonTerminal(ident, _) => {
                // Single non-terminal field
                quote! { #label(std::sync::Arc<#ident>) }
            },
            FieldType::Collection { coll_type, element_type } => {
                // Single collection field
                let coll_type_ident = match coll_type {
                    CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
                        quote! { mettail_runtime::HashBag }
                    },
                    CollectionType::HashSet => quote! { std::collections::HashSet },
                    CollectionType::Vec => quote! { Vec },
                };
                quote! { #label(#coll_type_ident<#element_type>) }
            },
        }
    } else {
        // Multiple fields - tuple variant
        let field_types: Vec<TokenStream> = fields
            .iter()
            .map(|f| match f {
                FieldType::NonTerminal(_, NonTerminalKind::Var) => {
                    quote! { mettail_runtime::OrdVar }
                },
                FieldType::NonTerminal(ident, _) => {
                    quote! { std::sync::Arc<#ident> }
                },
                FieldType::Collection { coll_type, element_type } => {
                    let coll_type_ident = match coll_type {
                        CollectionType::HashBag
                        | CollectionType::HashMap
                        | CollectionType::PathMap => {
                            quote! { mettail_runtime::HashBag }
                        },
                        CollectionType::HashSet => quote! { std::collections::HashSet },
                        CollectionType::Vec => quote! { Vec },
                    };
                    quote! { #coll_type_ident<#element_type> }
                },
            })
            .collect();

        quote! { #label(#(#field_types),*) }
    }
}

/// Generate the AST variant for a rule written in judgement (`term_context`) form.
///
/// ★ Task #139 — the field ORDER is not decided here. It comes from
/// [`crate::gen::capture::field_layout`], the ONE derivation shared with the
/// construction site (`gen/runtime/wpda_codegen/binder.rs::emit_binder_action_entry`,
/// which emits `Cat::Label(field_names…, scope)`). This function decides only
/// each slot's TYPE.
///
/// # What this replaced, and why the split is the repair
///
/// Until #139 this function walked `term_context` — the DECLARATION order —
/// while the constructor walked `syntax_pattern` — the SURFACE order. The two
/// lists were independent, and they agreed only when the author happened to
/// declare parameters in the order the surface mentions them. Two same-typed
/// parameters written the other way round —
///
/// ```text
///   Sub . a:Proc, b:Proc |- "sub" "(" b "," a ")" : Proc ;
/// ```
///
/// — made the constructor emit `Sub(Arc::new(b), Arc::new(a))` against a
/// definition `Sub(Arc<Proc>, Arc<Proc>)`: type-correct, operands transposed,
/// no diagnostic anywhere. Adding a case for the shape that was noticed would
/// have left the class intact; deriving the order from one list removes it.
///
/// The capture-bearing branch that used to sit here was already correct for
/// exactly this reason — it walked the syntax pattern. It is gone because it is
/// now the general case, not a special one.
fn generate_variant_from_term_context(
    label: &syn::Ident,
    term_context: &[TermParam],
    syntax_pattern: Option<&[SyntaxExpr]>,
    language: &LanguageDef,
    category: &syn::Ident,
) -> TokenStream {
    let layout = field_layout(term_context, syntax_pattern);
    let mut fields: Vec<TokenStream> = Vec::new();
    for slot in &layout.slots {
        match (&slot.source, slot.optional) {
            // L9-3: a `v@Tok` capture is the matched token's TEXT, extracted by
            // the walker via `as_token_text()` and carried inertly as a bare
            // `String` — no `Arc`/`Box`, because a capture is plain text.
            (FieldSlotSource::TokenText, false) => fields.push(quote! { std::string::String }),
            (FieldSlotSource::TokenText, true) => {
                fields.push(quote! { Option<std::string::String> })
            },
            // L9-4: a `*flt(…)` guest body is an opaque `Arc<FltNode>` leaf.
            (FieldSlotSource::GuestBody { .. }, false) => {
                fields.push(quote! { std::sync::Arc<mettail_runtime::FltNode> })
            },
            (FieldSlotSource::GuestBody { .. }, true) => {
                fields.push(quote! { Option<std::sync::Arc<mettail_runtime::FltNode>> })
            },
            (FieldSlotSource::Param(param), false) => {
                fields.extend(required_param_field(param, language, category))
            },
            (FieldSlotSource::Param(param), true) => fields.extend(optional_param_field(param)),
        }
    }

    if fields.is_empty() {
        // Unit variant
        quote! { #label }
    } else if fields.len() == 1 {
        let field = &fields[0];
        quote! { #label(#field) }
    } else {
        quote! { #label(#(#fields),*) }
    }
}

/// The field type of a term-context parameter declared OUTSIDE any `#opt(…)`
/// group. Empty when the parameter contributes no field — an abstraction whose
/// declared type is not an arrow has no codomain to put in the `Scope`, so there
/// is nothing to emit.
fn required_param_field(
    param: &TermParam,
    language: &LanguageDef,
    category: &syn::Ident,
) -> Vec<TokenStream> {
    match param {
        TermParam::Simple { ty, .. } => {
            vec![type_expr_to_field_type(ty, Some((language, category)))]
        },
        // Single abstraction `^x.p:[A -> B]` → `Scope<Binder<String>, Arc<B>>`.
        TermParam::Abstraction { ty, .. } => match ty {
            TypeExpr::Arrow { codomain, .. } => {
                let body_type = type_expr_to_rust_type(codomain);
                vec![quote! {
                    mettail_runtime::Scope<mettail_runtime::Binder<String>, std::sync::Arc<#body_type>>
                }]
            },
            _ => Vec::new(),
        },
        // Multi-abstraction `^[xs].p:[Name* -> B]` → `Scope<Vec<Binder<String>>, Arc<B>>`.
        TermParam::MultiAbstraction { ty, .. } => match ty {
            TypeExpr::Arrow { codomain, .. } => {
                let body_type = type_expr_to_rust_type(codomain);
                vec![quote! {
                    mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, std::sync::Arc<#body_type>>
                }]
            },
            _ => Vec::new(),
        },
        // Phase 2D (predicated types, 2026-04-08): a positional
        // `mettail_runtime::BehavioralPred` carrying the per-instance behavioral
        // predicate parsed at source-parse time by the language-generic
        // `mettail_prattail::parser::predicate::PredicateParser` (Phase 1B).
        //
        // The field is passive runtime data used for shape dispatch, display,
        // and hash-consing — not for runtime evaluation. At run time the
        // predicate is enforced host-side at COMM (RSpace matching, a Rholang
        // `where` guard, or a `RhoNativeJoin`) for Rho-backed languages, or
        // evaluated by `mettail_runtime::evaluate_pred_with_bindings` for WPDA
        // refinement guards (§8 of `docs/design/predicated-types.md`). The
        // legacy Ascent JOIN-clause lowering was retired in P6.
        TermParam::GuardBody { .. } => vec![quote! { mettail_runtime::BehavioralPred }],
        // `field_layout` flattens opt-groups into one slot per inner parameter,
        // so an `Optional` never arrives as a slot source.
        TermParam::Optional { .. } => Vec::new(),
    }
}

/// The field type of a term-context parameter declared INSIDE an `#opt(…)`
/// group: each inner parameter contributes its own `Option<T>` field (separate,
/// not a tuple). At runtime, when the syntax-pattern opt block matches, the
/// action populates each `Option` with `Some(…)`; when absent, each is `None`.
/// Nested `Optional` flattens — the engine never produces `Some(Some(…))`.
///
/// ⚠ These types are pinned to what `binder.rs`'s `ActionArgKind::Optional` arm
/// actually constructs, which is `Option<Arc<Cat>>` for a term slot
/// (`binder.rs`'s `into_term::<#cat_id>().map(std::sync::Arc::new)`). A
/// `type_expr_to_field_type` here would render a native-typed parameter as a
/// bare `Option<i64>` and disagree with that construction.
fn optional_param_field(param: &TermParam) -> Vec<TokenStream> {
    match param {
        TermParam::Simple { ty, .. } => {
            let inner_ty = type_expr_to_rust_type(ty);
            // Phase 4 #3 (2026-05-12): collections / maps inside Optional emit
            // `Option<Vec<T>>` / `Option<HashBag<T>>` / `Option<HashSet<T>>` /
            // `Option<HashMapLit<K,V>>` — NOT boxed. Matches the top-level
            // Class-2 convention (bare container, no Box). Container types are
            // already heap-allocated so Box is redundant.
            match ty {
                TypeExpr::Collection { .. } | TypeExpr::Map { .. } => {
                    vec![quote! { Option<#inner_ty> }]
                },
                _ => vec![quote! { Option<std::sync::Arc<#inner_ty>> }],
            }
        },
        TermParam::Abstraction { ty, .. } => match ty {
            TypeExpr::Arrow { codomain, .. } => {
                let body = type_expr_to_rust_type(codomain);
                vec![
                    quote! { Option<mettail_runtime::Scope<mettail_runtime::Binder<String>, std::sync::Arc<#body>>> },
                ]
            },
            _ => Vec::new(),
        },
        TermParam::MultiAbstraction { ty, .. } => match ty {
            TypeExpr::Arrow { codomain, .. } => {
                let body = type_expr_to_rust_type(codomain);
                vec![
                    quote! { Option<mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, std::sync::Arc<#body>>> },
                ]
            },
            _ => Vec::new(),
        },
        TermParam::GuardBody { .. } => vec![quote! { Option<mettail_runtime::BehavioralPred> }],
        // `field_layout` flattens nested opt-groups, so this is unreachable; it
        // is written as the same flatten rather than as an `unreachable!`.
        TermParam::Optional { params } => params.iter().flat_map(optional_param_field).collect(),
    }
}

fn generate_binder_variant(rule: &GrammarRule) -> TokenStream {
    let label = &rule.label;

    // For now, support single binder binding in single body
    // Future: support multiple binders and bodies
    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Get the binder and body categories
    let _binder_cat = match &rule.items[*binder_idx] {
        GrammarItem::Binder { category } => category,
        _ => panic!("Binding index doesn't point to a Binder"),
    };

    let body_cat = match &rule.items[body_idx] {
        GrammarItem::NonTerminal { ident: cat, .. } => cat,
        _ => panic!("Body index doesn't point to a NonTerminal"),
    };

    let mut fields = Vec::new();

    for (i, item) in rule.items.iter().enumerate() {
        if i == *binder_idx {
            // Skip the binder - it's part of the Scope
            continue;
        }

        if i == body_idx {
            // This is the body - generate Scope
            fields.push(quote! {
                mettail_runtime::Scope<mettail_runtime::Binder<String>, std::sync::Arc<#body_cat>>
            });
        } else {
            // Regular field (comes before or after, but not binder or body)
            match item {
                GrammarItem::NonTerminal { kind: NonTerminalKind::Var, .. } => {
                    fields.push(quote! { mettail_runtime::Var<String> });
                },
                GrammarItem::NonTerminal { ident: cat, .. } => {
                    fields.push(quote! { std::sync::Arc<#cat> });
                },
                GrammarItem::Collection { coll_type, element_type, .. } => {
                    // Collection becomes a field with the appropriate collection type
                    let coll_type_ident = match coll_type {
                        CollectionType::HashBag
                        | CollectionType::HashMap
                        | CollectionType::PathMap => {
                            quote! { mettail_runtime::HashBag }
                        },
                        CollectionType::HashSet => quote! { std::collections::HashSet },
                        CollectionType::Vec => quote! { Vec },
                    };
                    fields.push(quote! { #coll_type_ident<#element_type> });
                },
                GrammarItem::Binder { .. } => {
                    // Should have been skipped above
                    panic!("Unexpected binder at position {}", i);
                },
                GrammarItem::Terminal(_) => {
                    // Terminals don't become fields
                },
            }
        }
    }

    // Generate the variant
    quote! {
        #label(#(#fields),*)
    }
}

/// Convert TypeExpr to a Rust field type (for enum variant fields).
/// When language and category are provided, FloatLiteral uses the category's canonical float type (f32/f64).
fn type_expr_to_field_type(
    ty: &TypeExpr,
    language_category: Option<(&LanguageDef, &syn::Ident)>,
) -> TokenStream {
    match ty {
        TypeExpr::Base(ident) => match NonTerminalKind::classify(&ident.to_string()) {
            NonTerminalKind::Var => quote! { mettail_runtime::OrdVar },
            NonTerminalKind::Integer => quote! { i64 },
            NonTerminalKind::Boolean => quote! { bool },
            NonTerminalKind::StringLiteral => quote! { std::string::String },
            // An `Ident`-typed param is the token's TEXT, carried inertly. It is the SAME
            // Rust type as `StringLiteral` on purpose — every String-field seam (Eq/Hash/
            // Ord/subst/normalize/semantic_hash/Display) already treats it as an opaque
            // leaf, so no term operation can bind, capture, or rename it. Deliberately NOT
            // `OrdVar`: see `NonTerminalKind::Ident`'s doc for why binder semantics here
            // would let `new nth in { … }` capture a method name.
            NonTerminalKind::Ident => quote! { std::string::String },
            NonTerminalKind::FloatLiteral => language_category
                .and_then(|(lang, cat)| {
                    lang.types
                        .iter()
                        .find(|t| t.name == *cat)
                        .and_then(|t| t.native_type.as_ref())
                })
                .map(|native_type| match NativeType::from_syn_type(native_type) {
                    NativeType::Float32 => quote! { mettail_runtime::CanonicalFloat32 },
                    _ => quote! { mettail_runtime::CanonicalFloat64 },
                })
                .unwrap_or_else(|| quote! { mettail_runtime::CanonicalFloat64 }),
            NonTerminalKind::Category => quote! { std::sync::Arc<#ident> },
        },
        TypeExpr::Collection { coll_type, element } => {
            let elem_type = type_expr_to_rust_type(element);
            match coll_type {
                CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
                    quote! { mettail_runtime::HashBag<#elem_type> }
                },
                CollectionType::HashSet => quote! { std::collections::HashSet<#elem_type> },
                CollectionType::Vec => quote! { Vec<#elem_type> },
            }
        },
        TypeExpr::Arrow { .. } => {
            // Arrow types in simple params shouldn't happen, but handle gracefully
            quote! { Box<dyn std::any::Any> }
        },
        TypeExpr::MultiBinder(inner) => {
            // MultiBinder in simple context: Vec<T>
            let inner_type = type_expr_to_rust_type(inner);
            quote! { Vec<#inner_type> }
        },
        TypeExpr::Refined { base, .. } => {
            // Refinement type: delegate to the base type
            type_expr_to_field_type(base, language_category)
        },
        TypeExpr::Map { key, value } => {
            // Phase 4 #5b (2026-05-12): Map binder slot. Lower to
            // `HashMapLit<K, V>` for consistency with the action body's
            // CollectionDrain materialization (which produces a
            // `HashMapLit<elem, elem>` per binder.rs::3072-3090). The
            // prior behavior — `type_expr_to_field_type(value)` →
            // `Box<#value>` for `Base` value — was incorrect: it
            // produced a Box<Proc> field that did not match the
            // materialized HashMapLit container, causing a type
            // mismatch at variant construction.
            let k = type_expr_to_rust_type(key);
            let v = type_expr_to_rust_type(value);
            quote! { mettail_runtime::HashMapLit<#k, #v> }
        },
    }
}

/// Convert TypeExpr to a Rust type (for use inside Box<>, etc.)
fn type_expr_to_rust_type(ty: &TypeExpr) -> TokenStream {
    match ty {
        TypeExpr::Base(ident) => {
            quote! { #ident }
        },
        TypeExpr::Collection { coll_type, element } => {
            let elem_type = type_expr_to_rust_type(element);
            match coll_type {
                CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
                    quote! { mettail_runtime::HashBag<#elem_type> }
                },
                CollectionType::HashSet => quote! { std::collections::HashSet<#elem_type> },
                CollectionType::Vec => quote! { Vec<#elem_type> },
            }
        },
        TypeExpr::Arrow { domain, codomain } => {
            let dom = type_expr_to_rust_type(domain);
            let cod = type_expr_to_rust_type(codomain);
            quote! { (#dom -> #cod) }
        },
        TypeExpr::MultiBinder(inner) => {
            let inner_type = type_expr_to_rust_type(inner);
            quote! { Vec<#inner_type> }
        },
        TypeExpr::Refined { base, .. } => {
            // Refinement type: delegate to the base type
            type_expr_to_rust_type(base)
        },
        TypeExpr::Map { key, value } => {
            let k = type_expr_to_rust_type(key);
            let v = type_expr_to_rust_type(value);
            quote! { mettail_runtime::HashMapLit<#k, #v> }
        },
    }
}
