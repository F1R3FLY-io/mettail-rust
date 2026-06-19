//! Dovetail report helper generation.
//!
//! This concern emits AST-first lowering from macro-expanded `LanguageDef`
//! data into the runtime Dovetail API. It never reconstructs a language from
//! rendered syntax strings: constructor labels, categories, rules, and
//! patterns come directly from the parsed language definition.

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::{Equation, LanguageDef, Premise, RewriteRule};
use mettail_ast::pattern::{Pattern as AstPattern, PatternTerm};
use mettail_ast::types::CollectionType;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Ident, LitStr};

use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};

pub(crate) mod ac;
pub(crate) mod op_enum;
pub(crate) mod reconstruct;
pub(crate) mod typed_lowering;
pub(crate) mod typed_report;

/// Whether a language gets the typed-`L` Dovetail fold path (Increment 2/3): it has at least
/// one `fold` term rule whose OUTPUT category has no native type (a non-native-output fold,
/// e.g. RhoCalc's `int(..)`/`+`/`concat` casts that return `Proc`). Such folds reduce nowhere
/// on the `EGraph<String>` path (their `![{..}]` bodies were emitted only into the retired
/// Ascent backend), so these languages carry a generated typed op-enum and native-rewrite
/// dispatcher instead. Non-fold languages (Lambda, BaseMath) and native-output-only fold
/// languages keep the existing `EGraph<String>` path unchanged.
pub(crate) fn needs_typed_fold_path(language: &LanguageDef) -> bool {
    language.terms.iter().any(|rule| {
        rule.eval_mode == Some(mettail_ast::types::EvalMode::Fold)
            && language
                .get_type(&rule.category)
                .map_or(true, |t| t.native_type.is_none())
    })
}

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

fn lit(value: &str) -> LitStr {
    LitStr::new(value, Span::call_site())
}

fn constructor_label(language: &LanguageDef, constructor: &Ident) -> Result<String, String> {
    let category = language
        .category_of_constructor(constructor)
        .ok_or_else(|| format!("constructor `{constructor}` has no category"))?;
    Ok(format!("{}::{}::{}", language.name, category, constructor))
}

fn category_lowering_fn(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_add_{}", to_snake(&category.to_string()))
}

/// The e-graph operator expression for a constructor in a rewrite-rule pattern. With
/// `enum_id = None` (the `EGraph<String>` path) it is the `"Lang::Cat::Ctor"` label string;
/// with `enum_id = Some(L)` (the typed fold path) it is the typed op variant `L::<Cat>_<Ctor>`,
/// so `RewriteRule<L>` patterns match the typed lowering's nodes.
fn constructor_op_expr(
    language: &LanguageDef,
    constructor: &Ident,
    enum_id: Option<&Ident>,
) -> Result<TokenStream, String> {
    match enum_id {
        None => {
            let label = lit(&constructor_label(language, constructor)?);
            Ok(quote! { #label.to_string() })
        },
        Some(enum_id) => {
            let category = language
                .category_of_constructor(constructor)
                .ok_or_else(|| format!("constructor `{constructor}` has no category"))?;
            let variant = op_enum::op_variant_ident(&category, constructor);
            Ok(quote! { #enum_id::#variant })
        },
    }
}

fn opaque_leaf_expr(label: TokenStream, payload: TokenStream) -> TokenStream {
    quote! {
        eg.add(::dovetail::egraph::ENode::leaf(format!("{}::{:?}", #label, #payload)))
    }
}

/// Lower an associative-commutative bag (`HashBag<ElemCat>`) to an n-ary
/// [`dovetail::egraph::ENode`] whose children are the lowered bag elements (each
/// with multiplicity) SORTED by `canonical_class_key`.
///
/// Sorting yields the deterministic canonical (sorted) bag order; the stored
/// order is only a HINT — the AC matcher recomputes the multiset key fresh from
/// current union-find representatives at match time (R1), so a later `rebuild`
/// re-canonicalization cannot lose AC matches.
///
/// `bag_expr` must evaluate to a value exposing `len()` and
/// `iter_elements() -> impl Iterator<Item = &ElemCat>` (the `HashBag` API).
/// `element_add` is the element category's `__mettail_dovetail_add_<cat>` fn.
fn ac_bag_lowering(label: &LitStr, element_add: &Ident, bag_expr: TokenStream) -> TokenStream {
    quote! {
        {
            let __bag = #bag_expr;
            let mut __children: Vec<::dovetail::egraph::EClassId> =
                ::std::vec::Vec::with_capacity(__bag.len());
            for __elem in __bag.iter_elements() {
                __children.push(#element_add(eg, __elem));
            }
            // Canonical (sorted) bag order; cache each key (one computation each).
            __children.sort_by_cached_key(|__c| eg.canonical_class_key(*__c));
            eg.add(::dovetail::egraph::ENode::new(#label.to_string(), __children))
        }
    }
}

/// Whether a collection type is an associative-commutative MULTISET that gets the
/// n-ary canonical bag lowering. Only `HashBag` qualifies: it is the genuine AC
/// multiset (commutative, with multiplicity), so sorting its lowered children by
/// canonical key is sound. `Vec` (ordered, non-commutative), `HashSet` (a set),
/// and `HashMap` (a keyed map) keep the prior opaque-leaf lowering — sorting
/// would not respect their semantics, and the AC engine only consumes `HashBag`
/// bag nodes today.
fn coll_type_is_ac_bag(coll_type: Option<&CollectionType>) -> bool {
    matches!(coll_type, Some(CollectionType::HashBag))
}

fn field_child_expr(
    owner_label: &str,
    field_index: usize,
    field: &FieldInfo,
    field_var: &Ident,
) -> TokenStream {
    let none_label = lit(&format!("{owner_label}::field{field_index}::None"));
    let opaque_label = lit(&format!("{owner_label}::field{field_index}::opaque"));
    let collection_label = lit(&format!("{owner_label}::field{field_index}::collection"));
    let child_fn = category_lowering_fn(&field.category);
    let field_kind = NonTerminalKind::classify(&field.category.to_string());
    if field_kind.is_builtin() {
        let leaf = opaque_leaf_expr(quote! { #opaque_label }, quote! { #field_var });
        return quote! { #leaf };
    }

    if field.is_optional {
        if field.is_predicate {
            let leaf = opaque_leaf_expr(quote! { #opaque_label }, quote! { __pred });
            return quote! {
                match #field_var.as_ref() {
                    Some(__pred) => #leaf,
                    None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
                }
            };
        }
        if field.is_collection {
            if coll_type_is_ac_bag(field.coll_type.as_ref()) {
                // Optional n-ary AC bag field (HashBag): lower the present bag
                // to a sorted-by-canonical-key child list (mirrors the
                // VariantKind::Collection lowering); a missing collection is a
                // distinct nullary leaf.
                let body = ac_bag_lowering(&collection_label, &child_fn, quote! { __values });
                return quote! {
                    match #field_var.as_ref() {
                        Some(__values) => #body,
                        None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
                    }
                };
            }
            let leaf = opaque_leaf_expr(quote! { #collection_label }, quote! { __values });
            return quote! {
                match #field_var.as_ref() {
                    Some(__values) => #leaf,
                    None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
                }
            };
        }
        return quote! {
            match #field_var.as_ref() {
                Some(__inner) => #child_fn(eg, __inner.as_ref()),
                None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
            }
        };
    }

    if field.is_predicate {
        let leaf = opaque_leaf_expr(quote! { #opaque_label }, quote! { #field_var });
        return quote! { #leaf };
    }

    if field.is_collection {
        if coll_type_is_ac_bag(field.coll_type.as_ref()) {
            // Non-optional n-ary AC bag field (HashBag): lower to a
            // sorted-by-canonical-key child list (same as VariantKind::Collection).
            return ac_bag_lowering(&collection_label, &child_fn, quote! { #field_var });
        }
        let leaf = opaque_leaf_expr(quote! { #collection_label }, quote! { #field_var });
        return quote! { #leaf };
    }

    quote! { #child_fn(eg, #field_var.as_ref()) }
}

fn regular_arm(
    language: &LanguageDef,
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
) -> TokenStream {
    let owner = format!("{}::{}::{}", language.name, category, label);
    let owner_lit = lit(&owner);
    let field_vars: Vec<Ident> = (0..fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let child_exprs: Vec<TokenStream> = fields
        .iter()
        .zip(field_vars.iter())
        .enumerate()
        .map(|(i, (field, var))| field_child_expr(&owner, i, field, var))
        .collect();
    quote! {
        #category::#label(#(#field_vars),*) => {
            let __children = vec![#(#child_exprs),*];
            eg.add(::dovetail::egraph::ENode::new(#owner_lit.to_string(), __children))
        }
    }
}

fn binder_arm(
    language: &LanguageDef,
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    multi: bool,
) -> TokenStream {
    let owner = format!("{}::{}::{}", language.name, category, label);
    let owner_lit = lit(&owner);
    let binder_label = lit(&format!("{owner}::binder"));
    let pre_vars: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let scope_var = format_ident!("scope");
    let pre_child_exprs: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(pre_vars.iter())
        .enumerate()
        .map(|(i, (field, var))| field_child_expr(&owner, i, field, var))
        .collect();
    let body_fn = category_lowering_fn(category);
    // (FIX-A) The binder position is lowered to an ANONYMOUS, arity-only marker
    // — never the binder's `FreeVar` identity. moniker `Binder`'s `Debug`/`Hash`
    // expose the `FreeVar`'s `unique_id` (a process-global counter freshened by
    // every `unbind`), so a `{:?}` label leaked a run-varying, alpha-irrelevant
    // value into the e-graph `content_key`. The body (lowered via `unsafe_body`)
    // already carries the de-Bruijn `BoundVar{scope,binder}` coordinates that
    // alpha-canonically identify each bound occurrence, so the binder position
    // must contribute only its arity.
    let binder_child = if multi {
        quote! {
            eg.add(::dovetail::egraph::ENode::leaf(format!(
                "{}::arity::{}",
                #binder_label,
                #scope_var.unsafe_pattern().len()
            )))
        }
    } else {
        quote! {
            eg.add(::dovetail::egraph::ENode::leaf(format!(
                "{}::arity::1",
                #binder_label
            )))
        }
    };

    quote! {
        #category::#label(#(#pre_vars,)* #scope_var) => {
            let __binder = #binder_child;
            let __body = #body_fn(eg, #scope_var.unsafe_body().as_ref());
            let __children = vec![#(#pre_child_exprs,)* __binder, __body];
            eg.add(::dovetail::egraph::ENode::new(#owner_lit.to_string(), __children))
        }
    }
}

fn category_lowering(language: &LanguageDef, category: &Ident) -> TokenStream {
    let fn_name = category_lowering_fn(category);
    let arms: Vec<TokenStream> = collect_category_variants(category, language)
        .into_iter()
        .map(|variant| match variant {
            VariantKind::Var { label } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label(value) => {
                        eg.add(::dovetail::egraph::ENode::leaf(format!("{}::{:?}", #owner, value)))
                    }
                }
            },
            VariantKind::Literal { label } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label(value) => {
                        eg.add(::dovetail::egraph::ENode::leaf(format!("{}::{:?}", #owner, value)))
                    }
                }
            },
            VariantKind::Nullary { label } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label => {
                        eg.add(::dovetail::egraph::ENode::leaf(#owner.to_string()))
                    }
                }
            },
            VariantKind::Regular { label, fields } => {
                regular_arm(language, category, &label, &fields)
            },
            VariantKind::Collection { label, element_cat, coll_type } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                if coll_type_is_ac_bag(Some(&coll_type)) {
                    // n-ary AC bag lowering (HashBag). See `ac_bag_lowering`.
                    let element_add = category_lowering_fn(&element_cat);
                    let body = ac_bag_lowering(&owner, &element_add, quote! { values });
                    quote! {
                        #category::#label(values) => #body
                    }
                } else {
                    // Non-AC collection (Vec/HashSet/HashMap): opaque leaf
                    // (unchanged prior behavior — the AC engine consumes only
                    // HashBag bag nodes today).
                    quote! {
                        #category::#label(values) => {
                            eg.add(::dovetail::egraph::ENode::leaf(format!(
                                "{}::{:?}",
                                #owner,
                                values,
                            )))
                        }
                    }
                }
            },
            VariantKind::Binder { label, pre_scope_fields, .. } => {
                binder_arm(language, category, &label, &pre_scope_fields, false)
            },
            VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
                binder_arm(language, category, &label, &pre_scope_fields, true)
            },
        })
        .collect();

    quote! {
        fn #fn_name(
            eg: &mut ::dovetail::egraph::EGraph<String>,
            term: &#category,
        ) -> ::dovetail::egraph::EClassId {
            match term {
                #(#arms),*
            }
        }
    }
}

fn pattern_to_dovetail(
    language: &LanguageDef,
    pattern: &AstPattern,
    enum_id: Option<&Ident>,
) -> Result<TokenStream, String> {
    match pattern {
        AstPattern::Term(term) => pattern_term_to_dovetail(language, term, enum_id),
        // A collection directly under a constructor is lowered to an AC bag in
        // the `PatternTerm::Apply` arm (which supplies the operator label). A
        // bare/nested collection with no enclosing constructor has no operator and
        // is not produced by the current grammar — fail closed.
        AstPattern::Collection { .. } => {
            Err("a collection metapattern must be the argument of a constructor (AC bag); a bare collection has no operator".into())
        },
        AstPattern::Map { .. } => {
            Err("map metapatterns require collection-comprehension lowering".into())
        },
        AstPattern::Zip { .. } => {
            Err("zip metapatterns require collection-comprehension lowering".into())
        },
    }
}

fn pattern_term_to_dovetail(
    language: &LanguageDef,
    term: &PatternTerm,
    enum_id: Option<&Ident>,
) -> Result<TokenStream, String> {
    match term {
        PatternTerm::Var(var) => {
            if let Some(rule) = language.get_constructor(var) {
                let op = constructor_op_expr(language, &rule.label, enum_id)?;
                Ok(quote! { ::dovetail::rules::Pattern::leaf(#op) })
            } else {
                let name = lit(&var.to_string());
                Ok(quote! { ::dovetail::rules::Pattern::var(#name) })
            }
        },
        PatternTerm::Apply { constructor, args } => {
            // A constructor whose SOLE argument is a collection metapattern
            // `{ ... }` (e.g. Ambient `(PPar { P, Q, ...rest })`) lowers to an AC
            // bag pattern, with the constructor label as the AC operator. The
            // collection has no constructor of its own (see `Pattern::Collection`).
            if let [AstPattern::Collection { .. }] = args.as_slice() {
                if enum_id.is_some() {
                    return Err(
                        "AC collection metapatterns are not yet lowered on the typed fold path"
                            .into(),
                    );
                }
                let label = constructor_label(language, constructor)?;
                let label = lit(&label);
                return ac::lower_ac_collection(language, &label, &args[0]);
            }
            let op = constructor_op_expr(language, constructor, enum_id)?;
            let args = args
                .iter()
                .map(|arg| pattern_to_dovetail(language, arg, enum_id))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(quote! {
                ::dovetail::rules::Pattern::app(#op, vec![#(#args),*])
            })
        },
        PatternTerm::Lambda { .. } => Err("lambda patterns require binder lowering".into()),
        PatternTerm::MultiLambda { .. } => {
            Err("multi-lambda patterns require binder lowering".into())
        },
        PatternTerm::Subst { .. } => {
            Err("substitution patterns require generated substitution lowering".into())
        },
        PatternTerm::MultiSubst { .. } => {
            Err("multi-substitution patterns require generated substitution lowering".into())
        },
    }
}

fn premise_supported(premise: &Premise) -> bool {
    // EXHAUSTIVE over every `Premise` variant (no catch-all): only a congruence
    // premise is supplied by the e-graph congruence closure; all side-condition
    // premises (freshness, relation queries, universals, behavioral / synthetic
    // guards) require evidence the structural saturation does not model, so they
    // fail closed. Mirrors `GeneratedReportCompiler.premise_supported`.
    match premise {
        Premise::Congruence { .. } => true,
        Premise::Freshness(_) => false,
        Premise::RelationQuery { .. } => false,
        Premise::ForAll { .. } => false,
        Premise::BehavioralGuard(_) => false,
        Premise::SyntheticInjGuard { .. } => false,
    }
}

fn lower_equation(
    language: &LanguageDef,
    eq: &Equation,
    enum_id: Option<&Ident>,
) -> (Vec<TokenStream>, Vec<String>) {
    let mut out = Vec::new();
    let mut unsupported = Vec::new();
    if !eq.premises.iter().all(premise_supported) {
        unsupported.push(format!("equation `{}` has side conditions", eq.name));
        return (out, unsupported);
    }

    match pattern_to_dovetail(language, &eq.left, enum_id) {
        Ok(left) if !eq.left.is_just_variable() => {
            match pattern_to_dovetail(language, &eq.right, enum_id) {
                Ok(right) => {
                    let label = lit(&format!("{}::equation::{}::forward", language.name, eq.name));
                    out.push(quote! {
                        ::dovetail::rules::RewriteRule {
                            lhs: #left,
                            rhs: #right,
                            label: Some(#label.to_string()),
                        }
                    });
                },
                Err(reason) => unsupported.push(format!("equation `{}` RHS: {reason}", eq.name)),
            }
        },
        Ok(_) => {},
        Err(reason) => unsupported.push(format!("equation `{}` LHS: {reason}", eq.name)),
    }

    match pattern_to_dovetail(language, &eq.right, enum_id) {
        Ok(right) if !eq.right.is_just_variable() => {
            match pattern_to_dovetail(language, &eq.left, enum_id) {
                Ok(left) => {
                    let label = lit(&format!("{}::equation::{}::reverse", language.name, eq.name));
                    out.push(quote! {
                        ::dovetail::rules::RewriteRule {
                            lhs: #right,
                            rhs: #left,
                            label: Some(#label.to_string()),
                        }
                    });
                },
                Err(reason) => {
                    unsupported.push(format!("equation `{}` reverse RHS: {reason}", eq.name))
                },
            }
        },
        Ok(_) => {},
        Err(reason) => unsupported.push(format!("equation `{}` reverse LHS: {reason}", eq.name)),
    }

    (out, unsupported)
}

fn lower_rewrite(
    language: &LanguageDef,
    rw: &RewriteRule,
    enum_id: Option<&Ident>,
) -> (Vec<TokenStream>, Vec<String>) {
    if !rw.premises.iter().all(premise_supported) {
        return (Vec::new(), vec![format!("rewrite `{}` has side conditions", rw.name)]);
    }
    if rw.is_congruence_rule() {
        // The e-graph congruence closure supplies context closure after the
        // premise-free kernel rewrite has merged the child e-class, so explicit
        // generated congruence rules are not emitted as separate Dovetail data.
        return (Vec::new(), Vec::new());
    }

    match (
        pattern_to_dovetail(language, &rw.left, enum_id),
        pattern_to_dovetail(language, &rw.right, enum_id),
    ) {
        (Ok(lhs), Ok(rhs)) => {
            let label = lit(&format!("{}::rewrite::{}", language.name, rw.name));
            (
                vec![quote! {
                    ::dovetail::rules::RewriteRule {
                        lhs: #lhs,
                        rhs: #rhs,
                        label: Some(#label.to_string()),
                    }
                }],
                Vec::new(),
            )
        },
        (Err(reason), _) => (Vec::new(), vec![format!("rewrite `{}` LHS: {reason}", rw.name)]),
        (_, Err(reason)) => (Vec::new(), vec![format!("rewrite `{}` RHS: {reason}", rw.name)]),
    }
}

fn rule_block(language: &LanguageDef, enum_id: Option<&Ident>) -> (TokenStream, Vec<String>) {
    let mut rules = Vec::new();
    let mut unsupported = Vec::new();
    for eq in &language.equations {
        let (lowered, rejected) = lower_equation(language, eq, enum_id);
        rules.extend(lowered);
        unsupported.extend(rejected);
    }
    for rw in &language.rewrites {
        let (lowered, rejected) = lower_rewrite(language, rw, enum_id);
        rules.extend(lowered);
        unsupported.extend(rejected);
    }

    (quote! { vec![#(#rules),*] }, unsupported)
}

/// Generate feature-gated helpers that compile generated typed AST terms into
/// checked `RuntimeDovetailRunReport` values.
pub fn generate_dovetail_report(language: &LanguageDef) -> TokenStream {
    // Fold-bearing languages (non-native-output `fold`s — RhoCalc's Proc casts/arith) take the
    // typed-`L` path: a typed op-enum + native-rewrite dispatcher that actually reduces folds.
    // Every other language keeps the `EGraph<String>` path below, byte-for-byte unchanged.
    if needs_typed_fold_path(language) {
        return typed_report::generate_typed_dovetail_report(language);
    }
    let name = &language.name;
    let language_struct = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let language_lit = lit(&name.to_string());
    let category_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| category_lowering(language, &ty.name))
        .collect();
    let (rules, unsupported) = rule_block(language, None);
    let unsupported_lits: Vec<LitStr> = unsupported.iter().map(|s| lit(s)).collect();
    let primary_type = language
        .types
        .first()
        .map(|ty| ty.name.clone())
        .expect("language has at least one type");
    let primary_add = category_lowering_fn(&primary_type);

    // Inc 2/3: a host-less language with a binder handler (e.g. Ambient) floats
    // its `new`s outward (the binder congruences) BEFORE the in-engine AC
    // reduction, rather than failing closed on the unlowered equations. The
    // floated term is what gets lowered into the e-graph; the AC rules match the
    // soup under the floated news, so no peel/re-wrap is needed.
    let should_emit_binder =
        crate::gen::runtime::binder_congruence::should_emit_binder_congruence(language);
    let source_expr: TokenStream = if should_emit_binder {
        quote! { __source }
    } else {
        quote! { typed_term.0 }
    };

    let root_block = if language.types.len() > 1 {
        let inner_enum = format_ident!("{}TermInner", name);
        let mut arms = Vec::new();
        for ty in &language.types {
            let cat = &ty.name;
            let add_fn = category_lowering_fn(cat);
            arms.push(quote! {
                #inner_enum::#cat(value) => {
                    __roots.push(#add_fn(&mut eg, value));
                }
            });
        }
        quote! {
            for __alt in #source_expr.all_alts() {
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
            __roots.push(#primary_add(&mut eg, &#source_expr));
        }
    };

    // For a handler language the binder congruences are discharged by the float
    // (so there is no fail-closed gate and no native-eval short-circuit); the
    // floated term flows straight into the e-graph AC reduction. For every other
    // language the existing native-eval + fail-closed gate is preserved exactly.
    let native_gate: TokenStream = if should_emit_binder {
        quote! {}
    } else {
        quote! {
            if let Ok(report) =
                ::mettail_dovetail_runtime::complete_native_dovetail_report_for_language(
                    &#language_struct,
                    term,
                )
            {
                return Ok(report);
            }

            let unsupported: &[&str] = &[#(#unsupported_lits),*];
            if !unsupported.is_empty() {
                return Err(format!(
                    "generated Dovetail compiler for language {} needs specialized lowering before structural saturation can be complete: {}",
                    #language_lit,
                    unsupported.join("; "),
                ));
            }
        }
    };
    let source_binding: TokenStream = if should_emit_binder {
        quote! {
            // Inc 2: float `new`s outward (binder congruences) before AC
            // reduction. `binder_congruence_nf_term` returns `None` when there is
            // no floatable redex, in which case the original term is lowered.
            let __source = typed_term.0.binder_congruence_nf_term()
                .unwrap_or_else(|| typed_term.0.clone());
        }
    } else {
        quote! {}
    };

    quote! {
        #[cfg(feature = "dovetail-codegen")]
        impl #language_struct {
            /// Compile this language's generated typed AST into a checked
            /// runtime Dovetail report.
            ///
            /// The compiler is derived from the same macro-expanded
            /// `LanguageDef` as the AST constructors. Rholang-looking or
            /// source-language text is not parsed or reverse-engineered here.
            ///
            /// Formal models:
            /// - `dovetail/formal/rocq/theories/Lowering/GeneratedReportCompiler.v`
            /// - `dovetail/formal/rocq/theories/Refinement/RustModelBridge.v`
            /// - `dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v`
            pub fn dovetail_report_for(
                term: &dyn mettail_runtime::Term,
                max_iters: usize,
                max_nodes: usize,
            ) -> Result<mettail_runtime::RuntimeDovetailRunReport, String> {
                #native_gate

                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("expected {}Term, got {:?}", #language_lit, term))?;

                #source_binding

                let mut eg = ::dovetail::egraph::EGraph::<String>::with_config(
                    ::dovetail::egraph::EGraphConfig { max_nodes },
                );
                #(#category_fns)*

                let mut __roots = Vec::new();
                #root_block
                __roots.sort_unstable();
                __roots.dedup();
                if __roots.is_empty() {
                    return Err(format!(
                        "generated Dovetail compiler for language {} produced no roots",
                        #language_lit,
                    ));
                }

                let rules = #rules;
                let sat = eg.saturate(&rules, max_iters);
                if sat.outcome != ::dovetail::rules::SaturationOutcome::Converged {
                    return Err(format!(
                        "generated Dovetail saturation for language {} stopped before convergence: {:?}",
                        #language_lit,
                        sat.outcome,
                    ));
                }

                let mut extractor =
                    ::dovetail::extract::Extractor::new(&eg, |_| ::rigail::TropicalWeight(0.0));
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
    fn generated_report_uses_structured_constructor_rules() {
        let language = parse(
            r#"
                name: DovetailSmoke,
                types { Expr }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                    Wrap . x:Expr |- "wrap" "(" x ")" : Expr ;
                }
                equations {}
                rewrites {
                    AToB . |- A ~> B ;
                }
            "#,
        );

        let tokens = generate_dovetail_report(&language).to_string();
        let (_, unsupported) = rule_block(&language, None);
        assert!(tokens.contains("dovetail_report_for"));
        assert!(tokens.contains("DovetailSmoke"));
        assert!(tokens.contains("AToB"));
        assert!(unsupported.is_empty(), "unexpected unsupported rules: {unsupported:?}");
    }

    #[test]
    fn generated_report_fails_closed_for_binder_metapatterns() {
        let language = parse(
            r#"
                name: DovetailBinder,
                types { Expr Name }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                    Lam . ^x.p:[Name -> Expr] |- "lam" x "." p : Expr ;
                }
                equations {}
                rewrites {
                    BadBeta . |- (Lam ^x.A) ~> B ;
                }
            "#,
        );

        let tokens = generate_dovetail_report(&language).to_string();
        assert!(tokens.contains("dovetail_report_for"));
        assert!(tokens.contains("lambda patterns require binder lowering"));
    }

    #[test]
    fn generated_report_lowers_ac_bag_rewrite_to_pattern_ac() {
        // An Ambient-shaped fragment: a HashBag `PPar` and an OpenRule AC redex.
        // The rewrite must lower to `Pattern::ac` (NOT be rejected as
        // unsupported), with the constructor label as the AC operator.
        let language = parse(
            r#"
                name: AcSmoke,
                types { Proc Name }
                terms {
                    PZero . Proc ::= "0" ;
                    POpen . Proc ::= "open(" Name "," Proc ")" ;
                    PAmb . Proc ::= Name "[" Proc "]" ;
                    PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                }
                equations {}
                rewrites {
                    OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
                        ~> (PPar {P, Q, ...rest}) ;
                }
            "#,
        );

        let (_, unsupported) = rule_block(&language, None);
        assert!(
            unsupported.is_empty(),
            "AC bag rewrite must lower, not be rejected: {unsupported:?}"
        );

        let tokens = generate_dovetail_report(&language).to_string();
        // The lowered rule uses the AC pattern constructor with the PPar label.
        // (`::` inside a string literal is not token-spaced; the surrounding
        // path `Pattern::ac` IS spaced by the token stringifier.)
        assert!(tokens.contains("Pattern :: ac"), "AC bag pattern emitted");
        assert!(
            tokens.contains("AcSmoke::Proc::PPar"),
            "PPar is the AC operator label: {tokens}"
        );
        // The fixed sub-patterns (POpen / PAmb apps) and the `rest` remainder
        // are present.
        assert!(tokens.contains("AcSmoke::Proc::POpen"));
        assert!(tokens.contains("AcSmoke::Proc::PAmb"));
        assert!(tokens.contains("\"rest\""), "rest remainder variable bound");
    }

    #[test]
    fn premise_supported_is_exhaustive_and_only_congruence() {
        use mettail_ast::language::{FreshnessCondition, FreshnessTarget};
        use proc_macro2::Span;
        use syn::Ident;
        let id = |s: &str| Ident::new(s, Span::call_site());
        // Congruence is the ONLY supported premise; every other variant fails
        // closed (exhaustive match — no catch-all).
        assert!(premise_supported(&Premise::Congruence { source: id("S"), target: id("T") }));
        assert!(!premise_supported(&Premise::Freshness(FreshnessCondition {
            var: id("x"),
            term: FreshnessTarget::Var(id("P")),
        })));
        assert!(!premise_supported(&Premise::RelationQuery {
            relation: id("rel"),
            args: vec![id("a")],
        }));
    }
}
