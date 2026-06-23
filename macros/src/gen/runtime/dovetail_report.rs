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

/// Whether a language gets the typed-`L` Dovetail path (Increment 2/3 + E1). A language needs
/// the typed path when it has either:
///
///   1. **a non-native-output `fold`** — a `fold` term rule whose OUTPUT category has no native
///      type (e.g. RhoCalc's `int(..)`/`+`/`concat` casts that return `Proc`). Such folds reduce
///      nowhere on the `EGraph<String>` path (their `![{..}]` bodies were emitted only into the
///      retired Ascent backend); OR
///   2. **(E1.1) a substitution rewrite** — a rewrite whose RHS is a β-style `Subst`/`MultiSubst`
///      replacement ([`is_substitution_rewrite`]). The contractum is a NEW typed term the runtime
///      must reconstruct from the e-graph, run a generated `substitute_<cat>`/`multi_substitute_<cat>`
///      on, and re-add — exactly the typed-path machinery (`saturate_with_native` + a native-rule
///      dispatcher + reconstruction). On the `EGraph<String>` path such a rewrite is rejected
///      (`dovetail_report_for` errors), leaving the language (e.g. Lambda) with no reducer.
///
/// Languages with neither (BaseMath; native-output-only fold languages like Calculator) keep the
/// existing `EGraph<String>` path unchanged. Renamed from `needs_typed_fold_path` (the path is no
/// longer fold-only); the old name is retained as a thin alias for any external caller.
pub(crate) fn needs_typed_dovetail_path(language: &LanguageDef) -> bool {
    let has_native_fold = language.terms.iter().any(|rule| {
        rule.eval_mode == Some(mettail_ast::types::EvalMode::Fold)
            && language
                .get_type(&rule.category)
                .map_or(true, |t| t.native_type.is_none())
    });
    let has_substitution_rewrite = language
        .rewrites
        .iter()
        .any(|rw| is_substitution_rewrite(language, rw).is_some());
    has_native_fold || has_substitution_rewrite
}

/// Backward-compatible alias for [`needs_typed_dovetail_path`] (the typed path is no longer
/// fold-only after E1; this preserves the historical name for any out-of-module reference).
pub(crate) fn needs_typed_fold_path(language: &LanguageDef) -> bool {
    needs_typed_dovetail_path(language)
}

/// (E1.2) A rewrite recognized as a generalized **substitution rewrite** — a β-style replacement
/// whose contractum is produced by running a generated `substitute_<cat>`/`multi_substitute_<cat>`
/// on a reconstructed binder body. Everything here is derived from `LanguageDef`; there is NO
/// per-language hardcoding (no `App`/`Lam` literal, no `name == "Lambda"`).
#[derive(Debug, Clone)]
pub(crate) struct SubstRewrite {
    /// The rewrite's name/label (`<Lang>::rewrite::<name>` for the native-rule label).
    pub(crate) label: String,
    /// The whole LHS pattern (`rw.left`). The native-rule LHS is derived from it by
    /// [`subst_rewrite_native_lhs`], binding `scope_var` to the WHOLE binder node.
    pub(crate) left: AstPattern,
    /// The single scope variable — bound by the `binder_label` constructor in `left`, and the
    /// `scope` of the RHS `Subst`/`MultiSubst`.
    pub(crate) scope_var: Ident,
    /// The replacement argument variables (RHS `replacements`), in order. Each is a plain `Var`
    /// occurring in `left`; `repl_vars.len()` is the substitution arity.
    pub(crate) repl_vars: Vec<Ident>,
    /// The matched binder constructor label (a `VariantKind::Binder`/`MultiBinder` whose body the
    /// `scope_var` denotes) — reconstruction matches `binder_cat::binder_label(scope)`.
    pub(crate) binder_label: Ident,
    /// The binder constructor's category (the category `binder_label` constructs).
    pub(crate) binder_cat: Ident,
    /// The bound-variable (domain) category — the `substitute_<binder_cat_lc>` replacement type
    /// and the `&binder.0` free-variable type.
    pub(crate) binder_var_cat: Ident,
    /// The body (codomain) category — `build_<body_cat>_d` reconstructs the scope body, the result
    /// of substitution is a `body_cat`, re-added via `__mettail_dovetail_add_<body_cat>`.
    pub(crate) body_cat: Ident,
    /// Whether the matched binder is a `MultiBinder` (`multi_substitute_*` with an arity assert)
    /// vs a single `Binder` (`substitute_*`, arity-1).
    pub(crate) multi: bool,
    /// The outermost constructor of `left` (the redex head, e.g. `App`) — its op-enum variant
    /// (`op_variant_ident`) joins the MF1 redex-head set so extraction prefers the contractum.
    pub(crate) head_label: Ident,
    /// The category of the `head_label` constructor (for `op_variant_ident`).
    pub(crate) head_cat: Ident,
}

/// (E1.2 — MF4, shape-guarded) Classify a rewrite as a [`SubstRewrite`], or `None`.
///
/// Accepts ONLY the precise β-substitution shape, fail-closed on everything else (verified to
/// REJECT RhoCalc's `Comm`, whose RHS nests the `MultiSubst` inside an AC `PPar` and whose
/// replacement is a `Map`):
///
///  - premises are congruence-only (every other premise kind is a side condition the structural
///    saturation cannot discharge);
///  - the RHS is *exactly* a `Pattern::Term(MultiSubst { scope: Var, .. })` or
///    `Pattern::Term(Subst { term: Var, .. })` — the substitution is the WHOLE RHS, never nested
///    inside `Apply`/`Collection`/`Map`/`Zip`;
///  - exactly one scope variable (single binder), and the scope is a bare `Var`;
///  - every replacement is a plain `Var` (the supported, fully-general case) — `Map`/`Zip`/
///    `Collection` replacements (RhoCalc's `qs.*map(..)`) are rejected;
///  - the LHS contains NO collection metapattern anywhere (no AC-collection-nested redex);
///  - the `scope_var` is bound by a `Binder`/`MultiBinder` constructor position in the LHS —
///    i.e. `left` contains an `Apply { constructor: C, args: [Var(scope_var)] }` where `C` is a
///    `VariantKind::Binder`/`MultiBinder` of its category (resolved via
///    `collect_category_variants`). This yields `binder_label`/`binder_cat`/`binder_var_cat`/
///    `body_cat`/`multi`.
pub(crate) fn is_substitution_rewrite(
    language: &LanguageDef,
    rw: &RewriteRule,
) -> Option<SubstRewrite> {
    // Premises: congruence-only (same gate as the structural lowering).
    if !rw.premises.iter().all(premise_supported) {
        return None;
    }

    // RHS must be EXACTLY a top-level Subst/MultiSubst (not nested in Apply/Collection/Map/Zip).
    let AstPattern::Term(rhs_term) = &rw.right else {
        return None;
    };
    let (scope_pat, repl_pats): (&AstPattern, Vec<&AstPattern>) = match rhs_term {
        PatternTerm::MultiSubst { scope, replacements } => {
            (scope.as_ref(), replacements.iter().collect())
        },
        // Single `Subst { term, var, replacement }` is the 3-arg form; `term` is the scope body,
        // and `var`/`replacement` give a single (var ↦ replacement) pair. We accept only the
        // shape where `term` is a bare scope `Var` and there is one replacement, mirroring the
        // MultiSubst arity-1 case (the general 2-arg `(eval <var> <arg>)` always parses to a
        // MultiSubst; the 3-arg `Subst` is the legacy form).
        PatternTerm::Subst { term, replacement, .. } => {
            (term.as_ref(), vec![replacement.as_ref()])
        },
        _ => return None,
    };

    // Scope is a bare variable.
    let AstPattern::Term(PatternTerm::Var(scope_var)) = scope_pat else {
        return None;
    };

    // Every replacement is a plain `Var` (Map/Zip/Collection replacements rejected — this is what
    // excludes RhoCalc's `qs.*map(|q| (NQuote q))`).
    let mut repl_vars: Vec<Ident> = Vec::with_capacity(repl_pats.len());
    for rp in &repl_pats {
        match rp {
            AstPattern::Term(PatternTerm::Var(v)) => repl_vars.push(v.clone()),
            _ => return None,
        }
    }
    if repl_vars.is_empty() {
        return None;
    }

    // LHS must contain no collection metapattern anywhere (no AC-collection-nested redex).
    if pattern_contains_collection(&rw.left) {
        return None;
    }

    // `scope_var` must be bound by a `Binder`/`MultiBinder` constructor position in the LHS.
    let binder = find_binder_scope(language, &rw.left, scope_var)?;

    // The redex head: the outermost constructor of the LHS.
    let AstPattern::Term(PatternTerm::Apply { constructor: head_label, .. }) = &rw.left else {
        return None;
    };
    let head_cat = language.category_of_constructor(head_label)?.clone();

    Some(SubstRewrite {
        label: format!("{}::rewrite::{}", language.name, rw.name),
        left: rw.left.clone(),
        scope_var: scope_var.clone(),
        repl_vars,
        binder_label: binder.binder_label,
        binder_cat: binder.binder_cat,
        binder_var_cat: binder.binder_var_cat,
        body_cat: binder.body_cat,
        multi: binder.multi,
        head_label: head_label.clone(),
        head_cat,
    })
}

/// The binder constructor a scope variable is bound by, resolved from the LHS.
struct BinderScope {
    binder_label: Ident,
    binder_cat: Ident,
    binder_var_cat: Ident,
    body_cat: Ident,
    multi: bool,
}

/// Find the `Binder`/`MultiBinder` constructor that binds `scope_var` in `pattern` — an
/// `Apply { constructor: C, args: [Var(scope_var)] }` where `C` is a `VariantKind::Binder`/
/// `MultiBinder` of its category. Searches recursively through `Apply` argument positions (the
/// binder may be nested under the redex head, e.g. `(App (Lam fun) arg)`). Returns the binder's
/// label, its category, the bound-variable (domain) category, the body (codomain) category, and
/// whether it is a multi-binder.
fn find_binder_scope(
    language: &LanguageDef,
    pattern: &AstPattern,
    scope_var: &Ident,
) -> Option<BinderScope> {
    let AstPattern::Term(term) = pattern else {
        return None;
    };
    let PatternTerm::Apply { constructor, args } = term else {
        return None;
    };

    // Is THIS apply the binder binding `scope_var`? It must be a binder constructor whose sole
    // argument is exactly `Var(scope_var)`.
    if let [AstPattern::Term(PatternTerm::Var(v))] = args.as_slice() {
        if v == scope_var {
            if let Some(cat) = language.category_of_constructor(constructor) {
                for variant in collect_category_variants(cat, language) {
                    match variant {
                        VariantKind::Binder {
                            label,
                            binder_cat,
                            body_cat,
                            ..
                        } if &label == constructor => {
                            return Some(BinderScope {
                                binder_label: label,
                                binder_cat: cat.clone(),
                                binder_var_cat: binder_cat,
                                body_cat,
                                multi: false,
                            });
                        },
                        VariantKind::MultiBinder {
                            label,
                            binder_cat,
                            body_cat,
                            ..
                        } if &label == constructor => {
                            return Some(BinderScope {
                                binder_label: label,
                                binder_cat: cat.clone(),
                                binder_var_cat: binder_cat,
                                body_cat,
                                multi: true,
                            });
                        },
                        _ => {},
                    }
                }
            }
        }
    }

    // Otherwise recurse into the argument patterns.
    for arg in args {
        if let Some(found) = find_binder_scope(language, arg, scope_var) {
            return Some(found);
        }
    }
    None
}

/// Whether a pattern contains a `Pattern::Collection`/`Map`/`Zip` metapattern anywhere (used to
/// reject an AC-collection-nested substitution-rewrite LHS — MF4).
fn pattern_contains_collection(pattern: &AstPattern) -> bool {
    match pattern {
        AstPattern::Collection { .. } | AstPattern::Map { .. } | AstPattern::Zip { .. } => true,
        AstPattern::Term(term) => match term {
            PatternTerm::Apply { args, .. } => args.iter().any(pattern_contains_collection),
            PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                pattern_contains_collection(body)
            },
            PatternTerm::Subst { term, replacement, .. } => {
                pattern_contains_collection(term) || pattern_contains_collection(replacement)
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                pattern_contains_collection(scope)
                    || replacements.iter().any(pattern_contains_collection)
            },
            PatternTerm::Var(_) => false,
        },
    }
}

/// Whether any `PatternTerm::Subst`/`MultiSubst` appears anywhere in a pattern (recursing
/// through `Apply`/`Lambda`/`MultiLambda`/`Collection`/`Map`/`Zip` and the substitution
/// sub-patterns themselves). A substitution in a rewrite RHS means the language performs
/// β-style replacement, whose contractum is a NEW typed term that the runtime must
/// reconstruct from the e-graph — hence `dovetail_normal_term` is meaningful for it.
///
/// This is a self-contained structural detector for the MF7 gate; it deliberately does NOT
/// depend on E1's stricter `is_substitution_rewrite` shape-classifier (E1 is a separate
/// surface). Being more permissive here is safe: it can only enable `dovetail_normal_term`,
/// which is itself fail-closed (`Err` on a stuck reconstruction).
fn pattern_contains_substitution(pattern: &AstPattern) -> bool {
    match pattern {
        AstPattern::Term(term) => pattern_term_contains_substitution(term),
        AstPattern::Collection { elements, .. } => {
            elements.iter().any(pattern_contains_substitution)
        },
        AstPattern::Map { collection, body, .. } => {
            pattern_contains_substitution(collection) || pattern_contains_substitution(body)
        },
        AstPattern::Zip { first, second } => {
            pattern_contains_substitution(first) || pattern_contains_substitution(second)
        },
    }
}

fn pattern_term_contains_substitution(term: &PatternTerm) -> bool {
    match term {
        PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. } => true,
        PatternTerm::Apply { args, .. } => args.iter().any(pattern_contains_substitution),
        PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
            pattern_contains_substitution(body)
        },
        PatternTerm::Var(_) => false,
    }
}

/// Whether a generated language should also expose `dovetail_normal_term` (E2.2) — the method
/// that reduces a term to a typed Dovetail normal form and reconstructs it as a typed AST term
/// (rather than the `dovetail_report_for` report projection).
///
/// MF7 gate (generic; derived entirely from `LanguageDef` — no per-language hardcoding):
/// emit it iff the language
///   1. has a **substitution rewrite** (a rewrite whose RHS contains a `Subst`/`MultiSubst`),
///      i.e. it performs β-style replacement producing a fresh typed contractum; OR
///   2. has a **typed-path structural rewrite/equation** — a non-congruence rewrite, or any
///      equation (equations are structural rewrites the typed path turns into bidirectional
///      `RewriteRule`s); these can rewrite a term into a different typed normal form (e.g.
///      RhoCalc's `Comm`/`PNew` AC equations); OR
///   3. **declares a Rho/RhoMachine backend capability**. Raw `language!` codegen advertises
///      `NO_RUNTIME_BACKEND_CAPABILITIES` in metadata (backends are installed by runtime
///      wrappers, not the macro), so the closest `LanguageDef`-level signal is a `guards {
///      channels { … } }` block (channels + join patterns are the Rho-style COMM substrate).
///
/// A pure scalar-fold language (native-output folds only, no structural rewrites/equations, no
/// substitution, no channels — e.g. Calculator) satisfies none of these and is NOT given the
/// method. (Such a language also never reaches the typed-fold path at all — it stays on the
/// `EGraph<String>` path — so the gate is doubly fail-closed for it.)
pub(crate) fn needs_normal_term(language: &LanguageDef) -> bool {
    let has_substitution_rewrite = language
        .rewrites
        .iter()
        .any(|rw| pattern_contains_substitution(&rw.right));

    let has_structural_rewrite_or_equation = language
        .rewrites
        .iter()
        .any(|rw| !rw.is_congruence_rule())
        || !language.equations.is_empty();

    let declares_rho_backend = language
        .guard_config
        .as_ref()
        .and_then(|gc| gc.channels.as_ref())
        .is_some_and(|ch| !ch.channel_categories.is_empty() || !ch.join_patterns.is_empty());

    has_substitution_rewrite || has_structural_rewrite_or_equation || declares_rho_backend
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

/// (E1.4) The native-rule LHS pattern for a substitution rewrite, lowered over the typed op-enum.
///
/// The LHS is `rw.left` with the binder sub-pattern collapsed: the `Apply { constructor:
/// binder_label, args: [Var(scope_var)] }` node is replaced by a bare `Var(scope_var)`, so the
/// pattern variable `scope_var` binds the WHOLE binder e-class (the lowered binder node carries an
/// arity marker + body — two children — which a `Pattern::app(binder, [var])` would NOT match
/// positionally; binding the whole node is also exactly what the dispatch arm needs, since it
/// reconstructs `scope_var` back to the typed binder term and matches `binder_cat::binder_label`).
/// Every other position lowers via the ordinary [`pattern_to_dovetail`].
fn subst_rewrite_native_lhs(
    language: &LanguageDef,
    sr: &SubstRewrite,
    enum_id: &Ident,
) -> Result<TokenStream, String> {
    let collapsed = collapse_binder_scope(&sr.left, &sr.binder_label, &sr.scope_var);
    pattern_to_dovetail(language, &collapsed, Some(enum_id))
}

/// Replace the `Apply { constructor: binder_label, args: [Var(scope_var)] }` sub-pattern with a
/// bare `Var(scope_var)`, recursively. Pure structural rewrite of the metapattern (used only to
/// synthesize the native-rule LHS).
fn collapse_binder_scope(
    pattern: &AstPattern,
    binder_label: &Ident,
    scope_var: &Ident,
) -> AstPattern {
    match pattern {
        AstPattern::Term(PatternTerm::Apply { constructor, args }) => {
            // The binder node binding `scope_var` collapses to the scope variable itself.
            if constructor == binder_label {
                if let [AstPattern::Term(PatternTerm::Var(v))] = args.as_slice() {
                    if v == scope_var {
                        return AstPattern::Term(PatternTerm::Var(scope_var.clone()));
                    }
                }
            }
            let new_args = args
                .iter()
                .map(|a| collapse_binder_scope(a, binder_label, scope_var))
                .collect();
            AstPattern::Term(PatternTerm::Apply {
                constructor: constructor.clone(),
                args: new_args,
            })
        },
        // Substitution rewrites have no collection/map/zip/lambda LHS (rejected by the detector),
        // so every other node is returned unchanged.
        other => other.clone(),
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
    // (E1.3) A substitution rewrite is NOT a structural `RewriteRule` — it is lowered as a
    // native rule + dispatcher arm by `typed_report::generate_native_rules_and_dispatch`
    // (own op-id, own arm), so it must emit NOTHING here and add NOTHING to `unsupported`
    // (it is fully supported, just on the native lane). This branch is reached only on the
    // typed path (`enum_id.is_some()`); on the `EGraph<String>` path a substitution rewrite
    // never appears, because the language is routed to the typed path by
    // `needs_typed_dovetail_path`. (Gated on `enum_id.is_some()` defensively so the String
    // path's behavior is byte-identical.)
    if enum_id.is_some() && is_substitution_rewrite(language, rw).is_some() {
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

                let mut __derivations = Vec::new();
                let mut __completeness = ::dovetail::extract::ExtractionCompleteness::Complete;
                for __root in __roots {
                    let mut extractor =
                        ::dovetail::extract::Extractor::new(&eg, |_| ::rigail::TropicalWeight(0.0));
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
        assert!(tokens.contains("funded_best"));
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

    // ─── E2.2: `needs_normal_term` MF7 gating ───────────────────────────────────

    #[test]
    fn needs_normal_term_true_for_structural_rewrite() {
        // A language with a non-congruence structural rewrite (`A ~> B`) gets the method.
        let language = parse(
            r#"
                name: NntStructural,
                types { Expr }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                }
                equations {}
                rewrites { AToB . |- A ~> B ; }
            "#,
        );
        assert!(needs_normal_term(&language));
    }

    #[test]
    fn needs_normal_term_true_for_equation() {
        // A language with a (structural) equation gets the method even with no rewrites.
        let language = parse(
            r#"
                name: NntEquation,
                types { Expr }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                }
                equations { Swap . |- A = B ; }
                rewrites {}
            "#,
        );
        assert!(needs_normal_term(&language));
    }

    #[test]
    fn needs_normal_term_false_for_pure_scalar_fold() {
        // A pure scalar-fold language (a native-output `+`/`-` fold, no structural rewrites/
        // equations, no substitution, no channels) is NOT given `dovetail_normal_term`.
        let language = parse(
            r#"
                name: NntPureScalar,
                types { ![i32] as Int }
                terms {
                    AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
                    SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
                }
            "#,
        );
        assert!(!needs_normal_term(&language));
        // It also never reaches the typed-fold path (native output stays on the String path),
        // so the method is doubly excluded for it.
        assert!(!needs_typed_fold_path(&language));
    }

    #[test]
    fn needs_normal_term_true_for_substitution_rewrite() {
        // A β-style substitution in a rewrite RHS (`(eval fun arg)` parses to a `MultiSubst`)
        // triggers the gate. This is independent of E1's stricter `is_substitution_rewrite`
        // shape classifier — being permissive here is sound (it can only enable a fail-closed
        // method). Mirrors the Lambda `Beta` rule.
        let language = parse(
            r#"
                name: NntBeta,
                types { Term }
                terms {
                    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
                }
                equations {}
                rewrites {
                    Beta . |- (App (Lam fun) arg) ~> (eval fun arg);
                    AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
                }
            "#,
        );
        assert!(
            needs_normal_term(&language),
            "a MultiSubst in the rewrite RHS must trigger needs_normal_term"
        );
    }

    // ─── E1.2: `is_substitution_rewrite` shape classifier (MF4) ─────────────────────────────

    /// Find a rewrite by name in a parsed language.
    fn rewrite<'a>(language: &'a LanguageDef, name: &str) -> &'a RewriteRule {
        language
            .rewrites
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("rewrite `{name}` not found"))
    }

    /// The Lambda `Beta` rule — `(App (Lam fun) arg) ~> (eval fun arg)` — is detected, with all
    /// `SubstRewrite` fields derived from `LanguageDef` (single binder `[Term->Term]`).
    #[test]
    fn is_substitution_rewrite_detects_lambda_beta() {
        let language = parse(
            r#"
                name: Lam,
                types { Term }
                terms {
                    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
                }
                equations {}
                rewrites {
                    Beta . |- (App (Lam fun) arg) ~> (eval fun arg);
                    AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
                }
            "#,
        );
        let sr = is_substitution_rewrite(&language, rewrite(&language, "Beta"))
            .expect("Beta must be detected as a substitution rewrite");
        assert_eq!(sr.scope_var.to_string(), "fun");
        assert_eq!(sr.repl_vars.iter().map(|v| v.to_string()).collect::<Vec<_>>(), vec!["arg"]);
        assert_eq!(sr.binder_label.to_string(), "Lam");
        assert_eq!(sr.binder_cat.to_string(), "Term");
        assert_eq!(sr.binder_var_cat.to_string(), "Term");
        assert_eq!(sr.body_cat.to_string(), "Term");
        assert!(!sr.multi, "Lam is a single binder");
        assert_eq!(sr.head_label.to_string(), "App");
        assert_eq!(sr.head_cat.to_string(), "Term");

        // The congruence rule is NOT a substitution rewrite.
        assert!(is_substitution_rewrite(&language, rewrite(&language, "AppCongL")).is_none());

        // And it routes the language to the typed path.
        assert!(needs_typed_dovetail_path(&language));
    }

    /// (MF4 — the crux negative) RhoCalc's `Comm` is NOT a substitution rewrite: its RHS nests
    /// the `MultiSubst` inside an AC `PPar` collection, AND the replacement is a `*map(..)`
    /// comprehension (a `Pattern::Map`), AND the LHS is AC-collection-nested. ANY of these must
    /// reject it; this exercises all three guards together on the real `Comm` shape.
    #[test]
    fn is_substitution_rewrite_rejects_rhocalc_comm() {
        let language = parse(
            r#"
                name: RhoCalcSubset,
                types {
                    Name
                    Proc
                }
                terms {
                    PZero . Proc ::= "0" ;
                    NQuote . p:Proc |- "@" p : Name ;
                    POutput . n:Name, q:Proc |- n "!(" q ")" : Proc ;
                    PInputs . ^[xs].cont:[Name -> Proc] |- "for(" xs ")" "{" cont "}" : Proc ;
                    PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                }
                equations {}
                rewrites {
                    Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
                        ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
                }
            "#,
        );
        assert!(
            is_substitution_rewrite(&language, rewrite(&language, "Comm")).is_none(),
            "RhoCalc Comm (MultiSubst nested in AC PPar, Map replacement, AC-nested LHS) must NOT \
             be detected as a substitution rewrite"
        );
    }

    /// A rewrite whose substitution is NESTED inside another `Apply` (not the whole RHS) is
    /// rejected — the substitution must be the entire RHS.
    #[test]
    fn is_substitution_rewrite_rejects_nested_subst_rhs() {
        let language = parse(
            r#"
                name: NestedSubst,
                types { Term }
                terms {
                    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
                    Wrap . t:Term |- "wrap(" t ")" : Term;
                }
                equations {}
                rewrites {
                    BadBeta . |- (App (Lam fun) arg) ~> (Wrap (eval fun arg));
                }
            "#,
        );
        assert!(
            is_substitution_rewrite(&language, rewrite(&language, "BadBeta")).is_none(),
            "a MultiSubst nested under `Wrap` is not a whole-RHS substitution"
        );
    }

    /// A rewrite whose scope variable is NOT bound by a binder constructor in the LHS is
    /// rejected (no `Binder`/`MultiBinder` position binds `fun`).
    #[test]
    fn is_substitution_rewrite_rejects_non_binder_scope() {
        let language = parse(
            r#"
                name: NoBinderScope,
                types { Term }
                terms {
                    Pair . l:Term, r:Term |- "<" l "," r ">" : Term;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
                }
                equations {}
                rewrites {
                    BadBeta . |- (App (Pair fun other) arg) ~> (eval fun arg);
                }
            "#,
        );
        assert!(
            is_substitution_rewrite(&language, rewrite(&language, "BadBeta")).is_none(),
            "`Pair` is not a binder, so `fun` is not bound by a binder position"
        );
    }

    /// (Generality) A CROSS-category binder `[Name -> Proc]` is detected with the bound-variable
    /// category (`Name`) tracked SEPARATELY from the body category (`Proc`). This is what makes
    /// the generated dispatcher select the cross-category `substitute_name` (not
    /// `substitute_proc`) — the substitution lowering is not limited to same-category binders.
    /// (End-to-end reduction of a synthetic language is covered by the Lambda gates; a test-local
    /// `language!` is infeasible here because the macro writes crate-coupled `simulate_<lang>.rs`
    /// + `gen_<lang>_*.rs` files referencing `mettail_languages::<lang>`.)
    #[test]
    fn is_substitution_rewrite_tracks_cross_category_binder() {
        let language = parse(
            r#"
                name: CrossCat,
                types {
                    Name
                    Proc
                }
                terms {
                    NVar . n:Name |- "@" n : Proc;
                    Bind . ^x.body:[Name -> Proc] |- "bind " x "." body : Proc;
                    Send . k:Proc, arg:Name |- "send(" k "," arg ")" : Proc;
                }
                equations {}
                rewrites {
                    Deliver . |- (Send (Bind k) a) ~> (eval k a);
                }
            "#,
        );
        let sr = is_substitution_rewrite(&language, rewrite(&language, "Deliver"))
            .expect("Deliver must be detected (cross-category binder)");
        assert_eq!(sr.scope_var.to_string(), "k");
        assert_eq!(sr.binder_label.to_string(), "Bind");
        assert_eq!(sr.binder_cat.to_string(), "Proc", "Bind constructs a Proc");
        assert_eq!(sr.binder_var_cat.to_string(), "Name", "the bound variable is a Name");
        assert_eq!(sr.body_cat.to_string(), "Proc", "the body is a Proc");
        assert_ne!(
            sr.binder_var_cat.to_string(),
            sr.body_cat.to_string(),
            "cross-category: bound-variable category differs from body category — the dispatcher \
             must select `substitute_name`, not `substitute_proc`"
        );
        assert_eq!(sr.repl_vars.iter().map(|v| v.to_string()).collect::<Vec<_>>(), vec!["a"]);
        assert_eq!(sr.head_label.to_string(), "Send");
    }
}
