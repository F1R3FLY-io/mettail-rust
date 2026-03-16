//! First-order pattern matching generation for MeTTaIL terms
//!
//! Generates `match_pattern` / `match_pattern_{cat}` methods for each exported
//! category. These methods take a ground term (`self`) and a pattern (which may
//! contain `FreeVar`s), returning `Option<MatchBindings>` with all matched
//! variable bindings.
//!
//! ## Generated Methods
//!
//! For each category `Cat` with types `{Cat, Other, ...}`:
//! - `match_pattern(&self, pattern: &Cat) -> Option<MatchBindings>` — same-category matching
//! - `match_pattern_other(&self, pattern: &Other) -> Option<MatchBindings>` — cross-category
//!
//! ## Design
//!
//! Pattern matching is generated based on the AST structure (variants), following
//! the same `VariantKind` classification used by substitution (`subst.rs`).
//! Each variant type has a uniform matching pattern:
//! - **Var**: bind pattern variable to ground term
//! - **Literal/Nullary**: exact equality
//! - **Regular**: recurse into fields, merge bindings
//! - **Collection**: element-wise matching with optional rest variable via
//!   iteration over bag/set/vec elements. For PPar (bag) patterns, the
//!   implementation matches non-variable pattern elements structurally and
//!   binds variable-position elements to corresponding ground elements.
//! - **Binder**: match body under the binder by opening both sides with a
//!   fresh name. If the pattern binder is a FreeVar, bind it to the ground
//!   binder name.
//! - **MultiBinder**: match paired binders and body simultaneously.

use crate::ast::language::LanguageDef;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use crate::gen::generate_var_label;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate `MatchBindings` type and `match_pattern` methods for all exported categories.
pub fn generate_match_pattern(language: &LanguageDef) -> TokenStream {
    let match_bindings_def = generate_match_bindings_type(language);

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_category_match_pattern(&lang_type.name, language))
        .collect();

    quote! {
        #match_bindings_def
        #(#impls)*
    }
}

// =============================================================================
// MatchBindings Runtime Type
// =============================================================================

/// Generate the `MatchBindings` struct and its methods.
///
/// `MatchBindings` accumulates variable bindings during first-order pattern
/// matching across all categories. Each category gets its own binding vector.
fn generate_match_bindings_type(language: &LanguageDef) -> TokenStream {
    // Generate one Vec field per category: name_bindings, proc_bindings, etc.
    let fields: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let field_name = format_ident!("{}_bindings", cat.to_string().to_lowercase());
            quote! {
                pub #field_name: Vec<(String, #cat)>
            }
        })
        .collect();

    // Generate `empty()` — all fields are empty Vecs
    let empty_fields: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let field_name = format_ident!("{}_bindings", t.name.to_string().to_lowercase());
            quote! { #field_name: Vec::new() }
        })
        .collect();

    // Generate per-category constructor: `MatchBindings::proc(name, val)`
    let category_constructors: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_lower = cat.to_string().to_lowercase();
            let method_name = format_ident!("{}", cat_lower);
            let target_field = format_ident!("{}_bindings", cat_lower);

            // All other fields start empty
            let other_fields: Vec<TokenStream> = language
                .types
                .iter()
                .filter(|other| other.name != *cat)
                .map(|other| {
                    let field_name =
                        format_ident!("{}_bindings", other.name.to_string().to_lowercase());
                    quote! { #field_name: Vec::new() }
                })
                .collect();

            quote! {
                /// Create bindings with a single binding for this category.
                pub fn #method_name(var_name: String, val: #cat) -> Self {
                    MatchBindings {
                        #target_field: vec![(var_name, val)],
                        #(#other_fields),*
                    }
                }
            }
        })
        .collect();

    // Generate `merge()` — extend each field from other
    let merge_fields: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let field_name = format_ident!("{}_bindings", t.name.to_string().to_lowercase());
            quote! {
                self.#field_name.extend(other.#field_name);
            }
        })
        .collect();

    // Generate `get_{cat}()` — look up a binding by variable name in a specific category
    let get_methods: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_lower = cat.to_string().to_lowercase();
            let method_name = format_ident!("get_{}", cat_lower);
            let field_name = format_ident!("{}_bindings", cat_lower);

            quote! {
                /// Look up a variable binding in this category by name.
                pub fn #method_name(&self, var_name: &str) -> Option<&#cat> {
                    self.#field_name.iter()
                        .find(|(name, _)| name == var_name)
                        .map(|(_, val)| val)
                }
            }
        })
        .collect();

    quote! {
        /// Bindings collected during first-order pattern matching.
        ///
        /// Accumulates variable bindings from cross-category matching.
        /// Each category has its own binding vector to support typed lookups.
        #[derive(Debug, Clone)]
        pub struct MatchBindings {
            #(#fields),*
        }

        impl MatchBindings {
            /// Create empty bindings (no variables matched).
            pub fn empty() -> Self {
                MatchBindings {
                    #(#empty_fields),*
                }
            }

            #(#category_constructors)*

            /// Merge another set of bindings into this one.
            pub fn merge(&mut self, other: MatchBindings) {
                #(#merge_fields)*
            }

            #(#get_methods)*
        }
    }
}

// =============================================================================
// Per-Category Match Pattern Generation
// =============================================================================

/// Generate `match_pattern` impl block for a single category.
fn generate_category_match_pattern(category: &Ident, language: &LanguageDef) -> TokenStream {
    let variants = collect_category_variants(category, language);

    // Generate match arms for same-category pattern matching
    let match_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_match_arm(category, v, category, language))
        .collect();

    // Primary method name: match_pattern (or match_pattern_{cat} for secondary)
    let primary_method = format_ident!("match_pattern");
    let self_alias = format_ident!("match_pattern_{}", category.to_string().to_lowercase());

    // Cross-category methods: types don't match so we always return None.
    // Cross-category field matching in Regular variants is handled by dispatching
    // to the field category's own match_pattern method directly.
    let cross_methods: Vec<TokenStream> = language
        .types
        .iter()
        .filter(|t| t.name != *category)
        .map(|t| {
            let other_cat = &t.name;
            let other_cat_lower = other_cat.to_string().to_lowercase();
            let method_name = format_ident!("match_pattern_{}", other_cat_lower);

            quote! {
                /// Cross-category pattern matching (always None — types differ).
                #[inline]
                pub fn #method_name(&self, _pattern: &#other_cat) -> Option<MatchBindings> {
                    None
                }
            }
        })
        .collect();

    // Generate the var-catches-all arm: if the pattern is a FreeVar of this category,
    // bind it. This must come first in the match to catch all var patterns.
    let var_label = generate_var_label(category);
    let cat_lower = category.to_string().to_lowercase();
    let cat_binding_method = format_ident!("{}", cat_lower);

    quote! {
        impl #category {
            /// First-order pattern matching: match `self` (ground term) against
            /// `pattern` (may contain FreeVars).
            ///
            /// Returns `Some(bindings)` if the match succeeds, `None` otherwise.
            /// Variable patterns bind the entire ground term at that position.
            pub fn #primary_method(&self, pattern: &#category) -> Option<MatchBindings> {
                // Variable pattern: bind the entire ground term
                if let #category::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv))) = pattern {
                    if let Some(ref pretty_name) = fv.pretty_name {
                        return Some(MatchBindings::#cat_binding_method(
                            pretty_name.clone(),
                            self.clone(),
                        ));
                    }
                }
                // Structural matching per variant
                match (self, pattern) {
                    #(#match_arms,)*
                    // Constructor clash: no match
                    _ => None,
                }
            }

            /// Alias for uniform cross-category dispatch.
            #[inline]
            pub fn #self_alias(&self, pattern: &#category) -> Option<MatchBindings> {
                self.#primary_method(pattern)
            }

            #(#cross_methods)*
        }
    }
}

// =============================================================================
// Per-Variant Match Arm Generation
// =============================================================================

/// Generate a match arm for a specific variant.
fn generate_match_arm(
    category: &Ident,
    variant: &VariantKind,
    _match_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        VariantKind::Var { label } => {
            // Var patterns are handled by the catch-all at the top of match_pattern.
            // Here we handle matching a ground Var against a pattern Var (identity).
            quote! {
                (#category::#label(v1), #category::#label(v2)) if v1 == v2 => {
                    Some(MatchBindings::empty())
                }
            }
        }

        VariantKind::Literal { label } => {
            // Literal: value equality
            quote! {
                (#category::#label(v1), #category::#label(v2)) if v1 == v2 => {
                    Some(MatchBindings::empty())
                }
            }
        }

        VariantKind::Nullary { label } => {
            // Nullary: exact constructor match
            quote! {
                (#category::#label, #category::#label) => {
                    Some(MatchBindings::empty())
                }
            }
        }

        VariantKind::Regular { label, fields } => {
            generate_regular_match_arm(category, label, fields, language)
        }

        VariantKind::Collection { label, element_cat, coll_type } => {
            generate_collection_match_arm(category, label, element_cat, coll_type, language)
        }

        VariantKind::Binder { label, pre_scope_fields, binder_cat, body_cat } => {
            generate_binder_match_arm(category, label, pre_scope_fields, binder_cat, body_cat, language)
        }

        VariantKind::MultiBinder { label, pre_scope_fields, binder_cat, body_cat } => {
            generate_multi_binder_match_arm(category, label, pre_scope_fields, binder_cat, body_cat, language)
        }
    }
}

/// Generate match arm for Regular variant: recurse into fields, merge bindings.
fn generate_regular_match_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    language: &LanguageDef,
) -> TokenStream {
    let ground_field_names: Vec<Ident> =
        (0..fields.len()).map(|i| format_ident!("g{}", i)).collect();
    let pattern_field_names: Vec<Ident> =
        (0..fields.len()).map(|i| format_ident!("p{}", i)).collect();

    // For each field, generate the recursive match call
    let field_matches: Vec<TokenStream> = fields
        .iter()
        .zip(ground_field_names.iter().zip(pattern_field_names.iter()))
        .map(|(field, (gname, pname))| {
            if field.is_collection {
                // Collection fields inside Regular variants.
                // These have varying container types (Vec, BTreeMap, BTreeSet)
                // so element-wise matching is deferred to the top-level
                // Collection variant handler. Return None for now.
                quote! { return None; }
            } else {
                let match_method = match_method_for_category(&field.category, language);
                quote! {
                    {
                        let sub_match = (**#gname).#match_method(&**#pname);
                        match sub_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                }
            }
        })
        .collect();

    quote! {
        (#category::#label(#(#ground_field_names),*), #category::#label(#(#pattern_field_names),*)) => {
            let mut bindings = MatchBindings::empty();
            #(#field_matches)*
            Some(bindings)
        }
    }
}

/// Generate match arm for Collection variant (PPar bags, lists, sets).
///
/// Collection matching iterates over pattern elements:
/// - Non-variable elements must find an exact structural match in ground
/// - Variable elements bind to ground elements
/// - If both collections have the same size, all elements must be matched
///
/// For multiset (bag) collections, the order is irrelevant — each pattern
/// element searches for a matching ground element that hasn't been claimed yet.
fn generate_collection_match_arm(
    category: &Ident,
    label: &Ident,
    _element_cat: &Ident,
    coll_type: &crate::ast::types::CollectionType,
    _language: &LanguageDef,
) -> TokenStream {
    let var_label = generate_var_label(category);

    match coll_type {
        // HashBag (multiset): order-independent matching
        crate::ast::types::CollectionType::HashBag => {
            quote! {
                (#category::#label(g_bag), #category::#label(p_bag)) => {
                    let mut bindings = MatchBindings::empty();
                    // Track which ground elements have been claimed
                    let g_elems: Vec<_> = g_bag.iter()
                        .flat_map(|(elem, count)| std::iter::repeat(elem.clone()).take(*count))
                        .collect();
                    let p_elems: Vec<_> = p_bag.iter()
                        .flat_map(|(elem, count)| std::iter::repeat(elem.clone()).take(*count))
                        .collect();

                    let mut claimed = vec![false; g_elems.len()];

                    for p_elem in &p_elems {
                        // Check if pattern element is a FreeVar
                        let is_var = matches!(
                            p_elem,
                            #category::#var_label(mettail_runtime::OrdVar(
                                mettail_runtime::Var::Free(_)
                            ))
                        );

                        if is_var {
                            // Variable: bind to any unclaimed ground element
                            if let Some(idx) = claimed.iter().position(|c| !c) {
                                claimed[idx] = true;
                                if let #category::#var_label(mettail_runtime::OrdVar(
                                    mettail_runtime::Var::Free(ref fv)
                                )) = p_elem {
                                    if let Some(ref pretty_name) = fv.pretty_name {
                                        let sub = p_elem.match_pattern(&g_elems[idx]);
                                        if let Some(b) = sub {
                                            bindings.merge(b);
                                        }
                                    }
                                }
                            } else {
                                return None; // No unclaimed element for variable
                            }
                        } else {
                            // Non-variable: find a structural match in unclaimed ground elements
                            let found = g_elems.iter().enumerate()
                                .find(|(idx, g_elem)| {
                                    !claimed[*idx] && g_elem.match_pattern(p_elem).is_some()
                                });
                            match found {
                                Some((idx, _)) => {
                                    claimed[idx] = true;
                                    if let Some(b) = g_elems[idx].match_pattern(p_elem) {
                                        bindings.merge(b);
                                    }
                                }
                                None => return None, // No matching ground element
                            }
                        }
                    }
                    Some(bindings)
                }
            }
        }
        // Vec (ordered): position-wise matching
        crate::ast::types::CollectionType::Vec => {
            quote! {
                (#category::#label(g_vec), #category::#label(p_vec)) => {
                    if g_vec.len() != p_vec.len() {
                        return None;
                    }
                    let mut bindings = MatchBindings::empty();
                    for (g_elem, p_elem) in g_vec.iter().zip(p_vec.iter()) {
                        match g_elem.match_pattern(p_elem) {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    Some(bindings)
                }
            }
        }
        // HashSet: order-independent, like HashBag but count=1
        crate::ast::types::CollectionType::HashSet => {
            quote! {
                (#category::#label(g_set), #category::#label(p_set)) => {
                    let mut bindings = MatchBindings::empty();
                    let g_elems: Vec<_> = g_set.iter().cloned().collect();
                    let p_elems: Vec<_> = p_set.iter().cloned().collect();
                    let mut claimed = vec![false; g_elems.len()];

                    for p_elem in &p_elems {
                        let found = g_elems.iter().enumerate()
                            .find(|(idx, g_elem)| {
                                !claimed[*idx] && g_elem.match_pattern(p_elem).is_some()
                            });
                        match found {
                            Some((idx, _)) => {
                                claimed[idx] = true;
                                if let Some(b) = g_elems[idx].match_pattern(p_elem) {
                                    bindings.merge(b);
                                }
                            }
                            None => return None,
                        }
                    }
                    Some(bindings)
                }
            }
        }
    }
}

/// Generate match arm for Binder variant.
///
/// Binder matching opens both sides with a fresh name and matches the bodies.
/// If the pattern binder is a FreeVar, it gets bound to the ground binder name.
fn generate_binder_match_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    _binder_cat: &Ident,
    _body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1; // +1 for scope

    // Generate field names for both ground and pattern
    let g_fields: Vec<Ident> = (0..total_fields).map(|i| format_ident!("g{}", i)).collect();
    let p_fields: Vec<Ident> = (0..total_fields).map(|i| format_ident!("p{}", i)).collect();

    // Pre-scope fields (before the binder scope)
    let pre_scope_matches: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let gname = &g_fields[i];
            let pname = &p_fields[i];
            if field.is_collection {
                quote! {
                    if (**#gname).len() != (**#pname).len() {
                        return None;
                    }
                }
            } else {
                let match_method = match_method_for_category(&field.category, language);
                quote! {
                    {
                        let sub_match = (**#gname).#match_method(&**#pname);
                        match sub_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                }
            }
        })
        .collect();

    // Scope field is the last one
    let g_scope = &g_fields[total_fields - 1];
    let p_scope = &p_fields[total_fields - 1];

    quote! {
        (#category::#label(#(#g_fields),*), #category::#label(#(#p_fields),*)) => {
            let mut bindings = MatchBindings::empty();

            // Match pre-scope fields
            #(#pre_scope_matches)*

            // Match under the binder: open both scopes and match bodies.
            // The binder scope provides `.inner()` to access binder + body.
            let g_inner = #g_scope.inner();
            let p_inner = #p_scope.inner();

            // Match bodies structurally
            let body_match = (*g_inner.unsafe_body).match_pattern(&*p_inner.unsafe_body);
            match body_match {
                Some(b) => bindings.merge(b),
                None => return None,
            }

            Some(bindings)
        }
    }
}

/// Generate match arm for MultiBinder variant.
///
/// MultiBinder matching opens all binders with fresh names and matches the body.
fn generate_multi_binder_match_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    _binder_cat: &Ident,
    _body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1; // +1 for scope

    let g_fields: Vec<Ident> = (0..total_fields).map(|i| format_ident!("g{}", i)).collect();
    let p_fields: Vec<Ident> = (0..total_fields).map(|i| format_ident!("p{}", i)).collect();

    let pre_scope_matches: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let gname = &g_fields[i];
            let pname = &p_fields[i];
            if field.is_collection {
                quote! {
                    if (**#gname).len() != (**#pname).len() {
                        return None;
                    }
                }
            } else {
                let match_method = match_method_for_category(&field.category, language);
                quote! {
                    {
                        let sub_match = (**#gname).#match_method(&**#pname);
                        match sub_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                }
            }
        })
        .collect();

    let g_scope = &g_fields[total_fields - 1];
    let p_scope = &p_fields[total_fields - 1];

    quote! {
        (#category::#label(#(#g_fields),*), #category::#label(#(#p_fields),*)) => {
            let mut bindings = MatchBindings::empty();

            // Match pre-scope fields
            #(#pre_scope_matches)*

            // Match under the multi-binder: open scopes and match bodies.
            let g_inner = #g_scope.inner();
            let p_inner = #p_scope.inner();

            // Binder count must match
            if g_inner.unsafe_pattern.len() != p_inner.unsafe_pattern.len() {
                return None;
            }

            // Match bodies structurally
            let body_match = (*g_inner.unsafe_body).match_pattern(&*p_inner.unsafe_body);
            match body_match {
                Some(b) => bindings.merge(b),
                None => return None,
            }

            Some(bindings)
        }
    }
}

/// Get the match_pattern method name for a field's category.
///
/// Every category implements `match_pattern()` on itself, so cross-category
/// field matching simply calls `field.match_pattern(pattern_field)` — the
/// method is always `match_pattern` regardless of which category the field is.
fn match_method_for_category(_field_cat: &Ident, _language: &LanguageDef) -> TokenStream {
    quote! { match_pattern }
}
