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
//! ## Architecture: Iterative Work Stack
//!
//! Pattern matching uses an explicit work stack (`Vec<MatchTask>`) instead of
//! recursive function calls. This mirrors the trampoline parser design and
//! provides stack safety for arbitrarily deep terms (100K+ nesting depth).
//!
//! The `MatchTask` enum is a heterogeneous work item with one variant per
//! category (`MatchProc(Proc, Proc)`, `MatchName(Name, Name)`, etc.). When
//! processing a Regular variant with cross-category fields, the handler pushes
//! `MatchTask::MatchOtherCat(ground_field, pattern_field)` onto the stack.
//!
//! Thread-local pooling (`Cell<Vec<MatchTask>>`) ensures zero allocation in
//! steady state. Re-entrant calls from Collection matching get fresh vectors;
//! the outermost call retains its pool capacity.
//!
//! ## Variant Matching Strategies
//!
//! - **Var**: bind pattern variable to ground term (immediate, no stack push)
//! - **Literal/Nullary**: exact equality (immediate)
//! - **Regular**: push `MatchTask` for each field onto the work stack
//! - **Collection**: inline element-wise matching; each element's `match_pattern`
//!   call re-enters the iterative engine via TLS (bounded by collection size)
//! - **Binder/MultiBinder**: inline scope opening; body `match_pattern` call
//!   re-enters the iterative engine (one re-entry per binder level)

use crate::ast::language::LanguageDef;
use crate::gen::generate_var_label;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate `MatchBindings` type, `MatchTask` enum, TLS pool, iterative engine,
/// and `match_pattern` methods for all exported categories.
pub fn generate_match_pattern(language: &LanguageDef) -> TokenStream {
    let match_bindings_def = generate_match_bindings_type(language);
    let match_task_enum = generate_match_task_enum(language);
    let iterative_engine = generate_iterative_engine(language);

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_category_match_pattern(&lang_type.name, language))
        .collect();

    quote! {
        #match_bindings_def
        #match_task_enum
        #iterative_engine
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
// MatchTask Enum + TLS Pool
// =============================================================================

/// Generate the `MatchTask` enum and thread-local pool.
///
/// `MatchTask` has one variant per category: `MatchProc(Proc, Proc)`,
/// `MatchName(Name, Name)`, etc. This enables the iterative engine to handle
/// cross-category recursion (Proc → Name → Proc) via a single heterogeneous
/// work stack.
fn generate_match_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Match{}", cat);
            quote! {
                /// Match a #cat ground term against a #cat pattern.
                #variant_name(#cat, #cat)
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative match_pattern engine.
        ///
        /// Each variant wraps a `(ground, pattern)` pair for one category.
        /// The iterative engine pops tasks from a `Vec<MatchTask>` work stack,
        /// processes each one (binding variables, checking equality, or pushing
        /// sub-field tasks), and accumulates bindings until the stack is empty
        /// (success) or a constructor clash is detected (failure).
        #[allow(dead_code)]
        enum MatchTask {
            #(#variants),*
        }

        thread_local! {
            /// Pool for reusing `MatchTask` work stacks across calls.
            ///
            /// The `Cell<Vec<MatchTask>>` pattern allows zero-allocation
            /// steady-state operation: the first call allocates, subsequent
            /// calls reuse the same buffer. Re-entrant calls (from Collection
            /// matching) get fresh vectors; the outermost call retains capacity.
            static MATCH_TASK_POOL: std::cell::Cell<Vec<MatchTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Iterative Engine
// =============================================================================

/// Generate the `match_pattern_iterative` function.
///
/// This function processes the `Vec<MatchTask>` work stack until either:
/// - The stack is empty → return `Some(bindings)` (match succeeded)
/// - A constructor clash is detected → return `None` (match failed)
///
/// For Regular variants, sub-field matching pushes new `MatchTask` entries.
/// For Collection/Binder variants, the handler is inline and calls
/// `match_pattern()` for element/body sub-matches (re-entering the engine
/// via TLS — bounded by collection size, not nesting depth).
fn generate_iterative_engine(language: &LanguageDef) -> TokenStream {
    let category_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_iterative_category_arm(&lang_type.name, language))
        .collect();

    quote! {
        /// Iterative match pattern engine.
        ///
        /// Processes the work stack until empty (success) or a constructor
        /// clash is detected (failure). Stack-safe for arbitrarily deep terms.
        #[allow(dead_code)]
        fn match_pattern_iterative(
            stack: &mut Vec<MatchTask>,
        ) -> Option<MatchBindings> {
            let mut bindings = MatchBindings::empty();

            while let Some(task) = stack.pop() {
                match task {
                    #(#category_arms)*
                }
            }

            Some(bindings)
        }
    }
}

/// Generate the match arm for one category inside the iterative engine.
///
/// Structure:
/// ```rust,ignore
/// MatchTask::MatchProc(ground, pattern) => {
///     // 1. Variable check: if pattern is FreeVar, bind and continue
///     // 2. Constructor match: switch on (ground, pattern) variants
///     //    - Var/Literal/Nullary: equality check
///     //    - Regular: push sub-field tasks
///     //    - Collection: inline matching with re-entrant match_pattern calls
///     //    - Binder: inline scope open with re-entrant body match_pattern call
///     //    - Constructor clash: return None
/// }
/// ```
fn generate_iterative_category_arm(category: &Ident, language: &LanguageDef) -> TokenStream {
    let variant_name = format_ident!("Match{}", category);
    let var_label = generate_var_label(category);
    let cat_lower = category.to_string().to_lowercase();
    let cat_binding_method = format_ident!("{}", cat_lower);

    let variants = collect_category_variants(category, language);

    let variant_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_iterative_variant_arm(category, v, language))
        .collect();

    quote! {
        MatchTask::#variant_name(ground, pattern) => {
            // Variable pattern: bind the entire ground term
            if let #category::#var_label(mettail_runtime::OrdVar(
                mettail_runtime::Var::Free(ref fv)
            )) = pattern {
                if let Some(ref pretty_name) = fv.pretty_name {
                    bindings.merge(MatchBindings::#cat_binding_method(
                        pretty_name.clone(),
                        ground.clone(),
                    ));
                    continue;
                }
            }
            // Structural matching per variant
            match (&ground, &pattern) {
                #(#variant_arms,)*
                // Constructor clash: no match
                _ => return None,
            }
        }
    }
}

/// Generate a match arm for a specific variant inside the iterative engine.
fn generate_iterative_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        VariantKind::Var { label } => {
            // Var identity: ground Var == pattern Var
            quote! {
                (#category::#label(v1), #category::#label(v2)) if v1 == v2 => {}
            }
        }

        VariantKind::Literal { label } => {
            quote! {
                (#category::#label(v1), #category::#label(v2)) if v1 == v2 => {}
            }
        }

        VariantKind::Nullary { label } => {
            quote! {
                (#category::#label, #category::#label) => {}
            }
        }

        VariantKind::Regular { label, fields } => {
            generate_iterative_regular_arm(category, label, fields, language)
        }

        VariantKind::Collection { label, element_cat, coll_type } => {
            // Collection matching is inline — calls match_pattern() on elements
            // which re-enters the iterative engine (bounded by element count).
            generate_collection_match_arm(category, label, element_cat, coll_type, language)
        }

        VariantKind::Binder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => {
            // Binder matching is inline — calls match_pattern() on body
            // which re-enters the iterative engine (one re-entry per binder).
            generate_binder_match_arm_inline(
                category,
                label,
                pre_scope_fields,
                binder_cat,
                body_cat,
                language,
            )
        }

        VariantKind::MultiBinder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => {
            generate_multi_binder_match_arm_inline(
                category,
                label,
                pre_scope_fields,
                binder_cat,
                body_cat,
                language,
            )
        }
    }
}

/// Generate match arm for Regular variant in the iterative engine.
///
/// Instead of recursive calls, pushes `MatchTask` for each field.
/// Fields are pushed in reverse order so they are processed left-to-right
/// (stack is LIFO).
fn generate_iterative_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    _language: &LanguageDef,
) -> TokenStream {
    // If any field is a collection, return None (same as before).
    if fields.iter().any(|f| f.is_collection) {
        let wildcards: Vec<TokenStream> = (0..fields.len()).map(|_| quote! { _ }).collect();
        return quote! {
            (#category::#label(#(#wildcards),*), #category::#label(#(#wildcards),*)) => {
                return None
            }
        };
    }

    let ground_field_names: Vec<Ident> =
        (0..fields.len()).map(|i| format_ident!("g{}", i)).collect();
    let pattern_field_names: Vec<Ident> =
        (0..fields.len()).map(|i| format_ident!("p{}", i)).collect();

    // Push sub-field tasks in REVERSE order (stack is LIFO, we want left-to-right)
    let field_pushes: Vec<TokenStream> = fields
        .iter()
        .zip(ground_field_names.iter().zip(pattern_field_names.iter()))
        .rev() // reverse for correct processing order
        .map(|(field, (gname, pname))| {
            let task_variant = format_ident!("Match{}", field.category);
            quote! {
                stack.push(MatchTask::#task_variant(
                    (**#gname).clone(),
                    (**#pname).clone(),
                ));
            }
        })
        .collect();

    quote! {
        (#category::#label(#(#ground_field_names),*), #category::#label(#(#pattern_field_names),*)) => {
            #(#field_pushes)*
        }
    }
}

/// Generate inline Collection match arm for the iterative engine.
///
/// Collection matching calls `match_pattern()` on elements, which re-enters
/// the iterative engine via TLS. This is bounded by collection size.
fn generate_collection_match_arm(
    category: &Ident,
    label: &Ident,
    _element_cat: &Ident,
    coll_type: &crate::ast::types::CollectionType,
    _language: &LanguageDef,
) -> TokenStream {
    let var_label = generate_var_label(category);

    match coll_type {
        crate::ast::types::CollectionType::HashBag => {
            quote! {
                (#category::#label(g_bag), #category::#label(p_bag)) => {
                    let g_elems: Vec<_> = g_bag.iter()
                        .flat_map(|(elem, count)| std::iter::repeat(elem.clone()).take(count))
                        .collect();
                    let p_elems: Vec<_> = p_bag.iter()
                        .flat_map(|(elem, count)| std::iter::repeat(elem.clone()).take(count))
                        .collect();

                    let mut claimed = vec![false; g_elems.len()];

                    for p_elem in &p_elems {
                        let is_var = matches!(
                            p_elem,
                            #category::#var_label(mettail_runtime::OrdVar(
                                mettail_runtime::Var::Free(_)
                            ))
                        );

                        if is_var {
                            if let Some(idx) = claimed.iter().position(|c| !c) {
                                claimed[idx] = true;
                                if let #category::#var_label(mettail_runtime::OrdVar(
                                    mettail_runtime::Var::Free(ref fv)
                                )) = p_elem {
                                    if let Some(ref pretty_name) = fv.pretty_name {
                                        // Re-enter iterative engine via match_pattern
                                        let sub = p_elem.match_pattern(&g_elems[idx]);
                                        if let Some(b) = sub {
                                            bindings.merge(b);
                                        }
                                    }
                                }
                            } else {
                                return None;
                            }
                        } else {
                            let found = g_elems.iter().enumerate()
                                .find(|(idx, g_elem)| {
                                    // Re-enter iterative engine for structural check
                                    !claimed[*idx] && g_elem.match_pattern(p_elem).is_some()
                                });
                            match found {
                                Some((idx, _)) => {
                                    claimed[idx] = true;
                                    // Re-enter for binding extraction
                                    if let Some(b) = g_elems[idx].match_pattern(p_elem) {
                                        bindings.merge(b);
                                    }
                                }
                                None => return None,
                            }
                        }
                    }
                }
            }
        }
        crate::ast::types::CollectionType::Vec => {
            quote! {
                (#category::#label(g_vec), #category::#label(p_vec)) => {
                    if g_vec.len() != p_vec.len() {
                        return None;
                    }
                    for (g_elem, p_elem) in g_vec.iter().zip(p_vec.iter()) {
                        // Re-enter iterative engine via match_pattern
                        match g_elem.match_pattern(p_elem) {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                }
            }
        }
        crate::ast::types::CollectionType::HashSet => {
            quote! {
                (#category::#label(g_set), #category::#label(p_set)) => {
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
                }
            }
        }
    }
}

/// Generate inline Binder match arm for the iterative engine.
///
/// Opens both scopes and calls `match_pattern()` on the bodies, which
/// re-enters the iterative engine (one re-entry per binder level).
/// Pre-scope fields also use `match_pattern()` re-entry.
fn generate_binder_match_arm_inline(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    _binder_cat: &Ident,
    _body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;

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
                // Re-enter iterative engine for pre-scope field matching
                quote! {
                    {
                        let sub_match = (**#gname).match_pattern(&**#pname);
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
            #(#pre_scope_matches)*

            let g_inner = #g_scope.inner();
            let p_inner = #p_scope.inner();

            // Re-enter iterative engine for body matching
            let body_match = (*g_inner.unsafe_body).match_pattern(&*p_inner.unsafe_body);
            match body_match {
                Some(b) => bindings.merge(b),
                None => return None,
            }
        }
    }
}

/// Generate inline MultiBinder match arm for the iterative engine.
fn generate_multi_binder_match_arm_inline(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    _binder_cat: &Ident,
    _body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;

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
                quote! {
                    {
                        let sub_match = (**#gname).match_pattern(&**#pname);
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
            #(#pre_scope_matches)*

            let g_inner = #g_scope.inner();
            let p_inner = #p_scope.inner();

            if g_inner.unsafe_pattern.len() != p_inner.unsafe_pattern.len() {
                return None;
            }

            // Re-enter iterative engine for body matching
            let body_match = (*g_inner.unsafe_body).match_pattern(&*p_inner.unsafe_body);
            match body_match {
                Some(b) => bindings.merge(b),
                None => return None,
            }
        }
    }
}

// =============================================================================
// Per-Category Match Pattern Wrappers
// =============================================================================

/// Generate `match_pattern` impl block for a single category.
///
/// The public `match_pattern` method delegates to the iterative engine via
/// the TLS pool. Cross-category methods remain trivially None.
fn generate_category_match_pattern(category: &Ident, language: &LanguageDef) -> TokenStream {
    let primary_method = format_ident!("match_pattern");
    let self_alias = format_ident!("match_pattern_{}", category.to_string().to_lowercase());
    let task_variant = format_ident!("Match{}", category);

    // Cross-category methods: types don't match so we always return None.
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

    quote! {
        impl #category {
            /// First-order pattern matching: match `self` (ground term) against
            /// `pattern` (may contain FreeVars).
            ///
            /// Returns `Some(bindings)` if the match succeeds, `None` otherwise.
            /// Variable patterns bind the entire ground term at that position.
            ///
            /// Uses an iterative work stack for stack safety (supports 100K+
            /// nesting depth). Collection and Binder matching re-enter the
            /// engine via this method, bounded by element/binder count.
            pub fn #primary_method(&self, pattern: &#category) -> Option<MatchBindings> {
                MATCH_TASK_POOL.with(|cell| {
                    let mut stack = cell.take();
                    stack.clear();
                    stack.push(MatchTask::#task_variant(self.clone(), pattern.clone()));
                    let result = match_pattern_iterative(&mut stack);
                    cell.set(stack);
                    result
                })
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
