//! Trampolined (iterative) Clone generation for MeTTaIL AST enums
//!
//! Generates stack-safe `impl Clone` for each category enum to prevent stack
//! overflow on deeply nested terms. Deeply nested `Box<T>` chains cause O(n)
//! recursive `Clone::clone` calls, which overflow the stack for terms with
//! 100K+ nesting depth (common in rewriting systems).
//!
//! ## Architecture: Continuation-Passing Slot-Based Assembly
//!
//! Instead of relying on the compiler-generated recursive clone, each category
//! gets a manual `impl Clone` that uses an iterative work stack with two phases:
//!
//! **Phase 1 (Clone)**: Walk top-down. For each non-leaf node, allocate result
//! slots for children, push an `Assemble` task, then push `Clone` tasks for
//! children. Since stack is LIFO, children are processed before their parent's
//! Assemble task.
//!
//! **Phase 2 (Assemble)**: When popped, read cloned children from result slots
//! and construct the parent.
//!
//! ### Data structures:
//!
//! - `AnyClonedTerm`: One variant per category to hold cloned values
//! - `CloneTask`: Clone variants (one per category) + Assemble variants (one
//!   per non-leaf constructor)
//! - Result buffer: `Vec<Option<AnyClonedTerm>>` indexed by slot IDs
//! - TLS pools: `CLONE_TASK_POOL` and `CLONE_RESULT_POOL` for zero-allocation
//!   steady-state operation
//!
//! ### Safety
//!
//! All `*const Cat` pointers are derived from `&self` in `Clone::clone(&self)`.
//! The source tree is never modified (shared reference). All pointers are valid
//! for the full duration of `clone()`.

use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use crate::gen::native::native_type_to_string;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use crate::gen::generate_var_label;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate `AnyClonedTerm`, `CloneTask`, TLS pools, the iterative clone
/// engine, and `impl Clone for Cat` for all exported categories.
pub fn generate_iterative_clone(language: &LanguageDef) -> TokenStream {
    let any_cloned_term_enum = generate_any_cloned_term_enum(language);
    let clone_task_enum = generate_clone_task_enum(language);
    let clone_engine = generate_clone_engine(language);
    let clone_impls = generate_clone_impls(language);

    quote! {
        #any_cloned_term_enum
        #clone_task_enum
        #clone_engine
        #clone_impls
    }
}

// =============================================================================
// AnyClonedTerm Enum
// =============================================================================

/// Generate the `AnyClonedTerm` enum with one `Wrap{Cat}(Cat)` variant per category.
fn generate_any_cloned_term_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Wrap{}", cat);
            quote! { #variant_name(#cat) }
        })
        .collect();

    quote! {
        /// Holds a cloned value of any category. Used as the element type in
        /// the result buffer for the iterative clone engine.
        #[allow(dead_code)]
        enum AnyClonedTerm {
            #(#variants),*
        }
    }
}

// =============================================================================
// CloneTask Enum + TLS Pools
// =============================================================================

/// Generate the `CloneTask` enum with:
/// - One `Clone{Cat}` variant per category (for initiating clone of a term)
/// - One `Assemble{Label}` variant per non-leaf constructor (for reassembly)
///
/// Also generates TLS pools for the work stack and result buffer.
fn generate_clone_task_enum(language: &LanguageDef) -> TokenStream {
    // Clone variants: one per category
    let clone_variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Clone{}", cat);
            quote! {
                #variant_name { src: *const #cat, slot: usize }
            }
        })
        .collect();

    // Assemble variants: one per non-leaf constructor across all categories
    let mut assemble_variants: Vec<TokenStream> = Vec::new();
    for lang_type in &language.types {
        let category = &lang_type.name;
        let variants = collect_category_variants(category, language);
        for v in &variants {
            if let Some(asm) = generate_assemble_variant(category, v, language) {
                assemble_variants.push(asm);
            }
        }
    }

    quote! {
        /// Work item for the iterative clone engine.
        ///
        /// `Clone{Cat}` variants initiate cloning of a term at a source pointer,
        /// storing the result in the given slot.
        ///
        /// `Assemble{Label}` variants reconstruct a parent node from its
        /// already-cloned children (referenced by slot indices).
        #[allow(dead_code)]
        enum CloneTask {
            #(#clone_variants,)*
            #(#assemble_variants,)*
        }

        thread_local! {
            /// Pool for reusing `CloneTask` work stacks across `clone()` calls.
            static CLONE_TASK_POOL: std::cell::Cell<Vec<CloneTask>> =
                std::cell::Cell::new(Vec::new());

            /// Pool for reusing result buffers across `clone()` calls.
            static CLONE_RESULT_POOL: std::cell::Cell<Vec<Option<AnyClonedTerm>>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

/// Generate a single Assemble variant for a non-leaf constructor.
/// Returns `None` for leaf variants (Var, Literal, Nullary).
fn generate_assemble_variant(
    category: &Ident,
    variant: &VariantKind,
    _language: &LanguageDef,
) -> Option<TokenStream> {
    match variant {
        VariantKind::Var { .. } | VariantKind::Literal { .. } | VariantKind::Nullary { .. } => {
            None // Leaf — no assemble variant needed
        }

        VariantKind::Regular { label, fields } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            // For each field, we store either a single slot or (start, count) for collections
            let field_slots: Vec<TokenStream> = fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    if field.is_collection {
                        let start_name = format_ident!("f{}_start", i);
                        let count_name = format_ident!("f{}_count", i);
                        match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                            CollectionType::HashBag => {
                                let counts_name = format_ident!("f{}_counts", i);
                                quote! { #start_name: usize, #count_name: usize, #counts_name: Vec<usize> }
                            }
                            _ => {
                                quote! { #start_name: usize, #count_name: usize }
                            }
                        }
                    } else {
                        let slot_name = format_ident!("f{}_slot", i);
                        quote! { #slot_name: usize }
                    }
                })
                .collect();

            Some(quote! {
                #variant_name { slot: usize, #(#field_slots),* }
            })
        }

        VariantKind::Collection { label, coll_type, .. } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            match coll_type {
                CollectionType::HashBag => {
                    Some(quote! {
                        #variant_name { slot: usize, elements_start: usize, elements_count: usize, counts_vec: Vec<usize> }
                    })
                }
                _ => {
                    Some(quote! {
                        #variant_name { slot: usize, elements_start: usize, elements_count: usize }
                    })
                }
            }
        }

        VariantKind::Binder { label, pre_scope_fields, .. } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            let pre_field_slots: Vec<TokenStream> = pre_scope_fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    // Phase 3A-B1: predicate fields are bare values
                    // (not slots) — they're cloned directly during
                    // the parent's push arm and stored in the
                    // assemble variant as a `BehavioralPred` field.
                    if field.is_predicate {
                        let pred_name = format_ident!("pf{}_pred", i);
                        return quote! { #pred_name: mettail_runtime::BehavioralPred };
                    }
                    if field.is_collection {
                        let start_name = format_ident!("pf{}_start", i);
                        let count_name = format_ident!("pf{}_count", i);
                        match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                            CollectionType::HashBag => {
                                let counts_name = format_ident!("pf{}_counts", i);
                                quote! { #start_name: usize, #count_name: usize, #counts_name: Vec<usize> }
                            }
                            _ => {
                                quote! { #start_name: usize, #count_name: usize }
                            }
                        }
                    } else {
                        let slot_name = format_ident!("pf{}_slot", i);
                        quote! { #slot_name: usize }
                    }
                })
                .collect();

            Some(quote! {
                #variant_name {
                    slot: usize,
                    #(#pre_field_slots,)*
                    cloned_pattern: mettail_runtime::Binder<String>,
                    body_slot: usize,
                }
            })
        }

        VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            let pre_field_slots: Vec<TokenStream> = pre_scope_fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    // Phase 3A-B1: same predicate handling as Binder.
                    if field.is_predicate {
                        let pred_name = format_ident!("pf{}_pred", i);
                        return quote! { #pred_name: mettail_runtime::BehavioralPred };
                    }
                    if field.is_collection {
                        let start_name = format_ident!("pf{}_start", i);
                        let count_name = format_ident!("pf{}_count", i);
                        match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                            CollectionType::HashBag => {
                                let counts_name = format_ident!("pf{}_counts", i);
                                quote! { #start_name: usize, #count_name: usize, #counts_name: Vec<usize> }
                            }
                            _ => {
                                quote! { #start_name: usize, #count_name: usize }
                            }
                        }
                    } else {
                        let slot_name = format_ident!("pf{}_slot", i);
                        quote! { #slot_name: usize }
                    }
                })
                .collect();

            Some(quote! {
                #variant_name {
                    slot: usize,
                    #(#pre_field_slots,)*
                    cloned_pattern: Vec<mettail_runtime::Binder<String>>,
                    body_slot: usize,
                }
            })
        }
    }
}

// =============================================================================
// Clone Engine
// =============================================================================

/// Generate the `clone_iterative` function that processes the work stack.
fn generate_clone_engine(language: &LanguageDef) -> TokenStream {
    // Generate match arms for Clone{Cat} tasks
    let clone_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let clone_variant = format_ident!("Clone{}", cat);
            let wrap_variant = format_ident!("Wrap{}", cat);
            let variants = collect_category_variants(cat, language);

            let variant_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_clone_match_arm(cat, v, language))
                .collect();

            quote! {
                CloneTask::#clone_variant { src, slot } => {
                    let src_ref = unsafe { &*src };
                    match src_ref {
                        #(#variant_arms)*
                    }
                }
            }
        })
        .collect();

    // Generate match arms for Assemble tasks
    let mut assemble_arms: Vec<TokenStream> = Vec::new();
    for lang_type in &language.types {
        let category = &lang_type.name;
        let variants = collect_category_variants(category, language);
        for v in &variants {
            if let Some(arm) = generate_assemble_match_arm(category, v, language) {
                assemble_arms.push(arm);
            }
        }
    }

    quote! {
        /// Iterative clone engine. Processes the work stack until empty.
        ///
        /// # Safety
        ///
        /// All `*const Cat` pointers in `CloneTask::Clone{Cat}` must be valid
        /// for reads for the duration of this function call. This is guaranteed
        /// because they are derived from `&self` in `Clone::clone()` and the
        /// source tree is immutable (shared reference).
        #[allow(dead_code, unused_variables)]
        fn clone_iterative(stack: &mut Vec<CloneTask>, results: &mut Vec<Option<AnyClonedTerm>>) {
            while let Some(task) = stack.pop() {
                match task {
                    #(#clone_arms)*
                    #(#assemble_arms)*
                }
            }
        }
    }
}

/// Generate match arms within a Clone{Cat} task handler for a specific variant.
fn generate_clone_match_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    let wrap_variant = format_ident!("Wrap{}", category);

    match variant {
        VariantKind::Nullary { label } => {
            quote! {
                #category::#label => {
                    results[slot] = Some(AnyClonedTerm::#wrap_variant(#category::#label));
                }
            }
        }

        VariantKind::Literal { label } => {
            quote! {
                #category::#label(val) => {
                    results[slot] = Some(AnyClonedTerm::#wrap_variant(#category::#label(val.clone())));
                }
            }
        }

        VariantKind::Var { label } => {
            quote! {
                #category::#label(v) => {
                    results[slot] = Some(AnyClonedTerm::#wrap_variant(#category::#label(v.clone())));
                }
            }
        }

        VariantKind::Regular { label, fields } => {
            generate_regular_clone_arm(category, label, fields, language)
        }

        VariantKind::Collection { label, element_cat, coll_type } => {
            generate_collection_clone_arm(category, label, element_cat, coll_type, language)
        }

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_binder_clone_arm(category, label, pre_scope_fields, body_cat, language)
        }

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_multi_binder_clone_arm(category, label, pre_scope_fields, body_cat, language)
        }
    }
}

/// Generate clone arm for a Regular variant.
fn generate_regular_clone_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    _language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let assemble_variant = format_ident!("Assemble{}_{}", category, label);

    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_fields: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();

    for (i, field) in fields.iter().enumerate() {
        let name = &field_names[i];
        let clone_task = format_ident!("Clone{}", field.category);

        if field.is_collection {
            let start_name = format_ident!("f{}_start", i);
            let count_name = format_ident!("f{}_count", i);

            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::HashBag => {
                    let counts_name = format_ident!("f{}_counts", i);
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        let mut #counts_name: Vec<usize> = Vec::new();
                        for (elem, count) in #name.iter() {
                            let elem_slot = results.len();
                            results.push(None);
                            #counts_name.push(count);
                        }
                        let #count_name = results.len() - #start_name;
                    });
                    // Push clone tasks for each unique element
                    // Note: HashBag::iter() is not DoubleEndedIterator, so we iterate forward
                    push_stmts.push(quote! {
                        for (elem_idx, (elem, _count)) in #name.iter().enumerate() {
                            stack.push(CloneTask::#clone_task { src: elem as *const _, slot: #start_name + elem_idx });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name, #counts_name });
                }
                CollectionType::Vec => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (idx, elem) in #name.iter().enumerate().rev() {
                            stack.push(CloneTask::#clone_task { src: elem as *const _, slot: #start_name + idx });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name });
                }
                CollectionType::HashSet => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    // Note: HashSet::iter() is not DoubleEndedIterator, so we iterate forward
                    push_stmts.push(quote! {
                        for (elem_idx, elem) in #name.iter().enumerate() {
                            stack.push(CloneTask::#clone_task { src: elem as *const _, slot: #start_name + elem_idx });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name });
                }
            }
        } else {
            let slot_name = format_ident!("f{}_slot", i);
            alloc_stmts.push(quote! {
                let #slot_name = results.len();
                results.push(None);
            });
            push_stmts.push(quote! {
                stack.push(CloneTask::#clone_task { src: &**#name as *const _, slot: #slot_name });
            });
            assemble_fields.push(quote! { #slot_name });
        }
    }

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#alloc_stmts)*
            // Push assemble first (will be processed after children)
            stack.push(CloneTask::#assemble_variant { slot, #(#assemble_fields),* });
            // Push clone tasks for children (reverse order for LIFO)
            #(#push_stmts)*
        }
    }
}

/// Generate clone arm for a Collection variant.
fn generate_collection_clone_arm(
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    _language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", category, label);
    let clone_task = format_ident!("Clone{}", element_cat);

    match coll_type {
        CollectionType::HashBag => {
            quote! {
                #category::#label(ref coll) => {
                    let elements_start = results.len();
                    let mut counts_vec: Vec<usize> = Vec::new();
                    for (_elem, count) in coll.iter() {
                        results.push(None);
                        counts_vec.push(count);
                    }
                    let elements_count = results.len() - elements_start;
                    // Push assemble first
                    stack.push(CloneTask::#assemble_variant { slot, elements_start, elements_count, counts_vec });
                    // Push clone tasks for each unique element
                    // Note: HashBag::iter() is not DoubleEndedIterator, so we iterate forward
                    for (elem_idx, (elem, _count)) in coll.iter().enumerate() {
                        stack.push(CloneTask::#clone_task { src: elem as *const _, slot: elements_start + elem_idx });
                    }
                }
            }
        }
        CollectionType::Vec => {
            quote! {
                #category::#label(ref coll) => {
                    let elements_start = results.len();
                    for _ in 0..coll.len() {
                        results.push(None);
                    }
                    let elements_count = coll.len();
                    // Push assemble first
                    stack.push(CloneTask::#assemble_variant { slot, elements_start, elements_count });
                    // Push clone tasks (reverse order)
                    for (idx, elem) in coll.iter().enumerate().rev() {
                        stack.push(CloneTask::#clone_task { src: elem as *const _, slot: elements_start + idx });
                    }
                }
            }
        }
        CollectionType::HashSet => {
            quote! {
                #category::#label(ref coll) => {
                    let elements_start = results.len();
                    for _ in 0..coll.len() {
                        results.push(None);
                    }
                    let elements_count = coll.len();
                    // Push assemble first
                    stack.push(CloneTask::#assemble_variant { slot, elements_start, elements_count });
                    // Push clone tasks
                    // Note: HashSet::iter() is not DoubleEndedIterator, so we iterate forward
                    for (elem_idx, elem) in coll.iter().enumerate() {
                        stack.push(CloneTask::#clone_task { src: elem as *const _, slot: elements_start + elem_idx });
                    }
                }
            }
        }
    }
}

/// Generate clone arm for a Binder variant.
fn generate_binder_clone_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", category, label);
    let body_clone_task = format_ident!("Clone{}", body_cat);

    let total_fields = pre_scope_fields.len() + 1; // pre-scope fields + scope
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_fields: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();

    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];

        // Phase 3A-B1: predicate fields are bare BehavioralPred
        // values that we clone directly (no slot allocation, no
        // task push).
        if field.is_predicate {
            let pred_name = format_ident!("pf{}_pred", i);
            alloc_stmts.push(quote! {
                let #pred_name = #name.clone();
            });
            assemble_fields.push(quote! { #pred_name });
            continue;
        }

        let clone_task = format_ident!("Clone{}", field.category);

        if field.is_collection {
            let start_name = format_ident!("pf{}_start", i);
            let count_name = format_ident!("pf{}_count", i);

            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::HashBag => {
                    let counts_name = format_ident!("pf{}_counts", i);
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        let mut #counts_name: Vec<usize> = Vec::new();
                        for (_elem, count) in #name.iter() {
                            results.push(None);
                            #counts_name.push(count);
                        }
                        let #count_name = results.len() - #start_name;
                    });
                    // Note: HashBag::iter() is not DoubleEndedIterator, so we iterate forward
                    push_stmts.push(quote! {
                        for (elem_idx, (elem, _count)) in #name.iter().enumerate() {
                            stack.push(CloneTask::#clone_task { src: elem as *const _, slot: #start_name + elem_idx });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name, #counts_name });
                }
                CollectionType::Vec => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (idx, elem) in #name.iter().enumerate().rev() {
                            stack.push(CloneTask::#clone_task { src: elem as *const _, slot: #start_name + idx });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name });
                }
                CollectionType::HashSet => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    // Note: HashSet::iter() is not DoubleEndedIterator, so we iterate forward
                    push_stmts.push(quote! {
                        for (elem_idx, elem) in #name.iter().enumerate() {
                            stack.push(CloneTask::#clone_task { src: elem as *const _, slot: #start_name + elem_idx });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name });
                }
            }
        } else {
            let slot_name = format_ident!("pf{}_slot", i);
            alloc_stmts.push(quote! {
                let #slot_name = results.len();
                results.push(None);
            });
            push_stmts.push(quote! {
                stack.push(CloneTask::#clone_task { src: &**#name as *const _, slot: #slot_name });
            });
            assemble_fields.push(quote! { #slot_name });
        }
    }

    // Body slot
    alloc_stmts.push(quote! {
        let body_slot = results.len();
        results.push(None);
    });

    // Clone pattern directly (cheap: Binder<FreeVar<String>>)
    alloc_stmts.push(quote! {
        let cloned_pattern = #scope_name.inner().unsafe_pattern.clone();
    });

    // Push body clone task
    push_stmts.push(quote! {
        stack.push(CloneTask::#body_clone_task { src: &*#scope_name.inner().unsafe_body as *const _, slot: body_slot });
    });

    assemble_fields.push(quote! { cloned_pattern, body_slot });

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#alloc_stmts)*
            stack.push(CloneTask::#assemble_variant { slot, #(#assemble_fields),* });
            #(#push_stmts)*
        }
    }
}

/// Generate clone arm for a MultiBinder variant.
fn generate_multi_binder_clone_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", category, label);
    let body_clone_task = format_ident!("Clone{}", body_cat);

    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_fields: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();

    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];

        // Phase 3A-B1: predicate fields are bare values cloned
        // directly (no slot, no task push).
        if field.is_predicate {
            let pred_name = format_ident!("pf{}_pred", i);
            alloc_stmts.push(quote! {
                let #pred_name = #name.clone();
            });
            assemble_fields.push(quote! { #pred_name });
            continue;
        }

        let clone_task = format_ident!("Clone{}", field.category);

        if field.is_collection {
            let start_name = format_ident!("pf{}_start", i);
            let count_name = format_ident!("pf{}_count", i);

            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::HashBag => {
                    let counts_name = format_ident!("pf{}_counts", i);
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        let mut #counts_name: Vec<usize> = Vec::new();
                        for (_elem, count) in #name.iter() {
                            results.push(None);
                            #counts_name.push(count);
                        }
                        let #count_name = results.len() - #start_name;
                    });
                    // Note: HashBag::iter() is not DoubleEndedIterator, so we iterate forward
                    push_stmts.push(quote! {
                        for (elem_idx, (elem, _count)) in #name.iter().enumerate() {
                            stack.push(CloneTask::#clone_task { src: elem as *const _, slot: #start_name + elem_idx });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name, #counts_name });
                }
                CollectionType::Vec => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (idx, elem) in #name.iter().enumerate().rev() {
                            stack.push(CloneTask::#clone_task { src: elem as *const _, slot: #start_name + idx });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name });
                }
                CollectionType::HashSet => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    // Note: HashSet::iter() is not DoubleEndedIterator, so we iterate forward
                    push_stmts.push(quote! {
                        for (elem_idx, elem) in #name.iter().enumerate() {
                            stack.push(CloneTask::#clone_task { src: elem as *const _, slot: #start_name + elem_idx });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name });
                }
            }
        } else {
            let slot_name = format_ident!("pf{}_slot", i);
            alloc_stmts.push(quote! {
                let #slot_name = results.len();
                results.push(None);
            });
            push_stmts.push(quote! {
                stack.push(CloneTask::#clone_task { src: &**#name as *const _, slot: #slot_name });
            });
            assemble_fields.push(quote! { #slot_name });
        }
    }

    // Body slot
    alloc_stmts.push(quote! {
        let body_slot = results.len();
        results.push(None);
    });

    // Clone pattern directly (cheap: Vec<Binder<FreeVar<String>>>)
    alloc_stmts.push(quote! {
        let cloned_pattern = #scope_name.inner().unsafe_pattern.clone();
    });

    // Push body clone task
    push_stmts.push(quote! {
        stack.push(CloneTask::#body_clone_task { src: &*#scope_name.inner().unsafe_body as *const _, slot: body_slot });
    });

    assemble_fields.push(quote! { cloned_pattern, body_slot });

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#alloc_stmts)*
            stack.push(CloneTask::#assemble_variant { slot, #(#assemble_fields),* });
            #(#push_stmts)*
        }
    }
}

// =============================================================================
// Assemble Match Arms
// =============================================================================

/// Generate assemble match arm for a non-leaf constructor.
/// Returns `None` for leaf variants.
fn generate_assemble_match_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> Option<TokenStream> {
    match variant {
        VariantKind::Var { .. } | VariantKind::Literal { .. } | VariantKind::Nullary { .. } => {
            None
        }

        VariantKind::Regular { label, fields } => {
            Some(generate_regular_assemble_arm(category, label, fields, language))
        }

        VariantKind::Collection { label, element_cat, coll_type } => {
            Some(generate_collection_assemble_arm(category, label, element_cat, coll_type, language))
        }

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            Some(generate_binder_assemble_arm(category, label, pre_scope_fields, body_cat, language))
        }

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            Some(generate_multi_binder_assemble_arm(category, label, pre_scope_fields, body_cat, language))
        }
    }
}

/// Helper: generate an `unwrap_Cat` expression for extracting from AnyClonedTerm
fn unwrap_from_slot(cat: &Ident, slot_expr: TokenStream) -> TokenStream {
    let wrap_variant = format_ident!("Wrap{}", cat);
    quote! {
        match results[#slot_expr].take().expect("iterative clone: missing result in slot") {
            AnyClonedTerm::#wrap_variant(v) => v,
            _ => unreachable!("iterative clone: wrong category in slot"),
        }
    }
}

/// Generate assemble arm for Regular variant.
fn generate_regular_assemble_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    _language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", category, label);
    let wrap_variant = format_ident!("Wrap{}", category);

    let field_slot_names: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_collection {
                let start_name = format_ident!("f{}_start", i);
                let count_name = format_ident!("f{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag => {
                        let counts_name = format_ident!("f{}_counts", i);
                        quote! { #start_name, #count_name, #counts_name }
                    }
                    _ => {
                        quote! { #start_name, #count_name }
                    }
                }
            } else {
                let slot_name = format_ident!("f{}_slot", i);
                quote! { #slot_name }
            }
        })
        .collect();

    let field_extracts: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let wrap = format_ident!("Wrap{}", field.category);
            if field.is_collection {
                let start_name = format_ident!("f{}_start", i);
                let count_name = format_ident!("f{}_count", i);
                let result_ident = format_ident!("field_{}", i);

                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag => {
                        let counts_name = format_ident!("f{}_counts", i);
                        quote! {
                            let mut #result_ident = mettail_runtime::HashBag::new();
                            for (idx, count) in #counts_name.iter().enumerate() {
                                match results[#start_name + idx].take().expect("iterative clone: missing collection element") {
                                    AnyClonedTerm::#wrap(v) => #result_ident.insert_n(v, *count),
                                    _ => unreachable!("iterative clone: wrong category in collection slot"),
                                }
                            }
                        }
                    }
                    CollectionType::Vec => {
                        quote! {
                            let mut #result_ident = Vec::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take().expect("iterative clone: missing collection element") {
                                    AnyClonedTerm::#wrap(v) => #result_ident.push(v),
                                    _ => unreachable!("iterative clone: wrong category in collection slot"),
                                }
                            }
                        }
                    }
                    CollectionType::HashSet => {
                        quote! {
                            let mut #result_ident = std::collections::HashSet::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take().expect("iterative clone: missing collection element") {
                                    AnyClonedTerm::#wrap(v) => { #result_ident.insert(v); },
                                    _ => unreachable!("iterative clone: wrong category in collection slot"),
                                }
                            }
                        }
                    }
                }
            } else {
                let slot_name = format_ident!("f{}_slot", i);
                let result_ident = format_ident!("field_{}", i);
                quote! {
                    let #result_ident = match results[#slot_name].take().expect("iterative clone: missing result in slot") {
                        AnyClonedTerm::#wrap(v) => v,
                        _ => unreachable!("iterative clone: wrong category in slot"),
                    };
                }
            }
        })
        .collect();

    let construct_fields: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let result_ident = format_ident!("field_{}", i);
            if field.is_collection {
                quote! { #result_ident }
            } else {
                quote! { Box::new(#result_ident) }
            }
        })
        .collect();

    quote! {
        CloneTask::#assemble_variant { slot, #(#field_slot_names),* } => {
            #(#field_extracts)*
            results[slot] = Some(AnyClonedTerm::#wrap_variant(#category::#label(#(#construct_fields),*)));
        }
    }
}

/// Generate assemble arm for Collection variant.
fn generate_collection_assemble_arm(
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    _language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", category, label);
    let wrap_variant = format_ident!("Wrap{}", category);
    let elem_wrap = format_ident!("Wrap{}", element_cat);

    match coll_type {
        CollectionType::HashBag => {
            quote! {
                CloneTask::#assemble_variant { slot, elements_start, elements_count, counts_vec } => {
                    let mut bag = mettail_runtime::HashBag::new();
                    for (idx, count) in counts_vec.iter().enumerate() {
                        match results[elements_start + idx].take().expect("iterative clone: missing hashbag element") {
                            AnyClonedTerm::#elem_wrap(v) => bag.insert_n(v, *count),
                            _ => unreachable!("iterative clone: wrong category in hashbag slot"),
                        }
                    }
                    results[slot] = Some(AnyClonedTerm::#wrap_variant(#category::#label(bag)));
                }
            }
        }
        CollectionType::Vec => {
            quote! {
                CloneTask::#assemble_variant { slot, elements_start, elements_count } => {
                    let mut vec = Vec::with_capacity(elements_count);
                    for idx in 0..elements_count {
                        match results[elements_start + idx].take().expect("iterative clone: missing vec element") {
                            AnyClonedTerm::#elem_wrap(v) => vec.push(v),
                            _ => unreachable!("iterative clone: wrong category in vec slot"),
                        }
                    }
                    results[slot] = Some(AnyClonedTerm::#wrap_variant(#category::#label(vec)));
                }
            }
        }
        CollectionType::HashSet => {
            quote! {
                CloneTask::#assemble_variant { slot, elements_start, elements_count } => {
                    let mut set = std::collections::HashSet::with_capacity(elements_count);
                    for idx in 0..elements_count {
                        match results[elements_start + idx].take().expect("iterative clone: missing hashset element") {
                            AnyClonedTerm::#elem_wrap(v) => { set.insert(v); },
                            _ => unreachable!("iterative clone: wrong category in hashset slot"),
                        }
                    }
                    results[slot] = Some(AnyClonedTerm::#wrap_variant(#category::#label(set)));
                }
            }
        }
    }
}

/// Generate assemble arm for Binder variant.
fn generate_binder_assemble_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", category, label);
    let wrap_variant = format_ident!("Wrap{}", category);
    let body_wrap = format_ident!("Wrap{}", body_cat);

    let pre_field_slot_names: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            // Phase 3A-B1: predicate fields are bare values stored
            // directly in the assemble variant.
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name };
            }
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! { #start_name, #count_name, #counts_name }
                    }
                    _ => {
                        quote! { #start_name, #count_name }
                    }
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                quote! { #slot_name }
            }
        })
        .collect();

    let pre_field_extracts: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            // Phase 3A-B1: predicate fields don't need extraction —
            // they're already in scope as `pf{i}_pred`.
            if field.is_predicate {
                return quote! {};
            }
            let wrap = format_ident!("Wrap{}", field.category);
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                let result_ident = format_ident!("pre_field_{}", i);

                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! {
                            let mut #result_ident = mettail_runtime::HashBag::new();
                            for (idx, count) in #counts_name.iter().enumerate() {
                                match results[#start_name + idx].take().expect("iterative clone: missing pre-scope collection element") {
                                    AnyClonedTerm::#wrap(v) => #result_ident.insert_n(v, *count),
                                    _ => unreachable!("iterative clone: wrong category in pre-scope collection slot"),
                                }
                            }
                        }
                    }
                    CollectionType::Vec => {
                        quote! {
                            let mut #result_ident = Vec::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take().expect("iterative clone: missing pre-scope vec element") {
                                    AnyClonedTerm::#wrap(v) => #result_ident.push(v),
                                    _ => unreachable!("iterative clone: wrong category in pre-scope vec slot"),
                                }
                            }
                        }
                    }
                    CollectionType::HashSet => {
                        quote! {
                            let mut #result_ident = std::collections::HashSet::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take().expect("iterative clone: missing pre-scope hashset element") {
                                    AnyClonedTerm::#wrap(v) => { #result_ident.insert(v); },
                                    _ => unreachable!("iterative clone: wrong category in pre-scope hashset slot"),
                                }
                            }
                        }
                    }
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                let result_ident = format_ident!("pre_field_{}", i);
                quote! {
                    let #result_ident = match results[#slot_name].take().expect("iterative clone: missing pre-scope result") {
                        AnyClonedTerm::#wrap(v) => v,
                        _ => unreachable!("iterative clone: wrong category in pre-scope slot"),
                    };
                }
            }
        })
        .collect();

    let construct_pre_fields: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            // Phase 3A-B1: predicate fields go directly into the
            // constructor as bare values (no Box wrapping).
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name, };
            }
            let result_ident = format_ident!("pre_field_{}", i);
            if field.is_collection {
                quote! { #result_ident, }
            } else {
                quote! { Box::new(#result_ident), }
            }
        })
        .collect();

    quote! {
        CloneTask::#assemble_variant { slot, #(#pre_field_slot_names,)* cloned_pattern, body_slot } => {
            #(#pre_field_extracts)*
            let body = match results[body_slot].take().expect("iterative clone: missing binder body") {
                AnyClonedTerm::#body_wrap(v) => v,
                _ => unreachable!("iterative clone: wrong category in binder body slot"),
            };
            let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, Box::new(body));
            results[slot] = Some(AnyClonedTerm::#wrap_variant(#category::#label(#(#construct_pre_fields)* new_scope)));
        }
    }
}

/// Generate assemble arm for MultiBinder variant.
fn generate_multi_binder_assemble_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", category, label);
    let wrap_variant = format_ident!("Wrap{}", category);
    let body_wrap = format_ident!("Wrap{}", body_cat);

    let pre_field_slot_names: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            // Phase 3A-B1: see binder_assemble_arm.
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name };
            }
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! { #start_name, #count_name, #counts_name }
                    }
                    _ => {
                        quote! { #start_name, #count_name }
                    }
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                quote! { #slot_name }
            }
        })
        .collect();

    let pre_field_extracts: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            // Phase 3A-B1: predicate fields are already in scope.
            if field.is_predicate {
                return quote! {};
            }
            let wrap = format_ident!("Wrap{}", field.category);
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                let result_ident = format_ident!("pre_field_{}", i);

                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! {
                            let mut #result_ident = mettail_runtime::HashBag::new();
                            for (idx, count) in #counts_name.iter().enumerate() {
                                match results[#start_name + idx].take().expect("iterative clone: missing pre-scope collection element") {
                                    AnyClonedTerm::#wrap(v) => #result_ident.insert_n(v, *count),
                                    _ => unreachable!("iterative clone: wrong category in pre-scope collection slot"),
                                }
                            }
                        }
                    }
                    CollectionType::Vec => {
                        quote! {
                            let mut #result_ident = Vec::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take().expect("iterative clone: missing pre-scope vec element") {
                                    AnyClonedTerm::#wrap(v) => #result_ident.push(v),
                                    _ => unreachable!("iterative clone: wrong category in pre-scope vec slot"),
                                }
                            }
                        }
                    }
                    CollectionType::HashSet => {
                        quote! {
                            let mut #result_ident = std::collections::HashSet::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take().expect("iterative clone: missing pre-scope hashset element") {
                                    AnyClonedTerm::#wrap(v) => { #result_ident.insert(v); },
                                    _ => unreachable!("iterative clone: wrong category in pre-scope hashset slot"),
                                }
                            }
                        }
                    }
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                let result_ident = format_ident!("pre_field_{}", i);
                quote! {
                    let #result_ident = match results[#slot_name].take().expect("iterative clone: missing pre-scope result") {
                        AnyClonedTerm::#wrap(v) => v,
                        _ => unreachable!("iterative clone: wrong category in pre-scope slot"),
                    };
                }
            }
        })
        .collect();

    let construct_pre_fields: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            // Phase 3A-B1: predicate fields go directly into the constructor.
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name, };
            }
            let result_ident = format_ident!("pre_field_{}", i);
            if field.is_collection {
                quote! { #result_ident, }
            } else {
                quote! { Box::new(#result_ident), }
            }
        })
        .collect();

    quote! {
        CloneTask::#assemble_variant { slot, #(#pre_field_slot_names,)* cloned_pattern, body_slot } => {
            #(#pre_field_extracts)*
            let body = match results[body_slot].take().expect("iterative clone: missing multi-binder body") {
                AnyClonedTerm::#body_wrap(v) => v,
                _ => unreachable!("iterative clone: wrong category in multi-binder body slot"),
            };
            let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, Box::new(body));
            results[slot] = Some(AnyClonedTerm::#wrap_variant(#category::#label(#(#construct_pre_fields)* new_scope)));
        }
    }
}

// =============================================================================
// Clone Implementations
// =============================================================================

/// Generate `impl Clone for Cat` for each category.
fn generate_clone_impls(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_clone_impl(&lang_type.name, language))
        .collect();

    quote! { #(#impls)* }
}

/// Generate `impl Clone` for a single category.
fn generate_clone_impl(category: &Ident, _language: &LanguageDef) -> TokenStream {
    let clone_task_variant = format_ident!("Clone{}", category);
    let wrap_variant = format_ident!("Wrap{}", category);

    quote! {
        impl Clone for #category {
            fn clone(&self) -> Self {
                // Fast path: try TLS pools
                let tls_result = CLONE_TASK_POOL.try_with(|task_cell| {
                    CLONE_RESULT_POOL.try_with(|result_cell| {
                        let mut stack = task_cell.take();
                        let mut results = result_cell.take();

                        // Clear and reserve slot 0 for root result
                        stack.clear();
                        results.clear();
                        results.push(None); // slot 0 = root

                        // Push initial clone task
                        stack.push(CloneTask::#clone_task_variant {
                            src: self as *const _,
                            slot: 0,
                        });

                        // Run the iterative engine
                        clone_iterative(&mut stack, &mut results);

                        // Extract root result
                        let root = match results[0].take().expect("iterative clone: root slot empty after clone") {
                            AnyClonedTerm::#wrap_variant(v) => v,
                            _ => unreachable!("iterative clone: wrong category in root slot"),
                        };

                        // Return pools
                        result_cell.set(results);
                        task_cell.set(stack);

                        root
                    })
                });

                // If TLS is available, return the result
                if let Ok(Ok(root)) = tls_result {
                    return root;
                }

                // Fallback: TLS unavailable (thread shutdown). Use local allocations.
                let mut stack = Vec::new();
                let mut results = vec![None]; // slot 0 = root

                stack.push(CloneTask::#clone_task_variant {
                    src: self as *const _,
                    slot: 0,
                });

                clone_iterative(&mut stack, &mut results);

                match results[0].take().expect("iterative clone: root slot empty after clone (fallback)") {
                    AnyClonedTerm::#wrap_variant(v) => v,
                    _ => unreachable!("iterative clone: wrong category in root slot (fallback)"),
                }
            }
        }
    }
}
