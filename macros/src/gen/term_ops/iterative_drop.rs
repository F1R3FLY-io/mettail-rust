//! Trampolined (iterative) Drop generation for MeTTaIL AST enums
//!
//! Generates stack-safe `impl Drop` for each category enum to prevent stack
//! overflow on deeply nested terms. Deeply nested `Box<T>` chains cause O(n)
//! recursive `Drop::drop` calls, which overflow the stack for terms with
//! 100K+ nesting depth (common in rewriting systems).
//!
//! ## Architecture: Iterative Work Stack
//!
//! Instead of relying on the compiler-generated recursive drop, each category
//! gets a manual `impl Drop` that:
//!
//! 1. Extracts owned children from `Box<T>` fields via `std::mem::replace`,
//!    substituting cheap dummy leaf values.
//! 2. Pushes extracted children as `DropTask` variants onto a thread-local
//!    work stack.
//! 3. The outermost `drop()` call iteratively processes the stack, extracting
//!    and dropping children level by level.
//!
//! This mirrors the `MatchTask` pattern from `match_pattern.rs` and ensures
//! O(1) stack usage regardless of term depth.
//!
//! ## Re-Entrancy Safety
//!
//! A thread-local `DROP_ACTIVE` flag prevents re-entrant drops from executing
//! the iterative logic. When the outermost drop sets this flag and enters the
//! work loop, any inner `Drop::drop` calls (from dummy-filled values being
//! deallocated) see the flag and return immediately, letting the compiler's
//! default field-by-field deallocation handle the leaf dummies.
//!
//! ## Thread Shutdown Safety
//!
//! `Drop::drop` uses `try_with` (not `with`) to access TLS, returning early
//! when TLS has been destroyed during thread shutdown. A fallback local stack
//! is used if the pool is unavailable, ensuring safe deallocation even during
//! thread teardown.
//!
//! ## Generated Items
//!
//! - `DropTask` enum: one variant per category (e.g., `DropInt(Int)`)
//! - `DROP_TASK_POOL`: thread-local `Cell<Vec<DropTask>>` for zero-allocation
//!   steady-state operation
//! - `dummy_Cat() -> Cat`: returns the cheapest possible leaf value per category
//! - `push_drop_children_Cat(&mut Cat, &mut Vec<DropTask>)`: extracts boxed
//!   children from a category value and pushes them as drop tasks
//! - `impl Drop for Cat`: orchestrates the iterative drop for each category

use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use crate::gen::native::NativeType;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use crate::gen::generate_var_label;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate the `DropTask` enum, TLS pool, dummy functions, child-extraction
/// functions, and `impl Drop` for all exported categories.
pub fn generate_iterative_drop(language: &LanguageDef) -> TokenStream {
    let drop_task_enum = generate_drop_task_enum(language);
    let dummy_fns = generate_dummy_functions(language);
    let push_children_fns = generate_push_children_functions(language);
    let drop_impls = generate_drop_impls(language);

    quote! {
        #drop_task_enum
        #dummy_fns
        #push_children_fns
        #drop_impls
    }
}

// =============================================================================
// DropTask Enum + TLS Pool
// =============================================================================

/// Generate the `DropTask` enum and thread-local pool.
///
/// `DropTask` has one variant per category: `DropInt(Int)`, `DropProc(Proc)`,
/// etc. The work stack holds values whose children need to be extracted and
/// dropped iteratively.
fn generate_drop_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Drop{}", cat);
            quote! {
                #variant_name(#cat)
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative drop engine.
        ///
        /// Each variant wraps an owned value of one category. The iterative
        /// engine pops tasks, extracts their children (replacing with dummies),
        /// pushes children as new tasks, and lets the (now dummy-filled) value
        /// be dropped cheaply by the compiler.
        #[allow(dead_code)]
        enum DropTask {
            #(#variants),*
        }

        thread_local! {
            /// Pool for reusing `DropTask` work stacks across `drop()` calls.
            ///
            /// The `Cell<Vec<DropTask>>` pattern allows zero-allocation
            /// steady-state operation: the first drop allocates, subsequent
            /// drops reuse the same buffer. Re-entrant drops (from inner
            /// values being dropped during processing) get fresh empty vectors;
            /// the outermost call retains pool capacity.
            static DROP_TASK_POOL: std::cell::Cell<Vec<DropTask>> =
                std::cell::Cell::new(Vec::new());

            /// Flag indicating the current thread is inside the iterative
            /// drop loop. When set, inner `Drop::drop` calls skip the
            /// iterative logic — the value being dropped has already had its
            /// children extracted (replaced with dummies), so the compiler's
            /// default field-by-field drop is safe and O(1).
            static DROP_ACTIVE: std::cell::Cell<bool> = std::cell::Cell::new(false);
        }
    }
}

// =============================================================================
// Dummy Value Functions
// =============================================================================

/// Generate a `dummy_Cat() -> Cat` function for each category.
///
/// Returns the cheapest possible leaf value: a Nullary constructor if one
/// exists, otherwise a Literal with default value, otherwise a Var with a
/// dummy FreeVar.
fn generate_dummy_functions(language: &LanguageDef) -> TokenStream {
    let fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_dummy_fn(&lang_type.name, language))
        .collect();

    quote! { #(#fns)* }
}

/// Generate a single `dummy_Cat()` function for one category.
fn generate_dummy_fn(category: &Ident, language: &LanguageDef) -> TokenStream {
    let fn_name = format_ident!("dummy_{}", category.to_string().to_lowercase());
    let variants = collect_category_variants(category, language);

    // Strategy 1: Find a Nullary variant (cheapest — no allocation)
    for v in &variants {
        if let VariantKind::Nullary { label } = v {
            return quote! {
                /// Return the cheapest possible leaf value for this category.
                ///
                /// Used as a placeholder when extracting children during
                /// iterative drop. Must be a leaf (no `Box<T>` children).
                #[inline]
                #[allow(dead_code)]
                fn #fn_name() -> #category {
                    #category::#label
                }
            };
        }
    }

    // Strategy 2: Find a Literal variant (one allocation for String, zero for numeric)
    for v in &variants {
        if let VariantKind::Literal { label } = v {
            let default_value = generate_literal_default(category, language);
            return quote! {
                #[inline]
                #[allow(dead_code)]
                fn #fn_name() -> #category {
                    #category::#label(#default_value)
                }
            };
        }
    }

    // Strategy 3: Use the Var variant with a dummy FreeVar (always exists)
    let var_label = generate_var_label(category);
    quote! {
        #[inline]
        #[allow(dead_code)]
        fn #fn_name() -> #category {
            #category::#var_label(mettail_runtime::OrdVar(
                mettail_runtime::Var::Free(mettail_runtime::FreeVar::fresh(None))
            ))
        }
    }
}

/// Generate a default literal value expression for a category's literal type.
fn generate_literal_default(category: &Ident, language: &LanguageDef) -> TokenStream {
    let lang_type = language.get_type(category);
    match lang_type.and_then(|t| t.native_type.as_ref()) {
        Some(native_type) => {
            let nt = crate::gen::native::NativeType::from_syn_type(native_type);
            match nt {
                NativeType::Int32 => quote! { 0i32 },
                NativeType::Int64 => quote! { 0i64 },
                NativeType::UInt32 => quote! { 0u32 },
                NativeType::UInt64 => quote! { 0u64 },
                NativeType::Isize => quote! { 0isize },
                NativeType::Usize => quote! { 0usize },
                NativeType::Float32 => quote! { mettail_runtime::CanonicalFloat32::from(0.0f32) },
                NativeType::Float64 => quote! { mettail_runtime::CanonicalFloat64::from(0.0f64) },
                NativeType::Bool => quote! { false },
                NativeType::Str => quote! { std::string::String::new() },
                _ => quote! { Default::default() },
            }
        }
        None => quote! { 0i32 }, // fallback
    }
}

// =============================================================================
// Push Children Functions
// =============================================================================

/// Generate a `push_drop_children_Cat(&mut Cat, &mut Vec<DropTask>)` function
/// for each category.
///
/// These functions inspect the variant, extract ownership of `Box<T>` children
/// via `std::mem::replace`, and push the extracted children as `DropTask`
/// variants onto the work stack.
fn generate_push_children_functions(language: &LanguageDef) -> TokenStream {
    let fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_push_children_fn(&lang_type.name, language))
        .collect();

    quote! { #(#fns)* }
}

/// Generate a single `push_drop_children_Cat` function for one category.
fn generate_push_children_fn(category: &Ident, language: &LanguageDef) -> TokenStream {
    let fn_name = format_ident!("push_drop_children_{}", category.to_string().to_lowercase());
    let variants = collect_category_variants(category, language);

    let match_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_push_children_arm(category, v, language))
        .collect();

    quote! {
        /// Extract `Box<T>` children from a category value, replacing them
        /// with dummy values, and push the extracted children as `DropTask`s
        /// onto the work stack.
        #[allow(dead_code, unused_variables)]
        fn #fn_name(value: &mut #category, stack: &mut Vec<DropTask>) {
            match value {
                #(#match_arms)*
            }
        }
    }
}

/// Generate a single match arm for `push_drop_children_Cat`.
fn generate_push_children_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        // Var: leaf value, no children to extract
        VariantKind::Var { label } => {
            quote! {
                #category::#label(_) => {}
            }
        }

        // Literal: leaf value, no children to extract
        VariantKind::Literal { label } => {
            quote! {
                #category::#label(_) => {}
            }
        }

        // Nullary: leaf value, no fields at all
        VariantKind::Nullary { label } => {
            quote! {
                #category::#label => {}
            }
        }

        // Regular: extract Box<T> children, push as DropTasks
        VariantKind::Regular { label, fields } => {
            generate_regular_push_arm(category, label, fields, language)
        }

        // Collection: take the collection, push each element
        VariantKind::Collection {
            label,
            element_cat,
            coll_type,
        } => generate_collection_push_arm(category, label, element_cat, coll_type, language),

        // Binder: extract pre-scope Box<T> children and the scope body
        VariantKind::Binder {
            label,
            pre_scope_fields,
            body_cat,
            ..
        } => generate_binder_push_arm(category, label, pre_scope_fields, body_cat, language),

        // MultiBinder: same as Binder
        VariantKind::MultiBinder {
            label,
            pre_scope_fields,
            body_cat,
            ..
        } => generate_multi_binder_push_arm(category, label, pre_scope_fields, body_cat, language),
    }
}

/// Generate push arm for a Regular variant.
///
/// For each field:
/// - If it's a `Box<T>` (non-collection): replace with `Box::new(dummy_T())`
///   and push the extracted child as `DropTask::DropT(*child)`
/// - If it's a collection: take the collection, push each element
fn generate_regular_push_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    _language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();

    let push_stmts: Vec<TokenStream> = fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| {
            // Phase 3A-B3: predicate fields are bare (non-boxed)
            // BehavioralPred values that drop in place when their
            // parent is dropped. No DropTask, no dummy needed. Bind
            // the field name with `_` prefix to suppress unused-var
            // warnings while keeping destructure arity correct.
            if field.is_predicate {
                return quote! {
                    let _ = #name;
                };
            }
            let task_variant = format_ident!("Drop{}", field.category);
            let dummy_fn = format_ident!("dummy_{}", field.category.to_string().to_lowercase());

            if field.is_optional {
                if field.is_collection {
                    // Phase 4 #3 (2026-05-12): Optional-Collection — `take()`
                    // extracts the inner container (Vec/HashBag/HashSet), then
                    // we iterate and push DropTask per element.
                    let _ = dummy_fn.clone();
                    return match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                        CollectionType::Vec | CollectionType::HashSet => quote! {
                            if let Some(__c) = #name.take() {
                                for elem in __c {
                                    stack.push(DropTask::#task_variant(elem));
                                }
                            }
                        },
                        CollectionType::HashBag | CollectionType::HashMap => quote! {
                            if let Some(__c) = #name.take() {
                                for (elem, _count) in __c.into_iter() {
                                    stack.push(DropTask::#task_variant(elem));
                                }
                            }
                        },
                    };
                }
                // Opt-Group: `Option<Box<Cat>>` field. `take()` extracts
                // the Box (leaves None) without needing a dummy. Push
                // the inner if Some.
                let _ = dummy_fn.clone();
                return quote! {
                    if let Some(__b) = #name.take() {
                        stack.push(DropTask::#task_variant(*__b));
                    }
                };
            }

            if field.is_collection {
                // Collection field inside a Regular variant: take and push elements
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::Vec => {
                        quote! {
                            for elem in std::mem::take(#name) {
                                stack.push(DropTask::#task_variant(elem));
                            }
                        }
                    }
                    CollectionType::HashBag | CollectionType::HashMap => {
                        quote! {
                            for (elem, count) in std::mem::take(#name).into_iter() {
                                // Each element in a HashBag is unique; count is multiplicity.
                                // We only need to drop each unique element once.
                                stack.push(DropTask::#task_variant(elem));
                            }
                        }
                    }
                    CollectionType::HashSet => {
                        quote! {
                            for elem in std::mem::take(#name) {
                                stack.push(DropTask::#task_variant(elem));
                            }
                        }
                    }
                }
            } else {
                // Box<T> field: replace with dummy box, push extracted child
                quote! {
                    let child = std::mem::replace(#name, Box::new(#dummy_fn()));
                    stack.push(DropTask::#task_variant(*child));
                }
            }
        })
        .collect();

    // Only generate the arm if there are actual children to push
    if push_stmts.is_empty() {
        quote! {
            #category::#label(..) => {}
        }
    } else {
        quote! {
            #category::#label(#(ref mut #field_names),*) => {
                #(#push_stmts)*
            }
        }
    }
}

/// Generate push arm for a Collection variant.
///
/// Takes the collection, pushes each element as a DropTask.
fn generate_collection_push_arm(
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    _language: &LanguageDef,
) -> TokenStream {
    let task_variant = format_ident!("Drop{}", element_cat);

    match coll_type {
        CollectionType::Vec => {
            quote! {
                #category::#label(ref mut coll) => {
                    for elem in std::mem::take(coll) {
                        stack.push(DropTask::#task_variant(elem));
                    }
                }
            }
        }
        CollectionType::HashBag | CollectionType::HashMap => {
            quote! {
                #category::#label(ref mut coll) => {
                    for (elem, _count) in std::mem::take(coll).into_iter() {
                        stack.push(DropTask::#task_variant(elem));
                    }
                }
            }
        }
        CollectionType::HashSet => {
            quote! {
                #category::#label(ref mut coll) => {
                    for elem in std::mem::take(coll) {
                        stack.push(DropTask::#task_variant(elem));
                    }
                }
            }
        }
    }
}

/// Generate push arm for a Binder variant.
///
/// Extracts pre-scope `Box<T>` children and the scope body.
/// The scope is replaced with a dummy scope containing a dummy body.
fn generate_binder_push_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1; // pre-scope fields + scope
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();

    let mut push_stmts: Vec<TokenStream> = Vec::new();

    // Handle pre-scope fields
    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];
        // Phase 3A-B3: predicate fields (BehavioralPred) are bare
        // value payloads. They drop in place when the parent is
        // dropped — no DropTask, no dummy needed.
        if field.is_predicate {
            push_stmts.push(quote! {
                let _ = #name;
            });
            continue;
        }
        let task_variant = format_ident!("Drop{}", field.category);
        let dummy_fn = format_ident!("dummy_{}", field.category.to_string().to_lowercase());

        if field.is_collection {
            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::Vec => {
                    push_stmts.push(quote! {
                        for elem in std::mem::take(#name) {
                            stack.push(DropTask::#task_variant(elem));
                        }
                    });
                }
                CollectionType::HashBag | CollectionType::HashMap => {
                    push_stmts.push(quote! {
                        for (elem, _count) in std::mem::take(#name).into_iter() {
                            stack.push(DropTask::#task_variant(elem));
                        }
                    });
                }
                CollectionType::HashSet => {
                    push_stmts.push(quote! {
                        for elem in std::mem::take(#name) {
                            stack.push(DropTask::#task_variant(elem));
                        }
                    });
                }
            }
        } else {
            push_stmts.push(quote! {
                let child = std::mem::replace(#name, Box::new(#dummy_fn()));
                stack.push(DropTask::#task_variant(*child));
            });
        }
    }

    // Handle the scope field (last field)
    let scope_name = &field_names[total_fields - 1];
    let body_task_variant = format_ident!("Drop{}", body_cat);
    let body_dummy_fn = format_ident!("dummy_{}", body_cat.to_string().to_lowercase());

    push_stmts.push(quote! {
        {
            // Replace the scope with a dummy scope containing a dummy body.
            // This extracts the original scope's body for iterative dropping.
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                mettail_runtime::Binder(mettail_runtime::FreeVar::fresh(None)),
                Box::new(#body_dummy_fn()),
            );
            let old_scope = std::mem::replace(#scope_name, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::#body_task_variant(*body));
        }
    });

    quote! {
        #category::#label(#(ref mut #field_names),*) => {
            #(#push_stmts)*
        }
    }
}

/// Generate push arm for a MultiBinder variant.
///
/// Same as Binder but the pattern is `Vec<Binder<String>>`.
fn generate_multi_binder_push_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();

    let mut push_stmts: Vec<TokenStream> = Vec::new();

    // Handle pre-scope fields
    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];
        // Phase 3A-B3: predicate fields drop in place.
        if field.is_predicate {
            push_stmts.push(quote! {
                let _ = #name;
            });
            continue;
        }
        let task_variant = format_ident!("Drop{}", field.category);
        let dummy_fn = format_ident!("dummy_{}", field.category.to_string().to_lowercase());

        if field.is_collection {
            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::Vec => {
                    push_stmts.push(quote! {
                        for elem in std::mem::take(#name) {
                            stack.push(DropTask::#task_variant(elem));
                        }
                    });
                }
                CollectionType::HashBag | CollectionType::HashMap => {
                    push_stmts.push(quote! {
                        for (elem, _count) in std::mem::take(#name).into_iter() {
                            stack.push(DropTask::#task_variant(elem));
                        }
                    });
                }
                CollectionType::HashSet => {
                    push_stmts.push(quote! {
                        for elem in std::mem::take(#name) {
                            stack.push(DropTask::#task_variant(elem));
                        }
                    });
                }
            }
        } else {
            push_stmts.push(quote! {
                let child = std::mem::replace(#name, Box::new(#dummy_fn()));
                stack.push(DropTask::#task_variant(*child));
            });
        }
    }

    // Handle the scope field (last field)
    let scope_name = &field_names[total_fields - 1];
    let body_task_variant = format_ident!("Drop{}", body_cat);
    let body_dummy_fn = format_ident!("dummy_{}", body_cat.to_string().to_lowercase());

    push_stmts.push(quote! {
        {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                Vec::new(),
                Box::new(#body_dummy_fn()),
            );
            let old_scope = std::mem::replace(#scope_name, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::#body_task_variant(*body));
        }
    });

    quote! {
        #category::#label(#(ref mut #field_names),*) => {
            #(#push_stmts)*
        }
    }
}

// =============================================================================
// Drop Implementations
// =============================================================================

/// Generate `impl Drop for Cat` for each category.
fn generate_drop_impls(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_drop_impl(&lang_type.name, language))
        .collect();

    quote! { #(#impls)* }
}

/// Generate `impl Drop` for a single category.
///
/// The drop implementation:
/// 1. Takes the TLS work stack (or gets a fresh empty one if re-entrant)
/// 2. Extracts children from `self`, pushing them as `DropTask`s
/// 3. If this is the outermost drop (stack was empty before), iteratively
///    processes the stack until empty
/// 4. Returns the stack to the TLS pool
fn generate_drop_impl(category: &Ident, language: &LanguageDef) -> TokenStream {
    let push_fn = format_ident!("push_drop_children_{}", category.to_string().to_lowercase());

    // Generate the match arms for the iterative engine (processing DropTasks)
    let process_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let cat = &lang_type.name;
            let task_variant = format_ident!("Drop{}", cat);
            let cat_push_fn =
                format_ident!("push_drop_children_{}", cat.to_string().to_lowercase());
            quote! {
                DropTask::#task_variant(mut val) => {
                    #cat_push_fn(&mut val, &mut stack);
                    // `val` drops here. Its children were extracted and
                    // replaced with dummies, so its drop is cheap.
                    // The inner drop() call will take an empty Vec from
                    // the pool, push nothing (dummies have no children),
                    // and return the empty Vec.
                }
            }
        })
        .collect();

    quote! {
        impl Drop for #category {
            fn drop(&mut self) {
                // If the DROP_ACTIVE flag is set, we are inside the iterative
                // drop loop. The value being dropped has already had its
                // children extracted (replaced with leaf dummies), so the
                // compiler's default field-by-field deallocation is safe and
                // O(1). Skip the iterative logic to avoid redundant work and
                // re-entrant TLS access.
                let skip = DROP_ACTIVE.try_with(|flag| flag.get()).unwrap_or(false);
                if skip {
                    return;
                }

                // Use try_with to handle the case where TLS is being destroyed
                // during thread shutdown. If TLS is unavailable, fall back to
                // a local stack (allocates, but avoids the panic).
                let tls_available = DROP_TASK_POOL.try_with(|cell| {
                    let mut stack = cell.take();
                    let is_outermost = stack.is_empty();

                    // Extract children from self, replacing with dummies
                    #push_fn(self, &mut stack);

                    if is_outermost {
                        // Set the DROP_ACTIVE flag so that inner drops of
                        // dummy-filled values skip the iterative logic.
                        let _ = DROP_ACTIVE.try_with(|flag| flag.set(true));

                        // Process the entire work stack iteratively until all
                        // children have been extracted and dropped.
                        while let Some(task) = stack.pop() {
                            match task {
                                #(#process_arms)*
                            }
                        }

                        // Clear the flag and return the stack to the pool.
                        let _ = DROP_ACTIVE.try_with(|flag| flag.set(false));
                        cell.set(stack);
                    } else {
                        // Re-entrant call (we're inside the outermost loop's
                        // val drop). Put the stack back with our additions.
                        // The outermost loop will continue processing.
                        cell.set(stack);
                    }
                });

                if tls_available.is_err() {
                    // TLS is being destroyed (thread shutdown). Fall back to
                    // a local stack to avoid panicking. This allocates but is
                    // safe and only happens during thread teardown.
                    let mut stack = Vec::new();
                    #push_fn(self, &mut stack);
                    while let Some(task) = stack.pop() {
                        match task {
                            #(#process_arms)*
                        }
                    }
                }
            }
        }
    }
}
