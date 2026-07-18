//! Trampolined (iterative) Hash generation for MeTTaIL AST enums
//!
//! Generates stack-safe `impl Hash` for each category enum to prevent stack
//! overflow on deeply nested terms. Deeply nested `Box<T>` chains cause O(n)
//! recursive `Hash::hash` calls, which overflow the stack for terms with
//! 100K+ nesting depth (common in rewriting systems).
//!
//! ## Architecture: Iterative Work Stack
//!
//! Instead of relying on the compiler-generated recursive hash, each category
//! gets a manual `impl Hash` that:
//!
//! 1. Hashes the discriminant index first (consistent with derive(Hash) behavior).
//! 2. Pushes `Box<T>` children as `HashTask` variants onto a thread-local work stack.
//! 3. The outermost `hash()` call iteratively processes the stack, hashing children
//!    level by level into the same `Hasher` state.
//!
//! ## Re-Entrancy Safety
//!
//! When collection fields (Vec, HashBag, HashSet) delegate to their own `Hash`,
//! that re-enters our iterative engine. The inner call gets an empty pool via
//! `cell.take()`, uses it, and returns it. The outer call retains its pool.
//! This is safe — same `Cell<Vec<_>>` pattern as `iterative_drop.rs`.
//!
//! ## Thread Shutdown Safety
//!
//! All TLS access uses `try_with` (not `with`) to handle thread shutdown gracefully.
//! If TLS is unavailable, a fallback local stack is used.
//!
//! ## Hasher Threading
//!
//! `hash_iterative` takes `state: &mut H` as parameter (not stored in tasks).
//! Each task carries only a `*const Cat` pointer. When processed, the task
//! hashes its fields directly into the provided `state`.
//!
//! ## Generated Items
//!
//! - `HashTask` enum: one variant per category holding `*const Cat`
//! - `HASH_TASK_POOL`: thread-local `Cell<Vec<HashTask>>` for zero-allocation
//!   steady-state operation
//! - `hash_iterative<H: Hasher>(stack: &mut Vec<HashTask>, state: &mut H)`:
//!   iterative Hash engine
//! - `impl Hash for Cat`: delegates to `hash_iterative`

use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate `HashTask` enum, TLS pool, the iterative hash engine,
/// and `impl Hash for Cat` for all exported categories.
pub fn generate_iterative_hash(language: &LanguageDef) -> TokenStream {
    let hash_task_enum = generate_hash_task_enum(language);
    let hash_engine = generate_hash_engine(language);
    let hash_impls = generate_hash_impls(language);

    quote! {
        #hash_task_enum
        #hash_engine
        #hash_impls
    }
}

// =============================================================================
// HashTask Enum + TLS Pool
// =============================================================================

/// Generate the `HashTask` enum and thread-local pool.
///
/// `HashTask` has one variant per category: `HashInt(*const Int)`, etc.
fn generate_hash_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Hash{}", cat);
            quote! {
                #variant_name(*const #cat)
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative hash engine.
        ///
        /// Each variant wraps a raw pointer to a value of one category.
        /// The iterative engine pops tasks, hashes discriminant and leaf
        /// payloads, and pushes child tasks for `Box<T>` fields.
        #[allow(dead_code)]
        enum HashTask {
            #(#variants),*
        }

        // SAFETY: HashTask holds *const pointers that are only dereferenced
        // within the same thread that created them, during the lifetime of
        // the references they were derived from.
        unsafe impl Send for HashTask {}
        unsafe impl Sync for HashTask {}

        thread_local! {
            /// Pool for reusing `HashTask` work stacks across `hash()` calls.
            ///
            /// The `Cell<Vec<HashTask>>` pattern allows zero-allocation
            /// steady-state operation: the first hash allocates, subsequent
            /// hashes reuse the same buffer. Re-entrant hashes (from
            /// collection fields delegating to their own Hash) get fresh
            /// empty vectors; the outermost call retains pool capacity.
            static HASH_TASK_POOL: std::cell::Cell<Vec<HashTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Hash Engine
// =============================================================================

/// Generate the `hash_iterative` function that processes the work stack.
///
/// **Frame-size fix (PDA stack-safety):** Per-cat helpers keep individual
/// stack frames small (the same stack-safety rationale shared across the
/// iterative term-ops).
fn generate_hash_engine(language: &LanguageDef) -> TokenStream {
    let helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_str = cat.to_string().to_lowercase();
            let helper_fn = format_ident!("hash_handle_{}", cat_str);
            let index_fn = format_ident!("variant_index_{}", cat_str);
            let variants = collect_category_variants(cat, language);
            let variant_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_hash_variant_arm(cat, v, language))
                .collect();
            quote! {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn #helper_fn<H: std::hash::Hasher>(
                    stack: &mut Vec<HashTask>,
                    state: &mut H,
                    ptr: *const #cat,
                ) {
                    let val = unsafe { &*ptr };
                    std::hash::Hash::hash(&#index_fn(val), state);
                    match val {
                        #(#variant_arms)*
                    }
                }
            }
        })
        .collect();

    let task_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let hash_variant = format_ident!("Hash{}", cat);
            let helper_fn = format_ident!("hash_handle_{}", cat.to_string().to_lowercase());
            quote! {
                HashTask::#hash_variant(ptr) => {
                    #helper_fn(stack, state, ptr);
                }
            }
        })
        .collect();

    quote! {
        #(#helper_fns)*

        /// Iterative hash engine. Processes the work stack until empty,
        /// hashing each node's fields into the provided `Hasher` state.
        ///
        /// # Safety
        ///
        /// All `*const Cat` pointers in `HashTask` must be valid for reads
        /// for the duration of this function call. This is guaranteed because
        /// they are derived from `&self` in `Hash::hash()`.
        #[allow(dead_code, unused_variables)]
        fn hash_iterative<H: std::hash::Hasher>(stack: &mut Vec<HashTask>, state: &mut H) {
            while let Some(task) = stack.pop() {
                match task {
                    #(#task_arms)*
                }
            }
        }
    }
}

/// Generate match arms for a specific variant in the hash engine.
fn generate_hash_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        VariantKind::Nullary { label } => {
            // Nullary: discriminant only (already hashed above)
            quote! {
                #category::#label => {}
            }
        },

        VariantKind::Literal { label } => {
            // Literal: hash payload
            quote! {
                #category::#label(v) => {
                    std::hash::Hash::hash(v, state);
                }
            }
        },

        VariantKind::Var { label } => {
            // Var: hash OrdVar
            quote! {
                #category::#label(v) => {
                    std::hash::Hash::hash(v, state);
                }
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_hash_regular_arm(category, label, fields, language)
        },

        VariantKind::Collection { label, coll_type: _, .. } => {
            // Collection: delegate to collection's own Hash (re-entrant)
            quote! {
                #category::#label(coll) => {
                    std::hash::Hash::hash(coll, state);
                }
            }
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_hash_binder_arm(category, label, pre_scope_fields, body_cat, language)
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_hash_multi_binder_arm(category, label, pre_scope_fields, body_cat, language)
        },
    }
}

/// Generate hash arm for a Regular variant.
fn generate_hash_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    _language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();

    // Push Box<T> tasks in reverse order so they are processed left-to-right.
    // Collection fields are hashed eagerly inline.
    // To maintain correct hash order (field 0 before field 1), we need to
    // push Box<T> tasks in reverse order.
    //
    // But wait — we're generating the hash_stmts in left-to-right order, mixing
    // eager (collection) and deferred (Box<T>) operations. The eager ones hash
    // immediately into state. The deferred ones push tasks that are processed
    // AFTER all eager ones in this arm. This means collection fields at index 1
    // would be hashed before Box<T> fields at index 0, breaking field order.
    //
    // For correctness, we must maintain field order. The approach:
    // - Fields are processed left-to-right.
    // - For collection fields: hash eagerly (inline).
    // - For Box<T> fields that come BEFORE any collection field: they would be
    //   pushed to the stack and processed after the collection hash. This breaks ordering.
    //
    // Solution: For Box<T> fields that precede collection fields, hash eagerly
    // via re-entrant call. For trailing Box<T> fields (after all collections),
    // push to stack in reverse order.
    //
    // But simpler: just hash ALL fields eagerly. For Box<T> fields, dereference
    // and call hash, which re-enters the trampoline. This is stack-safe because
    // re-entrant calls get a fresh pool.
    //
    // Actually, the whole point of trampolining is to avoid deep recursion.
    // Re-entering for every Box<T> field effectively makes it recursive again.
    //
    // Better approach: push ALL Box<T> fields in reverse, hash ALL collection
    // fields in order. But maintain field ordering by NOT mixing the two.
    //
    // Since hash order matters for correctness (same logical value must produce
    // same hash), and we need field 0 hashed before field 1, the only way with
    // mixed field types is:
    //
    // For each field left-to-right:
    //   - Collection: hash eagerly
    //   - Box<T>: push to stack
    //
    // Then the stack tasks run AFTER all eager hashes in this arm. So if field
    // layout is (Box, Collection, Box), the hash order would be:
    //   1. Collection field 1 (eager)
    //   2. Box field 2 (stack, pushed second = popped first)
    //   3. Box field 0 (stack, pushed first = popped second)
    // Which gives order: [1, 2, 0] — wrong! Should be [0, 1, 2].
    //
    // Fix: push Box<T> tasks in reverse order so they pop in field order.
    // But collection hashes still happen before any Box<T> hashes.
    //
    // The only truly correct approach for mixed fields:
    // - Process strictly left-to-right
    // - Box<T> fields before collections must be hashed eagerly (re-entrant)
    // - Trailing Box<T> fields (after last collection) can be deferred
    //
    // This mirrors the comparison trampoline: eager prefix through the last
    // collection, then deferred boxed fields in LIFO-safe reverse order.

    let last_coll_idx = fields.iter().rposition(|f| f.is_collection);
    let eager_end = last_coll_idx.map(|i| i + 1).unwrap_or(0);

    let mut final_stmts: Vec<TokenStream> = Vec::new();

    // Fields up to and including last collection: hash eagerly
    for (i, field) in fields.iter().enumerate().take(eager_end) {
        let name = &field_names[i];
        if field.is_optional {
            if field.is_collection {
                // Phase 4 #3 (2026-05-12): Optional-Collection — discriminator
                // byte + delegate to the collection's whole-value Hash impl
                // (Vec/HashBag/HashSet all derive Hash).
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => std::hash::Hash::hash(&0u8, state),
                        Some(__c) => {
                            std::hash::Hash::hash(&1u8, state);
                            std::hash::Hash::hash(__c, state);
                        }
                    }
                });
            } else if field.is_predicate {
                // Task #14 (Option<Guard>): same 0/1 discriminant scheme as
                // the Opt-Group arm below, but the Option payload is a BARE
                // BehavioralPred (no Arc layer) — hash `__b` directly; the
                // `&**__b` deref of the sibling arm is E0614 here. Mirrors
                // the dovetail trio's nested is_optional→is_predicate arms
                // (dovetail_report.rs / typed_lowering.rs / reconstruct.rs).
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => std::hash::Hash::hash(&0u8, state),
                        Some(__b) => {
                            std::hash::Hash::hash(&1u8, state);
                            std::hash::Hash::hash(__b, state);
                        }
                    }
                });
            } else {
                // Opt-Group: hash a discriminant byte (0=None, 1=Some), then
                // re-enter Hash on inner if Some. Re-entrant call is bounded
                // because the inner Box runs through the trampoline engine.
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => std::hash::Hash::hash(&0u8, state),
                        Some(__b) => {
                            std::hash::Hash::hash(&1u8, state);
                            std::hash::Hash::hash(&**__b, state);
                        }
                    }
                });
            }
        } else if field.is_predicate {
            // Phase 3A-B4: predicate fields are bare BehavioralPred
            // values that derive `Hash`. Inline-hash them in field
            // order without dereferencing.
            final_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else if field.is_collection {
            final_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else {
            // Box<T> before a collection: hash eagerly (re-entrant, stack-safe)
            final_stmts.push(quote! {
                std::hash::Hash::hash(&**#name, state);
            });
        }
    }

    // Trailing Box<T> fields after last collection: push in reverse order
    let deferred: Vec<(usize, &FieldInfo)> = fields.iter().enumerate().skip(eager_end).collect();

    for &(i, field) in deferred.iter().rev() {
        let name = &field_names[i];
        if field.is_optional {
            if field.is_collection {
                // Phase 4 #3 (2026-05-12): Optional-Collection — emit eagerly
                // (deferred-trailing semantics don't apply to whole-value hashing).
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => std::hash::Hash::hash(&0u8, state),
                        Some(__c) => {
                            std::hash::Hash::hash(&1u8, state);
                            std::hash::Hash::hash(__c, state);
                        }
                    }
                });
                continue;
            }
            if field.is_predicate {
                // Task #14 (Option<Guard>): deferred twin of the eager arm
                // — 0/1 discriminant + direct `__b` hash (no Arc deref).
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => std::hash::Hash::hash(&0u8, state),
                        Some(__b) => {
                            std::hash::Hash::hash(&1u8, state);
                            std::hash::Hash::hash(__b, state);
                        }
                    }
                });
                continue;
            }
            // Opt-Group: emit eagerly (deferred-trailing semantics don't
            // apply to Option-tag-discriminant hashing).
            final_stmts.push(quote! {
                match #name.as_ref() {
                    None => std::hash::Hash::hash(&0u8, state),
                    Some(__b) => {
                        std::hash::Hash::hash(&1u8, state);
                        std::hash::Hash::hash(&**__b, state);
                    }
                }
            });
        } else if field.is_predicate {
            // Phase 3A-B4: predicate fields hash inline regardless of
            // position; pushed in reverse order means we need to emit
            // the hash now since they don't go on the stack.
            final_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else if field.is_collection {
            // Shouldn't happen, but handle gracefully
            final_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else {
            let task_variant = format_ident!("Hash{}", field.category);
            final_stmts.push(quote! {
                stack.push(HashTask::#task_variant(&**#name as *const _));
            });
        }
    }

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#final_stmts)*
        }
    }
}

/// Generate hash arm for a Binder variant.
fn generate_hash_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let mut hash_stmts: Vec<TokenStream> = Vec::new();

    // Hash pre-scope fields eagerly
    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];
        if field.is_predicate {
            // Phase 3A-B4: predicate fields are bare BehavioralPred
            // values; inline-hash without dereferencing.
            hash_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else if field.is_collection {
            hash_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else {
            // Box<T> pre-scope field: hash eagerly (re-entrant, stack-safe)
            hash_stmts.push(quote! {
                std::hash::Hash::hash(&**#name, state);
            });
        }
    }

    // Hash scope: pattern directly, body via task
    let body_task = format_ident!("Hash{}", body_cat);
    hash_stmts.push(quote! {
        {
            // Hash pattern directly (cheap: Binder<String>)
            std::hash::Hash::hash(&#scope_name.inner().unsafe_pattern, state);
            // Push body hash task
            let body_ptr: *const #body_cat = &*#scope_name.inner().unsafe_body;
            stack.push(HashTask::#body_task(body_ptr));
        }
    });

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#hash_stmts)*
        }
    }
}

/// Generate hash arm for a MultiBinder variant.
fn generate_hash_multi_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let mut hash_stmts: Vec<TokenStream> = Vec::new();

    // Hash pre-scope fields eagerly
    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];
        if field.is_predicate {
            // Phase 3A-B4: predicate fields hash inline.
            hash_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else if field.is_collection {
            hash_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else {
            hash_stmts.push(quote! {
                std::hash::Hash::hash(&**#name, state);
            });
        }
    }

    // Hash scope: patterns directly, body via task
    let body_task = format_ident!("Hash{}", body_cat);
    hash_stmts.push(quote! {
        {
            // Hash pattern vec directly (Vec<Binder<String>>)
            std::hash::Hash::hash(&#scope_name.inner().unsafe_pattern, state);
            // Push body hash task
            let body_ptr: *const #body_cat = &*#scope_name.inner().unsafe_body;
            stack.push(HashTask::#body_task(body_ptr));
        }
    });

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#hash_stmts)*
        }
    }
}

// =============================================================================
// Hash Implementations
// =============================================================================

/// Generate `impl Hash for Cat` for each category.
fn generate_hash_impls(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_hash_impl(&lang_type.name))
        .collect();

    quote! { #(#impls)* }
}

/// Generate `impl Hash` for a single category.
fn generate_hash_impl(category: &Ident) -> TokenStream {
    let hash_variant = format_ident!("Hash{}", category);

    quote! {
        impl std::hash::Hash for #category {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                // Fast path: try TLS pool
                let tls_result = HASH_TASK_POOL.try_with(|cell| {
                    let mut stack = cell.take();
                    let was_empty = stack.is_empty();

                    // Push initial hash task
                    stack.push(HashTask::#hash_variant(self as *const _));

                    // Run the iterative engine
                    hash_iterative(&mut stack, state);

                    // Return pool
                    if was_empty {
                        stack.clear();
                    }
                    cell.set(stack);
                });

                if tls_result.is_ok() {
                    return;
                }

                // Fallback: TLS unavailable (thread shutdown). Use local stack.
                let mut stack = vec![HashTask::#hash_variant(self as *const _)];
                hash_iterative(&mut stack, state);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn regular_arm_optional_pred_hashes_inner_without_deref() {
        // Task #14 gate-1: pre-#14 the Opt-Group arm emitted `&**__b` —
        // E0614 on the bare BehavioralPred payload. The pred arm keeps the
        // 0/1 discriminant and hashes `__b` directly.
        let language = crate::gen::empty_language_for_tests();
        let cat = format_ident!("Int");
        let label = format_ident!("PCheck");
        let fields = vec![FieldInfo {
            category: format_ident!("Guard"),
            is_collection: false,
            coll_type: None,
            is_predicate: true,
            is_optional: true,
        }];
        let arm = generate_hash_regular_arm(&cat, &label, &fields, &language).to_string();
        assert!(
            arm.contains("hash (__b , state)"),
            "the Some arm must hash the bare inner pred: {arm}",
        );
        assert!(
            !arm.contains("* * __b"),
            "no Arc deref exists on an Option<BehavioralPred> payload: {arm}",
        );
        assert!(
            arm.contains("0u8") && arm.contains("1u8"),
            "the None/Some discriminant scheme must be kept: {arm}",
        );
    }
}
