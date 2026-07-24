//! Trampolined (iterative) PartialEq/Eq/PartialOrd/Ord generation for MeTTaIL AST enums
//!
//! Generates stack-safe comparison trait implementations for each category enum
//! to prevent stack overflow on deeply nested terms. Deeply nested `Box<T>` chains
//! cause O(n) recursive comparison calls, which overflow the stack for terms with
//! 100K+ nesting depth (common in rewriting systems).
//!
//! ## Architecture: Iterative Work Stack
//!
//! Instead of relying on the compiler-generated recursive comparison, each category
//! gets manual `impl PartialEq`, `impl Eq`, `impl PartialOrd`, and `impl Ord` that:
//!
//! 1. Push comparison tasks for `Box<T>` child pairs onto a thread-local work stack.
//! 2. The outermost comparison call iteratively processes the stack, comparing
//!    children level by level.
//! 3. Early-exits on first inequality (for eq) or first non-Equal ordering (for cmp).
//!
//! ## Re-Entrancy Safety
//!
//! When collection fields (Vec, HashBag, HashSet) delegate to their own `PartialEq`
//! or `Ord`, that re-enters our iterative engine. The inner call gets an empty pool
//! via `cell.take()`, uses it, and returns it. The outer call retains its pool.
//! This is safe — same `Cell<Vec<_>>` pattern as `iterative_drop.rs`.
//!
//! ## Thread Shutdown Safety
//!
//! All TLS access uses `try_with` (not `with`) to handle thread shutdown gracefully.
//! If TLS is unavailable, a fallback local stack is used.
//!
//! ## Generated Items
//!
//! - `CmpTask` enum: one variant per category holding `(*const Left, *const Right)`
//! - `CMP_TASK_POOL`: thread-local `Cell<Vec<CmpTask>>` for zero-allocation
//!   steady-state operation
//! - `variant_index_cat(val: &Cat) -> usize`: maps variants to declaration-order index
//! - `eq_iterative(stack: &mut Vec<CmpTask>) -> bool`: iterative PartialEq engine
//! - `cmp_iterative(stack: &mut Vec<CmpTask>) -> std::cmp::Ordering`: iterative Ord engine
//! - `impl PartialEq for Cat`: delegates to `eq_iterative`
//! - `impl Eq for Cat`: marker trait
//! - `impl PartialOrd for Cat`: delegates to `Ord::cmp`
//! - `impl Ord for Cat`: delegates to `cmp_iterative`

use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate `CmpTask` enum, TLS pool, variant_index functions, iterative engines,
/// and `impl PartialEq/Eq/PartialOrd/Ord` for all exported categories.
pub fn generate_iterative_cmp(language: &LanguageDef) -> TokenStream {
    let cmp_task_enum = generate_cmp_task_enum(language);
    let variant_index_fns = generate_variant_index_fns(language);
    let eq_engine = generate_eq_engine(language);
    let cmp_engine = generate_cmp_engine(language);
    let trait_impls = generate_trait_impls(language);

    quote! {
        #cmp_task_enum
        #variant_index_fns
        #eq_engine
        #cmp_engine
        #trait_impls
    }
}

// =============================================================================
// CmpTask Enum + TLS Pool
// =============================================================================

/// Generate the `CmpTask` enum and thread-local pool.
///
/// `CmpTask` has one variant per category holding raw pointer pairs:
/// `CmpInt(*const Int, *const Int)`, `CmpProc(*const Proc, *const Proc)`, etc.
fn generate_cmp_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Cmp{}", cat);
            quote! {
                #variant_name(*const #cat, *const #cat)
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative comparison engines (eq and cmp).
        ///
        /// Each variant wraps a pair of raw pointers to values of the same
        /// category. The iterative engine pops tasks, compares discriminants
        /// and leaf payloads, and pushes child-pair tasks for `Box<T>` fields.
        #[allow(dead_code)]
        enum CmpTask {
            #(#variants),*
        }

        // SAFETY: CmpTask holds *const pointers that are only dereferenced
        // within the same thread that created them, during the lifetime of
        // the references they were derived from.
        unsafe impl Send for CmpTask {}
        unsafe impl Sync for CmpTask {}

        thread_local! {
            /// Pool for reusing `CmpTask` work stacks across comparison calls.
            ///
            /// The `Cell<Vec<CmpTask>>` pattern allows zero-allocation
            /// steady-state operation: the first comparison allocates, subsequent
            /// comparisons reuse the same buffer. Re-entrant comparisons (from
            /// collection fields delegating to their own PartialEq/Ord) get fresh
            /// empty vectors; the outermost call retains pool capacity.
            static CMP_TASK_POOL: std::cell::Cell<Vec<CmpTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Variant Index Functions
// =============================================================================

/// Generate `variant_index_cat(val: &Cat) -> usize` for each category.
///
/// Maps each variant to its declaration-order index. Used by `cmp_iterative`
/// to order variants by discriminant when they differ.
fn generate_variant_index_fns(language: &LanguageDef) -> TokenStream {
    let fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_variant_index_fn(&lang_type.name, language))
        .collect();

    quote! { #(#fns)* }
}

/// Generate a single `variant_index_cat` function for one category.
fn generate_variant_index_fn(category: &Ident, language: &LanguageDef) -> TokenStream {
    let fn_name = format_ident!("variant_index_{}", category.to_string().to_lowercase());
    let variants = collect_category_variants(category, language);

    let match_arms: Vec<TokenStream> = variants
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let pattern = variant_wildcard_pattern(category, v);
            quote! { #pattern => #i }
        })
        .collect();

    quote! {
        /// Map a variant to its declaration-order index for Ord comparison.
        #[inline]
        #[allow(dead_code)]
        fn #fn_name(val: &#category) -> usize {
            match val {
                #(#match_arms,)*
            }
        }
    }
}

/// Generate a wildcard match pattern for a variant (matches any payload).
fn variant_wildcard_pattern(category: &Ident, variant: &VariantKind) -> TokenStream {
    match variant {
        VariantKind::Nullary { label } => {
            quote! { #category::#label }
        },
        VariantKind::Literal { label }
        | VariantKind::Var { label }
        | VariantKind::Collection { label, .. } => {
            quote! { #category::#label(..) }
        },
        VariantKind::Regular { label, .. }
        | VariantKind::Binder { label, .. }
        | VariantKind::MultiBinder { label, .. } => {
            quote! { #category::#label(..) }
        },
    }
}

// =============================================================================
// Equality Engine
// =============================================================================

/// Generate the `eq_iterative` function that processes the work stack for equality.
///
/// **Frame-size fix (PDA stack-safety):** Each per-category arm is extracted
/// into its own `#[inline(never)]` helper. Without this split, `eq_iterative`
/// becomes one mega-function whose `match (left, right) { ... }` arms force
/// rustc to allocate stack space for every variant's locals up front,
/// overflowing the default 2 MB thread stack on the first call.
fn generate_eq_engine(language: &LanguageDef) -> TokenStream {
    // Per-cat helper functions: each handles one CmpTask::Cmp{Cat}.
    // Returns `Some(false)` to short-circuit (mismatch), `Some(true)` to
    // continue (equal so far for this pair), `None` if there's nothing to
    // do. We use `bool` directly via early return — caller must propagate.
    let helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_str = cat.to_string().to_lowercase();
            let helper_fn = format_ident!("eq_handle_{}", cat_str);
            let index_fn = format_ident!("variant_index_{}", cat_str);
            let variants = collect_category_variants(cat, language);
            let variant_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_eq_variant_arm(cat, v, language))
                .collect();
            quote! {
                /// Returns `false` on mismatch (caller should propagate),
                /// `true` if matched so far (caller should continue draining stack).
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn #helper_fn(
                    stack: &mut Vec<CmpTask>,
                    left_ptr: *const #cat,
                    right_ptr: *const #cat,
                ) -> bool {
                    let left = unsafe { &*left_ptr };
                    let right = unsafe { &*right_ptr };
                    if #index_fn(left) != #index_fn(right) {
                        return false;
                    }
                    match (left, right) {
                        #(#variant_arms)*
                        _ => { return false; }
                    }
                    true
                }
            }
        })
        .collect();

    let task_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cmp_variant = format_ident!("Cmp{}", cat);
            let helper_fn = format_ident!("eq_handle_{}", cat.to_string().to_lowercase());
            quote! {
                CmpTask::#cmp_variant(left_ptr, right_ptr) => {
                    if !#helper_fn(stack, left_ptr, right_ptr) {
                        return false;
                    }
                }
            }
        })
        .collect();

    quote! {
        #(#helper_fns)*

        /// Iterative equality engine. Processes the work stack until empty.
        ///
        /// Returns `true` if all pushed comparison pairs are equal.
        ///
        /// # Safety
        ///
        /// All `*const Cat` pointers in `CmpTask` must be valid for reads
        /// for the duration of this function call. This is guaranteed because
        /// they are derived from `&self` and `&other` in `PartialEq::eq()`.
        #[allow(dead_code, unused_variables)]
        fn eq_iterative(stack: &mut Vec<CmpTask>) -> bool {
            while let Some(task) = stack.pop() {
                match task {
                    #(#task_arms)*
                }
            }
            true
        }
    }
}

/// Generate match arms for a specific variant in the equality engine.
fn generate_eq_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        VariantKind::Nullary { label } => {
            // Nullary: always equal (discriminant already matched)
            quote! {
                (#category::#label, #category::#label) => {}
            }
        },

        VariantKind::Literal { label } => {
            // Literal: compare payloads directly
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    if a != b { return false; }
                }
            }
        },

        VariantKind::Var { label } => {
            // Var: compare OrdVar payloads directly
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    if a != b { return false; }
                }
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_eq_regular_arm(category, label, fields, language)
        },

        VariantKind::Collection { label, coll_type: _, .. } => {
            // Collection: delegate to the collection's own PartialEq
            // (re-entrant via TLS pool — safe per Cell<Vec> pattern)
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    if a != b { return false; }
                }
            }
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_eq_binder_arm(category, label, pre_scope_fields, body_cat, language)
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_eq_multi_binder_arm(category, label, pre_scope_fields, body_cat, language)
        },
    }
}

/// Generate eq arm for a Regular variant.
fn generate_eq_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    _language: &LanguageDef,
) -> TokenStream {
    let left_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("r{}", i)).collect();

    let compare_stmts: Vec<TokenStream> = fields
        .iter()
        .zip(left_names.iter().zip(right_names.iter()))
        .map(|(field, (lname, rname))| {
            // Phase 3A-B2: predicate fields use direct PartialEq.
            // BehavioralPred derives Eq, so the bare value comparison
            // is sound. L9-3: token-text captures are bare `String` leaves —
            // the identical direct-Eq (String: Eq), no CmpTask descent.
            if field.is_predicate || field.is_opaque_leaf() {
                return quote! {
                    if #lname != #rname { return false; }
                };
            }
            if field.is_optional {
                if field.is_collection {
                    // Phase 4 #3 (2026-05-12): Optional-Collection — delegate
                    // to Option<Container>::PartialEq directly. Vec/HashBag/HashSet
                    // all implement PartialEq elementwise.
                    return quote! {
                        if #lname != #rname { return false; }
                    };
                }
                // Opt-Group: equality on `Option<Box<Cat>>`. Push CmpTask
                // recursively if both Some; mismatched Some/None or
                // mismatched values short-circuit to false.
                let task_variant = format_ident!("Cmp{}", field.category);
                return quote! {
                    match (#lname.as_ref(), #rname.as_ref()) {
                        (None, None) => {}
                        (Some(__l), Some(__r)) => {
                            stack.push(CmpTask::#task_variant(
                                __l.as_ref() as *const _,
                                __r.as_ref() as *const _,
                            ));
                        }
                        _ => return false,
                    }
                };
            }
            if field.is_collection {
                // Collection field: delegate to collection's own PartialEq (re-entrant)
                quote! {
                    if #lname != #rname { return false; }
                }
            } else {
                // Box<T> field: push comparison task for children
                let task_variant = format_ident!("Cmp{}", field.category);
                quote! {
                    stack.push(CmpTask::#task_variant(&**#lname as *const _, &**#rname as *const _));
                }
            }
        })
        .collect();

    quote! {
        (#category::#label(#(ref #left_names),*), #category::#label(#(ref #right_names),*)) => {
            #(#compare_stmts)*
        }
    }
}

/// Generate eq arm for a Binder variant.
fn generate_eq_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1; // pre-scope fields + scope
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];

    let mut compare_stmts: Vec<TokenStream> = Vec::new();

    // Compare pre-scope fields
    for (i, field) in pre_scope_fields.iter().enumerate() {
        let lname = &left_names[i];
        let rname = &right_names[i];
        // Phase 3A-B2: predicate fields use direct PartialEq.
        if field.is_predicate {
            compare_stmts.push(quote! {
                if #lname != #rname { return false; }
            });
            continue;
        }
        if field.is_collection {
            compare_stmts.push(quote! {
                if #lname != #rname { return false; }
            });
        } else {
            let task_variant = format_ident!("Cmp{}", field.category);
            compare_stmts.push(quote! {
                stack.push(CmpTask::#task_variant(&**#lname as *const _, &**#rname as *const _));
            });
        }
    }

    // Compare scope: compare pattern directly, push body comparison task
    let body_task = format_ident!("Cmp{}", body_cat);
    compare_stmts.push(quote! {
        {
            let l_pat = &#scope_left.inner().unsafe_pattern;
            let r_pat = &#scope_right.inner().unsafe_pattern;
            if l_pat != r_pat { return false; }
            let l_body: *const #body_cat = &*#scope_left.inner().unsafe_body;
            let r_body: *const #body_cat = &*#scope_right.inner().unsafe_body;
            stack.push(CmpTask::#body_task(l_body, r_body));
        }
    });

    quote! {
        (#category::#label(#(ref #left_names),*), #category::#label(#(ref #right_names),*)) => {
            #(#compare_stmts)*
        }
    }
}

/// Generate eq arm for a MultiBinder variant.
fn generate_eq_multi_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];

    let mut compare_stmts: Vec<TokenStream> = Vec::new();

    for (i, field) in pre_scope_fields.iter().enumerate() {
        let lname = &left_names[i];
        let rname = &right_names[i];
        // Phase 3A-B2: predicate fields use direct PartialEq.
        if field.is_predicate {
            compare_stmts.push(quote! {
                if #lname != #rname { return false; }
            });
            continue;
        }
        if field.is_collection {
            compare_stmts.push(quote! {
                if #lname != #rname { return false; }
            });
        } else {
            let task_variant = format_ident!("Cmp{}", field.category);
            compare_stmts.push(quote! {
                stack.push(CmpTask::#task_variant(&**#lname as *const _, &**#rname as *const _));
            });
        }
    }

    let body_task = format_ident!("Cmp{}", body_cat);
    compare_stmts.push(quote! {
        {
            let l_pat = &#scope_left.inner().unsafe_pattern;
            let r_pat = &#scope_right.inner().unsafe_pattern;
            if l_pat != r_pat { return false; }
            let l_body: *const #body_cat = &*#scope_left.inner().unsafe_body;
            let r_body: *const #body_cat = &*#scope_right.inner().unsafe_body;
            stack.push(CmpTask::#body_task(l_body, r_body));
        }
    });

    quote! {
        (#category::#label(#(ref #left_names),*), #category::#label(#(ref #right_names),*)) => {
            #(#compare_stmts)*
        }
    }
}

// =============================================================================
// Ordering Engine
// =============================================================================

/// Generate the `cmp_iterative` function that processes the work stack for ordering.
///
/// **Frame-size fix (PDA stack-safety):** Same split as `eq_iterative` —
/// per-cat helpers keep individual stack frames small. Each helper returns
/// the ordering result; `Equal` means "continue draining stack", anything
/// else means "stop and propagate".
fn generate_cmp_engine(language: &LanguageDef) -> TokenStream {
    let helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_str = cat.to_string().to_lowercase();
            let helper_fn = format_ident!("cmp_handle_{}", cat_str);
            let index_fn = format_ident!("variant_index_{}", cat_str);
            let variants = collect_category_variants(cat, language);
            let variant_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_cmp_variant_arm(cat, v, language))
                .collect();
            quote! {
                /// Returns `Ordering::Equal` to keep draining the stack;
                /// any other ordering means "stop and propagate up".
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn #helper_fn(
                    stack: &mut Vec<CmpTask>,
                    left_ptr: *const #cat,
                    right_ptr: *const #cat,
                ) -> std::cmp::Ordering {
                    let left = unsafe { &*left_ptr };
                    let right = unsafe { &*right_ptr };
                    let l_idx = #index_fn(left);
                    let r_idx = #index_fn(right);
                    if l_idx != r_idx {
                        stack.clear();
                        return l_idx.cmp(&r_idx);
                    }
                    match (left, right) {
                        #(#variant_arms)*
                        _ => {
                            stack.clear();
                            return l_idx.cmp(&r_idx);
                        }
                    }
                    std::cmp::Ordering::Equal
                }
            }
        })
        .collect();

    let task_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cmp_variant = format_ident!("Cmp{}", cat);
            let helper_fn = format_ident!("cmp_handle_{}", cat.to_string().to_lowercase());
            quote! {
                CmpTask::#cmp_variant(left_ptr, right_ptr) => {
                    let ord = #helper_fn(stack, left_ptr, right_ptr);
                    if ord != std::cmp::Ordering::Equal {
                        return ord;
                    }
                }
            }
        })
        .collect();

    quote! {
        #(#helper_fns)*

        /// Iterative ordering engine. Processes the work stack until empty.
        ///
        /// Returns `std::cmp::Ordering` for the overall comparison.
        ///
        /// # Safety
        ///
        /// All `*const Cat` pointers in `CmpTask` must be valid for reads
        /// for the duration of this function call. This is guaranteed because
        /// they are derived from `&self` and `&other` in `Ord::cmp()`.
        #[allow(dead_code, unused_variables)]
        fn cmp_iterative(stack: &mut Vec<CmpTask>) -> std::cmp::Ordering {
            while let Some(task) = stack.pop() {
                match task {
                    #(#task_arms)*
                }
            }
            std::cmp::Ordering::Equal
        }
    }
}

/// Generate match arms for a specific variant in the ordering engine.
fn generate_cmp_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        VariantKind::Nullary { label } => {
            // Nullary: always equal
            quote! {
                (#category::#label, #category::#label) => {}
            }
        },

        VariantKind::Literal { label } => {
            // Literal: compare payloads with Ord
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    let ord = a.cmp(b);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            }
        },

        VariantKind::Var { label } => {
            // Var: compare OrdVar with Ord
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    let ord = a.cmp(b);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_cmp_regular_arm(category, label, fields, language)
        },

        VariantKind::Collection { label, coll_type: _, .. } => {
            // Collection: delegate to collection's own Ord (re-entrant)
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    let ord = a.cmp(b);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            }
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_cmp_binder_arm(category, label, pre_scope_fields, body_cat, language)
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_cmp_multi_binder_arm(category, label, pre_scope_fields, body_cat, language)
        },
    }
}

/// Generate cmp arm for a Regular variant.
///
/// Fields are compared left-to-right. For Box<T> fields, we must compare them
/// eagerly (not push to stack) because the ordering of earlier fields takes
/// precedence over later fields. We push child comparison tasks in reverse
/// order so they are processed left-to-right from the LIFO stack.
///
/// However, for correctness with the LIFO stack pattern, we need to compare
/// fields left-to-right with early exit. The trick: we push tasks for ALL
/// Box<T> fields in reverse, and the engine processes them left-to-right.
/// If any field returns non-Equal, it clears the stack and returns.
///
/// For collection fields, we compare eagerly inline (they use their own Ord).
/// For Box<T> fields, we push CmpTask variants. Since all fields must be
/// compared left-to-right, we push them in reverse order on the LIFO stack.
///
/// BUT: if a collection field comes before a Box<T> field, we must early-exit
/// on the collection comparison before pushing Box<T> tasks. So we split:
/// compare collections eagerly, push Box<T> tasks in reverse for remaining.
///
/// Actually, the simplest correct approach: push ALL Box<T> child comparisons
/// in reverse order. For collection fields between Box<T> fields, we can't
/// use the stack since collections are compared eagerly. The solution:
/// process fields strictly left-to-right, and for each field either compare
/// eagerly (collection/leaf) or push a single child task and continue.
///
/// Wait - with a LIFO stack, pushing tasks in reverse processes them in order.
/// But we need to early-exit on the FIRST non-Equal result. With the stack
/// approach, all tasks are pushed before any are processed. So if field 0 is
/// non-equal, field 1's task was already pushed but will be cleared.
///
/// The approach: push all Box<T> field tasks in reverse. For collection fields,
/// they are compared eagerly in a "pre-check" block. If any collection field
/// is non-Equal, we early-exit before pushing any tasks.
///
/// Simplified approach: we push tasks in reverse so they process left-to-right.
/// Collection/leaf fields are checked eagerly before pushing Box tasks. This
/// ensures correct left-to-right ordering semantics.
fn generate_cmp_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    _language: &LanguageDef,
) -> TokenStream {
    let left_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("r{}", i)).collect();

    // Split into eager (collection) and deferred (Box<T>) comparisons.
    // We need left-to-right semantics. Strategy:
    // 1. Compare all collection fields eagerly, in order. If any is non-Equal, return.
    // 2. Push all Box<T> fields as tasks in reverse order (LIFO -> left-to-right processing).
    //
    // This is correct because collection comparisons are self-contained (no child tasks),
    // and Box<T> tasks will be processed left-to-right after this arm completes.
    //
    // HOWEVER: this breaks left-to-right field semantics when a collection field
    // comes AFTER a Box<T> field. Example: Regular(Box<A>, Vec<B>, Box<C>).
    // We'd compare Vec<B> eagerly, then push Box<A> and Box<C>. But Box<A> should
    // be compared BEFORE Vec<B>.
    //
    // Correct solution: process ALL fields left-to-right. For Box<T> fields,
    // recursively push and process (but that's what we're trying to avoid for stack safety).
    //
    // Better: push ALL work onto the stack in reverse. For collection fields,
    // wrap them in a CmpTask that compares eagerly. But CmpTask only holds *const Cat...
    //
    // Simplest correct solution: push Box<T> tasks in reverse. Any collection
    // comparisons are done eagerly. If a collection comparison would come after
    // a Box<T> field in field order, we handle this by emitting comparison blocks
    // in LEFT-TO-RIGHT order, where each block either pushes a task or compares eagerly.
    // Since we push tasks in reverse and they'll be processed AFTER this arm body,
    // we need a different approach.
    //
    // ACTUAL simplest approach: just push all Box<T> child pairs as CmpTask variants
    // in REVERSE order. Collection fields are compared eagerly. The key insight is
    // that the generated Ord is semantically equivalent to the derived one; we're just
    // trampolining the Box<T> recursion. Collection fields already use their own Ord
    // which handles their internal recursion. The only concern is field ordering.
    //
    // For field ordering: we push Box<T> tasks in reverse so they pop left-to-right.
    // But eagerly-compared collection fields break left-to-right ordering if they
    // come BETWEEN two Box<T> fields.
    //
    // Final approach: we accumulate comparison stmts in left-to-right order.
    // For collection fields, emit eager comparison. For Box<T> fields, emit a push.
    // BUT we need to push tasks in reverse for LIFO ordering. Since we process
    // fields left-to-right in codegen, pushing them means they end up in reverse
    // on the stack (last pushed = first popped). So we actually need to push
    // Box<T> tasks in FIELD ORDER (not reversed), because the first push goes
    // deepest on the stack and the last push is popped first.
    //
    // Wait: no. We push all tasks in this arm body, then the engine pops from
    // the top. So the LAST pushed task is popped FIRST. To process field 0 first,
    // we need field 0 to be pushed LAST (i.e., push in reverse field order).
    //
    // But collection fields between Box fields break this. Solution: Don't push
    // collection comparisons as tasks. Instead, do a hybrid approach:
    //
    // Process fields left-to-right:
    //   - Collection: compare eagerly. If non-Equal, clear stack and return.
    //   - Box<T>: accumulate for later pushing.
    // Then push accumulated Box<T> tasks in reverse field order.
    //
    // This is correct IF no collection field comes AFTER a Box<T> field in the
    // same variant. But that's not guaranteed.
    //
    // So actually: for the first non-collection field that differs, we need to
    // return that ordering. For collection fields that come between box fields,
    // we need to ensure they're compared at the right time.
    //
    // The TRULY correct approach for heterogeneous fields: push tasks in reverse,
    // but for collection fields, use an intermediate "compare and continue" approach.
    //
    // Let me just use a simple, correct approach:
    // - For each field in LEFT-TO-RIGHT order, push a comparison task in REVERSE.
    //   Collections are compared eagerly BEFORE pushing any box tasks.
    //   If the collection comparison is non-equal, don't push anything, just return.
    //
    // Actually the simplest correct approach: just compare ALL fields in the match arm
    // body, left-to-right. For Box<T> fields, dereference and push tasks. Push them
    // in reverse to get left-to-right popping. For collection fields, compare inline.
    //
    // The only issue with pushing ALL fields' box tasks is that an earlier field's
    // non-Equal result should prevent comparing later fields. But with the work stack,
    // the engine WILL compare them (wasting work) unless we clear the stack on
    // non-Equal. And Box<T> comparisons on the stack all compare in the engine loop,
    // where non-Equal clears the stack and returns. So: the first non-Equal Box<T>
    // comparison will clear remaining tasks and return. This is correct.
    //
    // For collection fields compared eagerly: if non-Equal, we return immediately
    // (before reaching the stack). If Equal, we continue pushing Box<T> tasks.
    //
    // So the approach IS correct as long as we eagerly compare collections
    // BEFORE pushing Box<T> tasks. But that means collection comparisons always
    // happen before Box<T> comparisons, which breaks left-to-right ordering
    // when a collection field comes AFTER a Box<T> field.
    //
    // To handle this correctly with mixed field types, I'll use a different strategy:
    // Process fields sequentially, left to right. For each field:
    //   - If collection/leaf: compare eagerly. If non-Equal, clear stack, return.
    //   - If Box<T>: push a CmpTask.
    // Push all Box<T> tasks in reverse order for LIFO processing.
    //
    // But this still has the problem that box field 0 may be pushed to the stack
    // while collection field 1 is compared eagerly, and if collection field 1 is
    // non-Equal, we clear the stack (dropping the pushed task for field 0).
    // That's fine! The collection non-Equal result is the correct answer.
    //
    // Wait, but field 0 (Box) should be compared BEFORE field 1 (Collection).
    // If we push field 0's task then eagerly compare field 1, field 1 might
    // return non-Equal. But the correct result could be that field 0 is non-Equal
    // in the other direction. This is wrong.
    //
    // So we must process them strictly left-to-right. For Box<T> fields, we
    // can't defer them if there are later eager fields. The only safe approach
    // when there are mixed field types is to NOT defer Box<T> comparisons.
    //
    // BUT deferring is the whole point (stack safety). The key insight: in practice,
    // each field in a Regular variant is either all Box<T> or a mix. For mixed,
    // the collection fields' comparison is already stack-safe (they use their own
    // Ord impl which re-enters the trampoline). Box<T> fields are what need trampolining.
    //
    // SOLUTION: For all fields, push CmpTask variants in reverse order. For
    // collection fields, they get compared via the CmpTask engine which calls
    // the iterative cmp. But wait - CmpTask only holds category pointers, not
    // arbitrary types.
    //
    // FINAL SOLUTION: Push Box<T> children as CmpTask in reverse field order.
    // Compare collection fields eagerly. When mixing, always compare eagerly first
    // (left to right), and for Box<T> fields that precede collection fields,
    // push them. The engine processes remaining tasks after this arm.
    //
    // Actually, after much deliberation, the practical approach used by derive(Ord)
    // is: compare field 0, then field 1, etc. Each field comparison short-circuits
    // on non-Equal. The trampolined version does the same, just iteratively for
    // Box<T> fields.
    //
    // The CORRECT trampolined approach: push ALL fields (reversed) as tasks.
    // But we can only push category types. Collection fields hold elements of
    // category types, and the collection's own Ord compares elements.
    //
    // I'll just push Box<T> fields in reverse and compare collection fields eagerly.
    // Left-to-right ordering for the Box<T> fields is maintained by the stack.
    // Collection fields compared eagerly will short-circuit before stack processing.
    // This means collection results take priority over later Box<T> results, which
    // violates strict left-to-right semantics when a Box<T> comes before a collection.
    //
    // To fix: any Box<T> field that comes BEFORE a collection field must also be
    // compared eagerly (dereferenced inline). Only the TRAILING Box<T> fields
    // (after all collection fields) can be deferred to the stack.
    //
    // Let me implement this cleanly. Find the index of the last collection field.
    // All fields up to and including that index are compared eagerly. Fields after
    // are pushed as tasks in reverse.

    // Find the index of the last non-Box field (collection fields).
    let last_eager_idx = fields.iter().rposition(|f| f.is_collection);

    let mut stmts: Vec<TokenStream> = Vec::new();

    // Fields that must be compared eagerly (up to and including last collection field)
    let eager_end = last_eager_idx.map(|i| i + 1).unwrap_or(0);

    for (i, field) in fields.iter().enumerate().take(eager_end) {
        let lname = &left_names[i];
        let rname = &right_names[i];
        // Phase 3A-B2: predicate fields use direct cmp.
        // BehavioralPred derives Ord, so the bare value comparison is sound.
        // L9-3: token-text captures (bare `String`) compare identically.
        if field.is_predicate || field.is_opaque_leaf() {
            stmts.push(quote! {
                {
                    let ord = #lname.cmp(#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
            continue;
        }
        if field.is_optional {
            if field.is_collection {
                // Phase 4 #3 (2026-05-12): Optional-Collection — delegate to
                // Option<Container>::cmp. Vec/HashSet impl Ord directly;
                // HashBag impls Ord too (see mettail_runtime).
                stmts.push(quote! {
                    {
                        let ord = #lname.cmp(#rname);
                        if ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return ord;
                        }
                    }
                });
                continue;
            }
            // Opt-Group: order Option<Box<Cat>>. None < Some(_); Some(a)
            // vs Some(b) compares inner via re-entrant trampolined cmp.
            stmts.push(quote! {
                {
                    let ord = match (#lname.as_ref(), #rname.as_ref()) {
                        (None, None) => std::cmp::Ordering::Equal,
                        (None, Some(_)) => std::cmp::Ordering::Less,
                        (Some(_), None) => std::cmp::Ordering::Greater,
                        (Some(__l), Some(__r)) => (**__l).cmp(&**__r),
                    };
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
            continue;
        }
        if field.is_collection {
            stmts.push(quote! {
                {
                    let ord = #lname.cmp(#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
        } else {
            // Box<T> field before a collection field — must compare eagerly
            // to maintain left-to-right semantics. We dereference and push
            // as a single task, then drain the stack for it before continuing.
            //
            // Actually, for simplicity and correctness, compare via the task
            // mechanism but process immediately. We push a single task and
            // let the engine loop handle it on the next iteration. But other
            // tasks may be on the stack from a parent.
            //
            // Simplest: just push a single CmpTask. The engine will process
            // it next. But the eager collection comparison below will happen
            // in this arm body, not in the engine loop. So we can't push
            // and then eagerly compare — the push goes to the stack, and
            // the eager code runs in the arm body.
            //
            // True fix: compare Box<T> fields that precede collections eagerly too.
            // Dereference and recursively compare. But that defeats trampolining.
            //
            // Pragmatic fix: for Box<T> fields that precede collections, push them
            // as tasks. The task for the Box<T> field won't be processed until after
            // this match arm returns. The collection comparison happens in the arm.
            // This means the collection result might override the Box<T> result.
            //
            // For correctness: I'll just push ALL Box<T> fields as tasks, and
            // compare ALL collection fields eagerly. The stack processes tasks
            // in reverse-push order (LIFO). After the arm body, the engine pops
            // the next task. If there's a collection non-Equal, we already returned.
            // If not, the Box<T> tasks are processed. Since collection was Equal,
            // the Box<T> result determines the final ordering.
            //
            // The ONLY incorrectness: if Box field 0 is Less and Collection field 1
            // is Greater, we should return Less (field 0 takes priority). But we'd
            // return Greater (collection compared eagerly first). To fix this, when
            // a Box<T> field precedes a collection field, compare the Box<T> eagerly.
            //
            // For eager Box<T> comparison: use `cmp()` on the derefed values. This
            // re-enters our Ord::cmp, which uses the trampoline. So it IS stack-safe!
            // The re-entrant call gets a fresh stack from the pool.
            stmts.push(quote! {
                {
                    let ord = (**#lname).cmp(&**#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
        }
    }

    // Remaining Box<T> fields after the last collection field — push in reverse
    let deferred_fields: Vec<(usize, &FieldInfo)> =
        fields.iter().enumerate().skip(eager_end).collect();

    for &(i, field) in deferred_fields.iter().rev() {
        let lname = &left_names[i];
        let rname = &right_names[i];
        // Phase 3A-B2: predicate fields use direct cmp inline.
        // L9-3: token-text captures (bare `String`) compare identically.
        if field.is_predicate || field.is_opaque_leaf() {
            stmts.push(quote! {
                {
                    let ord = #lname.cmp(#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
            continue;
        }
        if field.is_optional {
            if field.is_collection {
                // Phase 4 #3 (2026-05-12): Optional-Collection — delegate to
                // Option<Container>::cmp (eager — same rationale as in the
                // eager-loop branch).
                stmts.push(quote! {
                    {
                        let ord = #lname.cmp(#rname);
                        if ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return ord;
                        }
                    }
                });
                continue;
            }
            // Opt-Group: same eager Optional-cmp as the eager-loop
            // branch (deferred-trailing semantics don't help here
            // because Some/None is a tag-discriminant compare).
            stmts.push(quote! {
                {
                    let ord = match (#lname.as_ref(), #rname.as_ref()) {
                        (None, None) => std::cmp::Ordering::Equal,
                        (None, Some(_)) => std::cmp::Ordering::Less,
                        (Some(_), None) => std::cmp::Ordering::Greater,
                        (Some(__l), Some(__r)) => (**__l).cmp(&**__r),
                    };
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
            continue;
        }
        if field.is_collection {
            // Should not happen — we processed all collections above
            stmts.push(quote! {
                {
                    let ord = #lname.cmp(#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
        } else {
            let task_variant = format_ident!("Cmp{}", field.category);
            stmts.push(quote! {
                stack.push(CmpTask::#task_variant(&**#lname as *const _, &**#rname as *const _));
            });
        }
    }

    quote! {
        (#category::#label(#(ref #left_names),*), #category::#label(#(ref #right_names),*)) => {
            #(#stmts)*
        }
    }
}

/// Generate cmp arm for a Binder variant.
fn generate_cmp_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];

    let mut stmts: Vec<TokenStream> = Vec::new();

    // Compare pre-scope fields eagerly (left-to-right)
    for (i, field) in pre_scope_fields.iter().enumerate() {
        let lname = &left_names[i];
        let rname = &right_names[i];
        // Phase 3A-B2: predicate fields use direct cmp.
        if field.is_predicate {
            stmts.push(quote! {
                {
                    let ord = #lname.cmp(#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
            continue;
        }
        if field.is_collection {
            stmts.push(quote! {
                {
                    let ord = #lname.cmp(#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
        } else {
            // Box<T> pre-scope field — compare eagerly (re-entrant, stack-safe)
            stmts.push(quote! {
                {
                    let ord = (**#lname).cmp(&**#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
        }
    }

    // Compare scope: pattern eagerly, body via task
    let body_task = format_ident!("Cmp{}", body_cat);
    stmts.push(quote! {
        {
            let ord = #scope_left.cmp(&#scope_right);
            // Scope::cmp already compares pattern hash then body.
            // But the body comparison in Scope::cmp will be recursive.
            // Instead, compare patterns eagerly and push body to stack.
            // Actually, we can't easily split Scope::cmp. Let's compare
            // patterns first, then push body.
        }
    });

    // Clear the above empty block, and do the actual comparison:
    stmts.pop(); // Remove the empty block
    stmts.push(quote! {
        {
            // Compare patterns eagerly (cheap: Binder<String>)
            let l_scope = #scope_left.inner();
            let r_scope = #scope_right.inner();
            // Pattern comparison: use hash-based ordering (same as Scope::cmp)
            let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                let mut h = std::collections::hash_map::DefaultHasher::new();
                std::hash::Hash::hash(p, &mut h);
                std::hash::Hasher::finish(&h)
            };
            let pat_ord = hash_pat(&l_scope.unsafe_pattern).cmp(&hash_pat(&r_scope.unsafe_pattern));
            if pat_ord != std::cmp::Ordering::Equal {
                stack.clear();
                return pat_ord;
            }
            // Push body comparison
            let l_body: *const #body_cat = &*l_scope.unsafe_body;
            let r_body: *const #body_cat = &*r_scope.unsafe_body;
            stack.push(CmpTask::#body_task(l_body, r_body));
        }
    });

    quote! {
        (#category::#label(#(ref #left_names),*), #category::#label(#(ref #right_names),*)) => {
            #(#stmts)*
        }
    }
}

/// Generate cmp arm for a MultiBinder variant.
fn generate_cmp_multi_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];

    let mut stmts: Vec<TokenStream> = Vec::new();

    for (i, field) in pre_scope_fields.iter().enumerate() {
        let lname = &left_names[i];
        let rname = &right_names[i];
        // Phase 3A-B2: predicate fields use direct cmp.
        if field.is_predicate {
            stmts.push(quote! {
                {
                    let ord = #lname.cmp(#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
            continue;
        }
        if field.is_collection {
            stmts.push(quote! {
                {
                    let ord = #lname.cmp(#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
        } else {
            stmts.push(quote! {
                {
                    let ord = (**#lname).cmp(&**#rname);
                    if ord != std::cmp::Ordering::Equal {
                        stack.clear();
                        return ord;
                    }
                }
            });
        }
    }

    let body_task = format_ident!("Cmp{}", body_cat);
    stmts.push(quote! {
        {
            // Compare patterns eagerly (Vec<Binder<String>>)
            let l_scope = #scope_left.inner();
            let r_scope = #scope_right.inner();
            // Compare pattern vecs: length then elements
            let l_pats = &l_scope.unsafe_pattern;
            let r_pats = &r_scope.unsafe_pattern;
            let len_ord = l_pats.len().cmp(&r_pats.len());
            if len_ord != std::cmp::Ordering::Equal {
                stack.clear();
                return len_ord;
            }
            for (lp, rp) in l_pats.iter().zip(r_pats.iter()) {
                let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                    let mut h = std::collections::hash_map::DefaultHasher::new();
                    std::hash::Hash::hash(p, &mut h);
                    std::hash::Hasher::finish(&h)
                };
                let pat_ord = hash_pat(lp).cmp(&hash_pat(rp));
                if pat_ord != std::cmp::Ordering::Equal {
                    stack.clear();
                    return pat_ord;
                }
            }
            // Push body comparison
            let l_body: *const #body_cat = &*l_scope.unsafe_body;
            let r_body: *const #body_cat = &*r_scope.unsafe_body;
            stack.push(CmpTask::#body_task(l_body, r_body));
        }
    });

    quote! {
        (#category::#label(#(ref #left_names),*), #category::#label(#(ref #right_names),*)) => {
            #(#stmts)*
        }
    }
}

// =============================================================================
// Trait Implementations
// =============================================================================

/// Generate `impl PartialEq/Eq/PartialOrd/Ord` for all categories.
fn generate_trait_impls(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_category_trait_impls(&lang_type.name))
        .collect();

    quote! { #(#impls)* }
}

/// Generate all four comparison trait impls for a single category.
fn generate_category_trait_impls(category: &Ident) -> TokenStream {
    let cmp_variant = format_ident!("Cmp{}", category);

    quote! {
        impl PartialEq for #category {
            fn eq(&self, other: &Self) -> bool {
                // Fast path: try TLS pool
                let tls_result = CMP_TASK_POOL.try_with(|cell| {
                    let mut stack = cell.take();
                    let was_empty = stack.is_empty();

                    // Push initial comparison task
                    stack.push(CmpTask::#cmp_variant(
                        self as *const _,
                        other as *const _,
                    ));

                    // Run the iterative engine
                    let result = eq_iterative(&mut stack);

                    // Return pool
                    if was_empty {
                        stack.clear();
                    }
                    cell.set(stack);

                    result
                });

                if let Ok(result) = tls_result {
                    return result;
                }

                // Fallback: TLS unavailable (thread shutdown). Use local stack.
                let mut stack = vec![CmpTask::#cmp_variant(
                    self as *const _,
                    other as *const _,
                )];
                eq_iterative(&mut stack)
            }
        }

        impl Eq for #category {}

        impl PartialOrd for #category {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for #category {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                // Fast path: try TLS pool
                let tls_result = CMP_TASK_POOL.try_with(|cell| {
                    let mut stack = cell.take();
                    let was_empty = stack.is_empty();

                    // Push initial comparison task
                    stack.push(CmpTask::#cmp_variant(
                        self as *const _,
                        other as *const _,
                    ));

                    // Run the iterative engine
                    let result = cmp_iterative(&mut stack);

                    // Return pool
                    if was_empty {
                        stack.clear();
                    }
                    cell.set(stack);

                    result
                });

                if let Ok(result) = tls_result {
                    return result;
                }

                // Fallback: TLS unavailable (thread shutdown). Use local stack.
                let mut stack = vec![CmpTask::#cmp_variant(
                    self as *const _,
                    other as *const _,
                )];
                cmp_iterative(&mut stack)
            }
        }
    }
}
