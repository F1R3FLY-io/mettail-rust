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

use crate::gen::term_ops::collection_walk::{
    for_each_subterm_pair, plan_for, CollectionPlan, OrderSensitivity, WalkOrder,
};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// ★ #162 — the COLLECTION-ELEMENT BOUNDARY, for both comparison engines
//
// See `collection_walk`'s module header for the defect, the mechanism and the
// proof of the boundary. These two functions are the only places `iterative_cmp`
// decides what to do with a collection of sub-terms, and both route through
// `collection_walk::plan_for` so the decision cannot drift between the eq and
// cmp halves or between the four syntactic positions a collection can occupy
// (`CollectionLiteral` category, `Collection` category, `Regular` field,
// `Binder`/`MultiBinder` pre-scope field).
// =============================================================================

/// The **eq** side: statements that decide equality of the collection pair
/// `(left_expr, right_expr)`, either by pushing one `CmpTask` per element or by
/// the container's own `PartialEq`.
///
/// `PartialEq` is a conjunction, so the ORDER in which positions are compared is
/// unobservable — the per-element pushes go on the stack forward, and the length
/// check (which `Vec::eq` performs first) stays eager because it is O(1) and
/// cannot be expressed as an element task.
fn eq_collection_stmts(
    element_cat: &Ident,
    coll_type: &CollectionType,
    left_expr: &TokenStream,
    right_expr: &TokenStream,
    language: &LanguageDef,
) -> TokenStream {
    match plan_for(element_cat, coll_type, OrderSensitivity::OrderSensitive, language) {
        CollectionPlan::PerElement { element_cat, coll_type } => {
            let task_variant = format_ident!("Cmp{}", element_cat);
            let pushes = for_each_subterm_pair(
                &coll_type,
                left_expr,
                right_expr,
                WalkOrder::Forward,
                &|l, r| {
                    quote! {
                        stack.push(CmpTask::#task_variant(#l as *const _, #r as *const _));
                    }
                },
            );
            quote! {
                // `Vec::eq` is `len` first, then element-wise — reproduced exactly.
                if #left_expr.len() != #right_expr.len() {
                    return false;
                }
                #pushes
            }
        },
        // The declared residue: an unordered container's `PartialEq` is a
        // membership/multiplicity question its own impl answers, and answering it
        // element-wise from here would need the canonical order it computes
        // internally. One host frame, then the element walk is flat again.
        CollectionPlan::WholeValue { .. } => quote! {
            if #left_expr != #right_expr {
                return false;
            }
        },
    }
}

/// The **cmp** side: statements that push the collection pair's contribution to
/// the lexicographic ordering onto the work stack.
///
/// ★ The push order is the subtle part. `Vec<T>: Ord` compares elements over the
/// common prefix and uses LENGTH only as the tiebreak, so the pop order must be
/// `elem₀, elem₁, …, elemₘ₋₁, length`. On a LIFO stack that means pushing the
/// length verdict FIRST and the elements in REVERSE index order.
fn cmp_collection_push_stmts(
    element_cat: &Ident,
    coll_type: &CollectionType,
    left_expr: &TokenStream,
    right_expr: &TokenStream,
    language: &LanguageDef,
) -> TokenStream {
    match plan_for(element_cat, coll_type, OrderSensitivity::OrderSensitive, language) {
        CollectionPlan::PerElement { element_cat, coll_type } => {
            let task_variant = format_ident!("Cmp{}", element_cat);
            let pushes = for_each_subterm_pair(
                &coll_type,
                left_expr,
                right_expr,
                WalkOrder::ReverseForLifo,
                &|l, r| {
                    quote! {
                        stack.push(CmpTask::#task_variant(#l as *const _, #r as *const _));
                    }
                },
            );
            quote! {
                // Pushed first ⇒ popped LAST ⇒ the length is the tiebreak, which
                // is what lexicographic order means.
                stack.push(CmpTask::Verdict(#left_expr.len().cmp(&#right_expr.len())));
                #pushes
            }
        },
        // The declared residue — see `eq_collection_stmts`. The verdict is
        // computed here and consulted in position order, so the ORDER of the
        // comparison is unchanged from the eager form this replaced.
        CollectionPlan::WholeValue { .. } => quote! {
            stack.push(CmpTask::Verdict(#left_expr.cmp(#right_expr)));
        },
    }
}

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
        /// Each per-category variant wraps a pair of raw pointers to values of
        /// the same category. The iterative engine pops tasks, compares
        /// discriminants, and pushes child-pair tasks for `Box<T>` fields and for
        /// the ELEMENTS of every order-faithful collection.
        #[allow(dead_code)]
        enum CmpTask {
            #(#variants,)*
            /// ★ #162 — an ALREADY-COMPUTED verdict, consulted in field order.
            ///
            /// A comparison arm has to interleave two kinds of work: DESCENTS
            /// into sub-terms (which must go on the stack, or the traversal is
            /// Θ(depth)) and LEAF comparisons (which cannot go on a stack of
            /// category-pointer pairs, because a leaf is not a category). Before
            /// this variant existed the only way to order the two was to run the
            /// leaf comparisons EAGERLY, up to and including the last collection
            /// field — which forced every collection to be compared by a
            /// whole-value `PartialEq`/`Ord` call, i.e. by host recursion.
            ///
            /// A leaf comparison is a pure function of that leaf pair alone, so
            /// its RESULT can be computed when the arm runs and consulted when
            /// the engine pops it. That makes the work stack able to express the
            /// WHOLE comparison in field order, and the eager prefix dissolves.
            Verdict(std::cmp::Ordering),
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
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Nullary { label } => {
            quote! { #category::#label }
        },
        VariantKind::Literal { label }
        | VariantKind::CollectionLiteral { label, .. }
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
                    // ★ #162 — a precomputed leaf verdict. `PartialEq` only asks
                    // whether every position agrees, so any non-`Equal` verdict
                    // is a mismatch regardless of direction.
                    CmpTask::Verdict(ord) => {
                        if ord != std::cmp::Ordering::Equal {
                            return false;
                        }
                    }
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
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Nullary { label } => {
            // Nullary: always equal (discriminant already matched)
            quote! {
                (#category::#label, #category::#label) => {}
            }
        },

        // An OPAQUE native leaf (`NumLit(i32)`, `StrLit(String)`) has no
        // sub-terms, so whole-value `PartialEq` is both correct and flat.
        VariantKind::Literal { label } => {
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    if a != b { return false; }
                }
            }
        },

        // ★ #162 — a collection LITERAL is a container OF SUB-TERMS, and sharing
        // the `Literal` arm above is what made `ast_eq` Θ(depth): `a != b` on
        // `&Vec<Proc>` calls `Proc::eq` per element, re-entering this very driver
        // by host recursion with no access to `stack`.
        VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
            let stmts = eq_collection_stmts(
                element_cat,
                coll_type,
                &quote! { a },
                &quote! { b },
                language,
            );
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #stmts
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

        // ★ #162 — the category-DIRECT collection field (`PPar . ps:HashBag(Proc)`),
        // the same boundary as `CollectionLiteral` above.
        VariantKind::Collection { label, element_cat, coll_type } => {
            let stmts = eq_collection_stmts(
                element_cat,
                coll_type,
                &quote! { a },
                &quote! { b },
                language,
            );
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #stmts
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
    language: &LanguageDef,
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
                // ★ #162 — a collection FIELD is the third syntactic position the
                // element boundary appears in, and it gets the same treatment as
                // the two category positions.
                let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
                eq_collection_stmts(
                    &field.category,
                    &coll_type,
                    &quote! { #lname },
                    &quote! { #rname },
                    language,
                )
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
    language: &LanguageDef,
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
            // ★ #162 — the FOURTH syntactic position: a collection in a binder's
            // pre-scope field list.
            let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
            compare_stmts.push(eq_collection_stmts(
                &field.category,
                &coll_type,
                &quote! { #lname },
                &quote! { #rname },
                language,
            ));
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
    language: &LanguageDef,
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
            // ★ #162 — same boundary, MultiBinder pre-scope position.
            let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
            compare_stmts.push(eq_collection_stmts(
                &field.category,
                &coll_type,
                &quote! { #lname },
                &quote! { #rname },
                language,
            ));
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
                    // ★ #162 — a precomputed leaf verdict. Because tasks are
                    // pushed in REVERSE position order, popping them yields
                    // strict left-to-right (lexicographic) semantics: the FIRST
                    // non-`Equal` verdict decides, exactly as `derive(Ord)` does.
                    CmpTask::Verdict(ord) => {
                        if ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return ord;
                        }
                    }
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
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Nullary { label } => {
            // Nullary: always equal
            quote! {
                (#category::#label, #category::#label) => {}
            }
        },

        // An OPAQUE native leaf has no sub-terms: whole-value `Ord` is correct and
        // flat, and it short-circuits here rather than through a `Verdict` push
        // because there is nothing after it in this arm to order against.
        VariantKind::Literal { label } => {
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

        // ★ #162 — the collection-literal boundary on the `Ord` side. `a.cmp(b)`
        // on `&Vec<Proc>` was `Proc::cmp` per element, i.e. host recursion.
        VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
            let pushes = cmp_collection_push_stmts(
                element_cat,
                coll_type,
                &quote! { a },
                &quote! { b },
                language,
            );
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #pushes
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

        // ★ #162 — the category-DIRECT collection field, `Ord` side.
        VariantKind::Collection { label, element_cat, coll_type } => {
            let pushes = cmp_collection_push_stmts(
                element_cat,
                coll_type,
                &quote! { a },
                &quote! { b },
                language,
            );
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #pushes
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
/// ## ★ #162 — the rewrite, and why the ORDER is provably unchanged
///
/// `Ord` on a multi-field variant is LEXICOGRAPHIC in field order: the first
/// field whose comparison is not `Equal` decides. This arm therefore has to
/// interleave two kinds of work in exactly field order — descents into sub-terms
/// and comparisons of leaves — and before `CmpTask::Verdict` existed the task
/// enum could only carry the first kind. What it did instead was an EAGER PREFIX:
///
/// ```text
///   eager_end = (index of the LAST collection field) + 1
///   fields [0, eager_end)  → compared eagerly, in field order, early-returning
///                            ⚠ INCLUDING `Box<Cat>` fields, as `(**l).cmp(&**r)`
///                              — a whole-value re-entry, i.e. HOST RECURSION
///   fields [eager_end, n)  → pushed in REVERSE, so they pop in field order
/// ```
///
/// (Its 130-line comment block, preserved in git history at `iterative_cmp.rs`
/// before this change, is the author walking into the wall from six directions:
/// *"But `CmpTask` only holds `*const Cat`…"*.)
///
/// The rewrite is:
///
/// ```text
///   split = index of the FIRST field that can be expressed as a task
///   fields [0, split)      → compared eagerly, in field order, early-returning
///                            (only leaves and unordered collections land here)
///   fields [split, n)      → pushed in REVERSE field order; leaves become
///                            `Verdict`, `Box<Cat>` becomes a descent, and an
///                            order-faithful collection becomes ONE PUSH PER
///                            ELEMENT plus a trailing length `Verdict`
/// ```
///
/// **Both schemes yield exactly strict field order**, so `Ord` is byte-for-byte
/// the same relation and nothing that sorts `Proc`s moves. Proof: in each scheme
/// the arm is a forward-ordered eager segment followed by a reverse-pushed
/// segment, and a reverse-pushed segment pops in forward order; concatenating a
/// forward prefix `[0, k)` with a forward suffix `[k, n)` is `[0, n)` for any `k`.
/// The two schemes differ only in `k`, and `k` is not observable.
///
/// ⚠ That identity is the load-bearing claim of this change, and it is asserted
/// mechanically rather than by argument alone — `iterative_cmp`'s own unit tests
/// below pin the emitted order, and `ord_is_a_total_order_and_agrees_with_eq`
/// exercises it behaviourally.
///
/// ## What short-circuiting survives
///
/// The eager segment still early-returns, so a leading leaf mismatch costs
/// nothing. Within the pushed segment every `Verdict` is computed when the arm
/// runs, so a variant whose FIRST field differs still evaluates the later
/// leaves' comparisons — wasted work, never a wrong answer, and the scheme it
/// replaced did the same thing for every field before the last collection.
/// ★ #162 — the ONE construction of a `cmp` arm body, shared by `Regular`,
/// `Binder` and `MultiBinder`.
///
/// `positions` are the arm's comparison positions in FIELD ORDER, plus — for the
/// two binder kinds — a trailing `scope_pushes` group that carries the pattern
/// verdict and the body descent. The emitted body is
///
/// ```text
///   [0, split)   compared eagerly, in field order, early-returning
///   [split, …]   pushed in REVERSE, so the engine pops them in field order
/// ```
///
/// where `split` is the index of the first position expressible as a task. See
/// [`generate_cmp_regular_arm`] for the proof that this is exactly strict field
/// order and therefore leaves the `Ord` relation unchanged.
fn cmp_arm_stmts(
    fields: &[FieldInfo],
    left_names: &[Ident],
    right_names: &[Ident],
    scope_pushes: Option<TokenStream>,
    language: &LanguageDef,
) -> Vec<TokenStream> {
    // Can this field's contribution be expressed as work ON THE STACK? A leaf
    // cannot (it is not a category), and neither can an unordered collection (its
    // `Ord` is its own; see `collection_walk`'s boundary) — but a `Box<Cat>`
    // child can, an `Option<Box<Cat>>` child can, and so can every element of an
    // order-faithful collection.
    let is_stack_expressible = |field: &FieldInfo| -> bool {
        if field.is_predicate || field.is_opaque_leaf() {
            return false;
        }
        if !field.is_collection {
            // A boxed category child, optional or not.
            return true;
        }
        // Phase 4 #3: `Option<Container>` is compared by `Option<C>::cmp`, which
        // is the container's own `Ord` under a tag — one whole value, not a
        // sequence of positions.
        if field.is_optional {
            return false;
        }
        let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
        matches!(
            plan_for(&field.category, &coll_type, OrderSensitivity::OrderSensitive, language),
            CollectionPlan::PerElement { .. }
        )
    };

    let split = fields.iter().position(is_stack_expressible).unwrap_or(fields.len());

    let mut stmts: Vec<TokenStream> = Vec::with_capacity(fields.len() + 1);

    // ── the eager segment: leaves and unordered containers, in field order ──
    //
    // Phase 3A-B2 / L9-3: `BehavioralPred` and token-text captures derive `Ord`
    // and have no sub-terms. Phase 4 #3: `Option<Container>` delegates to
    // `Option<C>::cmp`. An unordered container is the declared residue.
    for i in 0..split {
        let lname = &left_names[i];
        let rname = &right_names[i];
        stmts.push(quote! {
            {
                let ord = #lname.cmp(#rname);
                if ord != std::cmp::Ordering::Equal {
                    stack.clear();
                    return ord;
                }
            }
        });
    }

    // ── the pushed segment, in REVERSE position order ──
    //
    // The scope is the LAST position, so it is pushed FIRST.
    if let Some(scope_pushes) = scope_pushes {
        stmts.push(scope_pushes);
    }

    for (i, field) in fields.iter().enumerate().skip(split).rev() {
        let lname = &left_names[i];
        let rname = &right_names[i];

        if field.is_predicate || field.is_opaque_leaf() {
            // A leaf inside the pushed segment: its verdict is computed now and
            // consulted in position order. This is the case the eager prefix
            // could not express, and the reason it had to swallow collections.
            stmts.push(quote! {
                stack.push(CmpTask::Verdict(#lname.cmp(#rname)));
            });
            continue;
        }

        if field.is_optional {
            if field.is_collection {
                stmts.push(quote! {
                    stack.push(CmpTask::Verdict(#lname.cmp(#rname)));
                });
                continue;
            }
            // Opt-Group, `Option<Box<Cat>>`: `None < Some(_)`, and `Some` vs
            // `Some` is the inner comparison. Exactly one push on every path, so
            // the reverse-push discipline is preserved.
            //
            // ★ This replaces an eager `(**__l).cmp(&**__r)` — a whole-value
            // re-entry that was Θ(depth) in its own right, independently of any
            // collection.
            let task_variant = format_ident!("Cmp{}", field.category);
            stmts.push(quote! {
                match (#lname.as_ref(), #rname.as_ref()) {
                    (None, None) => {}
                    (None, Some(_)) => {
                        stack.push(CmpTask::Verdict(std::cmp::Ordering::Less));
                    }
                    (Some(_), None) => {
                        stack.push(CmpTask::Verdict(std::cmp::Ordering::Greater));
                    }
                    (Some(__l), Some(__r)) => {
                        stack.push(CmpTask::#task_variant(
                            __l.as_ref() as *const _,
                            __r.as_ref() as *const _,
                        ));
                    }
                }
            });
            continue;
        }

        if field.is_collection {
            let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
            stmts.push(cmp_collection_push_stmts(
                &field.category,
                &coll_type,
                &quote! { #lname },
                &quote! { #rname },
                language,
            ));
            continue;
        }

        // ★ A boxed category child. Before #162 a child at a position BEFORE the
        // last collection was compared by an eager `(**l).cmp(&**r)` — a
        // whole-value re-entry — purely because the eager prefix had to reach the
        // collection. Now every child is a task.
        let task_variant = format_ident!("Cmp{}", field.category);
        stmts.push(quote! {
            stack.push(CmpTask::#task_variant(&**#lname as *const _, &**#rname as *const _));
        });
    }

    stmts
}

fn generate_cmp_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    language: &LanguageDef,
) -> TokenStream {
    let left_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("r{}", i)).collect();
    let stmts = cmp_arm_stmts(fields, &left_names, &right_names, None, language);

    quote! {
        (#category::#label(#(ref #left_names),*), #category::#label(#(ref #right_names),*)) => {
            #(#stmts)*
        }
    }
}

/// Generate cmp arm for a Binder variant.
///
/// The scope is the arm's LAST comparison position: its pattern is a leaf (a
/// hash-ordered `Binder<String>`) and its body is a descent, so the group is one
/// `Verdict` followed by one `Cmp{Body}`. Pushed FIRST, because the pushed
/// segment goes on in reverse position order — see [`cmp_arm_stmts`].
fn generate_cmp_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];
    let body_task = format_ident!("Cmp{}", body_cat);

    // Pop order within the group must be pattern-then-body, so the pushes are
    // body-then-pattern. Unchanged from the pre-#162 arm in WHAT it compares —
    // only the body descent's ordering relative to the pre-scope fields moves,
    // and it moves to the position the field order says it should have.
    let scope_pushes = quote! {
        {
            let l_scope = #scope_left.inner();
            let r_scope = #scope_right.inner();
            // Pattern comparison: hash-based ordering, same as `Scope::cmp`.
            let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                let mut h = std::collections::hash_map::DefaultHasher::new();
                std::hash::Hash::hash(p, &mut h);
                std::hash::Hasher::finish(&h)
            };
            let pat_ord =
                hash_pat(&l_scope.unsafe_pattern).cmp(&hash_pat(&r_scope.unsafe_pattern));
            let l_body: *const #body_cat = &*l_scope.unsafe_body;
            let r_body: *const #body_cat = &*r_scope.unsafe_body;
            stack.push(CmpTask::#body_task(l_body, r_body));
            stack.push(CmpTask::Verdict(pat_ord));
        }
    };

    let stmts =
        cmp_arm_stmts(pre_scope_fields, &left_names, &right_names, Some(scope_pushes), language);

    quote! {
        (#category::#label(#(ref #left_names),*), #category::#label(#(ref #right_names),*)) => {
            #(#stmts)*
        }
    }
}

/// Generate cmp arm for a MultiBinder variant.
///
/// Identical to [`generate_cmp_binder_arm`] except that the pattern is a
/// `Vec<Binder<String>>`, ordered length-first and then element-wise by binder
/// hash. That whole judgement is a leaf — no sub-terms — so it collapses to ONE
/// `Verdict`, computed with `Ordering::then_with` so the length still dominates.
fn generate_cmp_multi_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];
    let body_task = format_ident!("Cmp{}", body_cat);

    let scope_pushes = quote! {
        {
            let l_scope = #scope_left.inner();
            let r_scope = #scope_right.inner();
            let l_pats = &l_scope.unsafe_pattern;
            let r_pats = &r_scope.unsafe_pattern;
            let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                let mut h = std::collections::hash_map::DefaultHasher::new();
                std::hash::Hash::hash(p, &mut h);
                std::hash::Hasher::finish(&h)
            };
            // Length dominates, then the binder hashes element-wise — the exact
            // judgement the pre-#162 arm made with two early returns.
            let pat_ord = l_pats.len().cmp(&r_pats.len()).then_with(|| {
                l_pats
                    .iter()
                    .zip(r_pats.iter())
                    .map(|(lp, rp)| hash_pat(lp).cmp(&hash_pat(rp)))
                    .find(|o| *o != std::cmp::Ordering::Equal)
                    .unwrap_or(std::cmp::Ordering::Equal)
            });
            let l_body: *const #body_cat = &*l_scope.unsafe_body;
            let r_body: *const #body_cat = &*r_scope.unsafe_body;
            stack.push(CmpTask::#body_task(l_body, r_body));
            stack.push(CmpTask::Verdict(pat_ord));
        }
    };

    let stmts =
        cmp_arm_stmts(pre_scope_fields, &left_names, &right_names, Some(scope_pushes), language);

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
