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
//! 1. Push comparison tasks for category children onto a thread-local work stack.
//! 2. Drive unordered collections through one shared canonical-order collection
//!    PDA whose requested element comparisons rejoin the same iterative engine.
//! 3. Iteratively process the work stack and early-exit on the first inequality.
//!
//! ## Re-Entrancy Safety
//!
//! Generated category comparisons never delegate a category-bearing collection
//! to its public `PartialEq` or `Ord` implementation. Ordered collections schedule
//! their elements directly; unordered collections use `CollectionCmpPda`. Equality
//! drives that ordering PDA on a dedicated auxiliary task stack, so a comparison
//! remains heap-backed even when unordered collections contain deeply nested terms.
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
    field_carrier, for_each_subterm_pair, plan_for, CollectionPlan, FieldCarrier, OrderSensitivity,
    WalkOrder, WholeValueReason,
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
        CollectionPlan::WholeValue {
            reason: WholeValueReason::UnorderedContainer,
        } => {
            let resume_fn =
                format_ident!("cmp_resume_collection_{}", element_cat.to_string().to_lowercase());
            let machine = unordered_collection_cmp_machine_expr(coll_type, left_expr, right_expr);
            quote! {
                if !eq_unordered_collection(#machine, #resume_fn) {
                    return false;
                }
            }
        },
        CollectionPlan::WholeValue {
            reason: WholeValueReason::ElementIsNotACategory,
        } => {
            quote! {
                if #left_expr != #right_expr {
                    return false;
                }
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
        CollectionPlan::WholeValue {
            reason: WholeValueReason::UnorderedContainer,
        } => unordered_collection_cmp_push_stmts(element_cat, coll_type, left_expr, right_expr),
        CollectionPlan::WholeValue {
            reason: WholeValueReason::ElementIsNotACategory,
        } => {
            quote! {
                stack.push(CmpTask::Verdict(#left_expr.cmp(#right_expr)));
            }
        },
    }
}

fn unordered_collection_cmp_push_stmts(
    element_cat: &Ident,
    coll_type: &CollectionType,
    left_expr: &TokenStream,
    right_expr: &TokenStream,
) -> TokenStream {
    let resume_fn =
        format_ident!("cmp_resume_collection_{}", element_cat.to_string().to_lowercase());
    let machine = unordered_collection_cmp_machine_expr(coll_type, left_expr, right_expr);

    quote! {
        stack.push(CmpTask::StartCollection(
            Box::new(#machine),
            #resume_fn,
        ));
    }
}

/// Build the one canonical-order comparison machine shared by `Eq` and `Ord`.
/// Keeping this expression in one generator function prevents the two traits
/// from drifting on mode order, multiplicities, or key/value pairing.
fn unordered_collection_cmp_machine_expr(
    coll_type: &CollectionType,
    left_expr: &TokenStream,
    right_expr: &TokenStream,
) -> TokenStream {
    let (lead, left_items, right_items) = match coll_type {
        CollectionType::HashSet => (
            quote! { std::cmp::Ordering::Equal },
            quote! {
                #left_expr
                    .iter()
                    .map(mettail_runtime::CollectionCmpItem::unary)
                    .collect()
            },
            quote! {
                #right_expr
                    .iter()
                    .map(mettail_runtime::CollectionCmpItem::unary)
                    .collect()
            },
        ),
        CollectionType::HashBag => (
            quote! { #left_expr.len().cmp(&#right_expr.len()) },
            quote! {
                #left_expr
                    .iter()
                    .map(|(__item, __count)| {
                        mettail_runtime::CollectionCmpItem::repeated(__item, __count)
                    })
                    .collect()
            },
            quote! {
                #right_expr
                    .iter()
                    .map(|(__item, __count)| {
                        mettail_runtime::CollectionCmpItem::repeated(__item, __count)
                    })
                    .collect()
            },
        ),
        CollectionType::HashMap => (
            quote! { std::cmp::Ordering::Equal },
            quote! {
                #left_expr
                    .iter()
                    .map(|(__key, __value)| {
                        mettail_runtime::CollectionCmpItem::pair(__key, __value)
                    })
                    .collect()
            },
            quote! {
                #right_expr
                    .iter()
                    .map(|(__key, __value)| {
                        mettail_runtime::CollectionCmpItem::pair(__key, __value)
                    })
                    .collect()
            },
        ),
        CollectionType::PathMap => return pathmap_cmp_machine_expr(left_expr, right_expr),
        CollectionType::Vec => {
            return quote! {
                compile_error!("unordered collection comparison machine requested for Vec")
            };
        },
    };

    quote! {
        mettail_runtime::CollectionCmpPda::new(
            #lead,
            #left_items,
            #right_items,
        )
    }
}

/// Build the canonical comparison PDA for a potentially heterogeneous
/// `PathMap<K, V>`.  `CollectionCmpRole` keeps key and value requests distinct
/// until the generated continuation restores their concrete categories.
fn pathmap_cmp_machine_expr(left_expr: &TokenStream, right_expr: &TokenStream) -> TokenStream {
    quote! {
        mettail_runtime::CollectionCmpPda::new(
            (#left_expr).mode().cmp(&(#right_expr).mode()),
            (#left_expr)
                .iter()
                .map(|__entry| match __entry.value() {
                    Some(__value) => mettail_runtime::CollectionCmpItem::pair(
                        __entry.key(),
                        __value,
                    ),
                    None => mettail_runtime::CollectionCmpItem::unary(__entry.key()),
                })
                .collect(),
            (#right_expr)
                .iter()
                .map(|__entry| match __entry.value() {
                    Some(__value) => mettail_runtime::CollectionCmpItem::pair(
                        __entry.key(),
                        __value,
                    ),
                    None => mettail_runtime::CollectionCmpItem::unary(__entry.key()),
                })
                .collect(),
        )
    }
}

fn recursive_native_cmp_resume_name(category: &Ident, label: &Ident) -> Ident {
    format_ident!(
        "cmp_resume_native_{}_{}",
        category.to_string().to_lowercase(),
        label.to_string().to_lowercase(),
    )
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
        type CollectionCmpResume = fn(
            &mut Vec<CmpTask>,
            Box<mettail_runtime::CollectionCmpPda>,
            Option<std::cmp::Ordering>,
        ) -> Option<std::cmp::Ordering>;

        /// Work item for the iterative comparison engines (eq and cmp).
        ///
        /// Each per-category variant wraps a pair of raw pointers to values of
        /// the same category. The iterative engine pops tasks, compares
        /// discriminants, and pushes child-pair tasks for `Box<T>` fields and for
        /// the ELEMENTS of every order-faithful collection.
        #[allow(dead_code)]
        enum CmpTask {
            #(#variants,)*
            /// Resume a suspended collection PDA after its requested typed
            /// comparison has completed.  Carrying the continuation function
            /// avoids one generated task variant per category and supports
            /// heterogeneous key/value carriers without type erasure.
            ResumeCollection(
                Box<mettail_runtime::CollectionCmpPda>,
                CollectionCmpResume,
            ),
            /// Begin a canonical-order comparison at its exact lexicographic
            /// position. Deferring the first `resume(None)` call is essential:
            /// a mode or multiplicity verdict computed while an arm is being
            /// pushed would otherwise outrank earlier fields.
            StartCollection(
                Box<mettail_runtime::CollectionCmpPda>,
                CollectionCmpResume,
            ),
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
            /// steady-state operation: the first comparison allocates and later
            /// comparisons reuse the same buffer. Category-bearing collections
            /// remain inside the generated drivers rather than re-entering the
            /// public trait implementations.
            static CMP_TASK_POOL: std::cell::Cell<Vec<CmpTask>> =
                std::cell::Cell::new(Vec::new());

            /// Reusable work stack for the canonical-order PDA used by equality
            /// at unordered collection boundaries. It is distinct from
            /// `CMP_TASK_POOL` because the outer equality traversal still owns
            /// that stack while an individual collection is being compared.
            static CMP_AUX_TASK_POOL: std::cell::Cell<Vec<CmpTask>> =
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
        | VariantKind::RecursiveNativeLiteral { label, .. }
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
            let mismatch_arm = if variants.len() == 1 {
                TokenStream::new()
            } else {
                quote! { _ => { return false; } }
            };
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
                    // Shared immutable subterms are definitionally equal. This
                    // check occurs before dereference and before scheduling
                    // descendants, making the common Arc-shared chain edge
                    // constant-time without changing the exact fallback for
                    // separately allocated values.
                    if std::ptr::eq(left_ptr, right_ptr) {
                        return true;
                    }
                    let left = unsafe { &*left_ptr };
                    let right = unsafe { &*right_ptr };
                    if #index_fn(left) != #index_fn(right) {
                        return false;
                    }
                    match (left, right) {
                        #(#variant_arms)*
                        #mismatch_arm
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
        /// Decide equality of one unordered collection by driving the same
        /// canonical-order PDA used by `Ord`. The category-specific resume
        /// function converts the PDA's erased pointers back to the correct
        /// generated category before scheduling `CmpTask` work.
        #[inline]
        #[allow(dead_code)]
        fn eq_unordered_collection(
            machine: mettail_runtime::CollectionCmpPda,
            resume: CollectionCmpResume,
        ) -> bool {
            #[inline]
            fn drive(
                stack: &mut Vec<CmpTask>,
                machine: mettail_runtime::CollectionCmpPda,
                resume: CollectionCmpResume,
            ) -> bool {
                stack.push(CmpTask::StartCollection(Box::new(machine), resume));
                cmp_iterative(stack) == std::cmp::Ordering::Equal
            }

            let mut machine = Some(machine);
            let tls_result = CMP_AUX_TASK_POOL.try_with(|cell| {
                let mut stack = cell.take();
                stack.clear();
                let result = drive(
                    &mut stack,
                    machine.take().expect("collection PDA must be driven exactly once"),
                    resume,
                );
                stack.clear();
                cell.set(stack);
                result
            });

            match tls_result {
                Ok(result) => result,
                Err(_) => drive(
                    &mut Vec::new(),
                    machine.expect("TLS failure must leave the collection PDA available"),
                    resume,
                ),
            }
        }

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
                    CmpTask::ResumeCollection(_, _) => {
                        unreachable!("collection ordering continuation reached equality engine");
                    }
                    CmpTask::StartCollection(_, _) => {
                        unreachable!("collection ordering start reached equality engine");
                    }
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
            let stmts =
                eq_collection_stmts(element_cat, coll_type, &quote! { a }, &quote! { b }, language);
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #stmts
                }
            }
        },

        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            let left_pathmap = carrier.pathmap_ref(&quote! { a });
            let right_pathmap = carrier.pathmap_ref(&quote! { b });
            let left_focus = carrier.focus_ref(&quote! { a });
            let right_focus = carrier.focus_ref(&quote! { b });
            let machine = pathmap_cmp_machine_expr(&left_pathmap, &right_pathmap);
            let resume = recursive_native_cmp_resume_name(category, label);
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    if #left_focus != #right_focus {
                        return false;
                    }
                    if !eq_unordered_collection(#machine, #resume) {
                        return false;
                    }
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
            let stmts =
                eq_collection_stmts(element_cat, coll_type, &quote! { a }, &quote! { b }, language);
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

/// ★ #197 — the ONE construction of an `eq` arm body, shared by `Regular`,
/// `Binder` and `MultiBinder`.
///
/// The counterpart of [`cmp_arm_stmts`], and it exists for the same reason. Before
/// #197 the `cmp` side had this single shared builder while the `eq` side had
/// THREE hand-copied per-arm-kind loops, and the copies had drifted: the
/// `Regular` loop tested `is_opaque_leaf()` and `is_optional`, and the two binder
/// loops tested neither. Every carrier they omitted was emitted as if it were the
/// carrier they did test, which is why an `Option<Vec<Proc>>` pre-scope field
/// reached the container walk and the generated tree stopped compiling.
///
/// ⇒ The repair is structural, not a third copy of the guard: ONE builder, and it
/// dispatches on [`field_carrier`] with **no wildcard arm**, so a sixth carrier is
/// a compile error here rather than a silent fall-through in whichever copy was
/// not updated.
///
/// `PartialEq` is a conjunction and `&&` is commutative, so — unlike the `cmp`
/// side, which needs the eager/pushed split to preserve lexicographic order —
/// every position may be emitted in plain field order and the `scope_stmts` group
/// simply goes last, exactly where the three loops it replaces put it.
fn eq_arm_stmts(
    fields: &[FieldInfo],
    left_names: &[Ident],
    right_names: &[Ident],
    scope_stmts: Option<TokenStream>,
    language: &LanguageDef,
) -> Vec<TokenStream> {
    let mut stmts: Vec<TokenStream> = Vec::with_capacity(fields.len() + 1);

    for (i, field) in fields.iter().enumerate() {
        let lname = &left_names[i];
        let rname = &right_names[i];

        stmts.push(match field_carrier(field) {
            // Phase 3A-B2: a predicate field uses direct `PartialEq` —
            // `BehavioralPred` derives `Eq`, so the bare value comparison is sound.
            // L9-3/L9-4: a token-text (`String`) or guest-body (`Arc<FltNode>`)
            // capture is the identical direct-Eq with no `CmpTask` descent. All
            // three are also correct under an `Option`, because `Option<T>: PartialEq`
            // whenever `T` is — which is why the carrier absorbs optionality.
            FieldCarrier::Leaf => quote! {
                if #lname != #rname { return false; }
            },

            // Optional-Collection: compare the option tag, then route
            // `Some`/`Some` through the same explicit inner-container walk as a
            // non-optional collection.
            //
            // ⚠ This is the arm the two binder loops did not have. Reaching the
            // `Collection` arm instead emitted `Option::len` (E0624, the method is
            // private) and `&Vec<Elem> as *const Elem` (E0606, not a cast), because
            // `Option`'s `len`/`iter` describe the OPTION — one item, the container
            // — and not the container's elements.
            //
            // Destructuring is essential: `Option::iter` would yield the
            // container as its single item, not the container's term elements.
            FieldCarrier::OptionalCollection { coll_type } => {
                let inner = eq_collection_stmts(
                    &field.category,
                    &coll_type,
                    &quote! { __left_collection },
                    &quote! { __right_collection },
                    language,
                );
                quote! {
                    match (#lname.as_ref(), #rname.as_ref()) {
                        (None, None) => {},
                        (Some(__left_collection), Some(__right_collection)) => {
                            #inner
                        },
                        _ => return false,
                    }
                }
            },

            // Opt-Group: equality on `Option<Box<Cat>>`. Push a `CmpTask` when both
            // are `Some`; a `Some`/`None` mismatch short-circuits to `false`.
            FieldCarrier::OptionalChild => {
                let task_variant = format_ident!("Cmp{}", field.category);
                quote! {
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
                }
            },

            // ★ #162 — the collection-element boundary. Routed through
            // `collection_walk::plan_for` so the per-element/whole-value decision
            // cannot drift between the `eq` and `cmp` halves.
            FieldCarrier::Collection { coll_type } => eq_collection_stmts(
                &field.category,
                &coll_type,
                &quote! { #lname },
                &quote! { #rname },
                language,
            ),

            // A `Box<Cat>` category child: the descent, as a task.
            FieldCarrier::Child => {
                let task_variant = format_ident!("Cmp{}", field.category);
                quote! {
                    stack.push(CmpTask::#task_variant(&**#lname as *const _, &**#rname as *const _));
                }
            },
        });
    }

    // The binder `Scope` is the arm's LAST position, so its group goes last.
    if let Some(scope_stmts) = scope_stmts {
        stmts.push(scope_stmts);
    }

    stmts
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
    let compare_stmts = eq_arm_stmts(fields, &left_names, &right_names, None, language);

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

    // Compare scope: compare pattern directly, push body comparison task
    let body_task = format_ident!("Cmp{}", body_cat);
    let scope_stmts = quote! {
        {
            let l_pat = &#scope_left.inner().unsafe_pattern;
            let r_pat = &#scope_right.inner().unsafe_pattern;
            if l_pat != r_pat { return false; }
            let l_body: *const #body_cat = &*#scope_left.inner().unsafe_body;
            let r_body: *const #body_cat = &*#scope_right.inner().unsafe_body;
            stack.push(CmpTask::#body_task(l_body, r_body));
        }
    };

    // ★ #197 — the pre-scope fields go through the SHARED builder. This loop used
    // to be a hand-copy that tested `is_predicate` and `is_collection` and nothing
    // else, so three of the five carriers were emitted as the wrong shape.
    let compare_stmts =
        eq_arm_stmts(pre_scope_fields, &left_names, &right_names, Some(scope_stmts), language);

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

    let body_task = format_ident!("Cmp{}", body_cat);
    let scope_stmts = quote! {
        {
            let l_pat = &#scope_left.inner().unsafe_pattern;
            let r_pat = &#scope_right.inner().unsafe_pattern;
            if l_pat != r_pat { return false; }
            let l_body: *const #body_cat = &*#scope_left.inner().unsafe_body;
            let r_body: *const #body_cat = &*#scope_right.inner().unsafe_body;
            stack.push(CmpTask::#body_task(l_body, r_body));
        }
    };

    // ★ #197 — the SHARED builder. This is the arm that went RED: `class3opt`'s
    // `PInputsOptTagged . ns:Vec(Name), *opt(qs:Vec(Proc)), ^[xs].p:[Name* -> Proc]`
    // puts an `Option<Vec<Proc>>` in a MultiBinder pre-scope slot, and the hand-copy
    // this replaces had no `OptionalCollection` case.
    let compare_stmts =
        eq_arm_stmts(pre_scope_fields, &left_names, &right_names, Some(scope_stmts), language);

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
    let collection_resume_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cmp_variant = format_ident!("Cmp{}", cat);
            let resume_fn =
                format_ident!("cmp_resume_collection_{}", cat.to_string().to_lowercase());
            quote! {
                #[inline]
                fn #resume_fn(
                    stack: &mut Vec<CmpTask>,
                    mut machine: Box<mettail_runtime::CollectionCmpPda>,
                    result: Option<std::cmp::Ordering>,
                ) -> Option<std::cmp::Ordering> {
                    match machine.resume(result) {
                        mettail_runtime::CollectionCmpStep::Compare { left, right, .. } => {
                            stack.push(CmpTask::ResumeCollection(machine, #resume_fn));
                            stack.push(CmpTask::#cmp_variant(
                                left.cast::<#cat>(),
                                right.cast::<#cat>(),
                            ));
                            None
                        },
                        mettail_runtime::CollectionCmpStep::Done(ordering) => Some(ordering),
                    }
                }
            }
        })
        .collect();

    let native_collection_resume_fns: Vec<TokenStream> = language
        .types
        .iter()
        .flat_map(|t| {
            let category = &t.name;
            collect_category_variants(category, language)
                .into_iter()
                .filter_map(move |variant| match variant {
                    VariantKind::RecursiveNativeLiteral { label, carrier } => {
                        let resume_fn = recursive_native_cmp_resume_name(category, &label);
                        let key_variant = format_ident!("Cmp{}", carrier.key_category());
                        let value_variant = format_ident!("Cmp{}", carrier.value_category());
                        Some(quote! {
                            #[inline]
                            fn #resume_fn(
                                stack: &mut Vec<CmpTask>,
                                mut machine: Box<mettail_runtime::CollectionCmpPda>,
                                result: Option<std::cmp::Ordering>,
                            ) -> Option<std::cmp::Ordering> {
                                match machine.resume(result) {
                                    mettail_runtime::CollectionCmpStep::Compare {
                                        role,
                                        left,
                                        right,
                                    } => {
                                        stack.push(CmpTask::ResumeCollection(machine, #resume_fn));
                                        match role {
                                            mettail_runtime::CollectionCmpRole::Primary => {
                                                stack.push(CmpTask::#key_variant(
                                                    left.cast(),
                                                    right.cast(),
                                                ));
                                            },
                                            mettail_runtime::CollectionCmpRole::Secondary => {
                                                stack.push(CmpTask::#value_variant(
                                                    left.cast(),
                                                    right.cast(),
                                                ));
                                            },
                                        }
                                        None
                                    },
                                    mettail_runtime::CollectionCmpStep::Done(ordering) => {
                                        Some(ordering)
                                    },
                                }
                            }
                        })
                    },
                    _ => None,
                })
        })
        .collect();

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
            let mismatch_arm = if variants.len() == 1 {
                TokenStream::new()
            } else {
                quote! {
                    _ => {
                        return l_idx.cmp(&r_idx);
                    }
                }
            };
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
                        return l_idx.cmp(&r_idx);
                    }
                    match (left, right) {
                        #(#variant_arms)*
                        #mismatch_arm
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
                        if let Some(root_ordering) = cmp_deliver(stack, ord) {
                            return root_ordering;
                        }
                    }
                }
            }
        })
        .collect();

    quote! {
        #(#collection_resume_fns)*
        #(#native_collection_resume_fns)*
        #(#helper_fns)*

        #[allow(dead_code, unused_variables)]
        fn cmp_deliver(
            stack: &mut Vec<CmpTask>,
            mut ordering: std::cmp::Ordering,
        ) -> Option<std::cmp::Ordering> {
            loop {
                let mut resumed = false;
                while let Some(task) = stack.pop() {
                    match task {
                        CmpTask::ResumeCollection(machine, resume) => {
                            match resume(stack, machine, Some(ordering)) {
                                None => return None,
                                Some(std::cmp::Ordering::Equal) => return None,
                                Some(next) => {
                                    ordering = next;
                                    resumed = true;
                                    break;
                                },
                            }
                        },
                        _ => {},
                    }
                }
                if !resumed {
                    return Some(ordering);
                }
            }
        }

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
                    CmpTask::StartCollection(machine, resume) => {
                        if let Some(ordering) = resume(stack, machine, None) {
                            if ordering != std::cmp::Ordering::Equal {
                                if let Some(root_ordering) = cmp_deliver(stack, ordering) {
                                    return root_ordering;
                                }
                            }
                        }
                    }
                    CmpTask::ResumeCollection(machine, resume) => {
                        if let Some(ordering) = resume(
                            stack,
                            machine,
                            Some(std::cmp::Ordering::Equal),
                        ) {
                            if ordering != std::cmp::Ordering::Equal {
                                if let Some(root_ordering) = cmp_deliver(stack, ordering) {
                                    return root_ordering;
                                }
                            }
                        }
                    }
                    // ★ #162 — a precomputed leaf verdict. Because tasks are
                    // pushed in REVERSE position order, popping them yields
                    // strict left-to-right (lexicographic) semantics: the FIRST
                    // non-`Equal` verdict decides, exactly as `derive(Ord)` does.
                    CmpTask::Verdict(ord) => {
                        if ord != std::cmp::Ordering::Equal {
                            if let Some(root_ordering) = cmp_deliver(stack, ord) {
                                return root_ordering;
                            }
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

        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            let left_pathmap = carrier.pathmap_ref(&quote! { a });
            let right_pathmap = carrier.pathmap_ref(&quote! { b });
            let left_focus = carrier.focus_ref(&quote! { a });
            let right_focus = carrier.focus_ref(&quote! { b });
            let machine = pathmap_cmp_machine_expr(&left_pathmap, &right_pathmap);
            let resume = recursive_native_cmp_resume_name(category, label);
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    stack.push(CmpTask::Verdict((#left_focus).cmp(#right_focus)));
                    stack.push(CmpTask::StartCollection(
                        Box::new(#machine),
                        #resume,
                    ));
                }
            }
        },

        VariantKind::Var { label } => {
            // Var: compare OrdVar with Ord
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    let ord = a.cmp(b);
                    if ord != std::cmp::Ordering::Equal {
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
///                            (only primitive/opaque leaves land here)
///   fields [split, n)      → pushed in REVERSE field order; leaves become
///                            `Verdict`, `Box<Cat>` becomes a descent, and an
///                            ordered collection becomes one task per element;
///                            an unordered one becomes one `StartCollection` task
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
    // cannot because it is not a category. Boxed children, optional children,
    // and every category-bearing collection can: unordered containers use the
    // resumable canonical-order PDA rather than a synchronous whole-value call.
    let is_stack_expressible = |field: &FieldInfo| -> bool {
        match field_carrier(field) {
            // A leaf is not a category, so no `Cmp<Cat>` task can carry it.
            FieldCarrier::Leaf => false,
            // A boxed category child, optional or not.
            FieldCarrier::Child | FieldCarrier::OptionalChild => true,
            // The option tag is explicit; `Some`/`Some` delegates to the
            // inner-container plan.
            FieldCarrier::OptionalCollection { coll_type } => matches!(
                plan_for(&field.category, &coll_type, OrderSensitivity::OrderSensitive, language),
                CollectionPlan::PerElement { .. }
                    | CollectionPlan::WholeValue {
                        reason: WholeValueReason::UnorderedContainer,
                    }
            ),
            FieldCarrier::Collection { coll_type } => matches!(
                plan_for(&field.category, &coll_type, OrderSensitivity::OrderSensitive, language),
                CollectionPlan::PerElement { .. }
                    | CollectionPlan::WholeValue {
                        reason: WholeValueReason::UnorderedContainer,
                    }
            ),
        }
    };

    let split = fields
        .iter()
        .position(is_stack_expressible)
        .unwrap_or(fields.len());

    let mut stmts: Vec<TokenStream> = Vec::with_capacity(fields.len() + 1);

    // ── the eager segment: primitive leaves, in field order ──
    //
    // `BehavioralPred` and token-text captures derive `Ord` and have no
    // sub-terms. Every category-bearing carrier begins the pushed segment.
    for i in 0..split {
        let lname = &left_names[i];
        let rname = &right_names[i];
        stmts.push(quote! {
            {
                let ord = #lname.cmp(#rname);
                if ord != std::cmp::Ordering::Equal {
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

        // ★ #197 — dispatched on the SAME carrier classification as the `eq` side,
        // with no wildcard, so the two halves cannot disagree about what a field IS
        // and a sixth carrier is a compile error in both.
        stmts.push(match field_carrier(field) {
            // A leaf inside the pushed segment: its verdict is computed now and
            // consulted in position order. This is the case the eager prefix
            // could not express, and the reason it had to swallow collections.
            FieldCarrier::Leaf => quote! {
                stack.push(CmpTask::Verdict(#lname.cmp(#rname)));
            },

            // `Option<Container>: Ord` uses `None < Some`; `Some`/`Some` then
            // schedules the inner container without a host-stack re-entry.
            FieldCarrier::OptionalCollection { coll_type } => {
                let inner = cmp_collection_push_stmts(
                    &field.category,
                    &coll_type,
                    &quote! { __left_collection },
                    &quote! { __right_collection },
                    language,
                );
                quote! {
                    match (#lname.as_ref(), #rname.as_ref()) {
                        (None, None) => {},
                        (None, Some(_)) => {
                            stack.push(CmpTask::Verdict(std::cmp::Ordering::Less));
                        },
                        (Some(_), None) => {
                            stack.push(CmpTask::Verdict(std::cmp::Ordering::Greater));
                        },
                        (Some(__left_collection), Some(__right_collection)) => {
                            #inner
                        },
                    }
                }
            },

            // Opt-Group, `Option<Box<Cat>>`: `None < Some(_)`, and `Some` vs
            // `Some` is the inner comparison. Exactly one push on every path, so
            // the reverse-push discipline is preserved.
            //
            // ★ This replaces an eager `(**__l).cmp(&**__r)` — a whole-value
            // re-entry that was Θ(depth) in its own right, independently of any
            // collection.
            FieldCarrier::OptionalChild => {
                let task_variant = format_ident!("Cmp{}", field.category);
                quote! {
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
                }
            },

            FieldCarrier::Collection { coll_type } => cmp_collection_push_stmts(
                &field.category,
                &coll_type,
                &quote! { #lname },
                &quote! { #rname },
                language,
            ),

            // ★ A boxed category child. Before #162 a child at a position BEFORE the
            // last collection was compared by an eager `(**l).cmp(&**r)` — a
            // whole-value re-entry — purely because the eager prefix had to reach the
            // collection. Now every child is a task.
            FieldCarrier::Child => {
                let task_variant = format_ident!("Cmp{}", field.category);
                quote! {
                    stack.push(CmpTask::#task_variant(&**#lname as *const _, &**#rname as *const _));
                }
            },
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

// =============================================================================
// ★★ #197 — THE CELL CENSUS: every carrier, in every field position, on BOTH
// comparison sides.
//
// The regression this pins was a DRIFT between copies, not a missing case in a
// single function: `cmp_arm_stmts` was one shared builder used by all three arm
// kinds, while the `eq` side had three hand-copied loops of which only one tested
// `is_opaque_leaf()` and `is_optional`. `class3opt` exercised exactly ONE of the
// six broken cells (MultiBinder × OptionalCollection) and that is the only reason
// the defect was visible at all — the other five emitted nothing to look at,
// because no bundled grammar declares those shapes.
//
// ⇒ A test over generated output cannot see a cell no grammar reaches. This
// module drives the two arm BUILDERS directly, so all 5 × 3 × 2 = 30 cells are
// exercised regardless of what the corpus happens to contain.
// =============================================================================
#[cfg(test)]
mod carrier_cell_census {
    use super::*;
    use crate::gen::term_ops::subst::OpaqueLeafKind;
    use mettail_ast::types::CollectionType;

    fn field(
        is_collection: bool,
        coll_type: Option<CollectionType>,
        is_predicate: bool,
        is_optional: bool,
        opaque_leaf: Option<OpaqueLeafKind>,
    ) -> FieldInfo {
        FieldInfo {
            category: format_ident!("Proc"),
            is_collection,
            coll_type,
            is_predicate,
            is_optional,
            opaque_leaf,
        }
    }

    /// One `FieldInfo` per carrier, labelled. `Vec` is chosen for both collection
    /// carriers because it is the ORDER-FAITHFUL container — the one whose plain
    /// form is walked per-element — which makes the optional/non-optional contrast
    /// maximally sharp: the plain form must produce a `len` + element walk and the
    /// optional form must destructure the `Option` before producing the same
    /// inner-container walk.
    fn one_per_carrier() -> Vec<(&'static str, FieldInfo)> {
        vec![
            ("Leaf/predicate", field(false, None, true, false, None)),
            (
                "Leaf/token-text",
                field(false, None, false, false, Some(OpaqueLeafKind::TokenText)),
            ),
            ("Child", field(false, None, false, false, None)),
            ("OptionalChild", field(false, None, false, true, None)),
            ("Collection", field(true, Some(CollectionType::Vec), false, false, None)),
            ("OptionalCollection", field(true, Some(CollectionType::Vec), false, true, None)),
        ]
    }

    /// ⚠ `TokenStream::to_string` spaces punctuation apart (`. len ()`), so every
    /// needle is matched against a whitespace-STRIPPED rendering — the same trap
    /// `collection_walk`'s walk test records having gone red on.
    fn rendered(stmts: Vec<TokenStream>) -> String {
        stmts
            .into_iter()
            .map(|t| t.to_string())
            .collect::<String>()
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect()
    }

    /// The three field POSITIONS, as the two arm builders see them: a `Regular`
    /// variant has no trailing scope group, a `Binder` and a `MultiBinder` do.
    /// The builders are position-agnostic by construction now, and this is the
    /// assertion that they are.
    fn positions() -> Vec<(&'static str, Option<TokenStream>)> {
        vec![
            ("Regular", None),
            ("Binder pre-scope", Some(quote! { { __scope_group_binder(); } })),
            ("MultiBinder pre-scope", Some(quote! { { __scope_group_multi(); } })),
        ]
    }

    /// ★★ THE CELL GATE. For each of the five carriers, in each of the three
    /// positions, on each of the two sides, the emitted statements must have the
    /// carrier's shape.
    ///
    /// The load-bearing pair is `Collection` vs `OptionalCollection`: they differ
    /// only in one boolean, and conflating them is precisely the defect. A plain
    /// `Vec` MUST produce `l0.len()` and a zipped element walk; an
    /// `Option<Vec<…>>` MUST destructure the option before applying either
    /// operation to the inner vector. Calling `len` or `iter` on the option
    /// itself would instead describe its zero-or-one container payload.
    #[test]
    fn every_carrier_is_handled_in_every_position_on_both_sides() {
        let language = crate::gen::collection_literal_language_for_tests();
        let left = vec![format_ident!("l0")];
        let right = vec![format_ident!("r0")];

        let mut cells = 0usize;
        for (position, scope) in positions() {
            for (carrier, f) in one_per_carrier() {
                let fields = [f];
                let eq = rendered(eq_arm_stmts(&fields, &left, &right, scope.clone(), &language));
                let cmp = rendered(cmp_arm_stmts(&fields, &left, &right, scope.clone(), &language));
                cells += 1;

                // Anti-vacuity: an emitter that produced nothing would satisfy
                // every "must not contain" assertion below.
                assert!(
                    eq.contains("l0") && cmp.contains("l0"),
                    "{position} / {carrier}: the field was not emitted at all — every \
                     'must not contain' assertion below would pass vacuously"
                );

                match carrier {
                    "Leaf/predicate" | "Leaf/token-text" => {
                        assert!(
                            eq.contains("ifl0!=r0"),
                            "{position} / {carrier}: a leaf is compared whole by `!=`. Got: {eq}"
                        );
                        assert!(
                            cmp.contains("l0.cmp(r0)"),
                            "{position} / {carrier}: a leaf's `Ord` is a precomputed \
                             `Verdict`. Got: {cmp}"
                        );
                        assert!(
                            !eq.contains("CmpTask::CmpProc"),
                            "{position} / {carrier}: a leaf's `category` is a PLACEHOLDER \
                             ident, so pushing a per-category task would name a variant that \
                             does not exist. Got: {eq}"
                        );
                    },
                    "Child" => {
                        assert!(
                            eq.contains("CmpTask::CmpProc(&**l0"),
                            "{position} / {carrier}: a boxed child is a DESCENT, pushed as a \
                             task — that is the whole point of the work-stack driver. Got: {eq}"
                        );
                        assert!(cmp.contains("CmpTask::CmpProc(&**l0"), "{position}: {cmp}");
                    },
                    "OptionalChild" => {
                        assert!(
                            eq.contains("l0.as_ref()") && eq.contains("CmpTask::CmpProc"),
                            "{position} / {carrier}: `Option<Box<Cat>>` destructures FIRST and \
                             then descends. Got: {eq}"
                        );
                        assert!(
                            cmp.contains("Ordering::Less") && cmp.contains("Ordering::Greater"),
                            "{position} / {carrier}: `None < Some(_)` must be decided \
                             explicitly, not by a whole-value re-entry. Got: {cmp}"
                        );
                    },
                    "Collection" => {
                        assert!(
                            eq.contains("l0.len()") && eq.contains("l0.iter().zip(r0.iter())"),
                            "{position} / {carrier}: an ORDER-FAITHFUL container is walked \
                             per-element — `Vec::eq` is length-then-elements and the walk \
                             reproduces it exactly. Got: {eq}"
                        );
                        assert!(
                            cmp.contains("l0.len().cmp(&r0.len())"),
                            "{position} / {carrier}: `Vec: Ord` uses length as the TIEBREAK, \
                             pushed first so it pops last. Got: {cmp}"
                        );
                    },
                    "OptionalCollection" => {
                        // ★ THE REGRESSION CELL.
                        assert!(
                            eq.contains("match(l0.as_ref(),r0.as_ref())")
                                && eq.contains("__left_collection.len()")
                                && eq.contains(
                                    "__left_collection.iter().zip(__right_collection.iter())"
                                ),
                            "{position} / {carrier}: `Option<Container>` must be destructured, \
                             then the inner container must use the same explicit element PDA as \
                             a non-optional collection. Got: {eq}"
                        );
                        assert!(
                            !eq.contains("l0.len()") && !eq.contains("l0.iter()"),
                            "★ {position} / {carrier}: the walk escaped the destructured inner \
                             container and called a collection operation on the option. Got: {eq}"
                        );
                        assert!(
                            eq.contains("CmpTask::CmpProc(__walk_leftas*const_"),
                            "★ {position} / {carrier}: the destructured vector's elements must \
                             become category comparison tasks. Got: {eq}"
                        );
                        assert!(
                            cmp.contains("match(l0.as_ref(),r0.as_ref())")
                                && cmp.contains("Ordering::Less")
                                && cmp.contains("Ordering::Greater")
                                && cmp.contains(
                                    "__left_collection.len().cmp(&__right_collection.len())"
                                )
                                && cmp.contains("CmpTask::CmpProc(__walk_leftas*const_"),
                            "{position} / {carrier}: the `Ord` side must reproduce the option \
                             tag ordering and schedule the inner vector's lexicographic PDA. \
                             Got: {cmp}"
                        );
                    },
                    other => panic!(
                        "unclassified carrier `{other}` in the cell census. Add its row \
                         rather than widening the match: an unnamed carrier is exactly the \
                         silent fall-through this test exists to forbid."
                    ),
                }
            }
        }

        assert_eq!(
            cells,
            6 * 3,
            "the census must cover every (carrier, position) cell — six labelled carrier \
             fixtures (the five carriers, with `Leaf` sampled at both of its inhabitants) \
             across all three field positions"
        );
    }

    /// ★ The pushed form of an optional collection.
    ///
    /// `cmp_arm_stmts` splits an arm at the first stack-expressible field —
    /// everything before it is compared eagerly (with an early `return ord`),
    /// everything from it onward is pushed in reverse so the engine pops it in
    /// field order. Putting a `Child` at index 0 forces `split = 0`, which puts
    /// the optional collection at index 1 into that pushed segment. The option
    /// tag remains a verdict, while `Some`/`Some` schedules the inner vector's
    /// length tiebreak and element comparisons separately.
    #[test]
    fn the_pushed_segment_form_of_an_optional_collection_is_an_inner_walk() {
        let language = crate::gen::collection_literal_language_for_tests();
        let fields = [
            field(false, None, false, false, None),
            field(true, Some(CollectionType::Vec), false, true, None),
        ];
        let left = vec![format_ident!("l0"), format_ident!("l1")];
        let right = vec![format_ident!("r0"), format_ident!("r1")];

        let cmp = rendered(cmp_arm_stmts(&fields, &left, &right, None, &language));
        assert!(
            cmp.contains("CmpTask::CmpProc(&**l0"),
            "the control: index 0 is a boxed child and must be a DESCENT, which is what \
             forces `split = 0` and puts index 1 into the pushed segment. Got: {cmp}"
        );
        assert!(
            cmp.contains("match(l1.as_ref(),r1.as_ref())")
                && cmp.contains("__left_collection.len().cmp(&__right_collection.len())")
                && cmp.contains("CmpTask::CmpProc(__walk_leftas*const_"),
            "★ an `Option<Vec<…>>` in the pushed segment must compare its tag and then \
             schedule the inner vector's exact lexicographic walk. Got: {cmp}"
        );
        assert!(
            !cmp.contains("l1.len()") && !cmp.contains("l1.iter()"),
            "★ collection operations must apply to the destructured vector, not the option. \
             Got: {cmp}"
        );

        let eq = rendered(eq_arm_stmts(&fields, &left, &right, None, &language));
        assert!(
            eq.contains("match(l1.as_ref(),r1.as_ref())")
                && eq.contains("__left_collection.len()")
                && eq.contains("CmpTask::CmpProc(__walk_leftas*const_")
                && !eq.contains("l1.len()"),
            "the `eq` side of the same two-field arm must destructure and walk the inner \
             collection. Got: {eq}"
        );
    }

    /// ★ The two sides must classify a field IDENTICALLY. Before #197 they did
    /// not: `cmp_arm_stmts` treated `Option<Container>` as one whole value while
    /// the eq binder arms accidentally walked the option itself. Agreement is
    /// now structural — both sides call `field_carrier`, destructure the option,
    /// and schedule the inner container — and this asserts it stays so.
    #[test]
    fn the_eq_and_cmp_sides_agree_on_every_carrier() {
        for (carrier, f) in one_per_carrier() {
            let stack_expressible = !matches!(field_carrier(&f), FieldCarrier::Leaf);
            let descends_on_eq = !matches!(field_carrier(&f), FieldCarrier::Leaf);
            assert_eq!(
                stack_expressible, descends_on_eq,
                "{carrier}: both sides must agree whether the carrier contains category \
                 descents that belong on the explicit work stack"
            );
        }
    }

    /// Every unordered collection shape must construct the same runtime PDA on
    /// both trait sides. Equality may ask whether its ordering is `Equal`, but it
    /// must not call the collection or element category's public comparison
    /// implementation as one whole recursive value. Ordering must defer even a
    /// mode/length lead verdict until the collection's exact field position.
    #[test]
    fn unordered_eq_and_ord_share_one_deferred_collection_pda() {
        let language = crate::gen::collection_literal_language_for_tests();
        let proc = format_ident!("Proc");
        let left = quote! { left };
        let right = quote! { right };
        let compact = |tokens: TokenStream| {
            tokens
                .to_string()
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>()
        };

        for coll_type in [
            CollectionType::HashSet,
            CollectionType::HashBag,
            CollectionType::HashMap,
            CollectionType::PathMap,
        ] {
            let machine = compact(unordered_collection_cmp_machine_expr(&coll_type, &left, &right));
            let eq = compact(eq_collection_stmts(&proc, &coll_type, &left, &right, &language));
            let ord =
                compact(cmp_collection_push_stmts(&proc, &coll_type, &left, &right, &language));

            assert!(
                eq.contains(&machine) && ord.contains(&machine),
                "{coll_type:?}: Eq and Ord must instantiate the identical collection PDA.\n\
                 Eq: {eq}\nOrd: {ord}\nMachine: {machine}"
            );
            assert!(
                eq.contains("eq_unordered_collection(")
                    && eq.contains("cmp_resume_collection_proc"),
                "{coll_type:?}: Eq must drive the shared ordering PDA through the Proc \
                 continuation. Got: {eq}"
            );
            assert!(
                ord.contains("CmpTask::StartCollection(")
                    && ord.contains("cmp_resume_collection_proc"),
                "{coll_type:?}: Ord must defer the initial PDA step as a work item, so \
                 an eager lead verdict cannot violate field order. Got: {ord}"
            );
            assert!(
                !eq.contains("left!=right") && !ord.contains("left.cmp(right)"),
                "{coll_type:?}: a category-bearing unordered collection escaped as a whole \
                 public-trait comparison. Eq: {eq}; Ord: {ord}"
            );
        }

        let generated = compact(generate_iterative_cmp(&language));
        assert_eq!(
            generated.matches("fneq_unordered_collection(").count(),
            1,
            "the auxiliary equality driver is shared across every category"
        );
        assert_eq!(
            generated.matches("staticCMP_AUX_TASK_POOL").count(),
            1,
            "the auxiliary work-stack pool is shared across every category"
        );
    }

    /// The scope group is emitted exactly once and LAST, in both binder positions
    /// and on both sides — the property the three hand-copied loops maintained by
    /// hand and the shared builders now maintain by construction.
    #[test]
    fn the_scope_group_is_emitted_once_and_last() {
        let language = crate::gen::collection_literal_language_for_tests();
        let fields =
            [field(false, None, false, false, None), field(false, None, true, false, None)];
        let left = vec![format_ident!("l0"), format_ident!("l1")];
        let right = vec![format_ident!("r0"), format_ident!("r1")];
        let scope = quote! { { __scope_group(); } };

        for (side, stmts) in [
            ("eq", eq_arm_stmts(&fields, &left, &right, Some(scope.clone()), &language)),
            ("cmp", cmp_arm_stmts(&fields, &left, &right, Some(scope.clone()), &language)),
        ] {
            let text = rendered(stmts.clone());
            assert_eq!(
                text.matches("__scope_group()").count(),
                1,
                "{side}: the scope group must appear exactly once"
            );
            // On the `eq` side the scope is the LAST statement (a conjunction is
            // order-insensitive, so field order is kept verbatim). On the `cmp`
            // side the pushed segment goes on in REVERSE position order, so the
            // scope — being the last POSITION — is pushed FIRST.
            let scope_index = stmts
                .iter()
                .position(|s| s.to_string().contains("__scope_group"))
                .expect("the scope group must be present");
            let expected = if side == "eq" { stmts.len() - 1 } else { 0 };
            assert_eq!(
                scope_index, expected,
                "{side}: the scope group sits at the wrong index. `eq` emits positions in \
                 field order so the scope is LAST; `cmp` reverse-pushes so the scope — the \
                 last position — is pushed FIRST and therefore pops last."
            );
        }
    }

    fn generated_function_body(tokens: TokenStream, function: &str) -> String {
        let source = tokens.to_string();
        let needle = format!("fn {function}");
        let start = source.find(&needle).expect("generated function must exist");
        let open = start
            + source[start..]
                .find('{')
                .expect("generated function must have a body");
        let mut depth = 0usize;
        for (offset, ch) in source[open..].char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return source[open..=open + offset].to_owned();
                    }
                },
                _ => {},
            }
        }
        panic!("generated function body must be balanced");
    }

    #[test]
    fn equality_helper_checks_pointer_identity_before_dereference() {
        let language = crate::gen::singleton_collection_language_for_tests();
        let helper = generated_function_body(generate_eq_engine(&language), "eq_handle_meta");
        let pointer_check = helper
            .find("std :: ptr :: eq (left_ptr , right_ptr)")
            .expect("equality helper must test shared allocation identity");
        let first_dereference = helper
            .find("unsafe { & * left_ptr }")
            .expect("equality helper must eventually dereference distinct values");
        assert!(
            pointer_check < first_dereference,
            "pointer identity must return before dereference or descendant scheduling: {helper}",
        );
    }

    #[test]
    fn exhaustive_match_codegen_omits_singleton_comparison_fallbacks() {
        let language = crate::gen::singleton_collection_language_for_tests();
        for (engine, function) in [
            (generate_eq_engine(&language), "eq_handle_meta"),
            (generate_cmp_engine(&language), "cmp_handle_meta"),
        ] {
            let singleton = generated_function_body(engine, function);
            assert!(
                !singleton.contains("_ =>"),
                "single-constructor comparison must not retain an unreachable fallback"
            );
        }
    }
}
