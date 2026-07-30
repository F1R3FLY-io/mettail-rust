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

use crate::gen::term_ops::collection_walk::{
    for_each_subterm, plan_for, CollectionPlan, OrderSensitivity, WalkOrder,
};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
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
            #(#variants,)*
            /// ★ #162 — a `usize` written to `state` at its position in the stream.
            ///
            /// `Hash for [T]` is `state.write_length_prefix(len)` followed by each
            /// element in index order, and `write_length_prefix`'s default (the only
            /// one reachable from stable code, since the method is unstable) is
            /// `write_usize`. So a `Vec` whose elements are pushed as tasks needs its
            /// LENGTH PREFIX to arrive first — as a task, or the driver would have to
            /// hash the whole container eagerly, which is the escape this closes.
            AbsorbUsize(usize),
            /// ★ #162 — a `u8` written to `state` at its position in the stream.
            ///
            /// The `Option` discriminant byte of an Opt-Group field: `0` for `None`,
            /// `1` for `Some`, then the inner value. Pushing the byte as a task is
            /// what lets the inner value be a DESCENT instead of an eager
            /// `Hash::hash(&**__b, state)` re-entry.
            AbsorbU8(u8),
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
                    // ★ #162 — precomputed stream content, written at its own
                    // position. `Hash::hash(&n, state)` on a `usize`/`u8` is exactly
                    // `state.write_usize(n)` / `state.write_u8(n)`, so the byte
                    // stream is identical to the eager form these replaced.
                    HashTask::AbsorbUsize(n) => {
                        std::hash::Hash::hash(&n, state);
                    }
                    HashTask::AbsorbU8(b) => {
                        std::hash::Hash::hash(&b, state);
                    }
                }
            }
        }
    }
}

/// ★ #162 — the ONE place `iterative_hash` decides what to do with a collection
/// of sub-terms, for all four syntactic positions it can occupy.
///
/// The emitted stream must be BYTE-IDENTICAL to the whole-value `Hash::hash` it
/// replaces, because a generated `Hash` value is consensus-visible (`Proc` is a
/// hash key inside the AST, and `semantic_fingerprint` feeds the realize-dedup).
/// For `Vec` that is exact and provable: `Hash for [T]` writes the length prefix
/// and then each element in index order, so the conversion is
/// `AbsorbUsize(len)` + one `Hash{Elem}` per element, pushed so they pop in that
/// order. For every other container shape the stream is NOT reproducible
/// element-wise (see [`collection_walk::is_order_faithful`]), and the whole-value
/// call stays — the declared residue.
fn hash_collection_stmts(
    element_cat: &Ident,
    coll_type: &CollectionType,
    coll_expr: &TokenStream,
    language: &LanguageDef,
) -> TokenStream {
    match plan_for(element_cat, coll_type, OrderSensitivity::OrderSensitive, language) {
        CollectionPlan::PerElement { element_cat, coll_type } => {
            let task_variant = format_ident!("Hash{}", element_cat);
            let pushes =
                for_each_subterm(&coll_type, coll_expr, WalkOrder::ReverseForLifo, &|e| {
                    quote! {
                        stack.push(HashTask::#task_variant(#e as *const _));
                    }
                });
            quote! {
                // ⚠ The length prefix is written BEFORE the elements, so on a LIFO
                // stack it must be pushed AFTER them. This is the OPPOSITE of the
                // `Ord` side, where `Vec`'s length is the lexicographic TIEBREAK and
                // therefore pops last — see `iterative_cmp::cmp_collection_push_stmts`.
                // The two orders are genuinely different and getting them
                // interchanged silently changes every hash and every ordering.
                #pushes
                stack.push(HashTask::AbsorbUsize(#coll_expr.len()));
            }
        },
        CollectionPlan::WholeValue { .. } => quote! {
            std::hash::Hash::hash(#coll_expr, state);
        },
    }
}

/// Generate match arms for a specific variant in the hash engine.
fn generate_hash_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Nullary { label } => {
            // Nullary: discriminant only (already hashed above)
            quote! {
                #category::#label => {}
            }
        },

        // An OPAQUE native leaf: whole-value `Hash` is correct and flat.
        VariantKind::Literal { label } => {
            quote! {
                #category::#label(v) => {
                    std::hash::Hash::hash(v, state);
                }
            }
        },

        // ★ #162 — the collection-literal boundary. `Hash::hash(v, state)` on a
        // `&Vec<Proc>` calls `Proc::hash` per element, re-entering this driver by
        // host recursion. See `collection_walk`'s header.
        VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
            let body = hash_collection_stmts(element_cat, coll_type, &quote! { v }, language);
            quote! {
                #category::#label(v) => {
                    #body
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

        // ★ #162 — the category-DIRECT collection field, same boundary.
        VariantKind::Collection { label, element_cat, coll_type } => {
            let body = hash_collection_stmts(element_cat, coll_type, &quote! { coll }, language);
            quote! {
                #category::#label(coll) => {
                    #body
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
///
/// ## ★ #162 — the EAGER PREFIX is gone, and what replaced it
///
/// A `Hash` arm must write its fields' contributions to `state` in FIELD ORDER,
/// because the digest is that stream. Before this change the only work the task
/// enum could carry was a DESCENT, so any field whose contribution had to be
/// written between two descents forced the arm to run eagerly. The emitter
/// resolved that with an EAGER PREFIX running "up to and including the last
/// collection field" (its 60-line deliberation is preserved in git history) —
/// which meant a `Box<Cat>` child sitting before a collection was hashed by
/// `Hash::hash(&**f, state)`, a whole-value re-entry, i.e. HOST RECURSION.
///
/// With `HashTask::AbsorbUsize` / `AbsorbU8` the stack can carry the two kinds of
/// non-descent content the arms actually need (a `Vec` length prefix and an
/// `Option` tag byte), so the split moves to the FIRST DESCENT:
///
/// ```text
///   split = index of the first field expressible as a task
///   [0, split)   hashed eagerly, in field order — leaves only, no sub-terms
///   [split, n)   pushed in REVERSE, so they pop in field order
/// ```
///
/// ## ⚠ The one shape this cannot express, and the measurement that bounds it
///
/// A LEAF whose contribution must be written AFTER a descent cannot be a task:
/// its stream is arbitrary (a `String`, a `BehavioralPred`, a `Binder<String>`),
/// and byte-splicing a recorded stream is NOT equivalent — a `Hasher` may frame
/// each `write` call, so `write(&recorded_bytes)` and the original sequence of
/// `write_*` calls can produce different digests. (`FramedSemanticKeyHasher` in
/// this workspace does exactly that framing.)
///
/// Such a variant therefore keeps the legacy eager-prefix emission, marked in the
/// generated source with `HASH_ORDER_RESIDUE` so the set is greppable rather than
/// implicit. **Measured 2026-07-30 across the generated rholang tree: ZERO
/// variants take it.** Every rholang `Binder` has an empty pre-scope field list,
/// so its `Binder<String>` pattern is always position 0; and every predicate /
/// token-text leaf precedes its variant's descents. The fallback exists for a
/// FUTURE grammar, and if one arrives the residue announces itself.
fn generate_hash_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let stmts = hash_arm_stmts(fields, &field_names, None, language);
    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#stmts)*
        }
    }
}

/// Is this field's hash contribution expressible as work ON THE STACK?
///
/// A boxed category child is (`Hash{Cat}`); an `Option<Box<Cat>>` is (`AbsorbU8`
/// for the tag, then `Hash{Cat}`); an order-faithful collection is
/// (`AbsorbUsize` for the length, then one `Hash{Elem}` per element). A bare
/// leaf, an `Option<Container>` and an unordered container are NOT — see
/// [`generate_hash_regular_arm`].
fn hash_field_is_stack_expressible(field: &FieldInfo, language: &LanguageDef) -> bool {
    if field.is_predicate || field.is_opaque_leaf() {
        return false;
    }
    if !field.is_collection {
        return true;
    }
    if field.is_optional {
        return false;
    }
    let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
    matches!(
        plan_for(&field.category, &coll_type, OrderSensitivity::OrderSensitive, language),
        CollectionPlan::PerElement { .. }
    )
}

/// The eager, in-field-order hash of one field — the pre-#162 emission, retained
/// verbatim for the fields that legitimately belong in the eager prefix and for
/// the `HASH_ORDER_RESIDUE` fallback.
fn hash_field_eagerly(field: &FieldInfo, name: &Ident) -> TokenStream {
    if field.is_optional {
        if field.is_collection {
            // Phase 4 #3 (2026-05-12): Optional-Collection — discriminator byte
            // then the container's whole-value `Hash`.
            return quote! {
                match #name.as_ref() {
                    None => std::hash::Hash::hash(&0u8, state),
                    Some(__c) => {
                        std::hash::Hash::hash(&1u8, state);
                        std::hash::Hash::hash(__c, state);
                    }
                }
            };
        }
        if field.is_predicate || field.is_opaque_leaf() {
            // Task #14 (`Option<Guard>`) / L9-3 (`Option<String>`): the payload is
            // a bare value, so `__b` is hashed directly (the `&**__b` deref of the
            // sibling arm is `E0614` here).
            return quote! {
                match #name.as_ref() {
                    None => std::hash::Hash::hash(&0u8, state),
                    Some(__b) => {
                        std::hash::Hash::hash(&1u8, state);
                        std::hash::Hash::hash(__b, state);
                    }
                }
            };
        }
        return quote! {
            match #name.as_ref() {
                None => std::hash::Hash::hash(&0u8, state),
                Some(__b) => {
                    std::hash::Hash::hash(&1u8, state);
                    std::hash::Hash::hash(&**__b, state);
                }
            }
        };
    }
    if field.is_predicate || field.is_opaque_leaf() || field.is_collection {
        // Phase 3A-B4 / L9-3: predicate and token-text leaves hash inline.
        return quote! {
            std::hash::Hash::hash(#name, state);
        };
    }
    quote! {
        std::hash::Hash::hash(&**#name, state);
    }
}

/// ★ #162 — the ONE construction of a hash arm body, shared by `Regular`,
/// `Binder` and `MultiBinder`. See [`generate_hash_regular_arm`] for the scheme
/// and for the `HASH_ORDER_RESIDUE` fallback.
fn hash_arm_stmts(
    fields: &[FieldInfo],
    field_names: &[Ident],
    scope_pushes: Option<TokenStream>,
    language: &LanguageDef,
) -> Vec<TokenStream> {
    let expressible: Vec<bool> =
        fields.iter().map(|f| hash_field_is_stack_expressible(f, language)).collect();
    let split = expressible.iter().position(|e| *e).unwrap_or(fields.len());
    // A leaf whose bytes must land AFTER a descent — the shape no task can carry.
    let leaf_after_descent = expressible.iter().skip(split).any(|e| !*e);

    if leaf_after_descent {
        let mut legacy: Vec<TokenStream> = Vec::with_capacity(fields.len() + 1);
        // ⚠ A REAL TOKEN, not a comment. A `//` comment inside `quote!` is not a
        // token and does not reach the generated file at all — the first version of
        // this marker was therefore invisible, and the "zero residues" reading it
        // produced was VACUOUS. A binding is greppable in `target/generated/**`.
        legacy.push(quote! {
            let _HASH_ORDER_RESIDUE_leaf_after_descent = ();
        });
        for (i, field) in fields.iter().enumerate() {
            legacy.push(hash_field_eagerly(field, &field_names[i]));
        }
        if let Some(scope_pushes) = scope_pushes {
            legacy.push(scope_pushes);
        }
        return legacy;
    }

    let mut stmts: Vec<TokenStream> = Vec::with_capacity(fields.len() + 1);

    // ── the eager segment: leaves, in field order ──
    for (i, field) in fields.iter().enumerate().take(split) {
        stmts.push(hash_field_eagerly(field, &field_names[i]));
    }

    // ── the pushed segment, in REVERSE field order (the scope is last ⇒ first) ──
    if let Some(scope_pushes) = scope_pushes {
        stmts.push(scope_pushes);
    }

    for (i, field) in fields.iter().enumerate().skip(split).rev() {
        let name = &field_names[i];

        if field.is_optional {
            // Opt-Group `Option<Box<Cat>>`: tag byte, then the inner value. Pop
            // order must be tag-then-value, so the value is pushed first.
            //
            // ★ This replaces an eager `Hash::hash(&**__b, state)` re-entry.
            let task_variant = format_ident!("Hash{}", field.category);
            stmts.push(quote! {
                match #name.as_ref() {
                    None => stack.push(HashTask::AbsorbU8(0u8)),
                    Some(__b) => {
                        stack.push(HashTask::#task_variant(&**__b as *const _));
                        stack.push(HashTask::AbsorbU8(1u8));
                    }
                }
            });
            continue;
        }

        if field.is_collection {
            let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
            stmts.push(hash_collection_stmts(
                &field.category,
                &coll_type,
                &quote! { #name },
                language,
            ));
            continue;
        }

        let task_variant = format_ident!("Hash{}", field.category);
        stmts.push(quote! {
            stack.push(HashTask::#task_variant(&**#name as *const _));
        });
    }

    stmts
}

/// Generate hash arm for a Binder variant.
///
/// ## ★ #162 — why this arm is UNCHANGED, and that is a derivation not an omission
///
/// A binder arm's positions are `pre_scope_fields… , pattern , body`. The PATTERN
/// (a `Binder<String>`, or a `Vec<Binder<String>>` for the multi form) is a LEAF
/// with an arbitrary hash stream, and it sits immediately before the body
/// descent. So:
///
/// * If the pre-scope list contains NO descent — every rholang binder, whose
///   pre-scope list is EMPTY — the fields and the pattern are all leaves and
///   belong in the eager segment anyway, and the body is the single pushed task.
///   That is exactly the pre-#162 emission, so there is nothing to change.
/// * If the pre-scope list DOES contain a descent (a `Box<Cat>` child or an
///   order-faithful collection), the pattern leaf would have to be written AFTER
///   it — the one shape `HashTask` cannot carry byte-exactly (see
///   [`generate_hash_regular_arm`]). The arm therefore stays eager and announces
///   itself with `HASH_ORDER_RESIDUE`.
///
/// ⚠ Which means a binder with a `Box<Cat>` pre-scope field is still Θ(depth) in
/// `Hash`. No shipped grammar has one — the marker is what makes that checkable
/// instead of assumed.
fn generate_hash_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    generate_hash_scoped_arm(category, label, pre_scope_fields, body_cat, language)
}

/// Generate hash arm for a MultiBinder variant. Identical in shape to
/// [`generate_hash_binder_arm`] — the pattern is a `Vec<Binder<String>>` rather
/// than a single `Binder<String>`, and `Hash::hash` on it is the same leaf
/// operation.
fn generate_hash_multi_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    generate_hash_scoped_arm(category, label, pre_scope_fields, body_cat, language)
}

/// The shared body of the two scoped-arm generators. See
/// [`generate_hash_binder_arm`].
fn generate_hash_scoped_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let mut hash_stmts: Vec<TokenStream> = Vec::with_capacity(total_fields + 1);

    // The pattern leaf follows every pre-scope position, so a pre-scope DESCENT
    // would make the pattern a leaf-after-descent. Announce it.
    if pre_scope_fields
        .iter()
        .any(|f| hash_field_is_stack_expressible(f, language))
    {
        // A REAL TOKEN — see the sibling marker in `hash_arm_stmts`.
        hash_stmts.push(quote! {
            let _HASH_ORDER_RESIDUE_binder_pattern_after_descent = ();
        });
    }

    // Pre-scope fields, eagerly and in field order. Every one of them precedes the
    // pattern leaf, so none may be deferred.
    for (i, field) in pre_scope_fields.iter().enumerate() {
        hash_stmts.push(hash_field_eagerly(field, &field_names[i]));
    }

    let body_task = format_ident!("Hash{}", body_cat);
    hash_stmts.push(quote! {
        {
            // The pattern is a leaf — `Binder<String>` / `Vec<Binder<String>>` — so
            // it goes straight into `state`, in position, before the body descent.
            std::hash::Hash::hash(&#scope_name.inner().unsafe_pattern, state);
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
            opaque_leaf: None,
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
