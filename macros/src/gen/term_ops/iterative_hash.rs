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
//! ## Collection boundaries
//!
//! Category-bearing collections never call a whole-container `Hash` that would
//! re-enter this driver. Ordered vectors schedule their elements directly;
//! sets, maps, and homogeneous path maps schedule a canonical ordering of
//! borrowed entries; bags absorb their maintained order-independent summary in
//! constant time. Collections of non-category leaves remain one bounded opaque
//! task because they contain no generated recursive term.
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
    for_each_subterm, plan_for, CollectionPlan, OrderSensitivity, WalkOrder, WholeValueReason,
};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

#[path = "iterative_hash_map_inspection.rs"]
mod map_inspection;

/// Distinct interpretations of the shared source traversal.
#[derive(Clone, Copy, PartialEq, Eq)]
enum HashInterpretation {
    Ordinary,
    CheckedExecution,
    InspectContributions,
}

/// Names and admission expressions shared by the task, driver, field and trait
/// emitters. Ordinary Hash retains its exact native stream and TLS hot path.
struct HashEmissionNames {
    interpretation: HashInterpretation,
    task_enum: Ident,
    task_pool: Ident,
    opaque_constructor: Ident,
    driver: Ident,
    handler_prefix: &'static str,
}

impl HashEmissionNames {
    fn ordinary() -> Self {
        Self {
            interpretation: HashInterpretation::Ordinary,
            task_enum: format_ident!("HashTask"),
            task_pool: format_ident!("HASH_TASK_POOL"),
            opaque_constructor: format_ident!("hash_opaque_task"),
            driver: format_ident!("hash_iterative"),
            handler_prefix: "hash_handle_",
        }
    }

    #[allow(dead_code)]
    fn checked() -> Self {
        Self {
            interpretation: HashInterpretation::CheckedExecution,
            task_enum: format_ident!("CheckedHashTask"),
            task_pool: format_ident!("CHECKED_HASH_TASK_POOL"),
            opaque_constructor: format_ident!("checked_hash_opaque_task"),
            driver: format_ident!("checked_hash_iterative"),
            handler_prefix: "checked_hash_handle_",
        }
    }

    #[allow(dead_code)]
    fn inspect_contributions() -> Self {
        Self {
            interpretation: HashInterpretation::InspectContributions,
            task_enum: format_ident!("InspectHashContributionTask"),
            task_pool: format_ident!("INSPECT_HASH_CONTRIBUTION_TASK_POOL"),
            opaque_constructor: format_ident!("inspect_hash_contribution_opaque_task"),
            driver: format_ident!("inspect_hash_contribution_worklist"),
            handler_prefix: "inspect_hash_contribution_handle_",
        }
    }

    fn admitted(&self) -> bool {
        self.interpretation != HashInterpretation::Ordinary
    }

    fn inspecting(&self) -> bool {
        self.interpretation == HashInterpretation::InspectContributions
    }

    /// Add a proved component of future ordinary Hash work. The accumulator
    /// pays for its own metadata arithmetic; this does not reserve execution.
    fn inspect_contribution(&self, work: usize, records: usize) -> TokenStream {
        if self.inspecting() {
            quote! {
                state.try_accumulate_parts(#work, #records, 0, reserve)
                    .map_err(mettail_runtime::KeyHashFailure::Admission)?;
            }
        } else {
            TokenStream::new()
        }
    }

    fn task_type(&self) -> TokenStream {
        let task = &self.task_enum;
        if self.admitted() {
            quote! { #task<E> }
        } else {
            quote! { #task }
        }
    }

    fn generics(&self) -> TokenStream {
        if self.admitted() {
            quote! { <E> }
        } else {
            quote! { <H: std::hash::Hasher> }
        }
    }

    fn state_type(&self) -> TokenStream {
        match self.interpretation {
            HashInterpretation::Ordinary => quote! { H },
            HashInterpretation::CheckedExecution => quote! { mettail_runtime::CheckedFxHasher },
            HashInterpretation::InspectContributions => {
                quote! { mettail_runtime::binding_receipt::BindingCharge }
            },
        }
    }

    fn parameters(&self) -> TokenStream {
        if self.admitted() {
            quote! { reserve: &mut impl FnMut(usize, usize) -> Result<(), E>, }
        } else {
            TokenStream::new()
        }
    }

    fn arguments(&self) -> TokenStream {
        if self.admitted() {
            quote! { , reserve }
        } else {
            TokenStream::new()
        }
    }

    fn result_type(&self) -> TokenStream {
        if self.admitted() {
            quote! { -> Result<(), mettail_runtime::KeyHashFailure<E>> }
        } else {
            TokenStream::new()
        }
    }

    fn propagate(&self) -> TokenStream {
        if self.admitted() {
            quote! { ? }
        } else {
            TokenStream::new()
        }
    }

    fn success(&self) -> TokenStream {
        if self.admitted() {
            quote! { Ok(()) }
        } else {
            TokenStream::new()
        }
    }

    fn routing(&self) -> TokenStream {
        if self.admitted() {
            quote! {
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                    .map_err(mettail_runtime::KeyHashFailure::Admission)?;
            }
        } else {
            TokenStream::new()
        }
    }

    fn push_task(&self, task: TokenStream) -> TokenStream {
        self.push_task_with_error(task, quote! { mettail_runtime::KeyHashFailure::Admission })
    }

    fn push_task_with_error(&self, task: TokenStream, failure: TokenStream) -> TokenStream {
        if self.admitted() {
            quote! {{
                mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                    .map_err(#failure)?;
                stack.push(#task);
            }}
        } else {
            quote! { stack.push(#task) }
        }
    }

    fn opaque_task(&self, value: TokenStream) -> TokenStream {
        let constructor = &self.opaque_constructor;
        if self.admitted() {
            quote! { #constructor::<_, E>(#value) }
        } else {
            quote! { #constructor::<_, H>(#value) }
        }
    }

    fn handler(&self, category: &Ident) -> Ident {
        format_ident!("{}{}", self.handler_prefix, category.to_string().to_lowercase())
    }

    fn map_scheduler(&self, category: &Ident) -> Ident {
        format_ident!("checked_hash_schedule_map_{}", category.to_string().to_lowercase())
    }

    /// Preserve the native call expression at its existing stream position.
    fn hash_value(&self, value: TokenStream) -> TokenStream {
        self.leaf_action(value, quote! { reserve })
    }

    fn leaf_action(&self, value: TokenStream, reserve: TokenStream) -> TokenStream {
        match self.interpretation {
            HashInterpretation::Ordinary => quote! { std::hash::Hash::hash(#value, state) },
            HashInterpretation::CheckedExecution => quote! {{
                mettail_runtime::CheckedFxHashLeaf::try_hash_fx(#value, state, #reserve)?;
            }},
            HashInterpretation::InspectContributions => quote! {{
                let work = mettail_runtime::CheckedFxHashLeaf::try_inspect_hash_fx_work(
                    #value, #reserve,
                )?;
                state.try_accumulate_parts(work, 0, 0, #reserve)
                    .map_err(mettail_runtime::KeyHashFailure::Admission)?;
            }},
        }
    }
}

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate `HashTask` enum, TLS pool, the iterative hash engine,
/// and `impl Hash for Cat` for all exported categories.
pub fn generate_iterative_hash(language: &LanguageDef) -> TokenStream {
    let emission = HashEmissionNames::ordinary();
    let hash_task_enum = generate_hash_task_enum(language, &emission);
    let hash_engine = generate_hash_engine(language, &emission);
    let hash_impls = generate_hash_impls(language, &emission);

    quote! {
        #hash_task_enum
        #hash_engine
        #hash_impls
    }
}

/// Compose native-leaf, driver, and Map callback contributions privately.
///
/// This private integration entrypoint deliberately does not activate a public
/// category-admission interface. It reuses the exact field and scope builders,
/// pays its own metadata walk, and never executes Hash, Eq, Ord or sorting.
/// The result remains accounting data: an execution provider must reserve it
/// against the same retained source and pinned native profile before use.
#[allow(dead_code)]
pub(super) fn generate_hash_contribution_inspection(language: &LanguageDef) -> TokenStream {
    let emission = HashEmissionNames::inspect_contributions();
    let tasks = generate_hash_task_enum(language, &emission);
    let driver = generate_hash_engine(language, &emission);
    let interfaces = generate_hash_impls(language, &emission);
    let comparisons = super::iterative_cmp::generate_comparison_contribution_inspection(language);
    let maps = map_inspection::generate_map_hash_contribution_inspection(language);
    quote! { #comparisons #maps #tasks #driver #interfaces }
}

// =============================================================================
// HashTask Enum + TLS Pool
// =============================================================================

/// Generate the `HashTask` enum and thread-local pool.
///
/// `HashTask` has one variant per category: `HashInt(*const Int)`, etc.
fn generate_hash_task_enum(language: &LanguageDef, emission: &HashEmissionNames) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task_pool = &emission.task_pool;
    let opaque_constructor = &emission.opaque_constructor;
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

    if emission.admitted() {
        let state_type = emission.state_type();
        let apply_leaf = emission
            .leaf_action(quote! { value }, quote! { &mut |work, units| reserve(work, units) });
        return quote! {
            #[allow(dead_code)]
            enum #task_enum<E> {
                #(#variants,)*
                AbsorbUsize(usize),
                AbsorbU8(u8),
                Opaque {
                    value: *const (),
                    hash: unsafe fn(
                        *const (),
                        &mut #state_type,
                        &mut dyn FnMut(usize, usize) -> Result<(), E>,
                    ) -> Result<(), mettail_runtime::KeyHashFailure<E>>,
                },
            }

            #[inline]
            fn #opaque_constructor<T: mettail_runtime::CheckedFxHashLeaf, E>(
                value: &T,
            ) -> #task_enum<E> {
                unsafe fn apply<T: mettail_runtime::CheckedFxHashLeaf, E>(
                    value: *const (),
                    state: &mut #state_type,
                    reserve: &mut dyn FnMut(usize, usize) -> Result<(), E>,
                ) -> Result<(), mettail_runtime::KeyHashFailure<E>> {
                    // The root remains immutably borrowed until the worklist
                    // returns. Scheduling this pointer never hashes its value.
                    let value = unsafe { &*value.cast::<T>() };
                    #apply_leaf;
                    Ok(())
                }
                #task_enum::Opaque {
                    value: value as *const T as *const (),
                    hash: apply::<T, E>,
                }
            }
        };
    }

    quote! {
        /// Work item for the iterative hash engine.
        ///
        /// Each variant wraps a raw pointer to a value of one category.
        /// The iterative engine pops tasks, hashes discriminant and leaf
        /// payloads, and pushes child tasks for `Box<T>` fields.
        #[allow(dead_code)]
        enum #task_enum {
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
            HashPathMapMode(mettail_runtime::PathMapMode),
            Opaque {
                value: *const (),
                hash: unsafe fn(*const (), *mut ()),
            },
        }

        #[inline]
        fn #opaque_constructor<T, H>(value: &T) -> #task_enum
        where
            T: std::hash::Hash,
            H: std::hash::Hasher,
        {
            unsafe fn apply<T, H>(value: *const (), state: *mut ())
            where
                T: std::hash::Hash,
                H: std::hash::Hasher,
            {
                let value = unsafe { &*value.cast::<T>() };
                let state = unsafe { &mut *state.cast::<H>() };
                std::hash::Hash::hash(value, state);
            }

            #task_enum::Opaque {
                value: value as *const T as *const (),
                hash: apply::<T, H>,
            }
        }

        // SAFETY: HashTask holds *const pointers that are only dereferenced
        // within the same thread that created them, during the lifetime of
        // the references they were derived from.
        unsafe impl Send for #task_enum {}
        unsafe impl Sync for #task_enum {}

        thread_local! {
            /// Pool for reusing `HashTask` work stacks across `hash()` calls.
            ///
            /// The `Cell<Vec<HashTask>>` pattern allows zero-allocation
            /// steady-state operation: the first hash allocates, subsequent
            /// hashes reuse the same buffer. Re-entrant hashes (from
            /// collection fields delegating to their own Hash) get fresh
            /// empty vectors; the outermost call retains pool capacity.
            static #task_pool: std::cell::Cell<Vec<#task_enum>> =
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
fn generate_hash_engine(language: &LanguageDef, emission: &HashEmissionNames) -> TokenStream {
    let task_enum = &emission.task_enum;
    let driver = &emission.driver;
    let task_type = emission.task_type();
    let generics = emission.generics();
    let state_type = emission.state_type();
    let parameters = emission.parameters();
    let arguments = emission.arguments();
    let result_type = emission.result_type();
    let propagate = emission.propagate();
    let success = emission.success();
    let routing = emission.routing();
    let category_control = emission.inspect_contribution(5, 0);
    let helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let helper_fn = emission.handler(cat);
            let index_fn = format_ident!("variant_index_{}", cat.to_string().to_lowercase());
            let hash_discriminant = emission.hash_value(quote! { &#index_fn(val) });
            let variants = collect_category_variants(cat, language);
            let variant_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_hash_variant_arm(cat, v, language, emission))
                .collect();
            quote! {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn #helper_fn #generics(
                    stack: &mut Vec<#task_type>,
                    state: &mut #state_type,
                    ptr: *const #cat,
                    #parameters
                ) #result_type {
                    #routing
                    #category_control
                    let val = unsafe { &*ptr };
                    #hash_discriminant;
                    match val {
                        #(#variant_arms)*
                    }
                    #success
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
            let helper_fn = emission.handler(cat);
            quote! {
                #task_enum::#hash_variant(ptr) => {
                    #helper_fn(stack, state, ptr #arguments) #propagate;
                }
            }
        })
        .collect();

    let absorb_usize = emission.hash_value(quote! { &n });
    let absorb_u8 = emission.hash_value(quote! { &b });
    let absorb_pathmap_mode = emission.hash_value(quote! { &mode });

    if emission.admitted() {
        let map_helpers = if emission.inspecting() {
            Vec::new()
        } else {
            generate_checked_map_hash_helpers(language, emission)
        };
        // GeneratedHashDriverControl derives the root wrapper/control sum:
        // 15 + 4*N + 5*C + 5*O work, 2 + N records. A successful pop
        // represents one original occurrence. Pushes and terminal routing
        // are already included in this sum and must not be added again.
        let popped_control = emission.inspect_contribution(4, 1);
        let opaque_control = emission.inspect_contribution(5, 0);
        return quote! {
            #(#map_helpers)*
            #(#helper_fns)*

            #[allow(dead_code, unused_variables)]
            fn #driver<E>(
                stack: &mut Vec<#task_enum<E>>,
                state: &mut #state_type,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<(), mettail_runtime::KeyHashFailure<E>> {
                loop {
                    #routing
                    let Some(task) = stack.pop() else { break };
                    #popped_control
                    match task {
                        #(#task_arms)*
                        #task_enum::AbsorbUsize(n) => { #absorb_usize; },
                        #task_enum::AbsorbU8(b) => { #absorb_u8; },
                        #task_enum::Opaque { value, hash } => {
                            #opaque_control
                            unsafe { hash(value, state, reserve) }?;
                        },
                    }
                }
                Ok(())
            }
        };
    }

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
        fn #driver<H: std::hash::Hasher>(stack: &mut Vec<#task_enum>, state: &mut H) {
            while let Some(task) = stack.pop() {
                match task {
                    #(#task_arms)*
                    // ★ #162 — precomputed stream content, written at its own
                    // position. `Hash::hash(&n, state)` on a `usize`/`u8` is exactly
                    // `state.write_usize(n)` / `state.write_u8(n)`, so the byte
                    // stream is identical to the eager form these replaced.
                    #task_enum::AbsorbUsize(n) => {
                        #absorb_usize;
                    }
                    #task_enum::AbsorbU8(b) => {
                        #absorb_u8;
                    }
                    #task_enum::HashPathMapMode(mode) => {
                        #absorb_pathmap_mode;
                    }
                    #task_enum::Opaque { value, hash } => {
                        unsafe { hash(value, state as *mut H as *mut ()) };
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
/// order. Unordered wrappers use their exact public hashing contracts: sorted
/// element/entry order for sets and maps, a cached commutative summary for bags,
/// and a homogeneous mode tag plus sorted entries for path maps. No
/// category-bearing container remains a synchronous recursive escape.
fn hash_collection_stmts(
    element_cat: &Ident,
    coll_type: &CollectionType,
    coll_expr: &TokenStream,
    language: &LanguageDef,
    emission: &HashEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let opaque_constructor = &emission.opaque_constructor;
    match plan_for(element_cat, coll_type, OrderSensitivity::OrderSensitive, language) {
        CollectionPlan::PerElement { element_cat, coll_type } => {
            let task_variant = format_ident!("Hash{}", element_cat);
            if emission.admitted() {
                let routing = emission.routing();
                // GeneratedHashHandlerControl reuses the existing borrowed
                // iterator boundary. Add per-yield pointer work on the same
                // walk, without a second traversal or unchecked width math.
                let vector_control = emission.inspect_contribution(4, 1);
                let element_control = emission.inspect_contribution(2, 0);
                let push_child = emission.push_task(quote! {
                    #task_enum::#task_variant(__hash_item as *const _)
                });
                let push_length = emission.push_task(quote! {
                    #task_enum::AbsorbUsize(__hash_length)
                });
                return quote! {{
                    #routing
                    #vector_control
                    let __hash_length = (#coll_expr).len();
                    let mut __hash_items = (#coll_expr).iter().rev();
                    loop {
                        #routing
                        let Some(__hash_item) = __hash_items.next() else { break };
                        #element_control
                        #push_child;
                    }
                    #push_length;
                }};
            }
            let pushes =
                for_each_subterm(&coll_type, coll_expr, WalkOrder::ReverseForLifo, &|e, _| {
                    quote! {
                        stack.push(#task_enum::#task_variant(#e as *const _));
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
                stack.push(#task_enum::AbsorbUsize(#coll_expr.len()));
            }
        },
        CollectionPlan::WholeValue {
            reason: WholeValueReason::UnorderedContainer,
        } => unordered_collection_hash_stmts(element_cat, coll_type, coll_expr, emission),
        CollectionPlan::WholeValue {
            reason: WholeValueReason::ElementIsNotACategory,
        } => {
            quote! {
                stack.push(#opaque_constructor::<_, H>(#coll_expr));
            }
        },
    }
}

/// Select the original supported Map element categories for both checked
/// execution and metadata inspection, without a second support census.
fn required_map_hash_categories(language: &LanguageDef) -> std::collections::BTreeSet<String> {
    let mut required = std::collections::BTreeSet::new();
    for ty in &language.types {
        for variant in collect_category_variants(&ty.name, language) {
            if !checked_hash_variant_supported(&ty.name, &variant, language) {
                continue;
            }
            match variant {
                VariantKind::Collection {
                    element_cat,
                    coll_type: CollectionType::HashMap,
                    ..
                }
                | VariantKind::CollectionLiteral {
                    element_cat,
                    coll_type: CollectionType::HashMap,
                    ..
                } => {
                    required.insert(element_cat.to_string());
                },
                VariantKind::Regular { fields, .. }
                | VariantKind::Binder { pre_scope_fields: fields, .. }
                | VariantKind::MultiBinder { pre_scope_fields: fields, .. } => {
                    for field in fields {
                        if field.is_collection
                            && field.coll_type.as_ref() == Some(&CollectionType::HashMap)
                        {
                            required.insert(field.category.to_string());
                        }
                    }
                },
                _ => {},
            }
        }
    }
    required
}

/// Schedule original Map borrows using the existing admitted stable sorter.
/// Sorting never receives a hasher; reverse pops schedule value then key, and
/// the length is pushed last so the native length/key/value stream drains first.
fn generate_checked_map_hash_helpers(
    language: &LanguageDef,
    emission: &HashEmissionNames,
) -> Vec<TokenStream> {
    let required = required_map_hash_categories(language);
    language.types.iter().filter(|ty| required.contains(&ty.name.to_string())).map(|ty| {
        let category = &ty.name;
        let helper = emission.map_scheduler(category);
        let task_enum = &emission.task_enum;
        let task_variant = format_ident!("Hash{}", category);
        let routing = emission.routing();
        let push_value = emission.push_task(quote! { #task_enum::#task_variant(value.cast::<#category>()) });
        let push_key = emission.push_task(quote! { #task_enum::#task_variant(key.cast::<#category>()) });
        let push_length = emission.push_task(quote! { #task_enum::AbsorbUsize(length) });
        quote! {
            #[inline(never)]
            #[allow(dead_code)]
            fn #helper<E>(
                source: &mettail_runtime::HashMapLit<#category, #category>,
                stack: &mut Vec<#task_enum<E>>,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<(), mettail_runtime::KeyHashFailure<E>> {
                #routing
                let roster = source.try_comparison_roster(reserve)?;
                let mut machine = mettail_runtime::CheckedCollectionSortPda::try_new(roster, reserve)?;
                let mut response = None;
                let mut sorted = loop {
                    #routing
                    match machine.try_resume(response.take(), reserve)? {
                        mettail_runtime::CheckedCollectionSortStep::CompareEntries { machine: next, left, right } => {
                            let (left_key, left_value) = left.try_pair_ptrs(reserve)?;
                            let (right_key, right_value) = right.try_pair_ptrs(reserve)?;
                            // The sole roster producer borrowed this immutable
                            // Map. Restore exactly its original category; the
                            // root remains borrowed throughout Hash task draining.
                            let ordering = unsafe {
                                <#category as mettail_runtime::CheckedIterativeComparison>::try_cmp_iterative(
                                    &*left_key.cast::<#category>(), &*right_key.cast::<#category>(), reserve,
                                )
                            }?;
                            #routing
                            response = Some(match ordering {
                                std::cmp::Ordering::Equal => unsafe {
                                    <#category as mettail_runtime::CheckedIterativeComparison>::try_cmp_iterative(
                                        &*left_value.cast::<#category>(), &*right_value.cast::<#category>(), reserve,
                                    )
                                }?,
                                other => other,
                            });
                            machine = next;
                        },
                        mettail_runtime::CheckedCollectionSortStep::Done(sorted) => break sorted,
                    }
                };
                loop {
                    #routing
                    let Some(item) = sorted.try_pop(reserve)? else { break };
                    let (key, value) = item.try_pair_ptrs(reserve)?;
                    #push_value;
                    #push_key;
                }
                #routing
                let length = source.len();
                #push_length;
                Ok(())
            }
        }
    }).collect()
}

fn unordered_collection_hash_stmts(
    element_cat: &Ident,
    coll_type: &CollectionType,
    coll_expr: &TokenStream,
    emission: &HashEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let opaque_constructor = &emission.opaque_constructor;
    let task_variant = format_ident!("Hash{}", element_cat);
    if emission.admitted() && *coll_type == CollectionType::HashBag {
        let push = emission.push_task(emission.opaque_task(quote! { #coll_expr }));
        return quote! { #push; };
    }
    if emission.admitted() && *coll_type == CollectionType::HashMap {
        if emission.inspecting() {
            let routing = emission.routing();
            let inspect = format_ident!(
                "inspect_map_hash_contributions_{}",
                element_cat.to_string().to_lowercase()
            );
            let error = quote! { mettail_runtime::NativeComparisonFailure::Admission };
            let push_value = emission.push_task_with_error(
                quote! { #task_enum::#task_variant(value as *const _) },
                error.clone(),
            );
            let push_key = emission
                .push_task_with_error(quote! { #task_enum::#task_variant(key as *const _) }, error);
            let push_length = emission.push_task(quote! { #task_enum::AbsorbUsize(length) });
            return quote! {{
                #routing
                #inspect(#coll_expr, state, reserve)?;
                let length = (#coll_expr).len();
                (#coll_expr).try_for_each_entry(reserve, |key, value, reserve| {
                    #push_value;
                    #push_key;
                    Ok(())
                })?;
                // This sum is permutation-invariant, unlike the Hash stream.
                // The original pair stays together; no sort/comparison runs.
                #push_length;
            }};
        }
        let helper = emission.map_scheduler(element_cat);
        return quote! { #helper(#coll_expr, stack, reserve)?; };
    }
    match coll_type {
        CollectionType::HashSet => quote! {
            {
                let mut __items: Vec<_> = #coll_expr.iter().collect();
                __items.sort_by(|__left, __right| (*__left).cmp(*__right));
                for __item in __items.into_iter().rev() {
                    stack.push(#task_enum::#task_variant(__item as *const _));
                }
                stack.push(#task_enum::AbsorbUsize(#coll_expr.len()));
            }
        },
        CollectionType::HashBag => quote! {
            stack.push(#opaque_constructor::<_, H>(#coll_expr));
        },
        CollectionType::HashMap => quote! {
            {
                let mut __items: Vec<_> = #coll_expr.iter().collect();
                __items.sort_by(|(__left_key, __left_value), (__right_key, __right_value)| {
                    __left_key
                        .cmp(__right_key)
                        .then_with(|| __left_value.cmp(__right_value))
                });
                for (__key, __value) in __items.into_iter().rev() {
                    stack.push(#task_enum::#task_variant(__value as *const _));
                    stack.push(#task_enum::#task_variant(__key as *const _));
                }
                stack.push(#task_enum::AbsorbUsize(#coll_expr.len()));
            }
        },
        CollectionType::PathMap => {
            pathmap_hash_stmts(element_cat, element_cat, coll_expr, emission)
        },
        CollectionType::Vec => quote! {
            compile_error!("unordered collection hashing requested for Vec");
        },
    }
}

/// Schedule the exact public `Hash` stream of `PathMapLit<K, V>` without
/// recursively hashing either generated category.  Mode is absorbed first;
/// each valued mode then emits the `HashMapLit` length prefix and canonical
/// key/value sequence.  Distinct key/value task variants preserve
/// heterogeneous recursive native carriers.
fn pathmap_hash_stmts(
    key_category: &Ident,
    value_category: &Ident,
    pathmap: &TokenStream,
    emission: &HashEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let key_task = format_ident!("Hash{}", key_category);
    let value_task = format_ident!("Hash{}", value_category);
    quote! {
        {
            match #pathmap {
                mettail_runtime::PathMapLit::Empty => {},
                mettail_runtime::PathMapLit::Set(__entries) => {
                    let mut __items: Vec<_> = __entries.iter().collect();
                    __items.sort_by(|__left, __right| __left.0.cmp(__right.0));
                    for (__key, _) in __items.into_iter().rev() {
                        stack.push(#task_enum::#key_task(__key as *const _));
                    }
                    stack.push(#task_enum::AbsorbUsize(__entries.len()));
                },
                mettail_runtime::PathMapLit::Map(__entries) => {
                    let mut __items: Vec<_> = __entries.iter().collect();
                    __items.sort_by(
                        |(__left_key, __left_value), (__right_key, __right_value)| {
                            __left_key
                                .cmp(__right_key)
                                .then_with(|| __left_value.cmp(__right_value))
                        },
                    );
                    for (__key, __value) in __items.into_iter().rev() {
                        stack.push(#task_enum::#value_task(__value as *const _));
                        stack.push(#task_enum::#key_task(__key as *const _));
                    }
                    stack.push(#task_enum::AbsorbUsize(__entries.len()));
                },
            }
            stack.push(#task_enum::HashPathMapMode((#pathmap).mode()));
        }
    }
}

/// Generate match arms for a specific variant in the hash engine.
fn checked_hash_collection_supported(
    category: &Ident,
    kind: &CollectionType,
    language: &LanguageDef,
) -> bool {
    matches!(kind, CollectionType::Vec | CollectionType::HashBag | CollectionType::HashMap)
        && language.types.iter().any(|ty| ty.name == *category)
}

fn checked_hash_fields_supported(fields: &[FieldInfo], language: &LanguageDef) -> bool {
    fields.iter().all(|field| {
        !field.is_predicate
            && (!field.is_collection
                || checked_hash_collection_supported(
                    &field.category,
                    field.coll_type.as_ref().unwrap_or(&CollectionType::HashBag),
                    language,
                ))
    })
}

// This is an explicit native-operation profile, not a change to the canonical
// grammar classifier. Refused constructors remain ordinary Hash implementations.
fn checked_hash_variant_supported(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> bool {
    match variant {
        VariantKind::Refused { .. } | VariantKind::Nullary { .. } | VariantKind::Var { .. } => true,
        VariantKind::Literal { .. } => language
            .types
            .iter()
            .find(|ty| ty.name == *category)
            .and_then(|ty| ty.native_type.as_ref())
            .is_some_and(|ty| {
                matches!(
                    mettail_ast::language::NativeKind::from_syn_type(ty),
                    mettail_ast::language::NativeKind::Int64
                        | mettail_ast::language::NativeKind::Bool
                        | mettail_ast::language::NativeKind::Str
                        | mettail_ast::language::NativeKind::UInt8
                        | mettail_ast::language::NativeKind::Usize
                )
            }),
        VariantKind::Regular { fields, .. } => checked_hash_fields_supported(fields, language),
        VariantKind::Binder { pre_scope_fields, .. }
        | VariantKind::MultiBinder { pre_scope_fields, .. } => {
            checked_hash_fields_supported(pre_scope_fields, language)
        },
        VariantKind::Collection { element_cat, coll_type, .. }
        | VariantKind::CollectionLiteral { element_cat, coll_type, .. } => {
            checked_hash_collection_supported(element_cat, coll_type, language)
        },
        VariantKind::RecursiveNativeLiteral { .. } => false,
    }
}

fn generate_hash_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
    emission: &HashEmissionNames,
) -> TokenStream {
    if emission.admitted() && !checked_hash_variant_supported(category, variant, language) {
        let label = variant.label();
        let category_name = category.to_string();
        let constructor = label.to_string();
        return quote! {
            #category::#label(..) => {
                return Err(mettail_runtime::KeyHashFailure::UnsupportedConstructor {
                    category: #category_name, constructor: #constructor,
                });
            }
        };
    }
    let opaque_constructor = &emission.opaque_constructor;
    let payload_handoff = emission.inspect_contribution(1, 0);
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
            let hash_value = emission.hash_value(quote! { v });
            quote! {
                #category::#label(v) => {
                    #payload_handoff
                    #hash_value;
                }
            }
        },

        // ★ #162 — the collection-literal boundary. `Hash::hash(v, state)` on a
        // `&Vec<Proc>` calls `Proc::hash` per element, re-entering this driver by
        // host recursion. See `collection_walk`'s header.
        VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
            let body =
                hash_collection_stmts(element_cat, coll_type, &quote! { v }, language, emission);
            quote! {
                #category::#label(v) => {
                    #payload_handoff
                    #body
                }
            }
        },

        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            let pathmap = carrier.pathmap_ref(&quote! { v });
            let focus = carrier.focus_ref(&quote! { v });
            let body = pathmap_hash_stmts(
                carrier.key_category(),
                carrier.value_category(),
                &pathmap,
                emission,
            );
            quote! {
                #category::#label(v) => {
                    // The carrier hash is the lexicographic product
                    // `PathMap` then focus.  Focus is pushed first so the LIFO
                    // machine absorbs it after every structural PathMap task.
                    stack.push(#opaque_constructor::<_, H>(#focus));
                    #body
                }
            }
        },

        VariantKind::Var { label } => {
            // Var: hash OrdVar
            let hash_value = emission.hash_value(quote! { v });
            quote! {
                #category::#label(v) => {
                    #payload_handoff
                    #hash_value;
                }
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_hash_regular_arm(category, label, fields, language, emission)
        },

        // ★ #162 — the category-DIRECT collection field, same boundary.
        VariantKind::Collection { label, element_cat, coll_type } => {
            let body =
                hash_collection_stmts(element_cat, coll_type, &quote! { coll }, language, emission);
            quote! {
                #category::#label(coll) => {
                    #payload_handoff
                    #body
                }
            }
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => generate_hash_binder_arm(
            category,
            label,
            pre_scope_fields,
            body_cat,
            language,
            emission,
        ),

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_hash_multi_binder_arm(
                category,
                label,
                pre_scope_fields,
                body_cat,
                language,
                emission,
            )
        },
    }
}

/// Generate hash arm for a Regular variant.
///
/// ## ★ #162 — exact call order without recursive re-entry
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
/// `HashTask::AbsorbUsize`, `AbsorbU8`, and `Opaque` can carry every contribution
/// that may follow a descent while preserving the original sequence of
/// `Hasher::write_*` calls. The split therefore moves to the first deferred
/// category contribution:
///
/// ```text
///   split = index of the first category-bearing field
///   [0, split)   hashed eagerly, in field order — bounded leaves only
///   [split, n)   pushed in REVERSE, so they pop in field order
/// ```
///
/// `Opaque` stores a type-erased function pointer specialized to the caller's
/// hasher type, so it replays the leaf's exact calls against the original hasher;
/// it never hashes to an intermediate byte buffer. Consequently there is no
/// field-order residue for future grammar shapes either.
fn generate_hash_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    language: &LanguageDef,
    emission: &HashEmissionNames,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let stmts = hash_arm_stmts(fields, &field_names, None, language, emission);
    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#stmts)*
        }
    }
}

/// Does this field begin the suffix that must be represented on the work stack?
///
/// A boxed category child is (`Hash{Cat}`); an `Option<Box<Cat>>` is (`AbsorbU8`
/// for the tag, then `Hash{Cat}`); every category-bearing collection has a
/// specialized deferred representation. Bounded leaves before the first such
/// field stay eager to avoid needless task traffic; leaves after it use
/// `HashTask::Opaque`.
fn hash_field_begins_deferred_suffix(field: &FieldInfo, language: &LanguageDef) -> bool {
    if field.is_predicate || field.is_opaque_leaf() {
        return false;
    }
    if !field.is_collection {
        return true;
    }
    let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
    matches!(
        plan_for(&field.category, &coll_type, OrderSensitivity::OrderSensitive, language),
        CollectionPlan::PerElement { .. }
            | CollectionPlan::WholeValue {
                reason: WholeValueReason::UnorderedContainer,
            }
    )
}

/// Hash one bounded field in the eager prefix, in original field order.
fn hash_field_eagerly(
    field: &FieldInfo,
    name: &Ident,
    emission: &HashEmissionNames,
) -> TokenStream {
    let field_control = emission.inspect_contribution(1 + usize::from(field.is_optional), 0);
    let child_control = emission.inspect_contribution(1, 0);
    if field.is_optional {
        let hash_none = emission.hash_value(quote! { &0u8 });
        let hash_some = emission.hash_value(quote! { &1u8 });
        if field.is_collection {
            // Phase 4 #3 (2026-05-12): Optional-Collection — discriminator byte
            // then the container's whole-value `Hash`.
            let hash_value = emission.hash_value(quote! { __c });
            return quote! {
                #field_control
                match #name.as_ref() {
                    None => #hash_none,
                    Some(__c) => {
                        #hash_some;
                        #hash_value;
                    }
                }
            };
        }
        if field.is_predicate || field.is_opaque_leaf() {
            // Task #14 (`Option<Guard>`) / L9-3 (`Option<String>`): the payload is
            // a bare value, so `__b` is hashed directly (the `&**__b` deref of the
            // sibling arm is `E0614` here).
            let hash_value = emission.hash_value(quote! { __b });
            return quote! {
                #field_control
                match #name.as_ref() {
                    None => #hash_none,
                    Some(__b) => {
                        #hash_some;
                        #hash_value;
                    }
                }
            };
        }
        let hash_value = emission.hash_value(quote! { &**__b });
        return quote! {
            #field_control
            match #name.as_ref() {
                None => #hash_none,
                Some(__b) => {
                    #child_control
                    #hash_some;
                    #hash_value;
                }
            }
        };
    }
    if field.is_predicate || field.is_opaque_leaf() || field.is_collection {
        // Phase 3A-B4 / L9-3: predicate and token-text leaves hash inline.
        let hash_value = emission.hash_value(quote! { #name });
        return quote! {
            #field_control
            #hash_value;
        };
    }
    let hash_value = emission.hash_value(quote! { &**#name });
    quote! {
        #field_control
        #child_control
        #hash_value;
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
    emission: &HashEmissionNames,
) -> Vec<TokenStream> {
    let task_enum = &emission.task_enum;
    let push_none = emission.push_task(quote! { #task_enum::AbsorbU8(0u8) });
    let push_some = emission.push_task(quote! { #task_enum::AbsorbU8(1u8) });
    let deferred: Vec<bool> = fields
        .iter()
        .map(|f| hash_field_begins_deferred_suffix(f, language))
        .collect();
    let split = deferred.iter().position(|e| *e).unwrap_or(fields.len());
    let mut stmts: Vec<TokenStream> = Vec::with_capacity(fields.len() + 1);

    // ── the eager segment: leaves, in field order ──
    for (i, field) in fields.iter().enumerate().take(split) {
        stmts.push(hash_field_eagerly(field, &field_names[i], emission));
    }

    // ── the pushed segment, in REVERSE field order (the scope is last ⇒ first) ──
    if let Some(scope_pushes) = scope_pushes {
        stmts.push(scope_pushes);
    }

    for (i, field) in fields.iter().enumerate().skip(split).rev() {
        let name = &field_names[i];
        let field_control = emission.inspect_contribution(1 + usize::from(field.is_optional), 0);
        let child_control = emission.inspect_contribution(1, 0);
        let body = match crate::gen::term_ops::collection_walk::field_carrier(field) {
            crate::gen::term_ops::collection_walk::FieldCarrier::Leaf if field.is_optional => {
                let push = emission.push_task(emission.opaque_task(quote! { __leaf }));
                quote! {
                    match #name.as_ref() {
                        None => #push_none,
                        Some(__leaf) => {
                            #push;
                            #push_some;
                        },
                    }
                }
            },
            crate::gen::term_ops::collection_walk::FieldCarrier::Leaf => {
                let push = emission.push_task(emission.opaque_task(quote! { #name }));
                quote! { #push; }
            },
            crate::gen::term_ops::collection_walk::FieldCarrier::OptionalChild => {
                let task_variant = format_ident!("Hash{}", field.category);
                let push = emission.push_task(quote! {
                    #task_enum::#task_variant(&**__child as *const _)
                });
                quote! {
                    match #name.as_ref() {
                        None => #push_none,
                        Some(__child) => {
                            #child_control
                            #push;
                            #push_some;
                        },
                    }
                }
            },
            crate::gen::term_ops::collection_walk::FieldCarrier::OptionalCollection {
                coll_type,
            } => {
                let collection = hash_collection_stmts(
                    &field.category,
                    &coll_type,
                    &quote! { __collection },
                    language,
                    emission,
                );
                quote! {
                    match #name.as_ref() {
                        None => #push_none,
                        Some(__collection) => {
                            #collection
                            #push_some;
                        },
                    }
                }
            },
            crate::gen::term_ops::collection_walk::FieldCarrier::Collection { coll_type } => {
                hash_collection_stmts(
                    &field.category,
                    &coll_type,
                    &quote! { #name },
                    language,
                    emission,
                )
            },
            crate::gen::term_ops::collection_walk::FieldCarrier::Child => {
                let task_variant = format_ident!("Hash{}", field.category);
                let push = emission.push_task(quote! {
                    #task_enum::#task_variant(&**#name as *const _)
                });
                quote! {
                    #child_control
                    #push;
                }
            },
        };
        stmts.push(quote! { #field_control #body });
    }

    stmts
}

/// Generate hash arm for a Binder variant.
///
/// A binder arm's positions are `pre_scope_fields… , pattern , body`. The PATTERN
/// (a `Binder<String>`, or a `Vec<Binder<String>>` for the multi form) is a LEAF
/// with an arbitrary hash stream, and it sits immediately before the body
/// descent. It is therefore an `Opaque` task followed by the body category task.
/// Pre-scope fields share the regular-arm suffix builder, including collection
/// PDAs, so binders with recursive pre-scope fields remain stack-safe for any
/// grammar shape.
fn generate_hash_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
    emission: &HashEmissionNames,
) -> TokenStream {
    generate_hash_scoped_arm(category, label, pre_scope_fields, body_cat, language, emission)
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
    emission: &HashEmissionNames,
) -> TokenStream {
    generate_hash_scoped_arm(category, label, pre_scope_fields, body_cat, language, emission)
}

/// The shared body of the two scoped-arm generators. See
/// [`generate_hash_binder_arm`].
fn generate_hash_scoped_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
    emission: &HashEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let body_task = format_ident!("Hash{}", body_cat);
    let push_body = emission.push_task(quote! { #task_enum::#body_task(body_ptr) });
    let push_pattern = emission.push_task(emission.opaque_task(quote! {
        &#scope_name.inner().unsafe_pattern
    }));
    let scope_control = emission.inspect_contribution(3, 0);
    let scope_pushes = quote! {
        {
            #scope_control
            let body_ptr: *const #body_cat = &*#scope_name.inner().unsafe_body;
            #push_body;
            #push_pattern;
        }
    };
    let hash_stmts =
        hash_arm_stmts(pre_scope_fields, &field_names, Some(scope_pushes), language, emission);

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
fn generate_hash_impls(language: &LanguageDef, emission: &HashEmissionNames) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_hash_impl(&lang_type.name, emission))
        .collect();

    quote! { #(#impls)* }
}

/// Generate `impl Hash` for a single category.
fn generate_hash_impl(category: &Ident, emission: &HashEmissionNames) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task_pool = &emission.task_pool;
    let driver = &emission.driver;
    let hash_variant = format_ident!("Hash{}", category);

    if emission.inspecting() {
        let inspect =
            format_ident!("inspect_hash_contribution_{}", category.to_string().to_lowercase());
        let push_root =
            emission.push_task(quote! { #task_enum::#hash_variant(source as *const _) });
        return quote! {
            // Partial contribution: never use as whole-category Hash authority.
            #[allow(dead_code)]
            fn #inspect<E>(
                source: &#category,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<mettail_runtime::binding_receipt::BindingCharge, mettail_runtime::KeyHashFailure<E>> {
                if !mettail_runtime::CHECKED_FX_PROFILE_AVAILABLE {
                    return Err(mettail_runtime::KeyHashFailure::UnsupportedProfile);
                }
                // Accumulator initialization and normal disposal, separately
                // from borrowed task-vector initialization and disposal.
                mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                    .map_err(mettail_runtime::KeyHashFailure::Admission)?;
                let mut native_charge = mettail_runtime::binding_receipt::BindingCharge::ZERO;
                native_charge.try_accumulate_parts(15, 2, 0, reserve)
                    .map_err(mettail_runtime::KeyHashFailure::Admission)?;
                mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                    .map_err(mettail_runtime::KeyHashFailure::Admission)?;
                let mut tasks = Vec::new();
                let stack = &mut tasks;
                #push_root;
                #driver(stack, &mut native_charge, reserve)?;
                Ok(native_charge)
            }
        };
    }

    if emission.admitted() {
        let push_root = emission.push_task(quote! { #task_enum::#hash_variant(self as *const _) });
        return quote! {
            impl mettail_runtime::CheckedIterativeHash for #category {
                fn try_hash_iterative<E>(
                    &self,
                    state: &mut mettail_runtime::CheckedFxHasher,
                    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
                ) -> Result<(), mettail_runtime::KeyHashFailure<E>> {
                    if !mettail_runtime::CHECKED_FX_PROFILE_AVAILABLE {
                        return Err(mettail_runtime::KeyHashFailure::UnsupportedProfile);
                    }
                    // Local vector header and normal release; pending borrowed
                    // task disposal is prepaid at each push, not a recursive drop.
                    mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                        .map_err(mettail_runtime::KeyHashFailure::Admission)?;
                    let mut tasks = Vec::new();
                    let stack = &mut tasks;
                    #push_root;
                    #driver(stack, state, reserve)
                }
            }
        };
    }

    quote! {
        impl std::hash::Hash for #category {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                // Fast path: try TLS pool
                let tls_result = #task_pool.try_with(|cell| {
                    let mut stack = cell.take();
                    let was_empty = stack.is_empty();

                    // Push initial hash task
                    stack.push(#task_enum::#hash_variant(self as *const _));

                    // Run the iterative engine
                    #driver(&mut stack, state);

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
                let mut stack = vec![#task_enum::#hash_variant(self as *const _)];
                #driver(&mut stack, state);
            }
        }
    }
}

#[cfg(test)]
#[path = "iterative_hash_checked_tests.rs"]
pub(super) mod checked_tests;

#[cfg(test)]
mod tests {
    use super::*;

    fn ordinary_surface_language() -> LanguageDef {
        syn::parse_str(
            r#"
            name: OrdinaryHashSurfaces,
            types {
                Proc ![i64] as Int ![bool] as Bool ![str] as Text
                ![Vec<u8>] as Bytes ![Vec<Proc>] as List
                ![mettail_runtime::HashBag<Proc>] as Bag
                ![mettail_runtime::HashSetLit<Proc>] as Set
                ![mettail_runtime::HashMapLit<Proc, Proc>] as Map
                ![mettail_runtime::PathMapLit<Proc, Proc>] as Pathmap
            },
            terms {
                PZero . |- "0" : Proc;
                PMixed . child:Proc, ?guard:Guard
                    |- before@Word child *flt(node, Open, Close) guard after@Word : Proc;
                POptional . *opt(child:Proc, ?guard:Guard)
                    |- prefix@Word *opt(before@Word child *flt(node, Open, Close) guard) : Proc;
                POptionalVec . *opt(children:Vec(Proc)) |- *opt(children) : Proc;
                PVector . children:Vec(Proc) |- "vector" children : Proc;
                PBag . children:HashBag(Proc) |- "bag" children : Proc;
                PSingle . pre:Proc, ^x.body:[Proc -> Proc] |- "single" pre x body : Proc;
                PMulti . children:Vec(Proc), ^[xs].body:[Proc* -> Proc]
                    |- "multi" children xs body : Proc;
            },
            equations {}, rewrites {},
            "#,
        )
        .expect("ordinary hash fixture uses the production language parser")
    }

    fn surface_variant(language: &LanguageDef, category: &str, label: &str) -> VariantKind {
        collect_category_variants(&format_ident!("{}", category), language)
            .into_iter()
            .find(|variant| variant.label() == label)
            .unwrap_or_else(|| panic!("missing actual {category}::{label} classification"))
    }

    fn compact(tokens: TokenStream) -> String {
        tokens.to_string().split_whitespace().collect()
    }

    fn positions_are_ordered(source: &str, needles: &[&str]) {
        let mut remaining = source;
        for needle in needles {
            let offset = remaining
                .find(needle)
                .unwrap_or_else(|| panic!("missing ordered fragment {needle} in {source}"));
            remaining = &remaining[offset + needle.len()..];
        }
    }

    #[test]
    fn ordinary_hash_surface_census_and_exact_expansion_capture() {
        let language = ordinary_surface_language();
        for category in ["Int", "Bool", "Text", "Bytes"] {
            let variants = collect_category_variants(&format_ident!("{}", category), &language);
            assert!(variants
                .iter()
                .any(|v| matches!(v, VariantKind::Literal { .. })));
            assert!(!variants
                .iter()
                .any(|v| matches!(v, VariantKind::CollectionLiteral { .. })));
        }
        for (category, expected) in [
            ("List", CollectionType::Vec),
            ("Bag", CollectionType::HashBag),
            ("Set", CollectionType::HashSet),
            ("Map", CollectionType::HashMap),
            ("Pathmap", CollectionType::PathMap),
        ] {
            let variants = collect_category_variants(&format_ident!("{}", category), &language);
            assert!(variants.iter().any(|v| matches!(v,
                VariantKind::CollectionLiteral { element_cat, coll_type, .. }
                    if element_cat == "Proc" && *coll_type == expected)));
        }
        let variants = collect_category_variants(&format_ident!("Proc"), &language);
        assert!(variants
            .iter()
            .any(|v| matches!(v, VariantKind::Var { .. })));
        assert!(matches!(
            surface_variant(&language, "Proc", "PVector"),
            VariantKind::Collection { coll_type: CollectionType::Vec, .. }
        ));
        assert!(matches!(
            surface_variant(&language, "Proc", "PBag"),
            VariantKind::Collection { coll_type: CollectionType::HashBag, .. }
        ));
        assert!(matches!(
            surface_variant(&language, "Proc", "PSingle"),
            VariantKind::Binder { .. }
        ));
        assert!(matches!(
            surface_variant(&language, "Proc", "PMulti"),
            VariantKind::MultiBinder { .. }
        ));

        for (name, language) in [
            ("ordinary-surfaces", language),
            ("singleton", crate::gen::singleton_collection_language_for_tests()),
        ] {
            let expansion = generate_iterative_hash(&language);
            syn::parse2::<syn::File>(expansion.clone()).expect("ordinary hash Rust item syntax");
            // Opt-in baseline artifacts; the default unit test has no filesystem writes.
            // Compare the complete token strings before/after emitter parameterization.
            if let Ok(phase) = std::env::var("METTAIL_HASH_EXPANSION_PHASE") {
                assert!(matches!(phase.as_str(), "before" | "after"));
                let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../target/verification/hash-emitter")
                    .join(phase);
                std::fs::create_dir_all(&directory).expect("create hash capture directory");
                std::fs::write(directory.join(format!("{name}.tokens")), expansion.to_string())
                    .expect("capture exact ordinary hash emitter output");
            }
        }
    }

    #[test]
    fn ordinary_mixed_fields_keep_eager_prefix_and_reversed_deferred_suffix() {
        let language = ordinary_surface_language();
        let emission = HashEmissionNames::ordinary();
        let variant = surface_variant(&language, "Proc", "PMixed");
        let VariantKind::Regular { fields, .. } = &variant else {
            panic!("regular mixed fields")
        };
        assert_eq!(fields.len(), 5);
        assert!(fields[0].is_opaque_leaf() && fields[2].is_opaque_leaf());
        assert!(fields[3].is_predicate && fields[4].is_opaque_leaf());
        let arm = compact(generate_hash_variant_arm(
            &format_ident!("Proc"),
            &variant,
            &language,
            &emission,
        ));
        positions_are_ordered(
            &arm,
            &[
                "Hash::hash(f0,state)",
                "hash_opaque_task::<_,H>(f4)",
                "hash_opaque_task::<_,H>(f3)",
                "hash_opaque_task::<_,H>(f2)",
                "HashTask::HashProc(&**f1as*const_)",
            ],
        );
        assert!(!arm.contains("Hash::hash(&**f1,state)"));

        let variant = surface_variant(&language, "Proc", "POptional");
        let VariantKind::Regular { fields, .. } = &variant else {
            panic!("regular optional fields")
        };
        assert!(fields.iter().any(|f| f.is_optional && f.is_opaque_leaf()));
        assert!(fields.iter().any(|f| f.is_optional && f.is_predicate));
        assert!(fields
            .iter()
            .any(|f| f.is_optional && !f.is_collection && !f.is_predicate && !f.is_opaque_leaf()));
        let arm = compact(generate_hash_variant_arm(
            &format_ident!("Proc"),
            &variant,
            &language,
            &emission,
        ));
        assert!(arm.contains("Hash::hash(__b,state)")); // Optional native eager prefix.
        assert!(arm.contains("hash_opaque_task::<_,H>(__leaf)")); // Optional native suffix.
        positions_are_ordered(
            &arm,
            &["HashTask::HashProc(&**__childas*const_)", "HashTask::AbsorbU8(1u8)"],
        );
    }

    #[test]
    fn ordinary_optional_vectors_and_scopes_keep_lifo_stream_order() {
        let language = ordinary_surface_language();
        let emission = HashEmissionNames::ordinary();
        let variant = surface_variant(&language, "Proc", "POptionalVec");
        let VariantKind::Regular { fields, .. } = &variant else {
            panic!("optional vector field")
        };
        assert!(fields.iter().any(|f| f.is_optional && f.is_collection));
        let arm = compact(generate_hash_variant_arm(
            &format_ident!("Proc"),
            &variant,
            &language,
            &emission,
        ));
        positions_are_ordered(
            &arm,
            &[
                "HashTask::HashProc(",
                "HashTask::AbsorbUsize(__collection.len())",
                "HashTask::AbsorbU8(1u8)",
            ],
        );
        for label in ["PSingle", "PMulti"] {
            let variant = surface_variant(&language, "Proc", label);
            let arm = compact(generate_hash_variant_arm(
                &format_ident!("Proc"),
                &variant,
                &language,
                &emission,
            ));
            positions_are_ordered(
                &arm,
                &[
                    "HashTask::HashProc(body_ptr)",
                    "hash_opaque_task::<_,H>(&f1.inner().unsafe_pattern)",
                    "HashTask::HashProc(",
                ],
            );
        }
    }

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
        let arm = generate_hash_regular_arm(
            &cat,
            &label,
            &fields,
            &language,
            &HashEmissionNames::ordinary(),
        )
        .to_string();
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
