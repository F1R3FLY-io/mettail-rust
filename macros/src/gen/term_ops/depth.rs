//! Stack-safe term-depth measurement generation for MeTTaIL terms
//!
//! Generates a per-category `term_depth()` that computes the maximum nesting
//! depth of a term. The Dovetail e-graph build consumes the measurement when it
//! derives a saturation-work allowance (`dovetail_report.rs`, 40 generated call
//! sites). It never truncates the AST walk, silently accepts partial saturation,
//! or acts as an accepted-term depth limit: a non-converged saturation is an
//! explicit error.
//!
//! ## Depth semantics — UNCHANGED by the #162 conversion
//!
//! - Variables, literals, nullary constructors: 0
//! - Constructor application: `1 + max(field depths)`
//! - Collection CATEGORY (`Collection` / `CollectionLiteral`): `1 + max(element depths)`
//! - Collection FIELD inside a constructor: `max(element depths)` — the container
//!   itself adds NO level; only the enclosing node's `1 +` counts
//! - Binders: `1 + max(pre-scope field depths, body depth)`
//! - Predicate and opaque-capture leaf fields: 0 (constant-size payloads, not host
//!   term nesting)
//!
//! ## ★★ #162 — `term_depth` was the TENTH driver, and a different KIND of defect
//!
//! The other nine generated traversals are work-stack drivers that escaped their
//! worklist at the collection-element boundary. `term_depth` had **no work stack at
//! all**: it emitted bare host recursion — `1 + f0.term_depth()`,
//! `1 + coll.iter().map(|x| x.term_depth()).max().unwrap_or(0)` — so it was
//! Θ(depth) for every shape, not just for collections. The discriminating
//! measurement is its `*_add` twin: `ast_term_depth_add` sloped at **2,367 B/level**
//! on the pure `Proc::Add(Arc<Proc>, Arc<Proc>)` chain, where every one of the other
//! nine reads 0. Nine escaped a worklist they HAD; this one never had one.
//!
//! ⚠ **It is live, and an earlier record said otherwise.** The claim on file was
//! "no caller anywhere in the workspace … a latent trap rather than a live
//! exposure". `target/generated/rholang/dovetail_report.rs` calls it at 40 sites —
//! `__max_depth = __max_depth.max(value.term_depth())`, one per `RholangTermInner`
//! arm in the Dovetail e-graph build — emitted by
//! `macros/src/gen/runtime/dovetail_report/typed_report.rs:1845/1933/2659/2677`. A
//! grep of the SOURCE tree finds only the emitter's `quote!` fragments; the call
//! sites exist only after expansion. So deleting it was never an option and this is
//! a CONVERSION.
//!
//! ## The conversion needs NO result stack, and that is a derivation
//!
//! The obvious iterative form of `1 + max(children)` is a post-order walk with a
//! value stack and per-node "combine" tasks — the shape `subst` uses. `term_depth`
//! does not need it, because the recurrence collapses.
//!
//! Write `base(n) = 0` for a leaf kind (`Var`, `Literal`, `Nullary`) and
//! `base(n) = 1` for every other kind, and let `dist(n, m)` be the number of
//! child-position edges from `n` to `m`. Then
//!
//! ```math
//! f(n) \;=\; \max_{m \,\in\, \mathrm{desc}(n)} \big(\mathrm{dist}(n, m) + \mathrm{base}(m)\big)
//! ```
//!
//! **Proof.** By induction on the term. The recurrence is
//! `f(n) = 1 + max(0, max_x f(x))` over `n`'s pushed child positions `x` — the `0`
//! covers leaf fields, which contribute nothing, and it also covers a node with no
//! pushed children at all (an empty collection, or a constructor all of whose
//! fields are predicate/opaque leaves), for which `f(n) = 1`.
//!
//! *Base case.* No pushed children: `f(n) = 1`, and the right-hand side is
//! `dist(n, n) + base(n) = 0 + 1 = 1`. For a leaf kind `f(n) = 0` and the
//! right-hand side is `0 + 0 = 0`. Both agree.
//!
//! *Inductive step.* Each pushed child `x` sits at `dist(n, x) = 1`, so by the
//! induction hypothesis
//! `1 + f(x) = 1 + max_{m ∈ desc(x)} (dist(x, m) + base(m))
//!           = max_{m ∈ desc(x)} (dist(n, m) + base(m))`.
//! Taking the max over all `x` covers exactly `desc(n) \ {n}`, and the remaining
//! `0` term of the recurrence is dominated by `n`'s own contribution
//! `dist(n, n) + base(n) = 1`. So
//! `f(n) = max(1, max_{m ≠ n}(dist + base)) = max_{m ∈ desc(n)}(dist + base)`. ∎
//!
//! A `max` needs no ordering and no combine step, so the driver carries the
//! accumulated `dist` DOWN in each task and keeps one running maximum. No result
//! slots, no `Assemble` tasks, no second stack.
//!
//! ⚠ Two consequences of the collapse worth naming, because they are what makes it
//! sound rather than merely convenient:
//!
//! 1. **Order is irrelevant**, so the element walk uses
//!    [`OrderSensitivity::OrderAgnostic`](crate::gen::term_ops::collection_walk::OrderSensitivity)
//!    and EVERY container shape converts — unordered ones included. `term_depth`
//!    joins `Drop` as the second traversal with no residue at the boundary.
//! 2. **A collection FIELD's elements are pushed at `dist + 1`, not `dist + 2`**,
//!    because the container contributes no level of its own — while a collection
//!    CATEGORY's elements are pushed at `dist + 1` from a node whose own `base` is
//!    already 1. Conflating the two is the one way to get this wrong, and it is the
//!    same distinction the pre-conversion `field_depth_expr` /
//!    `generate_depth_arm` split encoded.

use crate::gen::term_ops::collection_walk::{
    for_each_subterm, plan_for, CollectionPlan, OrderSensitivity, WalkOrder,
};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::subst::{collect_category_variants, FieldInfo, VariantKind};

/// Generate the `DepthTask` worklist, its engine, and one
/// `impl Cat { pub fn term_depth(&self) -> u32 }` per category.
pub fn generate_term_depth_methods(language: &LanguageDef) -> TokenStream {
    let task_enum = generate_depth_task_enum(language);
    let engine = generate_depth_engine(language);
    let wrappers: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_depth_wrapper(&lang_type.name))
        .collect();

    quote! {
        #task_enum
        #engine
        #(#wrappers)*
    }
}

/// The `DepthTask` enum and its thread-local pool.
///
/// Each variant carries a raw pointer to a node AND the accumulated distance from
/// the root — the `(node, dist)` pair that makes a result stack unnecessary (see
/// the module header's proof).
fn generate_depth_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Depth{}", cat);
            quote! { #variant_name(*const #cat, u32) }
        })
        .collect();

    quote! {
        /// Work item for the iterative term-depth engine.
        ///
        /// `(node, dist)` — the node to inspect and its distance in child-position
        /// edges from the root of the walk. The engine keeps ONE running maximum of
        /// `dist + base(node)`, which is exactly `term_depth` (the derivation is in
        /// `macros/src/gen/term_ops/depth.rs`'s module header), so there is no result
        /// stack and no combine task.
        #[allow(dead_code)]
        enum DepthTask {
            #(#variants),*
        }

        // SAFETY: same justification as `HashTask` in iterative_hash.rs — the
        // pointers are dereferenced only on the thread that derived them, within the
        // lifetime of the `&self` they came from.
        unsafe impl Send for DepthTask {}
        unsafe impl Sync for DepthTask {}

        thread_local! {
            /// Pool for reusing `DepthTask` work stacks across `term_depth()` calls.
            /// Same `Cell<Vec<_>>` pattern as the other iterative term ops: the first
            /// call allocates, later calls reuse, and a re-entrant call gets a fresh
            /// empty vector.
            static DEPTH_TASK_POOL: std::cell::Cell<Vec<DepthTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

/// Per-category handlers plus the `depth_iterative` engine.
fn generate_depth_engine(language: &LanguageDef) -> TokenStream {
    let helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let helper_fn = format_ident!("depth_handle_{}", cat.to_string().to_lowercase());
            let variants = collect_category_variants(cat, language);
            let variant_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_depth_arm(cat, v, language))
                .collect();
            quote! {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn #helper_fn(
                    stack: &mut Vec<DepthTask>,
                    deepest: &mut u32,
                    ptr: *const #cat,
                    dist: u32,
                ) {
                    let val = unsafe { &*ptr };
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
            let task_variant = format_ident!("Depth{}", cat);
            let helper_fn = format_ident!("depth_handle_{}", cat.to_string().to_lowercase());
            quote! {
                DepthTask::#task_variant(ptr, dist) => {
                    #helper_fn(stack, &mut deepest, ptr, dist);
                }
            }
        })
        .collect();

    quote! {
        #(#helper_fns)*

        /// Iterative term-depth engine. Drains the work stack, keeping one running
        /// maximum of `dist + base(node)`.
        ///
        /// # Safety
        ///
        /// Every `*const Cat` in `DepthTask` must be valid for reads for the duration
        /// of this call. Guaranteed because they are derived from `&self` in
        /// `term_depth()`.
        #[allow(dead_code, unused_variables)]
        fn depth_iterative(stack: &mut Vec<DepthTask>) -> u32 {
            let mut deepest: u32 = 0;
            while let Some(task) = stack.pop() {
                match task {
                    #(#task_arms)*
                }
            }
            deepest
        }
    }
}

/// `impl Cat { pub fn term_depth(&self) -> u32 }` — seeds the stack at distance 0
/// and runs the engine.
fn generate_depth_wrapper(category: &Ident) -> TokenStream {
    let task_variant = format_ident!("Depth{}", category);
    quote! {
        impl #category {
            /// Compute the maximum nesting depth of this term.
            ///
            /// - Leaves (variables, literals, nullary constructors): 0
            /// - Constructors: 1 + max(child depths)
            /// - Collection categories: 1 + max(element depths)
            /// - Binders: 1 + max(pre-scope fields, body)
            ///
            /// ★ Heap-bounded (#162): an explicit `(node, dist)` worklist with one
            /// running maximum, so native stack usage does not grow with term
            /// nesting depth. The pre-#162 form was bare host recursion and measured
            /// 3,408 B/level (debug) / 207 (release).
            ///
            /// Used by the Dovetail e-graph build to derive its saturation-work
            /// allowance. It does not limit the depth of this traversal.
            pub fn term_depth(&self) -> u32 {
                let mut stack = DEPTH_TASK_POOL.with(|pool| pool.take());
                stack.clear();
                stack.push(DepthTask::#task_variant(self as *const _, 0u32));
                let result = depth_iterative(&mut stack);
                // Return the buffer so the steady state is allocation-free. A
                // re-entrant call took an empty vector and gives back its own.
                stack.clear();
                DEPTH_TASK_POOL.with(|pool| pool.set(stack));
                result
            }
        }
    }
}

/// Record this node's own contribution, `dist + base(n)`, into the running maximum.
///
/// `base` is 1 for every node that has child POSITIONS in the depth recurrence and 0
/// for a leaf kind. It is emitted as a statement rather than folded into the pushes
/// because a node with no pushed children (an empty collection, or a constructor
/// whose every field is a predicate/opaque leaf) still contributes `dist + 1`.
fn record_own_contribution(base: u32) -> TokenStream {
    if base == 0 {
        quote! {
            if dist > *deepest {
                *deepest = dist;
            }
        }
    } else {
        quote! {
            let __own = dist.saturating_add(#base);
            if __own > *deepest {
                *deepest = __own;
            }
        }
    }
}

/// Generate the handler arm for one variant.
fn generate_depth_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        // #141 G5 — a classification that refuses carries its diagnostic into the
        // emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },

        // -- the three LEAF kinds: base 0, no children --
        VariantKind::Var { label } => {
            let own = record_own_contribution(0);
            quote! { #category::#label(_) => { #own } }
        },
        // A SCALAR literal has depth 0: its payload is a native value with no term
        // structure, so there is nothing below it to measure.
        VariantKind::Literal { label } => {
            let own = record_own_contribution(0);
            quote! { #category::#label(_) => { #own } }
        },
        VariantKind::Nullary { label } => {
            let own = record_own_contribution(0);
            quote! { #category::#label => { #own } }
        },

        // #29 — a COLLECTION literal is a container OF TERMS, so it is a node in its
        // own right (base 1) whose element depths are measured one level below. This
        // arm once shared the scalar-literal arm and answered 0 unconditionally, so
        // `depth([1, [2, 3]])` was 0 — a term visibly two levels deep measured as a
        // leaf.
        VariantKind::CollectionLiteral { label, element_cat, coll_type }
        | VariantKind::Collection { label, element_cat, coll_type } => {
            let own = record_own_contribution(1);
            // The container IS the node, so its elements sit at `dist + 1`.
            let pushes = collection_element_pushes(
                element_cat,
                coll_type,
                &quote! { coll },
                &quote! { dist.saturating_add(1) },
                language,
            );
            quote! {
                #category::#label(coll) => {
                    #own
                    #pushes
                }
            }
        },

        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            let own = record_own_contribution(1);
            let pushes = carrier.for_each_borrowed_subterm(
                &quote! { native },
                crate::gen::native_carrier::NativeCarrierWalkOrder::Forward,
                &|child_category, child| {
                    let task = format_ident!("Depth{}", child_category);
                    quote! {
                        stack.push(DepthTask::#task(
                            #child as *const _,
                            dist.saturating_add(1),
                        ));
                    }
                },
            );
            quote! {
                #category::#label(native) => {
                    #own
                    #pushes
                }
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_regular_depth_arm(category, label, fields, language)
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
        | VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_binder_depth_arm(category, label, pre_scope_fields, body_cat, language)
        },
    }
}

/// Pushes for every ELEMENT position of a collection, at `child_dist`.
///
/// Routed through `collection_walk::plan_for` with
/// [`OrderSensitivity::OrderAgnostic`] — `max` needs no ordering, so EVERY container
/// shape converts here, unordered ones included. `term_depth` and `Drop` are the two
/// traversals with no residue at the collection boundary, and for the same reason.
fn collection_element_pushes(
    element_cat: &Ident,
    coll_type: &CollectionType,
    coll_expr: &TokenStream,
    child_dist: &TokenStream,
    language: &LanguageDef,
) -> TokenStream {
    match plan_for(element_cat, coll_type, OrderSensitivity::OrderAgnostic, language) {
        CollectionPlan::PerElement { element_cat, coll_type } => {
            let task_variant = format_ident!("Depth{}", element_cat);
            for_each_subterm(&coll_type, coll_expr, WalkOrder::Forward, &|elem, _| {
                quote! {
                    stack.push(DepthTask::#task_variant(#elem as *const _, #child_dist));
                }
            })
        },
        // A container of PRIMITIVES (`![Vec<u8>]`) has no sub-terms, so it
        // contributes no depth below its own node.
        CollectionPlan::WholeValue { .. } => quote! {},
    }
}

/// Pushes for one field's child positions, at `child_dist`.
///
/// Returns an empty stream for a field that contributes nothing: a `BehavioralPred`
/// or a token-text/guest-body capture is a constant-size payload and is NOT part of
/// host term nesting (`term_depth` counts host-term nesting only).
fn field_depth_pushes(
    field: &FieldInfo,
    name: &Ident,
    child_dist: &TokenStream,
    language: &LanguageDef,
) -> TokenStream {
    if field.is_predicate || field.is_opaque_leaf() {
        return quote! {};
    }
    if field.is_optional {
        if field.is_collection {
            // Phase 4 #3: Optional-Collection — `None` contributes 0, `Some(c)`
            // contributes its elements' depths.
            let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
            let inner = collection_element_pushes(
                &field.category,
                &coll_type,
                &quote! { __c },
                child_dist,
                language,
            );
            return quote! {
                if let Some(__c) = #name.as_ref() {
                    #inner
                }
            };
        }
        // Opt-Group `Option<Box<Cat>>`: `None` contributes 0.
        let task_variant = format_ident!("Depth{}", field.category);
        return quote! {
            if let Some(__b) = #name.as_ref() {
                stack.push(DepthTask::#task_variant(__b.as_ref() as *const _, #child_dist));
            }
        };
    }
    if field.is_collection {
        // A collection FIELD's container adds NO level of its own — only the
        // enclosing node's `base` of 1 counts — so its elements sit at the SAME
        // `child_dist` as a boxed sibling child, not one deeper. Conflating this with
        // the collection-CATEGORY case is the one way to get this conversion wrong.
        let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
        return collection_element_pushes(
            &field.category,
            &coll_type,
            &quote! { #name },
            child_dist,
            language,
        );
    }
    let task_variant = format_ident!("Depth{}", field.category);
    quote! {
        stack.push(DepthTask::#task_variant(&**#name as *const _, #child_dist));
    }
}

/// Handler arm for a `Regular` variant: base 1, every field's child positions at
/// `dist + 1`.
fn generate_regular_depth_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let own = record_own_contribution(1);
    let child_dist = quote! { __child_dist };
    let pushes: Vec<TokenStream> = fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| field_depth_pushes(field, name, &child_dist, language))
        .collect();

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #own
            let __child_dist = dist.saturating_add(1);
            let _ = __child_dist;
            #(#pushes)*
        }
    }
}

/// Handler arm for a `Binder` / `MultiBinder` variant: base 1, pre-scope fields AND
/// the scope body at `dist + 1`.
///
/// The scope's PATTERN contributes nothing — it is a `Binder<String>` (or a `Vec` of
/// them), a name, not a host sub-term. That matches the pre-#162 arm, which combined
/// only the pre-scope field depths and the body depth.
fn generate_binder_depth_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("f{}", i))
        .collect();
    let own = record_own_contribution(1);
    let child_dist = quote! { __child_dist };
    let pushes: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| field_depth_pushes(field, name, &child_dist, language))
        .collect();
    let body_task = format_ident!("Depth{}", body_cat);

    let pattern = if field_names.is_empty() {
        quote! { #category::#label(scope) }
    } else {
        quote! { #category::#label(#(ref #field_names,)* scope) }
    };

    quote! {
        #pattern => {
            #own
            let __child_dist = dist.saturating_add(1);
            let _ = __child_dist;
            #(#pushes)*
            let __body: *const #body_cat = &*scope.inner().unsafe_body;
            stack.push(DepthTask::#body_task(__body, __child_dist));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A `HashMap`-shaped collection must contribute BOTH its keys and its values.
    /// The pre-#162 emitter expressed that as `k.term_depth().max(v.term_depth())`;
    /// the converted one expresses it as two pushes per entry, which is what
    /// `collection_walk::for_each_subterm` emits for a key/value shape.
    #[test]
    fn collection_depth_hashmap_pushes_both_keys_and_values() {
        let language = crate::gen::collection_literal_language_for_tests();
        let proc = format_ident!("Proc");
        let generated = collection_element_pushes(
            &proc,
            &CollectionType::HashMap,
            &quote! { coll },
            &quote! { d },
            &language,
        )
        .to_string();
        assert_eq!(
            generated.matches("DepthProc").count(),
            2,
            "a map entry has a KEY and a VALUE sub-term; pushing only one leaves half \
             the container unmeasured: {generated}"
        );
    }

    /// A `HashBag`'s multiplicity is a count, not a term, so exactly one push per
    /// distinct element.
    #[test]
    fn collection_depth_hashbag_pushes_the_element_not_the_count() {
        let language = crate::gen::collection_literal_language_for_tests();
        let proc = format_ident!("Proc");
        let generated = collection_element_pushes(
            &proc,
            &CollectionType::HashBag,
            &quote! { coll },
            &quote! { d },
            &language,
        )
        .to_string();
        assert_eq!(
            generated.matches("DepthProc").count(),
            1,
            "a bag entry is `(element, count)` and only the element is a term: {generated}"
        );
    }

    /// Unlike the order-SENSITIVE traversals, `term_depth` converts every container
    /// shape — `max` needs no ordering. A `WholeValue` plan here would silently drop
    /// a whole container's depth, since there is no fallback expression to fall back
    /// TO (the pushes are the only thing measuring the elements).
    #[test]
    fn every_container_shape_is_walked_per_element() {
        let language = crate::gen::collection_literal_language_for_tests();
        let proc = format_ident!("Proc");
        for coll_type in [
            CollectionType::Vec,
            CollectionType::HashSet,
            CollectionType::HashBag,
            CollectionType::HashMap,
            CollectionType::PathMap,
        ] {
            let generated = collection_element_pushes(
                &proc,
                &coll_type,
                &quote! { coll },
                &quote! { d },
                &language,
            )
            .to_string();
            assert!(
                generated.contains("DepthProc"),
                "{coll_type:?} emitted no element push at all, so every element of such a \
                 container would be measured as depth 0: {generated}"
            );
        }
    }

    /// A predicate / opaque-capture leaf field emits NOTHING, rather than a push that
    /// would need a task variant for a non-category type.
    #[test]
    fn a_leaf_field_contributes_no_push() {
        let language = crate::gen::collection_literal_language_for_tests();
        let leaf = FieldInfo {
            category: format_ident!("Proc"),
            is_collection: false,
            coll_type: None,
            is_predicate: false,
            is_optional: false,
            opaque_leaf: Some(crate::gen::term_ops::subst::OpaqueLeafKind::TokenText),
        };
        let name = format_ident!("f0");
        assert!(
            field_depth_pushes(&leaf, &name, &quote! { d }, &language)
                .to_string()
                .trim()
                .is_empty(),
            "an opaque-capture leaf is a constant-size payload and is not host term \
             nesting, so it must emit no push — a push would need a `DepthString`, \
             which does not exist"
        );
    }
}
