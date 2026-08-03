//! Ground-term checking generation for MeTTaIL terms
//!
//! Generates a per-category `is_ground()` that reports whether a term contains any
//! free variables. A ground term is fully concrete — all leaf positions are literals
//! or nullary constructors.
//!
//! ## Motivation
//!
//! The previous `is_accepting()` implementation had two problems:
//! 1. **Wasteful**: for native types it called `try_eval()`, which computes the full
//!    native value then discards it, only to re-evaluate it later.
//! 2. **Shallow**: for non-native types it only checked for bare variables at the top
//!    level, missing variables nested inside compound terms.
//!
//! `is_ground()` fixes both: zero arithmetic, deep traversal.
//!
//! ## ★★ #189 — `is_ground` was the ELEVENTH driver, and it hid the same way the tenth did
//!
//! Before this conversion `ground.rs` emitted bare host recursion — `f0.is_ground()`,
//! `coll.iter().all(|x| x.is_ground())` — exactly the shape [`depth.rs`](super::depth)
//! had before #162 converted it. It is compiled into every language (2,650 recursive
//! call sites in `target/generated/rholang/is_ground.rs` alone, one handler family per
//! category) and it has a generated caller at
//! `target/generated/rholang/parse_alt_filter.rs`.
//!
//! ⚠★★ **The dangerous part was never the recursion — it was the INVISIBILITY.**
//! `stack_depth_gate`'s `the_sloped_driver_set_is_exactly_the_declared_one` totals in
//! *both* directions over a universe it enumerates from `stack_depth_probe`'s
//! `SUBJECTS` table at run time, precisely so that a new driver cannot go
//! unclassified. But `is_ground` had **no probe subject**, so it was not a row in the
//! table to be totalled — and a bidirectional totality gate over a universe that does
//! not contain the defect cannot see the defect. That is exactly how the TENTH driver
//! (`term_depth`) hid, and then this ELEVENTH one. The conversion below is the easy
//! half; the subject (`ast_is_ground` / `ast_is_ground_add`) and the derived
//! traversal-census gate are the fix for the hole.
//!
//! ## The conversion is SIMPLER than `term_depth`'s, and that is a derivation
//!
//! `term_depth` needed an accumulated `dist` carried down each task so that one
//! running maximum could stand in for a result stack. `is_ground` needs neither:
//!
//! ```math
//! g(n) \;=\; \bigwedge_{m \,\in\, \mathrm{desc}(n)} \mathrm{base}(m),
//! \qquad
//! \mathrm{base}(m) \;=\; \begin{cases} \bot & m \text{ is a } \mathtt{Var} \text{ leaf} \\ \top & \text{otherwise} \end{cases}
//! ```
//!
//! **Proof.** The pre-conversion recurrence is
//! `g(n) = base(n) ∧ ⋀_{x ∈ children(n)} g(x)`.
//!
//! *Base case.* A node with no pushed children: `g(n) = base(n)`, and the right-hand
//! side is the one-element conjunction `base(n)`. They agree.
//!
//! *Inductive step.* By the induction hypothesis each child contributes
//! `g(x) = ⋀_{m ∈ desc(x)} base(m)`. `desc(n) = {n} ⊎ ⨄_x desc(x)` is a partition, and
//! `∧` is associative and commutative, so
//! `base(n) ∧ ⋀_x ⋀_{m ∈ desc(x)} base(m) = ⋀_{m ∈ desc(n)} base(m)`. ∎
//!
//! Three consequences, and each is what makes the conversion sound rather than merely
//! convenient:
//!
//! 1. **No result stack, no combine task, and no `dist`.** The conjunction is over a
//!    SET, so the driver keeps no per-node state at all: a handler returns `false` the
//!    moment it sees a `Var` leaf and the driver stops. `term_depth` needed `dist`
//!    because `max(dist + base)` is a function of *where* a node sits; `⋀ base` is not.
//! 2. **Order is irrelevant**, because `∧` is commutative — so the element walk uses
//!    [`OrderSensitivity::OrderAgnostic`] and EVERY container shape converts,
//!    unordered ones included. `is_ground` joins `Drop` and `term_depth` as a traversal
//!    with no residue at the collection boundary.
//! 3. **Short-circuiting is preserved but REORDERED, and the result is unchanged.** The
//!    `&&`-join short-circuited in field order; the LIFO worklist short-circuits in
//!    whatever order the stack drains. `is_ground` is pure — it reads the term and
//!    writes nothing — so the two orders compute the same boolean. This is the one
//!    place the conversion is *observably* different from the original, and the
//!    difference is confined to which subterms get visited before the answer is known.
//!
//! ## What the conversion did NOT change, and one discrepancy it inherits
//!
//! Every arm's verdict is the pre-#189 verdict:
//!
//! | variant kind | verdict | children pushed |
//! |---|---|---|
//! | `Var` | `false` | — |
//! | `Literal` (native scalar payload) | `true` | — |
//! | `Nullary` | `true` | — |
//! | `Collection` / `CollectionLiteral` | `true` | every element position |
//! | `Regular` | `true` | every non-leaf field |
//! | `Binder` / `MultiBinder` | `true` | pre-scope fields + the scope BODY |
//!
//! ⚠ **An inherited discrepancy, reported and deliberately NOT changed here.** The doc
//! comment on the generated method used to say *"Bound variables (inside `Scope`) do
//! not make a term non-ground"*, but the `Var` arm answers `false` for `Var::Bound`
//! just as it does for `Var::Free` — `moniker` replaces bound occurrences with
//! `Var::Bound` inside a `Scope`, and the arm does not look. So `new a in { a!(1) }`
//! reports NOT ground. That is pre-#189 behaviour, it is a semantics question rather
//! than a stack-safety one, and changing it inside a conversion would make the
//! conversion unverifiable. The claim has been dropped from the emitted doc comment
//! (it was describing behaviour the code does not have) and recorded here instead, so
//! the next reader does not have to re-derive it.
//!
//! ## Deliberate retirement: the `clippy::eq_op` guard
//!
//! The pre-#189 emitter joined per-field checks with `&&`, and a variant whose fields
//! were all unconditionally ground produced the literal tautology `true && true` in
//! the generated source — `clippy::eq_op`, deny-by-default, which reached
//! `target/generated/l9modaltoy/is_ground.rs:25` for real. `field_ground_check`
//! returned `Option<TokenStream>` so an unconditional field could drop OUT of the join
//! rather than emit a literal `true`, and a unit test pinned it.
//!
//! That hazard is now structurally unspellable: there is no `&&`-join at all. A field
//! that asks no runtime question emits NO PUSH, and a variant with no pushes is an arm
//! whose body is the single expression `true`. The successor test
//! [`tests::a_leaf_field_contributes_no_push`] pins the same property in the shape it
//! now takes.

use crate::gen::term_ops::collection_walk::{
    for_each_subterm, plan_for, CollectionPlan, OrderSensitivity, WalkOrder,
};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::subst::{collect_category_variants, FieldInfo, VariantKind};

/// Generate the `GroundTask` worklist, its engine, and one
/// `impl Cat { pub fn is_ground(&self) -> bool }` per category.
pub fn generate_is_ground_methods(language: &LanguageDef) -> TokenStream {
    let task_enum = generate_ground_task_enum(language);
    let engine = generate_ground_engine(language);
    let wrappers: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_ground_wrapper(&lang_type.name))
        .collect();

    quote! {
        #task_enum
        #engine
        #(#wrappers)*
    }
}

/// The `GroundTask` enum and its thread-local pool.
///
/// One variant per category, carrying only a raw pointer: unlike `DepthTask` there is
/// no accumulated state to carry, because `⋀ base` does not depend on where a node
/// sits (see the module header's proof).
fn generate_ground_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Ground{}", cat);
            quote! { #variant_name(*const #cat) }
        })
        .collect();

    quote! {
        /// Work item for the iterative ground-check engine.
        ///
        /// A bare node pointer. `is_ground` is a conjunction over the DESCENDANT SET,
        /// which is order- and position-independent, so there is no accumulated
        /// distance to carry (as `DepthTask` must), no result stack and no combine
        /// task. The derivation is in `macros/src/gen/term_ops/ground.rs`'s header.
        #[allow(dead_code)]
        enum GroundTask {
            #(#variants),*
        }

        // SAFETY: same justification as `HashTask` in iterative_hash.rs — the
        // pointers are dereferenced only on the thread that derived them, within the
        // lifetime of the `&self` they came from.
        unsafe impl Send for GroundTask {}
        unsafe impl Sync for GroundTask {}

        thread_local! {
            /// Pool for reusing `GroundTask` work stacks across `is_ground()` calls.
            /// Same `Cell<Vec<_>>` pattern as the other iterative term ops: the first
            /// call allocates, later calls reuse, and a re-entrant call gets a fresh
            /// empty vector.
            static GROUND_TASK_POOL: std::cell::Cell<Vec<GroundTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

/// Per-category handlers plus the `ground_iterative` engine.
///
/// A handler returns `false` iff the node it inspected is itself a non-ground LEAF.
/// Everything else it has to say, it says by pushing children.
fn generate_ground_engine(language: &LanguageDef) -> TokenStream {
    let helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let helper_fn = format_ident!("ground_handle_{}", cat.to_string().to_lowercase());
            let variants = collect_category_variants(cat, language);
            let variant_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_ground_arm(cat, v, language))
                .collect();
            quote! {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn #helper_fn(
                    stack: &mut Vec<GroundTask>,
                    ptr: *const #cat,
                ) -> bool {
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
            let task_variant = format_ident!("Ground{}", cat);
            let helper_fn = format_ident!("ground_handle_{}", cat.to_string().to_lowercase());
            quote! {
                GroundTask::#task_variant(ptr) => #helper_fn(stack, ptr),
            }
        })
        .collect();

    quote! {
        #(#helper_fns)*

        /// Iterative ground-check engine. Drains the work stack and stops at the first
        /// non-ground leaf.
        ///
        /// # Safety
        ///
        /// Every `*const Cat` in `GroundTask` must be valid for reads for the duration
        /// of this call. Guaranteed because they are derived from `&self` in
        /// `is_ground()`.
        #[allow(dead_code, unused_variables)]
        fn ground_iterative(stack: &mut Vec<GroundTask>) -> bool {
            while let Some(task) = stack.pop() {
                let __node_is_ground = match task {
                    #(#task_arms)*
                };
                // ★ Short-circuit. `∧` is commutative, so stopping here yields the
                // same answer the pre-#189 `&&`-join did — it merely stops at a
                // different subterm. The caller clears whatever is left on the stack.
                if !__node_is_ground {
                    return false;
                }
            }
            true
        }
    }
}

/// `impl Cat { pub fn is_ground(&self) -> bool }` — seeds the stack and runs the engine.
fn generate_ground_wrapper(category: &Ident) -> TokenStream {
    let task_variant = format_ident!("Ground{}", category);
    quote! {
        impl #category {
            /// Returns `true` if this term contains no variable leaves.
            ///
            /// A ground term is fully concrete — all leaf positions are literals or
            /// nullary constructors.
            ///
            /// ★ Heap-bounded (#189): an explicit worklist over the descendant set, so
            /// native stack usage does not grow with term nesting depth. The pre-#189
            /// form was bare host recursion (`f0.is_ground()`,
            /// `coll.iter().all(|x| x.is_ground())`) — the same shape `term_depth` had
            /// before #162.
            pub fn is_ground(&self) -> bool {
                let mut stack = GROUND_TASK_POOL.with(|pool| pool.take());
                stack.clear();
                stack.push(GroundTask::#task_variant(self as *const _));
                let result = ground_iterative(&mut stack);
                // ⚠ The clear is load-bearing on the `false` path: `ground_iterative`
                // short-circuits with tasks still queued, and returning a non-empty
                // buffer to the pool would leak stale pointers into the NEXT call.
                stack.clear();
                GROUND_TASK_POOL.with(|pool| pool.set(stack));
                result
            }
        }
    }
}

/// Generate the handler arm for one variant.
fn generate_ground_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        // ★ #141 G5 — a classification that refuses carries its diagnostic into the
        // emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },

        // -- the one NON-GROUND leaf --
        //
        // ⚠ `Var::Bound` answers `false` here too; see the module header's "inherited
        // discrepancy" note. Unchanged from pre-#189.
        VariantKind::Var { label } => quote! { #category::#label(_) => false, },

        // A SCALAR literal is ground by construction: its payload is a native value
        // (`i64`, `String`, `CanonicalBigRat`, …) with no term structure, so there is
        // nothing to descend into and no position a free variable could occupy.
        VariantKind::Literal { label } => quote! { #category::#label(_) => true, },

        VariantKind::Nullary { label } => quote! { #category::#label => true, },

        // ★ #29 (collection-literal Stage 2). A COLLECTION literal is NOT ground by
        // construction — its payload is a container OF TERMS, each of which may be a
        // free variable. This arm once shared the scalar-literal arm and answered
        // `true` unconditionally, so `[1, v]` reported ground with `v` free.
        //
        // That was a contract violation in the FAILURE direction, which is the
        // dangerous one: `is_ground` is consulted to decide whether a term may be
        // treated as a finished value, so a false `true` licenses downstream code to
        // skip work that was actually required, and it does so silently. A false
        // `false` would merely cost a redundant descent.
        VariantKind::CollectionLiteral { label, element_cat, coll_type }
        | VariantKind::Collection { label, element_cat, coll_type } => {
            let pushes =
                collection_element_pushes(element_cat, coll_type, &quote! { coll }, language);
            quote! {
                #category::#label(coll) => {
                    #pushes
                    true
                },
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_regular_ground_arm(category, label, fields, language)
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
        | VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_binder_ground_arm(category, label, pre_scope_fields, body_cat, language)
        },
    }
}

/// Pushes for every ELEMENT position of a collection.
///
/// Routed through [`plan_for`] with [`OrderSensitivity::OrderAgnostic`] — `∧` is
/// commutative, so EVERY container shape converts here, unordered ones included.
/// `is_ground`, `term_depth` and `Drop` are the three traversals with no residue at the
/// collection boundary, and for the same reason.
///
/// `PathMap` needs no special-casing: [`for_each_subterm`] reads the homogeneous
/// container mode and contributes no value position for a set entry.
fn collection_element_pushes(
    element_cat: &Ident,
    coll_type: &CollectionType,
    coll_expr: &TokenStream,
    language: &LanguageDef,
) -> TokenStream {
    match plan_for(element_cat, coll_type, OrderSensitivity::OrderAgnostic, language) {
        CollectionPlan::PerElement { element_cat, coll_type } => {
            let task_variant = format_ident!("Ground{}", element_cat);
            for_each_subterm(&coll_type, coll_expr, WalkOrder::Forward, &|elem, _| {
                quote! {
                    stack.push(GroundTask::#task_variant(#elem as *const _));
                }
            })
        },
        // A container of PRIMITIVES (`![Vec<u8>]`) holds no sub-terms, so it holds no
        // position a free variable could occupy and is ground by construction.
        CollectionPlan::WholeValue { .. } => quote! {},
    }
}

/// Pushes for one field's child positions.
///
/// Returns an empty stream for a field that asks no runtime question — a
/// `BehavioralPred` or a token-text/guest-body capture. A predicate's variables (e.g.
/// `halts(y)` referencing a pattern-bound `y`) are bound by the parent's
/// `MatchBindings` rather than by a host-category `FreeVar<String>`, and a token's text
/// is a native `String` with no term structure. Both are ground unconditionally.
///
/// ★ An empty stream is the whole reason the `clippy::eq_op` hazard is gone: an
/// unconditional field contributes nothing at all rather than a literal `true` that
/// would then have to be `&&`-joined with its siblings. See the module header.
fn field_ground_pushes(field: &FieldInfo, name: &Ident, language: &LanguageDef) -> TokenStream {
    if field.is_predicate || field.is_opaque_leaf() {
        return quote! {};
    }
    if field.is_optional {
        if field.is_collection {
            // Phase 4 #3 (2026-05-12): Optional-Collection — `None` is trivially
            // ground; `Some(c)` is ground iff every element is.
            let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
            let inner =
                collection_element_pushes(&field.category, &coll_type, &quote! { __c }, language);
            return quote! {
                if let Some(__c) = #name.as_ref() {
                    #inner
                }
            };
        }
        // Opt-Group `Option<Box<Cat>>`: `None` is trivially ground (no variables).
        let task_variant = format_ident!("Ground{}", field.category);
        return quote! {
            if let Some(__b) = #name.as_ref() {
                stack.push(GroundTask::#task_variant(__b.as_ref() as *const _));
            }
        };
    }
    if field.is_collection {
        let coll_type = field.coll_type.clone().unwrap_or(CollectionType::HashBag);
        return collection_element_pushes(&field.category, &coll_type, &quote! { #name }, language);
    }
    let task_variant = format_ident!("Ground{}", field.category);
    quote! {
        stack.push(GroundTask::#task_variant(&**#name as *const _));
    }
}

/// Handler arm for a `Regular` variant: not a leaf, so `true`, with every field's child
/// positions pushed.
fn generate_regular_ground_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let pushes: Vec<TokenStream> = fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| field_ground_pushes(field, name, language))
        .collect();

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#pushes)*
            true
        },
    }
}

/// Handler arm for a `Binder` / `MultiBinder` variant: pre-scope fields AND the scope
/// body.
///
/// The scope's PATTERN contributes nothing — it is a `Binder<String>` (or a `Vec` of
/// them), a name rather than a host sub-term. That matches the pre-#189 arm, which
/// conjoined only the pre-scope field checks and `scope.inner().unsafe_body`.
fn generate_binder_ground_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("f{}", i))
        .collect();
    let pushes: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| field_ground_pushes(field, name, language))
        .collect();
    let body_task = format_ident!("Ground{}", body_cat);

    let pattern = if field_names.is_empty() {
        quote! { #category::#label(scope) }
    } else {
        quote! { #category::#label(#(ref #field_names,)* scope) }
    };

    quote! {
        #pattern => {
            #(#pushes)*
            let __body: *const #body_cat = &*scope.inner().unsafe_body;
            stack.push(GroundTask::#body_task(__body));
            true
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A `HashMap`-shaped collection must inspect BOTH its keys and its values. The
    /// pre-#189 emitter expressed that as `k.is_ground() && v.is_ground()`; the
    /// converted one expresses it as two pushes per entry, which is what
    /// `collection_walk::for_each_subterm` emits for a key/value shape.
    #[test]
    fn collection_ground_hashmap_pushes_both_keys_and_values() {
        let language = crate::gen::collection_literal_language_for_tests();
        let proc = format_ident!("Proc");
        let generated =
            collection_element_pushes(&proc, &CollectionType::HashMap, &quote! { coll }, &language)
                .to_string();
        assert_eq!(
            generated.matches("GroundProc").count(),
            2,
            "a map entry has a KEY and a VALUE sub-term; pushing only one leaves half the \
             container unchecked, so a free variable in the other half would report GROUND — \
             a false `true`, which is the dangerous direction: {generated}"
        );
    }

    /// A `HashBag`'s multiplicity is a count, not a term, so exactly one push per
    /// distinct element.
    #[test]
    fn collection_ground_hashbag_pushes_the_element_not_the_count() {
        let language = crate::gen::collection_literal_language_for_tests();
        let proc = format_ident!("Proc");
        let generated =
            collection_element_pushes(&proc, &CollectionType::HashBag, &quote! { coll }, &language)
                .to_string();
        assert_eq!(
            generated.matches("GroundProc").count(),
            1,
            "a bag entry is `(element, count)` and only the element is a term: {generated}"
        );
    }

    /// Like `term_depth` and unlike the order-SENSITIVE traversals, `is_ground` converts
    /// every container shape — `∧` is commutative. A `WholeValue` plan here would
    /// silently drop a whole container's contents, and since the arm answers `true`
    /// unconditionally there is no fallback expression to fall back TO: the pushes are
    /// the only thing checking the elements.
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
            let generated =
                collection_element_pushes(&proc, &coll_type, &quote! { coll }, &language)
                    .to_string();
            assert!(
                generated.contains("GroundProc"),
                "{coll_type:?} emitted no element push at all, so every element of such a \
                 container would go unchecked and the container would report GROUND: {generated}"
            );
        }
    }

    /// Set mode contributes no value position; map mode contributes one.
    #[test]
    fn a_pathmap_checks_the_key_always_and_the_value_only_when_set() {
        let language = crate::gen::collection_literal_language_for_tests();
        let proc = format_ident!("Proc");
        let generated =
            collection_element_pushes(&proc, &CollectionType::PathMap, &quote! { coll }, &language)
                .to_string();
        assert_eq!(
            generated.matches("GroundProc").count(),
            2,
            "a pathmap entry has a key and (in map mode) a value: {generated}"
        );
        assert!(
            generated.contains("entry . value"),
            "the value push is not guarded by the homogeneous entry's value projection: \
             {generated}"
        );
    }

    /// ★★ The successor to the pre-#189 `clippy::eq_op` regression test.
    ///
    /// That test asserted `field_ground_check` returned `None` for an unconditional
    /// field, because `Some(quote!{true})` would have produced the literal tautology
    /// `true && true` in the generated source — a deny-by-default lint that reached
    /// `target/generated/l9modaltoy/is_ground.rs:25` for real. There is no `&&`-join any
    /// more, so the tautology is unspellable; the property that MATTERS survives and is
    /// asserted here: an unconditional field emits no push, and a variant whose every
    /// field is unconditional is the single expression `true`.
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
            field_ground_pushes(&leaf, &name, &language)
                .to_string()
                .trim()
                .is_empty(),
            "an opaque-capture leaf is a native `String` with no host term structure, so it \
             must emit no push — a push would need a `GroundString`, which does not exist"
        );

        let arm = generate_regular_ground_arm(
            &format_ident!("Num"),
            &format_ident!("Two"),
            &[leaf.clone(), leaf],
            &language,
        )
        .to_string();
        assert!(
            !arm.contains("GroundProc") && !arm.contains("&&"),
            "an all-unconditional variant must be the single expression `true`, with no push \
             and no join: {arm}"
        );
    }

    /// The `Var` arm is the ONLY thing that can answer `false`, and it must answer
    /// `false`. If it ever started pushing instead, `is_ground` would return `true` for
    /// every term — a false `true` for every open term at once, in the failure direction
    /// #29 named as the dangerous one.
    #[test]
    fn the_var_arm_is_the_only_false() {
        let language = crate::gen::collection_literal_language_for_tests();
        let var = VariantKind::Var { label: format_ident!("PVar") };
        let arm = generate_ground_arm(&format_ident!("Proc"), &var, &language).to_string();
        assert!(
            arm.contains("false"),
            "the `Var` arm no longer answers `false`, so no term can ever be reported \
             non-ground: {arm}"
        );

        let nullary = VariantKind::Nullary { label: format_ident!("PZero") };
        let nullary_arm =
            generate_ground_arm(&format_ident!("Proc"), &nullary, &language).to_string();
        assert!(
            !nullary_arm.contains("false"),
            "a NULLARY constructor is ground — it has no position a variable could occupy — \
             so its arm must not answer `false`: {nullary_arm}"
        );
    }
}
