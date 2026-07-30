//! # The COLLECTION-ELEMENT BOUNDARY — one mechanism for every generated traversal
//!
//! ## The defect this module exists to end (#162)
//!
//! `macros/src/gen/` emits a family of per-category traversals over the AST
//! (`PartialEq`, `Ord`, `Hash`, `semantic_hash`, `Debug`, `Drop`,
//! `match_pattern`, `term_depth`, `is_ground`, `subst`, `normalize`, `Display`).
//! Most of them are **work-stack drivers**: a pooled `Vec<…Task>` worklist, a
//! `while let Some(task) = stack.pop()` engine, and one task variant per
//! category. The point of that shape is that native stack usage does not grow
//! with term nesting depth.
//!
//! Seven of them nevertheless grew with depth, and the escape was ALWAYS the
//! same three-hop shape:
//!
//! ```text
//!   Category  ──►  Collection<Elem>  ──►  Elem
//!   ▲              ▲                      ▲
//!   │              │                      └─ a sub-TERM: the driver must descend
//!   │              └─ handed WHOLE to a trait method (`PartialEq`, `Ord`,
//!   │                 `Hash`, `Debug`, `Drop`) that cannot see `stack`
//!   └─ reached correctly, ON the work stack
//! ```
//!
//! The category hop is followed correctly — `iterative_cmp` really does
//! `stack.push(CmpTask::CmpList(..))` for `Proc::CastList(Arc<List>)`. The
//! escape is one level FURTHER DOWN: `(List::ListLit(a), List::ListLit(b)) => if
//! a != b`, where `a` and `b` are `&Vec<Proc>` and `!=` is `Vec<Proc>:
//! PartialEq`, which calls `Proc::eq` per element — re-entering the driver by
//! HOST RECURSION, one native frame per level, with no access to `stack`.
//!
//! ## Why it happened, stated once so it is not re-introduced
//!
//! [`VariantKind::CollectionLiteral`](super::subst::VariantKind::CollectionLiteral)
//! was introduced (2026-07-25) as a DISTINCT discriminant from
//! [`VariantKind::Literal`](super::subst::VariantKind::Literal) precisely so the
//! exhaustiveness checker would force every consumer to declare its intent. The
//! seven sloped drivers are exactly the consumers that still shared `Literal`'s
//! arm — i.e. that still treated *a container of sub-terms* as *an opaque native
//! leaf*. So the slope and the `unique_id` leak of #154 are the SAME defect seen
//! from two angles, and this module is the shared answer to both.
//!
//! ## The second ingredient: a task enum has to be COMPLETE
//!
//! Pushing one task per element is necessary but not sufficient. A work-stack
//! driver can only replace host recursion for work its **task enum can
//! represent**. `DisplayTask` has `WriteLiteral`/`WriteString`, and `SubstTask`
//! has `Assemble…` + a result-slot array — non-descent work is a task in both,
//! so descents can be interleaved with it in exact order. That is *why*
//! `ast_display` and `ast_subst` are 0 B/level while their siblings are not.
//!
//! `CmpTask`/`HashTask` held ONLY descents. Any work that had to happen
//! *between* two descents therefore had to be done eagerly, and "eagerly" for a
//! container of sub-terms means a whole-value trait call. (Read
//! `generate_cmp_regular_arm`'s history in `iterative_cmp.rs` for 130 lines of
//! the author discovering exactly this wall: *"But CmpTask only holds `*const
//! Cat`…"*.) So each converted driver also gains a variant that carries
//! ALREADY-COMPUTED work — `CmpTask::Verdict(Ordering)`, `HashTask::Absorb*` —
//! and then the eager-prefix hack dissolves along with the escape.
//!
//! ## ★ The BOUNDARY, and why it is a proof rather than a scope-down
//!
//! Not every container can be walked element-wise. The test is
//! [`is_order_faithful`], and it is a statement about the container's own
//! `Hash`/`PartialEq`/`Ord` CONTRACT, not about this emitter's convenience:
//!
//! | container | its `Hash` writes | reproducible per-element on the SAME `state`? |
//! |---|---|---|
//! | `Vec<T>` | `write_usize(len)`, then each element in index order | **YES** — exactly |
//! | `HashSetLit<T>` | `len`, then elements in `T: Ord` SORTED order | no — the sort's comparator is `T::cmp` |
//! | `HashBag<T>` | `total_count`, `len`, then four commutative lanes built from PER-ELEMENT SUB-HASHERS | no — the elements never touch `state` |
//! | `HashMapLit<K,V>` / `PathMapLit<K,V>` | same commutative-lane shape | no |
//!
//! An unordered container's identity is *defined* by a canonical order or a
//! commutative combine over its elements. Computing either requires element-level
//! `cmp` or per-element sub-hashers — both of which are whole-value calls back
//! into the very driver. Flattening them onto the driver's own `state`/stack
//! would change the bytes written, and those bytes are CONSENSUS-VISIBLE
//! (`semantic_fingerprint` feeds the exact-key / realize-dedup surface, and
//! `Proc` is a hash key inside the AST: `Set`=`HashSetLit<Proc>`,
//! `Bag`=`HashBag<Proc>`, `Map`=`HashMap<Proc,Proc>`, `PPar(HashBag<Proc>)`).
//!
//! ⇒ For an unordered container the driver keeps its whole-value call, and the
//! residual host recursion is Θ(count of nested UNORDERED-container levels) —
//! **not** Θ(term depth). `Set(Set(Set(…)))` still pays; `[[[…]]]` no longer
//! does. That residue is MEASURED and DECLARED by
//! `rholang-runtime/tests/stack_depth_gate.rs` rather than left implicit.
//!
//! ⚠ `Drop` is the one exception and it is exempt for a reason, not by
//! oversight: destruction ORDER is unobservable, so every container shape can be
//! walked element-wise there. Callers say so with
//! [`OrderSensitivity::OrderAgnostic`].
//!
//! ## The other trap: an element that is not a category
//!
//! `![Vec<u8>]` (rholang's `Bytes` carrier) is a `Vec`, and it is order-faithful,
//! but `u8` is not a category and no `CmpTask::Cmpu8` exists. Emitting one
//! produced `DisplayTask::Displayu8` when `Bytes` gained a real carrier
//! (measured 2026-07-29). [`plan_for`] therefore asks
//! [`names_a_category`] and returns [`CollectionPlan::WholeValue`] with
//! [`WholeValueReason::ElementIsNotACategory`] — which is *also* stack-safe,
//! because a container of primitives has no sub-terms to recurse into.

use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

/// Direction in which the emitted loop visits a container's sub-term positions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WalkOrder {
    /// Container order. For a driver that ACTS on each sub-term immediately
    /// (`is_ground`'s `&&` fold, `term_depth`'s `max`), or for one whose order
    /// is unobservable (`Drop`).
    Forward,
    /// REVERSE container order, so that a LIFO work stack pops the positions in
    /// container order: the first position must be pushed LAST.
    ///
    /// ⚠ This is the only correct choice for `Hash`, `Ord` and `Debug`, whose
    /// output depends on the order the positions are visited in.
    ReverseForLifo,
}

/// Whether the CALLING traversal's result depends on the order in which a
/// container's elements are visited.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OrderSensitivity {
    /// `Hash`, `semantic_hash`, `Ord`, `PartialEq`, `Debug`, `match_pattern` —
    /// the answer changes if the elements are visited in a different order, so
    /// only an [order-faithful](is_order_faithful) container may be walked.
    OrderSensitive,
    /// `Drop` — destruction order is unobservable, so EVERY container shape may
    /// be walked element-wise.
    OrderAgnostic,
}

/// What a driver must do with one collection of sub-terms. Returned by
/// [`plan_for`].
///
/// ★ A two-variant enum rather than an `Option` or a bare predicate, so that the
/// exhaustiveness checker performs the census — the same reason
/// [`VariantKind::CollectionLiteral`](super::subst::VariantKind::CollectionLiteral)
/// is a discriminant. A caller cannot silently forget that the whole-value case
/// exists, and it cannot take it without naming a [`WholeValueReason`].
#[derive(Debug, Clone)]
pub(crate) enum CollectionPlan {
    /// Push/visit ONE sub-term at a time. `element_cat` names the category whose
    /// per-category task variant to use; `coll_type` selects the iteration shape
    /// (pass both to [`for_each_subterm`]).
    PerElement { element_cat: Ident, coll_type: CollectionType },
    /// Hand the container WHOLE to its own trait impl. Stack-safe only when the
    /// reason is [`WholeValueReason::ElementIsNotACategory`]; the other reason is
    /// the declared, measured residue described in the module header.
    WholeValue { reason: WholeValueReason },
}

/// Why a collection could not be walked element-wise. Both variants are proofs,
/// not excuses — see the module header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WholeValueReason {
    /// The container's `Hash`/`Eq`/`Ord` is defined by a canonical order or a
    /// commutative combine over its elements, so an element-wise walk on the
    /// driver's own `state` would write different (CONSENSUS-VISIBLE) bytes.
    UnorderedContainer,
    /// The element type is a Rust primitive, not a term category — there is no
    /// per-category task variant to push, and no sub-term to recurse into. This
    /// case is stack-safe.
    ElementIsNotACategory,
}

/// ★ **THE BOUNDARY.** `true` iff visiting `coll_type`'s elements in CONTAINER
/// ORDER reproduces its whole-value `Hash`/`PartialEq`/`Ord` semantics exactly.
///
/// Spelled ONCE, here, and consulted by every driver — the campaign's repeated
/// finding is that a law spelled in N copies drifts. See the table in the module
/// header for the per-container derivation.
pub(crate) fn is_order_faithful(coll_type: &CollectionType) -> bool {
    match coll_type {
        // `Hash for [T]`: `write_length_prefix(len)` then `hash_slice`, i.e. each
        // element in index order. `PartialEq`: length then element-wise.
        // `Ord`: lexicographic, elements first and length as the tiebreak.
        CollectionType::Vec => true,
        // `HashSetLit::hash` sorts by `T: Ord` before writing; `HashBag::hash`
        // and `HashMapLit::hash` build commutative lanes from per-element SUB-
        // hashers, so the elements never touch the caller's `state` at all.
        CollectionType::HashSet
        | CollectionType::HashBag
        | CollectionType::HashMap
        | CollectionType::PathMap => false,
    }
}

/// Does `cat` name a term category of `language` — i.e. is there a per-category
/// task variant (`CmpProc`, `HashProc`, …) that can be pushed for it?
///
/// ⚠ The direct question, deliberately: the generated task enums are built from
/// `language.types`, so membership of that list IS the existence of the variant.
/// A name-shaped heuristic would drift from the enum it is predicting.
pub(crate) fn names_a_category(cat: &Ident, language: &LanguageDef) -> bool {
    language.types.iter().any(|t| t.name == *cat)
}

/// Decide how one collection of sub-terms must be traversed.
///
/// `element_cat` / `coll_type` come from
/// [`VariantKind::CollectionLiteral`](super::subst::VariantKind::CollectionLiteral),
/// [`VariantKind::Collection`](super::subst::VariantKind::Collection) or a
/// [`FieldInfo`](super::subst::FieldInfo) — the three places a collection of
/// sub-terms can appear in a generated traversal.
pub(crate) fn plan_for(
    element_cat: &Ident,
    coll_type: &CollectionType,
    sensitivity: OrderSensitivity,
    language: &LanguageDef,
) -> CollectionPlan {
    if !names_a_category(element_cat, language) {
        return CollectionPlan::WholeValue {
            reason: WholeValueReason::ElementIsNotACategory,
        };
    }
    match sensitivity {
        OrderSensitivity::OrderAgnostic => CollectionPlan::PerElement {
            element_cat: element_cat.clone(),
            coll_type: coll_type.clone(),
        },
        OrderSensitivity::OrderSensitive if is_order_faithful(coll_type) => {
            CollectionPlan::PerElement {
                element_cat: element_cat.clone(),
                coll_type: coll_type.clone(),
            }
        },
        OrderSensitivity::OrderSensitive => CollectionPlan::WholeValue {
            reason: WholeValueReason::UnorderedContainer,
        },
    }
}

/// Emit a loop over every SUB-TERM position of `coll_expr`, invoking
/// `subterm(&expr)` once per position with an expression of type `&Elem`.
///
/// ## The per-container iteration shapes, in one place
///
/// | `coll_type` | `iter()` yields | sub-term positions per item |
/// |---|---|---|
/// | `Vec` | `&E` | the element |
/// | `HashSet` | `&E` | the element |
/// | `HashBag` | `(&E, usize)` | the element (the `usize` multiplicity is not a term) |
/// | `HashMap` | `(&K, &V)` | key, then value |
/// | `PathMap` | `(&K, &PathValue<V>)` | key, then the value IF `PathValue::Set` |
///
/// ★ `PathValue::Unset` contributes NO position. An unset pathmap entry is a
/// bare key (#74 / Ruling B: "unset ≠ Nil"), so there is no value sub-term to
/// visit, hash, compare or drop.
///
/// ## Order
///
/// With [`WalkOrder::ReverseForLifo`] the emitted loop yields the positions in
/// reverse, so a caller that pushes each onto a LIFO stack gets them back in
/// container order. For key/value containers that means *pairs in reverse, and
/// value before key within a pair* — the exact reverse of the flat position
/// sequence `k₀, v₀, k₁, v₁, …`.
///
/// ⚠ Only `Vec` has a `DoubleEndedIterator`. Reverse iteration over the other
/// shapes materialises the item refs into a `Vec` first; the allocation is
/// bounded by the container's own length and is only paid where a caller
/// genuinely needs LIFO order over an unordered container.
pub(crate) fn for_each_subterm(
    coll_type: &CollectionType,
    coll_expr: &TokenStream,
    order: WalkOrder,
    subterm: &dyn Fn(&TokenStream) -> TokenStream,
) -> TokenStream {
    let elem_body = subterm(&quote! { __walk_elem });
    let key_body = subterm(&quote! { __walk_key });
    let value_body = subterm(&quote! { __walk_value });

    match (coll_type, order) {
        // ── single-position shapes ──────────────────────────────────────────
        (CollectionType::Vec, WalkOrder::Forward) => quote! {
            for __walk_elem in #coll_expr.iter() {
                #elem_body
            }
        },
        (CollectionType::Vec, WalkOrder::ReverseForLifo) => quote! {
            for __walk_elem in #coll_expr.iter().rev() {
                #elem_body
            }
        },
        (CollectionType::HashSet, WalkOrder::Forward) => quote! {
            for __walk_elem in #coll_expr.iter() {
                #elem_body
            }
        },
        (CollectionType::HashSet, WalkOrder::ReverseForLifo) => quote! {
            {
                let __walk_items: Vec<_> = #coll_expr.iter().collect();
                for __walk_elem in __walk_items.into_iter().rev() {
                    #elem_body
                }
            }
        },
        // `HashBag::iter` yields `(&E, usize)`: the multiplicity is a count, not
        // a term, so it contributes no position.
        (CollectionType::HashBag, WalkOrder::Forward) => quote! {
            for (__walk_elem, _) in #coll_expr.iter() {
                #elem_body
            }
        },
        (CollectionType::HashBag, WalkOrder::ReverseForLifo) => quote! {
            {
                let __walk_items: Vec<_> = #coll_expr.iter().collect();
                for (__walk_elem, _) in __walk_items.into_iter().rev() {
                    #elem_body
                }
            }
        },
        // ── key/value shapes ────────────────────────────────────────────────
        (CollectionType::HashMap, WalkOrder::Forward) => quote! {
            for (__walk_key, __walk_value) in #coll_expr.iter() {
                #key_body
                #value_body
            }
        },
        (CollectionType::HashMap, WalkOrder::ReverseForLifo) => quote! {
            {
                let __walk_items: Vec<_> = #coll_expr.iter().collect();
                for (__walk_key, __walk_value) in __walk_items.into_iter().rev() {
                    #value_body
                    #key_body
                }
            }
        },
        (CollectionType::PathMap, WalkOrder::Forward) => quote! {
            for (__walk_key, __walk_path_value) in #coll_expr.iter() {
                #key_body
                if let mettail_runtime::PathValue::Set(__walk_value) = __walk_path_value {
                    #value_body
                }
            }
        },
        (CollectionType::PathMap, WalkOrder::ReverseForLifo) => quote! {
            {
                let __walk_items: Vec<_> = #coll_expr.iter().collect();
                for (__walk_key, __walk_path_value) in __walk_items.into_iter().rev() {
                    if let mettail_runtime::PathValue::Set(__walk_value) = __walk_path_value {
                        #value_body
                    }
                    #key_body
                }
            }
        },
    }
}

/// Emit a loop over the ZIPPED sub-term positions of two containers of the same
/// shape, invoking `subterm_pair(&left_expr, &right_expr)` once per position.
///
/// For the comparison traversals (`PartialEq`, `Ord`, `match_pattern`), which
/// walk two terms in lock-step rather than one.
///
/// ⚠ Only an [order-faithful](is_order_faithful) container admits a pairwise
/// walk at all: zipping two `HashSet` iterators pairs elements by *iteration
/// order*, which depends on insertion history and hash seeds, so it would report
/// two equal sets as unequal. Callers reach this function only through
/// [`CollectionPlan::PerElement`] with [`OrderSensitivity::OrderSensitive`],
/// which already implies `Vec`; any other shape emits a `compile_error!` so a
/// future change to [`is_order_faithful`] fails LOUDLY in the generated tree
/// rather than silently mis-comparing.
///
/// ⚠ It emits `compile_error!` rather than `panic!` deliberately: a `panic!` in a
/// proc macro does not unwind the `proc_macro` bridge under this workspace's
/// cranelift dev backend, and `rustc` aborts printing nothing at all.
pub(crate) fn for_each_subterm_pair(
    coll_type: &CollectionType,
    left_expr: &TokenStream,
    right_expr: &TokenStream,
    order: WalkOrder,
    subterm_pair: &dyn Fn(&TokenStream, &TokenStream) -> TokenStream,
) -> TokenStream {
    let body = subterm_pair(&quote! { __walk_left }, &quote! { __walk_right });
    match (coll_type, order) {
        (CollectionType::Vec, WalkOrder::Forward) => quote! {
            for (__walk_left, __walk_right) in #left_expr.iter().zip(#right_expr.iter()) {
                #body
            }
        },
        // `Zip<slice::Iter, slice::Iter>` is `DoubleEndedIterator` because both
        // halves are also `ExactSizeIterator`, so `.rev()` is a real reverse walk
        // over the COMMON prefix — which is exactly the lexicographic domain.
        (CollectionType::Vec, WalkOrder::ReverseForLifo) => quote! {
            for (__walk_left, __walk_right) in
                #left_expr.iter().zip(#right_expr.iter()).rev()
            {
                #body
            }
        },
        (other, _) => {
            let message = format!(
                "collection_walk::for_each_subterm_pair was asked for a PAIRWISE element walk \
                 over `{other:?}`, which is not order-faithful: zipping two of them pairs \
                 elements by iteration order, so two EQUAL containers could compare unequal. \
                 Either `is_order_faithful` changed without this function, or a caller reached \
                 here without going through `plan_for`."
            );
            quote! { compile_error!(#message); }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ★ The boundary is a CLOSED, EXHAUSTIVE statement about every container
    /// shape the AST admits — not a list that happens to cover today's grammars.
    /// A new `CollectionType` variant makes this test fail to compile, which is
    /// the point: its order-faithfulness has to be DERIVED and recorded.
    #[test]
    fn every_collection_type_declares_its_order_faithfulness() {
        for coll_type in [
            CollectionType::Vec,
            CollectionType::HashSet,
            CollectionType::HashBag,
            CollectionType::HashMap,
            CollectionType::PathMap,
        ] {
            let faithful = is_order_faithful(&coll_type);
            match coll_type {
                CollectionType::Vec => assert!(
                    faithful,
                    "`Vec` is the ORDERED container: `Hash for [T]` writes the length prefix \
                     then each element in index order, so an element-wise walk reproduces it \
                     exactly. If this ever reads false the conversion of every driver is void."
                ),
                CollectionType::HashSet
                | CollectionType::HashBag
                | CollectionType::HashMap
                | CollectionType::PathMap => assert!(
                    !faithful,
                    "{coll_type:?} defines its identity by a canonical order or a commutative \
                     combine over its elements (see the module header's table). Declaring it \
                     order-faithful would make the generated `Hash` write DIFFERENT, \
                     consensus-visible bytes."
                ),
            }
        }
    }

    /// `Drop` is exempt from the boundary and every other traversal is not.
    #[test]
    fn order_agnostic_traversals_may_walk_an_unordered_container() {
        let language = crate::gen::collection_literal_language_for_tests();
        let proc = quote::format_ident!("Proc");

        for coll_type in [
            CollectionType::HashSet,
            CollectionType::HashBag,
            CollectionType::HashMap,
            CollectionType::PathMap,
        ] {
            assert!(
                matches!(
                    plan_for(&proc, &coll_type, OrderSensitivity::OrderAgnostic, &language),
                    CollectionPlan::PerElement { .. }
                ),
                "{coll_type:?} must be walkable element-wise by an ORDER-AGNOSTIC traversal \
                 (`Drop`): destruction order is unobservable, so the boundary does not apply."
            );
            assert!(
                matches!(
                    plan_for(&proc, &coll_type, OrderSensitivity::OrderSensitive, &language),
                    CollectionPlan::WholeValue { reason: WholeValueReason::UnorderedContainer }
                ),
                "{coll_type:?} must NOT be walked element-wise by an ORDER-SENSITIVE traversal \
                 — that would change the bytes `Hash`/`Ord` produce."
            );
        }
    }

    /// The `![Vec<u8>]` trap: order-faithful, but `u8` has no task variant.
    #[test]
    fn a_primitive_element_is_never_walked_per_element() {
        let language = crate::gen::collection_literal_language_for_tests();
        let primitive = quote::format_ident!("u8");
        for sensitivity in [OrderSensitivity::OrderSensitive, OrderSensitivity::OrderAgnostic] {
            assert!(
                matches!(
                    plan_for(&primitive, &CollectionType::Vec, sensitivity, &language),
                    CollectionPlan::WholeValue {
                        reason: WholeValueReason::ElementIsNotACategory
                    }
                ),
                "`Vec<u8>` is order-faithful but `u8` is not a category: pushing a \
                 `…Task::…u8` would not compile. This is the `Bytes` carrier trap, measured \
                 2026-07-29 in the Display emitter."
            );
        }
    }

    /// The emitted loop must actually mention the caller's per-element body, and
    /// the reverse form must actually reverse. A helper that silently emitted an
    /// empty loop would make every converted driver vacuously "flat".
    #[test]
    fn the_emitted_walk_carries_the_callers_body_and_respects_order() {
        let coll = quote! { __c };
        let body = |e: &TokenStream| quote! { touch(#e); };

        // ⚠ `TokenStream::to_string` spaces punctuation apart (`. rev ()`), so the
        // needle must be matched against a whitespace-STRIPPED rendering. Matching
        // the literal `".rev()"` made this assertion read `false` for every shape
        // — which is how it was found: it went red on the very first run.
        let rendered = |t: TokenStream| -> String {
            t.to_string().chars().filter(|c| !c.is_whitespace()).collect()
        };

        for coll_type in [
            CollectionType::Vec,
            CollectionType::HashSet,
            CollectionType::HashBag,
            CollectionType::HashMap,
            CollectionType::PathMap,
        ] {
            for order in [WalkOrder::Forward, WalkOrder::ReverseForLifo] {
                let text = rendered(for_each_subterm(&coll_type, &coll, order, &body));
                assert!(
                    text.contains("touch"),
                    "{coll_type:?}/{order:?} dropped the caller's per-element body"
                );
                assert_eq!(
                    text.contains(".rev()"),
                    order == WalkOrder::ReverseForLifo,
                    "{coll_type:?}/{order:?}: `ReverseForLifo` must reverse and `Forward` \
                     must not — a LIFO driver that walks forward emits its work backwards"
                );
            }
        }

        // Key/value shapes visit TWO positions per item, so the body appears twice.
        for coll_type in [CollectionType::HashMap, CollectionType::PathMap] {
            let text = rendered(for_each_subterm(&coll_type, &coll, WalkOrder::Forward, &body));
            assert_eq!(
                text.matches("touch").count(),
                2,
                "{coll_type:?} has a KEY and a VALUE sub-term position; visiting only one \
                 leaves half the container untraversed"
            );
        }
    }
}
