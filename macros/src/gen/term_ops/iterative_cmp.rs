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
    field_carrier, for_each_subterm_pair, for_each_subterm_pair_with_loop, plan_for,
    CollectionPlan, FieldCarrier, OrderSensitivity, WalkOrder, WholeValueReason,
};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

#[derive(Clone, Copy, PartialEq, Eq)]
enum CmpInterpretation {
    Ordinary,
    CheckedExecution,
    InspectContributions,
}

/// Names shared by the comparison builders; ordinary emission is unchanged.
struct CmpEmissionNames {
    interpretation: CmpInterpretation,
    task_enum: Ident,
    task_pool: Ident,
    aux_task_pool: Ident,
    collection_resume: Ident,
    eq_driver: Ident,
    cmp_driver: Ident,
    deliver: Ident,
    unordered_eq: Ident,
    eq_handler_prefix: &'static str,
    cmp_handler_prefix: &'static str,
    resume_prefix: &'static str,
    native_resume_prefix: &'static str,
}

impl CmpEmissionNames {
    fn ordinary() -> Self {
        Self {
            interpretation: CmpInterpretation::Ordinary,
            task_enum: format_ident!("CmpTask"),
            task_pool: format_ident!("CMP_TASK_POOL"),
            aux_task_pool: format_ident!("CMP_AUX_TASK_POOL"),
            collection_resume: format_ident!("CollectionCmpResume"),
            eq_driver: format_ident!("eq_iterative"),
            cmp_driver: format_ident!("cmp_iterative"),
            deliver: format_ident!("cmp_deliver"),
            unordered_eq: format_ident!("eq_unordered_collection"),
            eq_handler_prefix: "eq_handle_",
            cmp_handler_prefix: "cmp_handle_",
            resume_prefix: "cmp_resume_collection_",
            native_resume_prefix: "cmp_resume_native_",
        }
    }

    fn eq_handler(&self, category: &Ident) -> Ident {
        format_ident!("{}{}", self.eq_handler_prefix, category.to_string().to_lowercase())
    }

    fn cmp_handler(&self, category: &Ident) -> Ident {
        format_ident!("{}{}", self.cmp_handler_prefix, category.to_string().to_lowercase())
    }

    fn resume(&self, category: &Ident) -> Ident {
        format_ident!("{}{}", self.resume_prefix, category.to_string().to_lowercase())
    }

    fn native_resume(&self, category: &Ident, label: &Ident) -> Ident {
        format_ident!(
            "{}{}_{}",
            self.native_resume_prefix,
            category.to_string().to_lowercase(),
            label.to_string().to_lowercase(),
        )
    }
}

// The checked path shares the ordinary builders and preserves native call sites.
impl CmpEmissionNames {
    fn checked() -> Self {
        Self {
            interpretation: CmpInterpretation::CheckedExecution,
            task_enum: format_ident!("CheckedCmpTask"),
            task_pool: format_ident!("CHECKED_CMP_TASK_POOL"),
            aux_task_pool: format_ident!("CHECKED_CMP_AUX_TASK_POOL"),
            collection_resume: format_ident!("CheckedCollectionCmpResume"),
            eq_driver: format_ident!("checked_eq_iterative"),
            cmp_driver: format_ident!("checked_cmp_iterative"),
            deliver: format_ident!("checked_cmp_deliver"),
            unordered_eq: format_ident!("checked_eq_unordered_collection"),
            eq_handler_prefix: "checked_eq_handle_",
            cmp_handler_prefix: "checked_cmp_handle_",
            resume_prefix: "checked_cmp_resume_collection_",
            native_resume_prefix: "checked_cmp_resume_native_",
        }
    }

    fn admitted(&self) -> bool {
        self.interpretation != CmpInterpretation::Ordinary
    }

    fn inspecting(&self) -> bool {
        self.interpretation == CmpInterpretation::InspectContributions
    }

    /// Private leaf-fragment interpretation. A complete generated comparison
    /// inspector must also cover drivers, child jobs, collections and owners.
    /// No whole-comparison entrypoint is exposed by these fragments.
    #[allow(dead_code)]
    fn inspect_contributions() -> Self {
        Self {
            interpretation: CmpInterpretation::InspectContributions,
            task_enum: format_ident!("InspectCmpContributionTask"),
            task_pool: format_ident!("INSPECT_CMP_CONTRIBUTION_TASK_POOL"),
            aux_task_pool: format_ident!("INSPECT_CMP_CONTRIBUTION_AUX_TASK_POOL"),
            collection_resume: format_ident!("InspectCmpContributionResume"),
            eq_driver: format_ident!("inspect_eq_contribution_worklist"),
            cmp_driver: format_ident!("inspect_cmp_contribution_worklist"),
            deliver: format_ident!("inspect_cmp_contribution_deliver"),
            unordered_eq: format_ident!("inspect_eq_contribution_unordered"),
            eq_handler_prefix: "inspect_eq_contribution_handle_",
            cmp_handler_prefix: "inspect_cmp_contribution_handle_",
            resume_prefix: "inspect_cmp_contribution_resume_",
            native_resume_prefix: "inspect_cmp_contribution_native_",
        }
    }

    fn generics(&self) -> TokenStream {
        if self.admitted() {
            quote! { <E> }
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

    fn resume_type(&self) -> TokenStream {
        let resume = &self.collection_resume;
        if self.admitted() {
            quote! { #resume<E> }
        } else {
            quote! { #resume }
        }
    }

    fn collection_owner_type(&self) -> TokenStream {
        if self.admitted() {
            quote! { mettail_runtime::CheckedCollectionCmpPda }
        } else {
            quote! { Box<mettail_runtime::CollectionCmpPda> }
        }
    }

    fn collection_owner(&self, machine: TokenStream) -> TokenStream {
        if self.admitted() {
            machine
        } else {
            quote! { Box::new(#machine) }
        }
    }

    fn collection_callback_parameters(&self) -> TokenStream {
        if self.admitted() {
            quote! { , reserve: &mut dyn FnMut(usize, usize) -> Result<(), E> }
        } else {
            TokenStream::new()
        }
    }

    fn collection_callback_begin(&self) -> TokenStream {
        if self.admitted() {
            quote! {
                reserve(1, 0).map_err(|error| mettail_runtime::NativeComparisonFailure::Admission(
                    mettail_runtime::BindingFailure::Reservation(error)))?;
                let mut __collection_reserve = |work, units| reserve(work, units);
                let reserve = &mut __collection_reserve;
            }
        } else {
            TokenStream::new()
        }
    }

    fn collection_step(&self) -> TokenStream {
        if self.admitted() {
            let route = self.routing();
            quote! {{
                let __collection_step = machine.try_resume(result, reserve)?;
                #route
                __collection_step
            }}
        } else {
            quote! { machine.resume(result) }
        }
    }

    fn collection_callback_result(&self, call: TokenStream) -> TokenStream {
        if self.admitted() {
            let route = self.routing();
            quote! {{
                let __collection_result = #call?;
                #route
                __collection_result
            }}
        } else {
            call
        }
    }

    // Leading commas retain ordinary signature punctuation exactly.
    fn parameters(&self) -> TokenStream {
        if self.admitted() {
            quote! { , reserve: &mut impl FnMut(usize, usize) -> Result<(), E> }
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

    fn result_type(&self, value: TokenStream) -> TokenStream {
        if self.admitted() {
            quote! { Result<#value, mettail_runtime::NativeComparisonFailure<E>> }
        } else {
            value
        }
    }

    fn success(&self, value: TokenStream) -> TokenStream {
        if self.admitted() {
            quote! { Ok(#value) }
        } else {
            value
        }
    }

    fn return_value(&self, value: TokenStream) -> TokenStream {
        let result = self.success(value);
        quote! { return #result; }
    }

    fn propagate(&self) -> TokenStream {
        if self.admitted() {
            quote! { ? }
        } else {
            TokenStream::new()
        }
    }

    fn reserve_work(&self, work: usize) -> TokenStream {
        if self.admitted() {
            quote! {
                mettail_runtime::reserve_binding_parts(#work, 0, 0, reserve)
                    .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            }
        } else {
            TokenStream::new()
        }
    }

    fn routing(&self) -> TokenStream {
        self.reserve_work(1)
    }

    // Root header/release or a borrowed task's construction/disposal.
    fn record_admission(&self) -> TokenStream {
        if self.admitted() {
            quote! {
                mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                    .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            }
        } else {
            TokenStream::new()
        }
    }

    fn push_task(&self, task: TokenStream) -> TokenStream {
        if self.admitted() {
            let admission = self.record_admission();
            quote! {{ #admission stack.push(#task); }}
        } else {
            quote! { stack.push(#task) }
        }
    }

    fn native_ne(&self, left: TokenStream, right: TokenStream) -> TokenStream {
        if self.admitted() {
            quote! {
                mettail_runtime::CheckedNativeEqualityLeaf::try_native_ne(#left, #right, reserve)?
            }
        } else {
            quote! { #left != #right }
        }
    }

    fn native_cmp(&self, left: TokenStream, right: TokenStream) -> TokenStream {
        if self.admitted() {
            quote! {
                mettail_runtime::CheckedNativeOrderingLeaf::try_native_cmp(#left, #right, reserve)?
            }
        } else {
            quote! { #left.cmp(#right) }
        }
    }

    /// A contribution to later native work, not permission to perform it.
    /// The accumulator separately charges its checked metadata arithmetic.
    fn inspect_contribution(&self, work: usize, records: usize) -> TokenStream {
        if self.inspecting() {
            quote! {
                state.try_accumulate_parts(#work, #records, 0, reserve)
                    .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            }
        } else {
            TokenStream::new()
        }
    }

    /// A source verdict occurrence has a lifecycle even when its value is not
    /// needed by metadata inspection. Preserve the original emitted push for
    /// execution, and count that occurrence without a comparison in inspection.
    fn push_verdict(&self, order: TokenStream) -> TokenStream {
        if self.inspecting() {
            self.inspect_contribution(4, 1)
        } else {
            let task_enum = &self.task_enum;
            self.push_task(quote! { #task_enum::Verdict(#order) })
        }
    }

    fn length_verdict(&self, left: TokenStream, right: TokenStream) -> TokenStream {
        if self.inspecting() {
            // The established LengthCmp group costs two units. Its
            // result is deferred by Ord, so it cannot prune the common prefix.
            let comparison = self.inspect_contribution(2, 0);
            let verdict = self.inspect_contribution(4, 1);
            quote! {{ #comparison #verdict }}
        } else {
            let order = self.usize_cmp(left, right);
            self.push_verdict(order)
        }
    }

    fn inspect_leaf_work(&self, call: TokenStream) -> TokenStream {
        quote! {{
            let __comparison_work = #call?;
            state.try_accumulate_parts(__comparison_work, 0, 0, reserve)
                .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
        }}
    }

    /// Interpret the WHOLE guard, not a fabricated inequality expression.
    /// GeneratedComparisonInspectionCover proves that retaining the unknown
    /// guard's continuation covers every actual result/refusal prefix.
    fn native_ne_guard(&self, left: TokenStream, right: TokenStream) -> TokenStream {
        if self.inspecting() {
            self.inspect_leaf_work(quote! {
                mettail_runtime::CheckedNativeEqualityLeaf::try_inspect_native_ne_work(
                    #left, #right, reserve)
            })
        } else {
            let different = self.native_ne(left, right);
            let return_false = self.return_value(quote! { false });
            quote! { if #different { #return_false } }
        }
    }

    fn native_cmp_guard(&self, left: TokenStream, right: TokenStream) -> TokenStream {
        if self.inspecting() {
            self.inspect_leaf_work(quote! {
                mettail_runtime::CheckedNativeOrderingLeaf::try_inspect_native_cmp_work(
                    #left, #right, reserve)
            })
        } else {
            let order = self.native_cmp(left, right);
            let return_order = self.return_value(quote! { ord });
            quote! {
                let ord = #order;
                if ord != std::cmp::Ordering::Equal { #return_order }
            }
        }
    }

    /// Deferred comparisons happen during source construction, not when their
    /// result is later popped. Inspection retains that call without pushing
    /// an invented Equal verdict or stopping construction on an unknown reply.
    fn native_cmp_verdict(&self, left: TokenStream, right: TokenStream) -> TokenStream {
        if self.inspecting() {
            let leaf = self.inspect_leaf_work(quote! {
                mettail_runtime::CheckedNativeOrderingLeaf::try_inspect_native_cmp_work(
                    #left, #right, reserve)
            });
            // GeneratedComparisonLocalControl counts every original task
            // occurrence, including verdicts inspected without their values.
            // Four work and one record cover its push, consultation/disposal;
            // no invented ordering is pushed to a comparison worklist.
            let verdict = self.inspect_contribution(4, 1);
            quote! {{ #leaf #verdict }}
        } else {
            let task_enum = &self.task_enum;
            let order = self.native_cmp(left, right);
            let push = self.push_task(quote! { #task_enum::Verdict(#order) });
            quote! { #push; }
        }
    }

    fn usize_ne(&self, left: TokenStream, right: TokenStream) -> TokenStream {
        if self.admitted() {
            let admission = self.reserve_work(2);
            quote! {{ #admission #left != #right }}
        } else {
            quote! { #left != #right }
        }
    }

    fn usize_cmp(&self, left: TokenStream, right: TokenStream) -> TokenStream {
        if self.admitted() {
            let admission = self.reserve_work(2);
            quote! {{ #admission #left.cmp(&#right) }}
        } else {
            quote! { #left.cmp(&#right) }
        }
    }

    fn pattern_order_precharge(
        &self,
        left: TokenStream,
        right: TokenStream,
        multi: bool,
    ) -> TokenStream {
        if !self.admitted() {
            return TokenStream::new();
        }
        let function = if multi {
            format_ident!("precharge_generated_multi_pattern_order")
        } else {
            format_ident!("precharge_generated_single_pattern_order")
        };
        quote! { mettail_runtime::#function(#left, #right, reserve)?; }
    }

    fn pattern_order(&self, left: TokenStream, right: TokenStream, multi: bool) -> TokenStream {
        if self.inspecting() {
            let function = if multi {
                format_ident!("inspect_generated_multi_pattern_order_work")
            } else {
                format_ident!("inspect_generated_single_pattern_order_work")
            };
            return self.inspect_leaf_work(quote! {
                mettail_runtime::#function(#left, #right, reserve)
            });
        }
        let precharge = self.pattern_order_precharge(left.clone(), right.clone(), multi);
        if multi {
            quote! {
                #precharge
                let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                    let mut h = std::collections::hash_map::DefaultHasher::new();
                    std::hash::Hash::hash(p, &mut h);
                    std::hash::Hasher::finish(&h)
                };
                // Length dominates, then the binder hashes element-wise — the exact
                // judgement the pre-#162 arm made with two early returns.
                let pat_ord = #left.len().cmp(&#right.len()).then_with(|| {
                    #left
                        .iter()
                        .zip(#right.iter())
                        .map(|(lp, rp)| hash_pat(lp).cmp(&hash_pat(rp)))
                        .find(|o| *o != std::cmp::Ordering::Equal)
                        .unwrap_or(std::cmp::Ordering::Equal)
                });
            }
        } else {
            quote! {
                #precharge
                // Pattern comparison: hash-based ordering, same as `Scope::cmp`.
                let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                    let mut h = std::collections::hash_map::DefaultHasher::new();
                    std::hash::Hash::hash(p, &mut h);
                    std::hash::Hasher::finish(&h)
                };
                let pat_ord = hash_pat(#left).cmp(&hash_pat(#right));
            }
        }
    }

    fn pair_loop(&self, iterator: &TokenStream, body: &TokenStream) -> TokenStream {
        if self.admitted() {
            let setup = self.routing();
            let advance = self.routing();
            quote! {{
                #setup
                let mut __cmp_walk = #iterator;
                loop {
                    #advance
                    let Some((__walk_left, __walk_right)) = __cmp_walk.next() else { break };
                    #body
                }
            }}
        } else {
            quote! { for (__walk_left, __walk_right) in #iterator { #body } }
        }
    }

    fn for_each_pair(
        &self,
        coll_type: &CollectionType,
        left: &TokenStream,
        right: &TokenStream,
        order: WalkOrder,
        body: &dyn Fn(&TokenStream, &TokenStream) -> TokenStream,
    ) -> TokenStream {
        if self.admitted() {
            for_each_subterm_pair_with_loop(
                coll_type,
                left,
                right,
                order,
                body,
                &|iterator, body| self.pair_loop(iterator, body),
            )
        } else {
            for_each_subterm_pair(coll_type, left, right, order, body)
        }
    }

    fn unsupported_return(&self, category: &Ident, constructor: &Ident) -> TokenStream {
        if !self.admitted() {
            return TokenStream::new();
        }
        let category = category.to_string();
        let constructor = constructor.to_string();
        quote! {
            return Err(mettail_runtime::NativeComparisonFailure::UnsupportedConstructor {
                category: #category, constructor: #constructor,
            });
        }
    }

    fn support_handler(&self, category: &Ident) -> Ident {
        format_ident!("{}_support", self.cmp_handler(category))
    }

    fn operand_support(&self, category: &Ident) -> TokenStream {
        if !self.admitted() {
            return TokenStream::new();
        }
        let support = self.support_handler(category);
        let category_name = category.to_string();
        let routing = self.routing();
        quote! {
            #routing
            if let Some(constructor) = #support(unsafe { &*left_ptr }) {
                return Err(mettail_runtime::NativeComparisonFailure::UnsupportedConstructor {
                    category: #category_name, constructor,
                });
            }
            #routing
            if let Some(constructor) = #support(unsafe { &*right_ptr }) {
                return Err(mettail_runtime::NativeComparisonFailure::UnsupportedConstructor {
                    category: #category_name, constructor,
                });
            }
        }
    }

    fn pop_loop(&self, body: TokenStream) -> TokenStream {
        if self.admitted() {
            let routing = self.routing();
            quote! {
                loop {
                    #routing
                    let Some(task) = stack.pop() else { break; };
                    #routing
                    #body
                }
            }
        } else {
            quote! { while let Some(task) = stack.pop() { #body } }
        }
    }
}

fn checked_cmp_collection_supported(
    category: &Ident,
    kind: &CollectionType,
    language: &LanguageDef,
) -> bool {
    match plan_for(category, kind, OrderSensitivity::OrderSensitive, language) {
        CollectionPlan::PerElement { coll_type: CollectionType::Vec, .. } => true,
        CollectionPlan::WholeValue {
            reason: WholeValueReason::UnorderedContainer,
        } => {
            matches!(kind, CollectionType::HashMap | CollectionType::HashBag)
        },
        _ => false,
    }
}

fn checked_cmp_fields_supported(fields: &[FieldInfo], language: &LanguageDef) -> bool {
    fields.iter().all(|field| match field_carrier(field) {
        FieldCarrier::Leaf => {
            !field.is_predicate
                && !field.is_optional
                && matches!(
                    field.opaque_leaf,
                    Some(crate::gen::term_ops::subst::OpaqueLeafKind::TokenText)
                        | Some(crate::gen::term_ops::subst::OpaqueLeafKind::GuestBody)
                )
        },
        FieldCarrier::Child | FieldCarrier::OptionalChild => {
            language.types.iter().any(|ty| ty.name == field.category)
        },
        FieldCarrier::Collection { coll_type } | FieldCarrier::OptionalCollection { coll_type } => {
            checked_cmp_collection_supported(&field.category, &coll_type, language)
        },
    })
}

fn checked_cmp_variant_supported(
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
                )
            }),
        VariantKind::Regular { fields, .. } => checked_cmp_fields_supported(fields, language),
        VariantKind::Binder { pre_scope_fields, .. }
        | VariantKind::MultiBinder { pre_scope_fields, .. } => {
            checked_cmp_fields_supported(pre_scope_fields, language)
        },
        VariantKind::Collection { element_cat, coll_type, .. }
        | VariantKind::CollectionLiteral { element_cat, coll_type, .. } => {
            checked_cmp_collection_supported(element_cat, coll_type, language)
        },
        VariantKind::RecursiveNativeLiteral { .. } => false,
    }
}

fn generate_cmp_support_fns(language: &LanguageDef, emission: &CmpEmissionNames) -> TokenStream {
    if !emission.admitted() {
        return TokenStream::new();
    }
    let functions = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
            let function = emission.support_handler(category);
            let arms = collect_category_variants(category, language)
                .into_iter()
                .map(|variant| {
                    let pattern = variant_wildcard_pattern(category, &variant);
                    let unsupported = if checked_cmp_variant_supported(category, &variant, language)
                    {
                        quote! { None }
                    } else {
                        let constructor = variant.label().to_string();
                        quote! { Some(#constructor) }
                    };
                    quote! { #pattern => #unsupported }
                })
                .collect::<Vec<_>>();
            quote! {
                #[inline]
                #[allow(dead_code)]
                fn #function(value: &#category) -> Option<&'static str> {
                    match value { #(#arms,)* }
                }
            }
        })
        .collect::<Vec<_>>();
    quote! { #(#functions)* }
}

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
    emission: &CmpEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let unordered_eq = &emission.unordered_eq;
    let return_false = emission.return_value(quote! { false });
    match plan_for(element_cat, coll_type, OrderSensitivity::OrderSensitive, language) {
        CollectionPlan::PerElement { element_cat, coll_type } => {
            let task_variant = format_ident!("Cmp{}", element_cat);
            let pushes = emission.for_each_pair(
                &coll_type,
                left_expr,
                right_expr,
                WalkOrder::Forward,
                &|l, r| {
                    let push = emission.push_task(quote! {
                        #task_enum::#task_variant(#l as *const _, #r as *const _)
                    });
                    quote! { #push; }
                },
            );
            let lengths_differ =
                emission.usize_ne(quote! { #left_expr.len() }, quote! { #right_expr.len() });
            quote! {
                // `Vec::eq` is `len` first, then element-wise — reproduced exactly.
                if #lengths_differ {
                    #return_false
                }
                #pushes
            }
        },
        CollectionPlan::WholeValue {
            reason: WholeValueReason::UnorderedContainer,
        } => {
            let resume_fn = emission.resume(element_cat);
            let machine =
                unordered_collection_cmp_machine_expr(coll_type, left_expr, right_expr, emission);
            let arguments = emission.arguments();
            let propagate = emission.propagate();
            quote! {
                if !#unordered_eq(#machine, #resume_fn #arguments) #propagate {
                    #return_false
                }
            }
        },
        CollectionPlan::WholeValue {
            reason: WholeValueReason::ElementIsNotACategory,
        } => emission.native_ne_guard(left_expr.clone(), right_expr.clone()),
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
    emission: &CmpEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    match plan_for(element_cat, coll_type, OrderSensitivity::OrderSensitive, language) {
        CollectionPlan::PerElement { element_cat, coll_type } => {
            let task_variant = format_ident!("Cmp{}", element_cat);
            let pushes = emission.for_each_pair(
                &coll_type,
                left_expr,
                right_expr,
                WalkOrder::ReverseForLifo,
                &|l, r| {
                    let push = emission.push_task(quote! {
                        #task_enum::#task_variant(#l as *const _, #r as *const _)
                    });
                    quote! { #push; }
                },
            );
            let push_length =
                emission.length_verdict(quote! { #left_expr.len() }, quote! { #right_expr.len() });
            quote! {
                // Pushed first ⇒ popped LAST ⇒ the length is the tiebreak, which
                // is what lexicographic order means.
                #push_length;
                #pushes
            }
        },
        CollectionPlan::WholeValue {
            reason: WholeValueReason::UnorderedContainer,
        } => unordered_collection_cmp_push_stmts(
            element_cat,
            coll_type,
            left_expr,
            right_expr,
            emission,
        ),
        CollectionPlan::WholeValue {
            reason: WholeValueReason::ElementIsNotACategory,
        } => emission.native_cmp_verdict(left_expr.clone(), right_expr.clone()),
    }
}

fn unordered_collection_cmp_push_stmts(
    element_cat: &Ident,
    coll_type: &CollectionType,
    left_expr: &TokenStream,
    right_expr: &TokenStream,
    emission: &CmpEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let resume_fn = emission.resume(element_cat);
    let machine = unordered_collection_cmp_machine_expr(coll_type, left_expr, right_expr, emission);
    let owner = emission.collection_owner(machine);
    let push = emission.push_task(quote! {
        #task_enum::StartCollection(#owner, #resume_fn,)
    });
    quote! { #push; }
}

/// Build the one canonical-order comparison machine shared by `Eq` and `Ord`.
/// Keeping this expression in one generator function prevents the two traits
/// from drifting on mode order, multiplicities, or key/value pairing.
fn unordered_collection_cmp_machine_expr(
    coll_type: &CollectionType,
    left_expr: &TokenStream,
    right_expr: &TokenStream,
    emission: &CmpEmissionNames,
) -> TokenStream {
    if emission.admitted() {
        return match coll_type {
            CollectionType::HashMap => quote! {{
                let __cmp_left = (#left_expr).try_comparison_roster(reserve)?;
                let __cmp_right = (#right_expr).try_comparison_roster(reserve)?;
                mettail_runtime::CheckedCollectionCmpPda::try_new(
                    std::cmp::Ordering::Equal, __cmp_left, __cmp_right, reserve)?
            }},
            CollectionType::HashBag => {
                let lead =
                    emission.usize_cmp(quote! { #left_expr.len() }, quote! { #right_expr.len() });
                quote! {{
                    let __cmp_lead = #lead;
                    let __cmp_left = (#left_expr).try_comparison_roster(reserve)?;
                    let __cmp_right = (#right_expr).try_comparison_roster(reserve)?;
                    mettail_runtime::CheckedCollectionCmpPda::try_new(
                        __cmp_lead, __cmp_left, __cmp_right, reserve)?
                }}
            },
            _ => {
                quote! { compile_error!("checked comparison source roster is unavailable for this collection") }
            },
        };
    }
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

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate `CmpTask` enum, TLS pool, variant_index functions, iterative engines,
/// and `impl PartialEq/Eq/PartialOrd/Ord` for all exported categories.
pub fn generate_iterative_cmp(language: &LanguageDef) -> TokenStream {
    let emission = CmpEmissionNames::ordinary();
    let cmp_task_enum = generate_cmp_task_enum(language, &emission);
    let variant_index_fns = generate_variant_index_fns(language);
    let eq_engine = generate_eq_engine(language, &emission);
    let cmp_engine = generate_cmp_engine(language, &emission);
    let trait_impls = generate_trait_impls(language, &emission);

    quote! {
        #cmp_task_enum
        #variant_index_fns
        #eq_engine
        #cmp_engine
        #trait_impls
    }
}

/// Generate the checked companion using the same classifiers and arm builders.
/// Ordinary comparison generation supplies the shared variant-index functions.
#[allow(dead_code)]
pub fn generate_checked_iterative_cmp(language: &LanguageDef) -> TokenStream {
    let emission = CmpEmissionNames::checked();
    let tasks = generate_cmp_task_enum(language, &emission);
    let support = generate_cmp_support_fns(language, &emission);
    let equality = generate_eq_engine(language, &emission);
    let ordering = generate_cmp_engine(language, &emission);
    let interfaces = language.types.iter().map(|ty| {
        let category = &ty.name;
        let task = format_ident!("Cmp{}", category);
        let task_enum = &emission.task_enum;
        let eq_driver = &emission.eq_driver;
        let cmp_driver = &emission.cmp_driver;
        let root = emission.record_admission();
        let push = emission.push_task(quote! { #task_enum::#task(self as *const _, other as *const _) });
        quote! {
            impl mettail_runtime::CheckedIterativeComparison for #category {
                fn try_eq_iterative<E>(
                    &self, other: &Self,
                    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
                ) -> Result<bool, mettail_runtime::NativeComparisonFailure<E>> {
                    if !mettail_runtime::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
                        return Err(mettail_runtime::NativeComparisonFailure::UnsupportedProfile);
                    }
                    #root
                    let mut stack = Vec::new();
                    #push;
                    #eq_driver(&mut stack, reserve)
                }
                fn try_cmp_iterative<E>(
                    &self, other: &Self,
                    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
                ) -> Result<std::cmp::Ordering, mettail_runtime::NativeComparisonFailure<E>> {
                    if !mettail_runtime::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
                        return Err(mettail_runtime::NativeComparisonFailure::UnsupportedProfile);
                    }
                    #root
                    let mut stack = Vec::new();
                    #push;
                    #cmp_driver(&mut stack, reserve)
                }
            }
        }
    }).collect::<Vec<_>>();
    quote! { #tasks #support #equality #ordering #(#interfaces)* }
}

// =============================================================================
// CmpTask Enum + TLS Pool
// =============================================================================

/// Generate the `CmpTask` enum and thread-local pool.
///
/// `CmpTask` has one variant per category holding raw pointer pairs:
/// `CmpInt(*const Int, *const Int)`, `CmpProc(*const Proc, *const Proc)`, etc.
fn generate_cmp_task_enum(language: &LanguageDef, emission: &CmpEmissionNames) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task_pool = &emission.task_pool;
    let aux_task_pool = &emission.aux_task_pool;
    let collection_resume = &emission.collection_resume;
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
    if emission.admitted() {
        return quote! {
            type #collection_resume<E> = fn(
                &mut Vec<#task_enum<E>>,
                mettail_runtime::CheckedCollectionCmpPda,
                Option<std::cmp::Ordering>,
                &mut dyn FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<Option<std::cmp::Ordering>, mettail_runtime::NativeComparisonFailure<E>>;

            #[allow(dead_code)]
            enum #task_enum<E> {
                #(#variants,)*
                ResumeCollection(mettail_runtime::CheckedCollectionCmpPda, #collection_resume<E>),
                StartCollection(mettail_runtime::CheckedCollectionCmpPda, #collection_resume<E>),
                Verdict(std::cmp::Ordering),
            }
        };
    }
    quote! {
        type #collection_resume = fn(
            &mut Vec<#task_enum>,
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
        enum #task_enum {
            #(#variants,)*
            /// Resume a suspended collection PDA after its requested typed
            /// comparison has completed.  Carrying the continuation function
            /// avoids one generated task variant per category and supports
            /// heterogeneous key/value carriers without type erasure.
            ResumeCollection(
                Box<mettail_runtime::CollectionCmpPda>,
                #collection_resume,
            ),
            /// Begin a canonical-order comparison at its exact lexicographic
            /// position. Deferring the first `resume(None)` call is essential:
            /// a mode or multiplicity verdict computed while an arm is being
            /// pushed would otherwise outrank earlier fields.
            StartCollection(
                Box<mettail_runtime::CollectionCmpPda>,
                #collection_resume,
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
        unsafe impl Send for #task_enum {}
        unsafe impl Sync for #task_enum {}

        thread_local! {
            /// Pool for reusing `CmpTask` work stacks across comparison calls.
            ///
            /// The `Cell<Vec<CmpTask>>` pattern allows zero-allocation
            /// steady-state operation: the first comparison allocates and later
            /// comparisons reuse the same buffer. Category-bearing collections
            /// remain inside the generated drivers rather than re-entering the
            /// public trait implementations.
            static #task_pool: std::cell::Cell<Vec<#task_enum>> =
                std::cell::Cell::new(Vec::new());

            /// Reusable work stack for the canonical-order PDA used by equality
            /// at unordered collection boundaries. It is distinct from
            /// `CMP_TASK_POOL` because the outer equality traversal still owns
            /// that stack while an individual collection is being compared.
            static #aux_task_pool: std::cell::Cell<Vec<#task_enum>> =
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
fn generate_eq_engine(language: &LanguageDef, emission: &CmpEmissionNames) -> TokenStream {
    assert!(
        !emission.inspecting(),
        "leaf contributions do not provide a complete Eq inspector"
    );
    let task_enum = &emission.task_enum;
    let task_type = emission.task_type();
    let aux_task_pool = &emission.aux_task_pool;
    let collection_resume = &emission.collection_resume;
    let eq_driver = &emission.eq_driver;
    let cmp_driver = &emission.cmp_driver;
    let unordered_eq = &emission.unordered_eq;
    let generics = emission.generics();
    let parameters = emission.parameters();
    let arguments = emission.arguments();
    let propagate = emission.propagate();
    let result_type = emission.result_type(quote! { bool });
    let return_false = emission.return_value(quote! { false });
    let success = emission.success(quote! { true });
    // Per-cat helper functions: each handles one CmpTask::Cmp{Cat}.
    // Returns `Some(false)` to short-circuit (mismatch), `Some(true)` to
    // continue (equal so far for this pair), `None` if there's nothing to
    // do. We use `bool` directly via early return — caller must propagate.
    let helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| generate_eq_category_handler(&t.name, language, emission))
        .collect();

    let task_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cmp_variant = format_ident!("Cmp{}", cat);
            let helper_fn = emission.eq_handler(cat);
            quote! {
                #task_enum::#cmp_variant(left_ptr, right_ptr) => {
                    if !#helper_fn(stack, left_ptr, right_ptr #arguments) #propagate {
                        #return_false
                    }
                }
            }
        })
        .collect();
    let unordered_helper = if emission.admitted() {
        let resume_type = emission.resume_type();
        let header = emission.record_admission();
        let push = emission.push_task(quote! { #task_enum::StartCollection(machine, resume) });
        let final_route = emission.routing();
        quote! {
            #[inline]
            #[allow(dead_code)]
            fn #unordered_eq #generics(
                machine: mettail_runtime::CheckedCollectionCmpPda,
                resume: #resume_type #parameters,
            ) -> #result_type {
                #header
                let mut __collection_stack = Vec::new();
                let stack = &mut __collection_stack;
                #push;
                let ordering = #cmp_driver(stack, reserve)?;
                #final_route
                Ok(ordering == std::cmp::Ordering::Equal)
            }
        }
    } else {
        quote! {
            /// Decide equality of one unordered collection by driving the same
            /// canonical-order PDA used by `Ord`. The category-specific resume
            /// function converts the PDA's erased pointers back to the correct
            /// generated category before scheduling `CmpTask` work.
            #[inline]
            #[allow(dead_code)]
            fn #unordered_eq(
                machine: mettail_runtime::CollectionCmpPda,
                resume: #collection_resume,
            ) -> bool {
                #[inline]
                fn drive(
                    stack: &mut Vec<#task_enum>,
                    machine: mettail_runtime::CollectionCmpPda,
                    resume: #collection_resume,
                ) -> bool {
                    stack.push(#task_enum::StartCollection(Box::new(machine), resume));
                    #cmp_driver(stack) == std::cmp::Ordering::Equal
                }

                let mut machine = Some(machine);
                let tls_result = #aux_task_pool.try_with(|cell| {
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

        }
    };
    let collection_arms = if emission.admitted() {
        quote! {
            #task_enum::ResumeCollection(_, _) => {
                return Err(mettail_runtime::NativeComparisonFailure::InvalidCollectionInput(
                    "collection ordering continuation reached equality engine"));
            }
            #task_enum::StartCollection(_, _) => {
                return Err(mettail_runtime::NativeComparisonFailure::InvalidCollectionInput(
                    "collection ordering start reached equality engine"));
            }
        }
    } else {
        quote! {
            #task_enum::ResumeCollection(_, _) => {
                unreachable!("collection ordering continuation reached equality engine");
            }
            #task_enum::StartCollection(_, _) => {
                unreachable!("collection ordering start reached equality engine");
            }
        }
    };
    let driver_loop = emission.pop_loop(quote! {
        match task {
            #(#task_arms)*
            #collection_arms
            // ★ #162 — a precomputed leaf verdict. `PartialEq` only asks
            // whether every position agrees, so any non-`Equal` verdict
            // is a mismatch regardless of direction.
            #task_enum::Verdict(ord) => {
                if ord != std::cmp::Ordering::Equal {
                    #return_false
                }
            }
        }
    });
    quote! {
        #unordered_helper
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
        fn #eq_driver #generics(stack: &mut Vec<#task_type> #parameters) -> #result_type {
            #driver_loop
            #success
        }
    }
}

/// The one category-handler recipe used by the equality engine. Keep this
/// separate from driver assembly so additional interpretations can reuse the
/// original variant classification, pointer/shape gates and field builders.
fn generate_eq_category_handler(
    cat: &Ident,
    language: &LanguageDef,
    emission: &CmpEmissionNames,
) -> TokenStream {
    assert!(
        !emission.inspecting(),
        "leaf contributions do not provide a complete Eq inspector"
    );
    let task_type = emission.task_type();
    let generics = emission.generics();
    let parameters = emission.parameters();
    let result_type = emission.result_type(quote! { bool });
    let return_true = emission.return_value(quote! { true });
    let return_false = emission.return_value(quote! { false });
    let success = emission.success(quote! { true });
    let routing = emission.routing();
    let indices = emission.reserve_work(2);
    let cat_str = cat.to_string().to_lowercase();
    let helper_fn = emission.eq_handler(cat);
    let index_fn = format_ident!("variant_index_{}", cat_str);
    let variants = collect_category_variants(cat, language);
    let variant_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_eq_variant_arm(cat, v, language, emission))
        .collect();
    let mismatch_arm = if variants.len() == 1 {
        TokenStream::new()
    } else {
        quote! { _ => { #return_false } }
    };
    let support = emission.operand_support(cat);
    let unequal = emission.usize_ne(quote! { #index_fn(left) }, quote! { #index_fn(right) });
    quote! {
        /// Returns `false` on mismatch (caller should propagate),
        /// `true` if matched so far (caller should continue draining stack).
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn #helper_fn #generics(
            stack: &mut Vec<#task_type>,
            left_ptr: *const #cat,
            right_ptr: *const #cat #parameters,
        ) -> #result_type {
            // Shared immutable subterms are definitionally equal. This
            // check occurs before dereference and before scheduling
            // descendants, making the common Arc-shared chain edge
            // constant-time without changing the exact fallback for
            // separately allocated values.
            #support
            #routing
            if std::ptr::eq(left_ptr, right_ptr) {
                #return_true
            }
            let left = unsafe { &*left_ptr };
            let right = unsafe { &*right_ptr };
            #indices
            if #unequal {
                #return_false
            }
            #routing
            match (left, right) {
                #(#variant_arms)*
                #mismatch_arm
            }
            #success
        }
    }
}

/// Generate match arms for a specific variant in the equality engine.
fn generate_eq_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
    emission: &CmpEmissionNames,
) -> TokenStream {
    if emission.admitted() && !checked_cmp_variant_supported(category, variant, language) {
        let pattern = variant_wildcard_pattern(category, variant);
        let refusal = emission.unsupported_return(category, variant.label());
        return quote! { (#pattern, #pattern) => { #refusal } };
    }
    let unordered_eq = &emission.unordered_eq;
    let routing = emission.routing();
    let native_guard = emission.native_ne_guard(quote! { a }, quote! { b });
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
                    #routing
                    #native_guard
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
                emission,
            );
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #routing
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
            let resume = emission.native_resume(category, label);
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    if #left_focus != #right_focus {
                        return false;
                    }
                    if !#unordered_eq(#machine, #resume) {
                        return false;
                    }
                }
            }
        },

        VariantKind::Var { label } => {
            // Var: compare OrdVar payloads directly
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #routing
                    #native_guard
                }
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_eq_regular_arm(category, label, fields, language, emission)
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
                emission,
            );
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #routing
                    #stmts
                }
            }
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_eq_binder_arm(category, label, pre_scope_fields, body_cat, language, emission)
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_eq_multi_binder_arm(
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
    emission: &CmpEmissionNames,
) -> Vec<TokenStream> {
    let task_enum = &emission.task_enum;
    let routing = emission.routing();
    let false_value = emission.success(quote! { false });
    let mut stmts: Vec<TokenStream> = Vec::with_capacity(fields.len() + 1);

    for (i, field) in fields.iter().enumerate() {
        let lname = &left_names[i];
        let rname = &right_names[i];

        let statement = match field_carrier(field) {
            // Phase 3A-B2: a predicate field uses direct `PartialEq` —
            // `BehavioralPred` derives `Eq`, so the bare value comparison is sound.
            // L9-3/L9-4: a token-text (`String`) or guest-body (`Arc<FltNode>`)
            // capture is the identical direct-Eq with no `CmpTask` descent. All
            // three are also correct under an `Option`, because `Option<T>: PartialEq`
            // whenever `T` is — which is why the carrier absorbs optionality.
            FieldCarrier::Leaf => emission.native_ne_guard(quote! { #lname }, quote! { #rname }),

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
                    emission,
                );
                quote! {
                    match (#lname.as_ref(), #rname.as_ref()) {
                        (None, None) => {},
                        (Some(__left_collection), Some(__right_collection)) => {
                            #inner
                        },
                        _ => return #false_value,
                    }
                }
            },

            // Opt-Group: equality on `Option<Box<Cat>>`. Push a `CmpTask` when both
            // are `Some`; a `Some`/`None` mismatch short-circuits to `false`.
            FieldCarrier::OptionalChild => {
                let task_variant = format_ident!("Cmp{}", field.category);
                let push = emission.push_task(quote! {
                    #task_enum::#task_variant(
                        __l.as_ref() as *const _,
                        __r.as_ref() as *const _,
                    )
                });
                quote! {
                    match (#lname.as_ref(), #rname.as_ref()) {
                        (None, None) => {}
                        (Some(__l), Some(__r)) => {
                            #push;
                        }
                        _ => return #false_value,
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
                emission,
            ),

            // A `Box<Cat>` category child: the descent, as a task.
            FieldCarrier::Child => {
                let task_variant = format_ident!("Cmp{}", field.category);
                let push = emission.push_task(quote! {
                    #task_enum::#task_variant(&**#lname as *const _, &**#rname as *const _)
                });
                quote! { #push; }
            },
        };
        stmts.push(quote! { #routing #statement });
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
    emission: &CmpEmissionNames,
) -> TokenStream {
    let left_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("r{}", i)).collect();
    let compare_stmts = eq_arm_stmts(fields, &left_names, &right_names, None, language, emission);

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
    emission: &CmpEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let total_fields = pre_scope_fields.len() + 1; // pre-scope fields + scope
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];

    // Compare scope: compare pattern directly, push body comparison task
    let body_task = format_ident!("Cmp{}", body_cat);
    let routing = emission.routing();
    let native_guard = emission.native_ne_guard(quote! { l_pat }, quote! { r_pat });
    let push_body = emission.push_task(quote! { #task_enum::#body_task(l_body, r_body) });
    let scope_stmts = quote! {
        {
            #routing
            let l_pat = &#scope_left.inner().unsafe_pattern;
            let r_pat = &#scope_right.inner().unsafe_pattern;
            #native_guard
            let l_body: *const #body_cat = &*#scope_left.inner().unsafe_body;
            let r_body: *const #body_cat = &*#scope_right.inner().unsafe_body;
            #push_body;
        }
    };

    // ★ #197 — the pre-scope fields go through the SHARED builder. This loop used
    // to be a hand-copy that tested `is_predicate` and `is_collection` and nothing
    // else, so three of the five carriers were emitted as the wrong shape.
    let compare_stmts = eq_arm_stmts(
        pre_scope_fields,
        &left_names,
        &right_names,
        Some(scope_stmts),
        language,
        emission,
    );

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
    emission: &CmpEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let total_fields = pre_scope_fields.len() + 1;
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];

    let body_task = format_ident!("Cmp{}", body_cat);
    let routing = emission.routing();
    let native_guard = emission.native_ne_guard(quote! { l_pat }, quote! { r_pat });
    let push_body = emission.push_task(quote! { #task_enum::#body_task(l_body, r_body) });
    let scope_stmts = quote! {
        {
            #routing
            let l_pat = &#scope_left.inner().unsafe_pattern;
            let r_pat = &#scope_right.inner().unsafe_pattern;
            #native_guard
            let l_body: *const #body_cat = &*#scope_left.inner().unsafe_body;
            let r_body: *const #body_cat = &*#scope_right.inner().unsafe_body;
            #push_body;
        }
    };

    // ★ #197 — the SHARED builder. This is the arm that went RED: `class3opt`'s
    // `PInputsOptTagged . ns:Vec(Name), *opt(qs:Vec(Proc)), ^[xs].p:[Name* -> Proc]`
    // puts an `Option<Vec<Proc>>` in a MultiBinder pre-scope slot, and the hand-copy
    // this replaces had no `OptionalCollection` case.
    let compare_stmts = eq_arm_stmts(
        pre_scope_fields,
        &left_names,
        &right_names,
        Some(scope_stmts),
        language,
        emission,
    );

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
fn generate_cmp_engine(language: &LanguageDef, emission: &CmpEmissionNames) -> TokenStream {
    assert!(
        !emission.inspecting(),
        "leaf contributions do not provide a complete Ord inspector"
    );
    let task_enum = &emission.task_enum;
    let task_type = emission.task_type();
    let cmp_driver = &emission.cmp_driver;
    let deliver = &emission.deliver;
    let generics = emission.generics();
    let parameters = emission.parameters();
    let arguments = emission.arguments();
    let propagate = emission.propagate();
    let result_type = emission.result_type(quote! { std::cmp::Ordering });
    let deliver_type = emission.result_type(quote! { Option<std::cmp::Ordering> });
    let return_root = emission.return_value(quote! { root_ordering });
    let success = emission.success(quote! { std::cmp::Ordering::Equal });
    let routing = emission.routing();
    let collection_resume_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cmp_variant = format_ident!("Cmp{}", cat);
            let resume_fn = emission.resume(cat);
            let owner_type = emission.collection_owner_type();
            let owner_binding = if emission.admitted() {
                quote! { machine }
            } else {
                quote! { mut machine }
            };
            let callback_parameters = emission.collection_callback_parameters();
            let begin = emission.collection_callback_begin();
            let step = emission.collection_step();
            let step_type = if emission.admitted() {
                quote! { mettail_runtime::CheckedCollectionCmpStep }
            } else {
                quote! { mettail_runtime::CollectionCmpStep }
            };
            let owner_field = if emission.admitted() {
                quote! { machine, }
            } else {
                TokenStream::new()
            };
            let push_resume = emission.push_task(quote! {
                #task_enum::ResumeCollection(machine, #resume_fn)
            });
            let push_child = emission.push_task(quote! {
                #task_enum::#cmp_variant(left.cast::<#cat>(), right.cast::<#cat>(),)
            });
            let none = emission.success(quote! { None });
            let done = emission.success(quote! { Some(ordering) });
            quote! {
                #[inline]
                fn #resume_fn #generics(
                    stack: &mut Vec<#task_type>,
                    #owner_binding: #owner_type,
                    result: Option<std::cmp::Ordering> #callback_parameters,
                ) -> #deliver_type {
                    #begin
                    match #step {
                        #step_type::Compare { #owner_field left, right, .. } => {
                            #push_resume;
                            #push_child;
                            #none
                        },
                        #step_type::Done(ordering) => #done,
                    }
                }
            }
        })
        .collect();

    let native_collection_resume_fns: Vec<TokenStream> = language
        .types
        .iter()
        .filter(|_| !emission.admitted())
        .flat_map(|t| {
            let category = &t.name;
            collect_category_variants(category, language)
                .into_iter()
                .filter_map(move |variant| match variant {
                    VariantKind::RecursiveNativeLiteral { label, carrier } => {
                        let resume_fn = emission.native_resume(category, &label);
                        let key_variant = format_ident!("Cmp{}", carrier.key_category());
                        let value_variant = format_ident!("Cmp{}", carrier.value_category());
                        Some(quote! {
                            #[inline]
                            fn #resume_fn(
                                stack: &mut Vec<#task_enum>,
                                mut machine: Box<mettail_runtime::CollectionCmpPda>,
                                result: Option<std::cmp::Ordering>,
                            ) -> Option<std::cmp::Ordering> {
                                match machine.resume(result) {
                                    mettail_runtime::CollectionCmpStep::Compare {
                                        role,
                                        left,
                                        right,
                                    } => {
                                        stack.push(#task_enum::ResumeCollection(machine, #resume_fn));
                                        match role {
                                            mettail_runtime::CollectionCmpRole::Primary => {
                                                stack.push(#task_enum::#key_variant(
                                                    left.cast(),
                                                    right.cast(),
                                                ));
                                            },
                                            mettail_runtime::CollectionCmpRole::Secondary => {
                                                stack.push(#task_enum::#value_variant(
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
        .map(|t| generate_cmp_category_handler(&t.name, language, emission))
        .collect();

    let task_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cmp_variant = format_ident!("Cmp{}", cat);
            let helper_fn = emission.cmp_handler(cat);
            quote! {
                #task_enum::#cmp_variant(left_ptr, right_ptr) => {
                    let ord = #helper_fn(stack, left_ptr, right_ptr #arguments) #propagate;
                    if ord != std::cmp::Ordering::Equal {
                        if let Some(root_ordering) = #deliver(stack, ord #arguments) #propagate {
                            #return_root
                        }
                    }
                }
            }
        })
        .collect();

    let deliver_resume = emission.collection_callback_result(quote! {
        resume(stack, machine, Some(ordering) #arguments)
    });
    let deliver_none = emission.success(quote! { None });
    let deliver_some = emission.success(quote! { Some(ordering) });
    let delivery_loop = emission.pop_loop(quote! {
        match task {
            #task_enum::ResumeCollection(machine, resume) => {
                match #deliver_resume {
                    None => return #deliver_none,
                    Some(std::cmp::Ordering::Equal) => return #deliver_none,
                    Some(next) => {
                        ordering = next;
                        resumed = true;
                        break;
                    },
                }
            },
            _ => {},
        }
    });
    let delivery_body = quote! {
        loop {
            #routing
            let mut resumed = false;
            #delivery_loop
            if !resumed {
                return #deliver_some;
            }
        }
    };
    let start_result = emission.collection_callback_result(quote! {
        resume(stack, machine, None #arguments)
    });
    let resume_result = emission.collection_callback_result(quote! {
        resume(stack, machine, Some(std::cmp::Ordering::Equal) #arguments,)
    });
    let collection_arms = quote! {
            #task_enum::StartCollection(machine, resume) => {
                if let Some(ordering) = #start_result {
                    if ordering != std::cmp::Ordering::Equal {
                        if let Some(root_ordering) = #deliver(stack, ordering #arguments) #propagate {
                            #return_root
                        }
                    }
                }
            }
            #task_enum::ResumeCollection(machine, resume) => {
                if let Some(ordering) = #resume_result {
                    if ordering != std::cmp::Ordering::Equal {
                        if let Some(root_ordering) = #deliver(stack, ordering #arguments) #propagate {
                            #return_root
                        }
                    }
                }
            }
    };
    let driver_loop = emission.pop_loop(quote! {
        match task {
            #(#task_arms)*
            #collection_arms
            // ★ #162 — a precomputed leaf verdict. Because tasks are
            // pushed in REVERSE position order, popping them yields
            // strict left-to-right (lexicographic) semantics: the FIRST
            // non-`Equal` verdict decides, exactly as `derive(Ord)` does.
            #task_enum::Verdict(ord) => {
                if ord != std::cmp::Ordering::Equal {
                    if let Some(root_ordering) = #deliver(stack, ord #arguments) #propagate {
                        #return_root
                    }
                }
            }
        }
    });
    quote! {
        #(#collection_resume_fns)*
        #(#native_collection_resume_fns)*
        #(#helper_fns)*

        #[allow(dead_code, unused_variables)]
        fn #deliver #generics(
            stack: &mut Vec<#task_type>,
            mut ordering: std::cmp::Ordering #parameters,
        ) -> #deliver_type {
            #delivery_body
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
        fn #cmp_driver #generics(stack: &mut Vec<#task_type> #parameters) -> #result_type {
            #driver_loop
            #success
        }
    }
}

fn generate_cmp_category_handler(
    cat: &Ident,
    language: &LanguageDef,
    emission: &CmpEmissionNames,
) -> TokenStream {
    assert!(
        !emission.inspecting(),
        "leaf contributions do not provide a complete Ord inspector"
    );
    let task_type = emission.task_type();
    let generics = emission.generics();
    let parameters = emission.parameters();
    let result_type = emission.result_type(quote! { std::cmp::Ordering });
    let success = emission.success(quote! { std::cmp::Ordering::Equal });
    let routing = emission.routing();
    let indices = emission.reserve_work(2);
    let cat_str = cat.to_string().to_lowercase();
    let helper_fn = emission.cmp_handler(cat);
    let index_fn = format_ident!("variant_index_{}", cat_str);
    let variants = collect_category_variants(cat, language);
    let variant_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_cmp_variant_arm(cat, v, language, emission))
        .collect();
    let support = emission.operand_support(cat);
    let unequal = emission.usize_ne(quote! { l_idx }, quote! { r_idx });
    let index_order = emission.usize_cmp(quote! { l_idx }, quote! { r_idx });
    let return_index = emission.return_value(index_order);
    let mismatch_arm = if variants.len() == 1 {
        TokenStream::new()
    } else {
        quote! {
            _ => {
                #return_index
            }
        }
    };
    quote! {
        /// Returns `Ordering::Equal` to keep draining the stack;
        /// any other ordering means "stop and propagate up".
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn #helper_fn #generics(
            stack: &mut Vec<#task_type>,
            left_ptr: *const #cat,
            right_ptr: *const #cat #parameters,
        ) -> #result_type {
            #support
            let left = unsafe { &*left_ptr };
            let right = unsafe { &*right_ptr };
            #indices
            let l_idx = #index_fn(left);
            let r_idx = #index_fn(right);
            if #unequal {
                #return_index
            }
            #routing
            match (left, right) {
                #(#variant_arms)*
                #mismatch_arm
            }
            #success
        }
    }
}

/// Generate match arms for a specific variant in the ordering engine.
fn generate_cmp_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
    emission: &CmpEmissionNames,
) -> TokenStream {
    if emission.admitted() && !checked_cmp_variant_supported(category, variant, language) {
        let pattern = variant_wildcard_pattern(category, variant);
        let refusal = emission.unsupported_return(category, variant.label());
        return quote! { (#pattern, #pattern) => { #refusal } };
    }
    let task_enum = &emission.task_enum;
    let routing = emission.routing();
    let native_guard = emission.native_cmp_guard(quote! { a }, quote! { b });
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
                    #routing
                    #native_guard
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
                emission,
            );
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #routing
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
            let resume = emission.native_resume(category, label);
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    stack.push(#task_enum::Verdict((#left_focus).cmp(#right_focus)));
                    stack.push(#task_enum::StartCollection(
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
                    #routing
                    #native_guard
                }
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_cmp_regular_arm(category, label, fields, language, emission)
        },

        // ★ #162 — the category-DIRECT collection field, `Ord` side.
        VariantKind::Collection { label, element_cat, coll_type } => {
            let pushes = cmp_collection_push_stmts(
                element_cat,
                coll_type,
                &quote! { a },
                &quote! { b },
                language,
                emission,
            );
            quote! {
                (#category::#label(a), #category::#label(b)) => {
                    #routing
                    #pushes
                }
            }
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_cmp_binder_arm(category, label, pre_scope_fields, body_cat, language, emission)
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_cmp_multi_binder_arm(
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
    emission: &CmpEmissionNames,
) -> Vec<TokenStream> {
    let task_enum = &emission.task_enum;
    let routing = emission.routing();
    let push_less = emission.push_verdict(quote! { std::cmp::Ordering::Less });
    let push_greater = emission.push_verdict(quote! { std::cmp::Ordering::Greater });
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
        let native_guard = emission.native_cmp_guard(quote! { #lname }, quote! { #rname });
        stmts.push(quote! {
            {
                #routing
                #native_guard
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
        let statement = match field_carrier(field) {
            // A leaf inside the pushed segment: its verdict is computed now and
            // consulted in position order. This is the case the eager prefix
            // could not express, and the reason it had to swallow collections.
            FieldCarrier::Leaf => emission.native_cmp_verdict(quote! { #lname }, quote! { #rname }),

            // `Option<Container>: Ord` uses `None < Some`; `Some`/`Some` then
            // schedules the inner container without a host-stack re-entry.
            FieldCarrier::OptionalCollection { coll_type } => {
                let inner = cmp_collection_push_stmts(
                    &field.category,
                    &coll_type,
                    &quote! { __left_collection },
                    &quote! { __right_collection },
                    language,
                    emission,
                );
                quote! {
                    match (#lname.as_ref(), #rname.as_ref()) {
                        (None, None) => {},
                        (None, Some(_)) => {
                            #push_less;
                        },
                        (Some(_), None) => {
                            #push_greater;
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
                let push = emission.push_task(quote! {
                    #task_enum::#task_variant(
                        __l.as_ref() as *const _,
                        __r.as_ref() as *const _,
                    )
                });
                quote! {
                    match (#lname.as_ref(), #rname.as_ref()) {
                        (None, None) => {}
                        (None, Some(_)) => {
                            #push_less;
                        }
                        (Some(_), None) => {
                            #push_greater;
                        }
                        (Some(__l), Some(__r)) => {
                            #push;
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
                emission,
            ),

            // ★ A boxed category child. Before #162 a child at a position BEFORE the
            // last collection was compared by an eager `(**l).cmp(&**r)` — a
            // whole-value re-entry — purely because the eager prefix had to reach the
            // collection. Now every child is a task.
            FieldCarrier::Child => {
                let task_variant = format_ident!("Cmp{}", field.category);
                let push = emission.push_task(quote! {
                    #task_enum::#task_variant(&**#lname as *const _, &**#rname as *const _)
                });
                quote! { #push; }
            },
        };
        stmts.push(quote! { #routing #statement });
    }

    stmts
}

fn generate_cmp_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    language: &LanguageDef,
    emission: &CmpEmissionNames,
) -> TokenStream {
    let left_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("r{}", i)).collect();
    let stmts = cmp_arm_stmts(fields, &left_names, &right_names, None, language, emission);

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
    emission: &CmpEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let total_fields = pre_scope_fields.len() + 1;
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];
    let body_task = format_ident!("Cmp{}", body_cat);
    let routing = emission.routing();
    let pattern_order = emission.pattern_order(
        quote! { &l_scope.unsafe_pattern },
        quote! { &r_scope.unsafe_pattern },
        false,
    );
    let push_body = emission.push_task(quote! { #task_enum::#body_task(l_body, r_body) });
    let push_pattern = emission.push_verdict(quote! { pat_ord });

    // Pop order within the group must be pattern-then-body, so the pushes are
    // body-then-pattern. Unchanged from the pre-#162 arm in WHAT it compares —
    // only the body descent's ordering relative to the pre-scope fields moves,
    // and it moves to the position the field order says it should have.
    let scope_pushes = quote! {
        {
            #routing
            let l_scope = #scope_left.inner();
            let r_scope = #scope_right.inner();
            #pattern_order
            let l_body: *const #body_cat = &*l_scope.unsafe_body;
            let r_body: *const #body_cat = &*r_scope.unsafe_body;
            #push_body;
            #push_pattern;
        }
    };

    let stmts = cmp_arm_stmts(
        pre_scope_fields,
        &left_names,
        &right_names,
        Some(scope_pushes),
        language,
        emission,
    );

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
    emission: &CmpEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let total_fields = pre_scope_fields.len() + 1;
    let left_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("l{}", i)).collect();
    let right_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("r{}", i)).collect();

    let scope_left = &left_names[total_fields - 1];
    let scope_right = &right_names[total_fields - 1];
    let body_task = format_ident!("Cmp{}", body_cat);
    let routing = emission.routing();
    let pattern_order = emission.pattern_order(quote! { l_pats }, quote! { r_pats }, true);
    let push_body = emission.push_task(quote! { #task_enum::#body_task(l_body, r_body) });
    let push_pattern = emission.push_verdict(quote! { pat_ord });

    let scope_pushes = quote! {
        {
            #routing
            let l_scope = #scope_left.inner();
            let r_scope = #scope_right.inner();
            let l_pats = &l_scope.unsafe_pattern;
            let r_pats = &r_scope.unsafe_pattern;
            #pattern_order
            let l_body: *const #body_cat = &*l_scope.unsafe_body;
            let r_body: *const #body_cat = &*r_scope.unsafe_body;
            #push_body;
            #push_pattern;
        }
    };

    let stmts = cmp_arm_stmts(
        pre_scope_fields,
        &left_names,
        &right_names,
        Some(scope_pushes),
        language,
        emission,
    );

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
fn generate_trait_impls(language: &LanguageDef, emission: &CmpEmissionNames) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_category_trait_impls(&lang_type.name, emission))
        .collect();

    quote! { #(#impls)* }
}

/// Generate all four comparison trait impls for a single category.
fn generate_category_trait_impls(category: &Ident, emission: &CmpEmissionNames) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task_pool = &emission.task_pool;
    let eq_driver = &emission.eq_driver;
    let cmp_driver = &emission.cmp_driver;
    let cmp_variant = format_ident!("Cmp{}", category);

    quote! {
        impl PartialEq for #category {
            fn eq(&self, other: &Self) -> bool {
                // Fast path: try TLS pool
                let tls_result = #task_pool.try_with(|cell| {
                    let mut stack = cell.take();
                    let was_empty = stack.is_empty();

                    // Push initial comparison task
                    stack.push(#task_enum::#cmp_variant(
                        self as *const _,
                        other as *const _,
                    ));

                    // Run the iterative engine
                    let result = #eq_driver(&mut stack);

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
                let mut stack = vec![#task_enum::#cmp_variant(
                    self as *const _,
                    other as *const _,
                )];
                #eq_driver(&mut stack)
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
                let tls_result = #task_pool.try_with(|cell| {
                    let mut stack = cell.take();
                    let was_empty = stack.is_empty();

                    // Push initial comparison task
                    stack.push(#task_enum::#cmp_variant(
                        self as *const _,
                        other as *const _,
                    ));

                    // Run the iterative engine
                    let result = #cmp_driver(&mut stack);

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
                let mut stack = vec![#task_enum::#cmp_variant(
                    self as *const _,
                    other as *const _,
                )];
                #cmp_driver(&mut stack)
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
#[path = "iterative_cmp_tests.rs"]
mod ordinary_baseline_tests;

#[cfg(test)]
#[path = "iterative_cmp_checked_tests.rs"]
mod checked_tests;

#[cfg(test)]
#[path = "iterative_cmp_inspection_tests.rs"]
mod inspection_tests;

#[cfg(test)]
#[path = "iterative_cmp_pattern_inspection_tests.rs"]
mod pattern_inspection_tests;

#[cfg(test)]
#[path = "iterative_cmp_census_tests.rs"]
mod census_tests;

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
                let eq = rendered(eq_arm_stmts(
                    &fields,
                    &left,
                    &right,
                    scope.clone(),
                    &language,
                    &CmpEmissionNames::ordinary(),
                ));
                let cmp = rendered(cmp_arm_stmts(
                    &fields,
                    &left,
                    &right,
                    scope.clone(),
                    &language,
                    &CmpEmissionNames::ordinary(),
                ));
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

        let cmp = rendered(cmp_arm_stmts(
            &fields,
            &left,
            &right,
            None,
            &language,
            &CmpEmissionNames::ordinary(),
        ));
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

        let eq = rendered(eq_arm_stmts(
            &fields,
            &left,
            &right,
            None,
            &language,
            &CmpEmissionNames::ordinary(),
        ));
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
            let machine = compact(unordered_collection_cmp_machine_expr(
                &coll_type,
                &left,
                &right,
                &CmpEmissionNames::ordinary(),
            ));
            let eq = compact(eq_collection_stmts(
                &proc,
                &coll_type,
                &left,
                &right,
                &language,
                &CmpEmissionNames::ordinary(),
            ));
            let ord = compact(cmp_collection_push_stmts(
                &proc,
                &coll_type,
                &left,
                &right,
                &language,
                &CmpEmissionNames::ordinary(),
            ));

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
            (
                "eq",
                eq_arm_stmts(
                    &fields,
                    &left,
                    &right,
                    Some(scope.clone()),
                    &language,
                    &CmpEmissionNames::ordinary(),
                ),
            ),
            (
                "cmp",
                cmp_arm_stmts(
                    &fields,
                    &left,
                    &right,
                    Some(scope.clone()),
                    &language,
                    &CmpEmissionNames::ordinary(),
                ),
            ),
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
        let helper = generated_function_body(
            generate_eq_engine(&language, &CmpEmissionNames::ordinary()),
            "eq_handle_meta",
        );
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
            (generate_eq_engine(&language, &CmpEmissionNames::ordinary()), "eq_handle_meta"),
            (generate_cmp_engine(&language, &CmpEmissionNames::ordinary()), "cmp_handle_meta"),
        ] {
            let singleton = generated_function_body(engine, function);
            assert!(
                !singleton.contains("_ =>"),
                "single-constructor comparison must not retain an unreachable fallback"
            );
        }
    }
}
