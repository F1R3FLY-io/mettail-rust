//! Stack-safe `Clone` generation for MeTTaIL term enums.
//!
//! Recursive enum fields are `Arc<Cat>`, so their ordinary clone is shallow and
//! already stack-safe. Collection fields are different: they own their element
//! terms, and a derived container clone recursively invokes `Cat::clone` once
//! per nesting level. This emitter preserves the shallow `Arc` behavior while
//! cloning owned collection elements through one explicit pushdown automaton.
//!
//! The source tree remains borrowed for the entire traversal. Assemble tasks
//! therefore retain only a source pointer, a destination slot, and the start
//! slot of each collection. Container mode, multiplicity, insertion order, and
//! non-collection fields are read from the immutable source at assembly time.

use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{BTreeMap, BTreeSet};
use syn::Ident;

use crate::gen::native_carrier::NativeRecursiveCarrier;

#[derive(Clone, Copy)]
enum CollectionSurface {
    Direct,
    Literal,
}

struct CheckedEmissionContext {
    dummy_indices: BTreeMap<String, usize>,
    supported_literals: BTreeSet<(String, String)>,
}

struct CloneEmissionNames {
    checked: Option<CheckedEmissionContext>,
    task_enum: Ident,
    task_pool: Ident,
    result_pool: Ident,
    driver: Ident,
    handler_prefix: &'static str,
}

impl CloneEmissionNames {
    fn ordinary() -> Self {
        Self {
            checked: None,
            task_enum: format_ident!("CloneTask"),
            task_pool: format_ident!("CLONE_TASK_POOL"),
            result_pool: format_ident!("CLONE_RESULT_POOL"),
            driver: format_ident!("clone_iterative"),
            handler_prefix: "clone_handle_",
        }
    }

    // Unsupported shapes and native payloads are explicit checked refusals.
    // This generation context does not activate a public parser entrypoint.
    #[allow(dead_code)]
    fn checked(
        language: &LanguageDef,
        receipts: &super::dummy_receipts::DummyReceiptEmission,
    ) -> Self {
        let mut supported_literals = BTreeSet::new();
        for ty in &language.types {
            for variant in collect_category_variants(&ty.name, language) {
                if let VariantKind::Literal { label } = variant {
                    if super::checked_native::literal_supported(
                        &ty.name,
                        &label,
                        language,
                        super::checked_native::LeafCapability::Binding,
                    ) {
                        supported_literals.insert((ty.name.to_string(), label.to_string()));
                    }
                }
            }
        }
        Self {
            checked: Some(CheckedEmissionContext {
                dummy_indices: receipts.indices.clone(),
                supported_literals,
            }),
            task_enum: format_ident!("CheckedBindingTask"),
            task_pool: format_ident!("CHECKED_BINDING_TASK_POOL"),
            result_pool: format_ident!("CHECKED_BINDING_RESULT_POOL"),
            driver: format_ident!("copy_binding_iterative"),
            handler_prefix: "binding_handle_",
        }
    }

    #[allow(dead_code)]
    fn dummy_charge(&self, category: &Ident) -> Result<TokenStream, syn::Error> {
        let index = self
            .checked
            .as_ref()
            .and_then(|context| context.dummy_indices.get(&category.to_string()))
            .ok_or_else(|| {
                syn::Error::new(
                    category.span(),
                    "checked binding requires the category's selected dummy receipt",
                )
            })?;
        Ok(quote! { dummy_charges[#index] })
    }

    fn base_admission(&self) -> TokenStream {
        if self.checked.is_some() {
            // ConstructCategory plus the independently rooted normal-cleanup
            // base. Owned children and field-local effects are separate.
            quote! { mettail_runtime::reserve_binding_parts(6, 2, 0, reserve)?; }
        } else {
            TokenStream::new()
        }
    }

    fn publish(&self, category: &Ident, value: TokenStream) -> TokenStream {
        let wrap = format_ident!("Wrap{}", category);
        if self.checked.is_some() {
            quote! {
                mettail_runtime::write_binding_slot(
                    results, slot, AnyClonedTerm::#wrap(#value),
                    |value| matches!(value, AnyClonedTerm::#wrap(_)), reserve,
                )?;
            }
        } else {
            quote! { results[slot] = Some(AnyClonedTerm::#wrap(#value)); }
        }
    }

    fn handler(&self, category: &Ident) -> Ident {
        format_ident!("{}{}", self.handler_prefix, category.to_string().to_lowercase())
    }

    fn task_type(&self) -> TokenStream {
        let task_enum = &self.task_enum;
        if self.checked.is_some() {
            quote! { (#task_enum, moniker::ScopeState) }
        } else {
            quote! { #task_enum }
        }
    }

    fn push_task(&self, task: TokenStream, state: TokenStream) -> TokenStream {
        if self.checked.is_some() {
            quote! {
                mettail_runtime::reserve_binding_parts(1, 1, 0, reserve)?;
                stack.push((#task, #state));
            }
        } else {
            quote! { stack.push(#task); }
        }
    }

    fn function_generics(&self) -> TokenStream {
        if self.checked.is_some() {
            quote! { <E, F: FnMut(usize, usize) -> Result<(), E>> }
        } else {
            TokenStream::new()
        }
    }

    // Insert after the existing final parameter's comma.
    fn binding_parameters(&self) -> TokenStream {
        if self.checked.is_some() {
            quote! {
                operation: mettail_runtime::BindingOperation<'_>,
                reserve: &mut F,
                dummy_charges: &[mettail_runtime::binding_receipt::BindingCharge],
            }
        } else {
            TokenStream::new()
        }
    }

    fn result_type(&self) -> TokenStream {
        if self.checked.is_some() {
            quote! { -> Result<(), mettail_runtime::BindingFailure<E>> }
        } else {
            TokenStream::new()
        }
    }

    fn success_tail(&self) -> TokenStream {
        if self.checked.is_some() {
            quote! { Ok(()) }
        } else {
            TokenStream::new()
        }
    }

    // Leading comma preserves ordinary calls without adding a trailing comma.
    fn binding_arguments(&self) -> TokenStream {
        if self.checked.is_some() {
            quote! { , operation, reserve, dummy_charges }
        } else {
            TokenStream::new()
        }
    }

    fn propagate(&self) -> TokenStream {
        if self.checked.is_some() {
            quote! { ? }
        } else {
            TokenStream::new()
        }
    }
}

pub fn generate_iterative_clone(language: &LanguageDef) -> TokenStream {
    let emission = CloneEmissionNames::ordinary();
    let values = generate_value_enum(language);
    let tasks = generate_task_enum(language, &emission);
    let engine = generate_engine(language, &emission);
    let impls = generate_impls(language, &emission);

    quote! {
        #values
        #tasks
        #engine
        #impls
    }
}

/// Add the checked interpretation beside the existing private Clone/Cmp/Hash
/// definitions. The ordinary wrapper enum and variant-index functions remain
/// the only authorities; no ordinary operation is replaced by this interface.
pub fn generate_checked_iterative_binding(
    language: &LanguageDef,
) -> Result<TokenStream, syn::Error> {
    let plan = super::iterative_drop::select_dummy_plan(language);
    if !super::dummy_receipts::selected_defaults_supported(language, &plan) {
        let implementations = language.types.iter().map(|ty| {
            let category = &ty.name;
            quote! {
                impl mettail_runtime::CheckedIterativeBinding for #category {
                    fn try_copy_iterative<E>(
                        &self,
                        _operation: mettail_runtime::BindingOperation<'_>,
                        _reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
                    ) -> Result<Self, mettail_runtime::BindingFailure<E>> {
                        Err(mettail_runtime::BindingFailure::UnsupportedProfile)
                    }
                }
            }
        });
        return Ok(quote! { #(#implementations)* });
    }
    let receipts = super::dummy_receipts::generate_dummy_receipts(language, &plan)?;
    let emission = CloneEmissionNames::checked(language, &receipts);
    let tasks = generate_task_enum(language, &emission);
    let engine = generate_engine(language, &emission);
    let implementations = generate_impls(language, &emission);
    let inspection = super::iterative_hash::generate_hash_contribution_inspection(language);
    let admission = super::hashbag_rebuild_admission::generate_hashbag_rebuild_admission(language);
    let table = receipts.tokens;
    Ok(quote! { #table #tasks #engine #implementations #inspection #admission })
}

fn generate_value_enum(language: &LanguageDef) -> TokenStream {
    let variants = language.types.iter().map(|ty| {
        let category = &ty.name;
        let wrap = format_ident!("Wrap{}", category);
        quote! { #wrap(#category) }
    });

    quote! {
        #[allow(dead_code)]
        enum AnyClonedTerm {
            #(#variants),*
        }
    }
}

fn generate_task_enum(language: &LanguageDef, emission: &CloneEmissionNames) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task_type = emission.task_type();
    let task_pool = &emission.task_pool;
    let result_pool = &emission.result_pool;
    let visits = language.types.iter().map(|ty| {
        let category = &ty.name;
        let visit = format_ident!("Clone{}", category);
        quote! { #visit { src: *const #category, slot: usize } }
    });

    let mut assemblies = Vec::new();
    for ty in &language.types {
        let category = &ty.name;
        for variant in collect_category_variants(category, language) {
            if let Some(task) = generate_assemble_task(category, &variant, emission) {
                assemblies.push(task);
            }
        }
    }

    quote! {
        #[allow(dead_code, non_camel_case_types)]
        enum #task_enum {
            #(#visits,)*
            #(#assemblies,)*
        }

        thread_local! {
            static #task_pool: std::cell::Cell<Vec<#task_type>> =
                const { std::cell::Cell::new(Vec::new()) };
            static #result_pool: std::cell::Cell<Vec<Option<AnyClonedTerm>>> =
                const { std::cell::Cell::new(Vec::new()) };
        }
    }
}

fn checked_scalar_fields(fields: &[FieldInfo], emission: &CloneEmissionNames) -> bool {
    emission.checked.is_some()
        && fields
            .iter()
            .all(|field| !field.is_collection || required_checked_collection_field(field))
}

fn required_vec_field(field: &FieldInfo) -> bool {
    field.is_collection
        && !field.is_optional
        && matches!(field.coll_type.as_ref(), None | Some(CollectionType::Vec))
}

fn required_bag_field(field: &FieldInfo) -> bool {
    field.is_collection
        && !field.is_optional
        && matches!(field.coll_type.as_ref(), Some(CollectionType::HashBag))
}

fn required_checked_collection_field(field: &FieldInfo) -> bool {
    required_vec_field(field) || required_bag_field(field)
}

// Direct and literal Vec/Bag payloads share the checked owned-field path.
// RequiredVecBindingReservation covers vector shells; RequiredHashBagBindingReservation
// supplies Bag reconstruction and ownership laws. Keep this adaptation local:
// the shared classifier and primitive literals retain their existing meaning
// for every other generated operation.
fn checked_collection_payload<'a>(
    variant: &'a VariantKind,
    emission: &CloneEmissionNames,
) -> Option<(&'a Ident, [FieldInfo; 1])> {
    emission.checked.as_ref()?;
    match variant {
        VariantKind::Collection {
            label,
            element_cat,
            coll_type: coll_type @ (CollectionType::Vec | CollectionType::HashBag),
        }
        | VariantKind::CollectionLiteral {
            label,
            element_cat,
            coll_type: coll_type @ (CollectionType::Vec | CollectionType::HashBag),
        } => Some((
            label,
            [FieldInfo {
                category: element_cat.clone(),
                is_collection: true,
                coll_type: Some(coll_type.clone()),
                is_predicate: false,
                is_optional: false,
                opaque_leaf: None,
            }],
        )),
        _ => None,
    }
}

fn inline_binding_leaf(field: &FieldInfo) -> bool {
    field.is_predicate || field.is_opaque_leaf()
}

#[derive(Clone, Copy)]
struct CheckedScopeField<'a> {
    body_category: &'a Ident,
    multiple: bool,
}

fn checked_scope_fields<'a>(
    variant: &'a VariantKind,
    emission: &CloneEmissionNames,
) -> Option<(&'a Ident, &'a [FieldInfo], CheckedScopeField<'a>)> {
    emission.checked.as_ref()?;
    let (label, fields, body_category, multiple) = match variant {
        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            (label, pre_scope_fields.as_slice(), body_cat, false)
        },
        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            (label, pre_scope_fields.as_slice(), body_cat, true)
        },
        _ => return None,
    };
    // Match the existing Binder/MultiBinder Drop arms, not Regular's broader
    // field support. Collection prefields need their own checked assembly.
    let eligible = fields.iter().all(|field| {
        required_checked_collection_field(field)
            || (!field.is_collection
                && (field.is_predicate || (!field.is_opaque_leaf() && !field.is_optional)))
    });
    eligible.then_some((label, fields, CheckedScopeField { body_category, multiple }))
}

// One eligibility decision controls all three builders. An unimplemented
// checked shape must never instantiate an ordinary, unmetered fallback arm.
fn checked_constructor_supported(
    category: &Ident,
    variant: &VariantKind,
    emission: &CloneEmissionNames,
) -> bool {
    if emission.checked.is_none() {
        return true;
    }
    match variant {
        // Preserve the existing compile-time diagnostic, not a runtime escape.
        VariantKind::Refused { .. } | VariantKind::Nullary { .. } | VariantKind::Var { .. } => true,
        VariantKind::Literal { label } => emission.checked.as_ref().is_some_and(|context| {
            context
                .supported_literals
                .contains(&(category.to_string(), label.to_string()))
        }),
        VariantKind::Regular { fields, .. } => checked_scalar_fields(fields, emission),
        VariantKind::Binder { .. } | VariantKind::MultiBinder { .. } => {
            checked_scope_fields(variant, emission).is_some()
        },
        VariantKind::Collection { .. } | VariantKind::CollectionLiteral { .. } => {
            checked_collection_payload(variant, emission).is_some()
        },
        VariantKind::RecursiveNativeLiteral { .. } => false,
    }
}

fn generate_assemble_task(
    category: &Ident,
    variant: &VariantKind,
    emission: &CloneEmissionNames,
) -> Option<TokenStream> {
    if !checked_constructor_supported(category, variant, emission) {
        return None;
    }
    if let Some((label, fields)) = checked_collection_payload(variant, emission) {
        let task = format_ident!("Assemble{}_{}", category, label);
        let slots = scalar_slot_fields(&fields);
        return Some(quote! { #task { src: *const #category, slot: usize, #(#slots),* } });
    }
    if let Some((label, fields, _)) = checked_scope_fields(variant, emission) {
        let task = format_ident!("Assemble{}_{}", category, label);
        let slots = scalar_slot_fields(fields);
        return Some(quote! {
            #task { src: *const #category, slot: usize, #(#slots,)* scope_body_slot: Option<usize> }
        });
    }
    let (label, fields, prefix) = match variant {
        VariantKind::Regular { label, fields } if checked_scalar_fields(fields, emission) => {
            let task = format_ident!("Assemble{}_{}", category, label);
            let slots = scalar_slot_fields(fields);
            return Some(quote! { #task { src: *const #category, slot: usize, #(#slots),* } });
        },
        VariantKind::Regular { label, fields } if fields.iter().any(|f| f.is_collection) => {
            (label, fields.as_slice(), "f")
        },
        VariantKind::Binder { label, pre_scope_fields, .. }
        | VariantKind::MultiBinder { label, pre_scope_fields, .. }
            if pre_scope_fields.iter().any(|f| f.is_collection) =>
        {
            (label, pre_scope_fields.as_slice(), "pf")
        },
        VariantKind::Collection { label, .. } | VariantKind::CollectionLiteral { label, .. } => {
            let task = format_ident!("Assemble{}_{}", category, label);
            return Some(quote! {
                #task { src: *const #category, slot: usize, elements_start: usize }
            });
        },
        VariantKind::RecursiveNativeLiteral { label, .. } => {
            let task = format_ident!("Assemble{}_{}", category, label);
            return Some(quote! {
                #task { src: *const #category, slot: usize, elements_start: usize }
            });
        },
        VariantKind::Refused { .. }
        | VariantKind::Var { .. }
        | VariantKind::Literal { .. }
        | VariantKind::Nullary { .. }
        | VariantKind::Regular { .. }
        | VariantKind::Binder { .. }
        | VariantKind::MultiBinder { .. } => return None,
    };

    let task = format_ident!("Assemble{}_{}", category, label);
    let starts = fields.iter().enumerate().filter_map(|(index, field)| {
        field.is_collection.then(|| {
            let start = format_ident!("{}{}_start", prefix, index);
            quote! { #start: usize }
        })
    });
    Some(quote! {
        #task { src: *const #category, slot: usize, #(#starts),* }
    })
}

/// Shared paid endpoint-reversal body. Both binding and source observation
/// preserve the original worklist prefix and move only whole newly appended
/// task records. The source groups match PaidTaskBatchReversal exactly.
pub(crate) fn paid_task_batch_reversal_body() -> TokenStream {
    quote! {
        mettail_runtime::reserve_binding_parts(3, 2, 0, reserve)?;
        let mut left = start;
        let mut right = stack.len();
        loop {
            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
            let width = right.checked_sub(left).ok_or(
                mettail_runtime::BindingFailure::InvalidCollectionInput(
                    "binding task batch starts beyond the worklist"))?;
            if width < 2 { return Ok(()) }
            mettail_runtime::reserve_binding_parts(6, 1, 0, reserve)?;
            right -= 1;
            stack.swap(left, right);
            left = left.checked_add(1)
                .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
        }
    }
}

// Constructor bodies have disjoint native frames, just as in checked_source.
// No helper traverses a child by calling this selector: children remain tasks
// on the one existing worklist. CheckedBindingTaskDispatch applies to both
// selector levels; native frame bounds additionally require compiled evidence.
fn generate_checked_category_handler(
    category: &Ident,
    language: &LanguageDef,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let handler = emission.handler(category);
    let task_type = emission.task_type();
    let generics = emission.function_generics();
    let parameters = emission.binding_parameters();
    let result_type = emission.result_type();
    let variants = collect_category_variants(category, language);
    let mut selections = Vec::with_capacity(variants.len());
    let mut helpers = Vec::with_capacity(variants.len());
    for variant in variants {
        let label = variant.label();
        let helper = format_ident!("{}_{}", handler, label);
        let pattern = match variant {
            VariantKind::Nullary { .. } => quote! { #category::#label },
            _ => quote! { #category::#label(..) },
        };
        selections.push(quote! { #pattern => #helper::<E, F>, });
        let arm = generate_visit_arm(category, &variant, emission);
        // An unsupported arm already returns its exact refusal. Do not emit
        // an unreachable success expression after that diverging match.
        let success =
            checked_constructor_supported(category, &variant, emission).then(|| quote! { Ok(()) });
        helpers.push(quote! {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case, unreachable_patterns)]
            fn #helper #generics(
                stack: &mut Vec<#task_type>, results: &mut Vec<Option<AnyClonedTerm>>,
                src: *const #category, slot: usize, #parameters
            ) #result_type {
                let source = unsafe { &*src };
                match source {
                    #arm
                    _ => unreachable!("checked binding constructor selector/payload mismatch"),
                }
                #success
            }
        });
    }
    quote! {
        #(#helpers)*
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn #handler #generics(
            stack: &mut Vec<#task_type>, results: &mut Vec<Option<AnyClonedTerm>>,
            src: *const #category, slot: usize, #parameters
        ) #result_type {
            let source = unsafe { &*src };
            // Selection/retention, call, and the helper's payload match.
            mettail_runtime::reserve_binding_parts(3, 1, 0, reserve)?;
            let visit: for<'operation> fn(
                &mut Vec<#task_type>, &mut Vec<Option<AnyClonedTerm>>,
                *const #category, usize, mettail_runtime::BindingOperation<'operation>,
                &mut F, &[mettail_runtime::binding_receipt::BindingCharge],
            ) -> Result<(), mettail_runtime::BindingFailure<E>> = match source {
                #(#selections)*
            };
            visit(stack, results, src, slot, operation, reserve, dummy_charges)
        }
    }
}

fn generate_checked_task_handler(
    task: &Ident,
    arm: TokenStream,
    emission: &CloneEmissionNames,
) -> (TokenStream, TokenStream) {
    let task_enum = &emission.task_enum;
    let task_type = emission.task_type();
    let generics = emission.function_generics();
    let parameters = emission.binding_parameters();
    let result_type = emission.result_type();
    let helper = format_ident!("binding_task_{}", task);
    let selection = quote! { #task_enum::#task { .. } => #helper::<E, F>, };
    let definition = quote! {
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case, unreachable_patterns)]
        fn #helper #generics(
            stack: &mut Vec<#task_type>, results: &mut Vec<Option<AnyClonedTerm>>,
            task: #task_enum, #parameters
        ) #result_type {
            match task {
                #arm
                _ => unreachable!("checked binding task selector/payload mismatch"),
            }
            Ok(())
        }
    };
    (selection, definition)
}

fn generate_engine(language: &LanguageDef, emission: &CloneEmissionNames) -> TokenStream {
    let task_enum = &emission.task_enum;
    let driver = &emission.driver;
    let task_type = emission.task_type();
    let generics = emission.function_generics();
    let binding_parameters = emission.binding_parameters();
    let result_type = emission.result_type();
    let success_tail = emission.success_tail();
    let binding_arguments = emission.binding_arguments();
    let propagate = emission.propagate();
    let batch_reversal = emission.checked.as_ref().map(|_| {
        let body = paid_task_batch_reversal_body();
        quote! {
            #[allow(dead_code)]
            fn reverse_binding_task_batch<E>(
                stack: &mut [#task_type], start: usize,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<(), mettail_runtime::BindingFailure<E>> {
                #body
            }
        }
    });
    let handlers = language.types.iter().map(|ty| {
        let category = &ty.name;
        if emission.checked.is_some() {
            return generate_checked_category_handler(category, language, emission);
        }
        let handler = emission.handler(category);
        let arms: Vec<_> = collect_category_variants(category, language)
            .iter()
            .map(|variant| generate_visit_arm(category, variant, emission))
            .collect();
        quote! {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn #handler #generics(
                stack: &mut Vec<#task_type>,
                results: &mut Vec<Option<AnyClonedTerm>>,
                src: *const #category,
                slot: usize,
                #binding_parameters
            ) #result_type {
                let source = unsafe { &*src };
                match source {
                    #(#arms)*
                }
                #success_tail
            }
        }
    });

    let mut task_helpers = Vec::new();
    let visits: Vec<_> = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
            let visit = format_ident!("Clone{}", category);
            let handler = emission.handler(category);
            let arm = quote! {
                #task_enum::#visit { src, slot } =>
                    #handler(stack, results, src, slot #binding_arguments) #propagate,
            };
            if emission.checked.is_some() {
                let (selection, helper) = generate_checked_task_handler(&visit, arm, emission);
                task_helpers.push(helper);
                selection
            } else {
                arm
            }
        })
        .collect();

    let mut assemblies = Vec::new();
    for ty in &language.types {
        let category = &ty.name;
        let variants = collect_category_variants(category, language);
        let destructure_is_irrefutable = variants.len() == 1;
        for variant in variants {
            if let Some(arm) =
                generate_assemble_arm(category, &variant, destructure_is_irrefutable, emission)
            {
                if emission.checked.is_some() {
                    let task = format_ident!("Assemble{}_{}", category, variant.label());
                    let (selection, helper) = generate_checked_task_handler(&task, arm, emission);
                    task_helpers.push(helper);
                    assemblies.push(selection);
                } else {
                    assemblies.push(arm);
                }
            }
        }
    }

    let loop_body = if emission.checked.is_some() {
        quote! {
            while !stack.is_empty() {
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
                let (task, state) = stack.pop()
                    .expect("nonempty checked binding worklist");
                let operation = operation.with_state(state);
                // A discriminant-only selector and one common call avoid
                // retaining all arm-local Result temporaries in this frame.
                mettail_runtime::reserve_binding_parts(3, 1, 0, reserve)?;
                let execute: for<'operation> fn(
                    &mut Vec<#task_type>, &mut Vec<Option<AnyClonedTerm>>, #task_enum,
                    mettail_runtime::BindingOperation<'operation>, &mut F,
                    &[mettail_runtime::binding_receipt::BindingCharge],
                ) -> Result<(), mettail_runtime::BindingFailure<E>> = match &task {
                    #(#visits)*
                    #(#assemblies)*
                };
                execute(stack, results, task, operation, reserve, dummy_charges)?;
            }
        }
    } else {
        quote! {
            while let Some(task) = stack.pop() {
                match task {
                    #(#visits)*
                    #(#assemblies)*
                }
            }
        }
    };

    quote! {
        #batch_reversal
        #(#handlers)*
        #(#task_helpers)*

        #[allow(dead_code, unused_variables, unreachable_patterns)]
        fn #driver #generics(
            stack: &mut Vec<#task_type>,
            results: &mut Vec<Option<AnyClonedTerm>>,
            #binding_parameters
        ) #result_type {
            #loop_body
            #success_tail
        }
    }
}

fn generate_visit_arm(
    category: &Ident,
    variant: &VariantKind,
    emission: &CloneEmissionNames,
) -> TokenStream {
    if !checked_constructor_supported(category, variant, emission) {
        let label = variant.label();
        let category_name = category.to_string();
        let constructor_name = label.to_string();
        return quote! {
            #category::#label(..) => {
                return Err(mettail_runtime::BindingFailure::UnsupportedConstructor {
                    category: #category_name, constructor: #constructor_name,
                });
            }
        };
    }
    if let Some((label, fields)) = checked_collection_payload(variant, emission) {
        return generate_scalar_visit(category, label, &fields, None, emission);
    }
    if let Some((label, fields, scope)) = checked_scope_fields(variant, emission) {
        return generate_scalar_visit(category, label, fields, Some(scope), emission);
    }
    let wrap = format_ident!("Wrap{}", category);
    match variant {
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Nullary { label } => {
            let admission = emission.base_admission();
            let publish = emission.publish(category, quote! { #category::#label });
            quote! {
                #category::#label => {
                    #admission
                    #publish
                }
            }
        },
        VariantKind::Var { label } | VariantKind::Literal { label } => {
            if emission.checked.is_some() {
                let admission = emission.base_admission();
                let publish = emission.publish(category, quote! { #category::#label(copied) });
                quote! {
                    #category::#label(value) => {
                        #admission
                        let copied = mettail_runtime::CheckedBindingLeaf::try_copy_binding(
                            value, operation, reserve,
                        )?;
                        #publish
                    }
                }
            } else {
                quote! {
                    #category::#label(value) => {
                        results[slot] =
                            Some(AnyClonedTerm::#wrap(#category::#label(value.clone())));
                    }
                }
            }
        },
        VariantKind::Regular { label, fields } => {
            if checked_scalar_fields(fields, emission) {
                generate_scalar_visit(category, label, fields, None, emission)
            } else {
                generate_structured_visit(category, label, fields, false, emission)
            }
        },
        VariantKind::Binder { label, pre_scope_fields, .. }
        | VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
            generate_structured_visit(category, label, pre_scope_fields, true, emission)
        },
        VariantKind::Collection { label, element_cat, coll_type } => generate_collection_visit(
            category,
            label,
            element_cat,
            coll_type,
            CollectionSurface::Direct,
            emission,
        ),
        VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
            generate_collection_visit(
                category,
                label,
                element_cat,
                coll_type,
                CollectionSurface::Literal,
                emission,
            )
        },
        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            generate_recursive_native_visit(category, label, carrier, emission)
        },
    }
}

fn generate_recursive_native_visit(
    category: &Ident,
    label: &Ident,
    carrier: &NativeRecursiveCarrier,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task = format_ident!("Assemble{}_{}", category, label);
    let pathmap = carrier.pathmap_ref(&quote! { native });
    let pushes = carrier.for_each_borrowed_subterm(
        &quote! { native },
        crate::gen::native_carrier::NativeCarrierWalkOrder::ReverseForLifo,
        &|child_category, child| {
            let visit = format_ident!("Clone{}", child_category);
            quote! {
                __native_next_slot -= 1;
                stack.push(#task_enum::#visit {
                    src: #child as *const _,
                    slot: __native_next_slot,
                });
            }
        },
    );
    quote! {
        #category::#label(native) => {
            let __native_count = match (#pathmap).mode() {
                mettail_runtime::PathMapMode::Empty => 0,
                mettail_runtime::PathMapMode::Set => (#pathmap).len(),
                mettail_runtime::PathMapMode::Map => (#pathmap).len().saturating_mul(2),
            };
            let __native_start = results.len();
            results.resize_with(__native_start + __native_count, || None);
            stack.push(#task_enum::#task {
                src: source as *const _,
                slot,
                elements_start: __native_start,
            });
            let mut __native_next_slot = __native_start + __native_count;
            #pushes
            debug_assert_eq!(__native_next_slot, __native_start);
        }
    }
}

fn scalar_slot_fields(fields: &[FieldInfo]) -> Vec<TokenStream> {
    fields
        .iter()
        .enumerate()
        .filter(|(_, field)| !inline_binding_leaf(field))
        .map(|(index, field)| {
            let slot = format_ident!("field_{}_slot", index);
            if required_checked_collection_field(field) {
                quote! { #slot: (usize, usize) }
            } else {
                // None means absent optional child or an untraversed shallow
                // Clone edge; operation/source presence distinguish the two.
                quote! { #slot: Option<usize> }
            }
        })
        .collect()
}

fn native_field_copy(field: &FieldInfo, source: &Ident, output: &Ident) -> TokenStream {
    if field.is_optional {
        // Native fields drop in place: no Option::take, dummy, or category
        // task. FlatBindingLeafReservation supplies only the 2/1 shell charge.
        quote! {
            mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)?;
            let #output = match #source.as_ref() {
                Some(value) => Some(mettail_runtime::CheckedBindingLeaf::try_copy_binding(
                    value, operation, reserve,
                )?),
                None => None,
            };
        }
    } else {
        quote! {
            let #output = mettail_runtime::CheckedBindingLeaf::try_copy_binding(
                #source, operation, reserve,
            )?;
        }
    }
}

// ScalarArcBindingReservation supplies these field-local projections. Parent,
// worker/slot charges and existing child credit remain separate.
fn scalar_field_admission(
    field: &FieldInfo,
    present: TokenStream,
    owned: bool,
    emission: &CloneEmissionNames,
) -> TokenStream {
    if field.is_optional {
        let (work, records) = if owned { (8usize, 4usize) } else { (7, 3) };
        quote! {
            let (work, records) = if #present { (#work, #records) } else { (5, 2) };
            mettail_runtime::reserve_binding_parts(work, records, 0, reserve)?;
        }
    } else {
        required_field_admission(&field.category, owned, emission)
    }
}

fn required_field_admission(
    category: &Ident,
    owned: bool,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let dummy = match emission.dummy_charge(category) {
        Ok(charge) => charge,
        Err(error) => return error.into_compile_error(),
    };
    let (work, records) = if owned { (7usize, 3usize) } else { (6, 2) };
    quote! {
        mettail_runtime::reserve_binding_parts(#work, #records, 0, reserve)?;
        #dummy.reserve(reserve)?;
    }
}

fn scope_field_admission(
    scope: CheckedScopeField<'_>,
    owned: bool,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let body = required_field_admission(scope.body_category, owned, emission);
    // ScopeBindingReservation: scope shells/unpack/dispatch plus the exact
    // replacement pattern. Original pattern copying is separately admitted.
    let work = if scope.multiple { 6usize } else { 7usize };
    quote! { #body mettail_runtime::reserve_binding_parts(#work, 3, 0, reserve)?; }
}

fn scope_pattern_copy() -> TokenStream {
    quote! {
        let copied_pattern = mettail_runtime::CheckedBindingLeaf::try_copy_binding(
            scope.unsafe_pattern(), operation, reserve,
        )?;
    }
}

fn vec_field_admission(range: &Ident) -> TokenStream {
    // RequiredVecBindingReservation, excluding child/slot/task charges.
    quote! {
        let width = #range.1;
        let work = width.checked_mul(4).and_then(|v| v.checked_add(10))
            .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
        let records = width.checked_mul(2).and_then(|v| v.checked_add(4))
            .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
        mettail_runtime::reserve_binding_parts(work, records, 0, reserve)?;
    }
}

fn vec_child_pushes(
    field: &FieldInfo,
    source: &Ident,
    range: &Ident,
    emission: &CloneEmissionNames,
) -> TokenStream {
    use super::collection_walk::{for_each_subterm, WalkOrder};
    let task_enum = &emission.task_enum;
    let visit = format_ident!("Clone{}", field.category);
    let pushes = for_each_subterm(
        &CollectionType::Vec,
        &quote! { #source },
        WalkOrder::ReverseForLifo,
        &|child, _| {
            let push = emission.push_task(
                quote! {
                    #task_enum::#visit { src: #child as *const _, slot: next_slot }
                },
                quote! { operation.state() },
            );
            quote! {
                next_slot = next_slot.checked_sub(1)
                    .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
                #push
            }
        },
    );
    quote! {{
        let (start, width) = #range;
        let work = width.checked_add(3)
            .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
        mettail_runtime::reserve_binding_parts(work, 1, 0, reserve)?;
        let mut next_slot = start.checked_add(width)
            .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
        #pushes
        debug_assert_eq!(next_slot, start);
    }}
}

fn bag_child_pushes(
    field: &FieldInfo,
    source: &Ident,
    range: &Ident,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let visit = format_ident!("Clone{}", field.category);
    let push = emission.push_task(
        quote! { #task_enum::#visit { src: child as *const _, slot: child_slot } },
        quote! { operation.state() },
    );
    quote! {{
        mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)?;
        let (start, width) = #range;
        let end = start.checked_add(width)
            .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
        let batch_start = stack.len();
        let mut child_slot = start;
        #source.try_for_each_entry(reserve, |child, _count, reserve| {
            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
            if child_slot >= end {
                return Err(mettail_runtime::BindingFailure::InvalidCollectionInput(
                    "binding Bag scan exceeds its original slot range"));
            }
            #push
            child_slot = child_slot.checked_add(1)
                .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
            Ok(())
        })?;
        if child_slot != end {
            return Err(mettail_runtime::BindingFailure::InvalidCollectionInput(
                "binding Bag scan did not fill its original slot range"));
        }
        reverse_binding_task_batch(stack, batch_start, reserve)?;
    }}
}

fn generate_scalar_visit(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    scope: Option<CheckedScopeField<'_>>,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let names: Vec<_> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let slots: Vec<_> = (0..fields.len())
        .map(|i| format_ident!("field_{}_slot", i))
        .collect();
    let base = emission.base_admission();
    let admissions = fields.iter().zip(&names).map(|(field, name)| {
        if inline_binding_leaf(field) {
            TokenStream::new()
        } else if required_checked_collection_field(field) {
            TokenStream::new() // Owned collections use assembly even in Clone.
        } else {
            scalar_field_admission(field, quote! { #name.is_some() }, false, emission)
        }
    });
    let native_copies =
        fields
            .iter()
            .zip(&names)
            .enumerate()
            .filter_map(|(index, (field, name))| {
                inline_binding_leaf(field)
                    .then(|| native_field_copy(field, name, &format_ident!("bare_{}", index)))
            });
    let mut clones: Vec<_> = fields
        .iter()
        .zip(&names)
        .enumerate()
        .map(|(index, (field, name))| {
            if inline_binding_leaf(field) {
                let bare = format_ident!("bare_{}", index);
                quote! { #bare }
            } else {
                quote! { #name.clone() }
            }
        })
        .collect();
    let mut source_names = names.clone();
    let scope_admission = scope.map(|scope| scope_field_admission(scope, false, emission));
    let pattern_copy = scope.map(|_| scope_pattern_copy());
    if scope.is_some() {
        source_names.push(format_ident!("scope"));
        clones.push(quote! {
            mettail_runtime::Scope::from_parts_unsafe(
                copied_pattern, std::sync::Arc::clone(scope.unsafe_body()))
        });
    }
    let publish = emission.publish(category, quote! { #category::#label(#(#clones),*) });
    let allocations = fields.iter().zip(&names).zip(&slots).map(|((field, name), slot)| {
        if inline_binding_leaf(field) { TokenStream::new() }
        else if required_vec_field(field) {
            quote! {
                let width = #name.len();
                let #slot = (mettail_runtime::append_binding_slots(results, width, reserve)?, width);
            }
        }
        else if required_bag_field(field) {
            quote! {
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
                let width = #name.distinct_len();
                let #slot = (mettail_runtime::append_binding_slots(results, width, reserve)?, width);
            }
        }
        else if field.is_optional {
            quote! {
                let #slot = match (#name, cloning) {
                    (Some(_), false) => Some(mettail_runtime::append_binding_slots(results, 1, reserve)?),
                    _ => None,
                };
            }
        } else {
            quote! { let #slot = if cloning { None }
                else { Some(mettail_runtime::append_binding_slots(results, 1, reserve)?) }; }
        }
    });
    let task_enum = &emission.task_enum;
    let task = format_ident!("Assemble{}_{}", category, label);
    let mut child_slots: Vec<_> = fields
        .iter()
        .zip(&slots)
        .filter_map(|(field, slot)| (!inline_binding_leaf(field)).then_some(slot.clone()))
        .collect();
    if scope.is_some() {
        child_slots.push(format_ident!("scope_body_slot"));
    }
    let assemble = emission.push_task(
        quote! { #task_enum::#task { src: source as *const _, slot, #(#child_slots),* } },
        quote! { operation.state() },
    );
    let pushes = fields
        .iter()
        .zip(&names)
        .zip(&slots)
        .rev()
        .map(|((field, name), slot)| {
            if inline_binding_leaf(field) {
                return TokenStream::new();
            }
            if required_vec_field(field) {
                return vec_child_pushes(field, name, slot, emission);
            }
            if required_bag_field(field) {
                return bag_child_pushes(field, name, slot, emission);
            }
            let visit = format_ident!("Clone{}", field.category);
            let push = emission.push_task(
                quote! { #task_enum::#visit { src: child.as_ref() as *const _, slot: child_slot } },
                quote! { operation.state() },
            );
            if field.is_optional {
                quote! {
                    if let (Some(child), Some(child_slot)) = (#name.as_ref(), #slot) { #push }
                }
            } else {
                quote! { if let Some(child_slot) = #slot { let child = #name; #push } }
            }
        });
    let scope_allocation = scope.map(|_| {
        quote! {
            let scope_body_slot = if cloning { None }
                else { Some(mettail_runtime::append_binding_slots(results, 1, reserve)?) };
        }
    });
    let scope_depth = scope.map(|_| {
        quote! {
            let body_operation = if cloning { operation } else {
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
                operation.under_scope()?
            };
        }
    });
    let scope_push = scope.map(|scope| {
        let visit = format_ident!("Clone{}", scope.body_category);
        let push = emission.push_task(
            quote! { #task_enum::#visit {
                src: scope.unsafe_body().as_ref() as *const _, slot: child_slot,
            } },
            quote! { body_operation.state() },
        );
        quote! { if let Some(child_slot) = scope_body_slot { #push } }
    });
    let schedule = quote! {
        let cloning = matches!(operation, mettail_runtime::BindingOperation::Clone);
        #scope_depth
        #(#allocations)*
        #scope_allocation
        #assemble
        // The last source child is pushed first on the LIFO stack.
        #scope_push
        #(#pushes)*
    };
    let body = if fields.iter().any(required_checked_collection_field) {
        schedule
    } else {
        quote! {
                match operation {
                    mettail_runtime::BindingOperation::Clone => {
                        #base
                        #(#admissions)*
                        #scope_admission
                        #(#native_copies)*
                        #pattern_copy
                        // No fallible call occurs between cloning the handles
                        // and forming the parent passed to checked publication.
                        #publish
                    },
                    mettail_runtime::BindingOperation::Open { .. }
                    | mettail_runtime::BindingOperation::Close { .. } => {
                        #schedule
                    },
                }
        }
    };
    quote! { #category::#label(#(ref #source_names),*) => { #body } }
}

fn generate_scalar_assemble(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    scope: Option<CheckedScopeField<'_>>,
    destructure_is_irrefutable: bool,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task = format_ident!("Assemble{}_{}", category, label);
    let slots: Vec<_> = (0..fields.len())
        .map(|i| format_ident!("field_{}_slot", i))
        .collect();
    let mut slot_fields = scalar_slot_fields(fields);
    let mut child_slots: Vec<_> = fields
        .iter()
        .zip(&slots)
        .filter_map(|(field, slot)| (!inline_binding_leaf(field)).then_some(slot.clone()))
        .collect();
    let names: Vec<_> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let mut source_names = names.clone();
    if scope.is_some() {
        slot_fields.push(quote! { scope_body_slot: Option<usize> });
        child_slots.push(format_ident!("scope_body_slot"));
        source_names.push(format_ident!("scope"));
    }
    let destructure = if destructure_is_irrefutable {
        quote! { let #category::#label(#(ref #source_names),*) = source; }
    } else {
        quote! {
            let #category::#label(#(ref #source_names),*) = source else {
                unreachable!("checked binding assembly retains its source variant")
            };
        }
    };
    let base = emission.base_admission();
    let admissions = fields
        .iter()
        .zip(&slots)
        .zip(&names)
        .map(|((field, slot), name)| {
            if inline_binding_leaf(field) {
                TokenStream::new()
            } else if required_checked_collection_field(field) {
                vec_field_admission(slot)
            } else {
                let shallow =
                    scalar_field_admission(field, quote! { #name.is_some() }, false, emission);
                let owned =
                    scalar_field_admission(field, quote! { #name.is_some() }, true, emission);
                quote! { if cloning { #shallow } else { #owned } }
            }
        });
    let bare: Vec<_> = (0..fields.len())
        .map(|i| format_ident!("bare_{}", i))
        .collect();
    let native_copies = fields
        .iter()
        .zip(&names)
        .zip(&bare)
        .filter_map(|((field, name), bare)| {
            inline_binding_leaf(field).then(|| native_field_copy(field, name, bare))
        });
    let takes = fields
        .iter()
        .zip(&slots)
        .zip(&bare)
        .zip(&names)
        .map(|(((field, slot), bare), name)| {
            if inline_binding_leaf(field) {
                return TokenStream::new();
            }
            let wrap = format_ident!("Wrap{}", field.category);
            let take = quote! {
                match mettail_runtime::take_binding_slot(results, child_slot,
                    |value| matches!(value, AnyClonedTerm::#wrap(_)), reserve)? {
                    AnyClonedTerm::#wrap(child) => child,
                    _ => unreachable!("checked category discriminant is unchanged during take"),
                }
            };
            if required_vec_field(field) {
                quote! {
                    let #bare = {
                        let (start, width) = #slot;
                        let mut copied = Vec::with_capacity(width);
                        for offset in 0..width {
                            let child_slot = start.checked_add(offset)
                                .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
                            copied.push(#take);
                        }
                        copied
                    };
                }
            } else if required_bag_field(field) {
                let category = &field.category;
                let admit = format_ident!("admit_bag_rebuild_{}", category.to_string().to_lowercase());
                quote! {
                    let #bare = {
                        // RequiredVec's total prepays this owned entry vector
                        // and all partial cleanup. Bag cleanup is in Start.
                        mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)?;
                        let (start, width) = #slot;
                        let end = start.checked_add(width)
                            .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
                        std::alloc::Layout::array::<(#category, usize)>(width)
                            .map_err(|_| mettail_runtime::BindingFailure::SizeOverflow)?;
                        let mut copied = Vec::with_capacity(width);
                        let mut child_slot = start;
                        // The immutable source keeps the same native entry
                        // order and original counts as the scheduling scan.
                        #name.try_for_each_entry(reserve, |_original, count, reserve| {
                            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
                            if child_slot >= end {
                                return Err(mettail_runtime::BindingFailure::InvalidCollectionInput(
                                    "binding Bag assembly exceeds its original slot range"));
                            }
                            copied.push((#take, count));
                            child_slot = child_slot.checked_add(1)
                                .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
                            Ok(())
                        })?;
                        if child_slot != end {
                            return Err(mettail_runtime::BindingFailure::InvalidCollectionInput(
                                "binding Bag assembly did not fill its original slot range"));
                        }
                        let mode = if cloning { mettail_runtime::HashBagRebuildMode::CloneEntries }
                            else { mettail_runtime::HashBagRebuildMode::BindingEntries };
                        #name.try_rebuild_entries_with(copied, mode, |step| #admit(step, reserve))?
                    };
                }
            } else if field.is_optional {
                quote! {
                    let #bare = match #slot {
                        Some(child_slot) => Some(#take),
                        None => None,
                    };
                }
            } else {
                quote! {
                    let #bare = if cloning { None } else {
                        let child_slot = #slot.expect("binding schedules every required scalar child");
                        Some(#take)
                    };
                }
            }
        });
    let mut wrappers: Vec<_> = fields
        .iter()
        .zip(&bare).zip(&names)
        .map(|((field, bare), name)| {
            if inline_binding_leaf(field) || required_checked_collection_field(field) {
                quote! { #bare }
            } else if field.is_optional {
                quote! { if cloning { #name.clone() } else { #bare.map(std::sync::Arc::new) } }
            } else {
                quote! { if cloning { std::sync::Arc::clone(#name) } else {
                    std::sync::Arc::new(#bare.expect("required scalar child was taken before wrapping"))
                } }
            }
        })
        .collect();
    let scope_admission = scope.map(|scope| {
        let shallow = scope_field_admission(scope, false, emission);
        let owned = scope_field_admission(scope, true, emission);
        quote! { if cloning { #shallow } else { #owned } }
    });
    let pattern_copy = scope.map(|_| scope_pattern_copy());
    let body_take = scope.map(|scope| {
        let wrap = format_ident!("Wrap{}", scope.body_category);
        quote! {
            let bare_body = if cloning { None } else {
                let child_slot = scope_body_slot.expect("binding schedules the scope body");
                Some(match mettail_runtime::take_binding_slot(
                results, child_slot,
                |value| matches!(value, AnyClonedTerm::#wrap(_)), reserve,
            )? {
                AnyClonedTerm::#wrap(child) => child,
                _ => unreachable!("checked scope body category is unchanged during take"),
                })
            };
        }
    });
    if scope.is_some() {
        wrappers.push(quote! {
            mettail_runtime::Scope::from_parts_unsafe(
                copied_pattern, if cloning { std::sync::Arc::clone(scope.unsafe_body()) }
                else { std::sync::Arc::new(bare_body.expect("scope body taken before wrapping")) })
        });
    }
    let publish = emission.publish(category, quote! { #category::#label(#(#wrappers),*) });
    quote! {
        #task_enum::#task { src, slot, #(#child_slots),* } => {
            #[inline(never)]
            fn assemble<E>(
                results: &mut Vec<Option<AnyClonedTerm>>,
                src: *const #category,
                slot: usize,
                #(#slot_fields,)*
                operation: mettail_runtime::BindingOperation<'_>,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
                dummy_charges: &[mettail_runtime::binding_receipt::BindingCharge],
            ) -> Result<(), mettail_runtime::BindingFailure<E>> {
                let source = unsafe { &*src };
                #destructure
                let cloning = matches!(operation, mettail_runtime::BindingOperation::Clone);
                #base
                #(#admissions)*
                #scope_admission
                #(#native_copies)*
                #pattern_copy
                // Every fallible take precedes ALL wrapper construction.
                // Failure drops admitted native locals and bare categories.
                #(#takes)*
                #body_take
                #publish
                Ok(())
            }
            assemble(results, src, slot, #(#child_slots,)* operation, reserve, dummy_charges)?;
        },
    }
}

fn generate_structured_visit(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    has_scope: bool,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let field_count = fields.len() + usize::from(has_scope);
    let names: Vec<Ident> = (0..field_count).map(|i| format_ident!("f{}", i)).collect();
    let collection_sites: Vec<_> = fields
        .iter()
        .enumerate()
        .filter(|(_, field)| field.is_collection)
        .collect();

    if collection_sites.is_empty() {
        let clones = names.iter().map(|name| quote! { #name.clone() });
        let wrap = format_ident!("Wrap{}", category);
        return quote! {
            #category::#label(#(ref #names),*) => {
                results[slot] = Some(AnyClonedTerm::#wrap(
                    #category::#label(#(#clones),*)
                ));
            }
        };
    }

    let task = format_ident!("Assemble{}_{}", category, label);
    let prefix = if has_scope { "pf" } else { "f" };
    let allocations = collection_sites.iter().map(|(index, field)| {
        let name = &names[*index];
        let start = format_ident!("{}{}_start", prefix, index);
        generate_collection_allocation(name, &start, field, field.is_optional)
    });
    let starts = collection_sites.iter().map(|(index, _)| {
        let start = format_ident!("{}{}_start", prefix, index);
        quote! { #start }
    });
    let pushes: Vec<_> = collection_sites
        .iter()
        .rev()
        .map(|(index, field)| {
            let name = &names[*index];
            let start = format_ident!("{}{}_start", prefix, index);
            generate_collection_push(name, &start, field, field.is_optional, emission)
        })
        .collect();

    quote! {
        #category::#label(#(ref #names),*) => {
            #(#allocations)*
            stack.push(#task_enum::#task {
                src: source as *const _,
                slot,
                #(#starts),*
            });
            #(#pushes)*
        }
    }
}

fn generate_collection_visit(
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    _surface: CollectionSurface,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task = format_ident!("Assemble{}_{}", category, label);
    let field = FieldInfo {
        category: element_cat.clone(),
        is_collection: true,
        coll_type: Some(coll_type.clone()),
        is_predicate: false,
        is_optional: false,
        opaque_leaf: None,
    };
    let collection = format_ident!("collection");
    let elements_start = format_ident!("elements_start");
    let allocation = generate_collection_allocation(&collection, &elements_start, &field, false);
    let push = generate_collection_push(&collection, &elements_start, &field, false, emission);

    quote! {
        #category::#label(ref collection) => {
            #allocation
            stack.push(#task_enum::#task {
                src: source as *const _,
                slot,
                elements_start,
            });
            #push
        }
    }
}

fn generate_collection_allocation(
    name: &Ident,
    start: &Ident,
    field: &FieldInfo,
    optional: bool,
) -> TokenStream {
    let maybe_collection = if optional {
        quote! { #name.as_ref() }
    } else {
        quote! { Some(#name) }
    };
    let slots = match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
        CollectionType::Vec | CollectionType::HashSet | CollectionType::HashBag => {
            quote! { __collection.iter().count() }
        },
        CollectionType::HashMap => quote! { __collection.len() * 2 },
        CollectionType::PathMap => quote! {
            __collection
                .iter()
                .map(|entry| if entry.is_map() { 2usize } else { 1usize })
                .sum()
        },
    };
    quote! {
        let #start = results.len();
        if let Some(__collection) = #maybe_collection {
            let __slot_count: usize = #slots;
            results.resize_with(results.len() + __slot_count, || None);
        }
    }
}

fn generate_collection_push(
    name: &Ident,
    start: &Ident,
    field: &FieldInfo,
    optional: bool,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let visit = format_ident!("Clone{}", field.category);
    let maybe_collection = if optional {
        quote! { #name.as_ref() }
    } else {
        quote! { Some(#name) }
    };
    let body = match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
        CollectionType::Vec | CollectionType::HashSet => quote! {
            for (__index, __element) in __collection.iter().enumerate() {
                stack.push(#task_enum::#visit {
                    src: __element as *const _,
                    slot: #start + __index,
                });
            }
        },
        CollectionType::HashBag => quote! {
            for (__index, (__element, _count)) in __collection.iter().enumerate() {
                stack.push(#task_enum::#visit {
                    src: __element as *const _,
                    slot: #start + __index,
                });
            }
        },
        CollectionType::HashMap => quote! {
            for (__index, (__key, __value)) in __collection.iter().enumerate() {
                stack.push(#task_enum::#visit {
                    src: __key as *const _,
                    slot: #start + __index * 2,
                });
                stack.push(#task_enum::#visit {
                    src: __value as *const _,
                    slot: #start + __index * 2 + 1,
                });
            }
        },
        CollectionType::PathMap => quote! {
            let mut __slot = #start;
            for __entry in __collection.iter() {
                stack.push(#task_enum::#visit {
                    src: __entry.key() as *const _,
                    slot: __slot,
                });
                __slot += 1;
                if let Some(__value) = __entry.value() {
                    stack.push(#task_enum::#visit {
                        src: __value as *const _,
                        slot: __slot,
                    });
                    __slot += 1;
                }
            }
        },
    };

    quote! {
        if let Some(__collection) = #maybe_collection {
            let __batch_start = stack.len();
            #body
            stack[__batch_start..].reverse();
        }
    }
}

fn generate_assemble_arm(
    category: &Ident,
    variant: &VariantKind,
    destructure_is_irrefutable: bool,
    emission: &CloneEmissionNames,
) -> Option<TokenStream> {
    if !checked_constructor_supported(category, variant, emission) {
        return None;
    }
    if let Some((label, fields)) = checked_collection_payload(variant, emission) {
        return Some(generate_scalar_assemble(
            category,
            label,
            &fields,
            None,
            destructure_is_irrefutable,
            emission,
        ));
    }
    if let Some((label, fields, scope)) = checked_scope_fields(variant, emission) {
        return Some(generate_scalar_assemble(
            category,
            label,
            fields,
            Some(scope),
            destructure_is_irrefutable,
            emission,
        ));
    }
    match variant {
        VariantKind::Regular { label, fields } if checked_scalar_fields(fields, emission) => {
            Some(generate_scalar_assemble(
                category,
                label,
                fields,
                None,
                destructure_is_irrefutable,
                emission,
            ))
        },
        VariantKind::Regular { label, fields } if fields.iter().any(|f| f.is_collection) => {
            Some(generate_structured_assemble(
                category,
                label,
                fields,
                false,
                destructure_is_irrefutable,
                emission,
            ))
        },
        VariantKind::Binder { label, pre_scope_fields, .. }
        | VariantKind::MultiBinder { label, pre_scope_fields, .. }
            if pre_scope_fields.iter().any(|f| f.is_collection) =>
        {
            Some(generate_structured_assemble(
                category,
                label,
                pre_scope_fields,
                true,
                destructure_is_irrefutable,
                emission,
            ))
        },
        VariantKind::Collection { label, element_cat, coll_type } => {
            Some(generate_collection_assemble(
                category,
                label,
                element_cat,
                coll_type,
                CollectionSurface::Direct,
                destructure_is_irrefutable,
                emission,
            ))
        },
        VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
            Some(generate_collection_assemble(
                category,
                label,
                element_cat,
                coll_type,
                CollectionSurface::Literal,
                destructure_is_irrefutable,
                emission,
            ))
        },
        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            Some(generate_recursive_native_assemble(
                category,
                label,
                carrier,
                destructure_is_irrefutable,
                emission,
            ))
        },
        VariantKind::Refused { .. }
        | VariantKind::Var { .. }
        | VariantKind::Literal { .. }
        | VariantKind::Nullary { .. }
        | VariantKind::Regular { .. }
        | VariantKind::Binder { .. }
        | VariantKind::MultiBinder { .. } => None,
    }
}

fn generate_recursive_native_assemble(
    category: &Ident,
    label: &Ident,
    carrier: &NativeRecursiveCarrier,
    destructure_is_irrefutable: bool,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task = format_ident!("Assemble{}_{}", category, label);
    let wrap = format_ident!("Wrap{}", category);
    let key_wrap = format_ident!("Wrap{}", carrier.key_category());
    let value_wrap = format_ident!("Wrap{}", carrier.value_category());
    let pathmap = carrier.pathmap_ref(&quote! { native });
    let focus = carrier.focus_ref(&quote! { native });
    let payload = carrier.construct(&quote! { rebuilt }, &quote! { (*#focus).clone() });
    let destructure = if destructure_is_irrefutable {
        quote! { let #category::#label(ref native) = source; }
    } else {
        quote! {
            let #category::#label(ref native) = source else {
                unreachable!("iterative clone: recursive-native assemble/source mismatch")
            };
        }
    };

    quote! {
        #task_enum::#task { src, slot, elements_start } => {
            #[inline(never)]
            fn assemble(
                results: &mut Vec<Option<AnyClonedTerm>>,
                src: *const #category,
                slot: usize,
                elements_start: usize,
            ) {
                let source = unsafe { &*src };
                #destructure
                let rebuilt = match (#pathmap).mode() {
                    mettail_runtime::PathMapMode::Empty => {
                        mettail_runtime::PathMapLit::Empty
                    },
                    mettail_runtime::PathMapMode::Set => {
                        let mut entries = mettail_runtime::HashMapLit::new();
                        for index in 0..(#pathmap).len() {
                            let key = match results[elements_start + index].take()
                                .expect("iterative clone: missing zipper set key")
                            {
                                AnyClonedTerm::#key_wrap(value) => value,
                                _ => unreachable!("iterative clone: zipper set-key category mismatch"),
                            };
                            entries.insert(key, ());
                        }
                        mettail_runtime::PathMapLit::Set(entries)
                    },
                    mettail_runtime::PathMapMode::Map => {
                        let mut entries = mettail_runtime::HashMapLit::new();
                        for index in 0..(#pathmap).len() {
                            let key = match results[elements_start + index * 2].take()
                                .expect("iterative clone: missing zipper map key")
                            {
                                AnyClonedTerm::#key_wrap(value) => value,
                                _ => unreachable!("iterative clone: zipper map-key category mismatch"),
                            };
                            let value = match results[elements_start + index * 2 + 1].take()
                                .expect("iterative clone: missing zipper map value")
                            {
                                AnyClonedTerm::#value_wrap(value) => value,
                                _ => unreachable!("iterative clone: zipper map-value category mismatch"),
                            };
                            entries.insert(key, value);
                        }
                        mettail_runtime::PathMapLit::Map(entries)
                    },
                };
                results[slot] = Some(AnyClonedTerm::#wrap(
                    #category::#label(#payload)
                ));
            }
            assemble(results, src, slot, elements_start);
        },
    }
}

fn generate_structured_assemble(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    has_scope: bool,
    destructure_is_irrefutable: bool,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task = format_ident!("Assemble{}_{}", category, label);
    let wrap = format_ident!("Wrap{}", category);
    let prefix = if has_scope { "pf" } else { "f" };
    let collection_sites: Vec<_> = fields
        .iter()
        .enumerate()
        .filter(|(_, field)| field.is_collection)
        .collect();
    let starts: Vec<_> = collection_sites
        .iter()
        .map(|(index, _)| format_ident!("{}{}_start", prefix, index))
        .collect();
    let field_count = fields.len() + usize::from(has_scope);
    let names: Vec<Ident> = (0..field_count).map(|i| format_ident!("f{}", i)).collect();
    let extracts = fields.iter().enumerate().map(|(index, field)| {
        let result = format_ident!("field_{}", index);
        let source_field = &names[index];
        if field.is_collection {
            let start = format_ident!("{}{}_start", prefix, index);
            let rebuilt_inner = generate_collection_rebuild(
                field,
                CollectionSurface::Direct,
                &quote! { __collection },
                &start,
            );
            let rebuilt = if field.is_optional {
                quote! {
                    #source_field.as_ref().map(|__collection| #rebuilt_inner)
                }
            } else {
                quote! {{
                    let __collection = #source_field;
                    #rebuilt_inner
                }}
            };
            quote! { let #result = #rebuilt; }
        } else {
            quote! { let #result = #source_field.clone(); }
        }
    });
    let mut constructed: Vec<TokenStream> = (0..fields.len())
        .map(|index| {
            let field = format_ident!("field_{}", index);
            quote! { #field }
        })
        .collect();
    if has_scope {
        let scope = &names[field_count - 1];
        constructed.push(quote! { #scope.clone() });
    }

    let destructure = if destructure_is_irrefutable {
        quote! {
            let #category::#label(#(ref #names),*) = source;
        }
    } else {
        quote! {
            let #category::#label(#(ref #names),*) = source else {
                unreachable!("iterative clone: assemble task/source variant mismatch")
            };
        }
    };

    quote! {
        #task_enum::#task { src, slot, #(#starts),* } => {
            // Keep container reconstruction out of the dispatch loop's native
            // stack frame.  In a large generated language, leaving every
            // assembly body's locals in this match makes rustc reserve the
            // maximum arm frame for every iteration of the PDA.
            #[inline(never)]
            fn assemble(
                results: &mut Vec<Option<AnyClonedTerm>>,
                src: *const #category,
                slot: usize,
                #(#starts: usize),*
            ) {
                let source = unsafe { &*src };
                #destructure
                #(#extracts)*
                results[slot] = Some(AnyClonedTerm::#wrap(
                    #category::#label(#(#constructed),*)
                ));
            }
            assemble(results, src, slot, #(#starts),*);
        },
    }
}

fn generate_collection_assemble(
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    surface: CollectionSurface,
    destructure_is_irrefutable: bool,
    emission: &CloneEmissionNames,
) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task = format_ident!("Assemble{}_{}", category, label);
    let wrap = format_ident!("Wrap{}", category);
    let field = FieldInfo {
        category: element_cat.clone(),
        is_collection: true,
        coll_type: Some(coll_type.clone()),
        is_predicate: false,
        is_optional: false,
        opaque_leaf: None,
    };
    let elements_start = format_ident!("elements_start");
    let rebuilt =
        generate_collection_rebuild(&field, surface, &quote! { collection }, &elements_start);

    let destructure = if destructure_is_irrefutable {
        quote! {
            let #category::#label(ref collection) = source;
        }
    } else {
        quote! {
            let #category::#label(ref collection) = source else {
                unreachable!("iterative clone: collection assemble/source mismatch")
            };
        }
    };

    quote! {
        #task_enum::#task { src, slot, elements_start } => {
            #[inline(never)]
            fn assemble(
                results: &mut Vec<Option<AnyClonedTerm>>,
                src: *const #category,
                slot: usize,
                elements_start: usize,
            ) {
                let source = unsafe { &*src };
                #destructure
                let cloned = #rebuilt;
                results[slot] =
                    Some(AnyClonedTerm::#wrap(#category::#label(cloned)));
            }
            assemble(results, src, slot, elements_start);
        },
    }
}

fn generate_collection_rebuild(
    field: &FieldInfo,
    surface: CollectionSurface,
    source: &TokenStream,
    start: &Ident,
) -> TokenStream {
    let wrap = format_ident!("Wrap{}", field.category);
    let take = |slot: TokenStream| {
        quote! {
            match results[#slot]
                .take()
                .expect("iterative clone: missing collection element")
            {
                AnyClonedTerm::#wrap(value) => value,
                _ => unreachable!("iterative clone: collection element category mismatch"),
            }
        }
    };

    match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
        CollectionType::Vec => {
            let value = take(quote! { #start + index });
            quote! {{
                let mut output = Vec::with_capacity(#source.len());
                for index in 0..#source.len() {
                    output.push(#value);
                }
                output
            }}
        },
        CollectionType::HashSet => {
            let value = take(quote! { #start + index });
            match surface {
                CollectionSurface::Direct => quote! {{
                    let mut output = std::collections::HashSet::with_capacity_and_hasher(
                        #source.capacity(),
                        #source.hasher().clone(),
                    );
                    for index in 0..#source.len() {
                        output.insert(#value);
                    }
                    output
                }},
                CollectionSurface::Literal => quote! {{
                    let mut output = mettail_runtime::HashSetLit::new();
                    for index in 0..#source.len() {
                        output.insert(#value);
                    }
                    output
                }},
            }
        },
        CollectionType::HashBag => {
            let value = take(quote! { #start + index });
            quote! {{
                let mut output = mettail_runtime::HashBag::new();
                for (index, (_source_value, count)) in #source.iter().enumerate() {
                    output.insert_n(#value, count);
                }
                output
            }}
        },
        CollectionType::HashMap => {
            let key = take(quote! { #start + index * 2 });
            let value = take(quote! { #start + index * 2 + 1 });
            quote! {{
                let mut output = mettail_runtime::HashMapLit::new();
                for index in 0..#source.len() {
                    output.insert(#key, #value);
                }
                output
            }}
        },
        CollectionType::PathMap => {
            let set_key = take(quote! { #start + index });
            let map_key = take(quote! { #start + index * 2 });
            let map_value = take(quote! { #start + index * 2 + 1 });
            quote! {{
                match #source.mode() {
                    mettail_runtime::PathMapMode::Empty => mettail_runtime::PathMapLit::Empty,
                    mettail_runtime::PathMapMode::Set => {
                        let mut entries = mettail_runtime::HashMapLit::new();
                        for index in 0..#source.len() {
                            entries.insert(#set_key, ());
                        }
                        mettail_runtime::PathMapLit::Set(entries)
                    },
                    mettail_runtime::PathMapMode::Map => {
                        let mut entries = mettail_runtime::HashMapLit::new();
                        for index in 0..#source.len() {
                            entries.insert(#map_key, #map_value);
                        }
                        mettail_runtime::PathMapLit::Map(entries)
                    },
                }
            }}
        },
    }
}

fn generate_impls(language: &LanguageDef, emission: &CloneEmissionNames) -> TokenStream {
    let task_enum = &emission.task_enum;
    let task_pool = &emission.task_pool;
    let result_pool = &emission.result_pool;
    let driver = &emission.driver;
    let impls = language.types.iter().map(|ty| {
        let category = &ty.name;
        let visit = format_ident!("Clone{}", category);
        let wrap = format_ident!("Wrap{}", category);
        let root_push = emission.push_task(
            quote! {
                #task_enum::#visit {
                    src: self as *const _,
                    slot: root,
                }
            },
            quote! { operation.state() },
        );
        if emission.checked.is_some() {
            return quote! {
                impl mettail_runtime::CheckedIterativeBinding for #category {
                    #[allow(unreachable_patterns)]
                    fn try_copy_iterative<E>(
                        &self,
                        operation: mettail_runtime::BindingOperation<'_>,
                        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
                    ) -> Result<Self, mettail_runtime::BindingFailure<E>> {
                        let dummy_charges = BINDING_DUMMY_CHARGES.as_ref()
                            .map_err(|_| mettail_runtime::BindingFailure::SizeOverflow)?;
                        // Logical task/result vector headers, regardless of
                        // whether this invocation reuses pooled capacity.
                        mettail_runtime::reserve_binding_parts(0, 2, 0, reserve)?;
                        mettail_runtime::visitor::with_two_pools_or_fallback(
                            &#task_pool,
                            &#result_pool,
                            |stack, results| {
                                let root =
                                    mettail_runtime::append_binding_slots(results, 1, reserve)?;
                                #root_push
                                #driver(stack, results, operation, reserve, dummy_charges)?;
                                let value = mettail_runtime::take_binding_slot(
                                    results,
                                    root,
                                    |value| matches!(value, AnyClonedTerm::#wrap(_)),
                                    reserve,
                                )?;
                                match value {
                                    AnyClonedTerm::#wrap(value) => Ok(value),
                                    _ => unreachable!(
                                        "checked binding: validated root category mismatch"
                                    ),
                                }
                            },
                        )
                    }
                }
            };
        }
        quote! {
            impl Clone for #category {
                #[allow(unreachable_patterns)]
                fn clone(&self) -> Self {
                    mettail_runtime::visitor::with_two_pools_or_fallback(
                        &#task_pool,
                        &#result_pool,
                        |stack, results| {
                            let root = results.len();
                            results.push(None);
                            #root_push
                            #driver(stack, results);
                            match results[root]
                                .take()
                                .expect("iterative clone: root result missing")
                            {
                                AnyClonedTerm::#wrap(value) => value,
                                _ => unreachable!(
                                    "iterative clone: root result category mismatch"
                                ),
                            }
                        },
                    )
                }
            }
        }
    });
    quote! { #(#impls)* }
}

#[cfg(test)]
#[path = "iterative_binding_activation_tests.rs"]
mod activation_tests;

#[cfg(test)]
#[path = "iterative_binding_dispatch_tests.rs"]
mod dispatch_tests;

#[cfg(test)]
#[path = "iterative_clone_bag_tests.rs"]
mod bag_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_variables_and_literals_use_the_existing_leaf_contracts() {
        let language: LanguageDef = syn::parse_str(
            r#"
            name: CheckedLeavesFixture,
            types { Proc ![i64] as Int ![str] as Text },
            terms { PZero . |- "0" : Proc; },
            equations {}, rewrites {},
        "#,
        )
        .expect("variable and native literal fixture");
        let plan = super::super::iterative_drop::select_dummy_plan(&language);
        let receipts = super::super::dummy_receipts::generate_dummy_receipts(&language, &plan)
            .expect("selected native receipts");
        let emission = CloneEmissionNames::checked(&language, &receipts);
        let enum_types: Vec<_> = language
            .types
            .iter()
            .map(|ty| {
                let category = &ty.name;
                let variants: Vec<_> = collect_category_variants(category, &language)
                    .iter()
                    .map(|v| match v {
                        VariantKind::Nullary { label } => quote! { #label },
                        VariantKind::Var { label } => quote! { #label(mettail_runtime::OrdVar) },
                        VariantKind::Literal { label } => {
                            if category == "Int" {
                                quote! { #label(i64) }
                            } else {
                                assert_eq!(category, "Text");
                                quote! { #label(String) }
                            }
                        },
                        _ => panic!("leaf fixture unexpectedly contains a recursive variant"),
                    })
                    .collect();
                quote! { enum #category { #(#variants),* } }
            })
            .collect();
        let proc_var = crate::gen::generate_var_label(&format_ident!("Proc"));
        let literal_label = |category: &str| {
            collect_category_variants(&format_ident!("{}", category), &language)
                .into_iter()
                .find_map(|variant| match variant {
                    VariantKind::Literal { label } => Some(label),
                    _ => None,
                })
                .expect("native literal variant")
        };
        let int_literal = literal_label("Int");
        let text_literal = literal_label("Text");
        let ordinary = generate_iterative_clone(&language);
        let tasks = generate_task_enum(&language, &emission);
        let engine = generate_engine(&language, &emission);
        let impls = generate_impls(&language, &emission);
        let drop = super::super::iterative_drop::generate_iterative_drop(&language);
        let table = receipts.tokens;
        let source = compact(engine.clone());
        assert!(source.contains("CheckedBindingLeaf::try_copy_binding(value,operation,reserve,)"));
        let fixture = quote! {
            #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case)]
            use mettail_runtime::{Binder, BindingFailure, BindingOperation,
                CheckedIterativeBinding, FreeVar, OrdVar, Var};
            #(#enum_types)* #ordinary #tasks #engine #impls #drop #table

            fn exercise<T: CheckedIterativeBinding>(source: &T,
                operation: BindingOperation<'_>, expected: (usize, usize)) -> T {
                let mut trace = Vec::new();
                let result = source.try_copy_iterative(operation, &mut |w, u| {
                    trace.push((w, u)); Ok::<_, &'static str>(())
                }).expect("successful checked leaf traversal");
                assert_eq!(trace.iter().fold((0, 0), |(w,u), (x,y)| (w+x,u+y)), expected);
                for stop in 1..=trace.len() {
                    let mut observed = Vec::new();
                    let failed = source.try_copy_iterative(operation, &mut |w, u| {
                        observed.push((w,u));
                        if observed.len() == stop { Err("cancelled") } else { Ok(()) }
                    });
                    assert!(matches!(failed, Err(BindingFailure::Reservation("cancelled"))));
                    assert_eq!(observed, trace[..stop]);
                }
                for limit in [(expected.0 - 1, expected.1), (expected.0, expected.1 - 1), expected] {
                    let mut used = (0,0);
                    let copied = source.try_copy_iterative(operation, &mut |w, u| {
                        if w > limit.0 - used.0 || u > limit.1 - used.1 { return Err("limit"); }
                        used.0 += w; used.1 += u; Ok(())
                    });
                    if limit == expected { assert!(copied.is_ok()); assert_eq!(used, expected); }
                    else { assert!(matches!(copied, Err(BindingFailure::Reservation("limit")))); }
                }
                result
            }
            fn main() {
                let integer = exercise(&Int::#int_literal(37), BindingOperation::Clone, (18,36));
                assert!(matches!(integer, Int::#int_literal(37)));
                let text = exercise(&Text::#text_literal("λ".into()), BindingOperation::Clone, (21,38));
                assert!(matches!(&text, Text::#text_literal(s) if s == "λ"));
                let name: FreeVar<String> = FreeVar::fresh_named("λ");
                let mut selected = name.clone(); selected.pretty_name = Some("selected".into());
                let roster = [Binder(selected.clone())];
                let original = Proc::#proc_var(OrdVar(Var::Free(name.clone())));
                let clone = exercise(&original, BindingOperation::Clone, (22,38));
                assert!(matches!(&clone, Proc::#proc_var(OrdVar(Var::Free(v)))
                    if v.unique_id == name.unique_id && v.pretty_name == name.pretty_name));
                let closed = exercise(&original, BindingOperation::Close {
                    state: moniker::ScopeState::new(), binders: &roster,
                }, (23,38));
                assert!(matches!(&closed, Proc::#proc_var(OrdVar(Var::Bound(v)))
                    if v.scope == moniker::ScopeOffset(0) && v.binder == moniker::BinderIndex(0)
                    && v.pretty_name.as_deref() == Some("λ")));
                let opened = exercise(&closed, BindingOperation::Open {
                    state: moniker::ScopeState::new(), binders: &roster,
                }, (28,44));
                assert!(matches!(&opened, Proc::#proc_var(OrdVar(Var::Free(v)))
                    if v.unique_id == selected.unique_id && v.pretty_name == selected.pretty_name));
                assert!(matches!(&original, Proc::#proc_var(OrdVar(Var::Free(v)))
                    if v.pretty_name.as_deref() == Some("λ")));
                println!("checked generated variable/literal semantics and all refusal boundaries verified");
            }
        };
        syn::parse2::<syn::File>(fixture.clone()).expect("generated checked leaf fixture syntax");
        if std::env::var_os("METTAIL_CAPTURE_CHECKED_BINDING").is_some() {
            let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../target/verification/clone-emitter");
            std::fs::create_dir_all(&directory).expect("create checked leaf fixture directory");
            std::fs::write(directory.join("checked-leaves.rs"), fixture.to_string())
                .expect("write generated variable/literal fixture");
        }
    }

    #[test]
    fn checked_nullary_uses_the_shared_driver_and_prepaid_publication() {
        let language: LanguageDef = syn::parse_str(
            r#"
            name: CheckedLeafFixture,
            types { data Atom },
            terms { Unit . |- "unit" : Atom; },
            equations {}, rewrites {},
        "#,
        )
        .expect("closed nullary category");
        let plan = super::super::iterative_drop::select_dummy_plan(&language);
        let receipts = super::super::dummy_receipts::generate_dummy_receipts(&language, &plan)
            .expect("selected nullary receipt");
        let checked = CloneEmissionNames::checked(&language, &receipts);
        assert_eq!(
            compact(
                checked
                    .dummy_charge(&format_ident!("Atom"))
                    .expect("exact selected index")
            ),
            "dummy_charges[0usize]"
        );
        assert!(checked.dummy_charge(&format_ident!("Missing")).is_err());
        let ordinary = generate_iterative_clone(&language);
        let tasks = generate_task_enum(&language, &checked);
        let engine = generate_engine(&language, &checked);
        let impls = generate_impls(&language, &checked);
        let checked_source = compact(quote! { #tasks #engine #impls });
        assert!(checked_source.contains("reserve_binding_parts(6,2,0,reserve)?"));
        assert!(checked_source.contains("write_binding_slot("));
        assert_eq!(
            checked_source
                .matches("BINDING_DUMMY_CHARGES.as_ref()")
                .count(),
            1
        );
        assert!(!checked_source.contains("replacement_charge()"));
        let drop = super::super::iterative_drop::generate_iterative_drop(&language);
        let table = receipts.tokens;
        let fixture = quote! {
            #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case)]
            mod valid {
                use mettail_runtime::{BindingFailure, BindingOperation, CheckedIterativeBinding};
                enum Atom { Unit }
                #ordinary #tasks #engine #impls #drop #table
                pub fn verify() {
                    let source = Atom::Unit;
                    // Each selector pays selection/retention, call and payload match.
                    let expected = [(0, 8), (1, 4), (1, 4), (1, 0),
                        (3, 4), (3, 4), (6, 8), (1, 0), (1, 0)];
                    let mut calls = Vec::new();
                    let copied = source.try_copy_iterative(BindingOperation::Clone,
                        &mut |work, units| {
                            calls.push((work, units));
                            Ok::<_, usize>(())
                        }).expect("paid nullary output");
                    assert!(matches!(copied, Atom::Unit));
                    assert_eq!(calls, expected);
                    drop(copied);
                    for stop in 1..=expected.len() {
                        let mut calls = Vec::new();
                        let result = source.try_copy_iterative(BindingOperation::Clone,
                            &mut |work, units| {
                                calls.push((work, units));
                                if calls.len() == stop { Err(stop) } else { Ok(()) }
                            });
                        assert!(matches!(result, Err(BindingFailure::Reservation(n)) if n == stop));
                        assert_eq!(calls, expected[..stop]);
                        // Both actual generated pools must be empty after
                        // refusal, including publication and final take.
                        CHECKED_BINDING_TASK_POOL.with(|pool| {
                            let tasks = pool.take();
                            assert!(tasks.is_empty());
                            pool.set(tasks);
                        });
                        CHECKED_BINDING_RESULT_POOL.with(|pool| {
                            let results = pool.take();
                            assert!(results.is_empty());
                            pool.set(results);
                        });
                        assert!(matches!(source, Atom::Unit));
                    }
                }
            }
            mod refused_table {
                use mettail_runtime::{BindingFailure, BindingOperation, CheckedIterativeBinding};
                enum Atom { Unit }
                #ordinary #tasks #engine #impls #drop
                static BINDING_DUMMY_CHARGES: Result<
                    [mettail_runtime::binding_receipt::BindingCharge; 1],
                    mettail_runtime::binding_receipt::DummyChargeError,
                > = Err(mettail_runtime::binding_receipt::DummyChargeError::Projection(
                    mettail_runtime::binding_receipt::ChargeOverflow::RetentionUnits));
                pub fn verify() {
                    let mut calls = 0;
                    let result = Atom::Unit.try_copy_iterative(BindingOperation::Clone,
                        &mut |_, _| { calls += 1; Ok::<_, ()>(()) });
                    assert!(matches!(result, Err(BindingFailure::SizeOverflow)));
                    assert_eq!(calls, 0);
                }
            }
            fn main() {
                valid::verify();
                refused_table::verify();
                println!("checked generated nullary admission, cancellation and table refusal verified");
            }
        };
        syn::parse2::<syn::File>(fixture.clone()).expect("checked fixture Rust items");
        if std::env::var_os("METTAIL_CAPTURE_CHECKED_BINDING").is_some() {
            let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../target/verification/clone-emitter");
            std::fs::create_dir_all(&directory).expect("create checked fixture directory");
            std::fs::write(directory.join("checked-leaf.rs"), fixture.to_string())
                .expect("write actual checked emitter fixture");
        }
    }

    #[test]
    fn checked_scalar_fields_preserve_sharing_binding_and_partial_cleanup() {
        let language: LanguageDef = syn::parse_str(
            r#"
            name: CheckedScalarFixture,
            types { Proc ![str] as Text ![Vec<Proc>] as List },
            terms {
                PZero . |- "0" : Proc;
                PUnary . child:Proc |- "unary" child : Proc;
                PPair . left:Proc, right:Proc |- "pair" left right : Proc;
                PMaybe . *opt(child:Proc) |- "maybe" *opt(child) : Proc;
                PText . text:Text |- "text" text : Proc;
                PToken . |- token@Word : Proc;
                PGuest . |- *flt(node, Open, Close) : Proc;
                PMixed . child:Proc, ?guard:Guard
                    |- before@Word child *flt(node, Open, Close) guard after@Word : Proc;
                POptional . *opt(child:Proc, ?guard:Guard)
                    |- prefix@Word *opt(before@Word child *flt(node, Open, Close) guard) : Proc;
                PSingle . pre:Proc, ^x.body:[Proc -> Proc]
                    |- "single" pre x body : Proc;
                PMulti . ^[xs].body:[Proc* -> Proc] |- "multi" xs body : Proc;
                PGuardScope . ?guard:Guard, ^x.body:[Proc -> Proc]
                    |- "guardScope" guard x body : Proc;
                PTextScope . ^x.body:[Proc -> Text] |- "textScope" x body : Proc;
                PTwoVec . first:Vec(Proc), second:Vec(Proc) |- "twoVec" first second : Proc;
                PVecMixed . children:Vec(Proc), tail:Proc, ?guard:Guard
                    |- prefix@Word children tail guard : Proc;
                PVecScope . entries:Vec(Proc), ^[xs].body:[Proc* -> Proc]
                    |- "vecScope" entries xs body : Proc;
                PVector . entries:Vec(Proc) |- "vector" entries : Proc;
                PList . entries:List |- "list" entries : Proc;
            },
            equations {}, rewrites {},
        "#,
        )
        .expect("scalar category field fixture");
        let proc_variants = collect_category_variants(&format_ident!("Proc"), &language);
        assert!(proc_variants.iter().any(|variant| matches!(variant,
            VariantKind::Collection { label, coll_type: CollectionType::Vec, .. }
                if label == "PVector")));
        let list_label = collect_category_variants(&format_ident!("List"), &language)
            .into_iter()
            .find_map(|variant| match variant {
                VariantKind::CollectionLiteral {
                    label, coll_type: CollectionType::Vec, ..
                } => Some(label),
                _ => None,
            })
            .expect("actual category-vector literal");
        let plan = super::super::iterative_drop::select_dummy_plan(&language);
        let receipts = super::super::dummy_receipts::generate_dummy_receipts(&language, &plan)
            .expect("selected scalar fixture receipts");
        let checked = CloneEmissionNames::checked(&language, &receipts);
        // Use the production enum layout, not an enum reconstructed from the
        // term-operation classifier. Omit unrelated derives in this focused
        // fixture; field names, order and Rust payload types remain unchanged.
        let declarations =
            syn::parse2::<syn::File>(crate::gen::types::enums::generate_ast_enums(&language))
                .expect("production enum declarations");
        let enum_types: Vec<_> = declarations
            .items
            .into_iter()
            .filter_map(|item| {
                if let syn::Item::Enum(mut item) = item {
                    if language.types.iter().any(|ty| ty.name == item.ident) {
                        item.attrs.clear();
                        return Some(item);
                    }
                }
                None
            })
            .collect();
        assert_eq!(enum_types.len(), language.types.len());
        let var = crate::gen::generate_var_label(&format_ident!("Proc"));
        let text_label = collect_category_variants(&format_ident!("Text"), &language)
            .into_iter()
            .find_map(|v| match v {
                VariantKind::Literal { label } => Some(label),
                _ => None,
            })
            .expect("text literal");
        let ordinary = generate_iterative_clone(&language);
        let tasks = generate_task_enum(&language, &checked);
        let engine = generate_engine(&language, &checked);
        let impls = generate_impls(&language, &checked);
        let drop = super::super::iterative_drop::generate_iterative_drop(&language);
        let table = receipts.tokens;
        let fixture = quote! {
            #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case)]
            use std::sync::Arc;
            use mettail_runtime::{Binder, BindingFailure, BindingOperation,
                CheckedIterativeBinding, FreeVar, OrdVar, Scope, Var};
            #(#enum_types)* #ordinary #tasks #engine #impls #drop #table

            fn pools_empty() {
                CHECKED_BINDING_TASK_POOL.with(|pool| {
                    let value = pool.take(); assert!(value.is_empty()); pool.set(value);
                });
                CHECKED_BINDING_RESULT_POOL.with(|pool| {
                    let value = pool.take(); assert!(value.is_empty()); pool.set(value);
                });
            }
            fn exercise<T: CheckedIterativeBinding>(source: &T, operation: BindingOperation<'_>) -> (T, (usize,usize)) {
                let mut trace = Vec::new();
                let result = source.try_copy_iterative(operation, &mut |w,u| {
                    trace.push((w,u)); Ok::<_, usize>(())
                }).expect("successful scalar copy");
                let total = trace.iter().fold((0,0), |(w,u),(x,y)| (w+x,u+y));
                for stop in 1..=trace.len() {
                    let mut observed = Vec::new();
                    let failed = source.try_copy_iterative(operation, &mut |w,u| {
                        observed.push((w,u));
                        if observed.len() == stop { Err(stop) } else { Ok(()) }
                    });
                    assert!(matches!(failed, Err(BindingFailure::Reservation(n)) if n == stop));
                    assert_eq!(observed, trace[..stop]); pools_empty();
                }
                for limit in [(total.0-1,total.1),(total.0,total.1-1),total] {
                    let mut used = (0,0);
                    let result = source.try_copy_iterative(operation, &mut |w,u| {
                        if w > limit.0-used.0 || u > limit.1-used.1 { return Err(()); }
                        used.0 += w; used.1 += u; Ok(())
                    });
                    assert_eq!(result.is_ok(), limit == total); pools_empty();
                }
                (result, total)
            }
            fn check_bound(value: &Proc, depth: u32) {
                assert!(matches!(value, Proc::#var(OrdVar(Var::Bound(v)))
                    if v.scope == moniker::ScopeOffset(depth) && v.binder == moniker::BinderIndex(0)));
            }
            fn main() {
                let close = BindingOperation::Close { state: moniker::ScopeState::new(), binders: &[] };
                let unary = Proc::PUnary(Arc::new(Proc::PZero));
                // Shallow Clone visits only the unary node (+6W/8units).
                // Close visits both nodes and assembles the unary (+15W/20units).
                assert_eq!(exercise(&unary, BindingOperation::Clone).1, (29,48));
                assert_eq!(exercise(&unary, close).1, (52,84));
                for present in [false,true] {
                    let maybe = Proc::PMaybe(present.then(|| Arc::new(Proc::PZero)));
                    for operation in [BindingOperation::Clone, close] {
                        let (copied,_) = exercise(&maybe, operation);
                        assert!(matches!(&copied, Proc::PMaybe(value) if value.is_some() == present));
                    }
                }
                let text = Proc::PText(Arc::new(Text::#text_label("λ雪".into())));
                let (copied,_) = exercise(&text, close);
                assert!(matches!(&copied, Proc::PText(value)
                    if matches!(value.as_ref(), Text::#text_label(s) if s == "λ雪")));
                let name = FreeVar::fresh_named("bound");
                let child = Arc::new(Proc::#var(OrdVar(Var::Free(name.clone()))));
                let pair = Proc::PPair(child.clone(), child.clone());
                let (copied,_) = exercise(&pair, BindingOperation::Clone);
                assert!(matches!(&copied, Proc::PPair(a,b)
                    if Arc::ptr_eq(a,&child) && Arc::ptr_eq(b,&child)));
                let roster = [Binder(name.clone())];
                let mut guest = mettail_runtime::FltNode::new("guest".into(), "Term".into(),
                    "a${x}// literal".into(), vec![mettail_runtime::FltHole {
                        id: mettail_runtime::FltHoleId(0), name: "x".into(), category: None,
                        first_occurrence: mettail_runtime::FltSourceRange::new(1,5),
                    }], 0).expect("structural FLT fixture");
                guest.selector = OrdVar(Var::Free(name.clone()));
                let guest = Arc::new(guest);
                let predicate = mettail_runtime::BehavioralPred::RelationQuery {
                    relation_name: "relation".into(),
                    args: vec![mettail_runtime::PredArg::Var("bound".into())], negated: false,
                };
                let mixed = Proc::PMixed("first".into(), child.clone(), guest.clone(),
                    predicate.clone(), "last".into());
                let (cloned,_) = exercise(&mixed,BindingOperation::Clone);
                let Proc::PMixed(first,term,payload,pred,last) = &cloned else { panic!("mixed clone"); };
                assert_eq!((first.as_str(),last.as_str()),("first","last"));
                assert!(Arc::ptr_eq(term,&child)); assert!(Arc::ptr_eq(payload,&guest));
                assert_eq!(pred,&predicate);
                for input in [Proc::PToken(String::new()),Proc::PGuest(guest.clone()),
                    Proc::POptional("prefix".into(),None,None,None,None)] {
                    exercise(&input,BindingOperation::Clone);
                    exercise(&input,BindingOperation::Close { state: moniker::ScopeState::new(), binders: &roster });
                }
                let some_empty = Proc::POptional("prefix".into(),Some(String::new()),None,None,None);
                let (copied,_) = exercise(&some_empty,BindingOperation::Clone);
                assert!(matches!(&copied,Proc::POptional(prefix,Some(s),None,None,None)
                    if prefix == "prefix" && s.is_empty()));
                for state in [moniker::ScopeState::new(), moniker::ScopeState::new().incr().incr()] {
                    let (closed_mixed,_) = exercise(&mixed,BindingOperation::Close { state, binders: &roster });
                    let Proc::PMixed(first,term,payload,pred,last) = &closed_mixed else { panic!("closed mixed"); };
                    assert_eq!((first.as_str(),last.as_str()),("first","last"));
                    check_bound(term,state.depth().0);
                    assert!(matches!(&payload.selector.0, Var::Bound(v)
                        if v.scope == state.depth() && v.binder == moniker::BinderIndex(0)));
                    let mut expected = guest.as_ref().clone(); expected.selector = payload.selector.clone();
                    assert_eq!(payload.as_ref(),&expected); assert_eq!(pred,&predicate);
                    let (opened_mixed,_) = exercise(&closed_mixed,BindingOperation::Open { state, binders: &roster });
                    let Proc::PMixed(_,_,payload,_,_) = &opened_mixed else { panic!("opened mixed"); };
                    assert_eq!(payload.as_ref(),guest.as_ref());
                    assert!(matches!(&payload.selector.0, Var::Free(v) if v.unique_id == name.unique_id));
                    let optional_mixed = Proc::POptional("prefix".into(),Some(String::new()),Some(child.clone()),
                        Some(guest.clone()),Some(predicate.clone()));
                    let (optional_closed,_) = exercise(&optional_mixed,
                        BindingOperation::Close { state, binders: &roster });
                    let Proc::POptional(prefix,Some(text),Some(term),Some(payload),Some(pred)) = &optional_closed
                        else { panic!("optional mixed presence"); };
                    assert_eq!(prefix,"prefix");
                    assert!(text.is_empty()); check_bound(term,state.depth().0);
                    assert!(matches!(&payload.selector.0, Var::Bound(v) if v.scope == state.depth()));
                    assert_eq!(pred,&predicate);
                    let optional = Proc::PMaybe(Some(child.clone()));
                    let (closed_optional,_) = exercise(&optional,
                        BindingOperation::Close { state, binders: &roster });
                    let Proc::PMaybe(Some(value)) = &closed_optional else { panic!("optional shape"); };
                    check_bound(value,state.depth().0);
                    let (closed,_) = exercise(&pair, BindingOperation::Close { state, binders: &roster });
                    let Proc::PPair(left,right) = &closed else { panic!("pair shape"); };
                    assert!(!Arc::ptr_eq(left,right));
                    check_bound(left,state.depth().0); check_bound(right,state.depth().0);
                    let (opened,_) = exercise(&closed, BindingOperation::Open { state, binders: &roster });
                    let Proc::PPair(left,right) = &opened else { panic!("opened pair shape"); };
                    for value in [left,right] {
                        assert!(matches!(value.as_ref(), Proc::#var(OrdVar(Var::Free(v)))
                            if v.unique_id == name.unique_id));
                    }
                }
                let pattern = Binder(name.clone());
                let single = Proc::PSingle(child.clone(),
                    Scope::from_parts_unsafe(pattern.clone(),child.clone()));
                let guarded = Proc::PGuardScope(predicate.clone(),
                    Scope::from_parts_unsafe(pattern.clone(),child.clone()));
                let text_body = Arc::new(Text::#text_label("body category".into()));
                let text_scope = Proc::PTextScope(Scope::from_parts_unsafe(pattern.clone(),text_body.clone()));
                for source in [
                    Proc::MApplyProc(child.clone(),vec![]),
                    Proc::MApplyProc(child.clone(),vec![child.as_ref().clone(),Proc::PZero]),
                    Proc::MApplyText(child.clone(),vec![Text::#text_label("first".into()),Text::#text_label("second".into())]),
                    Proc::PTwoVec(vec![Proc::PZero],vec![child.as_ref().clone(),Proc::PZero]),
                ] {
                    for operation in [BindingOperation::Clone,
                        BindingOperation::Close {state:moniker::ScopeState::new(),binders:&roster}] {
                        let (copied,_) = exercise(&source,operation);
                        match (&source,&copied) {
                            (Proc::MApplyProc(_,before),Proc::MApplyProc(function,after)) => {
                                assert_eq!(before.len(),after.len());
                                if !after.is_empty() {
                                    assert!(matches!(after[1],Proc::PZero));
                                    if matches!(operation,BindingOperation::Clone) {
                                        assert!(matches!(&after[0],Proc::#var(OrdVar(Var::Free(v))) if v.unique_id==name.unique_id));
                                    } else {check_bound(&after[0],0);}
                                }
                                if matches!(operation,BindingOperation::Clone) {assert!(Arc::ptr_eq(function,&child));}
                                else {check_bound(function,0);}
                            },
                            (Proc::MApplyText(..),Proc::MApplyText(function,after)) => {
                                assert_eq!(after.len(),2);
                                for (term,expected) in after.iter().zip(["first","second"]) {
                                    assert!(matches!(term,Text::#text_label(text) if text==expected));
                                }
                                if matches!(operation,BindingOperation::Clone) {assert!(Arc::ptr_eq(function,&child));}
                                else {check_bound(function,0);}
                            },
                            (Proc::PTwoVec(..),Proc::PTwoVec(first,second)) => {
                                assert_eq!(first.len(),1);assert_eq!(second.len(),2);
                                assert!(matches!(first[0],Proc::PZero));assert!(matches!(second[1],Proc::PZero));
                                if matches!(operation,BindingOperation::Clone) {
                                    assert!(matches!(&second[0],Proc::#var(OrdVar(Var::Free(v))) if v.unique_id==name.unique_id));
                                } else {check_bound(&second[0],0);}
                            },
                            _ => panic!("vector constructor preserved"),
                        }
                    }
                }
                let vector_mixed=Proc::PVecMixed("vector prefix".into(),
                    vec![child.as_ref().clone(),Proc::PZero],child.clone(),predicate.clone());
                let vector_scope=Proc::PVecScope(vec![child.as_ref().clone(),Proc::PZero],
                    Scope::from_parts_unsafe(vec![pattern.clone()],child.clone()));
                for values in [vec![],vec![child.as_ref().clone(),Proc::PZero,child.as_ref().clone()]] {
                    let expected_len=values.len();
                    let direct = Proc::PVector(values.clone());
                    let literal = Proc::PList(Arc::new(List::#list_label(values)));
                    let Proc::PList(list) = &literal else {panic!("source list");};
                    let (copied,_) = exercise(list.as_ref(),BindingOperation::Clone);
                    let List::#list_label(entries) = &copied else {panic!("root list clone");};
                    assert_eq!(entries.len(),expected_len);
                    for entry in entries.iter().step_by(2) {
                        assert!(matches!(entry,Proc::#var(OrdVar(Var::Free(v)))
                            if v.unique_id==name.unique_id && v.pretty_name==name.pretty_name));
                    }
                    for source in [&direct,&literal] {
                        for state in [moniker::ScopeState::new(),moniker::ScopeState::new().incr().incr()] {
                            let (cloned,_) = exercise(source,BindingOperation::Clone);
                            if let (Proc::PList(before),Proc::PList(after)) = (source,&cloned) {
                                assert!(Arc::ptr_eq(before,after));
                            }
                            let (closed,_) = exercise(source,BindingOperation::Close {state,binders:&roster});
                            let entries = match &closed {
                                Proc::PVector(entries) => entries,
                                Proc::PList(list) => match list.as_ref() {
                                    List::#list_label(entries) => entries,
                                    _ => panic!("literal vector variant"),
                                },
                                _ => panic!("vector surface variant"),
                            };
                            assert_eq!(entries.len(),expected_len);
                            if !entries.is_empty() {
                                assert_eq!(entries.len(),3);assert!(matches!(entries[1],Proc::PZero));
                                check_bound(&entries[0],state.depth().0);check_bound(&entries[2],state.depth().0);
                            }
                            let (opened,_) = exercise(&closed,BindingOperation::Open {state,binders:&roster});
                            let entries = match &opened {
                                Proc::PVector(entries) => entries,
                                Proc::PList(list) => match list.as_ref() {
                                    List::#list_label(entries) => entries,
                                    _ => panic!("opened literal vector"),
                                },
                                _ => panic!("opened vector surface"),
                            };
                            assert_eq!(entries.len(),expected_len);
                            for entry in entries.iter().step_by(2) {
                                assert!(matches!(entry,Proc::#var(OrdVar(Var::Free(v)))
                                    if v.unique_id==name.unique_id && v.pretty_name==name.pretty_name));
                            }
                        }
                    }
                }
                for state in [moniker::ScopeState::new(),moniker::ScopeState::new().incr().incr()] {
                    for operation in [BindingOperation::Clone,BindingOperation::Close {state,binders:&roster}] {
                        let (copied,_) = exercise(&vector_mixed,operation);
                        let Proc::PVecMixed(prefix,values,tail,pred) = &copied else {panic!("mixed vector");};
                        assert_eq!(prefix,"vector prefix"); assert_eq!(pred,&predicate);
                        assert_eq!(values.len(),2); assert!(matches!(values[1],Proc::PZero));
                        if matches!(operation,BindingOperation::Clone) {
                            assert!(Arc::ptr_eq(tail,&child));
                            assert!(matches!(&values[0],Proc::#var(OrdVar(Var::Free(v)))
                                if v.unique_id==name.unique_id && v.pretty_name==name.pretty_name));
                        } else {check_bound(&values[0],state.depth().0);check_bound(tail,state.depth().0);}
                        let (copied,_) = exercise(&vector_scope,operation);
                        let Proc::PVecScope(values,scope) = &copied else {panic!("vector scope");};
                        assert_eq!(values.len(),2); assert!(matches!(values[1],Proc::PZero));
                        assert_eq!(scope.unsafe_pattern()[0].0.unique_id,pattern.0.unique_id);
                        if matches!(operation,BindingOperation::Clone) {
                            assert!(Arc::ptr_eq(scope.unsafe_body(),&child));
                            assert!(matches!(&values[0],Proc::#var(OrdVar(Var::Free(v))) if v.unique_id==name.unique_id));
                        } else {
                            check_bound(&values[0],state.depth().0);
                            check_bound(scope.unsafe_body(),state.depth().0+1);
                            let (opened,_) = exercise(&copied,BindingOperation::Open {state,binders:&roster});
                            let Proc::PVecScope(values,scope) = &opened else {panic!("opened vector scope");};
                            for term in [&values[0],scope.unsafe_body().as_ref()] {
                                assert!(matches!(term,Proc::#var(OrdVar(Var::Free(v))) if v.unique_id==name.unique_id));
                            }
                        }
                    }
                }
                for operation in [BindingOperation::Clone,
                    BindingOperation::Close { state:moniker::ScopeState::new(),binders:&roster }] {
                    let (copied,_) = exercise(&text_scope,operation);
                    let Proc::PTextScope(scope) = &copied else { panic!("cross-category scope"); };
                    assert_eq!(scope.unsafe_pattern().0.unique_id,pattern.0.unique_id);
                    assert!(matches!(scope.unsafe_body().as_ref(),Text::#text_label(text) if text=="body category"));
                    if matches!(operation,BindingOperation::Clone) {
                        assert!(Arc::ptr_eq(scope.unsafe_body(),&text_body));
                    } else {
                        assert!(!Arc::ptr_eq(scope.unsafe_body(),&text_body));
                    }
                }
                let (cloned,_) = exercise(&single,BindingOperation::Clone);
                let Proc::PSingle(pre,scope) = &cloned else { panic!("single clone"); };
                assert!(Arc::ptr_eq(pre,&child));
                assert!(Arc::ptr_eq(scope.unsafe_body(),&child));
                assert_eq!(scope.unsafe_pattern().0.unique_id,pattern.0.unique_id);
                assert_eq!(scope.unsafe_pattern().0.pretty_name,pattern.0.pretty_name);
                for state in [moniker::ScopeState::new(),moniker::ScopeState::new().incr().incr()] {
                    let close = BindingOperation::Close { state, binders:&roster };
                    let open = BindingOperation::Open { state, binders:&roster };
                    let (closed,_) = exercise(&single,close);
                    let Proc::PSingle(pre,scope) = &closed else { panic!("single close"); };
                    check_bound(pre,state.depth().0);
                    check_bound(scope.unsafe_body(),state.depth().0+1);
                    assert_eq!(scope.unsafe_pattern().0.unique_id,pattern.0.unique_id);
                    assert_eq!(scope.unsafe_pattern().0.pretty_name,pattern.0.pretty_name);
                    let (opened,_) = exercise(&closed,open);
                    let Proc::PSingle(pre,scope) = &opened else { panic!("single open"); };
                    for term in [pre,scope.unsafe_body()] {
                        assert!(matches!(term.as_ref(),Proc::#var(OrdVar(Var::Free(v)))
                            if v.unique_id==name.unique_id && v.pretty_name==name.pretty_name));
                    }
                    let (guarded,_) = exercise(&guarded,close);
                    let Proc::PGuardScope(pred,scope) = &guarded else { panic!("scope predicate"); };
                    assert_eq!(pred,&predicate); check_bound(scope.unsafe_body(),state.depth().0+1);
                    let mut duplicate = name.clone(); duplicate.pretty_name=Some("duplicate hint".into());
                    let same_name = FreeVar::fresh_named("bound");
                    assert_ne!(same_name.unique_id,name.unique_id);
                    for pattern in [vec![],vec![Binder(name.clone())],
                        vec![Binder(duplicate),Binder(same_name),Binder(name.clone())]] {
                        let multi = Proc::PMulti(Scope::from_parts_unsafe(pattern.clone(),child.clone()));
                        for operation in [BindingOperation::Clone,close] {
                            let (copied,_) = exercise(&multi,operation);
                            let Proc::PMulti(scope) = &copied else { panic!("multi scope"); };
                            assert_eq!(scope.unsafe_pattern().len(),pattern.len());
                            for (a,b) in scope.unsafe_pattern().iter().zip(&pattern) {
                                assert_eq!(a.0.unique_id,b.0.unique_id);
                                assert_eq!(a.0.pretty_name,b.0.pretty_name);
                            }
                            match operation {
                                BindingOperation::Clone => assert!(Arc::ptr_eq(scope.unsafe_body(),&child)),
                                _ => {
                                    check_bound(scope.unsafe_body(),state.depth().0+1);
                                    let (opened,_) = exercise(&copied,open);
                                    let Proc::PMulti(scope) = &opened else { panic!("multi open"); };
                                    assert!(matches!(scope.unsafe_body().as_ref(),Proc::#var(OrdVar(Var::Free(v)))
                                        if v.unique_id==name.unique_id && v.pretty_name==name.pretty_name));
                                },
                            }
                        }
                    }
                    let nested = Proc::PMulti(Scope::from_parts_unsafe(vec![],Arc::new(single.clone())));
                    let (closed,_) = exercise(&nested,close);
                    let Proc::PMulti(outer) = &closed else { panic!("outer scope"); };
                    let Proc::PSingle(pre,inner) = outer.unsafe_body().as_ref() else { panic!("inner scope"); };
                    check_bound(pre,state.depth().0+1);
                    check_bound(inner.unsafe_body(),state.depth().0+2);
                }
                assert!(matches!(child.as_ref(), Proc::#var(OrdVar(Var::Free(v)))
                    if v.unique_id == name.unique_id));
                std::thread::Builder::new().stack_size(256*1024).spawn(|| {
                    let mut source = Proc::PZero;
                    for depth in 0..20_000 {
                        source = if depth % 2 == 0 { Proc::PUnary(Arc::new(source)) }
                            else { Proc::PMaybe(Some(Arc::new(source))) };
                    }
                    let operation = BindingOperation::Close {
                        state: moniker::ScopeState::new(), binders: &[],
                    };
                    let mut calls = 0;
                    let copied = source.try_copy_iterative(operation, &mut |_,_| {
                        calls += 1; Ok::<_, ()>(())
                    }).expect("deep checked binding");
                    let mut cursor = &copied;
                    for _ in 0..20_000 {
                        cursor = match cursor {
                            Proc::PUnary(child) | Proc::PMaybe(Some(child)) => child,
                            _ => panic!("deep spine shape"),
                        };
                    }
                    assert!(matches!(cursor, Proc::PZero));
                    drop(copied);
                    for stop in [calls/2, calls-3, calls] {
                        let mut observed = 0;
                        let refused = source.try_copy_iterative(operation, &mut |_,_| {
                            observed += 1;
                            if observed == stop { Err(()) } else { Ok(()) }
                        });
                        assert!(matches!(refused, Err(BindingFailure::Reservation(()))));
                        pools_empty();
                    }
                    drop(source); pools_empty();
                    let mut source = Proc::PZero;
                    for _ in 0..20_000 {source=Proc::PTwoVec(vec![source],vec![]);}
                    for operation in [BindingOperation::Clone,
                        BindingOperation::Close {state:moniker::ScopeState::new(),binders:&[]}] {
                        let mut calls=0;
                        let copied=source.try_copy_iterative(operation,&mut |_,_| {
                            calls+=1;Ok::<_,()>(())
                        }).expect("deep owned vector binding");
                        let mut cursor=&copied;
                        for _ in 0..20_000 {
                            let Proc::PTwoVec(first,second)=cursor else {panic!("vector spine");};
                            assert_eq!(first.len(),1);assert!(second.is_empty());cursor=&first[0];
                        }
                        assert!(matches!(cursor,Proc::PZero));drop(copied);
                        for stop in [calls/2,calls-3,calls] {
                            let mut observed=0;
                            let failed=source.try_copy_iterative(operation,&mut |_,_| {
                                observed+=1;if observed==stop {Err(())} else {Ok(())}
                            });
                            assert!(matches!(failed,Err(BindingFailure::Reservation(()))));pools_empty();
                        }
                    }
                    drop(source);pools_empty();
                    for literal_surface in [false,true] {
                        let mut source=Proc::PZero;
                        for _ in 0..20_000 {
                            source=if literal_surface {
                                Proc::PList(Arc::new(List::#list_label(vec![source])))
                            } else {Proc::PVector(vec![source])};
                        }
                        let operation=BindingOperation::Close {state:moniker::ScopeState::new(),binders:&[]};
                        let mut calls=0;
                        let copied=source.try_copy_iterative(operation,&mut |_,_| {
                            calls+=1;Ok::<_,()>(())
                        }).expect("deep vector surface");
                        let mut cursor=&copied;
                        for _ in 0..20_000 {
                            let entries=match cursor {
                                Proc::PVector(entries) => entries,
                                Proc::PList(list) => match list.as_ref() {
                                    List::#list_label(entries) => entries,
                                    _ => panic!("deep literal vector"),
                                },
                                _ => panic!("deep vector surface"),
                            };
                            assert_eq!(entries.len(),1);cursor=&entries[0];
                        }
                        assert!(matches!(cursor,Proc::PZero));drop(copied);
                        for stop in [calls/2,calls-3,calls] {
                            let mut observed=0;
                            let failed=source.try_copy_iterative(operation,&mut |_,_| {
                                observed+=1;if observed==stop {Err(())} else {Ok(())}
                            });
                            assert!(matches!(failed,Err(BindingFailure::Reservation(()))));pools_empty();
                        }
                        drop(source);pools_empty();
                    }
                    let name = FreeVar::fresh_named("deep");
                    let roster = [Binder(name.clone())];
                    let mut source = Proc::#var(OrdVar(Var::Free(name)));
                    for _ in 0..20_000 {
                        source = Proc::PMulti(Scope::from_parts_unsafe(vec![],Arc::new(source)));
                    }
                    let operation = BindingOperation::Close { state:moniker::ScopeState::new(),binders:&roster };
                    let mut calls = 0;
                    let copied = source.try_copy_iterative(operation,&mut |_,_| {
                        calls+=1; Ok::<_,()>(())
                    }).expect("deep scope binding");
                    let mut cursor = &copied;
                    for _ in 0..20_000 {
                        let Proc::PMulti(scope) = cursor else { panic!("scope spine"); };
                        assert!(scope.unsafe_pattern().is_empty()); cursor=scope.unsafe_body();
                    }
                    check_bound(cursor,20_000); drop(copied);
                    for stop in [calls/2,calls-3,calls] {
                        let mut observed=0;
                        let failed=source.try_copy_iterative(operation,&mut |_,_| {
                            observed+=1; if observed==stop {Err(())} else {Ok(())}
                        });
                        assert!(matches!(failed,Err(BindingFailure::Reservation(())))); pools_empty();
                    }
                    drop(source); pools_empty();
                }).expect("spawn scalar small-stack worker").join().expect("scalar small-stack worker");
                println!("checked category/native fields, FLT binding, refusal and 20k-depth cleanup verified");
            }
        };
        syn::parse2::<syn::File>(fixture.clone()).expect("checked scalar generated Rust syntax");
        if std::env::var_os("METTAIL_CAPTURE_CHECKED_BINDING").is_some() {
            let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../target/verification/clone-emitter");
            std::fs::create_dir_all(&directory).expect("create scalar fixture directory");
            std::fs::write(directory.join("checked-scalars.rs"), fixture.to_string())
                .expect("write actual checked scalar fixture");
        }
    }

    fn compact(tokens: TokenStream) -> String {
        tokens.to_string().split_whitespace().collect()
    }

    #[test]
    fn ordinary_clone_expansions_remain_valid_rust_items() {
        for (name, language) in [
            ("collections", crate::gen::collection_literal_language_for_tests()),
            ("singleton", crate::gen::singleton_collection_language_for_tests()),
        ] {
            let expansion = generate_iterative_clone(&language);
            syn::parse2::<syn::File>(expansion.clone())
                .expect("clone expansion parses as Rust items");
            // Optional exact before/after artifacts for emitter refactoring.
            // Default test execution needs no environment setting or writes.
            if let Ok(phase) = std::env::var("METTAIL_CLONE_EXPANSION_PHASE") {
                assert!(matches!(phase.as_str(), "before" | "after"));
                let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../target/verification/clone-emitter")
                    .join(phase);
                std::fs::create_dir_all(&directory)
                    .expect("create target-local expansion directory");
                std::fs::write(directory.join(format!("{name}.tokens")), expansion.to_string())
                    .expect("write exact clone expansion artifact");
            }
        }
    }

    #[test]
    fn every_category_uses_one_shared_clone_driver() {
        let language = crate::gen::collection_literal_language_for_tests();
        let generated = compact(generate_iterative_clone(&language));
        assert!(generated.contains("with_two_pools_or_fallback"));
        assert!(generated.contains("implCloneforProc"));
        assert!(generated.contains("implCloneforPathmap"));
    }

    #[test]
    fn collection_clone_emits_homogeneous_pathmap_rebuilds() {
        let language = crate::gen::collection_literal_language_for_tests();
        let generated = compact(generate_iterative_clone(&language));
        assert!(generated.contains("PathMapMode::Set"));
        assert!(generated.contains("PathMapMode::Map"));
        assert!(!generated.contains("Box::new"));
    }

    #[test]
    fn assembly_bodies_are_peeled_out_of_the_dispatch_frame() {
        let language = crate::gen::collection_literal_language_for_tests();
        let generated = compact(generate_iterative_clone(&language));
        assert!(generated.contains(
            "CloneTask::AssembleBag_BagLit{src,slot,elements_start}=>{#[inline(never)]fnassemble"
        ));
        assert!(generated.contains("assemble(results,src,slot,elements_start)"));
        assert!(generated.contains(
            "CloneTask::AssemblePathmap_PathmapLit{src,slot,elements_start}=>{#[inline(never)]fnassemble"
        ));
    }

    #[test]
    fn exhaustive_match_codegen_omits_singleton_clone_fallbacks() {
        let language = crate::gen::singleton_collection_language_for_tests();
        let generated = compact(generate_iterative_clone(&language));
        assert!(generated.contains("letMeta::MOnly(refcollection)=source;"));
        assert!(!generated.contains("letMeta::MOnly(refcollection)=sourceelse"));
    }
}
