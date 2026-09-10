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
use std::collections::BTreeMap;
use syn::Ident;

use crate::gen::native_carrier::NativeRecursiveCarrier;

#[derive(Clone, Copy)]
enum CollectionSurface {
    Direct,
    Literal,
}

struct CheckedEmissionContext {
    dummy_indices: BTreeMap<String, usize>,
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

    // Gated until every field/assembly branch has checked emission. This
    // constructor changes generation context, not parser activation.
    #[allow(dead_code)]
    fn checked(receipts: &super::dummy_receipts::DummyReceiptEmission) -> Self {
        Self {
            checked: Some(CheckedEmissionContext { dummy_indices: receipts.indices.clone() }),
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
            quote! { <E> }
        } else {
            TokenStream::new()
        }
    }

    // Insert after the existing final parameter's comma.
    fn binding_parameters(&self) -> TokenStream {
        if self.checked.is_some() {
            quote! {
                operation: mettail_runtime::BindingOperation<'_>,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
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
            if let Some(task) = generate_assemble_task(category, &variant) {
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

fn generate_assemble_task(category: &Ident, variant: &VariantKind) -> Option<TokenStream> {
    let (label, fields, prefix) = match variant {
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
    let handlers = language.types.iter().map(|ty| {
        let category = &ty.name;
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

    let visits: Vec<_> = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
            let visit = format_ident!("Clone{}", category);
            let handler = emission.handler(category);
            quote! {
                #task_enum::#visit { src, slot } =>
                    #handler(stack, results, src, slot #binding_arguments) #propagate,
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
                assemblies.push(arm);
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
                match task {
                    #(#visits)*
                    #(#assemblies)*
                }
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
        #(#handlers)*

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
        VariantKind::Var { label } | VariantKind::Literal { label } => quote! {
            #category::#label(value) => {
                results[slot] =
                    Some(AnyClonedTerm::#wrap(#category::#label(value.clone())));
            }
        },
        VariantKind::Regular { label, fields } => {
            generate_structured_visit(category, label, fields, false, emission)
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
    match variant {
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
mod tests {
    use super::*;

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
        let checked = CloneEmissionNames::checked(&receipts);
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
                    let expected = [(0, 8), (1, 4), (1, 4), (1, 0), (6, 8), (1, 0), (1, 0)];
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
