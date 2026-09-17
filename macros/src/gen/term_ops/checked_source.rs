//! Paid observation of original typed source occurrences.
//!
//! This is the checked source interpretation of the same category/field
//! classifier used by depth and binding. Policy is supplied by the host; no
//! language name, source-profile table, parser or evaluator lives here.
//! RholangSourceImports supplies the hereditary worklist law. SourceMapEntryVisit,
//! NativeHashBagEntryVisit and PaidTaskBatchReversal supply the original child
//! sequence; RholangInitialGraphResources supplies each precharged group.

use super::collection_walk::{field_carrier, names_a_category, FieldCarrier};
use super::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

pub fn generate_checked_source(language: &LanguageDef) -> TokenStream {
    let categories: Vec<_> = language.types.iter().map(|ty| &ty.name).collect();
    let tag_types = categories.iter().map(|category| {
        let labels: Vec<_> = collect_category_variants(category, language)
            .into_iter()
            .map(|kind| kind.label().clone())
            .collect();
        quote! {
            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub enum #category { #(#labels),* }
        }
    });
    let category_names = categories.iter().map(|category| {
        let name = category.to_string();
        quote! { Self::#category(_) => #name }
    });
    let constructor_names = categories.iter().map(|category| {
        let arms = collect_category_variants(category, language)
            .into_iter()
            .map(|kind| {
                let label = kind.label();
                let name = label.to_string();
                quote! { source_constructor::#category::#label => #name }
            })
            .collect::<Vec<_>>();
        quote! { Self::#category(tag) => match tag { #(#arms),* } }
    });
    let handlers = categories
        .iter()
        .map(|category| generate_handler(category, language));
    let dispatch = categories.iter().map(|category| {
        let handler = handler_name(category);
        quote! {
            SourceTask::#category(source, role) => {
                #handler(&mut stack, source, role, occurrence, profile, reserve)?;
            }
        }
    });
    let wrappers = categories.iter().map(|category| {
        quote! {
            impl #category {
                /// Inspect every original source occurrence under a trusted closed
                /// host policy. Success certifies structural closure only. It does
                /// not resolve names, inspect guest text, execute or authorize effects.
                pub fn try_check_source_profile<P: SourceProfile, E>(
                    &self, role: P::Role, profile: &P,
                    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
                ) -> Result<(), SourceProfileError<E, P::Role>> {
                    // Vec/ordinal initialization and flat vector disposal, then the
                    // root's construction, push and eventual flat job disposal.
                    mettail_runtime::reserve_binding_parts(3, 2, 0, reserve)?;
                    mettail_runtime::reserve_binding_parts(3, 1, 0, reserve)?;
                    check_source_worklist(SourceTask::#category(self, role), profile, reserve)
                }
            }
        }
    });
    let reverse_body = super::iterative_clone::paid_task_batch_reversal_body();
    quote! {
        /// Exact generated constructor identities, including closed data.
        #[allow(dead_code, non_camel_case_types)]
        pub mod source_constructor { #(#tag_types)* }

        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum SourceConstructor { #(#categories(source_constructor::#categories)),* }

        impl SourceConstructor {
            pub fn category_name(self) -> &'static str { match self { #(#category_names),* } }
            pub fn constructor_name(self) -> &'static str { match self { #(#constructor_names),* } }
        }

        /// Host-owned closed policy. Functions must be trusted, bounded and
        /// side-effect free; this observer pays dispatch, not arbitrary user code.
        /// Every original field has one entry: None for opaque data, Some for
        /// a category child, collection element role or original scope body.
        /// An outer None refuses the constructor before payload traversal.
        pub trait SourceProfile {
            type Role: Copy + 'static;
            fn fields(&self, constructor: SourceConstructor)
                -> Option<&'static [Option<fn(Self::Role) -> Self::Role>]>;
        }

        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum SourceProfileError<E, R> {
            Reservation(mettail_runtime::BindingFailure<E>),
            Unsupported { constructor: SourceConstructor, role: R, ordinal: usize },
            UnsupportedCarrier { constructor: SourceConstructor, role: R, ordinal: usize },
            InvalidPolicy { constructor: SourceConstructor, role: R, ordinal: usize },
        }
        impl<E, R> From<mettail_runtime::BindingFailure<E>> for SourceProfileError<E, R> {
            fn from(error: mettail_runtime::BindingFailure<E>) -> Self {
                Self::Reservation(error)
            }
        }

        // References retain the original root lifetime. Role: Copy excludes
        // recursive user destructors; dropping the vector never drops an AST.
        enum SourceTask<'a, R: Copy> { #(#categories(&'a #categories, R)),* }

        fn reverse_source_task_batch<R: Copy, E>(
            stack: &mut [SourceTask<'_, R>], start: usize,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<(), mettail_runtime::BindingFailure<E>> { #reverse_body }

        fn check_source_worklist<P: SourceProfile, E>(
            root: SourceTask<'_, P::Role>, profile: &P,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<(), SourceProfileError<E, P::Role>> {
            // Initialization/root retention were paid by the typed wrapper.
            let mut stack = vec![root];
            let mut ordinal = 0usize;
            loop {
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
                let Some(task) = stack.pop() else { return Ok(()) };
                // Task dispatch, checked ordinal advance and constructor match.
                mettail_runtime::reserve_binding_parts(3, 1, 0, reserve)?;
                let occurrence = ordinal;
                ordinal = ordinal.checked_add(1)
                    .ok_or(mettail_runtime::BindingFailure::SizeOverflow)?;
                match task { #(#dispatch)* }
            }
        }
        #(#handlers)*
        #(#wrappers)*
    }
}

fn handler_name(category: &Ident) -> Ident {
    format_ident!("check_source_{}", category.to_string().to_lowercase())
}

fn constructor_pattern(category: &Ident, kind: &VariantKind) -> TokenStream {
    let label = kind.label();
    match kind {
        VariantKind::Nullary { .. } => quote! { #category::#label },
        _ => quote! { #category::#label(..) },
    }
}

fn generate_handler(category: &Ident, language: &LanguageDef) -> TokenStream {
    let handler = handler_name(category);
    let variants = collect_category_variants(category, language);
    let tags = variants.iter().map(|kind| {
        let pattern = constructor_pattern(category, kind);
        let label = kind.label();
        quote! { #pattern => SourceConstructor::#category(source_constructor::#category::#label) }
    });
    let helpers: Vec<_> = variants
        .iter()
        .map(|kind| format_ident!("{}_{}", handler, kind.label()))
        .collect();
    let selections = variants.iter().zip(&helpers).map(|(kind, helper)| {
        let label = kind.label();
        quote! {
            SourceConstructor::#category(source_constructor::#category::#label) => #helper::<P, E, F>
        }
    });
    // Reuse the comparison engine's noinline frame factoring one level finer:
    // a real category can itself contain hundreds of constructor-local frames.
    // Every helper returns to the one worklist; none recursively visits a child.
    let bodies = variants.iter().zip(&helpers).map(|(kind, helper)| {
        let arm = generate_arm(category, kind, language);
        quote! {
            #[allow(unused_variables, non_snake_case, unreachable_patterns)]
            #[inline(never)]
            fn #helper<'a, P: SourceProfile, E, F: FnMut(usize, usize) -> Result<(), E>>(
                stack: &mut Vec<SourceTask<'a, P::Role>>, source: &'a #category,
                role: P::Role, ordinal: usize, constructor: SourceConstructor,
                fields: &'static [Option<fn(P::Role) -> P::Role>], reserve: &mut F,
            ) -> Result<(), SourceProfileError<E, P::Role>> {
                match source {
                    #arm,
                    _ => Err(SourceProfileError::InvalidPolicy { constructor, role, ordinal }),
                }
            }
        }
    });
    quote! {
        #[allow(unused_variables, non_snake_case, unreachable_patterns)]
        #[inline(never)]
        fn #handler<'a, P: SourceProfile, E, F: FnMut(usize, usize) -> Result<(), E>>(
            stack: &mut Vec<SourceTask<'a, P::Role>>, source: &'a #category,
            role: P::Role, ordinal: usize, profile: &P,
            reserve: &mut F,
        ) -> Result<(), SourceProfileError<E, P::Role>> {
            let constructor = match source { #(#tags),* };
            // Separate policy dispatch/slice retention from the paid tag match.
            mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)?;
            let fields = profile.fields(constructor).ok_or(
                SourceProfileError::Unsupported { constructor, role, ordinal })?;
            // Pay helper selection/retention, call, and its single payload
            // match. A common call site avoids per-arm Result temporaries in
            // this category frame, including in unoptimized generated code.
            mettail_runtime::reserve_binding_parts(3, 1, 0, reserve)?;
            // Helpers quantify over the original source lifetime. Preserve
            // that quantifier during selection, then instantiate it with this
            // call's borrow; fixing 'a here prevents match-arm item coercion.
            let observe: for<'source> fn(
                &mut Vec<SourceTask<'source, P::Role>>, &'source #category, P::Role, usize,
                SourceConstructor, &'static [Option<fn(P::Role) -> P::Role>], &mut F,
            ) -> Result<(), SourceProfileError<E, P::Role>> = match constructor {
                #(#selections),*,
                _ => return Err(SourceProfileError::InvalidPolicy { constructor, role, ordinal }),
            };
            observe(stack, source, role, ordinal, constructor, fields, reserve)
        }
        #(#bodies)*
    }
}

fn collection_supported(collection: &CollectionType) -> bool {
    matches!(
        collection,
        CollectionType::Vec | CollectionType::HashBag | CollectionType::HashMap
    )
}

fn field_supported(field: &FieldInfo, language: &LanguageDef) -> bool {
    match field_carrier(field) {
        FieldCarrier::Leaf => true,
        FieldCarrier::Child => names_a_category(&field.category, language),
        FieldCarrier::Collection { coll_type } => {
            names_a_category(&field.category, language) && collection_supported(&coll_type)
        },
        // No optional field is in the required source profile. Refuse the
        // whole constructor before projecting any sibling rather than invent
        // an unreviewed carrier recipe here.
        FieldCarrier::OptionalChild | FieldCarrier::OptionalCollection { .. } => false,
    }
}

fn validate_fields(children: &[bool]) -> TokenStream {
    let count = children.len();
    let checks = children.iter().enumerate().map(|(index, child)| {
        quote! {
            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
            if fields[#index].is_some() != #child {
                return Err(SourceProfileError::InvalidPolicy { constructor, role, ordinal });
            }
        }
    });
    quote! {
        mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
        if fields.len() != #count {
            return Err(SourceProfileError::InvalidPolicy { constructor, role, ordinal });
        }
        #(#checks)*
    }
}

fn select_role(index: usize) -> TokenStream {
    quote! {
        mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)?;
        let child_role = fields[#index].ok_or(
            SourceProfileError::InvalidPolicy { constructor, role, ordinal })?(role);
    }
}

// Each projection is separately paid before it is performed. Each job pays
// its construction, push and eventual normal disposal, even on later refusal.
fn push_child(category: &Ident, child: TokenStream) -> TokenStream {
    quote! {
        mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
        let child = #child;
        mettail_runtime::reserve_binding_parts(3, 1, 0, reserve)?;
        stack.push(SourceTask::#category(child, child_role));
    }
}

fn collection_children(
    category: &Ident,
    collection: &CollectionType,
    source: &Ident,
) -> TokenStream {
    let element = push_child(category, quote! { child });
    let key = push_child(category, quote! { key });
    let value = push_child(category, quote! { value });
    match collection {
        CollectionType::Vec => quote! {{
            mettail_runtime::reserve_binding_parts(1, 1, 0, reserve)?;
            let mut entries = #source.iter();
            loop {
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
                let Some(child) = entries.next() else { break };
                #element
            }
        }},
        CollectionType::HashBag => quote! {
            #source.try_for_each_entry(reserve, |child, _count, reserve| {
                #element
                Ok(())
            })?;
        },
        CollectionType::HashMap => quote! {
            #source.try_for_each_entry(reserve, |key, value, reserve| {
                (|| -> Result<(), mettail_runtime::BindingFailure<E>> {
                    #key
                    #value
                    Ok(())
                })().map_err(mettail_runtime::NativeComparisonFailure::Admission)
            }).map_err(mettail_runtime::BindingFailure::from)?;
        },
        CollectionType::HashSet | CollectionType::PathMap => {
            unreachable!("unsupported collection must be refused before child emission")
        },
    }
}

fn field_children(field: &FieldInfo, index: usize, source: &Ident) -> TokenStream {
    if matches!(field_carrier(field), FieldCarrier::Leaf) {
        return quote! {};
    }
    let role = select_role(index);
    let category = &field.category;
    let children = match field_carrier(field) {
        FieldCarrier::Child => push_child(category, quote! { #source.as_ref() }),
        FieldCarrier::Collection { coll_type } => {
            let entries = collection_children(category, &coll_type, source);
            quote! {
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
                #entries
            }
        },
        _ => unreachable!("unreviewed field carrier must be refused before child emission"),
    };
    quote! {{ #role #children }}
}

fn generate_arm(category: &Ident, kind: &VariantKind, language: &LanguageDef) -> TokenStream {
    let label = kind.label();
    let refused = || {
        let pattern = constructor_pattern(category, kind);
        quote! { #pattern => Err(SourceProfileError::UnsupportedCarrier { constructor, role, ordinal }) }
    };
    let (pattern, mask, children) = match kind {
        VariantKind::Refused { message, .. } => {
            return quote! { _ => { compile_error!(#message); } }
        },
        VariantKind::RecursiveNativeLiteral { .. } => return refused(),
        VariantKind::Nullary { .. } => (quote! { #category::#label }, vec![], quote! {}),
        VariantKind::Var { .. } | VariantKind::Literal { .. } => {
            (quote! { #category::#label(_) }, vec![false], quote! {})
        },
        VariantKind::Collection { element_cat, coll_type, .. }
        | VariantKind::CollectionLiteral { element_cat, coll_type, .. } => {
            if !names_a_category(element_cat, language) || !collection_supported(coll_type) {
                return refused();
            }
            let role = select_role(0);
            let elements =
                collection_children(element_cat, coll_type, &format_ident!("collection"));
            (
                quote! { #category::#label(collection) },
                vec![true],
                quote! {
                    #role
                    mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
                    #elements
                },
            )
        },
        VariantKind::Regular { fields, .. } => {
            if fields.iter().any(|field| !field_supported(field, language)) {
                return refused();
            }
            let names: Vec<_> = (0..fields.len())
                .map(|i| format_ident!("field_{i}"))
                .collect();
            let mask = fields
                .iter()
                .map(|field| !matches!(field_carrier(field), FieldCarrier::Leaf))
                .collect();
            let visits = fields
                .iter()
                .zip(&names)
                .enumerate()
                .map(|(index, (field, name))| field_children(field, index, name));
            (quote! { #category::#label(#(#names),*) }, mask, quote! { #(#visits)* })
        },
        VariantKind::Binder { pre_scope_fields, body_cat, .. }
        | VariantKind::MultiBinder { pre_scope_fields, body_cat, .. } => {
            if pre_scope_fields
                .iter()
                .any(|field| !field_supported(field, language))
            {
                return refused();
            }
            let names: Vec<_> = (0..pre_scope_fields.len())
                .map(|i| format_ident!("field_{i}"))
                .collect();
            let mut mask: Vec<_> = pre_scope_fields
                .iter()
                .map(|field| !matches!(field_carrier(field), FieldCarrier::Leaf))
                .collect();
            mask.push(true);
            let visits = pre_scope_fields
                .iter()
                .zip(&names)
                .enumerate()
                .map(|(index, (field, name))| field_children(field, index, name));
            let role = select_role(pre_scope_fields.len());
            let body = push_child(body_cat, quote! { scope.unsafe_body().as_ref() });
            (
                quote! { #category::#label(#(#names,)* scope) },
                mask,
                quote! {
                    #(#visits)*
                    { #role #body }
                },
            )
        },
    };
    let validation = validate_fields(&mask);
    quote! {
        #pattern => {
            #validation
            mettail_runtime::reserve_binding_parts(1, 1, 0, reserve)?;
            let batch_start = stack.len();
            #children
            reverse_source_task_batch(stack, batch_start, reserve)?;
            Ok(())
        }
    }
}

#[cfg(test)]
#[path = "checked_source_tests.rs"]
mod tests;
