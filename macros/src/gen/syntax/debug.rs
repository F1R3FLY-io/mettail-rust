//! Iterative (trampolined) Debug implementation for AST category enums.
//!
//! Derived `Debug` recurses through `Box<T>` fields, which causes stack
//! overflow on deeply nested terms (100K+ nesting depth). This module
//! generates a manual `impl Debug` that uses an explicit work-stack
//! (`Vec<DebugTask>`) to serialize the term iteratively.
//!
//! ## Architecture
//!
//! - `DebugTask` enum: category visits plus literal writes, indentation, and
//!   bounded opaque-leaf formatting
//! - `DEBUG_TASK_POOL` thread-local: reuses the work-stack across calls
//! - `debug_iterative(stack, formatter)`: pops tasks and writes to the formatter
//! - `impl Debug for Cat`: pushes `DebugTask::DebugCat(self as *const Cat)` and delegates
//!
//! The output format exactly matches what `#[derive(Debug)]` would produce:
//! - Nullary:    `PZero`
//! - Literal:    `NumLit(42)`
//! - Var:        `IVar(OrdVar(...))`
//! - Regular:    `AddInt(left, right)` — children become DebugTask pushes
//! - Collection: `PPar(HashBag {...})` — container and elements are scheduled
//!   on the same explicit work stack
//! - Binder:     `LamInt(Scope { ... })` — scope decomposed, body pushed as task
//!
//! Both compact (`{:?}`) and alternate (`{:#?}`) layouts reproduce Rust's
//! derived tuple-variant/collection layout. Alternate indentation is carried as
//! data in each task; it never consumes one host frame per term level.

#![allow(clippy::cmp_owned)]

use crate::gen::term_ops::collection_walk::{field_carrier, names_a_category, FieldCarrier};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate `DebugTask` enum, TLS pool, iterative engine, and `impl Debug`
/// for all exported categories.
pub fn generate_debug(language: &LanguageDef) -> TokenStream {
    let debug_task_enum = generate_debug_task_enum(language);
    let collection_helpers = generate_debug_collection_helpers(language);
    let iterative_engine = generate_debug_iterative_engine(language);
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_debug_impl(&lang_type.name, language))
        .collect();

    quote! {
        #debug_task_enum
        #collection_helpers
        #iterative_engine
        #(#impls)*
    }
}

fn generate_debug_collection_helpers(language: &LanguageDef) -> TokenStream {
    let mut uses = Vec::<(Ident, CollectionType)>::new();
    for lang_type in &language.types {
        for variant in collect_category_variants(&lang_type.name, language) {
            match variant {
                VariantKind::CollectionLiteral { element_cat, coll_type, .. }
                | VariantKind::Collection { element_cat, coll_type, .. } => {
                    record_debug_collection_use(&mut uses, element_cat, coll_type, language);
                },
                VariantKind::Regular { fields, .. } => {
                    record_debug_field_collection_uses(&mut uses, &fields, language);
                },
                VariantKind::Binder { pre_scope_fields, .. }
                | VariantKind::MultiBinder { pre_scope_fields, .. } => {
                    record_debug_field_collection_uses(&mut uses, &pre_scope_fields, language);
                },
                VariantKind::Var { .. }
                | VariantKind::Literal { .. }
                | VariantKind::Nullary { .. }
                | VariantKind::Refused { .. } => {},
            }
        }
    }

    let helpers = uses
        .iter()
        .map(|(cat, coll_type)| generate_debug_collection_helper(cat, coll_type));
    quote! { #(#helpers)* }
}

fn record_debug_field_collection_uses(
    uses: &mut Vec<(Ident, CollectionType)>,
    fields: &[FieldInfo],
    language: &LanguageDef,
) {
    for field in fields {
        match field_carrier(field) {
            FieldCarrier::Collection { coll_type }
            | FieldCarrier::OptionalCollection { coll_type } => {
                record_debug_collection_use(uses, field.category.clone(), coll_type, language)
            },
            FieldCarrier::Leaf | FieldCarrier::Child | FieldCarrier::OptionalChild => {},
        }
    }
}

fn record_debug_collection_use(
    uses: &mut Vec<(Ident, CollectionType)>,
    element_cat: Ident,
    coll_type: CollectionType,
    language: &LanguageDef,
) {
    if !names_a_category(&element_cat, language)
        || uses
            .iter()
            .any(|(cat, kind)| *cat == element_cat && *kind == coll_type)
    {
        return;
    }
    uses.push((element_cat, coll_type));
}

fn generate_debug_collection_helper(cat: &Ident, coll_type: &CollectionType) -> TokenStream {
    let task = format_ident!("Debug{}", cat);
    let suffix = cat.to_string().to_lowercase();

    match coll_type {
        CollectionType::Vec => {
            let helper = format_ident!("debug_push_vec_{}", suffix);
            quote! {
                #[inline(never)]
                fn #helper(
                    stack: &mut Vec<DebugTask>,
                    collection: &Vec<#cat>,
                    depth: usize,
                    alternate: bool,
                ) {
                    if alternate && !collection.is_empty() {
                        stack.push(DebugTask::WriteStr("]"));
                        stack.push(DebugTask::Indent(depth));
                        for item in collection.iter().rev() {
                            stack.push(DebugTask::WriteStr(",\n"));
                            stack.push(DebugTask::#task {
                                value: item as *const _,
                                depth: depth + 1,
                            });
                            stack.push(DebugTask::Indent(depth + 1));
                        }
                        stack.push(DebugTask::WriteStr("[\n"));
                    } else if alternate {
                        stack.push(DebugTask::WriteStr("[]"));
                    } else {
                        stack.push(DebugTask::WriteStr("]"));
                        for (index, item) in collection.iter().enumerate().rev() {
                            stack.push(DebugTask::#task {
                                value: item as *const _,
                                depth,
                            });
                            if index > 0 {
                                stack.push(DebugTask::WriteStr(", "));
                            }
                        }
                        stack.push(DebugTask::WriteStr("["));
                    }
                }
            }
        },
        CollectionType::HashSet => {
            let helper = format_ident!("debug_push_hashset_{}", suffix);
            quote! {
                #[inline(never)]
                fn #helper(
                    stack: &mut Vec<DebugTask>,
                    collection: &mettail_runtime::HashSetLit<#cat>,
                    depth: usize,
                    alternate: bool,
                ) {
                    let items: Vec<_> = collection.iter().collect();
                    if alternate {
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::Indent(depth));
                        stack.push(DebugTask::WriteStr(",\n"));
                        if items.is_empty() {
                            stack.push(DebugTask::WriteStr("{}"));
                        } else {
                            stack.push(DebugTask::WriteStr("}"));
                            stack.push(DebugTask::Indent(depth + 1));
                            for item in items.into_iter().rev() {
                                stack.push(DebugTask::WriteStr(",\n"));
                                stack.push(DebugTask::#task {
                                    value: item as *const _,
                                    depth: depth + 2,
                                });
                                stack.push(DebugTask::Indent(depth + 2));
                            }
                            stack.push(DebugTask::WriteStr("{\n"));
                        }
                        stack.push(DebugTask::Indent(depth + 1));
                        stack.push(DebugTask::WriteStr("HashSetLit(\n"));
                    } else {
                        stack.push(DebugTask::WriteStr("})"));
                        for (index, item) in items.into_iter().enumerate().rev() {
                            stack.push(DebugTask::#task {
                                value: item as *const _,
                                depth,
                            });
                            if index > 0 {
                                stack.push(DebugTask::WriteStr(", "));
                            }
                        }
                        stack.push(DebugTask::WriteStr("HashSetLit({"));
                    }
                }
            }
        },
        CollectionType::HashBag => {
            let helper = format_ident!("debug_push_hashbag_{}", suffix);
            quote! {
                #[inline(never)]
                fn #helper(
                    stack: &mut Vec<DebugTask>,
                    collection: &mettail_runtime::HashBag<#cat>,
                    depth: usize,
                    alternate: bool,
                ) {
                    let items: Vec<_> = collection.iter().collect();
                    if alternate {
                        stack.push(DebugTask::WriteStr("}"));
                        stack.push(DebugTask::Indent(depth));
                        stack.push(DebugTask::WriteStr(",\n"));
                        stack.push(DebugTask::WriteUsize(collection.len()));
                        stack.push(DebugTask::WriteStr("total_count: "));
                        stack.push(DebugTask::Indent(depth + 1));
                        stack.push(DebugTask::WriteStr(",\n"));
                        if items.is_empty() {
                            stack.push(DebugTask::WriteStr("{}"));
                        } else {
                            stack.push(DebugTask::WriteStr("}"));
                            stack.push(DebugTask::Indent(depth + 1));
                            for (item, count) in items.into_iter().rev() {
                                stack.push(DebugTask::WriteStr(",\n"));
                                stack.push(DebugTask::WriteUsize(count));
                                stack.push(DebugTask::WriteStr(": "));
                                stack.push(DebugTask::#task {
                                    value: item as *const _,
                                    depth: depth + 2,
                                });
                                stack.push(DebugTask::Indent(depth + 2));
                            }
                            stack.push(DebugTask::WriteStr("{\n"));
                        }
                        stack.push(DebugTask::WriteStr("counts: "));
                        stack.push(DebugTask::Indent(depth + 1));
                        stack.push(DebugTask::WriteStr("HashBag {\n"));
                    } else {
                        stack.push(DebugTask::WriteStr(" }"));
                        stack.push(DebugTask::WriteUsize(collection.len()));
                        stack.push(DebugTask::WriteStr(", total_count: "));
                        stack.push(DebugTask::WriteStr("}"));
                        for (index, (item, count)) in items.into_iter().enumerate().rev() {
                            stack.push(DebugTask::WriteUsize(count));
                            stack.push(DebugTask::WriteStr(": "));
                            stack.push(DebugTask::#task {
                                value: item as *const _,
                                depth,
                            });
                            if index > 0 {
                                stack.push(DebugTask::WriteStr(", "));
                            }
                        }
                        stack.push(DebugTask::WriteStr("HashBag { counts: {"));
                    }
                }
            }
        },
        CollectionType::HashMap => {
            let helper = format_ident!("debug_push_hashmap_{}", suffix);
            quote! {
                #[inline(never)]
                fn #helper(
                    stack: &mut Vec<DebugTask>,
                    collection: &mettail_runtime::HashMapLit<#cat, #cat>,
                    depth: usize,
                    alternate: bool,
                ) {
                    let items: Vec<_> = collection.iter().collect();
                    if alternate {
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::Indent(depth));
                        stack.push(DebugTask::WriteStr(",\n"));
                        if items.is_empty() {
                            stack.push(DebugTask::WriteStr("{}"));
                        } else {
                            stack.push(DebugTask::WriteStr("}"));
                            stack.push(DebugTask::Indent(depth + 1));
                            for (key, value) in items.into_iter().rev() {
                                stack.push(DebugTask::WriteStr(",\n"));
                                stack.push(DebugTask::#task {
                                    value: value as *const _,
                                    depth: depth + 2,
                                });
                                stack.push(DebugTask::WriteStr(": "));
                                stack.push(DebugTask::#task {
                                    value: key as *const _,
                                    depth: depth + 2,
                                });
                                stack.push(DebugTask::Indent(depth + 2));
                            }
                            stack.push(DebugTask::WriteStr("{\n"));
                        }
                        stack.push(DebugTask::Indent(depth + 1));
                        stack.push(DebugTask::WriteStr("HashMapLit(\n"));
                    } else {
                        stack.push(DebugTask::WriteStr("})"));
                        for (index, (key, value)) in items.into_iter().enumerate().rev() {
                            stack.push(DebugTask::#task {
                                value: value as *const _,
                                depth,
                            });
                            stack.push(DebugTask::WriteStr(": "));
                            stack.push(DebugTask::#task {
                                value: key as *const _,
                                depth,
                            });
                            if index > 0 {
                                stack.push(DebugTask::WriteStr(", "));
                            }
                        }
                        stack.push(DebugTask::WriteStr("HashMapLit({"));
                    }
                }
            }
        },
        CollectionType::PathMap => {
            let helper = format_ident!("debug_push_pathmap_{}", suffix);
            quote! {
                #[inline(never)]
                fn #helper(
                    stack: &mut Vec<DebugTask>,
                    collection: &mettail_runtime::PathMapLit<#cat, #cat>,
                    depth: usize,
                    alternate: bool,
                ) {
                    match collection {
                        mettail_runtime::PathMapLit::Empty => {
                            stack.push(DebugTask::WriteStr("Empty"));
                        },
                        mettail_runtime::PathMapLit::Set(entries) => {
                            let items: Vec<_> = entries.keys().collect();
                            if alternate {
                                stack.push(DebugTask::WriteStr(")"));
                                stack.push(DebugTask::Indent(depth));
                                stack.push(DebugTask::WriteStr(",\n"));
                                stack.push(DebugTask::WriteStr(")"));
                                stack.push(DebugTask::Indent(depth + 1));
                                stack.push(DebugTask::WriteStr(",\n"));
                                if items.is_empty() {
                                    stack.push(DebugTask::WriteStr("{}"));
                                } else {
                                    stack.push(DebugTask::WriteStr("}"));
                                    stack.push(DebugTask::Indent(depth + 2));
                                    for key in items.into_iter().rev() {
                                        stack.push(DebugTask::WriteStr(",\n"));
                                        stack.push(DebugTask::WriteStr("()"));
                                        stack.push(DebugTask::WriteStr(": "));
                                        stack.push(DebugTask::#task {
                                            value: key as *const _,
                                            depth: depth + 3,
                                        });
                                        stack.push(DebugTask::Indent(depth + 3));
                                    }
                                    stack.push(DebugTask::WriteStr("{\n"));
                                }
                                stack.push(DebugTask::Indent(depth + 2));
                                stack.push(DebugTask::WriteStr("HashMapLit(\n"));
                                stack.push(DebugTask::Indent(depth + 1));
                                stack.push(DebugTask::WriteStr("Set(\n"));
                            } else {
                                stack.push(DebugTask::WriteStr("}))"));
                                for (index, key) in items.into_iter().enumerate().rev() {
                                    stack.push(DebugTask::WriteStr("()"));
                                    stack.push(DebugTask::WriteStr(": "));
                                    stack.push(DebugTask::#task {
                                        value: key as *const _,
                                        depth,
                                    });
                                    if index > 0 {
                                        stack.push(DebugTask::WriteStr(", "));
                                    }
                                }
                                stack.push(DebugTask::WriteStr("Set(HashMapLit({"));
                            }
                        },
                        mettail_runtime::PathMapLit::Map(entries) => {
                            let items: Vec<_> = entries.iter().collect();
                            if alternate {
                                stack.push(DebugTask::WriteStr(")"));
                                stack.push(DebugTask::Indent(depth));
                                stack.push(DebugTask::WriteStr(",\n"));
                                stack.push(DebugTask::WriteStr(")"));
                                stack.push(DebugTask::Indent(depth + 1));
                                stack.push(DebugTask::WriteStr(",\n"));
                                if items.is_empty() {
                                    stack.push(DebugTask::WriteStr("{}"));
                                } else {
                                    stack.push(DebugTask::WriteStr("}"));
                                    stack.push(DebugTask::Indent(depth + 2));
                                    for (key, value) in items.into_iter().rev() {
                                        stack.push(DebugTask::WriteStr(",\n"));
                                        stack.push(DebugTask::#task {
                                            value: value as *const _,
                                            depth: depth + 3,
                                        });
                                        stack.push(DebugTask::WriteStr(": "));
                                        stack.push(DebugTask::#task {
                                            value: key as *const _,
                                            depth: depth + 3,
                                        });
                                        stack.push(DebugTask::Indent(depth + 3));
                                    }
                                    stack.push(DebugTask::WriteStr("{\n"));
                                }
                                stack.push(DebugTask::Indent(depth + 2));
                                stack.push(DebugTask::WriteStr("HashMapLit(\n"));
                                stack.push(DebugTask::Indent(depth + 1));
                                stack.push(DebugTask::WriteStr("Map(\n"));
                            } else {
                                stack.push(DebugTask::WriteStr("}))"));
                                for (index, (key, value)) in
                                    items.into_iter().enumerate().rev()
                                {
                                    stack.push(DebugTask::#task {
                                        value: value as *const _,
                                        depth,
                                    });
                                    stack.push(DebugTask::WriteStr(": "));
                                    stack.push(DebugTask::#task {
                                        value: key as *const _,
                                        depth,
                                    });
                                    if index > 0 {
                                        stack.push(DebugTask::WriteStr(", "));
                                    }
                                }
                                stack.push(DebugTask::WriteStr("Map(HashMapLit({"));
                            }
                        },
                    }
                }
            }
        },
    }
}

// =============================================================================
// DebugTask Enum + TLS Pool
// =============================================================================

/// Generate the `DebugTask` enum with one variant per category plus bounded
/// formatting primitives.
fn generate_debug_task_enum(language: &LanguageDef) -> TokenStream {
    let category_variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Debug{}", cat);
            quote! {
                #variant_name {
                    value: *const #cat,
                    depth: usize,
                }
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative Debug engine.
        ///
        /// Each category variant wraps a raw pointer to a term to format.
        /// The pointer is derived from a `&Cat` reference within the same
        /// `fmt()` call, so the referent is guaranteed to be alive for the
        /// duration. The remaining variants emit punctuation, indentation, or
        /// one non-category leaf without traversing a generated term.
        #[allow(dead_code)]
        enum DebugTask {
            #(#category_variants,)*
            /// Write a static string literal.
            WriteStr(&'static str),
            WriteUsize(usize),
            Indent(usize),
            Opaque {
                value: *const (),
                fmt: unsafe fn(
                    *const (),
                    &mut std::fmt::Formatter<'_>,
                    usize,
                ) -> std::fmt::Result,
                depth: usize,
            },
        }

        /// Adds the enclosing generated term's indentation after every newline
        /// produced by an opaque leaf's alternate `Debug`. This is the streaming
        /// equivalent of the `PadAdapter` used by `core::fmt::DebugBuilder`: no
        /// intermediary `String` is allocated.
        struct DebugIndentWriter<'a, 'b> {
            formatter: &'a mut std::fmt::Formatter<'b>,
            depth: usize,
            after_newline: bool,
        }

        impl std::fmt::Write for DebugIndentWriter<'_, '_> {
            fn write_str(&mut self, mut text: &str) -> std::fmt::Result {
                while !text.is_empty() {
                    if self.after_newline {
                        for _ in 0..self.depth {
                            self.formatter.write_str("    ")?;
                        }
                        self.after_newline = false;
                    }

                    match text.find('\n') {
                        Some(index) => {
                            let (line, rest) = text.split_at(index + 1);
                            self.formatter.write_str(line)?;
                            self.after_newline = true;
                            text = rest;
                        },
                        None => {
                            self.formatter.write_str(text)?;
                            break;
                        },
                    }
                }
                Ok(())
            }
        }

        #[inline]
        fn debug_opaque_task<T: std::fmt::Debug>(value: &T, depth: usize) -> DebugTask {
            unsafe fn apply<T: std::fmt::Debug>(
                value: *const (),
                f: &mut std::fmt::Formatter<'_>,
                depth: usize,
            ) -> std::fmt::Result {
                let value = unsafe { &*value.cast::<T>() };
                if f.alternate() && depth > 0 {
                    let mut writer = DebugIndentWriter {
                        formatter: f,
                        depth,
                        after_newline: false,
                    };
                    std::fmt::write(&mut writer, format_args!("{value:#?}"))
                } else {
                    std::fmt::Debug::fmt(value, f)
                }
            }

            DebugTask::Opaque {
                value: value as *const T as *const (),
                fmt: apply::<T>,
                depth,
            }
        }

        thread_local! {
            /// Pool for reusing `DebugTask` work stacks across `Debug::fmt` calls.
            static DEBUG_TASK_POOL: std::cell::Cell<Vec<DebugTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Iterative Engine
// =============================================================================

/// Generate the `debug_iterative` function that drains the work-stack.
///
/// **Frame-size fix (residual #11-2, 2026-07-14):** each category's variant
/// match is extracted into its own `#[inline(never)]` `debug_visit_<cat>`
/// helper (the same Tier-1 peel `normalize_iterative` uses for its `Visit`
/// arms). Without this split, `debug_iterative`'s frame is the -O0 alloca SUM
/// of every category's variant locals (measured 275,432 B for rholang). Each
/// helper returns `std::fmt::Result`, so the `?` writes inside the arms
/// propagate through it and the dispatch arm re-propagates with `?` — a
/// control-flow-equivalent refactor, not "pure code motion" (the arms escape
/// via `?`; there are no `return`/`continue`/`break` in the generated bodies).
fn generate_debug_iterative_engine(language: &LanguageDef) -> TokenStream {
    let visit_helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_debug_visit_helper(&lang_type.name, language))
        .collect();
    let category_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_debug_category_arm(&lang_type.name, language))
        .collect();

    quote! {
        #(#visit_helper_fns)*

        /// Iterative Debug engine.
        ///
        /// Pops tasks from the work-stack and writes to the formatter.
        /// Category tasks decompose into child tasks (pushed in reverse
        /// order for correct left-to-right output). Primitive tasks emit
        /// literal text, integers, indentation, or one bounded leaf.
        #[allow(dead_code)]
        fn debug_iterative(
            stack: &mut Vec<DebugTask>,
            f: &mut std::fmt::Formatter<'_>,
        ) -> std::fmt::Result {
            while let Some(task) = stack.pop() {
                match task {
                    DebugTask::WriteStr(s) => {
                        f.write_str(s)?;
                    }
                    DebugTask::WriteUsize(value) => {
                        std::fmt::Debug::fmt(&value, f)?;
                    }
                    DebugTask::Indent(depth) => {
                        for _ in 0..depth {
                            f.write_str("    ")?;
                        }
                    }
                    DebugTask::Opaque { value, fmt, depth } => unsafe {
                        fmt(value, f, depth)?;
                    }
                    #(#category_arms)*
                }
            }
            Ok(())
        }
    }
}

/// Emit the per-category `#[inline(never)] debug_visit_<cat>` helper (residual
/// #11-2). Frame-bound constraint: this fn's frame carries ONE category's
/// variant locals; peeling it out of `debug_iterative` keeps the driver frame
/// bounded (at most one helper frame is live at a time).
fn generate_debug_visit_helper(category: &Ident, language: &LanguageDef) -> TokenStream {
    let helper_fn = format_ident!("debug_visit_{}", category.to_string().to_lowercase());
    let variants = collect_category_variants(category, language);

    let variant_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_debug_variant_arm(category, v, language))
        .collect();

    quote! {
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn #helper_fn(
            stack: &mut Vec<DebugTask>,
            f: &mut std::fmt::Formatter<'_>,
            ptr: *const #category,
            depth: usize,
        ) -> std::fmt::Result {
            // SAFETY: ptr was derived from a &Cat reference within the same
            // fmt() call; the referent is alive for the entire duration.
            let term = unsafe { &*ptr };
            match term {
                #(#variant_arms,)*
            }
            Ok(())
        }
    }
}

/// Generate the match arm for one category inside the iterative Debug engine.
///
/// Residual #11-2 (2026-07-14): now a thin dispatch that delegates to the
/// per-category `#[inline(never)] debug_visit_<cat>` helper (the variant match
/// moved there — see `generate_debug_visit_helper`).
fn generate_debug_category_arm(category: &Ident, _language: &LanguageDef) -> TokenStream {
    let variant_name = format_ident!("Debug{}", category);
    let helper_fn = format_ident!("debug_visit_{}", category.to_string().to_lowercase());

    quote! {
        DebugTask::#variant_name { value, depth } => {
            #helper_fn(stack, f, value, depth)?;
        }
    }
}

/// Generate a Debug match arm for a specific variant.
///
/// Output format matches `#[derive(Debug)]`:
/// - Nullary: `VariantName`
/// - Literal: `VariantName(value)` using value's own Debug
/// - Var: `VariantName(OrdVar(...))` using OrdVar's Debug
/// - Regular: `VariantName(child1, child2)` — push children as tasks
/// - Collection: `VariantName(HashBag {...})` — format inline via Debug
/// - Binder: `VariantName(Scope { .. })` — format scope fields
fn generate_debug_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Nullary { label } => {
            let label_str = label.to_string();
            quote! {
                #category::#label => {
                    f.write_str(#label_str)?;
                }
            }
        },

        // An OPAQUE native leaf: its own `Debug` has no sub-terms to recurse into.
        VariantKind::Literal { label } => {
            let label_str = label.to_string();
            quote! {
                #category::#label(val) => {
                    f.write_str(#label_str)?;
                    if f.alternate() {
                        f.write_str("(\n")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::Indent(depth));
                        stack.push(DebugTask::WriteStr(",\n"));
                        stack.push(debug_opaque_task(val, depth + 1));
                        stack.push(DebugTask::Indent(depth + 1));
                    } else {
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(debug_opaque_task(val, depth));
                    }
                }
            }
        },

        // ★ #162 — the collection-literal boundary. `Debug::fmt(&val, f)` on a
        // `&Vec<Proc>` formats every element through `Proc::fmt`, re-entering this
        // driver by host recursion — the reason `ast_debug` was the second-worst
        // subject at 10,542 B/level in debug and 463 in release.
        VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
            let label_str = label.to_string();
            let compact = debug_collection_stmts(
                element_cat,
                coll_type,
                &quote! { val },
                language,
                &quote! { depth },
            );
            let alternate = debug_collection_stmts(
                element_cat,
                coll_type,
                &quote! { val },
                language,
                &quote! { depth + 1 },
            );
            quote! {
                #category::#label(val) => {
                    f.write_str(#label_str)?;
                    if f.alternate() {
                        f.write_str("(\n")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::Indent(depth));
                        stack.push(DebugTask::WriteStr(",\n"));
                        #alternate
                        stack.push(DebugTask::Indent(depth + 1));
                    } else {
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        #compact
                    }
                }
            }
        },

        VariantKind::Var { label } => {
            let label_str = label.to_string();
            quote! {
                #category::#label(var) => {
                    f.write_str(#label_str)?;
                    if f.alternate() {
                        f.write_str("(\n")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::Indent(depth));
                        stack.push(DebugTask::WriteStr(",\n"));
                        stack.push(debug_opaque_task(var, depth + 1));
                        stack.push(DebugTask::Indent(depth + 1));
                    } else {
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(debug_opaque_task(var, depth));
                    }
                }
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_debug_regular_arm(category, label, fields, language)
        },

        // ★ #162 — the category-DIRECT collection field, same boundary.
        VariantKind::Collection { label, element_cat, coll_type } => {
            generate_debug_collection_arm(category, label, element_cat, coll_type, language)
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_debug_binder_arm(category, label, pre_scope_fields, body_cat, language, false)
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_debug_binder_arm(category, label, pre_scope_fields, body_cat, language, true)
        },
    }
}

/// Generate Debug arm for Regular variant.
///
/// For each field:
/// - Boxed category type: push a `DebugTask` for the child category
/// - Collection field: format inline using `Debug::fmt`
///
/// Tasks are pushed in REVERSE order (stack is LIFO) so output is left-to-right.
fn generate_debug_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    language: &LanguageDef,
) -> TokenStream {
    let label_str = label.to_string();
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();

    let mut compact_pushes: Vec<TokenStream> =
        vec![quote! { stack.push(DebugTask::WriteStr(")")); }];
    let mut alternate_pushes: Vec<TokenStream> = vec![
        quote! { stack.push(DebugTask::WriteStr(")")); },
        quote! { stack.push(DebugTask::Indent(depth)); },
    ];
    for (i, (field, fname)) in fields.iter().zip(field_names.iter()).enumerate().rev() {
        if i < fields.len() - 1 {
            compact_pushes.push(quote! { stack.push(DebugTask::WriteStr(", ")); });
        }
        compact_pushes.push(debug_field_tasks(field, fname, language, &quote! { depth }));

        alternate_pushes.push(quote! { stack.push(DebugTask::WriteStr(",\n")); });
        alternate_pushes.push(debug_field_tasks(field, fname, language, &quote! { depth + 1 }));
        alternate_pushes.push(quote! { stack.push(DebugTask::Indent(depth + 1)); });
    }

    quote! {
        #category::#label(#(#field_names),*) => {
            f.write_str(#label_str)?;
            if f.alternate() {
                f.write_str("(\n")?;
                #(#alternate_pushes)*
            } else {
                f.write_str("(")?;
                #(#compact_pushes)*
            }
        }
    }
}

fn debug_field_tasks(
    field: &FieldInfo,
    name: &Ident,
    language: &LanguageDef,
    depth: &TokenStream,
) -> TokenStream {
    match field_carrier(field) {
        FieldCarrier::Leaf => quote! {
            stack.push(debug_opaque_task(#name, #depth));
        },
        FieldCarrier::OptionalChild if names_a_category(&field.category, language) => {
            let task = format_ident!("Debug{}", field.category);
            quote! {
                match #name.as_ref() {
                    None => stack.push(DebugTask::WriteStr("None")),
                    Some(__child) => {
                        if f.alternate() {
                            stack.push(DebugTask::WriteStr(")"));
                            stack.push(DebugTask::Indent(#depth));
                            stack.push(DebugTask::WriteStr(",\n"));
                            stack.push(DebugTask::#task {
                                value: &**__child as *const _,
                                depth: #depth + 1,
                            });
                            stack.push(DebugTask::Indent(#depth + 1));
                            stack.push(DebugTask::WriteStr("Some(\n"));
                        } else {
                            stack.push(DebugTask::WriteStr(")"));
                            stack.push(DebugTask::#task {
                                value: &**__child as *const _,
                                depth: #depth,
                            });
                            stack.push(DebugTask::WriteStr("Some("));
                        }
                    },
                }
            }
        },
        FieldCarrier::OptionalChild => quote! {
            stack.push(debug_opaque_task(#name, #depth));
        },
        FieldCarrier::OptionalCollection { coll_type } => {
            let compact = debug_collection_stmts(
                &field.category,
                &coll_type,
                &quote! { __collection },
                language,
                depth,
            );
            let alternate = debug_collection_stmts(
                &field.category,
                &coll_type,
                &quote! { __collection },
                language,
                &quote! { #depth + 1 },
            );
            quote! {
                match #name.as_ref() {
                    None => stack.push(DebugTask::WriteStr("None")),
                    Some(__collection) => {
                        if f.alternate() {
                            stack.push(DebugTask::WriteStr(")"));
                            stack.push(DebugTask::Indent(#depth));
                            stack.push(DebugTask::WriteStr(",\n"));
                            #alternate
                            stack.push(DebugTask::Indent(#depth + 1));
                            stack.push(DebugTask::WriteStr("Some(\n"));
                        } else {
                            stack.push(DebugTask::WriteStr(")"));
                            #compact
                            stack.push(DebugTask::WriteStr("Some("));
                        }
                    },
                }
            }
        },
        FieldCarrier::Collection { coll_type } => {
            debug_collection_stmts(&field.category, &coll_type, &quote! { #name }, language, depth)
        },
        FieldCarrier::Child if names_a_category(&field.category, language) => {
            let task = format_ident!("Debug{}", field.category);
            quote! {
                stack.push(DebugTask::#task {
                    value: &**#name as *const _,
                    depth: #depth,
                });
            }
        },
        FieldCarrier::Child => quote! {
            stack.push(debug_opaque_task(#name, #depth));
        },
    }
}

/// Generate Debug arm for Collection variant (top-level collection constructor).
///
/// The single collection field is formatted inline using its own Debug impl.
fn generate_debug_collection_arm(
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    language: &LanguageDef,
) -> TokenStream {
    let label_str = label.to_string();
    let compact = debug_collection_stmts(
        element_cat,
        coll_type,
        &quote! { coll },
        language,
        &quote! { depth },
    );
    let alternate = debug_collection_stmts(
        element_cat,
        coll_type,
        &quote! { coll },
        language,
        &quote! { depth + 1 },
    );

    quote! {
        #category::#label(coll) => {
            f.write_str(#label_str)?;
            if f.alternate() {
                f.write_str("(\n")?;
                stack.push(DebugTask::WriteStr(")"));
                stack.push(DebugTask::Indent(depth));
                stack.push(DebugTask::WriteStr(",\n"));
                #alternate
                stack.push(DebugTask::Indent(depth + 1));
            } else {
                f.write_str("(")?;
                stack.push(DebugTask::WriteStr(")"));
                #compact
            }
        }
    }
}

/// ★ #162 — the ONE place `Debug` decides what to do with a collection of
/// sub-terms. Emits only the container's tasks; the caller owns any enclosing
/// tuple-variant punctuation.
///
/// ## The rendering must be IDENTICAL, and for `Vec` that is checkable
///
/// `Vec<T>`'s derived `Debug` is `[a, b, c]` — open bracket, elements in index
/// order, `, ` between, close bracket. Reproducing it with `DebugTask::WriteStr`
/// glue and one `Debug{Elem}` task per element is exact, and
/// `languages/tests/generated_traversal_boundary_laws.rs` asserts it against the
/// container's OWN `Debug` as an independent oracle.
///
/// ⚠ The pushes are in REVERSE render order, and the closing bracket goes on
/// FIRST. This is the `display.rs:14827` idiom verbatim — the in-tree existence
/// proof that this shape can be walked in O(1) stack.
///
/// Unordered wrappers are decomposed according to their public `Debug`
/// contracts. This is necessary because calling their whole-value `Debug` would
/// recursively call the generated element formatter. Both compact and
/// alternate layouts are scheduled explicitly, including nested indentation.
fn debug_collection_stmts(
    element_cat: &Ident,
    coll_type: &CollectionType,
    coll_expr: &TokenStream,
    language: &LanguageDef,
    depth: &TokenStream,
) -> TokenStream {
    if !names_a_category(element_cat, language) {
        return quote! {
            stack.push(debug_opaque_task(#coll_expr, #depth));
        };
    }

    let suffix = element_cat.to_string().to_lowercase();
    let helper = match coll_type {
        CollectionType::Vec => format_ident!("debug_push_vec_{}", suffix),
        CollectionType::HashSet => format_ident!("debug_push_hashset_{}", suffix),
        CollectionType::HashBag => format_ident!("debug_push_hashbag_{}", suffix),
        CollectionType::HashMap => format_ident!("debug_push_hashmap_{}", suffix),
        CollectionType::PathMap => format_ident!("debug_push_pathmap_{}", suffix),
    };
    quote! {
        #helper(stack, #coll_expr, #depth, f.alternate());
    }
}

/// Generate Debug arm for Binder or MultiBinder variant.
///
/// Output: `LamInt(Scope { pattern: Binder(...), body: <body> })`
///
/// The body is pushed as a `DebugTask` so arbitrarily deep binders
/// don't overflow the call stack.
fn generate_debug_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
    _is_multi: bool,
) -> TokenStream {
    let label_str = label.to_string();

    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1]; // last field is the scope

    let compact_pre_scope_pushes: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .rev()
        .map(|(i, field)| {
            let fname = &field_names[i];
            let field_tasks = debug_field_tasks(field, fname, language, &quote! { depth });
            quote! {
                stack.push(DebugTask::WriteStr(", "));
                #field_tasks
            }
        })
        .collect();
    let alternate_pre_scope_pushes: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .rev()
        .map(|(i, field)| {
            let fname = &field_names[i];
            let field_tasks = debug_field_tasks(field, fname, language, &quote! { depth + 1 });
            quote! {
                stack.push(DebugTask::WriteStr(",\n"));
                #field_tasks
                stack.push(DebugTask::Indent(depth + 1));
            }
        })
        .collect();

    let body_task_variant = format_ident!("Debug{}", body_cat);

    quote! {
        #category::#label(#(#field_names),*) => {
            f.write_str(#label_str)?;
            let inner = #scope_name.inner();
            if f.alternate() {
                f.write_str("(\n")?;

                stack.push(DebugTask::WriteStr(")"));
                stack.push(DebugTask::Indent(depth));
                stack.push(DebugTask::WriteStr(",\n"));

                stack.push(DebugTask::WriteStr("}"));
                stack.push(DebugTask::Indent(depth + 1));
                stack.push(DebugTask::WriteStr(",\n"));
                stack.push(DebugTask::#body_task_variant {
                    value: &*inner.unsafe_body as *const _,
                    depth: depth + 2,
                });
                stack.push(DebugTask::WriteStr("body: "));
                stack.push(DebugTask::Indent(depth + 2));
                stack.push(DebugTask::WriteStr(",\n"));
                stack.push(debug_opaque_task(&inner.unsafe_pattern, depth + 2));
                stack.push(DebugTask::WriteStr("pattern: "));
                stack.push(DebugTask::Indent(depth + 2));
                stack.push(DebugTask::WriteStr("Scope {\n"));
                stack.push(DebugTask::Indent(depth + 1));

                #(#alternate_pre_scope_pushes)*
            } else {
                f.write_str("(")?;
                stack.push(DebugTask::WriteStr(")"));
                stack.push(DebugTask::WriteStr(" }"));
                stack.push(DebugTask::#body_task_variant {
                    value: &*inner.unsafe_body as *const _,
                    depth,
                });
                stack.push(DebugTask::WriteStr(", body: "));
                stack.push(debug_opaque_task(&inner.unsafe_pattern, depth));
                stack.push(DebugTask::WriteStr("Scope { pattern: "));
                #(#compact_pre_scope_pushes)*
            }
        }
    }
}

// =============================================================================
// Per-Category Debug Impl
// =============================================================================

/// Generate `impl Debug for Cat` that delegates to the iterative engine.
fn generate_debug_impl(category: &Ident, _language: &LanguageDef) -> TokenStream {
    let task_variant = format_ident!("Debug{}", category);

    quote! {
        impl std::fmt::Debug for #category {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                // Use try_with to avoid double-panic during unwinding.
                let result = DEBUG_TASK_POOL.try_with(|cell| {
                    let mut stack = cell.take();
                    stack.clear();
                    stack.push(DebugTask::#task_variant {
                        value: self as *const #category,
                        depth: 0,
                    });
                    let result = debug_iterative(&mut stack, f);
                    cell.set(stack);
                    result
                });
                match result {
                    Ok(fmt_result) => fmt_result,
                    Err(_) => {
                        let mut stack = Vec::new();
                        stack.push(DebugTask::#task_variant {
                            value: self as *const #category,
                            depth: 0,
                        });
                        debug_iterative(&mut stack, f)
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collection_helpers_are_emitted_only_for_declared_uses() {
        let language = crate::gen::collection_literal_language_for_tests();
        let generated = generate_debug_collection_helpers(&language).to_string();

        for helper in [
            "debug_push_vec_proc",
            "debug_push_hashset_proc",
            "debug_push_hashbag_proc",
            "debug_push_hashmap_proc",
            "debug_push_pathmap_proc",
        ] {
            assert!(generated.contains(helper), "missing required helper `{helper}`: {generated}");
        }
        assert_eq!(
            generated.matches("fn debug_push_").count(),
            5,
            "the five declared Proc collection kinds must emit exactly five helpers: {generated}",
        );
        for unused_category in ["list", "bag", "set", "map", "pathmap", "int"] {
            assert!(
                !generated.contains(&format!("debug_push_vec_{unused_category}")),
                "a category that is never a collection element received a helper: {generated}",
            );
        }
    }

    #[test]
    fn collection_free_language_emits_no_collection_helpers() {
        let mut language = crate::gen::empty_language_for_tests();
        language.types.push(mettail_ast::language::LangType {
            name: format_ident!("Term"),
            native_type: None,
            collection_kind: None,
        });
        let generated = generate_debug_collection_helpers(&language).to_string();
        assert!(
            generated.is_empty(),
            "a collection-free language must not pay to compile unused helpers: {generated}",
        );
    }
}
