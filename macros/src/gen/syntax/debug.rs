//! Iterative (trampolined) Debug implementation for AST category enums.
//!
//! Derived `Debug` recurses through `Box<T>` fields, which causes stack
//! overflow on deeply nested terms (100K+ nesting depth). This module
//! generates a manual `impl Debug` that uses an explicit work-stack
//! (`Vec<DebugTask>`) to serialize the term iteratively.
//!
//! ## Architecture
//!
//! - `DebugTask` enum: one variant per category + `WriteStr` + `WriteString`
//! - `DEBUG_TASK_POOL` thread-local: reuses the work-stack across calls
//! - `debug_iterative(stack, formatter)`: pops tasks and writes to the formatter
//! - `impl Debug for Cat`: pushes `DebugTask::DebugCat(self as *const Cat)` and delegates
//!
//! The output format exactly matches what `#[derive(Debug)]` would produce:
//! - Nullary:    `PZero`
//! - Literal:    `NumLit(42)`
//! - Var:        `IVar(OrdVar(...))`
//! - Regular:    `AddInt(left, right)` — children become DebugTask pushes
//! - Collection: `PPar(HashBag {...})` — formatted inline via Debug
//! - Binder:     `LamInt(Scope { ... })` — scope decomposed, body pushed as task

#![allow(clippy::cmp_owned)]

use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
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
    let iterative_engine = generate_debug_iterative_engine(language);
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_debug_impl(&lang_type.name, language))
        .collect();

    quote! {
        #debug_task_enum
        #iterative_engine
        #(#impls)*
    }
}

// =============================================================================
// DebugTask Enum + TLS Pool
// =============================================================================

/// Generate the `DebugTask` enum with one variant per category,
/// plus `WriteStr` and `WriteString` for formatting glue.
fn generate_debug_task_enum(language: &LanguageDef) -> TokenStream {
    let category_variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Debug{}", cat);
            quote! {
                #variant_name(*const #cat)
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative Debug engine.
        ///
        /// Each category variant wraps a raw pointer to a term to format.
        /// The pointer is derived from a `&Cat` reference within the same
        /// `fmt()` call, so the referent is guaranteed to be alive for the
        /// duration. `WriteStr` and `WriteString` emit literal text (commas,
        /// parens, field separators).
        #[allow(dead_code)]
        enum DebugTask {
            #(#category_variants,)*
            /// Write a static string literal.
            WriteStr(&'static str),
            /// Write an owned string.
            WriteString(String),
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
        /// order for correct left-to-right output). WriteStr/WriteString
        /// tasks emit literal text.
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
                    DebugTask::WriteString(ref s) => {
                        f.write_str(s)?;
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

    // PRE-PEEL body (residual #11-2, 2026-07-14): the variant match inlined the
    // whole category into `debug_iterative`. Commented-out-never-deleted; the
    // match now lives in `debug_visit_<cat>` and this arm just calls it.
    /*
    let variants = collect_category_variants(category, language);

    let variant_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_debug_variant_arm(category, v, language))
        .collect();

    quote! {
        DebugTask::#variant_name(ptr) => {
            // SAFETY: ptr was derived from a &Cat reference within the same
            // fmt() call; the referent is alive for the entire duration.
            let term = unsafe { &*ptr };
            match term {
                #(#variant_arms,)*
            }
        }
    }
    */
    quote! {
        DebugTask::#variant_name(ptr) => {
            #helper_fn(stack, f, ptr)?;
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
        VariantKind::Nullary { label } => {
            let label_str = label.to_string();
            quote! {
                #category::#label => {
                    f.write_str(#label_str)?;
                }
            }
        },

        // Stage 0 identity: Debug prints the payload via its own `Debug`, which
        // is correct for a collection wrapper too (it recurses structurally).
        VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
            let label_str = label.to_string();
            // Pattern destructures owned term, val is owned. Debug::fmt takes &self.
            quote! {
                #category::#label(val) => {
                    f.write_str(#label_str)?;
                    f.write_str("(")?;
                    std::fmt::Debug::fmt(&val, f)?;
                    f.write_str(")")?;
                }
            }
        },

        VariantKind::Var { label } => {
            let label_str = label.to_string();
            // OrdVar has its own Debug implementation
            quote! {
                #category::#label(var) => {
                    f.write_str(#label_str)?;
                    f.write_str("(")?;
                    std::fmt::Debug::fmt(&var, f)?;
                    f.write_str(")")?;
                }
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_debug_regular_arm(category, label, fields, language)
        },

        VariantKind::Collection { label, .. } => generate_debug_collection_arm(category, label),

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_debug_binder_arm(category, label, pre_scope_fields, body_cat, false)
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_debug_binder_arm(category, label, pre_scope_fields, body_cat, true)
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

    // Build push statements in reverse order for correct output ordering.
    // The stack is LIFO, so the first thing we push is the last thing printed.
    // We want: Label(field0, field1, ..., fieldN)
    //
    // Push order (first pushed = last printed):
    //   ")"
    //   fieldN
    //   ", "
    //   fieldN-1
    //   ...
    //   ", "
    //   field0
    //
    // Then we write "Label(" immediately.
    let mut push_stmts: Vec<TokenStream> = Vec::new();

    // Push closing paren (last to print, first to push)
    push_stmts.push(quote! { stack.push(DebugTask::WriteStr(")")); });

    for (i, (field, fname)) in fields.iter().zip(field_names.iter()).enumerate().rev() {
        // Separator before this field (in output order), but not before field 0
        if i < fields.len() - 1 {
            push_stmts.push(quote! { stack.push(DebugTask::WriteStr(", ")); });
        }

        if field.is_optional {
            if field.is_collection {
                // Phase 4 #3 (2026-05-12): Optional-Collection — format
                // the entire Option<Container> via Debug (containers derive
                // or implement Debug; elements derive Debug).
                push_stmts.push(quote! {
                    if let Some(__c) = #fname.as_ref() {
                        stack.push(DebugTask::WriteString(format!("Some({:?})", __c)));
                    } else {
                        stack.push(DebugTask::WriteStr("None"));
                    }
                });
                continue;
            }
            // Opt-Group: emit "Some(...)" with inner Debug-recursive, or
            // bare "None". Push order is reverse of output order (LIFO).
            let is_known_category = language.types.iter().any(|t| t.name == field.category);
            if is_known_category {
                let task_variant = format_ident!("Debug{}", field.category);
                push_stmts.push(quote! {
                    if let Some(__b) = #fname.as_ref() {
                        // Output order: "Some(" then inner then ")"
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::#task_variant(__b.as_ref() as *const _));
                        stack.push(DebugTask::WriteStr("Some("));
                    } else {
                        stack.push(DebugTask::WriteStr("None"));
                    }
                });
            } else {
                push_stmts.push(quote! {
                    stack.push(DebugTask::WriteString(format!("{:?}", #fname)));
                });
            }
            continue;
        }
        if field.is_collection {
            // Collection fields (Vec<T>, HashBag<T>, HashSet<T>): format inline via Debug
            push_stmts.push(quote! {
                stack.push(DebugTask::WriteString(format!("{:?}", #fname)));
            });
        } else {
            // Boxed category field: *fname gives the inner T from Box<T>
            let is_known_category = language.types.iter().any(|t| t.name == field.category);
            if is_known_category {
                let task_variant = format_ident!("Debug{}", field.category);
                push_stmts.push(quote! {
                    stack.push(DebugTask::#task_variant(&**#fname as *const _));
                });
            } else {
                // Unknown type — fall back to Debug of the boxed value
                push_stmts.push(quote! {
                    stack.push(DebugTask::WriteString(format!("{:?}", #fname)));
                });
            }
        }
    }

    quote! {
        #category::#label(#(#field_names),*) => {
            f.write_str(#label_str)?;
            f.write_str("(")?;
            #(#push_stmts)*
        }
    }
}

/// Generate Debug arm for Collection variant (top-level collection constructor).
///
/// The single collection field is formatted inline using its own Debug impl.
fn generate_debug_collection_arm(category: &Ident, label: &Ident) -> TokenStream {
    let label_str = label.to_string();

    quote! {
        #category::#label(coll) => {
            f.write_str(#label_str)?;
            f.write_str("(")?;
            std::fmt::Debug::fmt(&coll, f)?;
            f.write_str(")")?;
        }
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
    _is_multi: bool,
) -> TokenStream {
    let label_str = label.to_string();

    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1]; // last field is the scope

    // Pre-scope fields are formatted inline using their Debug
    let pre_scope_prints: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, _field)| {
            let fname = &field_names[i];
            quote! {
                std::fmt::Debug::fmt(&#fname, f)?;
                f.write_str(", ")?;
            }
        })
        .collect();

    let body_task_variant = format_ident!("Debug{}", body_cat);

    quote! {
        #category::#label(#(#field_names),*) => {
            f.write_str(#label_str)?;
            f.write_str("(")?;
            #(#pre_scope_prints)*
            // Format scope structure: Scope { pattern: ..., body: <pushed> }
            let inner = #scope_name.inner();
            f.write_str("Scope { pattern: ")?;
            std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
            f.write_str(", body: ")?;
            // Push closing text, then body task (reverse order for LIFO)
            stack.push(DebugTask::WriteStr(")"));
            stack.push(DebugTask::WriteStr(" }"));
            stack.push(DebugTask::#body_task_variant(
                &*inner.unsafe_body as *const _
            ));
            // The loop will process: body -> " }" -> ")"
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
                    stack.push(DebugTask::#task_variant(self as *const #category));
                    let result = debug_iterative(&mut stack, f);
                    cell.set(stack);
                    result
                });
                match result {
                    Ok(fmt_result) => fmt_result,
                    Err(_) => {
                        let mut stack = Vec::new();
                        stack.push(DebugTask::#task_variant(self as *const #category));
                        debug_iterative(&mut stack, f)
                    }
                }
            }
        }
    }
}
