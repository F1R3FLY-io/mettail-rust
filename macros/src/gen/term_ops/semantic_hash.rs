//! Trampolined (iterative) Semantic Hash generation for MeTTaIL AST enums
//!
//! Generates stack-safe `semantic_hash<H: Hasher>(&self, &mut H)` methods on
//! each category enum encoding **observational equivalence under Ascent's
//! rewrite relation** — distinct from the standard `Hash` impl which encodes
//! structural identity.
//!
//! ## Why two equivalence relations
//!
//! **Standard `Hash` (structural identity):**
//! - `IntToBigRat(NumLit(3))` and `BigIntToBigRat(IntToBigInt(NumLit(3)))`
//!   have different variant tags → different hashes.
//!
//! **`semantic_hash` (observational equivalence):**
//! - Both reduce to the same value under Ascent (the wrappers are pure
//!   identity projections with no syntax / no action).
//! - `semantic_hash` skips the variant tag for transparent wrappers and
//!   delegates to the inner term. Both hash to `semantic_hash(NumLit(3))`.
//!
//! This is the correct lift of Tomita 1986 §6.3 SPPF Symbol-dedup to typed
//! user ASTs: dedup by "what the evaluator can distinguish."
//!
//! ## What counts as a "transparent wrapper"
//!
//! A `GrammarRule` is transparent IFF `classify_simple_projection_shape`
//! returns `Some(...)`:
//! - Single `TermParam::Simple { name, ty: TypeExpr::Base(Source) }` with
//!   `Source != rule.category`.
//! - Single `SyntaxExpr::Param(name)` (zero literals).
//!
//! Examples in Calculator:
//! - `ProcInt . i:Int |- i : Proc`
//! - `IntToBigInt . i:Int |- i : BigInt`
//! - Auto-injected `BoolToBigInt`, `BigIntToBigRat`, etc.
//!
//! NOT transparent:
//! - `Neg . a:Int |- "-" a : Int` (has syntax `"-"`)
//! - `Fact . a:Int |- a "!" : Int` (has syntax `"!"`)
//! - `Add . a:Int, b:Int |- a "+" b : Int` (multiple params + syntax)
//!
//! ## Use sites
//!
//! - `from_alternatives` codegen (Stage 2.3.1): dedup by semantic_hash to
//!   collapse cast-permutation cohorts without losing the `-3!`-style
//!   evaluatively-distinct alts.
//! - `substitute_env` codegen (Stage 2.3.2): same.
//! - `parse_preserving_vars` codegen (Stage 2.3.3): same, weight-aligned.
//!
//! ## Architecture: Iterative Work Stack (same as `iterative_hash.rs`)
//!
//! 1. Each variant arm WRITES discriminant inline (NOT in dispatch fn) so
//!    transparent variants can SKIP the discriminant write.
//! 2. `Box<T>` children are pushed as `SemanticHashTask` variants onto a
//!    thread-local work stack — no recursion across category boundaries.
//! 3. Re-entrancy safety: `try_with` for thread-shutdown gracefully degrades
//!    to a local stack.
//!
//! ## Generated Items
//!
//! - `SemanticHashTask` enum: one variant per category holding `*const Cat`
//! - `SEMANTIC_HASH_TASK_POOL`: thread-local pool
//! - `semantic_hash_iterative<H: Hasher>(&mut Vec<SemanticHashTask>, &mut H)`
//! - `impl Cat { pub fn semantic_hash<H>(&self, &mut H) }` for each category

use crate::gen::runtime::wpda_codegen::builtin_metadata::classify_simple_projection_shape;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use syn::Ident;

pub fn generate_semantic_hash(language: &LanguageDef) -> TokenStream {
    // Compute the set of transparent-projection labels via the existing
    // classifier. These wrappers contribute nothing to semantic_hash —
    // their inner term's hash is emitted directly, collapsing cast
    // permutations.
    let transparent_labels: HashSet<String> = language
        .terms
        .iter()
        .filter(|r| classify_simple_projection_shape(r).is_some())
        .map(|r| r.label.to_string())
        .collect();

    let task_enum = generate_semantic_task_enum(language);
    let engine = generate_semantic_engine(language, &transparent_labels);
    let impls = generate_semantic_impls(language);

    quote! {
        #task_enum
        #engine
        #impls
    }
}

// =============================================================================
// SemanticHashTask Enum + TLS Pool
// =============================================================================

fn generate_semantic_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("SemHash{}", cat);
            quote! {
                #variant_name(*const #cat)
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative semantic_hash engine (Stage 2.3).
        ///
        /// Each variant wraps a raw pointer to a value of one category.
        /// The engine pops tasks, conditionally emits variant
        /// discriminants (skipped for transparent wrappers), and pushes
        /// child tasks for `Box<T>` fields.
        #[allow(dead_code)]
        enum SemanticHashTask {
            #(#variants),*
        }

        // SAFETY: same justification as `HashTask` in iterative_hash.rs.
        unsafe impl Send for SemanticHashTask {}
        unsafe impl Sync for SemanticHashTask {}

        thread_local! {
            /// Pool for reusing `SemanticHashTask` work stacks across
            /// `semantic_hash()` calls.
            static SEMANTIC_HASH_TASK_POOL: std::cell::Cell<Vec<SemanticHashTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Engine
// =============================================================================

fn generate_semantic_engine(
    language: &LanguageDef,
    transparent_labels: &HashSet<String>,
) -> TokenStream {
    let helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_str = cat.to_string().to_lowercase();
            let helper_fn = format_ident!("semantic_hash_handle_{}", cat_str);
            let variants = collect_category_variants(cat, language);
            // Phase F.13 Stage 2.3.6 (2026-05-23): per-variant indices
            // for per-node u8 discriminator. Reduces semantic_hash byte
            // cost from ~5 bytes/node (tag + label.as_bytes()) to 1
            // byte/node (variant_idx), matching derive(Hash). See
            // [[f13-stage-2-3-semantic-hash]] for the chain_10000
            // +46 % slowdown that motivated this optimization.
            assert!(
                variants.len() <= 255,
                "Category {} has {} variants > 255; semantic_hash variant_idx is u8. \
                 Bump to u16 if a real language hits this.",
                cat,
                variants.len(),
            );
            let variant_arms: Vec<TokenStream> = variants
                .iter()
                .enumerate()
                .map(|(idx, v)| {
                    generate_semantic_variant_arm(cat, idx as u8, v, transparent_labels, language)
                })
                .collect();
            quote! {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn #helper_fn<H: std::hash::Hasher>(
                    stack: &mut Vec<SemanticHashTask>,
                    state: &mut H,
                    ptr: *const #cat,
                ) {
                    let val = unsafe { &*ptr };
                    // NOTE: Unlike iterative_hash, we do NOT emit the
                    // variant discriminant here. Each arm decides for
                    // itself whether to emit a discriminant (transparent
                    // wrappers skip it entirely).
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
            let task_variant = format_ident!("SemHash{}", cat);
            let helper_fn =
                format_ident!("semantic_hash_handle_{}", cat.to_string().to_lowercase());
            quote! {
                SemanticHashTask::#task_variant(ptr) => {
                    #helper_fn(stack, state, ptr);
                }
            }
        })
        .collect();

    quote! {
        #(#helper_fns)*

        /// Iterative semantic_hash engine. Processes the work stack
        /// until empty, hashing each node's fields into `state`.
        #[allow(dead_code, unused_variables)]
        fn semantic_hash_iterative<H: std::hash::Hasher>(
            stack: &mut Vec<SemanticHashTask>,
            state: &mut H,
        ) {
            while let Some(task) = stack.pop() {
                match task {
                    #(#task_arms)*
                }
            }
        }
    }
}

/// Generate match arms for a specific variant in the semantic_hash engine.
///
/// Key difference from iterative_hash: each arm decides whether to emit a
/// discriminant. Transparent wrappers skip the discriminant AND skip the
/// variant tag, delegating directly to the inner child.
fn generate_semantic_variant_arm(
    category: &Ident,
    variant_idx: u8,
    variant: &VariantKind,
    transparent_labels: &HashSet<String>,
    language: &LanguageDef,
) -> TokenStream {
    // Phase F.13 Stage 2.3.6 (2026-05-23): per-variant u8 discriminator
    // replaces (kind_tag + label.as_bytes()). Unique within category;
    // combined with the inner-enum category tag, globally unique. Matches
    // derive(Hash) per-node cost (1 byte) instead of 4-12 bytes.
    match variant {
        VariantKind::Nullary { label } => {
            quote! {
                #category::#label => {
                    state.write_u8(#variant_idx);
                }
            }
        },

        VariantKind::Literal { label } => {
            quote! {
                #category::#label(v) => {
                    state.write_u8(#variant_idx);
                    std::hash::Hash::hash(v, state);
                }
            }
        },

        VariantKind::Var { label } => {
            quote! {
                #category::#label(v) => {
                    state.write_u8(#variant_idx);
                    std::hash::Hash::hash(v, state);
                }
            }
        },

        VariantKind::Regular { label, fields } => generate_semantic_regular_arm(
            category,
            variant_idx,
            label,
            fields,
            transparent_labels,
            language,
        ),

        VariantKind::Collection { label, .. } => {
            // Collections: emit variant_idx + delegate to collection's
            // Hash (its elements may themselves be category types — those
            // would use standard Hash, not semantic_hash. This is a known
            // limitation; semantic equivalence inside collections is
            // approximated by structural equivalence. Future refinement
            // could add a per-element semantic_hash visitor for
            // category-typed collections).
            quote! {
                #category::#label(coll) => {
                    state.write_u8(#variant_idx);
                    std::hash::Hash::hash(coll, state);
                }
            }
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_semantic_binder_arm(category, variant_idx, label, pre_scope_fields, body_cat)
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_semantic_multi_binder_arm(
                category,
                variant_idx,
                label,
                pre_scope_fields,
                body_cat,
            )
        },
    }
}

/// Generate semantic_hash arm for a Regular variant.
///
/// **Transparent-wrapper special case**: if `label` is in
/// `transparent_labels`, the arm emits NO discriminant and NO variant tag.
/// It pushes the single child task onto the stack so the inner term's
/// semantic_hash is written directly into `state`. This is what collapses
/// cast permutations to a canonical core.
fn generate_semantic_regular_arm(
    category: &Ident,
    variant_idx: u8,
    label: &Ident,
    fields: &[FieldInfo],
    transparent_labels: &HashSet<String>,
    _language: &LanguageDef,
) -> TokenStream {
    let label_str = label.to_string();
    let is_transparent = transparent_labels.contains(&label_str);

    if is_transparent {
        // Transparent: single Box<ChildCat> field by definition (verified
        // by classify_simple_projection_shape). Push the child as a
        // SemanticHashTask. NO discriminant write.
        // The inner term's semantic_hash is written by the next iteration
        // of semantic_hash_iterative.
        //
        // This is the cast-cohort collapse: BigRat::IntToBigRat(NumLit(3))
        // and BigRat::BigIntToBigRat(BigInt::IntToBigInt(NumLit(3))) both
        // become "push a task for the inner NumLit(3)" and so emit
        // identical bytes to state.
        debug_assert!(
            fields.len() == 1,
            "Transparent label {} should have exactly 1 field per classify_simple_projection_shape",
            label_str,
        );
        let field = &fields[0];
        if field.is_predicate || field.is_collection || field.is_optional {
            // Shouldn't happen for transparent rules (would fail
            // classify_simple_projection_shape), but be defensive.
            // Fall back to non-transparent behavior.
            quote! {
                #category::#label(inner) => {
                    state.write_u8(#variant_idx);
                    std::hash::Hash::hash(inner, state);
                }
            }
        } else {
            let task_variant = format_ident!("SemHash{}", field.category);
            quote! {
                #category::#label(inner) => {
                    // Transparent wrapper: NO discriminant. Just push the
                    // child's semantic_hash task to the stack.
                    stack.push(SemanticHashTask::#task_variant(&**inner as *const _));
                }
            }
        }
    } else {
        // Non-transparent: emit u8 variant_idx + recurse on fields.
        // Follows the iterative_hash pattern with eager Box<T> hashing
        // when before a collection field, stack push for trailing Box<T>.
        let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();

        let last_coll_idx = fields.iter().rposition(|f| f.is_collection);
        let eager_end = last_coll_idx.map(|i| i + 1).unwrap_or(0);

        let mut final_stmts: Vec<TokenStream> = Vec::new();

        // Emit single-byte variant discriminator ONCE at the top.
        final_stmts.push(quote! {
            state.write_u8(#variant_idx);
        });

        // Fields up to and including last collection: hash eagerly.
        for (i, field) in fields.iter().enumerate().take(eager_end) {
            let name = &field_names[i];
            if field.is_optional && field.is_collection {
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__c) => {
                            state.write_u8(1u8);
                            std::hash::Hash::hash(__c, state);
                        }
                    }
                });
            } else if field.is_optional {
                // Optional Box<T>: discriminant + recurse via standard
                // semantic_hash (re-entrant; bounded because the inner
                // task enters the trampoline).
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__b) => {
                            state.write_u8(1u8);
                            (&**__b).semantic_hash(state);
                        }
                    }
                });
            } else if field.is_predicate {
                // Predicate fields hash inline via standard Hash.
                final_stmts.push(quote! {
                    std::hash::Hash::hash(#name, state);
                });
            } else if field.is_collection {
                final_stmts.push(quote! {
                    std::hash::Hash::hash(#name, state);
                });
            } else {
                // Box<T> before a collection: eager via re-entrant
                // semantic_hash (stack-safe — inner uses the trampoline).
                final_stmts.push(quote! {
                    (&**#name).semantic_hash(state);
                });
            }
        }

        // Trailing Box<T> fields after last collection: push in reverse
        // order so they pop in field order.
        let deferred: Vec<(usize, &FieldInfo)> =
            fields.iter().enumerate().skip(eager_end).collect();

        for &(i, field) in deferred.iter().rev() {
            let name = &field_names[i];
            if field.is_optional && field.is_collection {
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__c) => {
                            state.write_u8(1u8);
                            std::hash::Hash::hash(__c, state);
                        }
                    }
                });
            } else if field.is_optional {
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__b) => {
                            state.write_u8(1u8);
                            (&**__b).semantic_hash(state);
                        }
                    }
                });
            } else if field.is_predicate {
                final_stmts.push(quote! {
                    std::hash::Hash::hash(#name, state);
                });
            } else if field.is_collection {
                final_stmts.push(quote! {
                    std::hash::Hash::hash(#name, state);
                });
            } else {
                let task_variant = format_ident!("SemHash{}", field.category);
                final_stmts.push(quote! {
                    stack.push(SemanticHashTask::#task_variant(&**#name as *const _));
                });
            }
        }

        quote! {
            #category::#label(#(ref #field_names),*) => {
                #(#final_stmts)*
            }
        }
    }
}

/// Generate semantic_hash arm for a Binder variant.
///
/// Binders are never transparent.
fn generate_semantic_binder_arm(
    category: &Ident,
    variant_idx: u8,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
) -> TokenStream {
    let _ = label; // label_str no longer hashed; idx is the discriminator
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let mut hash_stmts: Vec<TokenStream> = Vec::new();

    // Per-variant u8 discriminator (replaces tag + label.as_bytes()).
    hash_stmts.push(quote! {
        state.write_u8(#variant_idx);
    });

    // Hash pre-scope fields eagerly via re-entrant semantic_hash.
    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];
        if field.is_predicate {
            hash_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else if field.is_collection {
            hash_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else {
            hash_stmts.push(quote! {
                (&**#name).semantic_hash(state);
            });
        }
    }

    // Scope: hash pattern eagerly (Binder<String>), push body to stack.
    let body_task = format_ident!("SemHash{}", body_cat);
    hash_stmts.push(quote! {
        {
            std::hash::Hash::hash(&#scope_name.inner().unsafe_pattern, state);
            let body_ptr: *const #body_cat = &*#scope_name.inner().unsafe_body;
            stack.push(SemanticHashTask::#body_task(body_ptr));
        }
    });

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#hash_stmts)*
        }
    }
}

/// Generate semantic_hash arm for a MultiBinder variant.
fn generate_semantic_multi_binder_arm(
    category: &Ident,
    variant_idx: u8,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
) -> TokenStream {
    let _ = label; // label_str no longer hashed; idx is the discriminator
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let mut hash_stmts: Vec<TokenStream> = Vec::new();

    hash_stmts.push(quote! {
        state.write_u8(#variant_idx);
    });

    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];
        if field.is_predicate {
            hash_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else if field.is_collection {
            hash_stmts.push(quote! {
                std::hash::Hash::hash(#name, state);
            });
        } else {
            hash_stmts.push(quote! {
                (&**#name).semantic_hash(state);
            });
        }
    }

    let body_task = format_ident!("SemHash{}", body_cat);
    hash_stmts.push(quote! {
        {
            std::hash::Hash::hash(&#scope_name.inner().unsafe_pattern, state);
            let body_ptr: *const #body_cat = &*#scope_name.inner().unsafe_body;
            stack.push(SemanticHashTask::#body_task(body_ptr));
        }
    });

    quote! {
        #category::#label(#(ref #field_names),*) => {
            #(#hash_stmts)*
        }
    }
}

// =============================================================================
// `impl Cat { pub fn semantic_hash<H>(...) }` for each category
// =============================================================================

fn generate_semantic_impls(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_semantic_impl(&lang_type.name))
        .collect();

    quote! { #(#impls)* }
}

fn generate_semantic_impl(category: &Ident) -> TokenStream {
    let task_variant = format_ident!("SemHash{}", category);

    quote! {
        impl #category {
            /// Hash by observational equivalence under Ascent's rewrite
            /// relation. Transparent projection wrappers (identity
            /// cross-cat casts) are skipped — the inner term's hash is
            /// written directly. Two alts produce identical
            /// semantic_hash iff Ascent would reach identical normal
            /// forms from each (modulo 2⁻⁶⁴ hash collision).
            ///
            /// Stack-safe via trampolined iterative engine (mirrors
            /// `iterative_hash.rs`). No recursion across category
            /// boundaries — all cross-category descents push tasks
            /// onto an explicit work stack.
            #[allow(dead_code)]
            pub fn semantic_hash<H: std::hash::Hasher>(&self, state: &mut H) {
                // Fast path: try TLS pool.
                let tls_result = SEMANTIC_HASH_TASK_POOL.try_with(|cell| {
                    let mut stack = cell.take();
                    let was_empty = stack.is_empty();

                    stack.push(SemanticHashTask::#task_variant(self as *const _));
                    semantic_hash_iterative(&mut stack, state);

                    if was_empty {
                        stack.clear();
                    }
                    cell.set(stack);
                });

                if tls_result.is_ok() {
                    return;
                }

                // Fallback: TLS unavailable (thread shutdown). Local stack.
                let mut stack = vec![SemanticHashTask::#task_variant(self as *const _)];
                semantic_hash_iterative(&mut stack, state);
            }
        }
    }
}
