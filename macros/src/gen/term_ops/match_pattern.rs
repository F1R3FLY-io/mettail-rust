//! First-order pattern matching generation for MeTTaIL terms
//!
//! Generates `match_pattern` / `match_pattern_{cat}` methods for each exported
//! category. These methods take a ground term (`self`) and a pattern (which may
//! contain `FreeVar`s), returning `Option<MatchBindings>` with all matched
//! variable bindings.
//!
//! ## Generated Methods
//!
//! For each category `Cat` with types `{Cat, Other, ...}`:
//! - `match_pattern(&self, pattern: &Cat) -> Option<MatchBindings>` — same-category matching
//! - `match_pattern_other(&self, pattern: &Other) -> Option<MatchBindings>` — cross-category
//!
//! ## Architecture: Iterative Work Stack
//!
//! Pattern matching uses an explicit work stack (`Vec<MatchTask>`) instead of
//! recursive function calls. This mirrors the trampoline parser design and
//! provides stack safety for arbitrarily deep terms (100K+ nesting depth).
//!
//! The `MatchTask` enum is a heterogeneous work item with one variant per
//! category (`MatchProc(Proc, Proc)`, `MatchName(Name, Name)`, etc.). When
//! processing a Regular variant with cross-category fields, the handler pushes
//! `MatchTask::MatchOtherCat(ground_field, pattern_field)` onto the stack.
//!
//! Thread-local pooling (`Cell<Vec<MatchTask>>`) ensures zero allocation in
//! steady state. Re-entrant calls from Collection matching get fresh vectors;
//! the outermost call retains its pool capacity.
//!
//! ## Variant Matching Strategies
//!
//! - **Var**: bind pattern variable to ground term (immediate, no stack push)
//! - **Literal/Nullary**: exact equality (immediate)
//! - **Regular**: push `MatchTask` for each field onto the work stack
//! - **Collection**: inline element-wise matching; each element's `match_pattern`
//!   call re-enters the iterative engine via TLS (bounded by collection size)
//! - **Binder/MultiBinder**: inline scope opening; body `match_pattern` call
//!   re-enters the iterative engine (one re-entry per binder level)

use crate::gen::generate_var_label;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

/// COLL_MATCH_CARDINALITY_GATE — kill-switch for the ★D11 cardinality guard on
/// the UNORDERED collection match arms (`HashBag`, `HashSet`), 2026-07-25.
///
/// A collection pattern must account for every ground element. The unordered
/// arms claimed one ground element per pattern element and never compared
/// cardinalities, so a pattern that is a strict sub-multiset of the ground
/// MATCHED. The ordered `Vec` arm has always had the guard.
///
/// When `false` the guard is omitted ENTIRELY from the emission (the
/// `AT_QUOTED_BIND_GATE` convention), so the generated `match_pattern.rs` is
/// textually byte-identical to the pre-fix baseline. `true` is the SHIP DEFAULT
/// — this IS the fix.
///
/// Direction of change: strictly REMOVES matches, so it can only move a host
/// verdict `Some(true) → None`. Because the host's term arm is positive-only, a
/// removed match becomes a DECLINE and never a `Some(false)`, so differential
/// property (3) cannot break and `declined` may only rise. That is why the
/// false-positive family is landed before the false-negative family.
pub(crate) const COLL_MATCH_CARDINALITY_GATE: bool = true;

/// BINDER_COLL_FIELD_MATCH_GATE — kill-switch for the D1 fix, 2026-07-25.
///
/// A collection FIELD in Binder / MultiBinder PRE-SCOPE position was compared by
/// LENGTH ONLY — `if (**g0).len() != (**p0).len() { return None; }` — so two
/// collections of equal length but entirely different contents MATCHED, and no
/// element ever bound a pattern variable. When `false`, the length-only compare
/// is restored and the emission is byte-identical to the pre-fix baseline.
///
/// Blast radius, measured rather than estimated: exactly THREE generated sites
/// in TWO languages — `class3multi::TaggedInputs` (`Vec<Proc>` and `Vec<Name>`)
/// and `class3opt::PInputsOptTagged` (`Vec<Name>`). All three are `Vec`, so the
/// fix needs only positional element-wise matching; no unordered-collection
/// algorithm is pulled forward from Stage 4.
///
/// (An earlier estimate of ~721 sites came from grepping `len() != ` across the
/// generated tree, which also matches the LEGITIMATE `Vec` collection-arm
/// cardinality checks and the binder-ARITY checks
/// `g_inner.unsafe_pattern.len() != p_inner.unsafe_pattern.len()`. Those are
/// correct and untouched.)
pub(crate) const BINDER_COLL_FIELD_MATCH_GATE: bool = true;

/// D1 — the shared comparison for a category-direct COLLECTION FIELD.
///
/// `gaccess` / `paccess` are the already-dereferenced accessor expressions for
/// the two containers (e.g. `(**g0)`).
///
/// `Vec` is matched POSITIONALLY: cardinality, then element-wise
/// `match_pattern`, merging witnesses — identical in shape to the `Vec` branch
/// of [`generate_collection_match_arm`], which is the verified one.
///
/// Every other collection kind falls back to STRUCTURAL EQUALITY on the whole
/// container. That is deliberately conservative and is not a stub:
///
///  * it is strictly STRONGER than the length-only compare it replaces, so it
///    moves in the false-positive-removing direction that Stage 1 requires;
///  * it is trivially type-correct for every wrapper (derived `PartialEq`),
///    which the existing optional-collection path already relies on;
///  * no language instantiates it today (all three live sites are `Vec`), so
///    writing speculative per-wrapper iteration here would be exactly the
///    mistake that `generate_collection_match_arm` already embodies — three of
///    its four branches have never been compiled and its `HashMap` branch does
///    not type-check. Element-variable binding inside an UNORDERED collection
///    field is owned by Stage 4, which introduces one verified implementation.
fn collection_field_match_tokens(
    field: &FieldInfo,
    gaccess: &TokenStream,
    paccess: &TokenStream,
) -> TokenStream {
    if !BINDER_COLL_FIELD_MATCH_GATE {
        return quote! {
            if #gaccess.len() != #paccess.len() {
                return None;
            }
        };
    }
    match field.coll_type {
        Some(mettail_ast::types::CollectionType::Vec) => quote! {
            {
                let __g_coll = &#gaccess;
                let __p_coll = &#paccess;
                if __g_coll.len() != __p_coll.len() {
                    return None;
                }
                for (__g_elem, __p_elem) in __g_coll.iter().zip(__p_coll.iter()) {
                    match __g_elem.match_pattern(__p_elem) {
                        Some(b) => bindings.merge(b),
                        None => return None,
                    }
                }
            }
        },
        _ => quote! {
            if #gaccess != #paccess {
                return None;
            }
        },
    }
}

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate `MatchBindings` type, `MatchTask` enum, TLS pool, iterative engine,
/// and `match_pattern` methods for all exported categories.
pub fn generate_match_pattern(language: &LanguageDef) -> TokenStream {
    let match_bindings_def = generate_match_bindings_type(language);
    let match_task_enum = generate_match_task_enum(language);
    let iterative_engine = generate_iterative_engine(language);

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_category_match_pattern(&lang_type.name, language))
        .collect();

    quote! {
        #match_bindings_def
        #match_task_enum
        #iterative_engine
        #(#impls)*
    }
}

// =============================================================================
// MatchBindings Runtime Type
// =============================================================================

/// Generate the `MatchBindings` struct and its methods.
///
/// `MatchBindings` accumulates variable bindings during first-order pattern
/// matching across all categories. Each category gets its own binding vector.
fn generate_match_bindings_type(language: &LanguageDef) -> TokenStream {
    // Generate one Vec field per category: name_bindings, proc_bindings, etc.
    let fields: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let field_name = format_ident!("{}_bindings", cat.to_string().to_lowercase());
            quote! {
                pub #field_name: Vec<(String, #cat)>
            }
        })
        .collect();

    // Generate `empty()` — all fields are empty Vecs
    let empty_fields: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let field_name = format_ident!("{}_bindings", t.name.to_string().to_lowercase());
            quote! { #field_name: Vec::new() }
        })
        .collect();

    // Generate per-category constructor: `MatchBindings::proc(name, val)`
    let category_constructors: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_lower = cat.to_string().to_lowercase();
            let method_name = format_ident!("{}", cat_lower);
            let target_field = format_ident!("{}_bindings", cat_lower);

            // All other fields start empty
            let other_fields: Vec<TokenStream> = language
                .types
                .iter()
                .filter(|other| other.name != *cat)
                .map(|other| {
                    let field_name =
                        format_ident!("{}_bindings", other.name.to_string().to_lowercase());
                    quote! { #field_name: Vec::new() }
                })
                .collect();

            quote! {
                /// Create bindings with a single binding for this category.
                pub fn #method_name(var_name: String, val: #cat) -> Self {
                    MatchBindings {
                        #target_field: vec![(var_name, val)],
                        #(#other_fields),*
                    }
                }
            }
        })
        .collect();

    // Generate `merge()` — extend each field from other
    let merge_fields: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let field_name = format_ident!("{}_bindings", t.name.to_string().to_lowercase());
            quote! {
                self.#field_name.extend(other.#field_name);
            }
        })
        .collect();

    // Generate `get_{cat}()` — look up a binding by variable name in a specific category
    let get_methods: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_lower = cat.to_string().to_lowercase();
            let method_name = format_ident!("get_{}", cat_lower);
            let field_name = format_ident!("{}_bindings", cat_lower);

            quote! {
                /// Look up a variable binding in this category by name.
                pub fn #method_name(&self, var_name: &str) -> Option<&#cat> {
                    self.#field_name.iter()
                        .find(|(name, _)| name == var_name)
                        .map(|(_, val)| val)
                }
            }
        })
        .collect();

    quote! {
        /// Bindings collected during first-order pattern matching.
        ///
        /// Accumulates variable bindings from cross-category matching.
        /// Each category has its own binding vector to support typed lookups.
        #[derive(Debug, Clone)]
        pub struct MatchBindings {
            #(#fields),*
        }

        impl MatchBindings {
            /// Create empty bindings (no variables matched).
            pub fn empty() -> Self {
                MatchBindings {
                    #(#empty_fields),*
                }
            }

            #(#category_constructors)*

            /// Merge another set of bindings into this one.
            pub fn merge(&mut self, other: MatchBindings) {
                #(#merge_fields)*
            }

            #(#get_methods)*
        }
    }
}

// =============================================================================
// MatchTask Enum + TLS Pool
// =============================================================================

/// Generate the `MatchTask` enum and thread-local pool.
///
/// `MatchTask` has one variant per category: `MatchProc(Proc, Proc)`,
/// `MatchName(Name, Name)`, etc. This enables the iterative engine to handle
/// cross-category recursion (Proc → Name → Proc) via a single heterogeneous
/// work stack.
fn generate_match_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Match{}", cat);
            quote! {
                /// Match a #cat ground term against a #cat pattern.
                #variant_name(#cat, #cat)
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative match_pattern engine.
        ///
        /// Each variant wraps a `(ground, pattern)` pair for one category.
        /// The iterative engine pops tasks from a `Vec<MatchTask>` work stack,
        /// processes each one (binding variables, checking equality, or pushing
        /// sub-field tasks), and accumulates bindings until the stack is empty
        /// (success) or a constructor clash is detected (failure).
        #[allow(dead_code)]
        enum MatchTask {
            #(#variants),*
        }

        thread_local! {
            /// Pool for reusing `MatchTask` work stacks across calls.
            ///
            /// The `Cell<Vec<MatchTask>>` pattern allows zero-allocation
            /// steady-state operation: the first call allocates, subsequent
            /// calls reuse the same buffer. Re-entrant calls (from Collection
            /// matching) get fresh vectors; the outermost call retains capacity.
            static MATCH_TASK_POOL: std::cell::Cell<Vec<MatchTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Iterative Engine
// =============================================================================

/// Generate the `match_pattern_iterative` function.
///
/// This function processes the `Vec<MatchTask>` work stack until either:
/// - The stack is empty → return `Some(bindings)` (match succeeded)
/// - A constructor clash is detected → return `None` (match failed)
///
/// For Regular variants, sub-field matching pushes new `MatchTask` entries.
/// For Collection/Binder variants, the handler is inline and calls
/// `match_pattern()` for element/body sub-matches (re-entering the engine
/// via TLS — bounded by collection size, not nesting depth).
/// **Frame-size fix (residual #11-2, 2026-07-14):** each category's structural
/// match is peeled into a `#[inline(never)] match_visit_<cat>` helper (the
/// Tier-1 idiom `normalize_iterative` uses). Without it, `match_pattern_iterative`'s
/// -O0 frame is the alloca SUM of every category's variant locals (measured
/// 1,481,688 B for rholang — the second-largest driver, and it runs on the
/// sim/rewrite path whose `gen_rholang_prop` workers use the DEFAULT 2 MiB
/// stack). Helpers return `Option<()>`: the arms' `return None` propagate as
/// the engine's failure (the `?` at the call site turns `None` into the
/// engine's `return None`), and the FreeVar-branch `continue` becomes
/// `return Some(())`. This is a control-flow-equivalent refactor (the arms
/// escape via `return None`/`continue`), not the "pure code motion" the
/// escape-free normalize/subst families use.
fn generate_iterative_engine(language: &LanguageDef) -> TokenStream {
    let visit_helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_match_visit_helper(&lang_type.name, language))
        .collect();
    let category_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_iterative_category_dispatch(&lang_type.name))
        .collect();

    quote! {
        #(#visit_helper_fns)*

        /// Iterative match pattern engine.
        ///
        /// Processes the work stack until empty (success) or a constructor
        /// clash is detected (failure). Stack-safe for arbitrarily deep terms.
        #[allow(dead_code)]
        fn match_pattern_iterative(
            stack: &mut Vec<MatchTask>,
        ) -> Option<MatchBindings> {
            let mut bindings = MatchBindings::empty();

            while let Some(task) = stack.pop() {
                match task {
                    #(#category_arms)*
                }
            }

            Some(bindings)
        }
    }
}

/// Generate the match arm for one category inside the iterative engine.
///
/// Structure:
/// ```text
/// MatchTask::MatchProc(ground, pattern) => {
///     // 1. Variable check: if pattern is FreeVar, bind and continue
///     // 2. Constructor match: switch on (ground, pattern) variants
///     //    - Var/Literal/Nullary: equality check
///     //    - Regular: push sub-field tasks
///     //    - Collection: inline matching with re-entrant match_pattern calls
///     //    - Binder: inline scope open with re-entrant body match_pattern call
///     //    - Constructor clash: return None
/// }
/// ```
/// Emit the per-category `#[inline(never)] match_visit_<cat>` helper (residual
/// #11-2). Frame-bound constraint: this fn's frame carries ONE category's
/// variant locals, so peeling it out of `match_pattern_iterative` bounds the
/// driver frame. Returns `Option<()>` — `None` signals a constructor clash
/// (the engine returns `None`); `Some(())` means the task is done and the
/// match is still viable (the engine loops).
fn generate_match_visit_helper(category: &Ident, language: &LanguageDef) -> TokenStream {
    let helper_fn = format_ident!("match_visit_{}", category.to_string().to_lowercase());
    let var_label = generate_var_label(category);
    let cat_lower = category.to_string().to_lowercase();
    let cat_binding_method = format_ident!("{}", cat_lower);

    let variants = collect_category_variants(category, language);

    let variant_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_iterative_variant_arm(category, v, language))
        .collect();

    // PRE-PEEL body (residual #11-2, 2026-07-14): the FreeVar check + structural
    // match inlined the whole category into `match_pattern_iterative`.
    // Commented-out-never-deleted; the body now lives in `match_visit_<cat>` and
    // `generate_iterative_category_dispatch` emits the thin `?` call arm. The
    // ONLY generated-code change vs the inline form is `continue` -> `return
    // Some(())`; every `return None` inside `#variant_arms` is preserved verbatim
    // (it now returns `Option::<()>::None`, which `?` re-propagates as the
    // engine's `return None`).
    /*
    quote! {
        MatchTask::#variant_name(ground, pattern) => {
            // Variable pattern: bind the entire ground term
            if let #category::#var_label(mettail_runtime::OrdVar(
                mettail_runtime::Var::Free(ref fv)
            )) = pattern {
                if let Some(ref pretty_name) = fv.pretty_name {
                    bindings.merge(MatchBindings::#cat_binding_method(
                        pretty_name.clone(),
                        ground.clone(),
                    ));
                    continue;
                }
            }
            // Structural matching per variant
            match (&ground, &pattern) {
                #(#variant_arms,)*
                // Constructor clash: no match
                _ => return None,
            }
        }
    }
    */
    quote! {
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn #helper_fn(
            stack: &mut Vec<MatchTask>,
            bindings: &mut MatchBindings,
            ground: #category,
            pattern: #category,
        ) -> Option<()> {
            // Variable pattern: bind the entire ground term
            if let #category::#var_label(mettail_runtime::OrdVar(
                mettail_runtime::Var::Free(ref fv)
            )) = pattern {
                if let Some(ref pretty_name) = fv.pretty_name {
                    bindings.merge(MatchBindings::#cat_binding_method(
                        pretty_name.clone(),
                        ground.clone(),
                    ));
                    // Was `continue` in the driver loop: this task is done and
                    // the match is still viable — hand control back to the driver.
                    return Some(());
                }
            }
            // Structural matching per variant
            match (&ground, &pattern) {
                #(#variant_arms,)*
                // Constructor clash: no match
                _ => return None,
            }
            Some(())
        }
    }
}

/// Emit the thin dispatch arm that delegates to the per-category
/// `#[inline(never)] match_visit_<cat>` helper (residual #11-2). The `?`
/// propagates a `None` (clash) as the engine's `return None`.
fn generate_iterative_category_dispatch(category: &Ident) -> TokenStream {
    let variant_name = format_ident!("Match{}", category);
    let helper_fn = format_ident!("match_visit_{}", category.to_string().to_lowercase());
    quote! {
        MatchTask::#variant_name(ground, pattern) => {
            #helper_fn(stack, &mut bindings, ground, pattern)?;
        }
    }
}

/// Generate a match arm for a specific variant inside the iterative engine.
fn generate_iterative_variant_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Var { label } => {
            // Var identity: ground Var == pattern Var
            quote! {
                (#category::#label(v1), #category::#label(v2)) if v1 == v2 => {}
            }
        },

        // Stage 0 identity — MOVES in Stage 4 (equality on the wrapper cannot
        // bind pattern variables inside a collection literal).
        VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
            quote! {
                (#category::#label(v1), #category::#label(v2)) if v1 == v2 => {}
            }
        },

        VariantKind::Nullary { label } => {
            quote! {
                (#category::#label, #category::#label) => {}
            }
        },

        VariantKind::Regular { label, fields } => {
            generate_iterative_regular_arm(category, label, fields, language)
        },

        VariantKind::Collection { label, element_cat, coll_type } => {
            // Collection matching is inline — calls match_pattern() on elements
            // which re-enters the iterative engine (bounded by element count).
            generate_collection_match_arm(category, label, element_cat, coll_type, language)
        },

        VariantKind::Binder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => {
            // Binder matching is inline — calls match_pattern() on body
            // which re-enters the iterative engine (one re-entry per binder).
            generate_binder_match_arm_inline(
                category,
                label,
                pre_scope_fields,
                binder_cat,
                body_cat,
                language,
            )
        },

        VariantKind::MultiBinder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => generate_multi_binder_match_arm_inline(
            category,
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
            language,
        ),
    }
}

/// Generate match arm for Regular variant in the iterative engine.
///
/// Instead of recursive calls, pushes `MatchTask` for each field.
/// Fields are pushed in reverse order so they are processed left-to-right
/// (stack is LIFO).
fn generate_iterative_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    _language: &LanguageDef,
) -> TokenStream {
    // If any field is a collection, return None (same as before).
    if fields.iter().any(|f| f.is_collection) {
        let wildcards: Vec<TokenStream> = (0..fields.len()).map(|_| quote! { _ }).collect();
        return quote! {
            (#category::#label(#(#wildcards),*), #category::#label(#(#wildcards),*)) => {
                return None
            }
        };
    }

    let ground_field_names: Vec<Ident> =
        (0..fields.len()).map(|i| format_ident!("g{}", i)).collect();
    let pattern_field_names: Vec<Ident> =
        (0..fields.len()).map(|i| format_ident!("p{}", i)).collect();

    // Push sub-field tasks in REVERSE order (stack is LIFO, we want left-to-right)
    let field_pushes: Vec<TokenStream> = fields
        .iter()
        .zip(ground_field_names.iter().zip(pattern_field_names.iter()))
        .rev() // reverse for correct processing order
        .map(|(field, (gname, pname))| {
            // Task #14 (Option<Guard>): predicate-FIRST — predicates are
            // compared structurally BY CONVENTION (BehavioralPred is a
            // BoundTerm leaf whose term_eq delegates to Eq; its Quantified
            // variant IS a binder, so alpha-equivalent guards compare
            // unequal — accepted codebase-wide). Byte-for-byte the Binder
            // pre-scope arm in `generate_binder_match_arm_inline`; derived
            // PartialEq covers both the bare and the Option<BehavioralPred>
            // shapes, so no `MatchGuard` task (the Guard pseudo-category
            // has none) and no deref is ever emitted.
            // L9-3: token-text captures compare structurally (String: Eq) — a
            // ground COMM guard/pattern requires byte-equal token text; no
            // MatchTask descent (mirrors the predicate leaf).
            if field.is_predicate || field.is_opaque_leaf() {
                return quote! {
                    if #gname != #pname { return None; }
                };
            }
            let task_variant = format_ident!("Match{}", field.category);
            if field.is_optional {
                if field.is_collection {
                    // Phase 4 #3 (2026-05-12): Optional-Collection — structural
                    // equality on the whole Option<Container>. Element-level
                    // variable patterns inside an optional collection are NOT
                    // supported (would require multiset matching with carrier
                    // for an Option-tag too). Treat as opaque comparison.
                    return quote! {
                        if #gname != #pname { return None; }
                    };
                }
                // Opt-Group: matching on `Option<Box<Cat>>`. Same Some/None
                // discriminant requirement; if both Some, push MatchTask
                // recursively; if mismatched, return None.
                return quote! {
                    match (#gname.as_ref(), #pname.as_ref()) {
                        (None, None) => {}
                        (Some(__g), Some(__p)) => {
                            stack.push(MatchTask::#task_variant(
                                (**__g).clone(),
                                (**__p).clone(),
                            ));
                        }
                        _ => return None,
                    }
                };
            }
            quote! {
                stack.push(MatchTask::#task_variant(
                    (**#gname).clone(),
                    (**#pname).clone(),
                ));
            }
        })
        .collect();

    quote! {
        (#category::#label(#(#ground_field_names),*), #category::#label(#(#pattern_field_names),*)) => {
            #(#field_pushes)*
        }
    }
}

/// Generate inline Collection match arm for the iterative engine.
///
/// Collection matching calls `match_pattern()` on elements, which re-enters
/// the iterative engine via TLS. This is bounded by collection size.
fn generate_collection_match_arm(
    category: &Ident,
    label: &Ident,
    _element_cat: &Ident,
    coll_type: &mettail_ast::types::CollectionType,
    _language: &LanguageDef,
) -> TokenStream {
    let var_label = generate_var_label(category);

    // ★D11 (2026-07-25): the unordered branches claim one ground element per
    // PATTERN element and then stop, so every LEFTOVER ground element was
    // silently ignored and `pattern ⊆ ground` MATCHED. The sibling `Vec` branch
    // below has always compared lengths, so this was an asymmetry rather than a
    // considered choice.
    //
    // CONFIRMED LIVE by direct construction (`languages/tests/
    // collection_cardinality_probe.rs`): a canonical `Proc::PPar` over the bag
    // {1,2,3} matched the pattern bag {1,2}. ⚠ It is NOT reachable from surface
    // syntax — `1 | 2 | 3` parses to the binary infix tree
    // `PParInfix(PParInfix(1,2),3)`, a `Regular` variant whose cardinality is
    // enforced by the tree shape — so it is reachable only through the CANONICAL
    // par form that normalization produces, and the `rho_matches_differential`
    // MATRIX cannot witness it (the host declines that route).
    //
    // A collection pattern must ACCOUNT FOR every ground element. For `HashBag`
    // both sides are flattened by multiplicity first, so this compares MULTISET
    // cardinality, not distinct-element count.
    let cardinality_guard = if COLL_MATCH_CARDINALITY_GATE {
        quote! {
            if g_elems.len() != p_elems.len() {
                return None;
            }
        }
    } else {
        quote! {}
    };

    match coll_type {
        mettail_ast::types::CollectionType::HashBag
        | mettail_ast::types::CollectionType::HashMap
        | mettail_ast::types::CollectionType::PathMap => {
            quote! {
                (#category::#label(g_bag), #category::#label(p_bag)) => {
                    let g_elems: Vec<_> = g_bag.iter()
                        .flat_map(|(elem, count)| std::iter::repeat(elem.clone()).take(count))
                        .collect();
                    let p_elems: Vec<_> = p_bag.iter()
                        .flat_map(|(elem, count)| std::iter::repeat(elem.clone()).take(count))
                        .collect();

                    #cardinality_guard

                    let mut claimed = vec![false; g_elems.len()];

                    for p_elem in &p_elems {
                        let is_var = matches!(
                            p_elem,
                            #category::#var_label(mettail_runtime::OrdVar(
                                mettail_runtime::Var::Free(_)
                            ))
                        );

                        if is_var {
                            if let Some(idx) = claimed.iter().position(|c| !c) {
                                claimed[idx] = true;
                                if let #category::#var_label(mettail_runtime::OrdVar(
                                    mettail_runtime::Var::Free(ref fv)
                                )) = p_elem {
                                    if fv.pretty_name.is_some() {
                                        // Re-enter iterative engine via match_pattern
                                        let sub = p_elem.match_pattern(&g_elems[idx]);
                                        if let Some(b) = sub {
                                            bindings.merge(b);
                                        }
                                    }
                                }
                            } else {
                                return None;
                            }
                        } else {
                            let found = g_elems.iter().enumerate()
                                .find(|(idx, g_elem)| {
                                    // Re-enter iterative engine for structural check
                                    !claimed[*idx] && g_elem.match_pattern(p_elem).is_some()
                                });
                            match found {
                                Some((idx, _)) => {
                                    claimed[idx] = true;
                                    // Re-enter for binding extraction
                                    if let Some(b) = g_elems[idx].match_pattern(p_elem) {
                                        bindings.merge(b);
                                    }
                                }
                                None => return None,
                            }
                        }
                    }
                }
            }
        },
        mettail_ast::types::CollectionType::Vec => {
            quote! {
                (#category::#label(g_vec), #category::#label(p_vec)) => {
                    if g_vec.len() != p_vec.len() {
                        return None;
                    }
                    for (g_elem, p_elem) in g_vec.iter().zip(p_vec.iter()) {
                        // Re-enter iterative engine via match_pattern
                        match g_elem.match_pattern(p_elem) {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                }
            }
        },
        mettail_ast::types::CollectionType::HashSet => {
            quote! {
                (#category::#label(g_set), #category::#label(p_set)) => {
                    let g_elems: Vec<_> = g_set.iter().cloned().collect();
                    let p_elems: Vec<_> = p_set.iter().cloned().collect();

                    #cardinality_guard

                    let mut claimed = vec![false; g_elems.len()];

                    for p_elem in &p_elems {
                        let found = g_elems.iter().enumerate()
                            .find(|(idx, g_elem)| {
                                !claimed[*idx] && g_elem.match_pattern(p_elem).is_some()
                            });
                        match found {
                            Some((idx, _)) => {
                                claimed[idx] = true;
                                if let Some(b) = g_elems[idx].match_pattern(p_elem) {
                                    bindings.merge(b);
                                }
                            }
                            None => return None,
                        }
                    }
                }
            }
        },
    }
}

/// Generate inline Binder match arm for the iterative engine.
///
/// Opens both scopes and calls `match_pattern()` on the bodies, which
/// re-enters the iterative engine (one re-entry per binder level).
/// Pre-scope fields also use `match_pattern()` re-entry.
fn generate_binder_match_arm_inline(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    _binder_cat: &Ident,
    _body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;

    let g_fields: Vec<Ident> = (0..total_fields).map(|i| format_ident!("g{}", i)).collect();
    let p_fields: Vec<Ident> = (0..total_fields).map(|i| format_ident!("p{}", i)).collect();

    let pre_scope_matches: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let gname = &g_fields[i];
            let pname = &p_fields[i];
            // Phase 3A: predicate slots compare via structural equality.
            // A behavioral predicate is treated as an atomic token for
            // matching purposes — `ground.match_pattern(pattern)` succeeds
            // iff the two predicates are structurally equal. Variables
            // inside a predicate are NOT FreeVars of the host category
            // and do not need binding.
            if field.is_predicate || field.is_opaque_leaf() {
                return quote! {
                    if #gname != #pname {
                        return None;
                    }
                };
            }
            // Phase 4 #4 (2026-05-12): Optional-Collection — structural
            // equality on the whole Option<Container>. Element-level
            // variable patterns inside an optional collection are NOT
            // supported (would require multiset matching with carrier
            // for an Option-tag too). Treat as opaque comparison.
            if field.is_optional && field.is_collection {
                return quote! {
                    if #gname != #pname {
                        return None;
                    }
                };
            }
            if field.is_collection {
                // D1 (2026-07-25): was LENGTH-ONLY, so two equal-length
                // collections with different contents matched and no element
                // ever bound a pattern variable.
                collection_field_match_tokens(field, &quote! { (**#gname) }, &quote! { (**#pname) })
            } else {
                // Re-enter iterative engine for pre-scope field matching
                quote! {
                    {
                        let sub_match = (**#gname).match_pattern(&**#pname);
                        match sub_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                }
            }
        })
        .collect();

    let g_scope = &g_fields[total_fields - 1];
    let p_scope = &p_fields[total_fields - 1];

    quote! {
        (#category::#label(#(#g_fields),*), #category::#label(#(#p_fields),*)) => {
            #(#pre_scope_matches)*

            let g_inner = #g_scope.inner();
            let p_inner = #p_scope.inner();

            // Re-enter iterative engine for body matching
            let body_match = (*g_inner.unsafe_body).match_pattern(&*p_inner.unsafe_body);
            match body_match {
                Some(b) => bindings.merge(b),
                None => return None,
            }
        }
    }
}

/// Generate inline MultiBinder match arm for the iterative engine.
fn generate_multi_binder_match_arm_inline(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    _binder_cat: &Ident,
    _body_cat: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;

    let g_fields: Vec<Ident> = (0..total_fields).map(|i| format_ident!("g{}", i)).collect();
    let p_fields: Vec<Ident> = (0..total_fields).map(|i| format_ident!("p{}", i)).collect();

    let pre_scope_matches: Vec<TokenStream> = pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let gname = &g_fields[i];
            let pname = &p_fields[i];
            // Phase 3A: predicate slots compare via structural equality.
            if field.is_predicate || field.is_opaque_leaf() {
                return quote! {
                    if #gname != #pname {
                        return None;
                    }
                };
            }
            // Phase 4 #4 (2026-05-12): Optional-Collection — structural
            // equality on the whole Option<Container>.
            if field.is_optional && field.is_collection {
                return quote! {
                    if #gname != #pname {
                        return None;
                    }
                };
            }
            if field.is_collection {
                // D1 — same defect and same fix as the single-Binder arm above.
                collection_field_match_tokens(field, &quote! { (**#gname) }, &quote! { (**#pname) })
            } else {
                quote! {
                    {
                        let sub_match = (**#gname).match_pattern(&**#pname);
                        match sub_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                }
            }
        })
        .collect();

    let g_scope = &g_fields[total_fields - 1];
    let p_scope = &p_fields[total_fields - 1];

    quote! {
        (#category::#label(#(#g_fields),*), #category::#label(#(#p_fields),*)) => {
            #(#pre_scope_matches)*

            let g_inner = #g_scope.inner();
            let p_inner = #p_scope.inner();

            if g_inner.unsafe_pattern.len() != p_inner.unsafe_pattern.len() {
                return None;
            }

            // Re-enter iterative engine for body matching
            let body_match = (*g_inner.unsafe_body).match_pattern(&*p_inner.unsafe_body);
            match body_match {
                Some(b) => bindings.merge(b),
                None => return None,
            }
        }
    }
}

// =============================================================================
// Per-Category Match Pattern Wrappers
// =============================================================================

/// Generate `match_pattern` impl block for a single category.
///
/// The public `match_pattern` method delegates to the iterative engine via
/// the TLS pool. Cross-category methods remain trivially None.
fn generate_category_match_pattern(category: &Ident, language: &LanguageDef) -> TokenStream {
    let primary_method = format_ident!("match_pattern");
    let self_alias = format_ident!("match_pattern_{}", category.to_string().to_lowercase());
    let task_variant = format_ident!("Match{}", category);

    // Cross-category methods: types don't match so we always return None.
    let cross_methods: Vec<TokenStream> = language
        .types
        .iter()
        .filter(|t| t.name != *category)
        .map(|t| {
            let other_cat = &t.name;
            let other_cat_lower = other_cat.to_string().to_lowercase();
            let method_name = format_ident!("match_pattern_{}", other_cat_lower);

            quote! {
                /// Cross-category pattern matching (always None — types differ).
                #[inline]
                pub fn #method_name(&self, _pattern: &#other_cat) -> Option<MatchBindings> {
                    None
                }
            }
        })
        .collect();

    quote! {
        impl #category {
            /// First-order pattern matching: match `self` (ground term) against
            /// `pattern` (may contain FreeVars).
            ///
            /// Returns `Some(bindings)` if the match succeeds, `None` otherwise.
            /// Variable patterns bind the entire ground term at that position.
            ///
            /// Uses an iterative work stack for stack safety (supports 100K+
            /// nesting depth). Collection and Binder matching re-enter the
            /// engine via this method, bounded by element/binder count.
            pub fn #primary_method(&self, pattern: &#category) -> Option<MatchBindings> {
                MATCH_TASK_POOL.with(|cell| {
                    let mut stack = cell.take();
                    stack.clear();
                    stack.push(MatchTask::#task_variant(self.clone(), pattern.clone()));
                    let result = match_pattern_iterative(&mut stack);
                    cell.set(stack);
                    result
                })
            }

            /// Alias for uniform cross-category dispatch.
            #[inline]
            pub fn #self_alias(&self, pattern: &#category) -> Option<MatchBindings> {
                self.#primary_method(pattern)
            }

            #(#cross_methods)*
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn regular_arm_pred_compares_structurally() {
        // Task #14 gate-1: pre-#14 the Regular arm pushed the nonexistent
        // `MatchTask::MatchGuard` and deref'd the Option payload. The pred
        // arm must be a structural `!=` (the Binder pre-scope precedent),
        // which covers bare AND Option<BehavioralPred> shapes via derived
        // PartialEq.
        let language = crate::gen::empty_language_for_tests();
        let cat = format_ident!("Int");
        let label = format_ident!("PCheck");
        let fields = vec![
            FieldInfo {
                category: format_ident!("Int"),
                is_collection: false,
                coll_type: None,
                is_predicate: false,
                is_optional: false,
                opaque_leaf: None,
            },
            FieldInfo {
                category: format_ident!("Guard"),
                is_collection: false,
                coll_type: None,
                is_predicate: true,
                is_optional: true,
                opaque_leaf: None,
            },
        ];
        let arm = generate_iterative_regular_arm(&cat, &label, &fields, &language).to_string();
        assert!(
            arm.contains("if g1 != p1 { return None ; }"),
            "the pred position must compare structurally: {arm}",
        );
        assert!(
            !arm.contains("MatchGuard"),
            "no Match task exists for the Guard pseudo-category: {arm}",
        );
    }
}
