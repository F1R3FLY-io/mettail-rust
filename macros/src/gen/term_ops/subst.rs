//! Iterative (PDA) substitution generation for MeTTaIL terms.
//!
//! Generates stack-safe substitution methods that traverse term trees via an
//! explicit work-stack rather than recursive calls. This is required because
//! naively-recursive `subst`/`subst_by_name_<cat>`/`unify_freevars_impl`
//! methods across many categories create mutual recursion loops
//! (`Proc::subst_by_name_name` → `Name::subst_by_name_name` → `Proc::…`),
//! which stack-overflow even on small inputs (5-deep AST × 13 categories ≈
//! 65 frames per layer × fixed-point iterations).
//!
//! ## Architecture — unified PDA across 4 operation flavors
//!
//! One work-stack + one result buffer + one op-stack handles all four subst
//! flavors:
//! 1. **Same-category substitution** (`subst(vars, repls: &[Self])`)
//! 2. **Cross-category substitution** (`subst_<R>(vars, repls: &[R])`)
//! 3. **Environment substitution** (`subst_by_name_<R>(env_map)`)
//! 4. **FreeVar unification** (`unify_freevars_impl()`)
//!
//! The **op** carried with each Visit task discriminates which flavor is
//! active. Op variants `Match<R>`, `Env<R>`, and `Unify` are matched in the
//! Var visit arms; non-Var arms do not need to inspect the op at all (they
//! just allocate child slots and push children with the same op_idx).
//!
//! At binder descent, if the binder's category matches the op's replacement
//! category, a filtered op is appended to the ops vec and the body Visit
//! gets the new op_idx. Pre-scope fields visit with the UNFILTERED op.
//!
//! ## Phases
//!
//! **Phase 1 (Visit)**: Walk top-down. For each non-leaf node, allocate
//! result slots for children, push an Assemble task, then push Visit tasks
//! for children. Stack is LIFO, so children pop (and process) before the
//! parent's Assemble.
//!
//! **Phase 2 (Assemble)**: When popped, read substituted children from
//! result slots and reconstruct the parent.
//!
//! ## Re-entrancy
//!
//! Re-entrant calls (e.g., `substitute_env` calls `subst_by_name_<R>`
//! repeatedly, and later calls `normalize()` which calls `substitute_<D>`
//! for β-reduction) are safe because the TLS pools follow the `take`/`set`
//! discipline: nested calls get an empty Vec (because the outer already
//! took), do their own allocations, and set back — overwriting the cell
//! with THEIR buffer. The outermost call's `set` at the end reasserts its
//! own buffer. No cross-contamination of pools.

#![allow(clippy::cmp_owned)]

use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::{CollectionType, TypeExpr};
use crate::gen::{generate_literal_label, generate_var_label, is_literal_rule, is_var_rule};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Variant Kind — Unified representation of AST variants (shared with
// iterative_clone.rs, iterative_cmp.rs, etc. via `pub(crate)`)
// =============================================================================

/// Represents a variant of an AST enum for substitution purposes.
/// Abstracts over both old (BNFC) and new (judgement) syntax.
#[derive(Debug, Clone)]
pub(crate) enum VariantKind {
    /// Variable variant: PVar(OrdVar)
    Var { label: Ident },
    /// Literal variant: NumLit(i32)
    Literal { label: Ident },
    /// Nullary constructor: PZero
    Nullary { label: Ident },
    /// Regular constructor with fields: Add(Box<Int>, Box<Int>)
    Regular { label: Ident, fields: Vec<FieldInfo> },
    /// Collection constructor: PPar(HashBag<Proc>)
    Collection {
        label: Ident,
        element_cat: Ident,
        coll_type: CollectionType,
    },
    /// Single binder: PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>)
    Binder {
        label: Ident,
        pre_scope_fields: Vec<FieldInfo>,
        binder_cat: Ident,
        body_cat: Ident,
    },
    /// Multi-binder: PInputs(Vec<Name>, Scope<Vec<Binder<String>>, Box<Proc>>)
    MultiBinder {
        label: Ident,
        pre_scope_fields: Vec<FieldInfo>,
        binder_cat: Ident,
        body_cat: Ident,
    },
}

/// Information about a field in a constructor
#[derive(Debug, Clone)]
pub(crate) struct FieldInfo {
    /// The category of this field (e.g., Proc, Name)
    pub(crate) category: Ident,
    /// Whether this is a collection field
    pub(crate) is_collection: bool,
    /// Collection type if is_collection is true
    pub(crate) coll_type: Option<CollectionType>,
    /// Whether this field is a runtime `BehavioralPred` (from a
    /// `?guard:Guard` slot). Predicate fields are passed through
    /// unchanged during substitution — variable names inside
    /// predicates are not FreeVars of the host category and do not
    /// participate in alpha-conversion. (Phase 3A, predicated types.)
    pub(crate) is_predicate: bool,
}

// =============================================================================
// Main Entry Points
// =============================================================================

/// Generate the substitution PDA (enums, TLS pools, driver) plus per-category
/// `subst` / `substitute` / `subst_<R>` / `substitute_<R>` / `multi_substitute*`
/// wrapper methods.
///
/// Emitted output:
/// ```ignore
/// enum AnySubstTerm { Wrap<Cat>(<Cat>), ... }
/// enum SubstOp       { Match<R>{vars,repls}, Env<R>{env_map}, Unify, ... }
/// enum SubstTask     { Visit<Cat>{src,slot,op_idx}, Assemble<Cat>_<Label>{...}, ... }
/// thread_local!    { SUBST_TASK_POOL, SUBST_RESULT_POOL, SUBST_OP_POOL }
/// fn subst_iterative(stack, results, ops) { /* big match-on-task while loop */ }
/// impl <Cat> { pub fn substitute, subst, multi_substitute, ...; cross-cat methods; }
/// ```
pub fn generate_substitution(language: &LanguageDef) -> TokenStream {
    let any_subst_term = generate_any_subst_term_enum(language);
    let subst_op = generate_subst_op_enum(language);
    let subst_task = generate_subst_task_enum(language);
    let subst_tls = generate_subst_tls_pools();
    let subst_driver = generate_subst_driver(language);
    let subst_wrappers: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| generate_subst_wrappers(&t.name, language))
        .collect();

    quote! {
        #any_subst_term
        #subst_op
        #subst_task
        #subst_tls
        #subst_driver
        #(#subst_wrappers)*
    }
}

/// Generate `substitute_env`, `subst_by_name_<R>`, `unify_freevars`, and
/// `unify_freevars_impl` wrappers per exported category. These re-use the
/// PDA driver emitted by `generate_substitution`.
///
/// `substitute_env` remains a fixed-point loop (up to 100 iterations). Each
/// iteration is bounded: one PDA call per replacement category. No mutual
/// recursion, no stack growth proportional to tree depth.
pub fn generate_env_substitution(language: &LanguageDef) -> TokenStream {
    let language_name = &language.name;
    let env_name = format_ident!("{}Env", language_name);

    // Post-HOL-B size reduction: a replacement category `X` only needs
    // full PDA dispatch in `subst_by_name_X` if `X` can host replaceable
    // free variables. For pure-data categories (Int/UInt32/BigInt/…) the
    // method trivially clones. The PDA is still CAPABLE of dispatching —
    // the wrapper just short-circuits the non-variable-bearing replacement
    // categories with an early `self.clone()`. This preserves the API
    // while eliminating per-variant monomorphization cost for those cats.
    let hol_pairs = crate::logic::common::compute_hol_domain_pairs(language);
    let is_variable_bearing = |cat_name: &syn::Ident| -> bool {
        let cat_str = cat_name.to_string();
        hol_pairs.iter().any(|(c, d)| c == &cat_str || d == &cat_str)
            || language
                .terms
                .iter()
                .any(|r| r.category == *cat_name && crate::gen::is_var_rule(r))
    };

    let env_wrappers: Vec<TokenStream> = language
        .types
        .iter()
        .map(|host| {
            let host_cat = &host.name;
            let host_visit = format_ident!("Visit{}", host_cat);
            let host_wrap = format_ident!("Wrap{}", host_cat);

            // Per-replacement-category subst_by_name_<R> methods
            let subst_by_name_methods: Vec<TokenStream> = language
                .types
                .iter()
                .map(|repl| {
                    let repl_cat = &repl.name;
                    let repl_lower = repl_cat.to_string().to_lowercase();
                    let method_name = format_ident!("subst_by_name_{}", repl_lower);
                    let env_variant = format_ident!("Env{}", repl_cat);

                    let body = if is_variable_bearing(repl_cat) {
                        quote! {
                            if env_map.is_empty() { return self.clone(); }
                            let result: Self = SUBST_TASK_POOL.with(|t| {
                                SUBST_RESULT_POOL.with(|r| {
                                    SUBST_OP_POOL.with(|o| {
                                        let mut stack = t.take();
                                        let mut results = r.take();
                                        let mut ops = o.take();
                                        stack.clear();
                                        results.clear();
                                        ops.clear();

                                        results.push(None);
                                        ops.push(SubstOp::#env_variant {
                                            env_map: env_map.clone(),
                                        });
                                        stack.push(SubstTask::#host_visit {
                                            src: self as *const _,
                                            slot: 0,
                                            op_idx: 0,
                                        });

                                        subst_iterative(&mut stack, &mut results, &mut ops);

                                        let root = match results[0].take()
                                            .expect("iterative subst_by_name: root slot empty")
                                        {
                                            AnySubstTerm::#host_wrap(v) => v,
                                            _ => unreachable!(
                                                "iterative subst_by_name: wrong category in root slot"
                                            ),
                                        };

                                        o.set(ops);
                                        r.set(results);
                                        t.set(stack);
                                        root
                                    })
                                })
                            });
                            result
                        }
                    } else {
                        // Stub: replacement category has no variable
                        // producers; the PDA would just clone every
                        // node. Short-circuit to preserve API.
                        quote! {
                            let _ = env_map;
                            self.clone()
                        }
                    };

                    quote! {
                        /// Substitute variables by name from an env map
                        /// (preserves insertion order via IndexMap).
                        fn #method_name(
                            &self,
                            env_map: &indexmap::IndexMap<String, #repl_cat>,
                        ) -> Self {
                            #body
                        }
                    }
                })
                .collect();

            // substitute_env: fixed-point loop, each iter hits every
            // replacement category once. Preserved semantics from the
            // pre-PDA code — unchanged surface behavior.
            let all_subst_calls: Vec<TokenStream> = language
                .types
                .iter()
                .map(|repl| {
                    let field = format_ident!("{}", repl.name.to_string().to_lowercase());
                    let method = format_ident!("subst_by_name_{}", repl.name.to_string().to_lowercase());
                    quote! {
                        result = result.#method(&env.#field.0);
                    }
                })
                .collect();

            quote! {
                impl #host_cat {
                    /// Substitute all environment variables in this term by name.
                    ///
                    /// Replaces all free variables whose names match keys in
                    /// the environment with their corresponding values.
                    /// Uses name-based matching (not FreeVar identity).
                    /// Iterates until fixed point (no more substitutions
                    /// possible). Finally normalizes FreeVar IDs and
                    /// flattens any nested collections.
                    pub fn substitute_env(&self, env: &#env_name) -> Self {
                        let mut result = self.clone();
                        for _ in 0..100 {
                            let prev_str = format!("{}", result);
                            #(#all_subst_calls)*
                            if format!("{}", result) == prev_str {
                                break;
                            }
                        }
                        let result = result.unify_freevars();
                        result.normalize()
                    }

                    #(#subst_by_name_methods)*

                    /// Unify FreeVar IDs by pretty_name using the global
                    /// VAR_CACHE. Ensures all variables with the same
                    /// pretty_name share a single FreeVar ID (required
                    /// for Ascent equality checks when terms originate
                    /// from different parsing contexts).
                    pub fn unify_freevars(&self) -> Self {
                        self.unify_freevars_impl()
                    }

                    /// PDA-driven unify implementation. Walks the whole
                    /// tree via the subst work-stack, canonicalizing
                    /// every Var::Free encountered.
                    pub fn unify_freevars_impl(&self) -> Self {
                        let result: Self = SUBST_TASK_POOL.with(|t| {
                            SUBST_RESULT_POOL.with(|r| {
                                SUBST_OP_POOL.with(|o| {
                                    let mut stack = t.take();
                                    let mut results = r.take();
                                    let mut ops = o.take();
                                    stack.clear();
                                    results.clear();
                                    ops.clear();

                                    results.push(None);
                                    ops.push(SubstOp::Unify);
                                    stack.push(SubstTask::#host_visit {
                                        src: self as *const _,
                                        slot: 0,
                                        op_idx: 0,
                                    });

                                    subst_iterative(&mut stack, &mut results, &mut ops);

                                    let root = match results[0].take()
                                        .expect("iterative unify: root slot empty")
                                    {
                                        AnySubstTerm::#host_wrap(v) => v,
                                        _ => unreachable!("iterative unify: wrong category in root slot"),
                                    };

                                    o.set(ops);
                                    r.set(results);
                                    t.set(stack);
                                    root
                                })
                            })
                        });
                        result
                    }
                }
            }
        })
        .collect();

    quote! {
        #(#env_wrappers)*
    }
}

// =============================================================================
// AnySubstTerm Enum
// =============================================================================

/// Emit `AnySubstTerm` — heterogeneous wrapper for PDA result slots, one
/// variant per exported category (same shape as `AnyClonedTerm`).
fn generate_any_subst_term_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let wrap = format_ident!("Wrap{}", cat);
            quote! { #wrap(#cat) }
        })
        .collect();

    quote! {
        /// Result-buffer element for the iterative substitution engine.
        /// One variant per category so the buffer can hold mixed-category
        /// results during cross-category traversal.
        #[allow(dead_code)]
        enum AnySubstTerm {
            #(#variants),*
        }
    }
}

// =============================================================================
// SubstOp Enum
// =============================================================================

/// Emit `SubstOp` — the operation discriminant carried along each Visit task.
///
/// Three flavors per replacement category:
/// - `Match<R> { vars, repls }` — identity-based substitution (owned Vecs)
/// - `Env<R> { env_map }` — name-based substitution (owned IndexMap)
///
/// Plus `Unify` (no state) for FreeVar canonicalization.
///
/// All variants are owned (no lifetime parameter) so the enum can live in a
/// TLS `Cell`. Root-level wrappers clone their `&[…]` inputs into owned
/// Vecs at entry; filtered variants at binder descent are likewise owned.
fn generate_subst_op_enum(language: &LanguageDef) -> TokenStream {
    let match_variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("Match{}", cat);
            quote! {
                #variant {
                    vars: Vec<mettail_runtime::FreeVar<String>>,
                    repls: Vec<#cat>,
                }
            }
        })
        .collect();

    let env_variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("Env{}", cat);
            quote! {
                #variant {
                    env_map: indexmap::IndexMap<String, #cat>,
                }
            }
        })
        .collect();

    quote! {
        /// Operation discriminant carried along each Visit task.
        ///
        /// - `Match<R>` triggers identity-based substitution at same-R
        ///   Var nodes; filters at same-R Binder descents.
        /// - `Env<R>` triggers name-based substitution at same-R Var
        ///   nodes; filters env_map at same-R Binder descents.
        /// - `Unify` canonicalizes every `Var::Free` via the global
        ///   VAR_CACHE; no filtering at any binder.
        #[allow(dead_code)]
        enum SubstOp {
            #(#match_variants,)*
            #(#env_variants,)*
            Unify,
        }
    }
}

// =============================================================================
// SubstTask Enum
// =============================================================================

/// Emit `SubstTask` — the work-stack frame enum.
///
/// - `Visit<Cat> { src, slot, op_idx }` — initiates substitution of a term
///   at `src`, storing the result in `slot`, under operation `ops[op_idx]`.
/// - `Assemble<Cat>_<Label> { slot, <child slots> }` — reconstructs a parent
///   from already-substituted children (referenced by slot indices).
fn generate_subst_task_enum(language: &LanguageDef) -> TokenStream {
    let visit_variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("Visit{}", cat);
            quote! {
                #variant { src: *const #cat, slot: usize, op_idx: usize }
            }
        })
        .collect();

    let mut assemble_variants: Vec<TokenStream> = Vec::new();
    for lang_type in &language.types {
        let category = &lang_type.name;
        let variants = collect_category_variants(category, language);
        for v in &variants {
            if let Some(asm) = generate_assemble_variant_decl(category, v) {
                assemble_variants.push(asm);
            }
        }
    }

    quote! {
        /// Work-stack frame for the iterative substitution engine.
        #[allow(dead_code, non_camel_case_types)]
        enum SubstTask {
            #(#visit_variants,)*
            #(#assemble_variants,)*
        }
    }
}

/// Emit one Assemble variant declaration for a non-leaf constructor.
/// Returns `None` for leaf variants (Var, Literal, Nullary).
fn generate_assemble_variant_decl(
    category: &Ident,
    variant: &VariantKind,
) -> Option<TokenStream> {
    match variant {
        VariantKind::Var { .. } | VariantKind::Literal { .. } | VariantKind::Nullary { .. } => {
            None
        }

        VariantKind::Regular { label, fields } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            let field_slots: Vec<TokenStream> = fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    if field.is_collection {
                        let start_name = format_ident!("f{}_start", i);
                        let count_name = format_ident!("f{}_count", i);
                        match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                            CollectionType::HashBag | CollectionType::HashMap => {
                                let counts_name = format_ident!("f{}_counts", i);
                                quote! { #start_name: usize, #count_name: usize, #counts_name: Vec<usize> }
                            }
                            _ => {
                                quote! { #start_name: usize, #count_name: usize }
                            }
                        }
                    } else {
                        let slot_name = format_ident!("f{}_slot", i);
                        quote! { #slot_name: usize }
                    }
                })
                .collect();

            Some(quote! {
                #variant_name { slot: usize, #(#field_slots),* }
            })
        }

        VariantKind::Collection { label, coll_type, .. } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            match coll_type {
                CollectionType::HashBag | CollectionType::HashMap => {
                    Some(quote! {
                        #variant_name {
                            slot: usize,
                            elements_start: usize,
                            elements_count: usize,
                            counts_vec: Vec<usize>,
                        }
                    })
                }
                _ => {
                    Some(quote! {
                        #variant_name {
                            slot: usize,
                            elements_start: usize,
                            elements_count: usize,
                        }
                    })
                }
            }
        }

        VariantKind::Binder { label, pre_scope_fields, .. } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            let pre_field_slots = emit_pre_field_decl_list(pre_scope_fields);

            Some(quote! {
                #variant_name {
                    slot: usize,
                    #(#pre_field_slots,)*
                    cloned_pattern: mettail_runtime::Binder<String>,
                    body_slot: usize,
                }
            })
        }

        VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            let pre_field_slots = emit_pre_field_decl_list(pre_scope_fields);

            Some(quote! {
                #variant_name {
                    slot: usize,
                    #(#pre_field_slots,)*
                    cloned_pattern: Vec<mettail_runtime::Binder<String>>,
                    body_slot: usize,
                }
            })
        }
    }
}

/// Emit the list of pre-scope field slot declarations for a Binder/MultiBinder
/// Assemble variant. Predicate fields become bare `BehavioralPred` fields;
/// collection fields become (start, count, [counts]) tuples; regular fields
/// become single-slot indices.
fn emit_pre_field_decl_list(pre_scope_fields: &[FieldInfo]) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name: mettail_runtime::BehavioralPred };
            }
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! { #start_name: usize, #count_name: usize, #counts_name: Vec<usize> }
                    }
                    _ => quote! { #start_name: usize, #count_name: usize },
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                quote! { #slot_name: usize }
            }
        })
        .collect()
}

// =============================================================================
// TLS Pools
// =============================================================================

/// Emit the thread-local pools for the substitution PDA.
///
/// Three pools: the work stack, the result buffer, and the op stack. All
/// are reused across subst calls via the `take`/`set` idiom, giving
/// zero-allocation steady-state after warm-up.
fn generate_subst_tls_pools() -> TokenStream {
    quote! {
        thread_local! {
            /// Pool for reusing `SubstTask` work stacks across subst calls.
            static SUBST_TASK_POOL: std::cell::Cell<Vec<SubstTask>> =
                std::cell::Cell::new(Vec::new());

            /// Pool for reusing result buffers across subst calls.
            static SUBST_RESULT_POOL: std::cell::Cell<Vec<Option<AnySubstTerm>>> =
                std::cell::Cell::new(Vec::new());

            /// Pool for reusing op stacks across subst calls.
            static SUBST_OP_POOL: std::cell::Cell<Vec<SubstOp>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Subst Driver
// =============================================================================

/// Emit the iterative subst driver: one match arm per Visit variant (per
/// category), one match arm per Assemble variant (per non-leaf constructor).
///
/// **Frame-size fix (PDA stack-safety):** Each Visit{Cat} arm is extracted
/// into its own `#[inline(never)]` helper. Without this split, `subst_iterative`
/// becomes one mega-function whose match would require rustc to allocate
/// stack space for every variant's locals up front, overflowing the default
/// 2 MB thread stack.
fn generate_subst_driver(language: &LanguageDef) -> TokenStream {
    // Per-category Visit helpers (one fn per cat).
    let visit_helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| generate_visit_helper_fn(&t.name, language))
        .collect();

    // Tiny dispatch arms that delegate to the per-cat helper.
    let visit_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let visit_variant = format_ident!("Visit{}", cat);
            let helper_fn = format_ident!("subst_visit_{}", cat.to_string().to_lowercase());
            quote! {
                SubstTask::#visit_variant { src, slot, op_idx } => {
                    #helper_fn(stack, results, ops, src, slot, op_idx);
                }
            }
        })
        .collect();

    let mut assemble_arms: Vec<TokenStream> = Vec::new();
    for lang_type in &language.types {
        let category = &lang_type.name;
        let variants = collect_category_variants(category, language);
        for v in &variants {
            if let Some(arm) = generate_assemble_arm_for_variant(category, v) {
                assemble_arms.push(arm);
            }
        }
    }

    quote! {
        #(#visit_helper_fns)*

        /// Iterative subst engine. Processes the work stack until empty.
        ///
        /// # Safety
        ///
        /// All `*const Cat` pointers in `SubstTask::Visit<Cat>` must be valid
        /// for reads for the duration of this function call. This is
        /// guaranteed because they derive from `&self` in the public
        /// wrappers and the source tree is immutable (shared reference).
        #[allow(dead_code, unused_variables, clippy::needless_range_loop, non_snake_case)]
        fn subst_iterative(
            stack: &mut Vec<SubstTask>,
            results: &mut Vec<Option<AnySubstTerm>>,
            ops: &mut Vec<SubstOp>,
        ) {
            while let Some(task) = stack.pop() {
                match task {
                    #(#visit_arms)*
                    #(#assemble_arms)*
                }
            }
        }
    }
}

/// Emit the per-category Visit helper function. Each helper has a single
/// `match src_ref { variants... }` and pushes new tasks onto the shared stack.
fn generate_visit_helper_fn(cat: &Ident, language: &LanguageDef) -> TokenStream {
    let helper_fn = format_ident!("subst_visit_{}", cat.to_string().to_lowercase());
    let variants = collect_category_variants(cat, language);
    let variant_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_visit_variant_arm(cat, v, language))
        .collect();
    quote! {
        #[inline(never)]
        #[allow(dead_code, unused_variables, clippy::needless_range_loop, non_snake_case)]
        fn #helper_fn(
            stack: &mut Vec<SubstTask>,
            results: &mut Vec<Option<AnySubstTerm>>,
            ops: &mut Vec<SubstOp>,
            src: *const #cat,
            slot: usize,
            op_idx: usize,
        ) {
            let src_ref = unsafe { &*src };
            match src_ref {
                #(#variant_arms)*
            }
        }
    }
}

/// Dispatch per-variant Visit handling.
fn generate_visit_variant_arm(
    cat: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        VariantKind::Var { label } => generate_var_visit_arm(cat, label, language),
        VariantKind::Literal { label } => generate_literal_visit_arm(cat, label, language),
        VariantKind::Nullary { label } => generate_nullary_visit_arm(cat, label),
        VariantKind::Regular { label, fields } => {
            generate_regular_visit_arm(cat, label, fields)
        }
        VariantKind::Collection { label, element_cat, coll_type } => {
            generate_collection_visit_arm(cat, label, element_cat, coll_type)
        }
        VariantKind::Binder { label, pre_scope_fields, binder_cat, body_cat } => {
            generate_binder_visit_arm(cat, label, pre_scope_fields, binder_cat, body_cat)
        }
        VariantKind::MultiBinder { label, pre_scope_fields, binder_cat, body_cat } => {
            generate_multi_binder_visit_arm(cat, label, pre_scope_fields, binder_cat, body_cat)
        }
    }
}

/// Literal arm: just wrap the cloned literal value. Mirrors iterative_clone's
/// literal handling. Native literals (i32/String/etc.) may be Copy or Clone.
fn generate_literal_visit_arm(
    cat: &Ident,
    label: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let wrap = format_ident!("Wrap{}", cat);

    // Match the iterative_clone behavior: clone for non-Copy, copy for Copy.
    // Conservative: just clone — works for both.
    let lit_expr = language
        .types
        .iter()
        .find(|t| &t.name == cat)
        .and_then(|t| t.native_type.as_ref())
        .map(|ty| {
            let nt = crate::gen::native::NativeType::from_syn_type(ty);
            if nt.is_string() || nt.is_collection() {
                quote! { #cat::#label(v.clone()) }
            } else {
                quote! { #cat::#label(*v) }
            }
        })
        .unwrap_or_else(|| quote! { #cat::#label(v.clone()) });

    quote! {
        #cat::#label(v) => {
            results[slot] = Some(AnySubstTerm::#wrap(#lit_expr));
        }
    }
}

/// Nullary arm: no children, wrap the bare constructor.
fn generate_nullary_visit_arm(cat: &Ident, label: &Ident) -> TokenStream {
    let wrap = format_ident!("Wrap{}", cat);
    quote! {
        #cat::#label => {
            results[slot] = Some(AnySubstTerm::#wrap(#cat::#label));
        }
    }
}

/// Var arm — this is where the op matters. Sub-match on `&ops[op_idx]`:
/// - `Match<Cat>`: try to replace v.0 via vars/repls identity comparison.
/// - `Env<Cat>`: try to replace v.0 by pretty_name lookup.
/// - `Unify`: canonicalize FreeVar ID via VAR_CACHE.
/// - wildcard: op is for a different category, passthrough clone.
fn generate_var_visit_arm(
    cat: &Ident,
    label: &Ident,
    _language: &LanguageDef,
) -> TokenStream {
    let wrap = format_ident!("Wrap{}", cat);
    let match_variant = format_ident!("Match{}", cat);
    let env_variant = format_ident!("Env{}", cat);

    quote! {
        #cat::#label(v) => {
            match &ops[op_idx] {
                SubstOp::#match_variant { vars, repls } => {
                    let result = 'find: {
                        if let mettail_runtime::Var::Free(ref fv) = v.0 {
                            for (i, var) in vars.iter().enumerate() {
                                if fv == var {
                                    break 'find repls[i].clone();
                                }
                            }
                        }
                        #cat::#label(v.clone())
                    };
                    results[slot] = Some(AnySubstTerm::#wrap(result));
                }
                SubstOp::#env_variant { env_map } => {
                    let result = 'find: {
                        if let mettail_runtime::Var::Free(ref fv) = v.0 {
                            if let Some(name) = &fv.pretty_name {
                                if let Some(replacement) = env_map.get(name) {
                                    break 'find replacement.clone();
                                }
                            }
                        }
                        #cat::#label(v.clone())
                    };
                    results[slot] = Some(AnySubstTerm::#wrap(result));
                }
                SubstOp::Unify => {
                    let new_v = if let mettail_runtime::Var::Free(ref fv) = v.0 {
                        let canonical = mettail_runtime::get_or_insert_var(fv);
                        mettail_runtime::OrdVar(mettail_runtime::Var::Free(canonical))
                    } else {
                        v.clone()
                    };
                    results[slot] = Some(AnySubstTerm::#wrap(#cat::#label(new_v)));
                }
                _ => {
                    // Op is for a different replacement category — no
                    // substitution possible, passthrough clone.
                    results[slot] = Some(AnySubstTerm::#wrap(#cat::#label(v.clone())));
                }
            }
        }
    }
}

/// Regular arm: allocate child slots, push Assemble + per-field Visits with
/// the same op_idx. Collection fields expand to a slot range.
fn generate_regular_visit_arm(
    cat: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);

    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_fields: Vec<TokenStream> = Vec::new();

    for (i, field) in fields.iter().enumerate() {
        let name = &field_names[i];
        let visit_task = format_ident!("Visit{}", field.category);

        if field.is_collection {
            let start_name = format_ident!("f{}_start", i);
            let count_name = format_ident!("f{}_count", i);

            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::HashBag | CollectionType::HashMap => {
                    let counts_name = format_ident!("f{}_counts", i);
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        let mut #counts_name: Vec<usize> = Vec::new();
                        for (_elem, count) in #name.iter() {
                            results.push(None);
                            #counts_name.push(count);
                        }
                        let #count_name = results.len() - #start_name;
                    });
                    push_stmts.push(quote! {
                        for (elem_idx, (elem, _count)) in #name.iter().enumerate() {
                            stack.push(SubstTask::#visit_task {
                                src: elem as *const _,
                                slot: #start_name + elem_idx,
                                op_idx,
                            });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name, #counts_name });
                }
                CollectionType::Vec => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (idx, elem) in #name.iter().enumerate().rev() {
                            stack.push(SubstTask::#visit_task {
                                src: elem as *const _,
                                slot: #start_name + idx,
                                op_idx,
                            });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name });
                }
                CollectionType::HashSet => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (elem_idx, elem) in #name.iter().enumerate() {
                            stack.push(SubstTask::#visit_task {
                                src: elem as *const _,
                                slot: #start_name + elem_idx,
                                op_idx,
                            });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name });
                }
            }
        } else {
            let slot_name = format_ident!("f{}_slot", i);
            alloc_stmts.push(quote! {
                let #slot_name = results.len();
                results.push(None);
            });
            push_stmts.push(quote! {
                stack.push(SubstTask::#visit_task {
                    src: &**#name as *const _,
                    slot: #slot_name,
                    op_idx,
                });
            });
            assemble_fields.push(quote! { #slot_name });
        }
    }

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            #(#alloc_stmts)*
            stack.push(SubstTask::#assemble_variant { slot, #(#assemble_fields),* });
            #(#push_stmts)*
        }
    }
}

/// Collection arm: the top-level collection constructor (e.g. `PPar(HashBag<Proc>)`).
fn generate_collection_visit_arm(
    cat: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);
    let visit_task = format_ident!("Visit{}", element_cat);

    match coll_type {
        CollectionType::HashBag | CollectionType::HashMap => {
            quote! {
                #cat::#label(ref coll) => {
                    let elements_start = results.len();
                    let mut counts_vec: Vec<usize> = Vec::new();
                    for (_elem, count) in coll.iter() {
                        results.push(None);
                        counts_vec.push(count);
                    }
                    let elements_count = results.len() - elements_start;
                    stack.push(SubstTask::#assemble_variant {
                        slot,
                        elements_start,
                        elements_count,
                        counts_vec,
                    });
                    for (elem_idx, (elem, _count)) in coll.iter().enumerate() {
                        stack.push(SubstTask::#visit_task {
                            src: elem as *const _,
                            slot: elements_start + elem_idx,
                            op_idx,
                        });
                    }
                }
            }
        }
        CollectionType::Vec => {
            quote! {
                #cat::#label(ref coll) => {
                    let elements_start = results.len();
                    for _ in 0..coll.len() {
                        results.push(None);
                    }
                    let elements_count = coll.len();
                    stack.push(SubstTask::#assemble_variant {
                        slot,
                        elements_start,
                        elements_count,
                    });
                    for (idx, elem) in coll.iter().enumerate().rev() {
                        stack.push(SubstTask::#visit_task {
                            src: elem as *const _,
                            slot: elements_start + idx,
                            op_idx,
                        });
                    }
                }
            }
        }
        CollectionType::HashSet => {
            quote! {
                #cat::#label(ref coll) => {
                    let elements_start = results.len();
                    for _ in 0..coll.len() {
                        results.push(None);
                    }
                    let elements_count = coll.len();
                    stack.push(SubstTask::#assemble_variant {
                        slot,
                        elements_start,
                        elements_count,
                    });
                    for (elem_idx, elem) in coll.iter().enumerate() {
                        stack.push(SubstTask::#visit_task {
                            src: elem as *const _,
                            slot: elements_start + elem_idx,
                            op_idx,
                        });
                    }
                }
            }
        }
    }
}

/// Binder Visit arm — the main complication. Pre-scope fields get visited
/// with the UNFILTERED op; the body gets a filtered op (if op's R matches
/// binder_cat) or the unfiltered op (otherwise).
fn generate_binder_visit_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    binder_cat: &Ident,
    body_cat: &Ident,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);
    let body_visit = format_ident!("Visit{}", body_cat);
    let match_binder_variant = format_ident!("Match{}", binder_cat);
    let env_binder_variant = format_ident!("Env{}", binder_cat);

    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let (alloc_pre, push_pre, assemble_pre) =
        emit_pre_field_visit_alloc(pre_scope_fields, &field_names);

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let binder = &#scope_name.inner().unsafe_pattern;
            let body = &#scope_name.inner().unsafe_body;

            // Pre-scope allocations (outer op_idx used for pre-fields).
            #(#alloc_pre)*

            // Body slot + cloned binder pattern.
            let body_slot = results.len();
            results.push(None);
            let cloned_pattern = binder.clone();

            // Determine op_idx for body traversal.
            // If the op is Match<BinderCat> or Env<BinderCat>, filter
            // shadowed entries; else pass through unchanged.
            let body_op_idx = match &ops[op_idx] {
                SubstOp::#match_binder_variant { vars, repls } => {
                    let mut fvars: Vec<mettail_runtime::FreeVar<String>> = Vec::with_capacity(vars.len());
                    let mut frepls: Vec<#binder_cat> = Vec::with_capacity(repls.len());
                    for (i, vv) in vars.iter().enumerate() {
                        if binder.0 != *vv {
                            fvars.push(vv.clone());
                            frepls.push(repls[i].clone());
                        }
                    }
                    ops.push(SubstOp::#match_binder_variant { vars: fvars, repls: frepls });
                    ops.len() - 1
                }
                SubstOp::#env_binder_variant { env_map } => {
                    let filtered: indexmap::IndexMap<String, #binder_cat> =
                        if let Some(name) = &binder.0.pretty_name {
                            env_map.iter()
                                .filter(|(k, _)| *k != name)
                                .map(|(k, v)| (k.clone(), v.clone()))
                                .collect()
                        } else {
                            env_map.clone()
                        };
                    ops.push(SubstOp::#env_binder_variant { env_map: filtered });
                    ops.len() - 1
                }
                _ => op_idx,
            };

            stack.push(SubstTask::#assemble_variant {
                slot,
                #(#assemble_pre,)*
                cloned_pattern,
                body_slot,
            });

            // Push body first (pops last after pre-fields), then pre-fields in reverse.
            stack.push(SubstTask::#body_visit {
                src: &**body as *const _,
                slot: body_slot,
                op_idx: body_op_idx,
            });
            #(#push_pre)*
        }
    }
}

/// MultiBinder Visit arm — like Binder but filter against the set of all
/// binder names.
fn generate_multi_binder_visit_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    binder_cat: &Ident,
    body_cat: &Ident,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);
    let body_visit = format_ident!("Visit{}", body_cat);
    let match_binder_variant = format_ident!("Match{}", binder_cat);
    let env_binder_variant = format_ident!("Env{}", binder_cat);

    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let (alloc_pre, push_pre, assemble_pre) =
        emit_pre_field_visit_alloc(pre_scope_fields, &field_names);

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let binders = &#scope_name.inner().unsafe_pattern;
            let body = &#scope_name.inner().unsafe_body;

            #(#alloc_pre)*

            let body_slot = results.len();
            results.push(None);
            let cloned_pattern = binders.clone();

            let body_op_idx = match &ops[op_idx] {
                SubstOp::#match_binder_variant { vars, repls } => {
                    // A var is shadowed if ANY binder in the multi-binder matches it.
                    let mut fvars: Vec<mettail_runtime::FreeVar<String>> = Vec::with_capacity(vars.len());
                    let mut frepls: Vec<#binder_cat> = Vec::with_capacity(repls.len());
                    for (i, vv) in vars.iter().enumerate() {
                        let shadowed = binders.iter().any(|b| b.0 == *vv);
                        if !shadowed {
                            fvars.push(vv.clone());
                            frepls.push(repls[i].clone());
                        }
                    }
                    ops.push(SubstOp::#match_binder_variant { vars: fvars, repls: frepls });
                    ops.len() - 1
                }
                SubstOp::#env_binder_variant { env_map } => {
                    let bound_names: std::collections::HashSet<String> = binders.iter()
                        .filter_map(|b| b.0.pretty_name.clone())
                        .collect();
                    let filtered: indexmap::IndexMap<String, #binder_cat> = env_map.iter()
                        .filter(|(k, _)| !bound_names.contains(*k))
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect();
                    ops.push(SubstOp::#env_binder_variant { env_map: filtered });
                    ops.len() - 1
                }
                _ => op_idx,
            };

            stack.push(SubstTask::#assemble_variant {
                slot,
                #(#assemble_pre,)*
                cloned_pattern,
                body_slot,
            });

            stack.push(SubstTask::#body_visit {
                src: &**body as *const _,
                slot: body_slot,
                op_idx: body_op_idx,
            });
            #(#push_pre)*
        }
    }
}

/// Emit (alloc_stmts, push_stmts, assemble_field_refs) for a Binder's
/// pre-scope fields. Mirrors iterative_clone's approach.
fn emit_pre_field_visit_alloc(
    pre_scope_fields: &[FieldInfo],
    field_names: &[Ident],
) -> (Vec<TokenStream>, Vec<TokenStream>, Vec<TokenStream>) {
    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_refs: Vec<TokenStream> = Vec::new();

    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];

        if field.is_predicate {
            let pred_name = format_ident!("pf{}_pred", i);
            alloc_stmts.push(quote! {
                let #pred_name = #name.clone();
            });
            assemble_refs.push(quote! { #pred_name });
            continue;
        }

        let visit_task = format_ident!("Visit{}", field.category);

        if field.is_collection {
            let start_name = format_ident!("pf{}_start", i);
            let count_name = format_ident!("pf{}_count", i);

            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::HashBag | CollectionType::HashMap => {
                    let counts_name = format_ident!("pf{}_counts", i);
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        let mut #counts_name: Vec<usize> = Vec::new();
                        for (_elem, count) in #name.iter() {
                            results.push(None);
                            #counts_name.push(count);
                        }
                        let #count_name = results.len() - #start_name;
                    });
                    push_stmts.push(quote! {
                        for (elem_idx, (elem, _count)) in #name.iter().enumerate() {
                            stack.push(SubstTask::#visit_task {
                                src: elem as *const _,
                                slot: #start_name + elem_idx,
                                op_idx,
                            });
                        }
                    });
                    assemble_refs.push(quote! { #start_name, #count_name, #counts_name });
                }
                CollectionType::Vec => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (idx, elem) in #name.iter().enumerate().rev() {
                            stack.push(SubstTask::#visit_task {
                                src: elem as *const _,
                                slot: #start_name + idx,
                                op_idx,
                            });
                        }
                    });
                    assemble_refs.push(quote! { #start_name, #count_name });
                }
                CollectionType::HashSet => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (elem_idx, elem) in #name.iter().enumerate() {
                            stack.push(SubstTask::#visit_task {
                                src: elem as *const _,
                                slot: #start_name + elem_idx,
                                op_idx,
                            });
                        }
                    });
                    assemble_refs.push(quote! { #start_name, #count_name });
                }
            }
        } else {
            let slot_name = format_ident!("pf{}_slot", i);
            alloc_stmts.push(quote! {
                let #slot_name = results.len();
                results.push(None);
            });
            push_stmts.push(quote! {
                stack.push(SubstTask::#visit_task {
                    src: &**#name as *const _,
                    slot: #slot_name,
                    op_idx,
                });
            });
            assemble_refs.push(quote! { #slot_name });
        }
    }

    (alloc_stmts, push_stmts, assemble_refs)
}

// =============================================================================
// Assemble Arms
// =============================================================================

/// Dispatch per-variant Assemble arm emission. Leaf variants don't need
/// Assemble arms (they write to results directly during Visit).
fn generate_assemble_arm_for_variant(
    cat: &Ident,
    variant: &VariantKind,
) -> Option<TokenStream> {
    match variant {
        VariantKind::Var { .. } | VariantKind::Literal { .. } | VariantKind::Nullary { .. } => {
            None
        }
        VariantKind::Regular { label, fields } => {
            Some(generate_regular_assemble_arm(cat, label, fields))
        }
        VariantKind::Collection { label, element_cat, coll_type } => {
            Some(generate_collection_assemble_arm(cat, label, element_cat, coll_type))
        }
        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            Some(generate_binder_assemble_arm(cat, label, pre_scope_fields, body_cat))
        }
        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            Some(generate_multi_binder_assemble_arm(cat, label, pre_scope_fields, body_cat))
        }
    }
}

/// Regular variant Assemble: extract each field from its slot (or slot
/// range for collections), reconstruct the boxed-field constructor.
///
/// **Frame-size fix (PDA stack-safety, second tier):** wraps the body in a
/// local `#[inline(never)]` inner fn so per-variant locals (`field_N`,
/// `Box::new(...)`, collection builders) live in the helper's frame instead
/// of `subst_iterative`'s. See `iterative_clone.rs::generate_regular_assemble_arm`
/// for the same idiom.
fn generate_regular_assemble_arm(
    cat: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);

    // Build flat (pat-name, helper-arg-decl, helper-arg-name) lists.
    let mut pat_flat: Vec<TokenStream> = Vec::new();
    let mut decl_flat: Vec<TokenStream> = Vec::new();
    let mut call_flat: Vec<TokenStream> = Vec::new();
    for (i, field) in fields.iter().enumerate() {
        if field.is_collection {
            let start_name = format_ident!("f{}_start", i);
            let count_name = format_ident!("f{}_count", i);
            pat_flat.push(quote! { #start_name });
            decl_flat.push(quote! { #start_name: usize });
            call_flat.push(quote! { #start_name });
            pat_flat.push(quote! { #count_name });
            decl_flat.push(quote! { #count_name: usize });
            call_flat.push(quote! { #count_name });
            if matches!(
                field.coll_type.as_ref().unwrap_or(&CollectionType::Vec),
                CollectionType::HashBag | CollectionType::HashMap
            ) {
                let counts_name = format_ident!("f{}_counts", i);
                pat_flat.push(quote! { #counts_name });
                decl_flat.push(quote! { #counts_name: Vec<usize> });
                call_flat.push(quote! { #counts_name });
            }
        } else {
            let slot_name = format_ident!("f{}_slot", i);
            pat_flat.push(quote! { #slot_name });
            decl_flat.push(quote! { #slot_name: usize });
            call_flat.push(quote! { #slot_name });
        }
    }

    let field_extracts: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| emit_field_extract(i, field))
        .collect();

    let construct_fields: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let result_ident = format_ident!("field_{}", i);
            if field.is_collection {
                quote! { #result_ident }
            } else {
                quote! { Box::new(#result_ident) }
            }
        })
        .collect();

    quote! {
        SubstTask::#assemble_variant { slot, #(#pat_flat),* } => {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn assemble(
                results: &mut Vec<Option<AnySubstTerm>>,
                slot: usize,
                #(#decl_flat),*
            ) {
                #(#field_extracts)*
                results[slot] = Some(AnySubstTerm::#wrap(
                    #cat::#label(#(#construct_fields),*)
                ));
            }
            assemble(results, slot, #(#call_flat),*);
        }
    }
}

/// Extract the result for a single field from a slot (or slot range).
fn emit_field_extract(i: usize, field: &FieldInfo) -> TokenStream {
    let result_ident = format_ident!("field_{}", i);
    let wrap = format_ident!("Wrap{}", field.category);

    if field.is_collection {
        let start_name = format_ident!("f{}_start", i);
        let count_name = format_ident!("f{}_count", i);

        match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
            CollectionType::HashBag | CollectionType::HashMap => {
                let counts_name = format_ident!("f{}_counts", i);
                quote! {
                    let mut #result_ident = mettail_runtime::HashBag::new();
                    for (idx, count) in #counts_name.iter().enumerate() {
                        match results[#start_name + idx].take()
                            .expect("iterative subst: missing collection element")
                        {
                            AnySubstTerm::#wrap(v) => #result_ident.insert_n(v, *count),
                            _ => unreachable!(
                                "iterative subst: wrong category in collection slot"
                            ),
                        }
                    }
                }
            }
            CollectionType::Vec => {
                quote! {
                    let mut #result_ident = Vec::with_capacity(#count_name);
                    for idx in 0..#count_name {
                        match results[#start_name + idx].take()
                            .expect("iterative subst: missing vec element")
                        {
                            AnySubstTerm::#wrap(v) => #result_ident.push(v),
                            _ => unreachable!("iterative subst: wrong category in vec slot"),
                        }
                    }
                }
            }
            CollectionType::HashSet => {
                quote! {
                    let mut #result_ident = std::collections::HashSet::with_capacity(#count_name);
                    for idx in 0..#count_name {
                        match results[#start_name + idx].take()
                            .expect("iterative subst: missing hashset element")
                        {
                            AnySubstTerm::#wrap(v) => { #result_ident.insert(v); },
                            _ => unreachable!("iterative subst: wrong category in hashset slot"),
                        }
                    }
                }
            }
        }
    } else {
        let slot_name = format_ident!("f{}_slot", i);
        quote! {
            let #result_ident = match results[#slot_name].take()
                .expect("iterative subst: missing result in slot")
            {
                AnySubstTerm::#wrap(v) => v,
                _ => unreachable!("iterative subst: wrong category in slot"),
            };
        }
    }
}

/// Collection variant Assemble: reconstruct a single-collection constructor.
/// See `iterative_clone.rs::generate_collection_assemble_arm` for the
/// per-arm `#[inline(never)]` peel rationale.
fn generate_collection_assemble_arm(
    cat: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let elem_wrap = format_ident!("Wrap{}", element_cat);

    match coll_type {
        CollectionType::HashBag | CollectionType::HashMap => {
            quote! {
                SubstTask::#assemble_variant { slot, elements_start, elements_count, counts_vec } => {
                    #[inline(never)]
                    #[allow(dead_code, unused_variables, non_snake_case)]
                    fn assemble(
                        results: &mut Vec<Option<AnySubstTerm>>,
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                        counts_vec: Vec<usize>,
                    ) {
                        let mut bag = mettail_runtime::HashBag::new();
                        for (idx, count) in counts_vec.iter().enumerate() {
                            match results[elements_start + idx].take()
                                .expect("iterative subst: missing hashbag element")
                            {
                                AnySubstTerm::#elem_wrap(v) => bag.insert_n(v, *count),
                                _ => unreachable!("iterative subst: wrong category in hashbag slot"),
                            }
                        }
                        results[slot] = Some(AnySubstTerm::#wrap(#cat::#label(bag)));
                    }
                    assemble(results, slot, elements_start, elements_count, counts_vec);
                }
            }
        }
        CollectionType::Vec => {
            quote! {
                SubstTask::#assemble_variant { slot, elements_start, elements_count } => {
                    #[inline(never)]
                    #[allow(dead_code, unused_variables, non_snake_case)]
                    fn assemble(
                        results: &mut Vec<Option<AnySubstTerm>>,
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                    ) {
                        let mut vec = Vec::with_capacity(elements_count);
                        for idx in 0..elements_count {
                            match results[elements_start + idx].take()
                                .expect("iterative subst: missing vec element")
                            {
                                AnySubstTerm::#elem_wrap(v) => vec.push(v),
                                _ => unreachable!("iterative subst: wrong category in vec slot"),
                            }
                        }
                        results[slot] = Some(AnySubstTerm::#wrap(#cat::#label(vec)));
                    }
                    assemble(results, slot, elements_start, elements_count);
                }
            }
        }
        CollectionType::HashSet => {
            quote! {
                SubstTask::#assemble_variant { slot, elements_start, elements_count } => {
                    #[inline(never)]
                    #[allow(dead_code, unused_variables, non_snake_case)]
                    fn assemble(
                        results: &mut Vec<Option<AnySubstTerm>>,
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                    ) {
                        let mut set = std::collections::HashSet::with_capacity(elements_count);
                        for idx in 0..elements_count {
                            match results[elements_start + idx].take()
                                .expect("iterative subst: missing hashset element")
                            {
                                AnySubstTerm::#elem_wrap(v) => { set.insert(v); },
                                _ => unreachable!("iterative subst: wrong category in hashset slot"),
                            }
                        }
                        results[slot] = Some(AnySubstTerm::#wrap(#cat::#label(set)));
                    }
                    assemble(results, slot, elements_start, elements_count);
                }
            }
        }
    }
}

/// Binder Assemble: extract pre-fields + body, rebuild the scope.
fn generate_binder_assemble_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let body_wrap = format_ident!("Wrap{}", body_cat);

    let slot_pattern = emit_pre_field_assemble_slot_pattern(pre_scope_fields);
    let pre_extracts = emit_pre_field_extracts(pre_scope_fields);
    let pre_construct = emit_pre_field_constructs(pre_scope_fields);

    quote! {
        SubstTask::#assemble_variant { slot, #(#slot_pattern,)* cloned_pattern, body_slot } => {
            #(#pre_extracts)*
            let body = match results[body_slot].take()
                .expect("iterative subst: missing binder body")
            {
                AnySubstTerm::#body_wrap(v) => v,
                _ => unreachable!("iterative subst: wrong category in binder body slot"),
            };
            let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, Box::new(body));
            results[slot] = Some(AnySubstTerm::#wrap(
                #cat::#label(#(#pre_construct)* new_scope)
            ));
        }
    }
}

/// MultiBinder Assemble: same as Binder but cloned_pattern is a Vec.
fn generate_multi_binder_assemble_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let body_wrap = format_ident!("Wrap{}", body_cat);

    let slot_pattern = emit_pre_field_assemble_slot_pattern(pre_scope_fields);
    let pre_extracts = emit_pre_field_extracts(pre_scope_fields);
    let pre_construct = emit_pre_field_constructs(pre_scope_fields);

    quote! {
        SubstTask::#assemble_variant { slot, #(#slot_pattern,)* cloned_pattern, body_slot } => {
            #(#pre_extracts)*
            let body = match results[body_slot].take()
                .expect("iterative subst: missing multi-binder body")
            {
                AnySubstTerm::#body_wrap(v) => v,
                _ => unreachable!(
                    "iterative subst: wrong category in multi-binder body slot"
                ),
            };
            let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, Box::new(body));
            results[slot] = Some(AnySubstTerm::#wrap(
                #cat::#label(#(#pre_construct)* new_scope)
            ));
        }
    }
}

/// Slot pattern list for a Binder/MultiBinder Assemble arm's destructure.
fn emit_pre_field_assemble_slot_pattern(pre_scope_fields: &[FieldInfo]) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name };
            }
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! { #start_name, #count_name, #counts_name }
                    }
                    _ => quote! { #start_name, #count_name },
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                quote! { #slot_name }
            }
        })
        .collect()
}

/// Extract each pre-scope field into a local `pre_field_{i}` binding.
/// Predicate fields are already in scope as `pf{i}_pred` — no extract needed.
fn emit_pre_field_extracts(pre_scope_fields: &[FieldInfo]) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_predicate {
                return quote! {};
            }
            let wrap = format_ident!("Wrap{}", field.category);
            let result_ident = format_ident!("pre_field_{}", i);

            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! {
                            let mut #result_ident = mettail_runtime::HashBag::new();
                            for (idx, count) in #counts_name.iter().enumerate() {
                                match results[#start_name + idx].take()
                                    .expect("iterative subst: missing pre-scope collection element")
                                {
                                    AnySubstTerm::#wrap(v) => #result_ident.insert_n(v, *count),
                                    _ => unreachable!(
                                        "iterative subst: wrong category in pre-scope collection slot"
                                    ),
                                }
                            }
                        }
                    }
                    CollectionType::Vec => {
                        quote! {
                            let mut #result_ident = Vec::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take()
                                    .expect("iterative subst: missing pre-scope vec element")
                                {
                                    AnySubstTerm::#wrap(v) => #result_ident.push(v),
                                    _ => unreachable!(
                                        "iterative subst: wrong category in pre-scope vec slot"
                                    ),
                                }
                            }
                        }
                    }
                    CollectionType::HashSet => {
                        quote! {
                            let mut #result_ident = std::collections::HashSet::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take()
                                    .expect("iterative subst: missing pre-scope hashset element")
                                {
                                    AnySubstTerm::#wrap(v) => { #result_ident.insert(v); },
                                    _ => unreachable!(
                                        "iterative subst: wrong category in pre-scope hashset slot"
                                    ),
                                }
                            }
                        }
                    }
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                quote! {
                    let #result_ident = match results[#slot_name].take()
                        .expect("iterative subst: missing pre-scope result")
                    {
                        AnySubstTerm::#wrap(v) => v,
                        _ => unreachable!(
                            "iterative subst: wrong category in pre-scope slot"
                        ),
                    };
                }
            }
        })
        .collect()
}

/// Emit the pre-scope-field constructor arguments (with Box wrapping for
/// non-collection, non-predicate fields). Uses trailing commas so they can
/// be interspersed before `new_scope` in the constructor.
fn emit_pre_field_constructs(pre_scope_fields: &[FieldInfo]) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name, };
            }
            let result_ident = format_ident!("pre_field_{}", i);
            if field.is_collection {
                quote! { #result_ident, }
            } else {
                quote! { Box::new(#result_ident), }
            }
        })
        .collect()
}

// =============================================================================
// Subst Wrappers
// =============================================================================

/// Emit the per-category `impl Cat { substitute/subst/multi_substitute +
/// cross-cat subst_<R> / substitute_<R> / multi_substitute_<R> }` block.
///
/// All wrappers are thin boilerplate around the PDA driver; the driver does
/// the work.
fn generate_subst_wrappers(category: &Ident, language: &LanguageDef) -> TokenStream {
    let category_str = category.to_string();
    let host_visit = format_ident!("Visit{}", category);
    let host_wrap = format_ident!("Wrap{}", category);
    let match_self_variant = format_ident!("Match{}", category);

    // Same-category aliases
    let self_alias = format_ident!("subst_{}", category_str.to_lowercase());
    let substitute_self_alias = format_ident!("substitute_{}", category_str.to_lowercase());
    let multi_substitute_self_alias =
        format_ident!("multi_substitute_{}", category_str.to_lowercase());

    // Cross-category methods. Each emits a thin wrapper that pushes
    // SubstOp::Match<R> onto the op stack and invokes the PDA.
    let cross_methods: Vec<TokenStream> = language
        .types
        .iter()
        .filter(|t| t.name != *category)
        .map(|t| {
            let repl_cat = &t.name;
            let repl_lower = repl_cat.to_string().to_lowercase();
            let method_name = format_ident!("subst_{}", repl_lower);
            let substitute_alias = format_ident!("substitute_{}", repl_lower);
            let multi_substitute_alias = format_ident!("multi_substitute_{}", repl_lower);
            let match_variant = format_ident!("Match{}", repl_cat);

            quote! {
                /// Cross-category substitution: replace variables of the
                /// replacement category type with the provided values.
                pub fn #method_name(
                    &self,
                    vars: &[&mettail_runtime::FreeVar<String>],
                    repls: &[#repl_cat],
                ) -> Self {
                    if vars.is_empty() { return self.clone(); }
                    let result: Self = SUBST_TASK_POOL.with(|t| {
                        SUBST_RESULT_POOL.with(|r| {
                            SUBST_OP_POOL.with(|o| {
                                let mut stack = t.take();
                                let mut results = r.take();
                                let mut ops = o.take();
                                stack.clear();
                                results.clear();
                                ops.clear();

                                results.push(None);
                                ops.push(SubstOp::#match_variant {
                                    vars: vars.iter().map(|v| (**v).clone()).collect(),
                                    repls: repls.to_vec(),
                                });
                                stack.push(SubstTask::#host_visit {
                                    src: self as *const _,
                                    slot: 0,
                                    op_idx: 0,
                                });

                                subst_iterative(&mut stack, &mut results, &mut ops);

                                let root = match results[0].take()
                                    .expect("iterative subst: root slot empty")
                                {
                                    AnySubstTerm::#host_wrap(v) => v,
                                    _ => unreachable!(
                                        "iterative subst: wrong category in root slot"
                                    ),
                                };

                                o.set(ops);
                                r.set(results);
                                t.set(stack);
                                root
                            })
                        })
                    });
                    result
                }

                /// Single-variable cross-category substitution (backward
                /// compatibility alias).
                #[inline]
                pub fn #substitute_alias(
                    &self,
                    var: &mettail_runtime::FreeVar<String>,
                    replacement: &#repl_cat,
                ) -> Self {
                    self.#method_name(&[var], &[replacement.clone()])
                }

                /// Multi-variable cross-category substitution alias.
                #[inline]
                pub fn #multi_substitute_alias(
                    &self,
                    vars: &[&mettail_runtime::FreeVar<String>],
                    repls: &[#repl_cat],
                ) -> Self {
                    self.#method_name(vars, repls)
                }
            }
        })
        .collect();

    quote! {
        impl #category {
            /// Single-variable substitution (same category).
            pub fn substitute(
                &self,
                var: &mettail_runtime::FreeVar<String>,
                replacement: &Self,
            ) -> Self {
                self.subst(&[var], &[replacement.clone()])
            }

            /// Multi-variable simultaneous substitution (capture-avoiding).
            pub fn subst(
                &self,
                vars: &[&mettail_runtime::FreeVar<String>],
                repls: &[Self],
            ) -> Self {
                if vars.is_empty() { return self.clone(); }
                let result: Self = SUBST_TASK_POOL.with(|t| {
                    SUBST_RESULT_POOL.with(|r| {
                        SUBST_OP_POOL.with(|o| {
                            let mut stack = t.take();
                            let mut results = r.take();
                            let mut ops = o.take();
                            stack.clear();
                            results.clear();
                            ops.clear();

                            results.push(None);
                            ops.push(SubstOp::#match_self_variant {
                                vars: vars.iter().map(|v| (**v).clone()).collect(),
                                repls: repls.to_vec(),
                            });
                            stack.push(SubstTask::#host_visit {
                                src: self as *const _,
                                slot: 0,
                                op_idx: 0,
                            });

                            subst_iterative(&mut stack, &mut results, &mut ops);

                            let root = match results[0].take()
                                .expect("iterative subst: root slot empty")
                            {
                                AnySubstTerm::#host_wrap(v) => v,
                                _ => unreachable!(
                                    "iterative subst: wrong category in root slot"
                                ),
                            };

                            o.set(ops);
                            r.set(results);
                            t.set(stack);
                            root
                        })
                    })
                });
                result
            }

            /// Backward compatibility alias for `subst`.
            #[inline]
            pub fn multi_substitute(
                &self,
                vars: &[&mettail_runtime::FreeVar<String>],
                repls: &[Self],
            ) -> Self {
                self.subst(vars, repls)
            }

            /// Alias for uniform cross-category calls.
            #[inline]
            pub fn #self_alias(
                &self,
                vars: &[&mettail_runtime::FreeVar<String>],
                repls: &[Self],
            ) -> Self {
                self.subst(vars, repls)
            }

            /// Single-variable substitution alias: `substitute_<cat>`.
            #[inline]
            pub fn #substitute_self_alias(
                &self,
                var: &mettail_runtime::FreeVar<String>,
                replacement: &Self,
            ) -> Self {
                self.substitute(var, replacement)
            }

            /// Backward compatibility alias: `multi_substitute_<cat>`.
            #[inline]
            pub fn #multi_substitute_self_alias(
                &self,
                vars: &[&mettail_runtime::FreeVar<String>],
                repls: &[Self],
            ) -> Self {
                self.subst(vars, repls)
            }

            #(#cross_methods)*
        }
    }
}

// =============================================================================
// Variant Collection (UNCHANGED — shared with iterative_clone.rs and others)
// =============================================================================

/// Collect all variants for a category from grammar rules and auto-generated variants
pub(crate) fn collect_category_variants(
    category: &Ident,
    language: &LanguageDef,
) -> Vec<VariantKind> {
    let mut variants = Vec::new();

    // From grammar rules
    for rule in language.terms.iter().filter(|r| r.category == *category) {
        variants.push(rule_to_variant_kind(rule, language));
    }

    // Auto-generated Var variant (if no explicit Var rule)
    let has_var = variants
        .iter()
        .any(|v| matches!(v, VariantKind::Var { .. }));
    if !has_var {
        variants.push(VariantKind::Var { label: generate_var_label(category) });
    }

    // Auto-generated Literal variant (for native types)
    if let Some(lang_type) = language.get_type(category) {
        if let Some(native_type) = &lang_type.native_type {
            let has_lit = variants
                .iter()
                .any(|v| matches!(v, VariantKind::Literal { .. }));
            if !has_lit {
                variants.push(VariantKind::Literal {
                    label: generate_literal_label(native_type),
                });
            }
        }
    }

    // Auto-generated lambda/Apply variants (post-HOL-B: only for pairs
    // that `compute_hol_domain_pairs` flagged).
    let hol_pairs = crate::logic::common::compute_hol_domain_pairs(language);
    let category_str = category.to_string();

    for domain_lang_type in &language.types {
        let domain_name = &domain_lang_type.name;
        let domain_str = domain_name.to_string();

        if !hol_pairs.contains(&(category_str.clone(), domain_str.clone())) {
            continue;
        }

        // Single-binder lambda: Lam{Domain}
        let lam_label =
            syn::Ident::new(&format!("Lam{}", domain_name), proc_macro2::Span::call_site());
        variants.push(VariantKind::Binder {
            label: lam_label,
            pre_scope_fields: vec![],
            binder_cat: domain_name.clone(),
            body_cat: category.clone(),
        });

        // Multi-binder lambda: MLam{Domain}
        let mlam_label =
            syn::Ident::new(&format!("MLam{}", domain_name), proc_macro2::Span::call_site());
        variants.push(VariantKind::MultiBinder {
            label: mlam_label,
            pre_scope_fields: vec![],
            binder_cat: domain_name.clone(),
            body_cat: category.clone(),
        });

        // Application variant: Apply{Domain}
        let apply_label =
            syn::Ident::new(&format!("Apply{}", domain_name), proc_macro2::Span::call_site());
        variants.push(VariantKind::Regular {
            label: apply_label,
            fields: vec![
                FieldInfo {
                    category: category.clone(),
                    is_collection: false,
                    coll_type: None,
                    is_predicate: false,
                },
                FieldInfo {
                    category: domain_name.clone(),
                    is_collection: false,
                    coll_type: None,
                    is_predicate: false,
                },
            ],
        });

        // Multi-application variant: MApply{Domain}
        let mapply_label =
            syn::Ident::new(&format!("MApply{}", domain_name), proc_macro2::Span::call_site());
        variants.push(VariantKind::Regular {
            label: mapply_label,
            fields: vec![
                FieldInfo {
                    category: category.clone(),
                    is_collection: false,
                    coll_type: None,
                    is_predicate: false,
                },
                FieldInfo {
                    category: domain_name.clone(),
                    is_collection: true,
                    coll_type: Some(CollectionType::Vec),
                    is_predicate: false,
                },
            ],
        });
    }

    variants
}

/// Convert a grammar rule to a VariantKind
pub(crate) fn rule_to_variant_kind(rule: &GrammarRule, _language: &LanguageDef) -> VariantKind {
    let label = rule.label.clone();

    if is_var_rule(rule) {
        return VariantKind::Var { label };
    }

    if is_literal_rule(rule) {
        return VariantKind::Literal { label };
    }

    if let Some(ctx) = &rule.term_context {
        return variant_kind_from_term_context(&label, ctx);
    }

    variant_kind_from_items(&label, &rule.items, &rule.bindings)
}

/// Create VariantKind from new-style term_context
pub(crate) fn variant_kind_from_term_context(label: &Ident, ctx: &[TermParam]) -> VariantKind {
    let multi_abs = ctx.iter().find_map(|p| {
        if let TermParam::MultiAbstraction { ty, .. } = p {
            Some(ty)
        } else {
            None
        }
    });

    if let Some(TypeExpr::Arrow { domain, codomain }) = multi_abs {
        let binder_cat = extract_multi_binder_category(domain);
        let body_cat = extract_base_category(codomain);

        let pre_scope_fields: Vec<FieldInfo> = ctx
            .iter()
            .filter_map(|p| match p {
                TermParam::Simple { ty, .. } => Some(field_info_from_type_expr(ty)),
                TermParam::GuardBody { .. } => Some(field_info_for_guard_slot()),
                _ => None,
            })
            .collect();

        return VariantKind::MultiBinder {
            label: label.clone(),
            pre_scope_fields,
            binder_cat,
            body_cat,
        };
    }

    let single_abs = ctx.iter().find_map(|p| {
        if let TermParam::Abstraction { ty, .. } = p {
            Some(ty)
        } else {
            None
        }
    });

    if let Some(TypeExpr::Arrow { domain, codomain }) = single_abs {
        let binder_cat = extract_base_category(domain);
        let body_cat = extract_base_category(codomain);

        let pre_scope_fields: Vec<FieldInfo> = ctx
            .iter()
            .filter_map(|p| match p {
                TermParam::Simple { ty, .. } => Some(field_info_from_type_expr(ty)),
                TermParam::GuardBody { .. } => Some(field_info_for_guard_slot()),
                _ => None,
            })
            .collect();

        return VariantKind::Binder {
            label: label.clone(),
            pre_scope_fields,
            binder_cat,
            body_cat,
        };
    }

    let fields: Vec<FieldInfo> = ctx
        .iter()
        .filter_map(|p| {
            if let TermParam::Simple { ty, .. } = p {
                Some(field_info_from_type_expr(ty))
            } else {
                None
            }
        })
        .collect();

    if fields.len() == 1 && fields[0].is_collection {
        return VariantKind::Collection {
            label: label.clone(),
            element_cat: fields[0].category.clone(),
            coll_type: fields[0]
                .coll_type
                .clone()
                .unwrap_or(CollectionType::HashBag),
        };
    }

    if fields.is_empty() {
        VariantKind::Nullary { label: label.clone() }
    } else {
        VariantKind::Regular { label: label.clone(), fields }
    }
}

/// Create VariantKind from old-style items + bindings
pub(crate) fn variant_kind_from_items(
    label: &Ident,
    items: &[GrammarItem],
    bindings: &[(usize, Vec<usize>)],
) -> VariantKind {
    let collections: Vec<_> = items
        .iter()
        .filter_map(|item| {
            if let GrammarItem::Collection { element_type, coll_type, .. } = item {
                Some((element_type.clone(), coll_type.clone()))
            } else {
                None
            }
        })
        .collect();

    if collections.len() == 1
        && items
            .iter()
            .filter(|i| !matches!(i, GrammarItem::Terminal(_)))
            .count()
            == 1
    {
        let (element_cat, coll_type) = collections[0].clone();
        return VariantKind::Collection {
            label: label.clone(),
            element_cat,
            coll_type,
        };
    }

    if !bindings.is_empty() {
        let (binder_idx, body_indices) = &bindings[0];
        let body_idx = body_indices[0];

        let binder_cat = match &items[*binder_idx] {
            GrammarItem::Binder { category } => category.clone(),
            _ => panic!("Binding index doesn't point to a Binder"),
        };

        let body_cat = match &items[body_idx] {
            GrammarItem::NonTerminal { ident: cat, .. } => cat.clone(),
            _ => panic!("Body index doesn't point to a NonTerminal"),
        };

        let pre_scope_fields: Vec<FieldInfo> = items
            .iter()
            .take(*binder_idx)
            .filter_map(|item| match item {
                GrammarItem::NonTerminal { ident: cat, kind } if *kind != NonTerminalKind::Var => Some(FieldInfo {
                    category: cat.clone(),
                    is_collection: false,
                    coll_type: None,
                    is_predicate: false,
                }),
                GrammarItem::Collection { element_type, coll_type, .. } => Some(FieldInfo {
                    category: element_type.clone(),
                    is_collection: true,
                    coll_type: Some(coll_type.clone()),
                    is_predicate: false,
                }),
                _ => None,
            })
            .collect();

        return VariantKind::Binder {
            label: label.clone(),
            pre_scope_fields,
            binder_cat,
            body_cat,
        };
    }

    let fields: Vec<FieldInfo> = items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal { ident: cat, kind } if *kind != NonTerminalKind::Var => Some(FieldInfo {
                category: cat.clone(),
                is_collection: false,
                coll_type: None,
                is_predicate: false,
            }),
            GrammarItem::Collection { element_type, coll_type, .. } => Some(FieldInfo {
                category: element_type.clone(),
                is_collection: true,
                coll_type: Some(coll_type.clone()),
                is_predicate: false,
            }),
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        VariantKind::Nullary { label: label.clone() }
    } else {
        VariantKind::Regular { label: label.clone(), fields }
    }
}

// =============================================================================
// Helper Functions for Type Extraction (UNCHANGED)
// =============================================================================

/// Extract the base category from a TypeExpr
fn extract_base_category(ty: &TypeExpr) -> Ident {
    match ty {
        TypeExpr::Base(ident) => ident.clone(),
        TypeExpr::Collection { element, .. } => extract_base_category(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_category(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_category(inner),
        TypeExpr::Refined { base, .. } => extract_base_category(base),
        TypeExpr::Map { value, .. } => extract_base_category(value),
    }
}

/// Extract the binder category from a MultiBinder type (Name* -> ...)
fn extract_multi_binder_category(ty: &TypeExpr) -> Ident {
    match ty {
        TypeExpr::MultiBinder(inner) => extract_base_category(inner),
        _ => extract_base_category(ty),
    }
}

/// Create FieldInfo from a TypeExpr
fn field_info_from_type_expr(ty: &TypeExpr) -> FieldInfo {
    match ty {
        TypeExpr::Base(ident) => FieldInfo {
            category: ident.clone(),
            is_collection: false,
            coll_type: None,
            is_predicate: false,
        },
        TypeExpr::Collection { coll_type, element } => FieldInfo {
            category: extract_base_category(element),
            is_collection: true,
            coll_type: Some(coll_type.clone()),
            is_predicate: false,
        },
        _ => FieldInfo {
            category: format_ident!("Unknown"),
            is_collection: false,
            coll_type: None,
            is_predicate: false,
        },
    }
}

/// Create a synthetic FieldInfo for a `?guard:Guard` slot.
pub(crate) fn field_info_for_guard_slot() -> FieldInfo {
    FieldInfo {
        category: format_ident!("Guard"),
        is_collection: false,
        coll_type: None,
        is_predicate: true,
    }
}
