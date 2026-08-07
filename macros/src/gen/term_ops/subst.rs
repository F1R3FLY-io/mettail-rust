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

use crate::gen::term_param_walk::{TermParamLeafKind, TermParamLeaves};
use crate::gen::type_expr_walk::terminal_base;
use crate::gen::{generate_literal_label, generate_var_label, is_literal_rule, is_var_rule};
use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Variant Kind — Unified representation of AST variants (shared with
// iterative_cmp.rs, iterative_hash.rs, etc. via `pub(crate)`)
// =============================================================================

/// COLLECTION_LITERAL_KIND_GATE — kill-switch for the
/// [`VariantKind::CollectionLiteral`] discriminant (2026-07-25).
///
/// When `false`, [`collect_category_variants`] never constructs the variant, so
/// collection-literal categories fall back to [`VariantKind::Literal`] exactly
/// as they did before this change and every generator emits its pre-change
/// token stream — the generated tree under `target/generated/**` is BYTE-
/// IDENTICAL to the pre-change baseline. The `CollectionLiteral` arms elsewhere
/// remain compiled but unreachable.
///
/// When `true` (SHIP DEFAULT): the discriminant is produced, and each consumer
/// takes the branch it declared. As of Stage 0 every consumer still delegates to
/// its `Literal` behaviour, so `true` is ALSO byte-identical — that identity is
/// the Stage 0 acceptance gate, and it is what makes the subsequent per-consumer
/// moves auditable one at a time.
pub(crate) const COLLECTION_LITERAL_KIND_GATE: bool = true;

/// Represents a variant of an AST enum for substitution purposes.
/// Abstracts over both old (BNFC) and new (judgement) syntax.
#[derive(Debug, Clone)]
pub(crate) enum VariantKind {
    /// ★ #141 G5 — a rule whose AST SHAPE contradicts what the parser built.
    ///
    /// `rule_to_variant_kind` used to `panic!("Binding index doesn't point to a
    /// Binder")` when `GrammarRule::bindings` indexed an item that was not a
    /// binder (or not a non-terminal body). That invariant is established when
    /// `ast/src/grammar.rs` BUILDS the bindings list and is re-checked by
    /// nothing, so the panic was an unproved claim — and a mute one, since a
    /// proc-macro panic under this workspace's cranelift dev backend prints
    /// nothing at all (#141 RED-0).
    ///
    /// It is a DISCRIMINANT rather than a side channel for the same reason this
    /// enum's `CollectionLiteral` is: the exhaustiveness checker performs the
    /// census. Every consumer of a classification must now say what it does with
    /// one that refuses, and cannot silently treat it as some other shape.
    Refused { label: Ident, message: String },
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
    /// Native COLLECTION-LITERAL variant: `List(Vec<Proc>)`, `Bag(HashBag<Proc>)`,
    /// `Set(HashSetLit<Proc>)`, `Map(HashMapLit<Proc,Proc>)`, `Pathmap(PathMapLit<Proc,Proc>)`.
    ///
    /// Distinguished from its two neighbours — the distinction IS the point:
    ///
    /// - vs [`VariantKind::Literal`]: a `Literal` is an OPAQUE native leaf
    ///   (`NumLit(i32)`, `StrLit(String)`) with no sub-terms. A
    ///   `CollectionLiteral` is a native wrapper that CONTAINS element terms of
    ///   `element_cat`. Treating one as the other is the defect this variant
    ///   exists to make unrepresentable: every term op that clones a `Literal`
    ///   payload whole (`subst`, `is_ground`, `term_depth`, `matches`, …) is
    ///   silently WRONG on a collection literal, because it never recurses into
    ///   the elements.
    /// - vs [`VariantKind::Collection`]: a `Collection` is a category-DIRECT
    ///   collection FIELD declared by a grammar rule (`PPar . ps:HashBag(Proc)`),
    ///   so its payload is the bare container. A `CollectionLiteral` is a
    ///   CATEGORY declared as a native-type alias (`![Vec<Proc>] as List`) with
    ///   NO grammar rule, so its payload is the *literal wrapper* type
    ///   (`HashSetLit`, not the iterable `HashSet`). The two need different
    ///   iterator/rebuild shapes — reusing `Collection`'s arms for these
    ///   categories does not compile for Set/Bag (see the note on
    ///   [`collect_category_variants`]).
    ///
    /// Introduced as a distinct discriminant (rather than a predicate over
    /// `Literal`) so that the exhaustiveness checker performs the census: every
    /// present and FUTURE consumer of `VariantKind` is forced to state, at
    /// compile time, which of the two behaviours it wants. A predicate would
    /// leave every existing site free to keep the wrong behaviour silently.
    CollectionLiteral {
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
    /// Opt-Group (2026-04-29): if true, this field's runtime type is
    /// `Option<Box<Cat>>` (or `Option<Scope<...>>` for Optional inner
    /// abstractions, `Option<HashBag<Cat>>` for Optional collections).
    /// Iterators and constructor-emitters wrap reads in
    /// `if let Some(__inner) = field.as_ref() { ... }` and unwrap
    /// `__inner` to a borrow of the inner type. Nested Optional
    /// flattens — the parser-walker never produces `Some(Some(...))`.
    pub(crate) is_optional: bool,
    /// OPAQUE CAPTURE LEAF (L9-3 token-text, L9-4 guest-body): `Some(kind)` iff
    /// this field is a non-category leaf produced by a syntax-pattern capture —
    /// a `v@Tok` token text (`OpaqueLeafKind::TokenText` → `String`) or a `*flt`
    /// guest body (`OpaqueLeafKind::GuestBody` → `Arc<FltNode>`). Both are
    /// handled IDENTICALLY by every term op — like `is_predicate`, they are
    /// plain values that derive `Clone`/`Hash`/`Eq`/`Ord`, carried through
    /// substitution/normalization UNCHANGED (a captured token/body is not a host
    /// term: no free variables, no α-conversion, no β/shift, no descent). The
    /// ONLY per-kind difference is the emitted field TYPE ([`OpaqueLeafKind::
    /// field_type`]); every behavioral site branches on [`FieldInfo::
    /// is_opaque_leaf`] (which never reads the placeholder `category`), so
    /// token-text and guest-body share ONE mechanism with zero duplication.
    pub(crate) opaque_leaf: Option<OpaqueLeafKind>,
}

/// The two opaque capture-leaf field kinds (see [`FieldInfo::opaque_leaf`]).
/// They differ ONLY in the emitted Rust field type; every term op treats them
/// the same (inline hash/cmp, clone-through subst/normalize, no descent).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OpaqueLeafKind {
    /// L9-3: a `v@Tok` token-text capture → `std::string::String`.
    TokenText,
    /// L9-4: a `*flt(node, …)` guest-body capture → `Arc<FltNode>`.
    GuestBody,
}

impl OpaqueLeafKind {
    /// The bare (non-optional) Rust field type for this leaf kind.
    pub(crate) fn field_type(self) -> TokenStream {
        match self {
            OpaqueLeafKind::TokenText => quote! { std::string::String },
            OpaqueLeafKind::GuestBody => {
                quote! { std::sync::Arc<mettail_runtime::FltNode> }
            },
        }
    }
}

impl FieldInfo {
    /// True iff this field is an opaque capture leaf (token-text or guest-body)
    /// — the shared predicate every behavioral term-op branch uses BEFORE
    /// reading `category` (whose value is a placeholder for leaf fields).
    pub(crate) fn is_opaque_leaf(&self) -> bool {
        self.opaque_leaf.is_some()
    }

    /// The Rust field type for an opaque-leaf field (bare, or `Option<…>` when
    /// `is_optional`). Panics if called on a non-leaf field.
    pub(crate) fn opaque_leaf_type(&self) -> TokenStream {
        let base = self
            .opaque_leaf
            .expect("opaque_leaf_type on a non-leaf field")
            .field_type();
        if self.is_optional {
            quote! { Option<#base> }
        } else {
            base
        }
    }
}

// =============================================================================
// Main Entry Points
// =============================================================================

/// Generate the substitution PDA (enums, TLS pools, driver) plus per-category
/// `subst` / `substitute` / `subst_<R>` / `substitute_<R>` / `multi_substitute*`
/// wrapper methods.
///
/// Emitted output:
/// ```text
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

    // A replacement category `X` needs full PDA dispatch in `subst_by_name_X` only if an
    // `X`-typed FREE VARIABLE can occur in a term — otherwise there is nothing for the
    // walk to rewrite and the method may short-circuit to `self.clone()`.
    //
    // ⚠★ #98 — this predicate used to ask the HOL set, and that was a latent
    // unsoundness that only #98 could have detonated. Read carefully before editing:
    //
    //  * The old form was `hol_pairs.iter().any(|(c, d)| c == cat || d == cat) || <cat
    //    has a DECLARED var rule>`. Because `compute_hol_domain_pairs` returned the full
    //    cross-product, `(cat, cat)` was a member for EVERY declared category, so the
    //    first disjunct was unconditionally `true` and the second was dead. The
    //    "size reduction" the old comment described therefore never once fired.
    //  * #98 empties that set for a binderless language. The first disjunct then goes
    //    `false`, and the fallback decides — but the fallback only sees var rules the
    //    grammar DECLARES, whereas `gen/types/enums.rs` emits an auto-injected
    //    `<Cat>Var(OrdVar)` for every category that declares none. Every category has a
    //    variable form; only some declare it. The fallback would thus have answered
    //    `false` for categories that demonstrably hold variables, silently degrading
    //    `subst_by_name_X` to a clone and dropping substitutions on the floor.
    //
    // The predicate now asks the question it actually means, against the same source
    // `enums.rs` uses: does this category have a variable form in its emitted enum? That
    // is true for every declared category — by a DECLARED var rule, else by the
    // auto-injected one — so this is a no-op relative to the pre-#98 behavior (which was
    // also unconditionally `true`, by the accident above). The disjunction is spelled out
    // rather than collapsed to `true` because it names the two sources, so a future
    // change to `enums.rs` that stops emitting a variable form for some category has a
    // matching term here to update instead of a bare literal to rediscover.
    let is_variable_bearing = |cat_name: &syn::Ident| -> bool {
        let declares_var_rule = language
            .terms
            .iter()
            .any(|r| r.category == *cat_name && crate::gen::is_var_rule(r));
        // `enums.rs` emits `#var_label(OrdVar)` for exactly the categories with no
        // declared var rule, so a declared category always has one form or the other.
        let receives_auto_var = language.types.iter().any(|t| t.name == *cat_name);
        declares_var_rule || receives_auto_var
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
                        #[allow(unreachable_patterns)]
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

                    /// Like [`substitute_env`](Self::substitute_env) but WITHOUT the final
                    /// [`normalize`](Self::normalize) — it substitutes every environment-bound free
                    /// variable (to a name-match fixpoint) and unifies FreeVar IDs, but performs NO
                    /// constant folding / β-reduction / collection flattening, so the surface term
                    /// TREE is preserved. This is the structure-preserving substitution the REPL
                    /// `step` command needs: a term such as `1 + 2 * 3` keeps its operator tree
                    /// (rather than collapsing to `7`) so the stepper can show each reduction as a
                    /// navigable one-step rewrite. Backs `substitute_env_preserve_structure`.
                    pub fn substitute_env_no_normalize(&self, env: &#env_name) -> Self {
                        let mut result = self.clone();
                        for _ in 0..100 {
                            let prev_str = format!("{}", result);
                            #(#all_subst_calls)*
                            if format!("{}", result) == prev_str {
                                break;
                            }
                        }
                        result.unify_freevars()
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
                    #[allow(unreachable_patterns)]
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
            if let Some(asm) = generate_assemble_variant_decl(category, v, language) {
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
/// Returns `None` for leaf variants (Var, opaque Literal, Nullary).
///
/// GROUP B (2026-06-30): a `Literal` variant whose category is a *collection*
/// literal (List/Bag/Set/Map/Pathmap) is no longer a leaf — it emits a
/// per-wrapper `Assemble{Cat}_{Label}Lit` task-variant decl so its element
/// results can be reassembled. Opaque literals still return `None`.
fn generate_assemble_variant_decl(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> Option<TokenStream> {
    match variant {
        // ★ #141 G5 — `Some`, never `None`: `None` here means "this variant
        // contributes no arm", which would DISCARD the refusal.
        VariantKind::Refused { message, .. } => Some(quote! { compile_error!(#message); }),
        VariantKind::Var { .. } | VariantKind::Nullary { .. } => None,

        // Stage 0 identity: `CollectionLiteral` delegates to the `Literal` body,
        // which already re-derives `collection_literal_info` itself (returning
        // `None` — a leaf — for opaque literals). Byte-identical either way.
        VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
            let (coll_type, _element_cat) = collection_literal_info(category, language)?;
            let variant_name = format_ident!("Assemble{}_{}Lit", category, label);
            match coll_type {
                // HashBag carries per-distinct-element multiplicities.
                CollectionType::HashBag => Some(quote! {
                    #variant_name {
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                        counts_vec: Vec<usize>,
                    }
                }),
                // Vec / HashSet / HashMap / PathMap: (start, count) only.
                _ => Some(quote! {
                    #variant_name {
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                    }
                }),
            }
        },

        VariantKind::Regular { label, fields } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            let field_slots: Vec<TokenStream> = fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    if field.is_opaque_leaf() {
                        // L9-3/L9-4: opaque capture leaves (token-text `String` /
                        // guest-body `Arc<FltNode>`) ride the Assemble variant as
                        // a cloned carrier (subst never descends — not a host
                        // term). Mirrors is_predicate; type is the leaf's own.
                        let text_name = format_ident!("f{}_text", i);
                        let ty = field.opaque_leaf_type();
                        return quote! { #text_name: #ty };
                    }
                    if field.is_predicate {
                        // Task #14 (Option<Guard>): predicate-FIRST — the
                        // Regular path previously had NO is_predicate arm
                        // anywhere (decl/visit/assemble/extract), so a
                        // Regular-variant guard emitted nonexistent
                        // `SubstTask::VisitGuard` / `AnySubstTerm::WrapGuard`
                        // references. Predicates ride the Assemble variant
                        // as a cloned value (substitution never descends
                        // into predicates — Phase 3A spec at FieldInfo).
                        let pred_name = format_ident!("f{}_pred", i);
                        if field.is_optional {
                            return quote! { #pred_name: Option<mettail_runtime::BehavioralPred> };
                        }
                        return quote! { #pred_name: mettail_runtime::BehavioralPred };
                    }
                    if field.is_optional {
                        if field.is_collection {
                            // Phase 4 #3 (2026-05-12): Optional-Collection — cloned carrier.
                            let cloned = format_ident!("f{}_cloned", i);
                            let ty = optional_collection_field_type_subst(field);
                            return quote! { #cloned: #ty };
                        }
                        let slot_name = format_ident!("f{}_slot", i);
                        let some_flag = format_ident!("f{}_some", i);
                        return quote! { #slot_name: usize, #some_flag: bool };
                    }
                    if field.is_collection {
                        let start_name = format_ident!("f{}_start", i);
                        let count_name = format_ident!("f{}_count", i);
                        match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                            CollectionType::HashBag => {
                                let counts_name = format_ident!("f{}_counts", i);
                                quote! { #start_name: usize, #count_name: usize, #counts_name: Vec<usize> }
                            }
                            // Phase 4 #5b (2026-05-12): HashMap matches the
                            // Vec shape (start + count) — no counts vec.
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
        },

        VariantKind::Collection { label, coll_type, .. } => {
            let variant_name = format_ident!("Assemble{}_{}", category, label);
            match coll_type {
                CollectionType::HashBag | CollectionType::HashMap => Some(quote! {
                    #variant_name {
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                        counts_vec: Vec<usize>,
                    }
                }),
                _ => Some(quote! {
                    #variant_name {
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                    }
                }),
            }
        },

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
        },

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
        },
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
                // Task #14 (Option<Guard>): Option-aware pre-scope decl —
                // dormant until a Binder-rule optional guard exists, but
                // required for decl/clone type agreement.
                if field.is_optional {
                    return quote! { #pred_name: Option<mettail_runtime::BehavioralPred> };
                }
                return quote! { #pred_name: mettail_runtime::BehavioralPred };
            }
            // Phase 4 #4 (2026-05-12): Optional-Collection — cloned carrier
            // (Option<Container>) stored directly in the assemble variant.
            if field.is_optional && field.is_collection {
                let cloned = format_ident!("pf{}_cloned", i);
                let ty = optional_collection_field_type_subst(field);
                return quote! { #cloned: #ty };
            }
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! { #start_name: usize, #count_name: usize, #counts_name: Vec<usize> }
                    },
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
            if let Some(arm) = generate_assemble_arm_for_variant(category, v, language) {
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
        #[allow(
            dead_code,
            unused_variables,
            unreachable_patterns,
            clippy::needless_range_loop,
            non_snake_case
        )]
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
        #[allow(
            dead_code,
            unused_variables,
            unreachable_patterns,
            clippy::needless_range_loop,
            non_snake_case
        )]
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
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Var { label } => generate_var_visit_arm(cat, label, language),
        // Stage 0 identity: `generate_literal_visit_arm` already re-derives
        // `collection_literal_info` and routes to the recursing arm itself.
        VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
            generate_literal_visit_arm(cat, label, language)
        },
        VariantKind::Nullary { label } => generate_nullary_visit_arm(cat, label),
        VariantKind::Regular { label, fields } => generate_regular_visit_arm(cat, label, fields),
        VariantKind::Collection { label, element_cat, coll_type } => {
            generate_collection_visit_arm(cat, label, element_cat, coll_type)
        },
        VariantKind::Binder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => generate_binder_visit_arm(cat, label, pre_scope_fields, binder_cat, body_cat),
        VariantKind::MultiBinder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => generate_multi_binder_visit_arm(cat, label, pre_scope_fields, binder_cat, body_cat),
    }
}

/// GROUP B (2026-06-30): classify a category as a *collection literal* for the
/// substitution engine.
///
/// Collection-literal categories (List/Bag/Set/Map/Pathmap) are declared as
/// native-type aliases (`![Vec<Proc>] as List`, …) with NO grammar rule, so
/// `collect_category_variants` classifies each as the auto-`Literal` fallback.
/// The default `Literal` handling clones the wrapper *whole* and never recurses
/// into the element terms — a real semantic no-op bug: `subst([a,b,c],
/// a:=1,b:=2,c:=3)` returns `[a,b,c]` unchanged.
///
/// Rather than reclassify these categories to `VariantKind::Collection` (which
/// is the SHARED classifier imported by ~14 other generators — flipping the
/// discriminant regresses depth/ground/normalize/semantic_hash/…), we detect
/// them *locally* here and emit recursing visit/assemble arms confined to the
/// three subst-internal functions the importers never call.
///
/// Returns `Some((coll_type, element_cat))` for a collection-literal category,
/// where `coll_type` selects the wrapper's iterator/rebuild shape and
/// `element_cat` is the category of the element terms (e.g. `Proc`). Returns
/// `None` for opaque native literals (Int/Bool/Str/Float/Fixed/BigInt/BigRat/
/// ReadZipper/WriteZipper), which keep their byte-identical `v.clone()` body.
///
/// Hoisted to `pub(crate)` (2026-07-25) because it is now also the SOLE producer
/// predicate for [`VariantKind::CollectionLiteral`] in
/// [`collect_category_variants`], and the sibling term-op generators consume the
/// resulting discriminant.
///
/// ⚠ KNOWN GAP (pinned, fixed separately — see
/// `arm_integrity::readzipper_writezipper_collection_literal_gap`): this
/// resolves through `LanguageDef::collection_element_type_for_category`, whose
/// first branch is hardcoded to the category NAMES
/// `"List" | "Bag" | "Map" | "Set" | "Pathmap"` (`ast/src/language/model.rs`).
/// `ReadZipper`/`WriteZipper` genuinely contain `Proc`s
/// (`ReadZipperLit(PathMapLit<Proc, Proc>, Vec<u8>)`) but are named otherwise,
/// so they return `None` here and are treated as opaque leaves. The landed
/// `subst` fix does not cover them either; this is a pre-existing gap that the
/// new discriminant INHERITS rather than introduces.
pub(crate) fn collection_literal_info(
    cat: &Ident,
    language: &LanguageDef,
) -> Option<(CollectionType, Ident)> {
    let coll_type = language
        .get_type(cat)
        .and_then(|t| t.collection_kind.as_ref())?
        .coll_type();
    let element_cat = language.collection_element_type_for_category(cat)?;
    Some((coll_type, element_cat))
}

/// Literal arm: just wrap the cloned literal value. Native literals
/// (i32/String/etc.) may be Copy or Clone.
///
/// GROUP B (2026-06-30): collection-literal categories (List/Bag/Set/Map/
/// Pathmap) get a *recursing* visit arm (modeled on `generate_collection_visit_
/// arm`) that visits each element term under the same op and defers reassembly
/// to a per-wrapper `Assemble{Cat}_{Label}Lit` task. Opaque literals keep the
/// `v.clone()` body below unchanged.
fn generate_literal_visit_arm(cat: &Ident, label: &Ident, language: &LanguageDef) -> TokenStream {
    let wrap = format_ident!("Wrap{}", cat);

    // GROUP B: collection-literal wrappers recurse into their element terms.
    if let Some((coll_type, element_cat)) = collection_literal_info(cat, language) {
        return generate_collection_literal_visit_arm(cat, label, &element_cat, &coll_type);
    }

    // `v` is bound by reference (`#cat::#label(v)` on a borrowed term), so the
    // payload must be cloned out. Always clone: `v.clone()` resolves to the
    // payload type's `Clone` (not `&T`'s) and is correct for every native type —
    // Copy primitives (i32/bool/…), string/collection wrappers (HashBag,
    // HashSetLit, PathMapLit), and non-Copy structs (Arc<…ZipperLit>) alike.
    // For Copy types the clone compiles to a bitwise copy, so there is no cost.
    let lit_expr = quote! { #cat::#label(v.clone()) };

    quote! {
        #cat::#label(v) => {
            results[slot] = Some(AnySubstTerm::#wrap(#lit_expr));
        }
    }
}

/// GROUP B (2026-06-30): the recursing Visit arm for a collection-literal
/// wrapper. Allocates result slots for the element terms, pushes an
/// `Assemble{Cat}_{Label}Lit` task, then pushes a `Visit{ElemCat}` task per
/// element (under the *unfiltered* op — collection literals introduce no
/// binders). Mirrors `generate_collection_visit_arm` but iterates the literal
/// wrapper's own container and carries the wrapper label in the assemble task
/// name.
///
/// Per-wrapper slot layout:
/// - `Vec` (List)     : N slots, one `Visit{Elem}` per element (reverse order,
///   matching the Vec collection-field template); carries (start, count=N).
/// - `HashBag` (Bag)  : one slot per DISTINCT element + a `counts_vec` of
///   multiplicities; iterate `(&elem, count)`; carries (start, count, counts_vec).
/// - `HashSet` (Set)  : N slots, one `Visit{Elem}` per element; (start, count=N).
/// - `HashMap` (Map)  : 2N slots interleaved key,value; one `Visit{Elem}` each;
///   iterate `(&k, &v)`; carries (start, count=2N).
/// - `PathMap` (Pathmap): identical to `HashMap` (PathMapLit Derefs to HashMapLit).
fn generate_collection_literal_visit_arm(
    cat: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}Lit", cat, label);
    let visit_task = format_ident!("Visit{}", element_cat);

    match coll_type {
        CollectionType::Vec => quote! {
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
        },
        CollectionType::HashSet => quote! {
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
        },
        CollectionType::HashBag => quote! {
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
        },
        // Map: interleave key,value into 2N slots (key at even
        // offsets, value at odd). Both key and value are `element_cat` (Proc).
        CollectionType::HashMap => quote! {
            #cat::#label(ref coll) => {
                let elements_start = results.len();
                for _ in 0..coll.len() {
                    results.push(None); // key slot
                    results.push(None); // value slot
                }
                let elements_count = results.len() - elements_start;
                stack.push(SubstTask::#assemble_variant {
                    slot,
                    elements_start,
                    elements_count,
                });
                for (pair_idx, (k, v)) in coll.iter().enumerate() {
                    stack.push(SubstTask::#visit_task {
                        src: k as *const _,
                        slot: elements_start + pair_idx * 2,
                        op_idx,
                    });
                    stack.push(SubstTask::#visit_task {
                        src: v as *const _,
                        slot: elements_start + pair_idx * 2 + 1,
                        op_idx,
                    });
                }
            }
        },
        // Pathmap keeps the same 2N result layout. Set mode leaves every value
        // slot empty; map mode visits every value. The assembler infers the one
        // homogeneous mode from those slots (empty remains neutral).
        CollectionType::PathMap => quote! {
            #cat::#label(ref coll) => {
                let elements_start = results.len();
                for _ in 0..coll.len() {
                    results.push(None); // key slot
                    results.push(None); // value slot (None ⇒ Unset)
                }
                let elements_count = results.len() - elements_start;
                stack.push(SubstTask::#assemble_variant {
                    slot,
                    elements_start,
                    elements_count,
                });
                for (pair_idx, entry) in coll.iter().enumerate() {
                    let k = entry.key();
                    stack.push(SubstTask::#visit_task {
                        src: k as *const _,
                        slot: elements_start + pair_idx * 2,
                        op_idx,
                    });
                    if let Some(inner) = entry.value() {
                        stack.push(SubstTask::#visit_task {
                            src: inner as *const _,
                            slot: elements_start + pair_idx * 2 + 1,
                            op_idx,
                        });
                    }
                }
            }
        },
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
///
/// D5 fix (2026-05-13): emits per-source-cat `SubstOp::Env<Y>` arms for each
/// cross-cat cast rule `<Label> . a:Y |- ... : <cat>` in the grammar. When
/// env.<Y>[name] is bound and the term contains `<cat>::<label>(v)` whose
/// pretty_name matches, wrap env.<Y>[name] in the cast variant. This closes
/// `test_nfa_spillover_float_bool_var` and similar tests where the parse
/// alt is `Float::FloatId(Float::FVar(x))` with env.bool["x"] = BoolLit(true) —
/// the new EnvBool arm substitutes `Float::FVar(x)` with `Float::BoolToFloat(
/// Box::new(BoolLit(true)))` so eval can reduce to `FloatLit(1.0)`.
fn generate_var_visit_arm(cat: &Ident, label: &Ident, language: &LanguageDef) -> TokenStream {
    let wrap = format_ident!("Wrap{}", cat);
    let match_variant = format_ident!("Match{}", cat);
    let env_variant = format_ident!("Env{}", cat);

    // D5: scan grammar for cast rules `<Label> . a:Y |- ... : <cat>` where
    // Y != cat. These produce per-source-cat EnvY arms below.
    let cat_name = cat.to_string();
    let mut cross_cat_arms: Vec<TokenStream> = Vec::new();
    let mut seen_sources: std::collections::HashSet<String> = std::collections::HashSet::new();
    for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        let Some(tc) = rule.term_context.as_ref() else {
            continue;
        };
        if tc.len() != 1 {
            continue;
        }
        let mettail_ast::grammar::TermParam::Simple { ty, .. } = &tc[0] else {
            continue;
        };
        // An `Ident` param is identifier TEXT, not a source CATEGORY, so a rule like
        // `Tagged . m:Ident |- "tag" m : Num` is NOT a cross-category cast — there is no
        // `env.ident` map to substitute from, and `SubstOp::EnvIdent` names a variant
        // that is never declared (`env_variants` above is built from `language.types`,
        // and `Ident` is not among them). Without this the arm below emits both
        // `SubstOp::EnvIdent { .. }` and `let _: &Ident;` against types that do not exist.
        if ty.is_ident_text() {
            continue;
        }
        let mettail_ast::types::TypeExpr::Base(source_ident) = ty else {
            continue;
        };
        let source_name = source_ident.to_string();
        if source_name == cat_name {
            continue;
        }
        // Dedup: only the first cast rule per source_cat (source-order).
        if !seen_sources.insert(source_name.clone()) {
            continue;
        }
        let source_env_variant = format_ident!("Env{}", source_ident);
        let cast_label = &rule.label;
        let source_ident_clone = source_ident.clone();
        cross_cat_arms.push(quote! {
            SubstOp::#source_env_variant { env_map } => {
                // D5: cross-cat substitution via grammar-declared cast rule.
                // Replace `<cat>::<label>(v)` with `<cat>::<cast_label>(
                // Box::new(env.<source>[name]))` so eval can reduce.
                let result = 'find: {
                    if let mettail_runtime::Var::Free(ref fv) = v.0 {
                        if let Some(name) = &fv.pretty_name {
                            if let Some(replacement) = env_map.get(name) {
                                break 'find #cat::#cast_label(
                                    std::sync::Arc::new(replacement.clone())
                                );
                            }
                        }
                    }
                    let _: &#source_ident_clone;  // suppress unused-import-style warning
                    #cat::#label(v.clone())
                };
                results[slot] = Some(AnySubstTerm::#wrap(result));
            }
        });
    }

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
                #(#cross_cat_arms)*
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
fn generate_regular_visit_arm(cat: &Ident, label: &Ident, fields: &[FieldInfo]) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);

    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_fields: Vec<TokenStream> = Vec::new();

    for (i, field) in fields.iter().enumerate() {
        let name = &field_names[i];
        let visit_task = format_ident!("Visit{}", field.category);

        if field.is_opaque_leaf() {
            // L9-3: token-text captures are opaque `String` leaves — a token's
            // text is not a term, has no free variables, and never descends.
            // Clone the whole value into the Assemble carrier; no Visit task
            // exists for the `String` placeholder category (mirrors is_predicate).
            let text_name = format_ident!("f{}_text", i);
            alloc_stmts.push(quote! {
                let #text_name = #name.clone();
            });
            assemble_fields.push(quote! { #text_name });
            continue;
        }

        if field.is_predicate {
            // Task #14 (Option<Guard>): predicates are opaque to
            // substitution — clone the whole value (bare BehavioralPred or
            // Option<BehavioralPred>) into the Assemble carrier; no Visit
            // task exists for the Guard pseudo-category. Mirrors the Binder
            // pre-scope arm in `emit_pre_field_visit_alloc`.
            let pred_name = format_ident!("f{}_pred", i);
            alloc_stmts.push(quote! {
                let #pred_name = #name.clone();
            });
            assemble_fields.push(quote! { #pred_name });
            continue;
        }

        if field.is_optional {
            if field.is_collection {
                // Phase 4 #3 (2026-05-12): Optional-Collection — bypass
                // slot machinery. Clone the whole Option<Container> into
                // a carrier and pass it through to assemble. No element
                // substitution; the optional collection slot is treated
                // as a leaf for the purpose of the substitution PDA
                // (free variables inside elements are NOT substituted —
                // pending future support).
                let cloned = format_ident!("f{}_cloned", i);
                alloc_stmts.push(quote! {
                    let #cloned = #name.clone();
                });
                assemble_fields.push(quote! { #cloned });
                continue;
            }
            // Opt-Group: Optional fields use slot+some_flag pattern. Push
            // VisitTask only if Some; assemble reconstructs Option<Box<T>>.
            let slot_name = format_ident!("f{}_slot", i);
            let some_flag = format_ident!("f{}_some", i);
            alloc_stmts.push(quote! {
                let #some_flag: bool = #name.is_some();
                let #slot_name = results.len();
                if #some_flag { results.push(None); }
            });
            push_stmts.push(quote! {
                if let Some(__b) = #name.as_ref() {
                    stack.push(SubstTask::#visit_task {
                        src: __b.as_ref() as *const _,
                        slot: #slot_name,
                        op_idx,
                    });
                }
            });
            assemble_fields.push(quote! { #slot_name, #some_flag });
            continue;
        }

        if field.is_collection {
            let start_name = format_ident!("f{}_start", i);
            let count_name = format_ident!("f{}_count", i);

            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::HashBag => {
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
                },
                // Phase 4 #5b (2026-05-12): HashMap stores 2*N flat
                // slots (K, V, K, V, ...) — same shape as normalize.rs.
                CollectionType::HashMap | CollectionType::PathMap => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None); // k slot
                            results.push(None); // v slot
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (entry_idx, (k, v)) in #name.iter().enumerate() {
                            let k_slot = #start_name + entry_idx * 2;
                            let v_slot = #start_name + entry_idx * 2 + 1;
                            stack.push(SubstTask::#visit_task {
                                src: k as *const _,
                                slot: k_slot,
                                op_idx,
                            });
                            stack.push(SubstTask::#visit_task {
                                src: v as *const _,
                                slot: v_slot,
                                op_idx,
                            });
                        }
                    });
                    assemble_fields.push(quote! { #start_name, #count_name });
                },
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
                },
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
                },
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
        CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
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
        },
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
        },
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
        },
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
/// pre-scope fields.
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

        // Phase 4 #4 (2026-05-12): Optional-Collection — bypass slot/visit-task
        // machinery. Clone the Option<Container> as-is into the assemble carrier;
        // substitution on the whole container doesn't happen here (the inner
        // elements were already-normalized AST values at parse time; if the
        // grammar wants substitution into the optional collection elements,
        // that lands in a future enhancement that visits each element).
        if field.is_optional && field.is_collection {
            let cloned = format_ident!("pf{}_cloned", i);
            alloc_stmts.push(quote! {
                let #cloned = #name.clone();
            });
            assemble_refs.push(quote! { #cloned });
            continue;
        }

        let visit_task = format_ident!("Visit{}", field.category);

        if field.is_collection {
            let start_name = format_ident!("pf{}_start", i);
            let count_name = format_ident!("pf{}_count", i);

            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
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
                },
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
                },
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
                },
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
///
/// GROUP B (2026-06-30): a `Literal` whose category is a *collection* literal
/// gets a recursing Assemble arm that drains its element slots and rebuilds the
/// wrapper via the container's own constructor. Opaque literals return `None`.
fn generate_assemble_arm_for_variant(
    cat: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> Option<TokenStream> {
    match variant {
        // ★ #141 G5 — see the twin above; `Some` so the refusal is not discarded.
        VariantKind::Refused { message, .. } => Some(quote! { compile_error!(#message); }),
        VariantKind::Var { .. } | VariantKind::Nullary { .. } => None,
        // Stage 0 identity: same body for both discriminants.
        VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
            let (coll_type, element_cat) = collection_literal_info(cat, language)?;
            Some(generate_collection_literal_assemble_arm(cat, label, &element_cat, &coll_type))
        },
        VariantKind::Regular { label, fields } => {
            Some(generate_regular_assemble_arm(cat, label, fields))
        },
        VariantKind::Collection { label, element_cat, coll_type } => {
            Some(generate_collection_assemble_arm(cat, label, element_cat, coll_type))
        },
        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            Some(generate_binder_assemble_arm(cat, label, pre_scope_fields, body_cat))
        },
        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            Some(generate_multi_binder_assemble_arm(cat, label, pre_scope_fields, body_cat))
        },
    }
}

/// GROUP B (2026-06-30): the recursing Assemble arm for a collection-literal
/// wrapper. Drains the element result slots (already-substituted `Proc`s) and
/// rebuilds the wrapper with the container's OWN constructor, then wraps as
/// `AnySubstTerm::Wrap{Cat}(#cat::#label(rebuilt))`.
///
/// Body wrapped in the established `#[inline(never)]` inner-fn peel idiom
/// (shared with `generate_collection_assemble_arm`) so per-arm builder locals
/// live in this helper's frame rather than bloating `subst_iterative`.
///
/// Runtime constructors (all VERIFIED to exist — see runtime/src/*):
/// - Vec      → `Vec::with_capacity` + `push`                        → `List::ListLit`
/// - HashBag  → `HashBag::new()` + `insert_n(v, count)`              → `Bag::BagLit`
/// - HashSet  → `HashSetLit::new()` + `insert(v)`                    → `Set::SetLit`
/// - HashMap  → `HashMapLit::default()` + `insert(k, v)`             → `Map::MapLit`
/// - PathMap  → build `HashMapLit` then `PathMapLit(map)`            → `Pathmap::PathmapLit`
fn generate_collection_literal_assemble_arm(
    cat: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}Lit", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let elem_wrap = format_ident!("Wrap{}", element_cat);

    match coll_type {
        CollectionType::Vec => quote! {
            SubstTask::#assemble_variant { slot, elements_start, elements_count } => {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn assemble(
                    results: &mut Vec<Option<AnySubstTerm>>,
                    slot: usize,
                    elements_start: usize,
                    elements_count: usize,
                ) {
                    let mut out = Vec::with_capacity(elements_count);
                    for idx in 0..elements_count {
                        match results[elements_start + idx].take()
                            .expect("iterative subst: missing list-literal element")
                        {
                            AnySubstTerm::#elem_wrap(v) => out.push(v),
                            _ => unreachable!("iterative subst: wrong category in list-literal slot"),
                        }
                    }
                    results[slot] = Some(AnySubstTerm::#wrap(#cat::#label(out)));
                }
                assemble(results, slot, elements_start, elements_count);
            }
        },
        CollectionType::HashSet => quote! {
            SubstTask::#assemble_variant { slot, elements_start, elements_count } => {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn assemble(
                    results: &mut Vec<Option<AnySubstTerm>>,
                    slot: usize,
                    elements_start: usize,
                    elements_count: usize,
                ) {
                    let mut out = mettail_runtime::HashSetLit::new();
                    for idx in 0..elements_count {
                        match results[elements_start + idx].take()
                            .expect("iterative subst: missing set-literal element")
                        {
                            AnySubstTerm::#elem_wrap(v) => { out.insert(v); },
                            _ => unreachable!("iterative subst: wrong category in set-literal slot"),
                        }
                    }
                    results[slot] = Some(AnySubstTerm::#wrap(#cat::#label(out)));
                }
                assemble(results, slot, elements_start, elements_count);
            }
        },
        CollectionType::HashBag => quote! {
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
                    let mut out = mettail_runtime::HashBag::new();
                    for (idx, count) in counts_vec.iter().enumerate() {
                        match results[elements_start + idx].take()
                            .expect("iterative subst: missing bag-literal element")
                        {
                            AnySubstTerm::#elem_wrap(v) => out.insert_n(v, *count),
                            _ => unreachable!("iterative subst: wrong category in bag-literal slot"),
                        }
                    }
                    results[slot] = Some(AnySubstTerm::#wrap(#cat::#label(out)));
                }
                assemble(results, slot, elements_start, elements_count, counts_vec);
            }
        },
        CollectionType::HashMap => quote! {
            SubstTask::#assemble_variant { slot, elements_start, elements_count } => {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn assemble(
                    results: &mut Vec<Option<AnySubstTerm>>,
                    slot: usize,
                    elements_start: usize,
                    elements_count: usize,
                ) {
                    let mut out = mettail_runtime::HashMapLit::default();
                    let mut idx = 0;
                    while idx < elements_count {
                        let k = match results[elements_start + idx].take()
                            .expect("iterative subst: missing map-literal key")
                        {
                            AnySubstTerm::#elem_wrap(v) => v,
                            _ => unreachable!("iterative subst: wrong category in map-literal key slot"),
                        };
                        let v = match results[elements_start + idx + 1].take()
                            .expect("iterative subst: missing map-literal value")
                        {
                            AnySubstTerm::#elem_wrap(v) => v,
                            _ => unreachable!("iterative subst: wrong category in map-literal value slot"),
                        };
                        out.insert(k, v);
                        idx += 2;
                    }
                    results[slot] = Some(AnySubstTerm::#wrap(#cat::#label(out)));
                }
                assemble(results, slot, elements_start, elements_count);
            }
        },
        CollectionType::PathMap => quote! {
            SubstTask::#assemble_variant { slot, elements_start, elements_count } => {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn assemble(
                    results: &mut Vec<Option<AnySubstTerm>>,
                    slot: usize,
                    elements_start: usize,
                    elements_count: usize,
                ) {
                    let mut inner = mettail_runtime::PathMapLit::new();
                    let mut idx = 0;
                    while idx < elements_count {
                        let k = match results[elements_start + idx].take()
                            .expect("iterative subst: missing pathmap-literal key")
                        {
                            AnySubstTerm::#elem_wrap(v) => v,
                            _ => unreachable!("iterative subst: wrong category in pathmap-literal key slot"),
                        };
                        let value = match results[elements_start + idx + 1].take() {
                            None => None,
                            Some(AnySubstTerm::#elem_wrap(v)) => Some(v),
                            Some(_) => unreachable!(
                                "iterative subst: wrong category in pathmap-literal value slot"
                            ),
                        };
                        let inserted = match value {
                            None => inner.insert_set(k).map(|_| ()),
                            Some(value) => inner.insert_map(k, value).map(|_| ()),
                        };
                        inserted.expect("iterative subst preserves homogeneous pathmap mode");
                        idx += 2;
                    }
                    results[slot] = Some(AnySubstTerm::#wrap(
                        #cat::#label(inner)
                    ));
                }
                assemble(results, slot, elements_start, elements_count);
            }
        },
    }
}

/// Regular variant Assemble: extract each field from its slot (or slot
/// range for collections), reconstruct the boxed-field constructor.
///
/// **Frame-size fix (PDA stack-safety, second tier):** wraps the body in a
/// local `#[inline(never)]` inner fn so per-variant locals (`field_N`,
/// `Box::new(...)`, collection builders) live in the helper's frame instead
/// of `subst_iterative`'s. (The same `#[inline(never)]` peel idiom is shared
/// with the sibling iterative term-ops.)
fn generate_regular_assemble_arm(cat: &Ident, label: &Ident, fields: &[FieldInfo]) -> TokenStream {
    let assemble_variant = format_ident!("Assemble{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);

    // Build flat (pat-name, helper-arg-decl, helper-arg-name) lists.
    let mut pat_flat: Vec<TokenStream> = Vec::new();
    let mut decl_flat: Vec<TokenStream> = Vec::new();
    let mut call_flat: Vec<TokenStream> = Vec::new();
    for (i, field) in fields.iter().enumerate() {
        if field.is_opaque_leaf() {
            // L9-3/L9-4: opaque-leaf carrier `f{i}_text` (declared with the
            // leaf's own type in `generate_subst_task_variant`); pass-through.
            let text_name = format_ident!("f{}_text", i);
            let text_ty = field.opaque_leaf_type();
            pat_flat.push(quote! { #text_name });
            decl_flat.push(quote! { #text_name: #text_ty });
            call_flat.push(quote! { #text_name });
            continue;
        }
        if field.is_predicate {
            // Task #14 (Option<Guard>): predicate-FIRST — pat/decl/call ride
            // the Assemble variant's `f{i}_pred` field (declared Option-aware
            // in `generate_subst_task_variant`); extract is a no-op and the
            // construct closure passes the value through unchanged.
            let pred_name = format_ident!("f{}_pred", i);
            let pred_ty = if field.is_optional {
                quote! { Option<mettail_runtime::BehavioralPred> }
            } else {
                quote! { mettail_runtime::BehavioralPred }
            };
            pat_flat.push(quote! { #pred_name });
            decl_flat.push(quote! { #pred_name: #pred_ty });
            call_flat.push(quote! { #pred_name });
            continue;
        }
        if field.is_optional {
            if field.is_collection {
                // Phase 4 #3 (2026-05-12): Optional-Collection — cloned carrier.
                let cloned = format_ident!("f{}_cloned", i);
                let ty = optional_collection_field_type_subst(field);
                pat_flat.push(quote! { #cloned });
                decl_flat.push(quote! { #cloned: #ty });
                call_flat.push(quote! { #cloned });
                continue;
            }
            let slot_name = format_ident!("f{}_slot", i);
            let some_flag = format_ident!("f{}_some", i);
            pat_flat.push(quote! { #slot_name });
            pat_flat.push(quote! { #some_flag });
            decl_flat.push(quote! { #slot_name: usize });
            decl_flat.push(quote! { #some_flag: bool });
            call_flat.push(quote! { #slot_name });
            call_flat.push(quote! { #some_flag });
            continue;
        }
        if field.is_collection {
            let start_name = format_ident!("f{}_start", i);
            let count_name = format_ident!("f{}_count", i);
            pat_flat.push(quote! { #start_name });
            decl_flat.push(quote! { #start_name: usize });
            call_flat.push(quote! { #start_name });
            pat_flat.push(quote! { #count_name });
            decl_flat.push(quote! { #count_name: usize });
            call_flat.push(quote! { #count_name });
            // Phase 4 #5b (2026-05-12): only HashBag carries the counts
            // Vec; HashMap stores entries as flat 2*N slots (no counts).
            if matches!(
                field.coll_type.as_ref().unwrap_or(&CollectionType::Vec),
                CollectionType::HashBag
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
            if field.is_opaque_leaf() {
                // L9-3: token-text carrier is in scope by frame name; pass the
                // bare `String` through unwrapped (never Arc-wrapped).
                let text_name = format_ident!("f{}_text", i);
                return quote! { #text_name };
            }
            if field.is_predicate {
                // Task #14 (Option<Guard>): the pred is in scope by its
                // frame name (extract is a no-op); pass through unwrapped.
                let pred_name = format_ident!("f{}_pred", i);
                return quote! { #pred_name };
            }
            let result_ident = format_ident!("field_{}", i);
            if field.is_optional {
                // Already Option<Arc<T>> or Option<Container> from extract; pass through.
                quote! { #result_ident }
            } else if field.is_collection {
                quote! { #result_ident }
            } else {
                quote! { std::sync::Arc::new(#result_ident) }
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

/// Phase 4 #3 (2026-05-12): Derive the runtime carrier type for an
/// Optional-Collection field. Mirrors `enums.rs::one_optional_field`.
fn optional_collection_field_type_subst(field: &FieldInfo) -> TokenStream {
    let cat = &field.category;
    match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
        CollectionType::Vec => quote! { Option<Vec<#cat>> },
        CollectionType::HashBag => quote! { Option<mettail_runtime::HashBag<#cat>> },
        CollectionType::HashSet => quote! { Option<std::collections::HashSet<#cat>> },
        CollectionType::HashMap | CollectionType::PathMap => {
            quote! { Option<mettail_runtime::HashMapLit<#cat, #cat>> }
        },
    }
}

/// Extract the result for a single field from a slot (or slot range).
/// Predicate fields are already in scope as `f{i}_pred` — no extract needed
/// (mirrors `emit_pre_field_extracts`' predicate arm).
fn emit_field_extract(i: usize, field: &FieldInfo) -> TokenStream {
    if field.is_predicate || field.is_opaque_leaf() {
        // L9-3: token-text carrier `f{i}_text` is already in scope (no slot,
        // no Wrap) — nothing to extract (mirrors the predicate no-op).
        return quote! {};
    }
    let result_ident = format_ident!("field_{}", i);
    let wrap = format_ident!("Wrap{}", field.category);

    if field.is_optional {
        if field.is_collection {
            // Phase 4 #3 (2026-05-12): Optional-Collection — the cloned
            // carrier is already in scope by name; rebind to field_<i>.
            let cloned = format_ident!("f{}_cloned", i);
            return quote! {
                let #result_ident = #cloned;
            };
        }
        // Opt-Group: extract `Option<Box<Cat>>` from slot+some_flag.
        let slot_name = format_ident!("f{}_slot", i);
        let some_flag = format_ident!("f{}_some", i);
        return quote! {
            let #result_ident: Option<std::sync::Arc<_>> = if #some_flag {
                match results[#slot_name].take()
                    .expect("iterative subst: missing optional inner")
                {
                    AnySubstTerm::#wrap(v) => Some(std::sync::Arc::new(v)),
                    _ => unreachable!("iterative subst: wrong category in optional slot"),
                }
            } else {
                None
            };
        };
    }

    if field.is_collection {
        let start_name = format_ident!("f{}_start", i);
        let count_name = format_ident!("f{}_count", i);

        match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
            CollectionType::HashBag => {
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
            },
            // Phase 4 #5b (2026-05-12): HashMap — 2*N flat slots.
            CollectionType::HashMap | CollectionType::PathMap => {
                quote! {
                    let mut #result_ident =
                        mettail_runtime::HashMapLit::default();
                    for entry_idx in 0..#count_name {
                        let k_slot = #start_name + entry_idx * 2;
                        let v_slot = #start_name + entry_idx * 2 + 1;
                        let k = match results[k_slot].take()
                            .expect("iterative subst: missing hashmap key")
                        {
                            AnySubstTerm::#wrap(v) => v,
                            _ => unreachable!(
                                "iterative subst: wrong category in hashmap k slot"
                            ),
                        };
                        let v = match results[v_slot].take()
                            .expect("iterative subst: missing hashmap value")
                        {
                            AnySubstTerm::#wrap(v) => v,
                            _ => unreachable!(
                                "iterative subst: wrong category in hashmap v slot"
                            ),
                        };
                        #result_ident.insert(k, v);
                    }
                }
            },
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
            },
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
            },
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
/// (Per-arm `#[inline(never)]` peel rationale — shared with the sibling
/// iterative term-ops.)
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
        CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
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
        },
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
        },
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
        },
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
    // Residual #11-2 (2026-07-14): typed helper-param decls for the peel. subst's
    // `emit_pre_field_decl_list` is symmetric with `emit_pre_field_assemble_slot_pattern`
    // for every shape (HashBag|HashMap both -> 3 fields), and no HashBag/HashMap
    // pre-scope field exists in-tree anyway.
    let pre_decls = emit_pre_field_decl_list(pre_scope_fields);
    let pre_extracts = emit_pre_field_extracts(pre_scope_fields);
    let pre_construct = emit_pre_field_constructs(pre_scope_fields);

    // PRE-PEEL body (residual #11-2, 2026-07-14): commented-out-never-deleted;
    // replaced by the `#[inline(never)]` per-arm peel below (pure code motion).
    // `subst_iterative` nests under `normalize_iterative` at β time, so bounding
    // its ~800 Bind/MBind arms is required for the pin-retirement headroom.
    /*
    quote! {
        SubstTask::#assemble_variant { slot, #(#slot_pattern,)* cloned_pattern, body_slot } => {
            #(#pre_extracts)*
            let body = match results[body_slot].take()
                .expect("iterative subst: missing binder body")
            {
                AnySubstTerm::#body_wrap(v) => v,
                _ => unreachable!("iterative subst: wrong category in binder body slot"),
            };
            let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, std::sync::Arc::new(body));
            results[slot] = Some(AnySubstTerm::#wrap(
                #cat::#label(#(#pre_construct)* new_scope)
            ));
        }
    }
    */
    quote! {
        SubstTask::#assemble_variant { slot, #(#slot_pattern,)* cloned_pattern, body_slot } => {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn assemble_binder(
                results: &mut Vec<Option<AnySubstTerm>>,
                slot: usize,
                #(#pre_decls,)*
                cloned_pattern: mettail_runtime::Binder<String>,
                body_slot: usize,
            ) {
                #(#pre_extracts)*
                let body = match results[body_slot].take()
                    .expect("iterative subst: missing binder body")
                {
                    AnySubstTerm::#body_wrap(v) => v,
                    _ => unreachable!("iterative subst: wrong category in binder body slot"),
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, std::sync::Arc::new(body));
                results[slot] = Some(AnySubstTerm::#wrap(
                    #cat::#label(#(#pre_construct)* new_scope)
                ));
            }
            assemble_binder(results, slot, #(#slot_pattern,)* cloned_pattern, body_slot);
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
    // Residual #11-2 (2026-07-14): typed helper-param decls for the peel (see
    // `generate_binder_assemble_arm` for the arity-agreement argument).
    let pre_decls = emit_pre_field_decl_list(pre_scope_fields);
    let pre_extracts = emit_pre_field_extracts(pre_scope_fields);
    let pre_construct = emit_pre_field_constructs(pre_scope_fields);

    // PRE-PEEL body (residual #11-2, 2026-07-14): commented-out-never-deleted;
    // replaced by the `#[inline(never)]` per-arm peel below (pure code motion).
    /*
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
            let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, std::sync::Arc::new(body));
            results[slot] = Some(AnySubstTerm::#wrap(
                #cat::#label(#(#pre_construct)* new_scope)
            ));
        }
    }
    */
    quote! {
        SubstTask::#assemble_variant { slot, #(#slot_pattern,)* cloned_pattern, body_slot } => {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn assemble_multi_binder(
                results: &mut Vec<Option<AnySubstTerm>>,
                slot: usize,
                #(#pre_decls,)*
                cloned_pattern: Vec<mettail_runtime::Binder<String>>,
                body_slot: usize,
            ) {
                #(#pre_extracts)*
                let body = match results[body_slot].take()
                    .expect("iterative subst: missing multi-binder body")
                {
                    AnySubstTerm::#body_wrap(v) => v,
                    _ => unreachable!(
                        "iterative subst: wrong category in multi-binder body slot"
                    ),
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, std::sync::Arc::new(body));
                results[slot] = Some(AnySubstTerm::#wrap(
                    #cat::#label(#(#pre_construct)* new_scope)
                ));
            }
            assemble_multi_binder(results, slot, #(#slot_pattern,)* cloned_pattern, body_slot);
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
            // Phase 4 #4 (2026-05-12): Optional-Collection — cloned carrier name.
            if field.is_optional && field.is_collection {
                let cloned = format_ident!("pf{}_cloned", i);
                return quote! { #cloned };
            }
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! { #start_name, #count_name, #counts_name }
                    },
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
            // Phase 4 #4 (2026-05-12): Optional-Collection — rebind the cloned
            // carrier to pre_field_<i> for the construct step.
            if field.is_optional && field.is_collection {
                let cloned = format_ident!("pf{}_cloned", i);
                let result_ident = format_ident!("pre_field_{}", i);
                return quote! {
                    let #result_ident = #cloned;
                };
            }
            let wrap = format_ident!("Wrap{}", field.category);
            let result_ident = format_ident!("pre_field_{}", i);

            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
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
            // Phase 4 #4 (2026-05-12): Optional-Collection — already
            // Option<Container>, pass through without Box wrapping.
            if field.is_optional && field.is_collection {
                return quote! { #result_ident, };
            }
            if field.is_collection {
                quote! { #result_ident, }
            } else {
                quote! { std::sync::Arc::new(#result_ident), }
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
                #[allow(unreachable_patterns)]
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
            #[allow(unreachable_patterns)]
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
// Variant Collection (UNCHANGED — shared with the sibling iterative term-ops)
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

    // Auto-generated Literal variant (for native types).
    //
    // COLLECTION LITERALS (record corrected 2026-07-25; supersedes the
    // 2026-06-30 "GROUP B deferred" note that stood here).
    //
    // Collection-literal categories (List/Bag/Set/Map/Pathmap) are declared as
    // native-type aliases (`![Vec<Proc>] as List`) with NO grammar rule, so they
    // reach this fallback. They are NOT opaque leaves: their payload contains
    // element terms. Classifying them `Literal` makes every term op clone the
    // wrapper whole and never recurse — e.g. `subst([a,b,c], a:=1,b:=2,c:=3)`
    // returns `[a,b,c]` unchanged.
    //
    // History, so the reverted attempt is not re-attempted:
    //
    //  * ATTEMPT #1 (2026-06-30) reclassified these categories to
    //    `VariantKind::Collection` and REVERTED. Two independent causes:
    //    (i) `Collection`'s arms were authored for category-DIRECT collection
    //    FIELDS (`PPar . ps:HashBag(Proc)`), whose payload is the bare iterable
    //    container — against the literal wrappers they produced 15 compile
    //    errors (`HashSetLit` is not `HashSet`; no `insert_into_baglit`);
    //    (ii) for `List` (`Vec`) it compiled but was NET-NEGATIVE, because
    //    flipping an EXISTING discriminant silently re-routed ~13 consumers at
    //    once, changing depth/ground/normalize/semantic-hash semantics and
    //    regressing zipper/map tests without fixing the polyadic target.
    //
    //  * SOLVED FOR `subst` (2026-06-30, in tree and green): rather than flip
    //    the shared discriminant, `subst` detects these categories LOCALLY via
    //    [`collection_literal_info`] and emits recursing Visit/Assemble arms
    //    ([`generate_collection_literal_visit_arm`],
    //    [`generate_collection_literal_assemble_arm`]) with the correct
    //    per-wrapper constructors. The hard part — the assemble side that
    //    defeated attempt #1 — is therefore already solved and validated.
    //
    //  * THE ROOT FIX (this change): promote that local classification to a
    //    first-class discriminant, [`VariantKind::CollectionLiteral`]. It has NO
    //    pre-existing arm anywhere, so it cannot silently re-route anybody the
    //    way attempt #1 did; instead the exhaustiveness checker forces every
    //    consumer to declare its intent. Consumers that must keep leaf
    //    behaviour stay on the `Literal` arm PERMANENTLY and deliberately —
    //    that set is exactly the one whose implicit flip caused attempt #1's
    //    regressions.
    //
    // See [[empty-receiver-polyadic-cluster-roots]].
    if let Some(lang_type) = language.get_type(category) {
        if let Some(native_type) = &lang_type.native_type {
            let has_lit = variants.iter().any(|v| {
                matches!(v, VariantKind::Literal { .. } | VariantKind::CollectionLiteral { .. })
            });
            if !has_lit {
                let label = generate_literal_label(native_type);
                match collection_literal_info(category, language) {
                    Some((coll_type, element_cat)) if COLLECTION_LITERAL_KIND_GATE => {
                        variants.push(VariantKind::CollectionLiteral {
                            label,
                            element_cat,
                            coll_type,
                        });
                    },
                    _ => variants.push(VariantKind::Literal { label }),
                }
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
                    is_optional: false,
                    opaque_leaf: None,
                },
                FieldInfo {
                    category: domain_name.clone(),
                    is_collection: false,
                    coll_type: None,
                    is_predicate: false,
                    is_optional: false,
                    opaque_leaf: None,
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
                    is_optional: false,
                    opaque_leaf: None,
                },
                FieldInfo {
                    category: domain_name.clone(),
                    is_collection: true,
                    coll_type: Some(CollectionType::Vec),
                    is_predicate: false,
                    is_optional: false,
                    opaque_leaf: None,
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

    // L9-3/L9-4: a capture-bearing rule (`b@Tok` / `*flt(node, open, close)`)
    // must go through the capture-aware builder so its opaque-leaf field
    // (token-text `String` / `Arc<FltNode>`) is stamped `opaque_leaf` — checked
    // FIRST, so it fires whether the term context is empty (`Some([])`), absent
    // (`None`), or non-empty. `capture_layout` reads only the syntax pattern.
    // Without this a bare `Label . |- *flt(…) : Cat` (empty/absent context)
    // falls to `variant_kind_from_items`, which yields a plain NonTerminal
    // `FieldInfo { category: FltNode, opaque_leaf: None }`; every term-op emitter
    // that recurses by category — notably the Dovetail e-graph add/build, which
    // synthesizes `__mettail_dovetail_{add,build}_flt_node…` for a real category
    // — then fails to resolve, since an opaque leaf has no such recursion fns.
    if let Some(sp) = rule.syntax_pattern.as_deref() {
        if sp.iter().any(|e| {
            matches!(
                e,
                mettail_ast::grammar::SyntaxExpr::TokenKind { .. }
                    | mettail_ast::grammar::SyntaxExpr::GuestBody { .. }
            )
        }) {
            let ctx = rule.term_context.as_deref().unwrap_or(&[]);
            return variant_kind_from_term_context(&label, ctx, Some(sp));
        }
    }

    if let Some(ctx) = &rule.term_context {
        return variant_kind_from_term_context(&label, ctx, rule.syntax_pattern.as_deref());
    }

    variant_kind_from_items(&label, &rule.items, &rule.bindings)
}

/// Create VariantKind from new-style term_context.
///
/// `syntax_pattern` is threaded so that a rule containing one or more `v@Tok`
/// captures (L9-3) builds its `FieldInfo` list from the SAME
/// `capture_layout` sp-walk that `gen/types/enums.rs` uses for the variant
/// definition — keeping the term-op patterns positionally aligned with the
/// generated enum. Capture-free rules skip that branch and keep the
/// byte-identical term_context walk below.
pub(crate) fn variant_kind_from_term_context(
    label: &Ident,
    ctx: &[TermParam],
    syntax_pattern: Option<&[SyntaxExpr]>,
) -> VariantKind {
    if let Some(sp) = syntax_pattern {
        if let Some(layout) = crate::gen::capture::capture_layout(ctx, sp) {
            let pre_scope_fields: Vec<FieldInfo> = layout
                .non_scope
                .iter()
                .map(|f| {
                    let mut info = match &f.kind {
                        crate::gen::capture::CaptureFieldKind::TokenText => {
                            field_info_for_token_capture()
                        },
                        crate::gen::capture::CaptureFieldKind::GuestBody { .. } => {
                            field_info_for_guest_body()
                        },
                        crate::gen::capture::CaptureFieldKind::Term(ty) => {
                            field_info_from_type_expr(ty)
                        },
                        crate::gen::capture::CaptureFieldKind::Predicate => {
                            field_info_for_guard_slot()
                        },
                    };
                    info.is_optional = f.optional;
                    info
                })
                .collect();

            if let Some(scope) = &layout.scope {
                if let TypeExpr::Arrow { domain, codomain } = scope.ty {
                    let body_cat = extract_base_category(codomain);
                    if scope.multi {
                        return VariantKind::MultiBinder {
                            label: label.clone(),
                            pre_scope_fields,
                            binder_cat: extract_multi_binder_category(domain),
                            body_cat,
                        };
                    }
                    return VariantKind::Binder {
                        label: label.clone(),
                        pre_scope_fields,
                        binder_cat: extract_base_category(domain),
                        body_cat,
                    };
                }
            }

            // No binder: a capture rule is a Regular variant of leaf/term
            // fields (never a single-collection Collection variant — a capture
            // trigger excludes the Class-5 collection shape).
            return if pre_scope_fields.is_empty() {
                VariantKind::Nullary { label: label.clone() }
            } else {
                VariantKind::Regular {
                    label: label.clone(),
                    fields: pre_scope_fields,
                }
            };
        }
    }

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

        // Opt-Group: pre-scope fields recursively flatten Optional groups,
        // tagging each inner field with `is_optional: true`.
        let pre_scope_fields: Vec<FieldInfo> = ctx
            .iter()
            .flat_map(|p| field_infos_from_term_param(p, false))
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
            .flat_map(|p| field_infos_from_term_param(p, false))
            .collect();

        return VariantKind::Binder {
            label: label.clone(),
            pre_scope_fields,
            binder_cat,
            body_cat,
        };
    }

    // Opt-Group: regular variant fields recursively flatten Optional groups.
    // Each inner Simple/GuardBody contributes one FieldInfo with
    // `is_optional: true` tagged. Inner Abstractions in Optional context
    // (rare) emit `Option<Scope<...>>` typed fields.
    let fields: Vec<FieldInfo> = ctx
        .iter()
        .flat_map(|p| field_infos_from_term_param(p, false))
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

        // ★ #141 G5 — see `VariantKind::Refused`.
        let GrammarItem::Binder { category: binder_cat } = &items[*binder_idx] else {
            return VariantKind::Refused {
                label: label.clone(),
                message: format!(
                    "mettail internal error: rule `{label}` declares a binding whose binder \
                     index does not point at a binder item. The parser builds this \
                     structure, so it and this classifier have drifted apart. This is a \
                     macro bug, not a grammar bug — please report it."
                ),
            };
        };
        let binder_cat = binder_cat.clone();

        let GrammarItem::NonTerminal { ident: body_cat, .. } = &items[body_idx] else {
            return VariantKind::Refused {
                label: label.clone(),
                message: format!(
                    "mettail internal error: rule `{label}` declares a binding whose body \
                     index does not point at a non-terminal item. The parser builds this \
                     structure, so it and this classifier have drifted apart. This is a \
                     macro bug, not a grammar bug — please report it."
                ),
            };
        };
        let body_cat = body_cat.clone();

        let pre_scope_fields: Vec<FieldInfo> = items
            .iter()
            .take(*binder_idx)
            .filter_map(|item| match item {
                GrammarItem::NonTerminal { ident: cat, kind } if *kind != NonTerminalKind::Var => {
                    Some(FieldInfo {
                        category: cat.clone(),
                        is_collection: false,
                        coll_type: None,
                        is_predicate: false,
                        is_optional: false,
                        opaque_leaf: None,
                    })
                },
                GrammarItem::Collection { element_type, coll_type, .. } => Some(FieldInfo {
                    category: element_type.clone(),
                    is_collection: true,
                    coll_type: Some(coll_type.clone()),
                    is_predicate: false,
                    is_optional: false,
                    opaque_leaf: None,
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
            GrammarItem::NonTerminal { ident: cat, kind } if *kind != NonTerminalKind::Var => {
                Some(FieldInfo {
                    category: cat.clone(),
                    is_collection: false,
                    coll_type: None,
                    is_predicate: false,
                    is_optional: false,
                    opaque_leaf: None,
                })
            },
            GrammarItem::Collection { element_type, coll_type, .. } => Some(FieldInfo {
                category: element_type.clone(),
                is_collection: true,
                coll_type: Some(coll_type.clone()),
                is_predicate: false,
                is_optional: false,
                opaque_leaf: None,
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
    terminal_base(ty).clone()
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
        // An `m:Ident` param is an OPAQUE STRING LEAF, not a category to descend into.
        // Routed here — before the generic `Base` arm — because `Ident` is a builtin token
        // class with no enum to visit: left as `category: Ident, opaque_leaf: None` the
        // iterative walkers emit `NormTask::VisitIdent` / `AnySubstTerm::WrapIdent` /
        // `CmpTask::CmpIdent` / `DisplayTask::DisplayIdent` / `DropTask::DropIdent` /
        // `SemanticHashTask::SemHashIdent` and call `is_ground()`/`term_depth()` on a
        // `String` — MEASURED as 35 compile errors across eight walkers on the first build
        // of a language using the param.
        //
        // It reuses `OpaqueLeafKind::TokenText` rather than adding a kind: that kind means
        // "an opaque `String` leaf", which is exactly what this is. The two differ only in
        // PROVENANCE (a declared `tokens { }` kind via `as_token_text()` vs the builtin
        // `Ident` via `as_ident()`), and provenance is settled in the walker/action layer
        // (`BinderPosition::IdentTextCapture`), not here. Sharing the kind is what makes
        // every term op — Eq/Hash/Ord/subst/normalize/display/semantic_hash — treat a
        // method name inertly with no new match arm anywhere.
        TypeExpr::Base(ident)
            if mettail_ast::grammar::NonTerminalKind::classify(&ident.to_string())
                == mettail_ast::grammar::NonTerminalKind::Ident =>
        {
            field_info_for_token_capture()
        },
        TypeExpr::Base(ident) => FieldInfo {
            category: ident.clone(),
            is_collection: false,
            coll_type: None,
            is_predicate: false,
            is_optional: false,
            opaque_leaf: None,
        },
        TypeExpr::Collection { coll_type, element } => FieldInfo {
            category: extract_base_category(element),
            is_collection: true,
            coll_type: Some(coll_type.clone()),
            is_predicate: false,
            is_optional: false,
            opaque_leaf: None,
        },
        // Phase 4 #5b (2026-05-12): HashMap(K, V) Map type. Lower to a
        // collection field with `coll_type: HashMap` mirroring the K==V
        // invariant enforced by `classify_binder`. The value type is
        // chosen as the element category (consistent with the
        // CollectionDrain materialization that produces
        // `HashMapLit<elem, elem>`).
        TypeExpr::Map { value, .. } => FieldInfo {
            category: extract_base_category(value),
            is_collection: true,
            coll_type: Some(CollectionType::HashMap),
            is_predicate: false,
            is_optional: false,
            opaque_leaf: None,
        },
        _ => FieldInfo {
            category: format_ident!("Unknown"),
            is_collection: false,
            coll_type: None,
            is_predicate: false,
            is_optional: false,
            opaque_leaf: None,
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
        is_optional: false,
        opaque_leaf: None,
    }
}

/// L9-3: create a synthetic FieldInfo for a `v@Tok` token-kind capture — a
/// bare `std::string::String` opaque leaf carrying the matched token text. The
/// `category` is the placeholder ident `String` (never dereferenced: every
/// consumer branches on `is_opaque_leaf()` first). Mirrors
/// `field_info_for_guard_slot` for the predicate leaf.
pub(crate) fn field_info_for_token_capture() -> FieldInfo {
    FieldInfo {
        category: format_ident!("String"),
        is_collection: false,
        coll_type: None,
        is_predicate: false,
        is_optional: false,
        opaque_leaf: Some(OpaqueLeafKind::TokenText),
    }
}

/// L9-4: create a synthetic FieldInfo for a `*flt(node, …)` guest-body capture —
/// an `Arc<FltNode>` opaque leaf. Same shared leaf handling as the token-text
/// capture (inline hash/cmp, clone-through subst/normalize, no descent); only
/// the emitted field type differs (`OpaqueLeafKind::field_type`). The
/// `category` is the placeholder ident `FltNode` (never dereferenced).
pub(crate) fn field_info_for_guest_body() -> FieldInfo {
    FieldInfo {
        category: format_ident!("FltNode"),
        is_collection: false,
        coll_type: None,
        is_predicate: false,
        is_optional: false,
        opaque_leaf: Some(OpaqueLeafKind::GuestBody),
    }
}

/// Opt-Group: create FieldInfo from a TermParam through the shared stack-safe
/// leaf iterator, flattening
/// `TermParam::Optional` so each inner Simple/Abstraction/MultiAbstraction/
/// GuardBody contributes one FieldInfo with `is_optional: true`. Returns
/// a Vec because Optional groups may contain multiple inner params, each
/// becoming its own variant field.
pub(crate) fn field_infos_from_term_param(param: &TermParam, in_optional: bool) -> Vec<FieldInfo> {
    let mut out = Vec::new();
    for leaf in TermParamLeaves::new(std::slice::from_ref(param), in_optional) {
        match leaf.kind {
            TermParamLeafKind::Simple { ty, .. } => {
                let mut info = field_info_from_type_expr(ty);
                info.is_optional = leaf.is_optional;
                out.push(info);
            },
            TermParamLeafKind::GuardBody { .. } => {
                let mut info = field_info_for_guard_slot();
                info.is_optional = leaf.is_optional;
                out.push(info);
            },
            TermParamLeafKind::Abstraction { ty, .. }
            | TermParamLeafKind::MultiAbstraction { ty, .. }
                if leaf.is_optional =>
            {
                let body_cat = if let TypeExpr::Arrow { codomain, .. } = ty {
                    extract_base_category(codomain)
                } else {
                    format_ident!("Unknown")
                };
                out.push(FieldInfo {
                    category: body_cat,
                    is_collection: false,
                    coll_type: None,
                    is_predicate: false,
                    is_optional: true,
                    opaque_leaf: None,
                });
            },
            TermParamLeafKind::Abstraction { .. } | TermParamLeafKind::MultiAbstraction { .. } => {
            },
        }
    }
    out
}

// ═══════════════════════════════════════════════════════════════════════════
// #141 G5 RED — a rule whose binding metadata contradicts its items REFUSES
// ═══════════════════════════════════════════════════════════════════════════
//
// ⚠ No cell expects a panic: each reads the classification the function returns.
#[cfg(test)]
mod shape_refusal_red {
    use super::*;
    use mettail_ast::grammar::{rule_fixture, GrammarItem, NonTerminalKind};
    use proc_macro2::Span;
    use syn::Ident;

    fn id(name: &str) -> Ident {
        Ident::new(name, Span::call_site())
    }

    /// A binder rule as ITEMS — a binder at index 0, a body non-terminal at 1,
    /// and `bindings` saying exactly that. `binder_item` is the ONLY thing the
    /// mutated and control fixtures differ in.
    fn binder_rule(binder_item: GrammarItem) -> GrammarRule {
        GrammarRule {
            items: vec![
                binder_item,
                GrammarItem::NonTerminal {
                    ident: id("Term"),
                    kind: NonTerminalKind::Category,
                },
            ],
            bindings: vec![(0usize, vec![1usize])],
            ..rule_fixture(id("Lam"), id("Term"))
        }
    }

    /// ★ THE MUTATION CELL. A `bindings` entry whose binder index points at a
    /// TERMINAL classifies as `Refused`, carrying a message that names the rule.
    #[test]
    fn a_binding_that_does_not_point_at_a_binder_refuses() {
        let mutated = binder_rule(GrammarItem::Terminal("lambda".to_string()));
        let control = binder_rule(GrammarItem::Binder { category: id("Term") });

        // The mutation is applied, and is the only difference.
        assert_eq!(mutated.bindings, control.bindings, "same binding metadata");
        assert_eq!(mutated.items.len(), control.items.len(), "same item count");
        assert!(
            matches!(mutated.items[0], GrammarItem::Terminal(_)),
            "the mutated fixture's item 0 is a TERMINAL, which is what makes the \
             binding metadata a lie",
        );

        let language = crate::gen::empty_language_for_tests();
        let VariantKind::Refused { label, message } = rule_to_variant_kind(&mutated, &language)
        else {
            panic!(
                "a rule whose binding index does not point at a binder must classify as \
                 `Refused` — resolving it as some other shape is the silent \
                 misclassification this discriminant exists to make impossible",
            );
        };

        assert_eq!(label, "Lam", "the refusal must carry the rule's LABEL");
        assert!(
            message.contains("`Lam`"),
            "and the message must name it — an index names nothing an author can act \
             on. Got: {message}",
        );
        assert!(
            message.contains("binder index"),
            "the message must say WHICH index disagrees with the items, since a rule \
             has both a binder index and a body index. Got: {message}",
        );
        assert!(
            message.contains("macro bug"),
            "and it must say the fault is the macro's, so the reader does not go \
             looking for a mistake in their grammar. Got: {message}",
        );
    }

    /// ★ THE MUTATION CELL for the BODY index — a different index, a different
    /// message. One message for both would not say which to look at.
    #[test]
    fn a_binding_whose_body_is_not_a_non_terminal_refuses_differently() {
        let mut mutated = binder_rule(GrammarItem::Binder { category: id("Term") });
        mutated.items[1] = GrammarItem::Terminal(".".to_string());

        let language = crate::gen::empty_language_for_tests();
        let VariantKind::Refused { message, .. } = rule_to_variant_kind(&mutated, &language) else {
            panic!("a body index that does not point at a non-terminal must refuse");
        };
        assert!(
            message.contains("body index"),
            "the body-index refusal must be distinguishable from the binder-index one: \
             {message}",
        );
        assert!(
            !message.contains("binder index"),
            "…and must not claim the binder index is what went wrong: {message}",
        );
    }

    /// ★ THE CONTROL that must NOT discriminate: the well-formed twin still
    /// classifies as a binder, with the categories it declares.
    #[test]
    fn a_well_formed_binder_rule_still_classifies_as_a_binder() {
        let control = binder_rule(GrammarItem::Binder { category: id("Term") });
        let language = crate::gen::empty_language_for_tests();
        match rule_to_variant_kind(&control, &language) {
            VariantKind::Binder { label, binder_cat, body_cat, .. } => {
                assert_eq!(label, "Lam", "the control keeps its label");
                assert_eq!(binder_cat, "Term", "and its binder category");
                assert_eq!(body_cat, "Term", "and its body category");
            },
            other => panic!(
                "the well-formed twin must still classify as a binder — otherwise the \
                 cells above prove only that this classifier refuses everything. Got: \
                 {other:?}"
            ),
        }
    }
}

#[cfg(test)]
mod task14_tests {
    use super::*;

    fn pred_field(optional: bool) -> FieldInfo {
        FieldInfo {
            category: format_ident!("Guard"),
            is_collection: false,
            coll_type: None,
            is_predicate: true,
            is_optional: optional,
            opaque_leaf: None,
        }
    }

    fn scalar_field(cat: &str) -> FieldInfo {
        FieldInfo {
            category: format_ident!("{}", cat),
            is_collection: false,
            coll_type: None,
            is_predicate: false,
            is_optional: false,
            opaque_leaf: None,
        }
    }

    #[test]
    fn regular_visit_arm_pred_clones_no_visit_guard() {
        // Task #14 gate-1: pre-#14 the Regular visit arm pushed the
        // nonexistent `SubstTask::VisitGuard` for an optional pred.
        let cat = format_ident!("Int");
        let label = format_ident!("PCheck");
        let fields = vec![scalar_field("Int"), pred_field(true)];
        let arm = generate_regular_visit_arm(&cat, &label, &fields).to_string();
        assert!(
            arm.contains("let f1_pred = f1 . clone ()"),
            "the pred must be cloned into the assemble carrier: {arm}",
        );
        assert!(
            !arm.contains("VisitGuard"),
            "no Visit task exists for the Guard pseudo-category: {arm}",
        );
    }

    #[test]
    fn regular_assemble_arm_pred_passthrough_no_wrap_guard() {
        // Pre-#14 the extract emitted `AnySubstTerm::WrapGuard` (nonexistent)
        // and the construct Arc-wrapped the pred.
        let cat = format_ident!("Int");
        let label = format_ident!("PCheck");
        let fields = vec![scalar_field("Int"), pred_field(true)];
        let arm = generate_regular_assemble_arm(&cat, &label, &fields).to_string();
        assert!(
            arm.contains("f1_pred : Option < mettail_runtime :: BehavioralPred >"),
            "the Assemble decl must carry the Option type: {arm}",
        );
        assert!(
            !arm.contains("WrapGuard"),
            "predicates never round-trip through AnySubstTerm: {arm}",
        );
        assert!(
            !arm.contains("Arc :: new (f1_pred)"),
            "the pred passes through unwrapped: {arm}",
        );
    }

    #[test]
    fn field_extract_pred_is_noop() {
        assert!(emit_field_extract(1, &pred_field(true)).is_empty());
        assert!(emit_field_extract(1, &pred_field(false)).is_empty());
    }
}
