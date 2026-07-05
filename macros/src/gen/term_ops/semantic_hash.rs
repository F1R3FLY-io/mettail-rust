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
//! - `from_alternatives` codegen (Stage 2.3.1): dedup by an exact
//!   semantic key collected from the `semantic_hash` write stream. This
//!   collapses cast-permutation cohorts without losing the `-3!`-style
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

use crate::gen::runtime::wpda_codegen::builtin_metadata::{
    classify_fold_alias_shape, classify_simple_projection_shape,
};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use syn::Ident;

/// A reconstruction recipe for a fold-alias (sugar) variant's `semantic_hash`
/// arm. Keyed by label in the `fold_alias_map`; see [`build_fold_alias_arm`].
struct FoldAliasArm {
    /// The fold action's parameter idents in `term_context` order — a 1:1 map
    /// to the variant's boxed fields (`f0`, `f1`, …). Bound to `&Cat` borrows so
    /// the spliced body consumes them via `.clone()`.
    params: Vec<Ident>,
    /// The `fold` action body (`rule.rust_code.code`) — a PURE constructor
    /// re-wrap (verified by `classify_fold_alias_shape`) that rebuilds the
    /// canonical node from the params.
    body: syn::Expr,
}

/// Build a [`FoldAliasArm`] for a rule iff it is a fold-alias whose params are
/// all BOXED CATEGORY fields (non-native, non-collection), so the `&**field`
/// deref in the generated arm is well-typed. Returns `None` otherwise.
///
/// `classify_fold_alias_shape` (the ast-crate structural classifier) guarantees
/// the body is a pure re-wrap and the params are `Simple { Base }`; this adds
/// the macro-side check that each param category is stored boxed (a Proc/Name
/// category, not an inline native `i64`/collection) — the only extra fact the
/// `LanguageDef` carries that the ast crate cannot see.
fn build_fold_alias_arm(rule: &mettail_ast::grammar::GrammarRule, language: &LanguageDef) -> Option<FoldAliasArm> {
    use mettail_ast::grammar::TermParam;
    use mettail_ast::types::TypeExpr;

    classify_fold_alias_shape(rule)?;

    let tc = rule.term_context.as_ref()?;
    let mut params: Vec<Ident> = Vec::with_capacity(tc.len());
    for p in tc {
        match p {
            TermParam::Simple { name, ty: TypeExpr::Base(cat) } => {
                let lt = language.get_type(cat);
                let is_boxed_category = lt
                    .map(|t| t.native_type.is_none() && t.collection_kind.is_none())
                    .unwrap_or(false);
                if !is_boxed_category {
                    return None;
                }
                params.push(name.clone());
            },
            // classify_fold_alias_shape already rejects non-Simple params; this
            // is a defensive re-check that keeps the field↔param mapping 1:1.
            _ => return None,
        }
    }

    let body = rule.rust_code.as_ref()?.code.clone();
    Some(FoldAliasArm { params, body })
}

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

    // Fold-alias sugar canonicalization (2026-06-29). A sugar `fold` rule whose
    // action is a pure constructor re-wrap (`POutputShort → POutput(NQuote(p),
    // q)`, `NQuoteShort → NQuote(p)`, `NQuoteNil → NQuote(PZero)`) hashes its
    // RECONSTRUCTED canonical node, so the realize-dedup collapses the sugar
    // reading with its (eval-identical) fold target. Keyed by variant label.
    let fold_alias_map: HashMap<String, FoldAliasArm> = language
        .terms
        .iter()
        .filter_map(|rule| {
            build_fold_alias_arm(rule, language).map(|arm| (rule.label.to_string(), arm))
        })
        .collect();

    let task_enum = generate_semantic_task_enum(language);
    let engine = generate_semantic_engine(language, &transparent_labels, &fold_alias_map);
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
    fold_alias_map: &HashMap<String, FoldAliasArm>,
) -> TokenStream {
    let helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            // The category's declared native Rust type drives numeric-leaf
            // canonicalization in the `Literal` arm (threaded to
            // `generate_semantic_variant_arm`).
            let native_type = t.native_type.as_ref();
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
                    generate_semantic_variant_arm(
                        cat,
                        idx as u8,
                        v,
                        transparent_labels,
                        language,
                        native_type,
                        fold_alias_map,
                    )
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

/// (FIX-A) Emit alpha-canonical SEMANTIC hashing for a collection whose elements
/// are a category type (which may contain binders). Each element is routed through
/// its `semantic_hash` (de-Bruijn body + arity-only binder position) instead of
/// structural `Hash` — which hashes a binder's `unique_id`, a process-global
/// counter freshened by every `unbind` and never reset, leaking a run-varying,
/// alpha-irrelevant value into the semantic fingerprint (`exact_key`). The
/// collection's order semantics are preserved per kind:
/// - `Vec`: ordered — length + each element in order.
/// - `HashBag`: order-independent multiset combine (`HashBag::semantic_hash_into`).
/// - `HashMap`: order-independent map combine, ordered by semantic digest
///   (`HashMapLit::semantic_hash_into`).
/// - `HashSet`: no language declares a set of a category element, so this arm is
///   reachable only for non-binder elements whose structural `Hash` is already
///   canonical; it falls back to that.
///
/// `coll_expr` borrows the collection; `element_cat` is its element category.
fn semantic_hash_collection(
    coll_expr: &TokenStream,
    element_cat: &Ident,
    coll_type: &CollectionType,
) -> TokenStream {
    match coll_type {
        CollectionType::Vec => quote! {
            state.write_usize(#coll_expr.len());
            for __e in #coll_expr.iter() {
                #element_cat::semantic_hash(__e, state);
            }
        },
        CollectionType::HashBag => quote! {
            #coll_expr.semantic_hash_into(state, |__e, __h| #element_cat::semantic_hash(__e, __h));
        },
        CollectionType::HashMap | CollectionType::PathMap => quote! {
            #coll_expr.semantic_hash_into(
                state,
                |__k, __h| #element_cat::semantic_hash(__k, __h),
                |__v, __h| #element_cat::semantic_hash(__v, __h),
            );
        },
        CollectionType::HashSet => quote! {
            std::hash::Hash::hash(#coll_expr, state);
        },
    }
}

/// Numeric-leaf canonicalization (2026-06-29) — collapse the cast-promotion
/// tower so the realize-dedup sees ONE representative per numeric *value*.
///
/// ## Problem
///
/// A numeric literal the lexer read from a single source token can reach a
/// category through several *transparent* lossless promotion casts
/// (`Int → BigInt`, `UInt32 → Int → BigInt`, `Fixed → BigRat`, …). After the
/// transparent-wrapper collapse (see `generate_semantic_regular_arm`) those reps
/// all reduce to hashing their *leaf* literal — but the leaves live in different
/// categories (`Int`/`BigInt`/`UInt32`/…) with different per-category
/// `variant_idx` AND different native-value encodings, so equal mathematical
/// values hash *differently*. With `k` literals each gaining `m` transparent
/// reps the cohort blows up to `m^k` (the measured `3^4 = 81` for the chained
/// `Map().set(1,10).set(2,20)` case), overflowing the realize frontier budget.
///
/// ## Fix
///
/// Rewrite a NUMERIC leaf's hash to a FAMILY-TAGGED CANONICAL value that depends
/// only on the mathematical value and its family — never on the source category
/// or native width:
///   - integer family (`NativeType::is_integer()`): `NUMERIC_INT_TAG` followed
///     by `CanonicalBigInt::to_canonical_bytes()` (minimal two's-complement LE).
///     Primitive widths promote losslessly through `num_bigint::BigInt`
///     (mirrors `native::lossless_coercion` codegen); `CanonicalBigInt` is
///     already canonical.
///   - rational family (`CanonicalBigRat` / `CanonicalFixedPoint`):
///     `NUMERIC_RAT_TAG` followed by `to_canonical_bytes()` — the length-framed
///     reduced `(numer, denom)` of the value's rational form. The two wrappers
///     emit the SAME framed format, so a fixed-point and a big-rational of equal
///     value hash identically.
///
/// The two distinct family tags keep the integer `1` and the rational `1/1`
/// observationally apart (they ARE distinct under the evaluator).
///
/// ## Why `to_canonical_bytes()` and not `Hash::hash`
///
/// `num_rational::Ratio::hash` hashes the *continued-fraction* expansion
/// (`div_mod_floor` recursion), so `CanonicalBigRat(3/2)::hash` writes `[1,2,0]`
/// while `CanonicalFixedPoint(1.5)::hash` (manual `numer.hash();denom.hash();`)
/// writes `[3,2]` — `Hash::hash` would NOT unify the two rational wrappers.
/// `to_canonical_bytes()` is the documented `Eq`-agreeing canonical form (the
/// same key the Dovetail op-enum uses) and is identical across wrappers, so it
/// unifies them by construction. The bytes are written through `Hasher::write`
/// behind an explicit `write_usize(len)` frame so the leaf is self-delimiting
/// for ANY `Hasher` (the dedup's `FramedSemanticKeyHasher` already frames
/// `write`, but the framing keeps the stream unambiguous regardless).
///
/// ## Soundness
///
/// The realize-dedup only ever compares alternatives spanning the SAME source
/// tokens — i.e. the SAME lexed value — so collapsing them keeps the
/// minimum-weight representative of one value and never merges two values.
///
/// Returns `None` for non-numeric leaves (`Bool`/`Str`/`Float`/collection/
/// other), whose arm is left byte-identical to the pre-change behavior.
fn semantic_hash_numeric_literal_body(native_type: &syn::Type) -> Option<TokenStream> {
    use crate::gen::native::NativeType;

    // High sentinels distinct from any realistic per-category `variant_idx`
    // (the engine asserts <= 255 variants, and a numeric token never derives a
    // non-numeric structural variant, so an idx==tag collision is unreachable in
    // the same-span dedup comparison).
    const NUMERIC_INT_TAG: u8 = 0xFE;
    const NUMERIC_RAT_TAG: u8 = 0xFD;

    let nt = NativeType::from_syn_type(native_type);

    if nt.is_integer() {
        // `CanonicalBigInt` is already canonical; primitives promote losslessly
        // via `num_bigint::BigInt::from(_)` (every fixed integer width has a
        // `From` impl, exactly as `lossless_coercion.rs` emits).
        let canon_bytes = if matches!(nt, NativeType::CanonicalBigInt) {
            quote! { v.to_canonical_bytes() }
        } else {
            quote! {
                ::mettail_runtime::CanonicalBigInt::from(::num_bigint::BigInt::from(*v))
                    .to_canonical_bytes()
            }
        };
        return Some(quote! {
            state.write_u8(#NUMERIC_INT_TAG);
            let __numeric_canon: ::std::vec::Vec<u8> = #canon_bytes;
            state.write_usize(__numeric_canon.len());
            state.write(__numeric_canon.as_slice());
        });
    }

    if matches!(nt, NativeType::CanonicalBigRat | NativeType::CanonicalFixedPoint) {
        return Some(quote! {
            state.write_u8(#NUMERIC_RAT_TAG);
            let __numeric_canon: ::std::vec::Vec<u8> = v.to_canonical_bytes();
            state.write_usize(__numeric_canon.len());
            state.write(__numeric_canon.as_slice());
        });
    }

    None
}

/// The constructor label of any `VariantKind` (all variants carry one).
fn variant_label(variant: &VariantKind) -> &Ident {
    match variant {
        VariantKind::Var { label }
        | VariantKind::Literal { label }
        | VariantKind::Nullary { label }
        | VariantKind::Regular { label, .. }
        | VariantKind::Collection { label, .. }
        | VariantKind::Binder { label, .. }
        | VariantKind::MultiBinder { label, .. } => label,
    }
}

/// Emit the `semantic_hash` arm for a fold-alias (sugar) variant: bind each
/// param to a `&Cat` borrow of the corresponding boxed field, run the rule's own
/// `fold` action to RECONSTRUCT the canonical node, and recurse `semantic_hash`
/// on it. This makes `semantic_hash(POutputShort(p, q))` byte-identical to
/// `semantic_hash(POutput(NQuote(p), q))`, so the realize-dedup collapses the
/// sugar reading with its fold target.
///
/// ## Soundness & termination
///
/// The spliced body IS the evaluator's own fold action, so the reconstructed
/// node is observationally equal to the sugar node by construction — only
/// sugar≡target is merged, never two distinct sends (their params, hence
/// hashes, differ). `classify_fold_alias_shape` forbids a self-reconstruction
/// (root variant ≠ rule label); since each fold target is a normal-form
/// canonical constructor (not itself a fold-alias in practice), the nested
/// `semantic_hash` does not re-enter this arm — reconstruction terminates with
/// the fold relation (which terminates because it is the evaluator's).
///
/// ## Cost
///
/// Reconstruction clones the sugar node's subtree once and runs a (re-entrant,
/// TLS-pooled) nested `semantic_hash`. Sugar nodes are rare and shallow, so the
/// extra clone is negligible; correctness of the dedup fingerprint is the goal.
fn generate_fold_alias_arm(
    category: &Ident,
    variant: &VariantKind,
    arm: &FoldAliasArm,
) -> TokenStream {
    let body = &arm.body;
    match variant {
        VariantKind::Nullary { label } => {
            // Zero-param sugar, e.g. `NQuoteNil → NQuote(PZero)`.
            quote! {
                #category::#label => {
                    let __canonical: #category = #body;
                    __canonical.semantic_hash(state);
                }
            }
        },
        VariantKind::Regular { label, fields } => {
            let field_names: Vec<Ident> =
                (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
            debug_assert_eq!(
                arm.params.len(),
                fields.len(),
                "fold-alias {} param/field arity mismatch ({} params, {} fields)",
                label,
                arm.params.len(),
                fields.len(),
            );
            // Bind each fold param (term_context order) to a `&Cat` borrow of the
            // corresponding boxed field; the spliced body consumes them via
            // `.clone()` (which yields an owned `Cat`) to rebuild the canonical node.
            let bindings: Vec<TokenStream> = arm
                .params
                .iter()
                .zip(field_names.iter())
                .map(|(p, f)| quote! { let #p = &**#f; })
                .collect();
            quote! {
                #category::#label(#(ref #field_names),*) => {
                    #(#bindings)*
                    let __canonical: #category = #body;
                    __canonical.semantic_hash(state);
                }
            }
        },
        // `build_fold_alias_arm` only admits Nullary / all-Simple Regular variants.
        _ => unreachable!("fold-alias variant must be Nullary or Regular"),
    }
}

/// Generate match arms for a specific variant in the semantic_hash engine.
///
/// Key difference from iterative_hash: each arm decides whether to emit a
/// discriminant. Transparent wrappers skip the discriminant AND skip the
/// variant tag, delegating directly to the inner child.
///
/// `native_type` is the *category's* declared native Rust type (threaded from
/// `LangType::native_type`); it drives the numeric-leaf canonicalization in the
/// `Literal` arm and is unused by the other arms.
fn generate_semantic_variant_arm(
    category: &Ident,
    variant_idx: u8,
    variant: &VariantKind,
    transparent_labels: &HashSet<String>,
    language: &LanguageDef,
    native_type: Option<&syn::Type>,
    fold_alias_map: &HashMap<String, FoldAliasArm>,
) -> TokenStream {
    // Fold-alias sugar canonicalization (takes precedence over the structural
    // arms below): hash the RECONSTRUCTED canonical node so the sugar reading
    // dedups with its (eval-identical) fold target. Only Nullary / all-Simple-
    // CATEGORY-param Regular variants are admitted (see `build_fold_alias_arm`),
    // so the field↔param mapping is a trivial 1:1.
    if let Some(arm) = fold_alias_map.get(&variant_label(variant).to_string()) {
        return generate_fold_alias_arm(category, variant, arm);
    }

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
            // NUMERIC leaves (integer / rational families) get a family-tagged
            // canonical-value hash so cast-promotion-tower reps of one value
            // collapse (see `semantic_hash_numeric_literal_body`). Non-numeric
            // leaves (Bool/Str/Float/collection/other) fall through to the
            // original `(variant_idx, native value)` form — byte-identical.
            let body = native_type
                .and_then(semantic_hash_numeric_literal_body)
                .unwrap_or_else(|| {
                    quote! {
                        state.write_u8(#variant_idx);
                        std::hash::Hash::hash(v, state);
                    }
                });
            quote! {
                #category::#label(v) => {
                    #body
                }
            }
        },

        VariantKind::Var { label } => {
            // Free-variable cast-tower canonicalization (2026-06-29, "Arm B") —
            // sibling of the numeric-leaf canon (`semantic_hash_numeric_literal_body`).
            //
            // A single source identifier reaches a category through several
            // *transparent* lossless promotion casts and so realizes as a TOWER of
            // typed-var leaves of the SAME source variable — e.g. `a:Proc` becomes
            // `PVar(a)`, `CastBigRat(BVar(a))`, `CastBigRat(IntToBigRat(IVar(a)))`, …
            // (5 reps; verified by probe), all with the SAME `OrdVar` identity
            // (free `unique_id` / bound de-Bruijn). The transparent-wrapper collapse
            // (`generate_semantic_regular_arm`) strips the casts, so each rep bottoms
            // out at a Var arm whose only difference is the per-category `variant_idx`
            // — hashing 5 *different* keys for one variable. `realize_packing_call`'s
            // cartesian product multiplies that m-way tower across every operand of a
            // chain (`a | b | c | d`: m^k), overflowing `REALIZE_CAP` on bare infix
            // `|` (the braced-bag and numeric-literal paths are already canonicalized).
            //
            // Fix: write a UNIFORM var tag (independent of the source category's
            // `variant_idx`) followed by the unchanged `OrdVar` hash, so every
            // type-reading of one identifier collapses to ONE realize-dedup key while
            // DISTINCT variables (distinct `OrdVar`) stay distinct. Sound by the same
            // same-span argument as the numeric canon: the realize-dedup only compares
            // alternatives spanning the SAME source token, i.e. the SAME variable.
            // `0xFB` is a high sentinel distinct from the numeric tags (`0xFE`/`0xFD`)
            // and from any realistic per-category `variant_idx`; even a first-byte
            // brush with idx `0xFB` is harmless because the framed `OrdVar` hash that
            // follows disambiguates the full key.
            quote! {
                #category::#label(v) => {
                    state.write_u8(0xFBu8);
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

        VariantKind::Collection { label, element_cat, coll_type } => {
            // (FIX-A) Collections of category-typed elements are hashed via the
            // element's alpha-canonical `semantic_hash`, not structural `Hash`.
            // This closes the former limitation (noted here historically) where
            // category elements were hashed structurally — leaking a binder's
            // run-varying `unique_id` into the semantic fingerprint and making
            // `exact_key` non-deterministic for terms like Ambient's
            // `{ new(x, P) | Q }` (a `PNew` binder inside a `PPar` bag).
            let coll_expr = quote! { coll };
            let body = semantic_hash_collection(&coll_expr, element_cat, coll_type);
            quote! {
                #category::#label(coll) => {
                    state.write_u8(#variant_idx);
                    #body
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
                // (FIX-A) element semantic_hash, not structural Hash.
                let coll_type = field
                    .coll_type
                    .as_ref()
                    .expect("collection field must carry a CollectionType");
                let sem = semantic_hash_collection(&quote! { __c }, &field.category, coll_type);
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__c) => {
                            state.write_u8(1u8);
                            #sem
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
                // (FIX-A) Collection fields of category elements hash via the
                // element's alpha-canonical `semantic_hash`, not structural `Hash`.
                let coll_type = field
                    .coll_type
                    .as_ref()
                    .expect("collection field must carry a CollectionType");
                final_stmts.push(semantic_hash_collection(
                    &quote! { #name },
                    &field.category,
                    coll_type,
                ));
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
                // (FIX-A) element semantic_hash, not structural Hash.
                let coll_type = field
                    .coll_type
                    .as_ref()
                    .expect("collection field must carry a CollectionType");
                let sem = semantic_hash_collection(&quote! { __c }, &field.category, coll_type);
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__c) => {
                            state.write_u8(1u8);
                            #sem
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
                // (FIX-A) Collection fields of category elements hash via the
                // element's alpha-canonical `semantic_hash`, not structural `Hash`.
                let coll_type = field
                    .coll_type
                    .as_ref()
                    .expect("collection field must carry a CollectionType");
                final_stmts.push(semantic_hash_collection(
                    &quote! { #name },
                    &field.category,
                    coll_type,
                ));
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
            // (FIX-A) pre-scope collection: element semantic_hash, not std Hash.
            // Handles both `Coll` and `*opt(Coll)` = `Option<Coll>` shapes.
            let coll_type = field
                .coll_type
                .as_ref()
                .expect("collection field must carry a CollectionType");
            if field.is_optional {
                let sem = semantic_hash_collection(&quote! { __c }, &field.category, coll_type);
                hash_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__c) => {
                            state.write_u8(1u8);
                            #sem
                        }
                    }
                });
            } else {
                hash_stmts.push(semantic_hash_collection(
                    &quote! { #name },
                    &field.category,
                    coll_type,
                ));
            }
        } else {
            hash_stmts.push(quote! {
                (&**#name).semantic_hash(state);
            });
        }
    }

    // Scope: hash the binder ARITY (always 1 for a single binder), NOT the
    // binder's `FreeVar` identity. (FIX-A) moniker `FreeVar::Hash` hashes only
    // `unique_id`, a process-global counter freshened by every `unbind` and
    // never reset — so hashing the pattern leaked a run-varying, alpha-irrelevant
    // value into the semantic fingerprint (`exact_key`/`content_key`), making it
    // non-deterministic and non-alpha-canonical. The bound occurrences in the
    // body are de-Bruijn `BoundVar{scope,binder}` coordinates (name-free, already
    // alpha-canonical) and are hashed via the trampolined body task below, so the
    // arity is the only structural information the binder position must contribute.
    let body_task = format_ident!("SemHash{}", body_cat);
    hash_stmts.push(quote! {
        {
            state.write_usize(1usize);
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
            // (FIX-A) pre-scope collection: element semantic_hash, not std Hash.
            // Handles both `Coll` and `*opt(Coll)` = `Option<Coll>` shapes.
            let coll_type = field
                .coll_type
                .as_ref()
                .expect("collection field must carry a CollectionType");
            if field.is_optional {
                let sem = semantic_hash_collection(&quote! { __c }, &field.category, coll_type);
                hash_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__c) => {
                            state.write_u8(1u8);
                            #sem
                        }
                    }
                });
            } else {
                hash_stmts.push(semantic_hash_collection(
                    &quote! { #name },
                    &field.category,
                    coll_type,
                ));
            }
        } else {
            hash_stmts.push(quote! {
                (&**#name).semantic_hash(state);
            });
        }
    }

    // Scope: hash the binder ARITY (number of binders), NOT the binders'
    // `FreeVar` identities. (FIX-A) See the single-binder arm above for the
    // rationale; for a multi-binder the arity (`unsafe_pattern.len()`) is the
    // structural information that distinguishes, e.g., a 2-binder from a 3-binder
    // scope whose bodies coincide on a shared de-Bruijn prefix. The body's
    // `BoundVar{scope,binder}` coordinates (incl. `BinderIndex`) disambiguate
    // which binder each occurrence references and are hashed via the body task.
    let body_task = format_ident!("SemHash{}", body_cat);
    hash_stmts.push(quote! {
        {
            state.write_usize(#scope_name.inner().unsafe_pattern.len());
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
            /// written directly. Runtime ambiguity dedup compares the
            /// collected semantic write stream, not a finished 64-bit
            /// digest, so distinct streams are not lost to digest
            /// collisions.
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
