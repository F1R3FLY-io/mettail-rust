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
    classify_fold_alias_send_shape, classify_fold_alias_shape, classify_simple_projection_shape,
};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::grammar::{GrammarRule, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use syn::Ident;

/// FNV-1a (64-bit) of a category NAME, evaluated at codegen time.
///
/// #151 open thread 2: the collection-literal `semantic_hash` arm writes this
/// before the variant index so two categories' literals cannot produce identical
/// write streams (rholang's `Map::MapLit` and `Pathmap::PathmapLit` are both
/// variant `1`, both delegate to `HashMapLit::hash`, and both are reached
/// through TRANSPARENT wrappers that write zero bytes).
///
/// The NAME is hashed rather than a positional index because an index moves
/// whenever a category is inserted, which would silently re-pin every
/// fingerprint. FNV-1a is used for its two relevant properties: it is fully
/// specified (so the value is reproducible across toolchains and builds, unlike
/// `DefaultHasher`), and it is trivially computable in `const`-style code here.
///
/// Reference: Fowler, Noll & Vo, "The FNV Non-Cryptographic Hash Algorithm",
/// IETF draft-eastlake-fnv; 64-bit offset basis `0xcbf29ce484222325`, prime
/// `0x100000001b3`.
fn fnv1a64(name: &str) -> u64 {
    const OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut hash = OFFSET_BASIS;
    for byte in name.as_bytes() {
        hash ^= *byte as u64;
        hash = hash.wrapping_mul(PRIME);
    }
    hash
}

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
fn build_fold_alias_arm(
    rule: &mettail_ast::grammar::GrammarRule,
    language: &LanguageDef,
) -> Option<FoldAliasArm> {
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

// ── Fold-alias POLYADIC-SEND canonicalization (Residual #11-1, 2026-07-14) ────
//
// The scalar `FoldAliasArm` above cannot express the polyadic send sugars
// (`@p!(a, bs…)`, `POutputShort2Plus` / `PPersistOutputShort2Plus`): they carry
// a trailing `Vec` "rest" param and their grammar body LOWERS to the SCALAR
// `POutput` (via `mk_proc_list`), so RUNNING that body would collapse the sugar
// onto the scalar send — over-pruning past the polyadic canonical the prologue's
// receiver-led reading actually is. Instead the arm below SYNTHESIZES the
// paired polyadic CANONICAL node `POLY_CANON(NQuote(p), a, bs)` and hashes THAT
// structurally, matching the projection-isolation prologue's receiver-led
// reading `POLY_CANON(NQuoteShort(p), a, bs)` byte-for-byte (its `NQuoteShort`
// channel sub-folds to `NQuote(p)` via the existing scalar fold-alias), so the
// facade dedups 3→2 = walker. All derivation is GRAMMAR-DRIVEN (channel expr,
// scalar-target pairing key, operand smart-pointer) — no constructor name is
// hardcoded; the predicate fires only where a language exhibits the shape.

/// A reconstruction recipe for a fold-alias polyadic-SEND sugar's `semantic_hash`
/// arm. Keyed by sugar label in `fold_alias_send_map`; see
/// [`build_fold_alias_send_map`].
struct FoldAliasSendArm {
    /// The canonical target variant (POLY_CANON, e.g. `POutput2Plus`) — the
    /// bare-channel sibling with the same scalar fold target. Reconstruction root.
    poly_canon_label: Ident,
    /// The channel expr lifted VERBATIM from the sugar body's tail-constructor
    /// first arg (`Arc::new(Name::NQuote(Arc::new(p.clone())))`) — spliced as
    /// POLY_CANON's channel field 0 (its `p.clone()` resolves through the arm's
    /// param bindings).
    channel_expr: syn::Expr,
    /// The smart-pointer constructor (`std::sync::Arc::new`) extracted from
    /// `channel_expr`'s outer `…::new`, reused to box the operand fields (a
    /// language boxes every category field with ONE smart pointer).
    box_new: syn::Expr,
    /// Sugar params in FIELD order: `(ident, is_vec_collection)`. Element 0 is the
    /// channel-source param (used inside `channel_expr`); the rest are operands.
    sugar_params: Vec<(Ident, bool)>,
    /// POLY_CANON operand fields (field index ≥1, i.e. excluding channel field 0),
    /// in order: whether each is a `Vec` collection. Aligned 1:1 with the sugar's
    /// operand params (`sugar_params[1..]`).
    poly_operand_is_collection: Vec<bool>,
}

/// Whether a `TermParam` is a `Simple` category param; returns `(ident,
/// is_vec_collection)`. Boxed-category (`Base`) ⇒ `false`; `Vec(_)` ⇒ `true`.
/// Any other shape ⇒ `None` (the send classifier already guaranteed these are
/// the only two, but this keeps the field↔param mapping explicit and total).
fn simple_send_param(p: &TermParam) -> Option<(Ident, bool)> {
    match p {
        TermParam::Simple { name, ty: TypeExpr::Base(_) } => Some((name.clone(), false)),
        TermParam::Simple {
            name,
            ty: TypeExpr::Collection { coll_type: CollectionType::Vec, .. },
        } => Some((name.clone(), true)),
        _ => None,
    }
}

/// Build the fold-alias-send reconstruction recipe for a SUGAR rule paired with
/// its canonical sibling `canon_rule`. Returns `None` (⇒ the sugar stays
/// structural) if the channel is not the first field in either rule, the operand
/// arities disagree, or the channel expr is not a smart-pointer wrap.
fn build_fold_alias_send_arm(
    sugar_rule: &GrammarRule,
    canon_rule: &GrammarRule,
    shape: &mettail_ast::grammar_shapes::FoldAliasSendShape,
) -> Option<FoldAliasSendArm> {
    // Sugar params in field order.
    let sugar_tc = sugar_rule.term_context.as_ref()?;
    let mut sugar_params: Vec<(Ident, bool)> = Vec::with_capacity(sugar_tc.len());
    for p in sugar_tc {
        sugar_params.push(simple_send_param(p)?);
    }
    // The channel-source param must be field 0 (the `@ chan ! ( ops )` shape;
    // the classifier already asserted this, re-check for the reconstruction).
    if sugar_params.first().map(|(id, _)| id.to_string()) != Some(shape.channel_param.clone()) {
        return None;
    }

    // POLY_CANON params in field order; its channel (the bare param) must be
    // field 0 too, so operand fields 1.. align with the sugar's operands 1...
    let canon_tc = canon_rule.term_context.as_ref()?;
    let canon_shape = classify_fold_alias_send_shape(canon_rule)?;
    let mut canon_params: Vec<(Ident, bool)> = Vec::with_capacity(canon_tc.len());
    for p in canon_tc {
        canon_params.push(simple_send_param(p)?);
    }
    if canon_params.first().map(|(id, _)| id.to_string()) != Some(canon_shape.channel_param.clone())
    {
        return None;
    }
    // Operand arity + collection-kind parity (the sugar's operand tail must match
    // the canonical's field-by-field so the reconstruction is well-typed).
    if sugar_params.len() != canon_params.len() {
        return None;
    }
    let poly_operand_is_collection: Vec<bool> =
        canon_params.iter().skip(1).map(|(_, c)| *c).collect();
    for ((_, sugar_c), poly_c) in sugar_params
        .iter()
        .skip(1)
        .zip(poly_operand_is_collection.iter())
    {
        if sugar_c != poly_c {
            return None;
        }
    }

    // The operand smart-pointer = the channel expr's outer `…::new` call func.
    let box_new = match &shape.channel_expr {
        syn::Expr::Call(c) => (*c.func).clone(),
        _ => return None,
    };

    Some(FoldAliasSendArm {
        poly_canon_label: canon_rule.label.clone(),
        channel_expr: shape.channel_expr.clone(),
        box_new,
        sugar_params,
        poly_operand_is_collection,
    })
}

/// Map every fold-alias-send SUGAR label to its reconstruction recipe. Each
/// sugar is paired with the UNIQUE bare-channel CANONICAL sibling that shares its
/// category and scalar fold target (A1c self-exclusion: canonicals are bare,
/// sugars are not, so `POLY_CANON.label != sugar.label` automatically — no
/// self-reconstruction / ∞ codegen recursion). A sugar with 0 or ≥2 candidate
/// canonicals is left structural (safety).
fn build_fold_alias_send_map(language: &LanguageDef) -> HashMap<String, FoldAliasSendArm> {
    // Classify every rule that matches the send shape (sugars AND canonicals).
    let shaped: Vec<(&GrammarRule, mettail_ast::grammar_shapes::FoldAliasSendShape)> = language
        .terms
        .iter()
        .filter_map(|r| classify_fold_alias_send_shape(r).map(|s| (r, s)))
        .collect();

    let mut map: HashMap<String, FoldAliasSendArm> = HashMap::new();
    for (sugar_rule, shape) in &shaped {
        // A1c: canonicals (bare channel) are the pairing TARGETS — never folded.
        if shape.channel_is_bare_param {
            continue;
        }
        // POLY_CANON = the bare-channel sibling, same category + scalar target.
        let canons: Vec<&(&GrammarRule, mettail_ast::grammar_shapes::FoldAliasSendShape)> = shaped
            .iter()
            .filter(|(_, s)| {
                s.channel_is_bare_param
                    && s.target_category == shape.target_category
                    && s.scalar_target_label == shape.scalar_target_label
            })
            .collect();
        // 0 = no canonical to reconstruct into; ≥2 = ambiguous ⇒ leave structural.
        let [canon] = canons.as_slice() else {
            continue;
        };
        let (canon_rule, _canon_shape) = canon;
        if let Some(arm) = build_fold_alias_send_arm(sugar_rule, canon_rule, shape) {
            map.insert(sugar_rule.label.to_string(), arm);
        }
    }
    map
}

/// Emit the `semantic_hash` arm for a fold-alias polyadic-SEND sugar: bind the
/// sugar's fields, SYNTHESIZE the paired canonical `POLY_CANON(channel_wrap,
/// operands…)` node (channel field 0 = the grammar-lifted `channel_expr`; each
/// operand field boxed via the language's own smart-pointer or cloned for the
/// `Vec` rest), and recurse `semantic_hash` on it — so the sugar dedups with the
/// prologue's receiver-led canonical reading.
///
/// ## Termination
///
/// `POLY_CANON` is a BARE-channel canonical (`channel_is_bare_param`), so it is
/// NEVER in `fold_alias_send_map`; its own arm is the structural one and the
/// nested `semantic_hash` does not re-enter this arm. The reconstruction is a
/// finite node built from clones of the sugar's fields.
fn generate_fold_alias_send_arm(
    category: &Ident,
    sugar_label: &Ident,
    arm: &FoldAliasSendArm,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..arm.sugar_params.len())
        .map(|i| format_ident!("f{}", i))
        .collect();

    // Bind each sugar param to its field so the spliced `channel_expr`
    // (`p.clone()`) and the operand exprs resolve: boxed-category → `&**f`
    // (⇒ `&Cat`); `Vec` rest → `f` (⇒ `&Vec<Cat>`).
    let bindings: Vec<TokenStream> = arm
        .sugar_params
        .iter()
        .zip(field_names.iter())
        .map(|((id, is_coll), f)| {
            if *is_coll {
                quote! { let #id = #f; }
            } else {
                quote! { let #id = &**#f; }
            }
        })
        .collect();

    // Operand exprs for POLY_CANON fields 1.. (channel is field 0): boxed →
    // `<box_new>(<param>.clone())`; `Vec` rest → `<param>.clone()`.
    let box_new = &arm.box_new;
    let operand_exprs: Vec<TokenStream> = arm
        .sugar_params
        .iter()
        .skip(1)
        .zip(arm.poly_operand_is_collection.iter())
        .map(|((id, _sugar_coll), poly_coll)| {
            if *poly_coll {
                quote! { #id.clone() }
            } else {
                quote! { #box_new(#id.clone()) }
            }
        })
        .collect();

    let channel_expr = &arm.channel_expr;
    let poly = &arm.poly_canon_label;
    quote! {
        #category::#sugar_label(#(ref #field_names),*) => {
            // Fold-alias polyadic-send (Residual #11-1): reconstruct the CANONICAL
            // `POLY_CANON(NQuote(p), a, bs…)` — the SAME rho term as the prologue's
            // receiver-led `POLY_CANON(NQuoteShort(p), a, bs…)` reading (NQuoteShort
            // sub-folds to NQuote) — and hash it structurally so the two dedup.
            #(#bindings)*
            let __canonical: #category = #category::#poly(
                #channel_expr,
                #(#operand_exprs),*
            );
            __canonical.semantic_hash(state);
        }
    }
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

    // Fold-alias POLYADIC-SEND canonicalization (Residual #11-1). The trailing-Vec
    // send sugars (`POutputShort2Plus`, `PPersistOutputShort2Plus`) reconstruct
    // their paired canonical `…2Plus(NQuote(p), a, bs)` so the projection-isolation
    // prologue's receiver-led reading dedups with them (facade 3→2 = walker).
    // Keyed by sugar label; disjoint from `fold_alias_map` (send sugars have a Vec
    // param ⇒ the scalar classifier rejects them).
    let fold_alias_send_map: HashMap<String, FoldAliasSendArm> =
        build_fold_alias_send_map(language);

    let task_enum = generate_semantic_task_enum(language);
    let engine = generate_semantic_engine(
        language,
        &transparent_labels,
        &fold_alias_map,
        &fold_alias_send_map,
    );
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
            #(#variants,)*
            /// ★ #162 — a `usize` written to `state` at its own position in the
            /// stream, so a collection's LENGTH PREFIX can precede element tasks.
            ///
            /// Without it the `Vec` arm had to write the prefix and then call
            /// `Elem::semantic_hash(e, state)` per element — a whole-value
            /// re-entry, Θ(depth). Measured 4,096 B/level (debug) the moment #154
            /// routed the collection-literal arm here from structural `Hash`.
            AbsorbUsize(usize),
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
    fold_alias_send_map: &HashMap<String, FoldAliasSendArm>,
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
                        fold_alias_send_map,
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
                    // ★ #162 — `state.write_usize(n)`, the exact call the eager
                    // form made, issued at its own position in the stream.
                    SemanticHashTask::AbsorbUsize(n) => {
                        std::hash::Hasher::write_usize(state, n);
                    }
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
        // ★ #162 — one task per element, so the walk stays on the work stack.
        //
        // ⚠ The LENGTH PREFIX is written FIRST, so on a LIFO stack it is pushed
        // LAST. Same discipline as `iterative_hash::hash_collection_stmts`, and the
        // OPPOSITE of `iterative_cmp`, where `Vec`'s length is the lexicographic
        // tiebreak and therefore pops last.
        CollectionType::Vec => {
            let task_variant = format_ident!("SemHash{}", element_cat);
            quote! {
                for __e in #coll_expr.iter().rev() {
                    stack.push(SemanticHashTask::#task_variant(__e as *const _));
                }
                stack.push(SemanticHashTask::AbsorbUsize(#coll_expr.len()));
            }
        },
        CollectionType::HashBag => quote! {
            #coll_expr.semantic_hash_into(state, |__e, __h| #element_cat::semantic_hash(__e, __h));
        },
        CollectionType::HashMap => quote! {
            #coll_expr.semantic_hash_into(
                state,
                |__k, __h| #element_cat::semantic_hash(__k, __h),
                |__v, __h| #element_cat::semantic_hash(__v, __h),
            );
        },
        // ★ #74 / #154 — a pathmap's VALUE is a `PathValue<E>`, not an `E`. An
        // `Unset` entry has no sub-term at all (Ruling B: unset ≠ Nil), so it
        // contributes only its 1-byte tag; a `Set` entry contributes the tag and
        // then its inner term's ALPHA-CANONICAL digest.
        //
        // ⚠ This arm used to share `HashMap`'s, which typechecked only because the
        // value closure was never instantiated with a real `PathValue` — the
        // `CollectionLiteral` route that reaches it was going through structural
        // `Hash` instead.
        CollectionType::PathMap => quote! {
            #coll_expr.semantic_hash_into(
                state,
                |__k, __h| #element_cat::semantic_hash(__k, __h),
                |__v, __h| match __v {
                    mettail_runtime::PathValue::Unset => {
                        std::hash::Hasher::write_u8(__h, 0u8);
                    },
                    mettail_runtime::PathValue::Set(__inner) => {
                        std::hash::Hasher::write_u8(__h, 1u8);
                        #element_cat::semantic_hash(__inner, __h);
                    },
                },
            );
        },
        // ★ #154 — was `std::hash::Hash::hash(#coll_expr, state)`, i.e. STRUCTURAL,
        // and therefore leaked a binder's run-varying `unique_id` exactly as the
        // collection-literal arm did. It read as correct next to its siblings
        // because the whole helper is named `semantic_hash_collection`; the only way
        // to see it was to read the arm. `HashSetLit::semantic_hash_into` was added
        // for this call.
        CollectionType::HashSet => quote! {
            #coll_expr.semantic_hash_into(
                state,
                |__e, __h| #element_cat::semantic_hash(__e, __h),
            );
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
            // Residual #11-3 (2026-07-14): compute the SAME canonical bytes
            // WITHOUT constructing a transient `CanonicalBigInt`.
            // `CanonicalBigInt::to_canonical_bytes()` is *exactly*
            // `self.get().to_signed_bytes_le()` (minimal two's-complement LE), so
            // `BigInt::from(*v).to_signed_bytes_le()` writes a BYTE-IDENTICAL
            // stream. The wrapper is avoided because `CanonicalBigInt::from`
            // deliberately LEAKS its boxed `BigInt` payload
            // (`runtime::canonical_bigint`, `Box::into_raw` — immortal by design
            // for interned Ascent/op-enum keys). In the realize-dedup fingerprint
            // that leak fires once PER NUMERIC LEAF PER `semantic_fingerprint`
            // call; on a deep chain the per-node fingerprint fan makes the leaf
            // count `Σ O(subtree) = O(tokens²)`, so the leaked (never-reclaimed)
            // `Box<BigInt>` allocations accumulated `O(tokens²)` resident memory
            // (the 20k-ternary memcg-OOM). A non-leaking `BigInt` drops normally.
            quote! {
                ::num_bigint::BigInt::from(*v).to_signed_bytes_le()
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
        | VariantKind::CollectionLiteral { label, .. }
        | VariantKind::Nullary { label }
        | VariantKind::Regular { label, .. }
        | VariantKind::Collection { label, .. }
        | VariantKind::Binder { label, .. }
        | VariantKind::Refused { label, .. }
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
        // ★ #141 G9. "`build_fold_alias_arm` only admits Nullary / all-Simple
        // Regular variants" is a claim about the CALLER'S filter, held by nothing
        // here. This function yields the arm's tokens, so the refusal is the arm.
        other => {
            let label = variant_label(other);
            let message = format!(
                "mettail internal error: the fold-alias `semantic_hash` arm for `{label}` \
                 was asked to lower a variant that is neither nullary nor an all-simple \
                 regular constructor, which its caller's admission filter is supposed to \
                 exclude. The filter and this emitter have drifted apart. This is a macro \
                 bug, not a grammar bug — please report it."
            );
            quote! { compile_error!(#message); }
        },
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
    fold_alias_send_map: &HashMap<String, FoldAliasSendArm>,
) -> TokenStream {
    // Fold-alias POLYADIC-SEND canonicalization (Residual #11-1; takes precedence
    // over BOTH the scalar fold-alias arm and the structural arms): reconstruct
    // the paired polyadic canonical `POLY_CANON(NQuote(p), a, bs)` and hash it so
    // the projection-isolation prologue's receiver-led reading dedups with the
    // sugar. Disjoint from `fold_alias_map` (send sugars carry a `Vec` param).
    if let Some(send_arm) = fold_alias_send_map.get(&variant_label(variant).to_string()) {
        return generate_fold_alias_send_arm(category, variant_label(variant), send_arm);
    }

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
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Nullary { label } => {
            quote! {
                #category::#label => {
                    state.write_u8(#variant_idx);
                }
            }
        },

        // Stage 0 identity — STAYS. Numeric-family canonicalisation does not
        // apply to collection wrappers; they fall to the structural default.
        // ★★ #154 (2026-07-30) — THE COLLECTION-LITERAL ARM NO LONGER SHARES THIS ONE.
        //
        // A `CollectionLiteral` used to fall through to the `(variant_idx,
        // STRUCTURAL Hash)` body below, and structural `Hash` on a binder-bearing
        // element writes the binder's moniker `unique_id` — a process-global counter
        // freshened by every `unbind` and never reset. So `semantic_hash` of a
        // binder inside a `Map`/`Pathmap`/`List`/`Set`/`Bag` LITERAL was RUN-VARYING,
        // while the same binder inside a `PPar` bag was not: the sibling
        // `VariantKind::Collection` arm had already been fixed by FIX-A (2026-06-29)
        // and routes through `semantic_hash_collection`.
        //
        // `semantic_hash` is CONSENSUS-VISIBLE — it backs `semantic_fingerprint` →
        // `exact_key`/`content_key`, the realize ambiguity-dedup surface — so two
        // nodes whose `unique_id` counters had diverged would disagree about which
        // parse readings are the same reading.
        //
        // ★ The fix is one line of routing because the machinery already existed;
        // what was missing was the DECLARATION that a collection literal is not a
        // leaf. That is the same root cause as #162's stack slope: the
        // `CollectionLiteral` discriminant exists precisely so every consumer states
        // its intent, and this was one of the consumers that had not.
        //
        // ⚠ Gated by `languages/tests/semantic_fingerprint_binder_in_collection_literal.rs`,
        // whose alpha-twin rows go RED the moment this arm rejoins `Literal`'s.
        VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
            let body = semantic_hash_collection(&quote! { v }, element_cat, coll_type);
            quote! {
                #category::#label(v) => {
                    state.write_u8(#variant_idx);
                    #body
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
                    // ★ #151 open thread 2 (2026-07-29) — THE CATEGORY TAG.
                    //
                    // A collection-literal arm used to write ONLY
                    // `(variant_idx, structural hash)`. Rholang's `Map::MapLit`
                    // and `Pathmap::PathmapLit` are BOTH variant `1` of their
                    // categories, `PathMapLit::hash` delegates verbatim to
                    // `HashMapLit::hash`, and the wrappers that reach them
                    // (`Proc::CastMap` / `Proc::CastPathmap`) are TRANSPARENT and
                    // write zero bytes. So the two literals' write streams were
                    // BYTE-IDENTICAL — not merely digest-equal — and
                    // `semantic_fingerprint` records that stream verbatim. The
                    // inner-enum discriminant does not help: both are `Proc`
                    // terms, so it is the same for each.
                    //
                    // The collision is currently LATENT: no shipped surface
                    // yields both a `Map` and a `Pathmap` reading of the same
                    // bytes (`{` opens a map, `{|` a pathmap), so nothing merges
                    // today. It becomes live the moment a surface admits both,
                    // which is the territory #116/#125 are moving through. This
                    // is hardening, landed because it is proven, cheap and
                    // adjacent — not a blocker.
                    //
                    // ⚠ `PathValue` alone does NOT close it. The value bytes gain
                    // a tag, which separates NON-EMPTY pathmaps from maps, but
                    // `{||}` and `{}` have no value bytes at all and would still
                    // collide. The tag is written unconditionally, before the
                    // variant index, so the empty case is covered too.
                    //
                    // The tag is a compile-time FNV-1a of the CATEGORY NAME:
                    // deterministic across builds and independent of category
                    // ORDER (a `src_idx` would move whenever a category is
                    // inserted, silently re-pinning every fingerprint). It is
                    // written only on collection-literal arms — the arms whose
                    // collision is proven — so no other digest moves.
                    // ★★ #151 open thread 2 — THE CATEGORY TAG IS PROVEN
                    // NECESSARY, DISABLED ANYWAY, AND HERE IS WHY. ★★
                    //
                    // ## The defect (PROVEN AT SOURCE, not merely suspected)
                    //
                    // This arm writes `(variant_idx, structural hash)` and NO
                    // category discriminator.
                    //
                    // ⚠ THE ENUMERATION BELOW IS TRANSCRIBED, NOT DERIVED, and that
                    // is worth saying out loud: a hand-maintained mirror of a
                    // computable domain is the exact shape that has shipped as a
                    // non-repair four times in this campaign. It cannot be derived
                    // in place, because this comment lives in the EMITTER and the
                    // domain is a property of a particular grammar's expansion —
                    // `macros` unit tests reach only
                    // `collection_literal_language_for_tests`, not rholang. It is
                    // therefore recorded as a DATED MEASUREMENT with the command
                    // that reproduces it:
                    //
                    //   python3 - <<'PY'   # over target/generated/rholang/semantic_hash.rs
                    //   import re; t=open(...).read()
                    //   re.finditer(r'([A-Za-z0-9_]+)::([A-Za-z0-9_]+)\((?:v|coll)\) => \{'
                    //               r'\s*\n\s*state\.write_u8\((\d+)u8\);', t)
                    //   PY
                    //
                    // RE-DERIVED 2026-07-30 (17 literal-ish arms in total; 11 of
                    // them write `variant_idx == 1`):
                    //
                    //   `Float::FloatLit`, `Bool::BoolLit`, `Str::StringLit`,
                    //   `Bytes::BytesLit`, `List::ListLit`, `Bag::BagLit`,
                    //   `Map::MapLit`, `Set::SetLit`, `Pathmap::PathmapLit`,
                    //   `ReadZipper::Lit`, `WriteZipper::Lit`
                    //
                    // ★ The count is UNCHANGED at eleven and exactly ONE name had
                    // gone stale: `Bytes::StringLit` → `Bytes::BytesLit`, renamed by
                    // `713e0364` when `b"deadbeef"` landed the `![Vec<u8>] as Bytes`
                    // carrier. The remaining six arms carry the numeric family tags
                    // (`0xFE`/`0xFD`) or a real per-variant index, so they were never
                    // part of the colliding class.
                    //
                    // All eleven reaching `Proc::Cast*` wrappers are TRANSPARENT — a
                    // bare `stack.push`, zero bytes.
                    //
                    // So the discriminating prefix of every one of those write
                    // streams is the same single byte `1`. Two pairs collide
                    // COMPLETELY, because their payload encodings also coincide:
                    //
                    //   Map::MapLit / Pathmap::PathmapLit   — `PathMapLit::hash`
                    //       delegates verbatim to `HashMapLit::hash`
                    //   Str::StringLit / Bytes::BytesLit    — both payloads WERE
                    //       `String`, hashed structurally
                    //
                    // ★★ BOTH of those pairs have since been DISSOLVED, by two
                    // unrelated changes, and the necessity claim above is therefore
                    // NO LONGER what it says. Measured 2026-07-30:
                    //
                    //   * `Str`/`Bytes`: `713e0364` gave `Bytes` a real `Vec<u8>`
                    //     carrier. `Hash for String` writes `(bytes, 0xff)` via
                    //     `write_str`; `Hash for Vec<u8>` writes
                    //     `(write_usize(len), bytes)` via `[T]`. Different streams —
                    //     so the collision is gone WITHOUT the tag, which is why
                    //     `2eebf722` found the five previously-moved goldens passing
                    //     unedited.
                    //   * `Map`/`Pathmap`: #154 (this change) routes the pathmap arm
                    //     through a value closure that writes `PathValue`'s own 1-byte
                    //     tag per entry; the map arm does not. Different streams for
                    //     every NON-EMPTY pathmap.
                    //
                    // ⇒ The residual uncovered case is exactly `{||}` vs `{}`: two
                    // EMPTY containers, both writing `variant_idx == 1` and a zero
                    // length and nothing else. That is a one-pair residue rather than
                    // the eleven-member class the block above describes.
                    //
                    // ⚠ The tag stays DISABLED regardless, and the reason has changed
                    // from "the (a)-vs-(b) semantics ruling is unrecorded" to "it is a
                    // CONSENSUS-VISIBLE change with one known beneficiary". Enabling
                    // it needs an owner and a `docs/consensus/consensus-change-register.md`
                    // entry; it is not #162's or #154's to take unilaterally.
                    //
                    // `semantic_fingerprint` records that stream verbatim, and
                    // the inner-enum discriminant does not help: `CastMap(..)`
                    // and `CastPathmap(..)` are both `Proc` terms, as are
                    // `CastStr(..)` and `CastBytes(..)`.
                    //
                    // ## The design premise this REFUTES
                    //
                    // The #151 design classified this as HARDENING and argued it
                    // was LATENT: "No shipped surface yields both a Map and a
                    // Pathmap reading of the same bytes (`{` opens a map, `{|` a
                    // pathmap) … no reading count in this RED is actually at
                    // risk."
                    //
                    // ⚠ MEASURED FALSE. The premise reasoned about ONE pair and
                    // the class has ELEVEN members. `Str`/`Bytes` IS co-reachable:
                    // a string literal `"a"` is readable as both, and the
                    // collision was silently MERGING the two readings at
                    // realize-time observational dedup. Writing the tag un-merges
                    // them, and the shipped suite moves:
                    //
                    //   languages::rholang_semantic_predicate_ambiguity
                    //     matches_forms_are_unambiguous
                    //       `x matches @"a"!(1)`                     1 → 2
                    //     ppar_forms_are_unambiguous
                    //       `t matches PPar(@"a"!(1), true)`         1 → 2
                    //     implies_forms_are_unambiguous
                    //       `@"OUT"!(true implies false)`            1 → 2
                    //     the_pre_existing_propositional_forms_keep_their_parse_counts
                    //       `for(@x <- @"c" where x > 0) {…}`        1 → 4
                    //   rholang-runtime::rho_rholang_ast
                    //     a_s4_ground_width_fold_value_…_at_comm_time
                    //       "one fold ⇒ one fold-contract spec"      1 → 2
                    //
                    // Controlled: with this `state.write_u64(cat_tag)` line
                    // active all five FAIL; with it commented out all five PASS,
                    // everything else in the workspace unchanged. So the tag is
                    // the sole cause.
                    //
                    // ## Why it is DISABLED rather than landed with re-blessed
                    // ## goldens
                    //
                    // The five goldens could be moved to 2/2/2/4/2 in one line
                    // each. That would be LAUNDERING, because which of two things
                    // happened is not yet established:
                    //
                    //   (a) `"a"` genuinely has both a `Str` and a `Bytes`
                    //       reading, the parser is right to produce both, and the
                    //       goldens were recording an AMBIGUITY HIDDEN BY A HASH
                    //       COLLISION. Then the higher counts are correct and the
                    //       goldens must move.
                    //   (b) the `Bytes` reading is spurious OVER-GENERATION. Then
                    //       the tag merely EXPOSES a different latent defect, the
                    //       real fix is to stop generating that reading, and
                    //       re-blessing the counts would ENSHRINE the
                    //       over-generation in the one set of tests whose whole
                    //       job is to catch reading-count growth.
                    //
                    // Distinguishing (a) from (b) is a user-visible semantics
                    // question — does a Rholang string literal have a `Bytes`
                    // reading? — and it is not this landing's to answer.
                    //
                    // ## Disposition
                    //
                    // The mechanism stays here, complete and one line from
                    // active, per the standing policy that disabled code is
                    // commented out with its reason rather than deleted. It is
                    // NOT a blocker for #151/#74: `PathValue`'s own 1-byte tag
                    // already separates `{|k|}` / `{|k:Nil|}` / `{|k:5|}` and
                    // every NON-EMPTY pathmap from every map, which is what those
                    // two issues require. What remains uncovered is `{||}` vs
                    // `{}` (no value bytes to tag) and the `Str`/`Bytes` pair.
                    //
                    // To re-enable: delete the `_` from `_cat_tag`, uncomment the
                    // `state.write_u64(#cat_tag);` line, and land the five golden
                    // moves WITH the (a)-vs-(b) ruling recorded. ⚠ It is a
                    // CONSENSUS-VISIBLE change — `semantic_fingerprint` feeds the
                    // exact-key / dedup surface — so it also needs an entry in
                    // `docs/consensus/consensus-change-register.md`.
                    let _cat_tag = fnv1a64(&category.to_string());
                    quote! {
                        // state.write_u64(#cat_tag);  // ← see the block above
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
        if field.is_predicate || field.is_collection || field.is_optional || field.is_opaque_leaf()
        {
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
            } else if field.is_optional && (field.is_predicate || field.is_opaque_leaf()) {
                // Task #14 (Option<Guard>): 0/1 discriminant + structural
                // Hash of the inner predicate (no Arc deref — the Option
                // payload is a bare BehavioralPred). Predicates carry no
                // host-term alpha-structure to canonicalize, so structural
                // Hash IS the semantic hash BY CONVENTION (matches the
                // bare-predicate arm below; Eq-consistent).
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__b) => {
                            state.write_u8(1u8);
                            std::hash::Hash::hash(__b, state);
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
            } else if field.is_predicate || field.is_opaque_leaf() {
                // Predicate fields hash inline via standard Hash. L9-3:
                // token-text captures (bare `String`) hash inline identically —
                // a token's text carries no host-term α-structure, so structural
                // Hash IS its semantic hash (Eq-consistent).
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
            } else if field.is_optional && (field.is_predicate || field.is_opaque_leaf()) {
                // Task #14 (Option<Guard>): deferred twin of the eager arm
                // — 0/1 discriminant + structural Hash, no Arc deref.
                final_stmts.push(quote! {
                    match #name.as_ref() {
                        None => state.write_u8(0u8),
                        Some(__b) => {
                            state.write_u8(1u8);
                            std::hash::Hash::hash(__b, state);
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
            } else if field.is_predicate || field.is_opaque_leaf() {
                // L9-3: deferred twin — token-text captures hash inline.
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

#[cfg(test)]
mod task14_tests {
    use super::*;

    #[test]
    fn regular_arm_optional_pred_structural_hash_no_deref() {
        // Task #14 gate-1: pre-#14 the optional arm emitted
        // `(&**__b).semantic_hash(state)` — E0614 on the bare
        // BehavioralPred payload (which has no semantic_hash anyway).
        // Predicates hash structurally (0/1 discriminant + Hash::hash) —
        // structural Hash IS the semantic hash for predicates BY
        // CONVENTION (no host-term alpha-structure; Eq-consistent).
        let language = crate::gen::empty_language_for_tests();
        let cat = format_ident!("Int");
        let label = format_ident!("PCheck");
        let fields = vec![FieldInfo {
            category: format_ident!("Guard"),
            is_collection: false,
            coll_type: None,
            is_predicate: true,
            is_optional: true,
            opaque_leaf: None,
        }];
        let arm =
            generate_semantic_regular_arm(&cat, 3u8, &label, &fields, &HashSet::new(), &language)
                .to_string();
        assert!(
            arm.contains("hash (__b , state)"),
            "the Some arm must hash the bare inner pred structurally: {arm}",
        );
        assert!(
            !arm.contains("* * __b"),
            "no Arc deref exists on an Option<BehavioralPred> payload: {arm}",
        );
        assert!(
            arm.contains("write_u8 (0u8)") && arm.contains("write_u8 (1u8)"),
            "the None/Some discriminant scheme must be kept: {arm}",
        );
    }
}

#[cfg(test)]
mod residual_11_1_send_fold_tests {
    //! Residual #11-1 (A2 codegen unit): the fold-alias polyadic-send map must
    //! emit reconstruction arms for EXACTLY the channel-rewrap SUGARS
    //! (`…Short2Plus`), pairing each to its bare-channel CANONICAL (`…2Plus`),
    //! and NONE for the canonicals / `*Quoted*` / `*Nil*` variants. Verified on
    //! both a rholang-shaped fixture AND a synthetic non-rholang grammar (the
    //! generality-by-structure guarantee).
    use super::*;
    use mettail_ast::grammar::rule_fixture;
    use mettail_ast::types::{EvalMode, RustCodeBlock};
    use proc_macro2::Span;

    fn id(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    fn sp(name: &str, base: &str) -> TermParam {
        TermParam::Simple {
            name: id(name),
            ty: TypeExpr::Base(id(base)),
        }
    }

    fn vp(name: &str, elem: &str) -> TermParam {
        TermParam::Simple {
            name: id(name),
            ty: TypeExpr::Collection {
                coll_type: CollectionType::Vec,
                element: Box::new(TypeExpr::Base(id(elem))),
            },
        }
    }

    fn fold_rule(label: &str, cat: &str, tc: Vec<TermParam>, code: syn::Expr) -> GrammarRule {
        GrammarRule {
            term_context: Some(tc),
            syntax_pattern: Some(Vec::new()),
            rust_code: Some(RustCodeBlock { code }),
            eval_mode: Some(EvalMode::Fold),
            ..rule_fixture(id(label), id(cat))
        }
    }

    /// The seven rholang send-family rules (verbatim bodies).
    fn rholang_send_terms() -> Vec<GrammarRule> {
        vec![
            // Canonicals (bare-param channel `n.clone()`).
            fold_rule(
                "POutput2Plus",
                "Proc",
                vec![sp("n", "Name"), sp("a", "Proc"), vp("bs", "Proc")],
                syn::parse_quote! {{
                    let mut items = Vec::with_capacity(1 + bs.len());
                    items.push(a.clone()); items.extend(bs.clone());
                    Proc::POutput(std::sync::Arc::new(n.clone()),
                        std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)))
                }},
            ),
            fold_rule(
                "PPersistOutput2Plus",
                "Proc",
                vec![sp("n", "Name"), sp("a", "Proc"), vp("bs", "Proc")],
                syn::parse_quote! {{
                    let mut items = Vec::with_capacity(1 + bs.len());
                    items.push(a.clone()); items.extend(bs.clone());
                    Proc::PPersistOutput(std::sync::Arc::new(n.clone()),
                        std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)))
                }},
            ),
            // Excluded: `*Nil*` (channel bottoms at Proc::PZero).
            fold_rule(
                "POutputNil2Plus",
                "Proc",
                vec![sp("a", "Proc"), vp("bs", "Proc")],
                syn::parse_quote! {{
                    let mut items = Vec::with_capacity(1 + bs.len());
                    items.push(a.clone()); items.extend(bs.clone());
                    Proc::POutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                        std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)))
                }},
            ),
            fold_rule(
                "PPersistOutputNil2Plus",
                "Proc",
                vec![sp("a", "Proc"), vp("bs", "Proc")],
                syn::parse_quote! {{
                    let mut items = Vec::with_capacity(1 + bs.len());
                    items.push(a.clone()); items.extend(bs.clone());
                    Proc::PPersistOutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                        std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)))
                }},
            ),
            // Excluded: `*Quoted*` (channel routes through the npt free fn).
            fold_rule(
                "POutputQuoted2Plus",
                "Proc",
                vec![sp("n", "Name"), sp("a", "Proc"), vp("bs", "Proc")],
                syn::parse_quote! {{
                    let mut items = Vec::with_capacity(1 + bs.len());
                    items.push(a.clone()); items.extend(bs.clone());
                    Proc::POutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(
                        crate::rholang::receive::name_pattern_to_proc(&n)))),
                        std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)))
                }},
            ),
            // Sugars (channel-rewrap `NQuote(p)`) — the ONLY two folded.
            fold_rule(
                "POutputShort2Plus",
                "Proc",
                vec![sp("p", "Proc"), sp("a", "Proc"), vp("bs", "Proc")],
                syn::parse_quote! {{
                    let mut items = Vec::with_capacity(1 + bs.len());
                    items.push(a.clone()); items.extend(bs.clone());
                    Proc::POutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                        std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)))
                }},
            ),
            fold_rule(
                "PPersistOutputShort2Plus",
                "Proc",
                vec![sp("p", "Proc"), sp("a", "Proc"), vp("bs", "Proc")],
                syn::parse_quote! {{
                    let mut items = Vec::with_capacity(1 + bs.len());
                    items.push(a.clone()); items.extend(bs.clone());
                    Proc::PPersistOutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                        std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)))
                }},
            ),
        ]
    }

    fn lang_with(terms: Vec<GrammarRule>) -> LanguageDef {
        let mut l = crate::gen::empty_language_for_tests();
        l.terms = terms;
        l
    }

    #[test]
    fn a2_send_map_fires_for_exactly_the_two_short_sugars() {
        let language = lang_with(rholang_send_terms());
        let map = build_fold_alias_send_map(&language);

        let mut keys: Vec<String> = map.keys().cloned().collect();
        keys.sort();
        assert_eq!(
            keys,
            vec!["POutputShort2Plus".to_string(), "PPersistOutputShort2Plus".to_string()],
            "send-fold arms must be emitted for EXACTLY the two channel-rewrap sugars",
        );

        // A1c: canonicals + `*Quoted*` + `*Nil*` are NEVER folded (structural).
        for excluded in [
            "POutput2Plus",
            "PPersistOutput2Plus",
            "POutputNil2Plus",
            "PPersistOutputNil2Plus",
            "POutputQuoted2Plus",
        ] {
            assert!(!map.contains_key(excluded), "{excluded} must stay structural (no fold arm)");
        }
    }

    #[test]
    fn a2_sugars_pair_to_the_matching_scalar_target_canonical() {
        let language = lang_with(rholang_send_terms());
        let map = build_fold_alias_send_map(&language);
        assert_eq!(
            map["POutputShort2Plus"].poly_canon_label.to_string(),
            "POutput2Plus",
            "the `!` sugar reconstructs the `POutput` canonical",
        );
        assert_eq!(
            map["PPersistOutputShort2Plus"].poly_canon_label.to_string(),
            "PPersistOutput2Plus",
            "the `!!` sugar reconstructs the PERSIST canonical (send/persist boundary held)",
        );
    }

    #[test]
    fn a2_generated_arm_reconstructs_canonical_2plus_with_nquote_channel() {
        let language = lang_with(rholang_send_terms());
        let map = build_fold_alias_send_map(&language);
        let arm = &map["POutputShort2Plus"];
        let ts =
            generate_fold_alias_send_arm(&id("Proc"), &id("POutputShort2Plus"), arm).to_string();
        // Reconstruction root is the polyadic canonical (NOT the scalar POutput),
        // with the grammar-lifted NQuote channel and the trailing Vec passed
        // through unpacked.
        assert!(ts.contains("Proc :: POutput2Plus"), "reconstructs the polyadic canonical: {ts}");
        assert!(ts.contains("NQuote"), "channel rewrap lifted from the body: {ts}");
        assert!(
            ts.contains("semantic_hash"),
            "recurses semantic_hash on the reconstruction: {ts}"
        );
        // The `bs` Vec rest is cloned through (NOT mk_proc_list-packed) so the
        // reconstruction matches POutput2Plus's (chan, first, rest-Vec) split.
        assert!(!ts.contains("mk_proc_list"), "operands must NOT be scalar list-packed: {ts}");
    }

    /// ★ Generality (macros level): a SYNTHETIC non-rholang grammar with the same
    /// send shape yields the fold arm too, pairing the sugar to its own bare
    /// canonical — proving the pass keys on structure, not names.
    #[test]
    fn generality_synthetic_language_send_fold() {
        let terms = vec![
            fold_rule(
                "EmitMulti",
                "Widget",
                vec![sp("n", "Chan"), sp("x", "Widget"), vp("xs", "Widget")],
                syn::parse_quote! {{
                    let mut acc = Vec::with_capacity(1 + xs.len());
                    acc.push(x.clone()); acc.extend(xs.clone());
                    Widget::Emit(std::sync::Arc::new(n.clone()),
                        std::sync::Arc::new(some_crate::mk_widget_list(acc)))
                }},
            ),
            fold_rule(
                "WrapSend",
                "Widget",
                vec![sp("w", "Widget"), sp("x", "Widget"), vp("xs", "Widget")],
                syn::parse_quote! {{
                    let mut acc = Vec::with_capacity(1 + xs.len());
                    acc.push(x.clone()); acc.extend(xs.clone());
                    Widget::Emit(std::sync::Arc::new(Chan::Wrap(std::sync::Arc::new(w.clone()))),
                        std::sync::Arc::new(some_crate::mk_widget_list(acc)))
                }},
            ),
        ];
        let language = lang_with(terms);
        let map = build_fold_alias_send_map(&language);
        let keys: Vec<String> = map.keys().cloned().collect();
        assert_eq!(keys, vec!["WrapSend".to_string()], "only the synthetic sugar folds");
        assert_eq!(map["WrapSend"].poly_canon_label.to_string(), "EmitMulti");
        let ts = generate_fold_alias_send_arm(&id("Widget"), &id("WrapSend"), &map["WrapSend"])
            .to_string();
        assert!(ts.contains("Widget :: EmitMulti"), "reconstructs the synthetic canonical: {ts}");
        assert!(ts.contains("Chan :: Wrap"), "lifts the synthetic channel wrap: {ts}");
    }
}
