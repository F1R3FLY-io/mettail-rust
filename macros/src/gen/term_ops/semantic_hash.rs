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
//! 2. Every category child, including children inside ordered and unordered
//!    collections, is pushed onto the same explicit work stack.
//! 3. Unordered containers suspend a resumable runtime PDA while each element
//!    writes into a stable boxed `FxHasher`; no callback re-enters the public
//!    method.
//! 4. Fold-alias reconstructions are owned by explicit keep-alive tasks until
//!    their canonical subtree has been consumed.
//! 5. `try_with` gracefully degrades to a local stack during thread shutdown.
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
use crate::gen::term_ops::collection_walk::{field_carrier, FieldCarrier};
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

/// Exact inventory of optional task shapes needed by one generated language.
/// Keeping this census beside the generator prevents a collection-free or
/// fold-free grammar from paying in emitted code or `SemanticHashTask` size for
/// machinery it cannot reach.
#[derive(Default)]
struct SemanticTaskUsage {
    unordered_element_categories: HashSet<String>,
    needs_opaque: bool,
    needs_keep_alive: bool,
}

impl SemanticTaskUsage {
    fn record_collection(&mut self, element_cat: &Ident, coll_type: &CollectionType) {
        if matches!(
            coll_type,
            CollectionType::HashSet
                | CollectionType::HashBag
                | CollectionType::HashMap
                | CollectionType::PathMap
        ) {
            self.unordered_element_categories
                .insert(element_cat.to_string());
        }
    }

    fn record_field(&mut self, field: &FieldInfo) {
        match field_carrier(field) {
            FieldCarrier::Leaf => self.needs_opaque = true,
            FieldCarrier::Collection { coll_type }
            | FieldCarrier::OptionalCollection { coll_type } => {
                self.record_collection(&field.category, &coll_type);
            },
            FieldCarrier::Child | FieldCarrier::OptionalChild => {},
        }
    }
}

fn semantic_task_usage(language: &LanguageDef, needs_keep_alive: bool) -> SemanticTaskUsage {
    let mut usage = SemanticTaskUsage {
        needs_keep_alive,
        ..SemanticTaskUsage::default()
    };

    for lang_type in &language.types {
        for variant in collect_category_variants(&lang_type.name, language) {
            match variant {
                VariantKind::CollectionLiteral { element_cat, coll_type, .. }
                | VariantKind::Collection { element_cat, coll_type, .. } => {
                    usage.record_collection(&element_cat, &coll_type);
                },
                VariantKind::RecursiveNativeLiteral { carrier, .. } => {
                    usage.record_collection(carrier.key_category(), &CollectionType::PathMap);
                    usage.record_collection(carrier.value_category(), &CollectionType::PathMap);
                    usage.needs_opaque = true;
                },
                VariantKind::Regular { fields, .. } => {
                    for field in &fields {
                        usage.record_field(field);
                    }
                },
                VariantKind::Binder { pre_scope_fields, .. }
                | VariantKind::MultiBinder { pre_scope_fields, .. } => {
                    for field in &pre_scope_fields {
                        usage.record_field(field);
                    }
                },
                VariantKind::Refused { .. }
                | VariantKind::Nullary { .. }
                | VariantKind::Literal { .. }
                | VariantKind::Var { .. } => {},
            }
        }
    }

    usage
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
    let task_variant = format_ident!("SemHash{}", category);
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
            let (__keep_alive, __canonical_ptr) = semantic_hash_keep_alive(__canonical);
            stack.push(__keep_alive);
            stack.push(SemanticHashTask::#task_variant {
                value: __canonical_ptr,
                target,
                cacheable: false,
            });
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

    let usage = semantic_task_usage(
        language,
        !fold_alias_map.is_empty() || !fold_alias_send_map.is_empty(),
    );

    let task_enum = generate_semantic_task_enum(language, &usage);
    let engine = generate_semantic_engine(
        language,
        &transparent_labels,
        &fold_alias_map,
        &fold_alias_send_map,
        &usage,
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

fn generate_semantic_sink_support() -> TokenStream {
    quote! {
        trait __MettailSemanticSink: std::hash::Hasher {
            const COMPOSES_KEYS: bool;

            fn max_key_bytes(&self) -> usize {
                usize::MAX
            }

            fn record_key_error(
                &mut self,
                _error: mettail_runtime::exact_semantic_key::ContentKeyCacheError,
            ) {
            }

            fn write_exact_key(
                &mut self,
                key: mettail_runtime::exact_semantic_key::ContentKey,
            ) {
                self.write(key.as_bytes());
            }

            fn begin_node(
                &mut self,
                _identity: mettail_runtime::exact_semantic_key::ContentKeyNodeIdentity,
                _cacheable: bool,
            ) -> bool {
                false
            }

            fn finish_node(
                &mut self,
                _identity: mettail_runtime::exact_semantic_key::ContentKeyNodeIdentity,
                _cacheable: bool,
            ) {
            }
        }

        struct __MettailFlatSemanticSink<'a, H>(&'a mut H);

        impl<H: std::hash::Hasher> std::hash::Hasher for __MettailFlatSemanticSink<'_, H> {
            fn finish(&self) -> u64 {
                self.0.finish()
            }
            fn write(&mut self, bytes: &[u8]) {
                self.0.write(bytes);
            }
            fn write_u8(&mut self, value: u8) {
                self.0.write_u8(value);
            }
            fn write_u16(&mut self, value: u16) {
                self.0.write_u16(value);
            }
            fn write_u32(&mut self, value: u32) {
                self.0.write_u32(value);
            }
            fn write_u64(&mut self, value: u64) {
                self.0.write_u64(value);
            }
            fn write_u128(&mut self, value: u128) {
                self.0.write_u128(value);
            }
            fn write_usize(&mut self, value: usize) {
                self.0.write_usize(value);
            }
            fn write_i8(&mut self, value: i8) {
                self.0.write_i8(value);
            }
            fn write_i16(&mut self, value: i16) {
                self.0.write_i16(value);
            }
            fn write_i32(&mut self, value: i32) {
                self.0.write_i32(value);
            }
            fn write_i64(&mut self, value: i64) {
                self.0.write_i64(value);
            }
            fn write_i128(&mut self, value: i128) {
                self.0.write_i128(value);
            }
            fn write_isize(&mut self, value: isize) {
                self.0.write_isize(value);
            }
        }

        impl<H: std::hash::Hasher> __MettailSemanticSink
            for __MettailFlatSemanticSink<'_, H>
        {
            const COMPOSES_KEYS: bool = false;
        }

        impl __MettailSemanticSink
            for mettail_runtime::exact_semantic_key::SemanticKeyBuilder
        {
            const COMPOSES_KEYS: bool = true;

            fn max_key_bytes(&self) -> usize {
                mettail_runtime::exact_semantic_key::SemanticKeyBuilder::max_key_bytes(self)
            }

            fn write_exact_key(
                &mut self,
                key: mettail_runtime::exact_semantic_key::ContentKey,
            ) {
                self.push_framed_key(key);
            }
        }

        struct __MettailComposingSemanticSink<'transaction, 'cache> {
            transaction:
                &'transaction mut mettail_runtime::exact_semantic_key::ContentKeyCacheTransaction<'cache>,
            frames: Vec<mettail_runtime::exact_semantic_key::SemanticKeyBuilder>,
            orphan: mettail_runtime::exact_semantic_key::SemanticKeyBuilder,
            root: Option<mettail_runtime::exact_semantic_key::ContentKey>,
            error: Option<mettail_runtime::exact_semantic_key::ContentKeyCacheError>,
        }

        impl<'transaction, 'cache> __MettailComposingSemanticSink<'transaction, 'cache> {
            fn new(
                transaction:
                    &'transaction mut mettail_runtime::exact_semantic_key::ContentKeyCacheTransaction<'cache>,
            ) -> Self {
                let max_key_bytes = transaction.max_key_bytes();
                Self {
                    transaction,
                    frames: Vec::new(),
                    orphan: mettail_runtime::exact_semantic_key::SemanticKeyBuilder::with_max_bytes(
                        max_key_bytes,
                    ),
                    root: None,
                    error: None,
                }
            }

            fn current(&mut self) -> &mut mettail_runtime::exact_semantic_key::SemanticKeyBuilder {
                let Some(current) = self.frames.last_mut() else {
                    self.error.get_or_insert(
                        mettail_runtime::exact_semantic_key::ContentKeyCacheError::ConstructionInvariant,
                    );
                    return &mut self.orphan;
                };
                current
            }

            fn append_key(&mut self, key: mettail_runtime::exact_semantic_key::ContentKey) {
                if let Some(parent) = self.frames.last_mut() {
                    parent.push_key(key);
                } else if self.root.is_none() {
                    self.root = Some(key);
                } else {
                    self.error.get_or_insert(
                        mettail_runtime::exact_semantic_key::ContentKeyCacheError::ConstructionInvariant,
                    );
                }
            }

            fn into_result(
                mut self,
            ) -> Result<
                mettail_runtime::exact_semantic_key::ContentKey,
                mettail_runtime::exact_semantic_key::ContentKeyCacheError,
            > {
                if !self.frames.is_empty() {
                    return Err(
                        mettail_runtime::exact_semantic_key::ContentKeyCacheError::ConstructionInvariant,
                    );
                }
                if let Some(error) = self.error.take() {
                    return Err(error);
                }
                self.root.take().ok_or(
                    mettail_runtime::exact_semantic_key::ContentKeyCacheError::ConstructionInvariant,
                )
            }
        }

        impl std::hash::Hasher for __MettailComposingSemanticSink<'_, '_> {
            fn finish(&self) -> u64 {
                self.frames.last().map_or(0, std::hash::Hasher::finish)
            }
            fn write(&mut self, bytes: &[u8]) {
                self.current().write(bytes);
            }
            fn write_u8(&mut self, value: u8) {
                self.current().write_u8(value);
            }
            fn write_u16(&mut self, value: u16) {
                self.current().write_u16(value);
            }
            fn write_u32(&mut self, value: u32) {
                self.current().write_u32(value);
            }
            fn write_u64(&mut self, value: u64) {
                self.current().write_u64(value);
            }
            fn write_u128(&mut self, value: u128) {
                self.current().write_u128(value);
            }
            fn write_usize(&mut self, value: usize) {
                self.current().write_usize(value);
            }
            fn write_i8(&mut self, value: i8) {
                self.current().write_i8(value);
            }
            fn write_i16(&mut self, value: i16) {
                self.current().write_i16(value);
            }
            fn write_i32(&mut self, value: i32) {
                self.current().write_i32(value);
            }
            fn write_i64(&mut self, value: i64) {
                self.current().write_i64(value);
            }
            fn write_i128(&mut self, value: i128) {
                self.current().write_i128(value);
            }
            fn write_isize(&mut self, value: isize) {
                self.current().write_isize(value);
            }
        }

        impl __MettailSemanticSink for __MettailComposingSemanticSink<'_, '_> {
            const COMPOSES_KEYS: bool = true;

            fn max_key_bytes(&self) -> usize {
                self.transaction.max_key_bytes()
            }

            fn record_key_error(
                &mut self,
                error: mettail_runtime::exact_semantic_key::ContentKeyCacheError,
            ) {
                self.error.get_or_insert(error);
            }

            fn write_exact_key(
                &mut self,
                key: mettail_runtime::exact_semantic_key::ContentKey,
            ) {
                self.current().push_framed_key(key);
            }

            fn begin_node(
                &mut self,
                identity: mettail_runtime::exact_semantic_key::ContentKeyNodeIdentity,
                cacheable: bool,
            ) -> bool {
                if cacheable {
                    if let Some(key) = self.transaction.get_identity(identity) {
                        self.append_key(key);
                        return true;
                    }
                }
                self.frames.push(
                    mettail_runtime::exact_semantic_key::SemanticKeyBuilder::with_max_bytes(
                        self.transaction.max_key_bytes(),
                    ),
                );
                false
            }

            fn finish_node(
                &mut self,
                identity: mettail_runtime::exact_semantic_key::ContentKeyNodeIdentity,
                cacheable: bool,
            ) {
                let Some(frame) = self.frames.pop() else {
                    self.error.get_or_insert(
                        mettail_runtime::exact_semantic_key::ContentKeyCacheError::ConstructionInvariant,
                    );
                    return;
                };
                let mut key = match frame.into_key() {
                    Ok(key) => key,
                    Err(error) => {
                        self.error.get_or_insert(error);
                        return;
                    },
                };
                if cacheable {
                    // SAFETY: generated tasks mark only nodes transitively
                    // owned by the transaction's retained immutable AST root.
                    match unsafe {
                        self.transaction.stage_identity(identity, key.clone())
                    } {
                        Ok(shared) => key = shared,
                        Err(error) => {
                            self.error.get_or_insert(error);
                        },
                    }
                }
                self.append_key(key);
            }
        }
    }
}

fn generate_semantic_task_enum(language: &LanguageDef, usage: &SemanticTaskUsage) -> TokenStream {
    let sink_support = generate_semantic_sink_support();
    let scratch_target = (!usage.unordered_element_categories.is_empty()).then(|| {
        quote! {
            Scratch(*mut mettail_runtime::CollectionSemanticHasher),
        }
    });
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("SemHash{}", cat);
            quote! {
                #variant_name {
                    value: *const #cat,
                    target: SemanticHashTarget,
                    cacheable: bool,
                }
            }
        })
        .collect();
    let resume_collection_variant = (!usage.unordered_element_categories.is_empty()).then(|| {
        quote! {
            ResumeCollection {
                pda: Box<mettail_runtime::CollectionSemanticHashPda>,
                target: SemanticHashTarget,
                schedule: SemanticHashCollectionSchedule,
            },
        }
    });
    let collection_schedule_alias = (!usage.unordered_element_categories.is_empty()).then(|| {
        quote! {
            type SemanticHashCollectionSchedule = fn(
                &mut Vec<SemanticHashTask>,
                mettail_runtime::CollectionSemanticHashRole,
                *const (),
                SemanticHashTarget,
            );
        }
    });

    let opaque_variant = usage.needs_opaque.then(|| {
        quote! {
            Opaque {
                value: *const (),
                hash: unsafe fn(*const (), *mut ()),
                target: SemanticHashTarget,
            },
        }
    });
    let keep_alive_variant = usage.needs_keep_alive.then(|| {
        quote! {
            KeepAlive {
                value: *mut (),
                drop_value: unsafe fn(*mut ()),
            },
        }
    });
    let opaque_helper = usage.needs_opaque.then(|| {
        quote! {
            #[inline]
            fn semantic_hash_opaque_task<T, S>(
                value: &T,
                target: SemanticHashTarget,
            ) -> SemanticHashTask
            where
                T: std::hash::Hash,
                S: std::hash::Hasher,
            {
                unsafe fn apply<T, S>(value: *const (), state: *mut ())
                where
                    T: std::hash::Hash,
                    S: std::hash::Hasher,
                {
                    let value = unsafe { &*value.cast::<T>() };
                    let state = unsafe { &mut *state.cast::<S>() };
                    std::hash::Hash::hash(value, state);
                }

                SemanticHashTask::Opaque {
                    value: value as *const T as *const (),
                    hash: apply::<T, S>,
                    target,
                }
            }
        }
    });
    let keep_alive_helper = usage.needs_keep_alive.then(|| {
        quote! {
            #[inline]
            fn semantic_hash_keep_alive<T>(value: T) -> (SemanticHashTask, *const T) {
                unsafe fn drop_value<T>(value: *mut ()) {
                    drop(unsafe { Box::from_raw(value.cast::<T>()) });
                }

                let value = Box::into_raw(Box::new(value));
                (
                    SemanticHashTask::KeepAlive {
                        value: value.cast::<()>(),
                        drop_value: drop_value::<T>,
                    },
                    value,
                )
            }
        }
    });

    quote! {
        #sink_support

        #[derive(Clone, Copy)]
        enum SemanticHashTarget {
            Root,
            #scratch_target
        }

        #collection_schedule_alias

        /// Work item for the iterative semantic_hash engine (Stage 2.3).
        ///
        /// Each variant wraps a raw pointer to a value of one category.
        /// The engine pops tasks, conditionally emits variant
        /// discriminants (skipped for transparent wrappers), and pushes
        /// child tasks for `Box<T>` fields.
        #[allow(dead_code)]
        enum SemanticHashTask {
            #(#variants,)*
            #resume_collection_variant
            /// ★ #162 — a `usize` written to `state` at its own position in the
            /// stream, so a collection's LENGTH PREFIX can precede element tasks.
            ///
            /// Without it the `Vec` arm had to write the prefix and then call
            /// `Elem::semantic_hash(e, state)` per element — a whole-value
            /// re-entry, Θ(depth). Measured 4,096 B/level (debug) the moment #154
            /// routed the collection-literal arm here from structural `Hash`.
            AbsorbUsize {
                value: usize,
                target: SemanticHashTarget,
            },
            AbsorbU8 {
                value: u8,
                target: SemanticHashTarget,
            },
            #opaque_variant
            #keep_alive_variant
            FinishNode {
                identity: mettail_runtime::exact_semantic_key::ContentKeyNodeIdentity,
                cacheable: bool,
            },
        }

        #opaque_helper
        #keep_alive_helper

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

fn recursive_native_semantic_schedule_name(category: &Ident, label: &Ident) -> Ident {
    format_ident!(
        "semantic_hash_schedule_native_{}_{}",
        category.to_string().to_lowercase(),
        label.to_string().to_lowercase(),
    )
}

fn generate_semantic_engine(
    language: &LanguageDef,
    transparent_labels: &HashSet<String>,
    fold_alias_map: &HashMap<String, FoldAliasArm>,
    fold_alias_send_map: &HashMap<String, FoldAliasSendArm>,
    usage: &SemanticTaskUsage,
) -> TokenStream {
    let has_scratch_target = !usage.unordered_element_categories.is_empty();
    let homogeneous_schedule_fns: Vec<TokenStream> = language
        .types
        .iter()
        .filter(|t| {
            usage
                .unordered_element_categories
                .contains(&t.name.to_string())
        })
        .map(|t| {
            let category = &t.name;
            let task_variant = format_ident!("SemHash{}", category);
            let schedule_fn = format_ident!(
                "semantic_hash_schedule_collection_{}",
                category.to_string().to_lowercase(),
            );
            quote! {
                #[inline]
                fn #schedule_fn(
                    stack: &mut Vec<SemanticHashTask>,
                    _role: mettail_runtime::CollectionSemanticHashRole,
                    value: *const (),
                    target: SemanticHashTarget,
                ) {
                    stack.push(SemanticHashTask::#task_variant {
                        value: value.cast::<#category>(),
                        target,
                        cacheable: false,
                    });
                }
            }
        })
        .collect();
    let native_schedule_fns: Vec<TokenStream> = language
        .types
        .iter()
        .flat_map(|t| {
            let category = &t.name;
            collect_category_variants(category, language)
                .into_iter()
                .filter_map(move |variant| match variant {
                    VariantKind::RecursiveNativeLiteral { label, carrier } => {
                        let schedule_fn = recursive_native_semantic_schedule_name(category, &label);
                        let key_task = format_ident!("SemHash{}", carrier.key_category());
                        let value_task = format_ident!("SemHash{}", carrier.value_category());
                        let key_category = carrier.key_category();
                        let value_category = carrier.value_category();
                        Some(quote! {
                            #[inline]
                            fn #schedule_fn(
                                stack: &mut Vec<SemanticHashTask>,
                                role: mettail_runtime::CollectionSemanticHashRole,
                                value: *const (),
                                target: SemanticHashTarget,
                            ) {
                                match role {
                                    mettail_runtime::CollectionSemanticHashRole::Primary => {
                                        stack.push(SemanticHashTask::#key_task {
                                            value: value.cast::<#key_category>(),
                                            target,
                                            cacheable: false,
                                        });
                                    },
                                    mettail_runtime::CollectionSemanticHashRole::Secondary => {
                                        stack.push(SemanticHashTask::#value_task {
                                            value: value.cast::<#value_category>(),
                                            target,
                                            cacheable: false,
                                        });
                                    },
                                }
                            }
                        })
                    },
                    _ => None,
                })
        })
        .collect();
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
            let visit_fn = format_ident!("semantic_hash_visit_{}", cat_str);
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
            let root_dispatch = quote! {
                if H::COMPOSES_KEYS {
                    let identity =
                        mettail_runtime::exact_semantic_key::ContentKeyNodeIdentity::of_ref(unsafe { &*ptr });
                    if root_state.begin_node(identity, cacheable) {
                        return;
                    }
                    stack.push(SemanticHashTask::FinishNode {
                        identity,
                        cacheable,
                    });
                }
                #visit_fn(stack, root_state, target, ptr, cacheable);
            };
            let dispatch = if has_scratch_target {
                quote! {
                    match target {
                        SemanticHashTarget::Root => {
                            #root_dispatch
                        },
                        SemanticHashTarget::Scratch(state) => {
                            #visit_fn(stack, unsafe { &mut *state }, target, ptr, false);
                        },
                    }
                }
            } else {
                quote! {
                    #root_dispatch
                }
            };
            quote! {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn #visit_fn<S: __MettailSemanticSink>(
                    stack: &mut Vec<SemanticHashTask>,
                    state: &mut S,
                    target: SemanticHashTarget,
                    ptr: *const #cat,
                    cacheable: bool,
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

                #[inline(never)]
                #[allow(dead_code)]
                fn #helper_fn<H: __MettailSemanticSink>(
                    stack: &mut Vec<SemanticHashTask>,
                    root_state: &mut H,
                    target: SemanticHashTarget,
                    ptr: *const #cat,
                    cacheable: bool,
                ) {
                    #dispatch
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
                SemanticHashTask::#task_variant {
                    value,
                    target,
                    cacheable,
                } => {
                    #helper_fn(stack, state, target, value, cacheable);
                }
            }
        })
        .collect();

    let opaque_scratch_arm = has_scratch_target.then(|| {
        quote! {
            SemanticHashTarget::Scratch(state) => unsafe {
                hash(value, state.cast::<()>());
            },
        }
    });
    let opaque_apply_helper = usage.needs_opaque.then(|| {
        quote! {
            #[inline]
            unsafe fn semantic_hash_apply_opaque<H: std::hash::Hasher>(
                root_state: &mut H,
                target: SemanticHashTarget,
                value: *const (),
                hash: unsafe fn(*const (), *mut ()),
            ) {
                match target {
                    SemanticHashTarget::Root => unsafe {
                        hash(value, root_state as *mut H as *mut ());
                    },
                    #opaque_scratch_arm
                }
            }
        }
    });
    let opaque_task_arm = usage.needs_opaque.then(|| {
        quote! {
            SemanticHashTask::Opaque { value, hash, target } => unsafe {
                semantic_hash_apply_opaque(state, target, value, hash);
            },
        }
    });
    let keep_alive_task_arm = usage.needs_keep_alive.then(|| {
        quote! {
            SemanticHashTask::KeepAlive { value, drop_value } => unsafe {
                drop_value(value);
            },
        }
    });
    let scratch_hash_arm = has_scratch_target.then(|| {
        quote! {
            SemanticHashTarget::Scratch(state) => {
                std::hash::Hash::hash(&value, unsafe { &mut *state });
            },
        }
    });
    let write_key_helper = has_scratch_target.then(|| {
        quote! {
            #[inline]
            fn semantic_hash_write_key<H: __MettailSemanticSink>(
                root_state: &mut H,
                target: SemanticHashTarget,
                key: mettail_runtime::exact_semantic_key::ContentKey,
            ) {
                match target {
                    SemanticHashTarget::Root => root_state.write_exact_key(key),
                    SemanticHashTarget::Scratch(state) => {
                        unsafe { &mut *state }.push_framed_key(key);
                    },
                }
            }
        }
    });
    let resume_collection_helper = has_scratch_target.then(|| {
        quote! {
            #[inline(never)]
            fn semantic_hash_resume_collection<H: __MettailSemanticSink>(
                stack: &mut Vec<SemanticHashTask>,
                root_state: &mut H,
                mut pda: Box<mettail_runtime::CollectionSemanticHashPda>,
                target: SemanticHashTarget,
                schedule: SemanticHashCollectionSchedule,
            ) {
                loop {
                    match pda.resume() {
                        mettail_runtime::CollectionSemanticHashStep::Hash {
                            role,
                            value,
                            state,
                        } => {
                            stack.push(SemanticHashTask::ResumeCollection {
                                pda,
                                target,
                                schedule,
                            });
                            schedule(
                                stack,
                                role,
                                value,
                                SemanticHashTarget::Scratch(state),
                            );
                            return;
                        },
                        mettail_runtime::CollectionSemanticHashStep::WriteUsize(value) => {
                            semantic_hash_write_usize(root_state, target, value);
                        },
                        mettail_runtime::CollectionSemanticHashStep::WriteU8(value) => {
                            semantic_hash_write_u8(root_state, target, value);
                        },
                        mettail_runtime::CollectionSemanticHashStep::WriteKey(key) => {
                            semantic_hash_write_key(root_state, target, key);
                        },
                        mettail_runtime::CollectionSemanticHashStep::Error(error) => {
                            root_state.record_key_error(error);
                            return;
                        },
                        mettail_runtime::CollectionSemanticHashStep::Done => return,
                    }
                }
            }
        }
    });
    let resume_collection_task_arm = has_scratch_target.then(|| {
        quote! {
            SemanticHashTask::ResumeCollection { pda, target, schedule } => {
                semantic_hash_resume_collection(stack, state, pda, target, schedule);
            },
        }
    });

    quote! {
        #(#homogeneous_schedule_fns)*
        #(#native_schedule_fns)*
        #(#helper_fns)*

        #[inline]
        fn semantic_hash_write_usize<H: std::hash::Hasher>(
            root_state: &mut H,
            target: SemanticHashTarget,
            value: usize,
        ) {
            match target {
                SemanticHashTarget::Root => std::hash::Hash::hash(&value, root_state),
                #scratch_hash_arm
            }
        }

        #[inline]
        fn semantic_hash_write_u8<H: std::hash::Hasher>(
            root_state: &mut H,
            target: SemanticHashTarget,
            value: u8,
        ) {
            match target {
                SemanticHashTarget::Root => std::hash::Hash::hash(&value, root_state),
                #scratch_hash_arm
            }
        }

        #write_key_helper
        #resume_collection_helper

        #opaque_apply_helper

        /// Iterative semantic_hash engine. Processes the work stack
        /// until empty, hashing each node's fields into `state`.
        #[allow(dead_code, unused_variables)]
        fn semantic_hash_iterative<H: __MettailSemanticSink>(
            stack: &mut Vec<SemanticHashTask>,
            state: &mut H,
        ) {
            while let Some(task) = stack.pop() {
                match task {
                    #(#task_arms)*
                    #resume_collection_task_arm
                    // ★ #162 — `state.write_usize(n)`, the exact call the eager
                    // form made, issued at its own position in the stream.
                    SemanticHashTask::AbsorbUsize { value, target } => {
                        semantic_hash_write_usize(state, target, value);
                    }
                    SemanticHashTask::AbsorbU8 { value, target } => {
                        semantic_hash_write_u8(state, target, value);
                    }
                    #opaque_task_arm
                    #keep_alive_task_arm
                    SemanticHashTask::FinishNode {
                        identity,
                        cacheable,
                    } => state.finish_node(identity, cacheable),
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
/// - `HashBag`: exact sorted element-key/multiplicity pairs.
/// - `HashMap`: exact sorted key/value pairs with preserved pair boundaries.
/// - `HashSet`: exact sorted element keys.
/// - `PathMap`: an explicit Empty/Set/Map mode and mode-correct exact entries.
///
/// `coll_expr` borrows the collection; `element_cat` is its element category.
fn semantic_hash_collection(
    coll_expr: &TokenStream,
    element_cat: &Ident,
    coll_type: &CollectionType,
) -> TokenStream {
    let task_variant = format_ident!("SemHash{}", element_cat);
    let schedule_fn = format_ident!(
        "semantic_hash_schedule_collection_{}",
        element_cat.to_string().to_lowercase(),
    );
    match coll_type {
        CollectionType::Vec => {
            quote! {
                for __e in #coll_expr.iter().rev() {
                    stack.push(SemanticHashTask::#task_variant {
                        value: __e as *const _,
                        target,
                        cacheable,
                    });
                }
                stack.push(SemanticHashTask::AbsorbUsize {
                    value: #coll_expr.len(),
                    target,
                });
            }
        },
        CollectionType::HashSet => quote! {
            {
                let __items = #coll_expr
                    .iter()
                    .map(mettail_runtime::CollectionSemanticHashItem::unary)
                    .collect();
                stack.push(SemanticHashTask::ResumeCollection {
                    pda: Box::new(
                        mettail_runtime::CollectionSemanticHashPda::set_with_max_bytes(
                            __items,
                            state.max_key_bytes(),
                        ),
                    ),
                    target,
                    schedule: #schedule_fn,
                });
            }
        },
        CollectionType::HashBag => quote! {
            {
                let __items = #coll_expr
                    .iter()
                    .map(|(__value, __count)| {
                        mettail_runtime::CollectionSemanticHashItem::repeated(
                            __value,
                            __count,
                        )
                    })
                    .collect();
                stack.push(SemanticHashTask::ResumeCollection {
                    pda: Box::new(mettail_runtime::CollectionSemanticHashPda::bag_with_max_bytes(
                        #coll_expr.len(),
                        __items,
                        state.max_key_bytes(),
                    )),
                    target,
                    schedule: #schedule_fn,
                });
            }
        },
        CollectionType::HashMap => quote! {
            {
                let __items = #coll_expr
                    .iter()
                    .map(|(__key, __value)| {
                        mettail_runtime::CollectionSemanticHashItem::pair(__key, __value)
                    })
                    .collect();
                stack.push(SemanticHashTask::ResumeCollection {
                    pda: Box::new(
                        mettail_runtime::CollectionSemanticHashPda::map_with_max_bytes(
                            __items,
                            state.max_key_bytes(),
                        ),
                    ),
                    target,
                    schedule: #schedule_fn,
                });
            }
        },
        CollectionType::PathMap => semantic_hash_pathmap(coll_expr, &quote! { #schedule_fn }),
    }
}

/// Schedule the exact semantic-hash stream of a PathMap through a supplied
/// typed callback.  The callback may be homogeneous or may route primary keys
/// and secondary values to distinct generated categories.
fn semantic_hash_pathmap(pathmap: &TokenStream, schedule: &TokenStream) -> TokenStream {
    quote! {
        {
            match #pathmap {
                mettail_runtime::PathMapLit::Empty => {
                    stack.push(SemanticHashTask::ResumeCollection {
                        pda: Box::new(
                            mettail_runtime::CollectionSemanticHashPda::path_neutral_with_max_bytes(
                                state.max_key_bytes(),
                            ),
                        ),
                        target,
                        schedule: #schedule,
                    });
                },
                mettail_runtime::PathMapLit::Set(__entries) => {
                    let __items = __entries
                        .keys()
                        .map(mettail_runtime::CollectionSemanticHashItem::key_only)
                        .collect();
                    stack.push(SemanticHashTask::ResumeCollection {
                        pda: Box::new(
                            mettail_runtime::CollectionSemanticHashPda::path_set_with_max_bytes(
                                __items,
                                state.max_key_bytes(),
                            ),
                        ),
                        target,
                        schedule: #schedule,
                    });
                },
                mettail_runtime::PathMapLit::Map(__entries) => {
                    let __items = __entries
                        .iter()
                        .map(|(__key, __value)| {
                            mettail_runtime::CollectionSemanticHashItem::pair(
                                __key,
                                __value,
                            )
                        })
                        .collect();
                    stack.push(SemanticHashTask::ResumeCollection {
                        pda: Box::new(
                            mettail_runtime::CollectionSemanticHashPda::path_map_with_max_bytes(
                                __items,
                                state.max_key_bytes(),
                            ),
                        ),
                        target,
                        schedule: #schedule,
                    });
                },
            }
        }
    }
}

/// Push one field's complete semantic-hash contribution onto the generated
/// work stack. Callers visit fields in reverse so the LIFO engine observes the
/// original field order.
fn semantic_hash_field_tasks(field: &FieldInfo, name: &Ident) -> TokenStream {
    match field_carrier(field) {
        FieldCarrier::Leaf if field.is_optional => quote! {
            match #name.as_ref() {
                None => stack.push(SemanticHashTask::AbsorbU8 {
                    value: 0u8,
                    target,
                }),
                Some(__leaf) => {
                    stack.push(semantic_hash_opaque_task::<_, S>(__leaf, target));
                    stack.push(SemanticHashTask::AbsorbU8 {
                        value: 1u8,
                        target,
                    });
                },
            }
        },
        FieldCarrier::Leaf => quote! {
            stack.push(semantic_hash_opaque_task::<_, S>(#name, target));
        },
        FieldCarrier::OptionalChild => {
            let task_variant = format_ident!("SemHash{}", field.category);
            quote! {
                match #name.as_ref() {
                    None => stack.push(SemanticHashTask::AbsorbU8 {
                        value: 0u8,
                        target,
                    }),
                    Some(__child) => {
                        stack.push(SemanticHashTask::#task_variant {
                            value: &**__child as *const _,
                            target,
                            cacheable,
                        });
                        stack.push(SemanticHashTask::AbsorbU8 {
                            value: 1u8,
                            target,
                        });
                    },
                }
            }
        },
        FieldCarrier::OptionalCollection { coll_type } => {
            let collection =
                semantic_hash_collection(&quote! { __collection }, &field.category, &coll_type);
            quote! {
                match #name.as_ref() {
                    None => stack.push(SemanticHashTask::AbsorbU8 {
                        value: 0u8,
                        target,
                    }),
                    Some(__collection) => {
                        #collection
                        stack.push(SemanticHashTask::AbsorbU8 {
                            value: 1u8,
                            target,
                        });
                    },
                }
            }
        },
        FieldCarrier::Collection { coll_type } => {
            semantic_hash_collection(&quote! { #name }, &field.category, &coll_type)
        },
        FieldCarrier::Child => {
            let task_variant = format_ident!("SemHash{}", field.category);
            quote! {
                stack.push(SemanticHashTask::#task_variant {
                    value: &**#name as *const _,
                    target,
                    cacheable,
                });
            }
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
///     `NUMERIC_RAT_TAG` followed by the length-framed reduced `(numer, denom)`
///     of the value's rational form. The two wrappers emit the SAME framed
///     format, so a fixed-point and a big-rational of equal value hash
///     identically. ★ The METHOD NAME differs between them since work item #200
///     (2026-07-30): `CanonicalBigRat::to_canonical_bytes()` is already
///     value-keyed, while `CanonicalFixedPoint`'s value-keyed form is
///     `to_rational_canonical_bytes()` — its `to_canonical_bytes()` was moved
///     onto the raw `(unscaled, places)` pair so it agrees with the `Eq` the
///     owner ruled, which the op-enum content key
///     (`dovetail_report/op_enum.rs:141-146`) requires and this fingerprint must
///     NOT have. One method could not serve both; see
///     `CanonicalFixedPoint::to_rational_canonical_bytes`'s own doc for the
///     two-consumer table.
///
/// The two distinct family tags keep the integer `1` and the rational `1/1`
/// observationally apart (they ARE distinct under the evaluator).
///
/// ## Why a canonical-BYTES method and not `Hash::hash`
///
/// `num_rational::Ratio::hash` hashes the *continued-fraction* expansion
/// (`div_mod_floor` recursion), so `CanonicalBigRat(3/2)::hash` writes `[1,2,0]`,
/// while `CanonicalFixedPoint(1.5p1)::hash` writes its raw `(unscaled, places)`
/// stream `[15, 1]` — `Hash::hash` would NOT unify the two rational wrappers.
/// The value-keyed canonical-bytes methods are identical across wrappers, so
/// they unify them by construction. The bytes are written through `Hasher::write`
/// behind an explicit `write_usize(len)` frame so the leaf is self-delimiting
/// for ANY `Hasher` (the dedup's `FramedSemanticKeyHasher` already frames
/// `write`, but the framing keeps the stream unambiguous regardless).
///
/// ⚠ **RE-DERIVED 2026-07-30 (work item #200).** This paragraph read, verbatim:
///
/// > while `CanonicalFixedPoint(1.5)::hash` (manual `numer.hash();denom.hash();`)
/// > writes `[3,2]` — `Hash::hash` would NOT unify the two rational wrappers.
/// > `to_canonical_bytes()` is the documented `Eq`-agreeing canonical form (the
/// > same key the Dovetail op-enum uses) and is identical across wrappers, so it
/// > unifies them by construction.
///
/// Two clauses of that are now false and one is now the reason for the split:
/// `CanonicalFixedPoint`'s `Hash` no longer writes `numer`/`denom`; its
/// `to_canonical_bytes()` is no longer identical to `CanonicalBigRat`'s; and "the
/// same key the Dovetail op-enum uses" is now precisely what this arm must AVOID,
/// because the op-enum key must agree with an `Eq` that separates `7.00p2` from
/// `7.0p1` while this fingerprint must unify `1.5p1` with `3/2`. Contradictory
/// requirements, two methods.
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
        // ★ THE SPLIT (work item #200, 2026-07-30). `CanonicalFixedPoint::to_canonical_bytes`
        // no longer keys on the value — it keys on the raw `(unscaled, places)` pair, because
        // the op-enum content key (`dovetail_report/op_enum.rs:141-146`) must agree with `Eq`,
        // and `Eq` moved. The VALUE-keyed form survives under a qualifying name and is what
        // THIS fingerprint needs, because unifying `Fixed(1.5p1)` with `BigRat(3/2)` is the
        // whole point of the arm. `CanonicalBigRat` is unaffected: its only key is the value.
        let canon_bytes = if matches!(nt, NativeType::CanonicalFixedPoint) {
            quote! { v.to_rational_canonical_bytes() }
        } else {
            quote! { v.to_canonical_bytes() }
        };
        return Some(quote! {
            state.write_u8(#NUMERIC_RAT_TAG);
            let __numeric_canon: ::std::vec::Vec<u8> = #canon_bytes;
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
        | VariantKind::RecursiveNativeLiteral { label, .. }
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
/// `fold` action to RECONSTRUCT the canonical node, and schedule that node on
/// the same explicit work stack. This makes `semantic_hash(POutputShort(p, q))` byte-identical to
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
/// canonical constructor. The owned reconstruction remains below its visit on
/// the task stack, so its pointer is live through every descendant and is
/// released only after the visit completes. No public-method re-entry occurs.
///
/// ## Cost
///
/// Reconstruction retains the fold action's existing clone cost, but traversal
/// of the result reuses the current driver and task buffer. The keep-alive task
/// adds one box per active reconstructed alias rather than one native frame per
/// descendant.
fn generate_fold_alias_arm(
    category: &Ident,
    variant: &VariantKind,
    arm: &FoldAliasArm,
) -> TokenStream {
    let body = &arm.body;
    let task_variant = format_ident!("SemHash{}", category);
    match variant {
        VariantKind::Nullary { label } => {
            // Zero-param sugar, e.g. `NQuoteNil → NQuote(PZero)`.
            quote! {
                #category::#label => {
                    let __canonical: #category = #body;
                    let (__keep_alive, __canonical_ptr) =
                        semantic_hash_keep_alive(__canonical);
                    stack.push(__keep_alive);
                    stack.push(SemanticHashTask::#task_variant {
                        value: __canonical_ptr,
                        target,
                        cacheable: false,
                    });
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
                    let (__keep_alive, __canonical_ptr) =
                        semantic_hash_keep_alive(__canonical);
                    stack.push(__keep_alive);
                    stack.push(SemanticHashTask::#task_variant {
                        value: __canonical_ptr,
                        target,
                        cacheable: false,
                    });
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

        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            let category_tag = fnv1a64(&category.to_string());
            let pathmap = carrier.pathmap_ref(&quote! { v });
            let focus = carrier.focus_ref(&quote! { v });
            let schedule = recursive_native_semantic_schedule_name(category, label);
            let pathmap_body = semantic_hash_pathmap(&pathmap, &quote! { #schedule });
            quote! {
                #category::#label(v) => {
                    // Recursive native access types remain distinct even when
                    // an enclosing projection is transparent.  The stable
                    // category tag is therefore part of the structural key;
                    // topology and focus follow without rendering or reparsing.
                    state.write_u64(#category_tag);
                    state.write_u8(#variant_idx);
                    stack.push(semantic_hash_opaque_task::<_, S>(#focus, target));
                    #pathmap_body
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
                    // ⚠ A per-entry value tag would NOT close it: empty
                    // containers have no entry bytes. The homogeneous PathMap
                    // mode is instead hashed once at the container boundary.
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
                    //   * `Map`/`Pathmap`: the pathmap arm hashes its homogeneous
                    //     container mode before its entries; the map arm does
                    //     not. Different streams without a per-entry tag.
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
                    // NOT a blocker for #151/#74: PathMap's container-mode
                    // discriminator separates `{|k|}` / `{|k:Nil|}` /
                    // `{|k:5|}` without attaching a tag to every leaf.
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
            // `variant_idx`) followed by the variable's identity, so every
            // type-reading of one identifier collapses to ONE realize-dedup key while
            // DISTINCT variables stay distinct. Sound by the same
            // same-span argument as the numeric canon: the realize-dedup only compares
            // alternatives spanning the SAME source token, i.e. the SAME variable.
            // `0xFB` is a high sentinel distinct from the numeric tags (`0xFE`/`0xFD`)
            // and from any realistic per-category `variant_idx`; even a first-byte
            // brush with idx `0xFB` is harmless because the framed identity payload
            // that follows disambiguates the full key.
            //
            // ★★ #190 — the IDENTITY PAYLOAD, and why it is NOT `Hash::hash(v, …)`.
            //
            // This arm used to write `std::hash::Hash::hash(v, state)` on the `OrdVar`.
            // `OrdVar(pub Var<String>)` derives `Hash`, so for a FREE variable the
            // payload was whatever `moniker`'s `impl Hash for FreeVar` writes, and that
            // impl (`moniker-0.5.0/src/free_var.rs:45`) is exactly
            //
            //     fn hash<H: Hasher>(&self, state: &mut H) { self.unique_id.hash(state); }
            //
            // — `unique_id` and NOTHING else. `UniqueId(u32)` is drawn from a
            // process-global `AtomicUsize` that starts at 0 and is never reset
            // (`unique_id.rs:9`), and `pretty_name` — the SOURCE NAME, the only
            // deterministic identity a free variable has — was discarded.
            //
            // So the entire payload of a free-variable leaf in a CONSENSUS-VISIBLE
            // fingerprint was an accident of how many variables the process had
            // happened to allocate. Measured 2026-07-30, the bare term `a` parsed twice
            // (with the name→var memo cleared between, i.e. what two different NODES
            // always see) fingerprinted 24 B both times and DIFFERED at byte 20.
            // `semantic_hash` backs `semantic_fingerprint` → `exact_key`/`content_key`
            // realize dedup, so two nodes whose counters had diverged would disagree
            // about which parse readings are the same reading. Same argument as #154,
            // different arm — and reachable with no collection and no `Scope` in the
            // term at all, which is why #154's collection-literal repair could not have
            // covered it.
            //
            // ⚠ The witness is DETERMINISM, not alpha-invariance, and the distinction
            // decides the fix. The defect was first reported as "`for(@a <- @"c"){ Nil }`
            // differs from its alpha-renamed twin". It does — but at this layer that is
            // CORRECT: Rholang's `for` binds semantically, yet the AST models the
            // receive pattern as an ordinary free `PVar` with no `Scope` and resolves
            // the binding at COMM time through the substitution TRS. `for(@a <- c){ Nil }`
            // and `for(@b <- c){ Nil }` are two distinct terms that `Display` renders
            // differently, so merging their fingerprints would merge two distinct source
            // programs. Only the SAME-SOURCE-twice instability is a defect.
            //
            // The encoding: `FreeVar` has exactly two fields and one of them is
            // nondeterministic by construction, so there is no design freedom — the
            // source name is the only deterministic key available.
            //
            //     Var::Free(fv)  →  0u8  ++  (1u8 ++ hash(name)) | 0u8
            //     Var::Bound(bv) →  1u8  ++  hash(scope) ++ hash(binder)
            //
            // The `Var::Bound` payload is unchanged in content from the derived `Hash`
            // (`BoundVar`'s impl writes `scope` then `binder`, dropping `pretty_name`):
            // de-Bruijn coordinates are already alpha-canonical, which is why a `PNew`
            // binder was never part of this defect.
            //
            // ⚠ THE ONE THING TRADED AWAY, gated by
            // `languages/tests/semantic_fingerprint_free_var_identity.rs`: two DISTINCT
            // `FreeVar`s sharing a `pretty_name` now fingerprint identically. That is
            // precisely what `languages/src/rholang/guard_substrate.rs`'s `var_key`
            // refuses to do, and the two are not in conflict — they answer different
            // questions. `var_key` needs WITHIN-PROCESS binder identity ("which binder
            // does this guard constrain?"), so it keys on `name$unique_id`. A consensus
            // fingerprint needs CROSS-PROCESS determinism, which forbids `unique_id`
            // outright. The surface cannot separate them either: `Display` renders both
            // as `a`, so `parse(display(t))` already merges them. An ANONYMOUS free
            // variable (`pretty_name: None`) gets its own `0u8` tag — separated from
            // every named one, merged with every other anonymous one, mirroring
            // `Display`'s `_`.
            quote! {
                #category::#label(v) => {
                    state.write_u8(0xFBu8);
                    match &v.0 {
                        mettail_runtime::Var::Free(__fv) => {
                            state.write_u8(0u8);
                            match &__fv.pretty_name {
                                Some(__name) => {
                                    state.write_u8(1u8);
                                    std::hash::Hash::hash(__name.as_str(), state);
                                },
                                None => state.write_u8(0u8),
                            }
                        },
                        mettail_runtime::Var::Bound(__bv) => {
                            state.write_u8(1u8);
                            std::hash::Hash::hash(&__bv.scope, state);
                            std::hash::Hash::hash(&__bv.binder, state);
                        },
                    }
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
            let message = format!(
                "mettail internal error: transparent semantic-hash wrapper `{label_str}` has a \
                 non-scalar category field; the projection classifier and emitter disagree",
            );
            quote! {
                #category::#label(inner) => {
                    compile_error!(#message);
                }
            }
        } else {
            let task_variant = format_ident!("SemHash{}", field.category);
            quote! {
                #category::#label(inner) => {
                    // Transparent wrapper: NO discriminant. Just push the
                    // child's semantic_hash task to the stack.
                    stack.push(SemanticHashTask::#task_variant {
                        value: &**inner as *const _,
                        target,
                        cacheable,
                    });
                }
            }
        }
    } else {
        let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
        let field_pushes: Vec<TokenStream> = fields
            .iter()
            .zip(field_names.iter())
            .rev()
            .map(|(field, name)| semantic_hash_field_tasks(field, name))
            .collect();

        quote! {
            #category::#label(#(ref #field_names),*) => {
                state.write_u8(#variant_idx);
                #(#field_pushes)*
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
    generate_semantic_scoped_arm(category, variant_idx, label, pre_scope_fields, body_cat, false)
}

/// Generate semantic_hash arm for a MultiBinder variant.
fn generate_semantic_multi_binder_arm(
    category: &Ident,
    variant_idx: u8,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
) -> TokenStream {
    generate_semantic_scoped_arm(category, variant_idx, label, pre_scope_fields, body_cat, true)
}

fn generate_semantic_scoped_arm(
    category: &Ident,
    variant_idx: u8,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    is_multi: bool,
) -> TokenStream {
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];
    let pre_scope_pushes: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .rev()
        .map(|(field, name)| semantic_hash_field_tasks(field, name))
        .collect();
    let body_task = format_ident!("SemHash{}", body_cat);
    let arity = if is_multi {
        quote! { #scope_name.inner().unsafe_pattern.len() }
    } else {
        quote! { 1usize }
    };

    quote! {
        #category::#label(#(ref #field_names),*) => {
            state.write_u8(#variant_idx);
            let body_ptr: *const #body_cat = &*#scope_name.inner().unsafe_body;
            stack.push(SemanticHashTask::#body_task {
                value: body_ptr,
                target,
                cacheable,
            });
            stack.push(SemanticHashTask::AbsorbUsize {
                value: #arity,
                target,
            });
            #(#pre_scope_pushes)*
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
                let mut sink = __MettailFlatSemanticSink(state);
                // Fast path: try TLS pool.
                let tls_result = SEMANTIC_HASH_TASK_POOL.try_with(|cell| {
                    let mut stack = cell.take();
                    let was_empty = stack.is_empty();

                    stack.push(SemanticHashTask::#task_variant {
                        value: self as *const _,
                        target: SemanticHashTarget::Root,
                        cacheable: false,
                    });
                    semantic_hash_iterative(&mut stack, &mut sink);

                    if was_empty {
                        stack.clear();
                    }
                    cell.set(stack);
                });

                if tls_result.is_ok() {
                    return;
                }

                // Fallback: TLS unavailable (thread shutdown). Local stack.
                let mut stack = vec![SemanticHashTask::#task_variant {
                    value: self as *const _,
                    target: SemanticHashTarget::Root,
                    cacheable: false,
                }];
                semantic_hash_iterative(&mut stack, &mut sink);
            }

            /// Construct the same exact semantic stream as semantic_hash while
            /// retaining cached child streams as persistent ContentKey ropes.
            ///
            /// Every address admitted to the cache is transitively owned by
            /// owner. The transaction publishes all discovered keys together,
            /// or none of them when a deterministic cache limit is exhausted.
            pub fn semantic_content_key(
                owner: std::sync::Arc<Self>,
                cache: &mut mettail_runtime::exact_semantic_key::ContentKeyCache,
            ) -> Result<
                mettail_runtime::exact_semantic_key::ContentKey,
                mettail_runtime::exact_semantic_key::ContentKeyCacheError,
            > {
                let mut transaction = cache.transaction_for_root(owner.clone());
                let mut sink = __MettailComposingSemanticSink::new(&mut transaction);
                let used_tls = SEMANTIC_HASH_TASK_POOL
                    .try_with(|cell| {
                        let mut stack = cell.take();
                        stack.clear();
                        stack.push(SemanticHashTask::#task_variant {
                            value: std::sync::Arc::as_ptr(&owner),
                            target: SemanticHashTarget::Root,
                            cacheable: true,
                        });
                        semantic_hash_iterative(&mut stack, &mut sink);
                        stack.clear();
                        cell.set(stack);
                    })
                    .is_ok();
                if !used_tls {
                    let mut stack = vec![SemanticHashTask::#task_variant {
                        value: std::sync::Arc::as_ptr(&owner),
                        target: SemanticHashTarget::Root,
                        cacheable: true,
                    }];
                    semantic_hash_iterative(&mut stack, &mut sink);
                }
                let key = sink.into_result()?;
                transaction.commit()?;
                Ok(key)
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
            arm.contains("semantic_hash_opaque_task :: < _ , S > (__leaf , target)"),
            "the Some arm must defer the bare predicate's exact structural hash calls: {arm}",
        );
        assert!(
            !arm.contains("* * __b"),
            "no Arc deref exists on an Option<BehavioralPred> payload: {arm}",
        );
        assert!(
            arm.contains("value : 0u8") && arm.contains("value : 1u8"),
            "the deferred None/Some discriminant scheme must be kept: {arm}",
        );
        assert!(
            !arm.contains("semantic_hash (state)"),
            "no child semantic hash may re-enter the public driver: {arm}",
        );
    }
}

#[cfg(test)]
mod task_usage_tests {
    use super::*;

    fn compact(tokens: TokenStream) -> String {
        tokens
            .to_string()
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect()
    }

    #[test]
    fn unreachable_optional_task_shapes_are_not_emitted() {
        let language = crate::gen::empty_language_for_tests();
        let generated = compact(generate_semantic_hash(&language));

        for absent in [
            "semantic_hash_opaque_task",
            "semantic_hash_keep_alive",
            "SemanticHashTask::Opaque",
            "SemanticHashTask::KeepAlive",
            "SemanticHashTask::ResumeCollection",
            "Scratch(*mutmettail_runtime::CollectionSemanticHasher)",
            "fnsemantic_hash_write_key",
        ] {
            assert!(
                !generated.contains(absent),
                "an empty language cannot reach `{absent}`, so emitting it is dead code"
            );
        }
    }

    #[test]
    fn unordered_categories_share_one_resume_driver_and_keep_typed_schedulers() {
        let language = crate::gen::collection_literal_language_for_tests();
        let generated = compact(generate_semantic_hash(&language));

        assert!(
            generated.contains("SemanticHashTask::ResumeCollection"),
            "the fixture's Bag/Set/Map/Pathmap literals require the shared resume driver"
        );
        assert!(
            generated.contains("Scratch(*mutmettail_runtime::CollectionSemanticHasher)")
                && generated.contains("fnsemantic_hash_write_key"),
            "an unordered collection requires scratch construction and exact framed keys"
        );
        assert!(
            !generated.contains("CollectionSemanticHashStep::WriteU64")
                && !generated.contains("AbsorbPathMapMode"),
            "StructuralV2 must not retain digest-only lanes or implicit PathMap modes"
        );
        assert_eq!(
            generated
                .matches("fnsemantic_hash_resume_collection<")
                .count(),
            1,
            "all unordered shapes share one type-erased PDA resume driver"
        );
        assert_eq!(
            generated
                .matches("fnsemantic_hash_schedule_collection_proc")
                .count(),
            1,
            "the shared driver restores Proc through one typed scheduler"
        );
    }

    #[test]
    fn leaf_and_fold_usage_enable_their_exact_task_shapes() {
        let mut usage = SemanticTaskUsage::default();
        usage.record_field(&FieldInfo {
            category: format_ident!("Guard"),
            is_collection: false,
            coll_type: None,
            is_predicate: true,
            is_optional: true,
            opaque_leaf: None,
        });
        usage.needs_keep_alive = true;

        let generated =
            compact(generate_semantic_task_enum(&crate::gen::empty_language_for_tests(), &usage));
        assert!(generated.contains("semantic_hash_opaque_task"));
        assert!(generated.contains("SemanticHashTask::Opaque"));
        assert!(generated.contains("semantic_hash_keep_alive"));
        assert!(generated.contains("SemanticHashTask::KeepAlive"));
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
            ts.contains("SemHashProc") && ts.contains("semantic_hash_keep_alive"),
            "the canonical reconstruction must be retained and scheduled on the current PDA: {ts}"
        );
        assert!(
            !ts.contains(". semantic_hash ("),
            "a fold alias must not re-enter the public semantic-hash driver: {ts}",
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
