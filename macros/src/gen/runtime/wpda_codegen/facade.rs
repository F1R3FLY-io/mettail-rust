//! `parse_<Cat>_via_wpda` facade emission.
//!
//! Emits per-category wrapper functions that drive the WPDS walker to
//! saturation on a `TokenKind` slice and extract the resulting AST term.
//!
//! ## Signature
//!
//! ```ignore
//! pub fn parse_<Cat>_via_wpda(
//!     kinds: &[TokenKind],
//!     texts: &[&str],
//!     pos: &mut usize,
//!     min_bp: u8,
//! ) -> Result<<Cat>, WpdaParseError>
//! ```
//!
//! The caller is responsible for tokenizing the source input. Parity-test
//! harnesses (`test_gen/parity.rs`) provide a per-grammar `Token → TokenKind`
//! adapter so both engines can run on the same source.
//!
//! ## Recovery
//!
//! Strict parse entry points disable recovery by setting
//! `RecoveryConfig.max_recovery_depth = 0`. The explicit
//! `parse_<Cat>_via_wpda_recovering` entry point keeps the walker's default
//! recovery config and returns the committed recovery trail.

use mettail_ast::grammar::{PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Emit the generated-module-scope `__MettailWpdaSemanticKeyHasher` ONCE
/// (2026-06-28, SPPF-realize observational-dedup).
///
/// This was previously a function-local struct duplicated inside every
/// per-category facade parser. It is hoisted to module scope so BOTH the
/// facade's root-dedup (`__mettail_wpda_semantic_key`) AND the engine's
/// per-node `WpdaEngine::semantic_fingerprint` override consume the SAME
/// INJECTIVE-up-to-observational-equivalence byte key
/// (`term.semantic_hash(..)` → `into_key()`): the FULL tagged
/// length-prefixed byte stream (NOT `finish() -> u64`). Sharing one key
/// definition is what makes per-node dedup byte-for-byte equivalent to the
/// facade's root-only dedup (the output-identity theorem).
pub(crate) fn emit_semantic_key_hasher() -> TokenStream {
    quote! {
        #[derive(Default)]
        struct __MettailWpdaSemanticKeyHasher {
            bytes: Vec<u8>,
        }
        impl __MettailWpdaSemanticKeyHasher {
            fn into_key(self) -> Vec<u8> {
                self.bytes
            }
            fn push_raw(&mut self, tag: u8, payload: &[u8]) {
                self.bytes.push(tag);
                self.bytes.extend_from_slice(&(payload.len() as u64).to_le_bytes());
                self.bytes.extend_from_slice(payload);
            }
            fn push_fixed(&mut self, tag: u8, payload: &[u8]) {
                self.bytes.push(tag);
                self.bytes.extend_from_slice(payload);
            }
        }
        impl std::hash::Hasher for __MettailWpdaSemanticKeyHasher {
            fn finish(&self) -> u64 {
                let mut h = 0xcbf29ce484222325u64;
                for b in &self.bytes {
                    h ^= *b as u64;
                    h = h.wrapping_mul(0x100000001b3);
                }
                h
            }
            fn write(&mut self, bytes: &[u8]) {
                self.push_raw(0, bytes);
            }
            fn write_u8(&mut self, i: u8) {
                self.push_fixed(1, &[i]);
            }
            fn write_u16(&mut self, i: u16) {
                self.push_fixed(2, &i.to_le_bytes());
            }
            fn write_u32(&mut self, i: u32) {
                self.push_fixed(3, &i.to_le_bytes());
            }
            fn write_u64(&mut self, i: u64) {
                self.push_fixed(4, &i.to_le_bytes());
            }
            fn write_u128(&mut self, i: u128) {
                self.push_fixed(5, &i.to_le_bytes());
            }
            fn write_usize(&mut self, i: usize) {
                self.push_fixed(6, &(i as u128).to_le_bytes());
            }
            fn write_i8(&mut self, i: i8) {
                self.push_fixed(7, &i.to_le_bytes());
            }
            fn write_i16(&mut self, i: i16) {
                self.push_fixed(8, &i.to_le_bytes());
            }
            fn write_i32(&mut self, i: i32) {
                self.push_fixed(9, &i.to_le_bytes());
            }
            fn write_i64(&mut self, i: i64) {
                self.push_fixed(10, &i.to_le_bytes());
            }
            fn write_i128(&mut self, i: i128) {
                self.push_fixed(11, &i.to_le_bytes());
            }
            fn write_isize(&mut self, i: isize) {
                self.push_fixed(12, &(i as i128).to_le_bytes());
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// P2 ISOLATION+COMBINE CODEGEN (Plan a7986200, 2026-07-05) — ships the ROOT-P
// `.*sep` divide-and-conquer linearization into the generated facade.
// Gate: `super::forks::SEP_ISOLATION_COMBINE` + `SEP_ISOLATION_CATEGORIES`.
// ════════════════════════════════════════════════════════════════════════

/// One labeled AST variant a `.*sep` category builds, with the suffix
/// operand-groups AFTER the list (e.g. the `"where" cond:Proc` of
/// `ForRowWhere`). The bare list variant (e.g. `ForRowNoWhere`) has
/// `operand_groups` empty.
struct SepOperandGroup {
    /// The literal that introduces the group at depth 0 (e.g. `"where"`).
    lead: String,
    /// Operand category (e.g. `"Proc"`) — parsed via its own `_all` facade.
    category: String,
}

struct SepVariant {
    /// Constructor label (e.g. `"ForRowNoWhere"` / `"ForRowWhere"`).
    label: String,
    /// Suffix operand-groups (currently at most one supported; a shape with
    /// more is not isolation-eligible — see `derive_sep_combine_shape`).
    operand_groups: Vec<SepOperandGroup>,
}

/// Grammar-derived shape of a `head sep list.*sep(sep) [suffix]` category that
/// the isolation helper linearizes. Derived from the SAME grammar IR the walker
/// classifies (`GrammarRule.syntax_pattern`'s `PatternOp::Sep` — RT-1/7); NO
/// per-language / per-rule hardcode.
///
/// Currently accepts the top-level head+list form (list starting at token 0, no
/// prefix framing/operands, `Vec<Element>` list field, ≤1 suffix operand-group
/// per variant) — this is `ForRow` / `ForRowPersistent*`. Framed-list /
/// prefix-operand shapes (sends, polyadic binds, braced collections) return
/// `None` here (they fall through to the monolithic body — byte-identical,
/// sound) until the derivation is extended for them.
pub(crate) struct SepCombineShape {
    /// Element category parsed per segment (e.g. `"InputBind"`) — re-lexed +
    /// sub-parsed via its own `parse_via_wpda_all_with_weights` string entry.
    element_category: String,
    /// Depth-0 element separator text (e.g. `"&"`). A single ASCII byte for every
    /// shipped `.*sep` — enforced by `derive_sep_combine_shape`.
    separator: String,
    /// `src_idx` of the RESULT category (this `.*sep` category).
    result_src_idx: u16,
    /// Labeled variants, ordered most-specific first (more operand-groups first),
    /// so the scan elects the suffix variant when its lead literal is present.
    variants: Vec<SepVariant>,
}

/// Extract a base category name from a `TypeExpr::Base`.
fn sep_base_ty(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Base(id) => Some(id.to_string()),
        _ => None,
    }
}

/// Derive the [`SepCombineShape`] for `cat_name`, or `None` when the category is
/// not an isolation-eligible `.*sep` shape (grammar-derived — the single source
/// of truth for the emitted helper + prologues).
fn derive_sep_combine_shape(
    language: &LanguageDef,
    cat_name: &str,
    categories: &[String],
) -> Option<SepCombineShape> {
    let src_idx_of =
        |name: &str| -> Option<u16> { categories.iter().position(|c| c == name).map(|i| i as u16) };
    let result_src_idx = src_idx_of(cat_name)?;

    let mut element_category: Option<String> = None;
    let mut separator: Option<String> = None;
    let mut variants: Vec<SepVariant> = Vec::new();

    for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        let (Some(tc), Some(sp)) = (&normalized.term_context, &normalized.syntax_pattern) else {
            continue;
        };
        // Exactly one `.*sep` operand in the pattern.
        let sep_positions: Vec<usize> = sp
            .iter()
            .enumerate()
            .filter_map(|(i, e)| matches!(e, SyntaxExpr::Op(PatternOp::Sep { .. })).then_some(i))
            .collect();
        if sep_positions.len() != 1 {
            continue;
        }
        let sep_idx = sep_positions[0];
        let SyntaxExpr::Op(PatternOp::Sep { collection, separator: rule_sep, .. }) = &sp[sep_idx]
        else {
            continue;
        };
        // Head+list form ONLY: `[Param(head), Literal(sep), Op(Sep(list)), …]`
        // with the list at token 0 (no prefix framing / prefix operands).
        if sep_idx != 2 {
            continue;
        }
        let SyntaxExpr::Param(_) = &sp[0] else { continue };
        let SyntaxExpr::Literal(head_sep) = &sp[1] else { continue };
        // SEPARATOR-LOCALITY at the head: the head↔list join literal must equal
        // the list separator (uniform list — a genuine `.*sep`).
        if head_sep != rule_sep {
            continue;
        }
        // Element category = the inner type of the `Vec(elem)` list param.
        let elem_cat = tc.iter().find_map(|p| match p {
            TermParam::Simple { name, ty } if name == collection => match ty {
                TypeExpr::Collection { element, .. } => sep_base_ty(element),
                _ => None,
            },
            _ => None,
        })?;
        // Suffix operand-groups: `[Literal(lead), Param(op)]*` after the `.*sep`.
        let mut groups: Vec<SepOperandGroup> = Vec::new();
        let mut j = sep_idx + 1;
        let mut shape_ok = true;
        while j < sp.len() {
            let SyntaxExpr::Literal(lead) = &sp[j] else {
                shape_ok = false;
                break;
            };
            let Some(SyntaxExpr::Param(op)) = sp.get(j + 1) else {
                shape_ok = false;
                break;
            };
            let op_cat = tc.iter().find_map(|p| match p {
                TermParam::Simple { name, ty } if name == op => sep_base_ty(ty),
                _ => None,
            });
            let Some(op_cat) = op_cat else {
                shape_ok = false;
                break;
            };
            groups.push(SepOperandGroup { lead: lead.clone(), category: op_cat });
            j += 2;
        }
        if !shape_ok {
            continue;
        }
        // At most one suffix operand-group per variant (the shipped `where cond`);
        // richer suffixes are not isolation-eligible yet.
        if groups.len() > 1 {
            return None;
        }
        // Uniform element category + separator across all variants of this cat.
        match &element_category {
            None => element_category = Some(elem_cat.clone()),
            Some(e) if *e == elem_cat => {},
            Some(_) => return None,
        }
        match &separator {
            None => separator = Some(rule_sep.clone()),
            Some(s) if s == rule_sep => {},
            Some(_) => return None,
        }
        variants.push(SepVariant { label: normalized.label.to_string(), operand_groups: groups });
    }

    let element_category = element_category?;
    let separator = separator?;
    // The STRING-level depth split matches the separator as a single ASCII byte
    // (every shipped `.*sep` — `&`/`,`/`;`/`|`). Non-single-byte separators are
    // not isolation-eligible here.
    if separator.len() != 1 || !separator.is_ascii() {
        return None;
    }
    // Need the bare list variant (no suffix) plus at least one variant.
    if variants.is_empty() || !variants.iter().any(|v| v.operand_groups.is_empty()) {
        return None;
    }

    // SEPARATOR-LOCALITY soundness gate (T9): the separator must NOT be able to
    // occur at depth 0 WITHIN a single element — i.e. no rule BUILDS an element
    // using the separator (`… sep … : Element`). Else a depth-0 split would DROP
    // the readings where the separator binds as an element-internal operator
    // (never-disambiguate-early). We test `result_category == element_category`
    // (the separator PRODUCES an element); we deliberately do NOT test
    // `category == element_category` (the separator merely CONSUMES an element as
    // LHS) — that is exactly the `.*sep` rule we are handling (`b "&" … : ForRow`
    // has LHS category `InputBind`) and must not disqualify it. Mirrors the
    // spirit of C3 `category_recognizes_operator`.
    let infix_rules = super::infix::extract_infix_rules(language);
    let sep_builds_element = infix_rules
        .iter()
        .any(|r| r.terminal == separator && r.result_category == element_category);
    if sep_builds_element {
        return None;
    }

    // Order variants most-specific first (more operand-groups first).
    variants.sort_by(|a, b| b.operand_groups.len().cmp(&a.operand_groups.len()));

    Some(SepCombineShape { element_category, separator, result_src_idx, variants })
}

/// The module-scope identifier of the isolation helper for `cat_name`.
pub(crate) fn sep_isolation_helper_ident(cat_name: &str) -> proc_macro2::Ident {
    format_ident!("__mettail_wpda_sep_isolate_all_{}", cat_name)
}

/// The gated `.*sep` isolation shape for `cat_name`: `Some` iff the master
/// switch is ON, the category is in the include set, AND a shape is derivable.
/// The SINGLE source of truth shared by the helper emitter (facade) and the
/// string-entry prologue emitter (mod.rs).
pub(crate) fn sep_isolation_shape(
    language: &LanguageDef,
    cat_name: &str,
    categories: &[String],
) -> Option<SepCombineShape> {
    if super::forks::SEP_ISOLATION_COMBINE
        && super::forks::SEP_ISOLATION_CATEGORIES.contains(&cat_name)
    {
        derive_sep_combine_shape(language, cat_name, categories)
    } else {
        None
    }
}

/// Which string parse entry a prologue is emitted into.
pub(crate) enum SepSeam {
    /// `Cat::parse_via_wpda(input) -> Result<Cat, ParseError>` (single winner).
    Single,
    /// `Cat::parse_via_wpda_all_with_weights(input) -> Result<(Vec<Cat>, Vec<W>), ParseError>`.
    All,
}

/// Emit the guarded string-entry prologue that calls the isolation helper with
/// the RAW input string (before `lex_dag`). Runtime A/B: `PRATTAIL_NO_SEP_ISOLATION`
/// forces the monolithic path without a rebuild.
pub(crate) fn emit_sep_isolation_prologue(
    helper_name: &proc_macro2::Ident,
    seam: SepSeam,
) -> TokenStream {
    match seam {
        SepSeam::Single => quote! {
            // P2 ISOLATION+COMBINE prologue (Plan a7986200) — single winner.
            if std::env::var_os("PRATTAIL_NO_SEP_ISOLATION").is_none() {
                if let Some((__iso_terms, __iso_weights)) = #helper_name(input) {
                    if let Some((__t, _)) = __iso_terms
                        .into_iter()
                        .zip(__iso_weights.into_iter())
                        .min_by(|(_, __a), (_, __b)| __a.cmp(__b))
                    {
                        return Ok(__t);
                    }
                }
            }
        },
        SepSeam::All => quote! {
            // P2 ISOLATION+COMBINE prologue (Plan a7986200) — full alt set.
            if std::env::var_os("PRATTAIL_NO_SEP_ISOLATION").is_none() {
                if let Some(__iso) = #helper_name(input) {
                    return Ok(__iso);
                }
            }
        },
    }
}

/// Emit the shared per-category STRING-level isolation helper
/// `__mettail_wpda_sep_isolate_all_<Cat>(input: &str)`.
///
/// It mirrors the Stage-0-VALIDATED probe EXACTLY at the STRING level: a
/// bracket-depth-aware char split of the raw input (NOT the post-lex token
/// source — that is an ambiguous LATTICE for these surfaces, which is precisely
/// why the monolithic parse forks `dᵏ`), then a TRULY ISOLATED re-lex+parse of
/// each segment through the ELEMENT category's own `parse_via_wpda_all_with_weights`
/// string entry, then a cartesian combine (⊗-folded weights) + dedup + sort.
/// `None` ⇒ NOT-APPLICABLE or ANY sub-parse failure ⇒ the caller falls through to
/// the UNMODIFIED monolithic body (byte-identical; monolithic authoritative — RT-4).
fn emit_sep_isolation(cat_ident: &proc_macro2::Ident, shape: &SepCombineShape) -> TokenStream {
    let helper_name = sep_isolation_helper_ident(&cat_ident.to_string());
    let elem_ident = format_ident!("{}", shape.element_category);
    let result_src_idx = shape.result_src_idx;
    // Separator is a single ASCII byte for every shipped `.*sep` (`&`/`,`/`;`/`|`)
    // — `derive_sep_combine_shape` enforces this.
    let sep_byte = shape.separator.as_bytes()[0];

    // Per-variant: the depth-0 suffix-lead detection + the construction arm.
    let mut lead_checks: Vec<TokenStream> = Vec::new();
    let mut construct_arms: Vec<TokenStream> = Vec::new();
    let mut bare_variant_idx: usize = 0;
    for (vi, variant) in shape.variants.iter().enumerate() {
        let vi_lit = vi;
        let label_ident = format_ident!("{}", variant.label);
        if variant.operand_groups.is_empty() {
            // The bare list variant — `Cat::Label(Arc(elems[0]), elems[1..])`.
            // (Scalar HEAD is `Arc<Element>` — mirrors the walker `into_term_arc`;
            // the `.*sep` list field is a plain `Vec<Element>` — mirrors the drain.)
            bare_variant_idx = vi;
            construct_arms.push(quote! {
                #vi_lit => {
                    for (__elems, __w) in __element_combos {
                        __candidates.push((
                            #cat_ident::#label_ident(
                                std::sync::Arc::new(__elems[0].clone()),
                                __elems[1..].to_vec(),
                            ),
                            __w,
                        ));
                    }
                }
            });
        } else {
            // A suffix variant — one operand-group `lead op:Cat`.
            let group = &variant.operand_groups[0];
            let lead = &group.lead;
            let lead_len = group.lead.len();
            let op_ident = format_ident!("{}", group.category);
            // Depth-0 word-bounded lead detection over the raw bytes.
            lead_checks.push(quote! {
                if __i + #lead_len <= __n
                    && &__bytes[__i..__i + #lead_len] == #lead.as_bytes()
                    && (__i == 0 || !__is_word(__bytes[__i - 1]))
                    && (__i + #lead_len == __n || !__is_word(__bytes[__i + #lead_len]))
                {
                    __variant = #vi_lit;
                    __domain_end = __i;
                    __op_start = __i + #lead_len;
                    break 'scan;
                }
            });
            construct_arms.push(quote! {
                #vi_lit => {
                    let __suffix = input[__op_start..].trim();
                    if __suffix.is_empty() {
                        return None;
                    }
                    let (__op_terms, __op_weights) =
                        match #op_ident::parse_via_wpda_all_with_weights(__suffix) {
                            Ok(__v) => __v,
                            Err(_) => return None,
                        };
                    if __op_terms.is_empty() {
                        return None;
                    }
                    for (__elems, __we) in &__element_combos {
                        for (__op, __wo) in __op_terms.iter().zip(__op_weights.iter()) {
                            if __candidates.len() >= __REALIZE_CAP {
                                return None;
                            }
                            __candidates.push((
                                #cat_ident::#label_ident(
                                    std::sync::Arc::new(__elems[0].clone()),
                                    __elems[1..].to_vec(),
                                    std::sync::Arc::new(__op.clone()),
                                ),
                                Semiring::times(__we, __wo),
                            ));
                        }
                    }
                }
            });
        }
    }
    let bare_variant_idx_lit = bare_variant_idx;

    quote! {
        /// P2 ISOLATION+COMBINE (Plan a7986200): STRING-level divide-and-conquer
        /// `.*sep` linearizer for the `#cat_ident` category. See
        /// `emit_sep_isolation` in the macro for the full rationale.
        #[allow(
            non_snake_case,
            unused_assignments,
            unused_variables,
            clippy::needless_range_loop,
            clippy::manual_is_ascii_check
        )]
        fn #helper_name(
            input: &str,
        ) -> Option<(
            Vec<#cat_ident>,
            Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
        )> {
            use mettail_prattail::automata::semiring::Semiring;
            type __W = mettail_prattail::automata::lex_weight::LexicographicWeight;
            const __REALIZE_CAP: usize = 64;
            fn __is_word(c: u8) -> bool {
                c.is_ascii_alphanumeric() || c == b'_'
            }
            let __bytes = input.as_bytes();
            let __n = __bytes.len();
            if __n == 0 {
                return None;
            }

            // (1) Locate the depth-0 SUFFIX (optional `lead op` group) via a
            //     bracket-depth char scan. Standard ASCII brackets `([{` / `)]}`
            //     track depth; multi-char collection delimiters (`#{`/`{|`/…)
            //     balance via their `{`/`}` component (Stage-0-validated). This
            //     is the char-level analogue of the probe `split_amp_depth0`.
            let mut __variant: usize = #bare_variant_idx_lit;
            let mut __domain_end: usize = __n;
            #[allow(unused_assignments)]
            let mut __op_start: usize = __n;
            {
                let mut __depth: i32 = 0;
                let mut __i = 0usize;
                'scan: while __i < __n {
                    match __bytes[__i] {
                        b'(' | b'[' | b'{' => __depth += 1,
                        b')' | b']' | b'}' => __depth -= 1,
                        _ => {
                            if __depth == 0 {
                                #(#lead_checks)*
                            }
                        }
                    }
                    __i += 1;
                }
            }

            // (2) SPLIT the domain `[0, __domain_end)` at depth-0 separator bytes.
            let mut __seg_ranges: Vec<(usize, usize)> = Vec::new();
            {
                let mut __depth: i32 = 0;
                let mut __start = 0usize;
                let mut __i = 0usize;
                while __i < __domain_end {
                    match __bytes[__i] {
                        b'(' | b'[' | b'{' => __depth += 1,
                        b')' | b']' | b'}' => __depth -= 1,
                        __c if __depth == 0 && __c == #sep_byte => {
                            __seg_ranges.push((__start, __i));
                            __start = __i + 1;
                        }
                        _ => {}
                    }
                    __i += 1;
                }
                __seg_ranges.push((__start, __domain_end));
            }
            // 0 separators ⇒ single element ⇒ fall through (the monolithic single
            // variant is already fast; no `dᵏ` fork to linearize).
            if __seg_ranges.len() < 2 {
                return None;
            }

            // (3) ISOLATED per-segment RE-LEX + parse via the ELEMENT category's
            //     own string entry (fresh lex + walker from ROOT — NO
            //     cross-segment accumulation). Any Err / empty ⇒ None (RT-4). A
            //     `_all` string entry consumes the WHOLE segment or errors, so
            //     no partial-consume check is needed.
            let mut __per_seg: Vec<(Vec<#elem_ident>, Vec<__W>)> =
                Vec::with_capacity(__seg_ranges.len());
            for &(__s, __e) in &__seg_ranges {
                let __seg = input[__s..__e].trim();
                if __seg.is_empty() {
                    return None;
                }
                let (__terms, __weights) =
                    match #elem_ident::parse_via_wpda_all_with_weights(__seg) {
                        Ok(__v) => __v,
                        Err(_) => return None,
                    };
                if __terms.is_empty() {
                    return None;
                }
                __per_seg.push((__terms, __weights));
            }

            // (4) CARTESIAN COMBINE over segments (⊗-folded weights, cap 64).
            let mut __element_combos: Vec<(Vec<#elem_ident>, __W)> =
                vec![(Vec::new(), <__W as Semiring>::one())];
            for (__alts, __ws) in &__per_seg {
                let mut __next: Vec<(Vec<#elem_ident>, __W)> =
                    Vec::with_capacity(__element_combos.len() * __alts.len().max(1));
                for (__prefix, __pw) in &__element_combos {
                    for (__a, __aw) in __alts.iter().zip(__ws.iter()) {
                        if __next.len() >= __REALIZE_CAP {
                            return None;
                        }
                        let mut __v = __prefix.clone();
                        __v.push(__a.clone());
                        __next.push((__v, Semiring::times(__pw, __aw)));
                    }
                }
                __element_combos = __next;
            }
            // Fold in the framing weight (cost 0.0 ⇒ absorbed under ⊗; provenance
            // leg = the result category's) so the winner is the product of
            // per-segment minima = the monolithic minimum (T5).
            let __framing = __W::from_cost(0.0, #result_src_idx, 0);
            for __c in __element_combos.iter_mut() {
                __c.1 = Semiring::times(&__framing, &__c.1);
            }

            // (5) Construct per elected variant (specialized `emit_infix_action_entry`).
            let mut __candidates: Vec<(#cat_ident, __W)> = Vec::new();
            match __variant {
                #(#construct_arms)*
                _ => return None,
            }
            if __candidates.is_empty() {
                return None;
            }

            // (6) FINALIZE like the monolithic `_all`: dedup by semantic key,
            //     ⊕-min representative, weight-sort.
            let mut __seen: std::collections::HashMap<Vec<u8>, usize> =
                std::collections::HashMap::with_capacity(__candidates.len());
            let mut __out_terms: Vec<#cat_ident> = Vec::new();
            let mut __out_weights: Vec<__W> = Vec::new();
            for (__term, __w) in __candidates {
                let __key = {
                    let mut __h = __MettailWpdaSemanticKeyHasher::default();
                    __term.semantic_hash(&mut __h);
                    __h.into_key()
                };
                if let Some(&__idx) = __seen.get(&__key) {
                    if __w < __out_weights[__idx] {
                        __out_terms[__idx] = __term;
                        __out_weights[__idx] = __w;
                    }
                } else {
                    __seen.insert(__key, __out_terms.len());
                    __out_terms.push(__term);
                    __out_weights.push(__w);
                }
            }
            let mut __paired: Vec<_> =
                __out_terms.into_iter().zip(__out_weights.into_iter()).collect();
            __paired.sort_by(|(_, __a), (_, __b)| __a.cmp(__b));
            let (__out_terms, __out_weights): (Vec<_>, Vec<_>) =
                __paired.into_iter().unzip();
            Some((__out_terms, __out_weights))
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// P1 `@`-PROJECTION ISOLATION+COMBINE CODEGEN (Plan a8b32275, 2026-07-05) —
// the SIBLING of the P2 `.*sep` isolation above (ROOT AXIS-@ exponential-killer).
// Gate: `super::forks::PROJ_ISOLATION_COMBINE` + `PROJ_ISOLATION_CATEGORIES`.
//
// Difference from `.*sep`: rather than splitting a list at a separator and
// cartesian-combining SEGMENTS, projection isolation matches each `σ`-led
// frame-variant's grammar-derived Literal/Operand skeleton, extracts each
// cross-cat OPERAND by a bracket-depth scan, sub-parses it in isolation
// (recursing), and WRAPS the readings in the surface enum ctor. The shared
// semantic-key dedup (`semantic_hash` normalizes fold variants to canonical
// form) collapses over-produced fold-equivalents to EXACTLY the monolithic set.
// ════════════════════════════════════════════════════════════════════════

/// One slot in an `@`-projection / framed-list frame-variant's grammar-derived
/// skeleton.
enum ProjSlot {
    /// A fixed literal token (`@`, `Nil`, `!`, `(`, `)`, …).
    Lit(String),
    /// A cross-cat SCALAR operand `p:Category` — extracted by bracket-depth scan
    /// and sub-parsed via `Category::parse_via_wpda_all_with_weights` (recurses).
    /// Constructed as an `Arc<Category>` ctor field.
    Operand { category: String },
    /// A `.*sep(sep)` LIST operand `xs:Vec(Element)` (P4 framing, Plan a8b32275).
    /// The bracket-delimited region is split at the depth-0 single-byte `separator`
    /// and each element re-lexed + sub-parsed via
    /// `Element::parse_via_wpda_all_with_weights` (recurses through this prologue —
    /// so deep-`@` polyadic args linearize), then cartesian-combined into a
    /// `Vec<Element>` ctor field. This is what frames the polyadic sends
    /// (`n!(a, bs.*sep)`), query binds (`lhs<-n!?(args.*sep)`), and polyadic binds
    /// (`lhs, lhss.*sep <-n`) whose comma-lists carried the residual `dᵏ` blowup.
    SepList { element_category: String, separator: String },
}

/// One `σ`-led frame-variant the projection helper linearizes: a surface enum
/// constructor whose syntax begins with a NON-ident sigil literal and contains
/// ≥1 cross-cat operand.
struct ProjVariant {
    /// Surface enum-constructor label (e.g. `"POutputNil"` / `"NQuoteShort"`).
    label: String,
    /// The grammar-derived Literal/Operand skeleton (source order), slot 0 = σ.
    slots: Vec<ProjSlot>,
}

/// Grammar-derived shape of an `@`-projection category: the σ-led frame-variants.
pub(crate) struct ProjIsoShape {
    /// `src_idx` of the RESULT category (this `@`-projection category).
    result_src_idx: u16,
    /// Frame-variants, ordered most-specific first (more fixed literals first),
    /// so the scan/dedup elects the specific keyword-send (`@Nil!(q)`) before the
    /// general `@p!(q)` — matching the monolithic rule-order preference.
    variants: Vec<ProjVariant>,
}

/// Derive the [`ProjIsoShape`] for `cat_name`, or `None` when the category has no
/// isolation-eligible `@`-projection rule (grammar-derived — single source of
/// truth). Accepts every rule whose syntax pattern is a pure Literal/Param
/// sequence beginning with a NON-ident sigil and carrying ≥1 `Base`-typed Param.
/// Rules with a `.*sep`/`#opt`/binder operand (`Op`/non-`Simple` param) are NOT
/// projection shapes (they fall through to the monolithic body / the sep helper).
fn derive_projection_iso_shape(
    language: &LanguageDef,
    cat_name: &str,
    categories: &[String],
) -> Option<ProjIsoShape> {
    let src_idx_of =
        |name: &str| -> Option<u16> { categories.iter().position(|c| c == name).map(|i| i as u16) };
    let result_src_idx = src_idx_of(cat_name)?;

    let is_ident_shaped = |s: &str| s.chars().all(|c| c.is_alphanumeric() || c == '_');

    let mut variants: Vec<ProjVariant> = Vec::new();

    for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        let (Some(tc), Some(sp)) = (&normalized.term_context, &normalized.syntax_pattern) else {
            continue;
        };
        if sp.is_empty() {
            continue;
        }
        // ELIGIBILITY (relaxed for P4 framing, Plan a8b32275): a rule joins the
        // projection helper iff EITHER
        //   (a) slot 0 is a NON-ident sigil literal — the `@`/`(`/`*`/`-`-led
        //       projection shapes (`@Nil!(q)`, `@(p)`, `*n`, …), OR
        //   (b) it carries exactly one `.*sep` LIST operand over an ORDERED `Vec`
        //       collection — the FRAMED-LIST shapes whose comma-lists carried the
        //       residual `dᵏ` blowup (`n!(a, bs.*sep)`, `lhs<-n!?(args.*sep)`,
        //       `lhs, lhss.*sep <-n`). These start with a scalar OPERAND, not a
        //       sigil, so the sigil gate alone would miss them.
        // `HashBag`/`HashSet`/`HashMap`/binder collections are NOT ordered lists
        // and are handled elsewhere (collection codegen) — excluded below.
        let vec_sep_count = sp
            .iter()
            .filter(|e| {
                matches!(e, SyntaxExpr::Op(PatternOp::Sep { collection, .. })
                    if tc.iter().any(|tp| matches!(tp,
                        TermParam::Simple { name, ty: TypeExpr::Collection { coll_type: CollectionType::Vec, .. } }
                            if name == collection)))
            })
            .count();
        let sigil_led = matches!(&sp[0], SyntaxExpr::Literal(lead) if !is_ident_shaped(lead));
        // Reject any Sep that is NOT a single ordered-`Vec` list (multiple lists,
        // or a HashBag/Map list) — not framed-list-isolation-eligible.
        let total_sep = sp
            .iter()
            .filter(|e| matches!(e, SyntaxExpr::Op(PatternOp::Sep { .. })))
            .count();
        if total_sep != vec_sep_count || vec_sep_count > 1 {
            continue;
        }
        // A category that the DEDICATED `.*sep` helper owns
        // (`SEP_ISOLATION_CATEGORIES`, e.g. `ForRow`'s `&`-join) delegates ALL its
        // list shapes to that (validated, landed) helper — the projection helper
        // takes only its sigil-led shapes there (ForRow has none ⇒ no proj helper
        // for ForRow, unchanged). This keeps the two helpers disjoint (proj runs
        // first, declines, sep handles it) and avoids double-handling the `&`-list.
        let sep_owned = super::forks::SEP_ISOLATION_CATEGORIES.contains(&cat_name);
        if !(sigil_led || (vec_sep_count == 1 && !sep_owned)) {
            continue;
        }
        // Build the Literal / scalar-Operand / SepList skeleton; any `Opt` op or
        // non-`Base`/non-`Vec` (binder/HashBag) param makes the rule NOT a
        // framed-projection shape → skip (monolithic / collection codegen owns it).
        let mut slots: Vec<ProjSlot> = Vec::with_capacity(sp.len());
        let mut operand_count = 0usize;
        let mut shape_ok = true;
        for e in sp.iter() {
            match e {
                SyntaxExpr::Literal(l) => slots.push(ProjSlot::Lit(l.clone())),
                SyntaxExpr::Param(p) => {
                    let cat = tc.iter().find_map(|tp| match tp {
                        TermParam::Simple { name, ty } if name == p => sep_base_ty(ty),
                        _ => None,
                    });
                    match cat {
                        Some(c) if src_idx_of(&c).is_some() => {
                            slots.push(ProjSlot::Operand { category: c });
                            operand_count += 1;
                        }
                        _ => {
                            shape_ok = false;
                            break;
                        }
                    }
                }
                SyntaxExpr::Op(PatternOp::Sep { collection, separator, .. }) => {
                    // Element category = the inner type of the `Vec(elem)` list.
                    let elem_cat = tc.iter().find_map(|tp| match tp {
                        TermParam::Simple {
                            name,
                            ty: TypeExpr::Collection { coll_type: CollectionType::Vec, element },
                        } if name == collection => sep_base_ty(element),
                        _ => None,
                    });
                    // Single-byte ASCII separator (the string split matches one byte).
                    match elem_cat {
                        Some(c)
                            if src_idx_of(&c).is_some()
                                && separator.len() == 1
                                && separator.is_ascii() =>
                        {
                            slots.push(ProjSlot::SepList {
                                element_category: c,
                                separator: separator.clone(),
                            });
                            operand_count += 1;
                        }
                        _ => {
                            shape_ok = false;
                            break;
                        }
                    }
                }
                _ => {
                    shape_ok = false;
                    break;
                }
            }
        }
        if !shape_ok || operand_count == 0 {
            continue;
        }
        variants.push(ProjVariant { label: normalized.label.to_string(), slots });
    }

    if variants.is_empty() {
        return None;
    }
    // Most-specific first: more fixed-literal slots ⇒ earlier (so `@Nil!(q)`
    // beats `@p!(q)`); the semantic-key dedup keeps the min-weight (earliest)
    // representative, matching the monolithic specific-rule preference.
    variants.sort_by(|a, b| {
        let lits = |v: &ProjVariant| {
            v.slots.iter().filter(|s| matches!(s, ProjSlot::Lit(_))).count()
        };
        lits(b).cmp(&lits(a)).then_with(|| a.label.cmp(&b.label))
    });
    Some(ProjIsoShape { result_src_idx, variants })
}

/// The module-scope identifier of the projection-isolation helper for `cat_name`.
pub(crate) fn proj_isolation_helper_ident(cat_name: &str) -> proc_macro2::Ident {
    format_ident!("__mettail_wpda_proj_isolate_all_{}", cat_name)
}

/// The gated `@`-projection isolation shape for `cat_name`: `Some` iff the master
/// switch is ON, the category is in the include set, AND a shape is derivable.
pub(crate) fn projection_iso_shape(
    language: &LanguageDef,
    cat_name: &str,
    categories: &[String],
) -> Option<ProjIsoShape> {
    if super::forks::PROJ_ISOLATION_COMBINE
        && super::forks::PROJ_ISOLATION_CATEGORIES.contains(&cat_name)
    {
        derive_projection_iso_shape(language, cat_name, categories)
    } else {
        None
    }
}

/// Emit the guarded string-entry prologue that calls the projection-isolation
/// helper with the RAW input string (before `lex_dag`). Runtime A/B:
/// `PRATTAIL_NO_PROJ_ISOLATION` forces the monolithic path without a rebuild.
/// Wired BEFORE the sep-isolation prologue (mutually-exclusive by input shape).
pub(crate) fn emit_projection_isolation_prologue(
    helper_name: &proc_macro2::Ident,
    seam: SepSeam,
) -> TokenStream {
    match seam {
        SepSeam::Single => quote! {
            // P1 `@`-PROJECTION ISOLATION prologue (Plan a8b32275) — single winner.
            if std::env::var_os("PRATTAIL_NO_PROJ_ISOLATION").is_none() {
                if let Some((__piso_terms, __piso_weights)) = #helper_name(input) {
                    if let Some((__t, _)) = __piso_terms
                        .into_iter()
                        .zip(__piso_weights.into_iter())
                        .min_by(|(_, __a), (_, __b)| __a.cmp(__b))
                    {
                        return Ok(__t);
                    }
                }
            }
        },
        SepSeam::All => quote! {
            // P1 `@`-PROJECTION ISOLATION prologue (Plan a8b32275) — full alt set.
            if std::env::var_os("PRATTAIL_NO_PROJ_ISOLATION").is_none() {
                if let Some(__piso) = #helper_name(input) {
                    return Ok(__piso);
                }
            }
        },
    }
}

/// Emit the nested per-operand recursion + cartesian construction arm for one
/// projection variant (called from `emit_projection_isolation`). Each operand is
/// sub-parsed via its own `parse_via_wpda_all_with_weights` string entry; the
/// readings are cartesian-combined, ⊗-weighted, and wrapped in the surface ctor.
fn emit_proj_variant_arm(
    cat_ident: &proc_macro2::Ident,
    variant: &ProjVariant,
    variant_idx: usize,
) -> TokenStream {
    let label_ident = format_ident!("{}", variant.label);
    let variant_idx_lit = variant_idx as u16;

    // Emit the runtime skeleton (a slice of `__Slot`) for the matcher. A
    // `SepList` operand extracts the SAME bracket-delimited region as a scalar
    // `Op` (delimited by the next literal); the SPLIT into elements happens in
    // the arm below — so the runtime matcher treats both as `__Slot::Op`.
    let slot_exprs: Vec<TokenStream> = variant
        .slots
        .iter()
        .map(|s| match s {
            ProjSlot::Lit(l) => quote! { __Slot::Lit(#l) },
            ProjSlot::Operand { .. } | ProjSlot::SepList { .. } => quote! { __Slot::Op },
        })
        .collect();

    // Operand-bearing slots in source order (= enum ctor field order). `__ops`
    // (from the matcher) has one range per operand-bearing slot, in this order.
    enum OpKind<'a> {
        Scalar(&'a str),
        Sep { element: &'a str, sep_byte: u8 },
    }
    let op_slots: Vec<OpKind> = variant
        .slots
        .iter()
        .filter_map(|s| match s {
            ProjSlot::Operand { category } => Some(OpKind::Scalar(category)),
            ProjSlot::SepList { element_category, separator } => Some(OpKind::Sep {
                element: element_category,
                sep_byte: separator.as_bytes()[0],
            }),
            ProjSlot::Lit(_) => None,
        })
        .collect();
    let n_ops = op_slots.len();

    let label_str = variant.label.clone();
    // Bind each operand: a `Scalar` sub-parses the whole region; a `Sep` splits
    // the region at the depth-0 separator, sub-parses each element, and cartesian-
    // combines into `Vec<Element>` combos. Both bind a `__op{oi}` : Vec<(value,
    // weight)> where `value` is `Term` (scalar) or `Vec<Element>` (list).
    let mut parse_binds: Vec<TokenStream> = Vec::with_capacity(n_ops);
    for (oi, slot) in op_slots.iter().enumerate() {
        let pairs_id = format_ident!("__op{}", oi);
        match slot {
            OpKind::Scalar(cat) => {
                let ocat = format_ident!("{}", cat);
                let ocat_str = cat.to_string();
                parse_binds.push(quote! {
                    let #pairs_id: Vec<(#ocat, __W)> = {
                        let (__s, __e) = __ops[#oi];
                        let __seg = input[__s..__e].trim();
                        if __GRIND_DIAG {
                            eprintln!("[PISO]   v{} {} op{}:{} scalar seg={:?}",
                                #variant_idx_lit, #label_str, #oi, #ocat_str, __seg);
                        }
                        if __seg.is_empty() { break '__variant; }
                        let (__t, __w) = match #ocat::parse_via_wpda_all_with_weights(__seg) {
                            Ok(__v) => __v,
                            Err(_) => {
                                if __GRIND_DIAG {
                                    eprintln!("[PISO]   v{} {} op{} SUBPARSE-ERR ⇒ decline",
                                        #variant_idx_lit, #label_str, #oi);
                                }
                                break '__variant;
                            }
                        };
                        if __t.is_empty() { break '__variant; }
                        __t.into_iter().zip(__w.into_iter()).collect()
                    };
                });
            }
            OpKind::Sep { element, sep_byte } => {
                let ecat = format_ident!("{}", element);
                let ecat_str = element.to_string();
                let sb = *sep_byte;
                parse_binds.push(quote! {
                    let #pairs_id: Vec<(Vec<#ecat>, __W)> = {
                        let (__s, __e) = __ops[#oi];
                        let __region = input[__s..__e].trim();
                        if __GRIND_DIAG {
                            eprintln!("[PISO]   v{} {} op{}:{}.*sep region={:?}",
                                #variant_idx_lit, #label_str, #oi, #ecat_str, __region);
                        }
                        if __region.is_empty() { break '__variant; }
                        let __rb = __region.as_bytes();
                        let __rn = __rb.len();
                        // Split the region at depth-0 `sep_byte` (bracket-aware).
                        let mut __seg_ranges: Vec<(usize, usize)> = Vec::new();
                        {
                            let mut __depth: i32 = 0;
                            let mut __start = 0usize;
                            let mut __i = 0usize;
                            while __i < __rn {
                                match __rb[__i] {
                                    b'(' | b'[' | b'{' => __depth += 1,
                                    b')' | b']' | b'}' => __depth -= 1,
                                    __c if __depth == 0 && __c == #sb => {
                                        __seg_ranges.push((__start, __i));
                                        __start = __i + 1;
                                    }
                                    _ => {}
                                }
                                __i += 1;
                            }
                            __seg_ranges.push((__start, __rn));
                        }
                        // Isolated per-element re-lex + parse (recurses).
                        let mut __per_seg: Vec<(Vec<#ecat>, Vec<__W>)> =
                            Vec::with_capacity(__seg_ranges.len());
                        for &(__rs, __re) in &__seg_ranges {
                            let __eseg = __region[__rs..__re].trim();
                            if __eseg.is_empty() { break '__variant; }
                            let (__et, __ew) =
                                match #ecat::parse_via_wpda_all_with_weights(__eseg) {
                                    Ok(__v) => __v,
                                    Err(_) => {
                                        if __GRIND_DIAG {
                                            eprintln!("[PISO]   v{} {} op{} SEP-ELEM-ERR seg={:?} ⇒ decline",
                                                #variant_idx_lit, #label_str, #oi, __eseg);
                                        }
                                        break '__variant;
                                    }
                                };
                            if __et.is_empty() { break '__variant; }
                            __per_seg.push((__et, __ew));
                        }
                        // Cartesian combine element readings into `Vec<Element>`.
                        let mut __combos: Vec<(Vec<#ecat>, __W)> =
                            vec![(Vec::new(), <__W as Semiring>::one())];
                        for (__alts, __ws) in &__per_seg {
                            let mut __next: Vec<(Vec<#ecat>, __W)> =
                                Vec::with_capacity(__combos.len() * __alts.len().max(1));
                            for (__pre, __pw) in &__combos {
                                for (__a, __aw) in __alts.iter().zip(__ws.iter()) {
                                    if __next.len() >= __REALIZE_CAP {
                                        // Too many genuine combos to materialize
                                        // here ⇒ decline (monolithic authoritative).
                                        break '__variant;
                                    }
                                    let mut __v = __pre.clone();
                                    __v.push(__a.clone());
                                    __next.push((__v, Semiring::times(__pw, __aw)));
                                }
                            }
                            __combos = __next;
                        }
                        __combos
                    };
                });
            }
        }
        parse_binds.push(quote! {
            if #pairs_id.is_empty() {
                if __GRIND_DIAG {
                    eprintln!("[PISO]   v{} {} op{} EMPTY ⇒ decline",
                        #variant_idx_lit, #label_str, #oi);
                }
                break '__variant;
            }
        });
    }

    // Ctor arg per operand slot: scalar ⇒ `Arc<T>`, list ⇒ `Vec<Element>`.
    let ctor_args: Vec<TokenStream> = op_slots
        .iter()
        .enumerate()
        .map(|(oi, slot)| {
            let a = format_ident!("__a{}", oi);
            match slot {
                OpKind::Scalar(_) => quote! { std::sync::Arc::new(#a.clone()) },
                OpKind::Sep { .. } => quote! { #a.clone() },
            }
        })
        .collect();
    // ⊗ (times) fold of the per-operand weights + the framing weight.
    let mut weight_expr = quote! { __framing };
    for oi in 0..n_ops {
        let wa = format_ident!("__wa{}", oi);
        weight_expr = quote! { Semiring::times(&#weight_expr, #wa) };
    }
    let mut body = quote! {
        if __candidates.len() >= __REALIZE_CAP {
            return None;
        }
        let __framing = __W::from_cost(0.0, __RESULT_SRC_IDX, #variant_idx_lit);
        __candidates.push((
            #cat_ident::#label_ident( #(#ctor_args),* ),
            #weight_expr,
        ));
    };
    // Nest the loops from innermost (last operand) outward. Each `__op{oi}` is a
    // Vec<(value, weight)>; `__a{oi}` binds the value, `__wa{oi}` the weight.
    for oi in (0..n_ops).rev() {
        let a = format_ident!("__a{}", oi);
        let wa = format_ident!("__wa{}", oi);
        let pairs_id = format_ident!("__op{}", oi);
        body = quote! {
            for (#a, #wa) in #pairs_id.iter() {
                #body
            }
        };
    }

    quote! {
        {
            // Match this variant's skeleton; extract operand ranges.
            const __SKEL: &[__Slot] = &[ #(#slot_exprs),* ];
            '__variant: {
                let Some(__ops) = __proj_skeleton_match(__bytes, __n, __SKEL) else {
                    if __GRIND_DIAG {
                        eprintln!("[PISO]   v{} {} SKEL no-match", #variant_idx_lit, #label_str);
                    }
                    break '__variant;
                };
                if __GRIND_DIAG {
                    eprintln!("[PISO]   v{} {} SKEL matched ops={:?}",
                        #variant_idx_lit, #label_str, __ops);
                }
                #(#parse_binds)*
                #body
            }
        }
    }
}

/// Emit the shared per-category STRING-level projection-isolation helper
/// `__mettail_wpda_proj_isolate_all_<Cat>(input: &str)`.
///
/// It matches each σ-led frame-variant's grammar-derived skeleton against the raw
/// input, extracts each cross-cat operand by a bracket-depth scan, sub-parses each
/// through the OPERAND category's own `parse_via_wpda_all_with_weights` string
/// entry (fresh lex + walker from ROOT — RECURSES through this prologue), wraps the
/// cartesian-combined readings in the surface enum ctor, then dedups by semantic
/// key + ⊕-min + weight-sort (mirroring the monolithic `_all` finalize). `None` ⇒
/// NOT-APPLICABLE (no σ / no variant matches) or ANY sub-parse failure ⇒ the caller
/// falls through to the UNMODIFIED monolithic body (byte-identical — RT-4).
fn emit_projection_isolation(cat_ident: &proc_macro2::Ident, shape: &ProjIsoShape) -> TokenStream {
    let helper_name = proj_isolation_helper_ident(&cat_ident.to_string());
    let result_src_idx = shape.result_src_idx;
    let variant_arms: Vec<TokenStream> = shape
        .variants
        .iter()
        .enumerate()
        .map(|(vi, v)| emit_proj_variant_arm(cat_ident, v, vi))
        .collect();

    quote! {
        /// P1 `@`-PROJECTION ISOLATION+COMBINE (Plan a8b32275): STRING-level
        /// divide-and-conquer `@`-projection linearizer for the `#cat_ident`
        /// category. See `emit_projection_isolation` in the macro for the
        /// full rationale.
        #[allow(
            non_snake_case,
            unused_assignments,
            unused_variables,
            clippy::needless_range_loop,
            clippy::manual_is_ascii_check
        )]
        fn #helper_name(
            input: &str,
        ) -> Option<(
            Vec<#cat_ident>,
            Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
        )> {
            use mettail_prattail::automata::semiring::Semiring;
            type __W = mettail_prattail::automata::lex_weight::LexicographicWeight;
            const __REALIZE_CAP: usize = 64;
            const __RESULT_SRC_IDX: u16 = #result_src_idx;
            // Throwaway runtime diagnostic gate (env `GRIND_DIAG`); zero-cost when
            // unset. Traces helper entry, per-variant skeleton match, per-operand
            // sub-parse segment, and the return disposition.
            let __GRIND_DIAG = std::env::var_os("GRIND_DIAG").is_some();

            // One skeleton slot: a fixed literal token or a cross-cat operand hole.
            enum __Slot {
                Lit(&'static str),
                Op,
            }
            fn __is_word(c: u8) -> bool {
                c.is_ascii_alphanumeric() || c == b'_'
            }
            /// Match `skel` against `bytes[0..n]`, returning the byte-range of each
            /// `Op` slot, or `None` if the skeleton does not match. Operands are
            /// delimited by the NEXT literal at bracket-depth 0 (standard ASCII
            /// brackets `([{`/`)]}`; multi-char collection delimiters balance via
            /// their `{`/`}` component). A depth-0 close that is NOT the delimiter
            /// ⇒ unbalanced ⇒ `None` (this variant does not match).
            fn __proj_skeleton_match(
                bytes: &[u8],
                n: usize,
                skel: &[__Slot],
            ) -> Option<Vec<(usize, usize)>> {
                let mut i = 0usize;
                let mut ops: Vec<(usize, usize)> = Vec::new();
                let mut k = 0usize;
                while k < skel.len() {
                    while i < n && bytes[i].is_ascii_whitespace() {
                        i += 1;
                    }
                    match &skel[k] {
                        __Slot::Lit(l) => {
                            let lb = l.as_bytes();
                            if i + lb.len() > n || &bytes[i..i + lb.len()] != lb {
                                return None;
                            }
                            if lb.iter().all(|&c| __is_word(c)) {
                                let before_ok = i == 0 || !__is_word(bytes[i - 1]);
                                let after_ok =
                                    i + lb.len() == n || !__is_word(bytes[i + lb.len()]);
                                if !(before_ok && after_ok) {
                                    return None;
                                }
                            }
                            i += lb.len();
                            k += 1;
                        }
                        __Slot::Op => {
                            // The delimiter = the next literal slot's text (if any).
                            let next_lit: Option<&'static str> =
                                skel[k + 1..].iter().find_map(|s| match s {
                                    __Slot::Lit(l) => Some(*l),
                                    __Slot::Op => None,
                                });
                            let start = i;
                            match next_lit {
                                None => {
                                    // Last slot: operand runs to end of input.
                                    ops.push((start, n));
                                    i = n;
                                    k += 1;
                                }
                                Some(l) => {
                                    let lb = l.as_bytes();
                                    let identish = lb.iter().all(|&c| __is_word(c));
                                    let mut depth: i32 = 0;
                                    let mut j = start;
                                    let mut found: Option<usize> = None;
                                    while j < n {
                                        let c = bytes[j];
                                        // Depth-0 delimiter match (checked BEFORE
                                        // adjusting depth for this char, so a close
                                        // bracket delimiter matches at its own pos).
                                        if depth == 0
                                            && j + lb.len() <= n
                                            && &bytes[j..j + lb.len()] == lb
                                        {
                                            let wb = !identish
                                                || ((j == 0 || !__is_word(bytes[j - 1]))
                                                    && (j + lb.len() == n
                                                        || !__is_word(bytes[j + lb.len()])));
                                            if wb {
                                                found = Some(j);
                                                break;
                                            }
                                        }
                                        match c {
                                            b'(' | b'[' | b'{' => depth += 1,
                                            b')' | b']' | b'}' => {
                                                if depth == 0 {
                                                    // Unbalanced close before the
                                                    // delimiter ⇒ no match.
                                                    return None;
                                                }
                                                depth -= 1;
                                            }
                                            _ => {}
                                        }
                                        j += 1;
                                    }
                                    let end = found?;
                                    ops.push((start, end));
                                    i = end;
                                    // Advance PAST this `Op` slot so the next
                                    // iteration matches the delimiter `Lit` slot
                                    // (which sits at `bytes[end..]`). Without this
                                    // increment, `k` would stay on the `Op` slot,
                                    // re-scan from `i = end`, immediately re-find the
                                    // delimiter at position `end` (a zero-width
                                    // operand), and loop forever — the hang that
                                    // afflicts every non-trailing operand (`Op`
                                    // followed by more `Lit`/`Op` slots).
                                    k += 1;
                                }
                            }
                        }
                    }
                }
                // The whole input must be consumed (a `_all` entry is total).
                while i < n && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }
                if i != n {
                    return None;
                }
                Some(ops)
            }

            let input = input.trim();
            let __bytes = input.as_bytes();
            let __n = __bytes.len();
            if __n == 0 {
                return None;
            }
            if __GRIND_DIAG {
                eprintln!(
                    "[PISO] ENTER {} n={} input={:?}",
                    stringify!(#cat_ident), __n, input,
                );
            }

            let mut __candidates: Vec<(#cat_ident, __W)> = Vec::new();
            #(#variant_arms)*

            if __candidates.is_empty() {
                if __GRIND_DIAG {
                    eprintln!(
                        "[PISO] RETURN None {} input={:?} (no variant produced a reading ⇒ fall through to monolithic)",
                        stringify!(#cat_ident), input,
                    );
                }
                return None;
            }
            if __GRIND_DIAG {
                eprintln!(
                    "[PISO] {} input={:?} raw_candidates={}",
                    stringify!(#cat_ident), input, __candidates.len(),
                );
            }

            // FINALIZE like the monolithic `_all`: dedup by semantic key,
            // ⊕-min representative, weight-sort.
            let mut __seen: std::collections::HashMap<Vec<u8>, usize> =
                std::collections::HashMap::with_capacity(__candidates.len());
            let mut __out_terms: Vec<#cat_ident> = Vec::new();
            let mut __out_weights: Vec<__W> = Vec::new();
            for (__term, __w) in __candidates {
                let __key = {
                    let mut __h = __MettailWpdaSemanticKeyHasher::default();
                    __term.semantic_hash(&mut __h);
                    __h.into_key()
                };
                if let Some(&__idx) = __seen.get(&__key) {
                    if __w < __out_weights[__idx] {
                        __out_terms[__idx] = __term;
                        __out_weights[__idx] = __w;
                    }
                } else {
                    __seen.insert(__key, __out_terms.len());
                    __out_terms.push(__term);
                    __out_weights.push(__w);
                }
            }
            let mut __paired: Vec<_> =
                __out_terms.into_iter().zip(__out_weights.into_iter()).collect();
            __paired.sort_by(|(_, __a), (_, __b)| __a.cmp(__b));
            let (__out_terms, __out_weights): (Vec<_>, Vec<_>) = __paired.into_iter().unzip();
            if __GRIND_DIAG {
                eprintln!(
                    "[PISO] RETURN Some {} input={:?} readings={}",
                    stringify!(#cat_ident), input, __out_terms.len(),
                );
            }
            Some((__out_terms, __out_weights))
        }
    }
}

/// Emit per-category `parse_<Cat>_via_wpda` wrappers plus the shared
/// `WpdaParseError` type.
pub(crate) fn emit_parse_fns(
    language: &LanguageDef,
    categories: &[String],
    engine_ident: &proc_macro2::Ident,
) -> TokenStream {
    let mut fns = Vec::new();
    for (cat_src_idx, cat_name) in categories.iter().enumerate() {
        let cat_ident = format_ident!("{}", cat_name);
        let fn_name = format_ident!("parse_{}_via_wpda", cat_name);
        let recovering_fn_name = format_ident!("parse_{}_via_wpda_recovering", cat_name);
        let with_weight_fn_name = format_ident!("parse_{}_via_wpda_with_weight", cat_name);
        let with_source_fn_name = format_ident!("parse_{}_via_wpda_with_source", cat_name);
        // M8 (2026-05-14): multi-result entry points. `_all_with_source`
        // takes `&dyn WpdaTokenSource` (slice OR lattice) and returns
        // every accepted term from the walker's `WpdaResolveResult::Accepted`
        // vec. `_all` is a `SliceTokenSource` wrapper for backward compat.
        let all_with_source_fn_name = format_ident!("parse_{}_via_wpda_all_with_source", cat_name);
        let all_with_source_bounded_fn_name =
            format_ident!("parse_{}_via_wpda_all_with_source_and_bounding_mode", cat_name);
        let prefix_with_source_fn_name =
            format_ident!("parse_{}_via_wpda_prefix_with_source", cat_name);
        let prefix_with_source_bounded_fn_name =
            format_ident!("parse_{}_via_wpda_prefix_with_source_and_bounding_mode", cat_name);
        let prefix_fn_name = format_ident!("parse_{}_via_wpda_prefix", cat_name);
        let surface_exact_with_source_fn_name =
            format_ident!("parse_{}_via_wpda_surface_exact_with_source", cat_name);
        let surface_exact_fn_name = format_ident!("parse_{}_via_wpda_surface_exact", cat_name);
        let all_fn_name = format_ident!("parse_{}_via_wpda_all", cat_name);
        let cat_src_idx_u16 = cat_src_idx as u16;

        // ── P2 ISOLATION+COMBINE (Plan a7986200, 2026-07-05) ──
        //
        // When this category is an isolation-enabled `.*sep` shape, emit the
        // module-scope STRING-level helper `__mettail_wpda_sep_isolate_all_<Cat>`.
        // The guarded PROLOGUES that call it live at the STRING parse entries
        // (`Cat::parse_via_wpda` / `Cat::parse_via_wpda_all_with_weights` in
        // `gen/mod.rs`) — that is where the raw input string (not the ambiguous
        // post-lex LATTICE) is available. OFF / not-in-set / no-shape ⇒ empty ⇒
        // BYTE-IDENTICAL.
        let sep_helper_fns = match sep_isolation_shape(language, cat_name, categories) {
            Some(shape) => emit_sep_isolation(&cat_ident, &shape),
            None => quote! {},
        };

        // ── P1 `@`-PROJECTION ISOLATION+COMBINE (Plan a8b32275, 2026-07-05) ──
        //
        // The SIBLING of the `.*sep` helper above: when this category is an
        // isolation-enabled `@`-projection shape, emit the module-scope helper
        // `__mettail_wpda_proj_isolate_all_<Cat>`. Its guarded PROLOGUES live at
        // the same STRING parse entries (`gen/mod.rs`), wired BEFORE the sep
        // prologue (mutually-exclusive by input shape). OFF / not-in-set /
        // no-shape ⇒ empty ⇒ BYTE-IDENTICAL.
        let proj_helper_fns = match projection_iso_shape(language, cat_name, categories) {
            Some(shape) => emit_projection_isolation(&cat_ident, &shape),
            None => quote! {},
        };

        // ── ROOT2_DRIVER_FALLTHROUGH (2026-07-04, session da0842dc) ──
        //
        // Three kill-switch-gated token streams interpolated into the
        // single-result `parse_<Cat>_via_wpda_with_source` facade. When the
        // const is OFF the emitted body is the EXACT pre-edit shape
        // (byte-identical); when ON it factors the `AcceptedWithTrailing` retry
        // into `__mettail_wpda_exhaustive_retry` and adds the demand-`Accepted`
        // `None` fall-through that calls it.
        let root2_fallthrough_on = super::forks::ROOT2_DRIVER_FALLTHROUGH;

        // (1) The factored helper — emitted ONLY when ON. Its body is the exact
        //     (pre-edit) inlined `AcceptedWithTrailing` retry.
        let exhaustive_retry_helper: TokenStream = if root2_fallthrough_on {
            quote! {
                // The EXACT body of the historical `AcceptedWithTrailing` retry
                // (a fresh `WpdaWalker::new_for_category` with
                // `max_recovery_depth = 0`, the EXHAUSTIVE
                // `run_to_end_of_input_env_aware` driver, resolve, and the M6
                // min-weight realize-select over all 5 `WpdaResolveResult`
                // variants). BOTH the `AcceptedWithTrailing` arm AND the new
                // demand-`Accepted`-`None` fall-through arm call it (dedups
                // ~60 lines — Boy-Scout). It sets `*pos` and returns the
                // single-result `(term, weight)` OR the mapped error.
                //
                // The demand driver
                // (`run_to_end_of_input_until_accepting_env_aware`) EARLY-STOPS
                // on a category-correct but UNREALIZABLE accepting root (ROOT
                // aa8ab54d), yielding a `None` M6-select → `EmptyResult`. The
                // EXHAUSTIVE driver here explores the alternatives and realizes
                // the canonical term (e.g. `(@a!!(Nil))` →
                // `PPersistOutputShort`). Genuine-invalid surfaces still error
                // (the exhaustive pass realizes no root → `EmptyResult`), so no
                // spurious parse is fabricated (FV T4).
                //
                // NOTE: nested `fn` item — does NOT inherit the enclosing body's
                // `use`/`type DW`, so every path is fully qualified.
                #[allow(non_snake_case)]
                fn __mettail_wpda_exhaustive_retry(
                    source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                    pos: &mut usize,
                    min_bp: u8,
                    max_steps: usize,
                ) -> Result<
                    (
                        #cat_ident,
                        mettail_prattail::automata::lex_weight::LexicographicWeight,
                    ),
                    WpdaParseError,
                > {
                    use mettail_prattail::wpda_runtime::WpdaResolveResult;
                    use mettail_prattail::wpda_walker::WpdaWalker;
                    type __DW = mettail_prattail::automata::lex_weight::LexicographicWeight;
                    let mut walker = WpdaWalker::<__DW, _>::new_for_category(
                        #engine_ident::default(),
                        #cat_src_idx_u16,
                        min_bp,
                    );
                    let mut recovery_config =
                        mettail_prattail::recovery::RecoveryConfig::default();
                    recovery_config.max_recovery_depth = 0;
                    walker.set_recovery_config(recovery_config);
                    match walker.run_to_end_of_input_env_aware(max_steps, source) {
                        Ok(()) => match walker.resolve_at_end_of_input(source) {
                            WpdaResolveResult::Accepted { roots, .. } => {
                                *pos = walker.position();
                                // M6 realize-selection belt: iterate all
                                // full-span roots + global min-weight that
                                // actually realizes.
                                let (term, dw) =
                                    __mettail_wpda_select_min_weight_realizing(&walker, &roots)
                                        .ok_or(WpdaParseError::EmptyResult)?;
                                let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                    .map_err(|_| WpdaParseError::EmptyResult)?;
                                let typed = std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone());
                                Ok((typed, dw))
                            }
                            WpdaResolveResult::AcceptedWithTrailing {
                                roots,
                                position,
                                ..
                            } => {
                                *pos = position;
                                // M6 realize-selection belt (see helper above).
                                let (term, dw) =
                                    __mettail_wpda_select_min_weight_realizing(&walker, &roots)
                                        .ok_or(WpdaParseError::EmptyResult)?;
                                let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                    .map_err(|_| WpdaParseError::EmptyResult)?;
                                let typed = std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone());
                                Ok((typed, dw))
                            }
                            WpdaResolveResult::ParseError { message, position } => {
                                Err(WpdaParseError::ParseFailed {
                                    message,
                                    position,
                                    attempts: Vec::new(),
                                })
                            }
                            WpdaResolveResult::MaxStepsExceeded { position } => {
                                Err(WpdaParseError::Incomplete { position })
                            }
                            WpdaResolveResult::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 } => {
                                Err(WpdaParseError::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 })
                            }
                        },
                        Err(exceeded) => Err(WpdaParseError::Incomplete {
                            position: exceeded.position,
                        }),
                    }
                }
            }
        } else {
            quote! {}
        };

        // (2) The demand-`Accepted` arm body. OFF = the pre-edit unconditional
        //     `.ok_or(EmptyResult)?`. ON = Some(verbatim common path) / None
        //     (fall through to the exhaustive retry). Env
        //     `PRATTAIL_NO_ROOT2_FALLTHROUGH` forces the OFF behavior at
        //     RUNTIME (re-exposes the demand-driver defect without a rebuild).
        let accepted_arm_body: TokenStream = if root2_fallthrough_on {
            quote! {
                match __mettail_wpda_select_min_weight_realizing(&walker, &roots) {
                    // Common path — BYTE-IDENTICAL to the pre-edit behavior.
                    Some((term, dw)) => {
                        let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                            .map_err(|_| WpdaParseError::EmptyResult)?;
                        let typed = std::sync::Arc::try_unwrap(arc)
                            .unwrap_or_else(|arc| (*arc).clone());
                        Ok((typed, dw))
                    }
                    // Fall-through: the demand driver early-stopped on a
                    // category-correct but UNREALIZABLE accepting root (ROOT
                    // aa8ab54d). Re-run the EXHAUSTIVE driver + M6 select. The
                    // `None` arm is reached IFF the demand M6-select returned
                    // `None` — EXACTLY today's unconditional `EmptyResult` — so
                    // the common path is untouched.
                    None => {
                        if std::env::var_os("PRATTAIL_NO_ROOT2_FALLTHROUGH").is_some() {
                            // Runtime A/B: reproduce the pre-fix behavior.
                            return Err(WpdaParseError::EmptyResult);
                        }
                        __mettail_wpda_exhaustive_retry(source, pos, min_bp, MAX_STEPS)
                    }
                }
            }
        } else {
            // Pre-edit shape — byte-identical.
            quote! {
                let (term, dw) =
                    __mettail_wpda_select_min_weight_realizing(&walker, &roots)
                        .ok_or(WpdaParseError::EmptyResult)?;
                let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                    .map_err(|_| WpdaParseError::EmptyResult)?;
                let typed = std::sync::Arc::try_unwrap(arc)
                    .unwrap_or_else(|arc| (*arc).clone());
                Ok((typed, dw))
            }
        };

        // (3) The `AcceptedWithTrailing` arm body. OFF = the pre-edit inlined
        //     retry (byte-identical). ON = a call to the factored helper (same
        //     behavior). `MAX_STEPS` and `min_bp`/`source`/`pos` are in scope.
        let accepted_with_trailing_arm_body: TokenStream = if root2_fallthrough_on {
            quote! {
                __mettail_wpda_exhaustive_retry(source, pos, min_bp, MAX_STEPS)
            }
        } else {
            // Pre-edit shape — byte-identical.
            quote! {
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut recovery_config =
                    mettail_prattail::recovery::RecoveryConfig::default();
                recovery_config.max_recovery_depth = 0;
                walker.set_recovery_config(recovery_config);
                match walker.run_to_end_of_input_env_aware(MAX_STEPS, source) {
                    Ok(()) => match walker.resolve_at_end_of_input(source) {
                        WpdaResolveResult::Accepted { roots, .. } => {
                            *pos = walker.position();
                            let (term, dw) =
                                __mettail_wpda_select_min_weight_realizing(&walker, &roots)
                                    .ok_or(WpdaParseError::EmptyResult)?;
                            let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                .map_err(|_| WpdaParseError::EmptyResult)?;
                            let typed = std::sync::Arc::try_unwrap(arc)
                                .unwrap_or_else(|arc| (*arc).clone());
                            Ok((typed, dw))
                        }
                        WpdaResolveResult::AcceptedWithTrailing {
                            roots,
                            position,
                            ..
                        } => {
                            *pos = position;
                            let (term, dw) =
                                __mettail_wpda_select_min_weight_realizing(&walker, &roots)
                                    .ok_or(WpdaParseError::EmptyResult)?;
                            let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                .map_err(|_| WpdaParseError::EmptyResult)?;
                            let typed = std::sync::Arc::try_unwrap(arc)
                                .unwrap_or_else(|arc| (*arc).clone());
                            Ok((typed, dw))
                        }
                        WpdaResolveResult::ParseError { message, position } => {
                            Err(WpdaParseError::ParseFailed {
                                message,
                                position,
                                attempts: Vec::new(),
                            })
                        }
                        WpdaResolveResult::MaxStepsExceeded { position } => {
                            Err(WpdaParseError::Incomplete { position })
                        }
                        WpdaResolveResult::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 } => {
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 })
                        }
                    },
                    Err(exceeded) => Err(WpdaParseError::Incomplete {
                        position: exceeded.position,
                    }),
                }
            }
        };

        fns.push(quote! {
            // P2 ISOLATION+COMBINE (Plan a7986200): the per-category
            // `__mettail_wpda_sep_isolate_all_<Cat>` helper (+ its specialized
            // constructor arms). Emitted ONLY when this category is a `.*sep`
            // category in `SEP_ISOLATION_CATEGORIES`; empty otherwise.
            #sep_helper_fns

            // P1 `@`-PROJECTION ISOLATION+COMBINE (Plan a8b32275): the per-category
            // `__mettail_wpda_proj_isolate_all_<Cat>` helper. Emitted ONLY when this
            // category is an `@`-projection category in `PROJ_ISOLATION_CATEGORIES`;
            // empty otherwise.
            #proj_helper_fns

            /// WPDS-runtime parser for the `#cat_ident` category.
            ///
            /// Runs the walker to saturation and extracts the resulting AST
            /// term with recovery disabled. Use
            /// `parse_<Cat>_via_wpda_recovering` when repair attempts should
            /// be part of the result surface.
            #[allow(non_snake_case)]
            pub fn #fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<#cat_ident, WpdaParseError> {
                #with_weight_fn_name(kinds, texts, pos, min_bp).map(|(term, _)| term)
            }

            /// Source-generic WPDS parser variant that returns the walker's
            /// terminal weight alongside the parse result.
            ///
            /// Does NOT apply recovery — a clean accept yields
            /// `Ok((term, weight))`; any non-Accepted termination yields
            /// `Err(WpdaParseError)` without retries. Use
            /// `parse_<Cat>_via_wpda_recovering` when sync-token skip
            /// recovery is desired.
            #[allow(non_snake_case)]
            pub fn #with_source_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<
                (
                    #cat_ident,
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                ),
                WpdaParseError,
            > {
                use mettail_prattail::wpda_runtime::WpdaResolveResult;
                use mettail_prattail::wpda_walker::WpdaWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                // Phase 3.1.7 (C10, 2026-05-15): walker W reverted from
                // M11's DerivationWeight<...> multiset to plain
                // LexicographicWeight. The SPPF arena carries derivation
                // ambiguity (Tomita 1986 §6.3 / Scott-Johnstone 2010 §3 —
                // SPPF is a set of derivations with structural dedup);
                // W carries only the cursor-merge path-cost tiebreak.
                // Public return type reverts to (Cat, LexicographicWeight)
                // — the M11.6b D5 break is undone.
                use mettail_prattail::automata::semiring::SemiringRef;
                type DW = LexicographicWeight;

                // M6 realize-selection belt (2026-07-04, session da0842dc):
                // choose the single-result representative by iterating ALL
                // full-span accepting roots (they are full-span by
                // construction), realizing each, and returning the GLOBAL
                // min-weight `(term, weight)` among all realizing roots — not
                // just `roots.first()`.
                //
                // WHY (root-caused, Stage-0 measured — $SCRATCH/M6_STAGE0_FINDINGS.md):
                // committing to `roots.first()` (or even the min-weight root at
                // the fixed cap 128) is UNSOUND for a class of full-span roots
                // whose SPPF carries a self-cyclic packing (e.g. an @-first
                // polyadic bind-LHS `@a,b<-c` cross-cat re-entry). At the fixed
                // raw-probe cap 128 the LAZY realizer descends into the cyclic
                // packing and aborts (`RealizeLazyAbort::Cycle`); the EAGER
                // fallback's Tarjan/Newton cycle-discard then yields ZERO terms
                // for that SPPF — even though a SMALLER cap stops after the
                // first (correct, token-sound, min-weight) packing and realizes
                // the ORIGINAL term (measured: cap=1 → the correct term;
                // cap>=2 → 0; roundtrip-idempotent).
                //
                // So per root we probe a DESCENDING cap ladder [128,64,…,1] and
                // take the FIRST cap that yields >=1 term for THAT root. This is
                // INERT on the common path: cap 128 is tried first, so any root
                // that already realizes at 128 (every currently-passing input)
                // is byte-identical (same term, same weight, same min-weight
                // winner). The ladder is reached ONLY when the fixed cap yields
                // 0 for a root, exactly the cyclic-SPPF parse-gap. Preserves the
                // existing min-weight disambiguation (LexicographicWeight ⊕ is
                // lex-min; the winner is the global min over all realizing
                // roots). GENERAL: no per-category/per-language special-casing.
                //
                // Mirrors `__mettail_wpda_find_surface_exact` below, which
                // already iterates all accepted SPPF roots.
                // NOTE: this is a nested `fn` item — it does NOT inherit the
                // enclosing body's `use`/`type DW` — so every path is fully
                // qualified.
                fn __mettail_wpda_select_min_weight_realizing(
                    walker: &mettail_prattail::wpda_walker::WpdaWalker<
                        mettail_prattail::automata::lex_weight::LexicographicWeight,
                        #engine_ident,
                    >,
                    roots: &[mettail_prattail::sppf::SppfId],
                ) -> Option<(
                    std::sync::Arc<dyn std::any::Any + Send + Sync>,
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                )> {
                    type __W = mettail_prattail::automata::lex_weight::LexicographicWeight;
                    // The facade's historical single-result raw-probe cap. The
                    // ladder descends from here so the common path is
                    // byte-identical.
                    const RAW_PROBE_CAPS: &[usize] = &[128, 64, 32, 16, 8, 4, 2, 1];
                    // Kill-switch / A-B control: `PRATTAIL_NO_M6_SELECT=1`
                    // reproduces the PRE-M6 behavior EXACTLY — commit to
                    // `roots.first()` and realize it once at the fixed cap 128,
                    // taking that root's min-weight term. Used to prove the M6
                    // belt is causal for the polyadic-forrow parse-gap and inert
                    // elsewhere. Default (unset) = the M6 belt.
                    if std::env::var_os("PRATTAIL_NO_M6_SELECT").is_some() {
                        let root = roots.first().copied()?;
                        return walker
                            .realize_root_to_terms_with_weights(root, Some(128))
                            .into_iter()
                            .min_by(|(_, a), (_, b)| a.cmp(b));
                    }
                    let mut best: Option<(std::sync::Arc<dyn std::any::Any + Send + Sync>, __W)> = None;
                    for &root in roots {
                        // First cap that ACTUALLY realizes this root wins for
                        // this root; its own min-weight term is the candidate.
                        let mut per_root: Option<(std::sync::Arc<dyn std::any::Any + Send + Sync>, __W)> = None;
                        for &cap in RAW_PROBE_CAPS {
                            let realized = walker.realize_root_to_terms_with_weights(root, Some(cap));
                            if let Some((term, w)) = realized
                                .into_iter()
                                .min_by(|(_, a), (_, b)| a.cmp(b))
                            {
                                per_root = Some((term, w));
                                break;
                            }
                        }
                        if let Some((term, w)) = per_root {
                            let take = match &best {
                                None => true,
                                Some((_, bw)) => w.cmp(bw) == std::cmp::Ordering::Less,
                            };
                            if take {
                                best = Some((term, w));
                            }
                        }
                    }
                    best
                }

                // ROOT2_DRIVER_FALLTHROUGH (2026-07-04, session da0842dc): the
                // factored EXHAUSTIVE retry helper (emitted ONLY when the
                // kill-switch const is ON — byte-identical OFF). See
                // `#exhaustive_retry_helper` construction below.
                #exhaustive_retry_helper

                // Stage 6 G6+ (2026-05-02): default 1M; PRATTAIL_MAX_STEPS env
                // var overrides via the env-aware runner. The single-result
                // facade is demand-sensitive: it stops once a live accepting
                // root for this category exists. Exhaustive callers below use
                // the full EOI driver.
                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut recovery_config = mettail_prattail::recovery::RecoveryConfig::default();
                recovery_config.max_recovery_depth = 0;
                walker.set_recovery_config(recovery_config);
                match walker.run_to_end_of_input_until_accepting_env_aware(MAX_STEPS, source) {
                    Ok(()) => match walker.resolve_at_end_of_input(source) {
                        WpdaResolveResult::Accepted { roots, .. } => {
                            *pos = walker.position();
                            // Single-result representative extraction stays
                            // bounded and lazy, but no longer depends on SPPF
                            // packing insertion order NOR on `roots.first()`.
                            // Iterate ALL full-span accepting roots and choose
                            // the global min-weight term that ACTUALLY realizes
                            // (M6 realize-selection belt above); ambiguity-
                            // preserving callers still use the `_all`/`_prefix`
                            // APIs.
                            #accepted_arm_body
                        }
                        // Demand-sensitive parsing can discover a valid
                        // prefix before slower alternatives have produced a
                        // full-input root. Full `parse()` semantics require
                        // exhausting those alternatives before reporting
                        // trailing tokens, so retry with the ordinary EOI
                        // driver. If the exhaustive pass still resolves as
                        // trailing, return the prefix term + weight and set
                        // `*pos` to the prefix boundary so the generated
                        // wrapper's `pos < tokens.len()` check emits a
                        // structured `TrailingTokens` error.
                        WpdaResolveResult::AcceptedWithTrailing {
                            ..
                        } => {
                            #accepted_with_trailing_arm_body
                        }
                        WpdaResolveResult::ParseError { message, position } => {
                            Err(WpdaParseError::ParseFailed {
                                message,
                                position,
                                attempts: Vec::new(),
                            })
                        }
                        WpdaResolveResult::MaxStepsExceeded { position } => {
                            Err(WpdaParseError::Incomplete { position })
                        }
                        WpdaResolveResult::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 } => {
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 })
                        }
                    },
                    Err(exceeded) => Err(WpdaParseError::Incomplete {
                        position: exceeded.position,
                    }),
                }
            }

            /// L8 (2026-04-28): WPDS parser variant that returns the walker's
            /// terminal weight alongside the parse result. The weight's
            /// `primary` field carries the path's accumulated tropical cost;
            /// `parse_with_confidence` exposes this as a confidence score
            /// `exp(-cost)` ∈ (0, 1].
            ///
            /// This slice wrapper preserves the existing public ABI; callers
            /// that need lexical alternatives use `parse_<Cat>_via_wpda_with_source`
            /// with a `LatticeTokenSource`.
            #[allow(non_snake_case)]
            pub fn #with_weight_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<
                (
                    #cat_ident,
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                ),
                WpdaParseError,
            > {
                let src = mettail_prattail::wpda_runtime::SliceTokenSource::with_texts(
                    kinds, texts,
                );
                #with_source_fn_name(&src, pos, min_bp)
            }

            /// Source-generic raw-realization probe for surface-faithful
            /// single-result representative selection.
            ///
            /// The semantic prefix/all facades intentionally collapse
            /// transparent wrappers by `semantic_hash`. This helper is the
            /// complementary policy for `Cat::parse`: it walks raw SPPF
            /// derivations lazily and fairly across accepted SPPF roots,
            /// returning the first realized term whose Display exactly
            /// reproduces already-observed source text. It does not reject,
            /// reorder, or discard any ambiguity in the public
            /// ambiguity-preserving APIs.
            #[allow(non_snake_case)]
            pub fn #surface_exact_with_source_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
                expected_display: &str,
                max_raw_derivations: usize,
            ) -> Result<
                Option<(
                    #cat_ident,
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                )>,
                WpdaParseError,
            > {
                use mettail_prattail::wpda_runtime::WpdaResolveResult;
                use mettail_prattail::wpda_walker::WpdaWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                type DW = LexicographicWeight;

                if max_raw_derivations == 0 {
                    return Ok(None);
                }

                fn __mettail_wpda_find_surface_exact(
                    walker: &WpdaWalker<DW, #engine_ident>,
                    roots: &[mettail_prattail::sppf::SppfId],
                    expected_display: &str,
                    max_raw_derivations: usize,
                ) -> Result<
                    Option<(#cat_ident, mettail_prattail::automata::lex_weight::LexicographicWeight)>,
                    WpdaParseError,
                > {
                    const INITIAL_RAW_SURFACE_PROBE_LIMIT: usize = 128;
                    let mut per_root_limit =
                        max_raw_derivations.min(INITIAL_RAW_SURFACE_PROBE_LIMIT).max(1);
                    loop {
                        let mut exhausted_all_roots = true;
                        for &root in roots {
                            let realized =
                                walker.realize_root_to_terms_with_weights(root, Some(per_root_limit));
                            if realized.len() >= per_root_limit {
                                exhausted_all_roots = false;
                            }
                            for (term, weight) in realized.into_iter() {
                                let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                    .map_err(|_| WpdaParseError::EmptyResult)?;
                                let typed = std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone());
                                if format!("{}", typed) == expected_display {
                                    return Ok(Some((typed, weight)));
                                }
                            }
                        }
                        if exhausted_all_roots || per_root_limit >= max_raw_derivations {
                            return Ok(None);
                        }
                        per_root_limit =
                            per_root_limit.saturating_mul(4).min(max_raw_derivations);
                    }
                }

                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut recovery_config = mettail_prattail::recovery::RecoveryConfig::default();
                recovery_config.max_recovery_depth = 0;
                walker.set_recovery_config(recovery_config);
                match walker.run_to_end_of_input_env_aware(MAX_STEPS, source) {
                    Ok(()) => match walker.resolve_at_end_of_input(source) {
                        WpdaResolveResult::Accepted { roots, .. } => {
                            *pos = walker.position();
                            __mettail_wpda_find_surface_exact(
                                &walker,
                                &roots,
                                expected_display,
                                max_raw_derivations,
                            )
                        }
                        WpdaResolveResult::AcceptedWithTrailing {
                            roots, position, ..
                        } => {
                            *pos = position;
                            __mettail_wpda_find_surface_exact(
                                &walker,
                                &roots,
                                expected_display,
                                max_raw_derivations,
                            )
                        }
                        WpdaResolveResult::ParseError { message, position } => {
                            Err(WpdaParseError::ParseFailed {
                                message,
                                position,
                                attempts: Vec::new(),
                            })
                        }
                        WpdaResolveResult::MaxStepsExceeded { position } => {
                            Err(WpdaParseError::Incomplete { position })
                        }
                        WpdaResolveResult::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 } => {
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 })
                        }
                    },
                    Err(exceeded) => Err(WpdaParseError::Incomplete {
                        position: exceeded.position,
                    }),
                }
            }

            /// Slice-source wrapper for the raw surface-exact realization
            /// probe used by `Cat::parse`.
            #[allow(non_snake_case)]
            pub fn #surface_exact_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
                expected_display: &str,
                max_raw_derivations: usize,
            ) -> Result<
                Option<(
                    #cat_ident,
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                )>,
                WpdaParseError,
            > {
                let src = mettail_prattail::wpda_runtime::SliceTokenSource::with_texts(
                    kinds, texts,
                );
                #surface_exact_with_source_fn_name(
                    &src,
                    pos,
                    min_bp,
                    expected_display,
                    max_raw_derivations,
                )
            }

            /// M8 (2026-05-14): multi-result WPDS parser that takes any
            /// `WpdaTokenSource` impl (slice OR lattice). Returns every
            /// term the walker's `WpdaResolveResult::Accepted` carries —
            /// the ambiguity-preserving final state. Use this when you
            /// need to surface ALL parses for downstream disambiguation
            /// at the eval layer (run_ascent_typed's Ambiguous-flatten),
            /// or via `Cat::parse_all`.
            ///
            /// `parse_<Cat>_via_wpda_all_with_source` is the source-generic
            /// entry; `parse_<Cat>_via_wpda_all` wraps it with a
            /// `SliceTokenSource` for slice callers.
            ///
            /// Does NOT apply recovery — a clean accept yields
            /// `Ok((terms, weights))`; non-Accepted termination yields
            /// `Err(WpdaParseError)`.
            #[allow(non_snake_case)]
            pub fn #all_with_source_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                #all_with_source_bounded_fn_name(
                    source,
                    pos,
                    min_bp,
                    mettail_prattail::wpda_runtime::CursorBoundingMode::Unbounded,
                )
            }

            /// Source-generic bounded-prefix parser. Returns at most
            /// `max_alternatives` distinct semantic alternatives in the
            /// same weight-ordered surface shape as `parse_<Cat>_via_wpda_all`.
            ///
            /// This is a demand-bounded API: it asks each accepted SPPF
            /// root only for the raw realization prefix needed to satisfy
            /// the requested semantic prefix, growing the raw probe only
            /// when duplicate semantic realizations consume that demand.
            /// It does not call the eager all-results facade internally.
            #[allow(non_snake_case)]
            pub fn #prefix_with_source_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
                max_alternatives: usize,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                #prefix_with_source_bounded_fn_name(
                    source,
                    pos,
                    min_bp,
                    max_alternatives,
                    mettail_prattail::wpda_runtime::CursorBoundingMode::Unbounded,
                )
            }

            /// Source-generic bounded-prefix parser with explicit
            /// cursor-frontier bounding. The cursor budget reports
            /// structured `AmbiguityBudget` overflow without pruning; the
            /// `max_alternatives` demand only limits how many semantic
            /// alternatives are realized for this call.
            #[allow(non_snake_case)]
            pub fn #prefix_with_source_bounded_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
                max_alternatives: usize,
                bounding_mode: mettail_prattail::wpda_runtime::CursorBoundingMode,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                use mettail_prattail::wpda_runtime::WpdaResolveResult;
                use mettail_prattail::wpda_walker::WpdaWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                use std::collections::HashMap;
                type DW = LexicographicWeight;
                // `__MettailWpdaSemanticKeyHasher` is lifted to generated-module
                // scope (emitted once by `emit_semantic_key_hasher`) so the
                // facade root-dedup AND the engine's `semantic_fingerprint`
                // (per-node SPPF-realize dedup) share ONE byte-key definition.
                fn __mettail_wpda_semantic_key(term: &#cat_ident) -> Vec<u8> {
                    let mut hasher = __MettailWpdaSemanticKeyHasher::default();
                    term.semantic_hash(&mut hasher);
                    hasher.into_key()
                }
                fn __mettail_wpda_collect_prefix(
                    walker: &WpdaWalker<DW, #engine_ident>,
                    roots: &[mettail_prattail::sppf::SppfId],
                    max_alternatives: usize,
                    position: usize,
                ) -> Result<
                    (
                        Vec<#cat_ident>,
                        Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                    ),
                    WpdaParseError,
                > {
                    if max_alternatives == 0 {
                        return Ok((Vec::new(), Vec::new()));
                    }
                    const RAW_PREFIX_CAP: usize = 4096;
                    let mut raw_probe_limit = max_alternatives.saturating_add(1).max(1);
                    loop {
                        let mut typed_terms: Vec<#cat_ident> = Vec::new();
                        let mut typed_weights:
                            Vec<mettail_prattail::automata::lex_weight::LexicographicWeight> =
                            Vec::new();
                        let mut seen_terms: HashMap<Vec<u8>, usize> = HashMap::new();
                        let mut exhausted_all_roots = true;
                        for &root in roots {
                            let realized = walker.realize_root_to_terms_with_weights(
                                root,
                                Some(raw_probe_limit),
                            );
                            if realized.len() >= raw_probe_limit {
                                exhausted_all_roots = false;
                            }
                            for (term, weight) in realized {
                                let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                    .map_err(|_| WpdaParseError::EmptyResult)?;
                                let typed = std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone());
                                let semantic_key = __mettail_wpda_semantic_key(&typed);
                                if let Some(existing_idx) =
                                    seen_terms.get(&semantic_key).copied()
                                {
                                    if weight < typed_weights[existing_idx] {
                                        typed_terms[existing_idx] = typed;
                                        typed_weights[existing_idx] = weight;
                                    }
                                    continue;
                                }
                                seen_terms.insert(semantic_key, typed_terms.len());
                                typed_terms.push(typed);
                                typed_weights.push(weight);
                            }
                        }
                        let mut paired: Vec<_> =
                            typed_terms.into_iter().zip(typed_weights.into_iter()).collect();
                        paired.sort_by(|(_, a), (_, b)| a.cmp(b));
                        if paired.len() > max_alternatives {
                            paired.truncate(max_alternatives);
                        }
                        if paired.len() >= max_alternatives || exhausted_all_roots {
                            if paired.is_empty() {
                                return Err(WpdaParseError::EmptyResult);
                            }
                            let (typed_terms, typed_weights): (Vec<_>, Vec<_>) =
                                paired.into_iter().unzip();
                            return Ok((typed_terms, typed_weights));
                        }
                        if raw_probe_limit >= RAW_PREFIX_CAP {
                            return Err(WpdaParseError::AmbiguityBudget {
                                budget: RAW_PREFIX_CAP,
                                actual: RAW_PREFIX_CAP + 1,
                                position,
                                // EP-P4: pre-walker raw-probe cap — no live
                                // frontier to fold an ESS from.
                                frontier_ess_x1000: 0,
                            });
                        }
                        raw_probe_limit =
                            raw_probe_limit.saturating_mul(2).min(RAW_PREFIX_CAP);
                    }
                }
                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut recovery_config = mettail_prattail::recovery::RecoveryConfig::default();
                recovery_config.max_recovery_depth = 0;
                walker.set_recovery_config(recovery_config);
                walker.set_bounding_mode(bounding_mode);
                match walker.run_to_end_of_input_env_aware(MAX_STEPS, source) {
                    Ok(()) => match walker.resolve_at_end_of_input(source) {
                        WpdaResolveResult::Accepted { roots, .. } => {
                            let completion_position = walker.position();
                            *pos = completion_position;
                            __mettail_wpda_collect_prefix(
                                &walker,
                                &roots,
                                max_alternatives,
                                completion_position,
                            )
                        }
                        WpdaResolveResult::AcceptedWithTrailing {
                            roots, position, ..
                        } => {
                            *pos = position;
                            __mettail_wpda_collect_prefix(
                                &walker,
                                &roots,
                                max_alternatives,
                                position,
                            )
                        }
                        WpdaResolveResult::ParseError { message, position } => {
                            Err(WpdaParseError::ParseFailed {
                                message,
                                position,
                                attempts: Vec::new(),
                            })
                        }
                        WpdaResolveResult::MaxStepsExceeded { position } => {
                            Err(WpdaParseError::Incomplete { position })
                        }
                        WpdaResolveResult::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 } => {
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 })
                        }
                    },
                    Err(exceeded) => Err(WpdaParseError::Incomplete {
                        position: exceeded.position,
                    }),
                }
            }

            /// Slice-source convenience wrapper for bounded-prefix parsing.
            #[allow(non_snake_case)]
            pub fn #prefix_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
                max_alternatives: usize,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                let src = mettail_prattail::wpda_runtime::SliceTokenSource::with_texts(
                    kinds, texts,
                );
                #prefix_with_source_fn_name(&src, pos, min_bp, max_alternatives)
            }

            /// Source-generic all-results parser with explicit cursor-frontier
            /// bounding. The default all-results facade calls this with
            /// `CursorBoundingMode::Unbounded`; callers should pass an
            /// explicit bounded mode only when they want a structured
            /// `AmbiguityBudget` error instead of an unbounded ambiguity
            /// surface.
            #[allow(non_snake_case)]
            pub fn #all_with_source_bounded_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
                bounding_mode: mettail_prattail::wpda_runtime::CursorBoundingMode,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                use mettail_prattail::wpda_runtime::WpdaResolveResult;
                use mettail_prattail::wpda_walker::WpdaWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                use std::collections::HashMap;
                // Phase 3.1.7 (C10, 2026-05-15): walker W = LexicographicWeight.
                // SPPF arena owns derivation ambiguity; W owns path cost.
                type DW = LexicographicWeight;
                // `__MettailWpdaSemanticKeyHasher` is lifted to generated-module
                // scope (emitted once by `emit_semantic_key_hasher`) so the
                // facade root-dedup AND the engine's `semantic_fingerprint`
                // (per-node SPPF-realize dedup) share ONE byte-key definition.
                fn __mettail_wpda_semantic_key(term: &#cat_ident) -> Vec<u8> {
                    let mut hasher = __MettailWpdaSemanticKeyHasher::default();
                    term.semantic_hash(&mut hasher);
                    hasher.into_key()
                }
                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut recovery_config = mettail_prattail::recovery::RecoveryConfig::default();
                recovery_config.max_recovery_depth = 0;
                walker.set_recovery_config(recovery_config);
                walker.set_bounding_mode(bounding_mode);
                match walker.run_to_end_of_input_env_aware(MAX_STEPS, source) {
                    Ok(()) => match walker.resolve_at_end_of_input(source) {
                        WpdaResolveResult::Accepted { roots, .. } => {
                            // C7b (Phase 3.1.6, 2026-05-15): realize all
                            // SPPF roots; packing-fanout produces the
                            // ambiguity-preserving Vec<Cat>. The public cap
                            // is applied to DISTINCT semantic alternatives:
                            // raw duplicate derivations update the retained
                            // representative's best weight rather than
                            // consuming the ambiguity budget before language
                            // construction can quotient them.
                            const REALIZE_CAP: usize = 64;
                            const RAW_REALIZE_CAP: usize = 4096;
                            let completion_position = walker.position();
                            *pos = completion_position;
                            let mut typed_terms: Vec<#cat_ident> = Vec::new();
                            let mut typed_weights:
                                Vec<mettail_prattail::automata::lex_weight::LexicographicWeight> =
                                Vec::new();
                            let mut seen_terms: HashMap<Vec<u8>, usize> = HashMap::new();
                            let mut overflowed_realization = false;
                            let mut raw_realization_exhausted_budget = false;
                            for &root in &roots {
                                let mut raw_probe_limit = REALIZE_CAP.saturating_add(1);
                                loop {
                                    let realized = walker.realize_root_to_terms_with_weights(
                                        root,
                                        Some(raw_probe_limit),
                                    );
                                    let exhausted_root = realized.len() < raw_probe_limit;
                                    for (term, weight) in realized {
                                        let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                            .map_err(|_| WpdaParseError::EmptyResult)?;
                                        let typed = std::sync::Arc::try_unwrap(arc)
                                            .unwrap_or_else(|arc| (*arc).clone());
                                        let semantic_key = __mettail_wpda_semantic_key(&typed);
                                        if let Some(existing_idx) =
                                            seen_terms.get(&semantic_key).copied()
                                        {
                                            if weight < typed_weights[existing_idx] {
                                                typed_terms[existing_idx] = typed;
                                                typed_weights[existing_idx] = weight;
                                            }
                                            continue;
                                        }
                                        if typed_terms.len() >= REALIZE_CAP {
                                            overflowed_realization = true;
                                            break;
                                        }
                                        seen_terms.insert(semantic_key, typed_terms.len());
                                        typed_terms.push(typed);
                                        typed_weights.push(weight);
                                    }
                                    if overflowed_realization || exhausted_root {
                                        break;
                                    }
                                    if raw_probe_limit >= RAW_REALIZE_CAP {
                                        raw_realization_exhausted_budget = true;
                                        break;
                                    }
                                    raw_probe_limit =
                                        raw_probe_limit.saturating_mul(2).min(RAW_REALIZE_CAP);
                                }
                                if overflowed_realization || raw_realization_exhausted_budget {
                                    break;
                                }
                            }
                            if raw_realization_exhausted_budget {
                                return Err(WpdaParseError::AmbiguityBudget {
                                    budget: RAW_REALIZE_CAP,
                                    actual: RAW_REALIZE_CAP + 1,
                                    position: completion_position,
                                    // EP-P4: realize-side cap — no frontier ESS.
                                    frontier_ess_x1000: 0,
                                });
                            }
                            if overflowed_realization {
                                return Err(WpdaParseError::AmbiguityBudget {
                                    budget: REALIZE_CAP,
                                    actual: REALIZE_CAP + 1,
                                    position: completion_position,
                                    // EP-P4: realize-side cap — no frontier ESS.
                                    frontier_ess_x1000: 0,
                                });
                            }
                            if typed_terms.is_empty() {
                                return Err(WpdaParseError::EmptyResult);
                            }
                            let mut paired: Vec<_> =
                                typed_terms.into_iter().zip(typed_weights.into_iter()).collect();
                            paired.sort_by(|(_, a), (_, b)| a.cmp(b));
                            let (typed_terms, typed_weights): (Vec<_>, Vec<_>) =
                                paired.into_iter().unzip();
                            Ok((typed_terms, typed_weights))
                        }
                        // Cluster H (2026-05-29): valid-prefix parse with
                        // trailing tokens. Realize ALL prefix derivations
                        // (ambiguity-preserving) and set `*pos` to the
                        // prefix boundary so the caller's source-aware
                        // trailing check surfaces `TrailingTokens`.
                        WpdaResolveResult::AcceptedWithTrailing {
                            roots, position, ..
                        } => {
                            *pos = position;
                            const REALIZE_CAP: usize = 64;
                            const RAW_REALIZE_CAP: usize = 4096;
                            let mut typed_terms: Vec<#cat_ident> = Vec::new();
                            let mut typed_weights:
                                Vec<mettail_prattail::automata::lex_weight::LexicographicWeight> =
                                Vec::new();
                            let mut seen_terms: HashMap<Vec<u8>, usize> = HashMap::new();
                            let mut overflowed_realization = false;
                            let mut raw_realization_exhausted_budget = false;
                            for &root in &roots {
                                let mut raw_probe_limit = REALIZE_CAP.saturating_add(1);
                                loop {
                                    let realized = walker.realize_root_to_terms_with_weights(
                                        root,
                                        Some(raw_probe_limit),
                                    );
                                    let exhausted_root = realized.len() < raw_probe_limit;
                                    for (term, weight) in realized {
                                        let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                            .map_err(|_| WpdaParseError::EmptyResult)?;
                                        let typed = std::sync::Arc::try_unwrap(arc)
                                            .unwrap_or_else(|arc| (*arc).clone());
                                        let semantic_key = __mettail_wpda_semantic_key(&typed);
                                        if let Some(existing_idx) =
                                            seen_terms.get(&semantic_key).copied()
                                        {
                                            if weight < typed_weights[existing_idx] {
                                                typed_terms[existing_idx] = typed;
                                                typed_weights[existing_idx] = weight;
                                            }
                                            continue;
                                        }
                                        if typed_terms.len() >= REALIZE_CAP {
                                            overflowed_realization = true;
                                            break;
                                        }
                                        seen_terms.insert(semantic_key, typed_terms.len());
                                        typed_terms.push(typed);
                                        typed_weights.push(weight);
                                    }
                                    if overflowed_realization || exhausted_root {
                                        break;
                                    }
                                    if raw_probe_limit >= RAW_REALIZE_CAP {
                                        raw_realization_exhausted_budget = true;
                                        break;
                                    }
                                    raw_probe_limit =
                                        raw_probe_limit.saturating_mul(2).min(RAW_REALIZE_CAP);
                                }
                                if overflowed_realization || raw_realization_exhausted_budget {
                                    break;
                                }
                            }
                            if raw_realization_exhausted_budget {
                                return Err(WpdaParseError::AmbiguityBudget {
                                    budget: RAW_REALIZE_CAP,
                                    actual: RAW_REALIZE_CAP + 1,
                                    position,
                                    // EP-P4: realize-side cap — no frontier ESS.
                                    frontier_ess_x1000: 0,
                                });
                            }
                            if overflowed_realization {
                                return Err(WpdaParseError::AmbiguityBudget {
                                    budget: REALIZE_CAP,
                                    actual: REALIZE_CAP + 1,
                                    position,
                                    // EP-P4: realize-side cap — no frontier ESS.
                                    frontier_ess_x1000: 0,
                                });
                            }
                            if typed_terms.is_empty() {
                                return Err(WpdaParseError::EmptyResult);
                            }
                            let mut paired: Vec<_> =
                                typed_terms.into_iter().zip(typed_weights.into_iter()).collect();
                            paired.sort_by(|(_, a), (_, b)| a.cmp(b));
                            let (typed_terms, typed_weights): (Vec<_>, Vec<_>) =
                                paired.into_iter().unzip();
                            Ok((typed_terms, typed_weights))
                        }
                        WpdaResolveResult::ParseError { message, position } => {
                            Err(WpdaParseError::ParseFailed {
                                message,
                                position,
                                attempts: Vec::new(),
                            })
                        }
                        WpdaResolveResult::MaxStepsExceeded { position } => {
                            Err(WpdaParseError::Incomplete { position })
                        }
                        WpdaResolveResult::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 } => {
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 })
                        }
                    },
                    Err(exceeded) => Err(WpdaParseError::Incomplete {
                        position: exceeded.position,
                    }),
                }
            }

            /// M8 wrapper: slice-source convenience for callers that
            /// already have `kinds` + `texts` Vecs. Routes through
            /// `parse_<Cat>_via_wpda_all_with_source` with a
            /// `SliceTokenSource`.
            #[allow(non_snake_case)]
            pub fn #all_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                let src = mettail_prattail::wpda_runtime::SliceTokenSource::with_texts(
                    kinds, texts,
                );
                #all_with_source_fn_name(&src, pos, min_bp)
            }

            /// WPDS-runtime parser variant that exposes the recovery trail
            /// alongside the parse result. Returns
            /// `(Result<#cat_ident, WpdaParseError>, Vec<RecoveryAttempt>)`:
            /// - `Ok` with empty `attempts`: clean parse, no recovery.
            /// - `Ok` with non-empty `attempts`: parse succeeded but the
            ///   walker dispatched recovery one or more times along the
            ///   way; the trail records each recovery action that the
            ///   lex-min winner committed.
            /// - `Err(ParseFailed)` with non-empty `attempts`: walker
            ///   exhausted all bounded recovery dispatches without
            ///   finding an accepting derivation; the trail records every
            ///   recovery action attempted before failure.
            ///
            /// Stage 3.20 / L12 (Commit E, 2026-05-06): the legacy
            /// wrapper-level skip-to-sync retry loop has been deleted.
            /// Recovery is now intrinsic to the walker via
            /// `recovery_dispatch::emit_recovery_fork`, bounded by
            /// `RecoveryConfig.max_recovery_depth` (default 3) and the
            /// per-cursor `visited_recovery` cycle defense. Each
            /// `RecoveryEvent` the walker logs becomes one
            /// `RecoveryAttempt` in the returned trail.
            #[allow(non_snake_case)]
            pub fn #recovering_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> (Result<#cat_ident, WpdaParseError>, Vec<RecoveryAttempt>) {
                use mettail_prattail::wpda_runtime::WpdaResolveResult;
                use mettail_prattail::wpda_walker::WpdaWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                // Phase 3.1.7 (C10, 2026-05-15): walker W = LexicographicWeight.
                type DW = LexicographicWeight;

                // Stage 6 G6+ (2026-05-02): default 1M; PRATTAIL_MAX_STEPS env
                // var overrides via run_to_end_of_input_env_aware.
                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut src = mettail_prattail::wpda_runtime::MutableSliceTokenSource::with_texts(
                    kinds, texts,
                );
                walker.set_mutable_token_source(&mut src);
                let resolve = match walker.run_to_end_of_input_env_aware(MAX_STEPS, &src) {
                    Ok(()) => walker.resolve_at_end_of_input(&src),
                    Err(exceeded) => {
                        walker.clear_mutable_token_source();
                        return (
                            Err(WpdaParseError::Incomplete {
                                position: exceeded.position,
                            }),
                            Vec::new(),
                        );
                    }
                };
                walker.clear_mutable_token_source();
                // Stage 3.20 / L12 (Commit E, 2026-05-06): map walker's
                // recovery_trace into RecoveryAttempt for the public API.
                // Each RecoveryEvent the lex-min winner committed appears
                // in the trace; the action_kind discriminator + position
                // + token text describe what the walker did.
                let attempts: Vec<RecoveryAttempt> = walker
                    .recovery_trace()
                    .iter()
                    .map(|ev| RecoveryAttempt {
                        message: format!(
                            "recovery action_kind={} cost={:.3}",
                            ev.action_kind, ev.cost_tropical,
                        ),
                        position: ev.pos,
                        recovery: match ev.action_kind {
                            0 => Some("skip-to-sync".into()),
                            1 => Some("delete-token".into()),
                            2 => Some(format!(
                                "insert-token {:?}",
                                ev.text.as_deref().unwrap_or(""),
                            )),
                            3 => Some(format!(
                                "substitute-token {:?}",
                                ev.text.as_deref().unwrap_or(""),
                            )),
                            5 => Some("composite-recovery".into()),
                            7 => Some(format!(
                                "lex-alternative idx={}",
                                ev.alt_idx.unwrap_or(0),
                            )),
                            _ => None,
                        },
                    })
                    .collect();
                match resolve {
                    WpdaResolveResult::Accepted { roots, .. } => {
                        *pos = walker.position();
                        // C7b (Phase 3.1.6, 2026-05-15): realize the first
                        // SPPF root for backward-compat single-result return.
                        let pick = roots
                            .first()
                            .and_then(|&root|
                                walker
                                    .realize_root_to_terms(root, Some(1))
                                    .into_iter()
                                    .next()
                            );
                        let result = match pick {
                            Some(term) => std::sync::Arc::downcast::<#cat_ident>(term)
                                .map(|arc| std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone()))
                                .map_err(|_| WpdaParseError::EmptyResult),
                            None => Err(WpdaParseError::EmptyResult),
                        };
                        (result, attempts)
                    }
                    // Cluster H (2026-05-29): valid-prefix parse with
                    // trailing tokens. Return the prefix term (`Ok`) and
                    // set `*pos` to the prefix boundary; `parse_recovering`
                    // then appends a `TrailingTokens` error to its trail
                    // while STILL returning the partial AST — the
                    // recovering-mode "what parsed + what went wrong"
                    // contract (recovery_integration_tests assert
                    // `result.is_some()` for trailing-token inputs).
                    WpdaResolveResult::AcceptedWithTrailing { roots, position, .. } => {
                        *pos = position;
                        let pick = roots
                            .first()
                            .and_then(|&root|
                                walker
                                    .realize_root_to_terms(root, Some(1))
                                    .into_iter()
                                    .next()
                            );
                        let result = match pick {
                            Some(term) => std::sync::Arc::downcast::<#cat_ident>(term)
                                .map(|arc| std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone()))
                                .map_err(|_| WpdaParseError::EmptyResult),
                            None => Err(WpdaParseError::EmptyResult),
                        };
                        (result, attempts)
                    }
                    WpdaResolveResult::ParseError { message, position } => {
                        let err = WpdaParseError::ParseFailed {
                            message,
                            position,
                            attempts: attempts.clone(),
                        };
                        (Err(err), attempts)
                    }
                    WpdaResolveResult::MaxStepsExceeded { position } => {
                        (Err(WpdaParseError::Incomplete { position }), attempts)
                    }
                    WpdaResolveResult::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 } => {
                        (
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 }),
                            attempts,
                        )
                    }
                }
            }
        });
    }
    let _ = language;
    quote! {
        /// One round of WPDS-facade recovery — captures the message that
        /// triggered the round, the token position where it surfaced, and
        /// the sync-token-skip action taken (or `None` if recovery
        /// exhausted without finding a sync token).
        #[derive(Debug, Clone)]
        pub struct RecoveryAttempt {
            /// Diagnostic message from the walker's `WpdaState::Error`.
            pub message: std::string::String,
            /// Token position where the error surfaced.
            pub position: usize,
            /// Skip action taken, or `None` if no sync token was found
            /// (terminating round).
            pub recovery: Option<std::string::String>,
        }

        /// Error returned by `parse_<Cat>_via_wpda` wrappers when the walker
        /// terminates in a non-accepting state.
        ///
        /// `ParseFailed` carries the final-error fields plus the full
        /// recovery-attempt trail, so consumers don't need to re-run the
        /// recovering variant to inspect what was tried.
        #[derive(Debug, Clone)]
        pub enum WpdaParseError {
            /// Walker accepted, but the builder's term stack was empty —
            /// indicates a codegen bug (every successful parse should push
            /// exactly one term).
            EmptyResult,
            /// Walker entered `WpdaState::Error` with a diagnostic message.
            /// `attempts` records every recovery round (including the
            /// terminating one).
            ParseFailed {
                message: std::string::String,
                position: usize,
                attempts: Vec<RecoveryAttempt>,
            },
            /// Walker reached step budget without terminating.
            Incomplete {
                position: usize,
            },
            /// M11.7 (2026-05-14): walker was configured with
            /// `CursorBoundingMode::AmbiguityBudget(budget)` and the live
            /// frontier exceeded that budget. `actual` is the frontier
            /// size that triggered the overflow; `position` is the input
            /// position at the overflow point. Callers can react by
            /// relaxing the budget, switching strategy, or surfacing a
            /// structured "input too ambiguous" error.
            AmbiguityBudget {
                budget: usize,
                actual: usize,
                position: usize,
                /// EP-P4 (Stage E): frontier effective-sample-size ×1000 at
                /// the overflow point (Kish ESS over the live frontier's
                /// primary likelihood mass). Distinguishes "1 winner +
                /// noise" (≈1000) from genuine k-way ambiguity (≈k·1000).
                /// `0` = not computed at this emission site.
                frontier_ess_x1000: u32,
            },
        }

        impl std::fmt::Display for WpdaParseError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    WpdaParseError::EmptyResult => {
                        write!(f, "wpds parser produced no result")
                    }
                    WpdaParseError::ParseFailed { message, position, attempts } => {
                        if attempts.len() <= 1 {
                            write!(f, "wpds parse failed at position {}: {}", position, message)
                        } else {
                            write!(
                                f,
                                "wpds parse failed at position {}: {} ({} recovery rounds)",
                                position,
                                message,
                                attempts.len(),
                            )
                        }
                    }
                    WpdaParseError::Incomplete { position } => {
                        write!(f, "wpds parse incomplete at position {}", position)
                    }
                    WpdaParseError::AmbiguityBudget { budget, actual, position, frontier_ess_x1000 } => {
                        write!(
                            f,
                            "wpds parse aborted at position {}: ambiguity budget {} exceeded by frontier of {} cursors (frontier ESS≈{:.3} of {})",
                            position,
                            budget,
                            actual,
                            (*frontier_ess_x1000 as f64) / 1000.0,
                            actual,
                        )
                    }
                }
            }
        }

        impl std::error::Error for WpdaParseError {}

        #(#fns)*
    }
}
