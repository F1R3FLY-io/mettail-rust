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

use mettail_ast::grammar::{GrammarRule, PatternOp, SyntaxExpr, TermParam};
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
    /// SINGLE-ELEMENT TWIN (bug 2318): the label of the grammar rule that is this
    /// variant with the `.*sep` LIST removed — a bare scalar head plus the same
    /// suffix (e.g. `ForRowWhere . b "&" bs.*sep("&") "where" cond` ↦ twin
    /// `ForRowSingleWhere . b "where" cond`). When a `.*sep` category is fed a
    /// domain with only ONE element (no separator), the `.*sep` rule cannot
    /// construct (its list is empty ⇒ a spurious `&`); the twin is the correct
    /// constructor. Isolating the single-element case matters because it lets the
    /// SUFFIX operand (a ForRow `where`-cond `Proc`) be sub-parsed in ISOLATION —
    /// so `where p == @Nil!(q)` composes the cond's single-winner (`POutputNil`),
    /// matching monolithic, instead of the walker's whole-ForRow reading (which,
    /// with a query-bind head, elects the spurious channel-named-`Nil`
    /// `POutputQuoted` on the `open_len` tie). `None` when no such twin exists
    /// (then a single-element domain still declines to the walker — unchanged).
    single_twin: Option<String>,
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

/// Find the SINGLE-ELEMENT TWIN of a `.*sep` variant (bug 2318): a rule in
/// `cat_name` whose syntax is a BARE scalar head of `element_category` followed
/// by EXACTLY the same suffix operand-`groups` (each a `Literal(lead) Param(op)`
/// pair), with NO `.*sep` list and NO extra literals. Returns its label.
///
/// Example: for `ForRowWhere . b:InputBind, bs:Vec(InputBind), cond:Proc |-
/// b "&" bs.*sep("&") "where" cond` (element `InputBind`, groups `[where:Proc]`),
/// the twin is `ForRowSingleWhere . b:InputBind, cond:Proc |- b "where" cond`.
/// For the bare `ForRowNoWhere` (no groups) the twin is `ForRowSingleNoWhere .
/// b:InputBind |- b`. The twin is what the isolation helper CONSTRUCTS when a
/// `.*sep` domain carries only one element, so the single-element case can also
/// isolate its suffix operand.
fn find_single_element_twin(
    language: &LanguageDef,
    cat_name: &str,
    element_category: &str,
    groups: &[SepOperandGroup],
) -> Option<String> {
    'rule: for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        let (Some(tc), Some(sp)) = (&normalized.term_context, &normalized.syntax_pattern) else {
            continue;
        };
        // The twin carries NO `.*sep` list operand.
        if sp.iter().any(|e| matches!(e, SyntaxExpr::Op(PatternOp::Sep { .. }))) {
            continue;
        }
        // Expected shape: Param(head) then (Literal(lead), Param(op)) per group.
        if sp.len() != 1 + 2 * groups.len() {
            continue;
        }
        let cat_of = |name: &str| -> Option<String> {
            tc.iter().find_map(|p| match p {
                TermParam::Simple { name: n, ty } if n == name => sep_base_ty(ty),
                _ => None,
            })
        };
        // Slot 0: the scalar head of `element_category`.
        let SyntaxExpr::Param(head) = &sp[0] else { continue };
        match cat_of(&head.to_string()) {
            Some(c) if c == element_category => {},
            _ => continue,
        }
        // Each group: Literal(lead) then Param of the group's operand category.
        for (gi, group) in groups.iter().enumerate() {
            match &sp[1 + 2 * gi] {
                SyntaxExpr::Literal(l) if *l == group.lead => {},
                _ => continue 'rule,
            }
            let SyntaxExpr::Param(op) = &sp[2 + 2 * gi] else { continue 'rule };
            match cat_of(&op.to_string()) {
                Some(c) if c == group.category => {},
                _ => continue 'rule,
            }
        }
        return Some(normalized.label.to_string());
    }
    None
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
        let single_twin = find_single_element_twin(language, cat_name, &elem_cat, &groups);
        variants.push(SepVariant {
            label: normalized.label.to_string(),
            operand_groups: groups,
            single_twin,
        });
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

// ─────────────────────────────────────────────────────────────────────────
// P0 — GRAMMAR-DERIVED isolation-category selection (ROOT-P generalization).
//
// Replaces the three HARDCODED include-lists (`forks::SEP_ISOLATION_CATEGORIES`
// / `PROJ_ISOLATION_CATEGORIES` / `INFIX_ISOLATION_CATEGORIES`) with a
// GRAMMAR-DERIVED eligibility predicate, gated by
// `forks::GRAMMAR_DERIVED_ISOLATION_CATEGORIES` (ship default `false` ⇒ the
// hardcoded lists, byte-identical). The `debug_assert_isolation_oracle` proves —
// at codegen, for EVERY language and EVERY family — that the derived set EXACTLY
// equals the EFFECTIVE hardcoded set (`LIST ∩ derivable`), so the derived
// predicate is a CONSERVATIVE EXTENSION (flipping the switch is byte-identical).
// A future P1 extends the mechanism generically beyond the reproduced sets.

/// The OPERAND-REACHABILITY transitive closure over category names. `(C, D)` is a
/// member iff there is a path `C → … → D` of length ≥ 1 in the OPERAND GRAPH,
/// whose direct edge `C → D` holds iff some rule of category `C` has an OPERAND
/// slot — a simple `Param` of a `Base` category `D`, OR a `.*sep`/collection
/// element of category `D`. `(C, C)` is present iff `C` participates in a cycle
/// (`self_nests`), so NO reflexive `a != d` guard is used — the DELIBERATE
/// difference from [`super::kind_dispatch::emit_cat_can_reach`], which is
/// cross-cat-only, prefix-edge-EXCLUDING, and reflexive-free (a NARROWER graph
/// built for a different purpose). Broader-is-safe here: `reaches` only gates
/// "does an operand nest back into the result category", and the oracle certifies
/// the resulting sets do not over-include.
struct OperandReach {
    reach: std::collections::BTreeSet<(String, String)>,
}

impl OperandReach {
    /// Does category `from` reach category `to` via ≥ 1 operand edge?
    fn reaches(&self, from: &str, to: &str) -> bool {
        self.reach.contains(&(from.to_string(), to.to_string()))
    }
}

/// The categories of a rule's OPERAND slots (edge targets `D`): each simple
/// `Param` of a `Base` category, plus each `.*sep`/collection element category
/// (extracted via [`sep_base_ty`] over the collection's element type). Binder /
/// abstraction / guard / optional params are NOT simple operands and contribute
/// no edge. Mirrors the slot walk of the `derive_*_iso_shape` derivations.
fn rule_operand_categories(rule: &GrammarRule) -> Vec<String> {
    let mut normalized = rule.clone();
    mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
    let (Some(tc), Some(sp)) = (&normalized.term_context, &normalized.syntax_pattern) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for e in sp.iter() {
        match e {
            SyntaxExpr::Param(p) => {
                if let Some(cat) = tc.iter().find_map(|tp| match tp {
                    TermParam::Simple { name, ty } if name == p => sep_base_ty(ty),
                    _ => None,
                }) {
                    out.push(cat);
                }
            },
            SyntaxExpr::Op(PatternOp::Sep { collection, .. }) => {
                if let Some(cat) = tc.iter().find_map(|tp| match tp {
                    TermParam::Simple { name, ty: TypeExpr::Collection { element, .. } }
                        if name == collection =>
                    {
                        sep_base_ty(element)
                    },
                    _ => None,
                }) {
                    out.push(cat);
                }
            },
            _ => {},
        }
    }
    out
}

/// Build the operand-reachability closure (fixpoint, mirroring the closure loop
/// in [`super::kind_dispatch::emit_cat_can_reach`] — but WITHOUT the `a != d`
/// guard, so cyclic categories self-reach).
fn build_operand_reach(language: &LanguageDef) -> OperandReach {
    use std::collections::BTreeSet;
    let mut reach: BTreeSet<(String, String)> = BTreeSet::new();
    for rule in &language.terms {
        let c = rule.category.to_string();
        for d in rule_operand_categories(rule) {
            reach.insert((c.clone(), d));
        }
    }
    loop {
        let mut added = false;
        let snapshot: Vec<(String, String)> = reach.iter().cloned().collect();
        for (a, b) in &snapshot {
            for (c, d) in &snapshot {
                if b == c && reach.insert((a.clone(), d.clone())) {
                    added = true;
                }
            }
        }
        if !added {
            break;
        }
    }
    OperandReach { reach }
}

/// P0 PROJ eligibility (red-team-tightened A5a form — gated on `cat` ITSELF, NOT
/// its SCC): a derivable projection shape AND a non-ident-sigil PREFIX COHORT of
/// size ≥ 2 (≥ 2 rules of `cat` sharing ONE non-ident leading literal `σ`), ≥ 2
/// of whose members carry an operand slot whose category REACHES `cat` (nests
/// back — the exponential-blowup shape the isolator linearizes). `K = 2` cohort
/// floor. `non-ident-shaped` == the existing `derive_projection_iso_shape` test.
fn eligible_proj(
    language: &LanguageDef,
    reach: &OperandReach,
    cat_name: &str,
    categories: &[String],
) -> bool {
    if derive_projection_iso_shape(language, cat_name, categories).is_none() {
        return false;
    }
    let is_ident_shaped = |s: &str| s.chars().all(|c| c.is_alphanumeric() || c == '_');
    // Per non-ident sigil σ: (cohort size, count with an operand reaching `cat`).
    let mut cohort: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        let Some(sp) = &normalized.syntax_pattern else { continue };
        let Some(SyntaxExpr::Literal(sigil)) = sp.first() else { continue };
        if is_ident_shaped(sigil) {
            continue;
        }
        let nests = rule_operand_categories(rule)
            .iter()
            .any(|d| reach.reaches(d, cat_name));
        let entry = cohort.entry(sigil.clone()).or_insert((0, 0));
        entry.0 += 1;
        if nests {
            entry.1 += 1;
        }
    }
    // ∃ σ : |cohort(σ)| ≥ 2 ∧ ≥ 2 of its members have an operand reaching `cat`.
    cohort.values().any(|&(size, reaching)| size >= 2 && reaching >= 2)
}

/// P0 SEP eligibility: a derivable `.*sep` combine shape whose derived ELEMENT
/// category reaches `cat` (the list element nests back into the list category).
fn eligible_sep(
    language: &LanguageDef,
    reach: &OperandReach,
    cat_name: &str,
    categories: &[String],
) -> bool {
    match derive_sep_combine_shape(language, cat_name, categories) {
        Some(shape) => reach.reaches(&shape.element_category, cat_name),
        None => false,
    }
}

/// P0 INFIX eligibility: a derivable homogeneous binary-infix shape AND `cat`
/// reaches some category `D` that is itself PROJ- or SEP-eligible (the infix
/// operands recursively descend into an isolation-eligible sub-language).
fn eligible_infix(
    language: &LanguageDef,
    reach: &OperandReach,
    cat_name: &str,
    categories: &[String],
) -> bool {
    if derive_infix_iso_shape(language, cat_name, categories).is_none() {
        return false;
    }
    categories.iter().any(|d| {
        reach.reaches(cat_name, d)
            && (eligible_proj(language, reach, d, categories)
                || eligible_sep(language, reach, d, categories))
    })
}

/// The three isolation families selected by the P0 predicate.
enum IsoFamily {
    Sep,
    Proj,
    Infix,
}

/// The GRAMMAR-DERIVED eligibility for one family + category — consumed by the
/// three `*_iso_shape` gates when [`grammar_derived_isolation_enabled`] is true.
fn eligible_family(
    language: &LanguageDef,
    family: IsoFamily,
    cat_name: &str,
    categories: &[String],
) -> bool {
    let reach = build_operand_reach(language);
    match family {
        IsoFamily::Sep => eligible_sep(language, &reach, cat_name, categories),
        IsoFamily::Proj => eligible_proj(language, &reach, cat_name, categories),
        IsoFamily::Infix => eligible_infix(language, &reach, cat_name, categories),
    }
}

/// Whether GRAMMAR-DERIVED isolation-category selection is active at codegen.
/// Default = the [`super::forks::GRAMMAR_DERIVED_ISOLATION_CATEGORIES`] const
/// (ship default `true` ⇒ the grammar-derived predicate is the ACTIVE path). The
/// codegen-time env override `PRATTAIL_GRAMMAR_DERIVED_ISOLATION=1|0` flips it for
/// A/B WITHOUT a source edit (unset ⇒ the const). Mirrors the `PRATTAIL_*` A/B
/// convention. NOTE: derived is a behavior-preserving REFINEMENT of the hardcoded
/// lists, NOT byte-identical — it emits fewer (redundant) isolation helpers for
/// non-fork-exploding shapes in 5 languages; see
/// [`super::forks::GRAMMAR_DERIVED_ISOLATION_CATEGORIES`] for the validation.
fn grammar_derived_isolation_enabled() -> bool {
    match std::env::var_os("PRATTAIL_GRAMMAR_DERIVED_ISOLATION") {
        Some(v) if v == "1" || v == "true" => true,
        Some(v) if v == "0" || v == "false" => false,
        _ => super::forks::GRAMMAR_DERIVED_ISOLATION_CATEGORIES,
    }
}

/// P0 CONSERVATIVE-EXTENSION ORACLE — the make-or-break gate. For EVERY family,
/// assert the GRAMMAR-DERIVED category set (over ALL `categories`) EXACTLY equals
/// the EFFECTIVE hardcoded set `{ C ∈ hardcoded_LIST(family) : derive_F(C).is_some() }`
/// (the EFFECTIVE, not RAW, set — so an inert list entry whose `derive_F` is
/// `None`, e.g. the historical `ForRow`-in-PROJ, is NOT a spurious mismatch).
/// Runs once per language at codegen (macro expansion); a mismatch fires
/// `debug_assert_eq!` in debug builds of the macros crate. Independent of
/// [`grammar_derived_isolation_enabled`] — it certifies the two selection paths
/// agree, so flipping the switch is byte-identical.
fn debug_assert_isolation_oracle(language: &LanguageDef, categories: &[String]) {
    use std::collections::BTreeSet;
    let reach = build_operand_reach(language);

    let derived_sep: BTreeSet<String> = categories
        .iter()
        .filter(|c| eligible_sep(language, &reach, c.as_str(), categories))
        .cloned()
        .collect();
    let derived_proj: BTreeSet<String> = categories
        .iter()
        .filter(|c| eligible_proj(language, &reach, c.as_str(), categories))
        .cloned()
        .collect();
    let derived_infix: BTreeSet<String> = categories
        .iter()
        .filter(|c| eligible_infix(language, &reach, c.as_str(), categories))
        .cloned()
        .collect();

    let effective_sep: BTreeSet<String> = super::forks::SEP_ISOLATION_CATEGORIES
        .iter()
        .copied()
        .filter(|c| derive_sep_combine_shape(language, c, categories).is_some())
        .map(|c| c.to_string())
        .collect();
    let effective_proj: BTreeSet<String> = super::forks::PROJ_ISOLATION_CATEGORIES
        .iter()
        .copied()
        .filter(|c| derive_projection_iso_shape(language, c, categories).is_some())
        .map(|c| c.to_string())
        .collect();
    let effective_infix: BTreeSet<String> = super::forks::INFIX_ISOLATION_CATEGORIES
        .iter()
        .copied()
        .filter(|c| derive_infix_iso_shape(language, c, categories).is_some())
        .map(|c| c.to_string())
        .collect();

    // DIAGNOSTIC MODE (`PRATTAIL_ISOLATION_ORACLE_DEBUG`): print the per-language
    // derived vs effective sets for ALL three families and RETURN WITHOUT
    // asserting — so a full multi-language build reveals EVERY (dis)agreement
    // rather than aborting the whole compile at the first mismatch. Side-effect
    // only: does NOT change the emitted tokens (byte-identical to the silent path).
    if std::env::var_os("PRATTAIL_ISOLATION_ORACLE_DEBUG").is_some() {
        let lang = language.name.to_string();
        let status = |d: &BTreeSet<String>, e: &BTreeSet<String>| {
            if d == e {
                "OK"
            } else {
                "MISMATCH"
            }
        };
        eprintln!(
            "[P0-ORACLE] {lang} SEP   derived={derived_sep:?} effective={effective_sep:?} {}",
            status(&derived_sep, &effective_sep)
        );
        eprintln!(
            "[P0-ORACLE] {lang} PROJ  derived={derived_proj:?} effective={effective_proj:?} {}",
            status(&derived_proj, &effective_proj)
        );
        eprintln!(
            "[P0-ORACLE] {lang} INFIX derived={derived_infix:?} effective={effective_infix:?} {}",
            status(&derived_infix, &effective_infix)
        );
        return;
    }

    // ★ SET-EQUALITY ENFORCEMENT RETIRED (2026-07-07, user-approved activation).
    // The derived path is now the SHIP DEFAULT
    // (`GRAMMAR_DERIVED_ISOLATION_CATEGORIES = true`). The `derived == effective`
    // invariant this block enforced is KNOWN FALSE-BUT-BENIGN: the derived
    // predicate is a strict SUBSET of the effective hardcoded set for 5 languages
    // (Ambient/Class2Smoke `Proc`, Class3Multi/Class3Opt `Name`, GuardedRho
    // `Name`+`Proc` — all PROJ), because the hardcoded lists over-isolate those
    // non-fork-exploding SINGLETON-sigil / framed-list / method-frame shapes only
    // by rhocalc-name coincidence. Dropping those redundant isolation helpers is
    // EMPIRICALLY VALIDATED BEHAVIOR-PRESERVING (all 5 langs' suites + every
    // control pass IDENTICALLY ON vs OFF — 422/0 affected, prattail 3606/0,
    // rhocalc 386/0). A codegen set-equality `debug_assert_eq!` would therefore
    // (a) fire on the default build (bricking every debug test build) over a gap
    // that changes no observable behavior, and (b) WRONGLY block the very
    // generalization it was meant to enable — a FUTURE language with a genuine
    // fork-exploding cohort NOT named in the hardcoded lists SHOULD make
    // `derived ⊋ effective`, which set-equality would reject. The behavioral gate
    // is the full test suite (it exercises this default-ON path); the
    // `PRATTAIL_ISOLATION_ORACLE_DEBUG` diagnostic (above) prints the per-language
    // derived-vs-effective sets for inspection. No enforcement here.
    let _ = (
        &derived_sep,
        &derived_proj,
        &derived_infix,
        &effective_sep,
        &effective_proj,
        &effective_infix,
    );
}

/// The gated `.*sep` isolation shape for `cat_name`: `Some` iff the master
/// switch is ON, the category is selected (GRAMMAR-DERIVED when
/// [`grammar_derived_isolation_enabled`], else the hardcoded include set), AND a
/// shape is derivable. The SINGLE source of truth shared by the helper emitter
/// (facade) and the string-entry prologue emitter (mod.rs).
pub(crate) fn sep_isolation_shape(
    language: &LanguageDef,
    cat_name: &str,
    categories: &[String],
) -> Option<SepCombineShape> {
    let in_set = if grammar_derived_isolation_enabled() {
        eligible_family(language, IsoFamily::Sep, cat_name, categories)
    } else {
        super::forks::SEP_ISOLATION_CATEGORIES.contains(&cat_name)
    };
    if super::forks::SEP_ISOLATION_COMBINE && in_set {
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
            // `true` ⇒ per-segment/suffix SINGLE-winner composition (== monolithic
            // single result; bug 2318 — avoids the all-path `open_len` divergence).
            if std::env::var_os("PRATTAIL_NO_SEP_ISOLATION").is_none() {
                if let Some((__iso_terms, __iso_weights)) = #helper_name(input, true) {
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
            // `false` ⇒ ambiguity-preserving all-path per segment (cartesian).
            if std::env::var_os("PRATTAIL_NO_SEP_ISOLATION").is_none() {
                if let Some(__iso) = #helper_name(input, false) {
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
            // GROUP-A single-bare-element fix (2026-07-06, `SEP_ISOLATION_SINGLE_BARE`):
            // when the `.*sep` domain carries EXACTLY ONE element the bare list rule
            // (`ForRowNoWhere . b, bs`) cannot construct a 1-element list (its `bs`
            // would be empty ⇒ a trailing dangling `&`), so build the SINGLE-element
            // TWIN (`ForRowSingleNoWhere . b:InputBind |- b`) instead. Mirrors the
            // suffix-variant `build_suffix_term` twin logic (bug 2318). Const-gated so
            // that `SEP_ISOLATION_SINGLE_BARE == false` emits the EXACT pre-fix arm
            // (byte-identical) — the single-element path never engages then anyway.
            let bare_twin = if super::forks::SEP_ISOLATION_SINGLE_BARE {
                variant.single_twin.as_ref()
            } else {
                None
            };
            let bare_construct = if let Some(twin) = bare_twin {
                let twin_ident = format_ident!("{}", twin);
                quote! {
                    #vi_lit => {
                        for (__elems, __w) in __element_combos {
                            let __term = if __elems.len() == 1 {
                                #cat_ident::#twin_ident(std::sync::Arc::new(__elems[0].clone()))
                            } else {
                                #cat_ident::#label_ident(
                                    std::sync::Arc::new(__elems[0].clone()),
                                    __elems[1..].to_vec(),
                                )
                            };
                            __candidates.push((__term, __w));
                        }
                    }
                }
            } else {
                quote! {
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
                }
            };
            construct_arms.push(bare_construct);
        } else {
            // A suffix variant — one operand-group `lead op:Cat`.
            let group = &variant.operand_groups[0];
            let lead = &group.lead;
            let lead_len = group.lead.len();
            let op_ident = format_ident!("{}", group.category);
            // Bug 2318: build the SINGLE-ELEMENT TWIN (`ForRowSingleWhere`) when the
            // `.*sep` domain has exactly one element, so a single-bind `where`-cond
            // is still isolated (the `.*sep` rule cannot construct a 1-element list).
            let build_suffix_term = if let Some(twin) = &variant.single_twin {
                let twin_ident = format_ident!("{}", twin);
                quote! {
                    if __elems.len() == 1 {
                        #cat_ident::#twin_ident(
                            std::sync::Arc::new(__elems[0].clone()),
                            std::sync::Arc::new(__op.clone()),
                        )
                    } else {
                        #cat_ident::#label_ident(
                            std::sync::Arc::new(__elems[0].clone()),
                            __elems[1..].to_vec(),
                            std::sync::Arc::new(__op.clone()),
                        )
                    }
                }
            } else {
                quote! {
                    #cat_ident::#label_ident(
                        std::sync::Arc::new(__elems[0].clone()),
                        __elems[1..].to_vec(),
                        std::sync::Arc::new(__op.clone()),
                    )
                }
            };
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
                    // SINGLE-RESULT seam (bug 2318): the suffix operand (e.g. a
                    // ForRow `where`-cond Proc) composes its single-winner (==
                    // monolithic), so the isolated `where p == @Nil!(q)` cond does
                    // not inherit the all-path `open_len` maximal-munch that ranks
                    // the spurious channel-named-`Nil` `POutputQuoted` first. ALL
                    // seam keeps the ambiguity-preserving all-path.
                    let (__op_terms, __op_weights): (Vec<#op_ident>, Vec<__W>) = if __single_winner {
                        match #op_ident::parse_via_wpda(__suffix) {
                            Ok(__one) => (vec![__one], vec![<__W as Semiring>::one()]),
                            Err(_) => return None,
                        }
                    } else {
                        match #op_ident::parse_via_wpda_all_with_weights(__suffix) {
                            Ok(__v) => __v,
                            Err(_) => return None,
                        }
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
                                #build_suffix_term,
                                Semiring::times(__we, __wo),
                            ));
                        }
                    }
                }
            });
        }
    }
    let bare_variant_idx_lit = bare_variant_idx;

    // Bug 2318: SUFFIX variants (a `where`-cond to isolate) whose SINGLE-element
    // domain is isolation-eligible via a single-element TWIN constructor. Always
    // on (the original bug-2318 fix).
    let suffix_allowed_vis: Vec<usize> = shape
        .variants
        .iter()
        .enumerate()
        .filter(|(_, v)| !v.operand_groups.is_empty() && v.single_twin.is_some())
        .map(|(vi, _)| vi)
        .collect();
    // GROUP-A single-bare-element fix (2026-07-06): also allow the BARE variant
    // (`ForRowNoWhere`, no suffix) whose single-element TWIN is `ForRowSingleNoWhere`
    // to isolate its ONE `InputBind` and wrap it (closes the monolithic
    // `<-@Nil!?(Set(),send)` gap). Compile-time gated by `SEP_ISOLATION_SINGLE_BARE`
    // (OFF ⇒ the `allow_single_expr` is EMITTED BYTE-IDENTICALLY to the pre-fix
    // suffix-only helper) and runtime gated by `PRATTAIL_NO_SEP_SINGLE_BARE` (causal
    // A/B, no rebuild).
    let allow_single_expr = if super::forks::SEP_ISOLATION_SINGLE_BARE {
        let bare_allowed_vis: Vec<usize> = shape
            .variants
            .iter()
            .enumerate()
            .filter(|(_, v)| v.operand_groups.is_empty() && v.single_twin.is_some())
            .map(|(vi, _)| vi)
            .collect();
        let suffix_allow_expr = if suffix_allowed_vis.is_empty() {
            quote! { false }
        } else {
            quote! { matches!(__variant, #(#suffix_allowed_vis)|*) }
        };
        let bare_allow_expr = if bare_allowed_vis.is_empty() {
            quote! { false }
        } else {
            quote! {
                (matches!(__variant, #(#bare_allowed_vis)|*)
                    && std::env::var_os("PRATTAIL_NO_SEP_SINGLE_BARE").is_none())
            }
        };
        quote! { ((#suffix_allow_expr) || (#bare_allow_expr)) }
    } else {
        // Const OFF: EXACT pre-fix tokens (suffix-only, bug-2318).
        if suffix_allowed_vis.is_empty() {
            quote! { false }
        } else {
            quote! { matches!(__variant, #(#suffix_allowed_vis)|*) }
        }
    };

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
            __single_winner: bool,
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
            // 0 separators ⇒ single element. Fall through to the monolithic single
            // variant (already fast; no `dᵏ` fork to linearize) UNLESS the elected
            // variant is a SUFFIX variant with a single-element twin — then isolate
            // the single element + its suffix `where`-cond via the twin ctor (bug
            // 2318: keeps the single-bind `where p == @Nil!(q)` cond's isolated
            // single-winner `POutputNil` == monolithic).
            if __seg_ranges.is_empty() {
                return None;
            }
            // The single-element twin isolation runs ONLY in the single-result seam
            // (`__single_winner`): it exists to make the single-bind `where`-cond's
            // ISOLATED single-winner == monolithic (bug 2318). In the ALL seam a
            // single-element domain still declines to the walker, so the
            // ambiguity-preserving alt-SET is byte-identical to the pre-2318 helper.
            if __seg_ranges.len() < 2 && !(__single_winner && (#allow_single_expr)) {
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
                // SINGLE-RESULT seam (bug 2318): compose per-element single-winners
                // (== monolithic) rather than the all-path min; ALL seam keeps the
                // ambiguity-preserving all-path. See the proj helper's note.
                let (__terms, __weights): (Vec<#elem_ident>, Vec<__W>) = if __single_winner {
                    match #elem_ident::parse_via_wpda(__seg) {
                        Ok(__one) => (vec![__one], vec![<__W as Semiring>::one()]),
                        Err(_) => return None,
                    }
                } else {
                    match #elem_ident::parse_via_wpda_all_with_weights(__seg) {
                        Ok(__v) => __v,
                        Err(_) => return None,
                    }
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
/// ≥1 cross-cat operand. ROOT-D (2026-07-06) also admits RECEIVER-LED POSTFIX
/// (method-call) frames whose slot 0 is an OPERAND (the receiver) — those set
/// `leading_receiver_gated`.
struct ProjVariant {
    /// Surface enum-constructor label (e.g. `"POutputNil"` / `"NQuoteShort"` /
    /// `"MGet"`).
    label: String,
    /// The grammar-derived Literal/Operand skeleton (source order), slot 0 = σ
    /// (sigil-led / framed-list) OR the receiver operand (method frame).
    slots: Vec<ProjSlot>,
    /// ROOT-D: slot 0 is a `.`-left-recursive RECEIVER operand (a method-call
    /// frame like `m:Proc "." "get" "(" k ")"`). When set, the leading operand is
    /// matched GREEDY-LAST (rightmost depth-0 delimiter — the method `.` is unique
    /// there, so left-assoc CHAINS recover) and the receiver is soundness-gated (a
    /// depth-0-whitespace STRING pre-filter + the AST decline of
    /// `receiver_decline_labels`). FALSE for sigil-led (slot 0 = Literal) and
    /// framed-list (slot 0 = a channel Name that is NOT left-recursive via its
    /// delimiter) variants — those keep greedy-first / no gate (byte-identical).
    leading_receiver_gated: bool,
    /// Decline-set top-ctor labels for the gated receiver's category (empty unless
    /// `leading_receiver_gated`): binary-infix / prefix rules producing that
    /// category. A sub-parsed receiver whose top ctor is one of these is NOT the
    /// whole receiver (`Map() % @X` → `Mod`, `-Nil` → `NegProc`) ⇒ the AST gate
    /// drops it ⇒ the frame declines ⇒ monolithic (sound).
    receiver_decline_labels: Vec<String>,
    /// ROOT-P (Fix A / P1): one flag per skeleton slot (parallel to `slots`). TRUE
    /// at an operand slot whose following delimiter δ is AMBIGUOUS for the operand's
    /// category (δ producible at depth 0 in it — `category_produces_delim_at_depth0`),
    /// so `PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM` enumerates that operand's boundary
    /// instead of committing greedy-first. FALSE for `Lit` slots, the last operand
    /// (no following δ), and non-ambiguous δ (byte-boundary is unique ⇒ greedy-first).
    ambiguous_by_slot: Vec<bool>,
    /// ROOT-1 (design a9fbeefe): slot 0 is a NON-ident sigil literal (`@`/`*`/`-`/`(`
    /// …) — the `σ`-led projection shapes. Consumed by
    /// [`super::forks::PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT`]: when a `sigil_led`
    /// variant's enumerating matcher returns a non-empty whole-input tiling set the
    /// helper marks `__sigil_frame_matched`, and if EVERY tiling then fails to parse
    /// (no cap hit) it signals a DEFINITIVE reject rather than falling to the
    /// fork-exploding walker. FALSE for framed-list (slot 0 = scalar Name operand)
    /// and method-frame (slot 0 = receiver operand) variants — those are never the
    /// authoritative-reject trigger (their decline stays `None` → walker/monolithic).
    sigil_led: bool,
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

/// Grammar-derived DISTINCT first-bytes of a projection shape's σ-led variants'
/// leading literal (`@`/`*`/`-`/`(` …) — the projection sigils the category admits.
/// SINGLE SOURCE OF TRUTH shared by the authoritative-reject `starts_with_sigil`
/// gate (`emit_projection_isolation`) AND the ROOT-P recognizer pre-pass gate
/// (`emit_recognizer_prefilter`), so both fire on exactly the same σ-led domain. No
/// token hardcode — the bytes come straight from the grammar's leading literals.
fn proj_sigil_lead_bytes(shape: &ProjIsoShape) -> Vec<u8> {
    let mut bs: Vec<u8> = shape
        .variants
        .iter()
        .filter(|v| v.sigil_led)
        .filter_map(|v| match v.slots.first() {
            Some(ProjSlot::Lit(l)) => l.as_bytes().first().copied(),
            _ => None,
        })
        .collect();
    bs.sort_unstable();
    bs.dedup();
    bs
}

/// ROOT-D: is `cat` LEFT-RECURSIVE via the literal `delim`? I.e. does the grammar
/// have a rule producing `cat` whose syntax pattern begins with a `Param` of
/// category `cat` IMMEDIATELY followed by `Literal(delim)` (`cat delim … : cat`)?
/// This is precisely what lets a receiver-led operand's delimiter (the method `.`)
/// occur at depth 0 WITHIN the operand (method chains `a.b().c()`), so the leading
/// operand must be matched GREEDY-LAST rather than greedy-first. FALSE for a send
/// channel (`Name "!" …` — no `Name "!" … : Name` rule) ⇒ those keep greedy-first
/// (byte-identical). GRAMMAR-DERIVED, no hardcode.
fn category_left_recursive_via(language: &LanguageDef, cat: &str, delim: &str) -> bool {
    for rule in &language.terms {
        if rule.category.to_string() != cat {
            continue;
        }
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        let (Some(tc), Some(sp)) = (&normalized.term_context, &normalized.syntax_pattern) else {
            continue;
        };
        let (Some(SyntaxExpr::Param(p)), Some(SyntaxExpr::Literal(l))) = (sp.first(), sp.get(1))
        else {
            continue;
        };
        if l != delim {
            continue;
        }
        let p_cat = tc.iter().find_map(|tp| match tp {
            TermParam::Simple { name, ty } if name == p => sep_base_ty(ty),
            _ => None,
        });
        if p_cat.as_deref() == Some(cat) {
            return true;
        }
    }
    false
}

/// ROOT-P (Fix A / P1): can some term of category `cat` produce the literal `delim`
/// at BRACKET-DEPTH 0 — transitively through its DEPTH-0 cross-cat operands? This is
/// the AMBIGUOUS-BOUNDARY test consumed by `PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM`. When
/// TRUE, an operand of category `cat` that a frame skeleton delimits by `delim` can
/// itself CONTAIN `delim` at depth 0 (e.g. a send receiver `p:Proc` = `@Nil!(…)`
/// whose own `!` sits at depth 0), so the single greedy-first boundary mis-splits
/// and the matcher must ENUMERATE candidate boundaries. GRAMMAR-DERIVED (walks the
/// grammar tracking bracket depth via the openers `([{`/`{|` and closers `)]}`/`|}`
/// counted per literal), no token hardcode. Depth-0 `Param`s enqueue their operand
/// category (a depth-0 operand can itself carry `delim` at depth 0 — the transitive
/// case). `Op` (`.*sep`/`#opt`) operands are bracketed in every projection frame, so
/// they are NOT enqueued (a false negative here only leaves the pre-fix greedy
/// boundary — never unsound, since enumeration only ADDS valid whole-input splits).
fn category_produces_delim_at_depth0(language: &LanguageDef, cat: &str, delim: &str) -> bool {
    // Net bracket delta of a literal: (#openers − #closers) over its bytes, so a
    // multi-char collection delimiter (`{|` → +1, `|}` → −1) balances correctly.
    let depth_delta = |l: &str| -> i32 {
        l.bytes().fold(0i32, |d, c| match c {
            b'(' | b'[' | b'{' => d + 1,
            b')' | b']' | b'}' => d - 1,
            _ => d,
        })
    };
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut work: Vec<String> = vec![cat.to_string()];
    while let Some(c) = work.pop() {
        if !seen.insert(c.clone()) {
            continue;
        }
        for rule in &language.terms {
            if rule.category.to_string() != c {
                continue;
            }
            let mut normalized = rule.clone();
            mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
            let (Some(tc), Some(sp)) = (&normalized.term_context, &normalized.syntax_pattern)
            else {
                continue;
            };
            let mut depth: i32 = 0;
            for expr in sp {
                match expr {
                    SyntaxExpr::Literal(l) => {
                        // A non-bracket literal EQUAL to `delim` seen while depth==0
                        // ⇒ `cat` produces `delim` at depth 0.
                        if depth == 0 && depth_delta(l) == 0 && l == delim {
                            return true;
                        }
                        depth += depth_delta(l);
                    }
                    SyntaxExpr::Param(name) => {
                        if depth == 0 {
                            if let Some(pcat) = tc.iter().find_map(|tp| match tp {
                                TermParam::Simple { name: n, ty } if n == name => sep_base_ty(ty),
                                _ => None,
                            }) {
                                work.push(pcat);
                            }
                        }
                    }
                    SyntaxExpr::Op(_) => {}
                }
            }
        }
    }
    false
}

/// ROOT-D: the DECLINE-set labels for a receiver of category `cat` — rules
/// producing `cat` whose syntax pattern is a BINARY INFIX (`[Param, Literal,
/// Param]`) or a UNARY PREFIX (`[Literal, Param]`). A method-frame receiver whose
/// sub-parsed top ctor is one of these binds LOOSER than (`Mod`, `NegProc`) — or is
/// ambiguity-prone w.r.t. — the postfix `.`, so it is NOT the whole receiver span
/// (Stage-0 S0-SOUND: `Map() % @X . concat` = `Mod`, `-Nil . concat` = `NegProc`).
/// The AST gate DROPS such readings ⇒ the frame declines ⇒ monolithic (sound).
/// GRAMMAR-DERIVED (pure syntax-shape), no operator-token hardcode.
fn compute_receiver_decline_labels(language: &LanguageDef, cat: &str) -> Vec<String> {
    let mut labels = Vec::new();
    for rule in &language.terms {
        if rule.category.to_string() != cat {
            continue;
        }
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        let Some(sp) = &normalized.syntax_pattern else { continue };
        let is_binary_infix = sp.len() == 3
            && matches!(
                (&sp[0], &sp[1], &sp[2]),
                (SyntaxExpr::Param(_), SyntaxExpr::Literal(_), SyntaxExpr::Param(_))
            );
        let is_unary_prefix = sp.len() == 2
            && matches!((&sp[0], &sp[1]), (SyntaxExpr::Literal(_), SyntaxExpr::Param(_)));
        if is_binary_infix || is_unary_prefix {
            labels.push(normalized.label.to_string());
        }
    }
    labels
}

/// ROOT-D: is `sp` a RECEIVER-LED POSTFIX (method-call) frame — slot 0 an OPERAND
/// (`Param`), the LAST slot a closing-bracket `Literal`? The closing-bracket tail
/// EXCLUDES binary-infix (`a OP b` ends in a `Param`); a `Literal`-first prefix has
/// slot 0 = Literal (not Param) so is excluded too. So this admits `m . get ( k )`
/// / `m . keys ( )` / sends (`n ! ( a , bs )`, already covered by the framed-list
/// clause — same variant, harmless) but not `a | b` / `- a`. GRAMMAR-DERIVED.
fn is_receiver_led_postfix_frame(sp: &[SyntaxExpr]) -> bool {
    let Some(SyntaxExpr::Param(_)) = sp.first() else { return false };
    matches!(sp.last(), Some(SyntaxExpr::Literal(l)) if matches!(l.as_str(), ")" | "]" | "}"))
}

/// Derive the [`ProjIsoShape`] for `cat_name`, or `None` when the category has no
/// isolation-eligible `@`-projection rule (grammar-derived — single source of
/// truth). Accepts every rule whose syntax pattern is a pure Literal/Param
/// sequence beginning with a NON-ident sigil and carrying ≥1 `Base`-typed Param,
/// OR (ROOT-D, gated by `METHOD_FRAME_ISOLATION`) a RECEIVER-LED POSTFIX method
/// frame (slot 0 = Operand, last slot = closing bracket).
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
        //   (c) ROOT-D (gated by `METHOD_FRAME_ISOLATION`): a RECEIVER-LED POSTFIX
        //       (method-call) frame — slot 0 an OPERAND, the LAST slot a closing
        //       bracket (`m "." "get" "(" k ")"`, `m "." "keys" "(" ")"`). Its
        //       leading receiver is matched greedy-last + soundness-gated below.
        //       The tail bracket excludes binary-infix (ends in a Param); a prefix
        //       has slot 0 = Literal (caught by (a)). Sends match here too but are
        //       already covered by (b) — same variant, and their leading channel is
        //       NOT `.`-left-recursive so the gate flag stays false (byte-identical).
        let method_frame =
            super::forks::METHOD_FRAME_ISOLATION && is_receiver_led_postfix_frame(sp);
        if !(sigil_led || (vec_sep_count == 1 && !sep_owned) || method_frame) {
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
        // ROOT-D: a method frame's leading receiver operand needs greedy-last +
        // the soundness gate iff slot 0 is an Operand whose category is
        // LEFT-RECURSIVE via the slot-1 delimiter literal (so the delimiter — the
        // method `.` — can recur at depth 0 inside it: `a.b().c()`). Sends
        // (channel Name, delimiter `!`, no `Name "!" … : Name` rule) get `false`
        // ⇒ greedy-first / no gate, unchanged.
        let (leading_receiver_gated, receiver_decline_labels) = match (slots.first(), slots.get(1)) {
            (Some(ProjSlot::Operand { category }), Some(ProjSlot::Lit(delim)))
                if category_left_recursive_via(language, category, delim) =>
            {
                (true, compute_receiver_decline_labels(language, category))
            }
            _ => (false, Vec::new()),
        };
        // ROOT-P (Fix A / P1): per-slot ambiguous-boundary flags. An operand slot at
        // k ≥ 1 is ambiguous iff its following delimiter δ is producible at depth 0
        // in the operand's category (so the operand can contain δ and greedy-first
        // mis-splits). k == 0 (sigil Lit, or a method receiver matched greedy-last)
        // is never enumerated. The last operand (no following δ) runs to end.
        let ambiguous_by_slot: Vec<bool> = slots
            .iter()
            .enumerate()
            .map(|(k, s)| {
                if k == 0 {
                    return false;
                }
                let opcat = match s {
                    ProjSlot::Operand { category } => Some(category.as_str()),
                    ProjSlot::SepList { element_category, .. } => Some(element_category.as_str()),
                    ProjSlot::Lit(_) => None,
                };
                let Some(opcat) = opcat else { return false };
                let delim = slots[k + 1..].iter().find_map(|s2| match s2 {
                    ProjSlot::Lit(l) => Some(l.as_str()),
                    _ => None,
                });
                match delim {
                    Some(d) => category_produces_delim_at_depth0(language, opcat, d),
                    None => false,
                }
            })
            .collect();
        variants.push(ProjVariant {
            label: normalized.label.to_string(),
            slots,
            leading_receiver_gated,
            receiver_decline_labels,
            ambiguous_by_slot,
            // ROOT-1: carry the already-computed `sigil_led` (slot-0 non-ident
            // literal) so the arm/helper can mark `__sigil_frame_matched`.
            sigil_led,
        });
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
    let in_set = if grammar_derived_isolation_enabled() {
        eligible_family(language, IsoFamily::Proj, cat_name, categories)
    } else {
        super::forks::PROJ_ISOLATION_CATEGORIES.contains(&cat_name)
    };
    if super::forks::PROJ_ISOLATION_COMBINE && in_set {
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
            // `true` ⇒ compose per-operand SINGLE-winners (== monolithic single
            // result; see the helper's scalar-operand note, bug 2318).
            if std::env::var_os("PRATTAIL_NO_PROJ_ISOLATION").is_none() {
                if let Some((__piso_terms, __piso_weights)) = #helper_name(input, true) {
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
            // `false` ⇒ ambiguity-preserving all-path per operand (cartesian).
            if std::env::var_os("PRATTAIL_NO_PROJ_ISOLATION").is_none() {
                if let Some(__piso) = #helper_name(input, false) {
                    return Ok(__piso);
                }
            }
        },
    }
}

/// ROOT-P RECOGNIZER PRE-PASS (non-parseability oracle a166789b, gated by
/// [`super::forks::RECOGNIZER_PREFILTER`]). Emit the STRING-entry `parse_via_wpda`
/// FALL-THROUGH FALLBACK fragment for `cat_name`: the SINGLE-WINNER seam's poly-time
/// definitive fast-reject for the σ-led hard cases the authoritative-reject fails
/// safe on. Interpolated by `gen/mod.rs` at the fall-through point (AFTER
/// `proj_reject_fire`, BEFORE `lex_dag` — where the proj/sep/infix prologues + the
/// authoritative-reject have all DECLINED and a known-hard σ-led span is about to
/// hit the walker). Calls the module-scope `recognize_<Cat>_reachable_ws` facade fn
/// (emitted by [`emit_parse_fns`]) on the SAME token-source shape the guarded walker
/// path uses. OFF / non-proj / no-σ-led-variant ⇒ empty ⇒ BYTE-IDENTICAL. See the
/// const doc for the soundness argument (REJECT-only over-approximation) and the
/// σ-led gate rationale (not every parse — no ~2× on easy parses).
pub(crate) fn emit_recognizer_prefilter(
    cat_name: &str,
    language: &LanguageDef,
    categories: &[String],
) -> TokenStream {
    // Gate 1 (compile-time master): OFF ⇒ nothing ⇒ byte-identical.
    if !super::forks::RECOGNIZER_PREFILTER {
        return quote! {};
    }
    // Gate 2 (shape): only a derivable `@`-projection category can strand a σ-led
    // hard span; non-proj categories emit nothing.
    let Some(shape) = projection_iso_shape(language, cat_name, categories) else {
        return quote! {};
    };
    // Gate 3 (σ-led variants): a proj category with only framed-list / method-frame
    // variants (no σ-led leading literal) has no projection sigil to gate on ⇒
    // nothing to guard (it can never strand a σ-led hard span).
    let sigil_lead_bytes = proj_sigil_lead_bytes(&shape);
    if sigil_lead_bytes.is_empty() {
        return quote! {};
    }
    let recognize_ws_fn_name = format_ident!("recognize_{}_reachable_ws", cat_name);
    let byte_lits = sigil_lead_bytes.iter().map(|b| quote! { #b });
    // Runtime σ-led gate: the SAME grammar-derived projection-sigil set the
    // authoritative-reject's `starts_with_sigil` uses. NON-σ-led inputs skip the
    // recognizer entirely.
    let starts_with_sigil: TokenStream =
        quote! { matches!(input.trim_start().as_bytes().first(), Some(#(#byte_lits)|*)) };
    quote! {
        // ── ROOT-P RECOGNIZER PRE-PASS (non-parseability oracle a166789b) ──
        // FALL-THROUGH FALLBACK: the proj/sep/infix isolation prologues AND the
        // authoritative-reject have all DECLINED. A σ-led span reaching HERE has
        // already FAILED isolation ⇒ it is a KNOWN-HARD case about to drive the GLR
        // walker (potentially ≈`8^d`). Run the one-sided non-parseability recognizer
        // on the SAME token source the guarded walker path uses; a DEFINITIVE
        // `Unreachable` (`false`) ⇒ return the parse `Err` in poly time. REJECT-ONLY:
        // ANY doubt (true / max-steps inconclusive / a lex failure / env A-B) falls
        // through to the walker UNCHANGED (never a false reject). Gated on the trimmed
        // input starting with a grammar-derived projection sigil so NON-σ-led easy
        // parses skip it entirely (not ~2×'d). `PRATTAIL_NO_RECOGNIZER_PREFILTER` =
        // causal A-B suppress (no rebuild).
        if #starts_with_sigil
            && std::env::var_os("PRATTAIL_NO_RECOGNIZER_PREFILTER").is_none()
        {
            // Self-contained: mirror the body's dispatch below so the recognized
            // token stream is IDENTICAL to the walker's (a `LatticeTokenSource` when
            // `lex_dag(input)` is ambiguous, else the `SliceTokenSource` kinds/texts
            // shape). A `lex_dag`/`lex` failure here ⇒ inconclusive ⇒ do NOT reject
            // (the body's own `lex_dag(input)?` below surfaces the real lex error).
            if let Ok(__recog_dag) = lex_dag(input) {
                let __recog_reachable = if __recog_dag.has_ambiguity() {
                    let __recog_src =
                        mettail_prattail::wpda_runtime::LatticeTokenSource::new(__recog_dag);
                    #recognize_ws_fn_name(&__recog_src, 0, 1_000_000usize)
                } else {
                    match lex(input) {
                        Ok(__recog_tokens) => {
                            let __recog_kinds: Vec<mettail_prattail::automata::TokenKind> =
                                __recog_tokens
                                    .iter()
                                    .map(|(__t, _)| token_to_kind(__t))
                                    .collect();
                            let __recog_texts: Vec<&str> = __recog_tokens
                                .iter()
                                .map(|(__t, __r)| token_text(__t, input, *__r))
                                .collect();
                            let __recog_src =
                                mettail_prattail::wpda_runtime::SliceTokenSource::with_texts(
                                    &__recog_kinds,
                                    &__recog_texts,
                                );
                            #recognize_ws_fn_name(&__recog_src, 0, 1_000_000usize)
                        }
                        // lex failed ⇒ inconclusive ⇒ don't reject (fall to walker).
                        Err(_) => true,
                    }
                };
                if !__recog_reachable {
                    return Err(ParseError::UnexpectedToken {
                        expected: Cow::Borrowed(
                            "no valid parse: the non-parseability recognizer proved this span has no reachable accepting configuration",
                        ),
                        found: input
                            .trim_start()
                            .chars()
                            .next()
                            .map(|__c| __c.to_string())
                            .unwrap_or_else(|| "end of input".to_string()),
                        range: Range::from_byte_offsets(input, 0, input.len()),
                        hint: Some(Cow::Borrowed(
                            "recognizer fast-reject: a coarse SOUND over-approximation of the parser found this category unreachable for the input",
                        )),
                    });
                }
            }
        }
    }
}

/// ROOT-P / false-reject RECOGNIZER REJECT-GATE (non-parseability oracle a166789b,
/// gated by [`super::forks::RECOGNIZER_REJECT_GATE`]). Emit the recognizer-GATED form
/// of the authoritative-reject FIRE fragment for `cat_name`: the `parse_via_wpda`
/// prologue's `if __proj_sigil_reject { … }` block, but the reject `Err` returns ONLY
/// when the SOUND non-parseability recognizer CONFIRMS the span `Unreachable`
/// (`false`). Reachable / budget-exceeded / lex-fail / env-A-B ⇒ SUPPRESS the reject
/// and fall through to the full walker (never a false reject).
///
/// This is the PRINCIPLED replacement for the crude unconditional auth-reject: it
/// FIXES the false-reject of valid non-send `@`-quoted binds (`@([]) <= @(Map())`)
/// AND fast-rejects genuinely-unparseable deep-`@` spans (the recognizer converges
/// `Unreachable` in poly time before the exponential walker is reached).
///
/// Invoked ONLY where `__proj_sigil_reject` is already set — the σ-frame-matched
/// clean-decline residual — so it is inherently narrow (NOT every σ-led parse), and
/// the STAGE-2 coarse-frontier non-convergence costs at most the bounded
/// [`super::forks::RECOGNIZER_GATE_MAX_STEPS`] on those rare reject-candidate spans
/// (which fall through to the walker anyway). Calls the module-scope
/// `recognize_<Cat>_reachable_ws` facade fn (co-emitted under the widened gate). The
/// caller (`gen/mod.rs`) emits this ONLY when `RECOGNIZER_REJECT_GATE` is ON AND the
/// category is proj-eligible; OFF ⇒ the caller emits the VERBATIM unconditional
/// reject ⇒ byte-identical.
pub(crate) fn emit_recognizer_reject_gate(cat_name: &str) -> TokenStream {
    let recognize_ws_fn_name = format_ident!("recognize_{}_reachable_ws", cat_name);
    let max_steps = super::forks::RECOGNIZER_GATE_MAX_STEPS;
    quote! {
        if __proj_sigil_reject {
            // ── RECOGNIZER REJECT-GATE (non-parseability oracle a166789b) ──
            // The authoritative-reject WANTS to fire (a σ-led send skeleton matched
            // the whole input, enumeration was COMPLETE, and NO tiling parsed). But
            // that heuristic FALSE-REJECTS valid non-send `@`-quoted binds like
            // `@([]) <= @(Map())`. Confirm with the SOUND non-parseability recognizer:
            // fire the reject ONLY IF the recognizer proves the span `Unreachable`
            // (`false`). Reachable / budget-exceeded / lex-fail ⇒ SUPPRESS (fall
            // through to the full walker — never a false reject). Env
            // `PRATTAIL_NO_RECOGNIZER_REJECT_GATE` = causal A/B: revert to the
            // unconditional reject (today's behavior) without a rebuild.
            let __recog_confirms_unreachable = if
                std::env::var_os("PRATTAIL_NO_RECOGNIZER_REJECT_GATE").is_some()
            {
                // A/B disabled ⇒ the ORIGINAL unconditional reject (recognizer not run).
                true
            } else if let Ok(__recog_dag) = lex_dag(input) {
                // Mirror the walker's own dispatch so the recognized token stream is
                // IDENTICAL to the walker's (a `LatticeTokenSource` when `lex_dag` is
                // ambiguous, else the `SliceTokenSource` kinds/texts shape).
                let __reachable = if __recog_dag.has_ambiguity() {
                    let __recog_src =
                        mettail_prattail::wpda_runtime::LatticeTokenSource::new(__recog_dag);
                    #recognize_ws_fn_name(&__recog_src, 0, #max_steps)
                } else {
                    match lex(input) {
                        Ok(__recog_tokens) => {
                            let __recog_kinds: Vec<mettail_prattail::automata::TokenKind> =
                                __recog_tokens
                                    .iter()
                                    .map(|(__t, _)| token_to_kind(__t))
                                    .collect();
                            let __recog_texts: Vec<&str> = __recog_tokens
                                .iter()
                                .map(|(__t, __r)| token_text(__t, input, *__r))
                                .collect();
                            let __recog_src =
                                mettail_prattail::wpda_runtime::SliceTokenSource::with_texts(
                                    &__recog_kinds,
                                    &__recog_texts,
                                );
                            #recognize_ws_fn_name(&__recog_src, 0, #max_steps)
                        }
                        // lex failed ⇒ inconclusive ⇒ don't confirm (suppress reject).
                        Err(_) => true,
                    }
                };
                // `false` (Unreachable) ⇒ the recognizer CONFIRMS the reject.
                !__reachable
            } else {
                // `lex_dag` failed ⇒ inconclusive ⇒ suppress the reject and fall
                // through (the body's own `lex_dag(input)?` below surfaces the real
                // lex error — still a fast reject, never a false accept).
                false
            };
            if __recog_confirms_unreachable {
                return Err(ParseError::UnexpectedToken {
                    expected: Cow::Borrowed(
                        "no valid parse: a projection-sigil-led send frame whose operands do not parse",
                    ),
                    found: input
                        .trim_start()
                        .chars()
                        .next()
                        .map(|__c| __c.to_string())
                        .unwrap_or_else(|| "end of input".to_string()),
                    range: Range::from_byte_offsets(input, 0, input.len()),
                    hint: Some(Cow::Borrowed(
                        "an `@`-led span that is not a well-formed send (or infix of sends) is not a valid term",
                    )),
                });
            }
        }
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
    has_method: bool,
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

    // ROOT-1 (design a9fbeefe): the authoritative-reject machinery. When ON, the
    // materialization caps also set `__cap_hit` (so an INCOMPLETE enumeration never
    // triggers a reject) and a matched `sigil_led` variant sets `__sigil_frame_matched`.
    // OFF ⇒ both fragments are EMPTY ⇒ the cap sites + arm are byte-identical.
    let reject_on = super::forks::PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT;
    let set_cap_hit: TokenStream = if reject_on {
        quote! { __cap_hit = true; }
    } else {
        quote! {}
    };
    // Emitted only for `sigil_led` variants when ON: mark that a σ-led send skeleton
    // matched the WHOLE input (≥1 tiling). The decline site turns this into a reject.
    let set_sigil_matched: TokenStream = if reject_on && variant.sigil_led {
        quote! {
            if !__assignments.is_empty() {
                __sigil_frame_matched = true;
            }
        }
    } else {
        quote! {}
    };

    // ROOT-D method-frame gate pieces (empty for sigil-led / framed-list variants).
    let gated = variant.leading_receiver_gated;
    // The gated receiver's category (slot 0 = the first Operand) + the AST
    // decline pattern (`Cat::Add(..) | Cat::Mod(..) | Cat::NegProc(..) | …`).
    let decline_pat: Option<TokenStream> =
        if gated && !variant.receiver_decline_labels.is_empty() {
            variant
                .slots
                .iter()
                .find_map(|s| match s {
                    ProjSlot::Operand { category } => Some(format_ident!("{}", category)),
                    _ => None,
                })
                .map(|rcat| {
                    let arms: Vec<TokenStream> = variant
                        .receiver_decline_labels
                        .iter()
                        .map(|lbl| {
                            let l = format_ident!("{}", lbl);
                            quote! { #rcat::#l(..) }
                        })
                        .collect();
                    quote! { #(#arms)|* }
                })
        } else {
            None
        };

    // Bind each operand: a `Scalar` sub-parses the whole region; a `Sep` splits
    // the region at the depth-0 separator, sub-parses each element, and cartesian-
    // combines into `Vec<Element>` combos. Both bind a `__op{oi}` : Vec<(value,
    // weight)> where `value` is `Term` (scalar) or `Vec<Element>` (list).
    let mut parse_binds: Vec<TokenStream> = Vec::with_capacity(n_ops);
    for (oi, slot) in op_slots.iter().enumerate() {
        let pairs_id = format_ident!("__op{}", oi);
        // The gated receiver is the FIRST operand of a method frame.
        let is_gated_receiver = gated && oi == 0;
        match slot {
            OpKind::Scalar(cat) => {
                let ocat = format_ident!("{}", cat);
                let ocat_str = cat.to_string();
                // ROOT-D receiver STRING pre-filter: decline (cheaply, before the
                // sub-parse) when the receiver span has depth-0 whitespace — a
                // space-surrounded infix/prefix operator at the top (`a % b`,
                // `not a`) means the method `.` is NOT the whole receiver.
                // Primaries have NO depth-0 whitespace (args are bracketed).
                let recv_ws_gate: TokenStream = if is_gated_receiver {
                    quote! {
                        {
                            let __rb = __seg.as_bytes();
                            let mut __d: i32 = 0;
                            let mut __has_ws = false;
                            for &__c in __rb {
                                match __c {
                                    b'(' | b'[' | b'{' => __d += 1,
                                    b')' | b']' | b'}' => __d -= 1,
                                    _ if __d == 0 && __c.is_ascii_whitespace() => {
                                        __has_ws = true;
                                        break;
                                    }
                                    _ => {}
                                }
                            }
                            if __has_ws {
                                // ROOT-1 (a9fbeefe): this is a STRUCTURAL receiver
                                // gate (a depth-0 whitespace ⇒ the method `.` is not
                                // the whole receiver), NOT a genuine operand parse-Err.
                                // Mark enumeration incomplete (`__cap_hit`) so the
                                // authoritative-reject never escalates this decline to
                                // `Err` — it must fall to the walker. Empty when the
                                // reject const is OFF ⇒ byte-identical.
                                #set_cap_hit
                                break '__variant;
                            }
                        }
                    }
                } else {
                    quote! {}
                };
                // ROOT-D receiver AST gate: drop sub-parsed receiver readings whose
                // top ctor is a binary-infix / prefix (NOT the whole receiver —
                // e.g. `-Nil` → `NegProc`). If none survive ⇒ decline the frame.
                let recv_ast_filter: TokenStream = match (is_gated_receiver, &decline_pat) {
                    (true, Some(pat)) => quote! {
                        let __pairs: Vec<(#ocat, __W)> = __t
                            .into_iter()
                            .zip(__w.into_iter())
                            .filter(|(__r, _)| !matches!(__r, #pat))
                            .collect();
                        if __pairs.is_empty() {
                            // ROOT-1 (a9fbeefe): STRUCTURAL AST gate (every receiver
                            // reading top-ctor'd to a binary-infix/prefix ⇒ not the
                            // whole receiver), NOT a genuine parse-Err. Mark incomplete
                            // so the authoritative-reject falls to the walker.
                            #set_cap_hit
                            break '__variant;
                        }
                        __pairs
                    },
                    _ => quote! { __t.into_iter().zip(__w.into_iter()).collect() },
                };
                parse_binds.push(quote! {
                    let #pairs_id: Vec<(#ocat, __W)> = {
                        let (__s, __e) = __ops[#oi];
                        let __seg = input[__s..__e].trim();
                        // ROOT-1 (a9fbeefe): empty operand segment is a STRUCTURAL
                        // decline (a degenerate/empty tiling boundary), NOT a genuine
                        // parse-Err ⇒ mark incomplete so the reject falls to the walker.
                        if __seg.is_empty() { #set_cap_hit break '__variant; }
                        #recv_ws_gate
                        // SINGLE-RESULT seam (bug 2318): compose the operand's OWN
                        // single-winner (`parse_via_wpda` → the same M6 min-weight
                        // representative the monolithic parser elects), NOT the
                        // all-path min. The all-path `_all_with_weights` min can
                        // differ from the single-winner (e.g. a nested `@Nil!(q)`
                        // whose all-set ranks the spurious channel-named-`Nil`
                        // `POutputQuoted` first on the `open_len` maximal-munch tie
                        // while `parse_via_wpda` elects `POutputNil`), so a
                        // divide-and-conquer single result built from all-path
                        // per-operand mins diverges from monolithic. Composing
                        // per-operand single-winners keeps the proj-iso single
                        // result == monolithic (proj-iso operands are bracket-
                        // delimited ⇒ their disambiguation is LOCAL ⇒ compositional).
                        // The ALL seam keeps the ambiguity-preserving all-path.
                        let (__t, __w): (Vec<#ocat>, Vec<__W>) = if __single_winner {
                            match #ocat::parse_via_wpda(__seg) {
                                Ok(__one) => (vec![__one], vec![<__W as Semiring>::one()]),
                                Err(_) => {
                                    break '__variant;
                                }
                            }
                        } else {
                            match #ocat::parse_via_wpda_all_with_weights(__seg) {
                                Ok(__v) => __v,
                                Err(_) => {
                                    break '__variant;
                                }
                            }
                        };
                        // ROOT-1 (a9fbeefe): a successful sub-parse that yielded ZERO
                        // readings is STRUCTURAL (post-`Ok` empty; dead in the single-
                        // winner seam where `__t = vec![__one]`), NOT a parse-Err ⇒
                        // mark incomplete (fail-safe).
                        if __t.is_empty() { #set_cap_hit break '__variant; }
                        #recv_ast_filter
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
                        // ROOT-1 (a9fbeefe): empty SepList region is STRUCTURAL, NOT a
                        // parse-Err ⇒ mark incomplete so the reject falls to the walker.
                        if __region.is_empty() { #set_cap_hit break '__variant; }
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
                            // ROOT-1 (a9fbeefe): an empty ELEMENT segment is STRUCTURAL
                            // (a trailing/consecutive separator — `@Nil!(0,)` splits
                            // `"0,"` into `["0",""]`; the grammar's `args.*sep(",")`
                            // ACCEPTS a trailing separator and the walker parses it),
                            // NOT a genuine operand parse-Err. Mark incomplete so the
                            // authoritative-reject never escalates it to `Err` and it
                            // falls to the walker (the authoritative/complete parser).
                            if __eseg.is_empty() { #set_cap_hit break '__variant; }
                            // SINGLE-RESULT seam (bug 2318): per-element single-winner
                            // (see the scalar-operand note above). Keeps the framed-
                            // list single result == monolithic; ALL seam stays all-path.
                            let (__et, __ew): (Vec<#ecat>, Vec<__W>) = if __single_winner {
                                match #ecat::parse_via_wpda(__eseg) {
                                    Ok(__one) => (vec![__one], vec![<__W as Semiring>::one()]),
                                    Err(_) => {
                                        break '__variant;
                                    }
                                }
                            } else {
                                match #ecat::parse_via_wpda_all_with_weights(__eseg) {
                                    Ok(__v) => __v,
                                    Err(_) => {
                                        break '__variant;
                                    }
                                }
                            };
                            // ROOT-1 (a9fbeefe): post-`Ok` empty element readings is
                            // STRUCTURAL (dead in the single-winner seam), NOT a parse-
                            // Err ⇒ mark incomplete (fail-safe).
                            if __et.is_empty() { #set_cap_hit break '__variant; }
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
                                        // ROOT-1: the enumeration was cut short ⇒ mark
                                        // `__cap_hit` so the decline stays `None` (never
                                        // an authoritative reject — a valid parse may
                                        // be hidden past the cap).
                                        #set_cap_hit
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
                // ROOT-1 (a9fbeefe): no combos survived for this operand slot —
                // STRUCTURAL (defensive; the per-operand binds already `break` on a
                // genuine Err), NOT a parse-Err ⇒ mark incomplete (fail-safe).
                #set_cap_hit
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
    // Per-operand HOLE cost on the framing PRIMARY (bug 2318). Each cross-cat
    // operand a variant covers is a parse "hole"; the monolithic walker charges
    // a cross-cat dispatch cost for every hole and matches a fixed literal for
    // FREE. So among variants that cover the SAME span, the one with FEWER holes
    // (MORE fixed literals) — the more-SPECIFIC reading — must win the single-
    // result min, matching monolithic's specific-rule preference. Canonical
    // case: `@Nil!(q)` is BOTH `POutputNil(q)` (skeleton `@ Nil ! ( ⟨q⟩ )`,
    // 1 hole, the `Nil` keyword a LITERAL) and `POutputQuoted(NVar("Nil"), q)`
    // (skeleton `@ ⟨n⟩ ! ( ⟨q⟩ )`, 2 holes, `Nil` parsed as a channel-named-Nil
    // NVar operand) — semantically DISTINCT (`NQuote(PZero)` vs `NQuote(PVar
    // "Nil")`), so they never dedup; the winner must be the specific reading.
    //
    // The old `from_cost(0.0, …)` framing was tropical `one()` (primary 0.0), so
    // `Semiring::times`' identity short-circuit DROPPED the `variant_idx`
    // tiebreak and the winner fell to the (incommensurate) operand sub-parse
    // weights — which, on a primary tie, elected `POutputQuoted` by `src_idx`
    // (Name < Proc). Through the `parse_structured` display-fixpoint reparse of
    // `@Nil!(q)` this locked in the spurious channel-named-`Nil` send (bug 2318:
    // `query_receive_sugar_with_{arithmetic,string}_guard`).
    //
    // A tiny per-hole ε (≪ any BP-tier cost so it never overrides a genuine
    // operand cost difference; ≫ the f64 tropical-sum noise floor ~1e-6 so it
    // is not swamped) charges the extra hole on the PRIMARY *and* makes the
    // framing NON-identity, so on a primary tie `variant_idx` (the most-
    // specific-first sort order) is the operative tiebreak.
    //
    // APPLIED ONLY IN THE SINGLE-RESULT SEAM (`__single_winner`). In the ALL
    // seam the framing MUST stay tropical `one()` (cost 0.0) so the ⊕-min dedup
    // representative and weight-sort are BYTE-IDENTICAL to the pre-2318 helper —
    // otherwise the ε perturbs which eval-equal representative each semantic key
    // keeps, diverging the ambiguity-preserving alt-SET from the monolithic
    // `_all` (the `atproj_flip_soundness_ab` ON≡OFF gate). The single seam
    // composes per-operand SINGLE-winners (operand weights are `one()`), so the
    // framing is the ONLY discriminator there and MUST be non-identity to elect
    // the fewest-holes (most-specific) variant; the all seam keeps the genuine
    // per-operand weights and needs no framing bias.
    const PROJ_HOLE_EPSILON: f64 = 1e-5;
    let hole_cost: f64 = n_ops as f64 * PROJ_HOLE_EPSILON;
    let mut body = quote! {
        if __candidates.len() >= __REALIZE_CAP {
            // ROOT-1: cap reached with ≥ CAP genuine candidates — the span is
            // parseable (many ways); decline to the walker (which re-derives them).
            // Mark `__cap_hit` so this is never mistaken for an authoritative reject.
            #set_cap_hit
            return None;
        }
        let __framing = if __single_winner {
            __W::from_cost(#hole_cost, __RESULT_SRC_IDX, #variant_idx_lit)
        } else {
            __W::from_cost(0.0, __RESULT_SRC_IDX, #variant_idx_lit)
        };
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

    // ROOT-D: the leading receiver of a method frame matches GREEDY-LAST; and the
    // whole method-frame arm is skippable at runtime (causal A/B) via
    // `PRATTAIL_NO_METHOD_ISOLATION`. The matcher's greedy-last param exists ONLY
    // when this category has method frames (`has_method`) — otherwise the call is
    // byte-identical to the pre-ROOT-D `__proj_skeleton_match(bytes, n, skel)`.
    let skel_match_call: TokenStream = if has_method {
        let greedy_last_lit = gated;
        quote! { __proj_skeleton_match(__bytes, __n, __SKEL, #greedy_last_lit) }
    } else {
        quote! { __proj_skeleton_match(__bytes, __n, __SKEL) }
    };
    let method_ab_gate: TokenStream = if gated {
        quote! {
            if __no_method_iso {
                // ROOT-1 (a9fbeefe): the `PRATTAIL_NO_METHOD_ISOLATION` A/B gate is a
                // STRUCTURAL bail (debug knob), NOT a parse-Err ⇒ mark incomplete so a
                // forced-off method arm never leaves a spurious authoritative-reject.
                #set_cap_hit
                break '__variant;
            }
        }
    } else {
        quote! {}
    };

    // ROOT-P (Fix A / P1). When `PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM` is ON, emit the
    // ENUMERATING arm: the matcher returns ALL whole-input operand tilings (branching
    // at ambiguous-δ slots), and the arm runs the SAME per-operand binds + combine
    // for EACH tiling, reusing `'__variant` as the PER-ASSIGNMENT label (a
    // `break '__variant` skips THIS tiling and the `for` moves to the next; `#body`
    // pushes into the SHARED `__candidates`, so tilings UNION for the ALL seam and
    // the SINGLE seam min-weights over them). When OFF, emit the pre-P1 single-
    // assignment arm VERBATIM (byte-identical). The `__AMB` slice (parallel to
    // `__SKEL`) is the grammar-derived per-slot ambiguous-boundary flags.
    let enum_on = super::forks::PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM;
    if enum_on {
        let amb_exprs: Vec<TokenStream> = variant
            .ambiguous_by_slot
            .iter()
            .map(|b| quote! { #b })
            .collect();
        let match_all_call: TokenStream = if has_method {
            let greedy_last_lit = gated;
            quote! { __proj_skeleton_match_all(__bytes, __n, __SKEL, __AMB, #greedy_last_lit) }
        } else {
            quote! { __proj_skeleton_match_all(__bytes, __n, __SKEL, __AMB) }
        };
        quote! {
            {
                // Match this variant's skeleton; enumerate ALL operand tilings.
                const __SKEL: &[__Slot] = &[ #(#slot_exprs),* ];
                const __AMB: &[bool] = &[ #(#amb_exprs),* ];
                let __assignments: Vec<Vec<(usize, usize)>> = #match_all_call;
                // ROOT-1: a σ-led send skeleton matched the whole input ⇒ record it,
                // so an all-tilings-fail decline becomes an authoritative reject
                // (empty when OFF / non-sigil ⇒ byte-identical).
                #set_sigil_matched
                for __ops_vec in __assignments.iter() {
                    let __ops: &[(usize, usize)] = &__ops_vec[..];
                    '__variant: {
                        #method_ab_gate
                        #(#parse_binds)*
                        #body
                    }
                }
            }
        }
    } else {
        quote! {
            {
                // Match this variant's skeleton; extract operand ranges.
                const __SKEL: &[__Slot] = &[ #(#slot_exprs),* ];
                '__variant: {
                    #method_ab_gate
                    let Some(__ops) = #skel_match_call else {
                        break '__variant;
                    };
                    #(#parse_binds)*
                    #body
                }
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
    // ROOT-D: this category carries method frames iff ANY variant is a gated
    // receiver-led frame. When it does NOT (every non-`Proc` rhocalc category, and
    // EVERY calculator category, and EVERY category when `METHOD_FRAME_ISOLATION`
    // is OFF), the matcher/`__no_method_iso` additions are elided ⇒ the emitted
    // helper is BYTE-IDENTICAL to the pre-ROOT-D baseline.
    let has_method = shape.variants.iter().any(|v| v.leading_receiver_gated);
    let variant_arms: Vec<TokenStream> = shape
        .variants
        .iter()
        .enumerate()
        .map(|(vi, v)| emit_proj_variant_arm(cat_ident, v, vi, has_method))
        .collect();

    // The greedy-last matcher param + the `__no_method_iso` A/B read exist ONLY
    // when the category has method frames (byte-identical otherwise).
    let no_method_binding: TokenStream = if has_method {
        quote! {
            // ROOT-D causal A/B — read ONCE per helper call (NOT per method arm; a
            // per-arm `env::var_os` would be a hot-path regression). When set, every
            // method-frame variant arm short-circuits, reproducing the pre-ROOT-D
            // (monolithic) path without a rebuild.
            let __no_method_iso =
                std::env::var_os("PRATTAIL_NO_METHOD_ISOLATION").is_some();
        }
    } else {
        quote! {}
    };
    // Matcher signature + the greedy-last fragments, elided when !has_method.
    let recv_param: TokenStream =
        if has_method { quote! { leading_greedy_last: bool, } } else { quote! {} };
    let greedy_last_decl: TokenStream = if has_method {
        quote! { let greedy_last = k == 0 && leading_greedy_last; }
    } else {
        quote! {}
    };
    // In the "delimiter found" block: greedy-first always breaks; greedy-last keeps
    // scanning for a LATER depth-0 delimiter.
    let found_break: TokenStream = if has_method {
        quote! { if !greedy_last { break; } }
    } else {
        quote! { break; }
    };
    // On a depth-0 (unbalanced) close: greedy-first ⇒ no match; greedy-last ⇒ stop
    // and use the last delimiter found so far.
    let unbalanced_close: TokenStream = if has_method {
        quote! {
            if greedy_last {
                break;
            }
            return None;
        }
    } else {
        quote! { return None; }
    };
    // The matcher's greedy-last doc paragraph — emitted ONLY with method frames so
    // the OFF / non-method matcher doc is byte-identical to the pre-ROOT-D baseline.
    let matcher_rootd_doc: TokenStream = if has_method {
        quote! {
            ///
            /// ROOT-D: when `leading_greedy_last` is set, the FIRST slot (`k == 0`,
            /// a method-frame RECEIVER operand) is delimited by the RIGHTMOST
            /// depth-0 occurrence of its delimiter (the method `.` — which is the
            /// unique rightmost depth-0 `.` since the args are bracketed), so a
            /// left-assoc method CHAIN (`a.b().c()`) binds the WHOLE prefix
            /// `a.b()` as the receiver. All other operands stay greedy-first.
        }
    } else {
        quote! {}
    };

    // PROJ_ISO_LITERAL_RUN_ANCHOR (2026-07-06): the InputBind query-frame
    // `@@`-CHANNEL fix. When ON, emit the `__match_lit_run` helper + a per-call A/B
    // env read + anchor each operand's right boundary on the FULL consecutive
    // literal run (not just the single next literal). When OFF, all three pieces
    // fold away ⇒ the emitted matcher is BYTE-IDENTICAL to the pre-fix single-
    // literal boundary. See `super::forks::PROJ_ISO_LITERAL_RUN_ANCHOR`.
    let run_anchor_on = super::forks::PROJ_ISO_LITERAL_RUN_ANCHOR;
    let run_anchor_helper: TokenStream = if run_anchor_on {
        quote! {
            /// Match the MAXIMAL run of consecutive `Lit` slots of `skel` starting
            /// at slot `ks`, from byte `p0` (whitespace-flexible, with the SAME
            /// word-boundary rule as the main `Lit` arm), returning the byte
            /// position AFTER the last matched literal, or `None` if any literal in
            /// the run fails. Anchors an operand's right boundary on the FULL fixed-
            /// literal frame (not just the first literal) so an operand that itself
            /// contains the first delimiter char at depth 0 (`@@Nil!()` — the
            /// channel's own send `!`) is not split early. The run stops at the next
            /// `Op` slot.
            fn __match_lit_run(
                bytes: &[u8],
                n: usize,
                skel: &[__Slot],
                ks: usize,
                p0: usize,
            ) -> Option<usize> {
                let mut p = p0;
                let mut k = ks;
                while k < skel.len() {
                    match &skel[k] {
                        __Slot::Lit(l) => {
                            while p < n && bytes[p].is_ascii_whitespace() {
                                p += 1;
                            }
                            let lb = l.as_bytes();
                            if p + lb.len() > n || &bytes[p..p + lb.len()] != lb {
                                return None;
                            }
                            if lb.iter().all(|&c| __is_word(c)) {
                                let before_ok = p == 0 || !__is_word(bytes[p - 1]);
                                let after_ok =
                                    p + lb.len() == n || !__is_word(bytes[p + lb.len()]);
                                if !(before_ok && after_ok) {
                                    return None;
                                }
                            }
                            p += lb.len();
                            k += 1;
                        }
                        __Slot::Op => break,
                    }
                }
                Some(p)
            }
        }
    } else {
        quote! {}
    };
    let run_anchor_env: TokenStream = if run_anchor_on {
        quote! {
            // Per-call A/B (`PRATTAIL_NO_PROJ_RUN_ANCHOR`): when set, reproduce the
            // pre-fix single-literal boundary. The matcher runs O(variants)/parse
            // (the non-hot isolation prologue), so a per-call read is negligible.
            let __no_run_anchor =
                std::env::var_os("PRATTAIL_NO_PROJ_RUN_ANCHOR").is_some();
        }
    } else {
        quote! {}
    };
    // The `if wb { … }` boundary-accept block: ON anchors on the full literal run;
    // OFF is the verbatim pre-fix single-literal accept (byte-identical).
    let run_anchor_wb_guard: TokenStream = if run_anchor_on {
        quote! {
            // Accept this depth-0 delimiter position ONLY when the FULL literal run
            // (all `Lit` slots after this `Op`) also matches here — so a channel
            // whose own send `!` sits at depth 0 (`@@Nil!()`) is not split at that
            // `!` (which is followed by `(`, not the query run `! ? (`).
            let __run_ok = __no_run_anchor
                || __match_lit_run(bytes, n, skel, k + 1, j).is_some();
            if wb && __run_ok {
                found = Some(j);
                #found_break
            }
        }
    } else {
        quote! {
            if wb {
                found = Some(j);
                #found_break
            }
        }
    };

    // ROOT-P (Fix A / P1): the matcher. `PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM` OFF ⇒ the
    // pre-P1 single-assignment `__proj_skeleton_match` VERBATIM (byte-identical). ON
    // ⇒ the ENUMERATING `__proj_skeleton_match_all`, which returns ALL whole-input
    // operand tilings, branching at ambiguous-δ slots (`amb[k]`) over run-anchor-
    // passing depth-0 boundaries; the runtime env `PRATTAIL_NO_PROJ_BOUNDARY_ENUM`
    // collapses it back to single greedy-first (causal A/B without a rebuild).
    let enum_on = super::forks::PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM;
    let (matchall_recv_param, matchall_lgl_arg): (TokenStream, TokenStream) = if has_method {
        (quote! { leading_greedy_last: bool, }, quote! { leading_greedy_last })
    } else {
        (quote! {}, quote! { false })
    };
    let matchall_run_ok: TokenStream = if run_anchor_on {
        quote! { no_run_anchor || __match_lit_run(bytes, n, skel, k + 1, j).is_some() }
    } else {
        quote! { true }
    };
    let matchall_no_run_anchor: TokenStream = if run_anchor_on {
        quote! { std::env::var_os("PRATTAIL_NO_PROJ_RUN_ANCHOR").is_some() }
    } else {
        quote! { false }
    };
    let matcher_off: TokenStream = quote! {
        /// Match `skel` against `bytes[0..n]`, returning the byte-range of each
        /// `Op` slot, or `None` if the skeleton does not match. Operands are
        /// delimited by the NEXT literal at bracket-depth 0 (standard ASCII
        /// brackets `([{`/`)]}`; multi-char collection delimiters balance via
        /// their `{`/`}` component). A depth-0 close that is NOT the delimiter
        /// ⇒ unbalanced ⇒ `None` (this variant does not match).
        #matcher_rootd_doc
        fn __proj_skeleton_match(
            bytes: &[u8],
            n: usize,
            skel: &[__Slot],
            #recv_param
        ) -> Option<Vec<(usize, usize)>> {
            #run_anchor_env
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
                                // ROOT-D: the leading receiver of a method frame
                                // (`k == 0`) takes the RIGHTMOST depth-0
                                // delimiter; every other operand the first.
                                #greedy_last_decl
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
                                        // greedy-first breaks here; greedy-last keeps
                                        // scanning for a LATER depth-0 delimiter (the
                                        // delimiter char is not a bracket ⇒ depth
                                        // unaffected below). PROJ_ISO_LITERAL_RUN_ANCHOR
                                        // gates whether the boundary anchors on the full
                                        // literal run.
                                        #run_anchor_wb_guard
                                    }
                                    match c {
                                        b'(' | b'[' | b'{' => depth += 1,
                                        b')' | b']' | b'}' => {
                                            if depth == 0 {
                                                // Unbalanced depth-0 close: for
                                                // greedy-first no valid delimiter
                                                // precedes it (`None`); for
                                                // greedy-last the operand cannot
                                                // extend past it ⇒ stop and use
                                                // the last delimiter found so far.
                                                #unbalanced_close
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
    };
    let matcher_on: TokenStream = quote! {
        /// ROOT-P (Fix A / P1): ENUMERATE ALL whole-input operand tilings of `skel`
        /// against `bytes[0..n]`. Each returned `Vec<(usize,usize)>` is one tiling
        /// (a byte-range per `Op` slot, in order). At an AMBIGUOUS-δ operand slot
        /// (`amb[k]`) it BRANCHES over every run-anchor-passing depth-0 δ boundary
        /// (the operand can itself contain δ — a nested send `@Nil!(…)`); at a
        /// non-ambiguous slot it commits the single greedy-first boundary (`k == 0`
        /// method receiver keeps greedy-last), so a grammar with no ambiguous δ
        /// tiles exactly as the pre-P1 matcher. Whole-input consumption + the
        /// caller's per-operand sub-parse are the soundness filter (invalid tilings
        /// yield no candidate). `PRATTAIL_NO_PROJ_BOUNDARY_ENUM` forces greedy-first.
        fn __proj_skeleton_match_all(
            bytes: &[u8],
            n: usize,
            skel: &[__Slot],
            amb: &[bool],
            #matchall_recv_param
        ) -> Vec<Vec<(usize, usize)>> {
            let no_run_anchor = #matchall_no_run_anchor;
            let no_boundary_enum =
                std::env::var_os("PRATTAIL_NO_PROJ_BOUNDARY_ENUM").is_some();
            fn go(
                bytes: &[u8],
                n: usize,
                skel: &[__Slot],
                amb: &[bool],
                k: usize,
                i0: usize,
                leading_greedy_last: bool,
                no_run_anchor: bool,
                no_boundary_enum: bool,
            ) -> Vec<Vec<(usize, usize)>> {
                let mut i = i0;
                while i < n && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }
                if k == skel.len() {
                    let mut j = i;
                    while j < n && bytes[j].is_ascii_whitespace() {
                        j += 1;
                    }
                    return if j == n { vec![vec![]] } else { vec![] };
                }
                match &skel[k] {
                    __Slot::Lit(l) => {
                        let lb = l.as_bytes();
                        if i + lb.len() > n || &bytes[i..i + lb.len()] != lb {
                            return vec![];
                        }
                        if lb.iter().all(|&c| __is_word(c)) {
                            let before_ok = i == 0 || !__is_word(bytes[i - 1]);
                            let after_ok =
                                i + lb.len() == n || !__is_word(bytes[i + lb.len()]);
                            if !(before_ok && after_ok) {
                                return vec![];
                            }
                        }
                        go(
                            bytes, n, skel, amb, k + 1, i + lb.len(),
                            leading_greedy_last, no_run_anchor, no_boundary_enum,
                        )
                    }
                    __Slot::Op => {
                        let next_lit: Option<&'static str> =
                            skel[k + 1..].iter().find_map(|s| match s {
                                __Slot::Lit(l) => Some(*l),
                                __Slot::Op => None,
                            });
                        let start = i;
                        match next_lit {
                            None => {
                                let mut subs = go(
                                    bytes, n, skel, amb, k + 1, n,
                                    leading_greedy_last, no_run_anchor, no_boundary_enum,
                                );
                                for a in subs.iter_mut() {
                                    a.insert(0, (start, n));
                                }
                                subs
                            }
                            Some(l) => {
                                let lb = l.as_bytes();
                                let identish = lb.iter().all(|&c| __is_word(c));
                                let greedy_last = k == 0 && leading_greedy_last;
                                let enumerate = amb[k] && !no_boundary_enum && !greedy_last;
                                let mut cands: Vec<usize> = Vec::new();
                                let mut depth: i32 = 0;
                                let mut j = start;
                                while j < n {
                                    let c = bytes[j];
                                    if depth == 0
                                        && j + lb.len() <= n
                                        && &bytes[j..j + lb.len()] == lb
                                    {
                                        let wb = !identish
                                            || ((j == 0 || !__is_word(bytes[j - 1]))
                                                && (j + lb.len() == n
                                                    || !__is_word(bytes[j + lb.len()])));
                                        let __run_ok = #matchall_run_ok;
                                        if wb && __run_ok {
                                            cands.push(j);
                                            if !enumerate && !greedy_last {
                                                break;
                                            }
                                        }
                                    }
                                    match c {
                                        b'(' | b'[' | b'{' => depth += 1,
                                        b')' | b']' | b'}' => {
                                            if depth == 0 {
                                                break;
                                            }
                                            depth -= 1;
                                        }
                                        _ => {}
                                    }
                                    j += 1;
                                }
                                if greedy_last {
                                    match cands.last() {
                                        Some(&last) => cands = vec![last],
                                        None => cands.clear(),
                                    }
                                }
                                let mut out: Vec<Vec<(usize, usize)>> = Vec::new();
                                for &end in cands.iter() {
                                    let mut subs = go(
                                        bytes, n, skel, amb, k + 1, end,
                                        leading_greedy_last, no_run_anchor, no_boundary_enum,
                                    );
                                    for a in subs.iter_mut() {
                                        a.insert(0, (start, end));
                                    }
                                    out.append(&mut subs);
                                }
                                out
                            }
                        }
                    }
                }
            }
            go(
                bytes, n, skel, amb, 0, 0,
                #matchall_lgl_arg, no_run_anchor, no_boundary_enum,
            )
        }
    };
    let matcher_def: TokenStream = if enum_on { matcher_on } else { matcher_off };

    // ── ROOT-1 AUTHORITATIVE-REJECT (design a9fbeefe) ──
    // The two runtime bookkeeping locals + the reject-aware decline. OFF ⇒ every
    // fragment is empty / the pre-fix `return None` VERBATIM ⇒ byte-identical.
    let reject_on = super::forks::PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT;
    // Grammar-derived DISTINCT first-bytes of the σ-led variants' leading literal
    // (`@`/`*`/`-`/`(` …) — the projection sigils this category admits. No hardcode.
    // Shared with the ROOT-P recognizer pre-pass gate (`emit_recognizer_prefilter`).
    let sigil_lead_bytes: Vec<u8> = proj_sigil_lead_bytes(shape);
    // Declared whenever ON (the cap sites reference `__cap_hit` regardless of shape;
    // `__sigil_frame_matched` stays false for a category with no σ-led variant ⇒ that
    // category never rejects). `#[allow(unused_assignments)]` on the helper covers the
    // never-read case.
    let reject_locals: TokenStream = if reject_on {
        quote! {
            // ROOT-1 authoritative-reject bookkeeping.
            let mut __sigil_frame_matched = false;
            let mut __cap_hit = false;
        }
    } else {
        quote! {}
    };
    // The reject-aware decline is emitted ONLY for a category that actually has σ-led
    // variants (`!sigil_lead_bytes.is_empty()`); a proj category with only framed-list
    // / method-frame variants keeps the plain `return None` decline (it can never
    // authoritatively reject). `reject_locals` still declares both locals whenever ON
    // (the cap sites reference `__cap_hit`); an unread local is covered by the helper's
    // `#[allow(unused_variables, unused_assignments)]`.
    let decline: TokenStream = if reject_on && !sigil_lead_bytes.is_empty() {
        let byte_lits = sigil_lead_bytes.iter().map(|b| quote! { #b });
        let starts_with_sigil: TokenStream =
            quote! { matches!(__bytes.first(), Some(#(#byte_lits)|*)) };
        quote! {
            if __candidates.is_empty() {
                // ROOT-1 AUTHORITATIVE-REJECT: a σ-led send skeleton matched the whole
                // input (`__sigil_frame_matched`), enumeration was COMPLETE (`!__cap_hit`),
                // the trimmed input starts with a projection sigil, and NO tiling parsed
                // ⇒ the span is provably not a send. Signal a definitive reject (the
                // prologue turns it into `Err` — but only AFTER the infix prologue also
                // declines, so an infix-of-sends like `@Nil!(0) or @Nil!(0)` is still
                // recovered) instead of falling to the fork-exploding walker. SINGLE
                // seam only; `PRATTAIL_NO_PROJ_AUTHORITATIVE_REJECT` suppresses it (A/B).
                if __single_winner
                    && __sigil_frame_matched
                    && !__cap_hit
                    && #starts_with_sigil
                    && std::env::var_os("PRATTAIL_NO_PROJ_AUTHORITATIVE_REJECT").is_none()
                {
                    __proj_sigil_reject_set();
                }
                return None;
            }
        }
    } else {
        quote! {
            if __candidates.is_empty() {
                return None;
            }
        }
    };

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
            __single_winner: bool,
        ) -> Option<(
            Vec<#cat_ident>,
            Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
        )> {
            use mettail_prattail::automata::semiring::Semiring;
            type __W = mettail_prattail::automata::lex_weight::LexicographicWeight;
            const __REALIZE_CAP: usize = 64;
            const __RESULT_SRC_IDX: u16 = #result_src_idx;
            #no_method_binding

            // One skeleton slot: a fixed literal token or a cross-cat operand hole.
            enum __Slot {
                Lit(&'static str),
                Op,
            }
            fn __is_word(c: u8) -> bool {
                c.is_ascii_alphanumeric() || c == b'_'
            }
            #run_anchor_helper
            #matcher_def

            let input = input.trim();
            let __bytes = input.as_bytes();
            let __n = __bytes.len();
            if __n == 0 {
                return None;
            }

            let mut __candidates: Vec<(#cat_ident, __W)> = Vec::new();
            #reject_locals
            #(#variant_arms)*

            #decline

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
            Some((__out_terms, __out_weights))
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// P3 PRECEDENCE-AWARE BINARY-INFIX OPERAND ISOLATION+COMBINE CODEGEN
// (ROOT-2 `or`/PParInfix locus, 2026-07-06) — the THIRD sibling of the P2
// `.*sep` (list) and P1 `@`-projection (frame) isolators. Where those linearize
// LIST / FRAME operands, this linearizes the two operands of a TOP-LEVEL BINARY
// INFIX operator. Gate: `super::forks::INFIX_ISOLATION_COMBINE` +
// `INFIX_ISOLATION_CATEGORIES`.
//
// The root defect: `@Nil!!(true, @Nil!() / @Nil!()) or X` (a polyadic persistent
// send with a division-arg as the LEFT operand of `or`) dies monolithically ("no
// accepting branch reached end of input") — the GLR frontier does not RECONVERGE
// across the infix-operand boundary, though each operand parses in isolation and
// simpler `or`s parse. Stage-0 (2026-07-06) PROVED that splitting at the
// PRECEDENCE-correct root operator, parsing each operand in TRUE ISOLATION (its own
// walker from ROOT — recurses through proj/sep/infix), and combining via the
// operator's binary ctor is (a) SOUND (== monolithic on every case monolithic
// handles: 11/11 + 10/10 precedence/associativity) and (b) LINEAR (~const per
// operand vs the monolithic explosion; recovered BOTH counterexamples).
// ════════════════════════════════════════════════════════════════════════

/// One homogeneous binary-infix operator a category admits, with the precedence +
/// associativity read from the binding-power table (the SAME source the walker's
/// InfixLoop consumes — `build_bp_table`). `left_bp`/`right_bp` encode precedence
/// (`min(left_bp,right_bp)` = the Pratt level, LOWER = looser) and associativity
/// (`left_bp < right_bp` ⇒ left-assoc ⇒ split at the RIGHTMOST occurrence;
/// `left_bp > right_bp` ⇒ right-assoc ⇒ LEFTMOST).
struct InfixOp {
    /// Operator terminal text (e.g. `"or"`, `"|"`, `"<="`).
    terminal: String,
    /// Constructor label (e.g. `"Or"`, `"PParInfix"`, `"LtEq"`).
    label: String,
    left_bp: u8,
    right_bp: u8,
}

/// Grammar-derived shape of a category's HOMOGENEOUS (`operand == result == cat`)
/// binary-infix operator set that the isolation helper root-splits. Cross-category
/// comparisons (`Int×Int→Bool`) are NOT admitted (not chainable at one category —
/// they fall to the monolithic path, sound). Derived from `build_bp_table` — no
/// per-language / per-rule hardcode.
pub(crate) struct InfixIsoShape {
    /// `src_idx` of the RESULT category (== operand category — homogeneous).
    result_src_idx: u16,
    /// The admitted operators, in ORIGINAL binding-power (declaration) order — the
    /// index into this vec is the stable `op_idx` the ctor `match` dispatches on.
    ops: Vec<InfixOp>,
}

/// Derive the [`InfixIsoShape`] for `cat_name`, or `None` when the category has no
/// homogeneous binary-infix operator (grammar-derived — the single source of truth
/// for the emitted helper + prologues). Reads the binding-power table (same as the
/// walker) and keeps only `!postfix && !mixfix` operators whose operand AND result
/// category are `cat_name` (homogeneous, chainable).
fn derive_infix_iso_shape(
    language: &LanguageDef,
    cat_name: &str,
    categories: &[String],
) -> Option<InfixIsoShape> {
    let src_idx_of =
        |name: &str| -> Option<u16> { categories.iter().position(|c| c == name).map(|i| i as u16) };
    let result_src_idx = src_idx_of(cat_name)?;

    let bp_table = super::infix::build_bp_table(language);
    let mut ops: Vec<InfixOp> = Vec::new();
    for op in &bp_table.operators {
        // Homogeneous, chainable binary infix ONLY: operand category == result
        // category == this category, and not a postfix / mixfix operator.
        if op.is_postfix || op.is_mixfix {
            continue;
        }
        if op.category != cat_name || op.result_category != cat_name {
            continue;
        }
        // A binary infix has distinct left/right bp (left-assoc `<`, right-assoc
        // `>`); equal bp would be a degenerate/postfix entry — skip.
        if op.left_bp == op.right_bp {
            continue;
        }
        ops.push(InfixOp {
            terminal: op.terminal.clone(),
            label: op.label.clone(),
            left_bp: op.left_bp,
            right_bp: op.right_bp,
        });
    }
    if ops.is_empty() {
        return None;
    }
    Some(InfixIsoShape { result_src_idx, ops })
}

/// The module-scope identifier of the binary-infix isolation helper for `cat_name`.
pub(crate) fn infix_isolation_helper_ident(cat_name: &str) -> proc_macro2::Ident {
    format_ident!("__mettail_wpda_infix_isolate_all_{}", cat_name)
}

/// The gated binary-infix isolation shape for `cat_name`: `Some` iff the master
/// switch is ON, the category is in the include set, AND a shape is derivable.
/// The SINGLE source of truth shared by the helper emitter (facade) and the
/// string-entry prologue emitter (mod.rs).
pub(crate) fn infix_iso_shape(
    language: &LanguageDef,
    cat_name: &str,
    categories: &[String],
) -> Option<InfixIsoShape> {
    let in_set = if grammar_derived_isolation_enabled() {
        eligible_family(language, IsoFamily::Infix, cat_name, categories)
    } else {
        super::forks::INFIX_ISOLATION_CATEGORIES.contains(&cat_name)
    };
    if super::forks::INFIX_ISOLATION_COMBINE && in_set {
        derive_infix_iso_shape(language, cat_name, categories)
    } else {
        None
    }
}

/// Emit the guarded string-entry prologue that calls the binary-infix isolation
/// helper with the RAW input string (before `lex_dag`). Runtime A/B:
/// `PRATTAIL_NO_INFIX_ISOLATION` forces the monolithic path without a rebuild.
/// Wired AFTER the proj + sep prologues (mutually-exclusive by input shape: proj /
/// sep consume a WHOLE frame / list; infix needs a depth-0 operator with BOTH
/// operands present — a pure frame/atom finds no depth-0 infix ⇒ declines here).
pub(crate) fn emit_infix_isolation_prologue(
    helper_name: &proc_macro2::Ident,
    seam: SepSeam,
) -> TokenStream {
    match seam {
        SepSeam::Single => quote! {
            // P3 INFIX ISOLATION prologue (ROOT-2 `or`) — single winner.
            // `true` ⇒ compose per-operand SINGLE-winners (== monolithic single
            // result; operands are precedence-delimited ⇒ LOCAL disambiguation ⇒
            // compositional — Stage-0 sound 11/11).
            if std::env::var_os("PRATTAIL_NO_INFIX_ISOLATION").is_none() {
                if let Some((__iiso_terms, __iiso_weights)) = #helper_name(input, true) {
                    if let Some((__t, _)) = __iiso_terms
                        .into_iter()
                        .zip(__iiso_weights.into_iter())
                        .min_by(|(_, __a), (_, __b)| __a.cmp(__b))
                    {
                        return Ok(__t);
                    }
                }
            }
        },
        SepSeam::All => quote! {
            // P3 INFIX ISOLATION prologue (ROOT-2 `or`) — full alt set.
            // `false` ⇒ ambiguity-preserving all-path per operand (cartesian).
            if std::env::var_os("PRATTAIL_NO_INFIX_ISOLATION").is_none() {
                if let Some(__iiso) = #helper_name(input, false) {
                    return Ok(__iiso);
                }
            }
        },
    }
}

/// Emit the shared per-category STRING-level binary-infix isolation helper
/// `__mettail_wpda_infix_isolate_all_<Cat>(input, single_winner)`.
///
/// It elects the PRECEDENCE-correct ROOT operator (loosest depth-0 operator; among
/// its occurrences rightmost for left-assoc / leftmost for right-assoc), sub-parses
/// the LEFT and RIGHT operand spans through this category's own string entry (fresh
/// lex + walker from ROOT — RECURSES through every prologue incl proj/sep/infix),
/// wraps the cartesian-combined readings in the operator's binary ctor, then dedups
/// by semantic key + ⊕-min + weight-sort (the monolithic `_all` finalize). `None` ⇒
/// NOT-APPLICABLE (no depth-0 binary infix with both operands present) or ANY
/// sub-parse failure ⇒ the caller falls through to the UNMODIFIED monolithic body.
fn emit_infix_isolation(cat_ident: &proc_macro2::Ident, shape: &InfixIsoShape) -> TokenStream {
    let helper_name = infix_isolation_helper_ident(&cat_ident.to_string());
    let result_src_idx = shape.result_src_idx;

    // Runtime operator table entries `(terminal, prec, assoc_right, op_idx)`, ordered
    // by terminal LENGTH DESCENDING so the scan does MAXIMAL MUNCH (`>=` beats `>`,
    // `<=` beats `<`) — the first byte-match at a position is the longest operator.
    // `prec = min(left_bp,right_bp)` (LOWER = looser); `assoc_right = left_bp > right_bp`.
    let mut ordered: Vec<(usize, &InfixOp)> = shape.ops.iter().enumerate().collect();
    ordered.sort_by(|(_, a), (_, b)| b.terminal.len().cmp(&a.terminal.len()));
    let op_entries: Vec<TokenStream> = ordered
        .iter()
        .map(|(idx, op)| {
            let term = &op.terminal;
            let prec = op.left_bp.min(op.right_bp);
            let assoc_right = op.left_bp > op.right_bp;
            let idx_lit = *idx;
            quote! { (#term, #prec, #assoc_right, #idx_lit) }
        })
        .collect();

    // The ctor `match op_idx { … }` — each admitted operator's binary constructor.
    let ctor_arms: Vec<TokenStream> = shape
        .ops
        .iter()
        .enumerate()
        .map(|(idx, op)| {
            let label = format_ident!("{}", op.label);
            quote! {
                #idx => #cat_ident::#label(
                    std::sync::Arc::new(__l.clone()),
                    std::sync::Arc::new(__r.clone()),
                ),
            }
        })
        .collect();

    quote! {
        /// P3 PRECEDENCE-AWARE BINARY-INFIX ISOLATION+COMBINE (ROOT-2 `or`):
        /// STRING-level divide-and-conquer infix linearizer for the `#cat_ident`
        /// category. See `emit_infix_isolation` in the macro for the full rationale.
        #[allow(
            non_snake_case,
            unused_assignments,
            unused_variables,
            clippy::needless_range_loop,
            clippy::manual_is_ascii_check
        )]
        fn #helper_name(
            input: &str,
            __single_winner: bool,
        ) -> Option<(
            Vec<#cat_ident>,
            Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
        )> {
            use mettail_prattail::automata::semiring::Semiring;
            type __W = mettail_prattail::automata::lex_weight::LexicographicWeight;
            const __REALIZE_CAP: usize = 64;
            const __RESULT_SRC_IDX: u16 = #result_src_idx;
            // Operator table (maximal-munch order): `(terminal, prec, assoc_right, op_idx)`.
            const __OPS: &[(&str, u8, bool, usize)] = &[ #(#op_entries),* ];
            fn __is_word(c: u8) -> bool {
                c.is_ascii_alphanumeric() || c == b'_'
            }

            let input = input.trim();
            let __bytes = input.as_bytes();
            let __n = __bytes.len();
            if __n == 0 {
                return None;
            }

            // (1) Elect the ROOT operator: scan at bracket-depth 0 for operator
            //     terminals; keep the LOOSEST (min prec). Among equal-precedence
            //     occurrences: left-assoc (`!assoc_right`) ⇒ RIGHTMOST (later wins),
            //     right-assoc ⇒ LEFTMOST (earliest wins) — the exact Pratt root.
            //     A candidate is valid only with BOTH operands present AND a real
            //     LEFT operand (its last non-ws char is an operand terminal — word
            //     or close bracket — not another operator / open bracket; excludes a
            //     unary `-`/`*` sitting in operator position).
            let mut __best: Option<(u8, usize, usize, usize)> = None; // (prec, start, end, op_idx)
            {
                let mut __depth: i32 = 0;
                // STRING-LITERAL state: operator terminals inside a `"…"` string
                // literal (e.g. a `CastStr("a or b")` operand) are CONTENT, NOT
                // splits — skip them. A `"` toggles the state UNLESS escaped (an ODD
                // run of immediately-preceding backslashes; the display escapes an
                // inner `"` as `\"`). Brackets are also inert inside a string.
                let mut __in_str = false;
                let mut __i = 0usize;
                while __i < __n {
                    let __c = __bytes[__i];
                    if __c == b'"' {
                        let mut __bs = 0usize;
                        while __bs < __i && __bytes[__i - 1 - __bs] == b'\\' {
                            __bs += 1;
                        }
                        if __bs % 2 == 0 {
                            __in_str = !__in_str;
                        }
                        __i += 1;
                        continue;
                    }
                    if __in_str {
                        __i += 1;
                        continue;
                    }
                    match __c {
                        b'(' | b'[' | b'{' => {
                            __depth += 1;
                            __i += 1;
                            continue;
                        }
                        b')' | b']' | b'}' => {
                            __depth -= 1;
                            __i += 1;
                            continue;
                        }
                        _ => {}
                    }
                    if __depth == 0 {
                        let mut __matched: Option<(usize, u8, bool, usize)> = None; // (oplen, prec, assoc_right, op_idx)
                        for &(__term, __prec, __assoc_right, __op_idx) in __OPS {
                            let __tb = __term.as_bytes();
                            if __i + __tb.len() > __n || &__bytes[__i..__i + __tb.len()] != __tb {
                                continue;
                            }
                            // Word-boundary for identifier-shaped terminals (`or`, `and`,
                            // `bitor`) so `or` does not match inside `error`/`for`.
                            if __tb.iter().all(|&c| __is_word(c)) {
                                let __before_ok = __i == 0 || !__is_word(__bytes[__i - 1]);
                                let __after_ok = __i + __tb.len() == __n
                                    || !__is_word(__bytes[__i + __tb.len()]);
                                if !(__before_ok && __after_ok) {
                                    continue;
                                }
                            }
                            __matched = Some((__tb.len(), __prec, __assoc_right, __op_idx));
                            break; // maximal munch: longest terminal first
                        }
                        if let Some((__oplen, __prec, __assoc_right, __op_idx)) = __matched {
                            let __left = input[..__i].trim();
                            let __right = input[__i + __oplen..].trim();
                            let __left_is_operand = __left
                                .as_bytes()
                                .last()
                                // Operand terminal: identifier/number char, a closing
                                // bracket, or a closing string quote (`"foo"` operand).
                                .map(|&c| __is_word(c) || matches!(c, b')' | b']' | b'}' | b'"'))
                                .unwrap_or(false);
                            if !__left.is_empty() && !__right.is_empty() && __left_is_operand {
                                let __take = match __best {
                                    None => true,
                                    Some((__bp, _, _, _)) => {
                                        if __prec < __bp {
                                            true
                                        } else if __prec > __bp {
                                            false
                                        } else {
                                            // equal precedence: left-assoc ⇒ rightmost
                                            // (later replaces); right-assoc ⇒ leftmost.
                                            !__assoc_right
                                        }
                                    }
                                };
                                if __take {
                                    __best = Some((__prec, __i, __i + __oplen, __op_idx));
                                }
                            }
                            __i += __oplen;
                            continue;
                        }
                    }
                    __i += 1;
                }
            }
            let (_, __s0, __e0, __op_idx) = __best?;

            // (2) ISOLATED sub-parse of the LEFT + RIGHT operand spans via this
            //     category's own string entry (fresh lex + walker from ROOT —
            //     RECURSES through every prologue). Any Err / empty ⇒ None (fall to
            //     monolithic). SINGLE-RESULT seam composes per-operand single-winners
            //     (== monolithic); ALL seam keeps the ambiguity-preserving all-path.
            let __left = input[..__s0].trim();
            let __right = input[__e0..].trim();
            if __left.is_empty() || __right.is_empty() {
                return None;
            }
            let (__lt, __lw): (Vec<#cat_ident>, Vec<__W>) = if __single_winner {
                match #cat_ident::parse_via_wpda(__left) {
                    Ok(__one) => (vec![__one], vec![<__W as Semiring>::one()]),
                    Err(_) => return None,
                }
            } else {
                match #cat_ident::parse_via_wpda_all_with_weights(__left) {
                    Ok(__v) => __v,
                    Err(_) => return None,
                }
            };
            let (__rt, __rw): (Vec<#cat_ident>, Vec<__W>) = if __single_winner {
                match #cat_ident::parse_via_wpda(__right) {
                    Ok(__one) => (vec![__one], vec![<__W as Semiring>::one()]),
                    Err(_) => return None,
                }
            } else {
                match #cat_ident::parse_via_wpda_all_with_weights(__right) {
                    Ok(__v) => __v,
                    Err(_) => return None,
                }
            };
            if __lt.is_empty() || __rt.is_empty() {
                return None;
            }

            // (3) CARTESIAN COMBINE over the two operands (⊗-folded weights, cap 64),
            //     wrapped in the elected operator's binary ctor. Framing cost 0.0 is
            //     absorbed under ⊗ so the winner is the product of per-operand minima
            //     = the monolithic minimum.
            let __framing = __W::from_cost(0.0, __RESULT_SRC_IDX, __op_idx as u16);
            let mut __candidates: Vec<(#cat_ident, __W)> = Vec::new();
            for (__l, __wl) in __lt.iter().zip(__lw.iter()) {
                for (__r, __wr) in __rt.iter().zip(__rw.iter()) {
                    if __candidates.len() >= __REALIZE_CAP {
                        return None;
                    }
                    let __term = match __op_idx {
                        #(#ctor_arms)*
                        _ => return None,
                    };
                    __candidates.push((
                        __term,
                        Semiring::times(&Semiring::times(&__framing, __wl), __wr),
                    ));
                }
            }
            if __candidates.is_empty() {
                return None;
            }

            // (4) FINALIZE like the monolithic `_all`: dedup by semantic key,
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
            let (__out_terms, __out_weights): (Vec<_>, Vec<_>) = __paired.into_iter().unzip();
            Some((__out_terms, __out_weights))
        }
    }
}

/// ROOT-P MEMOIZED BEST-PARSE (design af7680e2, "3A LIGHT") — the SHARED
/// module-scope preamble: epoch/depth thread-locals + the RAII `__ProjMemoGuard`.
/// Emitted ONCE per language module (in [`emit_parse_fns`]), gated by
/// [`super::forks::PROJ_ISO_BESTPARSE_MEMO`] AND the presence of ≥1
/// isolation-eligible category — OFF ⇒ not emitted ⇒ byte-identical.
///
/// `__ProjMemoGuard::enter()` bumps `__PROJ_MEMO_EPOCH` (and refreshes the
/// `PRATTAIL_NO_PROJ_MEMO` bypass flag) ONLY on the OUTERMOST `parse_via_wpda`
/// entry (depth 0 → 1), distinguishing it from the nested isolation-recursion
/// sub-parses (depth ≥ 1). Each per-category memo map lazily clears when it
/// observes a stale epoch, so a memoized value never leaks across independent
/// top-level parses while every sub-parse WITHIN one top-level parse shares the
/// cache — collapsing the enumerating matcher's `O(n^{m·d})` recursion TREE into a
/// polynomial DAG. Mirrors the `runtime/src/binding.rs` BCG05_EPOCH /
/// clear_var_cache pattern. Referenced UNQUALIFIED from the `impl Cat` methods
/// (`gen/mod.rs`), which share this module's flat include scope.
fn emit_proj_memo_preamble() -> TokenStream {
    quote! {
        thread_local! {
            /// Bumped on the OUTERMOST `parse_via_wpda` entry; every memo map
            /// keys its validity on this so entries never cross top-level parses.
            static __PROJ_MEMO_EPOCH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
            /// Re-entrancy depth of `parse_via_wpda`. 0 → 1 marks the outermost
            /// call (epoch bump + env-bypass refresh); Drop decrements it.
            static __PROJ_MEMO_DEPTH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
            /// Snapshot of `PRATTAIL_NO_PROJ_MEMO` presence, read once per
            /// outermost parse (the isolation path is non-hot).
            static __PROJ_MEMO_BYPASS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
        }

        /// RAII epoch/depth guard for the ROOT-P memoized best-parse. Constructed
        /// at the top of every memoized `parse_via_wpda`; the depth counter (not a
        /// per-call flag) distinguishes the outermost parse from nested
        /// isolation-recursion sub-parses so the epoch is bumped exactly once per
        /// top-level parse.
        #[allow(dead_code)]
        struct __ProjMemoGuard;

        #[allow(dead_code)]
        impl __ProjMemoGuard {
            #[inline]
            fn enter() -> Self {
                __PROJ_MEMO_DEPTH.with(|__d| {
                    let __cur = __d.get();
                    if __cur == 0 {
                        // Outermost parse: start a fresh memo epoch and snapshot
                        // the runtime bypass switch once.
                        __PROJ_MEMO_EPOCH.with(|__e| __e.set(__e.get().wrapping_add(1)));
                        __PROJ_MEMO_BYPASS.with(|__b| {
                            __b.set(std::env::var_os("PRATTAIL_NO_PROJ_MEMO").is_some())
                        });
                    }
                    __d.set(__cur + 1);
                });
                __ProjMemoGuard
            }
            #[inline]
            fn epoch() -> u64 {
                __PROJ_MEMO_EPOCH.with(|__e| __e.get())
            }
            #[inline]
            fn bypassed() -> bool {
                __PROJ_MEMO_BYPASS.with(|__b| __b.get())
            }
        }

        impl Drop for __ProjMemoGuard {
            #[inline]
            fn drop(&mut self) {
                __PROJ_MEMO_DEPTH.with(|__d| __d.set(__d.get().saturating_sub(1)));
            }
        }
    }
}

/// ROOT-1 AUTHORITATIVE-REJECT (design a9fbeefe) — the module-scope thread-local
/// reject flag + its set/take accessors. Emitted ONCE per language module (in
/// [`emit_parse_fns`]), gated by [`super::forks::PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT`]
/// AND the presence of ≥1 `@`-projection-eligible category. OFF / none ⇒ not emitted
/// ⇒ byte-identical.
///
/// The isolation helper calls `__proj_sigil_reject_set()` at its decline when it
/// matched a whole-input σ-led send skeleton, enumeration was complete, and NO
/// tiling parsed (single-winner seam only). The `parse_via_wpda_uncached` prologue
/// calls `__proj_sigil_reject_take()` the statement AFTER the proj prologue declines
/// — it reads AND clears, so a nested operand sub-parse's flag is consumed by its
/// OWN prologue (never leaking to an enclosing frame). If the take returns `true`
/// AND the infix prologue then also declines, the prologue returns `Err` instead of
/// running the fork-exploding walker. Referenced UNQUALIFIED from the `impl Cat`
/// methods (`gen/mod.rs`) and the helper fns, which share this module's flat include
/// scope (mirrors `emit_proj_memo_preamble`).
fn emit_proj_sigil_reject_preamble() -> TokenStream {
    quote! {
        thread_local! {
            /// Set true by an isolation helper that AUTHORITATIVELY rejects a σ-led
            /// send frame; taken (read + cleared) by the prologue right after the
            /// proj prologue declines. Consume-once semantics keep nested sub-parse
            /// signals from leaking across frames.
            static __PROJ_SIGIL_REJECT: std::cell::Cell<bool> =
                const { std::cell::Cell::new(false) };
        }
        /// Mark that the current isolation-helper call authoritatively rejects.
        #[inline]
        #[allow(dead_code)]
        fn __proj_sigil_reject_set() {
            __PROJ_SIGIL_REJECT.with(|__c| __c.set(true));
        }
        /// Read AND clear the reject flag (consume-once).
        #[inline]
        #[allow(dead_code)]
        fn __proj_sigil_reject_take() -> bool {
            __PROJ_SIGIL_REJECT.with(|__c| __c.replace(false))
        }
    }
}

/// ROOT-P MEMOIZED BEST-PARSE (design af7680e2) — the PER-CATEGORY thread-local
/// memo map `__PROJ_MEMO_<Cat>` consulted by the memoized `Cat::parse_via_wpda`
/// (`gen/mod.rs`). Emitted in [`emit_parse_fns`] ONLY for isolation-eligible
/// categories when the master const is ON (byte-identical otherwise). The map is
/// keyed on the TRIMMED input content (`String`) and stores the FULL
/// `Result<Cat, ParseError>` (Ok AND Err — the latter is required for
/// polynomiality). The leading `u64` is the epoch the map's entries belong to;
/// a stale epoch triggers a lazy clear on next consult.
fn emit_proj_memo_thread_local(cat_ident: &proc_macro2::Ident) -> TokenStream {
    let memo_ident = format_ident!("__PROJ_MEMO_{}", cat_ident);
    quote! {
        thread_local! {
            #[allow(non_upper_case_globals, clippy::type_complexity)]
            static #memo_ident: std::cell::RefCell<(
                u64,
                std::collections::HashMap<
                    std::string::String,
                    Result<#cat_ident, mettail_prattail::runtime_types::ParseError>,
                >,
            )> = std::cell::RefCell::new((0, std::collections::HashMap::new()));
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
    // P0 conservative-extension oracle (runs once per language at codegen): the
    // GRAMMAR-DERIVED isolation-category sets EXACTLY equal the EFFECTIVE
    // hardcoded sets, so flipping `GRAMMAR_DERIVED_ISOLATION_CATEGORIES` is
    // byte-identical. Fires `debug_assert_eq!` on any drift (debug builds).
    debug_assert_isolation_oracle(language, categories);
    let mut fns = Vec::new();
    // ── ROOT-P MEMOIZED BEST-PARSE (design af7680e2, "3A LIGHT") ──
    // The shared epoch/depth thread-local preamble + RAII `__ProjMemoGuard` is
    // emitted ONCE per language module, and ONLY when the master const is ON AND
    // ≥1 category is isolation-eligible (`any_iso_eligible`). Gate: OFF ⇒ nothing
    // emitted ⇒ byte-identical. See `super::forks::PROJ_ISO_BESTPARSE_MEMO`.
    let memo_master_on = super::forks::PROJ_ISO_BESTPARSE_MEMO;
    let mut any_iso_eligible = false;
    // ROOT-1: whether ≥1 category emits an `@`-projection helper (which references
    // the reject accessors) ⇒ gates the module-scope reject preamble.
    let mut any_proj_eligible = false;
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
        // ROOT-P RECOGNIZER PRE-PASS (a166789b): module-scope non-parseability
        // recognizer facade for this category (emitted below, gated on the const +
        // a σ-led projection shape). Called by the `parse_via_wpda` fall-through
        // fragment (`emit_recognizer_prefilter`).
        let recognize_ws_fn_name = format_ident!("recognize_{}_reachable_ws", cat_name);
        let cat_src_idx_u16 = cat_src_idx as u16;

        // ── ROOT-P MEMOIZED BEST-PARSE per-category memo map ──
        // This category is memo-eligible iff it is isolation-eligible (its
        // `parse_via_wpda` recurses through a divide-and-conquer prologue), i.e.
        // ANY of the three isolation shapes is derivable — the SAME predicate the
        // `gen/mod.rs` `parse_via_wpda` split uses (`memo_on = const && (sep ∨
        // proj ∨ infix)`), so the emitted memo map and its user agree exactly.
        // OFF / non-eligible ⇒ empty ⇒ byte-identical.
        let memo_iso_eligible = sep_isolation_shape(language, cat_name, categories).is_some()
            || projection_iso_shape(language, cat_name, categories).is_some()
            || infix_iso_shape(language, cat_name, categories).is_some();
        let proj_memo_thread_local = if memo_master_on && memo_iso_eligible {
            any_iso_eligible = true;
            emit_proj_memo_thread_local(&cat_ident)
        } else {
            quote! {}
        };

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
            Some(shape) => {
                // ROOT-1: this category emits a proj helper that references the reject
                // accessors ⇒ the module preamble must be emitted.
                any_proj_eligible = true;
                emit_projection_isolation(&cat_ident, &shape)
            },
            None => quote! {},
        };

        // ── P3 BINARY-INFIX ISOLATION+COMBINE (ROOT-2 `or`, 2026-07-06) ──
        //
        // The THIRD sibling of the `.*sep` / `@`-projection helpers: when this
        // category has ≥1 homogeneous binary-infix operator AND opts in via
        // `INFIX_ISOLATION_CATEGORIES`, emit the module-scope helper
        // `__mettail_wpda_infix_isolate_all_<Cat>`. Its guarded PROLOGUES live at
        // the same STRING parse entries (`gen/mod.rs`), wired AFTER the proj + sep
        // prologues. OFF / not-in-set / no-shape ⇒ empty ⇒ BYTE-IDENTICAL.
        let infix_helper_fns = match infix_iso_shape(language, cat_name, categories) {
            Some(shape) => emit_infix_isolation(&cat_ident, &shape),
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

        // ── ROOT-P RECOGNIZER PRE-PASS facade fn (non-parseability oracle a166789b)
        // Emitted ONLY when the master const is ON AND this category has a σ-led
        // `@`-projection shape — the EXACT gate `emit_recognizer_prefilter` uses for
        // the calling fragment, so the fn and its sole caller are co-emitted (never
        // one without the other). OFF / non-proj / no-σ-led-variant ⇒ empty ⇒
        // byte-identical.
        let recognizer_facade_fn: TokenStream = {
            // SUPERSET of the fragment's gate (`emit_recognizer_prefilter` additionally
            // requires ≥1 σ-led variant): emit the fn whenever the const is ON AND this
            // category has ANY `@`-projection shape. The fragment (its sole caller) is
            // therefore never emitted without the fn; a fn emitted without a caller
            // (proj shape but no σ-led variant) is covered by `#[allow(dead_code)]`.
            let recog_gate = (super::forks::RECOGNIZER_PREFILTER
                || super::forks::RECOGNIZER_REJECT_GATE)
                && projection_iso_shape(language, cat_name, categories).is_some();
            if recog_gate {
                quote! {
                    /// ROOT-P RECOGNIZER PRE-PASS facade (non-parseability oracle
                    /// a166789b, gated by [`super::forks::RECOGNIZER_PREFILTER`]).
                    /// One-sided NON-PARSEABILITY oracle for the `#cat_ident`
                    /// category: builds a FRESH coarse (GLL-Slot cursor merge + Tomita
                    /// pop fan-out) walker via `recognize_reachable` and reports
                    /// whether an EOI-accepting configuration is REACHABLE over
                    /// `source`. `false` ⇒ the span is DEFINITIVELY non-parseable
                    /// (poly-time, even where the full parse is exponential); `true` /
                    /// max-steps ⇒ the span MAY be parseable (run the full parser).
                    /// Called ONLY from the `parse_via_wpda` σ-led structural-decline
                    /// fall-through (see `emit_recognizer_prefilter`). Not emitted when
                    /// the const is OFF ⇒ byte-identical.
                    #[allow(non_snake_case, dead_code)]
                    pub fn #recognize_ws_fn_name(
                        source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                        min_bp: u8,
                        __default_max_steps: usize,
                    ) -> bool {
                        use mettail_prattail::wpda_walker::WpdaWalker;
                        use mettail_prattail::automata::lex_weight::LexicographicWeight;
                        // Phase 3.1.7 (C10): walker W = LexicographicWeight.
                        type DW = LexicographicWeight;
                        // Coarse-walker step budget. Hitting the cap ⇒ conservatively
                        // `true` (inconclusive ⇒ fall to the walker; NEVER a false
                        // reject — soundness is budget-independent, since `false` is
                        // returned only when the run genuinely completes with no
                        // reachable accept). Env `PRATTAIL_RECOGNIZER_MAX_STEPS`
                        // overrides for tuning without a rebuild.
                        //
                        // The step budget defaults to the CALLER-supplied
                        // `__default_max_steps` (the narrow reject-gate passes the
                        // modest `RECOGNIZER_GATE_MAX_STEPS`; the dormant broad prefilter
                        // passes its 1M natural default). Env `PRATTAIL_RECOGNIZER_MAX_STEPS`
                        // overrides for tuning without a rebuild. Hitting the cap ⇒
                        // conservatively `true` (inconclusive ⇒ fall to the walker; NEVER
                        // a false reject — soundness is budget-independent, since `false`
                        // is returned only when the run genuinely completes with no
                        // reachable accept).
                        //
                        // ⚠ STAGE-2 FINDING (2026-07-08): `recognize_reachable`'s coarse
                        // frontier does NOT always converge — on some SMALL, PARSEABLE
                        // σ-led spans it never empties/accepts and grinds to `max_steps`
                        // (returning the inconclusive `true`). The BROAD prefilter gate
                        // (every σ-led fall-through) therefore regresses; the NARROW
                        // reject-gate (`RECOGNIZER_REJECT_GATE`) invokes this ONLY on the
                        // already-narrow `__proj_sigil_reject` reject-candidate set, so a
                        // modest bounded budget cleanly bounds that latency (genuine
                        // rejects converge fast; non-convergent parseable spans bail to
                        // the walker they were headed to anyway).
                        let max_steps: usize =
                            std::env::var("PRATTAIL_RECOGNIZER_MAX_STEPS")
                                .ok()
                                .and_then(|__s| __s.parse().ok())
                                .unwrap_or(__default_max_steps);
                        WpdaWalker::<DW, _>::recognize_reachable(
                            #engine_ident::default(),
                            #cat_src_idx_u16,
                            min_bp,
                            source,
                            max_steps,
                        )
                    }
                }
            } else {
                quote! {}
            }
        };

        fns.push(quote! {
            // ROOT-P MEMOIZED BEST-PARSE (design af7680e2): the per-category
            // thread-local memo map `__PROJ_MEMO_<Cat>` consulted by the memoized
            // `Cat::parse_via_wpda` (gen/mod.rs). Emitted ONLY when the master
            // const is ON AND this category is isolation-eligible; empty otherwise
            // (byte-identical). Shares the module scope with the `impl Cat` methods.
            #proj_memo_thread_local

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

            // P3 BINARY-INFIX ISOLATION+COMBINE (ROOT-2 `or`, 2026-07-06): the
            // per-category `__mettail_wpda_infix_isolate_all_<Cat>` helper. Emitted
            // ONLY when this category is in `INFIX_ISOLATION_CATEGORIES` with ≥1
            // homogeneous binary-infix operator; empty otherwise.
            #infix_helper_fns

            // ROOT-P RECOGNIZER PRE-PASS (non-parseability oracle a166789b): the
            // module-scope `recognize_<Cat>_reachable_ws` facade fn. Emitted ONLY
            // when `RECOGNIZER_PREFILTER` is ON AND this category has a σ-led
            // `@`-projection shape; empty otherwise (byte-identical). Called by the
            // `parse_via_wpda` fall-through fragment (`emit_recognizer_prefilter`).
            #recognizer_facade_fn

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
                            .realize_root_to_terms_with_weights(
                                root,
                                Some(128),
                                mettail_prattail::wpda_walker::RealizeRequestMode::SingleResultElection,
                            )
                            .into_iter()
                            .min_by(|(_, a), (_, b)| a.cmp(b));
                    }
                    let mut best: Option<(std::sync::Arc<dyn std::any::Any + Send + Sync>, __W)> = None;
                    for &root in roots {
                        // First cap that ACTUALLY realizes this root wins for
                        // this root; its own min-weight term is the candidate.
                        let mut per_root: Option<(std::sync::Arc<dyn std::any::Any + Send + Sync>, __W)> = None;
                        for &cap in RAW_PROBE_CAPS {
                            // Task #10 item 2: single-result facade semantics
                            // stated explicitly; the descending caps remain
                            // pure enumeration bounds for the fallback path.
                            let realized = walker.realize_root_to_terms_with_weights(
                                root,
                                Some(cap),
                                mettail_prattail::wpda_walker::RealizeRequestMode::SingleResultElection,
                            );
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
                        // Task #10 item 2b (USER-APPROVED 2026-07-14): this
                        // display-exact probe wants the raw packing FAMILY,
                        // never the elected reading — `BoundedEnumeration`
                        // restores the helper's own lazy/fair enumeration
                        // contract on BIN roots. (Pre-2b, the historical
                        // power-of-two ≤ 128 inference ELECTED at every
                        // ladder step ≤ 128: 1 reading realized,
                        // `exhausted_all_roots` stayed true, and the probe
                        // returned `Ok(None)` after one pass without ever
                        // enumerating — `Cat::parse` surface-faithfulness
                        // was silently dead on BIN roots, the flip-era
                        // regression the item-2 red-team confirmed.)
                        // Disclosed single-pick sub-effect (toward pre-flip
                        // classic): among MULTIPLE display-exact readings
                        // this returns the FIRST-ENUMERATED one, not a
                        // weight-min — the helper's pre-flip behavior.
                        let mut exhausted_all_roots = true;
                        for &root in roots {
                            let realized = walker.realize_root_to_terms_with_weights(
                                root,
                                Some(per_root_limit),
                                mettail_prattail::wpda_walker::RealizeRequestMode::BoundedEnumeration,
                            );
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
                        // Task #10 item 2b (USER-APPROVED 2026-07-14): this
                        // bounded-prefix `_all` enumerator requests
                        // `BoundedEnumeration` unconditionally — enumeration
                        // IS its contract (the ambiguity-preserving prefix
                        // facade). (Pre-2b, when `max_alternatives ∈
                        // {1,3,7,15,31,63,127}` the probe limit (max_alt+1)
                        // was a power of two ≤ 128, so BIN roots ELECTED and
                        // the `_all`-semantics facade collapsed to 1
                        // alternative regardless of family size — the
                        // surviving instance of the ledger's "caught +
                        // fixed" 65-doubling bug class.)
                        // Disclosed single-pick sub-effect (toward pre-flip
                        // classic): at `max_alternatives = 1` the returned
                        // single switches from the K-elected reading to the
                        // enumeration min-weight representative (the sort
                        // below still orders by weight).
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
                                mettail_prattail::wpda_walker::RealizeRequestMode::BoundedEnumeration,
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
                                    // Task #10 item 2: `_all` enumeration
                                    // semantics stated explicitly (the 65 →
                                    // ×2 → 4096 probe ladder never inferred
                                    // single-result — byte-identical).
                                    let realized = walker.realize_root_to_terms_with_weights(
                                        root,
                                        Some(raw_probe_limit),
                                        mettail_prattail::wpda_walker::RealizeRequestMode::BoundedEnumeration,
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
                                    // Task #10 item 2: `_all` enumeration
                                    // semantics stated explicitly (the 65 →
                                    // ×2 → 4096 probe ladder never inferred
                                    // single-result — byte-identical).
                                    let realized = walker.realize_root_to_terms_with_weights(
                                        root,
                                        Some(raw_probe_limit),
                                        mettail_prattail::wpda_walker::RealizeRequestMode::BoundedEnumeration,
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
                            // Task #10 item 4: swap-tokens (action_kind 4).
                            // The classic commit-replay's SwapTokens arm AND
                            // the pure SwapAdjacent virtual-chain lowering
                            // both log kind-4 events (`min(pos_a, pos_b)`,
                            // the swap tropical cost) — this arm maps them
                            // IDENTICALLY for either engine (the shared
                            // facade; red-team note: classic maps
                            // identically). Pre-item-4 kind-4 events fell to
                            // the `_ => None` arm.
                            4 => Some("swap-tokens".into()),
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
                        // Task #10 item 2 amendment 3: recovering-mode
                        // single-result pick → `SingleResultElection`
                        // (byte-identical: Some(1) inferred single before).
                        let pick = roots
                            .first()
                            .and_then(|&root|
                                walker
                                    .realize_root_to_terms(
                                        root,
                                        Some(1),
                                        mettail_prattail::wpda_walker::RealizeRequestMode::SingleResultElection,
                                    )
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
                        // Task #10 item 2 amendment 3: recovering-mode
                        // single-result pick → `SingleResultElection`
                        // (byte-identical: Some(1) inferred single before).
                        let pick = roots
                            .first()
                            .and_then(|&root|
                                walker
                                    .realize_root_to_terms(
                                        root,
                                        Some(1),
                                        mettail_prattail::wpda_walker::RealizeRequestMode::SingleResultElection,
                                    )
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
    // ── ROOT-P MEMOIZED BEST-PARSE shared preamble ──
    // The epoch/depth thread-locals + `__ProjMemoGuard` RAII struct, emitted ONCE
    // per language module (module scope, shared by every iso-eligible category's
    // memoized `parse_via_wpda`). Gate: master const ON AND ≥1 iso-eligible
    // category. OFF / no eligible category ⇒ empty ⇒ byte-identical.
    let memo_preamble = if memo_master_on && any_iso_eligible {
        emit_proj_memo_preamble()
    } else {
        quote! {}
    };
    // ── ROOT-1 AUTHORITATIVE-REJECT shared preamble (design a9fbeefe) ──
    // The thread-local reject flag + set/take accessors, emitted ONCE per module,
    // gated by the master const AND ≥1 `@`-projection-eligible category. OFF / none
    // ⇒ empty ⇒ byte-identical.
    let sigil_reject_preamble = if super::forks::PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT
        && any_proj_eligible
    {
        emit_proj_sigil_reject_preamble()
    } else {
        quote! {}
    };
    quote! {
        // ROOT-P MEMOIZED BEST-PARSE (design af7680e2): shared epoch/depth
        // thread-local preamble + `__ProjMemoGuard`. Empty when OFF / no
        // iso-eligible category (byte-identical).
        #memo_preamble
        // ROOT-1 AUTHORITATIVE-REJECT (design a9fbeefe): shared thread-local reject
        // flag + accessors. Empty when OFF / no proj-eligible category (byte-identical).
        #sigil_reject_preamble

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
                    WpdaParseError::AmbiguityBudget { budget, actual, position, .. } => {
                        // Engine-neutral wording (task #18, amdt #6): the PURE
                        // engine's `actual` is a DISTINCT-READING count (whole-run
                        // resolve cardinality `|R|_distinct`) while the CLASSIC
                        // lever's `actual` is a live cursor-frontier count — so the
                        // surface text must NOT say "frontier of N cursors".
                        // `frontier_ess_x1000` stays on the variant (classic
                        // diagnostics read it) but is omitted from the message.
                        write!(
                            f,
                            "wpds parse aborted at position {}: ambiguity budget {} exceeded (actual {})",
                            position,
                            budget,
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
