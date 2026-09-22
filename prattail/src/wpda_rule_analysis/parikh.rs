//! Original macro-era Parikh descriptor derivation, shared without re-derivation.
//!
//! Alphabet collection, shallow parameter/expression analysis, in-place fixed
//! points and suffix-row enumeration retain their original order and defaults.
//! The existing borrowed binder readers supply field observations; no AST,
//! grammar, or source text is reconstructed here. Only Rust quotation remains
//! in the macro frontend.
//!
//! `ParikhDescriptorProjection.v` checks source/accessor correspondence for
//! finite executions, including short-circuiting and intermediate map updates.
//! It does not discharge the separate premises of `ParikhObligationGate.v`,
//! prove arbitrary readers lawful, or admit untrusted images. Callers must
//! validate handles, category rows and numeric domains before dynamic use.
//! Original narrowing casts and fixed-point loops are intentionally unchanged.

use super::binder::optional::BinderSyntaxObservation;
use super::binder::rule::{BinderRuleReader, BinderTypeObservation};
use super::binder::term_param::TermParamObservation;
use crate::binding_power::InfixRuleInfo;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Original 128-bit token-class obligation mask.
pub type Mask = u128;

/// The resolved Parikh alphabet: trigger terminal → bit-index, plus the
/// coarse-class bit (always the highest assigned index).
pub struct Alphabet {
    /// Trigger terminal text → bit-index (`0..trigger_count`).
    pub trigger_bit: HashMap<String, u8>,
    /// Bit-index of the coarse "everything else" class.
    pub coarse_bit: u8,
}

impl Alphabet {
    /// The class-bit of a terminal text: its trigger bit if it is a
    /// declared cross-cat infix trigger, else the coarse class.
    pub fn class_of_terminal(&self, text: &str) -> u8 {
        *self.trigger_bit.get(text).unwrap_or(&self.coarse_bit)
    }

    /// Singleton mask for a terminal text.
    pub fn mask_of_terminal(&self, text: &str) -> Mask {
        1u128 << self.class_of_terminal(text)
    }

    /// ⊤: all assigned class bits set (the greatest-fixpoint seed).
    pub fn top(&self) -> Mask {
        // bits 0..=coarse_bit
        let n = self.coarse_bit as u32 + 1;
        if n >= 128 {
            u128::MAX
        } else {
            (1u128 << n) - 1
        }
    }
}

/// Collect the distinct cross-cat infix TRIGGER terminals across the whole
/// language (the `kind_dispatch.rs:289` walk: `classify_rule_public`,
/// `is_cross_category ∧ category ≠ result_category` → `info.terminal`).
/// Assign each a sequential bit; the coarse class is the next bit.
pub fn build_alphabet<T>(
    authored_rules: &[T],
    mut classify: impl FnMut(&T) -> Option<InfixRuleInfo>,
) -> Alphabet {
    let mut triggers: BTreeSet<String> = BTreeSet::new();
    for rule in authored_rules {
        if let Some(info) = classify(rule) {
            if info.is_cross_category && info.category != info.result_category {
                triggers.insert(info.terminal.clone());
            }
        }
    }
    let mut trigger_bit: HashMap<String, u8> = HashMap::with_capacity(triggers.len());
    let mut next: u8 = 0;
    for t in &triggers {
        if (next as usize) < 127 {
            // leave room for the coarse class below 128
            trigger_bit.insert(t.clone(), next);
            next += 1;
        }
    }
    let coarse_bit = next; // the next free bit is the coarse class
    Alphabet { trigger_bit, coarse_bit }
}

/// Build a `param-name → category-name` map for a judgement-style rule
/// from its `term_context`. Simple params map to their base type;
/// Abstraction/MultiAbstraction bodies map to the codomain category.
/// Params whose type is not a plain `Base`/arrow-to-`Base` are omitted
/// (their `must` defaults to ∅ — sound under-claim).
pub fn param_categories<'syntax, R: BinderRuleReader<'syntax>>(
    reader: &R,
    rule: R::Rule,
) -> HashMap<String, String> {
    let mut map = HashMap::new();
    let Some(tc) = reader.term_context(rule) else {
        return map;
    };
    for index in 0..reader.params_len(tc) {
        match reader.param(
            reader
                .param_at(tc, index)
                .expect("parameter index is in bounds"),
        ) {
            TermParamObservation::Simple { name, ty } => {
                if let Some(cat) = base_category(reader, ty) {
                    map.insert(name.to_string(), cat);
                }
            },
            TermParamObservation::Abstraction { body, ty, .. }
            | TermParamObservation::MultiAbstraction { body, ty, .. } => {
                // The body's category is the arrow codomain.
                if let Some(cat) = codomain_category(reader, ty) {
                    map.insert(body.to_string(), cat);
                }
            },
            TermParamObservation::GuardBody { .. } | TermParamObservation::Optional { .. } => {
                // Guard slots / optional groups: no scalar category to
                // resolve here — defaults to ∅ at the use site.
            },
        }
    }
    map
}

/// Extract the base category name from a `BinderTypeObservation::Base`.
pub fn base_category<'syntax, R: BinderRuleReader<'syntax>>(
    reader: &R,
    ty: R::Type,
) -> Option<String> {
    match reader.ty(ty) {
        BinderTypeObservation::Base(id) => Some(id.to_string()),
        _ => None,
    }
}

/// Extract the codomain category of an arrow type (for binder bodies).
pub fn codomain_category<'syntax, R: BinderRuleReader<'syntax>>(
    reader: &R,
    ty: R::Type,
) -> Option<String> {
    match reader.ty(ty) {
        BinderTypeObservation::Arrow { codomain, .. } => base_category(reader, codomain),
        _ => None,
    }
}

/// Per-position nullability + `must` of a single `SyntaxExpr`, given the
/// current category-`must` iterate and the rule's param→category map.
///
/// Returns `(nullable, must_mask)`. Soundness: under-claim freely.
pub fn expr_must<'syntax, N: ToString, O>(
    expr: BinderSyntaxObservation<'syntax, N, O>,
    params: &HashMap<String, String>,
    cat_must: &HashMap<String, Mask>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> (bool, Mask) {
    match expr {
        // A literal always consumes its own token: non-nullable, owns its class.
        BinderSyntaxObservation::Literal(text) => (false, alpha.mask_of_terminal(text)),
        // L9-3: a custom-kind capture consumes exactly one token (non-nullable),
        // owning the class of that kind's variant name.
        BinderSyntaxObservation::TokenKind { name, .. } => {
            (false, alpha.mask_of_terminal(&name.to_string()))
        },
        // L9-4: a guest body consumes at least the opener token (non-nullable);
        // it owns the opener kind's class (the closer/body classes are consumed
        // atomically inside the assembly action, not by the Parikh spine).
        BinderSyntaxObservation::GuestBody { open, .. } => {
            (false, alpha.mask_of_terminal(&open.to_string()))
        },
        // A parameter reference parses its declared category.
        BinderSyntaxObservation::Param(id) => {
            let name = id.to_string();
            match params.get(&name) {
                Some(cat) => {
                    let nul = *cat_nullable.get(cat).unwrap_or(&false);
                    let m = *cat_must.get(cat).unwrap_or(&0);
                    (nul, m)
                },
                // Unknown param (e.g. a binder ident with no scalar
                // category, or a guard body): treat as a single
                // coarse-class token (idents/values are coarse) but
                // NON-nullable only if we are sure; to stay sound, treat
                // as nullable with ∅ must (no refutation pressure).
                None => (true, 0),
            }
        },
        // `#opt(...)` has an explicit skip path → nullable, ∅ must.
        // `#sep(...)` admits 0 iterations → nullable, ∅ must.
        // `#map`/`#zip`/`#var`: complex; under-claim (nullable, ∅).
        // Every original operation arm returns this pair without traversing children.
        BinderSyntaxObservation::Op(_) => (true, 0),
    }
}

/// The suffix-`must` of rule `R` from item position `pos`:
/// `⋃_{i ≥ pos, ¬nullable(R.syntax[i])} must(R.syntax[i])`.
pub fn rule_suffix_must<'syntax, R: BinderRuleReader<'syntax>>(
    reader: &R,
    sp: R::Sequence,
    pos: usize,
    params: &HashMap<String, String>,
    cat_must: &HashMap<String, Mask>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> Mask {
    let mut acc: Mask = 0;
    for index in (0..reader.sequence_len(sp)).skip(pos) {
        let expr = reader.at(sp, index).expect("syntax index is in bounds");
        let (_nul, m) = expr_must(expr, params, cat_must, cat_nullable, alpha);
        // Union the obligation of NON-nullable positions only. A nullable
        // position contributes ∅ (its derivation may skip it).
        // `expr_must` already returns ∅ for the nullable constructs, and a
        // non-nullable Literal/Param returns its real must; OR-ing the ∅s
        // is harmless, so we can union unconditionally and stay sound.
        acc |= m;
    }
    acc
}

/// The whole-production `⋃_{s∈σ,¬nullable} must(s)` of one rule body
/// (= `rule_suffix_must` from position 0) — the per-production term of the
/// category intersection.
pub fn rule_production_must<'syntax, R: BinderRuleReader<'syntax>>(
    reader: &R,
    rule: R::Rule,
    cat_must: &HashMap<String, Mask>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> Mask {
    let params = param_categories(reader, rule);
    match reader.syntax_pattern(rule) {
        Some(sp) if reader.sequence_len(sp) != 0 => {
            rule_suffix_must(reader, sp, 0, &params, cat_must, cat_nullable, alpha)
        },
        // Synthetic literal/atomic rules have no syntax_pattern; they parse
        // a single literal/Var token of the coarse class. Treat the
        // production must as {coarse} so the category min-intersection sees
        // "at least one coarse token is always consumed" (sound: every
        // such parse consumes one literal token).
        _ => 1u128 << alpha.coarse_bit,
    }
}

/// Whether a single rule body can derive ε (all positions nullable), given
/// the current category-nullability iterate.
pub fn rule_production_nullable<'syntax, R: BinderRuleReader<'syntax>>(
    reader: &R,
    rule: R::Rule,
    params: &HashMap<String, String>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> bool {
    match reader.syntax_pattern(rule) {
        Some(sp) if reader.sequence_len(sp) != 0 => {
            // nullable iff EVERY position is nullable.
            let dummy: HashMap<String, Mask> = HashMap::new();
            (0..reader.sequence_len(sp)).all(|index| {
                let expr = reader.at(sp, index).expect("syntax index is in bounds");
                expr_must(expr, params, &dummy, cat_nullable, alpha).0
            })
        },
        // Synthetic literal/atomic rule: consumes a token → NOT nullable.
        _ => false,
    }
}

/// Greatest-fixpoint computation of per-category `must` and the standard
/// least-fixpoint of per-category `nullable`, over `per_cat`.
pub fn compute_category_must<'syntax, T: 'syntax, R>(
    reader: &R,
    per_cat: &'syntax [Vec<T>],
    categories: &[String],
    alpha: &Alphabet,
) -> (HashMap<String, Mask>, HashMap<String, bool>)
where
    R: BinderRuleReader<'syntax, Rule = &'syntax T>,
{
    let top = alpha.top();

    // ── nullable: least fixpoint, start all false, monotone-increasing. ──
    let mut cat_nullable: HashMap<String, bool> =
        categories.iter().map(|c| (c.clone(), false)).collect();
    loop {
        let mut changed = false;
        for (i, cat) in categories.iter().enumerate() {
            // A category is nullable iff SOME production is all-nullable.
            let any_nullable = per_cat[i].iter().any(|rule| {
                let params = param_categories(reader, rule);
                rule_production_nullable(reader, rule, &params, &cat_nullable, alpha)
            });
            if any_nullable && !*cat_nullable.get(cat).unwrap_or(&false) {
                cat_nullable.insert(cat.clone(), true);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // ── must: greatest fixpoint, start all ⊤, monotone-decreasing. ──
    let mut cat_must: HashMap<String, Mask> = categories.iter().map(|c| (c.clone(), top)).collect();
    loop {
        let mut changed = false;
        for (i, cat) in categories.iter().enumerate() {
            if per_cat[i].is_empty() {
                // A category with no productions: must = ∅ (no obligation;
                // nothing can be parsed, but ∅ is the safe identity that
                // never refutes).
                if *cat_must.get(cat).unwrap_or(&0) != 0 {
                    cat_must.insert(cat.clone(), 0);
                    changed = true;
                }
                continue;
            }
            // must(A) = ⋂ over productions of (⋃ non-nullable must).
            let mut intersection: Mask = top;
            for rule in &per_cat[i] {
                let prod = rule_production_must(reader, rule, &cat_must, &cat_nullable, alpha);
                intersection &= prod;
            }
            if intersection != *cat_must.get(cat).unwrap_or(&top) {
                cat_must.insert(cat.clone(), intersection);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    (cat_must, cat_nullable)
}

/// Owned results for quotation and runtime-image adapters.
pub struct ParikhDescriptors {
    pub alphabet: Alphabet,
    pub must_entries: BTreeMap<(u16, u16, u8), Mask>,
}

/// Derive the original alphabet and positional obligations once.
///
/// `authored_rules` is the original term roster, not the synthetic normalized
/// buckets. Those buckets are used only where the original analysis used them.
pub fn build_parikh_descriptors<'syntax, T: 'syntax, R>(
    reader: &R,
    authored_rules: &[T],
    categories: &[String],
    per_cat: &'syntax [Vec<T>],
    classify: impl FnMut(&T) -> Option<InfixRuleInfo>,
) -> ParikhDescriptors
where
    R: BinderRuleReader<'syntax, Rule = &'syntax T>,
{
    let alpha = build_alphabet(authored_rules, classify);
    let (cat_must, cat_nullable) = compute_category_must(reader, per_cat, categories, &alpha);

    let mut must_entries: BTreeMap<(u16, u16, u8), Mask> = BTreeMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let cat_idx = cat_i as u16;
        for (rule_i, rule) in rules.iter().enumerate() {
            let rule_idx = rule_i as u16;
            let Some(sp) = reader.syntax_pattern(rule) else {
                continue; // synthetic literal/atomic rules: no positional must
            };
            if reader.sequence_len(sp) == 0 {
                continue;
            }
            let params = param_categories(reader, rule);
            for pos in 0..reader.sequence_len(sp) {
                let mask =
                    rule_suffix_must(reader, sp, pos, &params, &cat_must, &cat_nullable, &alpha);
                if mask != 0 {
                    must_entries.insert((cat_idx, rule_idx, pos as u8), mask);
                }
            }
        }
    }

    ParikhDescriptors { alphabet: alpha, must_entries }
}
