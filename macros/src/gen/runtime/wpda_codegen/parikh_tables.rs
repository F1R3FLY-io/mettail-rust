//! EP-P2 (Stage B) Parikh obligation tables (codegen).
//!
//! Emits, into the per-language WPDA engine module, the token-class
//! machinery the shadow obligation gate reads at runtime:
//!
//! - `WPDA_PARIKH_CLASS_OF(kind: &TokenKind) -> u8` — the class bit-index
//!   of a token kind. One distinct class per grammar-declared cross-cat
//!   infix-trigger TERMINAL (FIRST-of-infix granularity, `==` ≠ `>=` —
//!   plan §P2 round-2 F6), plus ONE coarse class for everything else (the
//!   model admits coarse non-trigger classes; the alphabet stays small).
//!
//! - `WPDA_MUST_MASK(cat: u16, rule: u16, pos: u8) -> u128` — the
//!   suffix-`must` obligation of a `RuleAt(pos)` frame: the union of
//!   class-bits that EVERY completion of that rule from item position
//!   `pos` onward is guaranteed to consume. The table is TOTAL over the
//!   `(cat, rule, pos)` keys that can appear as `RuleAt` frames; every
//!   other `SymbolKind` is handled walker-side as `must = ∅` (the
//!   round-2 m-2 totality convention — non-`RuleAt` frames never refute).
//!
//! Both are emitted as plain `const`-table-shaped match functions beside
//! `WPDA_RULES` in `generate_wpda_engine_module`.
//!
//! ## The `must` model (transcribing ParikhObligationGate.v Part 1)
//!
//! `must` is the LARGEST family satisfying
//!   `must(t) = {class(t)}`                         (terminal)
//!   `must(A) = ⋂_{A→σ} ( ⋃_{s∈σ, ¬nullable(s)} must(s) )`   (nonterminal)
//! restricted to NON-NULLABLE rhs positions (round-1 M1: an unrestricted
//! union over a nullable `#sep`/`#opt` position over-claims and would
//! refute a valid skip derivation). We compute it as a greatest fixpoint:
//! start every category's mask at ⊤ (all alphabet bits) and intersect
//! down to convergence; `must(NonTerminal C)` reads the current iterate
//! of `C` (monotone-decreasing ⇒ terminates), so self/mutual recursion is
//! handled without special-casing.
//!
//! A `RuleAt(pos)` frame commits to ONE rule R, so there is no
//! intersection over productions at the frame: its obligation is the
//! single-completion union
//!   `must(R, pos) = ⋃_{i ≥ pos, ¬nullable(R.syntax[i])} must(R.syntax[i])`.
//! This is exactly the suffix of R's body from item index `pos`, and
//! `position` in `SymbolKind::RuleAt` IS the 0-based index into the
//! rule's `syntax_pattern` items (wpda_runtime.rs::SymbolKind doc + the
//! `sp.iter().enumerate()` position walk in binder.rs).
//!
//! ## Soundness direction (why under-claiming is safe)
//!
//! The gate refutes only when `must ⊄ S[pos]`. A SMALLER `must` ⇒ fewer
//! refutations ⇒ never unsound (the no-loss theorem requires
//! `must ⊆ true-must`). So every unmodeled/complex construct
//! (`#map`/`#zip`/guard slots/binders) defaults to `{nullable, must=∅}`:
//! the gate simply does not refute on it. Discriminating power comes from
//! `Literal` triggers and from `Param` positions whose category `must` is
//! a specific trigger class.

use mettail_ast::grammar::{GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// A class bitmask over the (small) Parikh alphabet.
type Mask = u128;

/// Result of `build_parikh_model`: the inventory + the emitted token
/// streams. Kept together so `generate_wpda_engine_module` splices both
/// fns and the diagnostic build can read the inventory sizes.
pub(crate) struct ParikhEmission {
    /// `WPDA_PARIKH_CLASS_OF` + `WPDA_MUST_MASK` definitions.
    pub(crate) tokens: TokenStream,
    /// Number of distinct trigger terminals (one class bit each).
    pub(crate) trigger_class_count: usize,
    /// Total alphabet size (triggers + 1 coarse class).
    pub(crate) alphabet_size: usize,
    /// Number of non-zero `(cat, rule, pos)` must entries emitted.
    pub(crate) must_entry_count: usize,
}

/// The resolved Parikh alphabet: trigger terminal → bit-index, plus the
/// coarse-class bit (always the highest assigned index).
struct Alphabet {
    /// Trigger terminal text → bit-index (`0..trigger_count`).
    trigger_bit: HashMap<String, u8>,
    /// Bit-index of the coarse "everything else" class.
    coarse_bit: u8,
}

impl Alphabet {
    /// The class-bit of a terminal text: its trigger bit if it is a
    /// declared cross-cat infix trigger, else the coarse class.
    fn class_of_terminal(&self, text: &str) -> u8 {
        *self.trigger_bit.get(text).unwrap_or(&self.coarse_bit)
    }

    /// Singleton mask for a terminal text.
    fn mask_of_terminal(&self, text: &str) -> Mask {
        1u128 << self.class_of_terminal(text)
    }

    /// ⊤: all assigned class bits set (the greatest-fixpoint seed).
    fn top(&self) -> Mask {
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
fn build_alphabet(language: &LanguageDef) -> Alphabet {
    let mut triggers: BTreeSet<String> = BTreeSet::new();
    for rule in &language.terms {
        if let Some(info) = super::infix::classify_rule_public(rule) {
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
fn param_categories(rule: &GrammarRule) -> HashMap<String, String> {
    let mut map = HashMap::new();
    let Some(tc) = rule.term_context.as_ref() else {
        return map;
    };
    for p in tc {
        match p {
            TermParam::Simple { name, ty } => {
                if let Some(cat) = base_category(ty) {
                    map.insert(name.to_string(), cat);
                }
            },
            TermParam::Abstraction { body, ty, .. }
            | TermParam::MultiAbstraction { body, ty, .. } => {
                // The body's category is the arrow codomain.
                if let Some(cat) = codomain_category(ty) {
                    map.insert(body.to_string(), cat);
                }
            },
            TermParam::GuardBody { .. } | TermParam::Optional { .. } => {
                // Guard slots / optional groups: no scalar category to
                // resolve here — defaults to ∅ at the use site.
            },
        }
    }
    map
}

/// Extract the base category name from a `TypeExpr::Base`.
fn base_category(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Base(id) => Some(id.to_string()),
        _ => None,
    }
}

/// Extract the codomain category of an arrow type (for binder bodies).
fn codomain_category(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Arrow { codomain, .. } => base_category(codomain),
        _ => None,
    }
}

/// Per-position nullability + `must` of a single `SyntaxExpr`, given the
/// current category-`must` iterate and the rule's param→category map.
///
/// Returns `(nullable, must_mask)`. Soundness: under-claim freely.
fn expr_must(
    expr: &SyntaxExpr,
    params: &HashMap<String, String>,
    cat_must: &HashMap<String, Mask>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> (bool, Mask) {
    match expr {
        // A literal always consumes its own token: non-nullable, owns its class.
        SyntaxExpr::Literal(text) => (false, alpha.mask_of_terminal(text)),
        // L9-3: a custom-kind capture consumes exactly one token (non-nullable),
        // owning the class of that kind's variant name.
        SyntaxExpr::TokenKind { name, .. } => (false, alpha.mask_of_terminal(&name.to_string())),
        // L9-4: a guest body consumes at least the opener token (non-nullable);
        // it owns the opener kind's class (the closer/body classes are consumed
        // atomically inside the assembly action, not by the Parikh spine).
        SyntaxExpr::GuestBody { open, .. } => (false, alpha.mask_of_terminal(&open.to_string())),
        // A parameter reference parses its declared category.
        SyntaxExpr::Param(id) => {
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
        SyntaxExpr::Op(op) => match op {
            PatternOp::Opt { .. } | PatternOp::Sep { .. } => (true, 0),
            PatternOp::Map { .. } | PatternOp::Zip { .. } | PatternOp::Var(_) => (true, 0),
        },
    }
}

/// The suffix-`must` of rule `R` from item position `pos`:
/// `⋃_{i ≥ pos, ¬nullable(R.syntax[i])} must(R.syntax[i])`.
fn rule_suffix_must(
    sp: &[SyntaxExpr],
    pos: usize,
    params: &HashMap<String, String>,
    cat_must: &HashMap<String, Mask>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> Mask {
    let mut acc: Mask = 0;
    for expr in sp.iter().skip(pos) {
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
fn rule_production_must(
    rule: &GrammarRule,
    cat_must: &HashMap<String, Mask>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> Mask {
    let params = param_categories(rule);
    match rule.syntax_pattern.as_ref() {
        Some(sp) if !sp.is_empty() => {
            rule_suffix_must(sp, 0, &params, cat_must, cat_nullable, alpha)
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
fn rule_production_nullable(
    rule: &GrammarRule,
    params: &HashMap<String, String>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> bool {
    match rule.syntax_pattern.as_ref() {
        Some(sp) if !sp.is_empty() => {
            // nullable iff EVERY position is nullable.
            let dummy: HashMap<String, Mask> = HashMap::new();
            sp.iter()
                .all(|e| expr_must(e, params, &dummy, cat_nullable, alpha).0)
        },
        // Synthetic literal/atomic rule: consumes a token → NOT nullable.
        _ => false,
    }
}

/// Greatest-fixpoint computation of per-category `must` and the standard
/// least-fixpoint of per-category `nullable`, over `per_cat`.
fn compute_category_must(
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
    alpha: &Alphabet,
) -> (HashMap<String, Mask>, HashMap<String, bool>) {
    let top = alpha.top();

    // ── nullable: least fixpoint, start all false, monotone-increasing. ──
    let mut cat_nullable: HashMap<String, bool> =
        categories.iter().map(|c| (c.clone(), false)).collect();
    loop {
        let mut changed = false;
        for (i, cat) in categories.iter().enumerate() {
            // A category is nullable iff SOME production is all-nullable.
            let any_nullable = per_cat[i].iter().any(|rule| {
                let params = param_categories(rule);
                rule_production_nullable(rule, &params, &cat_nullable, alpha)
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
                let prod = rule_production_must(rule, &cat_must, &cat_nullable, alpha);
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

/// Build the Parikh emission for a language: the alphabet, the
/// per-category `must` fixpoint, and the two emitted functions.
pub(crate) fn build_parikh_model(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> ParikhEmission {
    let alpha = build_alphabet(language);
    let (cat_must, cat_nullable) = compute_category_must(per_cat, categories, &alpha);

    // ── Emit WPDA_PARIKH_CLASS_OF ──
    // Trigger terminals get their bit; everything else → coarse.
    let coarse_bit = alpha.coarse_bit;
    // Deterministic emission order.
    let trigger_arms: Vec<TokenStream> = {
        let mut sorted: Vec<(&String, &u8)> = alpha.trigger_bit.iter().collect();
        sorted.sort_by(|a, b| a.1.cmp(b.1).then_with(|| a.0.cmp(b.0)));
        sorted
            .into_iter()
            .map(|(text, bit)| {
                quote! {
                    mettail_prattail::automata::TokenKind::Fixed(__t) if __t == #text => #bit,
                }
            })
            .collect()
    };

    let class_of_fn = quote! {
        /// EP-P2 (Stage B): class bit-index of a token kind. One bit per
        /// grammar-declared cross-cat infix-trigger terminal; the coarse
        /// class (`#coarse_bit`) covers every other kind (literals, idents,
        /// EOF, delimiters, non-trigger operators). Total over `TokenKind`.
        #[allow(dead_code, non_snake_case)]
        pub fn WPDA_PARIKH_CLASS_OF(kind: &mettail_prattail::automata::TokenKind) -> u8 {
            match kind {
                #( #trigger_arms )*
                _ => #coarse_bit,
            }
        }
    };

    // ── Emit WPDA_MUST_MASK ──
    // Enumerate every (cat, rule, pos) RuleAt key with a non-zero suffix
    // must. pos ranges over 0..=sp.len() (the runtime can hold a RuleAt at
    // the post-final position transiently; its suffix must is ∅, so we omit
    // it — the default 0 covers it).
    let mut must_entries: BTreeMap<(u16, u16, u8), Mask> = BTreeMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let cat_idx = cat_i as u16;
        for (rule_i, rule) in rules.iter().enumerate() {
            let rule_idx = rule_i as u16;
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue; // synthetic literal/atomic rules: no positional must
            };
            if sp.is_empty() {
                continue;
            }
            let params = param_categories(rule);
            for pos in 0..sp.len() {
                let mask = rule_suffix_must(sp, pos, &params, &cat_must, &cat_nullable, &alpha);
                if mask != 0 {
                    must_entries.insert((cat_idx, rule_idx, pos as u8), mask);
                }
            }
        }
    }

    let must_entry_count = must_entries.len();
    let must_arms: Vec<TokenStream> = must_entries
        .iter()
        .map(|((c, r, p), m)| {
            let lit = *m;
            quote! { (#c, #r, #p) => #lit, }
        })
        .collect();

    let must_mask_fn = quote! {
        /// EP-P2 (Stage B): the suffix-`must` obligation mask of a
        /// `RuleAt(pos)` frame `(category_src_idx, rule_index_in_category,
        /// position)` — the union of token-class bits EVERY completion of
        /// that rule from item position `pos` is guaranteed to consume.
        /// `0` (∅, never-refute) for any key not in the table (including
        /// every non-`RuleAt` `SymbolKind`, handled walker-side). See
        /// `ParikhObligationGate.v` `must_consume_sound` +
        /// `top_frame_refutation_sound`.
        #[allow(dead_code, non_snake_case)]
        pub fn WPDA_MUST_MASK(cat: u16, rule: u16, pos: u8) -> u128 {
            match (cat, rule, pos) {
                #( #must_arms )*
                _ => 0u128,
            }
        }
    };

    let tokens = quote! {
        #class_of_fn
        #must_mask_fn
    };

    ParikhEmission {
        tokens,
        trigger_class_count: alpha.trigger_bit.len(),
        alphabet_size: alpha.coarse_bit as usize + 1,
        must_entry_count,
    }
}
