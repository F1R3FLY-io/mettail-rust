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

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use mettail_prattail::wpda_rule_analysis::parikh;
use proc_macro2::TokenStream;
use quote::quote;

#[cfg(test)]
use mettail_ast::grammar::{PatternOp, SyntaxExpr, TermParam};
#[cfg(test)]
use mettail_ast::types::TypeExpr;
#[cfg(test)]
use mettail_prattail::wpda_rule_analysis::parikh::{Alphabet, Mask};
#[cfg(test)]
use std::collections::HashMap;

#[cfg(test)]
#[path = "../../../../tests/support/parikh_descriptor_baselines.rs"]
mod parikh_descriptor_baselines;

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

/// Build the Parikh emission for a language: the alphabet, the
/// per-category `must` fixpoint, and the two emitted functions.
pub(crate) fn build_parikh_model(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> ParikhEmission {
    let parikh::ParikhDescriptors { alphabet: alpha, must_entries } =
        parikh::build_parikh_descriptors(
            &super::binder::MacroBinderSyntaxReader,
            &language.terms,
            categories,
            per_cat,
            super::infix::classify_rule_public,
        );

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

    // Quote the shared original suffix table in its BTreeMap key order.
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

// Thin test adapters keep the pre-extraction baselines on the actual shared code.
#[cfg(test)]
fn build_alphabet(language: &LanguageDef) -> Alphabet {
    parikh::build_alphabet(&language.terms, super::infix::classify_rule_public)
}

#[cfg(test)]
fn param_categories(rule: &GrammarRule) -> HashMap<String, String> {
    parikh::param_categories(&super::binder::MacroBinderSyntaxReader, rule)
}

#[cfg(test)]
fn expr_must(
    expr: &SyntaxExpr,
    params: &HashMap<String, String>,
    cat_must: &HashMap<String, Mask>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> (bool, Mask) {
    use mettail_prattail::wpda_rule_analysis::binder::optional::BinderSyntaxReader;
    let observed = super::binder::MacroBinderSyntaxReader
        .at(std::slice::from_ref(expr), 0)
        .expect("single syntax expression exists");
    parikh::expr_must(observed, params, cat_must, cat_nullable, alpha)
}

#[cfg(test)]
fn rule_suffix_must(
    sp: &[SyntaxExpr],
    pos: usize,
    params: &HashMap<String, String>,
    cat_must: &HashMap<String, Mask>,
    cat_nullable: &HashMap<String, bool>,
    alpha: &Alphabet,
) -> Mask {
    parikh::rule_suffix_must(
        &super::binder::MacroBinderSyntaxReader,
        sp,
        pos,
        params,
        cat_must,
        cat_nullable,
        alpha,
    )
}

#[cfg(test)]
fn compute_category_must(
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
    alpha: &Alphabet,
) -> (HashMap<String, Mask>, HashMap<String, bool>) {
    parikh::compute_category_must(
        &super::binder::MacroBinderSyntaxReader,
        per_cat,
        categories,
        alpha,
    )
}
