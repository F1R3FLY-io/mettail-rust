//! M6c.2 (2026-05-14) — per-grammar `lex_alt_rule_for(cat_src_idx, kind)`
//! codegen helper.
//!
//! Generates a function that maps a `(category, TokenKind)` pair to the
//! `rule_idx` of an atomic-literal rule in that category that consumes the
//! kind. Returns `None` if no such rule exists.
//!
//! The lex-Fork emission path (M6c.3) uses this lookup to bind each lex
//! alternative to a concrete grammar rule before forking. A `None` result
//! means the alt's kind cannot produce an AST term in the requesting cat,
//! so the branch is dropped (rule-out by evidence, per the "never
//! disambiguate early" mandate — the parser doesn't pick; it rules out
//! impossibilities).
//!
//! The classification reuses `prefix.rs`'s `AtomicShape` so the table is
//! always in sync with the prefix-dispatch arms that produce the same
//! rule's AST.

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

use super::prefix::{classify_atomic, AtomicShape, LiteralFamily};

/// Emit the `lex_alt_rule_for` free function for a grammar.
///
/// The emitted signature is:
///
/// ```ignore
/// fn lex_alt_rule_for(
///     cat_src_idx: u16,
///     kind: &mettail_prattail::automata::TokenKind,
/// ) -> Option<u16>
/// ```
///
/// Body is a `match` over `(cat_src_idx, kind)` populated by walking
/// `per_cat`: for each (cat, rule_idx, rule) tuple, classify the rule via
/// `classify_atomic`; emit one or more arms mapping a `TokenKind` pattern
/// to `Some(rule_idx)`.
///
/// Multiple rules in the same cat with overlapping kind coverage CAN occur
/// (e.g., Calculator's Int has both `NumLit` consuming `Integer` AND a
/// `LiteralPatterned` covering `IntegerLit("Int")`). The match emits BOTH
/// arms; the first one matched wins. Order is by rule_idx ascending —
/// deterministic and stable.
pub fn emit_lex_alt_rule_for_fn(
    _language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms: Vec<TokenStream> = Vec::new();
    for (cat_src_idx, rules) in per_cat.iter().enumerate() {
        let cat_src_idx_u16 = cat_src_idx as u16;
        for (rule_idx, rule) in rules.iter().enumerate() {
            let rule_idx_u16 = rule_idx as u16;
            let shape = classify_atomic(rule, _language);
            emit_arms_for_shape(
                &shape,
                cat_src_idx_u16,
                rule_idx_u16,
                &mut arms,
            );
        }
    }
    quote! {
        /// M6c (2026-05-14): map `(cat_src_idx, kind)` to the atomic-literal
        /// rule that consumes the kind in that category. Used by the lex-Fork
        /// emitter to bind each `LexDagEdge` alternative to a concrete rule
        /// before forking — `None` means the alt's kind cannot produce an AST
        /// term in the requesting cat (rule-out by evidence).
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn lex_alt_rule_for(
            cat_src_idx: u16,
            kind: &mettail_prattail::automata::TokenKind,
        ) -> Option<u16> {
            match (cat_src_idx, kind) {
                #( #arms )*
                _ => None,
            }
        }
    }
}

/// Emit `(cat, kind) => Some(rule_idx)` arms for a given atomic shape.
///
/// Returns one or more match arms via the `arms` accumulator. Non-atomic
/// or non-literal shapes contribute zero arms.
fn emit_arms_for_shape(
    shape: &AtomicShape,
    cat_src_idx: u16,
    rule_idx: u16,
    arms: &mut Vec<TokenStream>,
) {
    // `push_simple` emits `(cat, KIND) => Some(rule_idx),`
    let push_simple = |k: TokenStream, arms: &mut Vec<TokenStream>| {
        arms.push(quote! {
            (#cat_src_idx, #k) => Some(#rule_idx),
        });
    };
    // `push_payload_eq` emits `(cat, KIND(__cat)) if __cat == "..." => ...`
    // — guard pattern is at the match-arm level, NOT inside the tuple
    // (guard patterns inside the pattern slot are still experimental in
    // stable Rust).
    let push_payload_eq = |k: TokenStream, expected: &str, arms: &mut Vec<TokenStream>| {
        arms.push(quote! {
            (#cat_src_idx, #k) if __cat == #expected => Some(#rule_idx),
        });
    };
    match shape {
        AtomicShape::LiteralInteger => {
            push_simple(
                quote! { mettail_prattail::automata::TokenKind::Integer },
                arms,
            );
        }
        AtomicShape::LiteralBoolean => {
            push_simple(
                quote! { mettail_prattail::automata::TokenKind::True },
                arms,
            );
            push_simple(
                quote! { mettail_prattail::automata::TokenKind::False },
                arms,
            );
            push_simple(
                quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                arms,
            );
        }
        AtomicShape::LiteralString => {
            push_simple(
                quote! { mettail_prattail::automata::TokenKind::StringLit },
                arms,
            );
        }
        AtomicShape::LiteralFloat => {
            push_simple(
                quote! { mettail_prattail::automata::TokenKind::Float },
                arms,
            );
        }
        AtomicShape::LiteralPatterned {
            cat_name, family, ..
        } => {
            let cat_name_lit = cat_name.as_str();
            // M6c.5.fix (2026-05-14): the calculator/rhocalc codegen
            // emits `TokenKind::Custom(cat_name)` for BigInt/BigRat/
            // Fixed literals (the suffix-tagged ones: `42n`, `1/2r`,
            // `3.14p`), AND `TokenKind::Integer/Float/etc.` for
            // unsuffixed numeric literals. Per `token_to_kind` in
            // `target/generated/<lang>/parser.rs`:
            //     Token::Integer(_, _) → TokenKind::Integer
            //     Token::BigInt(_)     → TokenKind::Custom("BigInt")
            //     Token::BigRat(_)     → TokenKind::Custom("BigRat")
            //     Token::Fixed(_)      → TokenKind::Custom("Fixed")
            //     Token::Float(_)      → TokenKind::Float
            // The previously-emitted `IntegerLit/RationalLit/
            // FixedPointLit(cat_name)` variants ARE in the
            // `TokenKind` enum but are never produced by current
            // codegen — they're legacy. Emit `Custom(cat_name)` for
            // the suffix-tagged literals AND keep the typed-lit
            // arms as defense-in-depth (zero-cost; match is exhaustive
            // on `_ => None`).
            match family {
                LiteralFamily::Integer => {
                    // Polymorphic bare `TokenKind::Integer` (unsuffixed)
                    // AND `Custom(cat_name)` (suffixed, for BigInt
                    // family) AND `IntegerLit(cat_name)` (legacy).
                    push_simple(
                        quote! { mettail_prattail::automata::TokenKind::Integer },
                        arms,
                    );
                    push_payload_eq(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        arms,
                    );
                    push_payload_eq(
                        quote! { mettail_prattail::automata::TokenKind::IntegerLit(__cat) },
                        cat_name_lit,
                        arms,
                    );
                }
                LiteralFamily::Rational => {
                    push_payload_eq(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        arms,
                    );
                    push_payload_eq(
                        quote! { mettail_prattail::automata::TokenKind::RationalLit(__cat) },
                        cat_name_lit,
                        arms,
                    );
                }
                LiteralFamily::FixedPoint => {
                    push_payload_eq(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        arms,
                    );
                    push_payload_eq(
                        quote! { mettail_prattail::automata::TokenKind::FixedPointLit(__cat) },
                        cat_name_lit,
                        arms,
                    );
                }
                LiteralFamily::Float => {
                    push_simple(
                        quote! { mettail_prattail::automata::TokenKind::Float },
                        arms,
                    );
                }
                LiteralFamily::Boolean => {
                    push_simple(
                        quote! { mettail_prattail::automata::TokenKind::True },
                        arms,
                    );
                    push_simple(
                        quote! { mettail_prattail::automata::TokenKind::False },
                        arms,
                    );
                    push_simple(
                        quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                        arms,
                    );
                }
                LiteralFamily::String => {
                    push_simple(
                        quote! { mettail_prattail::automata::TokenKind::StringLit },
                        arms,
                    );
                }
            }
        }
        // M6c.5 / P3 (2026-05-14): Var rules are NOT bound by the
        // lex-Fork. Var (Ident → categorical variable) is a
        // name-resolution concern; it's handled by standard
        // PrefixDispatch's per-cat Ident dispatch arms — which emit
        // their own Forks over `Ident → {Var, cross-cat-projection-1,
        // ...}` when in cats with cross-cat injection. The lex-Fork's
        // proper domain is multi-LITERAL ambiguity (Integer-vs-BigInt
        // for `"0"`), NOT Ident multiplicity.
        //
        // Concretely: at a position where the lex DAG has both
        // `Fixed("merge")` (keyword) AND `Ident "merge"` (var-name
        // interpretation), the canonical PARSE is the keyword. The
        // pre-P3 code mapped `Ident → MVar_rule` so the lex-Fork
        // emitted a phantom Var branch alongside the Fixed-keyword
        // primary; the phantom would `emit_push_token(Ident, "merge")`
        // and `cursor_gss_push(MVar_rule_idx.with_kind_return())`,
        // producing a downstream cursor with an AST term shaped like
        // `MVar("merge")` that polluted the cursor graph and crowded
        // out the canonical MergeMap dispatch.
        //
        // P3 fix: drop the `Ident → VarRule` mapping entirely. At
        // keyword positions, both Fixed (no rule in table — terminals
        // dispatch via standard PrefixDispatch trigger arms) AND Ident
        // (no rule after P3) yield None → `__branches.len() == 0` →
        // fall-through to standard PrefixDispatch which dispatches
        // `Fixed("merge")` → MergeMap canonically. At bare-variable
        // positions (Ident-only, no Fixed), `is_ambiguous_at` is false
        // so lex-Fork is inert; standard PrefixDispatch's Ident →
        // Var arm fires directly.
        //
        // Mandate compliance: pure rule-out by domain ("Var is not a
        // literal lex alternative"). No weight-based pre-filter. The
        // multiplicity for Var/cross-cat-from-Ident is still preserved
        // by standard PrefixDispatch's own Fork emission.
        //
        // Out of scope (M6c.6 / M6d): prefix-operator rules like
        // `Neg . - n:Int |- ... : Int`. To handle `-3!` →
        // BOTH `(-3)!` and `-(3!)`, `lex_alt_rule_for` needs to be
        // extended to map `Fixed("-")` to the unary prefix rule.
        // That requires a different walker action shape (binder-rule
        // entry, not atomic-literal with_kind_return).
        AtomicShape::VarRule { .. }
        // The remaining shapes don't directly consume a single TokenKind
        // via the lex-Fork code path. TerminalKeyword's `Fixed(text)` is
        // never a lex-DAG ambiguity producer (terminals are exact byte
        // matches, never multi-alt); CrossCatProjection/PrefixUnary
        // depend on cross-cat dispatch which the walker handles
        // separately; NonAtomic doesn't apply.
        | AtomicShape::TerminalKeyword { .. }
        | AtomicShape::CrossCatProjection { .. }
        | AtomicShape::CrossCatPrefixUnary { .. }
        | AtomicShape::NonAtomic => {}
    }
}
