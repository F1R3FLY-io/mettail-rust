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
    categories: &[String],
) -> TokenStream {
    // M6c.6.4.b (2026-05-14): split into two per-site tables —
    // `lex_alt_rule_for_prefix` for PrefixDispatch site (Atomic +
    // PrefixOp arms) and `lex_alt_rule_for_infix` for InfixLoop site
    // (PostfixOp + InfixOp + MixfixFirstTrigger arms; populated by
    // M6c.6.4.c/c2/c3). Same-token-kind ambiguity (e.g., `Fixed("-")`
    // for both unary `Neg` and binary `SubInt`) is resolved by site:
    // the lex-Fork at PrefixDispatch queries `_prefix`, the lex-Fork
    // at InfixLoop queries `_infix`. Each per-site table has no cross-
    // shape arms — clean rule-out by site discriminator.
    //
    // `categories` is threaded for codegen-time category name →
    // src_idx lookup (used by PrefixOp's `body_src_idx` resolution
    // and later by InfixOp's `result_src_idx` etc.).
    let mut prefix_arms: Vec<TokenStream> = Vec::new();
    let mut infix_arms: Vec<TokenStream> = Vec::new();
    for (cat_src_idx, rules) in per_cat.iter().enumerate() {
        let cat_src_idx_u16 = cat_src_idx as u16;
        for (rule_idx, rule) in rules.iter().enumerate() {
            let rule_idx_u16 = rule_idx as u16;
            let shape = classify_atomic(rule, _language);
            emit_arms_for_shape(
                &shape,
                cat_src_idx_u16,
                rule_idx_u16,
                categories,
                &mut prefix_arms,
                &mut infix_arms,
            );
        }
    }
    quote! {
        /// M6c.6.4.b (2026-05-14): map `(cat_src_idx, kind)` at
        /// `LexForkSite::PrefixDispatch` to a `LexAltRuleInfo` carrying
        /// the rule index AND a `LexAltRuleKind` discriminator. The
        /// lex-Fork at PrefixDispatch consults this fn; `_infix`
        /// sibling handles InfixLoop. `None` means the alt's kind has
        /// no consuming rule in the requesting cat at this site —
        /// rule-out by evidence per "never disambiguate early".
        ///
        /// Possible `kind` variants:
        /// - `Atomic`: atomic-literal rule (e.g., `NumLit`).
        /// - `PrefixOp { body_src_idx }`: same-cat unary prefix
        ///   rule (e.g., `Neg . a:Int |- "-" a : Int`).
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn lex_alt_rule_for_prefix(
            cat_src_idx: u16,
            kind: &mettail_prattail::automata::TokenKind,
        ) -> Option<mettail_prattail::wpds_runtime::LexAltRuleInfo> {
            match (cat_src_idx, kind) {
                #( #prefix_arms )*
                _ => None,
            }
        }

        /// M6c.6.4.b (2026-05-14): InfixLoop-site counterpart.
        /// Possible `kind` variants:
        /// - `PostfixOp { l_bp, result_src_idx }`: unary postfix.
        /// - `InfixOp { l_bp, r_bp, result_src_idx }`: binary infix.
        /// - `MixfixFirstTrigger { l_bp, result_src_idx }`: mixfix's
        ///   first trigger (e.g., `?` of Tern).
        ///
        /// M6c.6.4.c/c2/c3 populate the arms; until then this fn
        /// returns `None` for all inputs.
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn lex_alt_rule_for_infix(
            cat_src_idx: u16,
            kind: &mettail_prattail::automata::TokenKind,
        ) -> Option<mettail_prattail::wpds_runtime::LexAltRuleInfo> {
            match (cat_src_idx, kind) {
                #( #infix_arms )*
                _ => None,
            }
        }
    }
}

/// M6c.6.4.b: Emit `(cat, kind) => Some(LexAltRuleInfo { rule_idx, kind: ... })`
/// arms for a given atomic shape, routed to `prefix_arms` or `infix_arms`
/// based on the shape's dispatch site.
///
/// Returns one or more match arms via the accumulator references.
/// Non-atomic or non-literal shapes contribute zero arms.
///
/// `categories` is used for codegen-time category name → src_idx
/// lookup (e.g., PrefixOp's `body_src_idx`).
fn emit_arms_for_shape(
    shape: &AtomicShape,
    cat_src_idx: u16,
    rule_idx: u16,
    categories: &[String],
    prefix_arms: &mut Vec<TokenStream>,
    infix_arms: &mut Vec<TokenStream>,
) {
    // `push_simple_atomic` emits an Atomic-kind arm to prefix_arms.
    let push_simple_atomic = |k: TokenStream, arms: &mut Vec<TokenStream>| {
        arms.push(quote! {
            (#cat_src_idx, #k) => Some(
                mettail_prattail::wpds_runtime::LexAltRuleInfo {
                    rule_idx: #rule_idx,
                    kind: mettail_prattail::wpds_runtime::LexAltRuleKind::Atomic,
                }
            ),
        });
    };
    // `push_payload_eq_atomic` emits an Atomic-kind arm with a string-payload
    // equality guard (e.g., `Custom(__cat) if __cat == "BigInt"`).
    let push_payload_eq_atomic = |k: TokenStream, expected: &str, arms: &mut Vec<TokenStream>| {
        arms.push(quote! {
            (#cat_src_idx, #k) if __cat == #expected => Some(
                mettail_prattail::wpds_runtime::LexAltRuleInfo {
                    rule_idx: #rule_idx,
                    kind: mettail_prattail::wpds_runtime::LexAltRuleKind::Atomic,
                }
            ),
        });
    };
    match shape {
        AtomicShape::LiteralInteger => {
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::Integer },
                prefix_arms,
            );
        }
        AtomicShape::LiteralBoolean => {
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::True },
                prefix_arms,
            );
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::False },
                prefix_arms,
            );
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                prefix_arms,
            );
        }
        AtomicShape::LiteralString => {
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::StringLit },
                prefix_arms,
            );
        }
        AtomicShape::LiteralFloat => {
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::Float },
                prefix_arms,
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
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Integer },
                        prefix_arms,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        prefix_arms,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::IntegerLit(__cat) },
                        cat_name_lit,
                        prefix_arms,
                    );
                }
                LiteralFamily::Rational => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        prefix_arms,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::RationalLit(__cat) },
                        cat_name_lit,
                        prefix_arms,
                    );
                }
                LiteralFamily::FixedPoint => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        prefix_arms,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::FixedPointLit(__cat) },
                        cat_name_lit,
                        prefix_arms,
                    );
                }
                LiteralFamily::Float => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Float },
                        prefix_arms,
                    );
                }
                LiteralFamily::Boolean => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::True },
                        prefix_arms,
                    );
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::False },
                        prefix_arms,
                    );
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                        prefix_arms,
                    );
                }
                LiteralFamily::String => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::StringLit },
                        prefix_arms,
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
        // M6c.6.4.b (2026-05-14): same-cat unary prefix operator.
        // Emits a PrefixDispatch-site arm binding `Fixed(trigger)` to
        // this rule's `LexAltRuleKind::PrefixOp { body_src_idx }`.
        // The lex-Fork at PrefixDispatch uses this to spawn a Fork
        // branch that walker's `LexAltPrefixOp` apply arm dispatches
        // into the rule's BinderRule state (operand sub-parse).
        //
        // `body_src_idx` is the operand cat's src_idx — for same-cat
        // unary prefix it equals `cat_src_idx`. Looked up via
        // `categories` slice (codegen-baked).
        AtomicShape::PrefixOperator {
            trigger,
            operand_cat_name,
        } => {
            let body_src_idx = categories
                .iter()
                .position(|c| c == operand_cat_name)
                .map(|i| i as u16)
                .unwrap_or(cat_src_idx);
            let trigger_lit = trigger.as_str();
            prefix_arms.push(quote! {
                (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                    if __t == #trigger_lit => Some(
                        mettail_prattail::wpds_runtime::LexAltRuleInfo {
                            rule_idx: #rule_idx,
                            kind: mettail_prattail::wpds_runtime::LexAltRuleKind::PrefixOp {
                                body_src_idx: #body_src_idx,
                            },
                        }
                    ),
            });
        }
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
        | AtomicShape::NonAtomic => {
            // M6c.6.4.c/c2/c3 will route PostfixOperator/InfixOperator/
            // MixfixFirstTriggerOperator shapes to `infix_arms`.
            // Silence unused-var warning until then.
            let _ = infix_arms;
        }
    }
}
