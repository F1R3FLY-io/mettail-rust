//! M6c.2 (2026-05-14) — per-grammar lex-alt rule lookup
//! codegen helper.
//!
//! Generates functions that map a `(category, TokenKind)` pair to every
//! prefix- or infix-site token-consuming rule in that category that consumes
//! the kind. Empty result means no such rule exists.
//!
//! The lex-Fork emission path (M6c.3) uses this lookup to bind each lex
//! alternative to concrete grammar rules before forking. An empty result means
//! the alt's kind cannot produce an AST term in the requesting cat, so the
//! branch is dropped (rule-out by evidence, per the "never disambiguate early"
//! mandate — the parser doesn't pick; it rules out impossibilities).
//!
//! The classification reuses `prefix.rs`'s `AtomicShape` so the table is
//! always in sync with the prefix-dispatch arms that produce the same
//! rule's AST.

use mettail_ast::grammar::{GrammarRule, SyntaxExpr};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

use super::binder::{binder_initial_body_cat, classify_binder};
use super::infix::build_bp_table;
use super::prefix::{classify_atomic, first_set_of_category, AtomicShape, LiteralFamily};

/// Emit the lex-alt lookup free functions for a grammar.
///
/// The emitted signature is:
///
/// ```ignore
/// fn lex_alt_rules_for_prefix(
///     cat_src_idx: u16,
///     kind: &mettail_prattail::automata::TokenKind,
/// ) -> Vec<mettail_prattail::wpda_runtime::LexAltRuleInfo>
/// ```
///
/// Body is a sequence of local matches over `(cat_src_idx, kind)` populated by walking
/// `per_cat`: for each (cat, rule_idx, rule) tuple, classify the rule via
/// `classify_atomic`; emit one or more pushes mapping a `TokenKind` pattern
/// to `LexAltRuleInfo`.
///
/// Multiple rules in the same cat with overlapping kind coverage CAN occur
/// (e.g., Calculator's Int has both `NumLit` consuming `Integer` AND a
/// `LiteralPatterned` covering `IntegerLit("Int")`; Calculator's Float has
/// several `float(...)` binders). Every matching rule is returned in rule_idx
/// order so the lex fork preserves ambiguity instead of selecting the first
/// declaration too early.
pub fn emit_lex_alt_rule_for_fn(
    _language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
) -> TokenStream {
    // M6c.6.4.b (2026-05-14): split into two per-site tables —
    // `lex_alt_rules_for_prefix` for PrefixDispatch site (Atomic +
    // literal-leading binder arms) and `lex_alt_rules_for_infix` for InfixLoop site
    // (PostfixOp + InfixOp + MixfixFirstTrigger arms). Same-token-kind
    // ambiguity (e.g., `Fixed("-")` for both unary `Neg` and binary `SubInt`)
    // is resolved by site:
    // the lex-Fork at PrefixDispatch queries `_prefix`, the lex-Fork
    // at InfixLoop queries `_infix`. Each per-site table has no cross-
    // shape arms — clean rule-out by site discriminator.
    //
    // `categories` is threaded for codegen-time category name →
    // src_idx lookup (used by PrefixOp's `body_src_idx` resolution
    // and later by InfixOp's `result_src_idx` etc.).
    let mut prefix_pushes: Vec<TokenStream> = Vec::new();
    for (cat_src_idx, rules) in per_cat.iter().enumerate() {
        let cat_src_idx_u16 = cat_src_idx as u16;
        for (rule_idx, rule) in rules.iter().enumerate() {
            let rule_idx_u16 = rule_idx as u16;
            let shape = classify_atomic(rule, _language);
            emit_prefix_pushes_for_shape(
                &shape,
                cat_src_idx_u16,
                rule_idx_u16,
                categories,
                &mut prefix_pushes,
            );
            if matches!(shape, AtomicShape::NonAtomic) {
                emit_binder_prefix_pushes_for_rule(
                    rule,
                    cat_src_idx_u16,
                    rule_idx_u16,
                    categories,
                    &mut prefix_pushes,
                );
            }
            if let AtomicShape::CrossCatProjection { source_cat_name, .. } = &shape {
                emit_cross_cat_projection_prefix_pushes(
                    _language,
                    source_cat_name,
                    cat_src_idx_u16,
                    rule_idx_u16,
                    categories,
                    &mut prefix_pushes,
                );
            }
        }
    }
    emit_prefix_crosscat_lhs_pushes(_language, categories, &mut prefix_pushes);
    let prefix_primary_dispatch_arms = emit_prefix_primary_dispatch_arms(_language, per_cat);
    let prefix_primary_non_atom_dispatch_arms =
        emit_prefix_primary_non_atom_dispatch_arms(_language, per_cat);
    let prefix_crosscat_lhs_dispatch_arms =
        emit_prefix_crosscat_lhs_dispatch_arms(_language, categories);
    let prefix_crosscat_lhs_trigger_set_arms =
        emit_prefix_crosscat_lhs_trigger_set_arms(_language, categories);
    let infix_arms = emit_infix_lex_alt_rule_arms(_language, per_cat, categories);
    quote! {
        /// M6c.6.4.b (2026-05-14): map `(cat_src_idx, kind)` at
        /// `LexForkSite::PrefixDispatch` to every `LexAltRuleInfo`
        /// carrying the rule index AND a `LexAltRuleKind`
        /// discriminator. The lex-Fork at PrefixDispatch consults
        /// this fn; `_infix` sibling handles InfixLoop. An empty Vec
        /// means the alt's kind has no consuming rule in the
        /// requesting cat at this site — rule-out by evidence per
        /// "never disambiguate early".
        ///
        /// Possible `kind` variants:
        /// - `Atomic`: atomic-literal rule (e.g., `NumLit`).
        /// - `PrefixOp { body_src_idx }`: literal-leading binder
        ///   trigger (e.g., unary `Neg` or `FloatBin`'s `"float"`).
        /// - `CrossCatProjection { source_src_idx }`: transparent
        ///   wrapper whose source category can consume this token.
        /// - `CrossCatLhs { source_src_idx }`: source-category LHS
        ///   delegate whose source category can consume this token.
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn lex_alt_rules_for_prefix(
            cat_src_idx: u16,
            kind: &mettail_prattail::automata::TokenKind,
        ) -> Vec<mettail_prattail::wpda_runtime::LexAltRuleInfo> {
            let mut out = Vec::new();
            #( #prefix_pushes )*
            out
        }

        /// Returns true when normal PrefixDispatch has a primary-token arm
        /// for `(cat_src_idx, kind)` outside the lex-alt table. The lex fork
        /// uses this to avoid replacing a valid primary keyword/binder arm
        /// with a lone secondary `Ident -> Var` branch.
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn prefix_primary_has_dispatch_rule(
            cat_src_idx: u16,
            kind: &mettail_prattail::automata::TokenKind,
        ) -> bool {
            match (cat_src_idx, kind) {
                #( #prefix_primary_dispatch_arms )*
                _ => false,
            }
        }

        /// Returns true when normal PrefixDispatch has a primary-token arm
        /// for a prefix path that is not fully represented as a single-token
        /// atom. Chain synthesis uses this as live evidence to stay on the
        /// ordinary WPDA path instead of collapsing the ambiguous prefix.
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn prefix_primary_has_non_atom_dispatch_rule(
            cat_src_idx: u16,
            kind: &mettail_prattail::automata::TokenKind,
        ) -> bool {
            match (cat_src_idx, kind) {
                #( #prefix_primary_non_atom_dispatch_arms )*
                _ => false,
            }
        }

        /// Phase 5A cast-then-compare d1 (2026-06-10; FV:
        /// `CastLexForkCrossCatLhsGap.{d1_restores_hosting,
        /// extension_preserves_189_behavior, multilength_unaffected,
        /// d1_fanout_constant}`): true when normal PrefixDispatch owns a
        /// Pass-0 CROSS-CAT-LHS arm for `(cat_src_idx, kind)` — i.e. some
        /// source category `I` of a category-changing infix RESULTING in this
        /// category has `kind` in FIRST(I). The lex fork's fall-through
        /// consults this alongside `prefix_primary_has_dispatch_rule`: a
        /// keyword/ident-ambiguous cast trigger (e.g. `int` in a Bool-seeking
        /// context) falls through to the normal dispatch whose unified Pass-0
        /// arm pushes the `CrossCatLhs{I}` delegate — making the operand
        /// cursor a dispatch-time d-WORKER whose continuation hosts the infix
        /// result natively. Same-length keyword reservation applies, exactly
        /// as in the primary-rule fall-through. Secondary-keyword cases are
        /// preserved by `LexAltRuleKind::CrossCatLhs` rather than this
        /// primary-token fall-through path.
        /// Source set mirrors `prefix.rs` Pass-0 (cross_cat_infix_sources).
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn prefix_crosscat_lhs_has_dispatch_rule(
            cat_src_idx: u16,
            kind: &mettail_prattail::automata::TokenKind,
        ) -> bool {
            #( #prefix_crosscat_lhs_dispatch_arms )*
            false
        }

        /// Phase 5A d1 trigger-presence gate (2026-06-10; FV:
        /// `CastLexForkCrossCatLhsGap.{gate_no_loss,
        /// gate_zero_overhead_when_absent, gate_kills_tower_blowup}`): true
        /// when some category-changing infix RESULTING in `cat_src_idx` has
        /// its TRIGGER token in the remaining input (`pos+1..`). A
        /// cross-cat-LHS delegate can host a result ONLY by an infix that
        /// CONSUMES its trigger from the remaining input — so absence is
        /// definite, monotone refutation of every future firing, and gating
        /// the fall-through on presence drops no parse the input admits while
        /// collapsing trigger-free nested-cast towers from 2^depth delegate
        /// re-parse WORK back to owner-only work (the observed
        /// 18s/30s/>120s-timeout class). A spurious hit (the trigger occurs
        /// outside the relevant region) only dispatches a delegate that dies
        /// by evidence — soundness is one-sided by construction.
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn prefix_crosscat_lhs_trigger_ahead(
            cat_src_idx: u16,
            tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
            pos: usize,
        ) -> bool {
            let triggers: &[&str] = match cat_src_idx {
                #( #prefix_crosscat_lhs_trigger_set_arms )*
                _ => &[],
            };
            if triggers.is_empty() {
                return false;
            }
            let mut next = tokens.next_pos(pos, 0);
            while let Some(i) = next {
                if let Some(mettail_prattail::automata::TokenKind::Fixed(t)) =
                    tokens.peek_kind(i)
                {
                    if triggers.iter().any(|trig| t == *trig) {
                        return true;
                    }
                }
                let following = tokens.next_pos(i, 0);
                if following == Some(i) {
                    break;
                }
                next = following;
            }
            false
        }

        /// M6c.6.4.b (2026-05-14): InfixLoop-site counterpart.
        /// Possible `kind` variants:
        /// - `PostfixOp { l_bp, result_src_idx }`: unary postfix.
        /// - `InfixOp { l_bp, r_bp, result_src_idx }`: binary infix.
        /// - `MixfixFirstTrigger { l_bp, result_src_idx }`: mixfix's
        ///   first trigger (e.g., `?` of Tern).
        ///
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn lex_alt_rules_for_infix(
            cat_src_idx: u16,
            kind: &mettail_prattail::automata::TokenKind,
        ) -> Vec<mettail_prattail::wpda_runtime::LexAltRuleInfo> {
            match (cat_src_idx, kind) {
                #( #infix_arms )*
                _ => Vec::new(),
            }
        }
    }
}

/// Emit the body of `WpdaEngine::chain_atom_rules_for_token`.
///
/// This is deliberately narrower than `lex_alt_rules_for_prefix`: it returns
/// only token-consuming atomic rules that can form a complete single-token
/// chain atom. It includes exact terminal keywords (`"error"`,
/// `"cast_error_int"`, etc.) because chain absorption needs them even though
/// they are not lexical-alternative producers.
pub(crate) fn emit_chain_atom_rules_for_token_body(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut pushes: Vec<TokenStream> = Vec::new();
    for (cat_src_idx, rules) in per_cat.iter().enumerate() {
        let cat_src_idx_u16 = cat_src_idx as u16;
        for (rule_idx, rule) in rules.iter().enumerate() {
            let rule_idx_u16 = rule_idx as u16;
            let shape = classify_atomic(rule, language);
            emit_chain_atom_pushes_for_shape(&shape, cat_src_idx_u16, rule_idx_u16, &mut pushes);
        }
    }
    quote! {
        let mut out: Vec<u16> = Vec::new();
        let _ = text;
        #(#pushes)*
        out
    }
}

/// Emit the body of `WpdaEngine::chain_atom_producers_for_token`.
///
/// Direct producers are the same token-consuming atomic rules returned by
/// `chain_atom_rules_for_token`. Projected producers add exactly one declared
/// transparent projection from a token atom's source category into the
/// requested chain category, mirroring `single_hop_coercion`.
pub(crate) fn emit_chain_atom_producers_for_token_body(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
) -> TokenStream {
    let mut pushes: Vec<TokenStream> = Vec::new();
    for (cat_src_idx, rules) in per_cat.iter().enumerate() {
        let cat_src_idx_u16 = cat_src_idx as u16;
        for (rule_idx, rule) in rules.iter().enumerate() {
            let rule_idx_u16 = rule_idx as u16;
            let shape = classify_atomic(rule, language);
            emit_chain_atom_producer_pushes_for_shape(
                &shape,
                cat_src_idx_u16,
                quote! {
                    mettail_prattail::wpda_walker::ChainAtomProducer::direct(
                        #cat_src_idx_u16,
                        #rule_idx_u16,
                    )
                },
                &mut pushes,
            );
        }
    }

    for (from_cat, to_cat, wrap_rule_idx) in transparent_projection_rules(per_cat, categories) {
        let Some(source_rules) = per_cat.get(from_cat as usize) else {
            continue;
        };
        for (atom_rule_idx, atom_rule) in source_rules.iter().enumerate() {
            let atom_rule_idx_u16 = atom_rule_idx as u16;
            let shape = classify_atomic(atom_rule, language);
            emit_chain_atom_producer_pushes_for_shape(
                &shape,
                to_cat,
                quote! {
                    mettail_prattail::wpda_walker::ChainAtomProducer::projected(
                        #from_cat,
                        #atom_rule_idx_u16,
                        #wrap_rule_idx,
                    )
                },
                &mut pushes,
            );
        }
    }

    quote! {
        let mut out: Vec<mettail_prattail::wpda_walker::ChainAtomProducer> = Vec::new();
        let _ = text;
        #(#pushes)*
        out
    }
}

fn transparent_projection_rules(
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
) -> Vec<(u16, u16, u16)> {
    use mettail_ast::grammar::TermParam;
    use mettail_ast::types::TypeExpr;

    let mut out = Vec::new();
    for (to_cat_idx, rules) in per_cat.iter().enumerate() {
        let to_cat = to_cat_idx as u16;
        for (rule_idx, rule) in rules.iter().enumerate() {
            let Some(term_context) = rule.term_context.as_ref() else {
                continue;
            };
            if term_context.len() != 1 {
                continue;
            }
            let TermParam::Simple { name: param_name, ty } = &term_context[0] else {
                continue;
            };
            let TypeExpr::Base(source_ident) = ty else {
                continue;
            };
            let source_cat_name = source_ident.to_string();
            if source_cat_name == rule.category.to_string() {
                continue;
            }
            let Some(syntax_pattern) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            let is_transparent = syntax_pattern.len() == 1
                && matches!(
                    syntax_pattern.first(),
                    Some(SyntaxExpr::Param(syn_name)) if syn_name == param_name
                );
            if !is_transparent {
                continue;
            }
            let Some(from_cat) = categories
                .iter()
                .position(|category| category == &source_cat_name)
                .map(|idx| idx as u16)
            else {
                continue;
            };
            out.push((from_cat, to_cat, rule_idx as u16));
        }
    }
    out
}

fn emit_chain_atom_pushes_for_shape(
    shape: &AtomicShape,
    cat_src_idx: u16,
    rule_idx: u16,
    pushes: &mut Vec<TokenStream>,
) {
    let push_simple_atomic = |k: TokenStream, pushes: &mut Vec<TokenStream>| {
        pushes.push(quote! {
            match Some(kind.clone()) {
                Some(#k) if cat_src_idx == #cat_src_idx => out.push(#rule_idx),
                _ => {},
            }
        });
    };
    let push_payload_eq_atomic = |k: TokenStream, expected: &str, pushes: &mut Vec<TokenStream>| {
        pushes.push(quote! {
            match Some(kind.clone()) {
                Some(#k) if cat_src_idx == #cat_src_idx && __cat == #expected => {
                    out.push(#rule_idx)
                },
                _ => {},
            }
        });
    };

    match shape {
        AtomicShape::LiteralInteger => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::Integer }, pushes);
        },
        AtomicShape::LiteralBoolean => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::True }, pushes);
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::False }, pushes);
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                pushes,
            );
        },
        AtomicShape::LiteralString => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::StringLit }, pushes);
        },
        AtomicShape::LiteralFloat => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::Float }, pushes);
        },
        AtomicShape::LiteralPatterned { cat_name, family, .. } => {
            let cat_name_lit = cat_name.as_str();
            match family {
                LiteralFamily::Integer => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Integer },
                        pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::IntegerLit(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                },
                LiteralFamily::Rational => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::RationalLit(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                },
                LiteralFamily::FixedPoint => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::FixedPointLit(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                },
                LiteralFamily::Float => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Float },
                        pushes,
                    );
                },
                LiteralFamily::Boolean => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::True },
                        pushes,
                    );
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::False },
                        pushes,
                    );
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                        pushes,
                    );
                },
                LiteralFamily::String => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::StringLit },
                        pushes,
                    );
                },
            }
        },
        AtomicShape::TerminalKeyword { terminal_text, .. } => {
            let terminal_lit = terminal_text.as_str();
            pushes.push(quote! {
                match Some(kind.clone()) {
                    Some(mettail_prattail::automata::TokenKind::Fixed(__t))
                        if cat_src_idx == #cat_src_idx && __t == #terminal_lit => {
                            out.push(#rule_idx)
                        },
                    _ => {},
                }
            });
        },
        AtomicShape::VarRule { .. } => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::Ident }, pushes);
        },
        AtomicShape::CrossCatProjection { .. }
        | AtomicShape::CrossCatPrefixUnary { .. }
        | AtomicShape::PrefixOperator { .. }
        | AtomicShape::NonAtomic => {},
    }
}

fn emit_chain_atom_producer_pushes_for_shape(
    shape: &AtomicShape,
    target_cat_src_idx: u16,
    producer: TokenStream,
    pushes: &mut Vec<TokenStream>,
) {
    let push_simple_atomic = |k: TokenStream, pushes: &mut Vec<TokenStream>| {
        pushes.push(quote! {
            match Some(kind.clone()) {
                Some(#k) if cat_src_idx == #target_cat_src_idx => out.push(#producer),
                _ => {},
            }
        });
    };
    let push_payload_eq_atomic = |k: TokenStream, expected: &str, pushes: &mut Vec<TokenStream>| {
        pushes.push(quote! {
            match Some(kind.clone()) {
                Some(#k) if cat_src_idx == #target_cat_src_idx && __cat == #expected => {
                    out.push(#producer)
                },
                _ => {},
            }
        });
    };

    match shape {
        AtomicShape::LiteralInteger => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::Integer }, pushes);
        },
        AtomicShape::LiteralBoolean => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::True }, pushes);
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::False }, pushes);
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                pushes,
            );
        },
        AtomicShape::LiteralString => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::StringLit }, pushes);
        },
        AtomicShape::LiteralFloat => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::Float }, pushes);
        },
        AtomicShape::LiteralPatterned { cat_name, family, .. } => {
            let cat_name_lit = cat_name.as_str();
            match family {
                LiteralFamily::Integer => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Integer },
                        pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::IntegerLit(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                },
                LiteralFamily::Rational => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::RationalLit(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                },
                LiteralFamily::FixedPoint => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::FixedPointLit(__cat) },
                        cat_name_lit,
                        pushes,
                    );
                },
                LiteralFamily::Float => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Float },
                        pushes,
                    );
                },
                LiteralFamily::Boolean => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::True },
                        pushes,
                    );
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::False },
                        pushes,
                    );
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                        pushes,
                    );
                },
                LiteralFamily::String => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::StringLit },
                        pushes,
                    );
                },
            }
        },
        AtomicShape::TerminalKeyword { terminal_text, .. } => {
            let terminal_lit = terminal_text.as_str();
            pushes.push(quote! {
                match Some(kind.clone()) {
                    Some(mettail_prattail::automata::TokenKind::Fixed(__t))
                        if cat_src_idx == #target_cat_src_idx && __t == #terminal_lit => {
                            out.push(#producer)
                        },
                    _ => {},
                }
            });
        },
        AtomicShape::VarRule { .. } => {
            push_simple_atomic(quote! { mettail_prattail::automata::TokenKind::Ident }, pushes);
        },
        AtomicShape::CrossCatProjection { .. }
        | AtomicShape::CrossCatPrefixUnary { .. }
        | AtomicShape::PrefixOperator { .. }
        | AtomicShape::NonAtomic => {},
    }
}

fn emit_prefix_primary_dispatch_arms(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> Vec<TokenStream> {
    let mut fixed_triggers = std::collections::BTreeSet::<(u16, String)>::new();
    for (cat_src_idx, rules) in per_cat.iter().enumerate() {
        let cat_src_idx = cat_src_idx as u16;
        for rule in rules {
            match classify_atomic(rule, language) {
                AtomicShape::TerminalKeyword { terminal_text, .. }
                | AtomicShape::PrefixOperator { trigger: terminal_text, .. }
                | AtomicShape::CrossCatPrefixUnary { trigger: terminal_text, .. } => {
                    fixed_triggers.insert((cat_src_idx, terminal_text));
                },
                AtomicShape::NonAtomic => {
                    if let Some(sp) = rule.syntax_pattern.as_ref() {
                        if let Some(mettail_ast::grammar::SyntaxExpr::Literal(text)) = sp.first() {
                            fixed_triggers.insert((cat_src_idx, text.clone()));
                        }
                    }
                },
                _ => {},
            }
        }
    }

    fixed_triggers
        .into_iter()
        .map(|(cat_src_idx, terminal)| {
            quote! {
                (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                    if __t == #terminal => true,
            }
        })
        .collect()
}

fn emit_prefix_primary_non_atom_dispatch_arms(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> Vec<TokenStream> {
    let mut fixed_triggers = std::collections::BTreeSet::<(u16, String)>::new();
    for (cat_src_idx, rules) in per_cat.iter().enumerate() {
        let cat_src_idx = cat_src_idx as u16;
        for rule in rules {
            match classify_atomic(rule, language) {
                AtomicShape::PrefixOperator { trigger: terminal_text, .. }
                | AtomicShape::CrossCatPrefixUnary { trigger: terminal_text, .. } => {
                    fixed_triggers.insert((cat_src_idx, terminal_text));
                },
                AtomicShape::NonAtomic => {
                    if let Some(sp) = rule.syntax_pattern.as_ref() {
                        if let Some(mettail_ast::grammar::SyntaxExpr::Literal(text)) = sp.first() {
                            fixed_triggers.insert((cat_src_idx, text.clone()));
                        }
                    }
                },
                AtomicShape::TerminalKeyword { .. }
                | AtomicShape::LiteralInteger
                | AtomicShape::LiteralBoolean
                | AtomicShape::LiteralString
                | AtomicShape::LiteralFloat
                | AtomicShape::LiteralPatterned { .. }
                | AtomicShape::VarRule { .. }
                | AtomicShape::CrossCatProjection { .. } => {},
            }
        }
    }

    fixed_triggers
        .into_iter()
        .map(|(cat_src_idx, terminal)| {
            quote! {
                (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                    if __t == #terminal => true,
            }
        })
        .collect()
}

/// Phase 5A cast-then-compare d1 (2026-06-10): emit the
/// `prefix_crosscat_lhs_has_dispatch_rule` arms. For each category `d`, the
/// source set is computed EXACTLY as `prefix.rs`'s Pass-0
/// `cross_cat_infix_sources` (walk all rules whose result category is `d`;
/// keep cross-category infix LHS operand cats) so the predicate is true
/// precisely where the normal dispatch owns a unified Pass-0 `CrossCatLhs`
/// arm — no drift between the fall-through gate and the arm it falls through
/// to. Token coverage per source reuses `first_set_of_category` (the same
/// FIRST computation Pass-0's bucket patterns use). Each arm is a statement
/// `match Some(kind.clone()) { pat if cat==d && guard => return true, _ => {} }`
/// mirroring `emit_cross_cat_projection_prefix_pushes`'s pattern shape.
/// Phase 5A d1 trigger-presence gate (2026-06-10): emit the per-result-cat
/// TRIGGER-token sets for `prefix_crosscat_lhs_trigger_ahead`. For each
/// category `d` with cross-cat infix sources, the set is the `terminal` of
/// every category-changing infix resulting in `d` (the same rule walk as
/// `emit_prefix_crosscat_lhs_dispatch_arms` / prefix.rs Pass-0 — no drift).
/// Each arm: `#d_idx => &[#(triggers),*],`.
fn emit_prefix_crosscat_lhs_trigger_set_arms(
    language: &LanguageDef,
    categories: &[String],
) -> Vec<TokenStream> {
    let mut arms: Vec<TokenStream> = Vec::new();
    for (result_idx, result_cat_name) in categories.iter().enumerate() {
        let result_src_idx = result_idx as u16;
        let mut triggers: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for rule in &language.terms {
            if rule.category.to_string() != *result_cat_name {
                continue;
            }
            if let Some(info) = super::infix::classify_rule_public(rule) {
                if info.is_cross_category && info.category != info.result_category {
                    triggers.insert(info.terminal.clone());
                }
            }
        }
        if triggers.is_empty() {
            continue;
        }
        let trigger_lits: Vec<&String> = triggers.iter().collect();
        arms.push(quote! {
            #result_src_idx => &[ #( #trigger_lits ),* ],
        });
    }
    arms
}

fn emit_prefix_crosscat_lhs_dispatch_arms(
    language: &LanguageDef,
    categories: &[String],
) -> Vec<TokenStream> {
    let mut arms: Vec<TokenStream> = Vec::new();
    for (result_idx, result_cat_name) in categories.iter().enumerate() {
        let result_src_idx = result_idx as u16;
        // Mirror of prefix.rs:892-903 (Pass-0 cross_cat_infix_sources), with a
        // BTreeSet for deterministic emission order.
        let mut sources: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for rule in &language.terms {
            if rule.category.to_string() != *result_cat_name {
                continue;
            }
            if let Some(info) = super::infix::classify_rule_public(rule) {
                if info.is_cross_category && info.category != info.result_category {
                    sources.insert(info.category.clone());
                }
            }
        }
        for source_cat_name in &sources {
            for first in first_set_of_category(source_cat_name, language) {
                let pattern = first.pattern;
                let guard = first.extra_guard.unwrap_or_else(|| quote! { true });
                arms.push(quote! {
                    match Some(kind.clone()) {
                        #pattern if cat_src_idx == #result_src_idx && (#guard) => {
                            return true;
                        },
                        _ => {},
                    }
                });
            }
        }
    }
    arms
}

fn emit_prefix_crosscat_lhs_pushes(
    language: &LanguageDef,
    categories: &[String],
    prefix_pushes: &mut Vec<TokenStream>,
) {
    for (result_idx, result_cat_name) in categories.iter().enumerate() {
        let result_src_idx = result_idx as u16;
        let mut sources: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for rule in &language.terms {
            if rule.category.to_string() != *result_cat_name {
                continue;
            }
            if let Some(info) = super::infix::classify_rule_public(rule) {
                if info.is_cross_category && info.category != info.result_category {
                    sources.insert(info.category.clone());
                }
            }
        }
        for source_cat_name in &sources {
            let Some(source_src_idx) = categories
                .iter()
                .position(|cat| cat == source_cat_name)
                .map(|idx| idx as u16)
            else {
                continue;
            };
            for first in first_set_of_category(source_cat_name, language) {
                let pattern = first.pattern;
                let guard = first.extra_guard.unwrap_or_else(|| quote! { true });
                prefix_pushes.push(quote! {
                    match Some(kind.clone()) {
                        #pattern if cat_src_idx == #result_src_idx && (#guard) => out.push(
                            mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                rule_idx: #source_src_idx,
                                kind: mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatLhs {
                                    source_src_idx: #source_src_idx,
                                },
                            }
                        ),
                        _ => {},
                    }
                });
            }
        }
    }
}

/// M6c.6.4.b: Emit local match snippets that push
/// `LexAltRuleInfo { rule_idx, kind: ... }` for a given atomic shape.
///
/// Returns one or more match snippets via the accumulator references.
/// Non-atomic or non-literal shapes contribute zero arms.
///
/// `categories` is used for codegen-time category name → src_idx
/// lookup (e.g., PrefixOp's `body_src_idx`).
fn emit_prefix_pushes_for_shape(
    shape: &AtomicShape,
    cat_src_idx: u16,
    rule_idx: u16,
    categories: &[String],
    prefix_pushes: &mut Vec<TokenStream>,
) {
    // `push_simple_atomic` emits an Atomic-kind branch to prefix_pushes. The
    // generated LexAlt action captures token text and routes it through the
    // rule's return marker, which is the right shape for literals and Vars.
    let push_simple_atomic = |k: TokenStream, pushes: &mut Vec<TokenStream>| {
        pushes.push(quote! {
            match (cat_src_idx, kind) {
                (#cat_src_idx, #k) => out.push(
                    mettail_prattail::wpda_runtime::LexAltRuleInfo {
                        rule_idx: #rule_idx,
                        kind: mettail_prattail::wpda_runtime::LexAltRuleKind::Atomic,
                    }
                ),
                _ => {},
            }
        });
    };
    // `push_payload_eq_atomic` emits an Atomic-kind branch with a string-payload
    // equality guard (e.g., `Custom(__cat) if __cat == "BigInt"`).
    let push_payload_eq_atomic = |k: TokenStream, expected: &str, pushes: &mut Vec<TokenStream>| {
        pushes.push(quote! {
            match (cat_src_idx, kind) {
                (#cat_src_idx, #k) if __cat == #expected => out.push(
                    mettail_prattail::wpda_runtime::LexAltRuleInfo {
                        rule_idx: #rule_idx,
                        kind: mettail_prattail::wpda_runtime::LexAltRuleKind::Atomic,
                    }
                ),
                _ => {},
            }
        });
    };
    match shape {
        AtomicShape::LiteralInteger => {
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::Integer },
                prefix_pushes,
            );
        },
        AtomicShape::LiteralBoolean => {
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::True },
                prefix_pushes,
            );
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::False },
                prefix_pushes,
            );
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                prefix_pushes,
            );
        },
        AtomicShape::LiteralString => {
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::StringLit },
                prefix_pushes,
            );
        },
        AtomicShape::LiteralFloat => {
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::Float },
                prefix_pushes,
            );
        },
        AtomicShape::LiteralPatterned { cat_name, family, .. } => {
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
                        prefix_pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        prefix_pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::IntegerLit(__cat) },
                        cat_name_lit,
                        prefix_pushes,
                    );
                },
                LiteralFamily::Rational => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        prefix_pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::RationalLit(__cat) },
                        cat_name_lit,
                        prefix_pushes,
                    );
                },
                LiteralFamily::FixedPoint => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
                        prefix_pushes,
                    );
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::FixedPointLit(__cat) },
                        cat_name_lit,
                        prefix_pushes,
                    );
                },
                LiteralFamily::Float => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Float },
                        prefix_pushes,
                    );
                },
                LiteralFamily::Boolean => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::True },
                        prefix_pushes,
                    );
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::False },
                        prefix_pushes,
                    );
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::BooleanLit },
                        prefix_pushes,
                    );
                },
                LiteralFamily::String => {
                    push_simple_atomic(
                        quote! { mettail_prattail::automata::TokenKind::StringLit },
                        prefix_pushes,
                    );
                },
            }
        },
        AtomicShape::VarRule { .. } => {
            // Var rules are prefix-site token-consuming rules. When a lex DAG
            // position has both a keyword primary (`Fixed("merge")`) and an
            // identifier alternative (`Ident "merge"`), an identifier-only
            // category such as `Name` must be able to keep the Ident branch.
            // The generated LexAlt action has the same shape as atomic
            // literals: capture text, push the rule return marker, and let the
            // semantic action construct the Var node.
            push_simple_atomic(
                quote! { mettail_prattail::automata::TokenKind::Ident },
                prefix_pushes,
            );
        },

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
        AtomicShape::PrefixOperator { trigger, operand_cat_name } => {
            let body_src_idx = categories
                .iter()
                .position(|c| c == operand_cat_name)
                .map(|i| i as u16)
                .unwrap_or(cat_src_idx);
            let trigger_lit = trigger.as_str();
            prefix_pushes.push(quote! {
                match (cat_src_idx, kind) {
                    (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                        if __t == #trigger_lit => out.push(
                            mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                rule_idx: #rule_idx,
                                kind: mettail_prattail::wpda_runtime::LexAltRuleKind::PrefixOp {
                                    body_src_idx: #body_src_idx,
                                },
                            }
                        ),
                    _ => {},
                }
            });
        },
        // The remaining shapes don't directly consume a single TokenKind
        // via this AtomicShape path. TerminalKeyword's `Fixed(text)` is
        // never a lex-DAG ambiguity producer (terminals are exact byte
        // matches, never multi-alt); CrossCatProjection/PrefixUnary
        // depend on cross-cat dispatch which the walker handles
        // separately. NonAtomic literal-leading binders are emitted below
        // through `emit_binder_prefix_pushes_for_rule`.
        AtomicShape::TerminalKeyword { .. }
        | AtomicShape::CrossCatProjection { .. }
        | AtomicShape::CrossCatPrefixUnary { .. }
        | AtomicShape::NonAtomic => {},
    }
}

fn emit_binder_prefix_pushes_for_rule(
    rule: &GrammarRule,
    result_src_idx: u16,
    rule_idx: u16,
    categories: &[String],
    prefix_pushes: &mut Vec<TokenStream>,
) {
    let Some(shape) = classify_binder(rule) else {
        return;
    };
    let Some(SyntaxExpr::Literal(trigger)) = rule.syntax_pattern.as_ref().and_then(|sp| sp.first())
    else {
        return;
    };
    // `(`-triggered binders are handled by the paren-prefix fork, matching
    // `emit_binder_prefix_arms`; do not synthesize an extra lex-alt path here.
    if trigger == "(" {
        return;
    }
    let body_src_idx = binder_initial_body_cat(&shape)
        .and_then(|name| categories.iter().position(|c| c == name).map(|i| i as u16))
        .unwrap_or(result_src_idx);
    let trigger_lit = trigger.as_str();
    prefix_pushes.push(quote! {
        match (cat_src_idx, kind) {
            (#result_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                if __t == #trigger_lit => out.push(
                    mettail_prattail::wpda_runtime::LexAltRuleInfo {
                        rule_idx: #rule_idx,
                        kind: mettail_prattail::wpda_runtime::LexAltRuleKind::PrefixOp {
                            body_src_idx: #body_src_idx,
                        },
                    }
                ),
            _ => {},
        }
    });
}

fn emit_cross_cat_projection_prefix_pushes(
    language: &LanguageDef,
    source_cat_name: &str,
    result_src_idx: u16,
    rule_idx: u16,
    categories: &[String],
    prefix_pushes: &mut Vec<TokenStream>,
) {
    let source_src_idx = categories
        .iter()
        .position(|c| c == source_cat_name)
        .map(|i| i as u16)
        .unwrap_or(result_src_idx);
    for first in first_set_of_category(source_cat_name, language) {
        let pattern = first.pattern;
        let guard = first.extra_guard.unwrap_or_else(|| quote! { true });
        prefix_pushes.push(quote! {
            match Some(kind.clone()) {
                #pattern if cat_src_idx == #result_src_idx && (#guard) => out.push(
                    mettail_prattail::wpda_runtime::LexAltRuleInfo {
                        rule_idx: #rule_idx,
                        kind: mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatProjection {
                            source_src_idx: #source_src_idx,
                        },
                    }
                ),
                _ => {},
            }
        });
    }
}

fn build_label_index(
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> std::collections::HashMap<(String, String), (u16, u16)> {
    let mut idx = std::collections::HashMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let cat_name = &categories[cat_i];
        for (rule_i, rule) in rules.iter().enumerate() {
            idx.insert((cat_name.clone(), rule.label.to_string()), (cat_i as u16, rule_i as u16));
        }
    }
    idx
}

fn emit_infix_lex_alt_rule_arms(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
) -> Vec<TokenStream> {
    let bp_table = build_bp_table(language);
    let label_index = build_label_index(categories, per_cat);
    let mut grouped: std::collections::BTreeMap<(u16, String), Vec<TokenStream>> =
        std::collections::BTreeMap::new();

    for op in &bp_table.operators {
        let Some(cat_src_idx) = categories
            .iter()
            .position(|cat| cat == &op.category)
            .map(|idx| idx as u16)
        else {
            continue;
        };
        let Some((result_src_idx, rule_idx)) = label_index
            .get(&(op.result_category.clone(), op.label.clone()))
            .copied()
        else {
            continue;
        };
        let l_bp = op.left_bp;
        let r_bp = op.right_bp;
        let kind = if op.is_postfix {
            quote! {
                mettail_prattail::wpda_runtime::LexAltRuleKind::PostfixOp {
                    l_bp: #l_bp,
                    result_src_idx: #result_src_idx,
                }
            }
        } else if op.is_mixfix {
            quote! {
                mettail_prattail::wpda_runtime::LexAltRuleKind::MixfixFirstTrigger {
                    l_bp: #l_bp,
                    result_src_idx: #result_src_idx,
                }
            }
        } else {
            quote! {
                mettail_prattail::wpda_runtime::LexAltRuleKind::InfixOp {
                    l_bp: #l_bp,
                    r_bp: #r_bp,
                    result_src_idx: #result_src_idx,
                }
            }
        };
        grouped
            .entry((cat_src_idx, op.terminal.clone()))
            .or_default()
            .push(quote! {
                mettail_prattail::wpda_runtime::LexAltRuleInfo {
                    rule_idx: #rule_idx,
                    kind: #kind,
                }
            });
    }

    grouped
        .into_iter()
        .map(|((cat_src_idx, terminal), infos)| {
            quote! {
                (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                    if __t == #terminal => vec![ #( #infos ),* ],
            }
        })
        .collect()
}
