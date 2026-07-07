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

use mettail_ast::grammar::{GrammarRule, PatternOp, SyntaxExpr};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

use super::binder::{binder_initial_body_cat, classify_binder_in};
use super::infix::{build_bp_table, group_ops_by_cat_terminal};
use super::prefix::{classify_atomic, first_set_of_category, AtomicShape, LiteralFamily};

/// GEN-1 GAP-2 (2026-06-28): collect every `*sep` separator literal declared
/// anywhere in the grammar's syntax patterns (recursing through `#map` / `#opt`
/// chains). The cross-cat-LHS row-scoped trigger lookahead
/// (`prefix_crosscat_lhs_trigger_ahead_scoped`) treats these — minus the
/// cross-cat trigger set — as ROW / SEQUENCE separators that bound the scan at
/// depth 0, replacing the formerly-hardcoded rhocalc `;`. A separator that is
/// ALSO a cross-cat trigger must stay scannable (it binds a row's LHS), so it is
/// excluded by the caller; a pure sequence separator bounds the row.
pub(crate) fn collect_sequence_separators(language: &LanguageDef) -> std::collections::BTreeSet<String> {
    fn walk_sp(sp: &[SyntaxExpr], out: &mut std::collections::BTreeSet<String>) {
        for e in sp {
            if let SyntaxExpr::Op(op) = e {
                walk_op(op, out);
            }
        }
    }
    fn walk_op(op: &PatternOp, out: &mut std::collections::BTreeSet<String>) {
        match op {
            PatternOp::Sep { separator, source, .. } => {
                out.insert(separator.clone());
                if let Some(s) = source {
                    walk_op(s, out);
                }
            },
            PatternOp::Map { source, body, .. } => {
                walk_op(source, out);
                walk_sp(body, out);
            },
            PatternOp::Opt { inner } => walk_sp(inner, out),
            PatternOp::Zip { .. } | PatternOp::Var(_) => {},
        }
    }
    let mut seps = std::collections::BTreeSet::new();
    for rule in &language.terms {
        if let Some(sp) = &rule.syntax_pattern {
            walk_sp(sp, &mut seps);
        }
    }
    seps
}

/// GEN-1 GAP-2 (2026-06-28): the cross-cat LHS trigger set — every terminal of a
/// rule that `classify_rule_public` classifies as cross-category
/// (`is_cross_category ∧ category ≠ result_category`). Same source as
/// `emit_prefix_crosscat_lhs_trigger_set_arms`; consumed here to subtract
/// triggers from the row-separator table (a trigger must remain scannable at
/// depth 0 rather than bounding the row).
fn collect_cross_cat_triggers(language: &LanguageDef) -> std::collections::BTreeSet<String> {
    let mut triggers = std::collections::BTreeSet::new();
    for rule in &language.terms {
        if let Some(info) = super::infix::classify_rule_public(rule) {
            if info.is_cross_category && info.category != info.result_category {
                triggers.insert(info.terminal.clone());
            }
        }
    }
    triggers
}

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
                    _language,
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
    // AT_QUOTED_BIND_GATE (2026-07-03): per-category (bind_triggers,
    // polyadic_stops) arms for `prefix_at_quoted_bind_gate_evidence`.
    let at_quoted_bind_gate_trigger_arms =
        emit_at_quoted_bind_gate_trigger_arms(_language, categories);
    // F0 H1 (2026-06-28): transparent-projection fallback edges, consumed by
    // `crosscat_lhs_has_projection_fallback`. The pair tested is
    // (source_src, result_src); each emitted arm is a `(from, to)` projection
    // edge from `transparent_projection_rules` (from = source category, to =
    // result category). Same edge source as the goal-gate's `cat_can_reach`.
    let crosscat_lhs_projection_fallback_arms: Vec<TokenStream> =
        transparent_projection_rules(per_cat, categories)
            .into_iter()
            .map(|(from, to, _rule_idx)| quote! { (#from, #to) })
            .collect();
    let crosscat_lhs_projection_fallback_body = if crosscat_lhs_projection_fallback_arms.is_empty()
    {
        quote! { false }
    } else {
        quote! {
            matches!(
                (source_src, result_src),
                #( #crosscat_lhs_projection_fallback_arms )|*
            )
        }
    };
    let infix_arms = emit_infix_lex_alt_rule_arms(_language, per_cat, categories);

    // GEN-1 GAP-2 (2026-06-28): spec-derived structural-delimiter + row-separator
    // tables for `prefix_crosscat_lhs_trigger_ahead_scoped`, replacing the
    // hardcoded rhocalc bracket alphabet (`( [ { #{ {|` / `) ] } }# |}`) and the
    // hardcoded `;` row boundary. `opens`/`closes` come from the SAME
    // `collect_structural_delimiters` the rest of the backend consumes (for
    // rhocalc this is byte-identical to the former hardcode); `row_seps` is every
    // `*sep` separator declared in the grammar MINUS the cross-cat trigger set (a
    // trigger must stay scannable at depth 0; a pure sequence separator bounds the
    // row). For rhocalc this resolves to `{";", "|"}` — the extra `"|"` is the
    // Proc-parallel infix, which never occurs at depth 0 inside a for-binding
    // scan, so it is behaviorally identical to the former `{";"}`. Audit §GAP-2.
    let (gap2_opens, gap2_closes) = super::collection::collect_structural_delimiters(_language, per_cat);
    let gap2_triggers = collect_cross_cat_triggers(_language);
    let gap2_row_seps: Vec<String> = collect_sequence_separators(_language)
        .into_iter()
        .filter(|s| !gap2_triggers.contains(s))
        .collect();
    let gap2_open_lits: Vec<&String> = gap2_opens.iter().collect();
    let gap2_close_lits: Vec<&String> = gap2_closes.iter().collect();
    let gap2_row_sep_lits: Vec<&String> = gap2_row_seps.iter().collect();
    // AT_QUOTED_BIND_GATE (2026-07-03): emit `prefix_at_quoted_bind_gate_evidence`
    // ONLY when the kill-switch const is on. A baseline (gate-off) build emits an
    // EMPTY TokenStream here ⇒ the generated file is byte-identical to pre-gate.
    let at_quoted_bind_gate_evidence_fn: proc_macro2::TokenStream =
        if super::forks::AT_QUOTED_BIND_GATE {
            quote! {
                /// AT_QUOTED_BIND_GATE (2026-07-03): parse-time evidence that a
                /// `source → result` cross-cat-LHS delegate on a SIGIL that also
                /// directly triggers a sibling rule in `cat_src_idx` is the proven
                /// over-generation of that sigil-quoted sibling. Returns `true`
                /// iff the FIRST depth-0 whole-source trigger reached ahead is a
                /// `bind_trigger` (shared by a sigil-led sibling, e.g. `<-`/`<=`
                /// for rhocalc InputBind); returns `false` if a `polyadic_stop`
                /// (a whole-source trigger with NO sigil sibling, e.g. `,`) is
                /// reached first — a legitimate whole-source (polyadic) reading
                /// with no sigil counterpart, so the delegate must NOT be
                /// suppressed. Also `false` at a row boundary / bracket exit / end
                /// ⇒ FAIL-OPEN. Reuses the SAME spec-derived
                /// `__OPENS`/`__CLOSES`/`__ROW_SEPS` depth-tracking as
                /// `prefix_crosscat_lhs_trigger_ahead_scoped`. Soundness:
                /// one-sided monotone refutation of a proven over-generation (FV
                /// `AtQuotedBindGate.gate_no_loss`).
                #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
                fn prefix_at_quoted_bind_gate_evidence(
                    cat_src_idx: u16,
                    tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                    pos: usize,
                ) -> bool {
                    let (bind_triggers, polyadic_stops): (&[&str], &[&str]) =
                        match cat_src_idx {
                            #( #at_quoted_bind_gate_trigger_arms )*
                            _ => (&[], &[]),
                        };
                    if bind_triggers.is_empty() {
                        return false;
                    }
                    const __OPENS: &[&str] = &[ #( #gap2_open_lits ),* ];
                    const __CLOSES: &[&str] = &[ #( #gap2_close_lits ),* ];
                    const __ROW_SEPS: &[&str] = &[ #( #gap2_row_sep_lits ),* ];
                    let mut depth: i32 = 0;
                    let mut next = tokens.next_pos(pos, 0);
                    while let Some(i) = next {
                        if let Some(mettail_prattail::automata::TokenKind::Fixed(t)) =
                            tokens.peek_kind(i)
                        {
                            let __t = t.as_str();
                            if __OPENS.contains(&__t) {
                                depth += 1;
                            } else if __CLOSES.contains(&__t) {
                                depth -= 1;
                                if depth < 0 {
                                    return false;
                                }
                            } else if depth == 0 && __ROW_SEPS.contains(&__t) {
                                return false;
                            } else if depth == 0
                                && bind_triggers.iter().any(|trig| __t == *trig)
                            {
                                // First depth-0 whole-source trigger is a bind
                                // trigger with a sigil sibling ⇒ over-generation ⇒
                                // SUPPRESS.
                                return true;
                            } else if depth == 0
                                && polyadic_stops.iter().any(|stop| __t == *stop)
                            {
                                // First depth-0 whole-source trigger has NO sigil
                                // sibling (polyadic) ⇒ legitimate ⇒ KEEP.
                                return false;
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
            }
        } else {
            quote! {}
        };
    // CROSSCAT_LEX_COMPAT_GATE (option B backstop, 2026-07-03): emit
    // `crosscat_proj_lex_compatible` ONLY when the runtime kill-switch const is
    // on. Baseline (off) ⇒ EMPTY TokenStream ⇒ generated file byte-identical.
    //
    // The set of PROJECTION-SOURCE categories whose FIRST contains `Ident` ONLY
    // as a VAR CONTRIBUTION (the source cannot LITERALLY begin with an Ident —
    // its Ident-first comes solely from its Var rule). These are exactly the
    // sources gate (A) prunes from the `Some(Ident)` bucket. At runtime the
    // backstop refutes a CrossCatProjection push whose source is in this set
    // when the peek'd token is `Ident` — fail-open for every other case. Under
    // gate (A) this set of pushes was already removed at codegen, so the guard
    // fires 0 times (inert); it exists for the multi-token-source path + future
    // overlap. Grammar-derived: a source is included iff `Ident ∈ FIRST(source)`
    // and NO literal/keyword rule of `source` (transitively) begins with an
    // `Ident`-classified token (which, by construction, no literal rule does —
    // Idents are always variables), i.e. `Ident` is present but only via a
    // var-contribution.
    let crosscat_proj_ident_var_only_sources: Vec<TokenStream> = {
        let mut out: Vec<TokenStream> = Vec::new();
        for (idx, cat) in categories.iter().enumerate() {
            let fs = super::prefix::first_set_of_category(cat, _language);
            let has_ident = fs.iter().any(|ft| {
                ft.pattern.to_string().contains("Ident") && ft.extra_guard.is_none()
            });
            // Use the SAME soundness discriminator as gate (A): a source is
            // Ident-var-only iff it has an Ident in FIRST AND no NON-Var rule of
            // the source begins with an Ident (so a bare Ident reads ONLY as the
            // source's own var). This EXCLUDES structural sources like InputBind
            // (Ident-led `lhs:Name "<-" n`) / ForRow — whose projections must NOT
            // be refuted at runtime either.
            if has_ident && super::prefix::source_ident_first_is_var_only(cat, _language) {
                let i = idx as u16;
                out.push(quote! { #i });
            }
        }
        out
    };
    let crosscat_proj_lex_compat_fn: proc_macro2::TokenStream =
        if super::forks::CROSSCAT_LEX_COMPAT_RUNTIME_GATE {
            let members = &crosscat_proj_ident_var_only_sources;
            let membership_body = if members.is_empty() {
                quote! { false }
            } else {
                quote! { matches!(source_src, #( #members )|* ) }
            };
            quote! {
                /// CROSSCAT_LEX_COMPAT_GATE (option B backstop, 2026-07-03).
                /// Runtime lexical-compatibility guard for a cross-cat
                /// PROJECTION push: returns `true` iff the token peeked at `pos`
                /// is lex-compatible with the projection's `source_src` — i.e.
                /// the source category CAN begin with that token. It refutes
                /// (returns `false`) exactly one case: the peek is `Ident` AND
                /// `source_src`'s `Ident`-first is ONLY a var-contribution (the
                /// source cannot LITERALLY begin with an Ident) — the same
                /// over-generation gate (A) prunes at codegen. Every other token
                /// / source is FAIL-OPEN (`true`), so a legit literal-first cast
                /// (`@1`→CastBigInt on `Integer`, etc.) is never affected.
                /// INERT under gate (A) (that push no longer exists to guard).
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn crosscat_proj_lex_compatible(
                    source_src: u16,
                    tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                    pos: usize,
                ) -> bool {
                    // Only `Ident` peeks can be refuted; anything else is
                    // lex-compatible by fail-open.
                    if !matches!(
                        tokens.peek_kind(pos),
                        Some(mettail_prattail::automata::TokenKind::Ident)
                    ) {
                        return true;
                    }
                    // Peek is Ident: refute iff the source is Ident-var-only.
                    !( #membership_body )
                }
            }
        } else {
            quote! {}
        };
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

        /// ForRow Part-1 push-gate (F0, 2026-06-28): ROW-SCOPED variant of
        /// `prefix_crosscat_lhs_trigger_ahead`. The EOF predicate above scans
        /// the ENTIRE remaining input for a trigger (the legacy fall-through
        /// use, unchanged). This scoped variant instead bounds the scan to the
        /// CURRENT row / enclosing bracketed region: it depth-tracks brackets
        /// from `pos` (`( [ {` and the rhocalc multi-char collection openers
        /// `#{ {|` → +1; `) ] }` and closers `}# |}` → −1) and STOPS at the row
        /// boundary `;` (depth 0) or when a closer drops depth below 0 (the
        /// enclosing for-`)`). It returns `true` ONLY for a trigger seen at
        /// depth 0 — one that binds THIS row's LHS — before either boundary.
        ///
        /// Gating the cross-cat-LHS EXTENSION delegate PUSH (forks.rs) on this
        /// predicate keeps a triggerless in-row bind (`@[1]<-c`, `x<-a`) on its
        /// projection-only derivation while still forking the extension when a
        /// `&` / `where` / `<=` trigger genuinely binds the row's LHS. Soundness
        /// is one-sided & monotone (same shape as the EOF predicate's FV
        /// `CastLexForkCrossCatLhsGap.gate_no_loss`, extended to the PUSH site):
        /// a cross-cat-LHS delegate can host a result ONLY via an infix that
        /// CONSUMES its trigger from the remaining input at depth 0 in this row,
        /// so scoped-absence definitely refutes every in-row firing and drops
        /// only branches that would die by evidence. The `;` / depth-0 stop
        /// pins `for(@[1]<-c ; x<-a & y<-b){…}` row 1 to projection-only: a
        /// later `;`-row's `&` cannot re-enable an earlier no-`&` row. Note
        /// every rhocalc multi-char delimiter carries exactly one brace char, so
        /// single-char `{`/`}` tracking stays balanced even when a delimiter
        /// tokenizes split — the explicit multi-char arms only add robustness.
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn prefix_crosscat_lhs_trigger_ahead_scoped(
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
            // GEN-1 GAP-2 (2026-06-28): spec-derived delimiter / row-separator
            // tables (emitted from `collect_structural_delimiters` +
            // `collect_sequence_separators` \ cross-cat-triggers), replacing the
            // formerly-hardcoded rhocalc alphabet. `opens`/`closes` depth-track
            // brackets; a depth-0 `row_seps` entry bounds the row.
            const __OPENS: &[&str] = &[ #( #gap2_open_lits ),* ];
            const __CLOSES: &[&str] = &[ #( #gap2_close_lits ),* ];
            const __ROW_SEPS: &[&str] = &[ #( #gap2_row_sep_lits ),* ];
            let mut depth: i32 = 0;
            let mut next = tokens.next_pos(pos, 0);
            while let Some(i) = next {
                if let Some(mettail_prattail::automata::TokenKind::Fixed(t)) =
                    tokens.peek_kind(i)
                {
                    let __t = t.as_str();
                    if __OPENS.contains(&__t) {
                        depth += 1;
                    } else if __CLOSES.contains(&__t) {
                        depth -= 1;
                        if depth < 0 {
                            // Exited the enclosing bracketed region (for-`)`).
                            return false;
                        }
                    } else if depth == 0 && __ROW_SEPS.contains(&__t) {
                        // Row boundary: a trigger in a LATER row does not bind
                        // THIS row's LHS.
                        return false;
                    } else if depth == 0 && triggers.iter().any(|trig| __t == *trig) {
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

        // AT_QUOTED_BIND_GATE (2026-07-03): `prefix_at_quoted_bind_gate_evidence`
        // is emitted HERE only when the kill-switch const is on (see
        // `at_quoted_bind_gate_evidence_fn`); a baseline (gate-off) build emits
        // NOTHING at this point, keeping the generated file byte-identical.
        #at_quoted_bind_gate_evidence_fn

        // CROSSCAT_LEX_COMPAT_GATE (option B backstop, 2026-07-03): emitted ONLY
        // when the runtime kill-switch const is on; baseline emits NOTHING here
        // (byte-identical). See `crosscat_proj_lex_compat_fn` construction.
        #crosscat_proj_lex_compat_fn

        /// ForRow Part-1 push-gate, fallback guard (F0 H1, 2026-06-28). Returns
        /// `true` iff a TRANSPARENT PROJECTION `source_src → result_src` exists
        /// (a bare `result ::= source` injection, e.g. `ForRowSingleNoWhere`
        /// `InputBind → ForRow`). The scoped push-gate above is only NO-LOSS
        /// when such a projection exists to carry a triggerless bind: suppressing
        /// the cross-cat-LHS EXTENSION delegate then still leaves the projection
        /// derivation. Where NO projection fallback exists (e.g. LedTest
        /// `Num → Pred`, whose ONLY source→result path is the `==`/`!=`
        /// cross-cat-LHS), suppressing the delegate would remove the ONLY
        /// admitting parse — so the push MUST stay unconditional there, exactly
        /// as at baseline. Combined gate (forks.rs): keep the push iff
        /// `scoped_trigger_ahead OR NOT has_projection_fallback`. Edge set =
        /// `transparent_projection_rules` (the same projection edges the
        /// goal-gate's `cat_can_reach` consumes), so no drift.
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn crosscat_lhs_has_projection_fallback(result_src: u16, source_src: u16) -> bool {
            #crosscat_lhs_projection_fallback_body
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

/// GEN-1 goal-gate (2026-06-28): emit the engine's associated
/// `cat_can_reach(from, goal) -> bool` predicate body — `true` iff a `from`-
/// category term can be extended into a `goal`-category term by following the
/// POST-BUILT cross-cat extension graph (reflexive-transitive closure).
///
/// ## Edge set (the two facts the goal-gate rests on)
///
/// The direct edges are the UNION of:
///
/// - Cross-cat **infix / postfix / mixfix** LHS edges: for every rule that
///   `super::infix::classify_rule_public` classifies with
///   `is_cross_category ∧ category ≠ result_category`, the edge
///   `category → result_category` (the LHS source category to the operator's
///   result category, e.g. `POutput` `Name → Proc`, `InputBindPolyadic`
///   `Name → InputBind`, `ForRowWhere` `InputBind → ForRow`). `classify_rule_public`
///   classifies ONLY `[Param, …]`-leading shapes, so it returns `None` for
///   literal-leading **prefix** rules — `NQuote` (`Name ::= "@" Proc`) thus
///   contributes NO edge, i.e. `reaches(Proc, Name) = false`.
/// - **Transparent-projection** edges (`transparent_projection_rules`): a bare
///   `to ::= from` injection contributes `from → to` (e.g. `ProcInt`
///   `Int → Proc`). These too are `[Param]`-only (no literal), so prefix casts
///   never sneak in.
///
/// EXCLUDING prefix edges is load-bearing: it is exactly why a Name operand
/// (goal = Name) drops the `!`/`,` cross-cat-out operators (their results Proc /
/// InputBind cannot reach back to Name) while a top-level `CrossCatLhs`
/// (goal = None) keeps them. INCLUDING transparent projections keeps the gate a
/// CONSERVATIVE over-approximation (e.g. a Bool operator result is admitted
/// under a Proc goal when `Bool → Proc` is a transparent projection), so no
/// input-admissible parse is ever dropped.
///
/// Reflexivity (`from == goal`) is handled by an early return at the emitted
/// call site, so the `matches!` here lists only the non-reflexive transitive
/// pairs (or `false` when there are none).
pub(crate) fn emit_cat_can_reach(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
) -> TokenStream {
    use std::collections::BTreeSet;
    let idx_of = |name: &str| -> Option<u16> {
        categories
            .iter()
            .position(|category| category == name)
            .map(|i| i as u16)
    };
    // 1. Direct edges (source_cat → result_cat).
    let mut direct: BTreeSet<(u16, u16)> = BTreeSet::new();
    for rule in &language.terms {
        if let Some(info) = super::infix::classify_rule_public(rule) {
            if info.is_cross_category && info.category != info.result_category {
                if let (Some(from), Some(to)) =
                    (idx_of(&info.category), idx_of(&info.result_category))
                {
                    if from != to {
                        direct.insert((from, to));
                    }
                }
            }
        }
    }
    for (from_cat, to_cat, _rule_idx) in transparent_projection_rules(per_cat, categories) {
        if from_cat != to_cat {
            direct.insert((from_cat, to_cat));
        }
    }
    // 2. Transitive closure (reflexivity handled at the call site).
    let mut reach: BTreeSet<(u16, u16)> = direct.clone();
    loop {
        let mut added = false;
        let snapshot: Vec<(u16, u16)> = reach.iter().copied().collect();
        for &(a, b) in &snapshot {
            for &(c, d) in &snapshot {
                if b == c && a != d && reach.insert((a, d)) {
                    added = true;
                }
            }
        }
        if !added {
            break;
        }
    }
    // 3. Conservative-over-approximation guard (FV point 2): the emitted
    //    relation MUST contain every direct edge. True by construction
    //    (`reach ⊇ direct`); asserted at codegen time to catch any future
    //    regression in the closure computation — never wrongly drops.
    debug_assert!(
        direct.iter().all(|edge| reach.contains(edge)),
        "cat_can_reach RTC must contain every direct cross-cat edge (conservative over-approximation)"
    );
    // 4. Emit `matches!` over the non-reflexive pairs (or `false`).
    let pairs: Vec<(u16, u16)> = reach.into_iter().filter(|(a, b)| a != b).collect();
    if pairs.is_empty() {
        quote! { false }
    } else {
        let arms = pairs.into_iter().map(|(a, b)| quote! { (#a, #b) });
        quote! { matches!((from, goal), #( #arms )|* ) }
    }
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
        // GAP-3: a nullary multi-literal keyword run (`Map ()`, `@ Nil`) is a
        // MULTI-token primary entered via the prefix marker, NOT a single-token
        // chain atom — same exclusion as the prefix operators / NonAtomic
        // (which is what these rules classified as before GAP-3).
        AtomicShape::CrossCatProjection { .. }
        | AtomicShape::CrossCatPrefixUnary { .. }
        | AtomicShape::PrefixOperator { .. }
        | AtomicShape::NullaryLiteralRun { .. }
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
        // GAP-3: nullary multi-literal keyword run is a multi-token primary,
        // not a single-token chain-atom producer — excluded as for the prefix
        // operators / NonAtomic (its pre-GAP-3 classification).
        AtomicShape::CrossCatProjection { .. }
        | AtomicShape::CrossCatPrefixUnary { .. }
        | AtomicShape::PrefixOperator { .. }
        | AtomicShape::NullaryLiteralRun { .. }
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
                // GAP-3: a nullary multi-literal keyword run is a NON-ATOM
                // prefix dispatch (it pushes a marker + runs a multi-step
                // literal consume, not an immediate atom fire), so its trigger
                // belongs in this set — exactly as it did via the NonAtomic
                // leading-literal arm below before GAP-3 classified it.
                AtomicShape::PrefixOperator { trigger: terminal_text, .. }
                | AtomicShape::CrossCatPrefixUnary { trigger: terminal_text, .. }
                | AtomicShape::NullaryLiteralRun { trigger: terminal_text, .. } => {
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

/// AT_QUOTED_BIND_GATE (2026-07-03): per result-category match arms for the
/// `prefix_at_quoted_bind_gate_evidence` predicate. For each category emits a
/// `(bind_triggers, polyadic_stops)` pair:
///
///   - `bind_triggers` = the terminals `T` such that BOTH a whole-source
///     cross-cat-LHS rule `result ::= source T …` exists (contributing `T` to
///     the cross-cat trigger set) AND a SIGIL-LED sibling rule `result ::= σ …
///     T …` (a rule whose `syntax_pattern[0]` is a Literal `σ`) also carries
///     `T` as an interior terminal. For rhocalc InputBind + sigil `@`: `<-`
///     (InputBind `lhs "<-" n` ∧ InputBindQuoted `"@" pat "<-" n`) and `<=`
///     (InputBindPersistent ∧ InputBindQuotedPersistent). A bind-trigger
///     reached FIRST at depth 0 ⇒ the whole-`source` reading is the proven
///     over-generation of the sigil-quoted sibling ⇒ SUPPRESS.
///
///   - `polyadic_stops` = the whole-source cross-cat-LHS trigger terminals that
///     are NOT bind_triggers (no sigil-led sibling carries them) — e.g. the
///     polyadic `,` (`InputBindPolyadic lhs "," … "<-" n`, whose whole-`source`
///     reading has NO `@`-quoted counterpart). A polyadic-stop reached FIRST at
///     depth 0 ⇒ this is a legitimate whole-`source` reading with no sigil
///     sibling ⇒ do NOT suppress (the delegate is the only admitting parse).
///
/// The FIRST-hit-wins scan over `bind_triggers ∪ polyadic_stops` makes the gate
/// precise: `@a<-@b` (first depth-0 trigger `<-` ∈ bind) suppresses; `@a,b<-c`
/// (first depth-0 trigger `,` ∈ stops) does not. Both sets grammar-derived; an
/// empty `bind_triggers` (no sigil-quoted sibling shares a whole-source
/// trigger) ⇒ the predicate is always `false` ⇒ inert (baseline).
fn emit_at_quoted_bind_gate_trigger_arms(
    language: &LanguageDef,
    categories: &[String],
) -> Vec<TokenStream> {
    let mut arms: Vec<TokenStream> = Vec::new();
    for (result_idx, result_cat_name) in categories.iter().enumerate() {
        let result_src_idx = result_idx as u16;
        // whole-source cross-cat-LHS triggers (mirror
        // emit_prefix_crosscat_lhs_trigger_set_arms).
        let mut whole_source_triggers: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        for rule in &language.terms {
            if rule.category.to_string() != *result_cat_name {
                continue;
            }
            if let Some(info) = super::infix::classify_rule_public(rule) {
                if info.is_cross_category && info.category != info.result_category {
                    whole_source_triggers.insert(info.terminal.clone());
                }
            }
        }
        if whole_source_triggers.is_empty() {
            continue;
        }
        // Interior terminals of every SIGIL-LED rule in this result category
        // (rule whose syntax_pattern[0] is a Literal). Excludes that leading
        // sigil literal itself — we want the bind terminals that follow the
        // quoted operand.
        let mut sigil_interior_terminals: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        for rule in &language.terms {
            if rule.category.to_string() != *result_cat_name {
                continue;
            }
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            // Must be sigil-LED: first syntax element a literal.
            if !matches!(sp.first(), Some(mettail_ast::grammar::SyntaxExpr::Literal(_))) {
                continue;
            }
            for (i, item) in sp.iter().enumerate() {
                if i == 0 {
                    continue; // the leading sigil literal itself
                }
                if let mettail_ast::grammar::SyntaxExpr::Literal(t) = item {
                    sigil_interior_terminals.insert(t.clone());
                }
            }
        }
        let bind_triggers: Vec<&String> = whole_source_triggers
            .iter()
            .filter(|t| sigil_interior_terminals.contains(*t))
            .collect();
        let polyadic_stops: Vec<&String> = whole_source_triggers
            .iter()
            .filter(|t| !sigil_interior_terminals.contains(*t))
            .collect();
        // If no bind trigger has a sigil sibling, the gate is inert for this
        // category — omit the arm (falls through to the empty default).
        if bind_triggers.is_empty() {
            continue;
        }
        arms.push(quote! {
            #result_src_idx => (
                &[ #( #bind_triggers ),* ],
                &[ #( #polyadic_stops ),* ],
            ),
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
        // GAP-3 route (a) (2026-06-28): a nullary multi-literal keyword run
        // whose trigger ALSO lexes as an identifier (collection category names
        // `Map`/`Pathmap` lex as a `{Fixed,Ident}` lattice) MUST emit a lex-alt
        // rule here, so the `Fixed(trigger)` lattice reading is NOT dropped by
        // the lex-fork in favour of the `Ident → Var` reading. The new
        // `NullaryPrefixRun` kind routes (via forks.rs) to
        // `mixfix_marker + MixfixLiteralRun{kind:2}` — the SAME runtime arm the
        // singleton/unified-Fork prefix dispatch uses for non-lattice triggers
        // (e.g. `@Nil`, which needs no lex-alt rule because `@` is Fixed-only).
        AtomicShape::NullaryLiteralRun { trigger, .. } => {
            let trigger_lit = trigger.as_str();
            prefix_pushes.push(quote! {
                match (cat_src_idx, kind) {
                    (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                        if __t == #trigger_lit => out.push(
                            mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                rule_idx: #rule_idx,
                                kind: mettail_prattail::wpda_runtime::LexAltRuleKind::NullaryPrefixRun,
                            }
                        ),
                    _ => {},
                }
            });
        },
        // (2026-07-06) Nullary terminal-keyword atom (e.g. rhocalc `PZero . |-
        // "Nil" : Proc`; calculator `Err . |- "error" : …`). PRE-RESERVATION a
        // keyword terminal was "never a lex-DAG ambiguity producer" (an exact
        // byte match, single alt), so the PrefixDispatch lex-Fork never needed a
        // rule for it — the standard `Fixed(kw) → ConsumeAndPush(rule)` dispatch
        // arm handled it through the walker's
        // `__primary_has_dispatch && __all_alts_same_length` fall-through.
        //
        // Keyword RESERVATION invalidates that invariant. `subset.rs::
        // resolve_accept` drops the generic `Ident` co-accept at the keyword's
        // MAXIMAL DFA state, so the DAG lexer's longest-per-kind emission
        // (`runtime_types.rs::expand_lex_node`) falls the longest surviving
        // `Ident` accept back to a PROPER PREFIX of the keyword run
        // (`Nil`(len 3) → `Ni`(len 2)), fabricating a SHORTER `Ident` alt. The
        // token is now multi-alt (`is_ambiguous_at` = true) with DIFFERENT
        // lengths, so `__all_alts_same_length` is false, the fall-through is
        // BLOCKED, and the walker enters the lex-Fork. Lacking a rule for the
        // keyword's own `Fixed(kw)` reading, the lex-Fork seeded ONLY the
        // spurious `Ident → Var` prefix branch, which consumed the truncated
        // prefix and left trailing input ⇒ the reserved nullary keyword failed
        // to parse (the tracked `Nil`/`error` prefix/operand regressions).
        //
        // Emitting an `Atomic` rule here seeds the keyword's OWN `Fixed(kw)`
        // reading in the lex-Fork PRIMARY branch: forks.rs's `Atomic` arm builds
        // `rule_at(cat, rule_idx, 0).with_kind_return()` + `Unwinding` + a
        // `LexAlt` action — byte-for-byte the shape of the standard
        // `CaptureForBuilder` dispatch arm (walker's `LexAlt` apply "mirrors
        // ConsumeAndCaptureAndPush"), so the nullary AST is constructed
        // identically. The nullary cursor then competes on evidence and wins by
        // MAXIMAL MUNCH — it consumes the full keyword span (reaching the
        // downstream position / EOI), whereas the truncated `Ident` prefix
        // cursor leaves trailing input and dies. This PROPAGATES the ambiguity to
        // the WPDS fork (never disambiguating early in the lexer) — the parser
        // elects the reading with parse evidence.
        //
        // Grammar-derived, NO per-keyword hardcode: keyed on the rule's own
        // `TerminalKeyword` classification + terminal text. BYTE-IDENTICAL
        // without reservation: the keyword stays single-alt, `__all_alts_same_
        // length` holds, the fall-through fires FIRST, and `__branches` (hence
        // this rule) is never consulted. `NULLARY_KEYWORD_LEXFORK_SEED` is the
        // A/B kill-switch (flip to `false` + rebuild to reproduce the pre-fix
        // reserved-keyword failure with reservation still ON); the umbrella
        // `PRATTAIL_NO_KW_RESERVE` reverts reservation itself.
        AtomicShape::TerminalKeyword { terminal_text, .. } => {
            // Kill-switch `false` ⇒ pre-fix skip (byte-identical to the historical
            // no-op arm); reservation-off ⇒ inert regardless (fall-through
            // pre-empts the lex-Fork). See `NULLARY_KEYWORD_LEXFORK_SEED`.
            if NULLARY_KEYWORD_LEXFORK_SEED {
                let terminal_lit = terminal_text.as_str();
                prefix_pushes.push(quote! {
                    match (cat_src_idx, kind) {
                        (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                            if __t == #terminal_lit => out.push(
                                mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                    rule_idx: #rule_idx,
                                    kind: mettail_prattail::wpda_runtime::LexAltRuleKind::Atomic,
                                }
                            ),
                        _ => {},
                    }
                });
            }
        },
        // CrossCat* delegate via cross-cat dispatch; NonAtomic literal-leading
        // binders go through `emit_binder_prefix_pushes_for_rule` below.
        AtomicShape::CrossCatProjection { .. }
        | AtomicShape::CrossCatPrefixUnary { .. }
        | AtomicShape::NonAtomic => {},
    }
}

/// A/B kill-switch for the reserved nullary-keyword lex-Fork seeding fix
/// (2026-07-06; see the `AtomicShape::TerminalKeyword` arm in
/// [`emit_prefix_pushes_for_shape`]). Default `true` (fix ON). Flip to `false`
/// and rebuild to reproduce the pre-fix behavior — a reserved nullary keyword
/// (`Nil`, `error`) fails to parse in prefix/operand position because the
/// lex-Fork carries no rule for its own `Fixed(kw)` reading — WITH reservation
/// still enabled, isolating this fix from the umbrella `PRATTAIL_NO_KW_RESERVE`
/// (which reverts reservation itself). Inert without reservation regardless
/// (the fall-through pre-empts the lex-Fork), so a `false` build is byte-
/// identical to a `true` build for every non-reserving language.
pub(crate) const NULLARY_KEYWORD_LEXFORK_SEED: bool = true;

fn emit_binder_prefix_pushes_for_rule(
    language: &LanguageDef,
    rule: &GrammarRule,
    result_src_idx: u16,
    rule_idx: u16,
    categories: &[String],
    prefix_pushes: &mut Vec<TokenStream>,
) {
    let Some(shape) = classify_binder_in(rule, language) else {
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
    // GEN-1 B-2 (Stage S0): share the SAME (cat,terminal) grouping the per-tier
    // BP slice emitters consume (`group_ops_by_cat_terminal`, infix.rs), so the
    // lattice lex-alt rule multiset and the slice rule multiset are identical per
    // (cat,terminal) BY CONSTRUCTION (NO-LOSS). Pre-S0 this built its own private
    // inline `BTreeMap<(cat,terminal), Vec<LexAltRuleInfo>>`; the grouping (key,
    // membership, and within-group order) is byte-identical.
    let grouped = group_ops_by_cat_terminal(&bp_table, categories, &label_index);

    grouped
        .iter()
        .map(|((cat_src_idx, terminal), ops)| {
            let cat_src_idx = *cat_src_idx;
            let infos: Vec<TokenStream> = ops
                .iter()
                .map(|g| {
                    let op = g.op;
                    let result_src_idx = g.result_src_idx;
                    let rule_idx = g.rule_idx;
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
                    quote! {
                        mettail_prattail::wpda_runtime::LexAltRuleInfo {
                            rule_idx: #rule_idx,
                            kind: #kind,
                        }
                    }
                })
                .collect();
            quote! {
                (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                    if __t == #terminal => vec![ #( #infos ),* ],
            }
        })
        .collect()
}
