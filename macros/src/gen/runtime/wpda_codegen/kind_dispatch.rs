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
use super::infix::{build_bp_table, group_ops_by_cat_terminal, GroupedOp};
use super::prefix::{classify_atomic, first_set_of_category, AtomicShape, LiteralFamily};

/// GEN-1 GAP-2 (2026-06-28): collect every `*sep` separator literal declared
/// anywhere in the grammar's syntax patterns (recursing through `#map` / `#opt`
/// chains). The cross-cat-LHS row-scoped trigger lookahead
/// (`prefix_crosscat_lhs_trigger_ahead_scoped`) treats these — minus the
/// cross-cat trigger set — as ROW / SEQUENCE separators that bound the scan at
/// depth 0, replacing the formerly-hardcoded rholang `;`. A separator that is
/// ALSO a cross-cat trigger must stay scannable (it binds a row's LHS), so it is
/// excluded by the caller; a pure sequence separator bounds the row.
pub(crate) fn collect_sequence_separators(
    language: &LanguageDef,
) -> std::collections::BTreeSet<String> {
    enum Node<'syntax> {
        Expr(&'syntax SyntaxExpr),
        Op(&'syntax PatternOp),
    }
    fn walk_sp(sp: &[SyntaxExpr], out: &mut std::collections::BTreeSet<String>) {
        let mut work: Vec<Node<'_>> = sp.iter().rev().map(Node::Expr).collect();
        while let Some(node) = work.pop() {
            match node {
                Node::Expr(SyntaxExpr::Op(op)) => work.push(Node::Op(op)),
                Node::Expr(_) => {},
                Node::Op(op) => match op {
                    PatternOp::Sep { separator, source, .. } => {
                        out.insert(separator.clone());
                        if let Some(s) = source {
                            work.push(Node::Op(s));
                        }
                    },
                    PatternOp::Map { source, body, .. } => {
                        work.extend(body.iter().rev().map(Node::Expr));
                        work.push(Node::Op(source));
                    },
                    PatternOp::Opt { inner } => work.extend(inner.iter().rev().map(Node::Expr)),
                    PatternOp::Zip { .. } | PatternOp::Var(_) => {},
                },
            }
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
/// ```text
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
    // S1-FACTORING F1 amendment A3 (2026-07-12, red-team AV5): the lex-alt
    // surface is the SECOND dispatch surface for prefix triggers — without
    // group entries the lex-fork path would re-create the per-rule fan the
    // spine branch just removed. Grouped members' per-member
    // `PrefixOp`/`NullaryPrefixRun` entries are REPLACED by ONE
    // `PrefixOp { body_src_idx: group body }` entry carrying
    // `rule_idx = SPINE_ID` (the spine is BinderRule machinery regardless of
    // member kind — forks.rs's `LexAltPrefixOp` arm dispatches
    // `rule_at(cat, SPINE_ID, 1)`, the pre-root spine arm). EMPTY map while
    // `S1_FACTORING == false` ⇒ byte-identical emission.
    s1: &super::factoring::SpineEmission,
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
    let bp_table = build_bp_table(_language);
    for (cat_src_idx, rules) in per_cat.iter().enumerate() {
        let cat_src_idx_u16 = cat_src_idx as u16;
        for (rule_idx, rule) in rules.iter().enumerate() {
            let rule_idx_u16 = rule_idx as u16;
            let shape = classify_atomic(rule, _language);
            // S1-FACTORING A3: grouped members bypass EVERY per-member push
            // below (the item-3 assert "no per-member PrefixOp entries remain
            // for grouped members" holds by this `continue` — plus the shape
            // assert so a classifier/factoring drift fails codegen loudly).
            // The group's single spine entry rides its GroupFirst member.
            if let Some(disposition) = s1
                .dispositions
                .get(cat_src_idx)
                .and_then(|m| m.get(&rule_idx_u16))
            {
                // ★ #141 G4/G9 — both S1-FACTORING A3 invariants below refuse as
                // TOKENS. `prefix_pushes` is a `Vec<TokenStream>` spliced into the
                // emitted `lex_alt_rules_for_prefix` body, so a `compile_error!`
                // pushed here fails the build with a message rustc renders. The
                // `assert!`/`panic!` they replace could not: under this workspace's
                // cranelift dev backend a proc-macro panic prints nothing at all
                // (#141 RED-0), so "fails codegen loudly" was false as written.
                //
                // Both name the rule by LABEL as well as by the (cat, rule) index
                // pair the factoring model keys on — the pair identifies the drift
                // for a maintainer, the label identifies the rule for an author.
                if !matches!(shape, AtomicShape::NullaryLiteralRun { .. })
                    && super::binder::classify_binder_in(rule, _language).is_none()
                {
                    let message = format!(
                        "mettail: S1-FACTORING A3 — the grouped rule `{}` (category index \
                         {cat_src_idx_u16}, rule index {rule_idx_u16}) is neither a \
                         NullaryLiteralRun nor binder-classified, so the lex-alt surface \
                         would drift from the factoring model that grouped it. The \
                         classifier and the factoring model disagree; this is a macro bug, \
                         not a grammar bug — please report it.",
                        rule.label,
                    );
                    prefix_pushes.push(
                        quote::quote_spanned!(rule.label.span() => compile_error!(#message);),
                    );
                    continue;
                }
                if let super::factoring::SpineDisposition::GroupFirst {
                    spine_id,
                    body_src_idx,
                    ..
                } = disposition
                {
                    let Some(mettail_ast::grammar::SyntaxExpr::Literal(trigger)) =
                        rule.syntax_pattern.as_ref().and_then(|sp| sp.first())
                    else {
                        let message = format!(
                            "mettail: S1-FACTORING A3 — the grouped rule `{}` (category \
                             index {cat_src_idx_u16}, rule index {rule_idx_u16}) has no \
                             leading literal trigger, but a spine group is keyed on one. \
                             The factoring model and the rule's syntax pattern disagree; \
                             this is a macro bug, not a grammar bug — please report it.",
                            rule.label,
                        );
                        prefix_pushes.push(
                            quote::quote_spanned!(rule.label.span() => compile_error!(#message);),
                        );
                        continue;
                    };
                    let spine_id = *spine_id;
                    let body_src_idx = *body_src_idx;
                    let trigger_lit = trigger.as_str();
                    prefix_pushes.push(quote! {
                        match (cat_src_idx, kind) {
                            (#cat_src_idx_u16, mettail_prattail::automata::TokenKind::Fixed(__t))
                                if __t == #trigger_lit => out.push(
                                    mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                        rule_idx: #spine_id,
                                        kind: mettail_prattail::wpda_runtime::LexAltRuleKind::PrefixOp {
                                            body_src_idx: #body_src_idx,
                                        },
                                    }
                                ),
                            _ => {},
                        }
                    });
                }
                continue;
            }
            if let Some(collection) = super::collection::classify_collection(rule, _language) {
                let opener = collection.open_token;
                let has_synth_paren = collection.has_synth_paren;
                let element_src_idx = categories
                    .iter()
                    .position(|category| category == &collection.element_cat)
                    .expect("collection element category must be declared")
                    as u16;
                prefix_pushes.push(quote! {
                    match (cat_src_idx, kind) {
                        (#cat_src_idx_u16, mettail_prattail::automata::TokenKind::Fixed(text))
                            if text == #opener => out.push(
                                mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                    rule_idx: #rule_idx_u16,
                                    kind: mettail_prattail::wpda_runtime::LexAltRuleKind::CollectionOpen {
                                        element_src_idx: #element_src_idx,
                                        has_synth_paren: #has_synth_paren,
                                    },
                                }
                            ),
                        _ => {},
                    }
                });
                continue;
            }
            emit_prefix_pushes_for_shape(
                _language,
                rule,
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
                    &bp_table,
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
    let prefix_crosscat_one_token_arms =
        emit_prefix_crosscat_one_token_arms(_language, per_cat, categories);
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
    let infix_arms = emit_infix_lex_alt_rule_arms(_language, per_cat, categories, s1);

    // Native-stack bound: a large grammar can contribute hundreds of prefix
    // evidence rows.  Emitting all row constructors into one unoptimized Rust
    // function makes rustc reserve their aggregate temporaries in one native
    // frame, even though the logical transition is an iterative table scan.
    // Keep source-order accumulation exactly as before, but compile it as a
    // fixed-depth sequence of bounded, non-recursive table chunks.  Twenty-four
    // rows keeps each generated helper comfortably below the engine's 32-KiB
    // debug-frame budget for the largest shipped grammar.
    const PREFIX_LEX_ALT_ROWS_PER_CHUNK: usize = 24;
    let mut prefix_lex_alt_chunk_defs = Vec::<TokenStream>::new();
    let mut prefix_lex_alt_chunk_calls = Vec::<TokenStream>::new();
    for (chunk_idx, rows) in prefix_pushes
        .chunks(PREFIX_LEX_ALT_ROWS_PER_CHUNK)
        .enumerate()
    {
        let helper = quote::format_ident!("__lex_alt_rules_for_prefix_chunk_{chunk_idx}");
        prefix_lex_alt_chunk_defs.push(quote! {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
            fn #helper(
                cat_src_idx: u16,
                kind: &mettail_prattail::automata::TokenKind,
                out: &mut Vec<mettail_prattail::wpda_runtime::LexAltRuleInfo>,
            ) {
                #( #rows )*
            }
        });
        prefix_lex_alt_chunk_calls.push(quote! {
            #helper(cat_src_idx, kind, &mut out);
        });
    }

    // Cross-category lookahead uses the declared structural delimiters and
    // sequence separators. Cross-category triggers remain scannable at depth zero.
    // The quoted-bind gate below uses collection bracket pairs separately.
    // Binder repetition terminators must not change that gate's bracket depth.
    // AtQuotedBindGate.at_quoted_gate_dead_c4 records the old table defect.
    let (gap2_opens, gap2_closes) =
        super::collection::collect_structural_delimiters(_language, per_cat);
    let gap2_triggers = collect_cross_cat_triggers(_language);
    let gap2_row_seps: Vec<String> = collect_sequence_separators(_language)
        .into_iter()
        .filter(|s| !gap2_triggers.contains(s))
        .collect();
    let gap2_open_lits: Vec<&String> = gap2_opens.iter().collect();
    let gap2_close_lits: Vec<&String> = gap2_closes.iter().collect();
    let gap2_row_sep_lits: Vec<&String> = gap2_row_seps.iter().collect();
    let (evidence_opens, evidence_closes) =
        super::collection::collect_bracket_delimiters(_language, per_cat);
    let evidence_open_lits: Vec<&String> = evidence_opens.iter().collect();
    let evidence_close_lits: Vec<&String> = evidence_closes.iter().collect();
    let at_quoted_bind_gate_trigger_arms = emit_at_quoted_bind_gate_trigger_arms(
        _language,
        categories,
        &evidence_opens,
        &evidence_closes,
        &gap2_row_seps,
    );
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
                /// for rholang InputBind); returns `false` if a `polyadic_stop`
                /// (a whole-source trigger with NO sigil sibling, e.g. `,`) is
                /// reached first — a legitimate whole-source (polyadic) reading
                /// with no sigil counterpart, so the delegate must NOT be
                /// suppressed. A row boundary, bracket exit, or end keeps the route.
                /// The scan uses collection bracket pairs and source-specific triggers.
                /// Binder collection terminators do not change the bracket depth.
                #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
                fn prefix_at_quoted_bind_gate_evidence(
                    cat_src_idx: u16,
                    source_src_idx: u16,
                    tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                    pos: usize,
                ) -> bool {
                    let Some(mettail_prattail::automata::TokenKind::Fixed(sigil)) = tokens.peek_kind(pos) else {
                        return false;
                    };
                    let (bind_triggers, polyadic_stops): (&[&str], &[&str]) =
                        match (cat_src_idx, source_src_idx) {
                            #( #at_quoted_bind_gate_trigger_arms )*
                            _ => (&[], &[]),
                        };
                    const __OPENS: &[&str] = &[ #( #evidence_open_lits ),* ];
                    const __CLOSES: &[&str] = &[ #( #evidence_close_lits ),* ];
                    const __ROW_SEPS: &[&str] = &[ #( #gap2_row_sep_lits ),* ];
                    mettail_prattail::wpda_transitions::prefix_policy::prefix_at_quoted_bind_gate_evidence(
                        tokens, pos, bind_triggers, polyadic_stops,
                        __OPENS, __CLOSES, __ROW_SEPS,
                    )
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
            let has_ident = fs
                .iter()
                .any(|ft| ft.pattern.to_string().contains("Ident") && ft.extra_guard.is_none());
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
                    mettail_prattail::wpda_transitions::prefix_policy::crosscat_proj_lex_compatible(
                        source_src, tokens, pos, |source_src| { #membership_body },
                    )
                }
            }
        } else {
            quote! {}
        };
    quote! {
        #( #prefix_lex_alt_chunk_defs )*

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
            #( #prefix_lex_alt_chunk_calls )*
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
            mettail_prattail::wpda_transitions::prefix_policy::prefix_crosscat_lhs_trigger_ahead(
                tokens, pos, triggers,
            )
        }

        /// Reject only source/operator pairs whose entire selected `Ident`
        /// prefix is grammar-certified as a one-token atom and whose next
        /// lexical node admits neither that pair's operator nor a source
        /// extension. Unknown grammar shapes and token edges fail open.
        #[allow(dead_code, unused_variables, non_snake_case, clippy::match_same_arms)]
        fn prefix_crosscat_one_token_feasible(
            result_src: u16,
            source_src: u16,
            kind: &mettail_prattail::automata::TokenKind,
            tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
            pos: usize,
            alt_idx: usize,
        ) -> bool {
            match (result_src, source_src, kind) {
                #( #prefix_crosscat_one_token_arms )*
                _ => true,
            }
        }

        /// ForRow Part-1 push-gate (F0, 2026-06-28): ROW-SCOPED variant of
        /// `prefix_crosscat_lhs_trigger_ahead`. The EOF predicate above scans
        /// the ENTIRE remaining input for a trigger (the legacy fall-through
        /// use, unchanged). This scoped variant instead bounds the scan to the
        /// CURRENT row / enclosing bracketed region: it depth-tracks brackets
        /// from `pos` (`( [ {` and the rholang multi-char collection openers
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
        /// every rholang multi-char delimiter carries exactly one brace char, so
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
            const __OPENS: &[&str] = &[ #( #gap2_open_lits ),* ];
            const __CLOSES: &[&str] = &[ #( #gap2_close_lits ),* ];
            const __ROW_SEPS: &[&str] = &[ #( #gap2_row_sep_lits ),* ];
            mettail_prattail::wpda_transitions::prefix_policy::prefix_crosscat_lhs_trigger_ahead_scoped(
                tokens, pos, triggers, __OPENS, __CLOSES, __ROW_SEPS,
            )
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
    let borrowed: Vec<Vec<_>> = per_cat.iter().map(|rules| rules.iter().collect()).collect();
    mettail_prattail::wpda_rule_analysis::rule_observation::transparent_projection_rules(
        &super::binder::MacroBinderSyntaxReader,
        &borrowed,
        categories,
    )
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
    let pairs = category_extension_reachability(language, per_cat, categories);
    // 4. Emit `matches!` over the non-reflexive pairs (or `false`).
    if pairs.is_empty() {
        quote! { false }
    } else {
        let arms = pairs.into_iter().map(|(a, b)| quote! { (#a, #b) });
        quote! { matches!((from, goal), #( #arms )|* ) }
    }
}
pub(crate) fn category_extension_reachability(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
) -> Vec<(u16, u16)> {
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
    // 3. The original conservative-over-approximation assertion lives with
    //    the relocated closure body.
    let pairs =
        mettail_prattail::wpda_rule_analysis::rule_observation::non_reflexive_category_reachability(
            direct,
        );
    pairs
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
                // A DECLARED-pattern literal (`LiteralFamily::Custom`) reaches the parser as
                // exactly one token kind: the per-category `TokenKind::Custom(cat)` compiled from
                // its own regex. The `cat_name_lit` payload equality is what keeps two custom
                // literal categories from consuming each other's tokens — identical discipline to
                // the `Rational` / `FixedPoint` arms above, minus the legacy typed-lit variant
                // (there is no `CustomLit(cat)` in `TokenKind`, and none is wanted: the whole
                // point of the family is that the category's own pattern IS its token).
                LiteralFamily::Custom => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
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
                // A DECLARED-pattern literal (`LiteralFamily::Custom`) reaches the parser as
                // exactly one token kind: the per-category `TokenKind::Custom(cat)` compiled from
                // its own regex. The `cat_name_lit` payload equality is what keeps two custom
                // literal categories from consuming each other's tokens — identical discipline to
                // the `Rational` / `FixedPoint` arms above, minus the legacy typed-lit variant
                // (there is no `CustomLit(cat)` in `TokenKind`, and none is wanted: the whole
                // point of the family is that the category's own pattern IS its token).
                LiteralFamily::Custom => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
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
/// A conservative certificate for an `Ident`-led source. It is issued only
/// when every `Ident`-starting prefix path is a synthetic one-token variable
/// atom or a transparent projection to another certified category. All
/// infix/postfix continuations of every category on that projection chain
/// are retained as possible immediate successors; an unrecognized shape or
/// projection cycle disables the certificate. This is intentionally a
/// negative-only optimization, not a new parsing rule.
fn certified_ident_source_extensions(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
    source_idx: u16,
) -> Option<Vec<String>> {
    let mut pending = vec![usize::from(source_idx)];
    let mut seen = std::collections::BTreeSet::new();
    let mut extensions = std::collections::BTreeSet::new();
    let mut found_atom = false;
    while let Some(cat_idx) = pending.pop() {
        if !seen.insert(cat_idx) {
            return None;
        }
        let cat_name = categories.get(cat_idx)?;
        for rule in per_cat.get(cat_idx)? {
            if let Some(infix) = super::infix::classify_rule_public(rule) {
                if infix.category != *cat_name {
                    // A category-changing LHS can begin with Ident and need
                    // not complete after one token.
                    return None;
                }
                extensions.insert(infix.terminal);
                continue;
            }
            match classify_atomic(rule, language) {
                AtomicShape::VarRule { .. } => found_atom = true,
                AtomicShape::CrossCatProjection { source_cat_name, .. } => {
                    pending.push(categories.iter().position(|c| c == &source_cat_name)?);
                },
                AtomicShape::TerminalKeyword { terminal_text, .. } => {
                    if mettail_prattail::grammar_core_bridge::terminal_may_start_with_ident(
                        &terminal_text,
                    ) {
                        return None;
                    }
                },
                AtomicShape::NullaryLiteralRun { trigger, .. }
                | AtomicShape::CrossCatPrefixUnary { trigger, .. }
                | AtomicShape::PrefixOperator { trigger, .. } => {
                    if mettail_prattail::grammar_core_bridge::terminal_may_start_with_ident(
                        &trigger,
                    ) {
                        return None;
                    }
                },
                // The native literal families may be customized by the
                // lexer. Without an exact edge-disjointness proof, do not
                // certify their selected Ident alternative.
                AtomicShape::LiteralInteger
                | AtomicShape::LiteralBoolean
                | AtomicShape::LiteralString
                | AtomicShape::LiteralFloat => return None,
                AtomicShape::NonAtomic => {
                    let fixed_opener = rule
                        .syntax_pattern
                        .as_ref()
                        .and_then(|pattern| pattern.first())
                        .and_then(|part| match part {
                            SyntaxExpr::Literal(text) => Some(text.as_str()),
                            _ => None,
                        })
                        .or_else(|| match rule.items.first() {
                            Some(mettail_ast::grammar::GrammarItem::Terminal(text)) => {
                                Some(text.as_str())
                            },
                            _ => None,
                        });
                    let Some(opener) = fixed_opener else {
                        return None;
                    };
                    if opener.is_empty()
                        || mettail_prattail::grammar_core_bridge::terminal_may_start_with_ident(
                            opener,
                        )
                    {
                        return None;
                    }
                },
                AtomicShape::LiteralPatterned { .. } => return None,
            }
        }
    }
    found_atom.then(|| extensions.into_iter().collect())
}

fn emit_prefix_crosscat_one_token_arms(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
    categories: &[String],
) -> Vec<TokenStream> {
    let mut pairs =
        std::collections::BTreeMap::<(u16, u16), std::collections::BTreeSet<String>>::new();
    for rule in &language.terms {
        let Some(infix) = super::infix::classify_rule_public(rule) else {
            continue;
        };
        if !infix.is_cross_category || infix.category == infix.result_category {
            continue;
        }
        let Some(result) = categories.iter().position(|c| c == &infix.result_category) else {
            continue;
        };
        let Some(source) = categories.iter().position(|c| c == &infix.category) else {
            continue;
        };
        pairs
            .entry((result as u16, source as u16))
            .or_default()
            .insert(infix.terminal);
    }
    pairs
        .into_iter()
        .filter_map(|((result, source), target_operators)| {
            let source_extensions =
                certified_ident_source_extensions(language, per_cat, categories, source)?;
            let target_operators: Vec<_> = target_operators.into_iter().collect();
            Some(quote! {
                (#result, #source, mettail_prattail::automata::TokenKind::Ident) =>
                    mettail_prattail::wpda_transitions::prefix_policy::crosscat_one_token_successor_may_continue(
                        tokens, pos, alt_idx,
                        &[ #( #target_operators ),* ],
                        &[ #( #source_extensions ),* ],
                    ),
            })
        })
        .collect()
}

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

fn quoted_bind_tail(
    rule: &GrammarRule,
    prefix: Option<&str>,
    operand_category: &str,
) -> Option<(
    Vec<mettail_prattail::wpda_rule_analysis::InfixTypeShape>,
    Vec<mettail_prattail::wpda_rule_analysis::InfixSyntaxShape>,
)> {
    use mettail_prattail::wpda_rule_analysis::{InfixParamShape, InfixSyntaxShape, InfixTypeShape};
    let mut shape = super::infix::project_infix_rule(rule);
    let params = shape.term_context.take()?;
    let mut syntax = shape.syntax_pattern.take()?;
    if let Some(prefix) = prefix {
        if !matches!(syntax.first(), Some(InfixSyntaxShape::Literal(text)) if text == prefix) {
            return None;
        }
        syntax.remove(0);
    }
    let mut names = std::collections::BTreeMap::new();
    let mut types = Vec::with_capacity(params.len());
    for (index, param) in params.into_iter().enumerate() {
        let InfixParamShape::Simple { name, ty } = param else {
            return None;
        };
        if matches!(ty, InfixTypeShape::Other | InfixTypeShape::Collection { element_base: None })
            || names.insert(name, index.to_string()).is_some()
        {
            return None;
        }
        types.push(ty);
    }
    if types.first() != Some(&InfixTypeShape::Base(operand_category.into())) {
        return None;
    }
    for part in &mut syntax {
        match part {
            InfixSyntaxShape::Param(name) | InfixSyntaxShape::Sep { collection: name, .. } => {
                *name = names.get(name)?.clone();
            },
            InfixSyntaxShape::Literal(_) => {},
            InfixSyntaxShape::Other => return None,
        }
    }
    if syntax.first() != Some(&InfixSyntaxShape::Param("0".into())) {
        return None;
    }
    Some((types.into_iter().skip(1).collect(), syntax.into_iter().skip(1).collect()))
}

pub(super) struct QuotedBindFamily {
    pub result: String,
    pub source: String,
    pub prefix: String,
    pub binds: std::collections::BTreeSet<String>,
    pub stops: std::collections::BTreeSet<String>,
    pub rule_pairs: std::collections::BTreeSet<(String, String)>,
}

pub(super) fn quoted_bind_families(language: &LanguageDef) -> Vec<QuotedBindFamily> {
    use std::collections::{BTreeMap, BTreeSet};
    let mut normalized = language.clone();
    for rule in &mut normalized.terms {
        mettail_ast::grammar::convert_items_to_term_context(rule);
    }
    let aliases = crate::gen::syntax::synonymy::derive(&normalized);
    let mut operators: BTreeMap<(String, String), BTreeMap<String, Vec<&GrammarRule>>> =
        BTreeMap::new();
    for rule in &normalized.terms {
        if let Some(info) = super::infix::classify_rule_public(rule) {
            if info.is_cross_category {
                operators
                    .entry((info.result_category, info.category))
                    .or_default()
                    .entry(info.terminal)
                    .or_default()
                    .push(rule);
            }
        }
    }
    let mut families = Vec::new();
    for ((result, source), triggers) in operators {
        let mut wrappers: BTreeMap<String, Vec<(&GrammarRule, String)>> = BTreeMap::new();
        for rule in normalized
            .terms
            .iter()
            .filter(|rule| rule.category == source)
        {
            if let AtomicShape::CrossCatPrefixUnary { trigger, source_cat_name, .. } =
                classify_atomic(rule, &normalized)
            {
                wrappers
                    .entry(trigger)
                    .or_default()
                    .push((rule, source_cat_name));
            }
        }
        for (prefix, wrappers) in wrappers {
            let mut source_labels = BTreeSet::new();
            for (wrapper, _) in &wrappers {
                source_labels.insert(wrapper.label.to_string());
                for class in &aliases.classes {
                    if class.category == source
                        && class.members.contains(&wrapper.label.to_string())
                    {
                        source_labels.extend(normalized.terms.iter().filter(|rule| {
                            class.members.contains(&rule.label.to_string())
                                && matches!(rule.syntax_pattern.as_deref().and_then(|syntax| syntax.first()),
                                    Some(SyntaxExpr::Literal(text)) if text == &prefix)
                        }).map(|rule| rule.label.to_string()));
                    }
                }
            }
            let complete_source = normalized
                .terms
                .iter()
                .filter(|rule| rule.category == source)
                .all(|rule| {
                    match rule
                        .syntax_pattern
                        .as_deref()
                        .and_then(|syntax| syntax.first())
                    {
                        Some(SyntaxExpr::Literal(text)) if text == &prefix => {
                            source_labels.contains(&rule.label.to_string())
                        },
                        _ => true,
                    }
                });
            if !complete_source {
                continue;
            }
            let mut family = QuotedBindFamily {
                result: result.clone(),
                source: source.clone(),
                prefix: prefix.clone(),
                binds: BTreeSet::new(),
                stops: BTreeSet::new(),
                rule_pairs: BTreeSet::new(),
            };
            for (trigger, whole_rules) in &triggers {
                let covered = whole_rules.iter().all(|whole| {
                    let Some(whole_tail) = quoted_bind_tail(whole, None, &source) else {
                        return false;
                    };
                    wrappers.iter().all(|(_, operand)| {
                        normalized.terms.iter().any(|direct| {
                            direct.category == result
                                && quoted_bind_tail(direct, Some(&prefix), operand)
                                    .is_some_and(|tail| tail == whole_tail)
                        })
                    })
                });
                if covered {
                    family.binds.insert(trigger.clone());
                    for whole in whole_rules {
                        family.rule_pairs.extend(
                            source_labels
                                .iter()
                                .map(|atom| (whole.label.to_string(), atom.clone())),
                        );
                    }
                } else {
                    family.stops.insert(trigger.clone());
                }
            }
            if !family.binds.is_empty() {
                families.push(family);
            }
        }
    }
    families
}

fn emit_at_quoted_bind_gate_trigger_arms(
    language: &LanguageDef,
    categories: &[String],
    opens: &std::collections::BTreeSet<String>,
    closes: &std::collections::BTreeSet<String>,
    rows: &[String],
) -> Vec<TokenStream> {
    quoted_bind_families(language)
        .into_iter()
        .filter_map(|family| {
            let result_src_idx = categories.iter().position(|cat| cat == &family.result)? as u16;
            let source_src_idx = categories.iter().position(|cat| cat == &family.source)? as u16;
            if family.binds.iter().chain(&family.stops).any(|trigger| {
                opens.contains(trigger) || closes.contains(trigger) || rows.contains(trigger)
            }) {
                return None;
            }
            let prefix = family.prefix;
            let binds = family.binds;
            let stops = family.stops;
            Some(quote! {
                (#result_src_idx, #source_src_idx) if sigil.as_str() == #prefix => (
                    &[ #(#binds),* ], &[ #(#stops),* ],
                ),
            })
        })
        .collect()
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
    language: &LanguageDef,
    rule: &GrammarRule,
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
            // M6c.5.fix (2026-05-14): the calculator/rholang codegen
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
                // A DECLARED-pattern literal (`LiteralFamily::Custom`) reaches the parser as
                // exactly one token kind: the per-category `TokenKind::Custom(cat)` compiled from
                // its own regex. The `cat_name_lit` payload equality is what keeps two custom
                // literal categories from consuming each other's tokens — identical discipline to
                // the `Rational` / `FixedPoint` arms above, minus the legacy typed-lit variant
                // (there is no `CustomLit(cat)` in `TokenKind`, and none is wanted: the whole
                // point of the family is that the category's own pattern IS its token).
                LiteralFamily::Custom => {
                    push_payload_eq_atomic(
                        quote! { mettail_prattail::automata::TokenKind::Custom(__cat) },
                        cat_name_lit,
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
        AtomicShape::CrossCatPrefixUnary { trigger, source_cat_name, .. } => {
            let source_src_idx = categories
                .iter()
                .position(|category| category == source_cat_name)
                .map(|index| index as u16)
                .unwrap_or(cat_src_idx);
            let bp_table = build_bp_table(language);
            let operand_bp = mettail_prattail::binding_power::compute_prefix_bp(
                source_cat_name,
                rule.prefix_bp,
                &bp_table,
            );
            let trigger_lit = trigger.as_str();
            prefix_pushes.push(quote! {
                match (cat_src_idx, kind) {
                    (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                        if __t == #trigger_lit => out.push(
                            mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                rule_idx: #rule_idx,
                                kind: mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatPrefixUnary {
                                    source_src_idx: #source_src_idx,
                                    operand_bp: #operand_bp,
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
        // (2026-07-06) Nullary terminal-keyword atom (e.g. rholang `PZero . |-
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
        // reserved-keyword failure with reservation still ON). Keyword
        // reservation itself is now unconditional (derived per policy).
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
        AtomicShape::CrossCatProjection { .. } | AtomicShape::NonAtomic => {},
    }
}

/// A/B kill-switch for the reserved nullary-keyword lex-Fork seeding fix
/// (2026-07-06; see the `AtomicShape::TerminalKeyword` arm in
/// [`emit_prefix_pushes_for_shape`]). Default `true` (fix ON). Flip to `false`
/// and rebuild to reproduce the pre-fix behavior — a reserved nullary keyword
/// (`Nil`, `error`) fails to parse in prefix/operand position because the
/// lex-Fork carries no rule for its own `Fixed(kw)` reading — WITH reservation
/// still enabled, isolating this fix from keyword reservation itself (now
/// unconditional, derived per policy). Inert without reservation regardless
/// (the fall-through pre-empts the lex-Fork), so a `false` build is byte-
/// identical to a `true` build for every non-reserving language.
pub(crate) const NULLARY_KEYWORD_LEXFORK_SEED: bool = true;

fn emit_binder_prefix_pushes_for_rule(
    language: &LanguageDef,
    rule: &GrammarRule,
    result_src_idx: u16,
    rule_idx: u16,
    categories: &[String],
    bp_table: &mettail_prattail::binding_power::BindingPowerTable,
    prefix_pushes: &mut Vec<TokenStream>,
) {
    let Some(shape) = classify_binder_in(rule, language) else {
        return;
    };
    let body_src_idx = binder_initial_body_cat(&shape)
        .and_then(|name| categories.iter().position(|c| c == name).map(|i| i as u16))
        .unwrap_or(result_src_idx);
    match rule.syntax_pattern.as_ref().and_then(|sp| sp.first()) {
        Some(SyntaxExpr::Literal(trigger)) => {
            // `(`-triggered binders are handled by the paren-prefix fork, matching
            // `emit_binder_prefix_arms`; do not synthesize an extra lex-alt path here.
            if trigger == "(" {
                return;
            }
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
        },
        // L9-3 — a LEADING `b@Tok` builtin/custom token-family capture. The
        // matching kind IS the
        // trigger; register it so the modern lattice prefix dispatch explores
        // the capture reading (the legacy peek-arm only fires on fall-through,
        // which a lex-ambiguous opener suppresses).
        Some(SyntaxExpr::TokenKind { name, .. }) => {
            let kind_name = name.to_string();
            prefix_pushes.push(quote! {
                match (cat_src_idx, kind) {
                    (#result_src_idx, __kind)
                        if mettail_prattail::automata::token_kind_matches_capture_name(
                            #kind_name,
                            __kind,
                        ) => out.push(
                            mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                rule_idx: #rule_idx,
                                kind: mettail_prattail::wpda_runtime::LexAltRuleKind::LeadingTokenKindCapture {
                                    body_src_idx: #body_src_idx,
                                    kind_name: #kind_name,
                                },
                            }
                        ),
                    _ => {},
                }
            });
        },
        // L9-4 — a LEADING `*flt(node, open, close)` GuestBody capture. The
        // opener kind is the trigger; register it (same rationale as the
        // TokenKind capture) so the FLT reading survives lex ambiguity of the
        // opener (e.g. `` lam` `` also lexing as `Ident`).
        Some(SyntaxExpr::GuestBody { open, close, .. }) => {
            let open_kind = open.to_string();
            let nested_open_kinds = super::guest_body_nested_open_kinds(language, &open_kind);
            let close_kind = close.to_string();
            prefix_pushes.push(quote! {
                match (cat_src_idx, kind) {
                    (#result_src_idx, mettail_prattail::automata::TokenKind::Custom(ref __k))
                        if __k == #open_kind => out.push(
                            mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                rule_idx: #rule_idx,
                                kind: mettail_prattail::wpda_runtime::LexAltRuleKind::LeadingGuestBody {
                                    body_src_idx: #body_src_idx,
                                    open_kind: #open_kind,
                                    nested_open_kinds: &[#(#nested_open_kinds),*],
                                    close_kind: #close_kind,
                                },
                            }
                        ),
                    _ => {},
                }
            });
        },
        Some(SyntaxExpr::Param(_)) => {
            let Some(source_cat_name) = shape.leading_category.as_deref() else {
                return;
            };
            let Some(source_src_idx) = categories
                .iter()
                .position(|category| category == source_cat_name)
                .map(|index| index as u16)
            else {
                return;
            };
            let result_category = rule.category.to_string();
            // Same-category led rules are represented by the infix lexical
            // table and InfixLoop only. Publishing them as prefix lexical
            // alternatives would recreate the generic-continuation bypass of
            // their Pratt right power.
            if super::prefix::same_category_led_left_bp(rule, &result_category, bp_table).is_some()
            {
                return;
            }
            for first in first_set_of_category(source_cat_name, language) {
                let pattern = first.pattern;
                let guard = first.extra_guard.unwrap_or_else(|| quote! { true });
                prefix_pushes.push(quote! {
                    match Some(kind.clone()) {
                        #pattern if cat_src_idx == #result_src_idx && (#guard) => out.push(
                            mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                rule_idx: #rule_idx,
                                kind: mettail_prattail::wpda_runtime::LexAltRuleKind::LeadingCategory {
                                    source_src_idx: #source_src_idx,
                                },
                            }
                        ),
                        _ => {},
                    }
                });
            }
        },
        _ => {},
    }
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
    // S1-FACTORING F5-2 (A3-analog, red-team A-M5): factored mixfix cohorts
    // must ALSO be grouped on the lex-alt surface — without group entries
    // the lattice lex-fork path re-creates the per-member fan the spine
    // branch just removed. Grouped members' per-member `MixfixFirstTrigger`
    // entries are REPLACED by ONE entry carrying `rule_idx = SPINE_ID` and
    // `l_bp = the cohort MIN l_bp` (the D-1 full-admission gate expressed
    // through the site's own floor-only predicate `l_bp >= cur_bp`);
    // forks.rs's `LexAltMixfixOp` sites redirect the weight/action
    // identities to the MIN member via `__s1_spine_weight_rule`. EMPTY
    // `mixfix_groups` ⇒ byte-identical emission.
    s1: &super::factoring::SpineEmission,
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
            let mixfix_group = s1
                .mixfix_groups
                .iter()
                .find(|g| {
                    g.dispatch_cat_src_idx == cat_src_idx && &g.trigger == terminal
                });
            if let Some(group) = mixfix_group {
                // D-5 whole-slice agreement between the factoring model and
                // THIS surface's mixfix subset (same grouping + the same
                // `GEN1_MAX_SLICE` window as `mixfix_bp_<cat>`): drift fails
                // codegen loudly instead of silently splitting the cohort
                // across surfaces.
                let mixfix_rules: Vec<u16> = ops
                    .iter()
                    .filter(|g| g.op.is_mixfix)
                    .take(super::infix::GEN1_MAX_SLICE)
                    .map(|g| g.rule_idx)
                    .collect();
                assert_eq!(
                    mixfix_rules, group.member_rule_idxs,
                    "S1-FACTORING F5-2 A3-analog: (cat {cat_src_idx}, {terminal:?}) \
                     lex-alt mixfix subset diverged from the factored cohort",
                );
            }
            let mut spine_entry_emitted = false;
            let infos: Vec<TokenStream> = ops
                .iter()
                .filter_map(|g| {
                    // Grouped mixfix members: ONE spine entry at the first
                    // member's position; the rest are REPLACED (no
                    // per-member MixfixFirstTrigger entries remain).
                    if let Some(group) = mixfix_group {
                        if g.op.is_mixfix
                            && group.member_rule_idxs.contains(&g.rule_idx)
                        {
                            if spine_entry_emitted {
                                return None;
                            }
                            spine_entry_emitted = true;
                            let spine_id = group.spine_id;
                            let min_l_bp = group.min_l_bp;
                            let result_src_idx = group.result_src_idx;
                            return Some(quote! {
                                mettail_prattail::wpda_runtime::LexAltRuleInfo {
                                    rule_idx: #spine_id,
                                    kind: mettail_prattail::wpda_runtime::LexAltRuleKind::MixfixFirstTrigger {
                                        l_bp: #min_l_bp,
                                        result_src_idx: #result_src_idx,
                                    },
                                }
                            });
                        }
                    }
                    Some(emit_infix_lex_alt_info(g))
                })
                .collect();
            let info_count = infos.len();
            let info_pushes = infos.iter().map(|info| {
                quote! {
                    __lex_alt_infos.push(#info);
                }
            });
            quote! {
                (#cat_src_idx, mettail_prattail::automata::TokenKind::Fixed(__t))
                    if __t == #terminal => {
                        let mut __lex_alt_infos =
                            ::std::vec::Vec::with_capacity(#info_count);
                        #( #info_pushes )*
                        __lex_alt_infos
                    },
            }
        })
        .collect()
}

/// One per-op `LexAltRuleInfo` record (the pre-F5-2 inline mapping,
/// extracted verbatim).
fn emit_infix_lex_alt_info(g: &GroupedOp<'_>) -> TokenStream {
    {
        {
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{rule_fixture, GrammarItem, SyntaxExpr, TermParam};
    use mettail_ast::types::TypeExpr;
    use proc_macro2::Span;
    use syn::Ident;

    fn empty_lang() -> LanguageDef {
        LanguageDef {
            name: Ident::new("LexAltPhaseTest", Span::call_site()),
            version: None,
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    fn terminal_rule(label: &str, category: &str, text: &str) -> GrammarRule {
        GrammarRule {
            items: vec![GrammarItem::Terminal(text.into())],
            ..rule_fixture(
                Ident::new(label, Span::call_site()),
                Ident::new(category, Span::call_site()),
            )
        }
    }

    fn judgment_rule(
        label: &str,
        category: &str,
        params: &[(&str, &str)],
        syntax: Vec<SyntaxExpr>,
    ) -> GrammarRule {
        GrammarRule {
            term_context: Some(
                params
                    .iter()
                    .map(|(name, ty)| TermParam::Simple {
                        name: Ident::new(name, Span::call_site()),
                        ty: TypeExpr::Base(Ident::new(ty, Span::call_site())),
                    })
                    .collect(),
            ),
            syntax_pattern: Some(syntax),
            ..rule_fixture(
                Ident::new(label, Span::call_site()),
                Ident::new(category, Span::call_site()),
            )
        }
    }

    proptest::proptest! {
        #![proptest_config(proptest::test_runner::Config::with_cases(64))]

        #[test]
        fn quoted_bind_rows_preserve_rule_associations(suffix in "[A-Z]{1,6}") {
            use proptest::prelude::*;
            let value = format!("Value{suffix}");
            let source = format!("Source{suffix}");
            let result = format!("Result{suffix}");
            let mut language = empty_lang();
            let param = |name: &str| SyntaxExpr::Param(Ident::new(name, Span::call_site()));
            let lit = |text: &str| SyntaxExpr::Literal(text.into());
            let whole = |label: &str, trigger: &str| judgment_rule(
                label, &result, &[("lhs", &source), ("rhs", &value)],
                vec![param("lhs"), lit(trigger), lit("("), param("rhs"), lit(")")],
            );
            let direct = |label: &str, prefix: &str, trigger: &str, body: &str, close: &str| judgment_rule(
                label, &result, &[("body", body), ("arg", &value)],
                vec![lit(prefix), param("body"), lit(trigger), lit("("), param("arg"), lit(close)],
            );
            language.terms = vec![
                judgment_rule("Quote", &source, &[("value", &value)], vec![lit("@"), param("value")]),
                judgment_rule("Mark", &source, &[("value", &value)], vec![lit("#"), param("value")]),
                whole("Send", "!"), whole("Ask", "?"),
                direct("DirectSend", "@", "!", &value, ")"),
                direct("DirectAsk", "#", "?", &value, ")"),
                terminal_rule("Unrelated", &result, "("),
            ];
            let families = quoted_bind_families(&language);
            prop_assert_eq!(families.len(), 2);
            let quote = families.iter().find(|family| family.prefix == "@").expect("quote family");
            let mark = families.iter().find(|family| family.prefix == "#").expect("mark family");
            prop_assert_eq!(&quote.binds, &std::collections::BTreeSet::from(["!".into()]));
            prop_assert_eq!(&quote.stops, &std::collections::BTreeSet::from(["?".into()]));
            prop_assert_eq!(&mark.binds, &std::collections::BTreeSet::from(["?".into()]));
            prop_assert_eq!(&mark.stops, &std::collections::BTreeSet::from(["!".into()]));
            prop_assert_eq!(&quote.rule_pairs, &std::collections::BTreeSet::from([("Send".into(), "Quote".into())]));
            prop_assert_eq!(&mark.rule_pairs, &std::collections::BTreeSet::from([("Ask".into(), "Mark".into())]));
            for family in &families {
                prop_assert_eq!(&family.result, &result);
                prop_assert_eq!(&family.source, &source);
            }
            let categories = vec![result.clone(), source.clone(), value.clone()];
            let arms = emit_at_quoted_bind_gate_trigger_arms(&language, &categories, &Default::default(), &Default::default(), &[]);
            prop_assert_eq!(arms.len(), 2);
            let mut partial = language.clone();
            let mut extra = whole("Uncovered", "!");
            extra.syntax_pattern.as_mut().expect("syntax").push(lit("tail"));
            partial.terms.push(extra);
            prop_assert!(quoted_bind_families(&partial).iter().all(|family| family.prefix != "@"));
            for bad in [
                direct("Bad", "@", "!", "Foreign", ")"),
                direct("Bad", "@", "!", &value, "}"),
                judgment_rule("Bad", &result, &[], vec![lit("@"), lit("empty"), lit("!"), lit("("), lit(")")]),
            ] {
                let mut invalid = language.clone();
                invalid.terms[4] = bad;
                prop_assert!(quoted_bind_families(&invalid).iter().all(|family| family.prefix != "@"));
            }
            let mut aliased = language.clone();
            let source_ident = Ident::new(&source, Span::call_site());
            aliased.terms[1].eval_mode = Some(mettail_ast::types::EvalMode::Fold);
            aliased.terms[1].rust_code = Some(mettail_ast::types::RustCodeBlock {
                code: syn::parse_quote! { #source_ident::Quote(std::sync::Arc::new(value.clone())) },
            });
            let alias_families = quoted_bind_families(&aliased);
            prop_assert_eq!(alias_families.len(), 2);
            for family in &alias_families {
                let expected = if family.prefix == "@" { ("Send".into(), "Quote".into()) } else { ("Ask".into(), "Mark".into()) };
                prop_assert_eq!(&family.rule_pairs, &std::collections::BTreeSet::from([expected]));
            }
            let mut unrelated_source = language.clone();
            unrelated_source.terms.push(judgment_rule("Special", &source, &[], vec![lit("@"), lit("special")]));
            prop_assert!(quoted_bind_families(&unrelated_source).iter().all(|family| family.prefix != "@"));
            let mut foreign = language.clone();
            foreign.terms[4].category = Ident::new("ForeignResult", Span::call_site());
            prop_assert!(quoted_bind_families(&foreign).iter().all(|family| family.prefix != "@"));
            let mut empty = language;
            empty.terms.clear();
            prop_assert!(quoted_bind_families(&empty).is_empty());
        }
    }

    fn emitted_lex_alt_tables(
        mut language: LanguageDef,
        categories: Vec<String>,
        per_cat: Vec<Vec<GrammarRule>>,
    ) -> String {
        language.terms = per_cat.iter().flatten().cloned().collect();
        let spine = super::super::factoring::build_spine_emission(&language, &categories, &per_cat);
        emit_lex_alt_rule_for_fn(&language, &per_cat, &categories, &spine).to_string()
    }

    fn lex_alt_surfaces(emitted: &str) -> (&str, &str) {
        emitted
            .split_once("fn lex_alt_rules_for_infix")
            .expect("generator must emit distinct prefix and infix lexical tables")
    }

    #[test]
    fn ident_certificate_follows_transparent_projection_and_source_extensions() {
        let categories = vec!["Proc".into(), "CostSig".into(), "Name".into()];
        let var_name = GrammarRule {
            items: vec![GrammarItem::NonTerminal {
                kind: mettail_ast::grammar::NonTerminalKind::Var,
                ident: Ident::new("Name", Span::call_site()),
            }],
            ..rule_fixture(
                Ident::new("NVar", Span::call_site()),
                Ident::new("Name", Span::call_site()),
            )
        };
        let ground = judgment_rule(
            "Ground",
            "CostSig",
            &[("name", "Name")],
            vec![SyntaxExpr::Param(Ident::new("name", Span::call_site()))],
        );
        let transfer = judgment_rule(
            "Transfer",
            "CostSig",
            &[("left", "CostSig"), ("right", "CostSig")],
            vec![
                SyntaxExpr::Param(Ident::new("left", Span::call_site())),
                SyntaxExpr::Literal("-o".into()),
                SyntaxExpr::Param(Ident::new("right", Span::call_site())),
            ],
        );
        let hash = judgment_rule(
            "Hash",
            "CostSig",
            &[("body", "Proc")],
            vec![
                SyntaxExpr::Literal("#".into()),
                SyntaxExpr::Param(Ident::new("body", Span::call_site())),
            ],
        );
        let per_cat = vec![vec![], vec![ground, transfer, hash], vec![var_name]];
        let language = empty_lang();
        assert_eq!(
            certified_ident_source_extensions(&language, &per_cat, &categories, 1),
            Some(vec!["-o".into()]),
        );

        // An identifier-starting fixed opener may have an Ident co-accept. Even though
        // its rule is syntactically fixed-led, that does not certify the
        // selected Ident edge as a one-token source atom.
        let mut contextual = per_cat.clone();
        contextual[1].push(judgment_rule(
            "KeywordBody",
            "CostSig",
            &[("body", "Proc")],
            vec![
                SyntaxExpr::Literal("hash".into()),
                SyntaxExpr::Param(Ident::new("body", Span::call_site())),
            ],
        ));
        assert_eq!(certified_ident_source_extensions(&language, &contextual, &categories, 1), None,);

        let mut compound_keyword = per_cat.clone();
        compound_keyword[1].push(judgment_rule(
            "CompoundKeywordBody",
            "CostSig",
            &[("body", "Proc")],
            vec![
                SyntaxExpr::Literal("hash!".into()),
                SyntaxExpr::Param(Ident::new("body", Span::call_site())),
            ],
        ));
        assert_eq!(
            certified_ident_source_extensions(&language, &compound_keyword, &categories, 1),
            None,
        );

        let mut keyword_atom = per_cat.clone();
        keyword_atom[1].push(terminal_rule("Keyword", "CostSig", "yes"));
        assert_eq!(
            certified_ident_source_extensions(&language, &keyword_atom, &categories, 1),
            None,
        );

        let mut uncertified = per_cat;
        uncertified[2].push(judgment_rule(
            "UnknownName",
            "Name",
            &[("inner", "Proc"), ("tail", "Name")],
            vec![
                SyntaxExpr::Param(Ident::new("inner", Span::call_site())),
                SyntaxExpr::Literal("?".into()),
                SyntaxExpr::Param(Ident::new("tail", Span::call_site())),
            ],
        ));
        assert_eq!(
            certified_ident_source_extensions(&language, &uncertified, &categories, 1),
            None,
        );
    }

    #[test]
    fn same_category_led_rule_exists_only_on_the_lex_alt_infix_surface() {
        let atom = terminal_rule("Atom", "Expr", "a");
        let parallel = judgment_rule(
            "Parallel",
            "Expr",
            &[("left", "Expr"), ("right", "Expr")],
            vec![
                SyntaxExpr::Param(Ident::new("left", Span::call_site())),
                SyntaxExpr::Literal("|".into()),
                SyntaxExpr::Param(Ident::new("right", Span::call_site())),
            ],
        );
        let emitted = emitted_lex_alt_tables(
            empty_lang(),
            vec!["Expr".to_string()],
            vec![vec![atom, parallel]],
        );

        let (prefix_surface, infix_surface) = lex_alt_surfaces(&emitted);

        assert_eq!(
            prefix_surface.matches("rule_idx : 1u16").count(),
            0,
            "same-category led rule leaked into prefix lexical dispatch: {prefix_surface}",
        );
        assert_eq!(
            infix_surface.matches("rule_idx : 1u16").count(),
            1,
            "same-category led rule must have one infix lexical entry: {infix_surface}",
        );
        assert!(infix_surface.contains("LexAltRuleKind :: InfixOp"), "{infix_surface}",);
    }

    #[test]
    fn cross_category_closed_rule_remains_on_the_lex_alt_prefix_surface() {
        let proc_atom = terminal_rule("ProcAtom", "Proc", "p");
        let send = judgment_rule(
            "Send",
            "Proc",
            &[("name", "Name"), ("body", "Proc")],
            vec![
                SyntaxExpr::Param(Ident::new("name", Span::call_site())),
                SyntaxExpr::Literal("!".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Param(Ident::new("body", Span::call_site())),
                SyntaxExpr::Literal(")".into()),
            ],
        );
        let name_atom = terminal_rule("NameAtom", "Name", "n");
        let emitted = emitted_lex_alt_tables(
            empty_lang(),
            vec!["Proc".to_string(), "Name".to_string()],
            vec![vec![proc_atom, send], vec![name_atom]],
        );

        let (prefix_surface, infix_surface) = lex_alt_surfaces(&emitted);

        assert!(
            prefix_surface.contains("rule_idx : 1u16"),
            "cross-category closed rule was lost from prefix lexical dispatch: {prefix_surface}",
        );
        assert!(
            prefix_surface.contains("LexAltRuleKind :: LeadingCategory"),
            "cross-category closed delegate was lost from prefix lexical dispatch: {prefix_surface}",
        );
        assert!(
            infix_surface.contains("rule_idx : 1u16"),
            "source-category led dispatch was accidentally removed: {infix_surface}",
        );
    }
}
