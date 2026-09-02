//! Phase A.3 (merged with A.4): Pratt rule shapes + cross-cat dispatch.
//!
//! Classifies rules from `language.terms` into infix / prefix / postfix /
//! mixfix shapes by inspecting the judgement-style `term_context` and
//! `syntax_pattern`. Builds `InfixRuleInfo` records, feeds them to
//! `prattail::binding_power::analyze_binding_powers`, and emits the
//! resulting `InfixOperator` entries into per-category static tables
//! consumed by the engine's `InfixLoop` state.
//!
//! Cross-category operators (e.g., Calculator's `EqInt: Int × Int → Bool`)
//! are handled in the same classification pass — the `is_cross_category`
//! flag on `InfixRuleInfo` drives Fork-based selection at runtime when a
//! token has multiple candidate result categories.

use mettail_ast::grammar::{GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
use mettail_prattail::binding_power::{
    analyze_binding_powers, Associativity, BindingPowerTable, InfixOperator, InfixRuleInfo,
    MixfixPart, MixfixRep,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// #131: the `operand_src_idx` a CAPTURE `MixfixPart` carries in the emitted
/// `mixfix_part` table.
///
/// A capture part consumes ONE token and yields no operand, so no category index
/// is honest for it. The alternative — resolving `"Ident"` through the category
/// list — silently produced `0`, the FIRST declared category, and the walker then
/// sub-parsed the wrong category with no diagnostic anywhere. This value is the
/// backstop that makes such a read detectable; the driver reads `capture_kind`
/// first and never reaches it.
///
/// Emitted verbatim as the generated `MIXFIX_PART_NO_OPERAND` so the codegen-time
/// and runtime notions cannot drift.
const MIXFIX_PART_NO_OPERAND: u16 = u16::MAX;

/// Build the BindingPowerTable for a language from its `terms` block.
pub(crate) fn build_bp_table(language: &LanguageDef) -> BindingPowerTable {
    let infix_rules = extract_infix_rules(language);
    analyze_binding_powers(&infix_rules)
}

/// Extract `InfixRuleInfo` entries from the language's rules. Covers
/// binary infix (old + judgement-style), unary-postfix, and mixfix.
/// Unary prefix rules are classified separately in `prefix.rs`.
///
/// Plan 3 (ambient cluster, 2026-05-10): clones each rule and runs
/// `convert_items_to_term_context` on the clone before classification
/// so BNF-style rules (e.g., ambient.rs's `PAmb . Proc ::= Name "[" Proc "]"`)
/// get classified as judgement-style. The conversion is a no-op for rules
/// that already have `term_context` + `syntax_pattern` set.
pub(crate) fn extract_infix_rules(language: &LanguageDef) -> Vec<InfixRuleInfo> {
    let mut rules = Vec::new();
    for rule in &language.terms {
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        if let Some(info) = classify_rule(&normalized) {
            rules.push(info);
        }
    }
    rules
}

/// Classify a single `GrammarRule` as infix / postfix / mixfix or None
/// (everything else: atomics, binders, cross-cat projections, etc.).
fn classify_rule(rule: &GrammarRule) -> Option<InfixRuleInfo> {
    if let (Some(tc), Some(sp)) = (&rule.term_context, &rule.syntax_pattern) {
        return classify_judgement(rule, tc, sp);
    }
    None
}

/// Public re-export of `classify_rule` for use in `semantic_actions.rs`.
///
/// Plan 3 (ambient cluster, 2026-05-10): clones the rule and runs
/// `convert_items_to_term_context` so BNF-style rules are normalized
/// before classification. No-op for judgement-style rules.
pub(crate) fn classify_rule_public(rule: &GrammarRule) -> Option<InfixRuleInfo> {
    let mut normalized = rule.clone();
    mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
    classify_rule(&normalized)
}

fn classify_judgement(
    rule: &GrammarRule,
    term_context: &[TermParam],
    syntax_pattern: &[SyntaxExpr],
) -> Option<InfixRuleInfo> {
    // Filter to Simple params only — binder / guard / multi-abstraction
    // rules are Phase A.5 / A.6 / A.8.
    let simples: Vec<(&syn::Ident, &TypeExpr)> = term_context
        .iter()
        .filter_map(|p| match p {
            TermParam::Simple { name, ty } => Some((name, ty)),
            _ => None,
        })
        .collect();
    if simples.len() != term_context.len() {
        return None;
    }

    let result_cat = rule.category.to_string();

    // Binary infix: 2 Simple params, pattern = [Param, Literal, Param].
    if simples.len() == 2 && syntax_pattern.len() == 3 {
        if let (SyntaxExpr::Param(p1), SyntaxExpr::Literal(op), SyntaxExpr::Param(p2)) =
            (&syntax_pattern[0], &syntax_pattern[1], &syntax_pattern[2])
        {
            let (n1, t1) = simples[0];
            let (n2, t2) = simples[1];
            if n1 == p1 && n2 == p2 {
                let t1_str = base_type_name(t1)?;
                let t2_str = base_type_name(t2)?;
                // GEN-1 GAP-1 (2026-06-28): only the HOMOGENEOUS-operand binary
                // (t1 == t2) is a plain binary infix. For HETEROGENEOUS operands
                // (t1 ≠ t2) we MUST NOT `return None` from the whole classifier —
                // that silently dropped `A op B → C` (A ≠ B), losing its table
                // entry, its lex-alt arm, AND its `cat_can_reach` edge (the
                // goal-gate then becomes non-conservative). Instead we fall
                // through to `classify_postfix_mixfix` below (reached at
                // `simples.len() >= 1 && syntax_pattern.len() >= 3`), which treats
                // `[Param, Literal, Param]` as an LHS (cross-cat source = t1) plus
                // ONE goal-bounded inner operand (t2) — emitted as a mixfix with
                // `category = t1`, `result_category = C`. This restores the
                // `t1 → C` LHS edge for heterogeneous casts (`e:Expr "as" t:Type
                // |- :R`, `x satisfies T`, `x is T`). Audit §GAP-1.
                if t1_str == t2_str {
                    let is_cross_category = t1_str != result_cat;
                    return Some(InfixRuleInfo {
                        label: rule.label.to_string(),
                        terminal: op.clone(),
                        category: t1_str,
                        result_category: result_cat,
                        associativity: if rule.is_right_assoc {
                            Associativity::Right
                        } else {
                            Associativity::Left
                        },
                        shares_level_with_previous: rule.shares_level_with_previous,
                        is_cross_category,
                        is_postfix: false,
                        is_mixfix: false,
                        mixfix_parts: Vec::new(),
                        nullary_literals: Vec::new(),
                    });
                }
                // t1 ≠ t2: fall through to classify_postfix_mixfix (no return).
            }
        }
    }

    // Unary postfix: 1 Simple param, pattern = [Param, Literal].
    if simples.len() == 1 && syntax_pattern.len() == 2 {
        if let (SyntaxExpr::Param(p1), SyntaxExpr::Literal(op)) =
            (&syntax_pattern[0], &syntax_pattern[1])
        {
            let (n1, t1) = simples[0];
            if n1 == p1 {
                let t1_str = base_type_name(t1)?;
                let is_cross_category = t1_str != result_cat;
                return Some(InfixRuleInfo {
                    label: rule.label.to_string(),
                    terminal: op.clone(),
                    category: t1_str,
                    result_category: result_cat,
                    // A postfix operator has no right operand, so it has no
                    // associativity to declare; `analyze_binding_powers` lays every
                    // postfix operator out in a separate pass ABOVE the whole infix
                    // range, where neither this field nor `shares_level_with_previous`
                    // is read.
                    associativity: Associativity::Left,
                    shares_level_with_previous: false,
                    is_cross_category,
                    is_postfix: true,
                    is_mixfix: false,
                    mixfix_parts: Vec::new(),
                    nullary_literals: Vec::new(),
                });
            }
        }
    }

    // Mixfix: 3+ Simple params with alternating [Param, Lit, Param, ...].
    if simples.len() >= 3 {
        if let Some(info) = classify_mixfix(rule, &simples, syntax_pattern) {
            return Some(info);
        }
    }

    // L12 follow-up B6 step 3 (2026-05-07) — Class 1 MIXFIX-LHS-PARAM:
    // classify_postfix_mixfix is now ACTIVE in the dispatch chain. The
    // walker-side `WpdaState::MixfixLiteralRun` (added in this same
    // commit) walks the postfix-mixfix per-part literal sequences via
    // per-iteration ConsumeAndReplace.
    //
    // GEN-1 B-1 (Stage S2): gate relaxed `simples >= 2` → `simples >= 1` so a
    // 0-operand ("nullary") Param-prefixed rule — only LHS, then literals
    // (POutputEmpty `n "!" "(" ")"`, zero-arg methods `.size()`) — reaches
    // the classifier and is emitted as a nullary mixfix (arity-1 LHS-only).
    if simples.len() >= 1 && syntax_pattern.len() >= 3 {
        if let Some(info) = classify_postfix_mixfix(rule, &simples, syntax_pattern) {
            return Some(info);
        }
    }

    None
}

/// L12 follow-up B6 step 2 (2026-05-07) — Class 1 classifier.
///
/// Recognizes Param-prefixed multi-element rules with possibly-consecutive
/// literals between operands. The first Param is the LHS (cross-cat-source);
/// the first Literal is the trigger; subsequent Literals are absorbed into
/// preceding_terminals (before the next operand) or following_terminals
/// (after the most-recent operand).
///
/// Returns InfixRuleInfo with `is_mixfix: true` so downstream dispatch
/// (mixfix_bp_<cat> table, Unwinding-MixfixMarker arm, MixfixContinuation
/// state) handles the rule via the existing mixfix machinery — the widened
/// MixfixPart::preceding_terminals/following_terminals (B6 step 1) carry
/// the multi-literal sequences.
fn classify_postfix_mixfix(
    rule: &GrammarRule,
    simples: &[(&syn::Ident, &TypeExpr)],
    syntax_pattern: &[SyntaxExpr],
) -> Option<InfixRuleInfo> {
    // GEN-1 B-1 (Stage S2): gate relaxed `< 2` → `< 1`. A 1-Simple rule whose
    // only param is the LHS, followed by trigger + literals with NO inner
    // operand, is a NULLARY mixfix (POutputEmpty `n "!" "(" ")"`, zero-arg
    // methods `.size()`); it is emitted with empty `mixfix_parts` and the
    // post-trigger literals in `nullary_literals`.
    if simples.len() < 1 || syntax_pattern.len() < 3 {
        return None;
    }
    // Position 0 must be the LHS Param.
    let SyntaxExpr::Param(lhs_name) = &syntax_pattern[0] else {
        return None;
    };
    let (lhs_simple_name, lhs_ty) = simples[0];
    if lhs_simple_name != lhs_name {
        return None;
    }
    let lhs_cat = base_type_name(lhs_ty)?;
    let result_cat = rule.category.to_string();
    let is_cross_category = lhs_cat != result_cat;

    // Trigger: must be a Literal immediately after LHS.
    let trigger = match syntax_pattern.get(1) {
        Some(SyntaxExpr::Literal(t)) => t.clone(),
        _ => return None,
    };

    // Walk the remaining pattern, accumulating preceding_terminals before
    // each new operand and following_terminals after the most-recent one.
    let mut preceding_buffer: Vec<String> = Vec::new();
    let mut parts: Vec<MixfixPart> = Vec::new();
    let mut simple_idx: usize = 1; // simples[0] is the LHS already consumed.
    let mut idx: usize = 2;
    while idx < syntax_pattern.len() {
        match &syntax_pattern[idx] {
            SyntaxExpr::Literal(t) => {
                match parts.last_mut() {
                    // GEN-1 B-3 (Stage S2/S3): a literal AFTER a `*sep`
                    // repetition part belongs to that repetition's CLOSE (the
                    // per-element loop owns the terminator), NOT to
                    // following_terminals — see `MixfixRep::close`.
                    Some(last) if last.repetition.is_some() => {
                        last.repetition
                            .as_mut()
                            .expect("repetition is_some in this arm")
                            .close
                            .push(t.clone());
                    },
                    // After the most-recent (non-rep) operand — append to its
                    // following_terminals.
                    Some(last) => last.following_terminals.push(t.clone()),
                    // Before any inner operand — accumulate as preceding for
                    // the next operand (or, if no operand ever appears, as the
                    // nullary literal run).
                    None => preceding_buffer.push(t.clone()),
                }
                idx += 1;
            },
            SyntaxExpr::Param(p) => {
                let (sname, sty) = simples.get(simple_idx)?;
                if sname != &p {
                    return None;
                }
                let scat = base_type_name(sty)?;
                parts.push(MixfixPart {
                    operand_category: scat,
                    param_name: p.to_string(),
                    preceding_terminals: std::mem::take(&mut preceding_buffer),
                    following_terminals: Vec::new(),
                    repetition: None,
                    // #131: an `m:Ident` param in an OPERAND-LEADING rule is a TOKEN
                    // CAPTURE, not a category operand. Rholang's collapsed method
                    // surface — `recv "." m "(" args.*sep(",") ")"` — is exactly this
                    // shape, and it is the whole reason the field exists.
                    //
                    // Before this, `base_type_name` yielded `"Ident"`, which is not a
                    // declared category, and the walker sub-parsed a category that does
                    // not exist: the rule had NO realizable reading and `# . f ( )`
                    // failed at every arity with a diagnostic that never mentioned
                    // `Ident`. See `MixfixPart::capture_kind` for why this is a field
                    // and not a variant, and why the kind is carried by name.
                    capture_kind: capture_kind_of(sty),
                });
                simple_idx += 1;
                idx += 1;
            },
            // GEN-1 B-3 C3 (Stage S2): `xs.*sep(s)` — a repetition operand.
            // The `*sep` consumes exactly one Simple param (`xs:Vec(elem)`);
            // push a repetition MixfixPart carrying the element category and
            // the separator. The CLOSE is filled by subsequent literals (see
            // the Literal arm above). Until the S3 walker handling lands, the
            // rep part is INERT: `mixfix_part(..)` returns None for it
            // (`emit_mixfix_parts_fn` skips rep parts) while
            // `mixfix_parts_len` still counts it, so a parse that reaches the
            // rep slot cleanly Errors (the fork dies, NO mis-parse).
            SyntaxExpr::Op(PatternOp::Sep { collection, separator, .. }) => {
                // GEN-1 B-3 stage gate (Stage S3): classify the repetition operand
                // into a `MixfixRep` part UNLESS the rule's RESULT category is
                // excluded (the ForRow `&`-join — the root-caused S2 regression).
                // Returning `None` here leaves the whole rule unclassified, exactly
                // as at baseline. See [`gen1_rep_classify_enabled`].
                if !gen1_rep_classify_enabled(&result_cat) {
                    return None;
                }
                let (sname, sty) = simples.get(simple_idx)?;
                // The `*sep` collection name must be the next Simple param.
                if sname != &collection {
                    return None;
                }
                // Element category = the inner type of the `Vec(elem)` /
                // `HashBag(elem)` / … collection param.
                let elem_cat = match sty {
                    TypeExpr::Collection { element, .. } => base_type_name(element)?,
                    _ => return None,
                };
                parts.push(MixfixPart {
                    operand_category: elem_cat,
                    param_name: collection.to_string(),
                    preceding_terminals: std::mem::take(&mut preceding_buffer),
                    following_terminals: Vec::new(),
                    repetition: Some(MixfixRep {
                        separator: separator.clone(),
                        min: 0,
                        close: Vec::new(),
                    }),
                    // #131: a repetition accumulates CATEGORY operands, so it is never
                    // also a token capture. The two modes are orthogonal and both
                    // appear in `Call` — on DIFFERENT parts.
                    capture_kind: None,
                });
                simple_idx += 1;
                idx += 1;
            },
            _ => return None,
        }
    }
    // All simples must be consumed.
    if simple_idx != simples.len() {
        return None;
    }

    // GEN-1 B-1 (Stage S2): NULLARY path. No inner operand was parsed but the
    // pattern had post-trigger literals (now in `preceding_buffer`). Emit a
    // 0-operand mixfix: empty `mixfix_parts`, literals in `nullary_literals`.
    // The walker's `(2, None) if parts_len == 0` arm consumes them and fires
    // the arity-1 (LHS-only) action.
    if parts.is_empty() {
        if preceding_buffer.is_empty() {
            // Degenerate: LHS + trigger only (a plain postfix `a op`), which is
            // the 2-token postfix path's job (syntax_pattern.len() == 2 there);
            // here syntax_pattern.len() >= 3 with no operand and no literals is
            // impossible, but reject defensively.
            return None;
        }
        return Some(InfixRuleInfo {
            label: rule.label.to_string(),
            terminal: trigger,
            category: lhs_cat,
            result_category: result_cat,
            // A NULLARY mixfix (`n "!" "(" ")"`) has no operand after the trigger, so it
            // has no right edge for a chain to nest into and associativity is not
            // observable in its surface. See `classify_mixfix` for the shape where it is.
            associativity: Associativity::Left,
            shares_level_with_previous: rule.shares_level_with_previous,
            is_cross_category,
            is_postfix: false,
            is_mixfix: true,
            mixfix_parts: Vec::new(),
            nullary_literals: preceding_buffer,
        });
    }

    // preceding_buffer should be empty at end (literals after the last operand
    // were routed into its following_terminals or — for a rep — its close).
    if !preceding_buffer.is_empty() {
        return None;
    }

    Some(InfixRuleInfo {
        label: rule.label.to_string(),
        terminal: trigger,
        category: lhs_cat,
        result_category: result_cat,
        // A postfix-mixfix (`n "!" "(" q ")"`) closes with a literal, so its final
        // operand is delimited and the rule has no open right edge — associativity is
        // not observable. `classify_mixfix` handles the shape where it is.
        associativity: Associativity::Left,
        shares_level_with_previous: rule.shares_level_with_previous,
        is_cross_category,
        is_postfix: false,
        // Treated as mixfix for downstream dispatch — the widened
        // MixfixPart vectors carry the postfix-mixfix-specific terminal
        // sequences.
        is_mixfix: true,
        mixfix_parts: parts,
        nullary_literals: Vec::new(),
    })
}

fn classify_mixfix(
    rule: &GrammarRule,
    simples: &[(&syn::Ident, &TypeExpr)],
    syntax_pattern: &[SyntaxExpr],
) -> Option<InfixRuleInfo> {
    if syntax_pattern.len() != 2 * simples.len() - 1 {
        return None;
    }
    let mut parts = Vec::new();
    let mut trigger: Option<String> = None;
    for (i, expr) in syntax_pattern.iter().enumerate() {
        if i % 2 == 0 {
            match expr {
                SyntaxExpr::Param(p) => {
                    let param_idx = i / 2;
                    let (pname, pty) = simples.get(param_idx)?;
                    if *pname != p {
                        return None;
                    }
                    if param_idx > 0 {
                        // #131: an `Ident` param here is a TOKEN CAPTURE, carried by
                        // `MixfixPart::capture_kind` and consumed one token at a time by
                        // the walker's mixfix part driver.
                        //
                        // ⚠ THE GUARD THAT USED TO STAND HERE IS GONE ON PURPOSE. It
                        // panicked at macro-expansion time because `MixfixPart` had no
                        // representation for a token consumption, so `base_type_name`
                        // yielded the non-category `"Ident"` and the walker sub-parsed a
                        // category that does not exist — the rule had no realizable
                        // reading at all. Making that LOUD was right while the shape was
                        // unsupported; keeping it once the shape IS supported would
                        // reject exactly the grammars the field was added to serve
                        // (Rholang's collapsed `EMethodCall`). `capture_kind_of` replaces
                        // the rejection with the representation.
                        let cat = base_type_name(pty)?;
                        // L12 follow-up B6 (2026-05-07): widened from
                        // `following_terminal: Option<String>` to vectors.
                        // For traditional mixfix the per-part separator
                        // appears as a single-element following_terminals
                        // vec; preceding_terminals stays empty (the trigger
                        // OR the previous part's following_terminals
                        // already consumed the literals before this operand).
                        let following = if i + 1 < syntax_pattern.len() {
                            if let SyntaxExpr::Literal(t) = &syntax_pattern[i + 1] {
                                vec![t.clone()]
                            } else {
                                return None;
                            }
                        } else {
                            Vec::new()
                        };
                        parts.push(MixfixPart {
                            operand_category: cat,
                            param_name: p.to_string(),
                            preceding_terminals: Vec::new(),
                            following_terminals: following,
                            repetition: None,
                            // #131: the classic-mixfix twin of the postfix-mixfix site.
                            // Both classifiers reach `capture_kind_of` so a rule's
                            // reading does not depend on WHICH classifier claimed it —
                            // the very asymmetry that made `Tagged` (literal-leading,
                            // binder path) green while `Call` (operand-leading, Pratt
                            // path) had no realizable reading at all.
                            capture_kind: capture_kind_of(pty),
                        });
                    }
                },
                // GEN-1 B-3 (Stage S2): a `*sep` repetition operand at an even
                // (operand) position makes this rule defer to
                // `classify_postfix_mixfix`, which owns the repetition-part
                // construction (single canonical path). Returning None here lets
                // the caller fall through to that classifier.
                _ => return None,
            }
        } else {
            match expr {
                SyntaxExpr::Literal(t) => {
                    if i == 1 {
                        trigger = Some(t.clone());
                    }
                },
                _ => return None,
            }
        }
    }
    let trigger = trigger?;
    let (_, lhs_ty) = simples[0];
    let lhs_cat = base_type_name(lhs_ty)?;
    let result_cat = rule.category.to_string();
    let is_cross_category = lhs_cat != result_cat;

    // ★ MIXFIX ASSOCIATIVITY (2026-07-28) — this used to be a hard-coded
    // `Associativity::Left`, which silently DROPPED a declared `right` on every mixfix
    // rule. `Tern` (`c "?" t ":" e … step right` in Calculator) is exactly such a rule,
    // and `macros/src/gen/syntax/display.rs` honours the declaration, so the printer and
    // this table disagreed about what the same grammar meant.
    //
    // Associativity is a property of the rule's RIGHT EDGE — it decides how a chain of
    // the operator nests, which is only observable when the FINAL operand is open on the
    // right. It is derived here rather than assumed: a mixfix whose last part is followed
    // by a literal (`n "!" "(" q ")"`) is self-delimiting, and `right` on such a rule has
    // no chain to re-nest. The ternary's last part (`e`) has no following terminal, so it
    // does, and `1 ? 2 : 0 ? 3 : 4` reads `1 ? 2 : (0 ? 3 : 4)`.
    let has_open_right_edge = parts
        .last()
        .is_some_and(|part| part.following_terminals.is_empty());

    Some(InfixRuleInfo {
        label: rule.label.to_string(),
        terminal: trigger,
        category: lhs_cat,
        result_category: result_cat,
        associativity: if rule.is_right_assoc && has_open_right_edge {
            Associativity::Right
        } else {
            Associativity::Left
        },
        shares_level_with_previous: rule.shares_level_with_previous,
        is_cross_category,
        is_postfix: false,
        is_mixfix: true,
        mixfix_parts: parts,
        nullary_literals: Vec::new(),
    })
}

fn base_type_name(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Base(ident) => Some(ident.to_string()),
        _ => None,
    }
}

/// #131: the TOKEN KIND a mixfix part must consume, or `None` if the part is an
/// ordinary category operand.
///
/// This is the SINGLE decision point that turns a declared param type into
/// [`MixfixPart::capture_kind`]. It answers exactly one question — "does this
/// param consume a token instead of naming a category?" — and it answers it from
/// [`TypeExpr::is_ident_text`], the same predicate the binder path uses to route
/// `m:Ident` to `BinderPosition::IdentTextCapture`. Both paths therefore agree on
/// what an identifier param IS, which is what lets the LITERAL-leading rule
/// (`Tagged . m:Ident |- "tag" m`) and the OPERAND-leading rule
/// (`Call . recv:Num, m:Ident, … |- recv "." m …`) deliver the same `String` field
/// through two different machines.
///
/// The returned name is resolved at parse time by the walker's `capture_kind`,
/// which maps `"Ident"` to the builtin `TokenKind::Ident` the lexer actually
/// emits (commit `ac46362b`) — NOT to `TokenKind::Custom("Ident")`, which no lexer
/// ever produces and which would leave the gate permanently dead.
fn capture_kind_of(ty: &TypeExpr) -> Option<String> {
    match ty.is_ident_text() {
        true => {
            // ⚠ The name is spelled ONCE, here, and the assertion below is what stops it
            // from drifting away from the classifier that decided we are on this branch.
            // A silent drift would emit `capture_kind: Some("…")` for a kind the walker's
            // `capture_kind` resolves to `TokenKind::Custom("…")`, which no lexer emits —
            // reproducing the exact dead gate `ac46362b` root-caused and fixed.
            debug_assert_eq!(
                mettail_ast::grammar::NonTerminalKind::classify(IDENT_CAPTURE_KIND_NAME),
                mettail_ast::grammar::NonTerminalKind::Ident,
                "IDENT_CAPTURE_KIND_NAME must be the name `NonTerminalKind::classify` \
                 maps to `Ident`",
            );
            Some(IDENT_CAPTURE_KIND_NAME.to_string())
        },
        false => None,
    }
}

/// The token-kind name a builtin-`Ident` mixfix capture demands. See
/// [`capture_kind_of`] for why it is spelled exactly once.
const IDENT_CAPTURE_KIND_NAME: &str = "Ident";

/// Emit per-category static BP tables consumed by the `InfixLoop` engine
/// state. Tables are indexed by terminal text at runtime via the emitted
/// lookup helpers.
///
/// The lookup returns `(left_bp, right_bp, result_src_idx, rule_idx)` so
/// the engine can emit the correct InfixContinuation Return symbol with
/// the rule_idx pointing at the operator's arity-2 action.
pub(crate) fn emit_bp_tables(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
) -> TokenStream {
    let bp_table = build_bp_table(language);
    // Lookup: rule label → (cat_src_idx, rule_idx) for resolving result
    // categories and rule indices in the BP-table emission.
    let label_to_indices = build_label_index(categories, per_cat);
    // C1 S0: per-category literal-injection rule index (`NumLit` for Int).
    // The synth_atom_symbol primitive needs each operand category's literal
    // rule to build atom leaves. `generate_literal_label(native_type)` names
    // the synthetic rule; resolve its local rule_idx via the label index.
    let cat_lit_rule_idx: std::collections::HashMap<String, u16> = language
        .types
        .iter()
        .filter_map(|td| {
            let cat_name = td.name.to_string();
            let nt = td.native_type.as_ref()?;
            let lit_label = crate::gen::generate_literal_label(nt).to_string();
            let (_, ri) = label_to_indices.get(&(cat_name.clone(), lit_label))?;
            Some((cat_name, *ri))
        })
        .collect();
    // C1 D1: per-category value-home rank source — `true` if the category
    // parses its literal operand via a tier-0.0 polymorphic home prefix arm
    // (integer kinds incl. `CanonicalBigInt`), else `false`. This is the
    // lex-min PRIMARY key the canonical-op winner selection mirrors: a
    // bare-integer chain converges on the integer-home category (Int) even
    // when a non-integer-home category (e.g. BigRat) has a lower
    // `category_src_idx` but reaches a bare integer only via a cross-cat
    // projection (tier >= BP_TIER_CROSSCAT_PROJECTION = 0.025).
    let cat_is_value_home: std::collections::HashMap<String, bool> = language
        .types
        .iter()
        .map(|td| {
            let is_home = td
                .native_type
                .as_ref()
                .map(|nt| crate::gen::native::NativeType::from_syn_type(nt).is_integer())
                .unwrap_or(false);
            (td.name.to_string(), is_home)
        })
        .collect();
    // GEN-1 B-2 (Stage S0): one shared (cat,terminal) grouping consumed by all
    // three per-tier slice emitters below AND by `emit_infix_lex_alt_rule_arms`
    // (kind_dispatch.rs) ⇒ the slice and lex-alt rule multisets are identical per
    // (cat,terminal) by construction (NO-LOSS).
    let grouped = group_ops_by_cat_terminal(&bp_table, categories, &label_to_indices);
    let mut per_cat_tables = Vec::new();
    for (cat_i, cat) in categories.iter().enumerate() {
        let cat_src_idx = cat_i as u16;
        let cat_lower = cat.to_lowercase();
        let infix_ident = format_ident!("infix_bp_{}", cat_lower);
        let postfix_ident = format_ident!("postfix_bp_{}", cat_lower);
        let mixfix_ident = format_ident!("mixfix_bp_{}", cat_lower);
        // Phase F.13 chain_10000 Exp 6 Substage 6b (2026-05-26): per-cat
        // iter-eligible lookup. Returns `Some((left_bp, right_bp))` when
        // the (rs, ri) tuple refers to an iterative-eligible operator
        // AND no other operator in the same category shares the same
        // (terminal, left_bp) pair (Plan A invariant I1 — singleton
        // InfixLoop dispatch).
        let iter_ident = format_ident!("iter_eligible_{}", cat_lower);
        per_cat_tables.push(emit_infix_bp_fn(&grouped, cat_src_idx, &infix_ident));
        per_cat_tables.push(emit_postfix_bp_fn(&grouped, cat_src_idx, &postfix_ident));
        per_cat_tables.push(emit_mixfix_bp_fn(&grouped, cat_src_idx, &mixfix_ident));
        per_cat_tables.push(emit_iter_eligible_fn(
            &bp_table,
            cat,
            &iter_ident,
            &label_to_indices,
            categories,
            &cat_lit_rule_idx,
            &cat_is_value_home,
        ));
    }
    // B7 Pattern 1: per-rule mixfix-parts metadata. Used by the engine's
    // Unwinding-MixfixMarker / MixfixContinuation arms to look up each
    // inner operand's category and the separator that follows it. Keyed
    // on (result_src_idx, rule_idx, part_idx).
    per_cat_tables.push(emit_mixfix_parts_fn(
        &bp_table,
        categories,
        &label_to_indices,
        per_cat,
        language,
    ));
    quote! { #(#per_cat_tables)* }
}

/// Build a map from rule.label → (cat_src_idx, rule_idx). Used to look up
/// the pair for an operator's `result_category` + `label`.
/// F5-2 (2026-07-13): `pub(crate)` so `factoring::discover_mixfix_cohorts`
/// reads the SAME (cat,terminal) grouping the slice emitters consume.
pub(crate) fn build_label_index(
    categories: &[String],
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
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

/// GEN-1 compile-time kill-switch (B-2 slice migration, Stage S0).
///
/// Each per-tier binding-power lookup (`infix_bp_<cat>` / `postfix_bp_<cat>` /
/// `mixfix_bp_<cat>`) returns a `&'static [..]` slice of EVERY rule that shares a
/// `(category, terminal)` trigger, in canonical `rule_idx` order.
/// `GEN1_MAX_SLICE` truncates every emitted slice to its first `GEN1_MAX_SLICE`
/// element(s) at macro-expansion time.
///
/// At `cap = 1` the slice holds only the canonical-order-first (rule_idx-min)
/// element — exactly the operator the pre-S0 `Option`-returning lookups returned
/// via Rust's first-arm-wins `match` — so the slice dispatch is BYTE-IDENTICAL to
/// the legacy single-winner dispatch. Raising the cap (S1+) admits the remaining
/// trigger-sharing rules as fork candidates with NO further plumbing change;
/// reverting GEN-1 is a one-line flip back to `1`.
///
/// Stage S1 (2026-06-28): UNCAPPED to `usize::MAX` so multi-element slices FORK.
/// The only pre-C3 multi-element slices are the 24 `.`-method mixfix rules (they
/// share the `.` trigger in `mixfix_bp_proc`); they now fork 24-way and each
/// non-matching branch dies in ONE step at its method-name literal-run
/// (`__checked_literal_consume!` → 0-edge `Error`), so methods still roundtrip.
/// Revert = flip back to `1`.
pub(crate) const GEN1_MAX_SLICE: usize = usize::MAX;

/// GEN-1 B-3 repetition-classification stage gate (Stage S3, 2026-06-28).
///
/// Per-RESULT-category compile-time gate (consistent with the [`GEN1_MAX_SLICE`]
/// kill-switch pattern: a `const` resolved at macro expansion, NOT a runtime env
/// var) selecting which `xs.*sep(s)` repetition operands — in Param-prefixed
/// rules routed through [`classify_postfix_mixfix`] — are classified into a
/// [`MixfixRep`] part and driven by the B-3 walker. A rule whose RESULT category
/// appears here keeps the pre-S3 behavior: its `*sep` operand is NOT classified
/// (the `Op(Sep)` arm returns `None`), so the rule stays unclassified EXACTLY as
/// at baseline — regression-free.
///
/// EXCLUDED — `ForRow`. The InputBind→ForRow cross-cat `&`-join repetition rules
/// (`ForRowWhere` / `ForRowNoWhere` / `ForRowPersistentWhere` /
/// `ForRowPersistentNoWhere` — all `… "&" bs.*sep("&") …`, result category
/// `ForRow`, LHS category InputBind or Name) REGRESS 6 pattern-COMM / quoted-bind
/// tests when classified — EVEN with the repetition INERT. The breakage is
/// PRESENCE-based: registering them as `&`- (or `<=`-) triggered mixfix operators
/// on the InputBind / Name tiers removes the valid derivation of
/// quoted-collection pattern binds `for(@[..]/@#{..}# <- c){…}` (cursors reach the
/// body but no branch accepts at EOF). Root-caused by the S2 bisect: enabling rep
/// classification GLOBALLY gave 6 regressions — `comm::pattern_comm_{bag,list}_`
/// `literal_pattern_{matches,blocks_mismatch}`,
/// `comm::join_pattern_mismatch_is_noop_for_receive_group`,
/// `parsing::quoted_plain_bind_parses` — while gating `ForRow` OUT removes all 6
/// AND classifies the safe set cleanly (POutput2Plus / PPersistOutput2Plus →
/// `Proc`; InputBind query / polyadic binds → `InputBind`). See
/// `scratchpad/s1-s3-gate.log`.
///
/// This is a STAGE BOUNDARY, not a permanent exclusion: a separate ForRow fix
/// (co-designing the `&`-join classification + dispatch so it does not disturb the
/// InputBind→ForRow projection) lands the join, at which point `ForRow` is removed
/// from this list. Full B-3 revert = add every rep-bearing result category
/// (`"Proc"`, `"InputBind"`, `"ForRow"`) here, or restore the pre-S3 snapshot.
///
/// F1 (2026-06-28): `ForRow` REMOVED — the `&`-join rules (`ForRowWhere` /
/// `ForRowNoWhere` / `ForRowPersistentWhere` / `ForRowPersistentNoWhere`) now
/// classify. The 6 pattern-COMM / quoted-bind regressions that this caused at S2
/// are now prevented by the F0 cross-cat-LHS PUSH-gate (forks.rs +
/// `prefix_crosscat_lhs_trigger_ahead_scoped` + `crosscat_lhs_has_projection_fallback`,
/// kind_dispatch.rs): a triggerless quoted-collection bind (`for(@[..]<-c){…}`)
/// has the `InputBind→ForRow` projection fallback (`ForRowSingleNoWhere`), so its
/// EXTENSION delegate is suppressed and it parses projection-only — exactly the
/// pre-S2 derivation. The classified `&`-rep itself stays INERT until the §4.5
/// no-close repetition walker (F2) lands; until then an `&`-join parses its first
/// bind, forks on `&`, and cleanly Errors at the rep slot (no mis-parse).
const GEN1_REP_CLASSIFY_EXCLUDED_CATEGORIES: &[&str] = &[];

/// Compile-time per-result-category gate for GEN-1 B-3 repetition classification
/// (see [`GEN1_REP_CLASSIFY_EXCLUDED_CATEGORIES`]). Returns `true` when a `*sep`
/// repetition operand in a rule producing `result_category` may be classified
/// into a [`MixfixRep`] part.
fn gen1_rep_classify_enabled(result_category: &str) -> bool {
    !GEN1_REP_CLASSIFY_EXCLUDED_CATEGORIES.contains(&result_category)
}

/// One operator resolved to its global packing coordinates, retaining a borrow of
/// the source [`InfixOperator`] for its tier flags and binding powers. Produced by
/// [`group_ops_by_cat_terminal`].
pub(crate) struct GroupedOp<'a> {
    /// The source operator (tier flags `is_postfix` / `is_mixfix`, `left_bp`,
    /// `right_bp`, `terminal`, ...).
    pub(crate) op: &'a InfixOperator,
    /// Result-category source index (the packing's category).
    pub(crate) result_src_idx: u16,
    /// Local rule index within the result category.
    pub(crate) rule_idx: u16,
}

/// B-2 (Stage S0) NO-LOSS foundation: group EVERY operator by
/// `(operand cat_src_idx, terminal)`, preserving the canonical
/// `bp_table.operators` order within each group (category-alphabetical ×
/// infix/mixfix-then-postfix, each in declaration order — see
/// `analyze_binding_powers`).
///
/// This single grouping feeds BOTH the per-tier slice emitters
/// (`emit_{infix,postfix,mixfix}_bp_fn`) AND the lattice lex-alt emitter
/// (`emit_infix_lex_alt_rule_arms`, `kind_dispatch.rs`), so the per-(cat,terminal)
/// rule multiset is IDENTICAL across the two dispatch surfaces by construction —
/// the GEN-1 NO-LOSS invariant. Operators whose operand category or
/// `(result_category, label)` packing coordinates cannot be resolved are skipped
/// (matching the legacy emitters' defensive `filter_map` / `continue`).
pub(crate) fn group_ops_by_cat_terminal<'a>(
    bp_table: &'a BindingPowerTable,
    categories: &[String],
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
) -> std::collections::BTreeMap<(u16, String), Vec<GroupedOp<'a>>> {
    let mut grouped: std::collections::BTreeMap<(u16, String), Vec<GroupedOp<'a>>> =
        std::collections::BTreeMap::new();
    for op in &bp_table.operators {
        let Some(cat_src_idx) = categories
            .iter()
            .position(|cat| cat == &op.category)
            .map(|idx| idx as u16)
        else {
            continue;
        };
        let Some(&(result_src_idx, rule_idx)) =
            label_index.get(&(op.result_category.clone(), op.label.clone()))
        else {
            continue;
        };
        grouped
            .entry((cat_src_idx, op.terminal.clone()))
            .or_default()
            .push(GroupedOp { op, result_src_idx, rule_idx });
    }
    grouped
}

/// Emit `infix_bp_<cat>(terminal) -> &'static [(l_bp, r_bp, result_src, rule_idx)]`.
///
/// GEN-1 B-2 (Stage S0): returns a slice of every infix rule sharing the terminal
/// in this category, truncated to [`GEN1_MAX_SLICE`] (1 at S0 ⇒ the legacy
/// single-winner / first-arm-wins element). The four-tuple KEEPS `r_bp` — the
/// cross-cat / right-assoc sub-parse floor — unlike the postfix/mixfix tiers.
fn emit_infix_bp_fn(
    grouped: &std::collections::BTreeMap<(u16, String), Vec<GroupedOp>>,
    cat_src_idx: u16,
    fn_ident: &proc_macro2::Ident,
) -> TokenStream {
    let arms = grouped
        .iter()
        .filter(|((c, _t), _ops)| *c == cat_src_idx)
        .filter_map(|((_c, terminal), ops)| {
            let tuples: Vec<TokenStream> = ops
                .iter()
                .filter(|g| !g.op.is_postfix && !g.op.is_mixfix)
                .take(GEN1_MAX_SLICE)
                .map(|g| {
                    let l = g.op.left_bp;
                    let r = g.op.right_bp;
                    let result_src_idx = g.result_src_idx;
                    let rule_idx = g.rule_idx;
                    quote! { (#l, #r, #result_src_idx, #rule_idx) }
                })
                .collect();
            if tuples.is_empty() {
                return None;
            }
            Some(quote! {
                #terminal => &[ #(#tuples),* ],
            })
        });
    quote! {
        /// Binding-power lookup for infix operators in this category. Returns a
        /// slice of `(left_bp, right_bp, result_src_idx, rule_idx)` for every
        /// infix rule sharing the terminal (GEN-1 B-2; capped to `GEN1_MAX_SLICE`
        /// at codegen — 1 at Stage S0 ⇒ legacy single-winner).
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(terminal: &str) -> &'static [(u8, u8, u16, u16)] {
            match terminal {
                #(#arms)*
                _ => &[],
            }
        }
    }
}

/// Phase F.13 chain_10000 Exp 6 Substage 6b (2026-05-26): emit
/// `iter_eligible_<cat>(rs, ri) -> Option<(u8, u8)>` returning
/// `Some((left_bp, right_bp))` when (rs, ri) refers to an
/// iterative-eligible operator AND no other operator in the same
/// category shares the same `(terminal, left_bp)` pair (Plan A
/// invariant I1 — singleton InfixLoop dispatch). The codegen-time
/// uniqueness check is required because `InfixOperator::is_iterative_candidate`
/// can only inspect a single operator at a time; the I1 invariant
/// requires a per-category scan.
///
/// At codegen time, the eligibility stays category-local: every same-category
/// iterative operator that is unique within its category may be summarized in
/// that category. Cross-category ambiguity is preserved as distinct WPDA
/// alternatives; the absorber only changes the representation of an
/// individual category-local derivation.
fn emit_iter_eligible_fn(
    bp_table: &BindingPowerTable,
    category: &str,
    fn_ident: &proc_macro2::Ident,
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
    categories: &[String],
    cat_lit_rule_idx: &std::collections::HashMap<String, u16>,
    cat_is_value_home: &std::collections::HashMap<String, bool>,
) -> TokenStream {
    let _ = (categories, cat_is_value_home);
    let cat_ops: Vec<&InfixOperator> = bp_table
        .operators
        .iter()
        .filter(|op| op.category == category)
        .collect();
    // GEN-1 B-2 (Stage S0) §2.4 — codegen DISJOINTNESS ASSERT.
    //
    // The InfixLoop pre-fork absorption blocks (engine_impl.rs) read the
    // iterative-eligible op via `#dispatch.first()` over the per-tier BP slice.
    // For that `.first()` to remain SOUND once `GEN1_MAX_SLICE` is uncapped
    // (S1+) — i.e. for the iter-eligible op to be the UNIQUE candidate at its
    // terminal so truncation can never drop it in favor of a competing rule —
    // every iter-eligible op in this category MUST be the only op in the
    // category bearing its terminal. This STRENGTHENS the (terminal, left_bp)
    // uniqueness (I1, below) to plain terminal uniqueness. A breach is a
    // grammar-level GEN-1 precondition violation ⇒ hard `compile_error!`.
    // Vacuous when no op in the category is iterative-eligible (e.g. rholang).
    let disjointness_errors: Vec<TokenStream> = cat_ops
        .iter()
        .enumerate()
        .filter(|(_, op)| op.is_iterative_candidate())
        .filter_map(|(i, op)| {
            let clash = cat_ops
                .iter()
                .enumerate()
                .find(|(j, other)| *j != i && other.terminal == op.terminal)
                .map(|(_, other)| other)?;
            let msg = format!(
                "GEN-1 B-2 disjointness violation: iterative-eligible operator \
                 `{}` (terminal `{}`) in category `{}` shares its terminal with \
                 operator `{}`. The InfixLoop pre-fork `.first()` absorption \
                 requires each iter-eligible op to own its terminal uniquely \
                 within its category.",
                op.label, op.terminal, category, clash.label,
            );
            Some(quote! { compile_error!(#msg); })
        })
        .collect();
    let arms: Vec<TokenStream> = cat_ops
        .iter()
        .filter(|op| op.is_iterative_candidate())
        .filter_map(|op| {
            // I1 (within-category): no other operator in this category shares
            // the same (terminal, left_bp) pair, so the singleton InfixLoop
            // dispatch is unambiguous.
            let conflict = cat_ops.iter().any(|other| {
                !std::ptr::eq(*other as *const _, *op as *const _)
                    && other.terminal == op.terminal
                    && other.left_bp == op.left_bp
            });
            if conflict {
                return None;
            }
            let (rs, ri) = *label_index.get(&(op.result_category.clone(), op.label.clone()))?;
            let l = op.left_bp;
            let r = op.right_bp;
            let assoc_right = op.left_bp > op.right_bp;
            let is_mixfix = op.is_mixfix;
            // For an iter-candidate (`!is_cross_category`) the operand
            // category equals the result category, so atom_cat_src_idx == rs.
            let atom_cat_src_idx = rs;
            let atom_lit_rule_idx = *cat_lit_rule_idx.get(&op.result_category)?;
            // Mixfix trigger + inner separator terminals (empty for binary).
            let (trigger, sep): (String, String) = if op.is_mixfix {
                let sep = op
                    .mixfix_parts
                    .first()
                    .and_then(|p| p.following_terminals.first().cloned())
                    .unwrap_or_default();
                (op.terminal.clone(), sep)
            } else {
                (String::new(), String::new())
            };
            let trigger_lit = proc_macro2::Literal::string(&trigger);
            let sep_lit = proc_macro2::Literal::string(&sep);
            Some(quote! {
                (#rs, #ri) => Some(mettail_prattail::binding_power::IterAbsorbSpec {
                    left_bp: #l,
                    right_bp: #r,
                    assoc_right: #assoc_right,
                    is_mixfix: #is_mixfix,
                    op_cat_src_idx: #rs,
                    op_rule_idx: #ri,
                    atom_cat_src_idx: #atom_cat_src_idx,
                    atom_lit_rule_idx: #atom_lit_rule_idx,
                    trigger: #trigger_lit,
                    sep: #sep_lit,
                }),
            })
        })
        .collect();
    quote! {
        // GEN-1 B-2 (Stage S0) §2.4: terminal-disjointness breaches (if any)
        // surface here as `compile_error!`. Empty ⇒ no tokens ⇒ byte-identical.
        #(#disjointness_errors)*
        /// C1: iterative-eligible operator lookup. Returns the canonical
        /// `IterAbsorbSpec` for `(rs, ri)` — present iff this op is THE
        /// canonical absorber for its terminal (cross-category D1 filter) and
        /// has no within-category (terminal, l_bp) conflict (I1). The walker's
        /// H3 absorption + the InfixLoop pre-fork trigger consume the spec.
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(rs: u16, ri: u16) -> Option<mettail_prattail::binding_power::IterAbsorbSpec> {
            match (rs, ri) {
                #(#arms)*
                _ => None,
            }
        }
    }
}

/// Emit `postfix_bp_<cat>(terminal) -> &'static [(l_bp, result_src, rule_idx)]`.
/// GEN-1 B-2 (Stage S0): slice of every postfix rule sharing the terminal,
/// truncated to [`GEN1_MAX_SLICE`] (1 at S0 ⇒ legacy single-winner).
fn emit_postfix_bp_fn(
    grouped: &std::collections::BTreeMap<(u16, String), Vec<GroupedOp>>,
    cat_src_idx: u16,
    fn_ident: &proc_macro2::Ident,
) -> TokenStream {
    let arms = grouped
        .iter()
        .filter(|((c, _t), _ops)| *c == cat_src_idx)
        .filter_map(|((_c, terminal), ops)| {
            let tuples: Vec<TokenStream> = ops
                .iter()
                .filter(|g| g.op.is_postfix)
                .take(GEN1_MAX_SLICE)
                .map(|g| {
                    let l = g.op.left_bp;
                    let result_src_idx = g.result_src_idx;
                    let rule_idx = g.rule_idx;
                    quote! { (#l, #result_src_idx, #rule_idx) }
                })
                .collect();
            if tuples.is_empty() {
                return None;
            }
            Some(quote! {
                #terminal => &[ #(#tuples),* ],
            })
        });
    quote! {
        /// Binding-power lookup for postfix operators in this category. Returns a
        /// slice of `(left_bp, result_src_idx, rule_idx)` (GEN-1 B-2; capped to
        /// `GEN1_MAX_SLICE` at codegen — 1 at Stage S0 ⇒ legacy single-winner).
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(terminal: &str) -> &'static [(u8, u16, u16)] {
            match terminal {
                #(#arms)*
                _ => &[],
            }
        }
    }
}

/// B7 Pattern 1: emit a per-category mixfix BP lookup, returning
/// `(left_bp, result_src_idx, rule_idx)` for any mixfix trigger keyword
/// whose left operand is in this category. The InfixLoop dispatch
/// queries this AFTER infix and postfix lookups; on hit, it consumes the
/// trigger token and pushes a MixfixMarker with `bp=0` (zero operands
/// completed so far).
fn emit_mixfix_bp_fn(
    grouped: &std::collections::BTreeMap<(u16, String), Vec<GroupedOp>>,
    cat_src_idx: u16,
    fn_ident: &proc_macro2::Ident,
) -> TokenStream {
    let arms = grouped
        .iter()
        .filter(|((c, _t), _ops)| *c == cat_src_idx)
        .filter_map(|((_c, terminal), ops)| {
            let tuples: Vec<TokenStream> = ops
                .iter()
                .filter(|g| g.op.is_mixfix)
                .take(GEN1_MAX_SLICE)
                .map(|g| {
                    let l = g.op.left_bp;
                    let result_src_idx = g.result_src_idx;
                    let rule_idx = g.rule_idx;
                    quote! { (#l, #result_src_idx, #rule_idx) }
                })
                .collect();
            if tuples.is_empty() {
                return None;
            }
            Some(quote! {
                #terminal => &[ #(#tuples),* ],
            })
        });
    quote! {
        /// Binding-power lookup for mixfix operators in this category. Returns a
        /// slice of `(left_bp, result_src_idx, rule_idx)` (GEN-1 B-2; capped to
        /// `GEN1_MAX_SLICE` at codegen — 1 at Stage S0 ⇒ legacy single-winner).
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(terminal: &str) -> &'static [(u8, u16, u16)] {
            match terminal {
                #(#arms)*
                _ => &[],
            }
        }
    }
}

/// B7 Pattern 1 + L12 follow-up B6 (2026-05-07): emit per-rule
/// mixfix-parts metadata. Returns
/// `mixfix_part(result_src_idx, rule_idx, part_idx) ->
///   Option<(operand_src_idx, preceding: &'static [&'static str],
///           following: &'static [&'static str])>`.
///
/// `preceding` is the literal sequence consumed BEFORE the operand
/// sub-parse (used for postfix-mixfix shapes like POutput's `(`
/// between trigger and inner operand). `following` is the literal
/// sequence consumed AFTER the operand sub-parse (used for trailing
/// brackets and per-part separators). Pre-B6 this was a single
/// `Option<&'static str>` for `following_terminal` only — widened to
/// vectors so postfix-mixfix patterns with consecutive literals are
/// expressible.
///
/// `mixfix_parts_len(result_src_idx, rule_idx) -> Option<u8>` returns
/// the number of inner operands so the engine knows when to stop.
fn emit_mixfix_parts_fn(
    bp_table: &BindingPowerTable,
    categories: &[String],
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
    language: &LanguageDef,
) -> TokenStream {
    let mut part_arms = Vec::new();
    let mut len_arms = Vec::new();
    let mut nullary_arms = Vec::new();
    // GEN-1 B-3 (Stage S3): per-rep-part metadata arms (one per `*sep` part).
    let mut rep_arms = Vec::new();
    for op in bp_table.operators.iter().filter(|op| op.is_mixfix) {
        let Some(&(result_src_idx, rule_idx)) =
            label_index.get(&(op.result_category.clone(), op.label.clone()))
        else {
            continue;
        };
        // ★ #141 G3 — the refusals below name the rule by its LABEL and point at
        // it. `label_index` is built by `build_label_index` from the very
        // `per_cat` this function is handed, and its value is exactly the
        // `(cat_i, rule_i)` pair that indexes it, so this cannot miss.
        let rule_label = op.label.clone();
        let rule_span = per_cat
            .get(result_src_idx as usize)
            .and_then(|rules| rules.get(rule_idx as usize))
            .map(|rule| rule.label.span())
            .unwrap_or_else(proc_macro2::Span::call_site);
        // `mixfix_parts_len` counts EVERY part, including a `*sep` repetition
        // part. The repetition part's per-part `mixfix_part(..)` arm is SKIPPED
        // below (Stage S2 ⇒ it returns None ⇒ the walker errors cleanly at the
        // rep slot until the Stage S3 repetition handling lands). Counting it
        // keeps `completed_idx + 1 == parts_len` accurate for the surrounding
        // mixfix literal-run accounting.
        let parts_len = op.mixfix_parts.len() as u8;
        len_arms.push(quote! {
            (#result_src_idx, #rule_idx) => Some(#parts_len),
        });
        // GEN-1 B-1 (Stage S2): nullary (0-operand) mixfix literal run.
        if !op.nullary_literals.is_empty() {
            let lits: Vec<TokenStream> =
                op.nullary_literals.iter().map(|t| quote! { #t }).collect();
            nullary_arms.push(quote! {
                (#result_src_idx, #rule_idx) => Some(&[ #( #lits ),* ][..]),
            });
        }
        for (part_idx, part) in op.mixfix_parts.iter().enumerate() {
            // GEN-1 B-3 (Stage S3): a `*sep` repetition part emits NO `mixfix_part`
            // arm (so `mixfix_part(..)` returns None for it) but DOES emit a
            // `mixfix_rep` arm carrying its
            // `(element_src, preceding, separator, close, min)`.
            // The walker's MixfixLiteralRun arms detect the rep slot via
            // `mixfix_rep(..).is_some()` and hand it off to the CollectionLoop;
            // `mixfix_parts_len` still counts it (accounting stays accurate).
            if let Some(rep) = &part.repetition {
                let rep_part_idx = part_idx as u8;
                // ★ #141 G3, AN EIGHTH SIBLING — not on the brief's list of seven,
                // found by reading the enclosing function rather than the list. This
                // `.unwrap_or(0)` is the SAME fails-open shape as the operand lookup
                // twenty lines below, in the same emitter, on the same
                // `part.operand_category` field: an unresolvable element category
                // became index 0, the FIRST declared category, and the emitted
                // `mixfix_rep` row told the CollectionLoop to sub-parse it. Token
                // position, so it takes the shared resolver.
                let elem_src_idx = super::binder::cat_idx_tokens(
                    &part.operand_category,
                    categories,
                    "a mixfix `*sep` repetition's element position",
                    &rule_label,
                    rule_span,
                );
                let separator = &rep.separator;
                let preceding_lits: Vec<TokenStream> = part
                    .preceding_terminals
                    .iter()
                    .map(|t| quote! { #t })
                    .collect();
                let close_lits: Vec<TokenStream> =
                    rep.close.iter().map(|t| quote! { #t }).collect();
                let min = rep.min;
                rep_arms.push(quote! {
                    (#result_src_idx, #rule_idx, #rep_part_idx) => Some((
                        #elem_src_idx,
                        &[ #( #preceding_lits ),* ][..],
                        #separator,
                        &[ #( #close_lits ),* ][..],
                        #min,
                    )),
                });
                continue;
            }
            let part_idx = part_idx as u8;
            // #131: a CAPTURE part consumes one token and yields NO operand, so it must
            // not occupy an operand slot. `MIXFIX_PART_NO_OPERAND` is emitted in the
            // `operand_src_idx` position precisely so a consumer that ignores
            // `capture_kind` and reads the index anyway cannot silently sub-parse
            // category 0 — the failure it would otherwise produce is the one this whole
            // task root-caused. The driver matches on the capture kind BEFORE the index
            // is ever read; the poison is the backstop, not the mechanism.
            let capture_kind_ts: TokenStream = match &part.capture_kind {
                Some(k) => quote! { Some(#k) },
                None => quote! { None },
            };
            // ⚠ SIBLING OF THE #131 ROOT, HARDENED. This is the same fails-open shape as
            // `semantic_actions.rs`'s `lookup_cat_idx(..).unwrap_or(0)`, which resolved
            // the unknown category `Ident` to index 0 — the FIRST declared category — and
            // made an action advertise "slot N expects a `Num` term" while its extractor
            // read identifier text. Here the consequence would be a mixfix part that
            // SUB-PARSES THE WRONG CATEGORY: silently wrong, never a diagnostic.
            //
            // A CAPTURE part legitimately names a non-category (`Ident`), so it takes the
            // poison instead of the lookup. Every OTHER part must resolve.
            //
            // ★ #141 G3 — TWO FIXES AT ONE SITE.
            //
            // (1) The refusal was a `panic!`. Under this workspace's cranelift dev
            //     backend a `panic!` inside a proc macro prints NOTHING: rustc dies with
            //     `fatal runtime error: Rust cannot catch foreign exceptions` and the
            //     payload never appears (#141 RED-0, 2026-07-29). So the message below
            //     could not be read even when it fired. It is now a spanned
            //     `compile_error!` — a TOKEN, rendered by rustc, which the backend
            //     cannot swallow.
            //
            // (2) The message said "mixfix part `{}` of rule `{}`" and passed
            //     `rule_idx`, AN INTEGER. Even had it printed, `rule 7` names nothing a
            //     grammar author can act on: `rule_idx` is a position within
            //     `per_cat[result_src_idx]`, an artefact of codegen ordering. It now
            //     names the rule by LABEL and points the diagnostic at that label's
            //     span, which is what `UnresolvedCategory` exists to make uniform.
            //
            // A capture row is emitted with the poison spelled by NAME rather than as
            // the bare literal `65535u16`, so the generated table says what it means at
            // the one place a reader would otherwise have to guess:
            //   `(0u16, 1u16, 0u8) => Some((MIXFIX_PART_NO_OPERAND, &[][..], &["("][..],
            //                              Some("Ident")))`
            let operand_src_idx: TokenStream = match part.capture_kind.is_some() {
                true => quote! { MIXFIX_PART_NO_OPERAND },
                false => super::binder::cat_idx_tokens(
                    &part.operand_category,
                    categories,
                    "a mixfix operand position",
                    &rule_label,
                    rule_span,
                ),
            };
            let preceding_lits: Vec<TokenStream> = part
                .preceding_terminals
                .iter()
                .map(|t| quote! { #t })
                .collect();
            let following_lits: Vec<TokenStream> = part
                .following_terminals
                .iter()
                .map(|t| quote! { #t })
                .collect();
            part_arms.push(quote! {
                (#result_src_idx, #rule_idx, #part_idx) => Some((
                    #operand_src_idx,
                    &[ #( #preceding_lits ),* ][..],
                    &[ #( #following_lits ),* ][..],
                    #capture_kind_ts,
                )),
            });
        }
    }
    // GAP-3 (2026-06-28): 0-operand MULTI-literal keyword-PREFIX rules
    // (`Map ()`, `Pathmap ()`, `@ Nil`) are NOT in `bp_table.operators` (they
    // have no binding power and are never `is_mixfix`), so the loop above never
    // sees them. They REUSE the same `MixfixLiteralRun { kind: 2, parts_len ==
    // 0 }` runtime arm as B-1, entered from the PREFIX site (prefix.rs) instead
    // of the InfixLoop. Emit their metadata here:
    //   - `mixfix_parts_len(cat, rule) == Some(0)` selects the nullary arm
    //     (distinct from a suppressed `*sep` rep slot, which has parts_len >= 1);
    //   - `mixfix_nullary_literals(cat, rule)` carries the POST-trigger literals
    //     the arm consumes (membership-checked) before popping the marker.
    // The (cat_i, rule_i) coordinates from `per_cat` enumeration MATCH the
    // prefix dispatch's (category_src_idx, rule_idx) exactly (both derive from
    // the same `build_per_category_rules` result — see engine_impl per_cat_indexed
    // and mod.rs). No dup-arm risk: these rules are never `is_mixfix`, so their
    // (result, rule) keys cannot collide with the loop above.
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let result_src_idx = cat_i as u16;
        for (rule_i, rule) in rules.iter().enumerate() {
            if let super::prefix::AtomicShape::NullaryLiteralRun { trailing_literals, .. } =
                super::prefix::classify_atomic(rule, language)
            {
                let rule_idx = rule_i as u16;
                len_arms.push(quote! {
                    (#result_src_idx, #rule_idx) => Some(0u8),
                });
                let lits: Vec<TokenStream> =
                    trailing_literals.iter().map(|t| quote! { #t }).collect();
                nullary_arms.push(quote! {
                    (#result_src_idx, #rule_idx) => Some(&[ #( #lits ),* ][..]),
                });
            }
        }
    }
    // S1-FACTORING F5-2 (2026-07-13): mixfix SPINE `parts_len` PRESENCE rows,
    // `Some(u8::MAX)` poison. The Unwinding-MixfixMarker arm validates
    // `Some(..)` then DISCARDS the value (engine_impl `let _ = parts_len`),
    // so a spine-marked operand return re-enters
    // `MixfixLiteralRun { kind: 0 }` — which the spliced spine prelude
    // intercepts BEFORE the generic reads. An escaped spine id at any OTHER
    // `parts_len` consumer dies loudly on the poison. Rows come from the
    // const-gated partition (`mixfix_emission_partition` — deterministic, so
    // this agrees with the `build_spine_emission` bundle without threading);
    // EMPTY while `S1_FACTORING && S1F5_MIXFIX_COHORTS` is off
    // (byte-identity).
    for (spine_result_src, spine_id) in
        super::factoring::mixfix_spine_parts_len_rows(language, categories, per_cat)
    {
        len_arms.push(quote! {
            (#spine_result_src, #spine_id) => Some(u8::MAX),
        });
    }
    let no_operand_lit = MIXFIX_PART_NO_OPERAND;
    quote! {
        /// Mixfix per-part metadata: returns
        /// `(operand_src_idx, preceding_terminals, following_terminals, capture_kind)`.
        /// L12 follow-up B6 (2026-05-07): widened to vector terminals
        /// for postfix-mixfix support.
        ///
        /// #131 (2026-07-28): the 4th element is the TOKEN CAPTURE kind. `Some(k)`
        /// means "consume ONE token of kind `k`", NOT "sub-parse the category `k`";
        /// `None` is an ordinary category operand. A capture part yields no operand,
        /// so its `operand_src_idx` is the poison `MIXFIX_PART_NO_OPERAND` — reading
        /// it as a category index is a bug, and the poison makes that bug loud
        /// instead of letting it sub-parse category 0.
        #[allow(non_snake_case, dead_code)]
        fn mixfix_part(
            result_src_idx: u16,
            rule_idx: u16,
            part_idx: u8,
        ) -> Option<(
            u16,
            &'static [&'static str],
            &'static [&'static str],
            Option<&'static str>,
        )> {
            match (result_src_idx, rule_idx, part_idx) {
                #(#part_arms)*
                _ => None,
            }
        }

        /// #131: the `operand_src_idx` a CAPTURE part carries. A capture consumes a
        /// token and produces no operand, so there is no honest category index to
        /// put here; this value exists so that reading one is detectable rather than
        /// silently equal to the first declared category.
        #[allow(dead_code)]
        const MIXFIX_PART_NO_OPERAND: u16 = #no_operand_lit;

        /// Mixfix parts count: returns the number of inner operands for
        /// the (result_src, rule_idx) mixfix rule. Counts a `*sep` repetition
        /// part even though its per-part metadata is suppressed (B-3 S2).
        #[allow(non_snake_case, dead_code)]
        fn mixfix_parts_len(result_src_idx: u16, rule_idx: u16) -> Option<u8> {
            match (result_src_idx, rule_idx) {
                #(#len_arms)*
                _ => None,
            }
        }

        /// GEN-1 B-1 (Stage S2): post-trigger literal run for a 0-operand
        /// (nullary) mixfix rule (POutputEmpty `n "!" "(" ")"` ⇒ `["(", ")"]`,
        /// zero-arg methods `.size()` ⇒ `["size", "(", ")"]`). The walker's
        /// `(2, None) if parts_len == 0` arm consumes these literals then pops
        /// the marker and fires the arity-1 (LHS-only) action. `None` for every
        /// operand-bearing mixfix rule (`mixfix_parts_len(..) != Some(0)`).
        #[allow(non_snake_case, dead_code)]
        fn mixfix_nullary_literals(
            result_src_idx: u16,
            rule_idx: u16,
        ) -> Option<&'static [&'static str]> {
            match (result_src_idx, rule_idx) {
                #(#nullary_arms)*
                _ => None,
            }
        }

        /// GEN-1 B-3 (Stage S3): repetition-part metadata. For a `*sep`
        /// repetition `MixfixPart` (e.g. POutput2Plus's `bs.*sep(",")`), returns
        /// `(element_src_idx, preceding_terminals, separator, close_terminals,
        /// min)`; `None` for an ordinary single-operand part and for every
        /// non-rep rule. The walker's
        /// `MixfixLiteralRun` arms use `mixfix_rep(rs, ri, part_idx).is_some()` to
        /// detect a repetition slot and hand it off to the `CollectionLoop`
        /// (replace the marker → push a `CollectionMarker` for `part_idx` →
        /// `PrefixDispatch`). The close/sep/element_src are ALSO carried by the
        /// per-slot `collection_spec(rs, ri, part_idx)` record (the CollectionLoop
        /// reads those); `mixfix_rep` is the codegen-time presence signal + the
        /// documented descriptor.
        #[allow(non_snake_case, dead_code)]
        fn mixfix_rep(
            result_src_idx: u16,
            rule_idx: u16,
            part_idx: u8,
        ) -> Option<(
            u16,
            &'static [&'static str],
            &'static str,
            &'static [&'static str],
            u8,
        )> {
            match (result_src_idx, rule_idx, part_idx) {
                #(#rep_arms)*
                _ => None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{rule_fixture, GrammarRule};
    use mettail_ast::types::TypeExpr;
    use proc_macro2::Span;
    use syn::Ident;

    fn simple(name: &str, ty: &str) -> TermParam {
        TermParam::Simple {
            name: Ident::new(name, Span::call_site()),
            ty: TypeExpr::Base(Ident::new(ty, Span::call_site())),
        }
    }

    fn param(name: &str) -> SyntaxExpr {
        SyntaxExpr::Param(Ident::new(name, Span::call_site()))
    }

    fn lit(s: &str) -> SyntaxExpr {
        SyntaxExpr::Literal(s.to_string())
    }

    fn infix_rule(label: &str, cat: &str, operand: &str, op: &str) -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![simple("a", operand), simple("b", operand)]),
            syntax_pattern: Some(vec![param("a"), lit(op), param("b")]),
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    fn postfix_rule(label: &str, cat: &str, operand: &str, op: &str) -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![simple("a", operand)]),
            syntax_pattern: Some(vec![param("a"), lit(op)]),
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    #[test]
    fn classifies_binary_infix_same_cat() {
        let rule = infix_rule("AddInt", "Int", "Int", "+");
        let info = classify_rule(&rule).expect("infix");
        assert_eq!(info.label, "AddInt");
        assert_eq!(info.terminal, "+");
        assert_eq!(info.category, "Int");
        assert_eq!(info.result_category, "Int");
        assert!(!info.is_cross_category);
        assert!(!info.is_postfix);
    }

    #[test]
    fn classifies_cross_cat_infix() {
        let rule = infix_rule("EqInt", "Bool", "Int", "==");
        let info = classify_rule(&rule).expect("cross-cat infix");
        assert_eq!(info.category, "Int");
        assert_eq!(info.result_category, "Bool");
        assert!(info.is_cross_category);
    }

    #[test]
    fn classifies_postfix() {
        let rule = postfix_rule("Fact", "Int", "Int", "!");
        let info = classify_rule(&rule).expect("postfix");
        assert!(info.is_postfix);
        assert_eq!(info.terminal, "!");
    }

    /// GEN-1 GAP-1 (2026-06-28): a HETEROGENEOUS-operand binary
    /// (`a:Int "+" b:Float`) is no longer DROPPED. It falls through from the
    /// binary-infix arm to `classify_postfix_mixfix` and is emitted as a mixfix
    /// whose LHS category is the FIRST operand (`Int`, the cross-cat source)
    /// with the second operand (`Float`) as a goal-bounded inner mixfix part.
    /// Previously `classify_rule` returned `None`, silently losing the rule's BP
    /// table entry, its lex-alt arm, AND its `cat_can_reach` edge — making the
    /// goal-gate non-conservative for heterogeneous casts (`e:Expr "as" t:Type`,
    /// `x satisfies T`). Audit §GAP-1; replaces the prior
    /// `rejects_mixed_operand_types` test that asserted the dropped behavior.
    #[test]
    fn heterogeneous_operand_binary_classifies_as_mixfix() {
        let mut rule = infix_rule("Mix", "Int", "Int", "+");
        rule.term_context = Some(vec![simple("a", "Int"), simple("b", "Float")]);
        let info = classify_rule(&rule).expect("heterogeneous binary now classifies (GAP-1)");
        assert_eq!(info.category, "Int", "LHS (first operand) is the cross-cat source category");
        assert_eq!(info.result_category, "Int");
        assert!(info.is_mixfix, "heterogeneous binary is emitted as a mixfix");
        assert!(
            info.mixfix_parts
                .iter()
                .any(|p| p.operand_category == "Float"),
            "the second (heterogeneous) operand becomes a goal-bounded inner mixfix part",
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // #141 G3 RED — the mixfix operand refusal SPEAKS, and names the RULE
    // ═══════════════════════════════════════════════════════════════════════
    //
    // Two defects at one site. (1) The refusal was a `panic!`, which prints
    // NOTHING inside a proc macro under this workspace's cranelift dev backend
    // (#141 RED-0) — so the message could not be read even when it fired. (2) The
    // message read "mixfix part `{}` of rule `{}`" and passed `rule_idx`, AN
    // INTEGER: even had it printed, `rule 0` names nothing a grammar author can
    // act on.
    //
    // ⚠ Neither cell expects a panic; both read the emitted tokens.

    /// A one-rule language whose heterogeneous binary `a:Int "+" b:<operand>`
    /// classifies as a mixfix, so the emitter resolves `<operand>`.
    fn mixfix_language(operand: &str) -> (LanguageDef, Vec<String>, Vec<Vec<GrammarRule>>) {
        let mut rule = infix_rule("Mix", "Int", "Int", "+");
        rule.term_context = Some(vec![simple("a", "Int"), simple("b", operand)]);
        let mut language = crate::gen::empty_language_for_tests();
        language.types.push(mettail_ast::language::LangType {
            name: Ident::new("Int", Span::call_site()),
            role: Default::default(),
            native_type: None,
            collection_kind: None,
        });
        language.terms.push(rule.clone());
        (language, vec!["Int".to_string()], vec![vec![rule]])
    }

    /// ★ THE MUTATION CELL. A mixfix operand naming an UNDECLARED category emits a
    /// `compile_error!` that names the category AND the rule's LABEL.
    #[test]
    fn an_undeclared_mixfix_operand_refuses_and_names_the_rule_label() {
        let (language, categories, per_cat) = mixfix_language("Ghost");
        let (control_language, _, _) = mixfix_language("Int");

        // The mutation is applied, and is the only difference.
        assert_ne!(
            format!("{:?}", language.terms[0].term_context),
            format!("{:?}", control_language.terms[0].term_context),
            "the two fixtures differ in exactly the OPERAND CATEGORY, which is what \
             this emitter resolves",
        );

        let rendered = emit_bp_tables(&language, &categories, &per_cat).to_string();

        assert!(
            rendered.contains("compile_error"),
            "an undeclared mixfix operand must REFUSE as a token rustc renders, not as \
             a panic the backend swallows. Got: {rendered}",
        );
        assert!(
            rendered.contains("Ghost"),
            "the diagnostic must name the CATEGORY it could not resolve. Got: {rendered}",
        );
        assert!(
            rendered.contains("`Mix`"),
            "★ and it must name the RULE BY LABEL. The message it replaces claimed to \
             name the rule and passed `rule_idx`, an integer — a position within \
             `per_cat[cat]`, which is an artefact of codegen ordering and names nothing \
             a grammar author can act on. Got: {rendered}",
        );
        assert!(
            rendered.contains("mixfix operand position"),
            "…and it must say WHERE, since one rule can name a category in several \
             positions. Got: {rendered}",
        );
    }

    /// ★ THE CONTROL that must NOT discriminate: a DECLARED operand still emits
    /// its table, with no diagnostic at all.
    #[test]
    fn a_declared_mixfix_operand_still_emits_its_table() {
        let (language, categories, per_cat) = mixfix_language("Int");
        let rendered = emit_bp_tables(&language, &categories, &per_cat).to_string();
        assert!(
            !rendered.contains("compile_error"),
            "an operand category the language declares must not be refused — otherwise \
             the cell above proves only that this emitter refuses everything. Got: \
             {rendered}",
        );
        assert!(
            rendered.contains("mixfix_part"),
            "and the mixfix part table must still be emitted. Got: {rendered}",
        );
    }
}
