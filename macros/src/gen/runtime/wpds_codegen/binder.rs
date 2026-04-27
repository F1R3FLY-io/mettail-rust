//! Phase 5: Binder + multi-step rule codegen.
//!
//! Detects judgement-style rules with one or more of: literal terminals,
//! parameter sub-parses, single-binder ident slot, multi-binder list,
//! body parse, guard slot. Emits a multi-step state machine that walks
//! the rule's `syntax_pattern`, capturing args along the way, firing the
//! rule's action when the marker pops.
//!
//! Supported rule shapes:
//! - **Single-binder** (Phase 5a, e.g. Lambda's `Lam`): `^x.body:[T -> T]`
//!   with syntax `"trigger" x "." body`.
//! - **Multi-Param non-binder** (Phase 5b, e.g. Calculator's `Fraction`):
//!   `a:T, b:T |- "trigger" "(" a "," b ")"`. The rule has multiple
//!   `Simple` params and no binder.
//! - **Multi-binder list** (Phase 5b, e.g. RhoCalc's `PNew`):
//!   `^[xs].p:[T* -> T]` with syntax containing a `Sep` operator over
//!   the binder list.
//! - **Mixed** (Phase 5b, e.g. PInputs): combines `Simple` params,
//!   collection-as-`Op(Sep)`, and binder via `MultiAbstraction`.
//! - **Guard slot** (Phase 6, e.g. PGuardedInput): includes a
//!   `?guard:Guard` parameter parsed via `parse_predicate_from_tokens`.

use mettail_ast::grammar::{GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::types::TypeExpr;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

/// Classification of a multi-step rule.
#[derive(Debug, Clone)]
pub struct BinderShape {
    /// Constructor label (e.g., `"Lam"`, `"Fraction"`, `"PNew"`).
    #[allow(dead_code)]
    pub label: String,
    /// Result category name (e.g., `"Term"`, `"BigRat"`, `"Proc"`).
    #[allow(dead_code)]
    pub result_cat: String,
    /// Per-position dispatch entries (excluding position 0 which is the
    /// trigger consumed at PrefixDispatch open arm).
    pub positions: Vec<BinderPosition>,
    /// Whether the rule uses a multi-binder list (^[xs]).
    pub is_multi: bool,
    /// Whether the rule has any binder slot at all (for action body shape).
    pub has_binder: bool,
    /// Action arity (number of args the action consumes).
    pub action_arity: u8,
    /// Action body: per-arg, what kind of arg it is (Ident binder name,
    /// Term sub-parse, Predicate, BinderListNames). Used to construct the
    /// Cat::Label(...) expression.
    pub action_args: Vec<ActionArgKind>,
    /// Body category (for single-binder rules — None for non-binder).
    #[allow(dead_code)]
    pub body_cat: Option<String>,
    /// Param categories in declaration order (for non-binder Simple params).
    #[allow(dead_code)]
    pub param_cats: Vec<String>,
}

/// A single position in a multi-step rule's syntax pattern.
#[derive(Debug, Clone)]
pub enum BinderPosition {
    /// `Literal("text")` — consume + advance position.
    Literal(String),
    /// `Param(binder_name)` — capture single Ident, start_binder_scope,
    /// advance position.
    BinderIdent,
    /// `Op(Sep { collection: xs, separator })` — for ^[xs] multi-binder
    /// list. Engine enters BinderListLoop sub-state, captures Idents
    /// separated by `separator`, until close delim of position N+1 (the
    /// next Literal in the syntax pattern).
    BinderListLoop { separator: String, close: String },
    /// `Param(name)` — sub-parse the param's category. After the parse
    /// returns, the marker advances to the next position. If `is_final`,
    /// the action fires when the marker pops in Unwinding.
    ParamParse { cat: String, is_final: bool },
    /// `Param(guard)` for `?guard:Guard` — parse predicate inline via
    /// `parse_predicate_from_tokens`. Advance position.
    GuardSlot,
}

/// What kind of arg the action body extracts at each position (in push order).
#[derive(Debug, Clone)]
pub enum ActionArgKind {
    /// `ActionArg::Ident { name }` — single binder name.
    BinderName,
    /// `ActionArg::Term { value, .. }` of a specific category.
    Term(String),
    /// `ActionArg::Predicate` — parsed predicate.
    Predicate,
    /// Multi-binder list: a `BinderHandle` pushed by the binder-list-loop
    /// finalize step. Action body wraps as `Scope<Vec<Binder>, ...>`.
    BinderList,
}

/// Try to classify a `GrammarRule` as a multi-step rule (binder, multi-Param,
/// or guard-bearing).
pub(crate) fn classify_binder(rule: &GrammarRule) -> Option<BinderShape> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    if sp.is_empty() {
        return None;
    }
    // Position 0 must be a Literal trigger (otherwise it's an infix/prefix
    // Pratt rule handled by Phase 3).
    if !matches!(&sp[0], SyntaxExpr::Literal(_)) {
        return None;
    }

    // Build a map: param name → (kind, type_info).
    enum ParamKind {
        Simple { cat: String },
        Binder,
        BinderList,
        Body { cat: String },
        Guard,
    }
    let mut param_map: std::collections::HashMap<String, ParamKind> =
        std::collections::HashMap::new();
    let mut binder_param: Option<String> = None;
    let mut body_param: Option<String> = None;
    let mut is_multi = false;
    let mut has_binder = false;
    let mut body_cat: Option<String> = None;
    let mut param_cats: Vec<String> = Vec::new();
    for p in tc {
        match p {
            TermParam::Simple { name, ty } => match ty {
                TypeExpr::Base(ident) => {
                    let cat = ident.to_string();
                    param_cats.push(cat.clone());
                    param_map.insert(name.to_string(), ParamKind::Simple { cat });
                }
                _ => return None,
            },
            TermParam::Abstraction { binder, body, ty } => {
                let bcat = arrow_codomain_name(ty)?;
                binder_param = Some(binder.to_string());
                body_param = Some(body.to_string());
                body_cat = Some(bcat.clone());
                has_binder = true;
                param_map.insert(binder.to_string(), ParamKind::Binder);
                param_map.insert(body.to_string(), ParamKind::Body { cat: bcat });
            }
            TermParam::MultiAbstraction { binder, body, ty } => {
                let bcat = arrow_codomain_name(ty)?;
                binder_param = Some(binder.to_string());
                body_param = Some(body.to_string());
                body_cat = Some(bcat.clone());
                has_binder = true;
                is_multi = true;
                param_map.insert(binder.to_string(), ParamKind::BinderList);
                param_map.insert(body.to_string(), ParamKind::Body { cat: bcat });
            }
            TermParam::GuardBody { name } => {
                param_map.insert(name.to_string(), ParamKind::Guard);
            }
        }
    }
    let _ = (binder_param, body_param);

    // Walk syntax_pattern (skipping index 0 = trigger) building positions
    // + action_args in encountered-order (push order).
    let mut positions = Vec::new();
    let mut action_args = Vec::new();
    let mut last_param_idx: Option<usize> = None;
    let sp_len = sp.len();
    for (i, item) in sp.iter().enumerate().skip(1) {
        match item {
            SyntaxExpr::Literal(text) => {
                positions.push(BinderPosition::Literal(text.clone()));
            }
            SyntaxExpr::Param(name) => {
                let n = name.to_string();
                let kind = param_map.get(&n)?;
                match kind {
                    ParamKind::Binder => {
                        positions.push(BinderPosition::BinderIdent);
                        action_args.push(ActionArgKind::BinderName);
                    }
                    ParamKind::Body { cat } | ParamKind::Simple { cat } => {
                        // Determine if this Param is the FINAL Param/Body in the syntax_pattern
                        // (any later index is Literal-only — implies action fires on this
                        // Param's marker pop).
                        let is_final = sp.iter().enumerate().skip(i + 1).all(|(_, it)| {
                            matches!(it, SyntaxExpr::Literal(_))
                        });
                        positions.push(BinderPosition::ParamParse {
                            cat: cat.clone(),
                            is_final,
                        });
                        action_args.push(ActionArgKind::Term(cat.clone()));
                        last_param_idx = Some(positions.len() - 1);
                    }
                    ParamKind::Guard => {
                        positions.push(BinderPosition::GuardSlot);
                        action_args.push(ActionArgKind::Predicate);
                    }
                    ParamKind::BinderList => {
                        // BinderList shouldn't appear as a bare Param —
                        // it's expressed as Op(Sep) below. Defensive.
                        return None;
                    }
                }
            }
            SyntaxExpr::Op(PatternOp::Sep {
                collection,
                separator,
                source: None,
            }) => {
                let n = collection.to_string();
                let kind = param_map.get(&n)?;
                match kind {
                    ParamKind::BinderList => {
                        // Find the next Literal in syntax_pattern — that's
                        // the close delim of the binder-list loop.
                        let close = match sp.get(i + 1) {
                            Some(SyntaxExpr::Literal(text)) => text.clone(),
                            _ => return None,
                        };
                        positions.push(BinderPosition::BinderListLoop {
                            separator: separator.clone(),
                            close,
                        });
                        action_args.push(ActionArgKind::BinderList);
                    }
                    _ => return None, // Phase 5b doesn't yet handle Sep over a Simple param (collection-style).
                }
            }
            // Op(Map/Zip/Opt) or chained ops — Phase 5c (PInputs) territory; skip for now.
            SyntaxExpr::Op(_) => return None,
        }
    }
    let _ = (last_param_idx, sp_len);

    // Skip rules with no parsed positions (they're trivial and likely not
    // multi-step — let the atomic / TerminalKeyword classifier handle them).
    if positions.is_empty() {
        return None;
    }
    // Skip pure-literal rules (no params, no binder, no guard) — those are
    // already handled by the TerminalKeyword classifier.
    if action_args.is_empty() {
        return None;
    }

    let action_arity: u8 = action_args.len() as u8;

    Some(BinderShape {
        label: rule.label.to_string(),
        result_cat: rule.category.to_string(),
        positions,
        is_multi,
        has_binder,
        action_arity,
        action_args,
        body_cat,
        param_cats,
    })
}

/// Extract the codomain name from `TypeExpr::Arrow { domain, codomain }`.
fn arrow_codomain_name(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Arrow { codomain, .. } => match codomain.as_ref() {
            TypeExpr::Base(ident) => Some(ident.to_string()),
            _ => None,
        },
        _ => None,
    }
}

/// Look up a category name's src_idx in the categories slice.
fn lookup_src_idx(name: &str, categories: &[String]) -> Option<u16> {
    categories.iter().position(|c| c == name).map(|i| i as u16)
}

/// Phase 5: emit prefix-dispatch arms that recognize the FIRST literal
/// of each multi-step rule. On match, the arm pushes a `RuleAt(1)`
/// marker symbol and transitions to `BinderRule { ... }`.
///
/// **Multi-rule trigger disambiguation (Stage 4 fix, 2026-04-27):** when
/// multiple rules in the same result category share the same trigger
/// keyword (e.g., Calculator's five `bool(arg)` cast rules with `arg` of
/// different categories), naive per-rule arm emission produces identical
/// match patterns where only the first arm fires (Rust match semantics).
/// To match the trampoline's lookahead-based dispatch, we group rules by
/// `(trigger, result_src_idx)` and for groups with ≥2 rules emit a single
/// combined arm that peeks the token after the rule's literal prefix
/// (typically `pos + 2` for `kw "(" arg ...` patterns) and dispatches to
/// the rule whose first sub-parse `Param`'s source category has the peeked
/// token in its FIRST set.
///
/// **TECHNICAL DEBT (per `feedback_use_wpds_disambiguation_not_heuristics.md`):**
/// the FIRST-set fallback table and the separator-lookahead scan in this
/// function are HEURISTICS that paper over the absence of GLR-style
/// branching. The principled fix is to emit `WpdsStepAction::Fork` with
/// one branch per ambiguous rule and let the engine's lex-min weight
/// machinery select the surviving branch. That requires the engine's
/// step function to drive AmbiguityFanout state forward (currently it
/// returns Idle), which is a runtime prerequisite. Until then, treat
/// the heuristics here as a temporary scaffold and replace them with
/// Fork emission once the engine supports the full Fork +
/// AmbiguityFanout + BranchResolved handshake.
pub(crate) fn emit_binder_prefix_arms(
    language: &mettail_ast::language::LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    use std::collections::BTreeMap;

    /// Per-rule arm metadata.
    struct RuleEntry<'a> {
        rule_i: usize,
        shape: BinderShape,
        rule: &'a GrammarRule,
        literal_prefix_count: usize,
    }

    // Group entries by (trigger, result_src_idx). BTreeMap gives
    // deterministic iteration order; within a group, source order is
    // preserved by insertion.
    let mut groups: BTreeMap<(String, u16), Vec<RuleEntry<'_>>> = BTreeMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            let trigger = match rule
                .syntax_pattern
                .as_ref()
                .and_then(|sp| sp.first())
            {
                Some(SyntaxExpr::Literal(text)) => text.clone(),
                _ => continue,
            };
            let literal_prefix_count = literal_prefix_count_of(
                rule.syntax_pattern.as_ref().expect("checked above"),
            );
            let key = (trigger, cat_i as u16);
            groups.entry(key).or_default().push(RuleEntry {
                rule_i,
                shape,
                rule,
                literal_prefix_count,
            });
        }
    }

    let mut arms = Vec::new();
    for ((trigger, result_src_idx), entries) in groups {
        if entries.len() == 1 {
            // Single-rule group: emit the legacy arm verbatim.
            let entry = &entries[0];
            let rule_idx = entry.rule_i as u16;
            let body_src_idx = match &entry.shape.body_cat {
                Some(name) => lookup_src_idx(name, categories).unwrap_or(result_src_idx),
                None => result_src_idx,
            };
            arms.push(quote! {
                Some(mettail_prattail::automata::TokenKind::Fixed(__trigger))
                    if __trigger == #trigger && state_cat_src_idx == #result_src_idx => {
                    return WpdsStepAction::ConsumeAndPush {
                        symbol: StackSymbolV2::rule_at(
                            #result_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                        ),
                        weight: LexicographicWeight::from_cost(
                            0.0, #result_src_idx, #rule_idx,
                        ),
                        new_state: WpdsState::BinderRule {
                            result_src_idx: #result_src_idx,
                            rule_idx: #rule_idx,
                            body_src_idx: #body_src_idx,
                            outer_bp: _outer_bp,
                        },
                        capture_token: false,
                    };
                }
            });
            continue;
        }

        // Multi-rule group: emit a combined disambiguating arm.
        //
        // Require all rules in the group to share the same literal-prefix
        // count (i.e., they all peek at the same offset). This holds for
        // shapes like Calculator's five `bool(...)` rules. If they
        // diverge, fall back to the legacy emission per-rule (the first
        // arm wins, matching pre-fix behavior — diagnostics may surface
        // via the parity gate).
        let prefix_count = entries[0].literal_prefix_count;
        let prefix_count_homogeneous = entries
            .iter()
            .all(|e| e.literal_prefix_count == prefix_count);
        if !prefix_count_homogeneous {
            // Diverging prefix counts. Emit per-rule arms (only first
            // fires) — the parity gate will surface this as a known
            // limitation; future work tracked in
            // wpds_codegen/binder.rs::emit_binder_prefix_arms doc.
            for entry in &entries {
                let rule_idx = entry.rule_i as u16;
                let body_src_idx = match &entry.shape.body_cat {
                    Some(name) => lookup_src_idx(name, categories).unwrap_or(result_src_idx),
                    None => result_src_idx,
                };
                arms.push(quote! {
                    Some(mettail_prattail::automata::TokenKind::Fixed(__trigger))
                        if __trigger == #trigger && state_cat_src_idx == #result_src_idx => {
                        return WpdsStepAction::ConsumeAndPush {
                            symbol: StackSymbolV2::rule_at(
                                #result_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                            ),
                            weight: LexicographicWeight::from_cost(
                                0.0, #result_src_idx, #rule_idx,
                            ),
                            new_state: WpdsState::BinderRule {
                                result_src_idx: #result_src_idx,
                                rule_idx: #rule_idx,
                                body_src_idx: #body_src_idx,
                                outer_bp: _outer_bp,
                            },
                            capture_token: false,
                        };
                    }
                });
            }
            continue;
        }

        // Build the inner match: per-FIRST-token → (rule_idx, body_src_idx).
        // Conflicts (two rules' FIRST sets sharing a token) are resolved
        // by source order (first-declared wins) via insert-only on a
        // pattern-string key.
        let mut seen_patterns: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut inner_arms: Vec<TokenStream> = Vec::new();
        // Pick the fallback rule: the one whose first-Param category is
        // declared latest in `categories` (typically the most general
        // domain like Proc). If no first-Param cat is found, use the
        // last entry in source order.
        let fallback_idx = entries
            .iter()
            .enumerate()
            .max_by_key(|(_, entry)| {
                entry
                    .shape
                    .param_cats
                    .first()
                    .and_then(|c| categories.iter().position(|cn| cn == c))
                    .unwrap_or(0)
            })
            .map(|(i, _)| i)
            .unwrap_or(entries.len() - 1);
        let fallback_rule_idx = entries[fallback_idx].rule_i as u16;
        let fallback_body_src_idx = entries[fallback_idx]
            .shape
            .param_cats
            .first()
            .and_then(|c| lookup_src_idx(c, categories))
            .unwrap_or(result_src_idx);

        // Stage 4 fix: include the fallback rule in the FIRST-set scan
        // (do NOT skip it). The fallback's role is purely to handle
        // unknown tokens (the `_ =>` arm); its FIRST tokens still belong
        // in the dispatch table so its specific tokens map to its own
        // rule_idx (e.g., `StringLit → StrToBool`) instead of leaking
        // into the next iterated rule whose FIRST set also accepts the
        // shared token (e.g., `ProcToBool` accepting `StringLit` via
        // `ProcStr` cross-cat). Without this, the SECOND rule with a
        // shared FIRST token wins (since `seen_patterns.insert` rejects
        // duplicates after the first), inverting the trampoline's
        // first-declared-wins tiebreak convention.
        for entry in entries.iter() {
            let rule_idx_u16 = entry.rule_i as u16;
            let first_param_cat = entry.shape.param_cats.first();
            let first_param_src_idx = first_param_cat
                .and_then(|c| lookup_src_idx(c, categories))
                .unwrap_or(result_src_idx);
            let Some(cat_name) = first_param_cat else {
                continue;
            };
            let first_set = super::prefix::first_set_of_category(cat_name, language);
            for ft in &first_set {
                let pat = &ft.pattern;
                let key = format!(
                    "{}::{}",
                    pat,
                    ft.extra_guard
                        .as_ref()
                        .map(|g| g.to_string())
                        .unwrap_or_default()
                );
                if !seen_patterns.insert(key) {
                    continue;
                }
                let arm = match &ft.extra_guard {
                    Some(g) => quote! {
                        #pat if #g => (#rule_idx_u16, #first_param_src_idx),
                    },
                    None => quote! {
                        #pat => (#rule_idx_u16, #first_param_src_idx),
                    },
                };
                inner_arms.push(arm);
            }
        }

        // Stage 4 fix (Category B): when the multi-rule group has rules
        // of differing arity (e.g., Calculator's 1-arg `IntId` and 2-arg
        // `IntBin` both triggered by `int(`), the FIRST-set dispatch on
        // the first arg can't disambiguate (both rules accept the same
        // primitive integer in their first slot). Resolve by scanning
        // forward at runtime to the first separator at paren-depth 0:
        // a `,` selects a multi-arg rule; `)` selects a 1-arg rule.
        // Mirrors the trampoline's NFA-style try-each-rule loop.
        let arities: Vec<u8> = entries.iter().map(|e| e.shape.action_arity).collect();
        let has_mixed_arity = arities.iter().min() != arities.iter().max();
        let arity_dispatch = if has_mixed_arity {
            let multi_arity_idx = entries
                .iter()
                .position(|e| e.shape.action_arity > 1)
                .unwrap_or(0);
            let multi_rule_idx = entries[multi_arity_idx].rule_i as u16;
            let multi_body_src_idx = entries[multi_arity_idx]
                .shape
                .param_cats
                .first()
                .and_then(|c| lookup_src_idx(c, categories))
                .unwrap_or(result_src_idx);
            Some(quote! {
                {
                    // Lookahead scan: starting just past the literal
                    // prefix (i.e., at the first arg's first token),
                    // walk forward tracking paren/bracket/brace depth.
                    // The first separator at depth 0 disambiguates:
                    // `,` → multi-arg rule; `)`/`]`/`}` → 1-arg rule.
                    let mut __depth: i32 = 0;
                    let mut __scan = *pos + #prefix_count;
                    let mut __sep: u8 = 0; // 0=none, 1=comma, 2=close
                    loop {
                        match tokens.peek_text(__scan) {
                            None => { break; }
                            Some(t) => {
                                if t == "(" || t == "[" || t == "{" {
                                    __depth += 1;
                                } else if t == ")" || t == "]" || t == "}" {
                                    if __depth == 0 { __sep = 2; break; }
                                    __depth -= 1;
                                } else if t == "," && __depth == 0 {
                                    __sep = 1;
                                    break;
                                }
                            }
                        }
                        __scan += 1;
                        if __scan > *pos + 4096 { break; } // guard runaway
                    }
                    if __sep == 1 {
                        (#multi_rule_idx, #multi_body_src_idx)
                    } else {
                        match __next {
                            #(#inner_arms)*
                            _ => (#fallback_rule_idx, #fallback_body_src_idx),
                        }
                    }
                }
            })
        } else {
            None
        };

        let dispatch_body = match arity_dispatch {
            Some(body) => body,
            None => quote! {
                match __next {
                    #(#inner_arms)*
                    _ => (#fallback_rule_idx, #fallback_body_src_idx),
                }
            },
        };

        arms.push(quote! {
            Some(mettail_prattail::automata::TokenKind::Fixed(__trigger))
                if __trigger == #trigger && state_cat_src_idx == #result_src_idx => {
                let __lookahead = *pos + #prefix_count;
                let __next = tokens.peek_kind(__lookahead);
                let (__rule_idx, __body_src_idx): (u16, u16) = #dispatch_body;
                return WpdsStepAction::ConsumeAndPush {
                    symbol: StackSymbolV2::rule_at(
                        #result_src_idx, __rule_idx, 1u8, Some(_outer_bp),
                    ),
                    weight: LexicographicWeight::from_cost(
                        0.0, #result_src_idx, __rule_idx,
                    ),
                    new_state: WpdsState::BinderRule {
                        result_src_idx: #result_src_idx,
                        rule_idx: __rule_idx,
                        body_src_idx: __body_src_idx,
                        outer_bp: _outer_bp,
                    },
                    capture_token: false,
                };
            }
        });
    }
    quote! { #(#arms)* }
}

/// Count consecutive `Literal` items at the start of a syntax pattern
/// (including the trigger at index 0). Returns the offset at which the
/// first sub-parse `Param` slot begins.
fn literal_prefix_count_of(sp: &[SyntaxExpr]) -> usize {
    let mut n = 0usize;
    for item in sp {
        match item {
            SyntaxExpr::Literal(_) => n += 1,
            _ => break,
        }
    }
    n.max(1) // trigger always counts
}

/// Phase 5: emit the body of `WpdsState::BinderRule`. Reads the marker's
/// `RuleAt(position)` from frontier_top, dispatches per-rule-per-position.
pub(crate) fn emit_binder_rule_body(
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            // Stage 4 fix: emit a "rule complete" arm at position
            // `positions.len() + 1`. This arm fires when the marker has
            // advanced past the final syntax-pattern position (either via
            // a ConsumeAndReplace from a closing literal or a ReplaceAndPush
            // from a final ParamParse). It pops the RuleAt and fires the
            // semantic action; transitions to InfixLoop so the parent rule
            // can apply postfix/infix operators on the freshly-built result.
            let final_pos = (shape.positions.len() + 1) as u8;
            arms.push(quote! {
                (#result_src_idx, #rule_idx, #final_pos) => {
                    return WpdsStepAction::Pop {
                        weight: LexicographicWeight::one(),
                        new_state: WpdsState::InfixLoop {
                            cur_bp: *outer_bp,
                        },
                    };
                }
            });
            for (idx, position) in shape.positions.iter().enumerate() {
                let pos = (idx + 1) as u8;
                let next_pos = pos + 1;
                let arm = match position {
                    BinderPosition::Literal(text) => quote! {
                        (#result_src_idx, #rule_idx, #pos) => {
                            let token_text = tokens.peek_text(_pos).unwrap_or("");
                            if token_text != #text {
                                return WpdsStepAction::Error(format!(
                                    "expected '{}' at rule pos {}, got '{}'",
                                    #text, #pos, token_text,
                                ));
                            }
                            return WpdsStepAction::ConsumeAndReplace {
                                symbol: StackSymbolV2::rule_at(
                                    #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                ),
                                weight: LexicographicWeight::one(),
                                new_state: WpdsState::BinderRule {
                                    result_src_idx: #result_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: *_body_src_idx,
                                    outer_bp: *outer_bp,
                                },
                            };
                        }
                    },
                    BinderPosition::BinderIdent => quote! {
                        (#result_src_idx, #rule_idx, #pos) => {
                            match tokens.peek_kind(_pos) {
                                Some(mettail_prattail::automata::TokenKind::Ident) => {}
                                _ => return WpdsStepAction::Error(format!(
                                    "expected identifier at rule pos {}", #pos,
                                )),
                            }
                            return WpdsStepAction::ConsumeIdentAndReplace {
                                symbol: StackSymbolV2::rule_at(
                                    #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                ),
                                weight: LexicographicWeight::one(),
                                new_state: WpdsState::BinderRule {
                                    result_src_idx: #result_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: *_body_src_idx,
                                    outer_bp: *outer_bp,
                                },
                                start_scope: true,
                            };
                        }
                    },
                    BinderPosition::BinderListLoop { separator, close } => {
                        let _ = (separator, close);
                        // Phase 5b: enter BinderListLoop sub-state. The
                        // sub-state captures Idents until close, advances
                        // marker to next_pos when close is observed.
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                // Check first token: if Ident, capture and start collecting.
                                // If close delim, transition to next pos (empty list).
                                let token_text = tokens.peek_text(_pos).unwrap_or("");
                                if token_text == #close {
                                    // Empty list. Push an empty BinderList arg
                                    // (handled via builder.start_binder_scope(vec![])).
                                    b_pre_finalize_empty_list();
                                    return WpdsStepAction::ConsumeAndReplace {
                                        symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                        ),
                                        weight: LexicographicWeight::one(),
                                        new_state: WpdsState::BinderRule {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *_body_src_idx,
                                            outer_bp: *outer_bp,
                                        },
                                    };
                                }
                                // Non-empty: consume first Ident and start scope-list.
                                match tokens.peek_kind(_pos) {
                                    Some(mettail_prattail::automata::TokenKind::Ident) => {}
                                    _ => return WpdsStepAction::Error(format!(
                                        "expected identifier or '{}' in binder list", #close,
                                    )),
                                }
                                return WpdsStepAction::ConsumeIdentAndReplace {
                                    symbol: StackSymbolV2::rule_at(
                                        #result_src_idx, #rule_idx, #pos, Some(*outer_bp),
                                    ),
                                    weight: LexicographicWeight::one(),
                                    new_state: WpdsState::BinderListLoop {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        body_src_idx: *_body_src_idx,
                                        outer_bp: *outer_bp,
                                        marker_pos: #pos,
                                        next_pos: #next_pos,
                                    },
                                    start_scope: true,
                                };
                            }
                        }
                    }
                    BinderPosition::ParamParse { cat, is_final } => {
                        let cat_src_idx = lookup_src_idx(cat, categories).unwrap_or(0);
                        let _ = is_final;
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                // Replace marker to next_pos so when the
                                // sub-parse returns, Unwinding-RuleAt sees
                                // the post-param position. THEN push
                                // CategoryEntry on top of the new marker.
                                return WpdsStepAction::ReplaceAndPush {
                                    replace_symbol: StackSymbolV2::rule_at(
                                        #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                    ),
                                    push_symbol: StackSymbolV2::category_entry(#cat_src_idx),
                                    weight: LexicographicWeight::one(),
                                    new_state: WpdsState::PrefixDispatch {
                                        pos: _pos,
                                        cur_bp: 0,
                                    },
                                };
                            }
                        }
                    }
                    BinderPosition::GuardSlot => quote! {
                        (#result_src_idx, #rule_idx, #pos) => {
                            // Phase 6: parse predicate inline. Walker
                            // invokes parse_predicate_from_tokens, pushes
                            // ActionArg::Predicate, advances pos.
                            return WpdsStepAction::ParsePredicate {
                                replace_symbol: StackSymbolV2::rule_at(
                                    #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                ),
                                weight: LexicographicWeight::one(),
                                new_state: WpdsState::BinderRule {
                                    result_src_idx: #result_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: *_body_src_idx,
                                    outer_bp: *outer_bp,
                                },
                            };
                        }
                    },
                };
                arms.push(arm);
            }
        }
    }
    if arms.is_empty() {
        return quote! { WpdsStepAction::Idle };
    }
    quote! {
        {
            let position: u8 = match frontier_top.map(|n| n.symbol.kind) {
                Some(mettail_prattail::wpds_runtime::SymbolKind::RuleAt(p)) => p,
                _ => return WpdsStepAction::Idle,
            };
            // The empty-list branch needs to push an empty BinderList arg
            // representing zero binders. Use a closure-based local helper.
            #[allow(unused_variables)]
            let b_pre_finalize_empty_list = || ();
            match (*result_src_idx, *rule_idx, position) {
                #(#arms)*
                _ => WpdsStepAction::Idle,
            }
        }
    }
}

/// Phase 5b: emit the body of `WpdsState::BinderListLoop`. Loop captures
/// `Ident, separator, Ident, separator, ..., close` into the binder scope.
pub(crate) fn emit_binder_list_loop_body(per_cat: &[Vec<GrammarRule>]) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            for (idx, position) in shape.positions.iter().enumerate() {
                if let BinderPosition::BinderListLoop { separator, close } = position {
                    let pos = (idx + 1) as u8;
                    let next_pos = pos + 1;
                    let result_src_idx = cat_i as u16;
                    let rule_idx = rule_i as u16;
                    arms.push(quote! {
                        (#result_src_idx, #rule_idx) => {
                            let token_text = tokens.peek_text(_pos).unwrap_or("");
                            if token_text == #close {
                                // Done. Advance to next position via Replace.
                                let _ = #pos; // suppress unused
                                return WpdsStepAction::ConsumeAndReplace {
                                    symbol: StackSymbolV2::rule_at(
                                        #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                    ),
                                    weight: LexicographicWeight::one(),
                                    new_state: WpdsState::BinderRule {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        body_src_idx: *body_src_idx,
                                        outer_bp: *outer_bp,
                                    },
                                };
                            }
                            if token_text == #separator {
                                // Consume separator, expect next Ident.
                                return WpdsStepAction::Consume {
                                    weight: LexicographicWeight::one(),
                                    new_state: WpdsState::BinderListLoop {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        body_src_idx: *body_src_idx,
                                        outer_bp: *outer_bp,
                                        marker_pos: *marker_pos,
                                        next_pos: *next_pos,
                                    },
                                };
                            }
                            // Expect Ident: append to binder list.
                            match tokens.peek_kind(_pos) {
                                Some(mettail_prattail::automata::TokenKind::Ident) => {}
                                _ => return WpdsStepAction::Error(format!(
                                    "expected '{}', '{}', or identifier in binder list",
                                    #separator, #close,
                                )),
                            }
                            return WpdsStepAction::ConsumeIdentAndReplace {
                                symbol: StackSymbolV2::rule_at(
                                    #result_src_idx, #rule_idx, *marker_pos, Some(*outer_bp),
                                ),
                                weight: LexicographicWeight::one(),
                                new_state: WpdsState::BinderListLoop {
                                    result_src_idx: #result_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: *body_src_idx,
                                    outer_bp: *outer_bp,
                                    marker_pos: *marker_pos,
                                    next_pos: *next_pos,
                                },
                                start_scope: false, // append to existing scope
                            };
                        }
                    });
                }
            }
        }
    }
    if arms.is_empty() {
        return quote! { WpdsStepAction::Idle };
    }
    quote! {
        {
            match (*result_src_idx, *rule_idx) {
                #(#arms)*
                _ => WpdsStepAction::Idle,
            }
        }
    }
}

/// Phase 5: emit the action_for arm for a multi-step rule.
pub(crate) fn emit_binder_action_entry(
    src_idx: u16,
    rule_idx: u16,
    shape: &BinderShape,
    cat_ident: &Ident,
) -> Option<TokenStream> {
    let label_ident = format_ident!("{}", shape.label);
    let arity = shape.action_arity;

    // Generate the per-arg extraction code in push order.
    let mut extracts: Vec<TokenStream> = Vec::new();
    let mut field_names: Vec<TokenStream> = Vec::new();
    let mut binder_name_holders: Vec<Ident> = Vec::new();
    let mut body_holder: Option<Ident> = None;
    let mut binder_list_holder: Option<Ident> = None;

    for (i, kind) in shape.action_args.iter().enumerate() {
        let var = format_ident!("arg_{}", i);
        match kind {
            ActionArgKind::BinderName => {
                extracts.push(quote! {
                    let #var = match iter.next() {
                        Some(mettail_prattail::wpds_runtime::ActionArg::Ident { name, .. }) => name,
                        _ => return,
                    };
                });
                binder_name_holders.push(var.clone());
            }
            ActionArgKind::Term(cat) => {
                let cat_id = format_ident!("{}", cat);
                extracts.push(quote! {
                    let #var = match iter.next().and_then(|a| a.into_term::<#cat_id>()) {
                        Some(t) => t,
                        None => return,
                    };
                });
                if shape.has_binder
                    && shape.body_cat.as_deref() == Some(cat.as_str())
                    && body_holder.is_none()
                {
                    body_holder = Some(var.clone());
                } else {
                    field_names.push(quote! { Box::new(#var) });
                }
            }
            ActionArgKind::Predicate => {
                extracts.push(quote! {
                    let #var = match iter.next().and_then(|a| a.into_predicate::<mettail_runtime::BehavioralPred>()) {
                        Some(p) => p,
                        None => return,
                    };
                });
                field_names.push(quote! { #var });
            }
            ActionArgKind::BinderList => {
                extracts.push(quote! {
                    let #var = match iter.next() {
                        Some(mettail_prattail::wpds_runtime::ActionArg::BinderScope(h)) => h.names,
                        _ => return,
                    };
                });
                binder_list_holder = Some(var.clone());
            }
        }
    }

    // Build the action body's construction expression based on rule shape.
    // For binder rules with auxiliary fields (e.g. PGuardedInput's
    // `(Name, BehavioralPred, Scope<...>)`), the AST variant takes the
    // auxiliary fields first, then the Scope. We emit the call as
    // `Cat::Label(field_names..., scope)` — field_names comes from
    // non-binder, non-body Term args + Predicate args in encounter order.
    let construct = if shape.has_binder && shape.is_multi {
        // Multi-binder: Scope<Vec<Binder>, Box<Body>>.
        let binder_list = binder_list_holder.expect("multi-binder shape must have binder list");
        let body = body_holder.expect("multi-binder shape must have body");
        quote! {
            let binders: Vec<mettail_runtime::Binder<String>> = #binder_list
                .iter()
                .map(|n| mettail_runtime::Binder(mettail_runtime::get_or_create_var(n.clone())))
                .collect();
            let scope = mettail_runtime::Scope::new(binders, Box::new(#body));
            b.push_term::<#cat_ident>(
                #cat_ident::#label_ident(#(#field_names,)* scope)
            );
        }
    } else if shape.has_binder {
        // Single-binder: Scope<Binder, Box<Body>>.
        let binder_name = binder_name_holders
            .first()
            .expect("single-binder shape must have one binder name");
        let body = body_holder.expect("single-binder shape must have body");
        quote! {
            b.pop_binder_scope_silent();
            let scope = mettail_runtime::Scope::new(
                mettail_runtime::Binder(mettail_runtime::get_or_create_var(#binder_name)),
                Box::new(#body),
            );
            b.push_term::<#cat_ident>(
                #cat_ident::#label_ident(#(#field_names,)* scope)
            );
        }
    } else {
        // Multi-Param non-binder: Cat::Label(Box::new(arg_0), Box::new(arg_1), ...).
        quote! {
            b.push_term::<#cat_ident>(
                #cat_ident::#label_ident(#(#field_names),*)
            );
        }
    };

    let action_fn = quote! {
        |b: &mut mettail_prattail::wpds_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpds_runtime::ActionArg>| {
            let mut iter = args.into_iter();
            #(#extracts)*
            #construct
        }
    };
    Some(quote! {
        (#src_idx, #rule_idx) => {
            static ENTRY: mettail_prattail::wpds_runtime::ActionEntry =
                mettail_prattail::wpds_runtime::ActionEntry {
                    action_fn: #action_fn,
                    arity: #arity,
                };
            Some(&ENTRY)
        }
        ,
    })
}

/// Phase 5b: per-(rule_idx, position) lookup — is the position the
/// FINAL ParamParse before the action fires? Used by Unwinding-RuleAt
/// to decide whether to fire the action or advance the marker.
pub(crate) fn emit_binder_unwinding_dispatch(per_cat: &[Vec<GrammarRule>]) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            // Find the FINAL position (last positions index + 1 = total positions).
            let total_pos = shape.positions.len() as u8 + 1;
            arms.push(quote! {
                (#result_src_idx, #rule_idx) => Some(#total_pos),
            });
        }
    }
    if arms.is_empty() {
        return quote! { None::<u8> };
    }
    quote! {
        match (result_src_idx, rule_idx) {
            #(#arms)*
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::GrammarRule;
    use proc_macro2::Span;
    use syn::Ident;

    fn lambda_lam_rule() -> GrammarRule {
        GrammarRule {
            label: Ident::new("Lam", Span::call_site()),
            category: Ident::new("Term", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(vec![TermParam::Abstraction {
                binder: Ident::new("x", Span::call_site()),
                body: Ident::new("body", Span::call_site()),
                ty: TypeExpr::Arrow {
                    domain: Box::new(TypeExpr::Base(Ident::new("Term", Span::call_site()))),
                    codomain: Box::new(TypeExpr::Base(Ident::new("Term", Span::call_site()))),
                },
            }]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("lam ".into()),
                SyntaxExpr::Param(Ident::new("x", Span::call_site())),
                SyntaxExpr::Literal(".".into()),
                SyntaxExpr::Param(Ident::new("body", Span::call_site())),
            ]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        }
    }

    fn fraction_rule() -> GrammarRule {
        GrammarRule {
            label: Ident::new("Fraction", Span::call_site()),
            category: Ident::new("BigRat", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(vec![
                TermParam::Simple {
                    name: Ident::new("a", Span::call_site()),
                    ty: TypeExpr::Base(Ident::new("BigInt", Span::call_site())),
                },
                TermParam::Simple {
                    name: Ident::new("b", Span::call_site()),
                    ty: TypeExpr::Base(Ident::new("BigInt", Span::call_site())),
                },
            ]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("fraction".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Param(Ident::new("a", Span::call_site())),
                SyntaxExpr::Literal(",".into()),
                SyntaxExpr::Param(Ident::new("b", Span::call_site())),
                SyntaxExpr::Literal(")".into()),
            ]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        }
    }

    #[test]
    fn classifies_lambda_lam_rule() {
        let shape = classify_binder(&lambda_lam_rule()).expect("Lam should classify");
        assert_eq!(shape.label, "Lam");
        assert!(!shape.is_multi);
        assert!(shape.has_binder);
        assert_eq!(shape.action_arity, 2);
    }

    #[test]
    fn classifies_fraction_multi_param_rule() {
        let shape = classify_binder(&fraction_rule()).expect("Fraction should classify");
        assert_eq!(shape.label, "Fraction");
        assert!(!shape.is_multi);
        assert!(!shape.has_binder);
        assert_eq!(shape.action_arity, 2);
        assert_eq!(shape.param_cats, vec!["BigInt", "BigInt"]);
    }

    #[test]
    fn emits_binder_prefix_arm_for_lambda() {
        let categories = vec!["Term".to_string()];
        let per_cat = vec![vec![lambda_lam_rule()]];
        let language = synthetic_lang_for_lambda_test();
        let ts = emit_binder_prefix_arms(&language, &categories, &per_cat);
        let s = ts.to_string();
        assert!(s.contains("ConsumeAndPush"));
        assert!(s.contains("BinderRule"));
        assert!(s.contains("\"lam \""));
    }

    fn synthetic_lang_for_lambda_test() -> mettail_ast::language::LanguageDef {
        use mettail_ast::language::LangType;
        let mut lang = mettail_ast::language::LanguageDef {
            name: Ident::new("Toy", proc_macro2::Span::call_site()),
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
            terms: vec![lambda_lam_rule()],
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        };
        lang.types.push(LangType {
            name: Ident::new("Term", proc_macro2::Span::call_site()),
            native_type: None,
            collection_kind: None,
        });
        lang
    }

    #[test]
    fn emits_binder_rule_body_for_lambda() {
        let categories = vec!["Term".to_string()];
        let per_cat = vec![vec![lambda_lam_rule()]];
        let ts = emit_binder_rule_body(&categories, &per_cat);
        let s = ts.to_string();
        assert!(s.contains("ConsumeIdentAndReplace"));
        assert!(s.contains("ConsumeAndReplace"));
        assert!(s.contains("\".\""));
    }

    #[test]
    fn emits_binder_rule_body_for_fraction() {
        let categories = vec!["BigInt".to_string(), "BigRat".to_string()];
        let per_cat = vec![Vec::new(), vec![fraction_rule()]];
        let ts = emit_binder_rule_body(&categories, &per_cat);
        let s = ts.to_string();
        // "fraction" is the trigger consumed at open; positions 1+ are
        // "(", a (ParamParse), ",", b (ParamParse), ")". Verify the
        // emitted code contains ReplaceAndPush (for ParamParse slots) and
        // the literals.
        assert!(s.contains("ReplaceAndPush"));
        assert!(s.contains("\"(\""));
        assert!(s.contains("\")\""));
        assert!(s.contains("\",\""));
    }
}
