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

use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
use mettail_prattail::binding_power::{
    analyze_binding_powers, Associativity, BindingPowerTable, InfixOperator, InfixRuleInfo,
    MixfixPart,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

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
                if t1_str != t2_str {
                    return None;
                }
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
                    is_cross_category,
                    is_postfix: false,
                    is_mixfix: false,
                    mixfix_parts: Vec::new(),
                });
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
                    associativity: Associativity::Left,
                    is_cross_category,
                    is_postfix: true,
                    is_mixfix: false,
                    mixfix_parts: Vec::new(),
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
    if simples.len() >= 2 && syntax_pattern.len() >= 3 {
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
    if simples.len() < 2 || syntax_pattern.len() < 3 {
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
    let mut parts: Vec<mettail_prattail::binding_power::MixfixPart> = Vec::new();
    let mut simple_idx: usize = 1; // simples[0] is the LHS already consumed.
    let mut idx: usize = 2;
    while idx < syntax_pattern.len() {
        match &syntax_pattern[idx] {
            SyntaxExpr::Literal(t) => {
                if parts.is_empty() {
                    // Before any inner operand — accumulate as preceding
                    // for the next operand.
                    preceding_buffer.push(t.clone());
                } else {
                    // After the most-recent operand — append to its
                    // following_terminals.
                    parts
                        .last_mut()
                        .expect("parts non-empty inside else branch")
                        .following_terminals
                        .push(t.clone());
                }
                idx += 1;
            }
            SyntaxExpr::Param(p) => {
                let (sname, sty) = simples.get(simple_idx)?;
                if sname != &p {
                    return None;
                }
                let scat = base_type_name(sty)?;
                parts.push(mettail_prattail::binding_power::MixfixPart {
                    operand_category: scat,
                    param_name: p.to_string(),
                    preceding_terminals: std::mem::take(&mut preceding_buffer),
                    following_terminals: Vec::new(),
                });
                simple_idx += 1;
                idx += 1;
            }
            _ => return None,
        }
    }
    // All simples must be consumed.
    if simple_idx != simples.len() {
        return None;
    }
    // preceding_buffer should be empty at end (literals after last operand
    // were appended to its following_terminals). If the original pattern
    // had a Literal-only tail past the last operand, the loop already
    // routed those into the last part's following_terminals.
    if !preceding_buffer.is_empty() {
        // This can only happen if the rule has literals AFTER the trigger
        // but no inner operands at all — which is degenerate (no parts to
        // attach them to). Reject.
        return None;
    }

    Some(InfixRuleInfo {
        label: rule.label.to_string(),
        terminal: trigger,
        category: lhs_cat,
        result_category: result_cat,
        associativity: mettail_prattail::binding_power::Associativity::Left,
        is_cross_category,
        is_postfix: false,
        // Treated as mixfix for downstream dispatch — the widened
        // MixfixPart vectors carry the postfix-mixfix-specific terminal
        // sequences.
        is_mixfix: true,
        mixfix_parts: parts,
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
                        });
                    }
                }
                _ => return None,
            }
        } else {
            match expr {
                SyntaxExpr::Literal(t) => {
                    if i == 1 {
                        trigger = Some(t.clone());
                    }
                }
                _ => return None,
            }
        }
    }
    let trigger = trigger?;
    let (_, lhs_ty) = simples[0];
    let lhs_cat = base_type_name(lhs_ty)?;
    let result_cat = rule.category.to_string();
    let is_cross_category = lhs_cat != result_cat;
    Some(InfixRuleInfo {
        label: rule.label.to_string(),
        terminal: trigger,
        category: lhs_cat,
        result_category: result_cat,
        associativity: Associativity::Left,
        is_cross_category,
        is_postfix: false,
        is_mixfix: true,
        mixfix_parts: parts,
    })
}

fn base_type_name(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Base(ident) => Some(ident.to_string()),
        _ => None,
    }
}

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
    let mut per_cat_tables = Vec::new();
    for cat in categories {
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
        per_cat_tables.push(emit_infix_bp_fn(&bp_table, cat, &infix_ident, &label_to_indices));
        per_cat_tables.push(emit_postfix_bp_fn(&bp_table, cat, &postfix_ident, &label_to_indices));
        per_cat_tables.push(emit_mixfix_bp_fn(&bp_table, cat, &mixfix_ident, &label_to_indices));
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
    per_cat_tables.push(emit_mixfix_parts_fn(&bp_table, categories, &label_to_indices));
    quote! { #(#per_cat_tables)* }
}

/// Build a map from rule.label → (cat_src_idx, rule_idx). Used to look up
/// the pair for an operator's `result_category` + `label`.
fn build_label_index(
    categories: &[String],
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
) -> std::collections::HashMap<(String, String), (u16, u16)> {
    let mut idx = std::collections::HashMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let cat_name = &categories[cat_i];
        for (rule_i, rule) in rules.iter().enumerate() {
            idx.insert(
                (cat_name.clone(), rule.label.to_string()),
                (cat_i as u16, rule_i as u16),
            );
        }
    }
    idx
}

fn emit_infix_bp_fn(
    bp_table: &BindingPowerTable,
    category: &str,
    fn_ident: &proc_macro2::Ident,
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
) -> TokenStream {
    let arms = bp_table
        .operators
        .iter()
        .filter(|op| op.category == category && !op.is_postfix && !op.is_mixfix)
        .filter_map(|op| {
            // Look up the operator's (result_src_idx, rule_idx) using its
            // result_category + label. Skip if not found (defensive).
            let (result_src_idx, rule_idx) = *label_index
                .get(&(op.result_category.clone(), op.label.clone()))?;
            let term = &op.terminal;
            let l = op.left_bp;
            let r = op.right_bp;
            Some(quote! {
                #term => Some((#l, #r, #result_src_idx, #rule_idx)),
            })
        });
    quote! {
        /// Binding-power lookup for infix operators in this category.
        /// Returns `(left_bp, right_bp, result_src_idx, rule_idx)`.
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(terminal: &str) -> Option<(u8, u8, u16, u16)> {
            match terminal {
                #(#arms)*
                _ => None,
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
/// At codegen time, also filters by `op.result_category == category`
/// to ensure the rule is in the dispatched category's table. Same-
/// category invariant guaranteed by `is_iterative_candidate`'s
/// `!is_cross_category` gate.
fn emit_iter_eligible_fn(
    bp_table: &BindingPowerTable,
    category: &str,
    fn_ident: &proc_macro2::Ident,
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
    categories: &[String],
    cat_lit_rule_idx: &std::collections::HashMap<String, u16>,
    cat_is_value_home: &std::collections::HashMap<String, bool>,
) -> TokenStream {
    // Resolve a category NAME → its source index (position in `categories`).
    let cat_pos = |name: &str| categories.iter().position(|c| c == name).map(|p| p as u16);
    // Value-home rank: 0 if the category parses its operand literal via a
    // tier-0.0 polymorphic home prefix arm (integer-home), else 1. Mirrors
    // the walker's lex-min primary key so the canonical winner matches the
    // category the convergent normal walker selects at EOI.
    let value_home_rank =
        |name: &str| -> u8 { u8::from(!*cat_is_value_home.get(name).unwrap_or(&false)) };
    let cat_ops: Vec<&InfixOperator> = bp_table
        .operators
        .iter()
        .filter(|op| op.category == category)
        .collect();
    let arms: Vec<TokenStream> = cat_ops
        .iter()
        .filter(|op| op.is_iterative_candidate())
        // D1 (cross-category canonical): only the lex-min WINNER category for
        // each terminal is eligible — lowest `(value_home_rank, src_idx,
        // label)` — so exactly ONE category absorbs a chain over that terminal
        // and the rest stay on the convergent normal walker (prevents the
        // WALK-S1.5 cross-cat fanout). The value-home key makes a bare-integer
        // chain converge on Int even when a non-integer-home category (BigRat)
        // has a lower src_idx.
        .filter(|op| bp_table.is_canonical_iter_op(op, &cat_pos, &value_home_rank))
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

fn emit_postfix_bp_fn(
    bp_table: &BindingPowerTable,
    category: &str,
    fn_ident: &proc_macro2::Ident,
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
) -> TokenStream {
    let arms = bp_table
        .operators
        .iter()
        .filter(|op| op.category == category && op.is_postfix)
        .filter_map(|op| {
            let (result_src_idx, rule_idx) = *label_index
                .get(&(op.result_category.clone(), op.label.clone()))?;
            let term = &op.terminal;
            let l = op.left_bp;
            Some(quote! {
                #term => Some((#l, #result_src_idx, #rule_idx)),
            })
        });
    quote! {
        /// Binding-power lookup for postfix operators in this category.
        /// Returns `(left_bp, result_src_idx, rule_idx)`.
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(terminal: &str) -> Option<(u8, u16, u16)> {
            match terminal {
                #(#arms)*
                _ => None,
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
    bp_table: &BindingPowerTable,
    category: &str,
    fn_ident: &proc_macro2::Ident,
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
) -> TokenStream {
    let arms = bp_table
        .operators
        .iter()
        .filter(|op| op.category == category && op.is_mixfix)
        .filter_map(|op| {
            let (result_src_idx, rule_idx) = *label_index
                .get(&(op.result_category.clone(), op.label.clone()))?;
            let term = &op.terminal;
            let l = op.left_bp;
            Some(quote! {
                #term => Some((#l, #result_src_idx, #rule_idx)),
            })
        });
    quote! {
        /// Binding-power lookup for mixfix operators in this category.
        /// Returns `(left_bp, result_src_idx, rule_idx)`.
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(terminal: &str) -> Option<(u8, u16, u16)> {
            match terminal {
                #(#arms)*
                _ => None,
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
) -> TokenStream {
    let mut part_arms = Vec::new();
    let mut len_arms = Vec::new();
    for op in bp_table.operators.iter().filter(|op| op.is_mixfix) {
        let Some(&(result_src_idx, rule_idx)) =
            label_index.get(&(op.result_category.clone(), op.label.clone()))
        else {
            continue;
        };
        let parts_len = op.mixfix_parts.len() as u8;
        len_arms.push(quote! {
            (#result_src_idx, #rule_idx) => Some(#parts_len),
        });
        for (part_idx, part) in op.mixfix_parts.iter().enumerate() {
            let part_idx = part_idx as u8;
            let operand_src_idx = categories
                .iter()
                .position(|c| c == &part.operand_category)
                .map(|i| i as u16)
                .unwrap_or(0);
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
                )),
            });
        }
    }
    quote! {
        /// Mixfix per-part metadata: returns
        /// `(operand_src_idx, preceding_terminals, following_terminals)`.
        /// L12 follow-up B6 (2026-05-07): widened to vector terminals
        /// for postfix-mixfix support.
        #[allow(non_snake_case, dead_code)]
        fn mixfix_part(
            result_src_idx: u16,
            rule_idx: u16,
            part_idx: u8,
        ) -> Option<(u16, &'static [&'static str], &'static [&'static str])> {
            match (result_src_idx, rule_idx, part_idx) {
                #(#part_arms)*
                _ => None,
            }
        }

        /// Mixfix parts count: returns the number of inner operands for
        /// the (result_src, rule_idx) mixfix rule.
        #[allow(non_snake_case, dead_code)]
        fn mixfix_parts_len(result_src_idx: u16, rule_idx: u16) -> Option<u8> {
            match (result_src_idx, rule_idx) {
                #(#len_arms)*
                _ => None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::GrammarRule;
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
            label: Ident::new(label, Span::call_site()),
            category: Ident::new(cat, Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(vec![simple("a", operand), simple("b", operand)]),
            syntax_pattern: Some(vec![param("a"), lit(op), param("b")]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
        }
    }

    fn postfix_rule(label: &str, cat: &str, operand: &str, op: &str) -> GrammarRule {
        GrammarRule {
            label: Ident::new(label, Span::call_site()),
            category: Ident::new(cat, Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(vec![simple("a", operand)]),
            syntax_pattern: Some(vec![param("a"), lit(op)]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
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

    #[test]
    fn rejects_mixed_operand_types() {
        let mut rule = infix_rule("Mix", "Int", "Int", "+");
        rule.term_context = Some(vec![simple("a", "Int"), simple("b", "Float")]);
        assert!(classify_rule(&rule).is_none());
    }
}
