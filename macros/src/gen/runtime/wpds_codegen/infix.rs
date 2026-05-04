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
    analyze_binding_powers, Associativity, BindingPowerTable, InfixRuleInfo, MixfixPart,
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
pub(crate) fn extract_infix_rules(language: &LanguageDef) -> Vec<InfixRuleInfo> {
    let mut rules = Vec::new();
    for rule in &language.terms {
        if let Some(info) = classify_rule(rule) {
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
pub(crate) fn classify_rule_public(rule: &GrammarRule) -> Option<InfixRuleInfo> {
    classify_rule(rule)
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

    None
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
                        let following = if i + 1 < syntax_pattern.len() {
                            if let SyntaxExpr::Literal(t) = &syntax_pattern[i + 1] {
                                Some(t.clone())
                            } else {
                                return None;
                            }
                        } else {
                            None
                        };
                        parts.push(MixfixPart {
                            operand_category: cat,
                            param_name: p.to_string(),
                            following_terminal: following,
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
    let mut per_cat_tables = Vec::new();
    for cat in categories {
        let cat_lower = cat.to_lowercase();
        let infix_ident = format_ident!("infix_bp_{}", cat_lower);
        let postfix_ident = format_ident!("postfix_bp_{}", cat_lower);
        let mixfix_ident = format_ident!("mixfix_bp_{}", cat_lower);
        per_cat_tables.push(emit_infix_bp_fn(&bp_table, cat, &infix_ident, &label_to_indices));
        per_cat_tables.push(emit_postfix_bp_fn(&bp_table, cat, &postfix_ident, &label_to_indices));
        per_cat_tables.push(emit_mixfix_bp_fn(&bp_table, cat, &mixfix_ident, &label_to_indices));
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

/// B7 Pattern 1: emit per-rule mixfix-parts metadata. Returns
/// `mixfix_part(result_src_idx, rule_idx, part_idx) -> Option<(operand_src_idx, following_terminal: Option<&'static str>)>`.
/// `following_terminal` is `Some(t)` for inner-not-last operands (the
/// separator after that operand) and `None` for the last operand.
/// `mixfix_parts_len(result_src_idx, rule_idx) -> Option<u8>` returns the
/// number of inner operands so the engine knows when to stop.
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
            let following_arm = match &part.following_terminal {
                Some(t) => quote! { Some((#operand_src_idx, Some(#t))) },
                None => quote! { Some((#operand_src_idx, None)) },
            };
            part_arms.push(quote! {
                (#result_src_idx, #rule_idx, #part_idx) => #following_arm,
            });
        }
    }
    quote! {
        /// Mixfix per-part metadata: returns `(operand_src_idx, following_terminal)`.
        #[allow(non_snake_case, dead_code)]
        fn mixfix_part(
            result_src_idx: u16,
            rule_idx: u16,
            part_idx: u8,
        ) -> Option<(u16, Option<&'static str>)> {
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
