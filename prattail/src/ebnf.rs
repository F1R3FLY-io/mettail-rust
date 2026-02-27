//! EBNF debug dump for PraTTaIL grammars.
//!
//! Produces an annotated EBNF representation of a language grammar,
//! using ISO 14977 conventions with practical extensions for binding powers,
//! FIRST/FOLLOW sets, binders, collections, and optional groups.
//!
//! Activated via the `PRATTAIL_DUMP_EBNF` environment variable:
//! - `PRATTAIL_DUMP_EBNF=1` writes to `target/prattail/<Name>.ebnf`
//! - `PRATTAIL_DUMP_EBNF=<dir>` writes to `<dir>/<Name>.ebnf`

use std::fmt::Write;

use crate::binding_power::{Associativity, BindingPowerTable, InfixOperator};
use crate::dispatch::{CastRule, CrossCategoryRule};
use crate::pipeline::{CategoryInfo, ParserBundle};
use crate::prediction::{compute_first_sets, compute_follow_sets_from_inputs, FirstSet};
use crate::recursive::{CollectionKind, RDRuleInfo, RDSyntaxItem};
use crate::{LanguageSpec, RuleSpec, SyntaxItemSpec};

// ══════════════════════════════════════════════════════════════════════════════
// Public API
// ══════════════════════════════════════════════════════════════════════════════

/// Format a complete EBNF representation of a language grammar.
///
/// Uses data from both the `LanguageSpec` (for full rule details including
/// syntax items) and the `ParserBundle` (for computed binding powers,
/// FIRST/FOLLOW sets, and rule classifications).
pub fn format_ebnf(spec: &LanguageSpec, bundle: &ParserBundle) -> String {
    let category_names: Vec<String> = bundle.categories.iter().map(|c| c.name.clone()).collect();

    // Compute FIRST sets (same logic as pipeline.rs generate_parser_code)
    let mut first_sets = compute_first_sets(&bundle.rule_infos, &category_names);
    for cat in &bundle.categories {
        if let Some(ref native_type) = cat.native_type {
            if let Some(first_set) = first_sets.get_mut(&cat.name) {
                augment_first_set_with_native(first_set, native_type);
            }
        }
    }

    // Augment FIRST set with Caret and dollar tokens if grammar has binders
    if bundle.has_binders {
        let primary_category = category_names.first().map(|s| s.as_str()).unwrap_or("");
        if let Some(first_set) = first_sets.get_mut(primary_category) {
            first_set.insert("Caret");
            for cat in &bundle.categories {
                let cat_lower = cat.name.to_lowercase();
                let capitalized = {
                    let mut s = String::with_capacity(cat_lower.len());
                    let mut chars = cat_lower.chars();
                    if let Some(first) = chars.next() {
                        s.extend(first.to_uppercase());
                    }
                    s.extend(chars);
                    s
                };
                first_set.insert(&format!("Dollar{}", capitalized));
                first_set.insert(&format!("Ddollar{}Lp", capitalized));
            }
        }
    }

    // Compute FOLLOW sets
    let primary_category = category_names.first().map(|s| s.as_str()).unwrap_or("");
    let follow_sets = compute_follow_sets_from_inputs(
        &bundle.follow_inputs,
        &category_names,
        &first_sets,
        primary_category,
    );

    let mut buf = String::with_capacity(4096);

    write_header(&mut buf, &spec.name);
    write_lexical_tokens(&mut buf, &bundle.categories);

    for cat in &bundle.categories {
        let cat_rules: Vec<&RuleSpec> = spec
            .rules
            .iter()
            .filter(|r| r.category == cat.name)
            .collect();

        if cat_rules.is_empty() {
            continue;
        }

        // Write precedence table if this category has operators
        write_precedence_table(&mut buf, &cat.name, &bundle.bp_table, &bundle.rd_rules);

        // Write category productions
        let first_set = first_sets.get(&cat.name);
        let follow_set = follow_sets.get(&cat.name);
        write_category(
            &mut buf,
            cat,
            &cat_rules,
            &bundle.bp_table,
            &bundle.cross_rules,
            &bundle.cast_rules,
            first_set,
            follow_set,
            bundle.has_binders,
            &bundle.categories,
        );
    }

    buf
}

/// Write EBNF output to the appropriate location based on the dump target.
///
/// - `"1"` → write to `target/prattail/<name>.ebnf`
/// - Any other value → treat as directory path, write to `<dir>/<name>.ebnf`
pub fn write_ebnf_output(ebnf: &str, language_name: &str, dump_target: &str) {
    let dir = if dump_target == "1" {
        std::path::PathBuf::from("target/prattail")
    } else {
        std::path::PathBuf::from(dump_target)
    };

    if let Err(e) = std::fs::create_dir_all(&dir) {
        eprintln!("warning: PRATTAIL_DUMP_EBNF: failed to create directory {:?}: {}", dir, e);
        return;
    }

    let path = dir.join(format!("{}.ebnf", language_name));
    match std::fs::write(&path, ebnf) {
        Ok(()) => eprintln!("info: PRATTAIL_DUMP_EBNF: wrote {}", path.display()),
        Err(e) => eprintln!("warning: PRATTAIL_DUMP_EBNF: failed to write {:?}: {}", path, e),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Header
// ══════════════════════════════════════════════════════════════════════════════

fn write_header(buf: &mut String, name: &str) {
    let title = format!("{}  {} — EBNF Grammar", " ", name);
    let gen = format!("{}  Generated by PraTTaIL", " ");
    let width = 58;
    let bar = "═".repeat(width - 5);

    writeln!(buf, "(* {} *)", bar).unwrap();
    writeln!(buf, "(*{:<w$}*)", title, w = width - 2).unwrap();
    writeln!(buf, "(*{:<w$}*)", gen, w = width - 2).unwrap();
    writeln!(buf, "(* {} *)", bar).unwrap();
    writeln!(buf).unwrap();
}

// ══════════════════════════════════════════════════════════════════════════════
// Lexical Tokens
// ══════════════════════════════════════════════════════════════════════════════

fn write_lexical_tokens(buf: &mut String, categories: &[CategoryInfo]) {
    writeln!(buf, "(* ── Lexical Tokens ──────────────────────────────────── *)").unwrap();
    writeln!(buf).unwrap();

    // Collect native types to emit corresponding token patterns
    let mut has_integer = false;
    let mut has_float = false;
    let mut has_boolean = false;
    let mut has_string = false;
    let mut integer_type = "i32";
    let mut float_type = "f64";

    for cat in categories {
        if let Some(ref native) = cat.native_type {
            match native.as_str() {
                "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => {
                    has_integer = true;
                    integer_type = match native.as_str() {
                        "i32" => "i32",
                        "i64" => "i64",
                        "u32" => "u32",
                        "u64" => "u64",
                        "isize" => "isize",
                        "usize" => "usize",
                        _ => "i32",
                    };
                },
                "f32" | "f64" => {
                    has_float = true;
                    float_type = if native == "f32" { "f32" } else { "f64" };
                },
                "bool" => {
                    has_boolean = true;
                },
                "str" | "String" => {
                    has_string = true;
                },
                _ => {},
            }
        }
    }

    if has_integer {
        writeln!(
            buf,
            "<integer> = /[0-9]+/{:>pad$}(* {} *) ;",
            "",
            integer_type,
            pad = 44_usize.saturating_sub("<integer> = /[0-9]+/".len())
        )
        .unwrap();
    }
    if has_float {
        writeln!(
            buf,
            "<float>   = /[0-9]+\\.[0-9]+/{:>pad$}(* {} *) ;",
            "",
            float_type,
            pad = 44_usize.saturating_sub("<float>   = /[0-9]+\\.[0-9]+/".len())
        )
        .unwrap();
    }
    if has_boolean {
        writeln!(buf, "<boolean> = /true|false/             (* bool *) ;").unwrap();
    }
    if has_string {
        writeln!(buf, "<string>  = /\"([^\"\\\\]|\\\\.)*\"/         (* str *) ;").unwrap();
    }

    writeln!(buf, "<ident>   = /[a-zA-Z_][a-zA-Z0-9_]*/ ;").unwrap();
    writeln!(buf).unwrap();
}

// ══════════════════════════════════════════════════════════════════════════════
// Precedence Table
// ══════════════════════════════════════════════════════════════════════════════

fn write_precedence_table(
    buf: &mut String,
    category: &str,
    bp_table: &BindingPowerTable,
    rd_rules: &[RDRuleInfo],
) {
    // Collect all operators for this category (infix, postfix, mixfix, cross-category)
    let all_ops: Vec<&InfixOperator> = bp_table
        .operators
        .iter()
        .filter(|op| op.category == category)
        .collect();

    // Collect prefix operators from RD rules
    let prefix_ops: Vec<&RDRuleInfo> = rd_rules
        .iter()
        .filter(|r| r.category == category && r.prefix_bp.is_some())
        .collect();

    if all_ops.is_empty() && prefix_ops.is_empty() {
        return;
    }

    writeln!(buf, "(* ── Precedence Table: {} ───────────────────────────── *)", category).unwrap();
    writeln!(buf, "(*{:>55}*)", "").unwrap();
    writeln!(
        buf,
        "(*  {:<8} {:<6} {:<8} {:<12} {:<16}*)",
        "BP", "Assoc", "Op", "Label", "Kind"
    )
    .unwrap();
    writeln!(
        buf,
        "(*  {:<8} {:<6} {:<8} {:<12} {:<16}*)",
        "───────", "─────", "──", "─────", "────"
    )
    .unwrap();

    // Non-postfix, non-prefix operators in BP order
    let mut infix_ops: Vec<&&InfixOperator> = all_ops.iter().filter(|op| !op.is_postfix).collect();
    infix_ops.sort_by_key(|op| op.left_bp);

    for op in &infix_ops {
        let assoc = match op.associativity() {
            Associativity::Left => "left",
            Associativity::Right => "right",
        };

        let op_str = if op.is_mixfix {
            // Show all terminals for mixfix (e.g., "? :")
            let mut parts = vec![op.terminal.clone()];
            for part in &op.mixfix_parts {
                if let Some(ref sep) = part.following_terminal {
                    parts.push(sep.clone());
                }
            }
            parts.join(" ")
        } else {
            op.terminal.clone()
        };

        let kind = if op.is_mixfix {
            "mixfix".to_string()
        } else if op.is_cross_category {
            format!("cross → {}", op.result_category)
        } else {
            "infix".to_string()
        };

        writeln!(
            buf,
            "(*  ({}, {})  {:<6} {:<8} {:<12} {:<12}*)",
            op.left_bp, op.right_bp, assoc, op_str, op.label, kind
        )
        .unwrap();
    }

    // Prefix operators
    for rd in &prefix_ops {
        let bp = rd.prefix_bp.unwrap_or(0);
        // Find the terminal in the rule items
        let op_str: String = rd
            .items
            .iter()
            .find_map(|item| {
                if let RDSyntaxItem::Terminal(t) = item {
                    Some(t.clone())
                } else {
                    None
                }
            })
            .unwrap_or_else(|| "?".to_string());

        writeln!(buf, "(*  prefix   ─       {:<8} {:<12} bp = {:<8}*)", op_str, rd.label, bp)
            .unwrap();
    }

    // Postfix operators
    let mut postfix_ops: Vec<&&InfixOperator> = all_ops.iter().filter(|op| op.is_postfix).collect();
    postfix_ops.sort_by_key(|op| op.left_bp);

    for op in &postfix_ops {
        writeln!(
            buf,
            "(*  postfix  ─       {:<8} {:<12} bp = {:<8}*)",
            op.terminal, op.label, op.left_bp
        )
        .unwrap();
    }

    writeln!(buf).unwrap();
}

// ══════════════════════════════════════════════════════════════════════════════
// Category Productions
// ══════════════════════════════════════════════════════════════════════════════

#[allow(clippy::too_many_arguments)]
fn write_category(
    buf: &mut String,
    cat: &CategoryInfo,
    rules: &[&RuleSpec],
    bp_table: &BindingPowerTable,
    cross_rules: &[CrossCategoryRule],
    cast_rules: &[CastRule],
    first_set: Option<&FirstSet>,
    follow_set: Option<&FirstSet>,
    has_binders: bool,
    all_categories: &[CategoryInfo],
) {
    // Category header
    let native_annotation = cat
        .native_type
        .as_ref()
        .map(|t| format!(", native: {}", t))
        .unwrap_or_default();
    let primary_annotation = if cat.is_primary { "primary" } else { "" };
    let annotations = match (primary_annotation.is_empty(), native_annotation.is_empty()) {
        (true, true) => String::new(),
        (false, true) => format!(" ({})", primary_annotation),
        (true, false) => format!(" ({})", native_annotation.trim_start_matches(", ")),
        (false, false) => format!(" ({}{})", primary_annotation, native_annotation),
    };

    writeln!(buf, "(* ── {}{} ─────────────────────────────── *)", cat.name, annotations).unwrap();
    writeln!(buf).unwrap();

    // Order rules for display:
    // 1. Literal, 2. Var, 3. Grouping, 4. RD (structural), 5. Prefix, 6. Cast, 7. Infix (by BP), 8. Postfix
    let sorted_rules = sort_rules_for_display(rules, bp_table);

    let cat_name = &cat.name;

    // Collect all production lines: (syntax_str, comment)
    let mut productions: Vec<(String, String)> = Vec::with_capacity(rules.len() + 3);

    // 1. Implicit native literal production (if category has native type)
    if let Some(ref native_type) = cat.native_type {
        let (token_name, label) = match native_type.as_str() {
            "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => ("<integer>", "NumLit"),
            "f32" | "f64" => ("<float>", "FloatLit"),
            "bool" => ("<boolean>", "BoolLit"),
            "str" | "String" => ("<string>", "StringLit"),
            _ => ("?native?", "Lit"),
        };
        productions.push((token_name.to_string(), format!("(* {} *)", label)));
    }

    // 2. Implicit variable production (all categories have Var fallback)
    {
        let first_letter = cat_name
            .chars()
            .next()
            .unwrap_or('V')
            .to_uppercase()
            .collect::<String>();
        let var_label = format!("{}Var", first_letter);
        productions.push(("<ident>".to_string(), format!("(* {} *)", var_label)));
    }

    // 3. Implicit grouping production: "(" Cat ")"
    // (Always generated by the Pratt parser for every category)
    productions.push((format!("\"(\" {} \")\"", cat_name), "(* group *)".to_string()));

    // 4. Implicit lambda productions (if primary category has binder rules)
    if cat.is_primary && has_binders {
        productions.push((
            "\"^\" <ident> \".\" \"{\" Cat \"}\"".replace("Cat", cat_name),
            "(* lambda *)".to_string(),
        ));
        productions.push((
            "\"^\" \"[\" <ident> { \",\" <ident> } \"]\" \".\" \"{\" Cat \"}\""
                .replace("Cat", cat_name),
            "(* multi-lambda *)".to_string(),
        ));

        // Dollar application productions: $dom(f, x) and $$dom(f, x1, x2, ...)
        for dom_cat in all_categories {
            let dom_lower = dom_cat.name.to_lowercase();
            let dom_name = &dom_cat.name;
            productions.push((
                format!("\"${}\" \"(\" {} \",\" {} \")\"", dom_lower, cat_name, dom_name),
                format!("(* apply-{} *)", dom_lower),
            ));
            productions.push((
                format!(
                    "\"$${}(\" {} \",\" {} {{ \",\" {} }} \")\"",
                    dom_lower, cat_name, dom_name, dom_name
                ),
                format!("(* multi-apply-{} *)", dom_lower),
            ));
        }
    }

    // 5. Explicit rules (sorted)
    for (rule, _annotation) in &sorted_rules {
        // Skip rules that duplicate implicit productions
        if rule.is_literal || rule.is_var || is_grouping_rule(rule) {
            continue;
        }
        let syntax_str = format_syntax(rule, cat_name);
        let comment = format_rule_annotation(rule, bp_table, cross_rules, cast_rules);
        productions.push((syntax_str, comment));
    }

    // Render all productions
    for (i, (syntax_str, comment)) in productions.iter().enumerate() {
        let line = if i == 0 {
            format!("{} = {}", cat_name, syntax_str)
        } else {
            format!("{:>w$}| {}", "", syntax_str, w = cat_name.len() + 1)
        };

        if comment.is_empty() {
            writeln!(buf, "{}", line).unwrap();
        } else {
            // Pad to column 42 for aligned comments
            let pad = if line.len() < 42 { 42 - line.len() } else { 1 };
            writeln!(buf, "{}{:>pad$}{}", line, "", comment, pad = pad).unwrap();
        }
    }

    writeln!(buf, "{:>w$};", "", w = cat_name.len() + 1).unwrap();
    writeln!(buf).unwrap();

    // FIRST set comment
    if let Some(first) = first_set {
        if !first.tokens.is_empty() {
            let tokens: Vec<String> = first
                .tokens
                .iter()
                .map(|t| format_token_name_for_ebnf(t))
                .collect();
            writeln!(buf, "(* FIRST({})  = {{ {} }} *)", cat_name, tokens.join(", ")).unwrap();
        }
    }

    // FOLLOW set comment
    if let Some(follow) = follow_set {
        if !follow.tokens.is_empty() {
            let tokens: Vec<String> = follow
                .tokens
                .iter()
                .map(|t| format_token_name_for_ebnf(t))
                .collect();
            writeln!(buf, "(* FOLLOW({}) = {{ {} }} *)", cat_name, tokens.join(", ")).unwrap();
        }
    }

    writeln!(buf).unwrap();
}

// ══════════════════════════════════════════════════════════════════════════════
// Rule Sorting
// ══════════════════════════════════════════════════════════════════════════════

/// Assign a sort key to a rule for display ordering.
/// Returns (priority, sub_key) where lower priority = displayed first.
fn rule_sort_key(rule: &RuleSpec, bp_table: &BindingPowerTable) -> (u8, u8) {
    if rule.is_literal {
        return (0, 0);
    }
    if rule.is_var {
        return (1, 0);
    }
    // Grouping/structural RD rules (not prefix, not cast)
    if !rule.is_infix && !rule.is_unary_prefix && !rule.is_cast {
        return (2, 0);
    }
    // Unary prefix
    if rule.is_unary_prefix {
        return (3, 0);
    }
    // Cast
    if rule.is_cast {
        return (4, 0);
    }
    // Infix (by binding power)
    if rule.is_infix && !rule.is_postfix {
        let bp = bp_table
            .operators
            .iter()
            .find(|op| op.label == rule.label)
            .map(|op| op.left_bp)
            .unwrap_or(128);
        return (5, bp);
    }
    // Postfix
    if rule.is_postfix {
        let bp = bp_table
            .operators
            .iter()
            .find(|op| op.label == rule.label)
            .map(|op| op.left_bp)
            .unwrap_or(128);
        return (6, bp);
    }
    (7, 0)
}

fn sort_rules_for_display<'a>(
    rules: &[&'a RuleSpec],
    bp_table: &BindingPowerTable,
) -> Vec<(&'a RuleSpec, String)> {
    let mut sorted: Vec<(&RuleSpec, (u8, u8))> = rules
        .iter()
        .map(|r| (*r, rule_sort_key(r, bp_table)))
        .collect();
    sorted.sort_by_key(|(_, key)| *key);
    sorted
        .into_iter()
        .map(|(r, _)| (r, String::new()))
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// Syntax Formatting
// ══════════════════════════════════════════════════════════════════════════════

/// Format the syntax pattern of a rule as an EBNF string.
fn format_syntax(rule: &RuleSpec, _category: &str) -> String {
    if rule.is_literal {
        // Literal rules use the native token
        return format_literal_rule(rule);
    }
    if rule.is_var {
        return "<ident>".to_string();
    }
    if rule.syntax.is_empty() {
        return "?empty?".to_string();
    }

    let items: Vec<String> = rule.syntax.iter().map(format_syntax_item).collect();
    items.join(" ")
}

/// Format a literal rule based on its native type.
fn format_literal_rule(rule: &RuleSpec) -> String {
    // Look at the category's native type to determine which token
    // The label often hints at the type (NumLit, BoolLit, StrLit)
    let label_lower = rule.label.to_lowercase();
    if label_lower.contains("bool") {
        "<boolean>".to_string()
    } else if label_lower.contains("str") {
        "<string>".to_string()
    } else if label_lower.contains("float") {
        "<float>".to_string()
    } else {
        // Default to integer for numeric literals
        "<integer>".to_string()
    }
}

/// Format a single syntax item as EBNF.
fn format_syntax_item(item: &SyntaxItemSpec) -> String {
    match item {
        SyntaxItemSpec::Terminal(t) => format!("\"{}\"", t),
        SyntaxItemSpec::NonTerminal { category, param_name: _ } => category.clone(),
        SyntaxItemSpec::IdentCapture { param_name: _ } => "<ident>".to_string(),
        SyntaxItemSpec::Binder { param_name, category, .. } => {
            format!("^{}:{}", param_name, category)
        },
        SyntaxItemSpec::Collection {
            param_name: _,
            element_category,
            separator,
            kind,
        } => {
            let kind_str = match kind {
                CollectionKind::HashBag => "HashBag",
                CollectionKind::HashSet => "HashSet",
                CollectionKind::Vec => "Vec",
            };
            format!("{{ {} / \"{}\" }}  (* {} *)", element_category, separator, kind_str)
        },
        SyntaxItemSpec::ZipMapSep {
            left_name: _,
            right_name: _,
            left_category: _,
            right_category: _,
            body_items,
            separator,
        } => {
            let body: Vec<String> = body_items.iter().map(format_syntax_item).collect();
            format!("{{ {} / \"{}\" }}", body.join(" "), separator)
        },
        SyntaxItemSpec::BinderCollection { param_name, separator } => {
            format!("{{ ^{} / \"{}\" }}", param_name, separator)
        },
        SyntaxItemSpec::Optional { inner } => {
            let items: Vec<String> = inner.iter().map(format_syntax_item).collect();
            format!("[ {} ]", items.join(" "))
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Rule Annotations
// ══════════════════════════════════════════════════════════════════════════════

/// Format the annotation comment for a rule (label, kind, binding power).
fn format_rule_annotation(
    rule: &RuleSpec,
    bp_table: &BindingPowerTable,
    cross_rules: &[CrossCategoryRule],
    _cast_rules: &[CastRule],
) -> String {
    let label = &rule.label;

    if rule.is_literal {
        return format!("(* {} *)", label);
    }
    if rule.is_var {
        return format!("(* {} *)", label);
    }

    let mut parts: Vec<String> = vec![label.clone()];

    // Prefix operator
    if rule.is_unary_prefix {
        let bp = if let Some(explicit_bp) = rule.prefix_precedence {
            explicit_bp
        } else {
            // Compute max non-postfix infix bp for this category
            let max_non_postfix = bp_table
                .operators
                .iter()
                .filter(|op| op.category == rule.category && !op.is_postfix)
                .map(|op| op.left_bp.max(op.right_bp))
                .max()
                .unwrap_or(0);
            max_non_postfix + 2
        };
        parts.push(format!("prefix bp={}", bp));
        return format!("(* {} *)", parts.join(" — "));
    }

    // Cast rule
    if rule.is_cast {
        if let Some(ref src) = rule.cast_source_category {
            parts.push(format!("cast {} → {}", src, rule.category));
        }
        return format!("(* {} *)", parts.join(" — "));
    }

    // Cross-category rule
    if rule.is_cross_category {
        if let Some(cross) = cross_rules.iter().find(|c| c.label == rule.label) {
            parts.push(format!("cross {} → {}", cross.source_category, cross.result_category));
        }
        // Also show BP if it's an infix cross-category
        if let Some(op) = bp_table.operators.iter().find(|op| op.label == rule.label) {
            parts.push(format!("({}, {})", op.left_bp, op.right_bp));
        }
        return format!("(* {} *)", parts.join(" — "));
    }

    // Postfix operator
    if rule.is_postfix {
        if let Some(op) = bp_table.operators.iter().find(|op| op.label == rule.label) {
            parts.push(format!("postfix bp={}", op.left_bp));
        }
        return format!("(* {} *)", parts.join(" — "));
    }

    // Regular infix operator
    if rule.is_infix {
        if let Some(op) = bp_table.operators.iter().find(|op| op.label == rule.label) {
            let bp_str = format!("({}, {})", op.left_bp, op.right_bp);
            parts.push(bp_str);

            if op.associativity() == Associativity::Right {
                parts.push("right".to_string());
            }
            if op.is_mixfix {
                parts.push("mixfix".to_string());
            }
        }
        return format!("(* {} *)", parts.join(" — "));
    }

    // RD rules (structural: grouping, binder constructs, etc.)
    if rule.has_binder {
        parts.push("binder".to_string());
    }
    if rule.is_collection {
        let kind = rule
            .collection_type
            .map(|k| match k {
                CollectionKind::HashBag => "HashBag",
                CollectionKind::HashSet => "HashSet",
                CollectionKind::Vec => "Vec",
            })
            .unwrap_or("collection");
        parts.push(kind.to_string());
    }

    // Check if this is a grouping rule (pattern like "(" Cat ")")
    if is_grouping_rule(rule) {
        parts.push("group".to_string());
    }

    format!("(* {} *)", parts.join(" — "))
}

/// Check if a rule is a grouping rule: pattern "(" <same-category> ")"
fn is_grouping_rule(rule: &RuleSpec) -> bool {
    if rule.syntax.len() != 3 {
        return false;
    }
    let open = matches!(&rule.syntax[0], SyntaxItemSpec::Terminal(t) if t == "(");
    let inner = matches!(&rule.syntax[1], SyntaxItemSpec::NonTerminal { category, .. } if *category == rule.category);
    let close = matches!(&rule.syntax[2], SyntaxItemSpec::Terminal(t) if t == ")");
    open && inner && close
}

// ══════════════════════════════════════════════════════════════════════════════
// Token Name Formatting
// ══════════════════════════════════════════════════════════════════════════════

/// Convert a FIRST/FOLLOW set token name to a human-readable EBNF representation.
///
/// Maps token variant names (as produced by `terminal_to_variant_name()`) back to
/// their terminal string representation for EBNF display.
fn format_token_name_for_ebnf(token: &str) -> String {
    match token {
        // Special tokens
        "Ident" => "<ident>".to_string(),
        "Integer" => "<integer>".to_string(),
        "Float" => "<float>".to_string(),
        "Boolean" => "<boolean>".to_string(),
        "StringLit" => "<string>".to_string(),
        "Dollar" => "\"$\"".to_string(),
        "DoubleDollar" => "\"$$\"".to_string(),
        "Eof" => "EOF".to_string(),
        // Delimiters
        "LParen" => "\"(\"".to_string(),
        "RParen" => "\")\"".to_string(),
        "LBrace" => "\"{\"".to_string(),
        "RBrace" => "\"}\"".to_string(),
        "LBracket" => "\"[\"".to_string(),
        "RBracket" => "\"]\"".to_string(),
        "EmptyBraces" => "\"{}\"".to_string(),
        // Single-char operators
        "Plus" => "\"+\"".to_string(),
        "Minus" => "\"-\"".to_string(),
        "Star" => "\"*\"".to_string(),
        "Slash" => "\"/\"".to_string(),
        "Percent" => "\"%\"".to_string(),
        "Caret" => "\"^\"".to_string(),
        "Bang" => "\"!\"".to_string(),
        "Question" => "\"?\"".to_string(),
        "Colon" => "\":\"".to_string(),
        "Semi" => "\";\"".to_string(),
        "Comma" => "\",\"".to_string(),
        "Eq" => "\"=\"".to_string(),
        "Pipe" => "\"|\"".to_string(),
        "Amp" => "\"&\"".to_string(),
        "Lt" => "\"<\"".to_string(),
        "Gt" => "\">\"".to_string(),
        "Dot" => "\".\"".to_string(),
        "At" => "\"@\"".to_string(),
        "Tilde" => "\"~\"".to_string(),
        "Hash" => "\"#\"".to_string(),
        // Multi-char operators
        "EqEq" => "\"==\"".to_string(),
        "BangEq" => "\"!=\"".to_string(),
        "LtEq" => "\"<=\"".to_string(),
        "GtEq" => "\">=\"".to_string(),
        "AmpAmp" => "\"&&\"".to_string(),
        "PipePipe" => "\"||\"".to_string(),
        "PlusPlus" => "\"++\"".to_string(),
        "MinusMinus" => "\"--\"".to_string(),
        "StarStar" => "\"**\"".to_string(),
        "Arrow" => "\"->\"".to_string(),
        "FatArrow" => "\"=>\"".to_string(),
        "LArrow" => "\"<-\"".to_string(),
        "ColonColon" => "\"::\"".to_string(),
        "DotDot" => "\"..\"".to_string(),
        "LtLt" => "\"<<\"".to_string(),
        "GtGt" => "\">>\"".to_string(),
        "GtGtGt" => "\">>>\"".to_string(),
        // Dollar tokens: DollarProc → "$proc", DdollarProcLp → "$$proc("
        other if other.starts_with("Ddollar") && other.ends_with("Lp") => {
            let inner = &other[7..other.len() - 2]; // strip "Ddollar" and "Lp"
            format!("\"$${}(\"", inner.to_lowercase())
        },
        other if other.starts_with("Dollar") => {
            let inner = &other[6..]; // strip "Dollar"
            format!("\"${}\"", inner.to_lowercase())
        },
        // Keywords: KwFoo → "foo" (lowercase)
        other if other.starts_with("Kw") => {
            let keyword = &other[2..];
            let lower = keyword.to_lowercase();
            format!("\"{}\"", lower)
        },
        // Hex-encoded terminals: Tok_6c_61_6d_20 → decode bytes to string
        other if other.starts_with("Tok_") => {
            let hex_part = &other[4..]; // skip "Tok_"
            let decoded: String = hex_part
                .split('_')
                .filter(|s| !s.is_empty())
                .filter_map(|hex| u32::from_str_radix(hex, 16).ok())
                .filter_map(char::from_u32)
                .collect();
            if decoded.is_empty() {
                format!("?{}?", other)
            } else {
                format!("\"{}\"", decoded)
            }
        },
        // Fallback: show as-is with special sequence markers
        other => format!("?{}?", other),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Augment a FIRST set with native literal tokens based on native type.
fn augment_first_set_with_native(first_set: &mut FirstSet, native_type: &str) {
    match native_type {
        "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => {
            first_set.insert("Integer");
        },
        "f32" | "f64" => {
            first_set.insert("Float");
        },
        "bool" => {
            first_set.insert("Boolean");
        },
        "str" | "String" => {
            first_set.insert("StringLit");
        },
        _ => {},
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_power::Associativity;
    use crate::pipeline::ParserBundle;
    use crate::{BeamWidthConfig, CategorySpec, LanguageSpec, RuleSpec, SyntaxItemSpec};

    /// Helper: build a default RuleSpec with the given fields.
    fn make_rule(label: &str, category: &str, syntax: Vec<SyntaxItemSpec>) -> RuleSpec {
        RuleSpec {
            label: label.to_string(),
            category: category.to_string(),
            syntax,
            is_infix: false,
            associativity: Associativity::Left,
            is_var: false,
            is_literal: false,
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            is_cross_category: false,
            cross_source_category: None,
            is_cast: false,
            cast_source_category: None,
            is_unary_prefix: false,
            prefix_precedence: None,
            is_postfix: false,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
        }
    }

    /// Build a Calculator LanguageSpec for testing.
    fn calculator_spec() -> LanguageSpec {
        LanguageSpec {
            name: "Calculator".to_string(),
            types: vec![CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: true,
                has_var: true,
            }],
            rules: vec![
                // NumLit
                {
                    let mut r = make_rule("NumLit", "Int", vec![]);
                    r.is_literal = true;
                    r
                },
                // IVar
                {
                    let mut r = make_rule(
                        "IVar",
                        "Int",
                        vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                    );
                    r.is_var = true;
                    r
                },
                // Grouping: "(" Int ")"
                make_rule(
                    "Group",
                    "Int",
                    vec![
                        SyntaxItemSpec::Terminal("(".to_string()),
                        SyntaxItemSpec::NonTerminal {
                            category: "Int".to_string(),
                            param_name: "e".to_string(),
                        },
                        SyntaxItemSpec::Terminal(")".to_string()),
                    ],
                ),
                // Add: Int "+" Int
                {
                    let mut r = make_rule(
                        "Add",
                        "Int",
                        vec![
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "a".to_string(),
                            },
                            SyntaxItemSpec::Terminal("+".to_string()),
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "b".to_string(),
                            },
                        ],
                    );
                    r.is_infix = true;
                    r
                },
                // Sub: Int "-" Int
                {
                    let mut r = make_rule(
                        "Sub",
                        "Int",
                        vec![
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "a".to_string(),
                            },
                            SyntaxItemSpec::Terminal("-".to_string()),
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "b".to_string(),
                            },
                        ],
                    );
                    r.is_infix = true;
                    r
                },
                // Mul: Int "*" Int
                {
                    let mut r = make_rule(
                        "Mul",
                        "Int",
                        vec![
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "a".to_string(),
                            },
                            SyntaxItemSpec::Terminal("*".to_string()),
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "b".to_string(),
                            },
                        ],
                    );
                    r.is_infix = true;
                    r
                },
                // Pow: Int "^" Int (right-associative)
                {
                    let mut r = make_rule(
                        "Pow",
                        "Int",
                        vec![
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "a".to_string(),
                            },
                            SyntaxItemSpec::Terminal("^".to_string()),
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "b".to_string(),
                            },
                        ],
                    );
                    r.is_infix = true;
                    r.associativity = Associativity::Right;
                    r
                },
                // Neg: "-" Int (unary prefix)
                {
                    let mut r = make_rule(
                        "Neg",
                        "Int",
                        vec![
                            SyntaxItemSpec::Terminal("-".to_string()),
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "a".to_string(),
                            },
                        ],
                    );
                    r.is_unary_prefix = true;
                    r
                },
                // Fact: Int "!" (postfix)
                {
                    let mut r = make_rule(
                        "Fact",
                        "Int",
                        vec![
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "a".to_string(),
                            },
                            SyntaxItemSpec::Terminal("!".to_string()),
                        ],
                    );
                    r.is_infix = true;
                    r.is_postfix = true;
                    r
                },
                // Tern: Int "?" Int ":" Int (mixfix)
                {
                    let mut r = make_rule(
                        "Tern",
                        "Int",
                        vec![
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "c".to_string(),
                            },
                            SyntaxItemSpec::Terminal("?".to_string()),
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "t".to_string(),
                            },
                            SyntaxItemSpec::Terminal(":".to_string()),
                            SyntaxItemSpec::NonTerminal {
                                category: "Int".to_string(),
                                param_name: "e".to_string(),
                            },
                        ],
                    );
                    r.is_infix = true;
                    r
                },
            ],
            beam_width: BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            dispatch_strategy: crate::DispatchStrategy::Static,
        }
    }

    /// Build a ParserBundle from a LanguageSpec using the pipeline extraction.
    /// This calls the same logic as the pipeline but gives us the bundle for testing.
    fn build_bundle(spec: &LanguageSpec) -> ParserBundle {
        // We can't call extract_from_spec directly (it's private),
        // so we use run_pipeline logic. Instead, we replicate the extraction
        // inline for testing purposes.
        use crate::binding_power::{analyze_binding_powers, InfixRuleInfo};
        use crate::dispatch::{CastRule, CrossCategoryRule};
        use crate::prediction::{FirstItem, FollowSetInput, RuleInfo};
        use crate::recursive::RDRuleInfo;
        use std::collections::BTreeMap;

        let categories: Vec<CategoryInfo> = spec
            .types
            .iter()
            .enumerate()
            .map(|(i, t)| CategoryInfo {
                name: t.name.clone(),
                native_type: t.native_type.clone(),
                is_primary: i == 0,
                has_var: t.has_var,
            })
            .collect();

        let category_names: Vec<String> = categories.iter().map(|c| c.name.clone()).collect();

        let infix_rules: Vec<InfixRuleInfo> = spec
            .rules
            .iter()
            .filter(|r| r.is_infix)
            .map(|r| {
                let (is_mixfix, mixfix_parts) = detect_mixfix(r);
                InfixRuleInfo {
                    label: r.label.clone(),
                    terminal: r
                        .syntax
                        .iter()
                        .find_map(|item| {
                            if let SyntaxItemSpec::Terminal(t) = item {
                                Some(t.clone())
                            } else {
                                None
                            }
                        })
                        .unwrap_or_default(),
                    category: r.category.clone(),
                    result_category: r.category.clone(),
                    associativity: r.associativity,
                    is_cross_category: r.is_cross_category,
                    is_postfix: r.is_postfix,
                    is_mixfix,
                    mixfix_parts,
                }
            })
            .collect();

        let bp_table = analyze_binding_powers(&infix_rules);

        let max_infix_bp: BTreeMap<String, u8> = {
            let mut map = BTreeMap::new();
            for op in &bp_table.operators {
                if op.is_postfix {
                    continue;
                }
                let max = map.entry(op.category.clone()).or_insert(0u8);
                *max = (*max).max(op.left_bp).max(op.right_bp);
            }
            map
        };

        let rule_infos: Vec<RuleInfo> = spec
            .rules
            .iter()
            .map(|r| RuleInfo {
                label: r.label.clone(),
                category: r.category.clone(),
                first_items: r
                    .syntax
                    .iter()
                    .take(1)
                    .map(|item| match item {
                        SyntaxItemSpec::Terminal(t) => FirstItem::Terminal(t.clone()),
                        SyntaxItemSpec::NonTerminal { category, .. } => {
                            if category_names.contains(category) {
                                FirstItem::NonTerminal(category.clone())
                            } else {
                                FirstItem::Ident
                            }
                        },
                        _ => FirstItem::Ident,
                    })
                    .collect(),
                is_infix: r.is_infix,
                is_var: r.is_var,
                is_literal: r.is_literal,
                is_cross_category: r.is_cross_category,
                is_cast: r.is_cast,
            })
            .collect();

        let follow_inputs: Vec<FollowSetInput> = spec
            .rules
            .iter()
            .map(|r| FollowSetInput {
                category: r.category.clone(),
                syntax: r.syntax.clone(),
            })
            .collect();

        let rd_rules: Vec<RDRuleInfo> = spec
            .rules
            .iter()
            .filter(|r| !r.is_infix && !r.is_var && !r.is_literal)
            .map(|rule| {
                let prefix_bp = if rule.is_unary_prefix {
                    if let Some(explicit_bp) = rule.prefix_precedence {
                        Some(explicit_bp)
                    } else {
                        let cat_max = max_infix_bp.get(&rule.category).copied().unwrap_or(0);
                        Some(cat_max + 2)
                    }
                } else {
                    None
                };

                RDRuleInfo {
                    label: rule.label.clone(),
                    category: rule.category.clone(),
                    items: rule.syntax.iter().map(convert_syntax_item).collect(),
                    has_binder: rule.has_binder,
                    has_multi_binder: rule.has_multi_binder,
                    is_collection: rule.is_collection,
                    collection_type: rule.collection_type,
                    separator: rule.separator.clone(),
                    prefix_bp,
                    eval_mode: rule.eval_mode.clone(),
                }
            })
            .collect();

        let cross_rules: Vec<CrossCategoryRule> = spec
            .rules
            .iter()
            .filter(|r| r.is_cross_category)
            .map(|r| CrossCategoryRule {
                label: r.label.clone(),
                source_category: r.cross_source_category.clone().unwrap_or_default(),
                result_category: r.category.clone(),
                operator: r
                    .syntax
                    .iter()
                    .find_map(|item| {
                        if let SyntaxItemSpec::Terminal(t) = item {
                            Some(t.clone())
                        } else {
                            None
                        }
                    })
                    .unwrap_or_default(),
                needs_backtrack: false,
            })
            .collect();

        let cast_rules: Vec<CastRule> = spec
            .rules
            .iter()
            .filter(|r| r.is_cast)
            .map(|r| CastRule {
                label: r.label.clone(),
                source_category: r.cast_source_category.clone().unwrap_or_default(),
                target_category: r.category.clone(),
            })
            .collect();

        let has_binders = spec
            .rules
            .iter()
            .any(|r| r.has_binder || r.has_multi_binder);

        ParserBundle {
            categories,
            bp_table,
            rule_infos,
            follow_inputs,
            rd_rules,
            cross_rules,
            cast_rules,
            has_binders,
            beam_width: crate::BeamWidthConfig::Disabled,
            dispatch_strategy: crate::DispatchStrategy::Static,
        }
    }

    fn detect_mixfix(rule: &RuleSpec) -> (bool, Vec<crate::binding_power::MixfixPart>) {
        let operand_count = rule
            .syntax
            .iter()
            .filter(|item| matches!(item, SyntaxItemSpec::NonTerminal { .. }))
            .count();
        let terminal_count = rule
            .syntax
            .iter()
            .filter(|item| matches!(item, SyntaxItemSpec::Terminal(_)))
            .count();

        if operand_count < 3 || terminal_count < 2 {
            return (false, Vec::new());
        }

        let mut parts = Vec::with_capacity(operand_count - 1);
        let mut after_trigger = false;
        let mut skip_count = 0;

        for item in &rule.syntax {
            match item {
                SyntaxItemSpec::NonTerminal { .. } if skip_count == 0 => {
                    skip_count += 1;
                },
                SyntaxItemSpec::Terminal(_) if !after_trigger => {
                    after_trigger = true;
                },
                SyntaxItemSpec::NonTerminal { category, param_name } if after_trigger => {
                    parts.push(crate::binding_power::MixfixPart {
                        operand_category: category.clone(),
                        param_name: param_name.clone(),
                        following_terminal: None,
                    });
                },
                SyntaxItemSpec::Terminal(t) if after_trigger => {
                    if let Some(last_part) = parts.last_mut() {
                        last_part.following_terminal = Some(t.clone());
                    }
                },
                _ => {},
            }
        }

        (true, parts)
    }

    fn convert_syntax_item(item: &SyntaxItemSpec) -> RDSyntaxItem {
        match item {
            SyntaxItemSpec::Terminal(t) => RDSyntaxItem::Terminal(t.clone()),
            SyntaxItemSpec::NonTerminal { category, param_name } => RDSyntaxItem::NonTerminal {
                category: category.clone(),
                param_name: param_name.clone(),
            },
            SyntaxItemSpec::IdentCapture { param_name } => {
                RDSyntaxItem::IdentCapture { param_name: param_name.clone() }
            },
            SyntaxItemSpec::Binder { param_name, category, .. } => RDSyntaxItem::Binder {
                param_name: param_name.clone(),
                binder_category: category.clone(),
            },
            SyntaxItemSpec::Collection {
                param_name,
                element_category,
                separator,
                kind,
            } => RDSyntaxItem::Collection {
                param_name: param_name.clone(),
                element_category: element_category.clone(),
                separator: separator.clone(),
                kind: *kind,
            },
            SyntaxItemSpec::ZipMapSep {
                left_name,
                right_name,
                left_category,
                right_category,
                body_items,
                separator,
            } => RDSyntaxItem::ZipMapSep {
                left_name: left_name.clone(),
                right_name: right_name.clone(),
                left_category: left_category.clone(),
                right_category: right_category.clone(),
                body_items: body_items.iter().map(convert_syntax_item).collect(),
                separator: separator.clone(),
            },
            SyntaxItemSpec::BinderCollection { param_name, separator } => {
                RDSyntaxItem::BinderCollection {
                    param_name: param_name.clone(),
                    separator: separator.clone(),
                }
            },
            SyntaxItemSpec::Optional { inner } => RDSyntaxItem::Optional {
                inner: inner.iter().map(convert_syntax_item).collect(),
            },
        }
    }

    // ── Snapshot test ──────────────────────────────────────────────────────

    #[test]
    fn test_ebnf_calculator_snapshot() {
        let spec = calculator_spec();
        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        // Header
        assert!(
            ebnf.contains("Calculator — EBNF Grammar"),
            "should contain language name in header"
        );
        assert!(ebnf.contains("Generated by PraTTaIL"), "should contain generator attribution");

        // Lexical tokens
        assert!(ebnf.contains("<integer>"), "should contain integer token: {}", ebnf);
        assert!(ebnf.contains("<ident>"), "should contain ident token: {}", ebnf);

        // Category production
        assert!(ebnf.contains("Int ="), "should contain Int production: {}", ebnf);

        // Rule labels in annotations
        assert!(ebnf.contains("NumLit"), "should contain NumLit label: {}", ebnf);
        assert!(ebnf.contains("Add"), "should contain Add label: {}", ebnf);
        assert!(ebnf.contains("Mul"), "should contain Mul label: {}", ebnf);
    }

    // ── Precedence table ───────────────────────────────────────────────────

    #[test]
    fn test_ebnf_contains_precedence_table() {
        let spec = calculator_spec();
        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        assert!(
            ebnf.contains("Precedence Table: Int"),
            "should contain precedence table header: {}",
            ebnf
        );
        assert!(ebnf.contains("BP"), "should contain BP column header: {}", ebnf);
        assert!(ebnf.contains("Assoc"), "should contain Assoc column header: {}", ebnf);
    }

    // ── FIRST/FOLLOW sets ──────────────────────────────────────────────────

    #[test]
    fn test_ebnf_contains_first_follow() {
        let spec = calculator_spec();
        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        assert!(ebnf.contains("FIRST(Int)"), "should contain FIRST set: {}", ebnf);
        assert!(ebnf.contains("FOLLOW(Int)"), "should contain FOLLOW set: {}", ebnf);
    }

    // ── Binder notation ────────────────────────────────────────────────────

    #[test]
    fn test_ebnf_binder_notation() {
        let spec = LanguageSpec {
            name: "Lambda".to_string(),
            types: vec![CategorySpec {
                name: "Term".to_string(),
                native_type: None,
                is_primary: true,
                has_var: true,
            }],
            rules: vec![
                {
                    let mut r = make_rule(
                        "TVar",
                        "Term",
                        vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                    );
                    r.is_var = true;
                    r
                },
                // Lam: "lam " ^x:Term "." Term
                {
                    let mut r = make_rule(
                        "Lam",
                        "Term",
                        vec![
                            SyntaxItemSpec::Terminal("lam ".to_string()),
                            SyntaxItemSpec::Binder {
                                param_name: "x".to_string(),
                                category: "Term".to_string(),
                                is_multi: false,
                            },
                            SyntaxItemSpec::Terminal(".".to_string()),
                            SyntaxItemSpec::NonTerminal {
                                category: "Term".to_string(),
                                param_name: "body".to_string(),
                            },
                        ],
                    );
                    r.has_binder = true;
                    r
                },
            ],
            beam_width: BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            dispatch_strategy: crate::DispatchStrategy::Static,
        };

        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        assert!(ebnf.contains("^x:Term"), "should contain binder notation ^x:Term: {}", ebnf);
        assert!(ebnf.contains("binder"), "should contain binder annotation: {}", ebnf);
    }

    // ── Collection notation ────────────────────────────────────────────────

    #[test]
    fn test_ebnf_collection_notation() {
        let spec = LanguageSpec {
            name: "ListLang".to_string(),
            types: vec![
                CategorySpec {
                    name: "Proc".to_string(),
                    native_type: None,
                    is_primary: true,
                    has_var: true,
                },
                CategorySpec {
                    name: "Name".to_string(),
                    native_type: None,
                    is_primary: false,
                    has_var: true,
                },
            ],
            rules: vec![
                {
                    let mut r = make_rule(
                        "PVar",
                        "Proc",
                        vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                    );
                    r.is_var = true;
                    r
                },
                {
                    let mut r = make_rule(
                        "NVar",
                        "Name",
                        vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                    );
                    r.is_var = true;
                    r
                },
                // ListProc: "[" { Proc / "," } "]"
                {
                    let mut r = make_rule(
                        "ListProc",
                        "Proc",
                        vec![
                            SyntaxItemSpec::Terminal("[".to_string()),
                            SyntaxItemSpec::Collection {
                                param_name: "ps".to_string(),
                                element_category: "Proc".to_string(),
                                separator: ",".to_string(),
                                kind: CollectionKind::Vec,
                            },
                            SyntaxItemSpec::Terminal("]".to_string()),
                        ],
                    );
                    r.is_collection = true;
                    r.collection_type = Some(CollectionKind::Vec);
                    r.separator = Some(",".to_string());
                    r
                },
            ],
            beam_width: BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            dispatch_strategy: crate::DispatchStrategy::Static,
        };

        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        assert!(
            ebnf.contains("{ Proc / \",\" }"),
            "should contain collection notation {{ Proc / \",\" }}: {}",
            ebnf
        );
        assert!(ebnf.contains("Vec"), "should contain Vec kind annotation: {}", ebnf);
    }

    // ── Optional notation ──────────────────────────────────────────────────

    #[test]
    fn test_ebnf_optional_notation() {
        let spec = LanguageSpec {
            name: "OptLang".to_string(),
            types: vec![CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: true,
                has_var: true,
            }],
            rules: vec![
                {
                    let mut r = make_rule("NumLit", "Int", vec![]);
                    r.is_literal = true;
                    r
                },
                {
                    let mut r = make_rule(
                        "IVar",
                        "Int",
                        vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                    );
                    r.is_var = true;
                    r
                },
                // IfExpr: "if" Int [ "else" Int ]
                make_rule(
                    "IfExpr",
                    "Int",
                    vec![
                        SyntaxItemSpec::Terminal("if".to_string()),
                        SyntaxItemSpec::NonTerminal {
                            category: "Int".to_string(),
                            param_name: "cond".to_string(),
                        },
                        SyntaxItemSpec::Optional {
                            inner: vec![
                                SyntaxItemSpec::Terminal("else".to_string()),
                                SyntaxItemSpec::NonTerminal {
                                    category: "Int".to_string(),
                                    param_name: "alt".to_string(),
                                },
                            ],
                        },
                    ],
                ),
            ],
            beam_width: BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            dispatch_strategy: crate::DispatchStrategy::Static,
        };

        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        assert!(
            ebnf.contains("[ \"else\" Int ]"),
            "should contain optional notation [ \"else\" Int ]: {}",
            ebnf
        );
    }

    // ── Postfix annotation ─────────────────────────────────────────────────

    #[test]
    fn test_ebnf_postfix_annotation() {
        let spec = calculator_spec();
        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        assert!(ebnf.contains("postfix"), "should contain postfix annotation: {}", ebnf);
        assert!(ebnf.contains("Fact"), "should contain Fact label: {}", ebnf);
    }

    // ── Right-associativity annotation ──────────────────────────────────────

    #[test]
    fn test_ebnf_right_assoc_annotation() {
        let spec = calculator_spec();
        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        // Pow should be marked as right-associative
        assert!(ebnf.contains("right"), "should contain right-assoc annotation: {}", ebnf);
    }

    // ── Mixfix annotation ──────────────────────────────────────────────────

    #[test]
    fn test_ebnf_mixfix_annotation() {
        let spec = calculator_spec();
        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        assert!(ebnf.contains("mixfix"), "should contain mixfix annotation: {}", ebnf);
        assert!(ebnf.contains("Tern"), "should contain Tern label: {}", ebnf);
    }

    // ── Grouping annotation ────────────────────────────────────────────────

    #[test]
    fn test_ebnf_grouping_annotation() {
        let spec = calculator_spec();
        let bundle = build_bundle(&spec);
        let ebnf = format_ebnf(&spec, &bundle);

        assert!(ebnf.contains("group"), "should contain group annotation: {}", ebnf);
        assert!(ebnf.contains("\"(\" Int \")\""), "should contain grouping syntax: {}", ebnf);
    }
}
