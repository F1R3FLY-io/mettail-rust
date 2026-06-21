use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// Diagnostic Grouping
// ══════════════════════════════════════════════════════════════════════════════

/// Group repeated lint diagnostics into compact summaries.
///
/// Partitions input by lint ID. Known groupable IDs delegate to per-ID
/// groupers; all other IDs pass through unchanged. Single-item groups
/// always pass through unchanged. Grouped results replace the **first
/// occurrence** position of each grouped ID, preserving relative ordering.
pub fn group_diagnostics(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    if diagnostics.len() <= 1 {
        return diagnostics;
    }

    // Partition by lint ID, tracking first-occurrence index per ID
    let mut by_id: BTreeMap<DiagnosticId, Vec<LintDiagnostic>> = BTreeMap::new();
    let mut first_index: HashMap<DiagnosticId, usize> = HashMap::new();
    let mut non_groupable: Vec<(usize, LintDiagnostic)> = Vec::new();

    for (i, diag) in diagnostics.into_iter().enumerate() {
        if diag.id.is_groupable() {
            first_index.entry(diag.id).or_insert(i);
            by_id.entry(diag.id).or_default().push(diag);
        } else {
            non_groupable.push((i, diag));
        }
    }

    // Build grouped results with their first-occurrence index
    let mut indexed: Vec<(usize, Vec<LintDiagnostic>)> = Vec::new();

    for (id, items) in by_id {
        let idx = first_index[&id];
        if items.len() == 1 {
            indexed.push((idx, items));
        } else {
            let grouped = match id {
                DiagnosticId::W01 => group_w01(items),
                DiagnosticId::W02 => group_w02(items),
                DiagnosticId::W03 => group_w03(items),
                DiagnosticId::W05 => group_w05(items),
                DiagnosticId::W07 => group_w07(items),
                DiagnosticId::G03 => group_g03(items),
                DiagnosticId::G08 => group_g08(items),
                DiagnosticId::G27 => group_g27(items),
                DiagnosticId::D01 => group_ambiguity_by_category(
                    DiagnosticId::D01,
                    "precision-ambiguity",
                    "precision ambiguity",
                    items,
                ),
                DiagnosticId::D02 => group_ambiguity_by_category(
                    DiagnosticId::D02,
                    "unresolvable-ambiguity",
                    "unresolvable ambiguity",
                    items,
                ),
                DiagnosticId::D03 => group_ambiguity_by_category(
                    DiagnosticId::D03,
                    "trie-unreachable-rule",
                    "unreachable trie rule(s)",
                    items,
                ),
                DiagnosticId::D08 => group_ambiguity_by_category(
                    DiagnosticId::D08,
                    "optimization-suggestion",
                    "optimization suggestion(s)",
                    items,
                ),
                DiagnosticId::D09 => group_ambiguity_by_category(
                    DiagnosticId::D09,
                    "conflict-resolution-guide",
                    "conflict resolution guidance",
                    items,
                ),
                DiagnosticId::A01 => group_a01(items),
                DiagnosticId::A04 => group_a04(items),
                DiagnosticId::A08 => group_a08(items),
                DiagnosticId::CAP03 => group_cap03(items),
                DiagnosticId::CAP05 => group_cap05(items),
                DiagnosticId::DIS01 => group_dis01(items),
                // Stage 10c (2026-05-04): W10 + W14 dispatch arms removed.
                DiagnosticId::W12 => group_w12(items),
                // Lint-B cleanup groupers for high-volume IDs.
                DiagnosticId::M01 => group_m01(items),
                DiagnosticId::K01 => group_k01(items),
                DiagnosticId::SYM02 => group_sym02(items),
                DiagnosticId::N02 => group_n02(items),
                DiagnosticId::N05 => group_n05(items),
                _ => items, // unreachable due to is_groupable() check
            };
            indexed.push((idx, grouped));
        }
    }

    // Merge non-groupable items
    for (i, diag) in non_groupable {
        indexed.push((i, vec![diag]));
    }

    // Sort by first-occurrence index to preserve relative ordering
    indexed.sort_by_key(|(i, _)| *i);
    indexed.into_iter().flat_map(|(_, diags)| diags).collect()
}

/// Group W01 (dead-rule) diagnostics by hint text (= warning type), then by category.
///
/// Output: `"N rules are unreachable...\n  Cat1: R1, R2\n  Cat2: R3"`
pub(crate) fn group_w01(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    // Group by hint text (each hint corresponds to a different dead-rule tier)
    let mut by_hint: BTreeMap<String, Vec<LintDiagnostic>> = BTreeMap::new();
    for diag in diagnostics {
        let key = diag.hint.clone().unwrap_or_default();
        by_hint.entry(key).or_default().push(diag);
    }

    let mut result = Vec::new();
    for (hint_key, items) in by_hint {
        if items.len() == 1 {
            result.extend(items);
            continue;
        }

        // Sub-group by category
        let mut by_cat: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for diag in &items {
            let cat = diag
                .category
                .clone()
                .unwrap_or_else(|| "unknown".to_string());
            let rule = diag.rule.clone().unwrap_or_else(|| "?".to_string());
            by_cat.entry(cat).or_default().push(rule);
        }

        let total = items.len();
        let cat_lines: Vec<String> = by_cat
            .iter()
            .map(|(cat, rules)| format!("  {}: {}", cat, rules.join(", ")))
            .collect();

        let first = &items[0];
        result.push(LintDiagnostic {
            id: first.id,
            name: first.name,
            severity: first.severity,
            category: None,
            rule: None,
            message: format!(
                "{} rules are unreachable (dead code)\n{}",
                total,
                cat_lines.join("\n"),
            ),
            hint: Some(hint_key),
            grammar_name: first.grammar_name.clone(),
            source_location: None,
        });
    }
    result
}

/// Group W02 (nfa-ambiguous-prefix) by category.
///
/// Output: `"ambiguous prefix dispatch in N categories\n  Cat: token matches [R1, R2]; ..."`
pub(crate) fn group_w02(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    group_ambiguity_by_category(
        DiagnosticId::W02,
        "nfa-ambiguous-prefix",
        "ambiguous NFA prefix dispatch",
        diagnostics,
    )
}

/// Group W03 (high-ambiguity-token) by category.
pub(crate) fn group_w03(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    group_ambiguity_by_category(
        DiagnosticId::W03,
        "high-ambiguity-token",
        "high-ambiguity tokens",
        diagnostics,
    )
}

/// Group W05 (composed-dispatch-ambiguity) by category.
///
/// Output: `"N ambiguities resolved by tropical shortest path\n  Cat: details..."`
pub(crate) fn group_w05(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    let mut by_cat: BTreeMap<String, Vec<LintDiagnostic>> = BTreeMap::new();
    for diag in diagnostics {
        let cat = diag
            .category
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        by_cat.entry(cat).or_default().push(diag);
    }

    // If only one category with one item, pass through
    if by_cat.len() == 1 && by_cat.values().next().map_or(false, |v| v.len() == 1) {
        return by_cat.into_values().flatten().collect();
    }

    let total: usize = by_cat.values().map(|v| v.len()).sum();
    let first = by_cat.values().next().and_then(|v| v.first());
    let (grammar_name, hint) = match first {
        Some(d) => (d.grammar_name.clone(), d.hint.clone()),
        None => return Vec::new(),
    };

    // Build per-category summary lines
    let mut cat_lines: Vec<String> = Vec::new();
    for (cat, items) in &by_cat {
        let summaries: Vec<String> = items
            .iter()
            .filter_map(|d| {
                // Extract winner from message: "Resolved by tropical shortest path → WINNER"
                let msg = &d.message;
                let winner = msg.rsplit("→ ").next().unwrap_or("?").trim();
                // Extract token entries: lines starting with "  - Token::"
                let entries: Vec<&str> = msg
                    .lines()
                    .filter(|l| l.trim_start().starts_with("- Token::"))
                    .collect();
                if entries.is_empty() {
                    return None;
                }
                // Summarize: "Token1→Rule1, Token2→Rule2 (vs Loser, wt X.XX)"
                let mut parts = Vec::new();
                let mut losers = Vec::new();
                for entry in &entries {
                    // Format: "  - Token::Variant → rule Label (weight X.XX)"
                    let trimmed = entry.trim_start().trim_start_matches("- Token::");
                    if let Some((variant_rule, weight_part)) = trimmed.split_once(" (weight ") {
                        let weight = weight_part.trim_end_matches(')');
                        if let Some((variant, rule)) = variant_rule.split_once(" → rule ") {
                            if rule.trim() == winner {
                                parts.push(format!("{}→{}", variant.trim(), rule.trim()));
                            } else {
                                losers.push(format!("{} wt {}", rule.trim(), weight));
                            }
                        }
                    }
                }
                let vs_str = if losers.is_empty() {
                    String::new()
                } else {
                    format!(" (vs {})", losers.join(", "))
                };
                if parts.is_empty() {
                    Some(format!("→ {}{}", winner, vs_str))
                } else {
                    Some(format!("{}{}", parts.join(", "), vs_str))
                }
            })
            .collect();
        cat_lines.push(format!("  {}: {}", cat, summaries.join("; ")));
    }

    vec![LintDiagnostic {
        id: DiagnosticId::W05,
        name: "composed-dispatch-ambiguity",
        severity: LintSeverity::Warning,
        category: None,
        rule: None,
        message: format!(
            "{} ambiguities resolved by tropical shortest path\n{}",
            total,
            cat_lines.join("\n"),
        ),
        hint,
        grammar_name,
        source_location: None,
    }]
}

/// Group W07 (nearly-dead-path) by category.
///
/// Output: `"N rules on nearly-dead paths\n  Cat: R1, R2"`
pub(crate) fn group_w07(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    let mut by_cat: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for diag in &diagnostics {
        let cat = diag
            .category
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        let rule = diag.rule.clone().unwrap_or_else(|| "?".to_string());
        by_cat.entry(cat).or_default().push(rule);
    }

    let total = diagnostics.len();
    let first = &diagnostics[0];

    let cat_lines: Vec<String> = by_cat
        .iter()
        .map(|(cat, rules)| format!("  {}: {}", cat, rules.join(", ")))
        .collect();

    vec![LintDiagnostic {
        id: first.id,
        name: first.name,
        severity: first.severity,
        category: None,
        rule: None,
        message: format!("{} rules on nearly-dead paths\n{}", total, cat_lines.join("\n"),),
        hint: first.hint.clone(),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

/// Group G03 (ambiguous-prefix) by category.
///
/// Output: `"ambiguous prefix dispatch in N categories\n  Cat: token1 matches [R1, R2]; ..."`
pub(crate) fn group_g03(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    group_ambiguity_by_category(
        DiagnosticId::G03,
        "ambiguous-prefix",
        "ambiguous prefix dispatch",
        diagnostics,
    )
}

/// Group G08 (missing-cast-to-root) into a single diagnostic listing all isolated categories.
///
/// Output: `"N categories have no value-flow path to primary\n  isolated: Cat1, Cat2, Cat3"`
pub(crate) fn group_g08(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    let cats: Vec<String> = diagnostics
        .iter()
        .filter_map(|d| d.category.clone())
        .collect();

    let first = &diagnostics[0];

    // Extract primary category from the first diagnostic's message
    let primary = first
        .message
        .rsplit("to primary category `")
        .next()
        .and_then(|s| s.strip_suffix('`'))
        .unwrap_or("?");

    vec![LintDiagnostic {
        id: first.id,
        name: first.name,
        severity: first.severity,
        category: None,
        rule: None,
        message: format!(
            "{} categories have no value-flow path to primary category `{}`\n  isolated: {}",
            cats.len(),
            primary,
            cats.join(", "),
        ),
        hint: Some(format!(
            "add cast/cross-category rules or syntax embeddings from these categories to `{}` or an intermediate category",
            primary,
        )),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

/// Group G27 (rule-subsumption-candidate) by general rule name (from the `rule` field).
///
/// Output: `"N rules may be subsumed by more general rule `General`\n  candidates: R1, R2"`
pub(crate) fn group_g27(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    // Group by general rule name (extracted from message)
    let mut by_general: BTreeMap<String, Vec<LintDiagnostic>> = BTreeMap::new();
    for diag in diagnostics {
        // Extract general rule name: "... subsumed by more general rule `GENERAL` ..."
        let general = diag
            .message
            .split("more general rule `")
            .nth(1)
            .and_then(|s| s.split('`').next())
            .unwrap_or("?")
            .to_string();
        by_general.entry(general).or_default().push(diag);
    }

    let mut result = Vec::new();
    for (general_name, items) in by_general {
        if items.len() == 1 {
            result.extend(items);
            continue;
        }

        // Collect specific rule names from messages
        let specific_names: Vec<String> = items
            .iter()
            .filter_map(|d| {
                // "rule `SPECIFIC` may be subsumed..."
                d.message
                    .split("rule `")
                    .nth(1)
                    .and_then(|s| s.split('`').next())
                    .map(|s| s.to_string())
            })
            .collect();

        let first = &items[0];
        result.push(LintDiagnostic {
            id: first.id,
            name: first.name,
            severity: first.severity,
            category: None,
            rule: None,
            message: format!(
                "{} rules may be subsumed by more general rule `{}`\n  candidates: {}",
                items.len(),
                general_name,
                specific_names.join(", "),
            ),
            hint: Some(format!(
                "review whether these rules can be removed or merged with `{}`",
                general_name,
            )),
            grammar_name: first.grammar_name.clone(),
            source_location: None,
        });
    }
    result
}

/// Shared helper for grouping ambiguity-style diagnostics (W02, W03, G03) by category.
///
/// Each diagnostic's message is preserved as a sub-item under its category.
pub(crate) fn group_ambiguity_by_category(
    id: DiagnosticId,
    name: &'static str,
    description: &str,
    diagnostics: Vec<LintDiagnostic>,
) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    let mut by_cat: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for diag in &diagnostics {
        let cat = diag
            .category
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        by_cat.entry(cat).or_default().push(diag.message.clone());
    }

    let total = diagnostics.len();
    let first = &diagnostics[0];

    let cat_lines: Vec<String> = by_cat
        .iter()
        .map(|(cat, msgs)| {
            if msgs.len() == 1 {
                format!("  {}: {}", cat, msgs[0])
            } else {
                let items: Vec<String> = msgs
                    .iter()
                    .enumerate()
                    .map(|(i, m)| format!("  {}[{}]: {}", cat, i + 1, m))
                    .collect();
                items.join("\n")
            }
        })
        .collect();

    vec![LintDiagnostic {
        id,
        name,
        severity: first.severity,
        category: None,
        rule: None,
        message: format!(
            "{} {} in {} categories\n{}",
            total,
            description,
            by_cat.len(),
            cat_lines.join("\n"),
        ),
        hint: first.hint.clone(),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

/// Group A01 (unbounded term growth) by category.
///
/// Output: `"N rules have potential unbounded term growth: Cat1(Rule1, Rule2), Cat2(Rule3)"`
pub(crate) fn group_a01(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    // Separate individual rule diagnostics (have category+rule) from summary diagnostics
    let mut rule_diags = Vec::new();
    let mut summary_diags = Vec::new();
    for diag in diagnostics {
        if diag.category.is_some() && diag.rule.is_some() {
            rule_diags.push(diag);
        } else {
            summary_diags.push(diag);
        }
    }

    let mut result = Vec::new();

    // Group individual rule diagnostics by category
    if !rule_diags.is_empty() {
        let grammar_name = rule_diags.first().and_then(|d| d.grammar_name.clone());
        let hint = rule_diags.first().and_then(|d| d.hint.clone());

        let mut by_cat: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for diag in &rule_diags {
            let cat = diag
                .category
                .clone()
                .unwrap_or_else(|| "unknown".to_string());
            let rule = diag.rule.clone().unwrap_or_else(|| "?".to_string());
            by_cat.entry(cat).or_default().push(rule);
        }

        let total = rule_diags.len();
        let cat_parts: Vec<String> = by_cat
            .iter()
            .map(|(cat, rules)| format!("{}({})", cat, rules.join(", ")))
            .collect();

        result.push(LintDiagnostic {
            id: DiagnosticId::A01,
            name: "unbounded-term-growth",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "{} rules have potential unbounded term growth: {}",
                total,
                cat_parts.join(", "),
            ),
            hint,
            grammar_name,
            source_location: None,
        });
    }

    // Pass through summary diagnostics unchanged
    result.extend(summary_diags);
    result
}

/// Group A04 (high dependency group count) by category.
///
/// Output: `"N constructors in 3+ dependency groups: Cat1(Ctor1), Cat2(Ctor2)"`
pub(crate) fn group_a04(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    let grammar_name = diagnostics.first().and_then(|d| d.grammar_name.clone());
    let severity = diagnostics
        .first()
        .map(|d| d.severity)
        .unwrap_or(LintSeverity::Warning);

    let mut by_cat: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for diag in &diagnostics {
        let cat = diag
            .category
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        // Extract constructor name from backtick-quoted name in message:
        // "constructor `Foo` appears in N dependency groups ..."
        let ctor = diag
            .message
            .split("constructor `")
            .nth(1)
            .and_then(|s| s.split('`').next())
            .unwrap_or("?")
            .to_string();
        by_cat.entry(cat).or_default().push(ctor);
    }

    let total = diagnostics.len();
    let cat_parts: Vec<String> = by_cat
        .iter()
        .map(|(cat, ctors)| format!("{}({})", cat, ctors.join(", ")))
        .collect();

    vec![LintDiagnostic {
        id: DiagnosticId::A04,
        name: "high-dependency-constructors",
        severity,
        category: None,
        rule: None,
        message: format!(
            "{} constructors appear in 3+ equation/rewrite groups (risk of equivalence class explosion): {}",
            total,
            cat_parts.join(", "),
        ),
        hint: Some(
            "these constructors are referenced by many equations/rewrites, which can cause \
             equivalence class explosion during Ascent fixpoint evaluation; consider \
             reducing the number of equations involving them, or simplifying \
             equational axioms (e.g., removing redundant commutativity/associativity declarations)"
                .to_string(),
        ),
        grammar_name,
        source_location: None,
    }]
}

/// Group A08 (equation-subsumed rewrites) by category.
///
/// Output: `"N constructors may have equation-subsumed rewrites: Cat1(Ctor1, Ctor2), Cat2(Ctor3)"`
pub(crate) fn group_a08(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    let grammar_name = diagnostics.first().and_then(|d| d.grammar_name.clone());
    let hint = diagnostics.first().and_then(|d| d.hint.clone());
    let severity = diagnostics
        .first()
        .map(|d| d.severity)
        .unwrap_or(LintSeverity::Note);

    let mut by_cat: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for diag in &diagnostics {
        let cat = diag
            .category
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        // Extract constructor name from: "constructor `Foo` appears in N dependency groups"
        let ctor = diag
            .message
            .split("constructor `")
            .nth(1)
            .and_then(|s| s.split('`').next())
            .unwrap_or("?")
            .to_string();
        by_cat.entry(cat).or_default().push(ctor);
    }

    let total = diagnostics.len();
    let cat_parts: Vec<String> = by_cat
        .iter()
        .map(|(cat, ctors)| format!("{}({})", cat, ctors.join(", ")))
        .collect();

    vec![LintDiagnostic {
        id: DiagnosticId::A08,
        name: "equation-subsumed-rewrites",
        severity,
        category: None,
        rule: None,
        message: format!(
            "{} constructors may have equation-subsumed rewrites: {}",
            total,
            cat_parts.join(", "),
        ),
        hint,
        grammar_name,
        source_location: None,
    }]
}

/// Group C-AP03 (deep congruence chains) by category.
///
/// Extracts category names from the message text (backtick-quoted after "category").
///
/// Output: `"N categories have unbounded congruence chain depth: Cat1, Cat2"`
pub(crate) fn group_cap03(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    let grammar_name = diagnostics.first().and_then(|d| d.grammar_name.clone());
    let hint = diagnostics.first().and_then(|d| d.hint.clone());

    let mut cats: Vec<String> = Vec::new();
    for diag in &diagnostics {
        // Extract category from message: "deep congruence chain: category `Proc` has ..."
        let cat = diag
            .message
            .split("category `")
            .nth(1)
            .and_then(|s| s.split('`').next())
            .unwrap_or("?")
            .to_string();
        if !cats.contains(&cat) {
            cats.push(cat);
        }
    }

    vec![LintDiagnostic {
        id: DiagnosticId::CAP03,
        name: "deep-congruence-chains",
        severity: LintSeverity::Warning,
        category: None,
        rule: None,
        message: format!(
            "{} categories have unbounded congruence chain depth: {}",
            cats.len(),
            cats.join(", "),
        ),
        hint,
        grammar_name,
        source_location: None,
    }]
}

/// Group C-AP05 (clone storm risk) by constructor/category.
///
/// Extracts constructor and category from the message text.
///
/// Output: `"N constructors have collection fields (clone storm risk): Ctor1(Cat1), Ctor2(Cat2)"`
pub(crate) fn group_cap05(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    let grammar_name = diagnostics.first().and_then(|d| d.grammar_name.clone());
    let hint = diagnostics.first().and_then(|d| d.hint.clone());

    let mut entries: Vec<String> = Vec::new();
    for diag in &diagnostics {
        // Extract constructor: "clone storm: constructor `PPar` (category `Proc`) has ..."
        let ctor = diag
            .message
            .split("constructor `")
            .nth(1)
            .and_then(|s| s.split('`').next())
            .unwrap_or("?");
        let cat = diag
            .message
            .split("category `")
            .nth(1)
            .and_then(|s| s.split('`').next())
            .unwrap_or("?");
        entries.push(format!("{}({})", ctor, cat));
    }

    let total = entries.len();
    vec![LintDiagnostic {
        id: DiagnosticId::CAP05,
        name: "clone-storm-risk",
        severity: LintSeverity::Warning,
        category: None,
        rule: None,
        message: format!(
            "{} constructors have collection fields (clone storm risk): {}",
            total,
            entries.join(", "),
        ),
        hint,
        grammar_name,
        source_location: None,
    }]
}

/// Group DIS01 (hot-path misalignment) by category.
///
/// Output: `"N categories have WFST action table misalignment (CD01 compensates): Cat1, Cat2"`
pub(crate) fn group_dis01(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    let grammar_name = diagnostics.first().and_then(|d| d.grammar_name.clone());
    let hint = diagnostics.first().and_then(|d| d.hint.clone());

    let cats: Vec<String> = diagnostics
        .iter()
        .filter_map(|d| d.category.clone())
        .collect();

    vec![LintDiagnostic {
        id: DiagnosticId::DIS01,
        name: "hot-path-misalignment",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "{} categories have WFST action table misalignment (CD01 compensates): {}",
            cats.len(),
            cats.join(", "),
        ),
        hint,
        grammar_name,
        source_location: None,
    }]
}

// Stage 10c (2026-05-04): group_w10 helper DELETED alongside W10.

/// Group W12 (dispatch entropy) by category with entropy values.
///
/// Extracts category and entropy (bits) from each diagnostic message.
///
/// Output: `"N categories have high dispatch entropy: Cat1(X.XX bits), Cat2(Y.YY bits)"`
pub(crate) fn group_w12(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    let grammar_name = diagnostics.first().and_then(|d| d.grammar_name.clone());
    let hint = diagnostics.first().and_then(|d| d.hint.clone());
    let severity = diagnostics
        .first()
        .map(|d| d.severity)
        .unwrap_or(LintSeverity::Note);

    let mut entries: Vec<String> = Vec::new();
    for diag in &diagnostics {
        // Extract category from backtick: "category `Proc` has high dispatch entropy (X.XX bits, ..."
        let cat = diag
            .message
            .split("category `")
            .nth(1)
            .and_then(|s| s.split('`').next())
            .unwrap_or("?");
        // Extract bits value: "entropy (X.XX bits,"
        let bits = diag
            .message
            .split('(')
            .nth(1)
            .and_then(|s| s.split(" bits").next())
            .unwrap_or("?");
        entries.push(format!("{}({} bits)", cat, bits));
    }

    let total = entries.len();
    vec![LintDiagnostic {
        id: DiagnosticId::W12,
        name: "dispatch-entropy",
        severity,
        category: None,
        rule: None,
        message: format!("{} categories have high dispatch entropy: {}", total, entries.join(", "),),
        hint,
        grammar_name,
        source_location: None,
    }]
}

// Stage 10c (2026-05-04): group_w14 helper DELETED. The repurposed W14
// (walker-fork-tight-margin) emits per-(category, token) diagnostics
// that are unique by construction; grouping is unnecessary and would
// hide the per-token data. Removed from `is_groupable()` and
// `group_diagnostics` dispatch in lockstep.

// ══════════════════════════════════════════════════════════════════════════════
// Lint-B cleanup: groupers for high-volume diagnostic IDs
// ══════════════════════════════════════════════════════════════════════════════
//
// The following groupers each collapse N duplicate-or-similar diagnostics
// into a single count-prefixed summary line. The design pattern:
//
//   1. Partition the input by some key (usually the message text or a
//      source/target field extracted from the message).
//   2. Single-key groups pass through unchanged (avoid adding noise when
//      there is no duplication to collapse).
//   3. Multi-key groups emit one summary per key with an "N occurrence(s)"
//      prefix and a semicolon-separated list of the distinct variant texts.
//
// Shared utility `collect_unique_messages` below deduplicates message
// strings while preserving insertion order.

/// Deduplicate messages preserving insertion order.
fn collect_unique_messages(diagnostics: &[LintDiagnostic]) -> Vec<String> {
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut result = Vec::new();
    for diag in diagnostics {
        if seen.insert(diag.message.clone()) {
            result.push(diag.message.clone());
        }
    }
    result
}

/// Group M01 (theory-morphism gap) diagnostics.
///
/// Input: N warnings of the form
/// `"theory morphism incomplete — missing constructor mapping: [MissingOperation] Type::Constructor: ..."`.
/// Output: 1 warning of the form
/// `"N theory morphism gap(s) (K unique): Type::Constructor; ..."`.
pub(crate) fn group_m01(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    if diagnostics.len() <= 1 {
        return diagnostics;
    }
    let first = diagnostics[0].clone();
    let unique_msgs = collect_unique_messages(&diagnostics);
    // Try to extract the "Type::Constructor" fragment from each unique
    // message. Format:
    //   "theory morphism incomplete — missing constructor mapping:
    //    [MissingOperation] X::Y: ..."
    let fragments: Vec<String> = unique_msgs
        .iter()
        .map(|m| {
            // Look for "[MissingOperation] " prefix. The text that follows
            // is typically of the form `Type::Constructor: Source operation
            // '…' has no translation case`. We want just the
            // `Type::Constructor` fragment — the `::` is a type-path
            // separator, while the first `: ` (colon-space) is the label
            // terminator.
            if let Some(idx) = m.find("[MissingOperation] ") {
                let after = &m[idx + "[MissingOperation] ".len()..];
                // Find the first ": " (colon followed by space) — this is
                // the label terminator. `::` does not match because there
                // is no space after the second colon.
                if let Some(colon_space) = after.find(": ") {
                    return after[..colon_space].to_string();
                }
                return after.to_string();
            }
            // Fallback: show the full (deduped) message
            m.clone()
        })
        .collect();

    let total = diagnostics.len();
    let unique_count = unique_msgs.len();
    let message = if unique_count == 1 {
        format!(
            "{} theory morphism gap(s) — missing constructor mapping for `{}`",
            total, fragments[0],
        )
    } else {
        format!(
            "{} theory morphism gap(s) ({} unique): {}",
            total,
            unique_count,
            fragments.join("; "),
        )
    };

    vec![LintDiagnostic {
        id: DiagnosticId::M01,
        name: "theory-morphism-gap",
        severity: first.severity,
        category: None,
        rule: None,
        message,
        hint: first.hint.clone(),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

/// Group K01 (KAT Hoare-triple failure) diagnostics.
///
/// Input: N warnings of the form
/// `"Hoare triple failed: [A -> B] {A_reachable} call_A_B {B_reachable}"`.
/// Output: 1 warning of the form
/// `"N KAT Hoare-triple failures: A→B; C→D; ..."`.
pub(crate) fn group_k01(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    if diagnostics.len() <= 1 {
        return diagnostics;
    }
    let first = diagnostics[0].clone();
    // Extract the "A -> B" type pair from each message.
    let mut pairs: Vec<String> = Vec::new();
    for diag in &diagnostics {
        // Message format: "Hoare triple failed: [A -> B] ..."
        if let Some(start) = diag.message.find('[') {
            if let Some(end) = diag.message[start..].find(']') {
                let inside = &diag.message[start + 1..start + end];
                let pair = inside.replace(" -> ", "→").trim().to_string();
                if !pairs.contains(&pair) {
                    pairs.push(pair);
                }
            }
        }
    }
    let total = diagnostics.len();
    let message = if pairs.is_empty() {
        format!("{} KAT Hoare-triple failures", total)
    } else {
        format!("{} KAT Hoare-triple failures: {}", total, pairs.join("; "),)
    };

    vec![LintDiagnostic {
        id: DiagnosticId::K01,
        name: "kat-hoare-triple-failure",
        severity: first.severity,
        category: None,
        rule: None,
        message,
        hint: first.hint.clone(),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

/// Group SYM02 (symbolic-automaton overlap) diagnostics by category.
///
/// Input: N notes of the form `"guards R1 and R2 overlap on ..."` scoped
/// to some category. Output: 1 note per grammar summarizing the count
/// per category.
pub(crate) fn group_sym02(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    if diagnostics.len() <= 1 {
        return diagnostics;
    }
    let first = diagnostics[0].clone();
    use std::collections::BTreeMap;
    let mut by_cat: BTreeMap<String, usize> = BTreeMap::new();
    for diag in &diagnostics {
        let cat = diag
            .category
            .clone()
            .unwrap_or_else(|| "(unknown)".to_string());
        *by_cat.entry(cat).or_default() += 1;
    }
    let total = diagnostics.len();
    let cat_summary: Vec<String> = by_cat
        .iter()
        .map(|(cat, n)| format!("{}:{}", cat, n))
        .collect();
    let message = format!(
        "{} symbolic-automaton guard overlaps across {} category(ies): {}",
        total,
        by_cat.len(),
        cat_summary.join(", "),
    );

    vec![LintDiagnostic {
        id: DiagnosticId::SYM02,
        name: "sfa-guard-overlap",
        severity: first.severity,
        category: None,
        rule: None,
        message,
        hint: first.hint.clone(),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

/// Group N02 (Petri-net unbounded place) diagnostics.
///
/// Input: N warnings of the form `"place X has unbounded token capacity"`.
/// Output: 1 warning of the form
/// `"N places with unbounded token capacity: [P1, P2, ...]"`.
pub(crate) fn group_n02(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    if diagnostics.len() <= 1 {
        return diagnostics;
    }
    let first = diagnostics[0].clone();
    // Extract the place name between backticks from each message.
    let mut places: Vec<String> = Vec::new();
    for diag in &diagnostics {
        if let Some(start) = diag.message.find('`') {
            if let Some(end) = diag.message[start + 1..].find('`') {
                let place = diag.message[start + 1..start + 1 + end].to_string();
                if !places.contains(&place) {
                    places.push(place);
                }
            }
        }
    }
    let total = diagnostics.len();
    let message = if places.is_empty() {
        format!("{} places with unbounded token capacity", total)
    } else {
        format!("{} places with unbounded token capacity: [{}]", total, places.join(", "),)
    };

    vec![LintDiagnostic {
        id: DiagnosticId::N02,
        name: "petri-unbounded-place",
        severity: first.severity,
        category: None,
        rule: None,
        message,
        hint: first.hint.clone(),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

/// Group N05 (alternating bisimulation non-equivalence) diagnostics.
///
/// Input: N warnings of the form
/// `"categories `A` and `B` are not bisimilar (attacker wins game)"`.
/// Output: 1 warning of the form
/// `"N category pairs are not bisimilar: (A,B); (C,D); ..."`.
pub(crate) fn group_n05(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    if diagnostics.len() <= 1 {
        return diagnostics;
    }
    let first = diagnostics[0].clone();
    let mut pairs: Vec<String> = Vec::new();
    for diag in &diagnostics {
        // Extract the two backtick-quoted category names from the message.
        let mut ticks: Vec<String> = Vec::new();
        let mut remaining = diag.message.as_str();
        while let Some(start) = remaining.find('`') {
            remaining = &remaining[start + 1..];
            if let Some(end) = remaining.find('`') {
                ticks.push(remaining[..end].to_string());
                remaining = &remaining[end + 1..];
            } else {
                break;
            }
            if ticks.len() == 2 {
                break;
            }
        }
        if ticks.len() == 2 {
            let pair = format!("({},{})", ticks[0], ticks[1]);
            if !pairs.contains(&pair) {
                pairs.push(pair);
            }
        }
    }
    let total = diagnostics.len();
    let message = if pairs.is_empty() {
        format!("{} category pairs are not bisimilar", total)
    } else {
        format!("{} category pairs are not bisimilar: {}", total, pairs.join("; "),)
    };

    vec![LintDiagnostic {
        id: DiagnosticId::N05,
        name: "alt-bisim-not-equivalent",
        severity: first.severity,
        category: None,
        rule: None,
        message,
        hint: first.hint.clone(),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}
