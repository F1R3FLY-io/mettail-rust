//! Unified compile-time lint layer for PraTTaIL grammars.
//!
//! Consolidates all grammar warnings and adds new grammar-level lints into a
//! single module with structured diagnostics. Lints leverage data already
//! computed during the Generate phase (FIRST/FOLLOW sets, prediction WFSTs,
//! recovery WFSTs, BP table, RecoveryConfig) — no separate analysis passes.
//!
//! ## Lint Categories
//!
//! | Prefix | Category | Source Data |
//! |--------|----------|-------------|
//! | G | Grammar structure | ParserBundle (pre-WFST) |
//! | W | WFST-specific | Prediction WFSTs |
//! | R | Recovery | Recovery WFSTs + RecoveryConfig |
//! | C | Cross-category | Cast rules + FIRST sets |
//! | P | Performance | DFA stats + WFST metrics |
//!
//! ## Display Format
//!
//! Rust-compiler-style diagnostics to stderr:
//!
//! ```text
//! error[C01]: cast cycle detected: Int -> Proc -> Int
//!   = hint: break the cycle by removing one cast direction
//!
//! warning[W01]: rule `FloatToStr` in category `Str` is unreachable (dead code)
//!   = hint: remove the rule or add a unique dispatch token
//! ```

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::binding_power::BindingPowerTable;
use crate::dispatch::{CastRule, CrossCategoryRule};
use crate::pipeline::CategoryInfo;
use crate::prediction::{FirstSet, FollowSetInput, RuleInfo};
use crate::recovery::{RecoveryConfig, RecoveryWfst};
use crate::recursive::RDRuleInfo;
use crate::wfst::PredictionWfst;
use crate::SyntaxItemSpec;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// Lint severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LintSeverity {
    /// Informational note — no action required.
    Note,
    /// Compile-time warning — possible issue.
    Warning,
    /// Compile-time error — correctness bug.
    Error,
}

impl fmt::Display for LintSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LintSeverity::Note => write!(f, "note"),
            LintSeverity::Warning => write!(f, "warning"),
            LintSeverity::Error => write!(f, "error"),
        }
    }
}

/// A structured lint diagnostic.
#[derive(Debug, Clone)]
pub struct LintDiagnostic {
    /// Lint ID (e.g., "G01", "W01", "C01").
    pub id: &'static str,
    /// Human-readable lint name (e.g., "left-recursion", "dead-rule").
    pub name: &'static str,
    /// Severity level.
    pub severity: LintSeverity,
    /// Category name (for category-specific lints).
    pub category: Option<String>,
    /// Rule label (for rule-specific lints).
    pub rule: Option<String>,
    /// Diagnostic message.
    pub message: String,
    /// Optional fix suggestion.
    pub hint: Option<String>,
}

impl fmt::Display for LintDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[{}]: {}", self.severity, self.id, self.message)?;
        if let Some(ref hint) = self.hint {
            write!(f, "\n  = hint: {}", hint)?;
        }
        Ok(())
    }
}

/// All pipeline data available for linting (borrows, no copies).
pub struct LintContext<'a> {
    /// Category metadata.
    pub categories: &'a [CategoryInfo],
    /// Rule analysis info (from prediction analysis).
    pub rules: &'a [RuleInfo],
    /// RD rule info (recursive-descent handler data).
    pub rd_rules: &'a [RDRuleInfo],
    /// FIRST sets per category.
    pub first_sets: &'a HashMap<String, FirstSet>,
    /// FOLLOW sets per category.
    pub follow_sets: &'a HashMap<String, FirstSet>,
    /// Binding power table.
    pub bp_table: &'a BindingPowerTable,
    /// Prediction WFSTs per category.
    pub prediction_wfsts: &'a HashMap<String, PredictionWfst>,
    /// Recovery WFSTs (one per category).
    pub recovery_wfsts: &'a [RecoveryWfst],
    /// Cast rules.
    pub cast_rules: &'a [CastRule],
    /// Cross-category rules.
    pub cross_rules: &'a [CrossCategoryRule],
    /// Categories needing NFA spillover buffers.
    pub nfa_spillover_categories: &'a HashSet<String>,
    /// Recovery configuration (19 fields).
    pub recovery_config: &'a RecoveryConfig,
    /// All syntax per rule: (label, category, syntax).
    pub all_syntax: &'a [(String, String, Vec<SyntaxItemSpec>)],
    /// FOLLOW set inputs (for terminal extraction).
    pub follow_inputs: &'a [FollowSetInput],
}

/// Run all lints and return structured diagnostics.
///
/// Lints are grouped by category and run in order:
/// 1. Grammar structure (G01-G10)
/// 2. WFST-specific (W01-W06)
/// 3. Recovery (R01-R07)
/// 4. Cross-category (C01-C04)
/// 5. Performance (P02-P04)
pub fn run_lints(ctx: &LintContext) -> Vec<LintDiagnostic> {
    let mut diagnostics = Vec::new();

    // ── Grammar structure lints ──
    lint_g01_left_recursion(ctx, &mut diagnostics);
    lint_g02_unused_category(ctx, &mut diagnostics);
    lint_g03_ambiguous_prefix(ctx, &mut diagnostics);
    lint_g04_duplicate_rule_label(ctx, &mut diagnostics);
    lint_g05_empty_category(ctx, &mut diagnostics);
    lint_g06_shadowed_operator(ctx, &mut diagnostics);
    lint_g07_identical_rules(ctx, &mut diagnostics);
    lint_g08_missing_cast_to_root(ctx, &mut diagnostics);
    lint_g09_unbalanced_delimiters(ctx, &mut diagnostics);
    lint_g10_ambiguous_associativity(ctx, &mut diagnostics);

    // ── WFST lints ──
    lint_w01_dead_rule(ctx, &mut diagnostics);
    lint_w02_nfa_ambiguous_prefix(ctx, &mut diagnostics);
    lint_w03_high_ambiguity_token(ctx, &mut diagnostics);
    lint_w04_weight_gap_anomaly(ctx, &mut diagnostics);
    lint_w06_weight_inversion(ctx, &mut diagnostics);

    // ── Recovery lints ──
    lint_r01_empty_sync_set(ctx, &mut diagnostics);
    lint_r02_sparse_recovery(ctx, &mut diagnostics);
    lint_r05_missing_bracket_sync(ctx, &mut diagnostics);
    lint_r06_inverted_recovery_costs(ctx, &mut diagnostics);
    lint_r07_transposition_candidate(ctx, &mut diagnostics);

    // ── Cross-category lints ──
    lint_c01_cast_cycle(ctx, &mut diagnostics);
    lint_c02_transitive_cast_redundancy(ctx, &mut diagnostics);
    lint_c04_wide_cross_overlap(ctx, &mut diagnostics);

    // ── Performance lints ──
    lint_p02_high_nfa_spillover(ctx, &mut diagnostics);
    lint_p03_deep_cast_nesting(ctx, &mut diagnostics);
    lint_p04_many_alternatives(ctx, &mut diagnostics);

    diagnostics
}

/// Emit all lint diagnostics to stderr.
pub fn emit_diagnostics(diagnostics: &[LintDiagnostic]) {
    for diag in diagnostics {
        eprintln!("{}", diag);
    }
}

/// Returns true if any diagnostic has Error severity.
pub fn has_errors(diagnostics: &[LintDiagnostic]) -> bool {
    diagnostics.iter().any(|d| d.severity == LintSeverity::Error)
}

// ══════════════════════════════════════════════════════════════════════════════
// G01: Left Recursion (migrated from prediction.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g01_left_recursion(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for (label, category, syntax) in ctx.all_syntax {
        if let Some(SyntaxItemSpec::NonTerminal { category: ref first_cat, .. }) = syntax.first() {
            if first_cat == category {
                // Skip infix, postfix, mixfix — handled by Pratt
                let terminal_count = syntax
                    .iter()
                    .filter(|i| matches!(i, SyntaxItemSpec::Terminal(_)))
                    .count();
                let nt_count = syntax
                    .iter()
                    .filter(|i| matches!(i, SyntaxItemSpec::NonTerminal { .. }))
                    .count();

                let is_infix_pattern = nt_count == 2
                    && terminal_count >= 1
                    && syntax.len() >= 3
                    && matches!(
                        syntax.last(),
                        Some(SyntaxItemSpec::NonTerminal { category: ref last_cat, .. })
                        if last_cat == category
                    );
                let is_postfix_pattern =
                    nt_count == 1 && terminal_count == 1 && syntax.len() == 2;
                let is_mixfix_pattern = nt_count >= 3 && terminal_count >= 2;

                if !is_infix_pattern && !is_postfix_pattern && !is_mixfix_pattern {
                    diagnostics.push(LintDiagnostic {
                        id: "G01",
                        name: "left-recursion",
                        severity: LintSeverity::Warning,
                        category: Some(category.clone()),
                        rule: Some(label.clone()),
                        message: format!(
                            "left-recursive rule `{}` in category `{}` \
                             (first item is NonTerminal of same category)",
                            label, category,
                        ),
                        hint: Some(
                            "convert to infix/postfix pattern for Pratt handling, \
                             or restructure to avoid same-category leading NonTerminal"
                                .to_string(),
                        ),
                    });
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G02: Unused Category (migrated from prediction.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g02_unused_category(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let mut referenced: HashSet<String> = HashSet::new();

    for (_, _, syntax) in ctx.all_syntax {
        collect_referenced_categories(syntax, &mut referenced);
    }

    // Categories with rules targeting them are "used"
    for (_, category, _) in ctx.all_syntax {
        referenced.insert(category.clone());
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();
    for cat_name in &category_names {
        if !referenced.contains(*cat_name) {
            diagnostics.push(LintDiagnostic {
                id: "G02",
                name: "unused-category",
                severity: LintSeverity::Warning,
                category: Some(cat_name.to_string()),
                rule: None,
                message: format!(
                    "category `{}` declared but never referenced in any rule syntax",
                    cat_name,
                ),
                hint: Some("remove the unused category or add rules that reference it".to_string()),
            });
        }
    }
}

/// Recursively collect all category names referenced in syntax items.
fn collect_referenced_categories(items: &[SyntaxItemSpec], referenced: &mut HashSet<String>) {
    for item in items {
        match item {
            SyntaxItemSpec::NonTerminal { category, .. } => {
                referenced.insert(category.clone());
            }
            SyntaxItemSpec::Collection {
                element_category, ..
            } => {
                referenced.insert(element_category.clone());
            }
            SyntaxItemSpec::ZipMapSep {
                left_category,
                right_category,
                body_items,
                ..
            } => {
                referenced.insert(left_category.clone());
                referenced.insert(right_category.clone());
                collect_referenced_categories(body_items, referenced);
            }
            SyntaxItemSpec::Optional { inner } => {
                collect_referenced_categories(inner, referenced);
            }
            SyntaxItemSpec::Binder { category, .. } => {
                referenced.insert(category.clone());
            }
            _ => {}
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G03: Ambiguous Prefix (migrated from prediction.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g03_ambiguous_prefix(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    use crate::prediction::FirstItem;

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        // Collect non-infix, non-var, non-literal rules for this category
        let prefix_rules: Vec<&RuleInfo> = ctx
            .rules
            .iter()
            .filter(|r| r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal)
            .collect();

        let mut terminal_to_rules: HashMap<String, Vec<String>> = HashMap::new();

        for rule in &prefix_rules {
            for item in &rule.first_items {
                if let FirstItem::Terminal(t) = item {
                    terminal_to_rules
                        .entry(t.clone())
                        .or_default()
                        .push(rule.label.clone());
                }
            }
        }

        for (token, rule_labels) in &terminal_to_rules {
            if rule_labels.len() > 1 {
                diagnostics.push(LintDiagnostic {
                    id: "G03",
                    name: "ambiguous-prefix",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message: format!(
                        "ambiguous prefix dispatch for token `{}` in category `{}`: \
                         rules [{}] all match",
                        token,
                        cat,
                        rule_labels.join(", "),
                    ),
                    hint: Some(
                        "add unique dispatch tokens or use WFST weights to disambiguate"
                            .to_string(),
                    ),
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G04: Duplicate Rule Label
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g04_duplicate_rule_label(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let mut seen: HashMap<(&str, &str), &str> = HashMap::new();
    for (label, category, _) in ctx.all_syntax {
        let key = (category.as_str(), label.as_str());
        if let Some(&_existing) = seen.get(&key) {
            diagnostics.push(LintDiagnostic {
                id: "G04",
                name: "duplicate-rule-label",
                severity: LintSeverity::Error,
                category: Some(category.clone()),
                rule: Some(label.clone()),
                message: format!(
                    "duplicate rule label `{}` in category `{}` — codegen will produce \
                     conflicting constructor names",
                    label, category,
                ),
                hint: Some("rename one of the rules to a unique label".to_string()),
            });
        } else {
            seen.insert(key, label.as_str());
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G05: Empty Category
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g05_empty_category(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();

    for cat_name in &category_names {
        let has_rules = ctx
            .all_syntax
            .iter()
            .any(|(_, category, _)| category.as_str() == *cat_name);
        if !has_rules {
            diagnostics.push(LintDiagnostic {
                id: "G05",
                name: "empty-category",
                severity: LintSeverity::Warning,
                category: Some(cat_name.to_string()),
                rule: None,
                message: format!(
                    "category `{}` has zero rules — cannot be parsed",
                    cat_name,
                ),
                hint: Some("add at least one rule or remove the category declaration".to_string()),
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G06: Shadowed Operator
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g06_shadowed_operator(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    use crate::prediction::FirstItem;

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        // Collect terminals from infix rules
        let infix_terminals: HashSet<String> = ctx
            .bp_table
            .operators_for_category(cat)
            .iter()
            .map(|op| op.terminal.clone())
            .collect();

        // Collect terminals from prefix rules (non-infix, non-var, non-literal)
        let mut prefix_terminals: HashSet<String> = HashSet::new();
        for rule in ctx.rules.iter().filter(|r| {
            r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal
        }) {
            for item in &rule.first_items {
                if let FirstItem::Terminal(t) = item {
                    prefix_terminals.insert(t.clone());
                }
            }
        }

        // Check for unary prefix rules specifically
        let unary_prefix_terminals: HashSet<String> = ctx
            .rules
            .iter()
            .filter(|r| r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal)
            .flat_map(|r| {
                r.first_items.iter().filter_map(|fi| match fi {
                    FirstItem::Terminal(t) => Some(t.clone()),
                    _ => None,
                })
            })
            .collect();

        let overlap: Vec<&String> = infix_terminals
            .intersection(&unary_prefix_terminals)
            .collect();

        for terminal in overlap {
            diagnostics.push(LintDiagnostic {
                id: "G06",
                name: "shadowed-operator",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "operator `{}` is both infix and prefix in category `{}`",
                    terminal, cat,
                ),
                hint: Some(
                    "this is intentional — prefix_bp = max_infix_bp + 2, so `-5!` = `-(5!)`"
                        .to_string(),
                ),
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G07: Identical Rules
// ══════════════════════════════════════════════════════════════════════════════

/// Normalize a syntax item sequence to a comparable string for G07.
fn syntax_signature(syntax: &[SyntaxItemSpec]) -> String {
    let mut parts = Vec::with_capacity(syntax.len());
    for item in syntax {
        match item {
            SyntaxItemSpec::Terminal(t) => parts.push(format!("T({})", t)),
            SyntaxItemSpec::NonTerminal { category, .. } => {
                parts.push(format!("NT({})", category))
            }
            SyntaxItemSpec::IdentCapture { .. } => parts.push("IDENT".to_string()),
            SyntaxItemSpec::Binder { category, is_multi, .. } => {
                parts.push(format!("BIND({},{})", category, is_multi))
            }
            SyntaxItemSpec::Collection {
                element_category,
                separator,
                kind,
                ..
            } => parts.push(format!("COL({},{},{:?})", element_category, separator, kind)),
            SyntaxItemSpec::ZipMapSep {
                left_category,
                right_category,
                body_items,
                separator,
                ..
            } => {
                let inner = syntax_signature(body_items);
                parts.push(format!(
                    "ZMS({},{},{},{})",
                    left_category, right_category, inner, separator
                ))
            }
            SyntaxItemSpec::BinderCollection { separator, .. } => {
                parts.push(format!("BCOL({})", separator))
            }
            SyntaxItemSpec::Optional { inner } => {
                let inner_sig = syntax_signature(inner);
                parts.push(format!("OPT({})", inner_sig))
            }
        }
    }
    parts.join("|")
}

fn lint_g07_identical_rules(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        let cat_syntax: Vec<(&str, &[SyntaxItemSpec])> = ctx
            .all_syntax
            .iter()
            .filter(|(_, c, _)| c == cat)
            .map(|(label, _, syntax)| (label.as_str(), syntax.as_slice()))
            .collect();

        let mut sig_to_labels: HashMap<String, Vec<&str>> = HashMap::new();
        for (label, syntax) in &cat_syntax {
            let sig = syntax_signature(syntax);
            sig_to_labels.entry(sig).or_default().push(label);
        }

        for (_, labels) in &sig_to_labels {
            if labels.len() > 1 {
                diagnostics.push(LintDiagnostic {
                    id: "G07",
                    name: "identical-rules",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message: format!(
                        "rules [{}] in category `{}` have identical syntax item sequences",
                        labels.join(", "),
                        cat,
                    ),
                    hint: Some(
                        "these rules are structurally identical — consider merging or \
                         differentiating their syntax"
                            .to_string(),
                    ),
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G08: Missing Cast to Root
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g08_missing_cast_to_root(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Find primary (root) category
    let primary = match ctx.categories.iter().find(|c| c.is_primary) {
        Some(c) => &c.name,
        None => return,
    };

    // Build directed graph from cast rules: source → target
    let mut adjacency: HashMap<&str, HashSet<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .insert(cast.target_category.as_str());
    }

    // Also add cross-category rules as edges
    for cross in ctx.cross_rules {
        adjacency
            .entry(cross.source_category.as_str())
            .or_default()
            .insert(cross.result_category.as_str());
    }

    // For each non-primary category, check if there's a path TO the primary category
    // (via cast/cross-category rules acting as edges in either direction)
    // A category needs a cast path FROM it TO the primary (the primary can parse it).
    // Actually: the question is whether the primary category can reach this category's values.
    // Cast rules go source → target (target wraps source). So target can receive source values.
    // We need: path from non-primary → primary via target edges.
    //
    // Build reverse graph: for each cast source→target, the target "imports" source values.
    // So primary can reach cat if: there's a path primary ←(imports)─ ... ←(imports)─ cat
    // Which means: path cat → ... → primary in the forward (source→target) graph.
    // Actually, cast rules mean target_category has a rule that wraps source_category.
    // So if we want cat's values to be usable in primary, we need a path from cat to primary
    // in the cast graph where each edge is source→target.

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();

    for cat_name in &category_names {
        if *cat_name == primary.as_str() {
            continue;
        }

        // DFS from cat_name following source→target edges to see if we reach primary
        let mut visited = HashSet::new();
        let mut stack = vec![*cat_name];
        let mut found = false;

        while let Some(node) = stack.pop() {
            if node == primary.as_str() {
                found = true;
                break;
            }
            if !visited.insert(node) {
                continue;
            }
            if let Some(neighbors) = adjacency.get(node) {
                for &next in neighbors {
                    stack.push(next);
                }
            }
        }

        if !found {
            diagnostics.push(LintDiagnostic {
                id: "G08",
                name: "missing-cast-to-root",
                severity: LintSeverity::Warning,
                category: Some(cat_name.to_string()),
                rule: None,
                message: format!(
                    "no cast path from category `{}` to primary category `{}`",
                    cat_name, primary,
                ),
                hint: Some(format!(
                    "add a cast rule from `{}` to `{}` or an intermediate category",
                    cat_name, primary,
                )),
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G09: Unbalanced Delimiters
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g09_unbalanced_delimiters(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let pairs = [("(", ")"), ("{", "}"), ("[", "]")];

    for (label, category, syntax) in ctx.all_syntax {
        let terminals = collect_terminals_flat(syntax);

        for &(open, close) in &pairs {
            let open_count = terminals.iter().filter(|t| t.as_str() == open).count();
            let close_count = terminals.iter().filter(|t| t.as_str() == close).count();

            if open_count != close_count {
                diagnostics.push(LintDiagnostic {
                    id: "G09",
                    name: "unbalanced-delimiters",
                    severity: LintSeverity::Warning,
                    category: Some(category.clone()),
                    rule: Some(label.clone()),
                    message: format!(
                        "rule `{}` in category `{}` has unbalanced delimiters: \
                         {} `{}` vs {} `{}`",
                        label, category, open_count, open, close_count, close,
                    ),
                    hint: Some(format!(
                        "add the missing `{}` or `{}` delimiter",
                        if open_count > close_count { close } else { open },
                        if open_count > close_count { close } else { open },
                    )),
                });
            }
        }
    }
}

/// Collect all terminal strings from syntax items (flat, including nested).
fn collect_terminals_flat(items: &[SyntaxItemSpec]) -> Vec<String> {
    let mut terminals = Vec::new();
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(t) => terminals.push(t.clone()),
            SyntaxItemSpec::Collection { separator, .. }
            | SyntaxItemSpec::BinderCollection { separator, .. } => {
                terminals.push(separator.clone());
            }
            SyntaxItemSpec::ZipMapSep {
                body_items,
                separator,
                ..
            } => {
                terminals.extend(collect_terminals_flat(body_items));
                terminals.push(separator.clone());
            }
            SyntaxItemSpec::Optional { inner } => {
                terminals.extend(collect_terminals_flat(inner));
            }
            _ => {}
        }
    }
    terminals
}

// ══════════════════════════════════════════════════════════════════════════════
// G10: Ambiguous Associativity
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g10_ambiguous_associativity(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        let ops = ctx.bp_table.operators_for_category(cat);

        // Group by left_bp (same precedence level)
        let mut bp_to_ops: HashMap<u8, Vec<&crate::binding_power::InfixOperator>> = HashMap::new();
        for op in &ops {
            bp_to_ops.entry(op.left_bp).or_default().push(op);
        }

        for (left_bp, group) in &bp_to_ops {
            if group.len() < 2 {
                continue;
            }

            let first_assoc = group[0].associativity();
            let has_mixed = group.iter().any(|op| op.associativity() != first_assoc);
            if has_mixed {
                let op_names: Vec<&str> = group.iter().map(|op| op.terminal.as_str()).collect();
                diagnostics.push(LintDiagnostic {
                    id: "G10",
                    name: "ambiguous-associativity",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message: format!(
                        "same-precedence operators [{}] in category `{}` (left_bp={}) \
                         have different associativity",
                        op_names.join(", "),
                        cat,
                        left_bp,
                    ),
                    hint: Some(
                        "use explicit precedence levels to separate operators with \
                         different associativity"
                            .to_string(),
                    ),
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W01: Dead Rule (migrated from pipeline.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w01_dead_rule(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let warnings = crate::pipeline::detect_dead_rules(
        ctx.rules,
        ctx.categories,
        ctx.first_sets,
        ctx.prediction_wfsts,
    );

    for w in warnings {
        let (rule_label, category, hint_msg) = match &w {
            crate::pipeline::DeadRuleWarning::LiteralNoNativeType {
                rule_label,
                category,
            } => (
                rule_label.clone(),
                category.clone(),
                "add a native_type to the category or remove the literal rule",
            ),
            crate::pipeline::DeadRuleWarning::UnreachableCategory {
                rule_label,
                category,
            } => (
                rule_label.clone(),
                category.clone(),
                "add a prefix rule to make the category reachable",
            ),
            crate::pipeline::DeadRuleWarning::WfstUnreachable {
                rule_label,
                category,
            } => (
                rule_label.clone(),
                category.clone(),
                "remove the rule or add a unique dispatch token",
            ),
        };

        diagnostics.push(LintDiagnostic {
            id: "W01",
            name: "dead-rule",
            severity: LintSeverity::Warning,
            category: Some(category.clone()),
            rule: Some(rule_label.clone()),
            message: format!("{}", w),
            hint: Some(hint_msg.to_string()),
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W02: NFA Ambiguous Prefix (migrated from pipeline.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w02_nfa_ambiguous_prefix(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for cat_name in ctx.nfa_spillover_categories {
        let rd_by_token = crate::trampoline::group_rd_by_dispatch_token_pub(ctx.rd_rules, cat_name);
        if let Some(wfst) = ctx.prediction_wfsts.get(cat_name.as_str()) {
            for (token, rules) in &rd_by_token {
                if rules.len() <= 1 {
                    continue;
                }
                let labels: Vec<&str> = rules.iter().map(|r| r.label.as_str()).collect();
                let ordered = wfst.nfa_alternative_order(token, &labels);
                let weights: Vec<f64> = ordered.iter().map(|(_, w)| w.0).collect();
                let all_equal =
                    weights.windows(2).all(|w| (w[0] - w[1]).abs() < 1e-12);

                let mut message = format!(
                    "ambiguous prefix dispatch for token `{}` in category `{}`: \
                     rules [{}] all match",
                    token,
                    cat_name,
                    labels.join(", "),
                );

                if all_equal {
                    message.push_str(&format!(
                        " — all {} alternatives have equal weight ({:.1}); \
                         resolution deferred to semantic disambiguation",
                        rules.len(),
                        weights.first().copied().unwrap_or(0.5),
                    ));
                }

                diagnostics.push(LintDiagnostic {
                    id: "W02",
                    name: "nfa-ambiguous-prefix",
                    severity: LintSeverity::Warning,
                    category: Some(cat_name.clone()),
                    rule: None,
                    message,
                    hint: Some(
                        "add distinguishing syntax or assign different WFST weights \
                         to resolve the ambiguity"
                            .to_string(),
                    ),
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W03: High Ambiguity Token
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w03_high_ambiguity_token(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let predictions = wfst.predict_with_confidence(&token);
                    if let Some((_, count_weight)) = predictions.first() {
                        if count_weight.count() >= 3 {
                            let action_labels: Vec<String> = predictions
                                .iter()
                                .map(|(a, _)| a.action.rule_label().to_string())
                                .collect();
                            diagnostics.push(LintDiagnostic {
                                id: "W03",
                                name: "high-ambiguity-token",
                                severity: LintSeverity::Warning,
                                category: Some(cat.clone()),
                                rule: None,
                                message: format!(
                                    "token `{}` dispatches to {} rules in category `{}`: [{}]",
                                    token,
                                    predictions.len(),
                                    cat,
                                    action_labels.join(", "),
                                ),
                                hint: Some(
                                    "high branching factor — consider adding unique \
                                     dispatch tokens to reduce ambiguity"
                                        .to_string(),
                                ),
                            });
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W04: Weight Gap Anomaly
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w04_weight_gap_anomaly(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let actions = wfst.predict(&token);
                    if actions.len() >= 2 {
                        let best = actions[0].weight.value();
                        let second = actions[1].weight.value();
                        let gap = second - best;

                        if gap > 5.0 {
                            diagnostics.push(LintDiagnostic {
                                id: "W04",
                                name: "weight-gap-anomaly",
                                severity: LintSeverity::Note,
                                category: Some(cat.clone()),
                                rule: None,
                                message: format!(
                                    "token `{}` in category `{}`: gap of {:.1} between best \
                                     rule `{}` (weight {:.1}) and second-best `{}` (weight {:.1}) \
                                     — near-deterministic treated as ambiguous",
                                    token,
                                    cat,
                                    gap,
                                    actions[0].action.rule_label(),
                                    best,
                                    actions[1].action.rule_label(),
                                    second,
                                ),
                                hint: Some(
                                    "the large weight gap suggests this token is effectively \
                                     unambiguous — the second alternative is very unlikely"
                                        .to_string(),
                                ),
                            });
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W06: Weight Inversion
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w06_weight_inversion(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build a map from rule label → syntax item count (specificity)
    let specificity: HashMap<&str, usize> = ctx
        .all_syntax
        .iter()
        .map(|(label, _, syntax)| (label.as_str(), syntax.len()))
        .collect();

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let actions = wfst.predict(&token);
                    // Check each pair: if less-specific rule has lower weight (better)
                    // than more-specific rule, that's an inversion
                    for i in 0..actions.len() {
                        for j in (i + 1)..actions.len() {
                            let label_i = actions[i].action.rule_label();
                            let label_j = actions[j].action.rule_label();
                            let spec_i = specificity.get(label_i.as_str()).copied().unwrap_or(0);
                            let spec_j = specificity.get(label_j.as_str()).copied().unwrap_or(0);
                            let w_i = actions[i].weight.value();
                            let w_j = actions[j].weight.value();

                            // Inversion: less-specific (lower spec) has lower weight (better priority)
                            // than more-specific (higher spec)
                            if spec_i < spec_j && w_i < w_j {
                                diagnostics.push(LintDiagnostic {
                                    id: "W06",
                                    name: "weight-inversion",
                                    severity: LintSeverity::Note,
                                    category: Some(cat.clone()),
                                    rule: None,
                                    message: format!(
                                        "weight inversion for token `{}` in category `{}`: \
                                         less-specific rule `{}` ({} items, weight {:.2}) has \
                                         better priority than more-specific `{}` ({} items, \
                                         weight {:.2})",
                                        token, cat, label_i, spec_i, w_i, label_j, spec_j, w_j,
                                    ),
                                    hint: Some(
                                        "more-specific rules should typically have lower \
                                         (better) weights — check rule ordering or WFST weights"
                                            .to_string(),
                                    ),
                                });
                            }
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R01: Empty Sync Set
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r01_empty_sync_set(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for rwfst in ctx.recovery_wfsts {
        if rwfst.sync_tokens().is_empty() {
            diagnostics.push(LintDiagnostic {
                id: "R01",
                name: "empty-sync-set",
                severity: LintSeverity::Warning,
                category: Some(rwfst.category().to_string()),
                rule: None,
                message: format!(
                    "category `{}` has no sync tokens — recovery always skips to EOF",
                    rwfst.category(),
                ),
                hint: Some(
                    "add structural delimiters or ensure the category has FOLLOW set tokens"
                        .to_string(),
                ),
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R02: Sparse Recovery
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r02_sparse_recovery(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for rwfst in ctx.recovery_wfsts {
        let count = rwfst.sync_tokens().len();
        if count > 0 && count < 2 {
            diagnostics.push(LintDiagnostic {
                id: "R02",
                name: "sparse-recovery",
                severity: LintSeverity::Note,
                category: Some(rwfst.category().to_string()),
                rule: None,
                message: format!(
                    "category `{}` has only {} sync token — limited recovery options",
                    rwfst.category(),
                    count,
                ),
                hint: Some(
                    "add more structural delimiters to improve error recovery quality"
                        .to_string(),
                ),
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R05: Missing Bracket Sync
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r05_missing_bracket_sync(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let bracket_pairs = [("(", "RParen"), ("{", "RBrace"), ("[", "RBracket")];

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        // Collect terminals used by rules in this category
        let mut cat_terminals: HashSet<String> = HashSet::new();
        for (_, category, syntax) in ctx.all_syntax {
            if category == cat {
                for t in collect_terminals_flat(syntax) {
                    cat_terminals.insert(t);
                }
            }
        }

        // Find the recovery WFST for this category
        let rwfst = match ctx.recovery_wfsts.iter().find(|r| r.category() == cat) {
            Some(r) => r,
            None => continue,
        };

        for &(open, close_variant) in &bracket_pairs {
            if cat_terminals.contains(open) {
                // Check if closing bracket is in sync set
                // The sync set uses TokenIds — we need to check by variant name
                // The TokenIdMap resolves names. Check if the closing variant
                // appears in any sync token name.
                let has_close_sync = rwfst.sync_tokens().iter().any(|&id| {
                    rwfst
                        .token_name(id)
                        .map_or(false, |name| name == close_variant)
                });

                if !has_close_sync {
                    diagnostics.push(LintDiagnostic {
                        id: "R05",
                        name: "missing-bracket-sync",
                        severity: LintSeverity::Warning,
                        category: Some(cat.clone()),
                        rule: None,
                        message: format!(
                            "category `{}` uses `{}` delimiter but closing `{}` is \
                             absent from sync set",
                            cat, open, close_variant,
                        ),
                        hint: Some(
                            "ensure the closing bracket is in the category's FOLLOW set \
                             or structural delimiters"
                                .to_string(),
                        ),
                    });
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R06: Inverted Recovery Costs
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r06_inverted_recovery_costs(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let config = ctx.recovery_config;

    // Expected hierarchy: skip < delete < swap < substitute < insert
    let expected_order = [
        ("skip_per_token", config.skip_per_token),
        ("delete_cost", config.delete_cost),
        ("swap_cost", config.swap_cost),
        ("substitute_cost", config.substitute_cost),
        ("insert_cost", config.insert_cost),
    ];

    for i in 0..expected_order.len() {
        for j in (i + 1)..expected_order.len() {
            let (name_i, cost_i) = expected_order[i];
            let (name_j, cost_j) = expected_order[j];

            if cost_i > cost_j {
                diagnostics.push(LintDiagnostic {
                    id: "R06",
                    name: "inverted-recovery-costs",
                    severity: LintSeverity::Warning,
                    category: None,
                    rule: None,
                    message: format!(
                        "RecoveryConfig cost hierarchy violated: {} ({:.2}) > {} ({:.2})",
                        name_i, cost_i, name_j, cost_j,
                    ),
                    hint: Some(format!(
                        "expected hierarchy: skip < delete < swap < substitute < insert; \
                         adjust {} or {} to restore the hierarchy",
                        name_i, name_j,
                    )),
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R07: Transposition Candidate
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r07_transposition_candidate(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Collect all unique operator terminals from the grammar
    let mut all_operators: Vec<String> = Vec::new();
    for (_, _, syntax) in ctx.all_syntax {
        for item in syntax {
            if let SyntaxItemSpec::Terminal(t) = item {
                // Skip structural delimiters
                if !matches!(t.as_str(), "(" | ")" | "{" | "}" | "[" | "]" | "," | ";") {
                    all_operators.push(t.clone());
                }
            }
        }
    }
    all_operators.sort();
    all_operators.dedup();

    // Check all pairs for Levenshtein distance = 1
    let mut reported = HashSet::new();
    for i in 0..all_operators.len() {
        for j in (i + 1)..all_operators.len() {
            let a = &all_operators[i];
            let b = &all_operators[j];

            if char_edit_distance_is_one(a, b) {
                let key = (a.clone(), b.clone());
                if reported.insert(key) {
                    diagnostics.push(LintDiagnostic {
                        id: "R07",
                        name: "transposition-candidate",
                        severity: LintSeverity::Note,
                        category: None,
                        rule: None,
                        message: format!(
                            "operators `{}` and `{}` differ by 1 character — \
                             transposition repair candidate",
                            a, b,
                        ),
                        hint: Some(
                            "the error recovery system can detect and fix common \
                             typos between these operators via SwapTokens"
                                .to_string(),
                        ),
                    });
                }
            }
        }
    }
}

/// Check if two strings have Levenshtein distance exactly 1.
fn char_edit_distance_is_one(a: &str, b: &str) -> bool {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let len_a = a_chars.len();
    let len_b = b_chars.len();

    match (len_a as isize) - (len_b as isize) {
        0 => {
            // Same length: exactly one substitution
            let mut diffs = 0;
            for i in 0..len_a {
                if a_chars[i] != b_chars[i] {
                    diffs += 1;
                    if diffs > 1 {
                        return false;
                    }
                }
            }
            diffs == 1
        }
        1 => {
            // a is one longer: one insertion in a (= one deletion from a to get b)
            one_insertion_away(&a_chars, &b_chars)
        }
        -1 => {
            // b is one longer: one insertion in b
            one_insertion_away(&b_chars, &a_chars)
        }
        _ => false,
    }
}

/// Check if `longer` can become `shorter` by removing exactly one character.
fn one_insertion_away(longer: &[char], shorter: &[char]) -> bool {
    let mut i = 0;
    let mut j = 0;
    let mut skipped = false;
    while i < longer.len() && j < shorter.len() {
        if longer[i] != shorter[j] {
            if skipped {
                return false;
            }
            skipped = true;
            i += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    true
}

// ══════════════════════════════════════════════════════════════════════════════
// C01: Cast Cycle
// ══════════════════════════════════════════════════════════════════════════════

fn lint_c01_cast_cycle(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build adjacency list from cast rules
    let mut adjacency: HashMap<&str, Vec<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .push(cast.target_category.as_str());
    }

    // DFS with coloring: White (unvisited), Gray (in stack), Black (done)
    #[derive(Clone, Copy, PartialEq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();
    let mut color: HashMap<&str, Color> = category_names
        .iter()
        .map(|&c| (c, Color::White))
        .collect();
    let mut path: Vec<&str> = Vec::new();

    fn dfs<'a>(
        node: &'a str,
        adjacency: &HashMap<&'a str, Vec<&'a str>>,
        color: &mut HashMap<&'a str, Color>,
        path: &mut Vec<&'a str>,
        diagnostics: &mut Vec<LintDiagnostic>,
    ) {
        color.insert(node, Color::Gray);
        path.push(node);

        if let Some(neighbors) = adjacency.get(node) {
            for &next in neighbors {
                match color.get(next) {
                    Some(Color::Gray) => {
                        // Found a cycle — extract the cycle path
                        let cycle_start = path.iter().position(|&n| n == next).unwrap_or(0);
                        let mut cycle_path: Vec<&str> =
                            path[cycle_start..].to_vec();
                        cycle_path.push(next);
                        let cycle_str = cycle_path.join(" -> ");

                        diagnostics.push(LintDiagnostic {
                            id: "C01",
                            name: "cast-cycle",
                            severity: LintSeverity::Error,
                            category: None,
                            rule: None,
                            message: format!("cast cycle detected: {}", cycle_str),
                            hint: Some(
                                "break the cycle by removing one cast direction".to_string(),
                            ),
                        });
                    }
                    Some(Color::White) | None => {
                        dfs(next, adjacency, color, path, diagnostics);
                    }
                    Some(Color::Black) => {
                        // Already fully explored, no cycle through this node
                    }
                }
            }
        }

        path.pop();
        color.insert(node, Color::Black);
    }

    for &cat in &category_names {
        if color.get(cat) == Some(&Color::White) {
            dfs(cat, &adjacency, &mut color, &mut path, diagnostics);
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// C02: Transitive Cast Redundancy
// ══════════════════════════════════════════════════════════════════════════════

fn lint_c02_transitive_cast_redundancy(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build adjacency list
    let mut adjacency: HashMap<&str, HashSet<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .insert(cast.target_category.as_str());
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();

    // Compute transitive closure via Floyd-Warshall-style approach
    let mut reachable: HashMap<(&str, &str), bool> = HashMap::new();
    for &src in &category_names {
        for &dst in &category_names {
            reachable.insert(
                (src, dst),
                adjacency
                    .get(src)
                    .map_or(false, |neighbors| neighbors.contains(dst)),
            );
        }
    }

    for &mid in &category_names {
        for &src in &category_names {
            for &dst in &category_names {
                if reachable[&(src, mid)] && reachable[&(mid, dst)] {
                    reachable.insert((src, dst), true);
                }
            }
        }
    }

    // Check for direct cast A→C alongside transitive A→...→C (path length ≥ 2)
    for cast in ctx.cast_rules {
        let src = cast.source_category.as_str();
        let dst = cast.target_category.as_str();

        // Is there a path of length ≥ 2 from src to dst?
        let has_indirect = adjacency.get(src).map_or(false, |neighbors| {
            neighbors.iter().any(|&mid| {
                mid != dst
                    && reachable
                        .get(&(mid, dst))
                        .copied()
                        .unwrap_or(false)
            })
        });

        if has_indirect {
            diagnostics.push(LintDiagnostic {
                id: "C02",
                name: "transitive-cast-redundancy",
                severity: LintSeverity::Note,
                category: None,
                rule: Some(cast.label.clone()),
                message: format!(
                    "direct cast `{}` → `{}` (rule `{}`) is redundant — a transitive \
                     path already exists",
                    src, dst, cast.label,
                ),
                hint: Some(
                    "the transitive path handles this cast — the direct rule may be \
                     intentional for performance or explicitness"
                        .to_string(),
                ),
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// C04: Wide Cross Overlap
// ══════════════════════════════════════════════════════════════════════════════

fn lint_c04_wide_cross_overlap(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for i in 0..category_names.len() {
        for j in (i + 1)..category_names.len() {
            let cat_a = &category_names[i];
            let cat_b = &category_names[j];

            let first_a = match ctx.first_sets.get(cat_a) {
                Some(fs) => fs,
                None => continue,
            };
            let first_b = match ctx.first_sets.get(cat_b) {
                Some(fs) => fs,
                None => continue,
            };

            let overlap = first_a.intersection(first_b);
            let overlap_count = overlap.tokens.len();

            if first_a.tokens.is_empty() || first_b.tokens.is_empty() {
                continue;
            }

            // Check overlap relative to the smaller FIRST set
            let min_size = first_a.tokens.len().min(first_b.tokens.len());
            let ratio = overlap_count as f64 / min_size as f64;

            if ratio >= 0.8 && overlap_count >= 2 {
                diagnostics.push(LintDiagnostic {
                    id: "C04",
                    name: "wide-cross-overlap",
                    severity: LintSeverity::Note,
                    category: None,
                    rule: None,
                    message: format!(
                        "cross-category overlap between `{}` and `{}`: {}/{} tokens ({:.0}%) \
                         — mostly save/restore dispatch",
                        cat_a,
                        cat_b,
                        overlap_count,
                        min_size,
                        ratio * 100.0,
                    ),
                    hint: Some(
                        "high FIRST-set overlap means many tokens need save/restore \
                         backtracking in cross-category dispatch"
                            .to_string(),
                    ),
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P02: High NFA Spillover
// ══════════════════════════════════════════════════════════════════════════════

fn lint_p02_high_nfa_spillover(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    if ctx.nfa_spillover_categories.len() > 3 {
        let mut sorted_cats: Vec<&String> = ctx.nfa_spillover_categories.iter().collect();
        sorted_cats.sort();
        let cats_str: Vec<&str> = sorted_cats.iter().map(|s| s.as_str()).collect();
        diagnostics.push(LintDiagnostic {
            id: "P02",
            name: "high-nfa-spillover",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "{} categories need NFA spillover buffers: [{}] — increases TLS overhead",
                ctx.nfa_spillover_categories.len(),
                cats_str.join(", "),
            ),
            hint: Some(
                "reduce prefix ambiguity to lower the number of categories needing \
                 NFA spillover"
                    .to_string(),
            ),
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P03: Deep Cast Nesting
// ══════════════════════════════════════════════════════════════════════════════

fn lint_p03_deep_cast_nesting(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build cast DAG adjacency list
    let mut adjacency: HashMap<&str, Vec<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .push(cast.target_category.as_str());
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();

    // Topological sort + DP to find longest path (only valid for DAGs — C01 catches cycles)
    let mut longest_path: HashMap<&str, usize> = HashMap::new();

    fn dp_longest<'a>(
        node: &'a str,
        adjacency: &HashMap<&'a str, Vec<&'a str>>,
        memo: &mut HashMap<&'a str, usize>,
        visited: &mut HashSet<&'a str>,
    ) -> usize {
        if let Some(&cached) = memo.get(node) {
            return cached;
        }
        // Cycle guard (C01 should catch this, but be defensive)
        if !visited.insert(node) {
            return 0;
        }

        let max_child = adjacency
            .get(node)
            .map_or(0, |neighbors| {
                neighbors
                    .iter()
                    .map(|&next| dp_longest(next, adjacency, memo, visited) + 1)
                    .max()
                    .unwrap_or(0)
            });

        visited.remove(node);
        memo.insert(node, max_child);
        max_child
    }

    let mut visited = HashSet::new();
    for &cat in &category_names {
        dp_longest(cat, &adjacency, &mut longest_path, &mut visited);
    }

    let max_depth = longest_path.values().copied().max().unwrap_or(0);
    if max_depth > 3 {
        let deepest = longest_path
            .iter()
            .filter(|(_, &d)| d == max_depth)
            .map(|(&name, _)| name)
            .collect::<Vec<_>>();

        diagnostics.push(LintDiagnostic {
            id: "P03",
            name: "deep-cast-nesting",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "cast chain depth is {} (starting from [{}]) — each level adds \
                 Box::new() wrapper overhead",
                max_depth,
                deepest.join(", "),
            ),
            hint: Some(
                "consider adding direct cast rules to bypass intermediate categories"
                    .to_string(),
            ),
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P04: Many Alternatives
// ══════════════════════════════════════════════════════════════════════════════

fn lint_p04_many_alternatives(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let actions = wfst.predict(&token);
                    if actions.len() > 4 {
                        diagnostics.push(LintDiagnostic {
                            id: "P04",
                            name: "many-alternatives",
                            severity: LintSeverity::Note,
                            category: Some(cat.clone()),
                            rule: None,
                            message: format!(
                                "token `{}` dispatches to {} rules in category `{}` — \
                                 save/restore overhead",
                                token,
                                actions.len(),
                                cat,
                            ),
                            hint: Some(
                                "reduce prefix ambiguity or use beam pruning to limit \
                                 alternatives"
                                    .to_string(),
                            ),
                        });
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_power::{BindingPowerTable, InfixOperator};
    use crate::dispatch::{CastRule, CrossCategoryRule};
    use crate::pipeline::CategoryInfo;
    use crate::prediction::{FirstItem, FirstSet, FollowSetInput, RuleInfo};
    use crate::recovery::RecoveryConfig;
    use crate::recursive::RDRuleInfo;

    // ── Helper constructors ──

    fn cat_info(name: &str, native_type: Option<&str>, is_primary: bool) -> CategoryInfo {
        CategoryInfo {
            name: name.to_string(),
            native_type: native_type.map(|s| s.to_string()),
            is_primary,
        }
    }

    fn make_rule_info(
        label: &str,
        category: &str,
        first_items: Vec<FirstItem>,
        is_infix: bool,
    ) -> RuleInfo {
        RuleInfo {
            label: label.to_string(),
            category: category.to_string(),
            first_items,
            is_infix,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        }
    }

    /// Minimal context builder for quick tests.
    struct CtxBuilder {
        categories: Vec<CategoryInfo>,
        rules: Vec<RuleInfo>,
        rd_rules: Vec<RDRuleInfo>,
        first_sets: HashMap<String, FirstSet>,
        follow_sets: HashMap<String, FirstSet>,
        bp_table: BindingPowerTable,
        prediction_wfsts: HashMap<String, PredictionWfst>,
        recovery_wfsts: Vec<RecoveryWfst>,
        cast_rules: Vec<CastRule>,
        cross_rules: Vec<CrossCategoryRule>,
        nfa_spillover_categories: HashSet<String>,
        recovery_config: RecoveryConfig,
        all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)>,
        follow_inputs: Vec<FollowSetInput>,
    }

    impl CtxBuilder {
        fn new() -> Self {
            CtxBuilder {
                categories: Vec::new(),
                rules: Vec::new(),
                rd_rules: Vec::new(),
                first_sets: HashMap::new(),
                follow_sets: HashMap::new(),
                bp_table: BindingPowerTable::new(),
                prediction_wfsts: HashMap::new(),
                recovery_wfsts: Vec::new(),
                cast_rules: Vec::new(),
                cross_rules: Vec::new(),
                nfa_spillover_categories: HashSet::new(),
                recovery_config: RecoveryConfig::default(),
                all_syntax: Vec::new(),
                follow_inputs: Vec::new(),
            }
        }

        fn ctx(&self) -> LintContext<'_> {
            LintContext {
                categories: &self.categories,
                rules: &self.rules,
                rd_rules: &self.rd_rules,
                first_sets: &self.first_sets,
                follow_sets: &self.follow_sets,
                bp_table: &self.bp_table,
                prediction_wfsts: &self.prediction_wfsts,
                recovery_wfsts: &self.recovery_wfsts,
                cast_rules: &self.cast_rules,
                cross_rules: &self.cross_rules,
                nfa_spillover_categories: &self.nfa_spillover_categories,
                recovery_config: &self.recovery_config,
                all_syntax: &self.all_syntax,
                follow_inputs: &self.follow_inputs,
            }
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // G01: Left Recursion
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g01_fires_on_left_recursive_rd_rule() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "BadRule".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::Terminal("@".to_string()),
                SyntaxItemSpec::Terminal("#".to_string()),
            ],
        ));

        let mut diags = Vec::new();
        lint_g01_left_recursion(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G01");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[test]
    fn g01_skips_infix_pattern() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Add".to_string(),
            "Int".to_string(),
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
        ));

        let mut diags = Vec::new();
        lint_g01_left_recursion(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G02: Unused Category
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g02_fires_on_unreferenced_category() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.categories.push(cat_info("Unused", None, false));
        b.all_syntax
            .push(("NumLit".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g02_unused_category(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G02");
        assert!(diags[0].message.contains("Unused"));
    }

    #[test]
    fn g02_does_not_fire_when_referenced() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax
            .push(("NumLit".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g02_unused_category(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G03: Ambiguous Prefix
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g03_fires_on_same_terminal() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.rules.push(make_rule_info(
            "Foo",
            "Int",
            vec![FirstItem::Terminal("!".to_string())],
            false,
        ));
        b.rules.push(make_rule_info(
            "Bar",
            "Int",
            vec![FirstItem::Terminal("!".to_string())],
            false,
        ));

        let mut diags = Vec::new();
        lint_g03_ambiguous_prefix(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G03");
    }

    #[test]
    fn g03_skips_infix_rules() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.rules.push(make_rule_info(
            "Add",
            "Int",
            vec![FirstItem::Terminal("+".to_string())],
            true,
        ));
        b.rules.push(make_rule_info(
            "Pos",
            "Int",
            vec![FirstItem::Terminal("+".to_string())],
            false,
        ));

        let mut diags = Vec::new();
        lint_g03_ambiguous_prefix(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G04: Duplicate Rule Label
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g04_fires_on_duplicate_label() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push(("Add".to_string(), "Int".to_string(), vec![]));
        b.all_syntax.push(("Add".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g04_duplicate_rule_label(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G04");
        assert_eq!(diags[0].severity, LintSeverity::Error);
    }

    #[test]
    fn g04_allows_same_label_different_category() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.categories.push(cat_info("Float", None, false));
        b.all_syntax.push(("Add".to_string(), "Int".to_string(), vec![]));
        b.all_syntax.push(("Add".to_string(), "Float".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g04_duplicate_rule_label(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G05: Empty Category
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g05_fires_on_empty_category() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.categories.push(cat_info("Empty", None, false));
        b.all_syntax.push(("NumLit".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g05_empty_category(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G05");
        assert!(diags[0].message.contains("Empty"));
    }

    #[test]
    fn g05_does_not_fire_when_has_rules() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push(("NumLit".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g05_empty_category(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G07: Identical Rules
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g07_fires_on_identical_syntax() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        let syntax = vec![
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal(")".to_string()),
        ];
        b.all_syntax
            .push(("Group1".to_string(), "Int".to_string(), syntax.clone()));
        b.all_syntax
            .push(("Group2".to_string(), "Int".to_string(), syntax));

        let mut diags = Vec::new();
        lint_g07_identical_rules(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G07");
    }

    #[test]
    fn g07_does_not_fire_on_different_syntax() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Neg".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::Terminal("-".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
            ],
        ));
        b.all_syntax.push((
            "Not".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::Terminal("~".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
            ],
        ));

        let mut diags = Vec::new();
        lint_g07_identical_rules(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G08: Missing Cast to Root
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g08_fires_when_no_cast_path() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        // No cast rules from Int to Proc

        let mut diags = Vec::new();
        lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G08");
        assert!(diags[0].message.contains("Int"));
    }

    #[test]
    fn g08_does_not_fire_with_cast_path() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });

        let mut diags = Vec::new();
        lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G09: Unbalanced Delimiters
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g09_fires_on_unbalanced() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Bad".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                // Missing ")"
            ],
        ));

        let mut diags = Vec::new();
        lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G09");
    }

    #[test]
    fn g09_does_not_fire_on_balanced() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Group".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::Terminal(")".to_string()),
            ],
        ));

        let mut diags = Vec::new();
        lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G10: Ambiguous Associativity
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g10_fires_on_mixed_associativity() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.bp_table.operators.push(InfixOperator {
            terminal: "+".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 3,
            label: "Add".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });
        b.bp_table.operators.push(InfixOperator {
            terminal: "-".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 1, // Right-associative at same left_bp
            label: "Sub".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });

        let mut diags = Vec::new();
        lint_g10_ambiguous_associativity(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G10");
    }

    #[test]
    fn g10_does_not_fire_on_same_associativity() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.bp_table.operators.push(InfixOperator {
            terminal: "+".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 3,
            label: "Add".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });
        b.bp_table.operators.push(InfixOperator {
            terminal: "-".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 3, // Same left-assoc
            label: "Sub".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });

        let mut diags = Vec::new();
        lint_g10_ambiguous_associativity(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // R06: Inverted Recovery Costs
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn r06_fires_on_inverted_costs() {
        let mut b = CtxBuilder::new();
        b.recovery_config.skip_per_token = 3.0; // Higher than insert!
        b.recovery_config.insert_cost = 1.0;

        let mut diags = Vec::new();
        lint_r06_inverted_recovery_costs(&b.ctx(), &mut diags);

        assert!(diags.iter().any(|d| d.id == "R06"));
    }

    #[test]
    fn r06_does_not_fire_on_default_config() {
        let b = CtxBuilder::new();

        let mut diags = Vec::new();
        lint_r06_inverted_recovery_costs(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // R07: Transposition Candidate
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn r07_fires_on_edit_distance_one() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Add".to_string(),
            "Int".to_string(),
            vec![SyntaxItemSpec::Terminal("+".to_string())],
        ));
        b.all_syntax.push((
            "Inc".to_string(),
            "Int".to_string(),
            vec![SyntaxItemSpec::Terminal("++".to_string())],
        ));

        let mut diags = Vec::new();
        lint_r07_transposition_candidate(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "R07");
        assert!(diags[0].message.contains("+") && diags[0].message.contains("++"));
    }

    #[test]
    fn r07_does_not_fire_on_distant_operators() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Add".to_string(),
            "Int".to_string(),
            vec![SyntaxItemSpec::Terminal("++".to_string())],
        ));
        b.all_syntax.push((
            "Arrow".to_string(),
            "Int".to_string(),
            vec![SyntaxItemSpec::Terminal("->".to_string())],
        ));

        let mut diags = Vec::new();
        lint_r07_transposition_candidate(&b.ctx(), &mut diags);
        assert!(diags.is_empty(), "operators `++` and `->` differ by 2 chars: {:?}", diags);
    }

    // ══════════════════════════════════════════════════════════════════════
    // C01: Cast Cycle
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn c01_fires_on_cycle() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.categories.push(cat_info("Proc", None, false));
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "ProcToInt".to_string(),
            source_category: "Proc".to_string(),
            target_category: "Int".to_string(),
        });

        let mut diags = Vec::new();
        lint_c01_cast_cycle(&b.ctx(), &mut diags);

        assert!(diags.iter().any(|d| d.id == "C01" && d.severity == LintSeverity::Error));
    }

    #[test]
    fn c01_does_not_fire_on_dag() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        b.categories.push(cat_info("Bool", None, false));
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "BoolToProc".to_string(),
            source_category: "Bool".to_string(),
            target_category: "Proc".to_string(),
        });

        let mut diags = Vec::new();
        lint_c01_cast_cycle(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // C02: Transitive Cast Redundancy
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn c02_fires_on_redundant_direct_cast() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        b.categories.push(cat_info("Bool", None, false));
        // Int → Bool → Proc (transitive) AND Int → Proc (direct)
        b.cast_rules.push(CastRule {
            label: "IntToBool".to_string(),
            source_category: "Int".to_string(),
            target_category: "Bool".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "BoolToProc".to_string(),
            source_category: "Bool".to_string(),
            target_category: "Proc".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });

        let mut diags = Vec::new();
        lint_c02_transitive_cast_redundancy(&b.ctx(), &mut diags);

        assert!(diags.iter().any(|d| d.id == "C02"));
    }

    #[test]
    fn c02_does_not_fire_without_indirect_path() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });

        let mut diags = Vec::new();
        lint_c02_transitive_cast_redundancy(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // P02: High NFA Spillover
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn p02_fires_on_many_spillover_categories() {
        let mut b = CtxBuilder::new();
        b.nfa_spillover_categories = ["A", "B", "C", "D"]
            .iter()
            .map(|s| s.to_string())
            .collect();

        let mut diags = Vec::new();
        lint_p02_high_nfa_spillover(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "P02");
    }

    #[test]
    fn p02_does_not_fire_on_few() {
        let mut b = CtxBuilder::new();
        b.nfa_spillover_categories = ["A"].iter().map(|s| s.to_string()).collect();

        let mut diags = Vec::new();
        lint_p02_high_nfa_spillover(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // P03: Deep Cast Nesting
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn p03_fires_on_deep_chain() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("A", None, true));
        b.categories.push(cat_info("B", None, false));
        b.categories.push(cat_info("C", None, false));
        b.categories.push(cat_info("D", None, false));
        b.categories.push(cat_info("E", None, false));
        // A → B → C → D → E (depth 4)
        b.cast_rules.push(CastRule {
            label: "AtoB".to_string(),
            source_category: "A".to_string(),
            target_category: "B".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "BtoC".to_string(),
            source_category: "B".to_string(),
            target_category: "C".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "CtoD".to_string(),
            source_category: "C".to_string(),
            target_category: "D".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "DtoE".to_string(),
            source_category: "D".to_string(),
            target_category: "E".to_string(),
        });

        let mut diags = Vec::new();
        lint_p03_deep_cast_nesting(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "P03");
    }

    #[test]
    fn p03_does_not_fire_on_shallow() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("A", None, true));
        b.categories.push(cat_info("B", None, false));
        b.cast_rules.push(CastRule {
            label: "AtoB".to_string(),
            source_category: "A".to_string(),
            target_category: "B".to_string(),
        });

        let mut diags = Vec::new();
        lint_p03_deep_cast_nesting(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // Display formatting
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn lint_display_format() {
        let diag = LintDiagnostic {
            id: "C01",
            name: "cast-cycle",
            severity: LintSeverity::Error,
            category: None,
            rule: None,
            message: "cast cycle detected: Int -> Proc -> Int".to_string(),
            hint: Some("break the cycle by removing one cast direction".to_string()),
        };
        let s = format!("{}", diag);
        assert!(s.contains("error[C01]"));
        assert!(s.contains("cast cycle detected"));
        assert!(s.contains("= hint:"));
    }

    #[test]
    fn lint_display_no_hint() {
        let diag = LintDiagnostic {
            id: "G06",
            name: "shadowed-operator",
            severity: LintSeverity::Note,
            category: Some("Int".to_string()),
            rule: None,
            message: "operator `-` is both infix and prefix".to_string(),
            hint: None,
        };
        let s = format!("{}", diag);
        assert!(s.contains("note[G06]"));
        assert!(!s.contains("hint"));
    }

    // ══════════════════════════════════════════════════════════════════════
    // char_edit_distance_is_one
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn edit_distance_one_substitution() {
        assert!(char_edit_distance_is_one("+", "*")); // single char sub
        assert!(char_edit_distance_is_one("<=", ">="));
    }

    #[test]
    fn edit_distance_one_insertion() {
        assert!(char_edit_distance_is_one("+", "++")); // insertion
        assert!(char_edit_distance_is_one("<", "<="));
    }

    #[test]
    fn edit_distance_not_one() {
        assert!(!char_edit_distance_is_one("+", "---")); // too different
        assert!(char_edit_distance_is_one("==", "!=")); // 1 sub (first char)
        assert!(!char_edit_distance_is_one("+", "+")); // zero distance
        assert!(!char_edit_distance_is_one("<<", ">>")); // 2 subs
    }
}
