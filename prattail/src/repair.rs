//! Analysis-driven repair suggestion engine.
//!
//! Transforms analysis diagnostics into actionable repair suggestions for
//! `language!` specs and programs written in those languages. Each analysis
//! that detects a failure can produce `RepairSuggestion` instances ranked
//! by semiring-guided criteria (edit cost, confidence, alternative count).
//!
//! ## Integration
//!
//! The repair engine integrates with the existing lint infrastructure (23 lints)
//! by following the same structured diagnostic pattern with severity levels
//! and hints.

use std::fmt;

/// A repair suggestion produced by an analysis.
///
/// Each suggestion describes a concrete fix for a detected issue,
/// along with confidence and cost metrics.
#[derive(Debug, Clone)]
pub struct RepairSuggestion {
    /// Short identifier for the repair type (e.g., "add-rule", "fix-confluence").
    pub kind: RepairKind,
    /// Human-readable description of the suggested fix.
    pub description: String,
    /// Confidence that this fix is correct, in [0.0, 1.0].
    /// Derived from FuzzyWeight when available.
    pub confidence: f64,
    /// Minimum edit cost to apply this fix (lower = simpler fix).
    /// Derived from EditWeight when available.
    pub edit_cost: u32,
    /// Number of alternative fixes available (from CountingWeight).
    pub alternative_count: u64,
    /// The specific code/rule change to apply.
    pub action: RepairAction,
}

/// Categories of repair suggestions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RepairKind {
    /// Add a missing grammar rule.
    AddRule,
    /// Add a cross-category reference to make a rule reachable.
    AddCrossRef,
    /// Disambiguate an ambiguous prefix.
    Disambiguate,
    /// Add a missing congruence rule.
    AddCongruence,
    /// Add an equation or rewrite to fix confluence.
    FixConfluence,
    /// Add a guard to break a non-terminating cycle.
    FixTermination,
    /// Strengthen a precondition for a Hoare triple.
    StrengthenPrecondition,
    /// Weaken a postcondition for a Hoare triple.
    WeakenPostcondition,
    /// Add a transition to fix bisimulation failure.
    FixBisimulation,
    /// Add a morphism translation case.
    CompleteMorphism,
    /// Generic custom repair.
    Custom(String),
}

/// A concrete repair action.
#[derive(Debug, Clone)]
pub enum RepairAction {
    /// Add a new rule to a category.
    AddRuleToCategory {
        category: String,
        rule_skeleton: String,
    },
    /// Add a cross-category reference.
    AddCrossCategoryRef {
        from_category: String,
        to_category: String,
        rule_label: String,
    },
    /// Add a congruence rule for a constructor.
    AddCongruenceRule {
        constructor: String,
        category: String,
        rule_text: String,
    },
    /// Add an equation.
    AddEquation {
        lhs: String,
        rhs: String,
    },
    /// Add a rewrite rule.
    AddRewrite {
        lhs: String,
        rhs: String,
        direction: String,
    },
    /// Textual description of the fix (for complex repairs).
    Description(String),
}

impl fmt::Display for RepairSuggestion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{:?}] {} (confidence: {:.2}, edit cost: {}, alternatives: {})",
            self.kind, self.description, self.confidence, self.edit_cost, self.alternative_count
        )
    }
}

impl RepairSuggestion {
    /// Create a simple repair suggestion with default metrics.
    pub fn new(kind: RepairKind, description: impl Into<String>, action: RepairAction) -> Self {
        RepairSuggestion {
            kind,
            description: description.into(),
            confidence: 1.0,
            edit_cost: 1,
            alternative_count: 1,
            action,
        }
    }

    /// Set the confidence level.
    pub fn with_confidence(mut self, confidence: f64) -> Self {
        self.confidence = confidence;
        self
    }

    /// Set the edit cost.
    pub fn with_edit_cost(mut self, cost: u32) -> Self {
        self.edit_cost = cost;
        self
    }

    /// Set the alternative count.
    pub fn with_alternatives(mut self, count: u64) -> Self {
        self.alternative_count = count;
        self
    }
}

/// A collection of repair suggestions, sortable by different criteria.
#[derive(Debug, Clone, Default)]
pub struct RepairSet {
    pub suggestions: Vec<RepairSuggestion>,
}

impl RepairSet {
    /// Create an empty repair set.
    pub fn new() -> Self {
        RepairSet { suggestions: Vec::new() }
    }

    /// Add a suggestion.
    pub fn add(&mut self, suggestion: RepairSuggestion) {
        self.suggestions.push(suggestion);
    }

    /// Sort by confidence (highest first).
    pub fn sort_by_confidence(&mut self) {
        self.suggestions.sort_by(|a, b| {
            b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal)
        });
    }

    /// Sort by edit cost (lowest first).
    pub fn sort_by_edit_cost(&mut self) {
        self.suggestions.sort_by_key(|s| s.edit_cost);
    }

    /// Sort by alternative count (most alternatives first).
    pub fn sort_by_alternatives(&mut self) {
        self.suggestions.sort_by(|a, b| b.alternative_count.cmp(&a.alternative_count));
    }

    /// Get the best suggestion by confidence.
    pub fn best_by_confidence(&self) -> Option<&RepairSuggestion> {
        self.suggestions.iter().max_by(|a, b| {
            a.confidence.partial_cmp(&b.confidence).unwrap_or(std::cmp::Ordering::Equal)
        })
    }

    /// Get the cheapest fix.
    pub fn cheapest(&self) -> Option<&RepairSuggestion> {
        self.suggestions.iter().min_by_key(|s| s.edit_cost)
    }
}

// =============================================================================
// Grammar completion suggestions (Phase 5C.2)
// =============================================================================

/// Suggest rules to add for tokens that have no dispatch target in a category.
///
/// `category` is the name of the grammar category. `missing_tokens` is a list
/// of terminal tokens that appear in FIRST sets of other categories but have
/// no rule starting with them in this category.
pub fn suggest_missing_rules(
    category: &str,
    missing_tokens: &[&str],
) -> RepairSet {
    let mut set = RepairSet::new();
    for token in missing_tokens {
        let skeleton = format!("NewRule . {} ::= \"{}\" ... ;", category, token);
        set.add(
            RepairSuggestion::new(
                RepairKind::AddRule,
                format!("Add a rule to {} starting with terminal '{}'", category, token),
                RepairAction::AddRuleToCategory {
                    category: category.to_string(),
                    rule_skeleton: skeleton,
                },
            )
            .with_confidence(0.7)
            .with_edit_cost(2),
        );
    }
    set
}

/// Suggest cross-category references to make dead rules reachable.
///
/// `dead_rule` is the unreachable rule label. `dead_category` is the category it
/// belongs to. `reachable_categories` are categories that ARE reachable and could
/// reference the dead category.
pub fn suggest_cross_category_ref(
    dead_rule: &str,
    dead_category: &str,
    reachable_categories: &[&str],
) -> RepairSet {
    let mut set = RepairSet::new();
    for cat in reachable_categories {
        let label = format!("Ref{}", dead_category);
        set.add(
            RepairSuggestion::new(
                RepairKind::AddCrossRef,
                format!(
                    "Add reference from {} to {} to make rule '{}' reachable",
                    cat, dead_category, dead_rule
                ),
                RepairAction::AddCrossCategoryRef {
                    from_category: cat.to_string(),
                    to_category: dead_category.to_string(),
                    rule_label: label,
                },
            )
            .with_confidence(0.85)
            .with_edit_cost(1),
        );
    }
    set
}

// =============================================================================
// Congruence rule synthesis (Phase 5C.3)
// =============================================================================

/// Suggest congruence rules for constructors that lack them.
///
/// `constructor` is the constructor name, `category` is the grammar category,
/// and `arity` is the number of arguments. Generates one congruence rule per
/// argument position.
pub fn suggest_congruence_rules(
    constructor: &str,
    category: &str,
    arity: usize,
) -> RepairSet {
    let mut set = RepairSet::new();
    for pos in 0..arity {
        let mut args_lhs = Vec::with_capacity(arity);
        let mut args_rhs = Vec::with_capacity(arity);
        for i in 0..arity {
            if i == pos {
                args_lhs.push("S".to_string());
                args_rhs.push("T".to_string());
            } else {
                args_lhs.push(format!("X{}", i));
                args_rhs.push(format!("X{}", i));
            }
        }
        let lhs = format!("({} {})", constructor, args_lhs.join(" "));
        let rhs = format!("({} {})", constructor, args_rhs.join(" "));
        let rule_text = format!(
            "{}Cong{} . |- S ~> T |- {} ~> {} ;",
            constructor, pos, lhs, rhs
        );

        set.add(
            RepairSuggestion::new(
                RepairKind::AddCongruence,
                format!(
                    "Add congruence rule for {} at argument position {}",
                    constructor, pos
                ),
                RepairAction::AddCongruenceRule {
                    constructor: constructor.to_string(),
                    category: category.to_string(),
                    rule_text,
                },
            )
            .with_confidence(0.95)
            .with_edit_cost(1),
        );
    }
    set
}

// =============================================================================
// Semiring-ranked repair (Phase 5C.5)
// =============================================================================

impl RepairSet {
    /// Merge another RepairSet into this one, deduplicating by description.
    pub fn merge(&mut self, other: &RepairSet) {
        let existing: std::collections::HashSet<String> = self
            .suggestions
            .iter()
            .map(|s| s.description.clone())
            .collect();
        for s in &other.suggestions {
            if !existing.contains(&s.description) {
                self.suggestions.push(s.clone());
            }
        }
    }

    /// Return the number of suggestions.
    pub fn len(&self) -> usize {
        self.suggestions.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.suggestions.is_empty()
    }

    /// Filter suggestions by minimum confidence threshold.
    pub fn filter_by_confidence(&self, min_confidence: f64) -> RepairSet {
        RepairSet {
            suggestions: self
                .suggestions
                .iter()
                .filter(|s| s.confidence >= min_confidence)
                .cloned()
                .collect(),
        }
    }

    /// Filter suggestions by maximum edit cost.
    pub fn filter_by_max_cost(&self, max_cost: u32) -> RepairSet {
        RepairSet {
            suggestions: self
                .suggestions
                .iter()
                .filter(|s| s.edit_cost <= max_cost)
                .cloned()
                .collect(),
        }
    }

    /// Get the top N suggestions by confidence (highest first).
    pub fn top_n_by_confidence(&self, n: usize) -> Vec<&RepairSuggestion> {
        let mut sorted: Vec<&RepairSuggestion> = self.suggestions.iter().collect();
        sorted.sort_by(|a, b| {
            b.confidence
                .partial_cmp(&a.confidence)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        sorted.truncate(n);
        sorted
    }

    /// Get the top N suggestions by cheapest edit cost (lowest first).
    pub fn top_n_by_cost(&self, n: usize) -> Vec<&RepairSuggestion> {
        let mut sorted: Vec<&RepairSuggestion> = self.suggestions.iter().collect();
        sorted.sort_by_key(|s| s.edit_cost);
        sorted.truncate(n);
        sorted
    }

    /// Multi-criteria ranking: score = confidence / (edit_cost + 1).
    /// Higher score = better suggestion.
    pub fn rank_multi_criteria(&self) -> Vec<(&RepairSuggestion, f64)> {
        let mut ranked: Vec<(&RepairSuggestion, f64)> = self
            .suggestions
            .iter()
            .map(|s| {
                let score = s.confidence / (s.edit_cost as f64 + 1.0);
                (s, score)
            })
            .collect();
        ranked.sort_by(|a, b| {
            b.1.partial_cmp(&a.1)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        ranked
    }
}

// =============================================================================
// Context-sensitive codegen analysis (Phase 5B.3)
// =============================================================================

/// A context-specific dispatch recommendation.
#[derive(Debug, Clone)]
pub struct ContextDispatchHint {
    /// The category being dispatched.
    pub category: String,
    /// The calling context (category that calls into this one).
    pub caller: String,
    /// Rules that are valid in this context.
    pub valid_rules: Vec<String>,
    /// Rules that can be skipped in this context (dead in this context).
    pub skippable_rules: Vec<String>,
}

/// Analyze context-sensitive dispatch opportunities.
///
/// Given a map of `(category, caller_context) → valid_rule_labels`,
/// identify categories where different callers enable different rule subsets.
/// Returns hints for generating caller-specific dispatch code.
pub fn analyze_context_dispatch(
    context_rules: &std::collections::HashMap<(String, String), Vec<String>>,
    all_rules: &std::collections::HashMap<String, Vec<String>>,
) -> Vec<ContextDispatchHint> {
    let mut hints = Vec::new();

    for ((category, caller), valid) in context_rules {
        let all = match all_rules.get(category) {
            Some(r) => r,
            None => continue,
        };

        // Only generate a hint if this context narrows the rule set
        if valid.len() < all.len() {
            let valid_set: std::collections::HashSet<&str> =
                valid.iter().map(|s| s.as_str()).collect();
            let skippable: Vec<String> = all
                .iter()
                .filter(|r| !valid_set.contains(r.as_str()))
                .cloned()
                .collect();

            hints.push(ContextDispatchHint {
                category: category.clone(),
                caller: caller.clone(),
                valid_rules: valid.clone(),
                skippable_rules: skippable,
            });
        }
    }

    hints
}

// =============================================================================
// Congruence rule fusion analysis (Phase 5B.4)
// =============================================================================

/// A fusion recommendation for congruence rules sharing the same constructor.
#[derive(Debug, Clone)]
pub struct CongruenceFusionHint {
    /// The constructor name.
    pub constructor: String,
    /// The category this constructor belongs to.
    pub category: String,
    /// Number of congruence rules that can be fused.
    pub rule_count: usize,
    /// Argument positions covered by the fused rule.
    pub argument_positions: Vec<usize>,
}

/// Analyze congruence rules for fusion opportunities.
///
/// Groups congruence rules by constructor and identifies cases where multiple
/// rules can be merged into a single match arm that rewrites all argument
/// positions in parallel.
///
/// `rules` is a list of `(constructor, category, argument_position)` triples
/// representing existing congruence rules.
pub fn analyze_congruence_fusion(
    rules: &[(String, String, usize)],
) -> Vec<CongruenceFusionHint> {
    let mut by_constructor: std::collections::HashMap<
        (String, String),
        Vec<usize>,
    > = std::collections::HashMap::new();

    for (constructor, category, pos) in rules {
        by_constructor
            .entry((constructor.clone(), category.clone()))
            .or_default()
            .push(*pos);
    }

    let mut hints = Vec::new();
    for ((constructor, category), mut positions) in by_constructor {
        if positions.len() > 1 {
            positions.sort_unstable();
            positions.dedup();
            hints.push(CongruenceFusionHint {
                constructor,
                category,
                rule_count: positions.len(),
                argument_positions: positions,
            });
        }
    }

    hints
}

// =============================================================================
// Lint integration (Phase 5C.8)
// =============================================================================

/// A structured diagnostic that integrates repair suggestions with the
/// existing lint framework.
#[derive(Debug, Clone)]
pub struct RepairDiagnostic {
    /// Lint code (e.g., "W01", "G03").
    pub lint_code: String,
    /// Severity level.
    pub severity: DiagnosticSeverity,
    /// Short message describing the issue.
    pub message: String,
    /// Repair suggestions for this diagnostic.
    pub repairs: RepairSet,
}

/// Diagnostic severity levels (matching existing lint infrastructure).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    /// Informational note.
    Note,
    /// Warning (may indicate a problem).
    Warning,
    /// Error (must be fixed).
    Error,
}

impl fmt::Display for DiagnosticSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DiagnosticSeverity::Note => write!(f, "note"),
            DiagnosticSeverity::Warning => write!(f, "warning"),
            DiagnosticSeverity::Error => write!(f, "error"),
        }
    }
}

impl fmt::Display for RepairDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}-{}] {}", self.lint_code, self.severity, self.message)?;
        if !self.repairs.is_empty() {
            write!(f, "\n  Suggestions:")?;
            for (i, s) in self.repairs.suggestions.iter().enumerate() {
                write!(
                    f,
                    "\n    {}. {} (confidence: {:.0}%, cost: {})",
                    i + 1,
                    s.description,
                    s.confidence * 100.0,
                    s.edit_cost
                )?;
            }
        }
        Ok(())
    }
}

impl RepairDiagnostic {
    /// Create a diagnostic from a lint code and message with optional repairs.
    pub fn new(
        lint_code: impl Into<String>,
        severity: DiagnosticSeverity,
        message: impl Into<String>,
    ) -> Self {
        RepairDiagnostic {
            lint_code: lint_code.into(),
            severity,
            message: message.into(),
            repairs: RepairSet::new(),
        }
    }

    /// Attach repair suggestions to this diagnostic.
    pub fn with_repairs(mut self, repairs: RepairSet) -> Self {
        self.repairs = repairs;
        self
    }

    /// Create a dead-rule diagnostic with cross-category repair suggestions.
    pub fn dead_rule(
        rule_label: &str,
        category: &str,
        reachable_categories: &[&str],
    ) -> Self {
        let repairs = suggest_cross_category_ref(rule_label, category, reachable_categories);
        RepairDiagnostic::new(
            "W01",
            DiagnosticSeverity::Warning,
            format!("dead rule '{}' in category '{}'", rule_label, category),
        )
        .with_repairs(repairs)
    }

    /// Create a missing-rule diagnostic with rule addition suggestions.
    pub fn missing_rule(category: &str, missing_tokens: &[&str]) -> Self {
        let repairs = suggest_missing_rules(category, missing_tokens);
        RepairDiagnostic::new(
            "G03",
            DiagnosticSeverity::Warning,
            format!(
                "category '{}' has no rules for tokens: {}",
                category,
                missing_tokens.join(", ")
            ),
        )
        .with_repairs(repairs)
    }

    /// Create a missing-congruence diagnostic with congruence rule suggestions.
    pub fn missing_congruence(constructor: &str, category: &str, arity: usize) -> Self {
        let repairs = suggest_congruence_rules(constructor, category, arity);
        RepairDiagnostic::new(
            "G03",
            DiagnosticSeverity::Note,
            format!(
                "constructor '{}' in '{}' has no congruence rules",
                constructor, category
            ),
        )
        .with_repairs(repairs)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline repair enrichment
// ══════════════════════════════════════════════════════════════════════════════

/// Enrich lint diagnostics with TRS repair suggestions.
///
/// Scans diagnostics for T01 (non-joinable critical pair) codes and appends
/// repair hint text from the confluence analysis.
#[cfg(feature = "trs-analysis")]
pub fn enrich_diagnostics_with_repairs(
    diagnostics: &mut Vec<crate::lint::LintDiagnostic>,
    confluence_result: Option<&crate::confluence::ConfluenceAnalysis>,
    _all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) {
    let analysis = match confluence_result {
        Some(a) if !a.is_confluent => a,
        _ => return,
    };

    let repairs = crate::confluence::suggest_confluence_repairs(analysis);
    if repairs.suggestions.is_empty() {
        return;
    }

    // Append repair hints to T01 diagnostics
    for diag in diagnostics.iter_mut() {
        if diag.id == "T01" {
            let repair_text: Vec<String> = repairs
                .suggestions
                .iter()
                .map(|s| format!("{}", s))
                .collect();
            let combined = repair_text.join("; ");
            if let Some(ref mut hint) = diag.hint {
                hint.push_str(&format!(" [repair: {}]", combined));
            } else {
                diag.hint = Some(format!("repair: {}", combined));
            }
        }
    }
}

/// Enrich lint diagnostics with morphism repair suggestions.
///
/// Scans diagnostics for M01 (morphism gap) codes and appends
/// repair descriptions based on the gap kind.
#[cfg(feature = "morphisms")]
pub fn enrich_diagnostics_with_morphism_repairs(
    diagnostics: &mut Vec<crate::lint::LintDiagnostic>,
    morphism_result: Option<&crate::morphism::MorphismCheck>,
) {
    let check = match morphism_result {
        Some(c) if !c.is_complete => c,
        _ => return,
    };

    if check.gaps.is_empty() {
        return;
    }

    // Append repair hints to M01 diagnostics based on gap kind
    for diag in diagnostics.iter_mut() {
        if diag.id == "M01" {
            let repair_text = format!(
                "{} gap(s) detected — add cross-category rules or constructor mappings to complete the morphism",
                check.gaps.len(),
            );
            if let Some(ref mut hint) = diag.hint {
                hint.push_str(&format!(" [repair: {}]", repair_text));
            } else {
                diag.hint = Some(format!("repair: {}", repair_text));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_repair_suggestion_display() {
        let r = RepairSuggestion::new(
            RepairKind::AddRule,
            "Add rule LetIn to Expr",
            RepairAction::AddRuleToCategory {
                category: "Expr".to_string(),
                rule_skeleton: "LetIn . Expr ::= \"let\" Expr \"in\" Expr ;".to_string(),
            },
        );
        let s = r.to_string();
        assert!(s.contains("AddRule"));
        assert!(s.contains("Add rule LetIn to Expr"));
    }

    #[test]
    fn test_repair_set_sort_by_confidence() {
        let mut set = RepairSet::new();
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "low", RepairAction::Description("low".into()),
        ).with_confidence(0.3));
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "high", RepairAction::Description("high".into()),
        ).with_confidence(0.9));
        set.sort_by_confidence();
        assert_eq!(set.suggestions[0].description, "high");
    }

    #[test]
    fn test_repair_set_cheapest() {
        let mut set = RepairSet::new();
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "expensive", RepairAction::Description("e".into()),
        ).with_edit_cost(5));
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "cheap", RepairAction::Description("c".into()),
        ).with_edit_cost(1));
        let cheapest = set.cheapest().expect("should have suggestions");
        assert_eq!(cheapest.description, "cheap");
    }

    // =========================================================================
    // Grammar completion tests (Phase 5C.2)
    // =========================================================================

    #[test]
    fn test_suggest_missing_rules() {
        let set = suggest_missing_rules("Expr", &["let", "match"]);
        assert_eq!(set.len(), 2);
        assert!(set.suggestions[0].description.contains("let"));
        assert!(set.suggestions[1].description.contains("match"));
        assert_eq!(set.suggestions[0].kind, RepairKind::AddRule);
    }

    #[test]
    fn test_suggest_cross_category_ref() {
        let set = suggest_cross_category_ref("LetIn", "Expr", &["Stmt", "Decl"]);
        assert_eq!(set.len(), 2);
        assert!(set.suggestions[0].description.contains("Stmt"));
        assert_eq!(set.suggestions[0].kind, RepairKind::AddCrossRef);
    }

    // =========================================================================
    // Congruence rule synthesis tests (Phase 5C.3)
    // =========================================================================

    #[test]
    fn test_suggest_congruence_binary() {
        let set = suggest_congruence_rules("Add", "Expr", 2);
        assert_eq!(set.len(), 2); // One per argument position
        assert_eq!(set.suggestions[0].kind, RepairKind::AddCongruence);
        assert!(set.suggestions[0].description.contains("position 0"));
        assert!(set.suggestions[1].description.contains("position 1"));
    }

    #[test]
    fn test_suggest_congruence_unary() {
        let set = suggest_congruence_rules("Neg", "Expr", 1);
        assert_eq!(set.len(), 1);
        assert!(set.suggestions[0].description.contains("position 0"));
    }

    // =========================================================================
    // Semiring-ranked repair tests (Phase 5C.5)
    // =========================================================================

    #[test]
    fn test_repair_set_merge_dedup() {
        let mut set1 = RepairSet::new();
        set1.add(RepairSuggestion::new(
            RepairKind::AddRule, "fix A", RepairAction::Description("a".into()),
        ));
        let mut set2 = RepairSet::new();
        set2.add(RepairSuggestion::new(
            RepairKind::AddRule, "fix A", RepairAction::Description("a".into()),
        ));
        set2.add(RepairSuggestion::new(
            RepairKind::AddRule, "fix B", RepairAction::Description("b".into()),
        ));
        set1.merge(&set2);
        assert_eq!(set1.len(), 2); // "fix A" deduplicated
    }

    #[test]
    fn test_filter_by_confidence() {
        let mut set = RepairSet::new();
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "low", RepairAction::Description("l".into()),
        ).with_confidence(0.3));
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "high", RepairAction::Description("h".into()),
        ).with_confidence(0.9));
        let filtered = set.filter_by_confidence(0.5);
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered.suggestions[0].description, "high");
    }

    #[test]
    fn test_filter_by_max_cost() {
        let mut set = RepairSet::new();
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "cheap", RepairAction::Description("c".into()),
        ).with_edit_cost(1));
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "expensive", RepairAction::Description("e".into()),
        ).with_edit_cost(10));
        let filtered = set.filter_by_max_cost(5);
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered.suggestions[0].description, "cheap");
    }

    #[test]
    fn test_top_n_by_confidence() {
        let mut set = RepairSet::new();
        for i in 0..5 {
            set.add(RepairSuggestion::new(
                RepairKind::AddRule,
                format!("fix{}", i),
                RepairAction::Description(format!("{}", i)),
            ).with_confidence(i as f64 * 0.2));
        }
        let top = set.top_n_by_confidence(2);
        assert_eq!(top.len(), 2);
        assert_eq!(top[0].description, "fix4"); // highest confidence
        assert_eq!(top[1].description, "fix3");
    }

    #[test]
    fn test_rank_multi_criteria() {
        let mut set = RepairSet::new();
        // High confidence, high cost → moderate score
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "a", RepairAction::Description("a".into()),
        ).with_confidence(0.9).with_edit_cost(9));
        // Moderate confidence, low cost → high score
        set.add(RepairSuggestion::new(
            RepairKind::AddRule, "b", RepairAction::Description("b".into()),
        ).with_confidence(0.8).with_edit_cost(1));
        let ranked = set.rank_multi_criteria();
        // b has score 0.8/2 = 0.4, a has score 0.9/10 = 0.09
        assert_eq!(ranked[0].0.description, "b");
    }

    // =========================================================================
    // Lint integration tests (Phase 5C.8)
    // =========================================================================

    #[test]
    fn test_repair_diagnostic_dead_rule() {
        let diag = RepairDiagnostic::dead_rule("LetIn", "Expr", &["Stmt"]);
        assert_eq!(diag.lint_code, "W01");
        assert_eq!(diag.severity, DiagnosticSeverity::Warning);
        assert!(!diag.repairs.is_empty());
        let s = diag.to_string();
        assert!(s.contains("W01"));
        assert!(s.contains("dead rule"));
    }

    #[test]
    fn test_repair_diagnostic_missing_rule() {
        let diag = RepairDiagnostic::missing_rule("Expr", &["let"]);
        assert!(!diag.repairs.is_empty());
        assert!(diag.message.contains("let"));
    }

    #[test]
    fn test_repair_diagnostic_missing_congruence() {
        let diag = RepairDiagnostic::missing_congruence("Add", "Expr", 2);
        assert_eq!(diag.severity, DiagnosticSeverity::Note);
        assert_eq!(diag.repairs.len(), 2);
    }

    // =========================================================================
    // Context-sensitive codegen tests (Phase 5B.3)
    // =========================================================================

    #[test]
    fn test_context_dispatch_analysis() {
        use std::collections::HashMap;
        let mut context_rules = HashMap::new();
        // In context "Stmt", Expr only uses rules ["Num", "Add"]
        context_rules.insert(
            ("Expr".to_string(), "Stmt".to_string()),
            vec!["Num".to_string(), "Add".to_string()],
        );
        // In context "Decl", Expr uses all rules
        context_rules.insert(
            ("Expr".to_string(), "Decl".to_string()),
            vec!["Num".to_string(), "Add".to_string(), "LetIn".to_string()],
        );

        let mut all_rules = HashMap::new();
        all_rules.insert(
            "Expr".to_string(),
            vec!["Num".to_string(), "Add".to_string(), "LetIn".to_string()],
        );

        let hints = analyze_context_dispatch(&context_rules, &all_rules);
        // Only Stmt context narrows the rule set
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].caller, "Stmt");
        assert_eq!(hints[0].skippable_rules, vec!["LetIn"]);
    }

    #[test]
    fn test_context_dispatch_no_narrowing() {
        use std::collections::HashMap;
        let mut context_rules = HashMap::new();
        context_rules.insert(
            ("Expr".to_string(), "Root".to_string()),
            vec!["A".to_string(), "B".to_string()],
        );
        let mut all_rules = HashMap::new();
        all_rules.insert("Expr".to_string(), vec!["A".to_string(), "B".to_string()]);

        let hints = analyze_context_dispatch(&context_rules, &all_rules);
        assert!(hints.is_empty(), "no narrowing = no hints");
    }

    // =========================================================================
    // Congruence rule fusion tests (Phase 5B.4)
    // =========================================================================

    #[test]
    fn test_congruence_fusion_binary() {
        let rules = vec![
            ("Add".to_string(), "Expr".to_string(), 0),
            ("Add".to_string(), "Expr".to_string(), 1),
        ];
        let hints = analyze_congruence_fusion(&rules);
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].constructor, "Add");
        assert_eq!(hints[0].rule_count, 2);
        assert_eq!(hints[0].argument_positions, vec![0, 1]);
    }

    #[test]
    fn test_congruence_fusion_no_merge_single() {
        let rules = vec![("Neg".to_string(), "Expr".to_string(), 0)];
        let hints = analyze_congruence_fusion(&rules);
        assert!(hints.is_empty(), "single rule = no fusion");
    }

    #[test]
    fn test_congruence_fusion_multiple_constructors() {
        let rules = vec![
            ("Add".to_string(), "Expr".to_string(), 0),
            ("Add".to_string(), "Expr".to_string(), 1),
            ("Mul".to_string(), "Expr".to_string(), 0),
            ("Mul".to_string(), "Expr".to_string(), 1),
            ("Neg".to_string(), "Expr".to_string(), 0),
        ];
        let hints = analyze_congruence_fusion(&rules);
        assert_eq!(hints.len(), 2); // Add and Mul can be fused, Neg cannot
    }

    #[test]
    fn test_repair_kind_variants() {
        let kinds = vec![
            RepairKind::AddRule,
            RepairKind::AddCrossRef,
            RepairKind::Disambiguate,
            RepairKind::AddCongruence,
            RepairKind::FixConfluence,
            RepairKind::FixTermination,
            RepairKind::StrengthenPrecondition,
            RepairKind::WeakenPostcondition,
            RepairKind::FixBisimulation,
            RepairKind::CompleteMorphism,
            RepairKind::Custom("test".into()),
        ];
        // All should be distinct.
        for (i, a) in kinds.iter().enumerate() {
            for (j, b) in kinds.iter().enumerate() {
                if i != j {
                    assert_ne!(a, b);
                }
            }
        }
    }

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn test_enrich_trs_repairs_appends_hint() {
        use crate::lint::{LintDiagnostic, LintSeverity};
        use crate::confluence::{ConfluenceAnalysis, CriticalPair, JoinabilityResult, Term};
        let mut diagnostics = vec![LintDiagnostic {
            id: "T01",
            name: "non-joinable-critical-pair",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: "critical pair not joinable".to_string(),
            hint: Some("original hint".to_string()),
            grammar_name: None,
            source_location: None,
        }];
        let confluence = ConfluenceAnalysis {
            is_confluent: false,
            critical_pairs: vec![CriticalPair {
                term1: Term::var("a"),
                term2: Term::var("b"),
                rule1_index: 0,
                rule2_index: 1,
                overlap_position: vec![0],
            }],
            joinability_results: vec![JoinabilityResult::NotJoinable {
                normal_form1: Term::var("a"),
                normal_form2: Term::var("b"),
            }],
            non_joinable_count: 1,
            unknown_count: 0,
        };
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];
        enrich_diagnostics_with_repairs(&mut diagnostics, Some(&confluence), &syntax);
        let hint = diagnostics[0].hint.as_deref().expect("hint should exist");
        assert!(
            hint.contains("[repair:"),
            "hint should contain repair suggestion, got: {}",
            hint
        );
    }

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn test_enrich_trs_repairs_noop_when_confluent() {
        use crate::lint::{LintDiagnostic, LintSeverity};
        let mut diagnostics = vec![LintDiagnostic {
            id: "T01",
            name: "non-joinable-critical-pair",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: "critical pair not joinable".to_string(),
            hint: Some("original hint".to_string()),
            grammar_name: None,
            source_location: None,
        }];
        let confluence = crate::confluence::ConfluenceAnalysis {
            is_confluent: true,
            critical_pairs: vec![],
            joinability_results: vec![],
            non_joinable_count: 0,
            unknown_count: 0,
        };
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];
        enrich_diagnostics_with_repairs(&mut diagnostics, Some(&confluence), &syntax);
        assert_eq!(
            diagnostics[0].hint.as_deref(),
            Some("original hint"),
            "hint should be unchanged when confluent"
        );
    }

    #[cfg(feature = "morphisms")]
    #[test]
    fn test_enrich_morphism_repairs_appends_hint() {
        use crate::lint::{LintDiagnostic, LintSeverity};
        let mut diagnostics = vec![LintDiagnostic {
            id: "M01",
            name: "morphism-gap",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: "morphism incomplete".to_string(),
            hint: Some("original hint".to_string()),
            grammar_name: None,
            source_location: None,
        }];
        let morphism = crate::morphism::MorphismCheck {
            gaps: vec![crate::morphism::MorphismGap {
                kind: crate::morphism::GapKind::MissingSort,
                source_name: "Bool".to_string(),
                description: "no target sort".to_string(),
            }],
            preservation_failures: vec![],
            is_complete: false,
        };
        enrich_diagnostics_with_morphism_repairs(&mut diagnostics, Some(&morphism));
        let hint = diagnostics[0].hint.as_deref().expect("hint should exist");
        assert!(
            hint.contains("[repair:"),
            "hint should contain repair suggestion, got: {}",
            hint
        );
    }

    #[cfg(feature = "morphisms")]
    #[test]
    fn test_enrich_morphism_repairs_noop_when_complete() {
        use crate::lint::{LintDiagnostic, LintSeverity};
        let mut diagnostics = vec![LintDiagnostic {
            id: "M01",
            name: "morphism-gap",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: "morphism incomplete".to_string(),
            hint: Some("original hint".to_string()),
            grammar_name: None,
            source_location: None,
        }];
        let morphism = crate::morphism::MorphismCheck {
            gaps: vec![],
            preservation_failures: vec![],
            is_complete: true,
        };
        enrich_diagnostics_with_morphism_repairs(&mut diagnostics, Some(&morphism));
        assert_eq!(
            diagnostics[0].hint.as_deref(),
            Some("original hint"),
            "hint should be unchanged when morphism is complete"
        );
    }
}
