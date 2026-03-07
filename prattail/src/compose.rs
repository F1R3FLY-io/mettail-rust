//! Grammar composition via WFST rational operations.
//!
//! Enables modular grammar definition: compose two `LanguageSpec`s into a
//! single merged specification, suitable for calling `generate_parser()`.
//!
//! ## Architecture
//!
//! ```text
//!   LanguageSpec A          LanguageSpec B
//!       │                       │
//!       └────────┬──────────────┘
//!                ▼
//!     compose_languages(A, B)
//!                │
//!       ┌────────┼────────────────┐
//!       │        │                │
//!       ▼        ▼                ▼
//!  Merge      Merge           Validate
//!  Categories Rules           Invariants
//!       │        │                │
//!       │   Reclassify           │
//!       │   via classify_rule()  │
//!       │        │                │
//!       └────────┼────────────────┘
//!                ▼
//!          LanguageSpec (merged)
//!                │
//!                ▼
//!         generate_parser()   ← Normal pipeline
//! ```
//!
//! ## Key Invariants
//!
//! 1. **Category uniqueness**: All category names unique; duplicates must have
//!    matching `native_type`.
//! 2. **Rule label uniqueness**: All rule labels globally unique.
//! 3. **Category reference validity**: Every `NonTerminal`, `Binder`, `Collection`,
//!    `Zip` category references must exist in the merged types.
//! 4. **Single primary**: Exactly one `is_primary: true` category.
//! 5. **Reclassification**: All derived flags re-derived via `classify::classify_rule()`.
//! 6. **FIRST/FOLLOW recomputation**: Handled by the pipeline (automatic).
//!
//! ## Derived from lling-llang
//!
//! The composition model draws from `lling-llang`'s `union()` and `compose()`
//! WFST operations. Grammar composition is the PraTTaIL analog of WFST union:
//! the merged grammar accepts inputs from either source grammar.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;

use crate::binding_power::Associativity;
use crate::{
    BeamWidthConfig, CategorySpec, LanguageSpec, LiteralPatterns, RuleSpecInput, SyntaxItemSpec,
};

// ══════════════════════════════════════════════════════════════════════════════
// CompositionError
// ══════════════════════════════════════════════════════════════════════════════

/// Errors that can occur during grammar composition.
#[derive(Debug, Clone)]
pub enum CompositionError {
    /// Two categories share a name but have different native types.
    CategoryNativeTypeMismatch {
        category: String,
        native_type_a: Option<String>,
        native_type_b: Option<String>,
    },

    /// Two rules share a label (constructor name).
    DuplicateRuleLabel {
        label: String,
        category_a: String,
        category_b: String,
    },

    /// A rule references a category that doesn't exist in the merged spec.
    InvalidCategoryReference {
        rule_label: String,
        referenced_category: String,
    },

    /// Two infix rules for the same `(terminal, category)` pair have
    /// conflicting associativity.
    AssociativityConflict {
        terminal: String,
        category: String,
        assoc_a: Associativity,
        assoc_b: Associativity,
    },

    /// Two infix rules for the same `(terminal, category)` pair have
    /// different explicit binding powers (prefix_precedence).
    BindingPowerConflict {
        terminal: String,
        category: String,
        bp_a: u8,
        bp_b: u8,
    },
    // Note: MultiplePrimaryCategories is intentionally NOT an error.
    // When two grammars both declare a primary, merge_categories() keeps
    // the first grammar's primary and demotes the second. This matches
    // the intuition that "base grammar defines the primary category."
}

impl fmt::Display for CompositionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompositionError::CategoryNativeTypeMismatch {
                category,
                native_type_a,
                native_type_b,
            } => {
                write!(
                    f,
                    "category '{}' has conflicting native types: {:?} vs {:?}",
                    category, native_type_a, native_type_b
                )
            },
            CompositionError::DuplicateRuleLabel { label, category_a, category_b } => {
                write!(
                    f,
                    "rule label '{}' appears in both grammars (categories: '{}' and '{}')",
                    label, category_a, category_b
                )
            },
            CompositionError::InvalidCategoryReference { rule_label, referenced_category } => {
                write!(
                    f,
                    "rule '{}' references non-existent category '{}'",
                    rule_label, referenced_category
                )
            },
            CompositionError::AssociativityConflict { terminal, category, assoc_a, assoc_b } => {
                write!(
                    f,
                    "operator '{}' in category '{}' has conflicting associativity: {:?} vs {:?}",
                    terminal, category, assoc_a, assoc_b
                )
            },
            CompositionError::BindingPowerConflict { terminal, category, bp_a, bp_b } => {
                write!(
                    f,
                    "operator '{}' in category '{}' has conflicting binding powers: {} vs {}",
                    terminal, category, bp_a, bp_b
                )
            },
        }
    }
}

impl std::error::Error for CompositionError {}

// ══════════════════════════════════════════════════════════════════════════════
// compose_languages — the main entry point
// ══════════════════════════════════════════════════════════════════════════════

/// Compose two language specifications into a single merged specification.
///
/// The merged spec can be passed to [`crate::generate_parser()`] to produce a
/// parser that handles both grammars.
///
/// # Merge Strategy
///
/// - **Categories**: Union by name. Duplicates are merged if `native_type` matches.
/// - **Rules**: Concatenated. Labels must be globally unique.
/// - **Primary**: The first grammar's primary category wins; if only the second
///   grammar has a primary, that one is used.
/// - **Classification**: All rules are reclassified after merge.
/// - **FIRST/FOLLOW**: Recomputed by the pipeline (not done here).
///
/// # Errors
///
/// Returns [`CompositionError`] if any invariant is violated.
pub fn compose_languages(
    spec_a: &LanguageSpec,
    spec_b: &LanguageSpec,
) -> Result<LanguageSpec, Vec<CompositionError>> {
    let mut errors: Vec<CompositionError> = Vec::new();

    // Step 1: Merge categories
    let merged_types = merge_categories(&spec_a.types, &spec_b.types, &mut errors);

    // Step 2: Primary category resolution
    // Multiple primaries from different grammars are resolved by
    // merge_categories() which keeps only the first primary encountered.
    // Grammar A's primary wins; B's primary is demoted.

    // Step 3: Merge rules — check for label collisions
    let merged_inputs = merge_rules(spec_a, spec_b, &mut errors);

    // Step 4: Validate category references in all rules
    let category_names: BTreeSet<String> = merged_types.iter().map(|c| c.name.clone()).collect();
    for input in &merged_inputs {
        validate_category_refs(&input.syntax, &input.label, &category_names, &mut errors);
    }

    // Step 5: Check associativity conflicts for same (terminal, category) pairs
    check_associativity_conflicts(spec_a, spec_b, &mut errors);

    // Step 6: Check binding power conflicts
    check_binding_power_conflicts(spec_a, spec_b, &mut errors);

    if !errors.is_empty() {
        return Err(errors);
    }

    // Step 7: Construct merged LanguageSpec — reclassifies all rules via classify_rule()
    let merged_name = format!("{}_{}", spec_a.name, spec_b.name);
    Ok(LanguageSpec::new(merged_name, merged_types, merged_inputs))
}

// ══════════════════════════════════════════════════════════════════════════════
// Category merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two category vectors, detecting native type mismatches.
///
/// Categories from `spec_a` take priority for ordering. Categories unique to
/// `spec_b` are appended after. The first category's `is_primary` flag is
/// preserved from the source grammar.
fn merge_categories(
    types_a: &[CategorySpec],
    types_b: &[CategorySpec],
    errors: &mut Vec<CompositionError>,
) -> Vec<CategorySpec> {
    let mut by_name: BTreeMap<String, &CategorySpec> = BTreeMap::new();
    let mut result: Vec<CategorySpec> = Vec::with_capacity(types_a.len() + types_b.len());
    let mut seen_primary = false;

    // Add all categories from grammar A
    for cat in types_a {
        by_name.insert(cat.name.clone(), cat);
        let is_primary = cat.is_primary && !seen_primary;
        if is_primary {
            seen_primary = true;
        }
        result.push(CategorySpec {
            name: cat.name.clone(),
            native_type: cat.native_type.clone(),
            is_primary,
        });
    }

    // Merge categories from grammar B
    for cat in types_b {
        if let Some(existing) = by_name.get(&cat.name) {
            // Category exists — verify native type matches
            if existing.native_type != cat.native_type {
                errors.push(CompositionError::CategoryNativeTypeMismatch {
                    category: cat.name.clone(),
                    native_type_a: existing.native_type.clone(),
                    native_type_b: cat.native_type.clone(),
                });
            }
            // Skip (already present from grammar A)
        } else {
            // New category from grammar B
            let is_primary = cat.is_primary && !seen_primary;
            if is_primary {
                seen_primary = true;
            }
            result.push(CategorySpec {
                name: cat.name.clone(),
                native_type: cat.native_type.clone(),
                is_primary,
            });
            by_name.insert(cat.name.clone(), cat);
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Rule merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge rules from two grammars, detecting label collisions.
///
/// Rules from grammar A come first, then grammar B. All rules are converted
/// to `RuleSpecInput` for reclassification.
fn merge_rules(
    spec_a: &LanguageSpec,
    spec_b: &LanguageSpec,
    errors: &mut Vec<CompositionError>,
) -> Vec<RuleSpecInput> {
    let mut labels: BTreeMap<String, String> = BTreeMap::new(); // label → category
    let mut result: Vec<RuleSpecInput> =
        Vec::with_capacity(spec_a.rules.len() + spec_b.rules.len());

    // Convert rules from grammar A
    for rule in &spec_a.rules {
        labels.insert(rule.label.clone(), rule.category.clone());
        result.push(RuleSpecInput {
            label: rule.label.clone(),
            category: rule.category.clone(),
            syntax: rule.syntax.clone(),
            associativity: rule.associativity,
            prefix_precedence: rule.prefix_precedence,
            has_rust_code: rule.has_rust_code,
            rust_code: rule.rust_code.clone(),
            eval_mode: rule.eval_mode.clone(),
            source_location: rule.source_location,
        });
    }

    // Convert rules from grammar B, checking for label collisions
    for rule in &spec_b.rules {
        if let Some(existing_cat) = labels.get(&rule.label) {
            errors.push(CompositionError::DuplicateRuleLabel {
                label: rule.label.clone(),
                category_a: existing_cat.clone(),
                category_b: rule.category.clone(),
            });
        }
        labels.insert(rule.label.clone(), rule.category.clone());
        result.push(RuleSpecInput {
            label: rule.label.clone(),
            category: rule.category.clone(),
            syntax: rule.syntax.clone(),
            associativity: rule.associativity,
            prefix_precedence: rule.prefix_precedence,
            has_rust_code: rule.has_rust_code,
            rust_code: rule.rust_code.clone(),
            eval_mode: rule.eval_mode.clone(),
            source_location: rule.source_location,
        });
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Category reference validation
// ══════════════════════════════════════════════════════════════════════════════

/// Recursively validate that all category references in syntax items exist.
fn validate_category_refs(
    items: &[SyntaxItemSpec],
    rule_label: &str,
    valid_categories: &BTreeSet<String>,
    errors: &mut Vec<CompositionError>,
) {
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(_)
            | SyntaxItemSpec::IdentCapture { .. }
            | SyntaxItemSpec::BinderCollection { .. } => {},

            SyntaxItemSpec::NonTerminal { category, .. } => {
                if !valid_categories.contains(category) {
                    errors.push(CompositionError::InvalidCategoryReference {
                        rule_label: rule_label.to_string(),
                        referenced_category: category.clone(),
                    });
                }
            },

            SyntaxItemSpec::Binder { category, .. } => {
                if !valid_categories.contains(category) {
                    errors.push(CompositionError::InvalidCategoryReference {
                        rule_label: rule_label.to_string(),
                        referenced_category: category.clone(),
                    });
                }
            },

            SyntaxItemSpec::Collection { element_category, .. } => {
                if !valid_categories.contains(element_category) {
                    errors.push(CompositionError::InvalidCategoryReference {
                        rule_label: rule_label.to_string(),
                        referenced_category: element_category.clone(),
                    });
                }
            },

            SyntaxItemSpec::Sep { body, .. } => {
                validate_category_refs(
                    std::slice::from_ref(body.as_ref()),
                    rule_label,
                    valid_categories,
                    errors,
                );
            },

            SyntaxItemSpec::Map { body_items } => {
                validate_category_refs(body_items, rule_label, valid_categories, errors);
            },

            SyntaxItemSpec::Zip {
                left_category,
                right_category,
                body,
                ..
            } => {
                if !valid_categories.contains(left_category) {
                    errors.push(CompositionError::InvalidCategoryReference {
                        rule_label: rule_label.to_string(),
                        referenced_category: left_category.clone(),
                    });
                }
                if !valid_categories.contains(right_category) {
                    errors.push(CompositionError::InvalidCategoryReference {
                        rule_label: rule_label.to_string(),
                        referenced_category: right_category.clone(),
                    });
                }
                validate_category_refs(
                    std::slice::from_ref(body.as_ref()),
                    rule_label,
                    valid_categories,
                    errors,
                );
            },

            SyntaxItemSpec::Optional { inner } => {
                validate_category_refs(inner, rule_label, valid_categories, errors);
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Associativity conflict detection
// ══════════════════════════════════════════════════════════════════════════════

/// Check for associativity conflicts between grammars.
///
/// If both grammars have an infix rule with the same `(terminal, category)` pair
/// but different associativity, that's a conflict.
fn check_associativity_conflicts(
    spec_a: &LanguageSpec,
    spec_b: &LanguageSpec,
    errors: &mut Vec<CompositionError>,
) {
    // Build map: (first_terminal_after_nonterminal, category) → associativity from grammar A
    let mut a_ops: BTreeMap<(String, String), Associativity> = BTreeMap::new();
    for rule in &spec_a.rules {
        if rule.is_infix {
            if let Some(terminal) = infix_terminal(&rule.syntax) {
                a_ops.insert((terminal.clone(), rule.category.clone()), rule.associativity);
            }
        }
    }

    // Check grammar B's infix rules against A's
    for rule in &spec_b.rules {
        if rule.is_infix {
            if let Some(terminal) = infix_terminal(&rule.syntax) {
                let key = (terminal.clone(), rule.category.clone());
                if let Some(&assoc_a) = a_ops.get(&key) {
                    if assoc_a != rule.associativity {
                        errors.push(CompositionError::AssociativityConflict {
                            terminal,
                            category: rule.category.clone(),
                            assoc_a,
                            assoc_b: rule.associativity,
                        });
                    }
                }
            }
        }
    }
}

/// Extract the infix operator terminal from a rule's syntax.
///
/// For an infix rule like `a "+" b`, the terminal is "+".
/// The pattern is: `NonTerminal(cat) Terminal(op) NonTerminal(cat)`.
fn infix_terminal(syntax: &[SyntaxItemSpec]) -> Option<String> {
    // Find the first terminal after the first nonterminal
    let mut seen_nonterminal = false;
    for item in syntax {
        match item {
            SyntaxItemSpec::NonTerminal { .. } if !seen_nonterminal => {
                seen_nonterminal = true;
            },
            SyntaxItemSpec::Terminal(t) if seen_nonterminal => {
                return Some(t.clone());
            },
            _ => {},
        }
    }
    None
}

// ══════════════════════════════════════════════════════════════════════════════
// Binding power conflict detection
// ══════════════════════════════════════════════════════════════════════════════

/// Check for binding power conflicts between grammars.
///
/// If both grammars have unary prefix rules for the same `(first_terminal, category)`
/// pair but different `prefix_precedence` values, that's a conflict. Binding power
/// conflicts indicate that the two grammars disagree on operator precedence, which
/// would produce ambiguous parse results after composition.
fn check_binding_power_conflicts(
    spec_a: &LanguageSpec,
    spec_b: &LanguageSpec,
    errors: &mut Vec<CompositionError>,
) {
    // Build map: (first_terminal, category) → prefix_precedence from grammar A
    let mut a_bps: BTreeMap<(String, String), u8> = BTreeMap::new();
    for rule in &spec_a.rules {
        if rule.is_unary_prefix {
            if let Some(bp) = rule.prefix_precedence {
                if let Some(SyntaxItemSpec::Terminal(t)) = rule.syntax.first() {
                    a_bps.insert((t.clone(), rule.category.clone()), bp);
                }
            }
        }
    }

    // Check grammar B's prefix rules against A's
    for rule in &spec_b.rules {
        if rule.is_unary_prefix {
            if let Some(bp_b) = rule.prefix_precedence {
                if let Some(SyntaxItemSpec::Terminal(t)) = rule.syntax.first() {
                    let key = (t.clone(), rule.category.clone());
                    if let Some(&bp_a) = a_bps.get(&key) {
                        if bp_a != bp_b {
                            errors.push(CompositionError::BindingPowerConflict {
                                terminal: t.clone(),
                                category: rule.category.clone(),
                                bp_a,
                                bp_b,
                            });
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Composition metadata
// ══════════════════════════════════════════════════════════════════════════════

/// Summary of what was merged, for diagnostics.
#[derive(Debug, Clone)]
pub struct CompositionSummary {
    /// Merged language name.
    pub merged_name: String,
    /// Number of categories from grammar A.
    pub categories_a: usize,
    /// Number of categories from grammar B.
    pub categories_b: usize,
    /// Number of categories in the merged spec (may be less than a + b if shared).
    pub categories_merged: usize,
    /// Number of rules from grammar A.
    pub rules_a: usize,
    /// Number of rules from grammar B.
    pub rules_b: usize,
    /// Categories that were shared (present in both grammars).
    pub shared_categories: Vec<String>,
}

impl fmt::Display for CompositionSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Composed '{}': {} categories ({} from A, {} from B, {} shared), {} rules ({} + {})",
            self.merged_name,
            self.categories_merged,
            self.categories_a,
            self.categories_b,
            self.shared_categories.len(),
            self.rules_a + self.rules_b,
            self.rules_a,
            self.rules_b,
        )
    }
}

/// Compute a summary of composition results.
pub fn composition_summary(
    spec_a: &LanguageSpec,
    spec_b: &LanguageSpec,
    merged: &LanguageSpec,
) -> CompositionSummary {
    let names_a: BTreeSet<&str> = spec_a.types.iter().map(|c| c.name.as_str()).collect();
    let names_b: BTreeSet<&str> = spec_b.types.iter().map(|c| c.name.as_str()).collect();
    let shared: Vec<String> = names_a
        .intersection(&names_b)
        .map(|s| s.to_string())
        .collect();

    CompositionSummary {
        merged_name: merged.name.clone(),
        categories_a: spec_a.types.len(),
        categories_b: spec_b.types.len(),
        categories_merged: merged.types.len(),
        rules_a: spec_a.rules.len(),
        rules_b: spec_b.rules.len(),
        shared_categories: shared,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Multi-grammar composition
// ══════════════════════════════════════════════════════════════════════════════

/// Compose multiple language specifications into a single merged specification.
///
/// Folds left: `compose(A, B)`, then `compose(AB, C)`, etc.
///
/// Returns the first set of errors encountered.
pub fn compose_many(specs: &[&LanguageSpec]) -> Result<LanguageSpec, Vec<CompositionError>> {
    if specs.is_empty() {
        return Ok(LanguageSpec {
            name: "empty".to_string(),
            types: Vec::new(),
            rules: Vec::new(),
            beam_width: BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            literal_patterns: LiteralPatterns::default(),
            recovery_config: crate::recovery::RecoveryConfig::default(),
            semantic_dependency_groups: Vec::new(),
        });
    }

    let mut merged = specs[0].clone();
    for spec in &specs[1..] {
        merged = compose_languages(&merged, spec)?;
    }

    Ok(merged)
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST-aware composition (requires `wfst` feature)
// ══════════════════════════════════════════════════════════════════════════════

/// Result of WFST-aware grammar composition.
///
/// Contains the merged `LanguageSpec` plus pre-built prediction WFSTs for each
/// category, constructed via weighted union rather than full pipeline rebuild.
#[derive(Debug)]
pub struct WfstCompositionResult {
    /// The merged language specification.
    pub spec: LanguageSpec,
    /// Per-category prediction WFSTs, built via weighted union of the input WFSTs.
    /// Categories that appear in only one source grammar get their WFST unchanged.
    /// Categories shared across both sources get a union of both WFSTs.
    pub prediction_wfsts: HashMap<String, crate::wfst::PredictionWfst>,
    /// Terminal set of the merged grammar (union of both sources).
    pub terminals: HashSet<String>,
    /// Enriched composition summary with WFST statistics.
    pub summary: WfstCompositionSummary,
    /// Decision trees for source grammar A (built via lightweight analysis pipeline).
    pub source_a_trees: Option<HashMap<String, crate::decision_tree::CategoryDecisionTree>>,
    /// Decision trees for source grammar B.
    pub source_b_trees: Option<HashMap<String, crate::decision_tree::CategoryDecisionTree>>,
    /// Decision trees for the merged grammar.
    pub merged_trees: Option<HashMap<String, crate::decision_tree::CategoryDecisionTree>>,
}

/// Enriched composition summary including WFST statistics.
#[derive(Debug, Clone)]
pub struct WfstCompositionSummary {
    /// Base composition summary.
    pub base: CompositionSummary,
    /// Number of prediction WFSTs in the merged result.
    pub wfst_count: usize,
    /// Number of WFSTs that were merged via union (shared categories).
    pub wfsts_merged: usize,
    /// Total number of weighted actions across all WFSTs.
    pub total_actions: usize,
    /// Total number of WFST states across all WFSTs.
    pub total_states: usize,
}

impl fmt::Display for WfstCompositionSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} | WFSTs: {} ({} merged), actions: {}, states: {}",
            self.base, self.wfst_count, self.wfsts_merged, self.total_actions, self.total_states,
        )
    }
}

/// Compose two grammars with WFST-aware prediction merging.
///
/// This performs the same grammar-level composition as `compose_languages()`,
/// but additionally merges per-category prediction WFSTs via weighted union
/// rather than requiring a full pipeline rebuild.
///
/// ## Merge Strategy for WFSTs
///
/// - **Disjoint categories**: the WFST from the source grammar is kept as-is.
/// - **Shared categories**: both WFSTs are merged via `PredictionWfst::union()`.
///   This combines all actions and transitions; ambiguous tokens get alternatives
///   from both grammars, sorted by weight.
/// - **Terminal sets**: merged via set union.
///
/// ## When to Use
///
/// Use `compose_with_wfst()` when you have pre-built WFSTs from a previous
/// pipeline run and want to extend the grammar without re-running the full
/// pipeline. This is useful for incremental grammar extension (e.g., adding
/// a module to an existing language).
///
/// For fresh builds, `compose_languages()` + a full pipeline run is simpler
/// and equally efficient.
pub fn compose_with_wfst(
    spec_a: &LanguageSpec,
    spec_b: &LanguageSpec,
    wfsts_a: &HashMap<String, crate::wfst::PredictionWfst>,
    wfsts_b: &HashMap<String, crate::wfst::PredictionWfst>,
    terminals_a: &HashSet<String>,
    terminals_b: &HashSet<String>,
) -> Result<WfstCompositionResult, Vec<CompositionError>> {
    // Step 1: Compose the language specs
    let merged_spec = compose_languages(spec_a, spec_b)?;
    let base_summary = composition_summary(spec_a, spec_b, &merged_spec);

    // Step 2: Merge terminal sets
    let terminals = crate::prediction::merge_terminal_sets(terminals_a, terminals_b);

    // Step 3: Merge prediction WFSTs per category
    let mut prediction_wfsts: HashMap<String, crate::wfst::PredictionWfst> = HashMap::new();
    let mut wfsts_merged = 0usize;

    for cat in &merged_spec.types {
        let name = &cat.name;
        match (wfsts_a.get(name), wfsts_b.get(name)) {
            (Some(a), Some(b)) => {
                // Shared category: merge via union
                let mut merged_wfst = a.clone();
                merged_wfst.union(b);
                prediction_wfsts.insert(name.clone(), merged_wfst);
                wfsts_merged += 1;
            },
            (Some(a), None) => {
                prediction_wfsts.insert(name.clone(), a.clone());
            },
            (None, Some(b)) => {
                prediction_wfsts.insert(name.clone(), b.clone());
            },
            (None, None) => {
                // No WFST for this category from either source — skip
            },
        }
    }

    // Step 3.5: Verify composition correctness (CVT)
    let cvt_report = crate::composition_verify::verify_composition(
        wfsts_a,
        wfsts_b,
        &prediction_wfsts,
        &base_summary.shared_categories,
    );
    if !cvt_report.all_pass {
        for result in &cvt_report.results {
            if !result.holds {
                for violation in &result.violations {
                    crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
                        id: "X06",
                        name: "composition-verification-violation",
                        severity: crate::lint::LintSeverity::Warning,
                        category: None,
                        rule: None,
                        message: format!("composition verification [{}]: {}", result.property, violation),
                        hint: Some("review the composed grammar for property violations".to_string()),
                        grammar_name: None,
                        source_location: None,
                    });
                }
            }
        }
    }
    // NoSpuriousActions is a critical invariant — debug-assert it
    debug_assert!(
        cvt_report
            .results
            .iter()
            .find(|r| r.property
                == crate::composition_verify::VerificationProperty::NoSpuriousActions)
            .map(|r| r.holds)
            .unwrap_or(true),
        "NoSpuriousActions violated: merged WFST contains phantom actions not in A or B.\n{}",
        cvt_report
    );

    // Step 3.6: Decision tree composition analysis (X06/X07) — automatic
    // Build decision trees for both source specs and the merged spec to detect:
    // - Common sublanguage (shared dispatch paths)
    // - New ambiguities introduced by composition
    let trees_a = crate::decision_tree::build_decision_trees_from_spec(spec_a);
    let trees_b = crate::decision_tree::build_decision_trees_from_spec(spec_b);
    let trees_merged = crate::decision_tree::build_decision_trees_from_spec(&merged_spec);

    if let (Some(ref ta), Some(ref tb), Some(ref _tm)) = (&trees_a, &trees_b, &trees_merged) {
        let cats_a: std::collections::HashSet<&str> = ta.keys().map(|s| s.as_str()).collect();
        let cats_b: std::collections::HashSet<&str> = tb.keys().map(|s| s.as_str()).collect();
        let shared_cats: Vec<&str> = cats_a.intersection(&cats_b).copied().collect();

        for cat in &shared_cats {
            if let (Some(tree_a), Some(tree_b)) = (ta.get(*cat), tb.get(*cat)) {
                let report = crate::decision_tree::composition_trie_analysis(tree_a, tree_b);
                if report.common_rules > 0 {
                    crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
                        id: "X06",
                        name: "common-sublanguage",
                        severity: crate::lint::LintSeverity::Note,
                        category: Some(cat.to_string()),
                        rule: None,
                        message: format!(
                            "composition: {} common dispatch paths, {} unique to A, {} unique to B",
                            report.common_rules, report.unique_a, report.unique_b,
                        ),
                        hint: None,
                        grammar_name: None,
                        source_location: None,
                    });
                }
                if report.new_ambiguities > 0 {
                    crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
                        id: "X07",
                        name: "composition-introduced-ambiguity",
                        severity: crate::lint::LintSeverity::Warning,
                        category: Some(cat.to_string()),
                        rule: None,
                        message: format!(
                            "composition introduces {} new ambiguous dispatch point(s) not present in either source",
                            report.new_ambiguities,
                        ),
                        hint: Some("review merged grammar for overlapping rules from different sources".to_string()),
                        grammar_name: None,
                        source_location: None,
                    });
                }
            }
        }
    }

    // Step 4: Compute statistics
    let total_actions: usize = prediction_wfsts.values().map(|w| w.num_actions()).sum();
    let total_states: usize = prediction_wfsts.values().map(|w| w.num_states()).sum();

    let summary = WfstCompositionSummary {
        base: base_summary,
        wfst_count: prediction_wfsts.len(),
        wfsts_merged,
        total_actions,
        total_states,
    };

    Ok(WfstCompositionResult {
        spec: merged_spec,
        prediction_wfsts,
        terminals,
        summary,
        source_a_trees: trees_a,
        source_b_trees: trees_b,
        merged_trees: trees_merged,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// A6: Composed Lexer-Parser WFST
// ══════════════════════════════════════════════════════════════════════════════

/// A6: A composed state in the lexer-parser product automaton.
///
/// Pairs a DFA lexer state with a prediction WFST state to create a single
/// automaton that maps `byte_class → dispatch_action` with combined weights.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ComposedState {
    /// DFA lexer state ID.
    pub lexer_state: u32,
    /// Prediction WFST state ID (per-category).
    pub wfst_state: u32,
}

/// A6: A transition in the composed lexer-parser WFST.
///
/// Input: byte class (from the lexer DFA's alphabet partition).
/// Output: dispatch action label (from the prediction WFST).
/// Weight: TropicalWeight product of lexer priority × WFST prediction weight.
#[derive(Debug, Clone)]
pub struct ComposedTransition {
    /// Source state in the composed automaton.
    pub from: ComposedState,
    /// Target state in the composed automaton.
    pub to: ComposedState,
    /// Input symbol: byte class from the lexer DFA.
    pub input_class: u8,
    /// Output label: token produced at the interface (empty for non-accepting lexer states).
    pub output_token: Option<String>,
    /// Combined weight: lexer priority + WFST prediction weight (tropical sum).
    pub weight: crate::automata::semiring::TropicalWeight,
}

/// A6: Composed lexer-parser WFST for a single grammar category.
///
/// Represents the composition of:
/// - The lexer DFA (mapping byte sequences → tokens with priority weights).
/// - The prediction WFST for a specific category (mapping tokens → dispatch actions).
///
/// The composed automaton maps `byte_class* → dispatch_action` in a single pass,
/// enabling:
/// 1. Token-level disambiguation that considers parser context.
/// 2. Globally optimal tokenization when multiple accept paths exist.
/// 3. Foundation for fused lex-parse on deterministic subgrammars.
///
/// ## Construction
///
/// Product construction: state `(q_lex, q_wfst)` transitions to `(q_lex', q_wfst')`
/// when:
/// - The lexer has a transition `q_lex →(class)→ q_lex'`.
/// - If `q_lex'` is accepting with token `t`, the WFST has a transition
///   `q_wfst →(t)→ q_wfst'` with weight `w`.
/// - The composed weight is `lexer_priority(q_lex', t) + w` (tropical product).
///
/// Non-accepting lexer transitions carry weight 0.0 (no WFST transition occurs).
#[derive(Debug, Clone)]
pub struct ComposedLexerParser {
    /// Category name this composed WFST serves.
    pub category: String,
    /// States in the composed automaton (BFS-discovered).
    pub states: Vec<ComposedState>,
    /// Transitions indexed by source state position in `states`.
    pub transitions: Vec<Vec<ComposedTransition>>,
    /// Accepting composed states and their associated dispatch actions.
    pub accepting: Vec<(ComposedState, Vec<String>)>,
    /// Number of lexer DFA states (for state space reporting).
    pub num_lexer_states: u32,
    /// Number of WFST states (for state space reporting).
    pub num_wfst_states: u32,
}

impl ComposedLexerParser {
    /// Construct the composed automaton from a lexer DFA and prediction WFST.
    ///
    /// # Arguments
    ///
    /// * `category` — Category name for this composed WFST.
    /// * `num_lexer_states` — Number of states in the lexer DFA.
    /// * `num_wfst_states` — Number of states in the prediction WFST.
    /// * `lexer_transitions` — Lexer DFA transition function: `(state, class) → state`.
    /// * `lexer_accepting` — Lexer accepting function: `state → Option<(token_name, priority_weight)>`.
    /// * `wfst_transitions` — WFST transition function: `(state, token_name) → Vec<(state, weight)>`.
    /// * `wfst_accepting_actions` — WFST final state → dispatch action labels.
    ///
    /// Returns the composed automaton discovered via BFS from `(0, 0)`.
    pub fn compose(
        category: &str,
        num_lexer_states: u32,
        num_wfst_states: u32,
        lexer_transitions: impl Fn(u32, u8) -> u32,
        lexer_accepting: impl Fn(u32) -> Vec<(String, f64)>,
        wfst_transitions: impl Fn(u32, &str) -> Vec<(u32, f64)>,
        wfst_accepting_actions: impl Fn(u32) -> Vec<String>,
        num_classes: u8,
    ) -> Self {
        use std::collections::{HashMap, VecDeque};
        use crate::automata::semiring::{Semiring, TropicalWeight};

        let start = ComposedState { lexer_state: 0, wfst_state: 0 };
        let mut state_map: HashMap<ComposedState, usize> = HashMap::new();
        let mut states = Vec::new();
        let mut transitions: Vec<Vec<ComposedTransition>> = Vec::new();
        let mut accepting = Vec::new();
        let mut queue = VecDeque::new();

        state_map.insert(start, 0);
        states.push(start);
        transitions.push(Vec::new());
        queue.push_back(start);

        while let Some(cs) = queue.pop_front() {
            let cs_idx = state_map[&cs];

            // For each byte class, compute composed transitions
            for class in 0..num_classes {
                let next_lex = lexer_transitions(cs.lexer_state, class);
                if next_lex == u32::MAX {
                    continue; // Dead lexer state
                }

                // Check if next_lex is accepting
                let accepts = lexer_accepting(next_lex);

                if accepts.is_empty() {
                    // Non-accepting: just advance the lexer, WFST stays in same state.
                    let target = ComposedState { lexer_state: next_lex, wfst_state: cs.wfst_state };
                    let target_idx = *state_map.entry(target).or_insert_with(|| {
                        let idx = states.len();
                        states.push(target);
                        transitions.push(Vec::new());
                        queue.push_back(target);
                        idx
                    });

                    transitions[cs_idx].push(ComposedTransition {
                        from: cs,
                        to: target,
                        input_class: class,
                        output_token: None,
                        weight: TropicalWeight::one(), // 0.0 cost for internal lexer transitions
                    });
                    let _ = target_idx; // suppress unused
                } else {
                    // Accepting: for each accepted token, compose with WFST transitions
                    for (token_name, lex_weight) in &accepts {
                        let wfst_targets = wfst_transitions(cs.wfst_state, token_name);
                        for (wfst_next, wfst_weight) in wfst_targets {
                            // Composed: lexer restarts from state 0 after accepting a token,
                            // WFST advances to the next state.
                            let target = ComposedState { lexer_state: 0, wfst_state: wfst_next };
                            let _target_idx = *state_map.entry(target).or_insert_with(|| {
                                let idx = states.len();
                                states.push(target);
                                transitions.push(Vec::new());
                                queue.push_back(target);
                                idx
                            });

                            // Combined weight: tropical product = sum
                            let combined = TropicalWeight::new(lex_weight + wfst_weight);

                            transitions[cs_idx].push(ComposedTransition {
                                from: cs,
                                to: target,
                                input_class: class,
                                output_token: Some(token_name.clone()),
                                weight: combined,
                            });
                        }
                    }
                }
            }

            // Check if this composed state is WFST-accepting
            let actions = wfst_accepting_actions(cs.wfst_state);
            if !actions.is_empty() {
                accepting.push((cs, actions));
            }
        }

        ComposedLexerParser {
            category: category.to_string(),
            states,
            transitions,
            accepting,
            num_lexer_states,
            num_wfst_states,
        }
    }

    /// Number of reachable states in the composed automaton.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Total number of transitions.
    pub fn num_transitions(&self) -> usize {
        self.transitions.iter().map(|t| t.len()).sum()
    }

    /// State space expansion factor: `composed_states / (lexer_states * wfst_states)`.
    ///
    /// Values near 0 indicate aggressive pruning (most product states were unreachable).
    /// Values near 1 indicate the composition is nearly the full cross-product.
    pub fn expansion_factor(&self) -> f64 {
        let max_states = self.num_lexer_states as f64 * self.num_wfst_states as f64;
        if max_states == 0.0 {
            0.0
        } else {
            self.states.len() as f64 / max_states
        }
    }

    /// Summary string for diagnostic output.
    pub fn summary(&self) -> String {
        format!(
            "ComposedLexerParser(category={}, states={}/{}, transitions={}, accepting={}, expansion={:.2}%)",
            self.category,
            self.num_states(),
            self.num_lexer_states as usize * self.num_wfst_states as usize,
            self.num_transitions(),
            self.accepting.len(),
            self.expansion_factor() * 100.0,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RuleSpec, SyntaxItemSpec};

    fn make_simple_spec(
        name: &str,
        categories: &[(&str, Option<&str>, bool)],
        rules: &[(&str, &str, Vec<SyntaxItemSpec>)],
    ) -> LanguageSpec {
        let types: Vec<CategorySpec> = categories
            .iter()
            .map(|(name, native, primary)| CategorySpec {
                name: name.to_string(),
                native_type: native.map(|s| s.to_string()),
                is_primary: *primary,
            })
            .collect();

        let cat_names: Vec<String> = types.iter().map(|c| c.name.clone()).collect();

        let rule_specs: Vec<RuleSpec> = rules
            .iter()
            .map(|(label, category, syntax)| {
                RuleSpec::classified(*label, *category, syntax.clone(), &cat_names)
            })
            .collect();

        LanguageSpec {
            name: name.to_string(),
            types,
            rules: rule_specs,
            beam_width: BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            literal_patterns: LiteralPatterns::default(),
            recovery_config: crate::recovery::RecoveryConfig::default(),
            semantic_dependency_groups: Vec::new(),
        }
    }

    #[test]
    fn test_compose_disjoint_grammars() {
        let spec_a = make_simple_spec(
            "Arith",
            &[("Int", Some("i32"), true)],
            &[("NumLit", "Int", vec![SyntaxItemSpec::Terminal("0".to_string())])],
        );

        let spec_b = make_simple_spec(
            "Logic",
            &[("Bool", Some("bool"), true)],
            &[("True", "Bool", vec![SyntaxItemSpec::Terminal("true".to_string())])],
        );

        let merged = compose_languages(&spec_a, &spec_b).expect("composition should succeed");

        assert_eq!(merged.name, "Arith_Logic");
        assert_eq!(merged.types.len(), 2);
        assert_eq!(merged.rules.len(), 2);

        // Int should be primary (from spec_a)
        assert!(merged.types[0].is_primary);
        assert!(!merged.types[1].is_primary);
    }

    #[test]
    fn test_compose_shared_categories() {
        let spec_a = make_simple_spec(
            "Base",
            &[("Expr", None, true)],
            &[("Num", "Expr", vec![SyntaxItemSpec::Terminal("0".to_string())])],
        );

        let spec_b = make_simple_spec(
            "Extension",
            &[("Expr", None, true)],
            &[(
                "Var",
                "Expr",
                vec![SyntaxItemSpec::IdentCapture { param_name: "x".to_string() }],
            )],
        );

        let merged = compose_languages(&spec_a, &spec_b).expect("composition should succeed");

        assert_eq!(merged.types.len(), 1); // shared category merged
        assert_eq!(merged.rules.len(), 2);
    }

    #[test]
    fn test_compose_native_type_mismatch() {
        let spec_a = make_simple_spec("A", &[("Int", Some("i32"), true)], &[]);

        let spec_b = make_simple_spec("B", &[("Int", Some("i64"), true)], &[]);

        let err = compose_languages(&spec_a, &spec_b).expect_err("should fail");
        assert_eq!(err.len(), 1);
        match &err[0] {
            CompositionError::CategoryNativeTypeMismatch { category, .. } => {
                assert_eq!(category, "Int");
            },
            other => panic!("Expected CategoryNativeTypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_compose_duplicate_rule_label() {
        let spec_a = make_simple_spec(
            "A",
            &[("Expr", None, true)],
            &[("Num", "Expr", vec![SyntaxItemSpec::Terminal("0".to_string())])],
        );

        let spec_b = make_simple_spec(
            "B",
            &[("Expr", None, true)],
            &[(
                "Num", // duplicate label
                "Expr",
                vec![SyntaxItemSpec::Terminal("1".to_string())],
            )],
        );

        let err = compose_languages(&spec_a, &spec_b).expect_err("should fail");
        assert!(err.iter().any(|e| matches!(
            e,
            CompositionError::DuplicateRuleLabel { label, .. } if label == "Num"
        )));
    }

    #[test]
    fn test_compose_invalid_category_reference() {
        let spec_a = make_simple_spec("A", &[("Expr", None, true)], &[]);

        // spec_b has a rule that references "Int" which doesn't exist in either grammar
        let types_b = vec![CategorySpec {
            name: "Stmt".to_string(),
            native_type: None,
            is_primary: false,
        }];
        let cat_names_b: Vec<String> = vec!["Stmt".to_string(), "Int".to_string()];
        let rules_b = vec![RuleSpec::classified(
            "Assign",
            "Stmt",
            vec![
                SyntaxItemSpec::IdentCapture { param_name: "x".to_string() },
                SyntaxItemSpec::Terminal("=".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "val".to_string(),
                },
            ],
            &cat_names_b,
        )];
        let spec_b = LanguageSpec {
            name: "B".to_string(),
            types: types_b,
            rules: rules_b,
            beam_width: BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            literal_patterns: LiteralPatterns::default(),
            recovery_config: crate::recovery::RecoveryConfig::default(),
            semantic_dependency_groups: Vec::new(),
        };

        let err = compose_languages(&spec_a, &spec_b).expect_err("should fail");
        assert!(err.iter().any(|e| matches!(
            e,
            CompositionError::InvalidCategoryReference {
                rule_label,
                referenced_category,
            } if rule_label == "Assign" && referenced_category == "Int"
        )));
    }

    #[test]
    fn test_compose_preserves_rule_classification() {
        let spec_a = make_simple_spec(
            "A",
            &[("Int", Some("i32"), true)],
            &[
                ("NumLit", "Int", vec![SyntaxItemSpec::Terminal("0".to_string())]),
                (
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
                ),
            ],
        );

        let spec_b = make_simple_spec(
            "B",
            &[("Int", Some("i32"), false)],
            &[(
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
            )],
        );

        let merged = compose_languages(&spec_a, &spec_b).expect("composition should succeed");

        assert_eq!(merged.rules.len(), 3);

        let num_lit = merged
            .rules
            .iter()
            .find(|r| r.label == "NumLit")
            .expect("NumLit");
        assert!(!num_lit.is_infix);
        assert!(!num_lit.is_var);

        let add = merged.rules.iter().find(|r| r.label == "Add").expect("Add");
        assert!(add.is_infix);

        let mul = merged.rules.iter().find(|r| r.label == "Mul").expect("Mul");
        assert!(mul.is_infix);
    }

    #[test]
    fn test_compose_many_three_grammars() {
        let spec_a = make_simple_spec(
            "A",
            &[("Int", Some("i32"), true)],
            &[("NumLit", "Int", vec![SyntaxItemSpec::Terminal("0".to_string())])],
        );

        let spec_b = make_simple_spec(
            "B",
            &[("Bool", Some("bool"), false)],
            &[("True", "Bool", vec![SyntaxItemSpec::Terminal("true".to_string())])],
        );

        let spec_c = make_simple_spec(
            "C",
            &[("Str", None, false)],
            &[("StrLit", "Str", vec![SyntaxItemSpec::Terminal("\"\"".to_string())])],
        );

        let merged =
            compose_many(&[&spec_a, &spec_b, &spec_c]).expect("composition should succeed");

        assert_eq!(merged.types.len(), 3);
        assert_eq!(merged.rules.len(), 3);
        assert!(merged.name.contains("A"));
        assert!(merged.name.contains("B"));
        assert!(merged.name.contains("C"));
    }

    #[test]
    fn test_composition_summary() {
        let spec_a = make_simple_spec(
            "A",
            &[("Int", Some("i32"), true), ("Bool", Some("bool"), false)],
            &[("NumLit", "Int", vec![SyntaxItemSpec::Terminal("0".to_string())])],
        );

        let spec_b = make_simple_spec(
            "B",
            &[("Int", Some("i32"), false), ("Str", None, false)],
            &[("StrLit", "Str", vec![SyntaxItemSpec::Terminal("\"\"".to_string())])],
        );

        let merged = compose_languages(&spec_a, &spec_b).expect("composition should succeed");
        let summary = composition_summary(&spec_a, &spec_b, &merged);

        assert_eq!(summary.categories_a, 2);
        assert_eq!(summary.categories_b, 2);
        assert_eq!(summary.categories_merged, 3); // Int shared, Bool + Str unique
        assert_eq!(summary.shared_categories, vec!["Int"]);
        assert_eq!(summary.rules_a, 1);
        assert_eq!(summary.rules_b, 1);
    }

    #[test]
    fn test_compose_empty_grammars() {
        let spec_a = make_simple_spec("A", &[], &[]);
        let spec_b = make_simple_spec("B", &[], &[]);

        let merged = compose_languages(&spec_a, &spec_b).expect("composition should succeed");
        assert_eq!(merged.types.len(), 0);
        assert_eq!(merged.rules.len(), 0);
    }

    #[test]
    fn test_compose_many_empty() {
        let merged = compose_many(&[]).expect("composition should succeed");
        assert_eq!(merged.name, "empty");
        assert_eq!(merged.types.len(), 0);
        assert_eq!(merged.rules.len(), 0);
    }

    #[test]
    fn test_compose_cross_category_rules() {
        let spec_a = make_simple_spec(
            "A",
            &[("Expr", None, true), ("Int", Some("i32"), false)],
            &[
                ("NumLit", "Int", vec![SyntaxItemSpec::Terminal("0".to_string())]),
                // Cross-category: Expr → Int (cast)
                (
                    "IntCast",
                    "Expr",
                    vec![SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "val".to_string(),
                    }],
                ),
            ],
        );

        let spec_b = make_simple_spec(
            "B",
            &[("Expr", None, false), ("Bool", Some("bool"), false)],
            &[
                ("TrueLit", "Bool", vec![SyntaxItemSpec::Terminal("true".to_string())]),
                // Cross-category: Expr → Bool (cast)
                (
                    "BoolCast",
                    "Expr",
                    vec![SyntaxItemSpec::NonTerminal {
                        category: "Bool".to_string(),
                        param_name: "val".to_string(),
                    }],
                ),
            ],
        );

        let merged = compose_languages(&spec_a, &spec_b).expect("composition should succeed");

        assert_eq!(merged.types.len(), 3); // Expr, Int, Bool
        assert_eq!(merged.rules.len(), 4);

        let int_cast = merged
            .rules
            .iter()
            .find(|r| r.label == "IntCast")
            .expect("IntCast");
        assert!(int_cast.is_cast);
        assert_eq!(int_cast.cast_source_category.as_deref(), Some("Int"));

        let bool_cast = merged
            .rules
            .iter()
            .find(|r| r.label == "BoolCast")
            .expect("BoolCast");
        assert!(bool_cast.is_cast);
        assert_eq!(bool_cast.cast_source_category.as_deref(), Some("Bool"));
    }

    #[test]
    fn test_compose_with_collection_rules() {
        let spec_a = make_simple_spec(
            "A",
            &[("Expr", None, true), ("Int", Some("i32"), false)],
            &[("NumLit", "Int", vec![SyntaxItemSpec::Terminal("0".to_string())])],
        );

        let spec_b = LanguageSpec {
            name: "B".to_string(),
            types: vec![CategorySpec {
                name: "Expr".to_string(),
                native_type: None,
                is_primary: false,
            }],
            rules: vec![RuleSpec::classified(
                "List",
                "Expr",
                vec![
                    SyntaxItemSpec::Terminal("[".to_string()),
                    SyntaxItemSpec::Collection {
                        param_name: "elems".to_string(),
                        element_category: "Expr".to_string(),
                        separator: ",".to_string(),
                        kind: crate::recursive::CollectionKind::Vec,
                    },
                    SyntaxItemSpec::Terminal("]".to_string()),
                ],
                &["Expr".to_string(), "Int".to_string()],
            )],
            beam_width: BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            literal_patterns: LiteralPatterns::default(),
            recovery_config: crate::recovery::RecoveryConfig::default(),
            semantic_dependency_groups: Vec::new(),
        };

        let merged = compose_languages(&spec_a, &spec_b).expect("composition should succeed");

        assert_eq!(merged.types.len(), 2);
        assert_eq!(merged.rules.len(), 2);

        let list = merged
            .rules
            .iter()
            .find(|r| r.label == "List")
            .expect("List");
        assert!(list.is_collection);
    }

    #[test]
    fn test_error_display() {
        let err = CompositionError::CategoryNativeTypeMismatch {
            category: "Int".to_string(),
            native_type_a: Some("i32".to_string()),
            native_type_b: Some("i64".to_string()),
        };
        assert!(format!("{}", err).contains("i32"));
        assert!(format!("{}", err).contains("i64"));

        let err = CompositionError::DuplicateRuleLabel {
            label: "Foo".to_string(),
            category_a: "A".to_string(),
            category_b: "B".to_string(),
        };
        assert!(format!("{}", err).contains("Foo"));

        let err = CompositionError::InvalidCategoryReference {
            rule_label: "Bar".to_string(),
            referenced_category: "Missing".to_string(),
        };
        assert!(format!("{}", err).contains("Missing"));

        let err = CompositionError::BindingPowerConflict {
            terminal: "-".to_string(),
            category: "Int".to_string(),
            bp_a: 10,
            bp_b: 20,
        };
        let msg = format!("{}", err);
        assert!(msg.contains("-"));
        assert!(msg.contains("10"));
        assert!(msg.contains("20"));
    }

    #[test]
    fn test_binding_power_conflict_detection() {
        // Grammar A: unary "-" with prefix_precedence 10
        let spec_a = {
            let types = vec![CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: true,
            }];
            let cat_names = vec!["Int".to_string()];
            let rules = vec![RuleSpec::classified(
                "Neg",
                "Int",
                vec![
                    SyntaxItemSpec::Terminal("-".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "a".to_string(),
                    },
                ],
                &cat_names,
            )];
            let mut spec = LanguageSpec {
                name: "A".to_string(),
                types,
                rules,
                beam_width: BeamWidthConfig::Disabled,
                log_semiring_model_path: None,
                    literal_patterns: LiteralPatterns::default(),
                recovery_config: crate::recovery::RecoveryConfig::default(),
                semantic_dependency_groups: Vec::new(),
            };
            // Manually set prefix_precedence to simulate user override
            spec.rules[0].prefix_precedence = Some(10);
            spec
        };

        // Grammar B: unary "-" with prefix_precedence 20 (conflict!)
        let spec_b = {
            let types = vec![CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: false,
            }];
            let cat_names = vec!["Int".to_string()];
            let rules = vec![RuleSpec::classified(
                "Negate",
                "Int",
                vec![
                    SyntaxItemSpec::Terminal("-".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "a".to_string(),
                    },
                ],
                &cat_names,
            )];
            let mut spec = LanguageSpec {
                name: "B".to_string(),
                types,
                rules,
                beam_width: BeamWidthConfig::Disabled,
                log_semiring_model_path: None,
                    literal_patterns: LiteralPatterns::default(),
                recovery_config: crate::recovery::RecoveryConfig::default(),
                semantic_dependency_groups: Vec::new(),
            };
            spec.rules[0].prefix_precedence = Some(20);
            spec
        };

        let err = compose_languages(&spec_a, &spec_b).expect_err("should fail with BP conflict");
        assert!(
            err.iter().any(|e| matches!(
                e,
                CompositionError::BindingPowerConflict { terminal, bp_a, bp_b, .. }
                if terminal == "-" && *bp_a == 10 && *bp_b == 20
            )),
            "Expected BindingPowerConflict for '-', got: {:?}",
            err
        );
    }

    #[test]
    fn test_binding_power_no_conflict_when_matching() {
        // Both grammars have "-" with prefix_precedence 10 — no conflict
        let spec_a = {
            let types = vec![CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: true,
            }];
            let cat_names = vec!["Int".to_string()];
            let rules = vec![RuleSpec::classified(
                "Neg",
                "Int",
                vec![
                    SyntaxItemSpec::Terminal("-".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "a".to_string(),
                    },
                ],
                &cat_names,
            )];
            let mut spec = LanguageSpec {
                name: "A".to_string(),
                types,
                rules,
                beam_width: BeamWidthConfig::Disabled,
                log_semiring_model_path: None,
                    literal_patterns: LiteralPatterns::default(),
                recovery_config: crate::recovery::RecoveryConfig::default(),
                semantic_dependency_groups: Vec::new(),
            };
            spec.rules[0].prefix_precedence = Some(10);
            spec
        };

        let spec_b = {
            let types = vec![CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: false,
            }];
            let cat_names = vec!["Int".to_string()];
            let rules = vec![RuleSpec::classified(
                "Negate",
                "Int",
                vec![
                    SyntaxItemSpec::Terminal("-".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "a".to_string(),
                    },
                ],
                &cat_names,
            )];
            let mut spec = LanguageSpec {
                name: "B".to_string(),
                types,
                rules,
                beam_width: BeamWidthConfig::Disabled,
                log_semiring_model_path: None,
                    literal_patterns: LiteralPatterns::default(),
                recovery_config: crate::recovery::RecoveryConfig::default(),
                semantic_dependency_groups: Vec::new(),
            };
            spec.rules[0].prefix_precedence = Some(10);
            spec
        };

        // This should succeed (label collision is the only error, but our labels differ)
        compose_languages(&spec_a, &spec_b).expect("composition should succeed with matching BPs");
    }

    // ── WFST-aware composition tests ────────────────────────────────────

    #[test]
    fn test_compose_with_wfst_disjoint() {
        use crate::automata::semiring::TropicalWeight;
        use crate::prediction::DispatchAction;
        use crate::token_id::TokenIdMap;
        use crate::wfst::PredictionWfstBuilder;

        let spec_a = make_simple_spec(
            "Arith",
            &[("Int", Some("i32"), true)],
            &[("NumLit", "Int", vec![SyntaxItemSpec::Terminal("0".to_string())])],
        );
        let spec_b = make_simple_spec(
            "Logic",
            &[("Bool", Some("bool"), true)],
            &[("True", "Bool", vec![SyntaxItemSpec::Terminal("true".to_string())])],
        );

        // Build WFSTs for each grammar
        let token_map_a = TokenIdMap::from_names(vec!["Zero".to_string()].into_iter());
        let mut builder_a = PredictionWfstBuilder::new("Int", token_map_a);
        builder_a.add_action(
            "Zero",
            DispatchAction::Direct {
                rule_label: "NumLit".to_string(),
                parse_fn: "parse_numlit".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst_a = builder_a.build();

        let token_map_b = TokenIdMap::from_names(vec!["True".to_string()].into_iter());
        let mut builder_b = PredictionWfstBuilder::new("Bool", token_map_b);
        builder_b.add_action(
            "True",
            DispatchAction::Direct {
                rule_label: "True".to_string(),
                parse_fn: "parse_true".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst_b = builder_b.build();

        let mut wfsts_a = HashMap::new();
        wfsts_a.insert("Int".to_string(), wfst_a);
        let mut wfsts_b = HashMap::new();
        wfsts_b.insert("Bool".to_string(), wfst_b);

        let terminals_a: HashSet<String> = ["0"].iter().map(|s| s.to_string()).collect();
        let terminals_b: HashSet<String> = ["true"].iter().map(|s| s.to_string()).collect();

        let result =
            compose_with_wfst(&spec_a, &spec_b, &wfsts_a, &wfsts_b, &terminals_a, &terminals_b)
                .expect("composition should succeed");

        assert_eq!(result.prediction_wfsts.len(), 2);
        assert_eq!(result.summary.wfsts_merged, 0); // disjoint = no merges
        assert_eq!(result.terminals.len(), 2);
        assert!(result.terminals.contains("0"));
        assert!(result.terminals.contains("true"));
    }

    #[test]
    fn test_compose_with_wfst_shared_category() {
        use crate::automata::semiring::TropicalWeight;
        use crate::prediction::DispatchAction;
        use crate::token_id::TokenIdMap;
        use crate::wfst::PredictionWfstBuilder;

        let spec_a = make_simple_spec(
            "Base",
            &[("Expr", None, true)],
            &[("Num", "Expr", vec![SyntaxItemSpec::Terminal("0".to_string())])],
        );
        let spec_b = make_simple_spec(
            "Extension",
            &[("Expr", None, true)],
            &[(
                "Var",
                "Expr",
                vec![SyntaxItemSpec::IdentCapture { param_name: "x".to_string() }],
            )],
        );

        // WFSTs for shared category "Expr"
        let token_map_a = TokenIdMap::from_names(vec!["Zero".to_string()].into_iter());
        let mut builder_a = PredictionWfstBuilder::new("Expr", token_map_a);
        builder_a.add_action(
            "Zero",
            DispatchAction::Direct {
                rule_label: "Num".to_string(),
                parse_fn: "parse_num".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst_a = builder_a.build();

        let token_map_b = TokenIdMap::from_names(vec!["Ident".to_string()].into_iter());
        let mut builder_b = PredictionWfstBuilder::new("Expr", token_map_b);
        builder_b.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0),
        );
        let wfst_b = builder_b.build();

        let mut wfsts_a = HashMap::new();
        wfsts_a.insert("Expr".to_string(), wfst_a);
        let mut wfsts_b = HashMap::new();
        wfsts_b.insert("Expr".to_string(), wfst_b);

        let terminals_a: HashSet<String> = ["0"].iter().map(|s| s.to_string()).collect();
        let terminals_b: HashSet<String> = ["x"].iter().map(|s| s.to_string()).collect();

        let result =
            compose_with_wfst(&spec_a, &spec_b, &wfsts_a, &wfsts_b, &terminals_a, &terminals_b)
                .expect("composition should succeed");

        assert_eq!(result.prediction_wfsts.len(), 1); // one shared category
        assert_eq!(result.summary.wfsts_merged, 1); // one union performed

        // The merged WFST should have actions from both sources
        let merged_wfst = result.prediction_wfsts.get("Expr").expect("Expr WFST");
        assert_eq!(merged_wfst.num_actions(), 2); // Num + Var

        // Should be able to predict both tokens
        let zero_results = merged_wfst.predict("Zero");
        assert_eq!(zero_results.len(), 1);
        assert_eq!(zero_results[0].weight, TropicalWeight::new(0.0));

        let ident_results = merged_wfst.predict("Ident");
        assert_eq!(ident_results.len(), 1);
        assert_eq!(ident_results[0].weight, TropicalWeight::new(2.0));
    }

    #[test]
    fn test_compose_with_wfst_summary_display() {
        use crate::automata::semiring::TropicalWeight;
        use crate::prediction::DispatchAction;
        use crate::token_id::TokenIdMap;
        use crate::wfst::PredictionWfstBuilder;

        let spec_a = make_simple_spec(
            "A",
            &[("Expr", None, true)],
            &[("NumA", "Expr", vec![SyntaxItemSpec::Terminal("0".to_string())])],
        );
        let spec_b = make_simple_spec(
            "B",
            &[("Expr", None, false)],
            &[("NumB", "Expr", vec![SyntaxItemSpec::Terminal("1".to_string())])],
        );

        let token_map = TokenIdMap::from_names(vec!["Zero".to_string()].into_iter());
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Zero",
            DispatchAction::Direct {
                rule_label: "NumA".to_string(),
                parse_fn: "parse_numa".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst_a = builder.build();

        let token_map = TokenIdMap::from_names(vec!["One".to_string()].into_iter());
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "One",
            DispatchAction::Direct {
                rule_label: "NumB".to_string(),
                parse_fn: "parse_numb".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst_b = builder.build();

        let mut wfsts_a = HashMap::new();
        wfsts_a.insert("Expr".to_string(), wfst_a);
        let mut wfsts_b = HashMap::new();
        wfsts_b.insert("Expr".to_string(), wfst_b);

        let terminals_a: HashSet<String> = ["0"].iter().map(|s| s.to_string()).collect();
        let terminals_b: HashSet<String> = ["1"].iter().map(|s| s.to_string()).collect();

        let result =
            compose_with_wfst(&spec_a, &spec_b, &wfsts_a, &wfsts_b, &terminals_a, &terminals_b)
                .expect("composition should succeed");

        let display = format!("{}", result.summary);
        assert!(display.contains("WFSTs: 1"));
        assert!(display.contains("1 merged"));
        assert!(display.contains("actions:"));
        assert!(display.contains("states:"));
    }

    // ── A6: ComposedLexerParser tests ────────────────────────────────────

    /// Simple linear lexer: state 0 →(class 0)→ state 1 (accepts "tok_a"),
    /// one WFST transition on "tok_a" from state 0 → state 1 (accepting with action "Act").
    #[test]
    fn test_a6_compose_single_token() {
        let composed = ComposedLexerParser::compose(
            "Expr",
            2,  // lexer states: 0, 1
            2,  // wfst states: 0, 1
            |state, class| {
                if state == 0 && class == 0 { 1 } else { u32::MAX }
            },
            |state| {
                if state == 1 {
                    vec![("tok_a".to_string(), 0.0)]
                } else {
                    vec![]
                }
            },
            |state, token| {
                if state == 0 && token == "tok_a" {
                    vec![(1, 1.5)]
                } else {
                    vec![]
                }
            },
            |state| {
                if state == 1 {
                    vec!["Act".to_string()]
                } else {
                    vec![]
                }
            },
            1,  // 1 byte class
        );

        assert_eq!(composed.category, "Expr");
        // States: (0,0) → (1,0) non-accepting internal step? No — state 1 is accepting,
        // so it goes (0,0) →(class 0)→ (0,1) with output "tok_a"
        // (0,1) is WFST-accepting with action "Act"
        assert!(composed.num_states() >= 2, "expected at least 2 states, got {}", composed.num_states());
        assert!(composed.num_transitions() >= 1, "expected at least 1 transition");

        // The accepting state should have WFST state 1
        let accepting_wfst_states: Vec<u32> = composed.accepting.iter().map(|(s, _)| s.wfst_state).collect();
        assert!(accepting_wfst_states.contains(&1), "expected WFST state 1 in accepting: {:?}", accepting_wfst_states);

        // Check the action label
        let actions: Vec<&str> = composed.accepting.iter()
            .filter(|(s, _)| s.wfst_state == 1)
            .flat_map(|(_, a)| a.iter().map(|s| s.as_str()))
            .collect();
        assert!(actions.contains(&"Act"), "expected 'Act' in actions: {:?}", actions);

        // Check the transition weight: lex_weight(0.0) + wfst_weight(1.5) = 1.5
        let token_transitions: Vec<&ComposedTransition> = composed.transitions.iter()
            .flat_map(|ts| ts.iter())
            .filter(|t| t.output_token.is_some())
            .collect();
        assert_eq!(token_transitions.len(), 1);
        assert_eq!(token_transitions[0].weight, crate::automata::semiring::TropicalWeight::new(1.5));
    }

    /// Two-step lexer: state 0 →(class 0)→ state 1 →(class 1)→ state 2 (accepts "kw").
    /// WFST: state 0 →("kw")→ state 1 (accepting).
    #[test]
    fn test_a6_compose_multi_step_lexer() {
        let composed = ComposedLexerParser::compose(
            "Stmt",
            3,  // lexer states: 0, 1, 2
            2,  // wfst states: 0, 1
            |state, class| match (state, class) {
                (0, 0) => 1,
                (1, 1) => 2,
                _ => u32::MAX,
            },
            |state| {
                if state == 2 {
                    vec![("kw".to_string(), 0.5)]
                } else {
                    vec![]
                }
            },
            |state, token| {
                if state == 0 && token == "kw" {
                    vec![(1, 2.0)]
                } else {
                    vec![]
                }
            },
            |state| {
                if state == 1 {
                    vec!["ParseKw".to_string()]
                } else {
                    vec![]
                }
            },
            2,  // 2 byte classes
        );

        // States: (0,0) →(class 0)→ (1,0) non-accepting →(class 1)→ (0,1) accepting
        assert!(composed.num_states() >= 3, "expected at least 3 states, got {}", composed.num_states());

        // Non-accepting transitions should carry weight TropicalWeight::one() (0.0)
        let internal_transitions: Vec<&ComposedTransition> = composed.transitions.iter()
            .flat_map(|ts| ts.iter())
            .filter(|t| t.output_token.is_none())
            .collect();
        for t in &internal_transitions {
            assert_eq!(t.weight, crate::automata::semiring::TropicalWeight::new(0.0),
                "internal transitions should have weight 0.0, got {:?}", t.weight);
        }

        // The accepting transition should carry combined weight: 0.5 + 2.0 = 2.5
        let token_transitions: Vec<&ComposedTransition> = composed.transitions.iter()
            .flat_map(|ts| ts.iter())
            .filter(|t| t.output_token.as_deref() == Some("kw"))
            .collect();
        assert_eq!(token_transitions.len(), 1);
        assert_eq!(token_transitions[0].weight, crate::automata::semiring::TropicalWeight::new(2.5));
    }

    /// Ambiguous lexer: state 1 accepts both "id" (weight 1.0) and "kw" (weight 0.0).
    /// WFST has transitions for both.
    #[test]
    fn test_a6_compose_ambiguous_lexer() {
        let composed = ComposedLexerParser::compose(
            "Expr",
            2,
            3,
            |state, class| {
                if state == 0 && class == 0 { 1 } else { u32::MAX }
            },
            |state| {
                if state == 1 {
                    vec![("kw".to_string(), 0.0), ("id".to_string(), 1.0)]
                } else {
                    vec![]
                }
            },
            |state, token| match (state, token) {
                (0, "kw") => vec![(1, 0.0)],
                (0, "id") => vec![(2, 0.5)],
                _ => vec![],
            },
            |state| match state {
                1 => vec!["ParseKw".to_string()],
                2 => vec!["ParseId".to_string()],
                _ => vec![],
            },
            1,
        );

        // Should produce two transitions from (0,0): one for "kw" and one for "id"
        let token_transitions: Vec<&ComposedTransition> = composed.transitions.iter()
            .flat_map(|ts| ts.iter())
            .filter(|t| t.output_token.is_some())
            .collect();
        assert_eq!(token_transitions.len(), 2, "expected 2 token transitions, got {}", token_transitions.len());

        // "kw" path: lex(0.0) + wfst(0.0) = 0.0
        let kw_trans = token_transitions.iter().find(|t| t.output_token.as_deref() == Some("kw")).expect("kw transition");
        assert_eq!(kw_trans.weight, crate::automata::semiring::TropicalWeight::new(0.0));

        // "id" path: lex(1.0) + wfst(0.5) = 1.5
        let id_trans = token_transitions.iter().find(|t| t.output_token.as_deref() == Some("id")).expect("id transition");
        assert_eq!(id_trans.weight, crate::automata::semiring::TropicalWeight::new(1.5));
    }

    /// Empty WFST (no transitions): composition should produce states but no token transitions.
    #[test]
    fn test_a6_compose_empty_wfst() {
        let composed = ComposedLexerParser::compose(
            "Empty",
            2,
            1,
            |state, class| {
                if state == 0 && class == 0 { 1 } else { u32::MAX }
            },
            |state| {
                if state == 1 {
                    vec![("tok".to_string(), 0.0)]
                } else {
                    vec![]
                }
            },
            |_state, _token| vec![], // No WFST transitions
            |_state| vec![],
            1,
        );

        // No token transitions because WFST has no transition for "tok"
        let token_transitions: usize = composed.transitions.iter()
            .flat_map(|ts| ts.iter())
            .filter(|t| t.output_token.is_some())
            .count();
        assert_eq!(token_transitions, 0, "no token transitions expected when WFST is empty");
        assert!(composed.accepting.is_empty(), "no accepting states expected");
    }

    /// Dead lexer states (u32::MAX) should not be explored.
    #[test]
    fn test_a6_compose_dead_lexer_states() {
        let composed = ComposedLexerParser::compose(
            "Expr",
            3,
            2,
            |state, class| match (state, class) {
                (0, 0) => 1,    // class 0 → state 1 (accepting)
                (0, 1) => u32::MAX, // class 1 → dead
                _ => u32::MAX,
            },
            |state| {
                if state == 1 { vec![("t".to_string(), 0.0)] } else { vec![] }
            },
            |state, token| {
                if state == 0 && token == "t" { vec![(1, 0.0)] } else { vec![] }
            },
            |state| {
                if state == 1 { vec!["A".to_string()] } else { vec![] }
            },
            2,
        );

        // Only reachable states should be discovered
        // (0,0) → (0,1) via token "t"
        // No state with lexer_state == 2 should appear (dead)
        for s in &composed.states {
            assert_ne!(s.lexer_state, 2, "lexer state 2 should not be reachable");
        }
    }

    /// Expansion factor calculation.
    #[test]
    fn test_a6_expansion_factor() {
        let composed = ComposedLexerParser::compose(
            "X",
            4,  // 4 lexer states
            3,  // 3 WFST states → max 12 composed states
            |state, class| {
                if state == 0 && class == 0 { 1 } else { u32::MAX }
            },
            |state| {
                if state == 1 { vec![("t".to_string(), 0.0)] } else { vec![] }
            },
            |state, token| {
                if state == 0 && token == "t" { vec![(1, 0.0)] } else { vec![] }
            },
            |state| {
                if state == 1 { vec!["Act".to_string()] } else { vec![] }
            },
            1,
        );

        let factor = composed.expansion_factor();
        assert!(factor > 0.0, "expansion factor should be positive");
        assert!(factor <= 1.0, "expansion factor should not exceed 1.0");
        // Only (0,0) and (0,1) reachable → 2 / 12 ≈ 0.167
        let expected = composed.num_states() as f64 / 12.0;
        assert!((factor - expected).abs() < 1e-10, "expected {}, got {}", expected, factor);
    }

    /// Summary string format.
    #[test]
    fn test_a6_summary_format() {
        let composed = ComposedLexerParser::compose(
            "Expr",
            2, 2,
            |s, c| if s == 0 && c == 0 { 1 } else { u32::MAX },
            |s| if s == 1 { vec![("t".to_string(), 0.0)] } else { vec![] },
            |s, t| if s == 0 && t == "t" { vec![(1, 0.0)] } else { vec![] },
            |s| if s == 1 { vec!["A".to_string()] } else { vec![] },
            1,
        );

        let summary = composed.summary();
        assert!(summary.contains("Expr"), "summary should contain category name");
        assert!(summary.contains("ComposedLexerParser"), "summary should contain struct name");
        assert!(summary.contains("expansion="), "summary should contain expansion factor");
    }
}
