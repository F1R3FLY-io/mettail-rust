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
//!    `ZipMapSep` category reference must exist in the merged types.
//! 4. **Single primary**: Exactly one `is_primary: true` category.
//! 5. **Reclassification**: All derived flags re-derived via `classify::classify_rule()`.
//! 6. **FIRST/FOLLOW recomputation**: Handled by the pipeline (automatic).
//!
//! ## Derived from lling-llang
//!
//! The composition model draws from `lling-llang`'s `union()` and `compose()`
//! WFST operations. Grammar composition is the PraTTaIL analog of WFST union:
//! the merged grammar accepts inputs from either source grammar.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::binding_power::Associativity;
use crate::{
    BeamWidthConfig, CategorySpec, DispatchStrategy, LanguageSpec, RuleSpecInput, SyntaxItemSpec,
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
            wrap_collection_in_literal: rule.wrap_collection_in_literal,
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
            wrap_collection_in_literal: rule.wrap_collection_in_literal,
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
            SyntaxItemSpec::Terminal(_) | SyntaxItemSpec::IdentCapture { .. } => {},

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

            SyntaxItemSpec::ZipMapSep {
                left_category,
                right_category,
                body_items,
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
                // Recurse into body_items
                validate_category_refs(body_items, rule_label, valid_categories, errors);
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
            dispatch_strategy: DispatchStrategy::Static,
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
#[cfg(feature = "wfst")]
#[derive(Debug)]
pub struct WfstCompositionResult {
    /// The merged language specification.
    pub spec: LanguageSpec,
    /// Per-category prediction WFSTs, built via weighted union of the input WFSTs.
    /// Categories that appear in only one source grammar get their WFST unchanged.
    /// Categories shared across both sources get a union of both WFSTs.
    pub prediction_wfsts: BTreeMap<String, crate::wfst::PredictionWfst>,
    /// Terminal set of the merged grammar (union of both sources).
    pub terminals: BTreeSet<String>,
    /// Enriched composition summary with WFST statistics.
    pub summary: WfstCompositionSummary,
}

/// Enriched composition summary including WFST statistics.
#[cfg(feature = "wfst")]
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

#[cfg(feature = "wfst")]
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
#[cfg(feature = "wfst")]
pub fn compose_with_wfst(
    spec_a: &LanguageSpec,
    spec_b: &LanguageSpec,
    wfsts_a: &BTreeMap<String, crate::wfst::PredictionWfst>,
    wfsts_b: &BTreeMap<String, crate::wfst::PredictionWfst>,
    terminals_a: &BTreeSet<String>,
    terminals_b: &BTreeSet<String>,
) -> Result<WfstCompositionResult, Vec<CompositionError>> {
    // Step 1: Compose the language specs
    let merged_spec = compose_languages(spec_a, spec_b)?;
    let base_summary = composition_summary(spec_a, spec_b, &merged_spec);

    // Step 2: Merge terminal sets
    let terminals = crate::prediction::merge_terminal_sets(terminals_a, terminals_b);

    // Step 3: Merge prediction WFSTs per category
    let mut prediction_wfsts: BTreeMap<String, crate::wfst::PredictionWfst> = BTreeMap::new();
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
    })
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
            dispatch_strategy: DispatchStrategy::Static,
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
            dispatch_strategy: DispatchStrategy::Static,
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
            dispatch_strategy: DispatchStrategy::Static,
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
                dispatch_strategy: DispatchStrategy::Static,
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
                dispatch_strategy: DispatchStrategy::Static,
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
                dispatch_strategy: DispatchStrategy::Static,
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
                dispatch_strategy: DispatchStrategy::Static,
            };
            spec.rules[0].prefix_precedence = Some(10);
            spec
        };

        // This should succeed (label collision is the only error, but our labels differ)
        compose_languages(&spec_a, &spec_b).expect("composition should succeed with matching BPs");
    }

    // ── WFST-aware composition tests ────────────────────────────────────

    #[cfg(feature = "wfst")]
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

        let mut wfsts_a = BTreeMap::new();
        wfsts_a.insert("Int".to_string(), wfst_a);
        let mut wfsts_b = BTreeMap::new();
        wfsts_b.insert("Bool".to_string(), wfst_b);

        let terminals_a: BTreeSet<String> = ["0"].iter().map(|s| s.to_string()).collect();
        let terminals_b: BTreeSet<String> = ["true"].iter().map(|s| s.to_string()).collect();

        let result =
            compose_with_wfst(&spec_a, &spec_b, &wfsts_a, &wfsts_b, &terminals_a, &terminals_b)
                .expect("composition should succeed");

        assert_eq!(result.prediction_wfsts.len(), 2);
        assert_eq!(result.summary.wfsts_merged, 0); // disjoint = no merges
        assert_eq!(result.terminals.len(), 2);
        assert!(result.terminals.contains("0"));
        assert!(result.terminals.contains("true"));
    }

    #[cfg(feature = "wfst")]
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

        let mut wfsts_a = BTreeMap::new();
        wfsts_a.insert("Expr".to_string(), wfst_a);
        let mut wfsts_b = BTreeMap::new();
        wfsts_b.insert("Expr".to_string(), wfst_b);

        let terminals_a: BTreeSet<String> = ["0"].iter().map(|s| s.to_string()).collect();
        let terminals_b: BTreeSet<String> = ["x"].iter().map(|s| s.to_string()).collect();

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

    #[cfg(feature = "wfst")]
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

        let mut wfsts_a = BTreeMap::new();
        wfsts_a.insert("Expr".to_string(), wfst_a);
        let mut wfsts_b = BTreeMap::new();
        wfsts_b.insert("Expr".to_string(), wfst_b);

        let terminals_a: BTreeSet<String> = ["0"].iter().map(|s| s.to_string()).collect();
        let terminals_b: BTreeSet<String> = ["1"].iter().map(|s| s.to_string()).collect();

        let result =
            compose_with_wfst(&spec_a, &spec_b, &wfsts_a, &wfsts_b, &terminals_a, &terminals_b)
                .expect("composition should succeed");

        let display = format!("{}", result.summary);
        assert!(display.contains("WFSTs: 1"));
        assert!(display.contains("1 merged"));
        assert!(display.contains("actions:"));
        assert!(display.contains("states:"));
    }
}
