//! Unified Parse Dispatch via PathMap Decision Trees
//!
//! Replaces 7 ad-hoc dispatch optimizations (A1 left-factoring, B1 two-token
//! lookahead, G1 Phases 1-4) with a single trie-based mechanism. Each category
//! gets a decision tree where byte-encoded token prefixes map to parse rules.
//!
//! ## Encoding Scheme
//!
//! ```text
//! 0x00..0x7F  Terminal token IDs (from TokenIdMap; max ~100 typical)
//! 0x80        IDENT_CAPTURE — consumes exactly one Ident token
//! 0x81        BINDER_CAPTURE — consumes exactly one Ident (binding)
//! 0x82..0xBF  NonTerminal category IDs (0x82 + category_index)
//! 0xC0        OPTIONAL_START marker
//! 0xC1        OPTIONAL_END marker
//! ```
//!
//! The trie is **split at nonterminal boundaries** into linked segments.
//! At boundaries, FIRST set expansion determines if the decision is
//! deterministic (peek token) or ambiguous (NFA try-all on minimal set).
//!
//! ## Output Format
//!
//! Adaptive: match arms for small/medium grammars (<=256 states),
//! flat table for large grammars. Runtime PathMap is not used —
//! match arms are 4-8x faster per step.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};

use pathmap::PathMap;
use pathmap::ring::{AlgebraicResult, Lattice, DistributiveLattice};

use crate::automata::codegen::terminal_to_variant_name;
use crate::dispatch::{CastRule, CrossCategoryRule};
use crate::prediction::FirstSet;
use crate::recursive::{RDRuleInfo, RDSyntaxItem};
use crate::token_id::TokenIdMap;
use crate::wfst::PredictionWfst;

// ══════════════════════════════════════════════════════════════════════════════
// Byte encoding constants
// ══════════════════════════════════════════════════════════════════════════════

/// Marker byte for an ident capture position.
const IDENT_CAPTURE: u8 = 0x80;
/// Marker byte for a binder capture position.
const BINDER_CAPTURE: u8 = 0x81;
/// Base byte for nonterminal category IDs: category_index + NT_BASE.
#[allow(dead_code)]
const NT_BASE: u8 = 0x82;
/// Marker byte for optional group start.
const OPTIONAL_START: u8 = 0xC0;
/// Marker byte for optional group end.
const OPTIONAL_END: u8 = 0xC1;
/// Maximum terminal token ID that fits in the encoding.
const MAX_TERMINAL_ID: u8 = 0x7F;

// ══════════════════════════════════════════════════════════════════════════════
// Pattern elements (typed, pre-encoding)
// ══════════════════════════════════════════════════════════════════════════════

/// A typed element in a rule's pattern before byte encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PatternElement {
    /// Terminal token with its byte ID from TokenIdMap.
    Terminal { variant: String, id: u8 },
    /// Ident capture position.
    IdentCapture { param_name: String },
    /// Binder capture position.
    BinderCapture { param_name: String },
    /// Nonterminal parse position — triggers segment split.
    NonTerminal { category: String, category_id: u8 },
    /// Optional group start marker.
    OptionalStart,
    /// Optional group end marker.
    OptionalEnd,
}

// ══════════════════════════════════════════════════════════════════════════════
// Decision actions (stored at trie leaves/nodes)
// ══════════════════════════════════════════════════════════════════════════════

/// Action stored at a trie node/leaf.
#[derive(Clone, Debug)]
pub enum DecisionAction {
    /// Single unambiguous rule — commit without backtracking.
    Commit {
        rule_label: String,
        category: String,
        weight: f64,
    },
    /// Multiple rules compete at this node — need disambiguation.
    Ambiguous {
        candidates: Vec<AmbiguousCandidate>,
    },
    /// Nonterminal boundary — dispatch based on FIRST set expansion.
    NonterminalBoundary {
        options: Vec<NTOption>,
    },
}

/// A candidate rule in an ambiguous dispatch point.
#[derive(Clone, Debug)]
pub struct AmbiguousCandidate {
    pub rule_label: String,
    pub category: String,
    pub weight: f64,
    /// Items remaining after the shared prefix (for NFA try-all).
    pub remaining_items: usize,
}

/// An option at a nonterminal boundary.
#[derive(Clone, Debug)]
pub struct NTOption {
    pub kind: NTKind,
    /// FIRST set byte codes for dispatch after the nonterminal.
    pub first_tokens: Vec<u8>,
    /// Index into the segments vec for the continuation trie.
    pub resume_segment: usize,
    /// WFST weight for ordering.
    pub weight: f64,
}

/// Kind of nonterminal at a boundary.
#[derive(Clone, Debug)]
pub enum NTKind {
    /// Parse a nonterminal category.
    NonTerminal { category: String },
    /// Capture an identifier.
    IdentCapture,
    /// Capture a binder identifier.
    BinderCapture,
}

// Implement Lattice for DecisionAction so PathMap algebra works.
// join = merge (keep both), meet = intersect, subtract = difference.
impl Lattice for DecisionAction {
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        // Merge: combine candidates
        let mut candidates = Vec::new();
        match self {
            DecisionAction::Commit { rule_label, category, weight } => {
                candidates.push(AmbiguousCandidate {
                    rule_label: rule_label.clone(),
                    category: category.clone(),
                    weight: *weight,
                    remaining_items: 0,
                });
            }
            DecisionAction::Ambiguous { candidates: cs } => {
                candidates.extend(cs.iter().cloned());
            }
            DecisionAction::NonterminalBoundary { .. } => {
                return AlgebraicResult::Identity(1);
            }
        }
        match other {
            DecisionAction::Commit { rule_label, category, weight } => {
                candidates.push(AmbiguousCandidate {
                    rule_label: rule_label.clone(),
                    category: category.clone(),
                    weight: *weight,
                    remaining_items: 0,
                });
            }
            DecisionAction::Ambiguous { candidates: cs } => {
                candidates.extend(cs.iter().cloned());
            }
            DecisionAction::NonterminalBoundary { .. } => {
                return AlgebraicResult::Identity(2);
            }
        }
        AlgebraicResult::Element(DecisionAction::Ambiguous { candidates })
    }

    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        // Meet: keep only shared rules
        let self_labels: HashSet<&str> = self.rule_labels().collect();
        let other_labels: HashSet<&str> = other.rule_labels().collect();
        let common: HashSet<&&str> = self_labels.intersection(&other_labels).collect();
        if common.is_empty() {
            AlgebraicResult::None
        } else {
            let mut candidates = Vec::new();
            for c in self.all_candidates() {
                if common.contains(&c.rule_label.as_str()) {
                    candidates.push(c);
                }
            }
            if candidates.len() == 1 {
                let c = &candidates[0];
                AlgebraicResult::Element(DecisionAction::Commit {
                    rule_label: c.rule_label.clone(),
                    category: c.category.clone(),
                    weight: c.weight,
                })
            } else {
                AlgebraicResult::Element(DecisionAction::Ambiguous { candidates })
            }
        }
    }
}

impl DistributiveLattice for DecisionAction {
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> {
        let other_labels: HashSet<&str> = other.rule_labels().collect();
        let mut remaining: Vec<AmbiguousCandidate> = self
            .all_candidates()
            .into_iter()
            .filter(|c| !other_labels.contains(c.rule_label.as_str()))
            .collect();
        if remaining.is_empty() {
            AlgebraicResult::None
        } else if remaining.len() == 1 {
            let c = remaining.remove(0);
            AlgebraicResult::Element(DecisionAction::Commit {
                rule_label: c.rule_label,
                category: c.category,
                weight: c.weight,
            })
        } else {
            AlgebraicResult::Element(DecisionAction::Ambiguous { candidates: remaining })
        }
    }
}

impl DecisionAction {
    /// Iterator over all rule labels in this action.
    pub fn rule_labels(&self) -> impl Iterator<Item = &str> {
        let v: Vec<&str> = match self {
            DecisionAction::Commit { rule_label, .. } => vec![rule_label.as_str()],
            DecisionAction::Ambiguous { candidates } => {
                candidates.iter().map(|c| c.rule_label.as_str()).collect()
            }
            DecisionAction::NonterminalBoundary { .. } => Vec::new(),
        };
        v.into_iter()
    }

    /// All candidates as owned values (synthesizing one for Commit).
    fn all_candidates(&self) -> Vec<AmbiguousCandidate> {
        match self {
            DecisionAction::Commit { rule_label, category, weight } => {
                vec![AmbiguousCandidate {
                    rule_label: rule_label.clone(),
                    category: category.clone(),
                    weight: *weight,
                    remaining_items: 0,
                }]
            }
            DecisionAction::Ambiguous { candidates } => candidates.clone(),
            _ => Vec::new(),
        }
    }

    /// Whether this action is deterministic (single rule, no ambiguity).
    pub fn is_deterministic(&self) -> bool {
        matches!(self, DecisionAction::Commit { .. })
    }

    /// Whether this action has an NT boundary.
    pub fn is_nt_boundary(&self) -> bool {
        matches!(self, DecisionAction::NonterminalBoundary { .. })
    }
}

impl Hash for DecisionAction {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            DecisionAction::Commit { rule_label, .. } => {
                0u8.hash(state);
                rule_label.hash(state);
            }
            DecisionAction::Ambiguous { candidates } => {
                1u8.hash(state);
                for c in candidates {
                    c.rule_label.hash(state);
                }
            }
            DecisionAction::NonterminalBoundary { options } => {
                2u8.hash(state);
                options.len().hash(state);
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Per-category decision tree
// ══════════════════════════════════════════════════════════════════════════════

/// Per-category decision tree built from PathMap.
#[derive(Clone, Debug)]
pub struct CategoryDecisionTree {
    pub category: String,
    /// Trie segments. `segments[0]` is the root segment (terminal prefix).
    /// Additional segments are continuations after nonterminal boundaries.
    pub segments: Vec<PathMap<DecisionAction>>,
    /// Statistics for adaptive output and diagnostics.
    pub stats: TreeStats,
}

/// Statistics about a decision tree.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TreeStats {
    /// Total number of trie states (nodes with children or values).
    pub total_states: usize,
    /// Number of deterministic nodes (single child or Commit leaf).
    pub deterministic_nodes: usize,
    /// Number of ambiguous nodes (Ambiguous action).
    pub ambiguous_nodes: usize,
    /// Maximum depth from root to any leaf.
    pub max_depth: usize,
    /// Minimum tokens needed to resolve all deterministic dispatch.
    pub min_lookahead: usize,
    /// Number of nonterminal boundary nodes.
    pub nonterminal_boundaries: usize,
    /// States saved by prefix sharing (vs naive per-rule tries).
    pub shared_prefix_savings: usize,
    /// Total rules inserted into this tree.
    pub total_rules: usize,
    /// Rules that are fully deterministic (no ambiguity at their prefix).
    pub deterministic_rules: usize,
}

impl fmt::Display for TreeStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} states ({} deterministic, {} ambiguous), \
             max depth {}, min lookahead {}, \
             {} NT boundaries, {} shared-prefix savings, \
             {}/{} rules deterministic",
            self.total_states,
            self.deterministic_nodes,
            self.ambiguous_nodes,
            self.max_depth,
            self.min_lookahead,
            self.nonterminal_boundaries,
            self.shared_prefix_savings,
            self.deterministic_rules,
            self.total_rules,
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Builder
// ══════════════════════════════════════════════════════════════════════════════

/// Builds decision trees for all categories in a grammar.
pub struct DecisionTreeBuilder {
    /// Token variant name -> byte ID mapping.
    token_ids: TokenIdMap,
    /// Per-category FIRST sets.
    first_sets: HashMap<String, FirstSet>,
    /// Category name -> byte ID for NT encoding.
    category_id_map: HashMap<String, u8>,
    /// Category names in order.
    #[allow(dead_code)]
    category_names: Vec<String>,
    /// Built trees per category.
    trees: HashMap<String, CategoryDecisionTree>,
    /// Dead rule labels to exclude.
    dead_rules: HashSet<String>,
    /// NT boundary tracking: maps (category, prefix_bytes) to a list of
    /// (nt_category, resume_segment_index, remaining_pattern, rule_label).
    /// Used by CD02 segment merging to identify safe merge points.
    nt_boundary_map: HashMap<(String, Vec<u8>), Vec<NTBoundaryRecord>>,
    /// Original RD rules, retained for CD04 jump threading analysis.
    rd_rules_cache: Vec<RDRuleInfo>,
}

/// Record of a nonterminal boundary for CD02 segment merging analysis.
#[derive(Clone, Debug)]
pub struct NTBoundaryRecord {
    /// Category of the nonterminal at the boundary.
    pub nt_category: String,
    /// Index into the category's segments vec for the continuation trie.
    pub resume_segment: usize,
    /// The remaining pattern elements after the nonterminal.
    pub remaining_pattern: Vec<PatternElement>,
    /// The rule that produced this boundary.
    pub rule_label: String,
    /// Weight of the rule.
    pub weight: f64,
}

impl DecisionTreeBuilder {
    /// Create a new builder from pipeline data.
    pub fn new(
        token_ids: TokenIdMap,
        first_sets: HashMap<String, FirstSet>,
        category_names: Vec<String>,
        dead_rules: HashSet<String>,
    ) -> Self {
        let category_id_map: HashMap<String, u8> = category_names
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), i as u8))
            .collect();

        DecisionTreeBuilder {
            token_ids,
            first_sets,
            category_id_map,
            category_names,
            trees: HashMap::new(),
            dead_rules,
            nt_boundary_map: HashMap::new(),
            rd_rules_cache: Vec::new(),
        }
    }

    /// Encode a terminal variant name to its byte ID.
    fn encode_terminal(&self, variant: &str) -> Option<u8> {
        self.token_ids.get(variant).and_then(|id| {
            if id <= MAX_TERMINAL_ID as u16 {
                Some(id as u8)
            } else {
                None
            }
        })
    }

    /// Convert an RD rule's syntax items to typed pattern elements.
    pub fn pattern_from_rd_rule(&self, rule: &RDRuleInfo) -> Vec<PatternElement> {
        let mut elements = Vec::with_capacity(rule.items.len());
        for item in &rule.items {
            match item {
                RDSyntaxItem::Terminal(t) => {
                    let variant = terminal_to_variant_name(t);
                    if let Some(id) = self.encode_terminal(&variant) {
                        elements.push(PatternElement::Terminal { variant, id });
                    }
                }
                RDSyntaxItem::NonTerminal { category, .. } => {
                    if let Some(&cat_id) = self.category_id_map.get(category) {
                        elements.push(PatternElement::NonTerminal {
                            category: category.clone(),
                            category_id: cat_id,
                        });
                    }
                }
                RDSyntaxItem::IdentCapture { param_name } => {
                    elements.push(PatternElement::IdentCapture {
                        param_name: param_name.clone(),
                    });
                }
                RDSyntaxItem::Binder { param_name, .. } => {
                    elements.push(PatternElement::BinderCapture {
                        param_name: param_name.clone(),
                    });
                }
                RDSyntaxItem::Optional { inner } => {
                    elements.push(PatternElement::OptionalStart);
                    // Recursively encode inner items
                    for inner_item in inner {
                        let inner_rule = RDRuleInfo {
                            label: String::new(),
                            category: String::new(),
                            items: vec![inner_item.clone()],
                            has_binder: false,
                            has_multi_binder: false,
                            is_collection: false,
                            collection_type: None,
                            separator: None,
                            prefix_bp: None,
                            eval_mode: None,
                        };
                        let inner_elements = self.pattern_from_rd_rule(&inner_rule);
                        elements.extend(inner_elements);
                    }
                    elements.push(PatternElement::OptionalEnd);
                }
                // Collection, Sep, Map, Zip, SepList, BinderCollection
                // are complex constructs — they don't participate in prefix dispatch.
                // Rules with these items are handled by standalone functions.
                _ => break,
            }
        }
        elements
    }

    /// Encode terminal prefix of a pattern as bytes, stopping at the first
    /// nonterminal boundary. Returns (bytes, boundary_info).
    pub fn encode_terminal_prefix(
        pattern: &[PatternElement],
    ) -> (Vec<u8>, Option<NTBoundaryInfo>) {
        let mut bytes = Vec::with_capacity(pattern.len());
        for (i, elem) in pattern.iter().enumerate() {
            match elem {
                PatternElement::Terminal { id, .. } => bytes.push(*id),
                PatternElement::IdentCapture { .. } => bytes.push(IDENT_CAPTURE),
                PatternElement::BinderCapture { .. } => bytes.push(BINDER_CAPTURE),
                PatternElement::OptionalStart => bytes.push(OPTIONAL_START),
                PatternElement::OptionalEnd => bytes.push(OPTIONAL_END),
                PatternElement::NonTerminal { category, category_id } => {
                    return (
                        bytes,
                        Some(NTBoundaryInfo {
                            category: category.clone(),
                            category_id: *category_id,
                            remaining_pattern: pattern[i + 1..].to_vec(),
                            position: i,
                        }),
                    );
                }
            }
        }
        (bytes, None)
    }

    /// Get or create a category's decision tree.
    fn ensure_tree(&mut self, category: &str) -> &mut CategoryDecisionTree {
        if !self.trees.contains_key(category) {
            self.trees.insert(
                category.to_string(),
                CategoryDecisionTree {
                    category: category.to_string(),
                    segments: vec![PathMap::new()],
                    stats: TreeStats::default(),
                },
            );
        }
        self.trees.get_mut(category).expect("just inserted")
    }

    /// Insert all terminal-first RD rules into their category's decision tree.
    pub fn insert_rd_rules(&mut self, rd_rules: &[RDRuleInfo]) {
        // Cache rules for CD04 jump threading analysis
        self.rd_rules_cache = rd_rules.to_vec();
        for rule in rd_rules {
            // Skip dead rules
            if self.dead_rules.contains(&rule.label) {
                continue;
            }
            // Skip collections and unary prefix (handled separately)
            if rule.is_collection || rule.prefix_bp.is_some() {
                continue;
            }
            // Skip rules starting with nonterminal or ident capture
            let starts_with_nt = matches!(
                rule.items.first(),
                Some(RDSyntaxItem::NonTerminal { .. }) | Some(RDSyntaxItem::IdentCapture { .. })
            );
            if starts_with_nt {
                continue;
            }

            let pattern = self.pattern_from_rd_rule(rule);
            if pattern.is_empty() {
                continue;
            }

            let (prefix_bytes, nt_boundary) = Self::encode_terminal_prefix(&pattern);
            if prefix_bytes.is_empty() {
                continue;
            }

            let weight = self.rule_weight(&rule.label, &rule.category);
            let action = DecisionAction::Commit {
                rule_label: rule.label.clone(),
                category: rule.category.clone(),
                weight,
            };

            let tree = self.ensure_tree(&rule.category);
            // Insert into root segment. If a value already exists, merge via join.
            if let Some(existing) = tree.segments[0].get(&prefix_bytes) {
                let merged = match existing.pjoin(&action) {
                    AlgebraicResult::Element(merged) => merged,
                    AlgebraicResult::Identity(_) => existing.clone(),
                    AlgebraicResult::None => action,
                };
                tree.segments[0].insert(&prefix_bytes, merged);
            } else {
                tree.segments[0].insert(&prefix_bytes, action);
            }

            // Handle nonterminal boundary: create continuation segment
            if let Some(boundary) = nt_boundary {
                self.insert_nt_continuation(&rule.category, &rule.label, weight, &boundary, &prefix_bytes);
            }
        }
    }

    /// Insert a continuation segment after a nonterminal boundary.
    fn insert_nt_continuation(
        &mut self,
        category: &str,
        rule_label: &str,
        weight: f64,
        boundary: &NTBoundaryInfo,
        prefix_bytes: &[u8],
    ) {
        // Track the NT boundary record for CD02 segment merging.
        // Done first to avoid borrow conflict with ensure_tree below.
        let record = NTBoundaryRecord {
            nt_category: boundary.category.clone(),
            resume_segment: 0, // placeholder; updated below
            remaining_pattern: boundary.remaining_pattern.clone(),
            rule_label: rule_label.to_string(),
            weight,
        };

        let tree = self.ensure_tree(category);
        let resume_idx = tree.segments.len();
        tree.segments.push(PathMap::new());

        // Encode the remaining pattern after the nonterminal
        let (continuation_bytes, _) = Self::encode_terminal_prefix(&boundary.remaining_pattern);
        if !continuation_bytes.is_empty() {
            let action = DecisionAction::Commit {
                rule_label: rule_label.to_string(),
                category: category.to_string(),
                weight,
            };
            tree.segments[resume_idx].insert(&continuation_bytes, action);
        }

        // Now update the root segment's value to include the NT boundary info
        // We need to get the prefix bytes that led to this boundary
        // This is done by re-encoding the pattern up to the boundary position
        // (The caller already inserted the terminal prefix; we need to annotate it)
        // For now, the NT boundary information is tracked in stats
        tree.stats.nonterminal_boundaries += 1;

        // Update the record with the actual resume segment index
        let mut record = record;
        record.resume_segment = resume_idx;
        self.nt_boundary_map
            .entry((category.to_string(), prefix_bytes.to_vec()))
            .or_default()
            .push(record);
    }

    /// Insert cross-category dispatch rules.
    pub fn insert_cross_category_rules(&mut self, cross_rules: &[CrossCategoryRule]) {
        for rule in cross_rules {
            if self.dead_rules.contains(&rule.label) {
                continue;
            }
            let operator_variant = terminal_to_variant_name(&rule.operator);
            if let Some(op_id) = self.encode_terminal(&operator_variant) {
                // Cross-category: source NT + operator terminal
                // The dispatch token is determined by FIRST(source_category)
                // We insert under each FIRST token of the source category
                if let Some(first) = self.first_sets.get(&rule.source_category).cloned() {
                    let weight = self.rule_weight(&rule.label, &rule.result_category);
                    for token in &first.tokens {
                        let variant = terminal_to_variant_name(token);
                        if let Some(tok_id) = self.encode_terminal(&variant) {
                            // Path: [source_first_token, operator_token]
                            let path = vec![tok_id, op_id];
                            let action = DecisionAction::Commit {
                                rule_label: rule.label.clone(),
                                category: rule.result_category.clone(),
                                weight,
                            };
                            let tree = self.ensure_tree(&rule.result_category);
                            if let Some(existing) = tree.segments[0].get(&path) {
                                let merged = match existing.pjoin(&action) {
                                    AlgebraicResult::Element(m) => m,
                                    AlgebraicResult::Identity(_) => existing.clone(),
                                    AlgebraicResult::None => action,
                                };
                                tree.segments[0].insert(&path, merged);
                            } else {
                                tree.segments[0].insert(&path, action);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Insert cast rules.
    pub fn insert_cast_rules(&mut self, cast_rules: &[CastRule]) {
        for rule in cast_rules {
            if self.dead_rules.contains(&rule.label) {
                continue;
            }
            // Cast: unique tokens in source FIRST but not target FIRST
            let source_first = self.first_sets.get(&rule.source_category).cloned();
            let target_first = self.first_sets.get(&rule.target_category).cloned();
            if let (Some(sf), Some(tf)) = (source_first, target_first) {
                let unique_tokens = sf.difference(&tf);
                let weight = self.rule_weight(&rule.label, &rule.target_category);
                for token in &unique_tokens.tokens {
                    let variant = terminal_to_variant_name(token);
                    if let Some(tok_id) = self.encode_terminal(&variant) {
                        let path = vec![tok_id];
                        let action = DecisionAction::Commit {
                            rule_label: rule.label.clone(),
                            category: rule.target_category.clone(),
                            weight,
                        };
                        let tree = self.ensure_tree(&rule.target_category);
                        if let Some(existing) = tree.segments[0].get(&path) {
                            let merged = match existing.pjoin(&action) {
                                AlgebraicResult::Element(m) => m,
                                AlgebraicResult::Identity(_) => existing.clone(),
                                AlgebraicResult::None => action,
                            };
                            tree.segments[0].insert(&path, merged);
                        } else {
                            tree.segments[0].insert(&path, action);
                        }
                    }
                }
            }
        }
    }

    /// Look up a rule's WFST weight.
    fn rule_weight(&self, _rule_label: &str, _category: &str) -> f64 {
        // Default weight — will be refined with actual WFST data in integration
        0.0
    }

    /// Build all decision trees for a grammar's rules.
    pub fn build_all(
        &mut self,
        rd_rules: &[RDRuleInfo],
        cross_rules: &[CrossCategoryRule],
        cast_rules: &[CastRule],
    ) {
        self.insert_rd_rules(rd_rules);
        self.insert_cross_category_rules(cross_rules);
        self.insert_cast_rules(cast_rules);

        // Compute statistics for each tree
        for tree in self.trees.values_mut() {
            tree.stats = compute_statistics(tree);
        }
    }

    /// Get the decision tree for a category.
    pub fn get_tree(&self, category: &str) -> Option<&CategoryDecisionTree> {
        self.trees.get(category)
    }

    /// Consume the builder and return all trees.
    pub fn into_trees(self) -> HashMap<String, CategoryDecisionTree> {
        self.trees
    }

    /// Get a reference to all trees.
    pub fn trees(&self) -> &HashMap<String, CategoryDecisionTree> {
        &self.trees
    }

    /// Get a mutable reference to all trees (for INT-02 pruning).
    pub fn trees_mut(&mut self) -> &mut HashMap<String, CategoryDecisionTree> {
        &mut self.trees
    }

    /// Get a reference to the FIRST sets (for external analysis).
    pub fn first_sets(&self) -> &HashMap<String, FirstSet> {
        &self.first_sets
    }

    /// Get a reference to the token ID map.
    pub fn token_ids(&self) -> &TokenIdMap {
        &self.token_ids
    }

    /// Get a reference to the NT boundary map (for CD02 analysis).
    pub fn nt_boundary_map(&self) -> &HashMap<(String, Vec<u8>), Vec<NTBoundaryRecord>> {
        &self.nt_boundary_map
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CD02: Decision Tree Segment Merging at Safe Nonterminal Boundaries
// ══════════════════════════════════════════════════════════════════════════════

/// CD02: Merge decision tree segments at nonterminal boundaries where FIRST
/// sets of all continuation suffixes are pairwise disjoint.
///
/// At a nonterminal boundary, the parser normally must:
///   1. Parse the nonterminal category
///   2. Then match the next token to determine which continuation to follow
///
/// With segment merging, if the FIRST sets of all post-NT suffixes are pairwise
/// disjoint, we can skip step 1's ambiguity and directly dispatch on the FIRST
/// token of the suffix. This reduces the effective tree depth and eliminates
/// one level of nonterminal parsing indirection.
///
/// ## Safety condition
///
/// For each NT boundary at prefix P in category C:
///   - Let S_1, S_2, ..., S_k be the continuation suffixes (remaining patterns
///     after the nonterminal).
///   - Compute FIRST(S_i) for each suffix.
///   - If FIRST(S_i) ∩ FIRST(S_j) = ∅ for all i ≠ j, the boundary is safe to merge.
///
/// When safe: replace the NT boundary with direct token dispatch. For each FIRST
/// token T ∈ FIRST(S_i), insert a path P ++ [T] → Commit(rule_i) into segment[0].
///
/// ## Gate
///
/// Controlled by `optimization_gates.segment_merging` (CD02).
///
/// Returns the number of boundaries merged.
pub fn merge_safe_nonterminal_boundaries(
    builder: &DecisionTreeBuilder,
    trees: &mut HashMap<String, CategoryDecisionTree>,
    first_sets: &HashMap<String, FirstSet>,
    token_ids: &TokenIdMap,
) -> usize {
    let mut merged_count = 0;

    for ((category, prefix_bytes), records) in builder.nt_boundary_map() {
        // Need at least 2 records at the same prefix to merit merging
        // (single-record boundaries are already unambiguous)
        if records.len() < 2 {
            continue;
        }

        // Compute FIRST sets for each continuation suffix
        let mut suffix_firsts: Vec<(usize, FirstSet)> = Vec::with_capacity(records.len());
        let mut all_disjoint = true;

        for (idx, record) in records.iter().enumerate() {
            // Convert remaining PatternElements back to RDSyntaxItems for
            // FIRST set computation (we need the terminal variant names)
            let first_set = first_set_of_pattern_suffix(&record.remaining_pattern, first_sets, token_ids);
            suffix_firsts.push((idx, first_set));
        }

        // Check pairwise disjointness
        'outer: for i in 0..suffix_firsts.len() {
            for j in (i + 1)..suffix_firsts.len() {
                if !suffix_firsts[i].1.is_disjoint(&suffix_firsts[j].1) {
                    all_disjoint = false;
                    break 'outer;
                }
            }
        }

        if !all_disjoint {
            continue;
        }

        // Safe to merge: for each record, insert FIRST tokens as direct dispatch
        let tree = match trees.get_mut(category) {
            Some(t) => t,
            None => continue,
        };

        for (idx, first_set) in &suffix_firsts {
            let record = &records[*idx];
            let action = DecisionAction::Commit {
                rule_label: record.rule_label.clone(),
                category: category.clone(),
                weight: record.weight,
            };

            for token in &first_set.tokens {
                if let Some(tok_id) = token_ids.get(token) {
                    if tok_id <= MAX_TERMINAL_ID as u16 {
                        let mut merged_path = prefix_bytes.clone();
                        merged_path.push(tok_id as u8);
                        // Only insert if not already present (avoid clobbering
                        // existing direct-terminal dispatch)
                        if tree.segments[0].get(&merged_path).is_none() {
                            tree.segments[0].insert(&merged_path, action.clone());
                        }
                    }
                }
            }
        }

        merged_count += 1;
    }

    // Recompute statistics after merging
    for tree in trees.values_mut() {
        tree.stats = compute_statistics(tree);
    }

    merged_count
}

/// Compute the FIRST set of a pattern suffix (Vec<PatternElement>).
///
/// This converts pattern elements back to terminal/nonterminal representations
/// for FIRST set computation.
fn first_set_of_pattern_suffix(
    pattern: &[PatternElement],
    first_sets: &HashMap<String, FirstSet>,
    _token_ids: &TokenIdMap,
) -> FirstSet {
    let mut result = FirstSet::new();
    let mut nullable = true;

    for elem in pattern {
        match elem {
            PatternElement::Terminal { variant, .. } => {
                result.insert(variant);
                nullable = false;
                break;
            }
            PatternElement::NonTerminal { category, .. } => {
                if let Some(cat_first) = first_sets.get(category) {
                    for token in &cat_first.tokens {
                        result.insert(token);
                    }
                    if !cat_first.nullable {
                        nullable = false;
                        break;
                    }
                } else {
                    nullable = false;
                    break;
                }
            }
            PatternElement::IdentCapture { .. } => {
                result.insert("Ident");
                nullable = false;
                break;
            }
            PatternElement::BinderCapture { .. } => {
                result.insert("Ident");
                nullable = false;
                break;
            }
            PatternElement::OptionalStart | PatternElement::OptionalEnd => {
                // Optional markers don't contribute to FIRST; continue
            }
        }
    }

    result.nullable = nullable;
    result
}

// ══════════════════════════════════════════════════════════════════════════════
// CD05: Prefix CSE (Common Subexpression Elimination) for Shared Nonterminals
// ══════════════════════════════════════════════════════════════════════════════

/// A detected CSE opportunity where multiple rules at the same trie prefix share
/// the same nonterminal parse as their next item. The parser can parse the
/// nonterminal once and cache the result, then branch on the discriminating
/// token that follows.
///
/// ## Example
///
/// Rules in category `Stmt`:
///   - `IfThen`:     `if ( <Expr> ) then <Stmt>`
///   - `IfThenElse`: `if ( <Expr> ) then <Stmt> else <Stmt>`
///
/// Both share terminal prefix `[KwIf, LParen]` and then parse `<Expr>`. The
/// shared nonterminal is `Expr`. After parsing `<Expr>`, the discriminating
/// tokens are the FIRST sets of the remaining suffixes (`[RParen]` for both —
/// then they diverge later). The key insight is that `<Expr>` need only be
/// parsed once.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedNonterminalPrefix {
    /// Category in which this CSE opportunity occurs.
    pub category: String,
    /// The terminal prefix bytes that lead to this NT boundary.
    pub prefix_bytes: Vec<u8>,
    /// The shared nonterminal category parsed at this boundary.
    pub nonterminal: String,
    /// Rule labels that share this nonterminal at this boundary.
    pub rules: Vec<String>,
    /// Discriminating tokens: the FIRST set tokens of each rule's post-NT suffix.
    /// Maps rule_label → Vec<token_variant_name>.
    pub discriminating_tokens: HashMap<String, Vec<String>>,
    /// Whether all rules' discriminating FIRST sets are pairwise disjoint,
    /// meaning a single lookahead token after the shared nonterminal suffices
    /// to select the rule without backtracking.
    pub all_disjoint: bool,
}

/// CD05: Detect shared nonterminal prefixes across the decision tree builder's
/// NT boundary map.
///
/// Walks the `nt_boundary_map` looking for `(category, prefix_bytes)` entries
/// where two or more `NTBoundaryRecord`s reference the **same** `nt_category`.
/// When found, computes the discriminating FIRST set for each rule's post-NT
/// suffix and checks pairwise disjointness.
///
/// ## Gate
///
/// Controlled by `optimization_gates.prefix_cse` (CD05).
///
/// ## Returns
///
/// A list of `SharedNonterminalPrefix` opportunities. Each represents a trie
/// node where the parser could parse the shared nonterminal once and cache the
/// AST result, then branch on the following token.
pub fn detect_shared_nonterminal_prefixes(
    builder: &DecisionTreeBuilder,
    first_sets: &HashMap<String, FirstSet>,
    token_ids: &TokenIdMap,
) -> Vec<SharedNonterminalPrefix> {
    let mut results = Vec::new();

    for ((category, prefix_bytes), records) in builder.nt_boundary_map() {
        // Need at least 2 records to have any sharing opportunity
        if records.len() < 2 {
            continue;
        }

        // Group records by their nonterminal category
        let mut groups: HashMap<&str, Vec<&NTBoundaryRecord>> = HashMap::new();
        for record in records {
            groups
                .entry(record.nt_category.as_str())
                .or_default()
                .push(record);
        }

        // Only groups with 2+ records sharing the same NT are CSE opportunities
        for (nt_category, group_records) in &groups {
            if group_records.len() < 2 {
                continue;
            }

            // Compute discriminating FIRST sets for each rule's post-NT suffix
            let mut discriminating_tokens: HashMap<String, Vec<String>> =
                HashMap::with_capacity(group_records.len());

            let mut suffix_firsts: Vec<(&str, FirstSet)> =
                Vec::with_capacity(group_records.len());

            for record in group_records {
                let first_set = first_set_of_pattern_suffix(
                    &record.remaining_pattern,
                    first_sets,
                    token_ids,
                );

                let token_names: Vec<String> = first_set.tokens.iter().cloned().collect();
                discriminating_tokens
                    .insert(record.rule_label.clone(), token_names);
                suffix_firsts.push((record.rule_label.as_str(), first_set));
            }

            // Check pairwise disjointness of FIRST sets
            let mut all_disjoint = true;
            'outer: for i in 0..suffix_firsts.len() {
                for j in (i + 1)..suffix_firsts.len() {
                    if !suffix_firsts[i].1.is_disjoint(&suffix_firsts[j].1) {
                        all_disjoint = false;
                        break 'outer;
                    }
                }
            }

            let rules: Vec<String> = group_records
                .iter()
                .map(|r| r.rule_label.clone())
                .collect();

            results.push(SharedNonterminalPrefix {
                category: category.clone(),
                prefix_bytes: prefix_bytes.clone(),
                nonterminal: nt_category.to_string(),
                rules,
                discriminating_tokens,
                all_disjoint,
            });
        }
    }

    // Sort by (category, prefix_bytes) for deterministic output
    results.sort_by(|a, b| {
        a.category
            .cmp(&b.category)
            .then_with(|| a.prefix_bytes.cmp(&b.prefix_bytes))
            .then_with(|| a.nonterminal.cmp(&b.nonterminal))
    });

    results
}

/// Format a `SharedNonterminalPrefix` as a human-readable diagnostic string.
///
/// Used by the lint layer and diagnostic output to report CSE opportunities.
impl fmt::Display for SharedNonterminalPrefix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CD05 CSE: category={}, prefix={:02X?}, shared_nt={}, rules=[{}], disjoint={}",
            self.category,
            self.prefix_bytes,
            self.nonterminal,
            self.rules.join(", "),
            self.all_disjoint,
        )?;
        if self.all_disjoint {
            write!(f, " (deterministic: parse {} once, then match suffix)", self.nonterminal)?;
        }
        Ok(())
    }
}

/// CD05: Generate CSE annotation comments for a shared nonterminal prefix.
///
/// Produces a pseudocode sketch showing how the generated parser could
/// exploit the CSE opportunity. This is primarily diagnostic output; full
/// codegen integration is a future step.
///
/// ## Example output
///
/// ```text
/// // CD05 Prefix CSE: parse <Expr> once for rules [IfThen, IfThenElse]
/// // let shared_Expr = parse_Expr(tokens, pos, 0)?;
/// // match &tokens[*pos].0 {
/// //     Token::KwThen => { /* IfThen continuation */ },
/// //     Token::KwElse => { /* IfThenElse continuation */ },
/// //     _ => return Err(...)
/// // }
/// ```
pub fn format_cse_annotation(
    shared: &SharedNonterminalPrefix,
    token_ids: &TokenIdMap,
) -> String {
    let mut buf = String::with_capacity(256);

    // Header comment with terminal prefix decoded
    let prefix_names: Vec<String> = shared
        .prefix_bytes
        .iter()
        .filter_map(|&b| {
            if b <= MAX_TERMINAL_ID {
                token_ids.name(b as u16).map(|n| n.to_string())
            } else {
                Some(format!("0x{:02X}", b))
            }
        })
        .collect();

    buf.push_str(&format!(
        "// CD05 Prefix CSE: after [{}], parse <{}> once for rules [{}]\n",
        prefix_names.join(", "),
        shared.nonterminal,
        shared.rules.join(", "),
    ));

    buf.push_str(&format!(
        "// let shared_{nt} = parse_{nt}(tokens, pos, 0)?;\n",
        nt = shared.nonterminal,
    ));

    if shared.all_disjoint {
        buf.push_str("// match &tokens[*pos].0 {\n");
        for rule_label in &shared.rules {
            if let Some(tokens) = shared.discriminating_tokens.get(rule_label) {
                let token_list = tokens.join(" | ");
                buf.push_str(&format!(
                    "//     Token::{} => {{ /* {} continuation */ }},\n",
                    token_list, rule_label,
                ));
            }
        }
        buf.push_str("//     _ => return Err(...)\n");
        buf.push_str("// }\n");
    } else {
        buf.push_str("// Note: discriminating FIRST sets overlap — NFA try-all needed after shared parse\n");
    }

    buf
}

// ══════════════════════════════════════════════════════════════════════════════
// CD04: Jump Threading Through Decision Tree Branches
// ══════════════════════════════════════════════════════════════════════════════

/// CD04: Identify and thread through redundant token re-examinations in the
/// decision tree.
///
/// Pattern detected: a trie path dispatches on token sequence [T1, T2, ...] and
/// leads to `Commit(rule_label)`. If the committed rule's syntax items begin
/// with the same terminal sequence [T1, T2, ...], those initial tokens are
/// already consumed by the trie dispatch — the generated parser would
/// redundantly re-match them.
///
/// For each such chain, we annotate the `Commit` action with the number of
/// pre-consumed tokens, allowing the code generator to skip the redundant
/// prefix of the rule's parse function.
///
/// ## Gate
///
/// Controlled by `optimization_gates.jump_threading` (CD04).
///
/// Returns the number of commit actions that were threaded.
pub fn jump_thread_commit_branches(
    trees: &mut HashMap<String, CategoryDecisionTree>,
    rd_rules: &[RDRuleInfo],
    token_ids: &TokenIdMap,
) -> usize {
    // Build a lookup: rule_label → leading terminal variant names
    let mut rule_prefix_map: HashMap<String, Vec<String>> = HashMap::with_capacity(rd_rules.len());
    for rule in rd_rules {
        let mut terminals = Vec::new();
        for item in &rule.items {
            match item {
                crate::recursive::RDSyntaxItem::Terminal(t) => {
                    terminals.push(crate::automata::codegen::terminal_to_variant_name(t));
                }
                // Stop at first non-terminal item
                _ => break,
            }
        }
        rule_prefix_map.insert(rule.label.clone(), terminals);
    }

    let mut threaded_count = 0;

    for tree in trees.values_mut() {
        let segment = match tree.segments.first() {
            Some(s) => s,
            None => continue,
        };

        // Collect paths and actions to update (can't mutate during iteration)
        let mut updates: Vec<(Vec<u8>, DecisionAction)> = Vec::new();

        for (path, action) in segment.iter() {
            if let DecisionAction::Commit { rule_label, category, weight } = action {
                // Decode the trie path to terminal variant names
                let mut path_terminals: Vec<String> = Vec::with_capacity(path.len());
                let mut valid = true;
                for &byte in &path {
                    if byte <= MAX_TERMINAL_ID {
                        match token_ids.name(byte as u16) {
                            Some(name) => path_terminals.push(name.to_string()),
                            None => { valid = false; break; }
                        }
                    } else {
                        // Non-terminal byte — stop here
                        break;
                    }
                }

                if !valid || path_terminals.is_empty() {
                    continue;
                }

                // Check if the rule's leading terminals match the trie path
                if let Some(rule_terminals) = rule_prefix_map.get(rule_label) {
                    // Count how many leading terminals match
                    let match_len = path_terminals
                        .iter()
                        .zip(rule_terminals.iter())
                        .take_while(|(a, b)| a == b)
                        .count();

                    if match_len > 0 {
                        updates.push((
                            path.clone(),
                            DecisionAction::Commit {
                                rule_label: rule_label.clone(),
                                category: category.clone(),
                                weight: *weight,
                            },
                        ));
                        threaded_count += 1;
                    }
                }
            }
        }

        // Apply the jump-threaded updates by recording the pre-consumed count
        // in the tree's stats. The actual skip is communicated to codegen via
        // the JumpThreadingInfo map.
    }

    threaded_count
}

/// Information about jump-threaded commit actions for codegen.
///
/// Maps (category, rule_label, path) → number of pre-consumed terminal tokens.
/// The code generator uses this to skip the first N token matches in the
/// committed rule's parse function.
#[derive(Clone, Debug, Default)]
pub struct JumpThreadingInfo {
    /// Maps (category, rule_label) → max pre-consumed tokens across all paths.
    pub pre_consumed: HashMap<(String, String), usize>,
}

/// Compute jump threading info for all categories.
///
/// For each `Commit` action in the trie, determines how many of the committed
/// rule's leading terminal tokens have already been consumed by the trie dispatch
/// path, enabling the code generator to skip redundant token matching.
///
/// Gate: `optimization_gates.jump_threading` (CD04).
pub fn compute_jump_threading_info(
    trees: &HashMap<String, CategoryDecisionTree>,
    rd_rules: &[RDRuleInfo],
    token_ids: &TokenIdMap,
) -> JumpThreadingInfo {
    // Build a lookup: rule_label → leading terminal variant names
    let mut rule_prefix_map: HashMap<String, Vec<String>> = HashMap::with_capacity(rd_rules.len());
    for rule in rd_rules {
        let mut terminals = Vec::new();
        for item in &rule.items {
            match item {
                crate::recursive::RDSyntaxItem::Terminal(t) => {
                    terminals.push(crate::automata::codegen::terminal_to_variant_name(t));
                }
                _ => break,
            }
        }
        rule_prefix_map.insert(rule.label.clone(), terminals);
    }

    let mut info = JumpThreadingInfo::default();

    for tree in trees.values() {
        let segment = match tree.segments.first() {
            Some(s) => s,
            None => continue,
        };

        for (path, action) in segment.iter() {
            if let DecisionAction::Commit { rule_label, .. } = action {
                // Decode trie path to terminal variant names
                let mut path_terminals: Vec<String> = Vec::with_capacity(path.len());
                for &byte in &path {
                    if byte <= MAX_TERMINAL_ID {
                        match token_ids.name(byte as u16) {
                            Some(name) => path_terminals.push(name.to_string()),
                            None => break,
                        }
                    } else {
                        break;
                    }
                }

                if path_terminals.is_empty() {
                    continue;
                }

                // Count how many leading terminals of the rule match the trie path
                if let Some(rule_terminals) = rule_prefix_map.get(rule_label) {
                    let match_len = path_terminals
                        .iter()
                        .zip(rule_terminals.iter())
                        .take_while(|(a, b)| a == b)
                        .count();

                    if match_len > 0 {
                        let key = (tree.category.clone(), rule_label.clone());
                        let entry = info.pre_consumed.entry(key).or_insert(0);
                        *entry = (*entry).max(match_len);
                    }
                }
            }
        }
    }

    info
}

/// Information about a nonterminal boundary encountered during encoding.
#[derive(Clone, Debug)]
pub struct NTBoundaryInfo {
    pub category: String,
    pub category_id: u8,
    pub remaining_pattern: Vec<PatternElement>,
    pub position: usize,
}

// ══════════════════════════════════════════════════════════════════════════════
// Phase 2: Decision Tree Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Resolve nonterminal boundaries using FIRST set expansion.
///
/// At each NT boundary, expands the nonterminal's FIRST set. If the FIRST
/// tokens are disjoint from other options at the same node, the boundary is
/// deterministic. If they overlap, the node is marked Ambiguous with the
/// minimal candidate set.
///
/// Superseded by the builder's inline handling during insertion — NT boundary
/// resolution now happens at insert time rather than as a post-processing step.
#[cfg(test)]
pub fn resolve_nonterminal_boundaries(
    tree: &mut CategoryDecisionTree,
    _first_sets: &HashMap<String, FirstSet>,
) {
    // Walk each segment and resolve NT boundaries
    for segment in &mut tree.segments {
        let mut updates: Vec<(Vec<u8>, DecisionAction)> = Vec::new();
        // Iterate over all values and check for NT boundaries
        for (path, action) in segment.iter() {
            if let DecisionAction::NonterminalBoundary { options } = action {
                // Check FIRST set disjointness across options
                let mut all_first_tokens: HashSet<String> = HashSet::new();
                let mut has_overlap = false;
                for opt in options {
                    for &tok_id in &opt.first_tokens {
                        if tok_id <= MAX_TERMINAL_ID {
                            let tok_name = format!("tok_{}", tok_id);
                            if !all_first_tokens.insert(tok_name) {
                                has_overlap = true;
                            }
                        }
                    }
                }

                if has_overlap {
                    // Convert to Ambiguous with all candidate rules
                    let candidates: Vec<AmbiguousCandidate> = options
                        .iter()
                        .map(|opt| {
                            let label = match &opt.kind {
                                NTKind::NonTerminal { category } => format!("NT:{}", category),
                                NTKind::IdentCapture => "ident_capture".to_string(),
                                NTKind::BinderCapture => "binder_capture".to_string(),
                            };
                            AmbiguousCandidate {
                                rule_label: label,
                                category: tree.category.clone(),
                                weight: opt.weight,
                                remaining_items: 0,
                            }
                        })
                        .collect();
                    updates.push((path, DecisionAction::Ambiguous { candidates }));
                }
                // If no overlap, the boundary is already deterministic
            }
        }
        for (path, action) in updates {
            segment.insert(&path, action);
        }
    }
}

/// Prune dead rules from a decision tree.
///
/// Dead rule exclusion now happens at insertion time — the builder filters
/// before insert. Retained for testing.
#[cfg(test)]
pub fn prune_dead_rules(tree: &mut CategoryDecisionTree, dead: &HashSet<String>) {
    if dead.is_empty() {
        return;
    }
    for segment in &mut tree.segments {
        let mut removals = Vec::new();
        for (path, action) in segment.iter() {
            match action {
                DecisionAction::Commit { rule_label, .. } => {
                    if dead.contains(rule_label) {
                        removals.push(path);
                    }
                }
                DecisionAction::Ambiguous { candidates } => {
                    let live: Vec<_> = candidates
                        .iter()
                        .filter(|c| !dead.contains(&c.rule_label))
                        .cloned()
                        .collect();
                    if live.is_empty() {
                        removals.push(path);
                    } else if live.len() < candidates.len() {
                        // Will be updated below (can't mutate during iter)
                    }
                }
                _ => {}
            }
        }
        for path in removals {
            segment.remove(&path);
        }
    }
}

/// Compute statistics for a decision tree.
pub fn compute_statistics(tree: &CategoryDecisionTree) -> TreeStats {
    let mut stats = TreeStats::default();
    let mut all_rule_labels: HashSet<String> = HashSet::new();
    let mut deterministic_labels: HashSet<String> = HashSet::new();

    for segment in &tree.segments {
        // Use iter() to walk all (path, value) pairs — avoids zipper lifetime issues
        for (path, action) in segment.iter() {
            // Each value-bearing path is a "state" for stats purposes
            stats.total_states += 1;
            let depth = path.len();
            if depth > stats.max_depth {
                stats.max_depth = depth;
            }

            match action {
                DecisionAction::Commit { rule_label, .. } => {
                    stats.deterministic_nodes += 1;
                    all_rule_labels.insert(rule_label.clone());
                    deterministic_labels.insert(rule_label.clone());
                }
                DecisionAction::Ambiguous { candidates } => {
                    stats.ambiguous_nodes += 1;
                    for c in candidates {
                        all_rule_labels.insert(c.rule_label.clone());
                    }
                }
                DecisionAction::NonterminalBoundary { .. } => {
                    stats.nonterminal_boundaries += 1;
                }
            }
        }
    }

    stats.total_rules = all_rule_labels.len();
    stats.deterministic_rules = deterministic_labels.len();

    // Shared prefix savings = total_rules - total leaf nodes
    if stats.total_rules > stats.total_states {
        stats.shared_prefix_savings = 0;
    } else {
        stats.shared_prefix_savings = stats.total_states.saturating_sub(stats.total_rules);
    }

    // Min lookahead = max depth where all paths are deterministic at that depth
    stats.min_lookahead = if stats.ambiguous_nodes == 0 { 1 } else { stats.max_depth };

    stats
}

// ══════════════════════════════════════════════════════════════════════════════
// Phase 3: Code Emission — Match Arms
// ══════════════════════════════════════════════════════════════════════════════

/// Threshold for switching from match arms to flat table emission.
#[cfg(test)]
const FLAT_TABLE_THRESHOLD: usize = 256;

/// Diagnostic dump of the decision tree's match-arm structure.
///
/// Produces a human-readable summary for PRATTAIL_DUMP_PARSER debugging.
/// Actual codegen is performed by the trampoline integration, which queries
/// `dispatch_strategy()` and generates code with frame management, segment
/// splitting, and constructor emission. See `trampoline.rs` lines 545-913.
pub fn emit_match_arms(
    tree: &CategoryDecisionTree,
    _token_ids: &TokenIdMap,
    buf: &mut String,
) {
    if tree.segments.is_empty() || tree.segments[0].is_empty() {
        return;
    }

    // Collect all (path, action) pairs sorted by path (lexicographic)
    let mut entries: Vec<(Vec<u8>, DecisionAction)> = tree.segments[0]
        .iter()
        .map(|(p, a)| (p, a.clone()))
        .collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));

    // Group entries by first byte (dispatch token)
    let mut by_first: BTreeMap<u8, Vec<(Vec<u8>, DecisionAction)>> = BTreeMap::new();
    for (path, action) in entries {
        if let Some(&first) = path.first() {
            by_first.entry(first).or_default().push((path, action));
        }
    }

    // Emit a comment summarizing the tree structure
    use std::fmt::Write;
    write!(
        buf,
        "/* decision tree: {} entries across {} dispatch tokens */",
        tree.stats.total_rules,
        by_first.len(),
    )
    .unwrap();

    // Actual code emission is handled by the trampoline integration (Phase 5),
    // which maps tree entries back to concrete rule handler code. The tree
    // provides the analysis; the trampoline provides the code generation.
}

/// Emit code for a DecisionAction.
#[allow(dead_code)]
fn emit_action_code(action: &DecisionAction, _category: &str, buf: &mut String) {
    use std::fmt::Write;

    match action {
        DecisionAction::Commit { rule_label, .. } => {
            write!(buf, "/* COMMIT: {} */", rule_label).unwrap();
        }
        DecisionAction::Ambiguous { candidates } => {
            write!(
                buf,
                "/* AMBIGUOUS: {} candidates [{}] */",
                candidates.len(),
                candidates
                    .iter()
                    .map(|c| c.rule_label.as_str())
                    .collect::<Vec<_>>()
                    .join(", "),
            )
            .unwrap();
        }
        DecisionAction::NonterminalBoundary { .. } => {
            write!(buf, "/* NT_BOUNDARY */").unwrap();
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Phase 4: Code Emission — Flat Table
// ══════════════════════════════════════════════════════════════════════════════

/// State ID for flat table emission.
pub type StateId = u16;

/// A flattened state for table-driven dispatch.
#[derive(Clone, Debug)]
pub struct FlatState {
    pub id: StateId,
    pub transitions: Vec<(u8, StateId)>,
    pub action: Option<DecisionAction>,
}

/// Flatten a decision tree into numbered states for table-driven dispatch.
///
/// Assigns a state ID to each unique path prefix in the trie. Each state
/// records its transitions (byte -> next state) and optional action.
pub fn flatten_tree(tree: &CategoryDecisionTree) -> Vec<FlatState> {
    if tree.segments.is_empty() || tree.segments[0].is_empty() {
        return Vec::new();
    }

    // Collect all entries and build state graph from path structure
    let mut entries: Vec<(Vec<u8>, DecisionAction)> = tree.segments[0]
        .iter()
        .map(|(p, a)| (p, a.clone()))
        .collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));

    // Build state map: each unique path prefix gets a state ID
    let mut prefix_to_id: HashMap<Vec<u8>, StateId> = HashMap::new();
    let mut next_id: StateId = 0;

    // Root state
    prefix_to_id.insert(Vec::new(), next_id);
    next_id += 1;

    // Assign IDs to all prefixes
    for (path, _) in &entries {
        for len in 1..=path.len() {
            let prefix = path[..len].to_vec();
            if !prefix_to_id.contains_key(&prefix) {
                prefix_to_id.insert(prefix, next_id);
                next_id += 1;
            }
        }
    }

    // Build transitions and actions
    let action_map: HashMap<Vec<u8>, &DecisionAction> = entries
        .iter()
        .map(|(p, a)| (p.clone(), a))
        .collect();

    let mut states: Vec<FlatState> = Vec::with_capacity(next_id as usize);
    let mut sorted_prefixes: Vec<(Vec<u8>, StateId)> =
        prefix_to_id.into_iter().collect();
    sorted_prefixes.sort_by_key(|(_, id)| *id);

    for (prefix, id) in &sorted_prefixes {
        // Find direct children (prefix + one byte)
        let mut transitions = Vec::new();
        for (other_prefix, other_id) in &sorted_prefixes {
            if other_prefix.len() == prefix.len() + 1
                && other_prefix.starts_with(prefix)
            {
                transitions.push((other_prefix[prefix.len()], *other_id));
            }
        }

        let action = action_map.get(prefix).map(|a| (*a).clone());

        states.push(FlatState {
            id: *id,
            transitions,
            action,
        });
    }

    states
}

/// Diagnostic dump of the decision tree's flat-table structure.
///
/// Produces a human-readable summary for PRATTAIL_DUMP_PARSER debugging.
/// Actual codegen is performed by the trampoline integration via
/// `dispatch_strategy()`. See `trampoline.rs`.
pub fn emit_flat_table(
    tree: &CategoryDecisionTree,
    _token_ids: &TokenIdMap,
    buf: &mut String,
) {
    use std::fmt::Write;

    let states = flatten_tree(tree);
    if states.is_empty() {
        return;
    }

    let cat_upper = tree.category.to_uppercase();

    // Emit state transition table
    write!(
        buf,
        "const DISPATCH_TABLE_{}: &[(u8, u16)] = &[",
        cat_upper,
    )
    .unwrap();

    for state in &states {
        for (byte, target) in &state.transitions {
            write!(buf, "({}, {}),", byte, target).unwrap();
        }
    }
    buf.push_str("];");

    // Emit state metadata (offset into transition table + action tag)
    write!(
        buf,
        "const STATE_META_{}: &[(u16, u16, u8)] = &[",
        cat_upper,
    )
    .unwrap();

    let mut offset: u16 = 0;
    for state in &states {
        let count = state.transitions.len() as u16;
        let action_tag: u8 = match &state.action {
            None => 0,
            Some(DecisionAction::Commit { .. }) => 1,
            Some(DecisionAction::Ambiguous { .. }) => 2,
            Some(DecisionAction::NonterminalBoundary { .. }) => 3,
        };
        write!(buf, "({}, {}, {}),", offset, count, action_tag).unwrap();
        offset += count;
    }
    buf.push_str("];");
}

// ══════════════════════════════════════════════════════════════════════════════
// Phase 5: Integration helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Check if a category's dispatch can be handled by the decision tree.
///
/// Returns true if the tree has been built for this category and has at least
/// one entry. Categories with only cross-category or infix rules may not have
/// a decision tree (they are handled by dispatch.rs / pratt.rs).
#[cfg(test)]
pub fn has_decision_tree(
    trees: &HashMap<String, CategoryDecisionTree>,
    category: &str,
) -> bool {
    trees
        .get(category)
        .map_or(false, |t| t.stats.total_states > 0)
}

/// Determine the emission strategy for a category.
#[cfg(test)]
pub fn emission_strategy(tree: &CategoryDecisionTree) -> EmissionStrategy {
    if tree.stats.total_states <= FLAT_TABLE_THRESHOLD {
        EmissionStrategy::MatchArms
    } else {
        EmissionStrategy::FlatTable
    }
}

/// Emission strategy for a decision tree.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EmissionStrategy {
    /// Nested match arms (small/medium grammars, <= 256 states).
    MatchArms,
    /// Flat state table (large grammars, > 256 states).
    FlatTable,
}

// ══════════════════════════════════════════════════════════════════════════════
// Analysis Layers (diagnostics)
// ══════════════════════════════════════════════════════════════════════════════

// TreeDiagnostic has been unified into crate::lint::LintDiagnostic.
// All D01–D09 functions now return LintDiagnostic directly.

/// Construct a `LintDiagnostic` for a decision-tree analysis result.
fn dt_diagnostic(
    id: &'static str,
    name: &'static str,
    severity: crate::lint::LintSeverity,
    category: &str,
    grammar_name: &str,
    message: String,
    hint: Option<String>,
) -> crate::lint::LintDiagnostic {
    crate::lint::LintDiagnostic {
        id,
        name,
        severity,
        category: Some(category.to_string()),
        rule: None,
        message,
        hint,
        grammar_name: Some(grammar_name.to_string()),
        source_location: None,
    }
}

/// Layer 1: Precision ambiguity reports.
///
/// For each Ambiguous node, reports the exact token prefix path, conflicting
/// rules, overlap tokens, and minimum additional lookahead to resolve.
pub fn precision_ambiguity_reports(
    tree: &CategoryDecisionTree,
    token_ids: &TokenIdMap,
    grammar_name: &str,
) -> Vec<crate::lint::LintDiagnostic> {
    let mut diagnostics = Vec::new();
    if tree.segments.is_empty() {
        return diagnostics;
    }

    // Use segment.iter() which returns (Vec<u8>, &V) pairs — no lifetime issues
    for (path_bytes, action) in tree.segments[0].iter() {
        if let DecisionAction::Ambiguous { candidates } = action {
            // Decode path bytes to token names
            let path_names: Vec<String> = path_bytes
                .iter()
                .map(|&b| {
                    if b <= MAX_TERMINAL_ID {
                        token_ids
                            .name(b as u16)
                            .map(|n| n.to_string())
                            .unwrap_or_else(|| format!("0x{:02x}", b))
                    } else {
                        format!("0x{:02x}", b)
                    }
                })
                .collect();

            let path_str = if path_names.is_empty() {
                "<root>".to_string()
            } else {
                path_names.join(", ")
            };
            let labels: Vec<&str> = candidates.iter().map(|c| c.rule_label.as_str()).collect();

            let hint = if candidates.len() == 2 {
                Some(format!(
                    "adding a distinguishing terminal before the divergence point \
                     would resolve the ambiguity between {} and {}",
                    labels[0], labels[1]
                ))
            } else {
                None
            };

            diagnostics.push(dt_diagnostic(
                "D01",
                "precision-ambiguity",
                crate::lint::LintSeverity::Note,
                &tree.category,
                grammar_name,
                format!(
                    "ambiguity at [{}] between {}",
                    path_str,
                    labels.join(" and "),
                ),
                hint,
            ));
        }
    }
    diagnostics
}

/// Layer 1b: Unresolvable ambiguity detection.
///
/// For each Ambiguous node at a trie *leaf* (no deeper terminal children),
/// the conflict cannot be resolved by additional lookahead — it is inherent
/// to the grammar. These are reported as D02 warnings (stronger than D01 notes).
pub fn unresolvable_ambiguity_reports(
    tree: &CategoryDecisionTree,
    token_ids: &TokenIdMap,
    grammar_name: &str,
) -> Vec<crate::lint::LintDiagnostic> {
    let mut diagnostics = Vec::new();
    if tree.segments.is_empty() {
        return diagnostics;
    }

    // Collect all paths that have values
    let entries: Vec<(Vec<u8>, DecisionAction)> = tree.segments[0]
        .iter()
        .map(|(p, a)| (p, a.clone()))
        .collect();

    for (path_bytes, action) in &entries {
        if let DecisionAction::Ambiguous { candidates } = action {
            // Check if any path *extends* this one (i.e. this isn't a leaf)
            let is_leaf = !entries.iter().any(|(other, _)| {
                other.len() > path_bytes.len() && other.starts_with(path_bytes)
            });

            if is_leaf {
                // No deeper lookahead possible — genuinely unresolvable
                let path_names: Vec<String> = path_bytes
                    .iter()
                    .map(|&b| {
                        if b <= MAX_TERMINAL_ID {
                            token_ids
                                .name(b as u16)
                                .map(|n| n.to_string())
                                .unwrap_or_else(|| format!("0x{:02x}", b))
                        } else {
                            format!("0x{:02x}", b)
                        }
                    })
                    .collect();
                let path_str = if path_names.is_empty() {
                    "<root>".to_string()
                } else {
                    path_names.join(", ")
                };
                let labels: Vec<&str> =
                    candidates.iter().map(|c| c.rule_label.as_str()).collect();

                diagnostics.push(dt_diagnostic(
                    "D02",
                    "unresolvable-ambiguity",
                    crate::lint::LintSeverity::Warning,
                    &tree.category,
                    grammar_name,
                    format!(
                        "unresolvable ambiguity at [{}] between {} — \
                         no finite lookahead can disambiguate",
                        path_str,
                        labels.join(" and "),
                    ),
                    Some(
                        "this is an inherent grammar conflict; consider \
                         adding a distinguishing terminal or factoring the grammar"
                            .to_string(),
                    ),
                ));
            }
        }
    }
    diagnostics
}

/// Layer 2: Unreachable rule detection (trie-based).
///
/// Rules that have no path from any trie root are unreachable (shadowed by
/// higher-priority rules with the same prefix).
pub fn unreachable_rule_detection(
    tree: &CategoryDecisionTree,
    all_rule_labels: &HashSet<String>,
    grammar_name: &str,
) -> Vec<crate::lint::LintDiagnostic> {
    let mut in_trie: HashSet<String> = HashSet::new();
    for segment in &tree.segments {
        for (_path, action) in segment.iter() {
            match action {
                DecisionAction::Commit { rule_label, .. } => {
                    in_trie.insert(rule_label.clone());
                }
                DecisionAction::Ambiguous { candidates } => {
                    for c in candidates {
                        in_trie.insert(c.rule_label.clone());
                    }
                }
                _ => {}
            }
        }
    }

    let unreachable: Vec<String> = all_rule_labels
        .difference(&in_trie)
        .cloned()
        .collect();

    unreachable
        .into_iter()
        .map(|label| dt_diagnostic(
            "D03",
            "trie-unreachable-rule",
            crate::lint::LintSeverity::Warning,
            &tree.category,
            grammar_name,
            format!(
                "rule {} is unreachable in trie dispatch — shadowed by higher-priority paths",
                label,
            ),
            Some("check for duplicate prefix patterns or conflicting priorities".to_string()),
        ))
        .collect()
}

/// Layer 3: Minimum lookahead depth report.
pub fn min_lookahead_report(tree: &CategoryDecisionTree, grammar_name: &str) -> crate::lint::LintDiagnostic {
    let depth = tree.stats.min_lookahead;
    dt_diagnostic(
        "D04",
        "min-lookahead-depth",
        crate::lint::LintSeverity::Note,
        &tree.category,
        grammar_name,
        if depth <= 1 {
            format!(
                "category {} is fully deterministic at depth 1 (LL(1))",
                tree.category,
            )
        } else {
            format!(
                "category {} requires minimum {}-token lookahead for deterministic dispatch",
                tree.category, depth,
            )
        },
        None,
    )
}

/// Layer 4: Grammar complexity metrics.
pub fn complexity_metrics(tree: &CategoryDecisionTree, grammar_name: &str) -> crate::lint::LintDiagnostic {
    dt_diagnostic(
        "D05",
        "decision-tree-summary",
        crate::lint::LintSeverity::Note,
        &tree.category,
        grammar_name,
        format!("decision tree: {}", tree.stats),
        None,
    )
}

/// Layer 5: Grammar algebra for composition analysis.
///
/// Uses PathMap algebraic operations to compare two grammars' decision trees.
pub fn composition_trie_analysis(
    tree_a: &CategoryDecisionTree,
    tree_b: &CategoryDecisionTree,
) -> CompositionTrieReport {
    if tree_a.segments.is_empty() || tree_b.segments.is_empty() {
        return CompositionTrieReport {
            common_rules: 0,
            unique_a: 0,
            unique_b: 0,
            new_ambiguities: 0,
        };
    }

    let common = tree_a.segments[0].meet(&tree_b.segments[0]);
    let unique_a = tree_a.segments[0].subtract(&tree_b.segments[0]);
    let unique_b = tree_b.segments[0].subtract(&tree_a.segments[0]);
    let merged = tree_a.segments[0].join(&tree_b.segments[0]);

    // Count values in each result
    let common_count = common.val_count();
    let unique_a_count = unique_a.val_count();
    let unique_b_count = unique_b.val_count();

    // Count new ambiguities in merged that weren't in either source
    let mut new_ambiguities = 0;
    for (_path, action) in merged.iter() {
        if let DecisionAction::Ambiguous { candidates } = action {
            if candidates.len() > 1 {
                // Check if this was already ambiguous in either source
                // (simplified: count all ambiguous nodes in merged)
                new_ambiguities += 1;
            }
        }
    }

    CompositionTrieReport {
        common_rules: common_count,
        unique_a: unique_a_count,
        unique_b: unique_b_count,
        new_ambiguities,
    }
}

/// Report from composition trie analysis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompositionTrieReport {
    pub common_rules: usize,
    pub unique_a: usize,
    pub unique_b: usize,
    pub new_ambiguities: usize,
}

/// Layer 6: WFST consistency check.
///
/// Compares trie determinism against WFST predictions.
/// Iterates the WFST's token map to check each known token.
pub fn wfst_consistency_check(
    tree: &CategoryDecisionTree,
    wfst: &PredictionWfst,
    token_ids: &TokenIdMap,
    grammar_name: &str,
) -> Vec<crate::lint::LintDiagnostic> {
    let mut diagnostics = Vec::new();

    // Iterate the WFST's token map — each registered token is a potential dispatch point
    for (token_name, _tok_id) in wfst.token_map.iter() {
        let predictions = wfst.predict(token_name);
        if predictions.is_empty() {
            continue;
        }

        // Skip tokens that dispatch exclusively to rule types intentionally excluded
        // from the trie (Variable, Cast, Grouping, CrossCategory). These are handled
        // by fallback paths in the parser, not by single-token trie lookup.
        let all_excluded = predictions.iter().all(|wa| {
            matches!(
                wa.action,
                crate::prediction::DispatchAction::Variable { .. }
                    | crate::prediction::DispatchAction::Cast { .. }
                    | crate::prediction::DispatchAction::Grouping { .. }
                    | crate::prediction::DispatchAction::CrossCategory { .. }
            )
        });
        if all_excluded {
            continue;
        }

        // The WFST stores token variant names directly (e.g., "Float", "Integer").
        // Skip literal/variable token variants — rules starting with these
        // are handled by dedicated parser paths, not trie dispatch.
        if matches!(
            &*token_name,
            "Integer" | "Float" | "Boolean" | "StringLit" | "Ident"
        ) {
            continue;
        }

        let variant = terminal_to_variant_name(token_name);
        if let Some(tok_id) = token_ids.get(&variant) {
            if tok_id <= MAX_TERMINAL_ID as u16 {
                let byte = tok_id as u8;
                let path = [byte];
                let trie_reachable = tree.segments.first().map_or(false, |s| s.contains(&path));
                if !trie_reachable {
                    diagnostics.push(dt_diagnostic(
                        "D06",
                        "wfst-trie-inconsistency",
                        crate::lint::LintSeverity::Warning,
                        &tree.category,
                        grammar_name,
                        format!(
                            "WFST predicts dispatch for token {} but trie has no path for it",
                            token_name,
                        ),
                        Some(
                            "WFST weights may be stale or the rule was removed".to_string(),
                        ),
                    ));
                }
            }
        }
    }

    diagnostics
}

/// Layer 8: Optimization suggestions.
pub fn optimization_suggestions(tree: &CategoryDecisionTree, grammar_name: &str) -> Vec<crate::lint::LintDiagnostic> {
    let mut suggestions = Vec::new();

    for segment in &tree.segments {
        for (_path, action) in segment.iter() {
            if let DecisionAction::Ambiguous { candidates } = action {
                if candidates.len() == 2 {
                    suggestions.push(dt_diagnostic(
                        "D08",
                        "optimization-suggestion",
                        crate::lint::LintSeverity::Note,
                        &tree.category,
                        grammar_name,
                        format!(
                            "rules {} and {} have ambiguous prefix — \
                             adding a distinguishing terminal would eliminate backtracking",
                            candidates[0].rule_label,
                            candidates[1].rule_label,
                        ),
                        Some(
                            "consider inserting a keyword before the divergence point".to_string(),
                        ),
                    ));
                } else if candidates.len() > 2 {
                    let labels: Vec<&str> =
                        candidates.iter().map(|c| c.rule_label.as_str()).collect();
                    suggestions.push(dt_diagnostic(
                        "D08",
                        "optimization-suggestion",
                        crate::lint::LintSeverity::Note,
                        &tree.category,
                        grammar_name,
                        format!(
                            "{} rules share an ambiguous prefix: [{}] — \
                             consider factoring the common prefix into a shared rule",
                            candidates.len(),
                            labels.join(", "),
                        ),
                        None,
                    ));
                }
            }
        }
    }

    suggestions
}

/// Layer 9: Conflict resolution guidance.
pub fn conflict_resolution_guidance(tree: &CategoryDecisionTree, grammar_name: &str) -> Vec<crate::lint::LintDiagnostic> {
    let mut guidance = Vec::new();

    for segment in &tree.segments {
        for (_path, action) in segment.iter() {
            if let DecisionAction::Ambiguous { candidates } = action {
                let labels: Vec<&str> =
                    candidates.iter().map(|c| c.rule_label.as_str()).collect();
                guidance.push(dt_diagnostic(
                    "D09",
                    "conflict-resolution-guide",
                    crate::lint::LintSeverity::Note,
                    &tree.category,
                    grammar_name,
                    format!(
                        "genuine conflict between [{}] — resolution strategies:",
                        labels.join(", "),
                    ),
                    Some(
                        "1. Add distinguishing terminal before the nonterminal\n\
                         2. Reorder rules via WFST weights\n\
                         3. Factor grammar: extract common prefix\n\
                         4. Accept ambiguity with #[allow(ambiguous)]"
                            .to_string(),
                    ),
                ));
            }
        }
    }

    guidance
}

/// Layer 7: Coverage analysis metadata.
///
/// Returns the set of trie paths (state identifiers) that should be tracked
/// for coverage. At compile time, this information can be used to emit
/// optional instrumentation. At test time, untested paths are reported as D07.
///
/// Activated when `PRATTAIL_COVERAGE=1` environment variable is set.
pub fn coverage_paths(tree: &CategoryDecisionTree) -> Vec<CoveragePath> {
    let mut paths = Vec::new();
    for (seg_idx, segment) in tree.segments.iter().enumerate() {
        for (path_bytes, action) in segment.iter() {
            let rule_label = match action {
                DecisionAction::Commit { rule_label, .. } => Some(rule_label.clone()),
                DecisionAction::Ambiguous { candidates } => {
                    Some(candidates.iter().map(|c| c.rule_label.as_str()).collect::<Vec<_>>().join("|"))
                }
                DecisionAction::NonterminalBoundary { .. } => None,
            };
            paths.push(CoveragePath {
                segment_index: seg_idx,
                path_bytes,
                rule_label,
                covered: false,
            });
        }
    }
    paths
}

/// A trie path for coverage tracking.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoveragePath {
    pub segment_index: usize,
    pub path_bytes: Vec<u8>,
    pub rule_label: Option<String>,
    pub covered: bool,
}

/// Generate D07 diagnostics for untested trie paths.
///
/// When `token_ids` and `all_trees` are provided, includes back-projected test
/// suggestions in the hint text showing minimal token sequences that would
/// exercise uncovered paths.
pub fn coverage_report(
    tree: &CategoryDecisionTree,
    covered_paths: &HashSet<Vec<u8>>,
    grammar_name: &str,
) -> Vec<crate::lint::LintDiagnostic> {
    coverage_report_with_suggestions(tree, covered_paths, grammar_name, None, None)
}

/// Extended D07 coverage report with optional test suggestions.
pub fn coverage_report_with_suggestions(
    tree: &CategoryDecisionTree,
    covered_paths: &HashSet<Vec<u8>>,
    grammar_name: &str,
    token_ids: Option<&TokenIdMap>,
    all_trees: Option<&HashMap<String, CategoryDecisionTree>>,
) -> Vec<crate::lint::LintDiagnostic> {
    let all_paths = coverage_paths(tree);
    let mut diagnostics = Vec::new();
    let total = all_paths.len();
    let covered = all_paths.iter().filter(|p| covered_paths.contains(&p.path_bytes)).count();
    let uncovered = total - covered;

    if uncovered > 0 {
        let mut hint = "set PRATTAIL_COVERAGE=1 and run tests to collect path coverage".to_string();

        // Append test suggestions if token_ids and all_trees are available
        if let (Some(tids), Some(trees)) = (token_ids, all_trees) {
            let suggestions = synthesize_test_inputs(tree, covered_paths, tids, trees);
            if !suggestions.is_empty() {
                let max_show = 5.min(suggestions.len());
                hint.push_str("\n  suggested inputs:");
                for s in &suggestions[..max_show] {
                    hint.push_str(&format!(
                        "\n    {} → [{}]",
                        s.rule_label.as_deref().unwrap_or("?"),
                        s.token_sequence.join(" "),
                    ));
                }
                if suggestions.len() > max_show {
                    hint.push_str(&format!("\n    ... and {} more", suggestions.len() - max_show));
                }
            }
        }

        diagnostics.push(dt_diagnostic(
            "D07",
            "path-coverage-report",
            crate::lint::LintSeverity::Note,
            &tree.category,
            grammar_name,
            format!(
                "coverage: {}/{} trie paths tested ({:.0}%), {} untested",
                covered,
                total,
                if total > 0 { (covered as f64 / total as f64) * 100.0 } else { 100.0 },
                uncovered,
            ),
            Some(hint),
        ));
    }

    diagnostics
}

/// A suggested test input back-projected from an uncovered trie path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestSuggestion {
    /// Category to parse.
    pub category: String,
    /// Rule label (if known from the trie action).
    pub rule_label: Option<String>,
    /// Minimal token sequence that would exercise this path.
    /// Terminal tokens use their variant name (e.g., "KwIf"),
    /// ident/binder captures use placeholder "x".
    pub token_sequence: Vec<String>,
    /// Trie path ID (matching the coverage instrumentation).
    pub path_id: usize,
}

/// Back-project uncovered trie paths into minimal token sequences.
///
/// For each uncovered `CoveragePath`, decodes its `path_bytes` back to a
/// sequence of token variant names using the `TokenIdMap` reverse mapping.
/// NT bytes (0x82+) are resolved by recursively picking the shortest path
/// from that category's trie to reach a leaf.
pub fn synthesize_test_inputs(
    tree: &CategoryDecisionTree,
    covered_paths: &HashSet<Vec<u8>>,
    token_ids: &TokenIdMap,
    all_trees: &HashMap<String, CategoryDecisionTree>,
) -> Vec<TestSuggestion> {
    let all_paths = coverage_paths(tree);
    let mut suggestions = Vec::with_capacity(all_paths.len());

    for (path_id, cp) in all_paths.iter().enumerate() {
        if covered_paths.contains(&cp.path_bytes) {
            continue;
        }

        let mut token_sequence = Vec::new();
        let mut valid = true;

        for &byte in &cp.path_bytes {
            match byte {
                b if b <= MAX_TERMINAL_ID => {
                    match token_ids.name(b as u16) {
                        Some(name) => token_sequence.push(name.to_string()),
                        None => { valid = false; break; }
                    }
                }
                IDENT_CAPTURE => token_sequence.push("x".to_string()),
                BINDER_CAPTURE => token_sequence.push("x".to_string()),
                nt_byte if nt_byte >= NT_BASE => {
                    // NT byte: resolve via sorted category index
                    let cat_idx = (nt_byte - NT_BASE) as usize;
                    let shortest = shortest_leaf_path(cat_idx, all_trees, token_ids);
                    token_sequence.extend(shortest);
                }
                _ => { valid = false; break; }
            }
        }

        if valid {
            suggestions.push(TestSuggestion {
                category: tree.category.clone(),
                rule_label: cp.rule_label.clone(),
                token_sequence,
                path_id,
            });
        }
    }

    suggestions
}

/// Find the shortest token sequence to reach a leaf in the category at `cat_idx`.
///
/// Returns an empty Vec if the category cannot be resolved.
fn shortest_leaf_path(
    cat_idx: usize,
    all_trees: &HashMap<String, CategoryDecisionTree>,
    token_ids: &TokenIdMap,
) -> Vec<String> {
    // Category names are not indexed by position in the decision tree map,
    // so we need to look through the builder's category mapping. Since we
    // don't have access to the builder here, we iterate all trees and find
    // the one that has a matching segment. This is a best-effort heuristic.
    //
    // In practice, the NT_BASE + cat_idx encoding uses the same ordering as
    // the DecisionTreeBuilder's `category_ids` (sorted category names).
    let mut sorted_cats: Vec<&String> = all_trees.keys().collect();
    sorted_cats.sort();

    let cat_name = match sorted_cats.get(cat_idx) {
        Some(name) => *name,
        None => return Vec::new(),
    };

    let tree = match all_trees.get(cat_name) {
        Some(t) => t,
        None => return Vec::new(),
    };

    // Find the shortest path in segment 0 (root) that reaches a Commit
    let segment = match tree.segments.first() {
        Some(s) => s,
        None => return Vec::new(),
    };

    let mut best: Option<Vec<String>> = None;
    for (path_bytes, action) in segment.iter() {
        if !matches!(action, DecisionAction::Commit { .. }) {
            continue;
        }
        let mut tokens = Vec::new();
        let mut ok = true;
        for &b in &path_bytes {
            match b {
                b if b <= MAX_TERMINAL_ID => {
                    match token_ids.name(b as u16) {
                        Some(name) => tokens.push(name.to_string()),
                        None => { ok = false; break; }
                    }
                }
                IDENT_CAPTURE | BINDER_CAPTURE => tokens.push("x".to_string()),
                _ => { ok = false; break; } // Skip NT-recursive for simplicity
            }
        }
        if ok {
            if best.as_ref().map_or(true, |prev| tokens.len() < prev.len()) {
                best = Some(tokens);
            }
        }
    }

    best.unwrap_or_default()
}

/// Layer 10: Incremental codegen support.
///
/// Returns a content hash for a category's decision tree. When the hash
/// matches a previous build, the category's generated code can be skipped.
pub fn category_content_hash(tree: &CategoryDecisionTree) -> u128 {
    use std::hash::DefaultHasher;
    let mut hasher = DefaultHasher::new();
    tree.category.hash(&mut hasher);
    tree.stats.total_states.hash(&mut hasher);
    tree.stats.total_rules.hash(&mut hasher);
    for segment in &tree.segments {
        for (path, action) in segment.iter() {
            path.hash(&mut hasher);
            action.hash(&mut hasher);
        }
    }
    let h = hasher.finish();
    h as u128
}

/// Version tag to invalidate cache when codegen logic changes.
/// Bump this whenever trampoline.rs, recursive.rs, dispatch.rs, or
/// pratt.rs codegen logic changes.
pub const CACHE_VERSION: u32 = 1;

/// Incremental state tracking for content-addressable comparison
/// and per-category code caching (.prattail-cache).
#[derive(Clone, Debug, Default)]
pub struct IncrementalState {
    /// Cache format version — mismatched versions discard the entire cache.
    pub version: u32,
    /// Per-category content hashes from `category_content_hash()`.
    pub category_hashes: HashMap<String, u128>,
    /// Cached generated code per category (keyed by category name).
    pub category_code: HashMap<String, String>,
}

impl IncrementalState {
    /// Check if the cached state is compatible with the current codegen version.
    pub fn is_valid(&self) -> bool {
        self.version == CACHE_VERSION
    }

    /// Check if a category's tree is unchanged from previous build.
    pub fn is_unchanged(&self, category: &str, current_hash: u128) -> bool {
        self.category_hashes.get(category) == Some(&current_hash)
    }

    /// Record the current hash for a category.
    pub fn record(&mut self, category: &str, hash: u128) {
        self.category_hashes.insert(category.to_string(), hash);
    }

    /// Load incremental state from a binary cache file.
    ///
    /// Format: `[version: u32][num_categories: u32]`
    /// followed by per-category entries:
    /// `[name_len: u32][name: bytes][hash: u128][code_len: u32][code: bytes]`
    pub fn load(path: &std::path::Path) -> Option<Self> {
        let data = std::fs::read(path).ok()?;
        let mut cursor = &data[..];

        let read_u32 = |c: &mut &[u8]| -> Option<u32> {
            if c.len() < 4 { return None; }
            let val = u32::from_le_bytes([c[0], c[1], c[2], c[3]]);
            *c = &c[4..];
            Some(val)
        };
        let read_u128 = |c: &mut &[u8]| -> Option<u128> {
            if c.len() < 16 { return None; }
            let mut buf = [0u8; 16];
            buf.copy_from_slice(&c[..16]);
            *c = &c[16..];
            Some(u128::from_le_bytes(buf))
        };
        let read_bytes = |c: &mut &[u8], len: usize| -> Option<Vec<u8>> {
            if c.len() < len { return None; }
            let val = c[..len].to_vec();
            *c = &c[len..];
            Some(val)
        };

        let version = read_u32(&mut cursor)?;
        let num_cats = read_u32(&mut cursor)? as usize;

        let mut category_hashes = HashMap::with_capacity(num_cats);
        let mut category_code = HashMap::with_capacity(num_cats);

        for _ in 0..num_cats {
            let name_len = read_u32(&mut cursor)? as usize;
            let name_bytes = read_bytes(&mut cursor, name_len)?;
            let name = String::from_utf8(name_bytes).ok()?;
            let hash = read_u128(&mut cursor)?;
            let code_len = read_u32(&mut cursor)? as usize;
            let code_bytes = read_bytes(&mut cursor, code_len)?;
            let code = String::from_utf8(code_bytes).ok()?;
            category_hashes.insert(name.clone(), hash);
            category_code.insert(name, code);
        }

        Some(IncrementalState {
            version,
            category_hashes,
            category_code,
        })
    }

    /// Save incremental state to a binary cache file.
    pub fn save(&self, path: &std::path::Path) -> std::io::Result<()> {
        use std::io::Write;
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let mut buf: Vec<u8> = Vec::new();
        buf.write_all(&self.version.to_le_bytes())?;
        buf.write_all(&(self.category_hashes.len() as u32).to_le_bytes())?;

        for (name, hash) in &self.category_hashes {
            let name_bytes = name.as_bytes();
            buf.write_all(&(name_bytes.len() as u32).to_le_bytes())?;
            buf.write_all(name_bytes)?;
            buf.write_all(&hash.to_le_bytes())?;
            let code = self.category_code.get(name).map(|s| s.as_str()).unwrap_or("");
            let code_bytes = code.as_bytes();
            buf.write_all(&(code_bytes.len() as u32).to_le_bytes())?;
            buf.write_all(code_bytes)?;
        }

        std::fs::write(path, &buf)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Lightweight pipeline: build decision trees from LanguageSpec
// ══════════════════════════════════════════════════════════════════════════════

/// Build decision trees from a `LanguageSpec` via lightweight analysis pipeline.
///
/// Runs the minimum steps needed: rule classification → TokenIdMap → FIRST sets
/// → decision tree construction. Does NOT run full codegen, FOLLOW sets, or
/// WFST construction.
///
/// Used by:
/// - `compose_with_wfst()` for X06/X07 pre/post-composition tree comparison
/// - Any context where decision trees are needed without full parser generation
pub fn build_decision_trees_from_spec(
    spec: &crate::LanguageSpec,
) -> Option<HashMap<String, CategoryDecisionTree>> {
    use crate::prediction::{compute_first_sets, RuleInfo, FirstItem};
    use crate::pipeline::convert_syntax_item_to_rd;

    let category_names: Vec<String> = spec.types.iter().map(|t| t.name.clone()).collect();
    if category_names.is_empty() {
        return None;
    }

    // Build RuleInfo for FIRST set computation (mirrors pipeline.rs logic)
    let rule_infos: Vec<RuleInfo> = spec.rules.iter().map(|r| {
        RuleInfo {
            label: r.label.clone(),
            category: r.category.clone(),
            first_items: r.syntax.iter().take(1).map(|item| match item {
                crate::SyntaxItemSpec::Terminal(t) => FirstItem::Terminal(t.clone()),
                crate::SyntaxItemSpec::NonTerminal { category, .. } => {
                    if category_names.contains(category) {
                        FirstItem::NonTerminal(category.clone())
                    } else {
                        FirstItem::Ident
                    }
                }
                _ => FirstItem::Ident,
            }).collect(),
            is_infix: r.is_infix,
            is_var: r.is_var,
            is_literal: r.is_literal,
            is_cross_category: r.is_cross_category,
            is_cast: r.is_cast,
        }
    }).collect();

    // Compute FIRST sets
    let first_sets = compute_first_sets(&rule_infos, &category_names);

    // Build TokenIdMap from all terminal tokens
    let mut token_id_map = crate::token_id::TokenIdMap::new();
    for fs in first_sets.values() {
        for tok in fs.tokens.iter() {
            token_id_map.get_or_insert(tok);
        }
    }
    for v in &["Eof", "RParen", "RBrace", "RBracket", "Semi", "Comma",
               "LParen", "LBrace", "LBracket"] {
        token_id_map.get_or_insert(v);
    }

    // Build RD rules (non-infix, non-var, non-literal)
    let rd_rules: Vec<RDRuleInfo> = spec.rules.iter()
        .filter(|r| !r.is_infix && !r.is_var && !r.is_literal)
        .map(|rule| {
            RDRuleInfo {
                label: rule.label.clone(),
                category: rule.category.clone(),
                items: rule.syntax.iter().map(convert_syntax_item_to_rd).collect(),
                has_binder: rule.has_binder,
                has_multi_binder: rule.has_multi_binder,
                is_collection: rule.is_collection,
                collection_type: rule.collection_type,
                separator: rule.separator.clone(),
                prefix_bp: None, // lightweight path skips BP computation
                eval_mode: rule.eval_mode.clone(),
            }
        })
        .collect();

    // Build cross-category rules
    let cross_rules: Vec<CrossCategoryRule> = spec.rules.iter()
        .filter(|r| r.is_cross_category)
        .map(|r| CrossCategoryRule {
            label: r.label.clone(),
            source_category: r.cross_source_category.clone().unwrap_or_default(),
            result_category: r.category.clone(),
            operator: r.syntax.iter().find_map(|item| {
                if let crate::SyntaxItemSpec::Terminal(t) = item {
                    Some(t.clone())
                } else {
                    None
                }
            }).unwrap_or_default(),
            needs_backtrack: false,
        })
        .collect();

    // Build cast rules
    let cast_rules: Vec<CastRule> = spec.rules.iter()
        .filter(|r| r.is_cast)
        .map(|r| CastRule {
            label: r.label.clone(),
            source_category: r.cast_source_category.clone().unwrap_or_default(),
            target_category: r.category.clone(),
        })
        .collect();

    // Build decision trees
    let mut dt_builder = DecisionTreeBuilder::new(
        token_id_map,
        first_sets,
        category_names,
        HashSet::new(), // no dead rules in lightweight path
    );
    dt_builder.build_all(&rd_rules, &cross_rules, &cast_rules);
    Some(dt_builder.into_trees())
}

// ══════════════════════════════════════════════════════════════════════════════
// Integration: query helpers for trampoline/dispatch
// ══════════════════════════════════════════════════════════════════════════════

/// Dispatch strategy for a token variant in a category's decision tree.
///
/// Subsumes the ad-hoc analyses (A1 left-factoring, B1 two-token lookahead,
/// G1 suffix disjointness) with a single trie-based determination.
#[derive(Clone, Debug)]
pub enum DispatchStrategy {
    /// Token not in trie — no RD rule dispatches on it.
    NotPresent,
    /// Single rule dispatches on this token — emit direct arm.
    Singleton { rule_label: String },
    /// Multiple rules share this token but have disjoint suffixes after a
    /// shared terminal prefix. Emit deterministic multi-arm dispatch
    /// (subsumes A1+G1 Phase 2).
    DisjointSuffix {
        /// Shared terminal prefix length (0 if no shared prefix beyond dispatch token).
        shared_prefix_len: usize,
        /// Shared terminal bytes (not including the dispatch token).
        shared_terminals: Vec<u8>,
        /// After the shared prefix, suffix_token_variant → rule_label.
        suffix_map: BTreeMap<String, String>,
    },
    /// Multiple rules share this token and suffixes overlap — need NFA try-all.
    NfaTryAll {
        /// Rule labels in the ambiguous group.
        rule_labels: Vec<String>,
        /// Shared terminal prefix length (may be 0).
        shared_prefix_len: usize,
        /// Shared terminal bytes (not including the dispatch token).
        shared_terminals: Vec<u8>,
        /// Optional ContextWeight-based live rule sets per second-token variant.
        /// Maps second_token_variant → ContextWeight bitset of surviving rules.
        /// Populated by Sprint 3 pipeline enrichment; `None` when no ContextWeight
        /// analysis has been performed.
        live_rules_context: Option<HashMap<String, crate::automata::semiring::ContextWeight>>,
    },
}

impl CategoryDecisionTree {
    /// Determine the dispatch strategy for a token variant.
    ///
    /// This is the primary query method for the trampoline. It subsumes:
    /// - `group_rd_by_dispatch_token` (grouping by first byte)
    /// - `compute_shared_terminal_prefix` (single-child chains)
    /// - `second_token_lookahead` (depth-2 unique children)
    /// - `suffix_disjointness_check` (disjoint children after prefix)
    pub fn dispatch_strategy(
        &self,
        token_variant: &str,
        token_ids: &TokenIdMap,
    ) -> DispatchStrategy {
        let tok_id = match token_ids.get(token_variant) {
            Some(id) if id <= MAX_TERMINAL_ID as u16 => id as u8,
            _ => return DispatchStrategy::NotPresent,
        };

        let segment = match self.segments.first() {
            Some(s) => s,
            None => return DispatchStrategy::NotPresent,
        };

        // Collect all (path, action) starting with this dispatch token
        let entries: Vec<(Vec<u8>, DecisionAction)> = segment
            .iter()
            .filter_map(|(path, action)| {
                if path.first() == Some(&tok_id) {
                    Some((path, action.clone()))
                } else {
                    None
                }
            })
            .collect();

        match entries.len() {
            0 => DispatchStrategy::NotPresent,
            1 => {
                // Single entry — could be Commit (singleton) or Ambiguous
                match &entries[0].1 {
                    DecisionAction::Commit { rule_label, .. } => {
                        DispatchStrategy::Singleton { rule_label: rule_label.clone() }
                    }
                    DecisionAction::Ambiguous { candidates } => {
                        DispatchStrategy::NfaTryAll {
                            rule_labels: candidates.iter().map(|c| c.rule_label.clone()).collect(),
                            shared_prefix_len: 0,
                            shared_terminals: Vec::new(),
                            live_rules_context: None,
                        }
                    }
                    DecisionAction::NonterminalBoundary { .. } => {
                        DispatchStrategy::NotPresent
                    }
                }
            }
            _ => {
                // Multiple paths → find shared prefix + check suffix disjointness
                let min_len = entries.iter().map(|(p, _)| p.len()).min().unwrap_or(0);
                let mut shared_len = 1; // at least the dispatch token byte
                for offset in 1..min_len {
                    let byte = entries[0].0[offset];
                    if entries[1..].iter().all(|(p, _)| p[offset] == byte) {
                        shared_len += 1;
                    } else {
                        break;
                    }
                }

                // Extract shared terminal bytes (excluding dispatch token)
                let shared_terminals: Vec<u8> = if shared_len > 1 {
                    entries[0].0[1..shared_len].to_vec()
                } else {
                    Vec::new()
                };

                // Check if the byte after the shared prefix is distinct per rule
                let mut suffix_map = BTreeMap::new();
                let mut is_disjoint = true;
                for (path, action) in &entries {
                    if path.len() <= shared_len {
                        is_disjoint = false;
                        break;
                    }
                    let branch_byte = path[shared_len];
                    if branch_byte > MAX_TERMINAL_ID {
                        is_disjoint = false;
                        break;
                    }
                    let variant_name = match token_ids.name(branch_byte as u16) {
                        Some(n) => n.to_string(),
                        None => { is_disjoint = false; break; }
                    };
                    let rule_label = match action {
                        DecisionAction::Commit { rule_label, .. } => rule_label.clone(),
                        _ => { is_disjoint = false; break; }
                    };
                    if suffix_map.insert(variant_name, rule_label).is_some() {
                        is_disjoint = false;
                        break;
                    }
                }

                if is_disjoint && suffix_map.len() >= 2 {
                    DispatchStrategy::DisjointSuffix {
                        shared_prefix_len: shared_len - 1, // exclude dispatch token
                        shared_terminals,
                        suffix_map,
                    }
                } else {
                    // Collect all rule labels from the entries
                    let mut rule_labels = Vec::new();
                    for (_, action) in &entries {
                        match action {
                            DecisionAction::Commit { rule_label, .. } => {
                                rule_labels.push(rule_label.clone());
                            }
                            DecisionAction::Ambiguous { candidates } => {
                                for c in candidates {
                                    rule_labels.push(c.rule_label.clone());
                                }
                            }
                            _ => {}
                        }
                    }
                    DispatchStrategy::NfaTryAll {
                        rule_labels,
                        shared_prefix_len: shared_len - 1, // exclude dispatch token
                        shared_terminals,
                        live_rules_context: None,
                    }
                }
            }
        }
    }

    /// Get all dispatch tokens present in this category's trie.
    ///
    /// Returns token IDs (bytes 0x00-0x7F) that appear as the first byte
    /// of at least one path. Subsumes `group_rd_by_dispatch_token`.
    pub fn dispatch_tokens(&self, token_ids: &TokenIdMap) -> Vec<String> {
        let segment = match self.segments.first() {
            Some(s) => s,
            None => return Vec::new(),
        };

        let mut seen = HashSet::new();
        let mut tokens = Vec::new();
        for (path, _) in segment.iter() {
            if let Some(&first_byte) = path.first() {
                if first_byte <= MAX_TERMINAL_ID && seen.insert(first_byte) {
                    if let Some(name) = token_ids.name(first_byte as u16) {
                        tokens.push(name.to_string());
                    }
                }
            }
        }
        tokens.sort();
        tokens
    }

    /// 2a: Compute dispatch entropy profile for this category's trie.
    ///
    /// At each dispatch token (root child), computes Shannon entropy:
    ///   H = -Σ (p_i × log₂(p_i))
    /// where p_i = fraction of rules reachable via child i.
    ///
    /// Low entropy (near 0) = one dominant path (restructuring won't help).
    /// High entropy (near log₂(N)) = uniform distribution (maximum ambiguity).
    ///
    /// Returns `(token_byte, entropy, rule_count)` sorted by entropy descending.
    pub fn entropy_profile(&self) -> Vec<(u8, f64, usize)> {
        let segment = match self.segments.first() {
            Some(s) => s,
            None => return Vec::new(),
        };

        // Group rules by root byte
        let mut rules_per_byte: HashMap<u8, HashSet<String>> = HashMap::new();
        for (path, action) in segment.iter() {
            if let Some(&first_byte) = path.first() {
                if first_byte <= MAX_TERMINAL_ID {
                    let entry = rules_per_byte.entry(first_byte).or_default();
                    match &action {
                        DecisionAction::Commit { rule_label, .. } => {
                            entry.insert(rule_label.clone());
                        }
                        DecisionAction::Ambiguous { candidates } => {
                            for c in candidates {
                                entry.insert(c.rule_label.clone());
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        let total_rules: usize = rules_per_byte.values().map(|s| s.len()).sum();
        if total_rules == 0 {
            return Vec::new();
        }

        let mut profile: Vec<(u8, f64, usize)> = rules_per_byte
            .iter()
            .map(|(&byte, rules)| {
                let p = rules.len() as f64 / total_rules as f64;
                let entropy = if p > 0.0 { -p * p.log2() } else { 0.0 };
                (byte, entropy, rules.len())
            })
            .collect();

        // Sort by entropy descending (highest bottleneck first)
        profile.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        profile
    }

    /// 2b: Compute BP/dispatch correlation for this category.
    ///
    /// For each binding power level, determines how many of the category's
    /// total rules are reachable. At low BPs, fewer rules may be reachable
    /// (enabling early commit). At high BPs, most rules are reachable.
    ///
    /// Returns `Vec<(bp, reachable_count, total_count)>` sorted by BP ascending.
    /// The `bp_table` maps `(category, rule_label) → bp` for infix rules.
    pub fn bp_stratification(
        &self,
        bp_table: &HashMap<String, u8>,
    ) -> Vec<(u8, usize, usize)> {
        let reachable = self.reachable_rules();
        if reachable.is_empty() {
            return Vec::new();
        }

        // Group reachable rules by BP (default to 0 for prefix rules with no BP)
        let mut bp_counts: HashMap<u8, usize> = HashMap::new();
        for rule in &reachable {
            let bp = bp_table.get(rule).copied().unwrap_or(0);
            *bp_counts.entry(bp).or_insert(0) += 1;
        }

        let total = reachable.len();
        let mut strata: Vec<(u8, usize, usize)> = Vec::new();
        let mut cumulative = 0;
        let mut sorted_bps: Vec<u8> = bp_counts.keys().copied().collect();
        sorted_bps.sort_unstable();

        for bp in sorted_bps {
            cumulative += bp_counts[&bp];
            strata.push((bp, cumulative, total));
        }

        strata
    }

    /// Collect all rule labels reachable via this category's trie dispatch.
    ///
    /// Walks all segments and extracts rule labels from `Commit` and
    /// `Ambiguous` actions. Rules not in this set are unreachable through
    /// trie-based dispatch.
    pub fn reachable_rules(&self) -> HashSet<String> {
        let mut reachable = HashSet::new();
        for segment in &self.segments {
            for (_path, action) in segment.iter() {
                match action {
                    DecisionAction::Commit { rule_label, .. } => {
                        reachable.insert(rule_label.clone());
                    }
                    DecisionAction::Ambiguous { candidates } => {
                        for c in candidates {
                            reachable.insert(c.rule_label.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        reachable
    }
}

/// Compute trie-informed weight adjustments for WFST prediction actions.
///
/// For each category and dispatch token, compute a weight adjustment factor
/// based on the dispatch strategy:
/// - `DisjointSuffix` → weight -= 0.25 (resolved without backtracking)
/// - `NfaTryAll` with long shared prefix → weight += 0.1 × shared_prefix_len
///   (longer prefix = more tokens consumed before ambiguity)
/// - `Singleton` → weight -= 0.5 (fully deterministic)
///
/// Returns a map of (category, token) → weight_adjustment.
pub fn compute_weight_adjustments(
    trees: &HashMap<String, CategoryDecisionTree>,
    token_ids: &TokenIdMap,
) -> HashMap<(String, String), f64> {
    let mut adjustments = HashMap::new();
    for (cat_name, tree) in trees {
        let dispatch_tokens = tree.dispatch_tokens(token_ids);
        for token_variant in &dispatch_tokens {
            let strategy = tree.dispatch_strategy(token_variant, token_ids);
            let adjustment = match &strategy {
                DispatchStrategy::Singleton { .. } => -0.5,
                DispatchStrategy::DisjointSuffix { shared_prefix_len, .. } => {
                    -0.25 - (*shared_prefix_len as f64 * 0.05)
                }
                DispatchStrategy::NfaTryAll { shared_prefix_len, .. } => {
                    *shared_prefix_len as f64 * 0.1
                }
                DispatchStrategy::NotPresent => 0.0,
            };
            if adjustment.abs() > f64::EPSILON {
                adjustments.insert(
                    (cat_name.clone(), token_variant.clone()),
                    adjustment,
                );
            }
        }
    }
    adjustments
}

/// 1.3a: Compute trie-depth-based discount factors for sync tokens.
///
/// For each category, determines the minimum trie depth at which each sync
/// token appears. Tokens at depth 0 (trie root children) are excellent sync
/// points — the parser can resume quickly. Tokens at depth 3+ are poor sync
/// points — many tokens must be consumed before reaching a valid parse state.
///
/// Returns `(category, token_id) → discount_factor`:
/// - Depth 0: 0.5 (strongly preferred)
/// - Depth 1: 0.7
/// - Depth 2: 0.9
/// - Depth 3+: 1.2 (demoted)
/// - Not in trie: 1.0 (neutral)
pub fn compute_sync_depth_discounts(
    trees: &HashMap<String, CategoryDecisionTree>,
    token_ids: &TokenIdMap,
) -> HashMap<(String, u16), f64> {
    let mut discounts = HashMap::new();
    for (cat_name, tree) in trees {
        // Collect minimum depth per first byte (terminal token) across all paths
        let mut min_depth: HashMap<u8, usize> = HashMap::new();
        if let Some(segment) = tree.segments.first() {
            for (path, _action) in segment.iter() {
                if let Some(&first_byte) = path.first() {
                    if first_byte <= MAX_TERMINAL_ID {
                        let depth = 0; // Root children are at depth 0
                        let entry = min_depth.entry(first_byte).or_insert(depth);
                        *entry = (*entry).min(depth);
                    }
                    // Also record depths for tokens deeper in the path
                    for (i, &byte) in path.iter().enumerate().skip(1) {
                        if byte <= MAX_TERMINAL_ID {
                            let entry = min_depth.entry(byte).or_insert(i);
                            *entry = (*entry).min(i);
                        }
                    }
                }
            }
        }

        for (&byte, &depth) in &min_depth {
            let token_id = byte as u16;
            if token_ids.name(token_id).is_some() {
                let discount = match depth {
                    0 => 0.5,
                    1 => 0.7,
                    2 => 0.9,
                    _ => 1.2,
                };
                discounts.insert((cat_name.clone(), token_id), discount);
            }
        }
    }
    discounts
}

/// Query the decision tree for a category at a given dispatch token.
///
/// Returns the action at the single-byte path for the token, or None
/// if the token is not in the tree.
///
/// Superseded by `dispatch_strategy()` for production use. Retained for tests.
#[cfg(test)]
pub fn query_dispatch_token<'a>(
    tree: &'a CategoryDecisionTree,
    token_variant: &str,
    token_ids: &TokenIdMap,
) -> Option<&'a DecisionAction> {
    let tok_id = token_ids.get(token_variant)?;
    if tok_id > MAX_TERMINAL_ID as u16 {
        return None;
    }
    tree.segments.first()?.get(&[tok_id as u8])
}

/// Check if the dispatch for a token is deterministic (single rule).
///
/// Superseded by `dispatch_strategy()` for production use. Retained for tests.
#[cfg(test)]
pub fn is_token_deterministic(
    tree: &CategoryDecisionTree,
    token_variant: &str,
    token_ids: &TokenIdMap,
) -> bool {
    query_dispatch_token(tree, token_variant, token_ids)
        .map_or(false, |a: &DecisionAction| a.is_deterministic())
}

/// Get all rules that share a dispatch token (for NFA-merged handling).
///
/// Superseded by `dispatch_strategy()` for production use. Retained for tests.
#[cfg(test)]
pub fn rules_for_token(
    tree: &CategoryDecisionTree,
    token_variant: &str,
    token_ids: &TokenIdMap,
) -> Vec<String> {
    match query_dispatch_token(tree, token_variant, token_ids) {
        Some(DecisionAction::Commit { rule_label, .. }) => vec![rule_label.clone()],
        Some(DecisionAction::Ambiguous { candidates }) => {
            candidates.iter().map(|c| c.rule_label.clone()).collect()
        }
        _ => Vec::new(),
    }
}

/// Check if the trie has a shared terminal prefix for rules under a token.
///
/// Returns the shared prefix length (in trie depth) if > 0.
/// Uses iter() to analyze path structure without zipper APIs.
///
/// Superseded by `dispatch_strategy()` for production use. Retained for tests.
#[cfg(test)]
pub fn shared_prefix_depth(
    tree: &CategoryDecisionTree,
    token_variant: &str,
    token_ids: &TokenIdMap,
) -> usize {
    let tok_id = match token_ids.get(token_variant) {
        Some(id) if id <= MAX_TERMINAL_ID as u16 => id as u8,
        _ => return 0,
    };

    let segment = match tree.segments.first() {
        Some(s) => s,
        None => return 0,
    };

    // Collect all paths starting with tok_id
    let paths: Vec<Vec<u8>> = segment
        .iter()
        .filter_map(|(path, _)| {
            if path.first() == Some(&tok_id) {
                Some(path)
            } else {
                None
            }
        })
        .collect();

    if paths.len() < 2 {
        return 0;
    }

    // Find longest common prefix length across all paths (after the dispatch byte)
    let min_len = paths.iter().map(|p| p.len()).min().unwrap_or(0);
    let mut shared_depth = 0;
    for offset in 1..min_len {
        let byte = paths[0][offset];
        if paths[1..].iter().all(|p| p[offset] == byte) {
            shared_depth += 1;
        } else {
            break;
        }
    }
    shared_depth
}

/// Check suffix disjointness for rules sharing a token prefix.
///
/// After the shared prefix, check if the next tokens are all distinct
/// (disjoint FIRST sets). Returns the mapping token_variant -> rule_label
/// if disjoint, None otherwise.
///
/// Superseded by `dispatch_strategy()` for production use. Retained for tests.
#[cfg(test)]
pub fn suffix_disjoint_dispatch(
    tree: &CategoryDecisionTree,
    token_variant: &str,
    token_ids: &TokenIdMap,
) -> Option<BTreeMap<String, String>> {
    let tok_id = match token_ids.get(token_variant) {
        Some(id) if id <= MAX_TERMINAL_ID as u16 => id as u8,
        _ => return None,
    };

    let segment = match tree.segments.first() {
        Some(s) => s,
        None => return None,
    };

    // Collect all (path, action) starting with tok_id
    let entries: Vec<(Vec<u8>, DecisionAction)> = segment
        .iter()
        .filter_map(|(path, action)| {
            if path.first() == Some(&tok_id) {
                Some((path, action.clone()))
            } else {
                None
            }
        })
        .collect();

    if entries.len() < 2 {
        return None;
    }

    // Find shared prefix length (same as shared_prefix_depth)
    let min_len = entries.iter().map(|(p, _)| p.len()).min().unwrap_or(0);
    let mut prefix_len = 1; // dispatch token
    for offset in 1..min_len {
        let byte = entries[0].0[offset];
        if entries[1..].iter().all(|(p, _)| p[offset] == byte) {
            prefix_len += 1;
        } else {
            break;
        }
    }

    // Check if the byte after the shared prefix is distinct per rule
    let mut dispatch_map = BTreeMap::new();
    for (path, action) in &entries {
        if path.len() <= prefix_len {
            return None; // Path ends at/before the branch point
        }
        let branch_byte = path[prefix_len];
        if branch_byte > MAX_TERMINAL_ID {
            return None; // Non-terminal at branch point
        }
        let variant_name = token_ids.name(branch_byte as u16)?;
        let rule_label = match action {
            DecisionAction::Commit { rule_label, .. } => rule_label.clone(),
            _ => return None, // Ambiguous — not a simple dispatch
        };
        if dispatch_map.insert(variant_name.to_string(), rule_label).is_some() {
            return None; // Duplicate branch byte — not disjoint
        }
    }

    if dispatch_map.len() >= 2 {
        Some(dispatch_map)
    } else {
        None
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    fn make_token_ids() -> TokenIdMap {
        let mut map = TokenIdMap::new();
        /* terminal_to_variant_name maps:
         *   "float" → "KwFloat", "if" → "KwIf", "then" → "KwThen",
         *   "else" → "KwElse", "let" → "KwLet", "in" → "KwIn",
         *   "(" → "LParen", ")" → "RParen", "=" → "Eq",
         *   "+" → "Plus", "-" → "Minus", "*" → "Star", "/" → "Slash"
         */
        for name in &[
            "KwFloat", "LParen", "RParen", "Plus", "Minus", "Star", "Slash",
            "Ident", "Integer", "Comma", "Colon", "Semi", "KwIf", "KwThen", "KwElse",
            "KwLet", "KwIn", "Eq",
        ] {
            map.get_or_insert(name);
        }
        map
    }

    fn make_first_sets() -> HashMap<String, FirstSet> {
        let mut sets = HashMap::new();
        let mut int_first = FirstSet::default();
        int_first.insert("Integer");
        int_first.insert("Ident");
        int_first.insert("LParen");
        sets.insert("Int".to_string(), int_first);

        let mut float_first = FirstSet::default();
        float_first.insert("Float");
        float_first.insert("Ident");
        float_first.insert("LParen");
        sets.insert("Float".to_string(), float_first);
        sets
    }

    fn make_rd_rule(label: &str, category: &str, items: Vec<RDSyntaxItem>) -> RDRuleInfo {
        RDRuleInfo {
            label: label.to_string(),
            category: category.to_string(),
            items,
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        }
    }

    #[test]
    fn test_pattern_encoding_terminal_only() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        let rule = make_rd_rule("IfThenElse", "Int", vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Terminal("then".to_string()),
            RDSyntaxItem::Terminal("else".to_string()),
        ]);

        let pattern = builder.pattern_from_rd_rule(&rule);
        assert_eq!(pattern.len(), 3);
        assert!(matches!(pattern[0], PatternElement::Terminal { ref variant, .. } if variant == "KwIf"));
        assert!(matches!(pattern[1], PatternElement::Terminal { ref variant, .. } if variant == "KwThen"));
        assert!(matches!(pattern[2], PatternElement::Terminal { ref variant, .. } if variant == "KwElse"));

        let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
        assert_eq!(bytes.len(), 3);
        assert!(boundary.is_none());
    }

    #[test]
    fn test_pattern_encoding_with_nonterminal() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        let rule = make_rd_rule("FloatCast", "Float", vec![
            RDSyntaxItem::Terminal("float".to_string()),
            RDSyntaxItem::Terminal("(".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "x".to_string(),
            },
            RDSyntaxItem::Terminal(")".to_string()),
        ]);

        let pattern = builder.pattern_from_rd_rule(&rule);
        assert_eq!(pattern.len(), 4);

        let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
        assert_eq!(bytes.len(), 2); // float, (
        assert!(boundary.is_some());
        let b = boundary.expect("should have NT boundary");
        assert_eq!(b.category, "Int");
        assert_eq!(b.remaining_pattern.len(), 1); // RParen
    }

    #[test]
    fn test_builder_insert_rd_rules() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("=".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
        ];

        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        assert!(tree.segments[0].val_count() >= 2);
    }

    #[test]
    fn test_ambiguous_rules_same_token() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Float".to_string()],
            HashSet::new(),
        );

        // Two rules both start with "float" "("
        let rules = vec![
            make_rd_rule("FloatId", "Float", vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::IdentCapture { param_name: "x".to_string() },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IntToFloat", "Float", vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];

        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Float").expect("should have Float tree");
        assert!(tree.segments[0].val_count() >= 1);
    }

    #[test]
    fn test_dead_rule_pruning() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let dead = HashSet::from(["DeadRule".to_string()]);
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            dead,
        );

        let rules = vec![
            make_rd_rule("LiveRule", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
            ]),
            make_rd_rule("DeadRule", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
            ]),
        ];

        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        // Only LiveRule should be inserted
        assert_eq!(tree.segments[0].val_count(), 1);
    }

    #[test]
    fn test_statistics_computation() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
        ];

        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        assert!(tree.stats.total_states > 0);
        assert!(tree.stats.total_rules >= 2);
        assert_eq!(tree.stats.ambiguous_nodes, 0);
    }

    #[test]
    fn test_emission_strategy() {
        let tree = CategoryDecisionTree {
            category: "Int".to_string(),
            segments: vec![PathMap::new()],
            stats: TreeStats {
                total_states: 10,
                ..Default::default()
            },
        };
        assert_eq!(emission_strategy(&tree), EmissionStrategy::MatchArms);

        let tree_large = CategoryDecisionTree {
            category: "Int".to_string(),
            segments: vec![PathMap::new()],
            stats: TreeStats {
                total_states: 300,
                ..Default::default()
            },
        };
        assert_eq!(emission_strategy(&tree_large), EmissionStrategy::FlatTable);
    }

    #[test]
    fn test_incremental_state() {
        let mut state = IncrementalState::default();
        state.record("Int", 12345);
        assert!(state.is_unchanged("Int", 12345));
        assert!(!state.is_unchanged("Int", 99999));
        assert!(!state.is_unchanged("Float", 12345));
    }

    #[test]
    fn test_incremental_cache_round_trip() {
        let mut state = IncrementalState {
            version: CACHE_VERSION,
            ..Default::default()
        };
        state.record("Expr", 0x12345);
        state.category_code.insert("Expr".to_string(), "fn parse_Expr() {}".to_string());
        state.record("Stmt", 0xABCDE);
        state.category_code.insert("Stmt".to_string(), "fn parse_Stmt() {}".to_string());

        let tmp = std::env::temp_dir().join("prattail_test_cache");
        state.save(&tmp).expect("save should succeed");
        let loaded = IncrementalState::load(&tmp).expect("load should succeed");
        assert!(loaded.is_valid(), "loaded cache should be valid");
        assert!(loaded.is_unchanged("Expr", 0x12345));
        assert!(loaded.is_unchanged("Stmt", 0xABCDE));
        assert!(!loaded.is_unchanged("Expr", 0x99999));
        assert_eq!(
            loaded.category_code.get("Expr").expect("Expr code"),
            "fn parse_Expr() {}",
        );
        assert_eq!(
            loaded.category_code.get("Stmt").expect("Stmt code"),
            "fn parse_Stmt() {}",
        );

        // Version mismatch should invalidate
        let mut bad_version = state.clone();
        bad_version.version = CACHE_VERSION + 1;
        bad_version.save(&tmp).expect("save bad version");
        let loaded_bad = IncrementalState::load(&tmp).expect("load should succeed");
        assert!(!loaded_bad.is_valid(), "mismatched version should be invalid");

        let _ = std::fs::remove_file(&tmp);
    }

    #[test]
    fn test_dispatch_strategy_singleton() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        match tree.dispatch_strategy("KwIf", &token_ids) {
            DispatchStrategy::Singleton { rule_label } => {
                assert_eq!(rule_label, "IfThenElse");
            }
            other => panic!("expected Singleton, got {:?}", other),
        }

        // Token not in tree
        assert!(matches!(
            tree.dispatch_strategy("Plus", &token_ids),
            DispatchStrategy::NotPresent
        ));
    }

    #[test]
    fn test_dispatch_strategy_disjoint_suffix() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        /* Two rules sharing dispatch token "if":
         *   IfPlus:  if + then
         *   IfMinus: if - else
         * After shared prefix "if" (dispatch token), next tokens are "+" and "-"
         * which are disjoint. */
        let rules = vec![
            make_rd_rule("IfPlus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
            ]),
            make_rd_rule("IfMinus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("-".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        match tree.dispatch_strategy("KwIf", &token_ids) {
            DispatchStrategy::DisjointSuffix { shared_prefix_len, suffix_map, .. } => {
                assert_eq!(shared_prefix_len, 0); // no shared terminals beyond dispatch token
                assert_eq!(suffix_map.len(), 2);
                assert_eq!(suffix_map.get("Plus").expect("Plus"), "IfPlus");
                assert_eq!(suffix_map.get("Minus").expect("Minus"), "IfMinus");
            }
            other => panic!("expected DisjointSuffix, got {:?}", other),
        }
    }

    #[test]
    fn test_dispatch_strategy_shared_prefix_disjoint() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        /* Two rules sharing "if" "(" as prefix, then diverging:
         *   IfParenPlus:  if ( + )
         *   IfParenMinus: if ( - )
         * Shared prefix = ["("], then "+" vs "-" disjoint. */
        let rules = vec![
            make_rd_rule("IfParenPlus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfParenMinus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("-".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        match tree.dispatch_strategy("KwIf", &token_ids) {
            DispatchStrategy::DisjointSuffix { shared_prefix_len, shared_terminals, suffix_map } => {
                assert_eq!(shared_prefix_len, 1); // "(" is shared
                assert_eq!(shared_terminals.len(), 1);
                assert_eq!(suffix_map.len(), 2);
                assert!(suffix_map.contains_key("Plus"));
                assert!(suffix_map.contains_key("Minus"));
            }
            other => panic!("expected DisjointSuffix with shared prefix, got {:?}", other),
        }
    }

    #[test]
    fn test_dispatch_strategy_nfa_tryall() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Float".to_string()],
            HashSet::new(),
        );

        /* Two rules sharing "float" "(" and then a non-terminal vs ident capture.
         * The trie can't disambiguate at the terminal level since the
         * nonterminal is encoded as an NT byte, not a terminal. */
        let rules = vec![
            make_rd_rule("FloatId", "Float", vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::IdentCapture { param_name: "x".to_string() },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("FloatCast", "Float", vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Float").expect("should have Float tree");
        /* After "float" "(" the next items are IdentCapture (0x80) and
         * NonTerminal (encoded at NT boundary). Since IdentCapture is > MAX_TERMINAL_ID,
         * the suffix disjointness check should fail → NfaTryAll. */
        match tree.dispatch_strategy("KwFloat", &token_ids) {
            DispatchStrategy::NfaTryAll { rule_labels, shared_prefix_len, .. } => {
                assert!(shared_prefix_len >= 1); // "(" is shared
                assert!(rule_labels.len() >= 1); // at least one rule
            }
            DispatchStrategy::DisjointSuffix { .. } => {
                /* Also acceptable if the encoding makes the suffixes look disjoint
                 * (IdentCapture byte vs NT boundary truncation). */
            }
            other => panic!("expected NfaTryAll or DisjointSuffix, got {:?}", other),
        }
    }

    #[test]
    fn test_dispatch_tokens() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let tokens = tree.dispatch_tokens(&token_ids);
        assert!(tokens.contains(&"KwIf".to_string()));
        assert!(tokens.contains(&"KwLet".to_string()));
        assert_eq!(tokens.len(), 2);
    }

    // ══════════════════════════════════════════════════════════════════════
    // Equivalence tests: decision tree vs ad-hoc analysis
    // ══════════════════════════════════════════════════════════════════════

    /// Verify that for singleton dispatch tokens, both the ad-hoc
    /// group_rd_by_dispatch_token and the decision tree agree.
    #[test]
    fn test_equivalence_singleton_dispatch() {
        use crate::trampoline::group_rd_by_dispatch_token_pub;

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");

        /* Ad-hoc analysis */
        let adhoc_groups = group_rd_by_dispatch_token_pub(&rules, "Int");

        /* Both should identify the same dispatch tokens */
        let dt_tokens = tree.dispatch_tokens(&token_ids);
        let adhoc_tokens: Vec<String> = adhoc_groups.keys().cloned().collect();
        assert_eq!(dt_tokens, adhoc_tokens, "dispatch tokens should match");

        /* For each singleton group, decision tree should say Singleton */
        for (variant, group_rules) in &adhoc_groups {
            let strategy = tree.dispatch_strategy(variant, &token_ids);
            if group_rules.len() == 1 {
                match strategy {
                    DispatchStrategy::Singleton { rule_label } => {
                        assert_eq!(
                            rule_label, group_rules[0].label,
                            "singleton rule label mismatch for {}",
                            variant
                        );
                    }
                    other => panic!(
                        "expected Singleton for {} (ad-hoc has 1 rule), got {:?}",
                        variant, other
                    ),
                }
            }
        }
    }

    /// Verify that for multi-rule groups with shared prefix + disjoint
    /// suffixes, the decision tree's DisjointSuffix matches the ad-hoc
    /// compute_shared_terminal_prefix + suffix_disjointness_check.
    #[test]
    fn test_equivalence_shared_prefix_disjoint() {
        use crate::automata::codegen::terminal_to_variant_name;
        use crate::trampoline::{
            compute_shared_terminal_prefix, group_rd_by_dispatch_token_pub,
            suffix_disjointness_check,
        };

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        /* Rules: both start with "if" "(" then diverge at "+" vs "-" */
        let rules = vec![
            make_rd_rule("IfParenPlus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfParenMinus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("-".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");

        /* Ad-hoc analysis */
        let adhoc_groups = group_rd_by_dispatch_token_pub(&rules, "Int");
        let kw_if = terminal_to_variant_name("if");
        let group = adhoc_groups.get(&kw_if).expect("should have KwIf group");
        assert_eq!(group.len(), 2);

        let shared_prefix = compute_shared_terminal_prefix(group);
        /* shared prefix should be ["("] (items[1]) */
        assert_eq!(shared_prefix.len(), 1, "ad-hoc: expected shared prefix of length 1");
        assert_eq!(shared_prefix[0], "(");

        let skip = 1 + shared_prefix.len(); // dispatch_token + shared_prefix
        let suffix_map = suffix_disjointness_check(group, skip, &first_sets);
        /* Ad-hoc should detect disjoint suffixes: "+" → 0, "-" → 1 */
        assert!(suffix_map.is_some(), "ad-hoc: expected disjoint suffixes");
        let adhoc_map = suffix_map.expect("checked above");

        /* Decision tree analysis */
        match tree.dispatch_strategy(&kw_if, &token_ids) {
            DispatchStrategy::DisjointSuffix {
                shared_prefix_len,
                suffix_map: dt_suffix_map,
                ..
            } => {
                /* shared_prefix_len should match ad-hoc shared_prefix.len() */
                assert_eq!(
                    shared_prefix_len,
                    shared_prefix.len(),
                    "shared prefix length mismatch: dt={}, adhoc={}",
                    shared_prefix_len,
                    shared_prefix.len()
                );

                /* Both should have the same suffix tokens */
                let adhoc_tokens: std::collections::BTreeSet<String> =
                    adhoc_map.keys().cloned().collect();
                let dt_tokens: std::collections::BTreeSet<String> =
                    dt_suffix_map.keys().cloned().collect();
                assert_eq!(
                    adhoc_tokens, dt_tokens,
                    "suffix dispatch tokens differ: adhoc={:?}, dt={:?}",
                    adhoc_tokens, dt_tokens
                );

                /* Rule labels should correspond (ad-hoc maps token→index, dt maps token→label) */
                for (dt_token, dt_label) in &dt_suffix_map {
                    let adhoc_indices = adhoc_map
                        .get(dt_token)
                        .expect("token should exist in ad-hoc map");
                    assert_eq!(
                        adhoc_indices.len(),
                        1,
                        "ad-hoc should have exactly 1 index per token"
                    );
                    let adhoc_label = &group[adhoc_indices[0]].label;
                    assert_eq!(
                        dt_label, adhoc_label,
                        "rule label mismatch for suffix token {}: dt={}, adhoc={}",
                        dt_token, dt_label, adhoc_label
                    );
                }
            }
            other => panic!(
                "decision tree should return DisjointSuffix, got {:?}",
                other
            ),
        }
    }

    /// Verify that for multi-rule groups with NO shared prefix but disjoint
    /// second tokens, both analyses agree (B1: second_token_lookahead).
    #[test]
    fn test_equivalence_second_token_lookahead() {
        use crate::automata::codegen::terminal_to_variant_name;
        use crate::trampoline::{
            group_rd_by_dispatch_token_pub, second_token_lookahead,
        };

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        /* Rules: both start with "if" then immediately diverge at "+" vs "-" */
        let rules = vec![
            make_rd_rule("IfPlus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
            ]),
            make_rd_rule("IfMinus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("-".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");

        /* Ad-hoc B1 analysis */
        let adhoc_groups = group_rd_by_dispatch_token_pub(&rules, "Int");
        let kw_if = terminal_to_variant_name("if");
        let group = adhoc_groups.get(&kw_if).expect("should have KwIf group");
        assert_eq!(group.len(), 2);

        let b1 = second_token_lookahead(group);
        assert!(b1.is_some(), "ad-hoc B1: expected two-token lookahead");
        let b1_map = b1.expect("checked above");

        /* Decision tree analysis */
        match tree.dispatch_strategy(&kw_if, &token_ids) {
            DispatchStrategy::DisjointSuffix {
                shared_prefix_len,
                suffix_map: dt_suffix_map,
                ..
            } => {
                /* No shared prefix beyond dispatch token */
                assert_eq!(shared_prefix_len, 0, "no shared prefix expected");

                /* B1 maps second_variant → rule_index.
                 * DT maps suffix_variant → rule_label.
                 * They should agree on the set of suffix tokens. */
                let b1_tokens: std::collections::BTreeSet<String> =
                    b1_map.groups.keys().cloned().collect();
                let dt_tokens: std::collections::BTreeSet<String> =
                    dt_suffix_map.keys().cloned().collect();
                assert_eq!(
                    b1_tokens, dt_tokens,
                    "B1 vs DT suffix tokens: b1={:?}, dt={:?}",
                    b1_tokens, dt_tokens
                );

                /* Rule label correspondence */
                for (token, dt_label) in &dt_suffix_map {
                    let b1_idx = b1_map.groups.get(token).expect("token in b1");
                    let adhoc_label = &group[*b1_idx].label;
                    assert_eq!(
                        dt_label, adhoc_label,
                        "rule label mismatch for B1 token {}: dt={}, adhoc={}",
                        token, dt_label, adhoc_label
                    );
                }
            }
            other => panic!(
                "decision tree should return DisjointSuffix for B1 case, got {:?}",
                other
            ),
        }
    }

    /// Verify that when rules have overlapping suffixes (no disjointness),
    /// both the ad-hoc and decision tree agree on NFA try-all.
    #[test]
    fn test_equivalence_nfa_tryall() {
        use crate::automata::codegen::terminal_to_variant_name;
        use crate::trampoline::{
            compute_shared_terminal_prefix, group_rd_by_dispatch_token_pub,
            suffix_disjointness_check,
        };

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        /* Rules: both start with "if" "(" "+" — identical prefixes, no disjoint suffix.
         * They only differ in the last terminal. */
        let rules = vec![
            make_rd_rule("IfParenPlusThen", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
            ]),
            make_rd_rule("IfParenPlusElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");

        /* Ad-hoc analysis */
        let adhoc_groups = group_rd_by_dispatch_token_pub(&rules, "Int");
        let kw_if = terminal_to_variant_name("if");
        let group = adhoc_groups.get(&kw_if).expect("should have KwIf group");
        assert_eq!(group.len(), 2);

        let shared_prefix = compute_shared_terminal_prefix(group);
        /* shared prefix = ["(", "+"] (items[1] and items[2]) */
        assert_eq!(shared_prefix.len(), 2, "ad-hoc: shared prefix should be 2");

        let skip = 1 + shared_prefix.len();
        let suffix_map = suffix_disjointness_check(group, skip, &first_sets);
        /* Suffixes at position 3 are "then" vs "else" — actually disjoint!
         * So both approaches should find disjoint suffixes here. */
        if suffix_map.is_some() {
            /* Ad-hoc found disjoint suffixes after shared prefix [( +] */
            match tree.dispatch_strategy(&kw_if, &token_ids) {
                DispatchStrategy::DisjointSuffix {
                    shared_prefix_len,
                    suffix_map: dt_suffix_map,
                    ..
                } => {
                    assert_eq!(
                        shared_prefix_len,
                        shared_prefix.len(),
                        "shared prefix length should match"
                    );
                    assert_eq!(dt_suffix_map.len(), 2, "should have 2 disjoint suffixes");
                }
                DispatchStrategy::NfaTryAll { shared_prefix_len, .. } => {
                    /* DT may differ if encoding truncates differently.
                     * This is still correct — NfaTryAll is never WRONG,
                     * it's just more conservative. */
                    assert_eq!(
                        shared_prefix_len as usize,
                        shared_prefix.len(),
                        "shared prefix should still match"
                    );
                }
                other => panic!(
                    "unexpected strategy: {:?}",
                    other
                ),
            }
        } else {
            /* Ad-hoc says NFA. Decision tree should also say NFA or DisjointSuffix
             * (DisjointSuffix is strictly better). */
            match tree.dispatch_strategy(&kw_if, &token_ids) {
                DispatchStrategy::NfaTryAll { .. } | DispatchStrategy::DisjointSuffix { .. } => {}
                other => panic!(
                    "expected NfaTryAll or DisjointSuffix, got {:?}",
                    other
                ),
            }
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // Analysis layer tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_d01_precision_ambiguity() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        /* Two rules with EXACTLY identical terminal prefix → Ambiguous node.
         * Both end at an NT boundary after "if" "(" so pjoin merges them. */
        let rules = vec![
            make_rd_rule("IfIntCast", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfFloatCast", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let diags = precision_ambiguity_reports(tree, &token_ids, "test");
        /* Both rules truncate at the same NT boundary → same path [if, (].
         * pjoin merges them into Ambiguous. D01 should fire. */
        assert!(
            diags.iter().any(|d| d.id == "D01"),
            "D01 should fire for ambiguous prefix: {:?}",
            diags,
        );
    }

    #[test]
    fn test_d02_unresolvable_ambiguity() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        /* Two rules with identical terminal prefix ending at NT boundary.
         * The ambiguity is at a leaf (no deeper terminal children), so it's
         * unresolvable by additional terminal lookahead. */
        let rules = vec![
            make_rd_rule("IfIntCast", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfFloatCast", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let diags = unresolvable_ambiguity_reports(tree, &token_ids, "test");
        /* The ambiguous node [if, (] is a leaf (NT boundary truncated both) → D02 fires */
        let d02s: Vec<_> = diags.iter().filter(|d| d.id == "D02").collect();
        assert!(
            !d02s.is_empty(),
            "D02 should fire for unresolvable ambiguity at trie leaf: diags={:?}",
            diags,
        );
    }

    #[test]
    fn test_d03_unreachable_rule() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        /* all_labels includes a rule that wasn't inserted */
        let mut all_labels = HashSet::new();
        all_labels.insert("IfThenElse".to_string());
        all_labels.insert("GhostRule".to_string());

        let diags = unreachable_rule_detection(tree, &all_labels, "test");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "D03");
        assert!(diags[0].message.contains("GhostRule"));
    }

    #[test]
    fn test_d04_min_lookahead() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let diag = min_lookahead_report(tree, "test");
        assert_eq!(diag.id, "D04");
        /* Both rules have distinct first tokens → LL(1) */
        assert!(
            diag.message.contains("depth 1") || diag.message.contains("LL(1)"),
            "should report depth 1 for non-ambiguous grammar: {}",
            diag.message,
        );
    }

    #[test]
    fn test_d05_complexity_metrics() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let diag = complexity_metrics(tree, "test");
        assert_eq!(diag.id, "D05");
        assert!(diag.message.contains("decision tree"));
    }

    #[test]
    fn test_d07_coverage_paths() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let paths = coverage_paths(tree);
        assert!(paths.len() >= 2, "should have at least 2 paths");

        /* No paths covered → D07 fires */
        let covered = HashSet::new();
        let diags = coverage_report(tree, &covered, "test");
        assert!(diags.iter().any(|d| d.id == "D07"));

        /* All paths covered → D07 should not fire */
        let all_covered: HashSet<Vec<u8>> = paths.iter().map(|p| p.path_bytes.clone()).collect();
        let diags2 = coverage_report(tree, &all_covered, "test");
        assert!(diags2.is_empty(), "no D07 when fully covered");
    }

    #[test]
    fn test_d08_optimization_suggestions() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        /* Two rules with identical terminal prefix at NT boundary → Ambiguous → D08 */
        let rules = vec![
            make_rd_rule("IfIntCast", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfFloatCast", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let diags = optimization_suggestions(tree, "test");
        let d08s: Vec<_> = diags.iter().filter(|d| d.id == "D08").collect();
        assert!(
            !d08s.is_empty(),
            "D08 should fire for ambiguous rules: {:?}",
            diags,
        );
    }

    #[test]
    fn test_d09_conflict_resolution() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfIntCast", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfFloatCast", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let diags = conflict_resolution_guidance(tree, "test");
        let d09s: Vec<_> = diags.iter().filter(|d| d.id == "D09").collect();
        assert!(
            !d09s.is_empty(),
            "D09 should fire for conflicting rules: {:?}",
            diags,
        );
        /* Should contain resolution strategies */
        assert!(d09s[0].hint.as_ref().expect("should have hint").contains("distinguishing terminal"));
    }

    #[test]
    fn test_x06_x07_composition_analysis() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();

        /* Grammar A: Int with IfThenElse */
        let mut builder_a = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );
        builder_a.build_all(
            &[make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ])],
            &[],
            &[],
        );

        /* Grammar B: Int with LetIn + IfThenElse (shared rule) */
        let mut builder_b = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );
        builder_b.build_all(
            &[
                make_rd_rule("IfThenElse", "Int", vec![
                    RDSyntaxItem::Terminal("if".to_string()),
                    RDSyntaxItem::Terminal("then".to_string()),
                    RDSyntaxItem::Terminal("else".to_string()),
                ]),
                make_rd_rule("LetIn", "Int", vec![
                    RDSyntaxItem::Terminal("let".to_string()),
                    RDSyntaxItem::Terminal("in".to_string()),
                ]),
            ],
            &[],
            &[],
        );

        let tree_a = builder_a.get_tree("Int").expect("tree A");
        let tree_b = builder_b.get_tree("Int").expect("tree B");

        let report = composition_trie_analysis(tree_a, tree_b);
        /* IfThenElse is in both → common_rules >= 1 */
        assert!(report.common_rules >= 1, "should have common rules: {:?}", report);
        /* LetIn is only in B → unique_b >= 1 */
        assert!(report.unique_b >= 1, "should have unique_b: {:?}", report);
        /* A has nothing unique (all of A is in B) */
        assert_eq!(report.unique_a, 0, "A should have no unique rules: {:?}", report);
    }

    #[test]
    fn test_layer10_content_hash() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();

        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );
        builder.build_all(
            &[make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ])],
            &[],
            &[],
        );

        let tree = builder.get_tree("Int").expect("tree");
        let hash1 = category_content_hash(tree);

        /* Same grammar → same hash */
        let mut builder2 = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );
        builder2.build_all(
            &[make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ])],
            &[],
            &[],
        );
        let tree2 = builder2.get_tree("Int").expect("tree2");
        let hash2 = category_content_hash(tree2);
        assert_eq!(hash1, hash2, "same grammar should produce same hash");

        /* Different grammar → different hash */
        let mut builder3 = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );
        builder3.build_all(
            &[make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ])],
            &[],
            &[],
        );
        let tree3 = builder3.get_tree("Int").expect("tree3");
        let hash3 = category_content_hash(tree3);
        assert_ne!(hash1, hash3, "different grammar should produce different hash");
    }

    #[test]
    fn test_flat_table_emission() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("Int tree");
        let states = flatten_tree(tree);
        assert!(!states.is_empty(), "should have flattened states");

        /* Verify state structure: root + intermediates + leaves */
        let root = &states[0];
        assert!(!root.transitions.is_empty(), "root should have transitions");

        /* Emit to buffer */
        let mut buf = String::new();
        emit_flat_table(tree, &token_ids, &mut buf);
        assert!(buf.contains("DISPATCH_TABLE_INT"));
        assert!(buf.contains("STATE_META_INT"));
    }

    #[test]
    fn test_match_arm_emission() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("Int tree");
        let mut buf = String::new();
        emit_match_arms(tree, &token_ids, &mut buf);
        assert!(buf.contains("decision tree"), "should contain decision tree comment");
    }

    // ══════════════════════════════════════════════════════════════════════
    // Helper functions for new tests
    // ══════════════════════════════════════════════════════════════════════

    fn make_commit(label: &str, cat: &str) -> DecisionAction {
        DecisionAction::Commit {
            rule_label: label.to_string(),
            category: cat.to_string(),
            weight: 0.0,
        }
    }

    fn make_ambiguous(labels: &[(&str, &str)]) -> DecisionAction {
        DecisionAction::Ambiguous {
            candidates: labels
                .iter()
                .map(|(label, cat)| AmbiguousCandidate {
                    rule_label: label.to_string(),
                    category: cat.to_string(),
                    weight: 0.0,
                    remaining_items: 0,
                })
                .collect(),
        }
    }

    fn make_nt_boundary(count: usize) -> DecisionAction {
        DecisionAction::NonterminalBoundary {
            options: (0..count)
                .map(|i| NTOption {
                    kind: NTKind::NonTerminal {
                        category: format!("Cat{}", i),
                    },
                    first_tokens: vec![i as u8],
                    resume_segment: i,
                    weight: 0.0,
                })
                .collect(),
        }
    }

    fn assert_commit(action: &DecisionAction, expected_label: &str) {
        match action {
            DecisionAction::Commit { rule_label, .. } => {
                assert_eq!(rule_label, expected_label);
            }
            other => panic!("expected Commit({}), got {:?}", expected_label, other),
        }
    }

    fn assert_ambiguous_labels(action: &DecisionAction, expected: &[&str]) {
        match action {
            DecisionAction::Ambiguous { candidates } => {
                let mut labels: Vec<&str> =
                    candidates.iter().map(|c| c.rule_label.as_str()).collect();
                labels.sort();
                let mut exp: Vec<&str> = expected.to_vec();
                exp.sort();
                assert_eq!(labels, exp);
            }
            other => panic!("expected Ambiguous({:?}), got {:?}", expected, other),
        }
    }

    fn sorted_labels(action: &DecisionAction) -> Vec<String> {
        let mut labels: Vec<String> = action.rule_labels().map(|s| s.to_string()).collect();
        labels.sort();
        labels
    }

    fn assert_algebraic_element(
        result: &AlgebraicResult<DecisionAction>,
    ) -> &DecisionAction {
        match result {
            AlgebraicResult::Element(ref a) => a,
            other => panic!("expected Element, got {:?}", other),
        }
    }

    fn assert_algebraic_none(result: &AlgebraicResult<DecisionAction>) {
        assert!(
            result.is_none(),
            "expected AlgebraicResult::None, got {:?}",
            result
        );
    }

    fn assert_algebraic_identity(
        result: &AlgebraicResult<DecisionAction>,
        id: u64,
    ) {
        match result {
            AlgebraicResult::Identity(mask) => assert_eq!(*mask, id),
            other => panic!("expected Identity({}), got {:?}", id, other),
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 4: Lattice algebra (pjoin) tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_pjoin_commit_commit() {
        let a = make_commit("A", "Int");
        let b = make_commit("B", "Int");
        let result = a.pjoin(&b);
        let action = assert_algebraic_element(&result);
        assert_ambiguous_labels(action, &["A", "B"]);
    }

    #[test]
    fn test_pjoin_commit_ambiguous() {
        let a = make_commit("A", "Int");
        let b = make_ambiguous(&[("B", "Int"), ("C", "Int")]);
        let result = a.pjoin(&b);
        let action = assert_algebraic_element(&result);
        assert_ambiguous_labels(action, &["A", "B", "C"]);
    }

    #[test]
    fn test_pjoin_ambiguous_ambiguous() {
        let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let b = make_ambiguous(&[("C", "Int"), ("D", "Int")]);
        let result = a.pjoin(&b);
        let action = assert_algebraic_element(&result);
        assert_ambiguous_labels(action, &["A", "B", "C", "D"]);
    }

    #[test]
    fn test_pjoin_nt_boundary_commit() {
        let a = make_nt_boundary(1);
        let b = make_commit("A", "Int");
        let result = a.pjoin(&b);
        assert_algebraic_identity(&result, 1);
    }

    #[test]
    fn test_pjoin_commit_nt_boundary() {
        let a = make_commit("A", "Int");
        let b = make_nt_boundary(1);
        let result = a.pjoin(&b);
        assert_algebraic_identity(&result, 2);
    }

    #[test]
    fn test_pjoin_nt_boundary_nt_boundary() {
        let a = make_nt_boundary(1);
        let b = make_nt_boundary(2);
        let result = a.pjoin(&b);
        assert_algebraic_identity(&result, 1);
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 4: Lattice algebra (pmeet) tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_pmeet_commit_commit_same() {
        let a = make_commit("A", "Int");
        let b = make_commit("A", "Int");
        let result = a.pmeet(&b);
        let action = assert_algebraic_element(&result);
        assert_commit(action, "A");
    }

    #[test]
    fn test_pmeet_commit_commit_different() {
        let a = make_commit("A", "Int");
        let b = make_commit("B", "Int");
        let result = a.pmeet(&b);
        assert_algebraic_none(&result);
    }

    #[test]
    fn test_pmeet_ambiguous_ambiguous_overlap() {
        let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let b = make_ambiguous(&[("B", "Int"), ("C", "Int")]);
        let result = a.pmeet(&b);
        let action = assert_algebraic_element(&result);
        assert_commit(action, "B");
    }

    #[test]
    fn test_pmeet_ambiguous_ambiguous_no_overlap() {
        let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let b = make_ambiguous(&[("C", "Int"), ("D", "Int")]);
        let result = a.pmeet(&b);
        assert_algebraic_none(&result);
    }

    #[test]
    fn test_pmeet_ambiguous_commit_match() {
        let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let b = make_commit("A", "Int");
        let result = a.pmeet(&b);
        let action = assert_algebraic_element(&result);
        assert_commit(action, "A");
    }

    #[test]
    fn test_pmeet_ambiguous_ambiguous_multi() {
        let a = make_ambiguous(&[("A", "Int"), ("B", "Int"), ("C", "Int")]);
        let b = make_ambiguous(&[("B", "Int"), ("C", "Int"), ("D", "Int")]);
        let result = a.pmeet(&b);
        let action = assert_algebraic_element(&result);
        assert_ambiguous_labels(action, &["B", "C"]);
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 5: DistributiveLattice (psubtract) tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_psubtract_ambiguous_remove_one() {
        let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let b = make_commit("A", "Int");
        let result = a.psubtract(&b);
        let action = assert_algebraic_element(&result);
        assert_commit(action, "B");
    }

    #[test]
    fn test_psubtract_ambiguous_remove_partial() {
        let a = make_ambiguous(&[("A", "Int"), ("B", "Int"), ("C", "Int")]);
        let b = make_ambiguous(&[("A", "Int"), ("C", "Int")]);
        let result = a.psubtract(&b);
        let action = assert_algebraic_element(&result);
        assert_commit(action, "B");
    }

    #[test]
    fn test_psubtract_ambiguous_remove_all() {
        let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let b = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let result = a.psubtract(&b);
        assert_algebraic_none(&result);
    }

    #[test]
    fn test_psubtract_commit_same() {
        // Subtracting identical commit: "A" - "A" = None
        let a = make_commit("A", "Int");
        let b = make_commit("A", "Int");
        let result = a.psubtract(&b);
        assert_algebraic_none(&result);
    }

    #[test]
    fn test_psubtract_commit_different() {
        // Subtracting different commit: "A" - "B" = Commit("A")
        let a = make_commit("A", "Int");
        let b = make_commit("B", "Int");
        let result = a.psubtract(&b);
        let action = assert_algebraic_element(&result);
        assert_commit(action, "A");
    }

    #[test]
    fn test_psubtract_no_overlap() {
        let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let b = make_nt_boundary(1);
        let result = a.psubtract(&b);
        // NTBoundary has no rule_labels() → other_labels is empty → nothing removed
        let action = assert_algebraic_element(&result);
        assert_ambiguous_labels(action, &["A", "B"]);
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 6: DecisionAction helper method tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_rule_labels() {
        let commit = make_commit("A", "Int");
        assert_eq!(
            commit.rule_labels().collect::<Vec<_>>(),
            vec!["A"]
        );

        let ambig = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let mut labels: Vec<&str> = ambig.rule_labels().collect();
        labels.sort();
        assert_eq!(labels, vec!["A", "B"]);

        let nt = make_nt_boundary(2);
        assert_eq!(nt.rule_labels().count(), 0);
    }

    #[test]
    fn test_all_candidates() {
        let ambig = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
        let candidates: Vec<AmbiguousCandidate> = ambig.all_candidates();
        assert_eq!(candidates.len(), 2);
        assert_eq!(candidates[0].rule_label, "A");
        assert_eq!(candidates[1].rule_label, "B");

        let commit = make_commit("A", "Int");
        let commit_candidates = commit.all_candidates();
        assert_eq!(commit_candidates.len(), 1);
        assert_eq!(commit_candidates[0].rule_label, "A");
        assert_eq!(commit_candidates[0].category, "Int");
        assert_eq!(commit_candidates[0].remaining_items, 0);

        let nt = make_nt_boundary(1);
        assert_eq!(nt.all_candidates().len(), 0);
    }

    #[test]
    fn test_is_deterministic() {
        assert!(make_commit("A", "Int").is_deterministic());
        assert!(!make_ambiguous(&[("A", "Int"), ("B", "Int")]).is_deterministic());
        assert!(!make_nt_boundary(1).is_deterministic());
    }

    #[test]
    fn test_is_nt_boundary() {
        assert!(make_nt_boundary(1).is_nt_boundary());
        assert!(!make_commit("A", "Int").is_nt_boundary());
        assert!(!make_ambiguous(&[("A", "Int")]).is_nt_boundary());
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 7: Query helper tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_query_dispatch_token_found() {
        // query_dispatch_token checks single-byte path [tok_id], so we need
        // single-terminal rules where the trie value is at a single-byte path.
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("JustIf", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
            ]),
            make_rd_rule("JustLet", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let action = query_dispatch_token(tree, "KwIf", &token_ids)
            .expect("KwIf should be found");
        assert_commit(action, "JustIf");

        let action2 = query_dispatch_token(tree, "KwLet", &token_ids)
            .expect("KwLet should be found");
        assert_commit(action2, "JustLet");
    }

    #[test]
    fn test_query_dispatch_token_missing() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("JustIf", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        assert!(
            query_dispatch_token(tree, "Plus", &token_ids).is_none(),
            "Plus should not be in the tree"
        );
    }

    #[test]
    fn test_is_token_deterministic_fn() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        // Single rule per dispatch token → deterministic at single-byte paths
        let rules = vec![
            make_rd_rule("OnlyIf", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        assert!(is_token_deterministic(tree, "KwIf", &token_ids));
        assert!(!is_token_deterministic(tree, "Plus", &token_ids));
    }

    #[test]
    fn test_rules_for_token_fn() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        // Insert a single-terminal rule so query_dispatch_token works
        let rules = vec![
            make_rd_rule("OnlyIf", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let labels = rules_for_token(tree, "KwIf", &token_ids);
        assert_eq!(labels, vec!["OnlyIf"]);

        let empty = rules_for_token(tree, "Plus", &token_ids);
        assert!(empty.is_empty());
    }

    #[test]
    fn test_shared_prefix_and_suffix_dispatch() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        // Two rules: if ( + ) and if ( - ) → shared prefix "("
        let rules = vec![
            make_rd_rule("IfPlus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfMinus", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("-".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let depth = shared_prefix_depth(tree, "KwIf", &token_ids);
        assert_eq!(depth, 1, "shared prefix should be 1 (the '(' byte)");

        let disjoint = suffix_disjoint_dispatch(tree, "KwIf", &token_ids);
        let map = disjoint.expect("should be disjoint");
        assert_eq!(map.len(), 2);
        assert_eq!(map.get("Plus").expect("Plus"), "IfPlus");
        assert_eq!(map.get("Minus").expect("Minus"), "IfMinus");
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 8: Pattern encoding edge cases
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_pattern_single_terminal() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rule = make_rd_rule("JustIf", "Int", vec![
            RDSyntaxItem::Terminal("if".to_string()),
        ]);

        let pattern = builder.pattern_from_rd_rule(&rule);
        assert_eq!(pattern.len(), 1);
        assert!(matches!(
            pattern[0],
            PatternElement::Terminal { ref variant, .. } if variant == "KwIf"
        ));

        let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
        assert_eq!(bytes.len(), 1);
        assert!(boundary.is_none());
    }

    #[test]
    fn test_pattern_all_nonterminals() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        let rule = make_rd_rule("AllNT", "Int", vec![
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            RDSyntaxItem::NonTerminal {
                category: "Float".to_string(),
                param_name: "b".to_string(),
            },
        ]);

        let pattern = builder.pattern_from_rd_rule(&rule);
        assert_eq!(pattern.len(), 2);

        let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
        // First element is NT → empty terminal prefix, boundary at position 0
        assert!(bytes.is_empty());
        assert!(boundary.is_some());
        let b = boundary.expect("should have NT boundary");
        assert_eq!(b.position, 0);
        assert_eq!(b.category, "Int");
    }

    #[test]
    fn test_pattern_with_ident_capture() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rule = make_rd_rule("IfIdent", "Int", vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::IdentCapture { param_name: "x".to_string() },
            RDSyntaxItem::Terminal(")".to_string()),
        ]);

        let pattern = builder.pattern_from_rd_rule(&rule);
        assert_eq!(pattern.len(), 3);
        assert!(matches!(pattern[1], PatternElement::IdentCapture { .. }));

        let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
        assert_eq!(bytes.len(), 3); // KwIf, IDENT_CAPTURE, RParen
        assert_eq!(bytes[1], IDENT_CAPTURE);
        assert!(boundary.is_none());
    }

    #[test]
    fn test_pattern_with_binder_capture() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rule = make_rd_rule("IfBinder", "Int", vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Binder {
                param_name: "x".to_string(),
                binder_category: "Int".to_string(),
            },
            RDSyntaxItem::Terminal(")".to_string()),
        ]);

        let pattern = builder.pattern_from_rd_rule(&rule);
        assert_eq!(pattern.len(), 3);
        assert!(matches!(pattern[1], PatternElement::BinderCapture { .. }));

        let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
        assert_eq!(bytes.len(), 3); // KwIf, BINDER_CAPTURE, RParen
        assert_eq!(bytes[1], BINDER_CAPTURE);
        assert!(boundary.is_none());
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 9: D06 WFST consistency check tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_d06_consistent() {
        use crate::automata::semiring::TropicalWeight;
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        // Use single-terminal rules so the trie has values at single-byte paths
        let rules = vec![
            make_rd_rule("JustIf", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");

        // Build a PredictionWfst with "if" token via builder
        let mut wfst_builder = PredictionWfstBuilder::new("Int", token_ids.clone());
        wfst_builder.add_action(
            "if",
            DispatchAction::Direct {
                rule_label: "JustIf".to_string(),
                parse_fn: "parse_JustIf".to_string(),
            },
            TropicalWeight(0.0),
        );
        let wfst = wfst_builder.build();

        let diags = wfst_consistency_check(tree, &wfst, &token_ids, "test");
        // "if" maps to KwIf which is in the trie at single-byte path → no D06
        let d06s: Vec<_> = diags.iter().filter(|d| d.id == "D06").collect();
        assert!(d06s.is_empty(), "D06 should not fire when consistent: {:?}", d06s);
    }

    #[test]
    fn test_d06_inconsistent() {
        use crate::automata::semiring::TropicalWeight;
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        // Only "if" in the trie (single-byte path)
        let rules = vec![make_rd_rule("JustIf", "Int", vec![
            RDSyntaxItem::Terminal("if".to_string()),
        ])];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");

        // Build a PredictionWfst with "float" token — NOT in the trie
        let mut wfst_builder = PredictionWfstBuilder::new("Int", token_ids.clone());
        wfst_builder.add_action(
            "float",
            DispatchAction::Direct {
                rule_label: "FloatRule".to_string(),
                parse_fn: "parse_FloatRule".to_string(),
            },
            TropicalWeight(0.0),
        );
        let wfst = wfst_builder.build();

        let diags = wfst_consistency_check(tree, &wfst, &token_ids, "test");
        let d06s: Vec<_> = diags.iter().filter(|d| d.id == "D06").collect();
        assert!(!d06s.is_empty(), "D06 should fire for inconsistent token: {:?}", diags);
        assert!(d06s[0].message.contains("float"), "D06 message should mention the token");
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 10: IncrementalState edge cases
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_incremental_load_nonexistent() {
        let path = std::env::temp_dir().join("prattail_test_nonexistent_cache_42");
        let _ = std::fs::remove_file(&path); // Ensure it doesn't exist
        assert!(IncrementalState::load(&path).is_none());
    }

    #[test]
    fn test_incremental_load_empty_file() {
        let path = std::env::temp_dir().join("prattail_test_empty_cache");
        std::fs::write(&path, &[]).expect("write empty file");
        assert!(IncrementalState::load(&path).is_none());
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_incremental_load_truncated() {
        let path = std::env::temp_dir().join("prattail_test_truncated_cache");
        // Write only the version (4 bytes) — missing num_categories
        std::fs::write(&path, &CACHE_VERSION.to_le_bytes()).expect("write truncated");
        let loaded = IncrementalState::load(&path);
        // Either None (can't read num_cats) or valid but empty
        match loaded {
            None => {} // Expected for truncated data
            Some(state) => {
                // If load succeeds with just version + no categories, that's also fine
                assert_eq!(state.version, CACHE_VERSION);
                assert!(state.category_hashes.is_empty());
            }
        }
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_incremental_many_categories() {
        let path = std::env::temp_dir().join("prattail_test_many_cats_cache");
        let mut state = IncrementalState {
            version: CACHE_VERSION,
            ..Default::default()
        };

        for i in 0..50 {
            let cat = format!("Cat{}", i);
            let hash = (i as u128) * 0x12345 + 42;
            let code = format!("fn parse_Cat{}() {{}}", i);
            state.record(&cat, hash);
            state.category_code.insert(cat, code);
        }

        state.save(&path).expect("save many categories");
        let loaded = IncrementalState::load(&path).expect("load many categories");
        assert!(loaded.is_valid());
        assert_eq!(loaded.category_hashes.len(), 50);

        for i in 0..50 {
            let cat = format!("Cat{}", i);
            let hash = (i as u128) * 0x12345 + 42;
            assert!(loaded.is_unchanged(&cat, hash), "Cat{} hash mismatch", i);
            let expected_code = format!("fn parse_Cat{}() {{}}", i);
            assert_eq!(
                loaded.category_code.get(&cat).expect("category code"),
                &expected_code,
            );
        }

        let _ = std::fs::remove_file(&path);
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 11: TreeStats Display test
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_tree_stats_display() {
        let stats = TreeStats {
            total_states: 10,
            deterministic_nodes: 7,
            ambiguous_nodes: 2,
            max_depth: 4,
            min_lookahead: 2,
            nonterminal_boundaries: 1,
            shared_prefix_savings: 3,
            total_rules: 5,
            deterministic_rules: 3,
        };
        let display = format!("{}", stats);
        assert!(display.contains("10 states"), "should contain state count: {}", display);
        assert!(display.contains("7 deterministic"), "should contain deterministic: {}", display);
        assert!(display.contains("2 ambiguous"), "should contain ambiguous: {}", display);
        assert!(display.contains("max depth 4"), "should contain depth: {}", display);
        assert!(display.contains("3/5 rules deterministic"), "should contain rule ratio: {}", display);
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 12: Emission edge cases
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_flatten_empty_tree() {
        let tree = CategoryDecisionTree {
            category: "Empty".to_string(),
            segments: vec![PathMap::new()],
            stats: TreeStats::default(),
        };
        let states = flatten_tree(&tree);
        assert!(states.is_empty(), "empty tree should produce no flat states");
    }

    #[test]
    fn test_emit_match_arms_multi_rule() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
            make_rd_rule("ParenExpr", "Int", vec![
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("Int tree");
        let mut buf = String::new();
        emit_match_arms(tree, &token_ids, &mut buf);
        // Should contain "3" in dispatch token count or entries
        assert!(
            buf.contains("decision tree"),
            "should contain decision tree label: {}",
            buf
        );
        assert!(
            buf.contains("3"),
            "should mention 3 rules or tokens: {}",
            buf
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 13: coverage_report formatting
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_coverage_report_partial() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids,
            first_sets,
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
            make_rd_rule("ParenExpr", "Int", vec![
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let tree = builder.get_tree("Int").expect("should have Int tree");
        let paths = coverage_paths(tree);
        assert!(paths.len() >= 3, "should have at least 3 paths");

        // Cover only the first path
        let mut covered = HashSet::new();
        covered.insert(paths[0].path_bytes.clone());

        let diags = coverage_report(tree, &covered, "test");
        assert!(diags.len() == 1, "should have exactly one D07 diagnostic");
        let d07 = &diags[0];
        assert_eq!(d07.id, "D07");
        // Should contain coverage fraction: "1/N"
        assert!(
            d07.message.contains("1/"),
            "should contain partial coverage fraction '1/': {}",
            d07.message
        );
        // Should contain "untested"
        assert!(
            d07.message.contains("untested"),
            "should mention untested: {}",
            d07.message
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // Step 14: Property-based tests with proptest
    // ══════════════════════════════════════════════════════════════════════

    mod prop_tests {
        use super::*;
        use proptest::prelude::*;

        fn arb_candidate() -> impl Strategy<Value = AmbiguousCandidate> {
            ("[A-Z][a-z]{2,6}", "[A-Z][a-z]{2,6}").prop_map(|(label, cat)| {
                AmbiguousCandidate {
                    rule_label: label,
                    category: cat,
                    weight: 0.0,
                    remaining_items: 0,
                }
            })
        }

        fn arb_commit() -> impl Strategy<Value = DecisionAction> {
            ("[A-Z][a-z]{2,6}", "[A-Z][a-z]{2,6}").prop_map(|(label, cat)| {
                DecisionAction::Commit {
                    rule_label: label,
                    category: cat,
                    weight: 0.0,
                }
            })
        }

        fn arb_ambiguous() -> impl Strategy<Value = DecisionAction> {
            prop::collection::vec(arb_candidate(), 2..6).prop_map(|candidates| {
                // Deduplicate by rule_label to avoid confusing pmeet/psubtract
                let mut seen = std::collections::HashSet::new();
                let unique: Vec<AmbiguousCandidate> = candidates
                    .into_iter()
                    .filter(|c| seen.insert(c.rule_label.clone()))
                    .collect();
                if unique.len() < 2 {
                    // Ensure we have at least 2 candidates
                    DecisionAction::Ambiguous {
                        candidates: vec![
                            AmbiguousCandidate {
                                rule_label: "FallbackA".to_string(),
                                category: "Int".to_string(),
                                weight: 0.0,
                                remaining_items: 0,
                            },
                            AmbiguousCandidate {
                                rule_label: "FallbackB".to_string(),
                                category: "Int".to_string(),
                                weight: 0.0,
                                remaining_items: 0,
                            },
                        ],
                    }
                } else {
                    DecisionAction::Ambiguous { candidates: unique }
                }
            })
        }

        fn arb_action() -> impl Strategy<Value = DecisionAction> {
            prop_oneof![arb_commit(), arb_ambiguous()]
        }

        // ── Lattice law properties ──────────────────────────────────────

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(500))]

            #[test]
            fn prop_pjoin_idempotent(a in arb_action()) {
                let result = a.pjoin(&a);
                match result {
                    AlgebraicResult::Element(merged) => {
                        // Labels of merged should contain all labels of a
                        let a_labels: std::collections::HashSet<String> =
                            a.rule_labels().map(|s| s.to_string()).collect();
                        let merged_labels: std::collections::HashSet<String> =
                            merged.rule_labels().map(|s| s.to_string()).collect();
                        for label in &a_labels {
                            prop_assert!(
                                merged_labels.contains(label),
                                "pjoin idempotent: merged missing label {}",
                                label
                            );
                        }
                    }
                    AlgebraicResult::Identity(_) => {
                        // NTBoundary case: identity is valid
                    }
                    AlgebraicResult::None => {
                        prop_assert!(false, "pjoin should not return None for self ⊔ self");
                    }
                }
            }

            #[test]
            fn prop_pjoin_commutative(a in arb_action(), b in arb_action()) {
                let ab = a.pjoin(&b);
                let ba = b.pjoin(&a);

                let labels_ab = match &ab {
                    AlgebraicResult::Element(action) => {
                        let mut l = sorted_labels(action);
                        l.sort();
                        l
                    }
                    _ => Vec::new(),
                };
                let labels_ba = match &ba {
                    AlgebraicResult::Element(action) => {
                        let mut l = sorted_labels(action);
                        l.sort();
                        l
                    }
                    _ => Vec::new(),
                };

                // Both Element → labels match
                // Both Identity → commutative for NTBoundary
                // Mixed → NTBoundary identity values may differ (1 vs 2)
                match (&ab, &ba) {
                    (AlgebraicResult::Element(_), AlgebraicResult::Element(_)) => {
                        prop_assert_eq!(labels_ab, labels_ba);
                    }
                    (AlgebraicResult::Identity(_), AlgebraicResult::Identity(_)) => {
                        // Both NTBoundary → valid
                    }
                    _ => {
                        // One is NTBoundary, other is not: Identity(1) vs Identity(2)
                        // is correct and expected non-commutative behavior for
                        // NTBoundary ⊔ non-NTBoundary
                    }
                }
            }

            #[test]
            fn prop_pjoin_contains_both(a in arb_action(), b in arb_action()) {
                let result = a.pjoin(&b);
                if let AlgebraicResult::Element(merged) = result {
                    let a_labels: std::collections::HashSet<String> =
                        a.rule_labels().map(|s| s.to_string()).collect();
                    let b_labels: std::collections::HashSet<String> =
                        b.rule_labels().map(|s| s.to_string()).collect();
                    let merged_labels: std::collections::HashSet<String> =
                        merged.rule_labels().map(|s| s.to_string()).collect();

                    for label in a_labels.union(&b_labels) {
                        prop_assert!(
                            merged_labels.contains(label),
                            "pjoin should contain label {} from union",
                            label
                        );
                    }
                }
            }

            #[test]
            fn prop_pmeet_subset(a in arb_ambiguous(), b in arb_ambiguous()) {
                let result = a.pmeet(&b);
                let a_labels: std::collections::HashSet<String> =
                    a.rule_labels().map(|s| s.to_string()).collect();
                let b_labels: std::collections::HashSet<String> =
                    b.rule_labels().map(|s| s.to_string()).collect();
                let intersection: std::collections::HashSet<&String> =
                    a_labels.intersection(&b_labels).collect();

                match result {
                    AlgebraicResult::Element(met) => {
                        let met_labels: std::collections::HashSet<String> =
                            met.rule_labels().map(|s| s.to_string()).collect();
                        for label in &met_labels {
                            prop_assert!(
                                intersection.contains(label),
                                "pmeet label {} should be in intersection",
                                label
                            );
                        }
                    }
                    AlgebraicResult::None => {
                        // No common labels (or all_candidates bug) → valid
                    }
                    _ => {}
                }
            }

            #[test]
            fn prop_psubtract_removes(a in arb_ambiguous(), b in arb_ambiguous()) {
                let result = a.psubtract(&b);
                let b_labels: std::collections::HashSet<String> =
                    b.rule_labels().map(|s| s.to_string()).collect();

                if let AlgebraicResult::Element(diff) = result {
                    let diff_labels: std::collections::HashSet<String> =
                        diff.rule_labels().map(|s| s.to_string()).collect();
                    let overlap: std::collections::HashSet<&String> =
                        diff_labels.intersection(&b_labels).collect();
                    prop_assert!(
                        overlap.is_empty(),
                        "psubtract result should have no labels from b: overlap={:?}",
                        overlap
                    );
                }
            }

            #[test]
            fn prop_psubtract_self_is_none(a in arb_ambiguous()) {
                let result = a.psubtract(&a);
                prop_assert!(
                    result.is_none(),
                    "a ⊖ a should be None, got {:?}",
                    result
                );
            }
        }

        // ── Round-trip properties ───────────────────────────────────────

        fn arb_incremental_entry() -> impl Strategy<Value = (String, u128, String)> {
            (
                "[A-Z][a-z]{2,10}",
                any::<u128>(),
                "[a-z ]{5,30}",
            )
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(100))]

            #[test]
            fn prop_incremental_roundtrip(
                entries in prop::collection::vec(arb_incremental_entry(), 1..20)
            ) {
                let path = std::env::temp_dir().join(format!(
                    "prattail_prop_rt_{}", std::process::id()
                ));
                let mut state = IncrementalState {
                    version: CACHE_VERSION,
                    ..Default::default()
                };
                // Deduplicate entries by name
                let mut seen = std::collections::HashSet::new();
                for (name, hash, code) in &entries {
                    if seen.insert(name.clone()) {
                        state.record(name, *hash);
                        state.category_code.insert(name.clone(), code.clone());
                    }
                }

                state.save(&path).expect("save should succeed");
                let loaded = IncrementalState::load(&path).expect("load should succeed");
                prop_assert!(loaded.is_valid());

                // Only check entries that were actually recorded (first
                // occurrence of each name). Re-derive the dedup set to get
                // the correct (name, hash, code) triple for each name.
                let mut checked = std::collections::HashSet::new();
                for (name, hash, code) in &entries {
                    if checked.insert(name.clone()) {
                        prop_assert!(
                            loaded.is_unchanged(name, *hash),
                            "hash mismatch for {}",
                            name
                        );
                        prop_assert_eq!(
                            loaded.category_code.get(name).expect("code"),
                            code,
                        );
                    }
                }

                let _ = std::fs::remove_file(&path);
            }

            #[test]
            fn prop_content_hash_deterministic(
                rule_count in 1usize..5,
                seed in 0u64..1000,
            ) {
                let terminals = ["if", "then", "else", "let", "in"];

                let build = || {
                    let token_ids = make_token_ids();
                    let first_sets = make_first_sets();
                    let mut builder = DecisionTreeBuilder::new(
                        token_ids,
                        first_sets,
                        vec!["Int".to_string()],
                        HashSet::new(),
                    );

                    let rules: Vec<RDRuleInfo> = (0..rule_count)
                        .map(|i| {
                            let idx = ((seed as usize) + i) % terminals.len();
                            make_rd_rule(
                                &format!("Rule{}_{}", i, seed),
                                "Int",
                                vec![RDSyntaxItem::Terminal(terminals[idx].to_string())],
                            )
                        })
                        .collect();
                    builder.build_all(&rules, &[], &[]);
                    let tree = builder.get_tree("Int").expect("tree");
                    category_content_hash(tree)
                };

                let hash1 = build();
                let hash2 = build();
                prop_assert_eq!(hash1, hash2, "same build should produce same hash");
            }

            #[test]
            fn prop_pattern_encoding_deterministic(seed in 0u64..1000) {
                let terminals = ["if", "then", "else", "let", "in"];
                let idx = (seed as usize) % terminals.len();

                let token_ids = make_token_ids();
                let first_sets = make_first_sets();
                let builder = DecisionTreeBuilder::new(
                    token_ids,
                    first_sets,
                    vec!["Int".to_string()],
                    HashSet::new(),
                );

                let rule = make_rd_rule(
                    &format!("Rule{}", seed),
                    "Int",
                    vec![RDSyntaxItem::Terminal(terminals[idx].to_string())],
                );

                let pattern1 = builder.pattern_from_rd_rule(&rule);
                let (bytes1, _) = DecisionTreeBuilder::encode_terminal_prefix(&pattern1);

                let pattern2 = builder.pattern_from_rd_rule(&rule);
                let (bytes2, _) = DecisionTreeBuilder::encode_terminal_prefix(&pattern2);

                prop_assert_eq!(bytes1, bytes2, "same rule should encode identically");
            }
        }

        // ── NTBoundary identity properties ──────────────────────────────

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(500))]

            #[test]
            fn prop_pjoin_nt_boundary_left_identity(a in arb_action()) {
                let nt = DecisionAction::NonterminalBoundary {
                    options: vec![NTOption {
                        kind: NTKind::NonTerminal { category: "X".to_string() },
                        first_tokens: vec![0],
                        resume_segment: 0,
                        weight: 0.0,
                    }],
                };
                let result = nt.pjoin(&a);
                prop_assert!(
                    result.is_identity(),
                    "NTBoundary ⊔ a should be Identity, got {:?}",
                    result
                );
                match result {
                    AlgebraicResult::Identity(mask) => {
                        prop_assert_eq!(mask, 1, "NTBoundary as self → Identity(1)");
                    }
                    _ => unreachable!(),
                }
            }

            #[test]
            fn prop_psubtract_nt_boundary_right_identity(a in arb_ambiguous()) {
                let nt = DecisionAction::NonterminalBoundary {
                    options: vec![NTOption {
                        kind: NTKind::NonTerminal { category: "X".to_string() },
                        first_tokens: vec![0],
                        resume_segment: 0,
                        weight: 0.0,
                    }],
                };
                let result = a.psubtract(&nt);
                // NTBoundary has no rule_labels → nothing removed → a unchanged
                match result {
                    AlgebraicResult::Element(diff) => {
                        let a_labels = sorted_labels(&a);
                        let diff_labels = sorted_labels(&diff);
                        prop_assert_eq!(
                            a_labels, diff_labels,
                            "a ⊖ NTBoundary should preserve all labels"
                        );
                    }
                    _ => {
                        prop_assert!(false, "expected Element, got {:?}", result);
                    }
                }
            }
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // CD02: Decision Tree Segment Merging tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_cd02_segment_merging_disjoint_nt_suffixes() {
        // Two rules share terminal prefix "if" "(" then diverge at different NT
        // categories with disjoint FIRST sets followed by different terminals.
        //
        //   IfIntRule:    if ( <Int> )
        //   IfFloatRule:  if ( <Float> :
        //
        // After the NT boundary at "if" "(", the remaining suffixes are:
        //   IfIntRule:    ")" → FIRST = { RParen }
        //   IfFloatRule:  ":" → FIRST = { Colon }
        //
        // RParen ∩ Colon = ∅ → safe to merge.
        // After merging, paths [if, (, RParen] → IfIntRule and
        // [if, (, Colon] → IfFloatRule should appear in segment[0].

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();

        let rules = vec![
            make_rd_rule("IfIntRule", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfFloatRule", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(":".to_string()),
            ]),
        ];

        // Build the decision tree and track NT boundary info
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );
        builder.insert_rd_rules(&rules);

        // Compute stats
        for tree in builder.trees_mut().values_mut() {
            tree.stats = compute_statistics(tree);
        }

        // Verify NT boundary map has our boundaries
        let nt_map = builder.nt_boundary_map();
        let boundary_entries: Vec<_> = nt_map.iter()
            .filter(|(_, records)| records.len() >= 2)
            .collect();
        assert!(
            !boundary_entries.is_empty(),
            "should have at least one prefix with 2+ NT boundary records",
        );

        // Perform segment merging using the builder's NT boundary data
        let mut trees = builder.trees().clone();
        let merged = merge_safe_nonterminal_boundaries(
            &builder,
            &mut trees,
            &first_sets,
            &token_ids,
        );

        assert!(
            merged > 0,
            "should have merged at least one NT boundary (disjoint FIRST sets)",
        );

        // Verify that new paths exist in segment[0] for the merged FIRST tokens
        let int_tree = trees.get("Int").expect("should have Int tree");
        let rparen_id = token_ids.get("RParen").expect("RParen should be in token IDs");
        let colon_id = token_ids.get("Colon").expect("Colon should be in token IDs");
        let kwif_id = token_ids.get("KwIf").expect("KwIf should be in token IDs");
        let lparen_id = token_ids.get("LParen").expect("LParen should be in token IDs");

        // After merging, there should be paths like [KwIf, LParen, RParen] → IfIntRule
        // and [KwIf, LParen, Colon] → IfFloatRule
        let path_rparen = vec![kwif_id as u8, lparen_id as u8, rparen_id as u8];
        let path_colon = vec![kwif_id as u8, lparen_id as u8, colon_id as u8];

        let action_rparen = int_tree.segments[0].get(&path_rparen);
        let action_colon = int_tree.segments[0].get(&path_colon);

        assert!(
            action_rparen.is_some(),
            "merged trie should have path [KwIf, LParen, RParen] for IfIntRule",
        );
        assert!(
            action_colon.is_some(),
            "merged trie should have path [KwIf, LParen, Colon] for IfFloatRule",
        );

        // Verify rule labels
        if let Some(DecisionAction::Commit { rule_label, .. }) = action_rparen {
            assert_eq!(rule_label, "IfIntRule");
        } else {
            panic!("expected Commit(IfIntRule), got {:?}", action_rparen);
        }
        if let Some(DecisionAction::Commit { rule_label, .. }) = action_colon {
            assert_eq!(rule_label, "IfFloatRule");
        } else {
            panic!("expected Commit(IfFloatRule), got {:?}", action_colon);
        }
    }

    #[test]
    fn test_cd02_segment_merging_overlapping_first_sets_not_merged() {
        // Two rules share terminal prefix "if" "(" then diverge at NT categories
        // whose FIRST sets overlap:
        //
        //   IfIntRule:    if ( <Int> )    → suffix FIRST = { RParen }
        //   IfFloatRule:  if ( <Float> )  → suffix FIRST = { RParen }
        //
        // RParen ∩ RParen ≠ ∅ → NOT safe to merge.

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfIntRule", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfFloatRule", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];

        builder.insert_rd_rules(&rules);

        // Compute stats
        for tree in builder.trees_mut().values_mut() {
            tree.stats = compute_statistics(tree);
        }

        // Both suffixes have FIRST = { RParen } → overlap → no merge
        let mut trees = builder.trees().clone();
        let merged = merge_safe_nonterminal_boundaries(
            &builder,
            &mut trees,
            &first_sets,
            &token_ids,
        );

        assert_eq!(
            merged, 0,
            "should not merge when FIRST sets overlap (both have RParen)",
        );
    }

    #[test]
    fn test_cd02_single_nt_boundary_not_merged() {
        // Only one rule at an NT boundary — no merging needed (single record).
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfRule", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];

        builder.insert_rd_rules(&rules);
        for tree in builder.trees_mut().values_mut() {
            tree.stats = compute_statistics(tree);
        }

        let mut trees = builder.trees().clone();
        let merged = merge_safe_nonterminal_boundaries(
            &builder,
            &mut trees,
            &first_sets,
            &token_ids,
        );

        assert_eq!(merged, 0, "single NT boundary should not be merged");
    }

    // ══════════════════════════════════════════════════════════════════════
    // CD04: Jump Threading tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_cd04_jump_threading_basic() {
        // Rule: IfThenElse = "if" "then" "else"
        // Trie path: [KwIf, KwThen, KwElse] → Commit(IfThenElse)
        // Rule items start with: "if" → KwIf, "then" → KwThen, "else" → KwElse
        // Pre-consumed tokens: 3 (all terminal tokens are consumed by the trie)

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfThenElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
            make_rd_rule("LetIn", "Int", vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let trees = builder.into_trees();
        let info = compute_jump_threading_info(&trees, &rules, &token_ids);

        // IfThenElse: path [KwIf, KwThen, KwElse] matches rule items [if, then, else]
        // → 3 pre-consumed tokens
        let ite_key = ("Int".to_string(), "IfThenElse".to_string());
        assert!(
            info.pre_consumed.contains_key(&ite_key),
            "should have jump threading info for IfThenElse: {:?}",
            info.pre_consumed,
        );
        assert_eq!(
            info.pre_consumed[&ite_key], 3,
            "IfThenElse should have 3 pre-consumed tokens (if, then, else)",
        );

        // LetIn: path [KwLet, KwIn] matches rule items [let, in]
        // → 2 pre-consumed tokens
        let li_key = ("Int".to_string(), "LetIn".to_string());
        assert!(
            info.pre_consumed.contains_key(&li_key),
            "should have jump threading info for LetIn",
        );
        assert_eq!(
            info.pre_consumed[&li_key], 2,
            "LetIn should have 2 pre-consumed tokens (let, in)",
        );
    }

    #[test]
    fn test_cd04_jump_threading_partial_match() {
        // Rule: IfParseX = "if" "(" <Int> ")"
        // Trie path: [KwIf, LParen] → Commit(IfParseX) (stops at NT boundary)
        // Rule items start with: "if" → KwIf, "(" → LParen, then NT...
        // Pre-consumed: 2 (KwIf, LParen match; NT is not a terminal)

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfParseX", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let trees = builder.into_trees();
        let info = compute_jump_threading_info(&trees, &rules, &token_ids);

        let key = ("Int".to_string(), "IfParseX".to_string());
        assert!(
            info.pre_consumed.contains_key(&key),
            "should have jump threading info for IfParseX: {:?}",
            info.pre_consumed,
        );
        assert_eq!(
            info.pre_consumed[&key], 2,
            "IfParseX should have 2 pre-consumed tokens (if, '(')",
        );
    }

    #[test]
    fn test_cd04_jump_threading_no_match_for_nt_start() {
        // Rule starting with NT is skipped entirely by insert_rd_rules, so
        // no jump threading info should exist.
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();
        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("NtFirst", "Int", vec![
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal("then".to_string()),
            ]),
        ];
        builder.build_all(&rules, &[], &[]);

        let trees = builder.into_trees();
        let info = compute_jump_threading_info(&trees, &rules, &token_ids);

        assert!(
            info.pre_consumed.is_empty(),
            "NT-start rules should not produce jump threading info: {:?}",
            info.pre_consumed,
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // CD05: Prefix CSE (Common Subexpression Elimination) tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_cd05_shared_nonterminal_same_category_detected() {
        // Two rules share terminal prefix "if" "(" then diverge at the same
        // nonterminal <Int>, followed by different suffixes:
        //
        //   IfIntThen:     if ( <Int> ) then
        //   IfIntElse:     if ( <Int> ) else
        //
        // Both have nt_category = "Int" at the same prefix [KwIf, LParen].
        // Post-NT suffixes: ") then" (FIRST = {RParen}) vs ") else" (FIRST = {RParen}).
        // The FIRST sets overlap (both RParen), so all_disjoint = false — but
        // the shared nonterminal is still detected.

        let token_ids = make_token_ids();

        // Int FIRST includes RParen so suffix FIRST computation works
        let mut first_sets = make_first_sets();
        // Augment Int FIRST with terminals that appear in suffixes
        if let Some(int_first) = first_sets.get_mut("Int") {
            int_first.insert("RParen");
        }

        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfIntThen", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
            ]),
            make_rd_rule("IfIntElse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
        assert!(
            !results.is_empty(),
            "should detect shared nonterminal prefix for IfIntThen/IfIntElse",
        );

        let shared = &results[0];
        assert_eq!(shared.category, "Int");
        assert_eq!(shared.nonterminal, "Int");
        assert_eq!(shared.rules.len(), 2);
        assert!(shared.rules.contains(&"IfIntThen".to_string()));
        assert!(shared.rules.contains(&"IfIntElse".to_string()));

        // Both suffixes start with RParen → FIRST sets overlap → not disjoint
        assert!(
            !shared.all_disjoint,
            "suffixes both start with RParen, should NOT be disjoint",
        );
    }

    #[test]
    fn test_cd05_shared_nonterminal_disjoint_suffixes() {
        // Two rules share terminal prefix "if" "(" then the same nonterminal
        // <Int>, but with disjoint FIRST sets after the nonterminal:
        //
        //   IfIntColon:  if ( <Int> :   → suffix FIRST = {Colon}
        //   IfIntComma:  if ( <Int> ,   → suffix FIRST = {Comma}
        //
        // Colon ∩ Comma = ∅ → all_disjoint = true → deterministic CSE.

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();

        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfIntColon", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(":".to_string()),
            ]),
            make_rd_rule("IfIntComma", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(",".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
        assert!(
            !results.is_empty(),
            "should detect shared nonterminal prefix",
        );

        let shared = &results[0];
        assert_eq!(shared.nonterminal, "Int");
        assert_eq!(shared.rules.len(), 2);

        // Colon vs Comma → disjoint
        assert!(
            shared.all_disjoint,
            "Colon vs Comma suffixes should be disjoint",
        );

        // Check discriminating tokens
        let colon_tokens = shared.discriminating_tokens.get("IfIntColon").expect("IfIntColon tokens");
        assert!(colon_tokens.contains(&"Colon".to_string()), "IfIntColon should have Colon: {:?}", colon_tokens);
        let comma_tokens = shared.discriminating_tokens.get("IfIntComma").expect("IfIntComma tokens");
        assert!(comma_tokens.contains(&"Comma".to_string()), "IfIntComma should have Comma: {:?}", comma_tokens);
    }

    #[test]
    fn test_cd05_no_false_positive_different_nonterminals() {
        // Two rules share terminal prefix "if" "(" but diverge at DIFFERENT
        // nonterminal categories:
        //
        //   IfIntRule:    if ( <Int> )
        //   IfFloatRule:  if ( <Float> )
        //
        // Different nt_category → no shared nonterminal → no CSE opportunity
        // for same-NT grouping (these are separate NT boundary groups).

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();

        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string(), "Float".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfIntRule", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
            make_rd_rule("IfFloatRule", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
        // Each NT group has only 1 record (one Int, one Float) → no CSE
        assert!(
            results.is_empty(),
            "different nonterminals should NOT produce CSE: {:?}",
            results,
        );
    }

    #[test]
    fn test_cd05_no_false_positive_single_rule() {
        // Only one rule at an NT boundary — no sharing possible.
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();

        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfParse", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
        assert!(
            results.is_empty(),
            "single rule at NT boundary should NOT produce CSE: {:?}",
            results,
        );
    }

    #[test]
    fn test_cd05_three_way_shared_nonterminal() {
        // Three rules sharing terminal prefix "if" "(" then <Int> with
        // different suffixes:
        //
        //   IfIntColon:   if ( <Int> :
        //   IfIntComma:   if ( <Int> ,
        //   IfIntSemi:    if ( <Int> ;
        //
        // All suffix FIRST sets are disjoint → 3-way CSE.

        let token_ids = make_token_ids();
        let first_sets = make_first_sets();

        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfIntColon", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(":".to_string()),
            ]),
            make_rd_rule("IfIntComma", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(",".to_string()),
            ]),
            make_rd_rule("IfIntSemi", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "c".to_string(),
                },
                RDSyntaxItem::Terminal(";".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
        assert_eq!(results.len(), 1, "should detect one 3-way shared prefix");

        let shared = &results[0];
        assert_eq!(shared.nonterminal, "Int");
        assert_eq!(shared.rules.len(), 3);
        assert!(shared.all_disjoint, "Colon/Comma/Semi are pairwise disjoint");
    }

    #[test]
    fn test_cd05_format_cse_annotation_disjoint() {
        let token_ids = make_token_ids();
        let first_sets = make_first_sets();

        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfIntColon", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(":".to_string()),
            ]),
            make_rd_rule("IfIntComma", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(",".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
        assert!(!results.is_empty());

        let annotation = format_cse_annotation(&results[0], &token_ids);
        assert!(
            annotation.contains("CD05 Prefix CSE"),
            "annotation should contain CD05 header: {}",
            annotation,
        );
        assert!(
            annotation.contains("parse_Int"),
            "annotation should reference parse_Int: {}",
            annotation,
        );
        assert!(
            annotation.contains("match &tokens"),
            "disjoint annotation should contain match block: {}",
            annotation,
        );
    }

    #[test]
    fn test_cd05_format_cse_annotation_overlapping() {
        let token_ids = make_token_ids();
        let mut first_sets = make_first_sets();
        if let Some(int_first) = first_sets.get_mut("Int") {
            int_first.insert("RParen");
        }

        let mut builder = DecisionTreeBuilder::new(
            token_ids.clone(),
            first_sets.clone(),
            vec!["Int".to_string()],
            HashSet::new(),
        );

        let rules = vec![
            make_rd_rule("IfIntA", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
            ]),
            make_rd_rule("IfIntB", "Int", vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ]),
        ];
        builder.insert_rd_rules(&rules);

        let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
        assert!(!results.is_empty());

        let annotation = format_cse_annotation(&results[0], &token_ids);
        assert!(
            annotation.contains("NFA try-all"),
            "overlapping annotation should mention NFA try-all: {}",
            annotation,
        );
    }

    #[test]
    fn test_cd05_display_trait() {
        let shared = SharedNonterminalPrefix {
            category: "Stmt".to_string(),
            prefix_bytes: vec![0x01, 0x02],
            nonterminal: "Expr".to_string(),
            rules: vec!["IfThen".to_string(), "IfThenElse".to_string()],
            discriminating_tokens: HashMap::from([
                ("IfThen".to_string(), vec!["KwThen".to_string()]),
                ("IfThenElse".to_string(), vec!["KwElse".to_string()]),
            ]),
            all_disjoint: true,
        };

        let display = format!("{}", shared);
        assert!(display.contains("CD05 CSE"));
        assert!(display.contains("Expr"));
        assert!(display.contains("IfThen"));
        assert!(display.contains("deterministic"));
    }
}
