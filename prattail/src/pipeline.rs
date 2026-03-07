//! Pipeline for lexer+parser code generation.
//!
//! Implements a state machine that:
//! 1. **Extracts** data bundles from `&LanguageSpec`
//! 2. **Generates** lexer and parser code (sequentially)
//! 3. **Finalizes** by concatenating both code strings and parsing into a `TokenStream`
//!
//! This architecture cleanly separates data extraction from code generation,
//! and isolates `!Send` `LanguageSpec` (which contains `proc_macro2::TokenStream`
//! fields) from the generation phase. The Send+Sync bundles enable future
//! parallelism if workload becomes large enough to justify thread overhead.
//!
//! ```text
//! LanguageSpec ──→ [Extract] ──→ Ready ──→ [Generate] ──→ Generated ──→ [Finalize] ──→ Complete
//!                  separate        LexerBundle ──→ lexer_code    concatenate + parse
//!                  bundles         ParserBundle ──→ parser_code   into TokenStream
//! ```

use std::collections::{HashMap, HashSet};
use std::fmt;

use proc_macro2::TokenStream;

use crate::binding_power::{analyze_binding_powers, BindingPowerTable, InfixRuleInfo, MixfixPart};
use crate::dispatch::{
    categories_needing_dispatch, write_category_dispatch, CastRule, CrossCategoryRule,
};
use crate::automata::codegen::{LexerAmbiguityInfo, TokenVariantMap};
use crate::lexer::{extract_terminals, generate_lexer_as_string, GrammarRuleInfo, TypeInfo};
use crate::pratt::{
    write_dispatch_recovering, write_parser_helpers, write_recovery_helpers, PrefixHandler,
};
use crate::prediction::{
    analyze_cross_category_overlaps, compute_first_sets, compute_follow_sets_from_inputs,
    generate_sync_predicate, FirstItem, FirstSet, FollowSetInput,
    RuleInfo,
};
use crate::recursive::{
    write_dollar_handlers, write_lambda_handlers, write_rd_handler, RDRuleInfo, RDSyntaxItem,
};
use crate::trampoline::{
    write_trampolined_parser, write_trampolined_parser_recovering, TrampolineConfig,
};
use crate::wfst::PredictionWfst;
use crate::{LanguageSpec, LiteralPatterns, SyntaxItemSpec};

// ══════════════════════════════════════════════════════════════════════════════
// Inter-category graph (shared by A4 and A8)
// ══════════════════════════════════════════════════════════════════════════════

/// Shared inter-category graph used by both A4 (dead-path detection) and
/// A8 (nearly-dead path detection). Nodes are categories; edges represent
/// inter-category connections via cast/cross-category rules and syntax-level
/// NonTerminal/Binder/Collection references.
pub(crate) struct InterCategoryGraph {
    pub cat_to_idx: HashMap<String, usize>,
    pub num_nodes: usize,
    pub root_idx: usize,
    /// Undirected adjacency (HashSet for dedup).
    pub adj: Vec<HashSet<usize>>,
}

impl InterCategoryGraph {
    /// BFS from `start`, returning all reachable node indices.
    pub fn bfs_reachable(&self, start: usize) -> HashSet<usize> {
        let mut visited = HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        visited.insert(start);
        queue.push_back(start);
        while let Some(node) = queue.pop_front() {
            for &target in &self.adj[node] {
                if visited.insert(target) {
                    queue.push_back(target);
                }
            }
        }
        visited
    }

}

/// Recursively collect cross-category edge pairs from a `SyntaxItemSpec`.
///
/// Unified helper used by both A4 and A8: any NonTerminal, Binder, or
/// Collection referencing a different category produces an edge pair
/// `(referenced_category_idx, rule_category_idx)`.
fn collect_syntax_refs(
    item: &crate::SyntaxItemSpec,
    rule_cat: &str,
    cat_to_idx: &HashMap<String, usize>,
    target_idx: usize,
    pairs: &mut Vec<(usize, usize)>,
) {
    match item {
        crate::SyntaxItemSpec::NonTerminal { category: ref nt_cat, .. } => {
            if nt_cat != rule_cat {
                if let Some(&src_idx) = cat_to_idx.get(nt_cat) {
                    pairs.push((src_idx, target_idx));
                }
            }
        }
        crate::SyntaxItemSpec::Binder { category: ref b_cat, .. } => {
            if b_cat != rule_cat {
                if let Some(&src_idx) = cat_to_idx.get(b_cat) {
                    pairs.push((src_idx, target_idx));
                }
            }
        }
        crate::SyntaxItemSpec::Collection { element_category: ref e_cat, .. } => {
            if e_cat != rule_cat {
                if let Some(&src_idx) = cat_to_idx.get(e_cat) {
                    pairs.push((src_idx, target_idx));
                }
            }
        }
        crate::SyntaxItemSpec::Sep { body, .. } => {
            collect_syntax_refs(body, rule_cat, cat_to_idx, target_idx, pairs);
        }
        crate::SyntaxItemSpec::Map { body_items } => {
            for sub in body_items {
                collect_syntax_refs(sub, rule_cat, cat_to_idx, target_idx, pairs);
            }
        }
        crate::SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
            for ref_cat in [left_category.as_str(), right_category.as_str()] {
                if ref_cat != rule_cat {
                    if let Some(&src_idx) = cat_to_idx.get(ref_cat) {
                        pairs.push((src_idx, target_idx));
                    }
                }
            }
            collect_syntax_refs(body, rule_cat, cat_to_idx, target_idx, pairs);
        }
        crate::SyntaxItemSpec::Optional { inner } => {
            for sub in inner {
                collect_syntax_refs(sub, rule_cat, cat_to_idx, target_idx, pairs);
            }
        }
        // Terminal, IdentCapture, BinderCollection — no cross-category refs
        _ => {}
    }
}

/// Build the shared inter-category graph from rule infos, categories, and syntax.
///
/// Nodes are categories; edges come from:
/// 1. Cast/cross-category rules (source↔target via first_items NonTerminal)
/// 2. Full syntax traversal (any cross-category NonTerminal/Binder/Collection)
///
/// Returns `None` if fewer than 2 categories (no inter-category analysis possible).
pub(crate) fn build_inter_category_graph(
    rule_infos: &[RuleInfo],
    categories: &[CategoryInfo],
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Option<InterCategoryGraph> {
    if categories.len() < 2 {
        return None;
    }

    let cat_to_idx: HashMap<String, usize> = categories
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name.clone(), i))
        .collect();
    let num_nodes = categories.len();

    let root_idx = categories
        .iter()
        .position(|c| c.is_primary)
        .unwrap_or(0);

    let mut adj: Vec<HashSet<usize>> = vec![HashSet::new(); num_nodes];

    // From cast/cross-category rules: source category ↔ target category
    for rule in rule_infos {
        if rule.is_cast || rule.is_cross_category {
            let target_idx = match cat_to_idx.get(&rule.category) {
                Some(&idx) => idx,
                None => continue,
            };
            for fi in &rule.first_items {
                if let FirstItem::NonTerminal(src_cat) = fi {
                    if let Some(&src_idx) = cat_to_idx.get(src_cat) {
                        adj[src_idx].insert(target_idx);
                        adj[target_idx].insert(src_idx);
                    }
                }
            }
        }
    }

    // From full syntax: any cross-category NonTerminal/Binder/Collection reference
    {
        let mut pairs = Vec::new();
        for (_, rule_cat, items) in all_syntax {
            let target_idx = match cat_to_idx.get(rule_cat) {
                Some(&idx) => idx,
                None => continue,
            };
            for item in items {
                collect_syntax_refs(item, rule_cat, &cat_to_idx, target_idx, &mut pairs);
            }
        }
        for (a, b) in pairs {
            adj[a].insert(b);
            adj[b].insert(a);
        }
    }

    Some(InterCategoryGraph { cat_to_idx, num_nodes, root_idx, adj })
}

// ══════════════════════════════════════════════════════════════════════════════
// Dead-rule detection
// ══════════════════════════════════════════════════════════════════════════════

/// A dead-rule warning produced by WFST-based reachability analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeadRuleWarning {
    /// Literal rule in a category with no `native_type`.
    LiteralNoNativeType {
        rule_label: String,
        category: String,
    },
    /// Infix/var rule whose entire category is unreachable (no prefix rule
    /// can start a parse in that category).
    UnreachableCategory {
        rule_label: String,
        category: String,
    },
    /// Prefix/cast/cross-category rule that no FIRST-set token dispatches to
    /// via the prediction WFST.
    WfstUnreachable {
        rule_label: String,
        category: String,
    },
    /// A4: Inter-category dead path detected by forward-backward analysis.
    /// The rule's category is not reachable from the root category via the
    /// inter-category dispatch graph, or cannot reach back to the root.
    InterCategoryDeadPath {
        rule_label: String,
        category: String,
        /// Which direction failed: "forward" (unreachable from root),
        /// "backward" (cannot reach root), or "both".
        direction: String,
    },
    /// A8: Nearly-dead inter-category path detected by ProductWeight<BooleanWeight, CountingWeight>
    /// forward-backward analysis. The path is reachable but has very few derivations
    /// relative to the total, suggesting the rule is practically unused.
    NearlyDeadPath {
        rule_label: String,
        category: String,
        /// Number of derivation paths through this category.
        derivation_count: u64,
        /// Total derivation paths through the root category.
        total_count: u64,
    },
}

impl fmt::Display for DeadRuleWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeadRuleWarning::LiteralNoNativeType { rule_label, category } => write!(
                f,
                "warning: literal rule {} in category {} is unreachable (dead code) — \
                 category has no native_type",
                rule_label, category,
            ),
            DeadRuleWarning::UnreachableCategory { rule_label, category } => write!(
                f,
                "warning: rule {} in category {} is unreachable (dead code) — \
                 category {} has no reachable prefix rules",
                rule_label, category, category,
            ),
            DeadRuleWarning::WfstUnreachable { rule_label, category } => write!(
                f,
                "warning: rule {} in category {} is unreachable (dead code) — \
                 no token in FIRST({}) dispatches to it via prediction WFST",
                rule_label, category, category,
            ),
            DeadRuleWarning::InterCategoryDeadPath { rule_label, category, direction } => write!(
                f,
                "warning: rule {} in category {} is on a dead inter-category path ({}) — \
                 forward-backward analysis with BooleanWeight indicates no live path through this category",
                rule_label, category, direction,
            ),
            DeadRuleWarning::NearlyDeadPath {
                rule_label, category, derivation_count, total_count,
            } => write!(
                f,
                "warning: rule {} in category {} is on a nearly-dead inter-category path — \
                 only {}/{} derivation paths traverse this category",
                rule_label, category, derivation_count, total_count,
            ),
        }
    }
}

/// Detect dead rules via three-tier analysis:
///   1. **Literal rules**: dead if their category has no `native_type`
///   2. **Infix/var rules**: dead if their entire category is unreachable
///   3. **Prefix rules** (incl. cast, cross-category): dead if no FIRST-set
///      token dispatches to them via the prediction WFST
///
/// Returns a list of warnings (one per dead rule). The caller decides whether
/// to `eprintln!` them or collect them for testing.
pub(crate) fn detect_dead_rules(
    rule_infos: &[RuleInfo],
    categories: &[CategoryInfo],
    first_sets: &HashMap<String, FirstSet>,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    semantic_dependency_groups: &[HashSet<String>],
    nfa_spillover_categories: &HashSet<String>,
    rd_rules: &[crate::recursive::RDRuleInfo],
) -> Vec<DeadRuleWarning> {
    let mut warnings = Vec::new();

    // Tier 2 prerequisite: compute reachable categories.
    // A category is reachable if it has a non-empty FIRST set or is
    // reachable via cross-category/cast rules from another reachable category.
    let reachable_categories: HashSet<String> = {
        let mut reachable = HashSet::new();
        // Seed: categories with non-empty FIRST sets
        for (cat, fs) in first_sets {
            if !fs.tokens.is_empty() {
                reachable.insert(cat.clone());
            }
        }
        // Fixed-point: add categories reachable via cross-cat/cast from
        // reachable sources.
        let mut changed = true;
        while changed {
            changed = false;
            for rule in rule_infos {
                if rule.is_cross_category || rule.is_cast {
                    let source = rule.first_items.iter().find_map(|fi| {
                        if let FirstItem::NonTerminal(cat) = fi {
                            Some(cat.clone())
                        } else {
                            None
                        }
                    });
                    if let Some(src) = source {
                        if reachable.contains(&src)
                            && reachable.insert(rule.category.clone())
                        {
                            changed = true;
                        }
                    }
                }
            }
        }
        reachable
    };

    // Pre-compute rule labels reachable via NFA spillover try-all dispatch.
    // In NFA-spillover categories, multiple RD rules share a dispatch token.
    // The trampoline tries all rules in each group — if ANY rule in the group
    // is WFST-reachable, all siblings are also reachable at runtime.
    let nfa_covered: HashSet<String> = {
        let mut covered = HashSet::new();
        for cat in nfa_spillover_categories {
            let groups = crate::trampoline::group_rd_by_dispatch_token_pub(rd_rules, cat);
            for (_token, rules) in &groups {
                if rules.len() < 2 {
                    continue;
                }
                // If any rule in the group is WFST-reachable, all are covered.
                let any_reachable =
                    prediction_wfsts
                        .get(cat.as_str())
                        .map_or(false, |wfst| {
                            first_sets.get(cat.as_str()).map_or(false, |fs| {
                                fs.tokens.iter().any(|tok| {
                                    let preds = wfst.predict(tok);
                                    rules.iter().any(|r| {
                                        preds
                                            .iter()
                                            .any(|a| a.action.rule_label() == r.label)
                                    })
                                })
                            })
                        });
                if any_reachable {
                    for r in rules {
                        covered.insert(r.label.clone());
                    }
                }
            }
        }
        covered
    };

    for rule_info in rule_infos {
        // Tier 1: literal rules — dead if category has no native_type.
        if rule_info.is_literal {
            let has_native = categories
                .iter()
                .any(|c| c.name == rule_info.category && c.native_type.is_some());
            if !has_native {
                warnings.push(DeadRuleWarning::LiteralNoNativeType {
                    rule_label: rule_info.label.clone(),
                    category: rule_info.category.clone(),
                });
            }
            continue;
        }

        // Tier 2: infix/postfix/mixfix and var rules — dead if their
        // dispatch category is unreachable. Cross-category infix rules are
        // dispatched from the SOURCE category's infix loop, so we check
        // source-category reachability; same-category infix/var rules check
        // their own category.
        if rule_info.is_infix || rule_info.is_var {
            let check_cat = if rule_info.is_cross_category {
                rule_info
                    .first_items
                    .iter()
                    .find_map(|fi| {
                        if let FirstItem::NonTerminal(cat) = fi {
                            Some(cat.as_str())
                        } else {
                            None
                        }
                    })
                    .unwrap_or(rule_info.category.as_str())
            } else {
                rule_info.category.as_str()
            };
            if !reachable_categories.contains(check_cat) {
                warnings.push(DeadRuleWarning::UnreachableCategory {
                    rule_label: rule_info.label.clone(),
                    category: rule_info.category.clone(),
                });
            }
            continue;
        }

        // Tier 3: all remaining prefix rules (including cast and cross-
        // category) — dead if no token in FIRST set dispatches to them
        // via the prediction WFST.
        let wfst = match prediction_wfsts.get(&rule_info.category) {
            Some(w) => w,
            None => continue,
        };

        let reachable = first_sets
            .get(&rule_info.category)
            .map_or(false, |fs| {
                fs.tokens.iter().any(|tok| {
                    wfst.predict(tok)
                        .iter()
                        .any(|a| a.action.rule_label() == rule_info.label)
                })
            });

        if !reachable && !nfa_covered.contains(&rule_info.label) {
            warnings.push(DeadRuleWarning::WfstUnreachable {
                rule_label: rule_info.label.clone(),
                category: rule_info.category.clone(),
            });
        }
    }

    // Tier 4: Transitive semantic liveness — equations, rewrites, and the
    // logic block may reference constructor labels that are parsing-dead but
    // semantically live. Compute the parsing-live set, expand via fixed-point
    // closure over dependency groups, and remove warnings for resurrected labels.
    if !semantic_dependency_groups.is_empty() {
        let flagged: HashSet<String> = warnings
            .iter()
            .map(|w| match w {
                DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
                | DeadRuleWarning::UnreachableCategory { rule_label, .. }
                | DeadRuleWarning::WfstUnreachable { rule_label, .. }
                | DeadRuleWarning::InterCategoryDeadPath { rule_label, .. }
                | DeadRuleWarning::NearlyDeadPath { rule_label, .. } => rule_label.clone(),
            })
            .collect();

        let parsing_live: HashSet<String> = rule_infos
            .iter()
            .map(|r| r.label.clone())
            .filter(|l| !flagged.contains(l))
            .collect();

        let semantic_live =
            compute_semantic_live_labels(&parsing_live, semantic_dependency_groups);

        // Remove warnings for labels that are semantically live.
        warnings.retain(|w| {
            let label = match w {
                DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
                | DeadRuleWarning::UnreachableCategory { rule_label, .. }
                | DeadRuleWarning::WfstUnreachable { rule_label, .. }
                | DeadRuleWarning::InterCategoryDeadPath { rule_label, .. }
                | DeadRuleWarning::NearlyDeadPath { rule_label, .. } => rule_label,
            };
            !semantic_live.contains(label)
        });
    }

    warnings
}

/// Compute the set of semantically live labels via transitive closure over dependency groups.
///
/// Starting from the set of labels that are parsing-live (reachable by the parser), expand
/// using dependency groups from equations, rewrites, and the logic block. If any label in a
/// dependency group is live, all labels in that group become live — the user's semantic
/// specification references them together and the Ascent codegen needs all variants.
///
/// **Termination**: The live set is monotonically growing and bounded by the finite set of
/// all rule labels. The fixed-point loop terminates in at most |labels| iterations.
///
/// **Complexity**: O(G × L × I) where G = groups, L = labels per group, I = iterations.
/// In practice G ≈ 10-50, L ≈ 2-4, I ≈ 2-3 — negligible.
pub(crate) fn compute_semantic_live_labels(
    parsing_live: &HashSet<String>,
    dependency_groups: &[HashSet<String>],
) -> HashSet<String> {
    let mut live = parsing_live.clone();
    let mut changed = true;
    while changed {
        changed = false;
        for group in dependency_groups {
            // If any label in this group is live, all labels become live.
            if group.iter().any(|label| live.contains(label)) {
                for label in group {
                    if live.insert(label.clone()) {
                        changed = true;
                    }
                }
            }
        }
    }
    live
}

/// A4: Inter-category dead-path detection via forward-backward analysis.
///
/// Builds a graph where each category is a node and edges represent
/// inter-category connections (cast rules, cross-category rules).
/// Uses `BooleanWeight` with `forward_backward.rs` to identify categories
/// that are structurally isolated from the root (primary) category.
///
/// A category is "dead" if:
/// - It has no forward path from the root category (cannot be reached by parsing)
/// - It has no backward path to the root category (its results are never consumed)
///
/// Rules in dead categories get `DeadRuleWarning::InterCategoryDeadPath`.
pub(crate) fn detect_inter_category_dead_paths(
    rule_infos: &[RuleInfo],
    categories: &[CategoryInfo],
    _first_sets: &HashMap<String, FirstSet>,
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Vec<DeadRuleWarning> {
    let graph = match build_inter_category_graph(rule_infos, categories, all_syntax) {
        Some(g) => g,
        None => return Vec::new(),
    };

    // Forward BFS from root: which categories are reachable
    let fwd_reachable = graph.bfs_reachable(graph.root_idx);

    // Backward BFS: build reverse edges, then BFS from root.
    // Since edges are bidirectional (adj is symmetric), backward = forward.
    // But for correctness with asymmetric future changes, use reverse graph.
    let bwd_reachable: HashSet<usize> = {
        let mut rev_adj: Vec<Vec<usize>> = vec![Vec::new(); graph.num_nodes];
        for (src, targets) in graph.adj.iter().enumerate() {
            for &tgt in targets {
                rev_adj[tgt].push(src);
            }
        }
        let mut visited = HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        visited.insert(graph.root_idx);
        queue.push_back(graph.root_idx);
        while let Some(node) = queue.pop_front() {
            for &source in &rev_adj[node] {
                if visited.insert(source) {
                    queue.push_back(source);
                }
            }
        }
        visited
    };

    // Collect warnings for rules in categories not reachable in both directions
    let mut warnings = Vec::new();

    for rule in rule_infos {
        let cat_idx = match graph.cat_to_idx.get(&rule.category) {
            Some(&idx) => idx,
            None => continue,
        };

        let fwd = fwd_reachable.contains(&cat_idx);
        let bwd = bwd_reachable.contains(&cat_idx);

        if !fwd || !bwd {
            let direction = match (fwd, bwd) {
                (false, false) => "forward+backward",
                (false, true) => "forward",
                (true, false) => "backward",
                (true, true) => unreachable!(),
            };

            warnings.push(DeadRuleWarning::InterCategoryDeadPath {
                rule_label: rule.label.clone(),
                category: rule.category.clone(),
                direction: direction.to_string(),
            });
        }
    }

    warnings
}

/// Threshold ratio below which a category's derivation count (relative to the root)
/// is flagged as "nearly dead." A ratio of 0.01 means the category accounts for less
/// than 1% of the total derivation paths through the root.
const NEARLY_DEAD_RATIO: f64 = 0.01;

/// A8: Nearly-dead inter-category path detection via `ProductWeight<BooleanWeight, CountingWeight>`.
///
/// Extends the A4 `BooleanWeight`-only analysis with `CountingWeight` to detect
/// categories that are technically reachable but practically unused. A category is
/// "nearly dead" if:
/// 1. It **is** reachable in both directions (not flagged by A4).
/// 2. Its derivation count is less than `NEARLY_DEAD_RATIO` × the root's total count.
///
/// The `ProductWeight<BooleanWeight, CountingWeight>` semiring carries:
/// - `left` (`BooleanWeight`): whether the node is reachable at all (OR semiring).
/// - `right` (`CountingWeight`): how many derivation paths reach/leave the node (+ semiring).
///
/// Using `ProductWeight` avoids a second graph traversal: a single `forward_scores`
/// and `backward_scores` call computes both reachability and derivation counts jointly.
///
/// Rules in nearly-dead categories get `DeadRuleWarning::NearlyDeadPath`.
pub(crate) fn detect_nearly_dead_paths(
    rule_infos: &[RuleInfo],
    categories: &[CategoryInfo],
    first_sets: &HashMap<String, FirstSet>,
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Vec<DeadRuleWarning> {
    use crate::automata::semiring::{BooleanWeight, CountingWeight, ProductWeight, Semiring};
    use crate::forward_backward::{forward_scores, backward_scores};

    type BoolCount = ProductWeight<BooleanWeight, CountingWeight>;

    let graph = match build_inter_category_graph(rule_infos, categories, all_syntax) {
        Some(g) => g,
        None => return Vec::new(),
    };

    // Build weighted edge list from shared graph adjacency
    let mut edges: Vec<Vec<(usize, BoolCount)>> = vec![Vec::new(); graph.num_nodes];
    let w_one = BoolCount::new(BooleanWeight::one(), CountingWeight::one());
    for (src, targets) in graph.adj.iter().enumerate() {
        for &dst in targets {
            edges[src].push((dst, w_one));
        }
    }

    // Self-edges for categories with non-empty FIRST sets
    for (cat, fs) in first_sets {
        if !fs.tokens.is_empty() {
            if let Some(&idx) = graph.cat_to_idx.get(cat) {
                edges[idx].push((idx, w_one));
            }
        }
    }

    // Forward from root
    let forward = forward_scores::<BoolCount>(&edges, graph.num_nodes);

    // Backward to root
    let backward = backward_scores::<BoolCount>(&edges, graph.num_nodes, graph.root_idx);

    // Compare each category's forward count to the maximum across all reachable
    // categories. A category with very few forward paths relative to the maximum
    // is nearly dead.
    let max_count = forward.iter()
        .filter(|w| w.left.is_reachable())
        .map(|w| w.right.count())
        .max()
        .unwrap_or(1)
        .max(1);

    let mut warnings = Vec::new();

    for rule in rule_infos {
        let cat_idx = match graph.cat_to_idx.get(&rule.category) {
            Some(&idx) => idx,
            None => continue,
        };

        let fwd = &forward[cat_idx];
        let bwd = &backward[cat_idx];

        // Skip categories that are completely unreachable (handled by A4)
        if fwd.left.is_zero() || bwd.left.is_zero() {
            continue;
        }

        // Skip the root category itself (always has count >= 1)
        if cat_idx == graph.root_idx {
            continue;
        }

        let cat_count = fwd.right.count();
        let ratio = cat_count as f64 / max_count as f64;

        if ratio < NEARLY_DEAD_RATIO && cat_count > 0 {
            warnings.push(DeadRuleWarning::NearlyDeadPath {
                rule_label: rule.label.clone(),
                category: rule.category.clone(),
                derivation_count: cat_count,
                total_count: max_count,
            });
        }
    }

    warnings
}

/// Detect dead prefixes: dispatch tokens whose entire trie subtree leads only
/// to dead rules. Returns `category → [dead_prefix_token_variant, ...]`.
///
/// Used by Sprint 4 to increase recovery WFST weights for dead-prefix tokens
/// (demoting them as recovery targets) and by `lint_w01_dead_rule` to emit
/// W01 dead-prefix sub-notes.
pub(crate) fn detect_dead_prefixes(
    dead_rule_warnings: &[DeadRuleWarning],
    decision_trees: &HashMap<String, crate::decision_tree::CategoryDecisionTree>,
    token_id_map: &crate::token_id::TokenIdMap,
) -> HashMap<String, Vec<String>> {
    if decision_trees.is_empty() {
        return HashMap::new();
    }

    let dead_labels: HashSet<String> = dead_rule_warnings
        .iter()
        .map(|w| match w {
            DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
            | DeadRuleWarning::UnreachableCategory { rule_label, .. }
            | DeadRuleWarning::WfstUnreachable { rule_label, .. }
            | DeadRuleWarning::InterCategoryDeadPath { rule_label, .. }
            | DeadRuleWarning::NearlyDeadPath { rule_label, .. } => rule_label.clone(),
        })
        .collect();

    if dead_labels.is_empty() {
        return HashMap::new();
    }

    let mut result: HashMap<String, Vec<String>> = HashMap::new();

    for (cat_name, tree) in decision_trees {
        let dispatch_tokens = tree.dispatch_tokens(token_id_map);
        for token_variant in &dispatch_tokens {
            let strategy = tree.dispatch_strategy(token_variant, token_id_map);
            let rule_labels = match &strategy {
                crate::decision_tree::DispatchStrategy::Singleton { rule_label } => {
                    vec![rule_label.clone()]
                }
                crate::decision_tree::DispatchStrategy::NfaTryAll { rule_labels, .. } => {
                    rule_labels.clone()
                }
                crate::decision_tree::DispatchStrategy::DisjointSuffix { suffix_map, .. } => {
                    suffix_map.values().cloned().collect()
                }
                crate::decision_tree::DispatchStrategy::NotPresent => Vec::new(),
            };
            if !rule_labels.is_empty() && rule_labels.iter().all(|l| dead_labels.contains(l)) {
                result
                    .entry(cat_name.clone())
                    .or_default()
                    .push(token_variant.clone());
            }
        }
    }

    result
}

/// A4: Collect dead rule labels safe for codegen suppression.
///
/// Runs `detect_dead_rules()` and returns the set of rule labels whose codegen
/// can safely be elided.
///
/// **Conservative filtering**: the dead-rule analysis (`detect_dead_rules`)
/// was designed for diagnostics (lint warnings), not codegen suppression.
/// Only provably unreachable rules are included:
///
/// - **Tier 1** (`LiteralNoNativeType`): literal rules in categories without
///   `native_type`. The category can never produce a native value.
/// - **Tier 2** (`UnreachableCategory`): infix/var rules in categories with
///   no reachable prefix rules. No parse can ever start in the category.
///
/// Intentionally **excluded** from the dead set:
///
/// - **`WfstUnreachable`** (Tier 3): the WFST only models prefix dispatch;
///   cross-category rules, cast rules, and NFA-merged rules are reachable
///   through alternative dispatch paths not captured by the prediction WFST.
/// - **`InterCategoryDeadPath`** (A4): the `backward_scores` function assumes
///   topological ordering, but the inter-category graph has cycles (bidirectional
///   edges from cast/cross-cat rules), producing false positives for categories
///   that appear later in the node ordering.
/// - **`NearlyDeadPath`** (A8): informational only — rules are technically
///   reachable.
pub(crate) fn collect_dead_rule_labels(
    rule_infos: &[RuleInfo],
    categories: &[CategoryInfo],
    first_sets: &HashMap<String, FirstSet>,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    semantic_dependency_groups: &[HashSet<String>],
    decision_trees: &HashMap<String, crate::decision_tree::CategoryDecisionTree>,
) -> HashSet<String> {
    let mut dead_labels = HashSet::new();

    // Tier 1: LiteralNoNativeType — literal rules in categories without native_type.
    // These are provably unreachable: the category can never produce a native value.
    // Tier 2: UnreachableCategory — rules in categories with no reachable prefix rules.
    // These are provably unreachable: no parse can ever start in the category.
    // Tier 3 (confirmed): WfstUnreachable AND trie-unreachable — dead in both WFST
    // and decision tree dispatch, so no alternative dispatch path exists.
    let trie_reachable: HashMap<String, HashSet<String>> = decision_trees
        .iter()
        .map(|(cat, tree)| (cat.clone(), tree.reachable_rules()))
        .collect();

    for w in detect_dead_rules(rule_infos, categories, first_sets, prediction_wfsts,
                               semantic_dependency_groups, &HashSet::new(), &[]) {
        match &w {
            DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
            | DeadRuleWarning::UnreachableCategory { rule_label, .. } => {
                dead_labels.insert(rule_label.clone());
            }
            // 1.2b: WfstUnreachable is now promoted to confirmed-dead if the rule
            // is also unreachable in the decision tree trie. This eliminates the
            // false-positive risk from cross-cat/cast/NFA dispatch paths: if the
            // trie also can't reach the rule, no dispatch path exists.
            DeadRuleWarning::WfstUnreachable { rule_label, category, .. } => {
                let trie_also_unreachable = trie_reachable
                    .get(category)
                    .map_or(false, |reachable| !reachable.contains(rule_label));
                if trie_also_unreachable {
                    dead_labels.insert(rule_label.clone());
                }
            }
            _ => {}
        }
    }

    // InterCategoryDeadPath excluded: backward_scores assumes topological
    // ordering but the inter-category graph has cycles, producing false positives.
    // NearlyDeadPath excluded: informational only, rules are technically reachable.

    dead_labels
}

// ══════════════════════════════════════════════════════════════════════════════
// Data bundles — all Send+Sync
// ══════════════════════════════════════════════════════════════════════════════

/// All data needed by the lexer pipeline. Send+Sync.
pub struct LexerBundle {
    grammar_rules: Vec<GrammarRuleInfo>,
    type_infos: Vec<TypeInfo>,
    /// Whether the grammar has binder rules (^x.{body} lambda syntax).
    has_binders: bool,
    /// Category names (needed for dollar terminal generation when has_binders).
    category_names: Vec<String>,
    /// Configurable literal token patterns for lexer generation.
    literal_patterns: LiteralPatterns,
}

/// Category metadata for the parser pipeline. Send+Sync.
pub struct CategoryInfo {
    /// Category name (e.g., "Proc", "Int").
    pub name: String,
    /// Native Rust type name, if any (e.g., "i32", "bool").
    pub native_type: Option<String>,
    /// Whether this is the primary (first-declared) category.
    pub is_primary: bool,
}

/// All data needed by the parser pipeline. Send+Sync.
pub struct ParserBundle {
    /// Grammar name (e.g., "RhoPi").
    pub(crate) grammar_name: String,
    pub(crate) categories: Vec<CategoryInfo>,
    pub(crate) bp_table: BindingPowerTable,
    pub(crate) rule_infos: Vec<RuleInfo>,
    pub(crate) follow_inputs: Vec<FollowSetInput>,
    pub(crate) rd_rules: Vec<RDRuleInfo>,
    pub(crate) cross_rules: Vec<CrossCategoryRule>,
    pub(crate) cast_rules: Vec<CastRule>,
    /// Whether the grammar has binder rules (^x.{body} lambda syntax).
    pub(crate) has_binders: bool,
    /// Beam width configuration for WFST prediction pruning.
    pub(crate) beam_width: crate::BeamWidthConfig,
    /// Recovery configuration (costs, thresholds, beam width).
    pub(crate) recovery_config: crate::recovery::RecoveryConfig,
    /// All syntax per rule: (label, category, syntax). Used by lint layer.
    pub(crate) all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)>,
    /// Rule source locations: (label, category) → SourceLocation. Used by lint layer.
    pub(crate) rule_locations: std::collections::HashMap<(String, String), crate::SourceLocation>,
    /// Dependency groups from equations/rewrites/logic for transitive liveness analysis.
    pub(crate) semantic_dependency_groups: Vec<HashSet<String>>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline state machine
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline state machine for parallel code generation.
///
/// Each state holds the data needed for the next transition.
// Compile-time state machine with 3 total moves — never stored in collections.
#[allow(clippy::large_enum_variant)]
pub enum PipelineState {
    /// Bundles extracted, ready for codegen.
    Ready {
        lexer_bundle: LexerBundle,
        parser_bundle: ParserBundle,
    },
    /// Both code strings generated, ready to merge.
    Generated {
        lexer_code: String,
        parser_code: String,
    },
    /// Final output produced.
    Complete(TokenStream),
}

impl PipelineState {
    /// Advance the pipeline to the next state.
    ///
    /// - `Ready → Generated`: runs lexer and parser codegen sequentially
    /// - `Generated → Complete`: concatenates code strings and parses into `TokenStream`
    /// - `Complete → panic`: pipeline is already done
    pub fn advance(self) -> Self {
        match self {
            PipelineState::Ready { lexer_bundle, parser_bundle } => {
                let (lexer_code, variant_map, ambiguity_info) =
                    generate_lexer_code_with_map(&lexer_bundle);
                let parser_code = generate_parser_code_with_context(
                    &parser_bundle,
                    &variant_map,
                    &ambiguity_info,
                );
                PipelineState::Generated { lexer_code, parser_code }
            },
            PipelineState::Generated { lexer_code, parser_code } => {
                let mut combined = lexer_code;
                combined.push_str(&parser_code);
                let ts = combined
                    .parse::<TokenStream>()
                    .expect("PraTTaIL pipeline: generated code failed to parse as TokenStream");
                PipelineState::Complete(ts)
            },
            PipelineState::Complete(_) => panic!("Pipeline already complete"),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline diagnostic helper
// ══════════════════════════════════════════════════════════════════════════════

/// Build and emit a structured pipeline diagnostic via the lint system.
fn pipeline_diagnostic(
    grammar_name: &str,
    id: &'static str,
    name: &'static str,
    severity: crate::lint::LintSeverity,
    message: String,
    hint: Option<String>,
) {
    crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
        id,
        name,
        severity,
        category: None,
        rule: None,
        message,
        hint,
        grammar_name: Some(grammar_name.to_string()),
        source_location: None,
    });
}

// ══════════════════════════════════════════════════════════════════════════════
// Entry point
// ══════════════════════════════════════════════════════════════════════════════

/// Run the full pipeline: extract → generate (parallel) → finalize.
///
/// This is the main entry point for parallel code generation. It:
/// 1. Extracts Send+Sync bundles from `&LanguageSpec` on the current thread
/// 2. Runs lexer and parser codegen in parallel via `rayon::join`
/// 3. Concatenates results and parses into a single `TokenStream`
pub fn run_pipeline(spec: &LanguageSpec) -> TokenStream {
    run_pipeline_with_analysis(spec).0
}

/// Run the full pipeline and return both the generated `TokenStream` and
/// a [`PipelineAnalysis`] capturing WFST-derived data for downstream
/// optimization (Ascent DCE, rule ordering, isomorphic WFST detection).
///
/// The analysis is populated during the Generate phase, where FIRST sets,
/// prediction WFSTs, dead-rule labels, and constructor weights are already
/// computed. This function captures that data before it would otherwise
/// be discarded.
pub fn run_pipeline_with_analysis(spec: &LanguageSpec) -> (TokenStream, crate::PipelineAnalysis) {
    let (lexer_bundle, parser_bundle) = extract_from_spec(spec);

    // NOTE: Grammar warnings (G01-G03) and WFST warnings (W01, W02) are now handled
    // by the unified lint layer inside generate_parser_code(). The early
    // detect_grammar_warnings() call has been migrated to lint::run_lints().

    // EBNF debug dump (opt-in via environment variable)
    if let Ok(dump_target) = std::env::var("PRATTAIL_DUMP_EBNF") {
        let ebnf = crate::ebnf::format_ebnf(spec, &parser_bundle);
        crate::ebnf::write_ebnf_output(&ebnf, &spec.name, &dump_target);
    }

    // Run lexer codegen
    let (lexer_code, variant_map, ambiguity_info) =
        generate_lexer_code_with_map(&lexer_bundle);

    // Run parser codegen with analysis capture
    let (parser_code, analysis) = generate_parser_code_with_analysis(
        &parser_bundle,
        &variant_map,
        &ambiguity_info,
    );

    // Finalize: concatenate and parse into TokenStream
    let mut combined = lexer_code;
    combined.push_str(&parser_code);
    let ts = combined
        .parse::<TokenStream>()
        .expect("PraTTaIL pipeline: generated code failed to parse as TokenStream");

    (ts, analysis)
}

// ══════════════════════════════════════════════════════════════════════════════
// Extract phase (main thread)
// ══════════════════════════════════════════════════════════════════════════════

/// Extract Send+Sync data bundles from the language specification.
///
/// Single pass over `spec.rules` builds all collections needed by both
/// the lexer and parser pipelines. The `rust_code: Option<TokenStream>`
/// field on `RuleSpec` is intentionally not copied — it is never used
/// by the recursive descent handler generator.
fn extract_from_spec(spec: &LanguageSpec) -> (LexerBundle, ParserBundle) {
    // ── Lexer bundle ──
    let grammar_rules: Vec<GrammarRuleInfo> = spec
        .rules
        .iter()
        .map(|r| GrammarRuleInfo {
            label: r.label.clone(),
            category: r.category.clone(),
            terminals: collect_terminals_recursive(&r.syntax),
            is_infix: r.is_infix,
        })
        .collect();

    let type_infos: Vec<TypeInfo> = spec
        .types
        .iter()
        .map(|t| TypeInfo {
            name: t.name.clone(),
            language_name: spec.name.clone(),
            native_type_name: t.native_type.clone(),
        })
        .collect();

    let has_binders = spec
        .rules
        .iter()
        .any(|r| r.has_binder || r.has_multi_binder);

    let lexer_category_names: Vec<String> = spec.types.iter().map(|t| t.name.clone()).collect();
    let lexer_bundle = LexerBundle {
        grammar_rules,
        type_infos,
        has_binders,
        category_names: lexer_category_names,
        literal_patterns: spec.literal_patterns.clone(),
    };

    // ── Parser bundle ──
    let categories: Vec<CategoryInfo> = spec
        .types
        .iter()
        .enumerate()
        .map(|(i, t)| CategoryInfo {
            name: t.name.clone(),
            native_type: t.native_type.clone(),
            is_primary: i == 0,
        })
        .collect();

    let category_names: Vec<String> = categories.iter().map(|c| c.name.clone()).collect();

    // Extract infix rules and compute BP table
    let infix_rules: Vec<InfixRuleInfo> = spec
        .rules
        .iter()
        .filter(|r| r.is_infix)
        .map(|r| {
            let (is_mixfix, mixfix_parts) = extract_mixfix_parts(&r.syntax);
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

    // Compute max infix bp per category (exclude postfix) for prefix_bp
    let max_infix_bp: HashMap<String, u8> = {
        let mut map = HashMap::new();
        for op in &bp_table.operators {
            if op.is_postfix {
                continue;
            }
            let max = map.entry(op.category.clone()).or_insert(0u8);
            *max = (*max).max(op.left_bp).max(op.right_bp);
        }
        map
    };

    // Extract rule_infos for FIRST set computation
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
                    SyntaxItemSpec::IdentCapture { .. }
                    | SyntaxItemSpec::Binder { .. }
                    | SyntaxItemSpec::BinderCollection { .. }
                    | SyntaxItemSpec::Collection { .. }
                    | SyntaxItemSpec::Sep { .. }
                    | SyntaxItemSpec::Map { .. }
                    | SyntaxItemSpec::Zip { .. }
                    | SyntaxItemSpec::Optional { .. } => FirstItem::Ident,
                })
                .collect(),
            is_infix: r.is_infix,
            is_var: r.is_var,
            is_literal: r.is_literal,
            is_cross_category: r.is_cross_category,
            is_cast: r.is_cast,
        })
        .collect();

    // Extract follow inputs (only category + syntax needed)
    let follow_inputs: Vec<FollowSetInput> = spec
        .rules
        .iter()
        .map(|r| FollowSetInput {
            category: r.category.clone(),
            syntax: r.syntax.clone(),
        })
        .collect();

    // Extract RD rules (without rust_code — it's never used by write_rd_handler)
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
                items: rule.syntax.iter().map(convert_syntax_item_to_rd).collect(),
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

    // Extract cross-category rules
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

    // Extract cast rules
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

    // Build all_syntax for lint layer (label, category, syntax triples)
    let all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = spec
        .rules
        .iter()
        .map(|r| (r.label.clone(), r.category.clone(), r.syntax.clone()))
        .collect();

    // Build rule_locations for lint layer (source location of each rule)
    let rule_locations: HashMap<(String, String), crate::SourceLocation> = spec
        .rules
        .iter()
        .filter_map(|r| {
            r.source_location.map(|loc| ((r.label.clone(), r.category.clone()), loc))
        })
        .collect();

    let parser_bundle = ParserBundle {
        grammar_name: spec.name.clone(),
        categories,
        bp_table,
        rule_infos,
        follow_inputs,
        rd_rules,
        cross_rules,
        cast_rules,
        has_binders,
        beam_width: spec.beam_width.clone(),
        recovery_config: spec.recovery_config.clone(),
        all_syntax,
        rule_locations,
        semantic_dependency_groups: spec.semantic_dependency_groups.clone(),
    };

    (lexer_bundle, parser_bundle)
}

// ══════════════════════════════════════════════════════════════════════════════
// Generate phase (parallel via rayon::join)
// ══════════════════════════════════════════════════════════════════════════════

/// Generate lexer code from the lexer bundle, returning the variant map
/// and ambiguity info alongside the generated code string.
fn generate_lexer_code_with_map(
    bundle: &LexerBundle,
) -> (String, TokenVariantMap, LexerAmbiguityInfo) {
    let mut lexer_input = extract_terminals(
        &bundle.grammar_rules,
        &bundle.type_infos,
        bundle.has_binders,
        &bundle.category_names,
    );
    lexer_input.literal_patterns = bundle.literal_patterns.clone();
    let (lexer_str, stats) = generate_lexer_as_string(&lexer_input);
    (lexer_str, stats.variant_map, stats.ambiguity_info)
}

/// Generate parser code with lexer context (variant map + ambiguity info).
///
/// Passes lexer context to `generate_parser_code()` so the composed dispatch
/// table can be computed once and used both for:
/// 1. Standard batch path: deterministic dispatch arms (no backtracking)
/// 2. Context-sensitive lex (feature-gated): Lexer struct, LexerAdapter, lazy parsers
fn generate_parser_code_with_context(
    bundle: &ParserBundle,
    variant_map: &TokenVariantMap,
    ambiguity_info: &LexerAmbiguityInfo,
) -> String {
    generate_parser_code(bundle, variant_map, ambiguity_info).0
}

/// Generate parser code with lexer context AND capture pipeline analysis data.
///
/// Returns both the generated code string and a [`PipelineAnalysis`] populated
/// from the pipeline's internal WFST data (dead rules, constructor weights, etc.).
fn generate_parser_code_with_analysis(
    bundle: &ParserBundle,
    variant_map: &TokenVariantMap,
    ambiguity_info: &LexerAmbiguityInfo,
) -> (String, crate::PipelineAnalysis) {
    generate_parser_code(bundle, variant_map, ambiguity_info)
}

/// Generate parser code from the parser bundle.
///
/// Runs: FIRST/FOLLOW sets → RD handlers → Pratt parsers → cross-category dispatch.
///
/// When `variant_map` and `ambiguity_info` are provided, computes the composed
/// dispatch table once and uses it to emit deterministic match arms in standard
/// batch dispatch (no backtracking).
///
/// Returns `(code_string, PipelineAnalysis)` where the analysis captures
/// WFST-derived data (dead rules, constructor weights, category weights)
/// for downstream optimization by the Ascent codegen in the macros crate.
fn generate_parser_code(
    bundle: &ParserBundle,
    variant_map: &TokenVariantMap,
    ambiguity_info: &LexerAmbiguityInfo,
) -> (String, crate::PipelineAnalysis) {
    let category_names: Vec<String> = bundle.categories.iter().map(|c| c.name.clone()).collect();
    let primary_category = category_names.first().map(|s| s.as_str()).unwrap_or("");

    // D07: Check if runtime coverage instrumentation is requested
    let emit_coverage = std::env::var("PRATTAIL_COVERAGE").is_ok();

    // Layer 10: Load incremental codegen cache (.prattail-cache)
    let cache_path = std::env::var("PRATTAIL_CACHE_DIR")
        .map(|d| std::path::PathBuf::from(d).join(".prattail-cache"))
        .ok();
    let prev_cache = cache_path.as_ref()
        .and_then(|p| crate::decision_tree::IncrementalState::load(p));
    let mut new_cache = crate::decision_tree::IncrementalState {
        version: crate::decision_tree::CACHE_VERSION,
        ..Default::default()
    };

    // Compute FIRST sets
    let mut first_sets = compute_first_sets(&bundle.rule_infos, &category_names);

    // Augment FIRST sets with native literal tokens
    for cat in &bundle.categories {
        if let Some(ref native_type) = cat.native_type {
            if let Some(first_set) = first_sets.get_mut(&cat.name) {
                match native_type.as_str() {
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
        }
    }

    // Augment FIRST sets with Ident for all categories.
    // Every category has auto-generated Var rules (e.g., IVar, BVar, FVar, SVar)
    // that accept Token::Ident as a prefix. These rules are synthesized by the
    // macros crate during code generation (not in LanguageSpec.rules), so the
    // fixed-point FIRST set computation doesn't see them. Without this, cross-
    // category dispatch never generates arms for Ident tokens, causing expressions
    // like `x >= 1` to fall through to the own-category parser and fail.
    for cat_name in &category_names {
        if let Some(first_set) = first_sets.get_mut(cat_name) {
            first_set.insert("Ident");
        }
    }

    // Augment FIRST sets with LParen for all categories.
    // Every category supports parenthesized grouping: `( expr )`.
    // Without this, cross-category dispatch classifies LParen as "unique to
    // source" (deterministic) instead of "ambiguous between source and target".
    // This causes deterministic arms to commit to a cross-category parse path
    // without fallback, breaking expressions like `(3+2)! == 120` where the
    // grouped arithmetic should be tried via both paths. Including LParen in
    // all FIRST sets makes it an ambiguous dispatch token, triggering save/
    // restore with proper fallback to parse_Cat_own.
    for cat_name in &category_names {
        if let Some(first_set) = first_sets.get_mut(cat_name) {
            first_set.insert("LParen");
        }
    }

    // Augment FIRST set of primary category with Caret and dollar tokens if grammar has binders
    if bundle.has_binders {
        if let Some(first_set) = first_sets.get_mut(primary_category) {
            first_set.insert("Caret");
            // Add dollar tokens: DollarProc, DdollarProcLp, etc.
            for cat in &bundle.categories {
                let cat_lower = cat.name.to_lowercase();
                let capitalized = capitalize_first(&cat_lower);
                first_set.insert(&format!("Dollar{}", capitalized));
                first_set.insert(&format!("Ddollar{}Lp", capitalized));
            }
        }
    }

    let overlaps = analyze_cross_category_overlaps(&category_names, &first_sets);

    // Compute FOLLOW sets from extracted inputs
    let follow_sets = compute_follow_sets_from_inputs(
        &bundle.follow_inputs,
        &category_names,
        &first_sets,
        primary_category,
    );

    // ── WFST construction ─────────────────────────────────────────────────
    // Build prediction WFSTs and recovery WFSTs from FIRST/FOLLOW/overlap data.
    // These are consulted by weighted dispatch and recovery codegen below.
    let (mut prediction_wfsts, mut recovery_wfsts, token_id_map) = {
        use crate::prediction::build_dispatch_action_tables;
        use crate::recovery::build_recovery_wfsts;
        use crate::token_id::TokenIdMap;
        use crate::wfst::build_prediction_wfsts;

        // Build native type map for dispatch action table extraction
        let native_types: std::collections::HashMap<String, Option<String>> = bundle
            .categories
            .iter()
            .map(|c| (c.name.clone(), c.native_type.clone()))
            .collect();

        // Build dispatch action tables (structured data for WFST weight assignment)
        let dispatch_actions = build_dispatch_action_tables(
            &category_names,
            &first_sets,
            &overlaps,
            &bundle.rd_rules,
            &bundle.cross_rules,
            &bundle.cast_rules,
            &native_types,
        );

        // Build prediction WFSTs (per-category, weight-ordered dispatch)
        let mut prediction_wfsts =
            build_prediction_wfsts(&category_names, &first_sets, &overlaps, &dispatch_actions);

        // Enrich WFSTs with two-token disambiguation paths.
        // For NFA-ambiguous groups where the second position (terminal or FIRST-expanded
        // nonterminal) uniquely identifies the rule, adds start → intermediate → accept
        // paths so predict_two_token() can resolve them.
        let two_token_paths_added = crate::wfst::enrich_with_two_token_paths(
            &mut prediction_wfsts,
            &bundle.rd_rules,
            &category_names,
            &first_sets,
        );
        if two_token_paths_added > 0 {
            pipeline_diagnostic(
                &bundle.grammar_name, "I02", "two-token-enrichment",
                crate::lint::LintSeverity::Info,
                format!("{} two-token disambiguation path(s) added to prediction WFSTs", two_token_paths_added),
                None,
            );
        }

        // Sprint 3: Assign ContextWeight bit positions to rules in each WFST.
        // For each category's PredictionWfst, find dispatch tokens that have
        // multiple competing rules (ambiguous groups). Assign sequential bit IDs
        // (0..N-1) to the rule labels so that `live_rules_context_after()` can
        // track which rules survive after consuming tokens.
        {
            let mut total_context_labels = 0usize;
            for wfst in prediction_wfsts.values_mut() {
                // Collect unique rule labels from all actions
                let mut rule_labels: Vec<String> = wfst.actions
                    .iter()
                    .map(|a| a.action.rule_label())
                    .collect();
                rule_labels.sort();
                rule_labels.dedup();
                if rule_labels.len() > 1 {
                    let label_refs: Vec<&str> = rule_labels.iter().map(|s| s.as_str()).collect();
                    wfst.assign_context_labels(&label_refs);
                    total_context_labels += rule_labels.len();
                }
            }
            if total_context_labels > 0 {
                pipeline_diagnostic(
                    &bundle.grammar_name, "I03", "context-weight-labels",
                    crate::lint::LintSeverity::Info,
                    format!("{} ContextWeight bit labels assigned across prediction WFSTs", total_context_labels),
                    None,
                );
            }
        }

        // B3: WFST minimization gate — skip cascade for trivial grammars.
        // The threshold is 4 WFST states: grammars below this (e.g., Lambda with
        // 2 states) gain no benefit from the cascade. Computed early (before the
        // cascade) using only total_wfst_states, which is available immediately
        // after build_prediction_wfsts().
        let total_wfst_states: usize = prediction_wfsts.values().map(|w| w.states.len()).sum();
        let run_cascade = total_wfst_states > 4;

        // E1: Transducer cascade — compose optimization passes into a fixed-point pipeline.
        // Replaces the standalone B3 minimization and beam width blocks with a unified
        // cascade that runs weight normalization → dead-state elimination → minimization
        // (→ beam pruning if configured) until convergence.
        // B3: Gated by WFST state count — trivial grammars skip the cascade.
        if run_cascade {
            let cascade = if let Some(beam_value) = bundle.beam_width.to_option() {
                crate::transducer::TransducerCascade::with_beam(beam_value)
            } else {
                crate::transducer::TransducerCascade::default_pipeline()
            };
            let summary = cascade.run_all(&mut prediction_wfsts);
            if !summary.is_empty() {
                pipeline_diagnostic(
                    &bundle.grammar_name, "I01", "transducer-cascade",
                    crate::lint::LintSeverity::Info, summary, None,
                );
            }
        } else {
            pipeline_diagnostic(
                &bundle.grammar_name, "I02", "cascade-skipped",
                crate::lint::LintSeverity::Info,
                format!("skipping transducer cascade ({} WFST states ≤ 4)", total_wfst_states),
                None,
            );
        }

        // Apply beam width configuration (stored on WFST for runtime predict_pruned)
        match &bundle.beam_width {
            crate::BeamWidthConfig::Explicit(beam_value) => {
                let beam = crate::automata::semiring::TropicalWeight::new(*beam_value);
                for wfst in prediction_wfsts.values_mut() {
                    wfst.set_beam_width(Some(beam));
                }
            }
            crate::BeamWidthConfig::Auto => {
                // A7: Entropy-based adaptive beam width per category.
                // When wfst-log is enabled, compute per-category Shannon entropy and
                // derive beam widths. Higher-entropy categories get wider beams.
                #[cfg(feature = "wfst-log")]
                {
                    for (cat_name, wfst) in prediction_wfsts.iter_mut() {
                        let (_entropy_nats, entropy_bits) = wfst.compute_entropy();
                        let beam_opt = crate::wfst::entropy_to_beam_width(
                            entropy_bits,
                            crate::wfst::ENTROPY_BEAM_BASE,
                            crate::wfst::ENTROPY_BEAM_SCALE,
                            crate::wfst::ENTROPY_BEAM_LOW_THRESHOLD,
                            crate::wfst::ENTROPY_BEAM_MAX,
                        );
                        if let Some(beam_value) = beam_opt {
                            let beam = crate::automata::semiring::TropicalWeight::new(beam_value);
                            wfst.set_beam_width(Some(beam));
                            pipeline_diagnostic(
                                &bundle.grammar_name, "I03", "adaptive-beam",
                                crate::lint::LintSeverity::Info,
                                format!("{}: entropy={:.2} bits → beam={:.2}", cat_name, entropy_bits, beam_value),
                                None,
                            );
                        } else {
                            pipeline_diagnostic(
                                &bundle.grammar_name, "I03", "adaptive-beam",
                                crate::lint::LintSeverity::Info,
                                format!("{}: entropy={:.2} bits → no beam (deterministic)", cat_name, entropy_bits),
                                None,
                            );
                        }
                    }
                }
                // Without wfst-log, Auto falls back to Disabled (no beam).
                #[cfg(not(feature = "wfst-log"))]
                {
                    pipeline_diagnostic(
                        &bundle.grammar_name, "I04", "beam-feature-required",
                        crate::lint::LintSeverity::Warning,
                        "beam_width: auto requires feature `wfst-log`; falling back to disabled".to_string(),
                        Some("enable `wfst-log` feature or use explicit beam_width".to_string()),
                    );
                }
            }
            crate::BeamWidthConfig::Disabled => {}
        }

        // NOTE: Dead-rule detection (W01) now handled by lint::run_lints() below.

        // Build token ID map from all FIRST set tokens (shared across recovery WFSTs)
        let mut all_tokens: Vec<String> = Vec::new();
        for first_set in first_sets.values() {
            all_tokens.extend(first_set.tokens.iter().cloned());
        }
        // Also include FOLLOW set tokens and structural tokens for recovery
        for follow_set in follow_sets.values() {
            all_tokens.extend(follow_set.tokens.iter().cloned());
        }
        all_tokens.push("Eof".to_string());
        all_tokens.push("RParen".to_string());
        all_tokens.push("RBrace".to_string());
        all_tokens.push("RBracket".to_string());
        all_tokens.push("Semi".to_string());
        all_tokens.push("Comma".to_string());
        let token_id_map = TokenIdMap::from_names(all_tokens);

        // Collect grammar terminals for recovery WFST construction
        let grammar_terminals_wfst: std::collections::HashSet<String> = {
            let mut terminals = std::collections::HashSet::new();
            for input in &bundle.follow_inputs {
                for t in collect_terminals_recursive(&input.syntax) {
                    terminals.insert(t);
                }
            }
            for delim in &["(", ")", "{", "}", "[", "]", ","] {
                terminals.insert(delim.to_string());
            }
            if bundle.has_binders {
                terminals.insert("^".to_string());
                terminals.insert(".".to_string());
            }
            terminals
        };

        // Build recovery WFSTs (per-category, weighted repair strategies)
        // B1: Thread prediction WFSTs into recovery construction for prediction-aware
        // discount factors on sync tokens (Tier 4 cost adjustment).
        let recovery_wfsts = build_recovery_wfsts(
            &category_names,
            &follow_sets,
            &grammar_terminals_wfst,
            &token_id_map,
            Some(&prediction_wfsts),
        );

        (prediction_wfsts, recovery_wfsts, token_id_map)
    };

    // ── WFST static embedding ─────────────────────────────────────────────
    // Emit prediction WFSTs as CSR-format static arrays with LazyLock constructors.
    // This makes the WFST data available at runtime for dynamic prediction
    // (e.g., with trained model weights overriding heuristic weights).
    let mut buf = String::with_capacity(8192);
    emit_prediction_wfst_static(&mut buf, &prediction_wfsts);
    emit_recovery_wfst_static(&mut buf, &recovery_wfsts);

    // Emit recovery beam width constant from RecoveryConfig.
    // Used by viterbi_multi_step() when multi-step recovery is wired (Sprint 8).
    {
        use std::fmt::Write;
        let beam_str = match bundle.recovery_config.beam_width {
            Some(w) => format!("Some({})", format_f64(w)),
            None => "None".to_string(),
        };
        write!(
            buf,
            "const RECOVERY_BEAM_WIDTH: Option<f64> = {};",
            beam_str
        )
        .unwrap();
    }

    // Emit ParseSimulator static data for Tier 3 recovery simulation.
    emit_parse_simulator_static(
        &mut buf,
        &first_sets,
        &follow_sets,
        &bundle.bp_table,
        &category_names,
        &token_id_map,
    );

    // Compute the set of token variant names that actually exist in the grammar's
    // Token enum. The TokenIdMap may contain superset tokens (e.g., Semi) that don't
    // appear in all grammars — emitting match arms for non-existent variants causes errors.
    let grammar_token_variants: std::collections::HashSet<String> = {
        let mut variants = std::collections::HashSet::new();
        // Always present
        variants.insert("Eof".to_string());
        variants.insert("Ident".to_string());
        // Native-type-derived builtin tokens
        for cat in &bundle.categories {
            match cat.native_type.as_deref() {
                Some("i32" | "i64" | "u32" | "u64" | "usize" | "isize") => {
                    variants.insert("Integer".to_string());
                }
                Some("f32" | "f64") => {
                    variants.insert("Float".to_string());
                }
                Some("bool") => {
                    variants.insert("Boolean".to_string());
                }
                Some("String" | "&str") => {
                    variants.insert("StringLit".to_string());
                }
                _ => {}
            }
        }
        // Structural delimiters (always in Token enum)
        for v in &["LParen", "RParen", "LBrace", "RBrace", "LBracket", "RBracket", "Comma"] {
            variants.insert(v.to_string());
        }
        // All FIRST set tokens (these must be in the Token enum)
        for fs in first_sets.values() {
            for tok in fs.sorted_tokens() {
                variants.insert(tok.to_string());
            }
        }
        // All FOLLOW set tokens
        for fs in follow_sets.values() {
            for tok in fs.sorted_tokens() {
                variants.insert(tok.to_string());
            }
        }
        variants
    };

    // Emit token_to_id helper for Tier 3 simulation (Token → u16 TokenId).
    emit_token_to_id_fn(&mut buf, &token_id_map, &grammar_token_variants);

    // Generate RD handlers
    let mut all_prefix_handlers: Vec<PrefixHandler> = Vec::with_capacity(bundle.rd_rules.len());

    for rd_rule in &bundle.rd_rules {
        let handler = write_rd_handler(&mut buf, rd_rule);
        all_prefix_handlers.push(handler);
    }

    // Generate lambda handlers for primary category if grammar has binders
    if bundle.has_binders {
        let lambda_handlers = write_lambda_handlers(&mut buf, primary_category, &category_names);
        all_prefix_handlers.extend(lambda_handlers);

        // Generate dollar-syntax handlers ($proc, $name, etc.) for function application
        let dollar_handlers = write_dollar_handlers(&mut buf, primary_category, &category_names);
        all_prefix_handlers.extend(dollar_handlers);
    }

    // Determine dispatch categories
    let dispatch_categories = categories_needing_dispatch(&bundle.cross_rules, &bundle.cast_rules);

    // ── Composed dispatch resolution ────────────────────────────────────────
    // Compute the composed dispatch table from lexer ambiguity info and
    // FIRST sets. This is used at codegen time to resolve ambiguous tokens
    // deterministically — eliminating save/restore backtracking in the
    // standard batch path. Computed before trampoline generation so that
    // composed weights are available for ident-lookahead handler sorting.
    use crate::prediction::{
        build_complete_weight_map, compute_composed_dispatch, resolve_dispatch_winners,
    };

    let (composed_resolutions, complete_weight_map, w05_diagnostics) =
        if ambiguity_info.has_ambiguous {
            let (composed, w05_diags) = compute_composed_dispatch(
                &ambiguity_info.ambiguous_states,
                &category_names,
                &first_sets,
                variant_map,
                Some(&prediction_wfsts),
                &bundle.rule_infos,
                &bundle.grammar_name,
            );

            // Build complete weight map covering ALL (category, token) pairs.
            // Ambiguous tokens use composed dispatch weights; deterministic tokens
            // use rule specificity weights. Used for dispatch arm ordering.
            let weight_map = build_complete_weight_map(
                &composed,
                &first_sets,
                &bundle.rule_infos,
                &category_names,
            );

            (
                Some(resolve_dispatch_winners(&composed)),
                Some(weight_map),
                w05_diags,
            )
        } else {
            // No ambiguous states — still build weight map for deterministic tokens
            let weight_map = build_complete_weight_map(
                &HashMap::new(),
                &first_sets,
                &bundle.rule_infos,
                &category_names,
            );
            (None, Some(weight_map), Vec::new())
        };

    // Detect which categories have NFA-ambiguous prefix groups (multiple rules
    // sharing the same dispatch token). These categories need thread-local spillover
    // buffers and forced-prefix replay for intra-category disambiguation.
    let mut nfa_spillover_categories = crate::trampoline::categories_needing_nfa_spillover(
        &bundle.rd_rules,
        &category_names,
    );

    // ── D1 + A3: Cost-benefit optimization analysis → optimization gating ──
    // Profile the grammar and evaluate which optimizations are beneficial.
    // Results are used to populate OptimizationGates, which controls which
    // compile-time optimization passes are emitted in codegen. This makes
    // the pipeline self-tuning per grammar.
    // The grammar_profile is computed once and reused for the D2 complexity report.
    let empty_dt: HashMap<String, crate::decision_tree::CategoryDecisionTree> = HashMap::new();
    let mut grammar_profile = crate::cost_benefit::build_grammar_profile(
        &prediction_wfsts,
        &first_sets,
        &nfa_spillover_categories,
        bundle.rule_infos.len(),
        bundle.beam_width.is_enabled(),
        &empty_dt,
    );
    let optimization_gates = {
        let recommended = crate::cost_benefit::recommended_optimizations(&grammar_profile);
        let gates = crate::cost_benefit::OptimizationGates::from_env_or_recommendations(&recommended);
        if !recommended.is_empty() {
            let detail_lines: Vec<String> = recommended.iter().map(|c| {
                format!("  {} (speedup={:.2}, cost={:.2}): {}", c.optimization, c.speedup.value(), c.compile_cost.value(), c.reason)
            }).collect();
            pipeline_diagnostic(
                &bundle.grammar_name, "I05", "cost-benefit-recommendations",
                crate::lint::LintSeverity::Info,
                format!(
                    "cost-benefit analysis recommends {} optimization(s):\n{}",
                    recommended.len(), detail_lines.join("\n"),
                ),
                None,
            );
        }
        gates
    };

    // ── A4: Dead-rule collection ─────────────────────────────────────────
    // Always compute dead rule labels for PipelineAnalysis export (consumed
    // by Ascent DCE in Sprint 1). When the enhanced_dce gate is also enabled,
    // these labels are additionally threaded into dispatch and trampoline
    // configs to suppress parser codegen for unreachable rules.
    // The lint layer still emits W01 warnings independently.
    let mut all_dead_rule_labels = collect_dead_rule_labels(
        &bundle.rule_infos,
        &bundle.categories,
        &first_sets,
        &prediction_wfsts,
        &bundle.semantic_dependency_groups,
        &HashMap::new(), // DTs not yet built; trie confirmation in 2nd pass below
    );
    let dead_rules: HashSet<String> = if optimization_gates.enhanced_dce {
        if !all_dead_rule_labels.is_empty() {
            let mut sorted: Vec<&str> = all_dead_rule_labels.iter().map(|s| s.as_str()).collect();
            sorted.sort_unstable();
            pipeline_diagnostic(
                &bundle.grammar_name, "I06", "enhanced-dce-active",
                crate::lint::LintSeverity::Info,
                format!(
                    "enhanced DCE: suppressing codegen for {} dead rule(s): [{}]",
                    all_dead_rule_labels.len(), sorted.join(", "),
                ),
                None,
            );
        }
        all_dead_rule_labels.clone()
    } else {
        HashSet::new()
    };

    // ── Decision tree construction ─────────────────────────────────────────
    // Build PathMap decision trees for all categories. The tree subsumes the
    // ad-hoc dispatch analyses (group_rd_by_dispatch_token, shared prefix,
    // second-token lookahead, suffix disjointness, etc.) into a single
    // unified trie-based mechanism. Built after FIRST sets and dead rules
    // are available; threaded into TrampolineConfig for codegen queries.
    let decision_trees = {
        use crate::decision_tree::DecisionTreeBuilder;
        let mut dt_builder = DecisionTreeBuilder::new(
            token_id_map.clone(),
            first_sets.clone(),
            category_names.clone(),
            dead_rules.clone(),
        );
        dt_builder.build_all(
            &bundle.rd_rules,
            &bundle.cross_rules,
            &bundle.cast_rules,
        );

        // ── Decision-tree diagnostics (D01–D09) ─────────────────────────────
        // Collect all DT diagnostics into a single Vec, then emit via the
        // standard lint framework for batching, grouping, and PRATTAIL_LINT_VERBOSE.
        let mut dt_diagnostics: Vec<crate::lint::LintDiagnostic> = Vec::new();

        for cat_name in &category_names {
            if let Some(tree) = dt_builder.get_tree(cat_name) {
                // D05: complexity metrics
                if tree.stats.total_states > 0 {
                    dt_diagnostics.push(
                        crate::decision_tree::complexity_metrics(tree, &bundle.grammar_name)
                    );
                }

                // D01: precision ambiguity
                dt_diagnostics.extend(
                    crate::decision_tree::precision_ambiguity_reports(tree, &token_id_map, &bundle.grammar_name)
                );

                // D02: unresolvable ambiguity
                dt_diagnostics.extend(
                    crate::decision_tree::unresolvable_ambiguity_reports(tree, &token_id_map, &bundle.grammar_name)
                );

                // D03: unreachable rules
                let all_labels: std::collections::HashSet<String> = bundle.rd_rules
                    .iter()
                    .filter(|r| r.category == *cat_name && !r.is_collection && r.prefix_bp.is_none())
                    .filter(|r| !matches!(
                        r.items.first(),
                        Some(crate::recursive::RDSyntaxItem::NonTerminal { .. }) |
                        Some(crate::recursive::RDSyntaxItem::IdentCapture { .. })
                    ))
                    .map(|r| r.label.clone())
                    .collect();
                dt_diagnostics.extend(
                    crate::decision_tree::unreachable_rule_detection(tree, &all_labels, &bundle.grammar_name)
                );

                // D04: min lookahead
                if tree.stats.total_states > 0 {
                    dt_diagnostics.push(
                        crate::decision_tree::min_lookahead_report(tree, &bundle.grammar_name)
                    );
                }
            }

            // D06: WFST consistency (needs both tree and wfst)
            if let (Some(tree), Some(wfst)) = (dt_builder.get_tree(cat_name), prediction_wfsts.get(cat_name)) {
                dt_diagnostics.extend(
                    crate::decision_tree::wfst_consistency_check(tree, wfst, &token_id_map, &bundle.grammar_name)
                );
            }

            if let Some(tree) = dt_builder.get_tree(cat_name) {
                // D08: optimization suggestions
                dt_diagnostics.extend(
                    crate::decision_tree::optimization_suggestions(tree, &bundle.grammar_name)
                );

                // D09: conflict resolution guidance
                dt_diagnostics.extend(
                    crate::decision_tree::conflict_resolution_guidance(tree, &bundle.grammar_name)
                );
            }
        }

        crate::lint::emit_diagnostics_for_grammar(&bundle.grammar_name, &dt_diagnostics);

        dt_builder
    };

    // ── Update grammar_profile with PathMap decision tree metrics ──────────
    {
        let dt_trees = decision_trees.trees();
        if !dt_trees.is_empty() {
            let mut total_depth = 0usize;
            let mut total_ambiguous = 0usize;
            let mut total_states = 0usize;
            let mut total_det_rules = 0usize;
            let mut total_rules = 0usize;
            for tree in dt_trees.values() {
                total_depth += tree.stats.max_depth;
                total_ambiguous += tree.stats.ambiguous_nodes;
                total_states += tree.stats.total_states;
                total_det_rules += tree.stats.deterministic_rules;
                total_rules += tree.stats.total_rules;
            }
            let n = dt_trees.len() as f64;
            grammar_profile.avg_trie_depth = total_depth as f64 / n;
            grammar_profile.ambiguity_score = if total_states > 0 {
                total_ambiguous as f64 / total_states as f64
            } else {
                0.0
            };
            grammar_profile.deterministic_ratio = if total_rules > 0 {
                total_det_rules as f64 / total_rules as f64
            } else {
                1.0
            };
        }
    }

    // ── 2a: Dispatch entropy analysis (optional) ───────────────────────────
    // Gated by PRATTAIL_ENTROPY=1 env var. Reports per-category dispatch
    // entropy to identify "decision bottlenecks" — tokens where grammar
    // restructuring would have maximum disambiguation impact.
    if std::env::var("PRATTAIL_ENTROPY").is_ok() {
        let dt_trees = decision_trees.trees();
        for (cat_name, tree) in dt_trees {
            let profile = tree.entropy_profile();
            if !profile.is_empty() {
                let lines: Vec<String> = profile.iter()
                    .take(5) // top 5 bottlenecks
                    .filter_map(|(byte, entropy, count)| {
                        token_id_map.name(*byte as u16).map(|name|
                            format!("{}: H={:.3}, {} rule(s)", name, entropy, count)
                        )
                    })
                    .collect();
                if !lines.is_empty() {
                    pipeline_diagnostic(
                        &bundle.grammar_name, "D11", "dispatch-entropy",
                        crate::lint::LintSeverity::Note,
                        format!(
                            "category {}: dispatch entropy (top bottlenecks): {}",
                            cat_name, lines.join("; "),
                        ),
                        None,
                    );
                }
            }
        }
    }

    // ── 2b: BP/dispatch correlation analysis (optional) ────────────────────
    // Gated by PRATTAIL_ENTROPY=1 env var (shared with entropy analysis).
    // Reports per-category BP stratification: how many rules are reachable
    // at each binding power level, enabling early-commit optimizations.
    if std::env::var("PRATTAIL_ENTROPY").is_ok() {
        let dt_trees = decision_trees.trees();
        for (cat_name, tree) in dt_trees {
            // Build a rule→BP map from the bp_table for this category
            let bp_map: HashMap<String, u8> = bundle.bp_table
                .operators_for_category(cat_name)
                .iter()
                .map(|op| (op.label.clone(), op.left_bp))
                .collect();
            let strata = tree.bp_stratification(&bp_map);
            if strata.len() > 1 {
                let lines: Vec<String> = strata.iter()
                    .map(|(bp, reachable, total)| {
                        format!("BP≤{}: {}/{} rules ({:.0}%)", bp, reachable, total,
                            *reachable as f64 / *total as f64 * 100.0)
                    })
                    .collect();
                pipeline_diagnostic(
                    &bundle.grammar_name, "D12", "bp-stratification",
                    crate::lint::LintSeverity::Note,
                    format!(
                        "category {}: BP stratification: {}",
                        cat_name, lines.join(", "),
                    ),
                    None,
                );
            }
        }
    }

    // ── 1.2a: Trie-informed WFST weight scaling ─────────────────────────────
    // Compute trie-informed weight adjustments from decision tree depth/ambiguity
    // and apply them to prediction WFST transition weights. Deeper unique prefixes
    // get lower weight (higher confidence), short shared prefixes get higher weight.
    {
        let dt_trees = decision_trees.trees();
        let trie_weight_adjustments =
            crate::decision_tree::compute_weight_adjustments(dt_trees, &token_id_map);
        for ((cat, token_variant), adjustment) in &trie_weight_adjustments {
            if let Some(wfst) = prediction_wfsts.get_mut(cat.as_str()) {
                wfst.adjust_weight(token_variant, *adjustment);
            }
        }
    }

    // ── 1.2b: Trie+WFST dead-rule confirmation (2nd pass) ──────────────────
    // Now that decision trees are built, re-run dead-rule collection with trie
    // reachability to confirm WfstUnreachable rules. Rules dead in BOTH the
    // WFST and the trie are added to the dead set.
    {
        let dt_trees = decision_trees.trees();
        let confirmed = collect_dead_rule_labels(
            &bundle.rule_infos,
            &bundle.categories,
            &first_sets,
            &prediction_wfsts,
            &bundle.semantic_dependency_groups,
            dt_trees,
        );
        let new_dead: Vec<String> = confirmed
            .difference(&all_dead_rule_labels)
            .cloned()
            .collect();
        if !new_dead.is_empty() {
            let mut sorted: Vec<&str> = new_dead.iter().map(|s| s.as_str()).collect();
            sorted.sort_unstable();
            pipeline_diagnostic(
                &bundle.grammar_name, "I07", "trie-confirmed-dead",
                crate::lint::LintSeverity::Info,
                format!(
                    "trie-confirmed dead: {} additional rule(s) confirmed dead via trie+WFST cross-validation: [{}]",
                    new_dead.len(), sorted.join(", "),
                ),
                None,
            );
            all_dead_rule_labels.extend(new_dead);
        }
    }

    // ── 1.3a: Trie-depth sync token ranking ─────────────────────────────────
    // Adjust recovery sync token discounts based on trie depth. Sync tokens at
    // trie root (depth 0) are preferred for error recovery; deep tokens are demoted.
    {
        let dt_trees = decision_trees.trees();
        let depth_discounts = crate::decision_tree::compute_sync_depth_discounts(
            dt_trees, &token_id_map,
        );
        if !depth_discounts.is_empty() {
            for rwfst in &mut recovery_wfsts {
                let cat_name = rwfst.category().to_string();
                let mut cat_discounts: std::collections::HashMap<u16, f64> =
                    std::collections::HashMap::new();
                for (&(ref cat, token_id), &discount) in &depth_discounts {
                    if cat == &cat_name {
                        // Merge with existing prediction discounts (multiply)
                        let existing = rwfst.prediction_discount(token_id);
                        cat_discounts.insert(token_id, existing * discount);
                    }
                }
                if !cat_discounts.is_empty() {
                    rwfst.set_prediction_discounts(cat_discounts);
                }
            }
        }
    }

    // ── 1.7a: Trie-pruned NFA spillover refinement ──────────────────────────
    // Refine NFA spillover set using decision tree dispatch strategy.
    // A category marked for NFA spillover by the ad-hoc grouping may actually
    // have disjoint suffixes (resolvable without backtracking) for all its
    // ambiguous tokens. Remove such categories from the spillover set.
    {
        let dt_trees = decision_trees.trees();
        let mut to_remove = Vec::new();
        for cat in &nfa_spillover_categories {
            if let Some(tree) = dt_trees.get(cat) {
                let dispatch_tokens = tree.dispatch_tokens(&token_id_map);
                let all_resolved = dispatch_tokens.iter().all(|token_variant| {
                    match tree.dispatch_strategy(token_variant, &token_id_map) {
                        crate::decision_tree::DispatchStrategy::NotPresent
                        | crate::decision_tree::DispatchStrategy::Singleton { .. }
                        | crate::decision_tree::DispatchStrategy::DisjointSuffix { .. } => true,
                        crate::decision_tree::DispatchStrategy::NfaTryAll { .. } => false,
                    }
                });
                if all_resolved {
                    to_remove.push(cat.clone());
                }
            }
        }
        if !to_remove.is_empty() {
            to_remove.sort();
            pipeline_diagnostic(
                &bundle.grammar_name, "I08", "trie-pruned-nfa-spillover",
                crate::lint::LintSeverity::Info,
                format!(
                    "trie-pruned NFA spillover: removed {} category(ies) with fully disjoint dispatch: [{}]",
                    to_remove.len(),
                    to_remove.join(", "),
                ),
                None,
            );
            for cat in &to_remove {
                nfa_spillover_categories.remove(cat);
            }
        }
    }

    // ── Sprint 4: Dead-prefix recovery weight penalty ──────────────────────
    // After trie+WFST dead-rule confirmation, detect "dead prefixes" — dispatch
    // tokens whose entire trie subtree leads only to dead rules. Increase their
    // recovery WFST weights (demoting them as recovery targets).
    // Data flow: WFST → Decision Tree → Dead Prefix → Recovery WFST
    {
        let dt_trees = decision_trees.trees();
        let dead_warnings = detect_dead_rules(
            &bundle.rule_infos,
            &bundle.categories,
            &first_sets,
            &prediction_wfsts,
            &bundle.semantic_dependency_groups,
            &nfa_spillover_categories,
            &bundle.rd_rules,
        );
        let dead_prefixes = detect_dead_prefixes(&dead_warnings, dt_trees, &token_id_map);
        if !dead_prefixes.is_empty() {
            const DEAD_PREFIX_WEIGHT_PENALTY: f64 = 2.0;
            let mut total_adjusted = 0usize;
            for rwfst in &mut recovery_wfsts {
                let cat_name = rwfst.category().to_string();
                if let Some(prefix_tokens) = dead_prefixes.get(&cat_name) {
                    let mut discounts: std::collections::HashMap<crate::token_id::TokenId, f64> =
                        std::collections::HashMap::new();
                    for token_variant in prefix_tokens {
                        if let Some(token_id) = token_id_map.get(token_variant) {
                            let existing = rwfst.prediction_discount(token_id);
                            // Increase weight = reduce discount (multiply by penalty)
                            discounts.insert(token_id, existing * DEAD_PREFIX_WEIGHT_PENALTY);
                            total_adjusted += 1;
                        }
                    }
                    if !discounts.is_empty() {
                        rwfst.set_prediction_discounts(discounts);
                    }
                }
            }
            if total_adjusted > 0 {
                pipeline_diagnostic(
                    &bundle.grammar_name, "I09", "dead-prefix-weight-penalty",
                    crate::lint::LintSeverity::Info,
                    format!(
                        "applied dead-prefix weight penalty (×{:.1}) to {} sync token(s) across {} category(ies)",
                        DEAD_PREFIX_WEIGHT_PENALTY, total_adjusted, dead_prefixes.len(),
                    ),
                    None,
                );
            }
        }
    }

    // ── G25: WPDS stack-aware reachability analysis ─────────────────────
    // Build WPDS and run poststar if the gate is enabled and grammar has ≥2 categories.
    let wpds_analysis = if optimization_gates.wpds_reachability
        && bundle.categories.len() >= 2
    {
        let wpds_cats: Vec<crate::wpds::WpdsCategoryInfo> = bundle
            .categories
            .iter()
            .map(|c| crate::wpds::WpdsCategoryInfo {
                name: c.name.clone(),
                is_primary: c.is_primary,
            })
            .collect();
        Some(crate::wpds::analyze_wpds_from_bundle(
            &bundle.grammar_name,
            &wpds_cats,
            &bundle.all_syntax,
            &prediction_wfsts,
        ))
    } else {
        None
    };

    // ── Unified lint layer ─────────────────────────────────────────────────
    // Construct LintContext with all pipeline data and run all lints.
    // Moved after decision tree construction so PathMap-derived lints
    // (G32, D10, W03 cross-category hotspot, etc.) can access decision_trees.
    {
        let dt_trees = decision_trees.trees();
        // Compute dead-rule warnings once for lint caching.
        // This replaces the duplicate detect_dead_rules() call that lint_w01
        // previously performed independently.
        let cached_dead_rule_warnings = crate::pipeline::detect_dead_rules(
            &bundle.rule_infos,
            &bundle.categories,
            &first_sets,
            &prediction_wfsts,
            &bundle.semantic_dependency_groups,
            &nfa_spillover_categories,
            &bundle.rd_rules,
        );

        let lint_ctx = crate::lint::LintContext {
            grammar_name: &bundle.grammar_name,
            rule_locations: &bundle.rule_locations,
            categories: &bundle.categories,
            rules: &bundle.rule_infos,
            rd_rules: &bundle.rd_rules,
            first_sets: &first_sets,
            follow_sets: &follow_sets,
            bp_table: &bundle.bp_table,
            prediction_wfsts: &prediction_wfsts,
            recovery_wfsts: &recovery_wfsts,
            cast_rules: &bundle.cast_rules,
            cross_rules: &bundle.cross_rules,
            nfa_spillover_categories: &nfa_spillover_categories,
            recovery_config: &bundle.recovery_config,
            all_syntax: &bundle.all_syntax,
            follow_inputs: &bundle.follow_inputs,
            semantic_dependency_groups: &bundle.semantic_dependency_groups,
            pre_collected_diagnostics: &w05_diagnostics,
            decision_trees: dt_trees,
            token_id_map: &token_id_map,
            dead_rule_warnings: &cached_dead_rule_warnings,
            grammar_profile: Some(&grammar_profile),
            wpds_analysis: wpds_analysis.as_ref(),
        };

        let diagnostics = crate::lint::run_lints(&lint_ctx);
        crate::lint::emit_diagnostics_for_grammar(&bundle.grammar_name, &diagnostics);
    }

    // ── A5: Ambiguity targeting analysis ──────────────────────────────────
    // Identify per-token ambiguity for downstream optimizations (B1, buffer
    // pre-sizing). The threshold=1 means any token with >1 alternative is
    // flagged as a candidate for multi-token lookahead.
    {
        let ambiguity_result = crate::cost_benefit::analyze_ambiguity_targets(
            &prediction_wfsts,
            &first_sets,
            1, // threshold: flag tokens with >1 alternative
        );
        if !ambiguity_result.ambiguous_tokens.is_empty() {
            let mut detail_lines: Vec<String> = ambiguity_result.ambiguous_tokens.iter().map(|info| {
                format!(
                    "  {}::{} — {} alternative(s): [{}]{}",
                    info.category, info.token, info.alternative_count,
                    info.rule_labels.join(", "),
                    if info.lookahead_candidate { " ← B1 candidate" } else { "" },
                )
            }).collect();
            if !ambiguity_result.presized_categories.is_empty() {
                detail_lines.push(format!(
                    "  NFA spillover pre-sizing: {}",
                    ambiguity_result.presized_categories
                        .iter()
                        .map(|(cat, sz)| format!("{}={}", cat, sz))
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
            pipeline_diagnostic(
                &bundle.grammar_name, "I07", "ambiguity-targeting",
                crate::lint::LintSeverity::Info,
                format!(
                    "ambiguity targeting: {} ambiguous token(s), {} unambiguous, max ambiguity={}\n{}",
                    ambiguity_result.ambiguous_tokens.len(),
                    ambiguity_result.unambiguous_count,
                    ambiguity_result.max_ambiguity,
                    detail_lines.join("\n"),
                ),
                None,
            );
        }
    }

    // ── D2: Grammar complexity report ─────────────────────────────────
    // Build and emit a unified complexity report that combines per-category
    // WFST metrics, ambiguity analysis, and optimization recommendations.
    // Reuses the grammar_profile computed above for D1 (no duplicate work).
    {
        let composed_entries = complete_weight_map.as_ref().map_or(0, |m| m.len());
        let resolved = composed_resolutions.as_ref().map_or(0, |r| r.len());
        let report = crate::cost_benefit::GrammarComplexityReport::build(
            &bundle.grammar_name,
            &grammar_profile,
            &prediction_wfsts,
            &first_sets,
            composed_entries,
            resolved,
        );
        crate::lint::emit_diagnostic(&report.to_diagnostic());
    }

    // Write parser helpers
    write_parser_helpers(&mut buf);

    // D07: Emit runtime coverage tracking module (gated by parser-coverage feature)
    if emit_coverage {
        buf.push_str(
            "#[cfg(feature = \"parser-coverage\")] \
             mod __coverage { \
                 use std::sync::Mutex; \
                 use std::collections::HashSet; \
                 static COVERED: Mutex<HashSet<(&'static str, u32)>> = Mutex::new(HashSet::new()); \
                 pub fn record(cat: &'static str, path_id: u32) { \
                     if let Ok(mut set) = COVERED.lock() { set.insert((cat, path_id)); } \
                 } \
                 pub fn dump() -> HashSet<(String, u32)> { \
                     COVERED.lock().map(|set| \
                         set.iter().map(|(c, id)| (c.to_string(), *id)).collect() \
                     ).unwrap_or_default() \
                 } \
                 pub fn reset() { \
                     if let Ok(mut set) = COVERED.lock() { set.clear(); } \
                 } \
             } ",
        );

        // D07 diagnostic: report number of instrumented categories
        let instrumented_cats: Vec<&str> = category_names.iter()
            .filter_map(|cat_name| {
                decision_trees.get_tree(cat_name)
                    .filter(|tree| tree.stats.total_states > 0)
                    .map(|_| cat_name.as_str())
            })
            .collect();
        if !instrumented_cats.is_empty() {
            pipeline_diagnostic(
                &bundle.grammar_name, "D07", "path-coverage-report",
                crate::lint::LintSeverity::Note,
                format!(
                    "{} categories instrumented for coverage tracking: [{}]",
                    instrumented_cats.len(),
                    instrumented_cats.join(", "),
                ),
                Some("run tests with `parser-coverage` feature enabled, then call __coverage::dump()".to_string()),
            );
        }
    }

    // Write trampolined parsers per category (stack-safe via explicit continuation stack)
    for cat in &bundle.categories {
        let has_infix = !bundle.bp_table.operators_for_category(&cat.name).is_empty();
        let has_postfix = !bundle
            .bp_table
            .postfix_operators_for_category(&cat.name)
            .is_empty();
        let has_mixfix = !bundle
            .bp_table
            .mixfix_operators_for_category(&cat.name)
            .is_empty();
        let needs_dispatch = dispatch_categories.contains(&cat.name);

        let cat_cast_rules: Vec<CastRule> = bundle
            .cast_rules
            .iter()
            .filter(|r| r.target_category == cat.name)
            .cloned()
            .collect();

        let own_first = first_sets.get(&cat.name).cloned().unwrap_or_default();
        let own_follow = follow_sets.get(&cat.name).cloned().unwrap_or_default();

        // Compute missing cast suggestions: for each source category that has
        // unique tokens (not in target's FIRST set) but NO cast rule to this
        // target category, map each unique token → source category name.
        let cast_suggestions: Vec<(String, String)> = {
            let existing_sources: std::collections::HashSet<&str> = cat_cast_rules
                .iter()
                .map(|r| r.source_category.as_str())
                .collect();
            let mut suggestions = Vec::new();
            for source_cat in &category_names {
                if source_cat == &cat.name {
                    continue; // skip self
                }
                if existing_sources.contains(source_cat.as_str()) {
                    continue; // cast rule already exists
                }
                if let Some(source_first) = first_sets.get(source_cat) {
                    let unique = source_first.difference(&own_first);
                    for token in unique.sorted_tokens() {
                        suggestions.push((token.to_string(), source_cat.clone()));
                    }
                }
            }
            suggestions
        };

        // Compute LED delegation for sum-type categories
        let projection_rules = detect_projection_rules(
            &cat.name,
            &cat_cast_rules,
            &bundle.rd_rules,
        );
        let led_delegation = compute_led_delegation(
            &cat.name,
            &cat_cast_rules,
            &bundle.cast_rules,
            &bundle.cross_rules,
            &bundle.bp_table,
            &projection_rules,
        );

        // 1.3b: Compute expected tokens string from decision tree dispatch tokens
        let expected_tokens_str = decision_trees.get_tree(&cat.name)
            .map(|tree| {
                let tokens = tree.dispatch_tokens(&token_id_map);
                if tokens.is_empty() {
                    format!("{} expression", cat.name)
                } else if tokens.len() <= 10 {
                    format!("one of: {}", tokens.join(", "))
                } else {
                    // Truncate very long token lists
                    let shown: Vec<&str> = tokens.iter().take(10).map(|s| s.as_str()).collect();
                    format!("one of: {}, ... ({} more)", shown.join(", "), tokens.len() - 10)
                }
            });

        let tramp_config = TrampolineConfig {
            category: cat.name.clone(),
            is_primary: cat.is_primary,
            has_infix,
            has_postfix,
            has_mixfix,
            all_categories: category_names.clone(),
            needs_dispatch,
            native_type: cat.native_type.clone(),
            cast_rules: cat_cast_rules,
            own_first_set: own_first,
            all_first_sets: first_sets.clone(),
            follow_set: own_follow,
            has_binders: bundle.has_binders,
            prediction_wfst: prediction_wfsts.get(&cat.name).cloned(),
            needs_nfa_spillover: nfa_spillover_categories.contains(&cat.name),
            cast_suggestions,
            optimization_gates: optimization_gates.clone(),
            dead_rules: dead_rules.clone(),
            complete_weight_map: complete_weight_map.clone(),
            led_delegation,
            decision_tree: decision_trees.get_tree(&cat.name).cloned(),
            emit_coverage,
            expected_tokens_str,
        };

        let cat_handlers: Vec<PrefixHandler> = all_prefix_handlers
            .iter()
            .filter(|h| h.category == cat.name)
            .cloned()
            .collect();

        // Layer 10: Incremental codegen — check if this category's code can be reused
        let current_hash = tramp_config.decision_tree.as_ref()
            .map(crate::decision_tree::category_content_hash);
        let cache_hit = current_hash.and_then(|h| {
            if let Some(ref prev) = prev_cache {
                if prev.is_valid() && prev.is_unchanged(&cat.name, h) {
                    return prev.category_code.get(&cat.name).cloned();
                }
            }
            None
        });

        if let Some(cached_code) = cache_hit {
            buf.push_str(&cached_code);
            if let Some(h) = current_hash {
                new_cache.record(&cat.name, h);
                new_cache.category_code.insert(cat.name.clone(), cached_code);
            }
        } else {
            let cat_start = buf.len();
            write_trampolined_parser(
                &mut buf,
                &tramp_config,
                &bundle.bp_table,
                &cat_handlers,
                &bundle.rd_rules,
            );
            let cat_code = buf[cat_start..].to_string();
            if let Some(h) = current_hash {
                new_cache.record(&cat.name, h);
                new_cache.category_code.insert(cat.name.clone(), cat_code);
            }
        }

    }

    // Write cross-category dispatch — uses composed resolutions for
    // deterministic arms (no backtracking)
    for cat in &bundle.categories {
        let cat_cross: Vec<CrossCategoryRule> = bundle
            .cross_rules
            .iter()
            .filter(|r| r.result_category == cat.name)
            .cloned()
            .collect();
        if cat_cross.is_empty() {
            continue;
        }

        // WFST-weighted dispatch (always-on)
        let wfst = prediction_wfsts.get(&cat.name).expect(
            "prediction WFST should exist for every category with cross-category rules"
        );
        write_category_dispatch(
            &mut buf,
            &cat.name,
            &cat_cross,
            &bundle.cast_rules,
            &overlaps,
            &first_sets,
            wfst,
            composed_resolutions.as_ref(),
            complete_weight_map.as_ref(),
            &optimization_gates,
            &dead_rules,
            &bundle.rd_rules,
        );
    }

    // ── Error recovery functions (parallel set, zero overhead on non-recovering path) ──

    // Collect all grammar terminals (raw strings) for sync predicate generation.
    // This determines which structural delimiters (";", ",", etc.) actually exist
    // in the grammar — only those will have corresponding Token variants.
    let grammar_terminals: std::collections::HashSet<String> = {
        let mut terminals = std::collections::HashSet::new();
        for input in &bundle.follow_inputs {
            for t in collect_terminals_recursive(&input.syntax) {
                terminals.insert(t);
            }
        }
        // Structural delimiters (){}[], are always in the terminal set
        for delim in &["(", ")", "{", "}", "[", "]", ","] {
            terminals.insert(delim.to_string());
        }
        // Binder terminals (^ and .) for lambda syntax
        if bundle.has_binders {
            terminals.insert("^".to_string());
            terminals.insert(".".to_string());
            // Dollar terminals for function application syntax
            for cat in &bundle.categories {
                let cat_lower = cat.name.to_lowercase();
                terminals.insert(format!("${}", cat_lower));
                terminals.insert(format!("$${}(", cat_lower));
            }
        }
        terminals
    };

    // Write recovery helpers (once)
    write_recovery_helpers(&mut buf);

    // Write sync predicates and recovering parsers per category
    for cat in &bundle.categories {
        let own_follow = follow_sets.get(&cat.name).cloned().unwrap_or_default();

        // Generate sync predicate: is_sync_Cat(token) -> bool
        generate_sync_predicate(&mut buf, &cat.name, &own_follow, &grammar_terminals);

        let needs_dispatch = dispatch_categories.contains(&cat.name);

        let tramp_config = TrampolineConfig {
            category: cat.name.clone(),
            is_primary: cat.is_primary,
            has_infix: !bundle.bp_table.operators_for_category(&cat.name).is_empty(),
            has_postfix: !bundle
                .bp_table
                .postfix_operators_for_category(&cat.name)
                .is_empty(),
            has_mixfix: !bundle
                .bp_table
                .mixfix_operators_for_category(&cat.name)
                .is_empty(),
            all_categories: category_names.clone(),
            needs_dispatch,
            native_type: cat.native_type.clone(),
            cast_rules: bundle
                .cast_rules
                .iter()
                .filter(|r| r.target_category == cat.name)
                .cloned()
                .collect(),
            own_first_set: first_sets.get(&cat.name).cloned().unwrap_or_default(),
            all_first_sets: first_sets.clone(),
            follow_set: own_follow,
            has_binders: bundle.has_binders,
            prediction_wfst: None, // Recovery wrappers don't need weighted dispatch
            needs_nfa_spillover: false, // Recovery path doesn't use NFA spillover
            cast_suggestions: Vec::new(), // Recovery path doesn't emit prefix match arms
            optimization_gates: optimization_gates.clone(),
            dead_rules: dead_rules.clone(),
            complete_weight_map: None, // Recovery path doesn't need composed weights
            decision_tree: None, // Recovery path doesn't use decision tree dispatch
            emit_coverage: false, // Recovery path doesn't need coverage tracking
            expected_tokens_str: None, // Recovery path uses its own error messages
            led_delegation: {
                let rec_cast_rules: Vec<CastRule> = bundle.cast_rules.iter()
                    .filter(|r| r.target_category == cat.name)
                    .cloned()
                    .collect();
                let rec_proj = detect_projection_rules(&cat.name, &rec_cast_rules, &bundle.rd_rules);
                compute_led_delegation(
                    &cat.name,
                    &rec_cast_rules,
                    &bundle.cast_rules,
                    &bundle.cross_rules,
                    &bundle.bp_table,
                    &rec_proj,
                )
            },
        };

        // Emit cross-category cast recovery static: for each source category
        // that has a cast rule to this category, list its FIRST set token IDs.
        // Used by Strategy 6 in wfst_recover_Cat for cross-category recovery.
        {
            use std::fmt::Write;
            let cat_cast_rules: Vec<_> = bundle
                .cast_rules
                .iter()
                .filter(|r| r.target_category == cat.name)
                .collect();

            // Only emit for multi-category grammars with cast rules
            if category_names.len() > 1 && !cat_cast_rules.is_empty() {
                write!(
                    buf,
                    "static CROSS_CAT_CASTS_{cat}: &[(&str, &[u16])] = &[",
                    cat = cat.name,
                )
                .unwrap();

                let mut first_entry = true;
                for cast_rule in &cat_cast_rules {
                    if let Some(source_first) = first_sets.get(&cast_rule.source_category) {
                        if !first_entry {
                            buf.push(',');
                        }
                        first_entry = false;
                        let ids: Vec<u16> = source_first
                            .sorted_tokens()
                            .iter()
                            .filter_map(|t| token_id_map.get(t))
                            .collect();
                        write!(buf, "(\"{}\", &[", cast_rule.source_category).unwrap();
                        for (i, id) in ids.iter().enumerate() {
                            if i > 0 {
                                buf.push(',');
                            }
                            write!(buf, "{}_u16", id).unwrap();
                        }
                        buf.push_str("])");
                    }
                }
                buf.push_str("];");
            }
        }

        // Generate WFST-based recovery function.
        // Generates a weighted recovery helper that evaluates skip, delete,
        // and substitute strategies — replacing the linear sync_to() scan.
        let has_cross_casts = category_names.len() > 1
            && bundle
                .cast_rules
                .iter()
                .any(|r| r.target_category == cat.name);
        if let Some(recovery_wfst) = recovery_wfsts.iter().find(|w| w.category() == cat.name) {
            generate_wfst_recovery_fn(
                &mut buf,
                &cat.name,
                recovery_wfst,
                has_cross_casts,
                &optimization_gates,
            );
        }

        // Generate recovering trampolined parser (wraps fail-fast trampoline with error catch)
        // Use WFST recovery when available
        if recovery_wfsts.iter().any(|w| w.category() == cat.name) {
            write_trampolined_parser_recovering_wfst(&mut buf, &tramp_config);
        } else {
            write_trampolined_parser_recovering(
                &mut buf,
                &tramp_config,
                &bundle.bp_table,
                &crate::trampoline::FrameInfo {
                    enum_name: format!("Frame_{}", cat.name),
                    variants: Vec::new(),
                },
            );
        }

        // Generate recovering dispatch wrapper if needed
        if needs_dispatch {
            write_dispatch_recovering(&mut buf, &cat.name);
        }
    }

    // Debug dump: write generated parser code to file for inspection
    if let Ok(dump_dir) = std::env::var("PRATTAIL_DUMP_PARSER") {
        let dir = if dump_dir == "1" {
            ".".to_string()
        } else {
            dump_dir
        };
        let cat_suffix = category_names.join("-");
        let filename = format!("{}/prattail-parser-{}.rs", dir, cat_suffix);
        if let Ok(()) = std::fs::write(&filename, &buf) {
            eprintln!("PraTTaIL: dumped parser code to {}", filename);
        }
    }

    // ── Build PipelineAnalysis from computed data ──────────────────────────
    // Uses all_dead_rule_labels (unconditionally computed) rather than
    // dead_rules (gated by enhanced_dce) so Ascent DCE always has full data.
    let analysis = build_pipeline_analysis(
        &all_dead_rule_labels,
        &prediction_wfsts,
        &bundle.categories,
        &bundle.rule_infos,
        decision_trees.trees().clone(),
    );

    // Layer 10: Save updated incremental state to .prattail-cache
    if let Some(ref path) = cache_path {
        let _ = new_cache.save(path); // Best-effort; don't fail on cache write error
    }

    (buf, analysis)
}

/// Build a [`PipelineAnalysis`] from the data computed during parser code generation.
///
/// Extracts constructor weights from prediction WFSTs, computes category-level
/// averages, and identifies fully unreachable categories. Isomorphic group
/// detection is deferred to Sprint 8.
fn build_pipeline_analysis(
    dead_rules: &HashSet<String>,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    categories: &[CategoryInfo],
    rule_infos: &[RuleInfo],
    decision_trees: HashMap<String, crate::decision_tree::CategoryDecisionTree>,
) -> crate::PipelineAnalysis {
    let mut constructor_weights = HashMap::new();
    let mut category_weights = HashMap::new();

    // Extract per-constructor weights from each category's PredictionWfst.
    // Each WeightedAction in the WFST's action table maps a dispatch decision
    // (constructor rule label) to a tropical weight (lower = more frequent).
    for (cat_name, wfst) in prediction_wfsts {
        let mut cat_total_weight = 0.0_f64;
        let mut cat_action_count = 0_usize;

        for action in &wfst.actions {
            let label = action.action.rule_label();
            let weight = action.weight.value();
            // Use the minimum weight if a constructor appears in multiple categories.
            // Minimum weight = highest frequency = most useful for ordering.
            let entry = constructor_weights.entry(label).or_insert(f64::INFINITY);
            if weight < *entry {
                *entry = weight;
            }
            cat_total_weight += weight;
            cat_action_count += 1;
        }

        if cat_action_count > 0 {
            category_weights.insert(
                cat_name.clone(),
                cat_total_weight / cat_action_count as f64,
            );
        }
    }

    // Determine unreachable categories: categories where ALL rules are dead.
    let mut unreachable_categories = HashSet::new();
    for cat in categories {
        let all_dead = rule_infos
            .iter()
            .filter(|r| r.category == cat.name)
            .all(|r| dead_rules.contains(&r.label));
        // Only mark as unreachable if the category actually has rules
        let has_rules = rule_infos.iter().any(|r| r.category == cat.name);
        if has_rules && all_dead {
            unreachable_categories.insert(cat.name.clone());
        }
    }

    // Sprint 8: Detect isomorphic WFST groups using De Bruijn canonicalization.
    let isomorphic_groups =
        group_isomorphic_wfsts(prediction_wfsts);
    let isomorphic_action_maps =
        build_isomorphic_action_maps(prediction_wfsts, &isomorphic_groups);

    crate::PipelineAnalysis {
        dead_rule_labels: dead_rules.clone(),
        unreachable_categories,
        constructor_weights,
        category_weights,
        isomorphic_groups,
        isomorphic_action_maps,
        decision_trees,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sprint 8: Isomorphic WFST detection
// ══════════════════════════════════════════════════════════════════════════════

/// Group categories whose PredictionWFSTs are alpha-equivalent (isomorphic).
///
/// Two WFSTs are alpha-equivalent if they have identical De Bruijn-canonicalized
/// structure: same states, same transitions, same weights, same action shapes —
/// but potentially different action labels (rule names, category names).
///
/// Only returns groups with ≥2 members. Categories within each group are sorted
/// alphabetically for deterministic output.
fn group_isomorphic_wfsts(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
) -> Vec<Vec<String>> {
    use crate::wfst::CanonicalWfstStructure;

    // Compute canonical structure for each category's WFST
    let mut canonical_groups: HashMap<CanonicalWfstStructure, Vec<String>> = HashMap::new();

    for (cat_name, wfst) in prediction_wfsts {
        let canonical = wfst.canonical_structure();
        canonical_groups
            .entry(canonical)
            .or_default()
            .push(cat_name.clone());
    }

    // Keep only groups with ≥2 members, sort members for deterministic output
    let mut groups: Vec<Vec<String>> = canonical_groups
        .into_values()
        .filter(|group| group.len() >= 2)
        .map(|mut group| {
            group.sort();
            group
        })
        .collect();

    // Sort groups by first member for deterministic ordering
    groups.sort_by(|a, b| a[0].cmp(&b[0]));
    groups
}

/// Build per-group De Bruijn action maps.
///
/// For each isomorphic group, maps De Bruijn action index → `Vec<(category, rule_label)>`.
/// This records which concrete action label in each category corresponds to each
/// De Bruijn position, enabling template instantiation to substitute the correct names.
fn build_isomorphic_action_maps(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    isomorphic_groups: &[Vec<String>],
) -> Vec<HashMap<u32, Vec<(String, String)>>> {
    isomorphic_groups
        .iter()
        .map(|group| {
            let mut action_map: HashMap<u32, Vec<(String, String)>> = HashMap::new();

            for cat_name in group {
                if let Some(wfst) = prediction_wfsts.get(cat_name) {
                    // Re-compute the De Bruijn mapping for this WFST
                    let mut action_debruijn: HashMap<u32, u32> = HashMap::new();
                    let mut next_debruijn: u32 = 0;

                    for state in &wfst.states {
                        let mut sorted_trans: Vec<_> = state.transitions.iter().collect();
                        sorted_trans.sort_by_key(|t| (t.input, t.action_idx));

                        for t in sorted_trans {
                            let db_idx =
                                *action_debruijn.entry(t.action_idx).or_insert_with(|| {
                                    let idx = next_debruijn;
                                    next_debruijn += 1;
                                    idx
                                });

                            // Record this category's concrete label at this De Bruijn position
                            if let Some(wa) = wfst.actions.get(t.action_idx as usize) {
                                let label = wa.action.rule_label();
                                action_map
                                    .entry(db_idx)
                                    .or_default()
                                    .push((cat_name.clone(), label));
                            }
                        }
                    }
                }
            }

            // Deduplicate: each (category, label) pair should appear only once per De Bruijn index
            for entries in action_map.values_mut() {
                entries.sort();
                entries.dedup();
            }

            action_map
        })
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// Helper functions (moved from lib.rs — only used by the pipeline)
// ══════════════════════════════════════════════════════════════════════════════

/// Capitalize the first letter of a string.
fn capitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => {
            let mut result = String::with_capacity(s.len());
            result.extend(first.to_uppercase());
            result.extend(chars);
            result
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// LED delegation computation
// ══════════════════════════════════════════════════════════════════════════════

use crate::pratt::{CrossCatLedOp, LedDelegationSource};

/// Compute LED delegation sources for a sum-type category.
///
/// A sum-type category is one that has cast rules from constituents (e.g., `Proc` has
/// `CastInt . a:Int |- a : Proc`). For each constituent (source category), this function
/// collects:
/// 1. Whether the source has same-category infix, postfix, or mixfix operators
/// 2. Cross-category operators FROM the source (e.g., `EqInt . a:Int, b:Int |- a "==" b : Bool`)
/// 3. The re-wrap label for cross-cat results (e.g., `CastBool` wrapping Bool → Proc)
/// 4. Projection labels for auto-projection (Phase 2)
///
/// Uses `cross_rules` (with correct `source_category` field) NOT `bp_table` for cross-cat ops.
fn compute_led_delegation(
    cat_name: &str,
    cat_cast_rules: &[CastRule],
    all_cast_rules: &[CastRule],
    cross_rules: &[CrossCategoryRule],
    bp_table: &crate::binding_power::BindingPowerTable,
    projection_rules: &HashMap<String, String>,
) -> Vec<LedDelegationSource> {
    if cat_cast_rules.is_empty() {
        return Vec::new();
    }

    let mut sources: Vec<LedDelegationSource> = Vec::with_capacity(cat_cast_rules.len());

    for cast_rule in cat_cast_rules {
        let source = &cast_rule.source_category;

        // Check if source has same-category operators
        let has_infix = !bp_table.operators_for_category(source).is_empty();
        let has_postfix = !bp_table.postfix_operators_for_category(source).is_empty();
        let has_mixfix = !bp_table.mixfix_operators_for_category(source).is_empty();

        // Collect cross-category operators FROM this source
        let mut cross_cat_ops: Vec<CrossCatLedOp> = Vec::new();
        for cross_rule in cross_rules {
            if cross_rule.source_category != *source {
                continue;
            }

            // Find the re-wrap cast rule: result_category → cat_name
            // E.g., if cross_rule.result_category == "Bool" and cat_name == "Proc",
            // find CastRule { source: "Bool", target: "Proc", label: "CastBool" }
            let rewrap = all_cast_rules.iter().find(|cr| {
                cr.source_category == cross_rule.result_category
                    && cr.target_category == cat_name
            });

            if let Some(rewrap_rule) = rewrap {
                // Get BP from the BP table for this cross-cat operator
                let bp_op = bp_table.operators.iter().find(|op| {
                    op.label == cross_rule.label && op.is_cross_category
                });
                let (left_bp, right_bp) = bp_op
                    .map(|op| (op.left_bp, op.right_bp))
                    .unwrap_or((0, 0));

                cross_cat_ops.push(CrossCatLedOp {
                    terminal: cross_rule.operator.clone(),
                    result_category: cross_rule.result_category.clone(),
                    label: cross_rule.label.clone(),
                    rewrap_label: rewrap_rule.label.clone(),
                    left_bp,
                    right_bp,
                });
            }
            // If no re-wrap rule exists, skip this cross-cat operator
            // (can't wrap the result back into the sum type)
        }

        // Only include source if it has at least one LED-relevant operator
        if !has_infix && !has_postfix && !has_mixfix && cross_cat_ops.is_empty() {
            continue;
        }

        let projection_label = projection_rules.get(source).cloned();

        sources.push(LedDelegationSource {
            cast_label: cast_rule.label.clone(),
            source_category: source.clone(),
            has_infix,
            has_postfix,
            has_mixfix,
            cross_cat_ops,
            projection_label,
        });
    }

    sources
}

/// Detect projection rules in the grammar.
///
/// A projection rule is one where:
/// - It has exactly one NonTerminal parameter of the sum-type category
/// - The result category is a constituent (has a cast INTO the sum type)
/// - It is NOT itself a cast rule or infix rule
///
/// Returns a map: source_category → projection_label.
fn detect_projection_rules(
    cat_name: &str,
    cat_cast_rules: &[CastRule],
    rd_rules: &[crate::recursive::RDRuleInfo],
) -> HashMap<String, String> {
    let constituent_sources: HashSet<&str> = cat_cast_rules
        .iter()
        .map(|cr| cr.source_category.as_str())
        .collect();

    let mut projections: HashMap<String, String> = HashMap::new();

    for rd_rule in rd_rules {
        // The result category must be a constituent (has cast into sum type)
        if !constituent_sources.contains(rd_rule.category.as_str()) {
            continue;
        }

        // Check if the rule has exactly one NonTerminal parameter of the sum-type category
        let sum_type_params: Vec<&crate::recursive::RDSyntaxItem> = rd_rule.items.iter()
            .filter(|item| matches!(
                item,
                crate::recursive::RDSyntaxItem::NonTerminal { category, .. }
                    if category == cat_name
            ))
            .collect();

        if sum_type_params.len() != 1 {
            continue;
        }

        // Must not already have a projection for this target category
        if projections.contains_key(&rd_rule.category) {
            continue;
        }

        projections.insert(rd_rule.category.clone(), rd_rule.label.clone());
    }

    projections
}

/// Recursively collect all terminal strings from a list of syntax items.
///
/// This extracts terminals from top-level items AND from nested structures
/// like `Sep`/`Map`/`Zip` body items and separators.
fn collect_terminals_recursive(items: &[SyntaxItemSpec]) -> Vec<String> {
    let mut terminals = Vec::new();
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(t) => terminals.push(t.clone()),
            SyntaxItemSpec::Collection { separator, .. }
            | SyntaxItemSpec::BinderCollection { separator, .. } => {
                terminals.push(separator.clone());
            },
            SyntaxItemSpec::Sep { body, separator, .. } => {
                terminals.extend(collect_terminals_recursive(std::slice::from_ref(body.as_ref())));
                terminals.push(separator.clone());
            },
            SyntaxItemSpec::Map { body_items } => {
                terminals.extend(collect_terminals_recursive(body_items));
            },
            SyntaxItemSpec::Zip { body, .. } => {
                terminals.extend(collect_terminals_recursive(std::slice::from_ref(body.as_ref())));
            },
            SyntaxItemSpec::Optional { inner } => {
                terminals.extend(collect_terminals_recursive(inner));
            },
            _ => {},
        }
    }
    terminals.sort();
    terminals.dedup();
    terminals
}

/// Detect whether an infix rule is mixfix and extract its parts.
///
/// A rule is mixfix if its syntax pattern has 3+ operands (NonTerminal items)
/// with 2+ interleaved terminals. The first operand is the left operand
/// (handled by the Pratt loop), and subsequent operand-terminal pairs
/// become `MixfixPart`s.
///
/// Returns `(is_mixfix, parts)` where `parts` is empty for non-mixfix rules.
///
/// Example: `cond "?" then ":" else` → parts = [
///   MixfixPart { category: "Int", param: "then", following: Some(":") },
///   MixfixPart { category: "Int", param: "else", following: None },
/// ]
fn extract_mixfix_parts(syntax: &[SyntaxItemSpec]) -> (bool, Vec<MixfixPart>) {
    // Count operands (NonTerminal) and terminals
    let operand_count = syntax
        .iter()
        .filter(|item| matches!(item, SyntaxItemSpec::NonTerminal { .. }))
        .count();
    let terminal_count = syntax
        .iter()
        .filter(|item| matches!(item, SyntaxItemSpec::Terminal(_)))
        .count();

    // Mixfix: 3+ operands, 2+ terminals
    // (Regular infix: 2 operands, 1 terminal. Postfix: 1 operand, 1 terminal.)
    if operand_count < 3 || terminal_count < 2 {
        return (false, Vec::new());
    }

    // Extract parts: skip the first operand (left) and first terminal (trigger).
    // Remaining items alternate: NonTerminal, Terminal, NonTerminal, Terminal, ..., NonTerminal
    let mut parts = Vec::with_capacity(operand_count - 1);
    let mut after_trigger = false;
    let mut skip_count = 0;

    for item in syntax {
        match item {
            SyntaxItemSpec::NonTerminal { category: _, param_name: _ } if skip_count == 0 => {
                // First NonTerminal = left operand, skip it
                skip_count += 1;
            },
            SyntaxItemSpec::Terminal(_) if !after_trigger => {
                // First Terminal = trigger, skip it
                after_trigger = true;
            },
            SyntaxItemSpec::NonTerminal { category, param_name } if after_trigger => {
                parts.push(MixfixPart {
                    operand_category: category.clone(),
                    param_name: param_name.clone(),
                    following_terminal: None, // will be filled below
                });
            },
            SyntaxItemSpec::Terminal(t) if after_trigger => {
                // This terminal follows the previous part
                if let Some(last_part) = parts.last_mut() {
                    last_part.following_terminal = Some(t.clone());
                }
            },
            _ => {},
        }
    }

    (true, parts)
}

/// Convert a `SyntaxItemSpec` to an `RDSyntaxItem`.
///
/// Used for converting syntax items when building `RDRuleInfo` from `RuleSpec`.
pub(crate) fn convert_syntax_item_to_rd(item: &SyntaxItemSpec) -> RDSyntaxItem {
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
        SyntaxItemSpec::Sep { body, separator, kind } => RDSyntaxItem::Sep {
            body: Box::new(convert_syntax_item_to_rd(body)),
            separator: separator.clone(),
            kind: *kind,
        },
        SyntaxItemSpec::Map { body_items } => RDSyntaxItem::Map {
            body_items: body_items.iter().map(convert_syntax_item_to_rd).collect(),
        },
        SyntaxItemSpec::Zip { left_name, right_name, left_category, right_category, body } => {
            RDSyntaxItem::Zip {
                left_name: left_name.clone(),
                right_name: right_name.clone(),
                left_category: left_category.clone(),
                right_category: right_category.clone(),
                body: Box::new(convert_syntax_item_to_rd(body)),
            }
        },
        SyntaxItemSpec::BinderCollection { param_name, separator } => {
            RDSyntaxItem::BinderCollection {
                param_name: param_name.clone(),
                separator: separator.clone(),
            }
        },
        SyntaxItemSpec::Optional { inner } => RDSyntaxItem::Optional {
            inner: inner.iter().map(convert_syntax_item_to_rd).collect(),
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Format an `f64` as a valid Rust literal. Handles infinities and NaN
/// which `{:?}` would render as `inf` / `nan` — not valid Rust tokens.
fn format_f64(v: f64) -> String {
    if v.is_infinite() && v.is_sign_positive() {
        "f64::INFINITY".to_string()
    } else if v.is_infinite() {
        "f64::NEG_INFINITY".to_string()
    } else if v.is_nan() {
        "f64::NAN".to_string()
    } else {
        format!("{:?}_f64", v)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST static embedding (always-on)
// ══════════════════════════════════════════════════════════════════════════════

/// Emit a `PredictionWfst` as CSR-format static arrays with a `LazyLock` constructor.
///
/// For each category with a prediction WFST, generates:
/// ```text
/// static WFST_TRANSITIONS_Cat: &[(u16, u32, f64)] = &[ ... ];
/// static WFST_STATE_OFFSETS_Cat: &[(usize, usize, bool, f64)] = &[ ... ];
/// static WFST_TOKEN_NAMES_Cat: &[&str] = &[ ... ];
/// static WFST_BEAM_WIDTH_Cat: Option<f64> = Some(1.5);  // or None
///
/// static PREDICTION_Cat: std::sync::LazyLock<mettail_prattail::wfst::PredictionWfst> =
///     std::sync::LazyLock::new(|| {
///         mettail_prattail::wfst::PredictionWfst::from_flat(
///             "Cat",
///             WFST_STATE_OFFSETS_Cat,
///             WFST_TRANSITIONS_Cat,
///             WFST_TOKEN_NAMES_Cat,
///             WFST_BEAM_WIDTH_Cat,
///         )
///     });
/// ```
///
/// The `LazyLock` is initialized on first access and persists for the process
/// lifetime. Since the data is entirely `static`, there is no runtime I/O.
fn emit_prediction_wfst_static(
    buf: &mut String,
    prediction_wfsts: &std::collections::HashMap<String, crate::wfst::PredictionWfst>,
) {
    use std::fmt::Write;

    for (category, wfst) in prediction_wfsts {
        if wfst.num_actions() == 0 {
            continue;
        }

        // ── Flatten transitions into CSR format ──
        let mut transitions_flat: Vec<(u16, u32, f64)> = Vec::new();
        let mut state_offsets: Vec<(usize, usize, bool, f64)> =
            Vec::with_capacity(wfst.states.len());

        for state in &wfst.states {
            let trans_start = transitions_flat.len();
            let trans_count = state.transitions.len();
            for t in &state.transitions {
                transitions_flat.push((t.input, t.to, t.weight.value()));
            }
            state_offsets.push((
                trans_start,
                trans_count,
                state.is_final,
                state.final_weight.value(),
            ));
        }

        // ── Collect token names from the token map ──
        let mut token_names: Vec<String> = Vec::with_capacity(wfst.token_map.len());
        for i in 0..wfst.token_map.len() {
            if let Some(name) = wfst.token_map.name(i as u16) {
                token_names.push(name.to_string());
            }
        }

        // ── Emit static arrays ──
        // Transitions
        write!(buf, "static WFST_TRANSITIONS_{cat}: &[(u16, u32, f64)] = &[", cat = category,)
            .unwrap();
        for (i, (token_id, target, weight)) in transitions_flat.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "({}_u16, {}_u32, {})", token_id, target, format_f64(*weight)).unwrap();
        }
        buf.push_str("];");

        // State offsets
        write!(
            buf,
            "static WFST_STATE_OFFSETS_{cat}: &[(usize, usize, bool, f64)] = &[",
            cat = category,
        )
        .unwrap();
        for (i, (start, count, is_final, fw)) in state_offsets.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "({}_usize, {}_usize, {}, {})", start, count, is_final, format_f64(*fw)).unwrap();
        }
        buf.push_str("];");

        // Token names
        write!(buf, "static WFST_TOKEN_NAMES_{cat}: &[&str] = &[", cat = category,).unwrap();
        for (i, name) in token_names.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "\"{}\"", name).unwrap();
        }
        buf.push_str("];");

        // Beam width
        match wfst.beam_width {
            Some(bw) => write!(
                buf,
                "static WFST_BEAM_WIDTH_{}: Option<f64> = Some({});",
                category, format_f64(bw.value()),
            )
            .unwrap(),
            None => {
                write!(buf, "static WFST_BEAM_WIDTH_{cat}: Option<f64> = None;", cat = category,)
                    .unwrap()
            },
        }

        // LazyLock constructor
        write!(buf,
            "static PREDICTION_{cat}: std::sync::LazyLock<mettail_prattail::wfst::PredictionWfst> = \
             std::sync::LazyLock::new(|| {{ \
                mettail_prattail::wfst::PredictionWfst::from_flat(\
                    \"{cat}\", \
                    WFST_STATE_OFFSETS_{cat}, \
                    WFST_TRANSITIONS_{cat}, \
                    WFST_TOKEN_NAMES_{cat}, \
                    WFST_BEAM_WIDTH_{cat}, \
                ) \
             }});",
            cat = category,
        ).unwrap();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST recovery static embedding (always-on)
// ══════════════════════════════════════════════════════════════════════════════

/// Emit recovery WFST data as static arrays for runtime context-aware recovery.
///
/// For each category with a recovery WFST, generates:
/// ```text
/// static RECOVERY_SYNC_TOKENS_Cat: &[u16] = &[...];
/// static RECOVERY_SYNC_SOURCES_Cat: &[(u16, u8)] = &[...];
/// static RECOVERY_TOKEN_NAMES_Cat: &[&str] = &[...];
/// ```
///
/// These arrays are consumed by `RecoveryWfst::from_flat()` at runtime when
/// full context-aware recovery is needed (Sprint 4).
fn emit_recovery_wfst_static(buf: &mut String, recovery_wfsts: &[crate::recovery::RecoveryWfst]) {
    use std::fmt::Write;

    for recovery_wfst in recovery_wfsts {
        let cat = recovery_wfst.category();

        // Sync token IDs (sorted)
        let sync_ids: Vec<u16> = recovery_wfst.sync_tokens().iter().copied().collect();
        write!(buf, "static RECOVERY_SYNC_TOKENS_{cat}: &[u16] = &[",).unwrap();
        for (i, id) in sync_ids.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "{}_u16", id).unwrap();
        }
        buf.push_str("];");

        // Sync sources: (token_id, source_tag)
        // 0=Eof, 1=StructuralDelimiter, 2=FollowSet
        write!(buf, "static RECOVERY_SYNC_SOURCES_{cat}: &[(u16, u8)] = &[",).unwrap();
        for (i, &id) in sync_ids.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            let source_tag = match recovery_wfst.token_name(id) {
                Some("Eof") => 0_u8,
                Some("RParen" | "RBrace" | "RBracket" | "Semi" | "Comma") => 1_u8,
                _ => 2_u8,
            };
            write!(buf, "({}_u16, {}_u8)", id, source_tag).unwrap();
        }
        buf.push_str("];");

        // Token names for reconstructing TokenIdMap
        let mut token_names: Vec<String> = Vec::new();
        // Recover all token names from the sync set
        for &id in recovery_wfst.sync_tokens() {
            if let Some(name) = recovery_wfst.token_name(id) {
                token_names.push(name.to_string());
            }
        }
        token_names.sort();
        token_names.dedup();

        write!(buf, "static RECOVERY_TOKEN_NAMES_{cat}: &[&str] = &[",).unwrap();
        for (i, name) in token_names.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "\"{}\"", name).unwrap();
        }
        buf.push_str("];");
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// ParseSimulator static embedding (Tier 3 recovery simulation)
// ══════════════════════════════════════════════════════════════════════════════

/// Emit ParseSimulator data as static arrays for runtime Tier 3 recovery simulation.
///
/// Generates per-category FIRST/FOLLOW/infix token ID arrays and a `LazyLock<ParseSimulator>`
/// for context-aware repair rescoring. Only initialized on first access (error path only).
///
/// Generated code:
/// ```text
/// static SIM_FIRST_SETS: &[(&str, &[u16])] = &[("Int", &[3, 7]), ("Bool", &[5])];
/// static SIM_FOLLOW_SETS: &[(&str, &[u16])] = &[("Int", &[1, 2]), ("Bool", &[1])];
/// static SIM_INFIX_SETS: &[(&str, &[u16])] = &[("Int", &[4]), ("Bool", &[])];
/// static PARSE_SIMULATOR: std::sync::LazyLock<ParseSimulator> = std::sync::LazyLock::new(|| {
///     ParseSimulator::from_flat(SIM_FIRST_SETS, SIM_FOLLOW_SETS, SIM_INFIX_SETS, 5)
/// });
/// ```
fn emit_parse_simulator_static(
    buf: &mut String,
    first_sets: &std::collections::HashMap<String, crate::prediction::FirstSet>,
    follow_sets: &std::collections::HashMap<String, crate::prediction::FirstSet>,
    bp_table: &crate::binding_power::BindingPowerTable,
    category_names: &[String],
    token_id_map: &crate::token_id::TokenIdMap,
) {
    use std::fmt::Write;

    // Helper to emit a set-of-sets array: &[(&str, &[u16])]
    let emit_set_array = |buf: &mut String, name: &str, sets: &std::collections::HashMap<String, crate::prediction::FirstSet>| {
        write!(buf, "static {}: &[(&str, &[u16])] = &[", name).unwrap();
        let mut first = true;
        for cat in category_names {
            if let Some(fs) = sets.get(cat) {
                if !first { buf.push(','); }
                first = false;
                let ids: Vec<u16> = fs.sorted_tokens()
                    .iter()
                    .filter_map(|t| token_id_map.get(*t))
                    .collect();
                write!(buf, "(\"{}\", &[", cat).unwrap();
                for (i, id) in ids.iter().enumerate() {
                    if i > 0 { buf.push(','); }
                    write!(buf, "{}_u16", id).unwrap();
                }
                buf.push_str("])");
            }
        }
        buf.push_str("];");
    };

    emit_set_array(buf, "SIM_FIRST_SETS", first_sets);
    emit_set_array(buf, "SIM_FOLLOW_SETS", follow_sets);

    // Build infix set from binding power table
    write!(buf, "static SIM_INFIX_SETS: &[(&str, &[u16])] = &[").unwrap();
    let mut first = true;
    for cat in category_names {
        let ops = bp_table.operators_for_category(cat);
        if !first { buf.push(','); }
        first = false;
        write!(buf, "(\"{}\", &[", cat).unwrap();
        let mut ids: Vec<u16> = ops
            .iter()
            .filter_map(|op| {
                let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
                token_id_map.get(&variant)
            })
            .collect();
        ids.sort();
        ids.dedup();
        for (i, id) in ids.iter().enumerate() {
            if i > 0 { buf.push(','); }
            write!(buf, "{}_u16", id).unwrap();
        }
        buf.push_str("])");
    }
    buf.push_str("];");

    // Emit LazyLock<ParseSimulator>
    buf.push_str(
        "static PARSE_SIMULATOR: std::sync::LazyLock<mettail_prattail::recovery::ParseSimulator> = \
         std::sync::LazyLock::new(|| { \
             mettail_prattail::recovery::ParseSimulator::from_flat(\
                 SIM_FIRST_SETS, SIM_FOLLOW_SETS, SIM_INFIX_SETS, 5\
             ) \
         });"
    );
}

/// Emit a `token_to_id(t: &Token) -> u16` function mapping each Token variant to its TokenId.
///
/// Used by Tier 3 recovery simulation: converts `&[(Token, Range)]` slices to `&[u16]`
/// for `ParseSimulator::simulate_after_repair()`. Only called on error paths.
///
/// Only emits match arms for token variants that actually exist in the grammar's Token enum
/// (filtered by `valid_variants`), avoiding compile errors for non-existent variants.
fn emit_token_to_id_fn(
    buf: &mut String,
    token_id_map: &crate::token_id::TokenIdMap,
    valid_variants: &std::collections::HashSet<String>,
) {
    use std::fmt::Write;

    buf.push_str("fn token_to_id(t: &Token) -> u16 { match t {");

    for (name, id) in token_id_map.iter() {
        // Only emit match arms for variants that exist in the grammar's Token enum
        if !valid_variants.contains(name) {
            continue;
        }

        // Tokens with payloads need wildcard patterns
        let pattern = match name {
            "Ident" => "Token::Ident(_)".to_string(),
            "Integer" => "Token::Integer(_)".to_string(),
            "Float" => "Token::Float(_)".to_string(),
            "Boolean" => "Token::Boolean(_)".to_string(),
            "StringLit" => "Token::StringLit(_)".to_string(),
            "Eof" => "Token::Eof".to_string(),
            other => format!("Token::{}", other),
        };
        write!(buf, "{} => {}_u16,", pattern, id).unwrap();
    }

    // Catch-all for any unmapped variants → use u16::MAX as sentinel
    buf.push_str("_ => u16::MAX,");
    buf.push_str("}}");
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST recovery codegen (always-on)
// ══════════════════════════════════════════════════════════════════════════════

/// Generate a WFST-based weighted recovery function for a category.
///
/// Emits a function `wfst_recover_Cat` that evaluates all 4 repair strategies
/// (skip-to-sync, delete, insert, substitute) with context-aware cost adjustments
/// from `RecoveryContext` (bracket balance, nesting depth, frame kind).
///
/// Also emits a helper `is_sync_token_Cat` for matching sync tokens.
///
/// Generated signatures:
/// ```text
/// fn wfst_recover_Cat<'a>(
///     tokens: &[(Token<'a>, Range)],
///     pos: &mut usize,
///     depth: usize,
///     binding_power: u8,
///     open_parens: u16,
///     open_braces: u16,
///     open_brackets: u16,
/// ) -> bool  // true if recovery succeeded
/// ```
fn generate_wfst_recovery_fn(
    buf: &mut String,
    category: &str,
    recovery_wfst: &crate::recovery::RecoveryWfst,
    has_cross_casts: bool,
    optimization_gates: &crate::cost_benefit::OptimizationGates,
) {
    use std::fmt::Write;

    // Collect sync token variant names for match patterns
    let sync_patterns: Vec<String> = recovery_wfst
        .sync_tokens()
        .iter()
        .filter_map(|&id| recovery_wfst.token_name(id))
        .map(|name| match name {
            "Ident" => "Token::Ident(_)".to_string(),
            "Integer" => "Token::Integer(_)".to_string(),
            "Float" => "Token::Float(_)".to_string(),
            "Boolean" => "Token::Boolean(_)".to_string(),
            "StringLit" => "Token::StringLit(_)".to_string(),
            "Eof" => "Token::Eof".to_string(),
            other => format!("Token::{}", other),
        })
        .collect();

    if sync_patterns.is_empty() {
        return;
    }

    // Build bracket-specific insert patterns for close delimiters
    let has_rparen = recovery_wfst
        .sync_tokens()
        .iter()
        .any(|&id| recovery_wfst.token_name(id) == Some("RParen"));
    let has_rbrace = recovery_wfst
        .sync_tokens()
        .iter()
        .any(|&id| recovery_wfst.token_name(id) == Some("RBrace"));
    let has_rbracket = recovery_wfst
        .sync_tokens()
        .iter()
        .any(|&id| recovery_wfst.token_name(id) == Some("RBracket"));

    let max_skip: usize = 32; // Same as recovery::costs::MAX_SKIP_LOOKAHEAD

    // Generate the full 4-strategy context-aware recovery function
    let cat_upper = category.to_uppercase();
    write!(
        buf,
        "/// WFST-based 4-strategy context-aware recovery for category `{cat}`.
         ///
         /// Evaluates skip-to-sync, delete, insert, and substitute strategies with
         /// context-aware cost adjustments from nesting depth, binding power,
         /// frame kind, and bracket balance.
         fn wfst_recover_{cat}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            depth: usize, \
            binding_power: u8, \
            open_parens: u16, \
            open_braces: u16, \
            open_brackets: u16, \
         ) -> Option<String> {{ \
            let start = *pos; \
            let remaining = tokens.len() - start; \
            let max_look = if remaining < {max_skip} {{ remaining }} else {{ {max_skip} }}; \
            let mut best_pos: Option<usize> = None; \
            let mut best_cost: f64 = f64::INFINITY; \
            let mut best_desc: String = String::new(); \
            /* Read frame state from thread-local (depth, frame_kind) */ \
            let (frame_depth, frame_kind) = FRAME_STATE_{cat_upper}.with(|c| c.get()); \
            let effective_depth = if frame_depth > 0 {{ frame_depth as usize }} else {{ depth }}; \
            /* Tier 1: depth-based skip multiplier */ \
            let skip_mult: f64 = if effective_depth > 1000 {{ 0.5 }} \
                else if effective_depth < 10 {{ 2.0 }} else {{ 1.0 }}; \
            /* Tier 1: BP-based skip multiplier */ \
            let bp_mult: f64 = if binding_power < 4 {{ 0.75 }} else {{ 1.0 }}; \
            /* Tier 1: frame-kind skip multiplier (InfixRHS = 1) */ \
            let frame_skip_mult: f64 = if frame_kind == 1 {{ 0.75 }} else {{ 1.0 }}; \
            let combined_skip_mult = skip_mult * bp_mult * frame_skip_mult{adaptive_skip_expr}; \
            /* B2: Adaptive insert multiplier from running weight */ \
            let adaptive_insert_mult: f64 = {adaptive_insert_expr}; \
            /* Strategy 1: Skip to nearest sync token (0.5/token * context mult) */ \
            for skip in 0..max_look {{ \
                let idx = start + skip; \
                if matches!(&tokens[idx].0, {sync_pats}) {{ \
                    let cost = (skip as f64) * 0.5 * combined_skip_mult; \
                    if cost < best_cost {{ \
                        best_cost = cost; \
                        best_pos = Some(idx); \
                        best_desc = format!(\"skip {{}} token(s) to '{{:?}}'\", skip, &tokens[idx].0); \
                    }} \
                    break; \
                }} \
            }} \
            /* Strategy 2: Delete one token (cost 1.0 * skip_mult) */ \
            if remaining > 0 {{ \
                let cost = 1.0 * combined_skip_mult; \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start + 1); \
                    best_desc = \"delete unexpected token\".to_string(); \
                }} \
            }} \
            /* Strategy 3: Insert missing closing delimiter (bracket-aware) */ \
            {{ \
                /* frame_kind: 3=Collection (0.5x), 4=Group (0.5x) */ \
                let frame_insert_mult: f64 = if frame_kind == 3 || frame_kind == 4 {{ 0.5 }} else {{ 1.0 }}; \
                let base_insert = 2.0_f64 * frame_insert_mult * adaptive_insert_mult;",
        cat = category,
        cat_upper = cat_upper,
        max_skip = max_skip,
        sync_pats = sync_patterns.join(" | "),
        adaptive_skip_expr = if optimization_gates.adaptive_recovery {
            let config = crate::recovery::RecoveryConfig::default();
            format!(
                " * {{ let rw = RUNNING_WEIGHT_{}.with(|c| c.get()); \
                 if rw < {:?} {{ {:?} }} else {{ 1.0 }} }}",
                cat_upper,
                config.adaptive_weight_threshold,
                config.deterministic_skip_discount,
            )
        } else {
            String::new()
        },
        adaptive_insert_expr = if optimization_gates.adaptive_recovery {
            let config = crate::recovery::RecoveryConfig::default();
            format!(
                "{{ let rw = RUNNING_WEIGHT_{}.with(|c| c.get()); \
                 if rw >= {:?} {{ {:?} }} else {{ 1.0 }} }}",
                cat_upper,
                config.adaptive_weight_threshold,
                config.ambiguous_insert_discount,
            )
        } else {
            "1.0".to_string()
        },
    )
    .unwrap();

    // Emit bracket-specific insert logic
    if has_rparen {
        write!(
            buf,
            "if open_parens > 0 {{ \
                let cost = base_insert * 0.3; /* strongly prefer closing unmatched parens */ \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start); /* phantom insert — don't advance */ \
                    best_desc = \"insert missing ')'\".to_string(); \
                }} \
            }}"
        )
        .unwrap();
    }
    if has_rbrace {
        write!(
            buf,
            "if open_braces > 0 {{ \
                let cost = base_insert * 0.3; \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start); \
                    best_desc = \"insert missing '}}'\".to_string(); \
                }} \
            }}"
        )
        .unwrap();
    }
    if has_rbracket {
        write!(
            buf,
            "if open_brackets > 0 {{ \
                let cost = base_insert * 0.3; \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start); \
                    best_desc = \"insert missing ']'\".to_string(); \
                }} \
            }}"
        )
        .unwrap();
    }

    write!(
        buf,
        "   }} \
            /* Strategy 4: Substitute current token with sync token (cost 1.5 * sub_mult) */ \
            if remaining > 0 {{ \
                /* frame_kind: 5=Mixfix (0.75x) */ \
                let sub_mult: f64 = if frame_kind == 5 {{ 0.75 }} else {{ 1.0 }}; \
                let cost = 1.5 * sub_mult; \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start + 1); \
                    best_desc = \"substitute unexpected token\".to_string(); \
                }} \
            }} \
            /* Tier 3: ParseSimulator rescoring — simulate continuation after best repair */ \
            if let Some(new_pos) = best_pos {{ \
                let sim_ids: Vec<u16> = tokens[new_pos..].iter().map(|(t, _)| token_to_id(t)).collect(); \
                let sim_result = PARSE_SIMULATOR.simulate_after_repair(&sim_ids, 0, \"{cat}\"); \
                let sim_mult = PARSE_SIMULATOR.cost_multiplier(&sim_result); \
                best_cost *= sim_mult; \
            }} \
            /* Multi-step Viterbi: evaluate composite repair sequences */ \
            {{ \
                let all_ids: Vec<u16> = tokens[start..].iter().map(|(t, _)| token_to_id(t)).collect(); \
                let sync_set: std::collections::BTreeSet<u16> = \
                    RECOVERY_SYNC_TOKENS_{cat}.iter().copied().collect(); \
                if let Some(seq) = mettail_prattail::recovery::viterbi_multi_step(\
                    &all_ids, 0, &sync_set, &mettail_prattail::recovery::RecoveryConfig::default()\
                ) {{ \
                    let multi_cost = seq.total_cost.left.value(); \
                    if multi_cost < best_cost {{ \
                        best_cost = multi_cost; \
                        best_pos = Some(start + seq.new_pos); \
                        best_desc = format!(\"{{}} action(s): {{}}\", \
                            seq.actions.len(), \
                            seq.actions.iter().map(|a| format!(\"{{:?}}\", a)).collect::<Vec<_>>().join(\", \") \
                        ); \
                    }} \
                }} \
            }}",
        cat = category,
    )
    .unwrap();

    // Strategy 6: Cross-category recovery (only for grammars with cast rules to this category)
    if has_cross_casts {
        buf.push_str("/* Strategy 6: Cross-category recovery via cast rules */");
        buf.push_str("if remaining > 0 {");
        buf.push_str("let err_tok_id = token_to_id(&tokens[start].0);");
        buf.push_str(&format!(
            "for &(source_cat, source_first_ids) in CROSS_CAT_CASTS_{}.iter() {{",
            category,
        ));
        buf.push_str("if source_first_ids.contains(&err_tok_id) {");
        buf.push_str("let cast_cost = 1.5_f64 * 0.5_f64;");
        buf.push_str("if cast_cost < best_cost {");
        buf.push_str("best_cost = cast_cost;");
        buf.push_str("best_pos = Some(start);");
        buf.push_str(&format!(
            r#"best_desc = format!("try parsing as {{}} (cast to {})", source_cat);"#,
            category,
        ));
        buf.push_str("} break; } } }");
    }

    buf.push_str(
        "/* Apply best strategy */ \
            match best_pos { \
                Some(new_pos) => { *pos = new_pos; Some(best_desc) } \
                None => None \
            } \
         }",
    );
}

/// Generate recovering parser variant that uses WFST recovery instead of sync_to.
///
/// On parse error, calls `wfst_recover_Cat()` with context parameters (depth,
/// binding power, bracket counters) for context-aware recovery with all 4 strategies.
///
/// Bracket counters are maintained inline: incremented on open delimiters,
/// decremented on close delimiters. This provides Tier 2 (bracket balance)
/// context to the recovery function at zero overhead on the happy path.
fn write_trampolined_parser_recovering_wfst(
    buf: &mut String,
    config: &crate::trampoline::TrampolineConfig,
) {
    use std::fmt::Write;

    let cat = &config.category;
    let parse_fn = if config.needs_dispatch {
        format!("parse_{}_own_recovering", cat)
    } else {
        format!("parse_{}_recovering", cat)
    };

    let own_parse_fn = if config.needs_dispatch {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    // Cascade prevention window (from RecoveryConfig default).
    let cascade_window = crate::recovery::RecoveryConfig::default().cascade_window;

    // Emit thread-local bracket state for incremental tracking.
    // State: (last_scanned_pos, paren_count, brace_count, bracket_count).
    // On each error, only scan tokens from last_scanned_pos to current pos,
    // giving O(total_tokens) across all errors instead of O(pos * num_errors).
    write!(
        buf,
        "thread_local! {{ \
            static BRACKET_STATE_{cat}: std::cell::Cell<(usize, u16, u16, u16)> = \
                std::cell::Cell::new((0, 0, 0, 0)); \
            static LAST_ERROR_POS_{cat}: std::cell::Cell<usize> = \
                std::cell::Cell::new(usize::MAX); \
        }} \
        fn {parse_fn}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            min_bp: u8, \
            errors: &mut Vec<ParseError>, \
        ) -> Option<{cat}> {{ \
            if min_bp == 0 {{ \
                BRACKET_STATE_{cat}.with(|c| c.set((0, 0, 0, 0))); \
                LAST_ERROR_POS_{cat}.with(|c| c.set(usize::MAX)); \
            }} \
            match {own_parse_fn}(tokens, pos, min_bp) {{ \
                Ok(v) => Some(v), \
                Err(e) => {{ \
                    /* Cascade prevention: if this error is within {cascade_window} tokens \
                       of the last error, suppress it and just advance by 1 */ \
                    let last_err = LAST_ERROR_POS_{cat}.with(|c| c.get()); \
                    if last_err != usize::MAX && *pos <= last_err + {cascade_window} {{ \
                        if *pos < tokens.len() {{ *pos += 1; }} \
                        return None; \
                    }} \
                    LAST_ERROR_POS_{cat}.with(|c| c.set(*pos)); \
                    /* Incremental bracket balance: scan only new tokens since last error */ \
                    let (op, ob, ok) = BRACKET_STATE_{cat}.with(|c| {{ \
                        let (last, mut op, mut ob, mut ok) = c.get(); \
                        let scan_to = if *pos < tokens.len() {{ *pos }} else {{ tokens.len() }}; \
                        for i in last..scan_to {{ \
                            match &tokens[i].0 {{ \
                                Token::LParen => op = op.saturating_add(1), \
                                Token::RParen => op = op.saturating_sub(1), \
                                Token::LBrace => ob = ob.saturating_add(1), \
                                Token::RBrace => ob = ob.saturating_sub(1), \
                                Token::LBracket => ok = ok.saturating_add(1), \
                                Token::RBracket => ok = ok.saturating_sub(1), \
                                _ => {{}} \
                            }} \
                        }} \
                        c.set((scan_to, op, ob, ok)); \
                        (op, ob, ok) \
                    }}); \
                    let repair_range = e.range(); \
                    match wfst_recover_{cat}(tokens, pos, 0, min_bp, op, ob, ok) {{ \
                        Some(desc) => errors.push(ParseError::RecoveryApplied {{ \
                            original_error: Box::new(e), \
                            repair_description: desc, \
                            range: repair_range, \
                        }}), \
                        None => errors.push(e), \
                    }} \
                    None \
                }} \
            }} \
        }}",
    )
    .unwrap();
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prediction::{FirstItem, FirstSet, RuleInfo};

    /// Helper: create a RuleInfo with sensible defaults.
    fn rule(label: &str, category: &str) -> RuleInfo {
        RuleInfo {
            label: label.to_string(),
            category: category.to_string(),
            first_items: Vec::new(),
            is_infix: false,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        }
    }

    /// Helper: create a CategoryInfo.
    fn category(name: &str, is_primary: bool) -> CategoryInfo {
        CategoryInfo {
            name: name.to_string(),
            native_type: None,
            is_primary,
        }
    }

    /// Helper: create a FirstSet with given tokens.
    fn first_set(tokens: &[&str]) -> FirstSet {
        FirstSet {
            tokens: tokens.iter().map(|s| s.to_string()).collect(),
            nullable: false,
        }
    }

    // ── A8: ProductWeight<BooleanWeight, CountingWeight> nearly-dead detection ──

    #[test]
    fn test_a8_nearly_dead_ratio_threshold() {
        // A8: NEARLY_DEAD_RATIO should be 0.01 (1%)
        assert_eq!(NEARLY_DEAD_RATIO, 0.01);
    }

    #[test]
    fn test_a8_single_category_returns_empty() {
        // A8: With only one category, no inter-category analysis is possible.
        let cats = vec![category("Expr", true)];
        let rules = vec![rule("Add", "Expr")];
        let first_sets: HashMap<String, FirstSet> = [("Expr".to_string(), first_set(&["Plus"]))].into();
        let warnings = detect_nearly_dead_paths(&rules, &cats, &first_sets, &[]);
        assert!(warnings.is_empty(), "single category should produce no warnings");
    }

    #[test]
    fn test_a8_well_connected_categories_no_warnings() {
        // A8: When all categories are well-connected via cast rules, no nearly-dead warnings.
        let cats = vec![category("Proc", true), category("Int", false)];
        let mut r1 = rule("IntToProc", "Proc");
        r1.is_cast = true;
        r1.first_items = vec![FirstItem::NonTerminal("Int".to_string())];
        let mut r2 = rule("ProcToInt", "Int");
        r2.is_cast = true;
        r2.first_items = vec![FirstItem::NonTerminal("Proc".to_string())];
        let r3 = rule("Add", "Int");
        let r4 = rule("Par", "Proc");
        let rules = vec![r1, r2, r3, r4];
        let first_sets: HashMap<String, FirstSet> = [
            ("Proc".to_string(), first_set(&["Par"])),
            ("Int".to_string(), first_set(&["Plus"])),
        ].into();

        let warnings = detect_nearly_dead_paths(&rules, &cats, &first_sets, &[]);
        assert!(warnings.is_empty(), "well-connected categories should not be nearly-dead: {:?}", warnings);
    }

    #[test]
    fn test_a8_isolated_category_not_flagged_as_nearly_dead() {
        // A8: Completely unreachable categories should NOT be flagged by detect_nearly_dead_paths
        // (they are handled by the A4 detect_inter_category_dead_paths function).
        let cats = vec![
            category("Proc", true),
            category("Int", false),
            category("Orphan", false),
        ];
        let mut r1 = rule("IntToProc", "Proc");
        r1.is_cast = true;
        r1.first_items = vec![FirstItem::NonTerminal("Int".to_string())];
        let r2 = rule("Add", "Int");
        let r3 = rule("OrphanRule", "Orphan");
        let rules = vec![r1, r2, r3];
        let first_sets: HashMap<String, FirstSet> = [
            ("Proc".to_string(), first_set(&["Par"])),
            ("Int".to_string(), first_set(&["Plus"])),
            ("Orphan".to_string(), first_set(&["Bang"])),
        ].into();

        let warnings = detect_nearly_dead_paths(&rules, &cats, &first_sets, &[]);
        // Orphan is completely unreachable (forward = zero), so it should NOT appear
        // in nearly-dead warnings (that's A4's job).
        let orphan_warnings: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::NearlyDeadPath { category, .. } if category == "Orphan")
        }).collect();
        assert!(orphan_warnings.is_empty(), "completely unreachable category should not be flagged as nearly-dead");
    }

    #[test]
    fn test_a8_product_weight_semiring_properties() {
        // A8: Verify ProductWeight<BooleanWeight, CountingWeight> semiring axioms.
        use crate::automata::semiring::{BooleanWeight, CountingWeight, ProductWeight, Semiring};

        type BoolCount = ProductWeight<BooleanWeight, CountingWeight>;

        // zero
        let z = BoolCount::zero();
        assert!(z.left.is_zero());
        assert_eq!(z.right.count(), 0);

        // one
        let o = BoolCount::one();
        assert!(o.left.is_reachable());
        assert_eq!(o.right.count(), 1);

        // plus (Boolean OR, Counting add)
        let a = BoolCount::new(BooleanWeight::new(true), CountingWeight::new(3));
        let b = BoolCount::new(BooleanWeight::new(true), CountingWeight::new(5));
        let ab = a.plus(&b);
        assert!(ab.left.is_reachable());
        assert_eq!(ab.right.count(), 8);

        // times (Boolean AND, Counting multiply)
        let c = a.times(&b);
        assert!(c.left.is_reachable());
        assert_eq!(c.right.count(), 15);

        // zero annihilates
        let az = a.times(&z);
        assert!(az.left.is_zero());
        assert_eq!(az.right.count(), 0);
    }

    #[test]
    fn test_a8_forward_backward_with_product_weight() {
        // A8: Verify forward-backward with ProductWeight produces correct counts.
        use crate::automata::semiring::{BooleanWeight, CountingWeight, ProductWeight, Semiring};
        use crate::forward_backward::{forward_scores, backward_scores};

        type BoolCount = ProductWeight<BooleanWeight, CountingWeight>;

        // Diamond: 0 → 1, 0 → 2, 1 → 3, 2 → 3
        let w = BoolCount::new(BooleanWeight::one(), CountingWeight::one());
        let edges: Vec<Vec<(usize, BoolCount)>> = vec![
            vec![(1, w), (2, w)],   // node 0 → 1, 2
            vec![(3, w)],           // node 1 → 3
            vec![(3, w)],           // node 2 → 3
            vec![],                 // node 3: sink
        ];

        let fwd = forward_scores::<BoolCount>(&edges, 4);
        // fwd[0] = one() = (true, 1)
        assert!(fwd[0].left.is_reachable());
        assert_eq!(fwd[0].right.count(), 1);
        // fwd[1] = (true, 1) — one path from 0
        assert!(fwd[1].left.is_reachable());
        assert_eq!(fwd[1].right.count(), 1);
        // fwd[2] = (true, 1) — one path from 0
        assert!(fwd[2].left.is_reachable());
        assert_eq!(fwd[2].right.count(), 1);
        // fwd[3] = (true, 2) — two paths: 0→1→3, 0→2→3
        assert!(fwd[3].left.is_reachable());
        assert_eq!(fwd[3].right.count(), 2);

        let bwd = backward_scores::<BoolCount>(&edges, 4, 3);
        // bwd[3] = one() = (true, 1)
        assert!(bwd[3].left.is_reachable());
        assert_eq!(bwd[3].right.count(), 1);
        // bwd[0] should also be (true, 2)
        assert!(bwd[0].left.is_reachable());
        assert_eq!(bwd[0].right.count(), 2);
    }

    #[test]
    fn test_a8_nearly_dead_warning_display() {
        // A8: Display format for NearlyDeadPath warning.
        let w = DeadRuleWarning::NearlyDeadPath {
            rule_label: "ObscureCast".to_string(),
            category: "Rare".to_string(),
            derivation_count: 1,
            total_count: 500,
        };
        let msg = format!("{}", w);
        assert!(msg.contains("nearly-dead"), "should mention nearly-dead: {}", msg);
        assert!(msg.contains("1/500"), "should mention 1/500: {}", msg);
        assert!(msg.contains("ObscureCast"), "should mention rule label: {}", msg);
        assert!(msg.contains("Rare"), "should mention category: {}", msg);
    }

    // ── A4: Inter-category dead-path detection ──

    #[test]
    fn test_a4_cyclic_graph_backward_reachable() {
        // Calculator pattern: Int(root), Float, Bool, Str.
        // Cross-cat edges: Int↔Bool, Float↔Bool, Str↔Bool (via comparison ops).
        // Str→Bool→Int is a valid path, so Str must NOT be flagged.
        let cats = vec![
            category("Int", true),
            category("Float", false),
            category("Bool", false),
            category("Str", false),
        ];
        // Cross-category infix rules creating bidirectional connections
        let mut eq_int = rule("EqInt", "Bool");
        eq_int.is_cross_category = true;
        eq_int.is_infix = true;
        eq_int.first_items = vec![FirstItem::NonTerminal("Int".to_string())];

        let mut eq_float = rule("EqFloat", "Bool");
        eq_float.is_cross_category = true;
        eq_float.is_infix = true;
        eq_float.first_items = vec![FirstItem::NonTerminal("Float".to_string())];

        let mut eq_str = rule("EqStr", "Bool");
        eq_str.is_cross_category = true;
        eq_str.is_infix = true;
        eq_str.first_items = vec![FirstItem::NonTerminal("Str".to_string())];

        let rules = vec![
            rule("NumLit", "Int"),
            rule("FltLit", "Float"),
            rule("True", "Bool"),
            rule("Concat", "Str"),
            eq_int,
            eq_float,
            eq_str,
        ];
        let first_sets: HashMap<String, FirstSet> = [
            ("Int".to_string(), first_set(&["Integer"])),
            ("Float".to_string(), first_set(&["Float"])),
            ("Bool".to_string(), first_set(&["true", "false"])),
            ("Str".to_string(), first_set(&["String"])),
        ].into();

        let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &[]);
        let str_warnings: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::InterCategoryDeadPath { category, .. } if category == "Str")
        }).collect();
        assert!(str_warnings.is_empty(),
            "Str should not be flagged as dead (Str→Bool→Int is valid): {:?}", str_warnings);

        // No categories should be flagged since all are connected through Bool
        assert!(warnings.is_empty(),
            "no categories should be flagged in well-connected cyclic graph: {:?}", warnings);
    }

    #[test]
    fn test_a4_prefix_rule_with_cross_category_nonterminal() {
        // NQuote pattern: Name has rule `"@" "(" Proc ")"` — a regular prefix rule
        // that references Proc as a NonTerminal in its syntax (not as first item).
        // Also: Proc has `"*" Name` (PDrop). So Name↔Proc are connected.
        let cats = vec![
            category("Proc", true),
            category("Name", false),
        ];
        let rules = vec![
            rule("PPar", "Proc"),
            rule("PDrop", "Proc"),
            rule("NQuote", "Name"),
        ];
        let first_sets: HashMap<String, FirstSet> = [
            ("Proc".to_string(), first_set(&["|", "*"])),
            ("Name".to_string(), first_set(&["@"])),
        ].into();

        // NQuote syntax: "@" "(" Proc ")" — references Proc as NonTerminal
        // PDrop syntax: "*" Name — references Name as NonTerminal
        let all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![
            ("NQuote".to_string(), "Name".to_string(), vec![
                SyntaxItemSpec::Terminal("@".to_string()),
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Proc".to_string(), param_name: "p".to_string() },
                SyntaxItemSpec::Terminal(")".to_string()),
            ]),
            ("PDrop".to_string(), "Proc".to_string(), vec![
                SyntaxItemSpec::Terminal("*".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Name".to_string(), param_name: "n".to_string() },
            ]),
        ];

        let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &all_syntax);
        let name_warnings: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::InterCategoryDeadPath { category, .. } if category == "Name")
        }).collect();
        assert!(name_warnings.is_empty(),
            "Name should not be flagged as dead (connected to Proc via syntax): {:?}", name_warnings);
        assert!(warnings.is_empty(),
            "no categories should be flagged: {:?}", warnings);
    }

    #[test]
    fn test_a4_truly_isolated_category_flagged() {
        // Orphan category with no cross-category references at all.
        let cats = vec![
            category("Proc", true),
            category("Int", false),
            category("Orphan", false),
        ];
        let mut cast = rule("IntToProc", "Proc");
        cast.is_cast = true;
        cast.first_items = vec![FirstItem::NonTerminal("Int".to_string())];
        let rules = vec![
            rule("PPar", "Proc"),
            rule("Add", "Int"),
            cast,
            rule("OrphanRule", "Orphan"),
        ];
        let first_sets: HashMap<String, FirstSet> = [
            ("Proc".to_string(), first_set(&["|"])),
            ("Int".to_string(), first_set(&["Integer"])),
            ("Orphan".to_string(), first_set(&["!"])),
        ].into();

        let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &[]);
        let orphan_warnings: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::InterCategoryDeadPath { category, .. } if category == "Orphan")
        }).collect();
        assert!(!orphan_warnings.is_empty(),
            "Orphan should be flagged as dead (no connections to root)");
        // Non-orphan categories should NOT be flagged
        let non_orphan: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::InterCategoryDeadPath { category, .. } if category != "Orphan")
        }).collect();
        assert!(non_orphan.is_empty(),
            "only Orphan should be flagged: {:?}", non_orphan);
    }

    #[test]
    fn test_a4_single_category_no_warnings() {
        // With only one category, no inter-category analysis possible.
        let cats = vec![category("Expr", true)];
        let rules = vec![rule("Add", "Expr")];
        let first_sets: HashMap<String, FirstSet> = [("Expr".to_string(), first_set(&["Plus"]))].into();
        let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &[]);
        assert!(warnings.is_empty(), "single category should produce no warnings");
    }

    #[test]
    fn test_a4_syntax_binder_creates_edge() {
        // A Binder referencing a different category creates an inter-category edge.
        let cats = vec![
            category("Proc", true),
            category("Name", false),
        ];
        let rules = vec![
            rule("PPar", "Proc"),
            rule("NVar", "Name"),
        ];
        let first_sets: HashMap<String, FirstSet> = [
            ("Proc".to_string(), first_set(&["|"])),
            ("Name".to_string(), first_set(&["Ident"])),
        ].into();

        // Proc rule with a Binder from Name category
        let all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![
            ("PNew".to_string(), "Proc".to_string(), vec![
                SyntaxItemSpec::Terminal("new".to_string()),
                SyntaxItemSpec::Binder {
                    param_name: "n".to_string(),
                    category: "Name".to_string(),
                    is_multi: false,
                },
                SyntaxItemSpec::Terminal("in".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Proc".to_string(), param_name: "p".to_string() },
            ]),
        ];

        let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &all_syntax);
        assert!(warnings.is_empty(),
            "Name should be reachable via Binder from Proc: {:?}", warnings);
    }

    #[test]
    fn test_a4_syntax_collection_creates_edge() {
        // A Collection referencing a different category creates an inter-category edge.
        let cats = vec![
            category("Proc", true),
            category("Arg", false),
        ];
        let rules = vec![
            rule("PPar", "Proc"),
            rule("ArgLit", "Arg"),
        ];
        let first_sets: HashMap<String, FirstSet> = [
            ("Proc".to_string(), first_set(&["|"])),
            ("Arg".to_string(), first_set(&["Integer"])),
        ].into();

        let all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![
            ("PCall".to_string(), "Proc".to_string(), vec![
                SyntaxItemSpec::Terminal("call".to_string()),
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::Collection {
                    param_name: "args".to_string(),
                    element_category: "Arg".to_string(),
                    separator: ",".to_string(),
                    kind: crate::recursive::CollectionKind::Vec,
                },
                SyntaxItemSpec::Terminal(")".to_string()),
            ]),
        ];

        let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &all_syntax);
        assert!(warnings.is_empty(),
            "Arg should be reachable via Collection from Proc: {:?}", warnings);
    }
}
