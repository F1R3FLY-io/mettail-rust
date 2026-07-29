use super::*;

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
        },
        crate::SyntaxItemSpec::Binder { category: ref b_cat, .. } => {
            if b_cat != rule_cat {
                if let Some(&src_idx) = cat_to_idx.get(b_cat) {
                    pairs.push((src_idx, target_idx));
                }
            }
        },
        crate::SyntaxItemSpec::Collection { element_category: ref e_cat, .. } => {
            if e_cat != rule_cat {
                if let Some(&src_idx) = cat_to_idx.get(e_cat) {
                    pairs.push((src_idx, target_idx));
                }
            }
        },
        crate::SyntaxItemSpec::Sep { body, .. } => {
            collect_syntax_refs(body, rule_cat, cat_to_idx, target_idx, pairs);
        },
        crate::SyntaxItemSpec::Map { body_items } => {
            for sub in body_items {
                collect_syntax_refs(sub, rule_cat, cat_to_idx, target_idx, pairs);
            }
        },
        crate::SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
            for ref_cat in [left_category.as_str(), right_category.as_str()] {
                if ref_cat != rule_cat {
                    if let Some(&src_idx) = cat_to_idx.get(ref_cat) {
                        pairs.push((src_idx, target_idx));
                    }
                }
            }
            collect_syntax_refs(body, rule_cat, cat_to_idx, target_idx, pairs);
        },
        crate::SyntaxItemSpec::Optional { inner } => {
            for sub in inner {
                collect_syntax_refs(sub, rule_cat, cat_to_idx, target_idx, pairs);
            }
        },
        // Terminal, IdentCapture, BinderCollection — no cross-category refs
        _ => {},
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

    let root_idx = categories.iter().position(|c| c.is_primary).unwrap_or(0);

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
    LiteralNoNativeType { rule_label: String, category: String },
    /// Infix/var rule whose entire category is unreachable (no prefix rule
    /// can start a parse in that category).
    UnreachableCategory { rule_label: String, category: String },
    /// Prefix/cast/cross-category rule that no FIRST-set token dispatches to
    /// via the prediction WFST.
    WfstUnreachable { rule_label: String, category: String },
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
#[cfg(test)]
pub(crate) fn detect_dead_rules(
    rule_infos: &[RuleInfo],
    categories: &[CategoryInfo],
    first_sets: &HashMap<String, FirstSet>,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    semantic_dependency_groups: &[HashSet<String>],
    nfa_spillover_categories: &HashSet<String>,
    rd_rules: &[crate::grammar::ir::RDRuleInfo],
) -> Vec<DeadRuleWarning> {
    detect_dead_rules_with_ignored(
        rule_infos,
        categories,
        first_sets,
        prediction_wfsts,
        semantic_dependency_groups,
        nfa_spillover_categories,
        rd_rules,
        &HashSet::new(),
    )
}

pub(crate) fn detect_dead_rules_with_ignored(
    rule_infos: &[RuleInfo],
    categories: &[CategoryInfo],
    first_sets: &HashMap<String, FirstSet>,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    semantic_dependency_groups: &[HashSet<String>],
    nfa_spillover_categories: &HashSet<String>,
    rd_rules: &[crate::grammar::ir::RDRuleInfo],
    ignored_rule_labels: &HashSet<String>,
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
                        if reachable.contains(&src) && reachable.insert(rule.category.clone()) {
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
            let groups = crate::rd_analysis::group_rd_by_dispatch_token_pub(rd_rules, cat);
            for (_token, rules) in &groups {
                if rules.len() < 2 {
                    continue;
                }
                // If any rule in the group is WFST-reachable, all are covered.
                let any_reachable = prediction_wfsts.get(cat.as_str()).map_or(false, |wfst| {
                    first_sets.get(cat.as_str()).map_or(false, |fs| {
                        fs.tokens.iter().any(|tok| {
                            let preds = wfst.predict(tok);
                            rules
                                .iter()
                                .any(|r| preds.iter().any(|a| a.action.rule_label() == r.label))
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

    // The prediction WFST models trie-backed prefix dispatch. It deliberately
    // omits rules handled by separate runtime mechanisms, so absence from the
    // WFST alone is not evidence that these labels are dead.
    let non_wfst_dispatch_rules: HashSet<&str> = rd_rules
        .iter()
        .filter(|rule| rule.is_collection || rule.prefix_bp.is_some())
        .map(|rule| rule.label.as_str())
        .collect();

    for rule_info in rule_infos {
        if ignored_rule_labels.contains(&rule_info.label) {
            continue;
        }

        // Tier 1: literal rules — dead if category has no native_type.
        // Cast rules (e.g., CastInt, CastBool, CastStr) are cross-category
        // literal injections that ARE reachable even without a native_type
        // in the target category. Exclude them to prevent false positives.
        if rule_info.is_literal && !rule_info.is_cast {
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
        if non_wfst_dispatch_rules.contains(rule_info.label.as_str()) {
            continue;
        }

        let wfst = match prediction_wfsts.get(&rule_info.category) {
            Some(w) => w,
            None => continue,
        };

        let reachable = first_sets.get(&rule_info.category).map_or(false, |fs| {
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

        let semantic_live = compute_semantic_live_labels(&parsing_live, semantic_dependency_groups);

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
                // Unreachable: this match is inside `if !fwd || !bwd`, so at
                // least one of fwd/bwd is false — both-true cannot enter here.
                (true, true) => {
                    unreachable!("inter-category dead-path direction: (fwd, bwd) = (true, true) is excluded by the enclosing `if !fwd || !bwd` guard")
                },
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
pub(crate) const NEARLY_DEAD_RATIO: f64 = 0.01;

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
    use crate::forward_backward::{backward_scores, forward_scores};

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
    let max_count = forward
        .iter()
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
                },
                crate::decision_tree::DispatchStrategy::AmbiguousFanout { rule_labels, .. } => {
                    rule_labels.clone()
                },
                crate::decision_tree::DispatchStrategy::DisjointSuffix { suffix_map, .. } => {
                    suffix_map.values().cloned().collect()
                },
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

/// A4: Collect the rule labels this analysis is willing to call UNREACHABLE.
///
/// Runs `detect_dead_rules()` and returns the subset of its warnings that are a
/// reachability *proof* rather than a reachability *heuristic*.
///
/// **Conservative filtering**: the dead-rule analysis (`detect_dead_rules`)
/// was designed for diagnostics (lint warnings), not for anything that acts.
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
///
/// # ★★ #112/D4 — Tier 3 was in the set, contradicting this comment and `lib.rs`
///
/// Until this repair the `match` below carried a third arm,
/// `DeadRuleWarning::WfstUnreachable { .. }`, admitted behind a "trie confirmation"
/// second pass. The exclusion above and
/// [`crate::PipelineAnalysis::dead_rule_labels`]'s own doc (*"Tier 3/4 are excluded
/// due to false-positive risk"*) both said it was not there. It was, and the
/// published Rholang list therefore named **`Proc::POutput`, `Proc::PNew`,
/// `Name::NQuote`** and 140 further live rules as dead.
///
/// ## Why the mitigation could not work — the two models share the blind spot
///
/// The admission was gated on [`filter_dead_rule_warnings_with_decision_trees`]:
/// a Tier-3 warning survived only if `CategoryDecisionTree::reachable_rules()`
/// *also* reported the rule unreachable. But that trie is indexed by **dispatch
/// token** — the same prefix-dispatch model the prediction WFST is. Tier 3's
/// flagging condition is *"no token in the category's FIRST set predicts this
/// label via the prediction WFST"*, which is structurally blind to any rule that
/// is not reached by a leading terminal:
///
/// ```text
///     POutput . n:Name, p:Proc |- n "!" "(" p ")" : Proc ;
///               ▲
///               └─ OPERAND-led. Reached through the Pratt loop's led/infix
///                  dispatch, never through prefix dispatch — so neither the
///                  WFST nor the trie has an entry for it, and both "agree".
/// ```
///
/// ⇒ Cross-validating two models that share a blind spot cannot catch the error
/// class the cross-validation was added for; it only makes the false positives
/// look corroborated. The `decision_trees` parameter is gone with the arm, and
/// with it the second collection pass in `pipeline::codegen` that existed solely
/// to feed it.
///
/// ## What is NOT changed, and why
///
/// [`filter_dead_rule_warnings_with_decision_trees`] itself stays: its other
/// caller (`pipeline::codegen`'s `cached_dead_rule_warnings`) feeds the **W01
/// lint**, where narrowing a set of *diagnostics* with a second heuristic is a
/// legitimate precision/recall trade — nothing acts on it, a human reads it.
/// Likewise [`detect_dead_prefixes`] still consults Tier-3 warnings: it demotes
/// recovery sync tokens by WEIGHT, which is a heuristic ranking rather than a
/// deadness verdict, and it receives the already-trie-filtered warning list. The
/// defect repaired here is a heuristic *published as a proof*, not the heuristic.
pub(crate) fn collect_dead_rule_labels_with_ignored(
    rule_infos: &[RuleInfo],
    categories: &[CategoryInfo],
    first_sets: &HashMap<String, FirstSet>,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    semantic_dependency_groups: &[HashSet<String>],
    rd_rules: &[crate::grammar::ir::RDRuleInfo],
    ignored_rule_labels: &HashSet<String>,
) -> HashSet<String> {
    let mut dead_labels = HashSet::new();

    let warnings = detect_dead_rules_with_ignored(
        rule_infos,
        categories,
        first_sets,
        prediction_wfsts,
        semantic_dependency_groups,
        &HashSet::new(),
        rd_rules,
        ignored_rule_labels,
    );

    for w in warnings {
        match &w {
            DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
            | DeadRuleWarning::UnreachableCategory { rule_label, .. } => {
                dead_labels.insert(rule_label.clone());
            },
            _ => {},
        }
    }

    // WfstUnreachable (Tier 3) excluded: see the doc comment above — it measures
    // "has no leading-terminal prefix dispatch", which an operand-led rule fails
    // while being perfectly reachable.
    // InterCategoryDeadPath excluded: backward_scores assumes topological
    // ordering but the inter-category graph has cycles, producing false positives.
    // NearlyDeadPath excluded: informational only, rules are technically reachable.

    dead_labels
}

pub(crate) fn filter_dead_rule_warnings_with_decision_trees(
    warnings: Vec<DeadRuleWarning>,
    decision_trees: &HashMap<String, crate::decision_tree::CategoryDecisionTree>,
) -> Vec<DeadRuleWarning> {
    let trie_reachable: HashMap<String, HashSet<String>> = decision_trees
        .iter()
        .map(|(cat, tree)| (cat.clone(), tree.reachable_rules()))
        .collect();

    warnings
        .into_iter()
        .filter(|warning| match warning {
            DeadRuleWarning::WfstUnreachable { rule_label, category } => trie_reachable
                .get(category)
                .is_some_and(|reachable| !reachable.contains(rule_label)),
            _ => true,
        })
        .collect()
}
