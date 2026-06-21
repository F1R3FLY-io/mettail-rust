use super::*;

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
                DiagnosticId::D01,
                "precision-ambiguity",
                crate::lint::LintSeverity::Note,
                &tree.category,
                grammar_name,
                format!("ambiguity at [{}] between {}", path_str, labels.join(" and "),),
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
            let is_leaf = !entries
                .iter()
                .any(|(other, _)| other.len() > path_bytes.len() && other.starts_with(path_bytes));

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
                let labels: Vec<&str> = candidates.iter().map(|c| c.rule_label.as_str()).collect();

                diagnostics.push(dt_diagnostic(
                    DiagnosticId::D02,
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
                },
                DecisionAction::Ambiguous { candidates } => {
                    for c in candidates {
                        in_trie.insert(c.rule_label.clone());
                    }
                },
                _ => {},
            }
        }
    }

    let unreachable: Vec<String> = all_rule_labels.difference(&in_trie).cloned().collect();

    unreachable
        .into_iter()
        .map(|label| {
            dt_diagnostic(
                DiagnosticId::D03,
                "trie-unreachable-rule",
                crate::lint::LintSeverity::Warning,
                &tree.category,
                grammar_name,
                format!(
                    "rule {} is unreachable in trie dispatch — shadowed by higher-priority paths",
                    label,
                ),
                Some("check for duplicate prefix patterns or conflicting priorities".to_string()),
            )
        })
        .collect()
}

/// Layer 3: Minimum lookahead depth report.
pub fn min_lookahead_report(
    tree: &CategoryDecisionTree,
    grammar_name: &str,
) -> crate::lint::LintDiagnostic {
    let depth = tree.stats.min_lookahead;
    dt_diagnostic(
        DiagnosticId::D04,
        "min-lookahead-depth",
        crate::lint::LintSeverity::Note,
        &tree.category,
        grammar_name,
        if depth <= 1 {
            format!("category {} is fully deterministic at depth 1 (LL(1))", tree.category,)
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
pub fn complexity_metrics(
    tree: &CategoryDecisionTree,
    grammar_name: &str,
) -> crate::lint::LintDiagnostic {
    dt_diagnostic(
        DiagnosticId::D05,
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
        let all_excluded = predictions
            .iter()
            .all(|wa| wfst_action_is_trie_excluded(&wa.action));
        if all_excluded {
            continue;
        }

        // The WFST stores token variant names directly (e.g., "Float", "Integer").
        // Skip literal/variable token variants — rules starting with these
        // are handled by dedicated parser paths, not trie dispatch.
        if matches!(&*token_name, "Integer" | "Float" | "Boolean" | "StringLit" | "Ident") {
            continue;
        }

        if wfst_predictions_are_category_literal_dispatch(tree, token_name, &predictions) {
            continue;
        }

        if let Some(byte) = wfst_token_byte(token_ids, token_name) {
            let trie_reachable = first_segment_has_terminal_prefix(tree, byte);
            if !trie_reachable {
                diagnostics.push(dt_diagnostic(
                    DiagnosticId::D06,
                    "wfst-trie-inconsistency",
                    crate::lint::LintSeverity::Warning,
                    &tree.category,
                    grammar_name,
                    format!(
                        "WFST predicts dispatch for token {} but trie has no path for it",
                        token_name,
                    ),
                    Some("WFST weights may be stale or the rule was removed".to_string()),
                ));
            }
        }
    }

    diagnostics
}

fn wfst_action_is_trie_excluded(action: &crate::prediction::DispatchAction) -> bool {
    matches!(
        action,
        crate::prediction::DispatchAction::Variable { .. }
            | crate::prediction::DispatchAction::Cast { .. }
            | crate::prediction::DispatchAction::Grouping { .. }
            | crate::prediction::DispatchAction::CrossCategory { .. }
    )
}

fn wfst_predictions_are_category_literal_dispatch(
    tree: &CategoryDecisionTree,
    token_name: &str,
    predictions: &[&crate::wfst::WeightedAction],
) -> bool {
    if token_name != tree.category {
        return false;
    }

    let expected_rule_label = format!("{}Lit", tree.category);
    let expected_parse_fn = format!("parse_{}_literal", tree.category.to_lowercase());

    predictions.iter().all(|wa| {
        matches!(
            &wa.action,
            crate::prediction::DispatchAction::Direct { rule_label, parse_fn }
                if rule_label == &expected_rule_label && parse_fn == &expected_parse_fn
        )
    })
}

pub(crate) fn wfst_token_byte(token_ids: &TokenIdMap, token_name: &str) -> Option<u8> {
    let tok_id = token_ids.get(token_name).or_else(|| {
        let variant = terminal_to_variant_name(token_name);
        token_ids.get(&variant)
    })?;

    (tok_id <= MAX_TERMINAL_ID as u16).then_some(tok_id as u8)
}

fn first_segment_has_terminal_prefix(tree: &CategoryDecisionTree, byte: u8) -> bool {
    tree.segments
        .first()
        .map_or(false, |segment| segment.iter().any(|(path, _)| path.first() == Some(&byte)))
}

/// Layer 8: Optimization suggestions.
pub fn optimization_suggestions(
    tree: &CategoryDecisionTree,
    grammar_name: &str,
) -> Vec<crate::lint::LintDiagnostic> {
    let mut suggestions = Vec::new();

    for segment in &tree.segments {
        for (_path, action) in segment.iter() {
            if let DecisionAction::Ambiguous { candidates } = action {
                if candidates.len() == 2 {
                    suggestions.push(dt_diagnostic(
                        DiagnosticId::D08,
                        "optimization-suggestion",
                        crate::lint::LintSeverity::Note,
                        &tree.category,
                        grammar_name,
                        format!(
                            "rules {} and {} have ambiguous prefix — \
                             adding a distinguishing terminal would eliminate backtracking",
                            candidates[0].rule_label, candidates[1].rule_label,
                        ),
                        Some(
                            "consider inserting a keyword before the divergence point".to_string(),
                        ),
                    ));
                } else if candidates.len() > 2 {
                    let labels: Vec<&str> =
                        candidates.iter().map(|c| c.rule_label.as_str()).collect();
                    suggestions.push(dt_diagnostic(
                        DiagnosticId::D08,
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
pub fn conflict_resolution_guidance(
    tree: &CategoryDecisionTree,
    grammar_name: &str,
) -> Vec<crate::lint::LintDiagnostic> {
    let mut guidance = Vec::new();

    for segment in &tree.segments {
        for (_path, action) in segment.iter() {
            if let DecisionAction::Ambiguous { candidates } = action {
                let labels: Vec<&str> = candidates.iter().map(|c| c.rule_label.as_str()).collect();
                guidance.push(dt_diagnostic(
                    DiagnosticId::D09,
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
                DecisionAction::Ambiguous { candidates } => Some(
                    candidates
                        .iter()
                        .map(|c| c.rule_label.as_str())
                        .collect::<Vec<_>>()
                        .join("|"),
                ),
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
    let covered = all_paths
        .iter()
        .filter(|p| covered_paths.contains(&p.path_bytes))
        .count();
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
            DiagnosticId::D07,
            "path-coverage-report",
            crate::lint::LintSeverity::Note,
            &tree.category,
            grammar_name,
            format!(
                "coverage: {}/{} trie paths tested ({:.0}%), {} untested",
                covered,
                total,
                if total > 0 {
                    (covered as f64 / total as f64) * 100.0
                } else {
                    100.0
                },
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
    /// ident/binder captures use synthetic token "x".
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
                b if b <= MAX_TERMINAL_ID => match token_ids.name(b as u16) {
                    Some(name) => token_sequence.push(name.to_string()),
                    None => {
                        valid = false;
                        break;
                    },
                },
                IDENT_CAPTURE => token_sequence.push("x".to_string()),
                BINDER_CAPTURE => token_sequence.push("x".to_string()),
                nt_byte if nt_byte >= NT_BASE => {
                    // NT byte: resolve via sorted category index
                    let cat_idx = (nt_byte - NT_BASE) as usize;
                    let shortest = shortest_leaf_path(cat_idx, all_trees, token_ids);
                    token_sequence.extend(shortest);
                },
                _ => {
                    valid = false;
                    break;
                },
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
                b if b <= MAX_TERMINAL_ID => match token_ids.name(b as u16) {
                    Some(name) => tokens.push(name.to_string()),
                    None => {
                        ok = false;
                        break;
                    },
                },
                IDENT_CAPTURE | BINDER_CAPTURE => tokens.push("x".to_string()),
                _ => {
                    ok = false;
                    break;
                }, // Skip NT-recursive for simplicity
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

/// Compute trie-informed weight adjustments for WFST prediction actions.
///
/// For each category and dispatch token, compute a weight adjustment factor
/// based on the dispatch strategy:
/// - `DisjointSuffix` → weight -= 0.25 (resolved without backtracking)
/// - `AmbiguousFanout` with long shared prefix → weight += 0.1 × shared_prefix_len
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
                },
                DispatchStrategy::AmbiguousFanout { shared_prefix_len, .. } => {
                    *shared_prefix_len as f64 * 0.1
                },
                DispatchStrategy::NotPresent => 0.0,
            };
            if adjustment.abs() > f64::EPSILON {
                adjustments.insert((cat_name.clone(), token_variant.clone()), adjustment);
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
        },
        _ => Vec::new(),
    }
}
