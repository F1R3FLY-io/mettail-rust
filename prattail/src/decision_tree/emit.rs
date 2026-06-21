use super::*;

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
                },
                DecisionAction::Ambiguous { candidates } => {
                    stats.ambiguous_nodes += 1;
                    for c in candidates {
                        all_rule_labels.insert(c.rule_label.clone());
                    }
                },
                DecisionAction::NonterminalBoundary { .. } => {
                    stats.nonterminal_boundaries += 1;
                },
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
    stats.min_lookahead = if stats.ambiguous_nodes == 0 {
        1
    } else {
        stats.max_depth
    };

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
/// Actual dispatch codegen is the WPDA walker emission in
/// `macros/src/gen/runtime/wpda_codegen/{prefix,kind_dispatch,forks}.rs`
/// (trampoline.rs DELETED Stage 10.6); `dispatch_strategy()` itself feeds the
/// dead-rule lint and the NFA-spillover refinement (pipeline.rs "1.7a").
pub fn emit_match_arms(tree: &CategoryDecisionTree, _token_ids: &TokenIdMap, buf: &mut String) {
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
        },
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
        },
        DecisionAction::NonterminalBoundary { .. } => {
            write!(buf, "/* NT_BOUNDARY */").unwrap();
        },
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
    let action_map: HashMap<Vec<u8>, &DecisionAction> =
        entries.iter().map(|(p, a)| (p.clone(), a)).collect();

    let mut states: Vec<FlatState> = Vec::with_capacity(next_id as usize);
    let mut sorted_prefixes: Vec<(Vec<u8>, StateId)> = prefix_to_id.into_iter().collect();
    sorted_prefixes.sort_by_key(|(_, id)| *id);

    for (prefix, id) in &sorted_prefixes {
        // Find direct children (prefix + one byte)
        let mut transitions = Vec::new();
        for (other_prefix, other_id) in &sorted_prefixes {
            if other_prefix.len() == prefix.len() + 1 && other_prefix.starts_with(prefix) {
                transitions.push((other_prefix[prefix.len()], *other_id));
            }
        }

        let action = action_map.get(prefix).map(|a| (*a).clone());

        states.push(FlatState { id: *id, transitions, action });
    }

    states
}

/// Diagnostic dump of the decision tree's flat-table structure.
///
/// Produces a human-readable summary for PRATTAIL_DUMP_PARSER debugging.
/// Actual dispatch codegen is the WPDA walker emission in
/// `macros/src/gen/runtime/wpda_codegen/` (trampoline.rs DELETED Stage 10.6).
pub fn emit_flat_table(tree: &CategoryDecisionTree, _token_ids: &TokenIdMap, buf: &mut String) {
    use std::fmt::Write;

    let states = flatten_tree(tree);
    if states.is_empty() {
        return;
    }

    let cat_upper = tree.category.to_uppercase();

    // Emit state transition table
    write!(buf, "const DISPATCH_TABLE_{}: &[(u8, u16)] = &[", cat_upper,).unwrap();

    for state in &states {
        for (byte, target) in &state.transitions {
            write!(buf, "({}, {}),", byte, target).unwrap();
        }
    }
    buf.push_str("];");

    // Emit state metadata (offset into transition table + action tag)
    write!(buf, "const STATE_META_{}: &[(u16, u16, u8)] = &[", cat_upper,).unwrap();

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
/// a decision tree (they are handled by the WPDA walker codegen's cross-cat
/// and InfixLoop arms; dispatch.rs/pratt.rs DELETED).
#[cfg(test)]
pub fn has_decision_tree(trees: &HashMap<String, CategoryDecisionTree>, category: &str) -> bool {
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
pub(crate) fn dt_diagnostic(
    id: DiagnosticId,
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
