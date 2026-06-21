use super::*;

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
                },
                RDSyntaxItem::NonTerminal { category, .. } => {
                    if let Some(&cat_id) = self.category_id_map.get(category) {
                        elements.push(PatternElement::NonTerminal {
                            category: category.clone(),
                            category_id: cat_id,
                        });
                    }
                },
                RDSyntaxItem::IdentCapture { param_name } => {
                    elements.push(PatternElement::IdentCapture { param_name: param_name.clone() });
                },
                RDSyntaxItem::Binder { param_name, .. } => {
                    elements.push(PatternElement::BinderCapture { param_name: param_name.clone() });
                },
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
                },
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
    pub fn encode_terminal_prefix(pattern: &[PatternElement]) -> (Vec<u8>, Option<NTBoundaryInfo>) {
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
                },
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
                self.insert_nt_continuation(
                    &rule.category,
                    &rule.label,
                    weight,
                    &boundary,
                    &prefix_bytes,
                );
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
        let mut record = NTBoundaryRecord {
            nt_category: boundary.category.clone(),
            resume_segment: 0,
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

        // Update the record with the actual resume segment index.
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
                        if let Some(tok_id) = wfst_token_byte(&self.token_ids, token) {
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

    /// Insert foreign-leading nonterminal rules.
    ///
    /// Rules such as `POutput . n:Name, p:Proc |- n "!" "(" p ")" : Proc`
    /// are not prefix commits: runtime first delegates to `Name`, then the
    /// Pratt/mixfix loop consumes `!` and fires `POutput`. Recording the
    /// two-token path `[FIRST(Name), Bang]` keeps trie reachability aligned
    /// with that runtime path for dead-rule analysis.
    pub fn insert_foreign_leading_nt_rules(&mut self, rd_rules: &[RDRuleInfo]) {
        for rule in rd_rules {
            if self.dead_rules.contains(&rule.label) {
                continue;
            }
            if rule.is_collection || rule.prefix_bp.is_some() || rule.items.len() < 2 {
                continue;
            }

            let Some(RDSyntaxItem::NonTerminal { category: source_category, .. }) =
                rule.items.first()
            else {
                continue;
            };
            if source_category == &rule.category {
                continue;
            }

            let Some(RDSyntaxItem::Terminal(operator)) = rule.items.get(1) else {
                continue;
            };
            let operator_variant = terminal_to_variant_name(operator);
            let Some(op_id) = self.encode_terminal(&operator_variant) else {
                continue;
            };

            let Some(source_first) = self.first_sets.get(source_category).cloned() else {
                continue;
            };
            let weight = self.rule_weight(&rule.label, &rule.category);
            for token in &source_first.tokens {
                if let Some(tok_id) = wfst_token_byte(&self.token_ids, token) {
                    let path = vec![tok_id, op_id];
                    let action = DecisionAction::Commit {
                        rule_label: rule.label.clone(),
                        category: rule.category.clone(),
                        weight,
                    };
                    let tree = self.ensure_tree(&rule.category);
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

    /// Insert cast rules.
    pub fn insert_cast_rules(&mut self, cast_rules: &[CastRule]) {
        for rule in cast_rules {
            if self.dead_rules.contains(&rule.label) {
                continue;
            }
            // Cast/projection dispatch follows the generated prefix
            // runtime's unified-bucket model: overlapping source/target
            // FIRST tokens are forked, not suppressed. Older analyses used
            // `source - target` here, which under-approximated rules like
            // `ProcInt . i:Int |- i : Proc` when `Proc` also had Integer in
            // its own FIRST set.
            let source_first = self.first_sets.get(&rule.source_category).cloned();
            if let Some(sf) = source_first {
                let weight = self.rule_weight(&rule.label, &rule.target_category);
                for token in &sf.tokens {
                    if let Some(tok_id) = wfst_token_byte(&self.token_ids, token) {
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
        self.insert_foreign_leading_nt_rules(rd_rules);
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
            let first_set =
                first_set_of_pattern_suffix(&record.remaining_pattern, first_sets, token_ids);
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
pub(crate) fn first_set_of_pattern_suffix(
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
            },
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
            },
            PatternElement::IdentCapture { .. } => {
                result.insert("Ident");
                nullable = false;
                break;
            },
            PatternElement::BinderCapture { .. } => {
                result.insert("Ident");
                nullable = false;
                break;
            },
            PatternElement::OptionalStart | PatternElement::OptionalEnd => {
                // Optional markers don't contribute to FIRST; continue
            },
        }
    }

    result.nullable = nullable;
    result
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
                },
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
                },
                _ => {},
            }
        }
        for path in removals {
            segment.remove(&path);
        }
    }
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
/// Bump this whenever the WPDA walker codegen
/// (macros/src/gen/runtime/wpda_codegen/) or this decision-tree logic
/// changes. (trampoline.rs/recursive.rs/dispatch.rs/pratt.rs DELETED.)
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
            if c.len() < 4 {
                return None;
            }
            let val = u32::from_le_bytes([c[0], c[1], c[2], c[3]]);
            *c = &c[4..];
            Some(val)
        };
        let read_u128 = |c: &mut &[u8]| -> Option<u128> {
            if c.len() < 16 {
                return None;
            }
            let mut buf = [0u8; 16];
            buf.copy_from_slice(&c[..16]);
            *c = &c[16..];
            Some(u128::from_le_bytes(buf))
        };
        let read_bytes = |c: &mut &[u8], len: usize| -> Option<Vec<u8>> {
            if c.len() < len {
                return None;
            }
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

        Some(IncrementalState { version, category_hashes, category_code })
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
            let code = self
                .category_code
                .get(name)
                .map(|s| s.as_str())
                .unwrap_or("");
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
    use crate::pipeline::convert_syntax_item_to_rd;
    use crate::prediction::{compute_first_sets, FirstItem, RuleInfo};

    let category_names: Vec<String> = spec.types.iter().map(|t| t.name.clone()).collect();
    if category_names.is_empty() {
        return None;
    }

    // Build RuleInfo for FIRST set computation (mirrors pipeline.rs logic)
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
                    crate::SyntaxItemSpec::Terminal(t) => FirstItem::Terminal(t.clone()),
                    crate::SyntaxItemSpec::NonTerminal { category, .. } => {
                        if category_names.contains(category) {
                            FirstItem::NonTerminal(category.clone())
                        } else {
                            FirstItem::Ident
                        }
                    },
                    _ => FirstItem::Ident,
                })
                .collect(),
            is_infix: r.is_infix,
            is_var: r.is_var,
            is_literal: r.is_literal,
            is_cross_category: r.is_cross_category,
            is_cast: r.is_cast,
        })
        .collect();

    // Compute FIRST sets
    let first_sets = compute_first_sets(&rule_infos, &category_names);

    // Build TokenIdMap from all terminal tokens
    let mut token_id_map = crate::token_id::TokenIdMap::new();
    for fs in first_sets.values() {
        for tok in fs.tokens.iter() {
            token_id_map.get_or_insert(tok);
        }
    }
    for v in &[
        "Eof", "RParen", "RBrace", "RBracket", "Semi", "Comma", "LParen", "LBrace", "LBracket",
    ] {
        token_id_map.get_or_insert(v);
    }

    // Build RD rules (non-infix, non-var, non-literal)
    let rd_rules: Vec<RDRuleInfo> = spec
        .rules
        .iter()
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
                    if let crate::SyntaxItemSpec::Terminal(t) = item {
                        Some(t.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or_default(),
            needs_backtrack: false,
        })
        .collect();

    // Build cast rules
    let cast_rules: Vec<CastRule> = spec
        .rules
        .iter()
        .filter(|r| r.is_cast)
        .map(|r| CastRule {
            label: r.label.clone(),
            source_category: r.cast_source_category.clone().unwrap_or_default(),
            target_category: r.category.clone(),
            shares_infix_with_target: false,
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
