use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// Byte encoding constants
// ══════════════════════════════════════════════════════════════════════════════

/// Marker byte for an ident capture position.
pub(crate) const IDENT_CAPTURE: u8 = 0x80;

/// Marker byte for a binder capture position.
pub(crate) const BINDER_CAPTURE: u8 = 0x81;

/// Base byte for nonterminal category IDs: category_index + NT_BASE.
pub(crate) const NT_BASE: u8 = 0x82;

/// Marker byte for optional group start.
pub(crate) const OPTIONAL_START: u8 = 0xC0;

/// Marker byte for optional group end.
pub(crate) const OPTIONAL_END: u8 = 0xC1;

/// Maximum terminal token ID that fits in the encoding.
pub(crate) const MAX_TERMINAL_ID: u8 = 0x7F;

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
    Ambiguous { candidates: Vec<AmbiguousCandidate> },
    /// Nonterminal boundary — dispatch based on FIRST set expansion.
    NonterminalBoundary { options: Vec<NTOption> },
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
            },
            DecisionAction::Ambiguous { candidates: cs } => {
                candidates.extend(cs.iter().cloned());
            },
            DecisionAction::NonterminalBoundary { .. } => {
                return AlgebraicResult::Identity(1);
            },
        }
        match other {
            DecisionAction::Commit { rule_label, category, weight } => {
                candidates.push(AmbiguousCandidate {
                    rule_label: rule_label.clone(),
                    category: category.clone(),
                    weight: *weight,
                    remaining_items: 0,
                });
            },
            DecisionAction::Ambiguous { candidates: cs } => {
                candidates.extend(cs.iter().cloned());
            },
            DecisionAction::NonterminalBoundary { .. } => {
                return AlgebraicResult::Identity(2);
            },
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
            },
            DecisionAction::NonterminalBoundary { .. } => Vec::new(),
        };
        v.into_iter()
    }

    /// All candidates as owned values (synthesizing one for Commit).
    pub(crate) fn all_candidates(&self) -> Vec<AmbiguousCandidate> {
        match self {
            DecisionAction::Commit { rule_label, category, weight } => {
                vec![AmbiguousCandidate {
                    rule_label: rule_label.clone(),
                    category: category.clone(),
                    weight: *weight,
                    remaining_items: 0,
                }]
            },
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
            },
            DecisionAction::Ambiguous { candidates } => {
                1u8.hash(state);
                for c in candidates {
                    c.rule_label.hash(state);
                }
            },
            DecisionAction::NonterminalBoundary { options } => {
                2u8.hash(state);
                options.len().hash(state);
            },
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
    /// Multiple rules share this token and suffixes overlap — Walker emits a
    /// Fork over the rule_labels with lex-min disambiguation. Renamed from the
    /// historical `NfaTryAll` (the trampoline-era runtime mechanism is gone;
    /// this variant survives because static analyses still want to enumerate
    /// the ambiguous prefix-overlap set for diagnostics).
    AmbiguousFanout {
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
                    },
                    DecisionAction::Ambiguous { candidates } => DispatchStrategy::AmbiguousFanout {
                        rule_labels: candidates.iter().map(|c| c.rule_label.clone()).collect(),
                        shared_prefix_len: 0,
                        shared_terminals: Vec::new(),
                        live_rules_context: None,
                    },
                    // CD07 Phase 4A (2026-06-10; FV: CD07_NfaFallbackNonLoss
                    // .{nfa_fallback_nonlossy, fixed_empty_boundary_not_present}):
                    // a boundary entry CARRIES the rules reachable through its
                    // continuation segments — mapping it to NotPresent reported
                    // a rule-carrying token as resolved-by-absence, which let
                    // the NFA-spillover refinement (pipeline.rs "1.7a") strip
                    // the category's NFA fallback (shipped_spillover_loss).
                    // Surface the reachable rules as a fanout; an EMPTY
                    // boundary still reports NotPresent (conservative).
                    DecisionAction::NonterminalBoundary { options } => {
                        let rule_labels = self.boundary_rule_labels(options);
                        if rule_labels.is_empty() {
                            DispatchStrategy::NotPresent
                        } else {
                            DispatchStrategy::AmbiguousFanout {
                                rule_labels,
                                shared_prefix_len: 0,
                                shared_terminals: Vec::new(),
                                live_rules_context: None,
                            }
                        }
                    },
                }
            },
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
                        None => {
                            is_disjoint = false;
                            break;
                        },
                    };
                    let rule_label = match action {
                        DecisionAction::Commit { rule_label, .. } => rule_label.clone(),
                        _ => {
                            is_disjoint = false;
                            break;
                        },
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
                            },
                            DecisionAction::Ambiguous { candidates } => {
                                for c in candidates {
                                    rule_labels.push(c.rule_label.clone());
                                }
                            },
                            // CD07 Phase 4A (2026-06-10; FV:
                            // CD07_NfaFallbackNonLoss.{fanout_complete,
                            // shipped_drops_boundary}): a mixed
                            // Commit+NonterminalBoundary overlap group must
                            // report the boundary's reachable rules too — the
                            // prior `_ => {}` silently dropped them, so the
                            // dead-rule lint could falsely flag a token as
                            // dead-only while the dropped boundary rules were
                            // live (and any future consumer of the fanout
                            // would under-fork).
                            DecisionAction::NonterminalBoundary { options } => {
                                rule_labels.extend(self.boundary_rule_labels(options));
                            },
                        }
                    }
                    DispatchStrategy::AmbiguousFanout {
                        rule_labels,
                        shared_prefix_len: shared_len - 1, // exclude dispatch token
                        shared_terminals,
                        live_rules_context: None,
                    }
                }
            },
        }
    }

    /// CD07 Phase 4A (2026-06-10; FV: CD07_NfaFallbackNonLoss — the boundary's
    /// `entry_labels`): collect every rule label reachable through a
    /// `NonterminalBoundary`'s continuation segments, transitively (a resume
    /// segment may itself contain boundaries), deduped with deterministic
    /// (sorted) order, cycle-safe via a visited-segment set. This is what
    /// makes `dispatch_strategy` COMPLETE over mixed Commit+Boundary overlap
    /// groups (fanout_complete) and stops a rule-carrying boundary token from
    /// reporting NotPresent (nfa_fallback_nonlossy).
    fn boundary_rule_labels(&self, options: &[NTOption]) -> Vec<String> {
        let mut labels: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let mut visited: HashSet<usize> = HashSet::new();
        let mut stack: Vec<usize> = options.iter().map(|o| o.resume_segment).collect();
        while let Some(seg_idx) = stack.pop() {
            if !visited.insert(seg_idx) {
                continue;
            }
            let Some(segment) = self.segments.get(seg_idx) else {
                continue;
            };
            for (_path, action) in segment.iter() {
                match action {
                    DecisionAction::Commit { rule_label, .. } => {
                        labels.insert(rule_label.clone());
                    },
                    DecisionAction::Ambiguous { candidates } => {
                        for c in candidates {
                            labels.insert(c.rule_label.clone());
                        }
                    },
                    DecisionAction::NonterminalBoundary { options } => {
                        stack.extend(options.iter().map(|o| o.resume_segment));
                    },
                }
            }
        }
        labels.into_iter().collect()
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
                        },
                        DecisionAction::Ambiguous { candidates } => {
                            for c in candidates {
                                entry.insert(c.rule_label.clone());
                            }
                        },
                        _ => {},
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
    pub fn bp_stratification(&self, bp_table: &HashMap<String, u8>) -> Vec<(u8, usize, usize)> {
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
                    },
                    DecisionAction::Ambiguous { candidates } => {
                        for c in candidates {
                            reachable.insert(c.rule_label.clone());
                        }
                    },
                    _ => {},
                }
            }
        }
        reachable
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
        if dispatch_map
            .insert(variant_name.to_string(), rule_label)
            .is_some()
        {
            return None; // Duplicate branch byte — not disjoint
        }
    }

    if dispatch_map.len() >= 2 {
        Some(dispatch_map)
    } else {
        None
    }
}
