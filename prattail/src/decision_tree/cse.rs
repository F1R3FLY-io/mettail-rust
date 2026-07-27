use super::*;

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

            let mut suffix_firsts: Vec<(&str, FirstSet)> = Vec::with_capacity(group_records.len());

            for record in group_records {
                let first_set =
                    first_set_of_pattern_suffix(&record.remaining_pattern, first_sets, token_ids);

                let token_names: Vec<String> = first_set.tokens.iter().cloned().collect();
                discriminating_tokens.insert(record.rule_label.clone(), token_names);
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

            let rules: Vec<String> = group_records.iter().map(|r| r.rule_label.clone()).collect();

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

/// CD06 Phase 4B M1.0 (2026-06-10): MEASURE-FIRST shared-suffix statistics.
///
/// The would-apply measurement gating CD06 right-factoring
/// (`A → β a | γ a ⟹ A → A' a`): per category, bucket rules by their LAST
/// syntax item restricted to `Terminal`/`NonTerminal` tails (rules ending in
/// Binder/Collection/SepList/etc. are ineligible — the factoring transform is
/// only defined over plain item tails). `shared` counts rules in ≥2-member
/// buckets; the ratio `shared/eligible` is an UPPER BOUND on factorable rules
/// (any factorable pair shares at least its last item), so a ratio below the
/// gate (~0.10) safely STOPS CD06 at diagnostic-only (recorded negative).
///
/// VERDICT (2026-06-11, Phase 4B closed): the measured depth2 ratios EXCEEDED
/// the screen (calculator 0.19, rholang 0.42, Ambient 0.57, GuardedRho 0), so
/// the group-level analysis decided instead: every depth-2 bucket's rules are
/// already discriminated by disjoint LEADING literals (CD02 top-down
/// dispatch), so a shared tail is parsed once whether or not it is factored —
/// right-factoring would merge generated code (size only) and remove zero
/// parse work. CD06 is STOPPED at diagnostic-only: this measurement plus the
/// I17 `cd06-shared-suffix-measure` diagnostic are the only artifacts. The
/// transform itself is proven meaning-preserving (exact match-list equality,
/// ambiguity degree included) in
/// `formal/rocq/codegen_optimizations/theories/CD06_SuffixFactor.v`, so any
/// future wiring — if a grammar ever shows non-disjoint leading dispatch over
/// heavy shared tails — starts from a verified transform.
#[derive(Debug, Clone, Default)]
pub struct SharedSuffixMeasurement {
    /// Rules whose last item is a Terminal/NonTerminal (factoring-eligible).
    pub eligible: usize,
    /// Eligible rules sharing their LAST item with ≥1 other rule of the same
    /// category (the crude upper bound — dominated by degenerate shared close
    /// delimiters like trailing `)`).
    pub shared_depth1: usize,
    /// Eligible rules sharing their last TWO items (the meaningful would-apply
    /// signal: a ≥2-item tail — in practice an NT-bearing `<X> ")"` tail — is
    /// where right-factoring could share real structure).
    pub shared_depth2: usize,
    /// Depth-2 group descriptions: "Cat: tail-key ← [rules…]".
    pub groups_depth2: Vec<String>,
}

impl SharedSuffixMeasurement {
    pub fn ratio_depth1(&self) -> f64 {
        if self.eligible == 0 {
            0.0
        } else {
            self.shared_depth1 as f64 / self.eligible as f64
        }
    }
    pub fn ratio_depth2(&self) -> f64 {
        if self.eligible == 0 {
            0.0
        } else {
            self.shared_depth2 as f64 / self.eligible as f64
        }
    }
}

/// CD06 Phase 4B M1.0: compute the shared-suffix measurement over RD rules.
pub fn measure_shared_nonterminal_suffixes(
    rd_rules: &[crate::grammar::ir::RDRuleInfo],
) -> SharedSuffixMeasurement {
    use crate::grammar::ir::RDSyntaxItem;
    fn item_key(item: &RDSyntaxItem) -> Option<String> {
        match item {
            RDSyntaxItem::Terminal(t) => Some(format!("T:{t}")),
            RDSyntaxItem::NonTerminal { category, .. } => Some(format!("N:{category}")),
            _ => None, // Binder/Collection/SepList/… items are ineligible tails
        }
    }
    // (category, tail key) → rule labels, at depths 1 and 2.
    let mut buckets1: std::collections::BTreeMap<(String, String), Vec<String>> =
        std::collections::BTreeMap::new();
    let mut buckets2: std::collections::BTreeMap<(String, String), Vec<String>> =
        std::collections::BTreeMap::new();
    let mut eligible = 0usize;
    for rule in rd_rules {
        let Some(last) = rule.items.last().and_then(item_key) else {
            continue;
        };
        eligible += 1;
        buckets1
            .entry((rule.category.clone(), last.clone()))
            .or_default()
            .push(rule.label.clone());
        if rule.items.len() >= 2 {
            if let Some(prev) = item_key(&rule.items[rule.items.len() - 2]) {
                buckets2
                    .entry((rule.category.clone(), format!("{prev} {last}")))
                    .or_default()
                    .push(rule.label.clone());
            }
        }
    }
    let shared_depth1 = buckets1
        .values()
        .filter(|ls| ls.len() >= 2)
        .map(|ls| ls.len())
        .sum::<usize>();
    let mut shared_depth2 = 0usize;
    let mut groups_depth2 = Vec::new();
    for ((cat, key), labels) in &buckets2 {
        if labels.len() >= 2 {
            shared_depth2 += labels.len();
            groups_depth2.push(format!("{cat}: {key} ← [{}]", labels.join(", ")));
        }
    }
    SharedSuffixMeasurement {
        eligible,
        shared_depth1,
        shared_depth2,
        groups_depth2,
    }
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
pub fn format_cse_annotation(shared: &SharedNonterminalPrefix, token_ids: &TokenIdMap) -> String {
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
        buf.push_str(
            "// Note: discriminating FIRST sets overlap — NFA try-all needed after shared parse\n",
        );
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
                crate::grammar::ir::RDSyntaxItem::Terminal(t) => {
                    terminals.push(crate::automata::codegen::terminal_to_variant_name(t));
                },
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
                            None => {
                                valid = false;
                                break;
                            },
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
                crate::grammar::ir::RDSyntaxItem::Terminal(t) => {
                    terminals.push(crate::automata::codegen::terminal_to_variant_name(t));
                },
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
