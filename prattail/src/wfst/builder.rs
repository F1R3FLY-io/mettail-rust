use super::*;
// B-M2 fix (DEFECT-B): BTreeMap gives deterministic, lexicographically-ordered
// iteration for the two-token enrichment maps (`groups`, `token_to_rule`),
// replacing HashMap's hasher-incidental order that randomized the emitted
// mid-state transition rows and the new-token-id assignment order.
use std::collections::BTreeMap;

// ══════════════════════════════════════════════════════════════════════════════
// A7: Entropy-based adaptive beam width
// ══════════════════════════════════════════════════════════════════════════════

/// A7: Compute per-category beam widths from entropy.
///
/// Maps Shannon entropy to beam width using a linear scaling:
/// - Entropy ≤ `low_threshold` → no beam (deterministic, pruning unnecessary)
/// - Entropy > `low_threshold` → beam = `base_beam + scale * (entropy - low_threshold)`
///
/// Higher-entropy categories (many equally-likely alternatives) get wider beams
/// to explore more possibilities. Low-entropy categories (dominated by one or
/// few alternatives) get narrow beams or no beam at all.
///
/// # Arguments
///
/// * `entropy_bits` — Shannon entropy in bits for this category.
/// * `base_beam` — Minimum beam width for categories above threshold (default: 1.0).
/// * `scale` — Beam width increase per additional bit of entropy (default: 0.5).
/// * `low_threshold` — Entropy below this → no beam (default: 0.5 bits).
/// * `max_beam` — Maximum beam width cap (default: 10.0).
pub fn entropy_to_beam_width(
    entropy_bits: f64,
    base_beam: f64,
    scale: f64,
    low_threshold: f64,
    max_beam: f64,
) -> Option<f64> {
    if entropy_bits <= low_threshold {
        None
    } else {
        let beam = base_beam + scale * (entropy_bits - low_threshold);
        Some(beam.min(max_beam))
    }
}

/// A7: Default entropy-to-beam-width parameters.
pub const ENTROPY_BEAM_BASE: f64 = 1.0;

pub const ENTROPY_BEAM_SCALE: f64 = 0.5;

pub const ENTROPY_BEAM_LOW_THRESHOLD: f64 = 0.5;

pub const ENTROPY_BEAM_MAX: f64 = 10.0;

/// C2: Position-aware NFA disambiguation — weight penalty per token difference.
///
/// When an alternative parse consumed a different number of tokens than the primary,
/// its weight is adjusted by `|pos_diff| * POSITION_WEIGHT_PENALTY` before beam
/// comparison. This implements "longest match" preference analogous to lexing:
/// - Longer matches (higher `alt_pos`) are treated as closer in weight to the primary
///   (they consumed more input, a positive signal).
/// - Shorter matches get penalized (they left more input unconsumed).
///
/// The penalty is applied symmetrically: `adjusted_w = alt_w + |alt_pos - primary_pos| * penalty`.
/// This means a shorter match must have a proportionally lower raw weight to remain competitive.
pub const POSITION_WEIGHT_PENALTY: f64 = 0.5;

// ══════════════════════════════════════════════════════════════════════════════
// Builder
// ══════════════════════════════════════════════════════════════════════════════

/// Builder for constructing a `PredictionWfst` from FIRST sets and dispatch tables.
pub struct PredictionWfstBuilder {
    category: String,
    token_map: TokenIdMap,
    actions: Vec<WeightedAction>,
    transitions: Vec<(TokenId, u32, TropicalWeight)>, // (input, action_idx, weight)
    /// Two-token transitions: (token1_id, token2_id, action_idx, weight)
    two_token_transitions: Vec<(TokenId, TokenId, u32, TropicalWeight)>,
    beam_width: Option<TropicalWeight>,
}

impl PredictionWfstBuilder {
    /// Create a new builder for the given category.
    pub fn new(category: &str, token_map: TokenIdMap) -> Self {
        PredictionWfstBuilder {
            category: category.to_string(),
            token_map,
            actions: Vec::new(),
            transitions: Vec::new(),
            two_token_transitions: Vec::new(),
            beam_width: None,
        }
    }

    /// Set the beam width for the built WFST.
    pub fn with_beam_width(mut self, beam: TropicalWeight) -> Self {
        self.beam_width = Some(beam);
        self
    }

    /// Add a dispatch action for a token with the given weight.
    pub fn add_action(&mut self, token_name: &str, action: DispatchAction, weight: TropicalWeight) {
        let token_id = self.token_map.get_or_insert(token_name);
        let action_idx = self.actions.len() as u32;
        self.actions.push(WeightedAction { action, weight });
        self.transitions.push((token_id, action_idx, weight));
    }

    /// Add a two-token dispatch action: `token1 → intermediate → token2 → accept`.
    ///
    /// Creates a 3-state path: `start --(token1)--> intermediate --(token2)--> accept`.
    /// Used when the first token is ambiguous but the second token disambiguates.
    ///
    /// The weight is split: first hop carries `weight`, second hop carries 0.0
    /// (all disambiguation cost is attributed to the dispatch decision).
    pub fn add_two_token_action(
        &mut self,
        token1: &str,
        token2: &str,
        action: DispatchAction,
        weight: TropicalWeight,
    ) {
        let token1_id = self.token_map.get_or_insert(token1);
        let token2_id = self.token_map.get_or_insert(token2);
        let action_idx = self.actions.len() as u32;
        self.actions.push(WeightedAction { action, weight });
        self.two_token_transitions
            .push((token1_id, token2_id, action_idx, weight));
    }

    /// Build the prediction WFST.
    ///
    /// Creates a multi-level WFST:
    /// - Single-token paths: `start → final` (one final state per action)
    /// - Two-token paths: `start → intermediate → final` (intermediate per unique
    ///   (token1, intermediate_group), final per action)
    pub fn build(self) -> PredictionWfst {
        // State 0: start state
        let mut start_state = WfstState::new(0);

        // Estimate capacity: single-token finals + two-token intermediates + finals
        let estimated_states = 1 + self.transitions.len() + self.two_token_transitions.len() * 2;
        let mut states = Vec::with_capacity(estimated_states);
        states.push(WfstState::new(0)); // overwritten with populated start state below

        // Single-token paths: start → final
        for (token_id, action_idx, weight) in &self.transitions {
            let final_id = states.len() as WfstStateId;
            states.push(WfstState::final_state(final_id, TropicalWeight::one()));

            start_state.transitions.push(WeightedTransition {
                from: 0,
                input: *token_id,
                action_idx: *action_idx,
                to: final_id,
                weight: *weight,
            });
        }

        // Two-token paths: start → intermediate → final
        // Group by token1 to share intermediate states
        if !self.two_token_transitions.is_empty() {
            let mut intermediate_map: HashMap<TokenId, WfstStateId> = HashMap::new();

            for (token1_id, token2_id, action_idx, weight) in &self.two_token_transitions {
                // Get or create intermediate state for this token1
                let mid_id = *intermediate_map.entry(*token1_id).or_insert_with(|| {
                    let mid = states.len() as WfstStateId;
                    states.push(WfstState::new(mid)); // non-final intermediate
                                                      // Add transition from start to intermediate (weight on first hop)
                    start_state.transitions.push(WeightedTransition {
                        from: 0,
                        input: *token1_id,
                        action_idx: 0, // sentinel: intermediate edge, not an action
                        to: mid,
                        weight: TropicalWeight::new(0.0), // weight deferred to second hop
                    });
                    mid
                });

                // Create final state for this action
                let final_id = states.len() as WfstStateId;
                states.push(WfstState::final_state(final_id, TropicalWeight::one()));

                // Add transition from intermediate to final (carries the action weight)
                states[mid_id as usize]
                    .transitions
                    .push(WeightedTransition {
                        from: mid_id,
                        input: *token2_id,
                        action_idx: *action_idx,
                        to: final_id,
                        weight: *weight,
                    });
            }
        }

        states[0] = start_state;

        PredictionWfst {
            category: self.category,
            states,
            start: 0,
            actions: self.actions,
            token_map: self.token_map,
            beam_width: self.beam_width,
            context_labels: HashMap::new(),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Construction from existing prediction analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Build prediction WFSTs for all categories from FIRST sets and overlap analysis.
///
/// Weight assignment strategy:
/// - Tokens unique to one category (no overlap): weight 0.0 (deterministic)
/// - Tokens shared across categories: weight = declaration_order * 1.0
///   (earlier-declared rules get lower weight)
/// - Cross-category with backtrack: source path weight 0.5, fallback weight 1.0
///   (try source first since it's the explicit cross-category rule)
pub fn build_prediction_wfsts(
    categories: &[String],
    first_sets: &HashMap<String, FirstSet>,
    overlaps: &HashMap<(String, String), CrossCategoryOverlap>,
    dispatch_actions: &HashMap<String, HashMap<String, DispatchAction>>,
) -> HashMap<String, PredictionWfst> {
    let mut result = HashMap::new();

    // Build shared token ID map from all FIRST sets
    let mut all_tokens: Vec<String> = Vec::new();
    for first_set in first_sets.values() {
        all_tokens.extend(first_set.tokens.iter().cloned());
    }
    let token_map = TokenIdMap::from_names(all_tokens);

    for category in categories {
        let mut builder = PredictionWfstBuilder::new(category, token_map.clone());

        if let Some(category_actions) = dispatch_actions.get(category) {
            let mut token_order: Vec<(&String, &DispatchAction)> =
                category_actions.iter().collect();
            // Sort for deterministic ordering (HashMap iteration order is arbitrary)
            token_order.sort_by(|(a, _), (b, _)| a.cmp(b));

            for (order, (token_name, action)) in token_order.iter().enumerate() {
                // Determine weight based on ambiguity analysis
                let weight = compute_action_weight(
                    token_name, action, category, first_sets, overlaps, order,
                );

                builder.add_action(token_name, (*action).clone(), weight);
            }
        }

        result.insert(category.clone(), builder.build());
    }

    result
}

/// Enrich prediction WFSTs with two-token paths for NFA-ambiguous groups.
///
/// For each category, identifies dispatch tokens where multiple RD rules
/// share the same first token. When the second syntax item uniquely identifies
/// the rule within the group — either directly (terminal) or via FIRST set
/// expansion (nonterminal) — adds two-token paths to the WFST:
/// `start --(token1)--> intermediate --(token2)--> accept`.
///
/// This migrates the `second_token_lookahead()` and `suffix_disjointness_check()`
/// analyses from trampoline.rs into the WFST itself, making them queryable by
/// all consumers (lint, decision tree, cost-benefit, error recovery).
///
/// ## FIRST-Set Expansion (Sprint 2)
///
/// When `items[1]` is `NonTerminal { category }`, the second-level transitions
/// are expanded using `FIRST(category)`. Each token in the FIRST set becomes a
/// second-level transition. This resolves cases like:
/// - `float ( Expr )` vs `float ( Ident )` — if FIRST(Expr) and FIRST(Ident)
///   are disjoint, the second token disambiguates.
///
/// Returns the number of two-token paths added across all categories.
pub fn enrich_with_two_token_paths(
    wfsts: &mut HashMap<String, PredictionWfst>,
    rd_rules: &[crate::grammar::ir::RDRuleInfo],
    category_names: &[String],
    first_sets: &HashMap<String, crate::prediction::FirstSet>,
) -> usize {
    use crate::grammar::ir::RDSyntaxItem;

    let mut total_added = 0;

    for cat in category_names {
        let wfst = match wfsts.get_mut(cat) {
            Some(w) => w,
            None => continue,
        };

        // Group RD rules by their dispatch token (first terminal). BTreeMap so the
        // `for (dispatch_token, rules) in &groups` loop below iterates dispatch
        // tokens in lexicographic order (deterministic mid-state ids + start-
        // transition append order across builds). (B-M2 fix, DEFECT-B.)
        let mut groups: BTreeMap<String, Vec<&crate::grammar::ir::RDRuleInfo>> = BTreeMap::new();
        for rule in rd_rules {
            if rule.category != *cat {
                continue;
            }
            if rule.is_pure_collection_literal() || rule.prefix_bp.is_some() {
                continue;
            }
            if let Some(RDSyntaxItem::Terminal(t)) = rule.items.first() {
                groups.entry(t.clone()).or_default().push(rule);
            }
        }

        // For ambiguous groups (>1 rule), check if second-position analysis resolves them
        for (dispatch_token, rules) in &groups {
            if rules.len() < 2 {
                continue;
            }

            // Build per-rule FIRST sets for items[1..] (suffix after dispatch token).
            // Terminal items[1] contribute their variant name directly.
            // NonTerminal items[1] contribute FIRST(category) tokens.
            // IdentCapture/Binder contribute "Ident".
            let mut per_rule_second_tokens: Vec<(&str, Vec<String>)> =
                Vec::with_capacity(rules.len());
            let mut all_valid = true;

            for rule in rules {
                if rule.items.len() < 2 {
                    all_valid = false;
                    break;
                }
                let suffix = &rule.items[1..];
                let (first, _nullable) = crate::prediction::first_of_rd_suffix(suffix, first_sets);
                if first.tokens.is_empty() {
                    all_valid = false;
                    break;
                }
                // Sort the drained FIRST-set tokens: `first.tokens` is a HashSet
                // whose drain order is hasher-incidental. Belt-and-braces — after
                // the disjointness gate below each token maps to exactly one rule,
                // so the per-rule vec is length-1 in practice — but sorting keeps
                // the intermediate deterministic. (B-M2 fix, DEFECT-B.)
                let mut second_tokens: Vec<String> = first.tokens.into_iter().collect();
                second_tokens.sort();
                per_rule_second_tokens.push((&rule.label, second_tokens));
            }

            if !all_valid {
                continue;
            }

            // Check pairwise disjointness: each second-position token must map to
            // exactly one rule. This is the WFST analog of suffix_disjointness_check().
            // BTreeMap so the `for (second_token, rule_labels) in &token_to_rule`
            // loop below iterates second tokens in lexicographic order — the SAME
            // "alphabetical by disambiguating token" convention as the single-token
            // `token_order.sort_by(|(a,_),(b,_)| a.cmp(b))` in build_prediction_wfsts
            // and `TokenIdMap::from_names`. This map is the DIRECT source of both
            // the emitted mid-state transition row order and the new-token-id
            // assignment order. (B-M2 fix, DEFECT-B: the actual randomizer.)
            let mut token_to_rule: BTreeMap<String, Vec<&str>> = BTreeMap::new();
            for (rule_label, tokens) in &per_rule_second_tokens {
                for token in tokens {
                    token_to_rule
                        .entry(token.clone())
                        .or_default()
                        .push(rule_label);
                }
            }

            if token_to_rule.values().any(|rules| rules.len() > 1) {
                continue; // Overlapping FIRST sets — can't disambiguate
            }

            // Disjoint! Add two-token paths for each (token2 → rule) mapping.
            let dispatch_token_variant =
                crate::automata::codegen::terminal_to_variant_name(dispatch_token);
            let token1_id = match wfst.token_map.get(&dispatch_token_variant) {
                Some(id) => id,
                None => wfst.token_map.get_or_insert(&dispatch_token_variant),
            };

            // Create a shared intermediate state for this dispatch token group
            let mid_id = wfst.states.len() as WfstStateId;
            wfst.states.push(WfstState::new(mid_id));

            // Add start → intermediate transition
            if let Some(start) = wfst.states.get_mut(wfst.start as usize) {
                start.transitions.push(WeightedTransition {
                    from: wfst.start,
                    input: token1_id,
                    action_idx: 0, // sentinel: intermediate edge, not an action
                    to: mid_id,
                    weight: TropicalWeight::new(0.0),
                });
            }

            // Preallocate the exact number of two-token paths about to be emitted:
            // one final state + one action + one mid→final transition per disjoint
            // second token. (DEFECT-B.)
            let path_count = token_to_rule.len();
            wfst.states.reserve(path_count);
            wfst.actions.reserve(path_count);
            wfst.states[mid_id as usize].transitions.reserve(path_count);

            for (second_token, rule_labels) in &token_to_rule {
                let rule_label = rule_labels[0];

                // Find the existing action for this rule to clone it
                let action = wfst
                    .actions
                    .iter()
                    .find(|a| a.action.rule_label() == rule_label);
                let (dispatch_action, weight) = if let Some(wa) = action {
                    (wa.action.clone(), wa.weight)
                } else {
                    (
                        DispatchAction::Direct {
                            rule_label: rule_label.to_string(),
                            parse_fn: format!("parse_{}", rule_label.to_lowercase()),
                        },
                        TropicalWeight::new(0.0),
                    )
                };

                // Register second token in token map
                let token2_id = wfst.token_map.get_or_insert(second_token);

                // Create final state
                let final_id = wfst.states.len() as WfstStateId;
                wfst.states
                    .push(WfstState::final_state(final_id, TropicalWeight::one()));

                // Register the action
                let action_idx = wfst.actions.len() as u32;
                wfst.actions
                    .push(WeightedAction { action: dispatch_action, weight });

                // Add intermediate → final transition
                wfst.states[mid_id as usize]
                    .transitions
                    .push(WeightedTransition {
                        from: mid_id,
                        input: token2_id,
                        action_idx,
                        to: final_id,
                        weight,
                    });

                total_added += 1;
            }
        }
    }

    total_added
}

/// Compute the tropical weight for a dispatch action.
///
/// Weight assignment:
/// - `Direct`: weight 0.0 (unambiguous, deterministic)
/// - `CrossCategory` with `needs_backtrack: false`: weight 0.0 (deterministic)
/// - `CrossCategory` with `needs_backtrack: true`: weight 0.5 (try source first)
/// - `Lookahead`: weight 1.0 + order (needs extra tokens to decide)
/// - `Cast`: weight 0.5 (slightly penalized vs direct)
/// - `Grouping`: weight 0.0 (delimiter-driven, deterministic)
/// - `Variable`: weight 2.0 (last resort)
pub(crate) fn compute_action_weight(
    _token_name: &str,
    action: &DispatchAction,
    _category: &str,
    _first_sets: &HashMap<String, FirstSet>,
    _overlaps: &HashMap<(String, String), CrossCategoryOverlap>,
    order: usize,
) -> TropicalWeight {
    match action {
        DispatchAction::Direct { .. } => TropicalWeight::new(0.0),
        DispatchAction::Grouping { .. } => TropicalWeight::new(0.0),
        DispatchAction::CrossCategory { needs_backtrack, .. } => {
            if *needs_backtrack {
                TropicalWeight::new(0.5)
            } else {
                TropicalWeight::new(0.0)
            }
        },
        DispatchAction::Cast { .. } => TropicalWeight::new(0.5),
        DispatchAction::Lookahead { .. } => TropicalWeight::new(1.0 + order as f64),
        DispatchAction::Variable { .. } => TropicalWeight::new(2.0),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// C1: Semantic Weight Feedback
// ══════════════════════════════════════════════════════════════════════════════

/// C1: A weight correction event recorded when the Ascent semantic layer
/// selects a non-primary alternative during NFA disambiguation.
///
/// When `from_alternatives()` or the spillover replay mechanism chooses an
/// alternative different from the weight-best (primary), this indicates that
/// the WFST's prediction weights were "wrong" for this input. Collecting
/// these corrections enables downstream consumers to:
///
/// 1. **Adjust weights offline**: Feed corrections to the `training.rs` SGD
///    infrastructure to update prediction weights between compilations.
/// 2. **Report weight accuracy**: Language servers can display per-category
///    prediction accuracy statistics.
/// 3. **Detect systematic mispredictions**: If the same category repeatedly
///    generates corrections, its WFST weights need retraining.
#[derive(Debug, Clone, PartialEq)]
pub struct WeightCorrection {
    /// Category where the correction occurred.
    pub category: &'static str,
    /// WFST tropical weight of the primary (best) alternative that was rejected.
    pub primary_weight: f64,
    /// WFST tropical weight of the alternative that was actually selected.
    pub selected_weight: f64,
    /// Number of alternatives that were considered (total candidates including primary).
    pub alternatives_considered: usize,
}

impl WeightCorrection {
    /// Weight delta: how much the prediction was off.
    ///
    /// Positive means the selected alternative had higher weight (worse predicted
    /// rank) than the primary — the WFST underestimated this alternative.
    /// Negative means the selected had lower weight — unusual, indicates the
    /// primary was accepted by weight but a better semantic match existed.
    #[inline]
    pub fn weight_delta(&self) -> f64 {
        self.selected_weight - self.primary_weight
    }

    /// Suggested weight adjustment for the primary rule: increase its weight
    /// (make it less preferred) by a fraction of the delta.
    ///
    /// The adjustment is clamped to `[0.0, max_adjustment]` to prevent
    /// overcorrection from a single event.
    #[inline]
    pub fn primary_adjustment(&self, learning_rate: f64, max_adjustment: f64) -> f64 {
        // If selected had higher weight, primary should also go up (penalize)
        // If selected had lower weight, primary should go down (this is rarer)
        let raw = self.weight_delta().abs() * learning_rate;
        raw.min(max_adjustment).max(0.0)
    }
}

#[cfg(test)]
mod defect_b_structural_tests {
    use crate::grammar::ir::{RDRuleInfo, RDSyntaxItem};
    use crate::prediction::FirstSet;
    use crate::token_id::TokenIdMap;
    use crate::wfst::{PredictionWfst, WfstState};
    use std::collections::HashMap;

    /// Build a two-terminal RD rule `Cat -> t1 t2` (dispatch token `t1`, second
    /// token `t2`), with every non-relevant flag cleared so `enrich_with_two_token_paths`
    /// admits it (not a collection, no prefix bp).
    fn rd_two_terminal(label: &str, category: &str, t1: &str, t2: &str) -> RDRuleInfo {
        RDRuleInfo {
            label: label.to_string(),
            category: category.to_string(),
            items: vec![
                RDSyntaxItem::Terminal(t1.to_string()),
                RDSyntaxItem::Terminal(t2.to_string()),
            ],
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        }
    }

    /// DEFECT-B B-M2 durable structural guard (amendment 5). All four rules share
    /// the dispatch token `@` and carry pairwise-disjoint second terminals
    /// (`!`, `,`, `=`, `;` ⇒ Bang, Comma, Eq, Semi), so `enrich_with_two_token_paths`
    /// builds ONE mid state with four token2→final transitions. Pre-fix, those
    /// transitions landed in `HashMap<String, Vec<&str>>` iteration order (the
    /// randomizer of the emitted `WFST_TRANSITIONS_<Cat>` mid rows); post-fix the
    /// `BTreeMap` keying makes their order lexicographic by second-token name.
    ///
    /// This asserts the emitted mid-row order is sorted-by-second-token — a
    /// DETERMINISTIC assertion (unlike the probabilistic byte-soak G2), rebuilt
    /// across 16 fresh rounds so a pre-fix regression (random order) is caught
    /// with probability 1 − (1/4!)^16 ≈ 1 − 2^-73.
    #[test]
    fn two_token_mid_transitions_sorted_by_second_token() {
        const ROUNDS: usize = 16;
        let category_names = vec!["Stmt".to_string()];
        let first_sets: HashMap<String, FirstSet> = HashMap::new();
        let rd_rules = vec![
            rd_two_terminal("SendBang", "Stmt", "@", "!"),
            rd_two_terminal("SendComma", "Stmt", "@", ","),
            rd_two_terminal("SendEq", "Stmt", "@", "="),
            rd_two_terminal("SendSemi", "Stmt", "@", ";"),
        ];
        let expected = vec!["Bang", "Comma", "Eq", "Semi"];

        let mut divergent_rounds: Vec<(usize, Vec<String>)> = Vec::new();
        for round in 0..ROUNDS {
            // Fresh WFST each round: enrich APPENDS, and every round rebuilds the
            // `groups`/`token_to_rule` maps ⇒ a fresh per-instance RandomState.
            let mut wfsts: HashMap<String, PredictionWfst> = HashMap::with_capacity(1);
            wfsts.insert(
                "Stmt".to_string(),
                PredictionWfst {
                    category: "Stmt".to_string(),
                    states: vec![WfstState::new(0)],
                    start: 0,
                    actions: Vec::new(),
                    token_map: TokenIdMap::new(),
                    beam_width: None,
                    context_labels: HashMap::new(),
                },
            );

            let added = super::enrich_with_two_token_paths(
                &mut wfsts,
                &rd_rules,
                &category_names,
                &first_sets,
            );
            assert_eq!(added, 4, "all four disjoint second tokens must produce paths");

            let wfst = wfsts.get("Stmt").expect("Stmt wfst present");
            let start = &wfst.states[wfst.start as usize];
            assert_eq!(
                start.transitions.len(),
                1,
                "one dispatch group (`@`) ⇒ exactly one start→mid edge",
            );
            let mid_id = start.transitions[0].to;
            let mid = &wfst.states[mid_id as usize];

            let names: Vec<String> = mid
                .transitions
                .iter()
                .map(|t| {
                    wfst.token_map
                        .name(t.input)
                        .expect("every mid transition's token id has a name")
                        .to_string()
                })
                .collect();

            if names != expected {
                divergent_rounds.push((round, names));
            }
        }

        assert!(
            divergent_rounds.is_empty(),
            "mid-state two-token transitions must be emitted sorted by second-token \
             name {expected:?} in EVERY round; diverged in {}/{} rounds: {:?}",
            divergent_rounds.len(),
            ROUNDS,
            divergent_rounds,
        );
    }
}
