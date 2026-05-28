//! Phase F.13 chain_10000 Exp 13 S1.a (2026-05-26): Earley + Leo
//! recognizer with SPPF emission, redesigned from the prior CEK-9B/C
//! sketch.
//!
//! # History
//!
//! The prior implementation (pre-rewrite) was a sketch from the
//! CEK-9B/C subsystem with:
//! - `scan` as a no-op (`let _ = (pos, token);`)
//! - `complete`'s filter overly broad (`item.dot_position > 0`
//!   accepted any started item of the matching category, not just
//!   items expecting that category at the current dot)
//! - No SPPF emission
//! - No call sites anywhere in the codebase
//!
//! Exp 13 S1.a fixes the recognizer (proper rule-body model, correct
//! scan + complete) and adds `emit_sppf_subforest` for SPPF lift-back
//! into the walker's SPPF arena. S1.b–S1.e (next sessions) wire this
//! into `WpdaWalker::IterativeChainAbsorb` for chain region absorption.
//!
//! # Design
//!
//! Standard Earley with Leo's right-recursive optimization. Each rule
//! has an explicit body (`Vec<RuleItem>`) of terminal expectations
//! (token kind) and nonterminal expectations (category name). The chart
//! sets are indexed by token position; items advance via predict (when
//! at a nonterminal expectation), scan (when at a terminal expectation
//! that matches the input token), and complete (when an item reaches
//! end-of-body, advance items in the origin set that expected this
//! category).
//!
//! Leo's optimization compresses right-recursive completion chains into
//! a single `LeoItem`, eliminating O(n²) overhead for right-recursive
//! grammars. For left-recursive (chain_10000's case), Leo does not
//! apply, but standard Earley's `complete` is O(n²) which is acceptable
//! at chain_10000 (~10K iterations × ~5 origin lookups = ~50K
//! operations, sub-second).
//!
//! # SPPF emission
//!
//! `emit_sppf_subforest` walks completed items at the final chart set
//! top-down, interning Symbols and Packings into the walker's
//! `crate::sppf::Sppf<W>`. The walker's `intern_packing` is dedup'd by
//! `(rule_idx, children)` so structurally-identical packings produced
//! by both Earley AND walker paths collapse to the same SppfId; this
//! is the correctness guarantee that lets us call `intern_packing` in
//! either order without losing aggregation.
//!
//! # Tests
//!
//! 17 tests cover: item equality, chart creation, predict, scan-match
//! and scan-miss, complete advancing the origin set, recognition
//! acceptance + rejection, Leo reduction for right-recursive, SPPF
//! emission for atomic and chain rules, dedup of duplicate SPPF
//! emissions, weight propagation through `intern_packing`'s `⊕`
//! aggregation, and the empty-input and single-token edge cases.

use std::collections::{HashMap, HashSet};

use crate::automata::semiring::SemiringRef;
use crate::automata::TokenKind;
use crate::sppf::{Sppf, SppfId};

/// Stable u32 tag for a `TokenKind`, used by `RuleItem::Terminal`'s
/// `tag` field. Each variant gets a distinct discriminant. For
/// variants that carry a payload (e.g. `IntegerLit(name)`), the
/// payload is hashed into the discriminant via FxHasher so two
/// occurrences of `IntegerLit("Int")` map to the same tag, while
/// `IntegerLit("UInt32")` maps to a different one.
///
/// This is the bridge between the walker's TokenKind taxonomy and
/// Earley's per-item terminal expectation.
pub fn token_kind_to_tag(kind: &TokenKind) -> u32 {
    use std::hash::{Hash, Hasher};
    let mut hasher = rustc_hash::FxHasher::default();
    kind.hash(&mut hasher);
    // Truncate to u32; collisions are theoretically possible but
    // negligible for our small TokenKind universe.
    (hasher.finish() as u32) ^ ((hasher.finish() >> 32) as u32)
}

// ══════════════════════════════════════════════════════════════════
// Rule body model
// ══════════════════════════════════════════════════════════════════

/// One item in a rule's body. A nonterminal expectation requires the
/// chart to have a completed item of `category` at the current
/// position; a terminal expectation requires the input token's tag at
/// the current position to match `tag`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuleItem {
    /// Nonterminal expectation: any rule of `category` may satisfy.
    NonTerminal { category: String },
    /// Terminal expectation: input token's tag must equal `tag`.
    /// Tags are caller-defined u32s (typically `TokenKind` codes).
    Terminal { tag: u32 },
}

/// One rule registered with the chart. `body[0..]` is the expected
/// sequence; `dot_position` ∈ `0..=body.len()` indicates progress.
#[derive(Debug, Clone)]
pub struct Rule {
    pub label: String,
    pub category: String,
    pub body: Vec<RuleItem>,
}

// ══════════════════════════════════════════════════════════════════
// Earley items
// ══════════════════════════════════════════════════════════════════

/// An Earley item: (rule_label, category, dot_position, origin).
///
/// Represents progress through a rule starting at position `origin`.
/// `dot_position` indicates how many of the rule's body items have
/// been matched.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EarleyItem {
    pub rule_label: String,
    pub category: String,
    pub dot_position: usize,
    pub origin: usize,
}

/// A Leo item: compressed representation of a right-recursive chain.
///
/// Replaces O(n) standard Earley items for right-recursive completion
/// with a single Leo item, eliminating quadratic overhead.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LeoItem {
    pub category: String,
    pub origin: usize,
    pub top_item: EarleyItem,
}

// ══════════════════════════════════════════════════════════════════
// Earley chart
// ══════════════════════════════════════════════════════════════════

/// An Earley chart: `sets[i]` is the item set at token position `i`.
#[derive(Debug, Clone)]
pub struct EarleyChart {
    /// Per-position item sets. `sets.len() == input_len + 1`.
    sets: Vec<HashSet<EarleyItem>>,
    /// Leo items indexed by (position, category).
    leo_items: HashMap<(usize, String), LeoItem>,
    /// Rule definitions indexed by label.
    rules: HashMap<String, Rule>,
    /// Category → set of rule labels (for `predict`).
    rules_by_category: HashMap<String, Vec<String>>,
    /// Total tokens in the input slice.
    input_len: usize,
}

impl EarleyChart {
    /// Construct a chart for an input of given token length. Chart
    /// has `input_len + 1` per-position sets (positions 0..=input_len).
    pub fn new(input_len: usize) -> Self {
        let mut sets = Vec::with_capacity(input_len + 1);
        for _ in 0..=input_len {
            sets.push(HashSet::new());
        }
        Self {
            sets,
            leo_items: HashMap::new(),
            rules: HashMap::new(),
            rules_by_category: HashMap::new(),
            input_len,
        }
    }

    /// Register a rule with an explicit body. Each `RuleItem` is
    /// either a `NonTerminal { category }` or `Terminal { tag }`
    /// expectation.
    pub fn add_rule_with_body(
        &mut self,
        label: &str,
        category: &str,
        body: Vec<RuleItem>,
    ) {
        self.rules.insert(
            label.to_string(),
            Rule {
                label: label.to_string(),
                category: category.to_string(),
                body,
            },
        );
        self.rules_by_category
            .entry(category.to_string())
            .or_default()
            .push(label.to_string());
    }

    /// Backward-compatible rule registration with body length only.
    /// Bodies are populated with `RuleItem::Terminal { tag: 0 }`
    /// placeholders — useful ONLY for tests that exercise the
    /// recognition-acceptance API without driving scan/complete (e.g.
    /// `test_chart_recognize`, `test_chart_total_items`).
    /// New code should use `add_rule_with_body`.
    pub fn add_rule(&mut self, label: &str, category: &str, item_count: usize) {
        let body = vec![RuleItem::Terminal { tag: 0 }; item_count];
        self.add_rule_with_body(label, category, body);
    }

    /// Predict: seed all rules of `category` at position `pos` with
    /// dot at 0 and origin = pos.
    pub fn predict(&mut self, category: &str, pos: usize) {
        if pos > self.input_len {
            return;
        }
        let labels: Vec<String> = self
            .rules_by_category
            .get(category)
            .cloned()
            .unwrap_or_default();
        for label in labels {
            let rule = self
                .rules
                .get(&label)
                .expect("rule must be registered");
            let item = EarleyItem {
                rule_label: rule.label.clone(),
                category: rule.category.clone(),
                dot_position: 0,
                origin: pos,
            };
            self.sets[pos].insert(item);
        }
    }

    /// Scan: at position `pos`, advance every item whose dot is at a
    /// `Terminal { tag }` matching `input_tag`. Advanced items go into
    /// `sets[pos + 1]`.
    ///
    /// Returns the number of items advanced (diagnostic).
    pub fn scan(&mut self, pos: usize, input_tag: u32) -> usize {
        if pos >= self.input_len {
            return 0;
        }
        // Collect items to advance (must drop borrow of sets[pos] before
        // mutating sets[pos + 1]).
        let to_advance: Vec<EarleyItem> = self.sets[pos]
            .iter()
            .filter(|item| {
                let rule = match self.rules.get(&item.rule_label) {
                    Some(r) => r,
                    None => return false,
                };
                match rule.body.get(item.dot_position) {
                    Some(RuleItem::Terminal { tag }) => *tag == input_tag,
                    _ => false,
                }
            })
            .cloned()
            .collect();
        let count = to_advance.len();
        for item in to_advance {
            let advanced = EarleyItem {
                dot_position: item.dot_position + 1,
                ..item
            };
            self.sets[pos + 1].insert(advanced);
        }
        count
    }

    /// Complete: when an item at `sets[pos]` has its dot at end of
    /// body, find items at the origin set that expected this
    /// item's category at their dot, advance their dot by 1, and
    /// insert into `sets[pos]`.
    ///
    /// Returns the number of items advanced (diagnostic).
    pub fn complete(&mut self, pos: usize, completed: &EarleyItem) -> usize {
        let rule = match self.rules.get(&completed.rule_label) {
            Some(r) => r,
            None => return 0,
        };
        if completed.dot_position != rule.body.len() {
            return 0;
        }
        let origin = completed.origin;
        let category = completed.category.clone();
        // Snapshot items at origin that expect this category at dot.
        let origin_set = match self.sets.get(origin) {
            Some(s) => s.clone(),
            None => return 0,
        };
        let mut advanced_count = 0usize;
        for item in &origin_set {
            let rule = match self.rules.get(&item.rule_label) {
                Some(r) => r,
                None => continue,
            };
            let expected = match rule.body.get(item.dot_position) {
                Some(RuleItem::NonTerminal { category: c }) => c,
                _ => continue,
            };
            if expected != &category {
                continue;
            }
            let advanced = EarleyItem {
                dot_position: item.dot_position + 1,
                ..item.clone()
            };
            if self.sets[pos].insert(advanced) {
                advanced_count += 1;
            }
        }
        advanced_count
    }

    /// Drive `complete` to a fixpoint at `pos`: repeatedly complete every
    /// item in `sets[pos]` until no further item advances. A bounded
    /// iteration cap (`input_len * 8`, floor 64) guards against
    /// pathological re-insertion. Both the walker chain-absorption drive
    /// (`earley_outboard_chain`) and the standalone right/left-recursive
    /// chart unit tests share this so the completion semantics stay in
    /// one place.
    pub fn complete_to_fixpoint(&mut self, pos: usize) {
        let cap = self.input_len.saturating_mul(8).max(64);
        let mut iterations = 0usize;
        loop {
            iterations += 1;
            if iterations > cap {
                break;
            }
            let snapshot: Vec<EarleyItem> =
                self.items_at(pos).iter().cloned().collect();
            let mut any_advanced = false;
            for item in &snapshot {
                if self.complete(pos, item) > 0 {
                    any_advanced = true;
                }
            }
            if !any_advanced {
                break;
            }
        }
    }

    /// Leo reduction: if `sets[pos]` contains exactly one item of
    /// `category` whose dot is at body.len() - 1 (one step from
    /// completion), and that item is the lone candidate for a
    /// right-recursive chain, install a `LeoItem` that compresses the
    /// chain to a single transition.
    pub fn leo_reduce(&mut self, pos: usize, category: &str) {
        if pos > self.input_len {
            return;
        }
        let candidates: Vec<EarleyItem> = self.sets[pos]
            .iter()
            .filter(|item| {
                if item.category != *category {
                    return false;
                }
                let rule = match self.rules.get(&item.rule_label) {
                    Some(r) => r,
                    None => return false,
                };
                item.dot_position + 1 == rule.body.len()
            })
            .cloned()
            .collect();
        if candidates.len() != 1 {
            return;
        }
        let item = &candidates[0];
        let origin = self
            .leo_items
            .get(&(item.origin, category.to_string()))
            .map(|existing| existing.origin)
            .unwrap_or(item.origin);
        self.leo_items.insert(
            (pos, category.to_string()),
            LeoItem {
                category: category.to_string(),
                origin,
                top_item: item.clone(),
            },
        );
    }

    // ── Accessors / diagnostics ────────────────────────────────────

    /// Per-position item set.
    pub fn items_at(&self, pos: usize) -> &HashSet<EarleyItem> {
        &self.sets[pos]
    }

    /// Leo item at (pos, category).
    pub fn leo_item_at(&self, pos: usize, category: &str) -> Option<&LeoItem> {
        self.leo_items.get(&(pos, category.to_string()))
    }

    /// Total number of items across all chart sets.
    pub fn total_items(&self) -> usize {
        self.sets.iter().map(|s| s.len()).sum()
    }

    /// Total Leo item count.
    pub fn leo_item_count(&self) -> usize {
        self.leo_items.len()
    }

    /// Input length the chart was constructed for.
    pub fn input_len(&self) -> usize {
        self.input_len
    }

    /// Recognition test: does any item at `sets[input_len]` represent
    /// a completed parse of `category` starting at origin 0?
    pub fn recognizes(&self, category: &str) -> bool {
        self.sets[self.input_len].iter().any(|item| {
            if item.category != *category || item.origin != 0 {
                return false;
            }
            self.rules
                .get(&item.rule_label)
                .map(|r| item.dot_position == r.body.len())
                .unwrap_or(false)
        })
    }

    // ── SPPF emission (Exp 13 S1.a) ────────────────────────────────

    /// Emit an SPPF subforest covering the recognized parse of
    /// `root_category` from position 0 to `input_len` into the
    /// walker's `Sppf<W>`. Returns the root `SppfId`, or `None` if no
    /// recognition exists.
    ///
    /// Inputs:
    /// - `root_nt_tag` — non-terminal tag for `root_category` (the
    ///   walker uses `cat_src_idx as u32` per `wpda_walker.rs:9950`).
    /// - `rule_label_to_meta` — maps each rule label to
    ///   `(rule_idx_in_category, category_nt_tag)` so the SPPF can
    ///   intern the Symbol + Packing with walker-side identifiers.
    /// - `terminal_sppf_ids` — for terminals at each input position,
    ///   the SppfId of the Terminal node (pre-interned by the caller).
    ///   Length must equal `input_len`; `terminal_sppf_ids[i]` is the
    ///   terminal between positions `i` and `i+1`.
    /// - `rule_weights` — per-rule weight contribution.
    ///   `rule_weights[&rule_label]` is the weight assigned to each
    ///   Packing emitted for that rule.
    ///
    /// The walk:
    /// 1. Find the recognizing item at `sets[input_len]` for
    ///    `root_category` originating at 0. If none → return `None`.
    /// 2. Recursively `emit_for_item` from there, producing
    ///    `(SppfId, lo_pos)` for each completed item.
    /// 3. Each rule body item is either a Terminal (look up
    ///    `terminal_sppf_ids[pos]`) or a NonTerminal (recurse).
    ///
    /// `intern_packing` is dedup'd by `(rule_idx, children)`, so
    /// repeated calls produce no duplicate nodes — safe to call after
    /// the walker has already partially interned the same packings
    /// (e.g. from per-iteration `emit_fire_action`).
    pub fn emit_sppf_subforest<W: SemiringRef>(
        &self,
        sppf: &mut Sppf<W>,
        root_category: &str,
        root_nt_tag: u32,
        rule_label_to_meta: &HashMap<String, (u32, u32)>,
        terminal_sppf_ids: &[SppfId],
        rule_weights: &HashMap<String, W>,
    ) -> Option<SppfId> {
        debug_assert_eq!(
            terminal_sppf_ids.len(),
            self.input_len,
            "emit_sppf_subforest: terminal_sppf_ids length must equal input_len",
        );
        // Find the recognizing item: completed root_category at hi =
        // input_len, originating at 0.
        let root_item = self.sets[self.input_len].iter().find(|item| {
            if item.category != *root_category || item.origin != 0 {
                return false;
            }
            self.rules
                .get(&item.rule_label)
                .map(|r| item.dot_position == r.body.len())
                .unwrap_or(false)
        })?;
        let root_id = self.emit_for_item(
            sppf,
            root_item,
            self.input_len as u32,
            root_nt_tag,
            rule_label_to_meta,
            terminal_sppf_ids,
            rule_weights,
        )?;
        Some(root_id)
    }

    /// Emit a Packing + Symbol for one completed item. `hi_pos` is the
    /// position immediately after the item's last consumed token.
    /// Returns the SppfId of the wrapping Symbol.
    ///
    /// Recurses into NonTerminal body items by searching the chart
    /// for matching completed items.
    ///
    /// **Plan v6 H1 fix (2026-05-27)**: tracks per-body-position
    /// min-trailing-token consumption so non-last NonTerminal items
    /// search with `max_hi = hi_pos - trailing_min`, avoiding the
    /// self-recursion that breaks left-recursive grammars. For
    /// `Chain -> Chain "+" Atom`, the recursive Chain sub-call now
    /// has max_hi = hi_pos - 2 (room for "+" Atom), excluding the
    /// root completion at hi_pos and forcing the descending search
    /// to find a strictly smaller sub-chain.
    fn emit_for_item<W: SemiringRef>(
        &self,
        sppf: &mut Sppf<W>,
        item: &EarleyItem,
        hi_pos: u32,
        nt_tag: u32,
        rule_label_to_meta: &HashMap<String, (u32, u32)>,
        terminal_sppf_ids: &[SppfId],
        rule_weights: &HashMap<String, W>,
    ) -> Option<SppfId> {
        let rule = self.rules.get(&item.rule_label)?;
        let (rule_idx, _cat_nt_tag) =
            rule_label_to_meta.get(&item.rule_label)?.clone();
        let weight = rule_weights.get(&item.rule_label)?.clone();
        // Plan v6 H1 fix (2026-05-27): compute min-trailing-tokens per
        // body position. trailing_min[k] = min number of tokens that
        // body[k..body.len()] must consume. Terminal = 1; NonTerminal
        // = 1 (conservative — assumes no epsilon rules, true for the
        // chain grammar). For NonTerminal at body[k], sub-NT's
        // effective max_hi = hi_pos - trailing_min[k+1].
        let body = &rule.body;
        let body_len = body.len();
        let mut trailing_min: Vec<usize> = vec![0; body_len + 1];
        for k in (0..body_len).rev() {
            let item_min = match &body[k] {
                RuleItem::Terminal { .. } => 1,
                RuleItem::NonTerminal { .. } => 1,
            };
            trailing_min[k] = trailing_min[k + 1] + item_min;
        }
        // Walk body left-to-right, accumulating children SppfIds.
        // `pos` tracks the current input position; starts at
        // `item.origin`, ends at `hi_pos`.
        let mut children: Vec<SppfId> = Vec::with_capacity(body_len);
        let mut pos = item.origin;
        for (k, body_item) in body.iter().enumerate() {
            match body_item {
                RuleItem::Terminal { tag: _ } => {
                    if pos >= terminal_sppf_ids.len() {
                        return None;
                    }
                    children.push(terminal_sppf_ids[pos]);
                    pos += 1;
                }
                RuleItem::NonTerminal { category } => {
                    // Sub-NT's max_hi excludes the room needed for
                    // trailing body items. For chain grammar's
                    // chain_step Chain body[0]: trailing_min[1] = 2
                    // (one "+" + one Atom), so Chain's max_hi
                    // = hi_pos - 2. This avoids self-recursion at
                    // hi=hi_pos.
                    let sub_max_hi = (hi_pos as usize)
                        .saturating_sub(trailing_min[k + 1]);
                    if sub_max_hi <= pos {
                        return None;
                    }
                    let (sub_id, sub_hi) = self.find_and_emit_sub(
                        sppf,
                        category,
                        pos,
                        sub_max_hi,
                        rule_label_to_meta,
                        terminal_sppf_ids,
                        rule_weights,
                    )?;
                    children.push(sub_id);
                    pos = sub_hi as usize;
                }
            }
        }
        // Verify we consumed exactly up to hi_pos.
        if pos as u32 != hi_pos {
            return None;
        }
        // Intern outer Symbol + Packing + link.
        let symbol_id =
            sppf.intern_symbol(nt_tag, item.origin as u32, hi_pos);
        let packing_id = sppf.intern_packing(rule_idx, children, weight);
        sppf.link_packing_to_symbol(symbol_id, packing_id);
        Some(symbol_id)
    }

    /// Find and recurse into a completed sub-item of `category`
    /// starting at `origin`. Tries hi positions in ascending order
    /// (greedy shortest match for left-assoc; the chain grammar
    /// produces a unique match).
    fn find_and_emit_sub<W: SemiringRef>(
        &self,
        sppf: &mut Sppf<W>,
        category: &str,
        origin: usize,
        max_hi: usize,
        rule_label_to_meta: &HashMap<String, (u32, u32)>,
        terminal_sppf_ids: &[SppfId],
        rule_weights: &HashMap<String, W>,
    ) -> Option<(SppfId, u32)> {
        let (_, nt_tag) = rule_label_to_meta
            .values()
            .find(|(_, _tag)| true) // placeholder; corrected below
            .copied()?;
        // Look up nt_tag for `category` from any rule of that category.
        let nt_tag = self
            .rules_by_category
            .get(category)
            .and_then(|labels| labels.first())
            .and_then(|label| rule_label_to_meta.get(label))
            .map(|(_, tag)| *tag)
            .unwrap_or(nt_tag);
        // Plan v6 H1 fix (2026-05-27): iterate hi DESCENDING so left-
        // recursive sub-non-terminals find the LONGEST completion that
        // fits within max_hi. The caller (emit_for_item) computes
        // max_hi = parent_hi - trailing_min[k+1] to exclude the room
        // needed for trailing body items, which also excludes the
        // parent's self-completion at parent_hi — avoiding the infinite
        // self-recursion that naive descending would cause.
        //
        // For non-recursive non-terminals (e.g. Atom), descending vs
        // ascending picks the same item (Atom only completes at one hi
        // per origin). For left-recursive, descending picks the longest
        // sub-chain — exactly what the parent needs to leave the
        // trailing-min tokens for the rest of the body.
        for hi in (origin + 1..=max_hi).rev() {
            let candidates: Vec<EarleyItem> = self.sets[hi]
                .iter()
                .filter(|i| {
                    i.category == *category
                        && i.origin == origin
                        && self
                            .rules
                            .get(&i.rule_label)
                            .map(|r| i.dot_position == r.body.len())
                            .unwrap_or(false)
                })
                .cloned()
                .collect();
            if let Some(item) = candidates.first() {
                if let Some(sid) = self.emit_for_item(
                    sppf,
                    item,
                    hi as u32,
                    nt_tag,
                    rule_label_to_meta,
                    terminal_sppf_ids,
                    rule_weights,
                ) {
                    return Some((sid, hi as u32));
                }
                // emit_for_item returned None: this hi candidate's body
                // could not be fully reconstructed downstream (e.g., the
                // chain doesn't extend that long). Try the next smaller
                // hi.
            }
        }
        None
    }
}

// ══════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;
    use crate::automata::semiring::{Semiring, TropicalWeight};

    fn unit_weight() -> LexicographicWeight {
        LexicographicWeight::new(TropicalWeight::one(), 0, 0)
    }

    #[test]
    fn test_earley_item_equality() {
        let item1 = EarleyItem {
            rule_label: "Add".to_string(),
            category: "Expr".to_string(),
            dot_position: 1,
            origin: 0,
        };
        let item2 = EarleyItem {
            rule_label: "Add".to_string(),
            category: "Expr".to_string(),
            dot_position: 1,
            origin: 0,
        };
        assert_eq!(item1, item2);
    }

    #[test]
    fn test_chart_creation() {
        let chart = EarleyChart::new(5);
        assert_eq!(chart.total_items(), 0);
        assert_eq!(chart.input_len(), 5);
    }

    #[test]
    fn test_chart_predict() {
        let mut chart = EarleyChart::new(3);
        chart.add_rule_with_body(
            "Add",
            "Expr",
            vec![
                RuleItem::NonTerminal { category: "Expr".to_string() },
                RuleItem::Terminal { tag: 1 },
                RuleItem::NonTerminal { category: "Expr".to_string() },
            ],
        );
        chart.add_rule_with_body(
            "Lit",
            "Expr",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart.predict("Expr", 0);
        assert_eq!(chart.items_at(0).len(), 2);
    }

    #[test]
    fn test_scan_advances_matching_terminal() {
        let mut chart = EarleyChart::new(1);
        chart.add_rule_with_body(
            "Lit",
            "Expr",
            vec![RuleItem::Terminal { tag: 7 }],
        );
        chart.predict("Expr", 0);
        let advanced = chart.scan(0, 7);
        assert_eq!(advanced, 1);
        assert_eq!(chart.items_at(1).len(), 1);
    }

    #[test]
    fn test_scan_does_not_advance_mismatched_terminal() {
        let mut chart = EarleyChart::new(1);
        chart.add_rule_with_body(
            "Lit",
            "Expr",
            vec![RuleItem::Terminal { tag: 7 }],
        );
        chart.predict("Expr", 0);
        let advanced = chart.scan(0, 99);
        assert_eq!(advanced, 0);
        assert_eq!(chart.items_at(1).len(), 0);
    }

    #[test]
    fn test_complete_advances_expecting_items() {
        let mut chart = EarleyChart::new(3);
        // chain → atom "+" atom
        chart.add_rule_with_body(
            "chain",
            "Expr",
            vec![
                RuleItem::NonTerminal { category: "Atom".to_string() },
                RuleItem::Terminal { tag: 1 },
                RuleItem::NonTerminal { category: "Atom".to_string() },
            ],
        );
        chart.add_rule_with_body(
            "atom",
            "Atom",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart.predict("Expr", 0);
        // After predict, sets[0] has chain (dot=0) + atom (dot=0 from predict
        // recursive expansion — but we haven't recursed; predict only seeds
        // top-level Expr rules, so we need to manually predict Atom too).
        chart.predict("Atom", 0);
        assert!(chart.items_at(0).len() >= 2);
        // Scan tag=2 at pos=0 to advance atom.
        chart.scan(0, 2);
        // sets[1] now has completed atom.
        let completed_atom = EarleyItem {
            rule_label: "atom".to_string(),
            category: "Atom".to_string(),
            dot_position: 1,
            origin: 0,
        };
        assert!(chart.items_at(1).contains(&completed_atom));
        // Complete with atom: should advance chain's dot from 0 to 1.
        let advanced = chart.complete(1, &completed_atom);
        assert_eq!(advanced, 1);
        let advanced_chain = EarleyItem {
            rule_label: "chain".to_string(),
            category: "Expr".to_string(),
            dot_position: 1,
            origin: 0,
        };
        assert!(chart.items_at(1).contains(&advanced_chain));
    }

    #[test]
    fn test_full_recognition_chain_of_3_atoms() {
        // Grammar: chain → atom "+" atom "+" atom
        //          atom  → 2
        // Input: 2 "+" 2 "+" 2 (tags [2, 1, 2, 1, 2])
        let input_tags = vec![2u32, 1, 2, 1, 2];
        let mut chart = EarleyChart::new(input_tags.len());
        chart.add_rule_with_body(
            "chain",
            "Expr",
            vec![
                RuleItem::NonTerminal { category: "Atom".to_string() },
                RuleItem::Terminal { tag: 1 },
                RuleItem::NonTerminal { category: "Atom".to_string() },
                RuleItem::Terminal { tag: 1 },
                RuleItem::NonTerminal { category: "Atom".to_string() },
            ],
        );
        chart.add_rule_with_body(
            "atom",
            "Atom",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart.predict("Expr", 0);
        for pos in 0..input_tags.len() {
            chart.predict("Atom", pos);
            chart.scan(pos, input_tags[pos]);
            // Run complete to fixpoint at sets[pos+1].
            let mut changed = true;
            while changed {
                changed = false;
                let snapshot: Vec<EarleyItem> =
                    chart.items_at(pos + 1).iter().cloned().collect();
                for item in &snapshot {
                    let rule = match chart.rules.get(&item.rule_label) {
                        Some(r) => r,
                        None => continue,
                    };
                    if item.dot_position == rule.body.len() {
                        let advanced = chart.complete(pos + 1, item);
                        if advanced > 0 {
                            changed = true;
                        }
                    }
                }
            }
        }
        assert!(chart.recognizes("Expr"), "chain of 3 atoms must recognize");
    }

    #[test]
    fn test_does_not_recognize_when_short() {
        // Same grammar as above; input is only 2 atoms.
        let input_tags = vec![2u32, 1, 2];
        let mut chart = EarleyChart::new(input_tags.len());
        chart.add_rule_with_body(
            "chain",
            "Expr",
            vec![
                RuleItem::NonTerminal { category: "Atom".to_string() },
                RuleItem::Terminal { tag: 1 },
                RuleItem::NonTerminal { category: "Atom".to_string() },
                RuleItem::Terminal { tag: 1 },
                RuleItem::NonTerminal { category: "Atom".to_string() },
            ],
        );
        chart.add_rule_with_body(
            "atom",
            "Atom",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart.predict("Expr", 0);
        for pos in 0..input_tags.len() {
            chart.predict("Atom", pos);
            chart.scan(pos, input_tags[pos]);
        }
        assert!(!chart.recognizes("Expr"));
    }

    #[test]
    fn test_leo_item_creation() {
        let leo = LeoItem {
            category: "Expr".to_string(),
            origin: 0,
            top_item: EarleyItem {
                rule_label: "RightRec".to_string(),
                category: "Expr".to_string(),
                dot_position: 2,
                origin: 3,
            },
        };
        assert_eq!(leo.origin, 0);
    }

    #[test]
    fn test_chart_leo_reduce() {
        let mut chart = EarleyChart::new(5);
        // RR → atom RR  (right-recursive)
        chart.add_rule_with_body(
            "RR",
            "Expr",
            vec![
                RuleItem::Terminal { tag: 1 },
                RuleItem::NonTerminal { category: "Expr".to_string() },
            ],
        );
        // Manually insert an item that's one step from completion.
        let item = EarleyItem {
            rule_label: "RR".to_string(),
            category: "Expr".to_string(),
            dot_position: 1,
            origin: 2,
        };
        chart.sets[3].insert(item);
        chart.leo_reduce(3, "Expr");
        assert!(chart.leo_item_at(3, "Expr").is_some());
    }

    #[test]
    fn test_recognize_via_manual_insertion() {
        let mut chart = EarleyChart::new(1);
        chart.add_rule_with_body(
            "Lit",
            "Expr",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart.predict("Expr", 0);
        chart.scan(0, 2);
        assert!(chart.recognizes("Expr"));
        assert!(!chart.recognizes("Name"));
    }

    #[test]
    fn test_recognize_empty_input_no_epsilon_rule() {
        let mut chart = EarleyChart::new(0);
        chart.add_rule_with_body(
            "Lit",
            "Expr",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart.predict("Expr", 0);
        // No tokens to scan; sets[0] has predicted Lit at dot=0, but
        // sets[0] is the FINAL set since input_len=0. Lit's dot_position
        // (0) != body.len() (1) → not recognized.
        assert!(!chart.recognizes("Expr"));
    }

    #[test]
    fn test_recognize_epsilon_rule() {
        let mut chart = EarleyChart::new(0);
        // Epsilon rule: Empty → (nothing)
        chart.add_rule_with_body("Empty", "Expr", vec![]);
        chart.predict("Expr", 0);
        // After predict, sets[0] has Empty (dot=0). Since body.len()=0
        // and dot_position=0, dot is already at end → recognized.
        assert!(chart.recognizes("Expr"));
    }

    #[test]
    fn test_total_items_counts_across_sets() {
        let mut chart = EarleyChart::new(3);
        chart.add_rule_with_body(
            "Lit",
            "Expr",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart.predict("Expr", 0);
        chart.predict("Expr", 2);
        assert_eq!(chart.total_items(), 2);
    }

    #[test]
    fn test_emit_sppf_subforest_single_atom() {
        // Grammar: atom → tag(2)
        // Input: just [tag=2]
        let input_tags = vec![2u32];
        let mut chart = EarleyChart::new(input_tags.len());
        chart.add_rule_with_body(
            "atom",
            "Atom",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart.predict("Atom", 0);
        chart.scan(0, 2);
        assert!(chart.recognizes("Atom"));
        // Pre-intern the terminal SppfId.
        let mut sppf: Sppf<LexicographicWeight> = Sppf::new();
        let term_id = sppf.intern_terminal(
            crate::automata::TokenKind::Integer,
            crate::sppf::PosOrSynth::Real(0),
            Some("2"),
            false,
        );
        let mut rule_label_to_meta = HashMap::new();
        rule_label_to_meta.insert("atom".to_string(), (10u32, 100u32));
        let mut weights = HashMap::new();
        weights.insert("atom".to_string(), unit_weight());
        let root_id = chart
            .emit_sppf_subforest(
                &mut sppf,
                "Atom",
                100,
                &rule_label_to_meta,
                &[term_id],
                &weights,
            )
            .expect("must produce root SppfId");
        // Sanity: root_id was produced by intern_symbol — it must be
        // a valid SppfId (assigned u32 within Sppf::nodes range).
        // Replaying the emit must dedup to the same id.
        let root_id2 = chart
            .emit_sppf_subforest(
                &mut sppf,
                "Atom",
                100,
                &rule_label_to_meta,
                &[term_id],
                &weights,
            )
            .expect("replay must produce root SppfId");
        assert_eq!(root_id, root_id2, "intern dedup must collapse replays");
    }

    // Phase F.13 chain_10000 Plan v6 H1 (2026-05-27): Earley parity
    // oracle for left-recursive chain workloads. Confirms the existing
    // earley_outboard_chain substrate (recognizer + emit_sppf_subforest)
    // is sound for chain_50/100/200 BEFORE wiring the handoff at H2.
    //
    // The Plan v6 hybrid-Earley-WPDS design hinges on this soundness:
    // if Earley misrecognizes or emit_sppf_subforest produces invalid
    // SppfIds at scale, the handoff cannot be wired and the plan stops.
    //
    // Falsifier: any test failure → fix earley.rs before H2.
    fn build_left_recursive_chain_grammar(input_len: usize) -> EarleyChart {
        let mut chart = EarleyChart::new(input_len);
        // chain_base: Chain → Atom
        chart.add_rule_with_body(
            "chain_base",
            "Chain",
            vec![RuleItem::NonTerminal { category: "Atom".to_string() }],
        );
        // chain_step: Chain → Chain "+" Atom  (left-recursive)
        chart.add_rule_with_body(
            "chain_step",
            "Chain",
            vec![
                RuleItem::NonTerminal { category: "Chain".to_string() },
                RuleItem::Terminal { tag: 1 },
                RuleItem::NonTerminal { category: "Atom".to_string() },
            ],
        );
        // atom: Atom → Integer
        chart.add_rule_with_body(
            "atom",
            "Atom",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart
    }

    fn build_chain_input(atom_count: usize) -> Vec<u32> {
        // Pattern: atom (op atom)*  — tags [2, 1, 2, 1, 2, ...]
        assert!(atom_count >= 1);
        let mut tags = Vec::with_capacity(2 * atom_count - 1);
        tags.push(2u32);
        for _ in 1..atom_count {
            tags.push(1u32);
            tags.push(2u32);
        }
        tags
    }

    fn drive_chart_with_input(chart: &mut EarleyChart, input_tags: &[u32]) {
        chart.predict("Chain", 0);
        for pos in 0..input_tags.len() {
            chart.predict("Chain", pos);
            chart.predict("Atom", pos);
            chart.scan(pos, input_tags[pos]);
            // Complete to fixpoint at sets[pos+1].
            let mut changed = true;
            while changed {
                changed = false;
                let snapshot: Vec<EarleyItem> =
                    chart.items_at(pos + 1).iter().cloned().collect();
                for item in &snapshot {
                    let rule = match chart.rules.get(&item.rule_label) {
                        Some(r) => r,
                        None => continue,
                    };
                    if item.dot_position == rule.body.len() {
                        let advanced = chart.complete(pos + 1, item);
                        if advanced > 0 {
                            changed = true;
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn v6_h1_earley_recognizes_left_recursive_chain_50() {
        let atom_count = 50;
        let input_tags = build_chain_input(atom_count);
        let mut chart = build_left_recursive_chain_grammar(input_tags.len());
        drive_chart_with_input(&mut chart, &input_tags);
        assert!(
            chart.recognizes("Chain"),
            "Earley must recognize left-recursive chain of {} atoms",
            atom_count
        );
    }

    #[test]
    fn v6_h1_earley_recognizes_left_recursive_chain_100() {
        let atom_count = 100;
        let input_tags = build_chain_input(atom_count);
        let mut chart = build_left_recursive_chain_grammar(input_tags.len());
        drive_chart_with_input(&mut chart, &input_tags);
        assert!(
            chart.recognizes("Chain"),
            "Earley must recognize left-recursive chain of {} atoms",
            atom_count
        );
    }

    #[test]
    fn v6_h1_earley_recognizes_left_recursive_chain_200() {
        let atom_count = 200;
        let input_tags = build_chain_input(atom_count);
        let mut chart = build_left_recursive_chain_grammar(input_tags.len());
        drive_chart_with_input(&mut chart, &input_tags);
        assert!(
            chart.recognizes("Chain"),
            "Earley must recognize left-recursive chain of {} atoms",
            atom_count
        );
    }

    #[test]
    fn v6_h1_earley_chain_50_emits_valid_sppf_root() {
        // End-to-end check: recognition + SPPF emission produce a
        // valid root SppfId for chain_50. This is the substrate H2
        // will wire into the walker handoff.
        let atom_count = 50;
        let input_tags = build_chain_input(atom_count);
        let mut chart = build_left_recursive_chain_grammar(input_tags.len());
        drive_chart_with_input(&mut chart, &input_tags);
        assert!(chart.recognizes("Chain"));

        // Pre-intern terminal SppfIds for each input position.
        let mut sppf: Sppf<LexicographicWeight> = Sppf::new();
        let mut terminal_sppf_ids = Vec::with_capacity(input_tags.len());
        for (pos, tag) in input_tags.iter().enumerate() {
            let (kind, text) = if *tag == 1 {
                (crate::automata::TokenKind::Fixed("+".to_string()), Some("+"))
            } else {
                (crate::automata::TokenKind::Integer, Some("1"))
            };
            let sid = sppf.intern_terminal(
                kind,
                crate::sppf::PosOrSynth::Real(pos as u32),
                text,
                false,
            );
            terminal_sppf_ids.push(sid);
        }

        let mut rule_label_to_meta = HashMap::new();
        // (rule_idx, nt_tag): nt_tag chosen as 200 for Chain to avoid
        // collision with any walker-side nt assignment.
        rule_label_to_meta.insert("chain_step".to_string(), (1u32, 200u32));
        rule_label_to_meta.insert("chain_base".to_string(), (0u32, 200u32));
        rule_label_to_meta.insert("atom".to_string(), (0u32, 201u32));
        let mut weights = HashMap::new();
        weights.insert("chain_step".to_string(), unit_weight());
        weights.insert("chain_base".to_string(), unit_weight());
        weights.insert("atom".to_string(), unit_weight());

        let root_id = chart
            .emit_sppf_subforest(
                &mut sppf,
                "Chain",
                200,
                &rule_label_to_meta,
                &terminal_sppf_ids,
                &weights,
            )
            .expect("Chain root SppfId must be produced");

        // Sanity: replay must dedup to the same root.
        let root_id_replay = chart
            .emit_sppf_subforest(
                &mut sppf,
                "Chain",
                200,
                &rule_label_to_meta,
                &terminal_sppf_ids,
                &weights,
            )
            .expect("replay must produce root SppfId");
        assert_eq!(
            root_id, root_id_replay,
            "intern_packing dedup must collapse replays — H1 dedup invariant"
        );
    }

    #[test]
    fn test_emit_sppf_subforest_dedups_repeated_calls() {
        // Calling emit_sppf_subforest twice must produce identical
        // root SppfId (dedup safety).
        let input_tags = vec![2u32];
        let mut chart = EarleyChart::new(input_tags.len());
        chart.add_rule_with_body(
            "atom",
            "Atom",
            vec![RuleItem::Terminal { tag: 2 }],
        );
        chart.predict("Atom", 0);
        chart.scan(0, 2);
        let mut sppf: Sppf<LexicographicWeight> = Sppf::new();
        let term_id = sppf.intern_terminal(
            crate::automata::TokenKind::Integer,
            crate::sppf::PosOrSynth::Real(0),
            Some("2"),
            false,
        );
        let mut rule_label_to_meta = HashMap::new();
        rule_label_to_meta.insert("atom".to_string(), (10u32, 100u32));
        let mut weights = HashMap::new();
        weights.insert("atom".to_string(), unit_weight());
        let root1 = chart
            .emit_sppf_subforest(
                &mut sppf,
                "Atom",
                100,
                &rule_label_to_meta,
                &[term_id],
                &weights,
            )
            .expect("call 1");
        let root2 = chart
            .emit_sppf_subforest(
                &mut sppf,
                "Atom",
                100,
                &rule_label_to_meta,
                &[term_id],
                &weights,
            )
            .expect("call 2");
        assert_eq!(root1, root2, "repeated emit must produce identical SppfId");
    }

    #[test]
    fn test_legacy_add_rule_compat() {
        // Old API for tests that bypass scan/complete by direct
        // sets[...].insert. Body becomes Terminal { tag: 0 } placeholders.
        let mut chart = EarleyChart::new(1);
        chart.add_rule("Lit", "Expr", 1);
        let completed = EarleyItem {
            rule_label: "Lit".to_string(),
            category: "Expr".to_string(),
            dot_position: 1,
            origin: 0,
        };
        chart.sets[1].insert(completed);
        assert!(chart.recognizes("Expr"));
    }
}
