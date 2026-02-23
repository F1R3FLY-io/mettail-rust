//! FIRST/FOLLOW set computation, decision automata, and cross-category analysis.
//!
//! Precomputes FIRST and FOLLOW sets and generates decision automata for
//! deterministic parse dispatch — eliminating sequential trial-and-error at
//! parse decision points.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{BTreeMap, BTreeSet};

use crate::automata::codegen::terminal_to_variant_name;

/// A FIRST set: the set of token kinds that can begin a particular alternative.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FirstSet {
    /// Set of token variant names (e.g., "Plus", "Ident", "Integer").
    pub tokens: BTreeSet<String>,
    /// Whether this category can derive the empty string (epsilon).
    /// A category is nullable if it has an optional group at top level,
    /// a zero-minimum collection, a cast to a nullable category, or
    /// all items in some rule are nullable.
    pub nullable: bool,
}

impl FirstSet {
    pub fn new() -> Self {
        FirstSet {
            tokens: BTreeSet::new(),
            nullable: false,
        }
    }

    pub fn insert(&mut self, token: &str) {
        self.tokens.insert(token.to_string());
    }

    pub fn contains(&self, token: &str) -> bool {
        self.tokens.contains(token)
    }

    pub fn union(&mut self, other: &FirstSet) {
        self.tokens.extend(other.tokens.iter().cloned());
        self.nullable = self.nullable || other.nullable;
    }

    pub fn intersection(&self, other: &FirstSet) -> FirstSet {
        FirstSet {
            tokens: self.tokens.intersection(&other.tokens).cloned().collect(),
            nullable: self.nullable && other.nullable,
        }
    }

    pub fn difference(&self, other: &FirstSet) -> FirstSet {
        FirstSet {
            tokens: self.tokens.difference(&other.tokens).cloned().collect(),
            nullable: self.nullable && !other.nullable,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    pub fn len(&self) -> usize {
        self.tokens.len()
    }
}

impl Default for FirstSet {
    fn default() -> Self {
        Self::new()
    }
}

/// How to dispatch when a token is seen at a parse decision point.
#[derive(Debug, Clone)]
pub enum DispatchAction {
    /// Unambiguous: directly call this parse function.
    Direct {
        /// Rule label (constructor name).
        rule_label: String,
        /// Parse function to call.
        parse_fn: String,
    },
    /// Ambiguous: need lookahead decision automaton.
    Lookahead {
        /// The ambiguous alternatives, each with their next-token discriminators.
        alternatives: Vec<LookaheadAlternative>,
        /// Fallback rule if no lookahead matches (usually variable).
        fallback: Option<String>,
    },
    /// Cross-category: try parsing a different category, then look for an operator.
    CrossCategory {
        /// The source category to try first.
        source_category: String,
        /// The expected operator token after the source parse.
        operator_token: String,
        /// The rule label for the cross-category result.
        rule_label: String,
        /// Whether this needs save/restore (ambiguous FIRST overlap).
        needs_backtrack: bool,
    },
    /// Cast: parse a different category and wrap it.
    Cast {
        /// Source category to parse.
        source_category: String,
        /// Constructor to wrap with.
        wrapper_label: String,
    },
    /// Grouping: parenthesized expression.
    Grouping {
        /// Opening delimiter token.
        open: String,
        /// Closing delimiter token.
        close: String,
    },
    /// Variable fallback for this category.
    Variable {
        /// Category name (to determine Var variant).
        category: String,
    },
}

/// One alternative in a lookahead decision.
#[derive(Debug, Clone)]
pub struct LookaheadAlternative {
    /// Token at position +1 that triggers this alternative.
    pub lookahead_token: String,
    /// Rule label.
    pub rule_label: String,
    /// Parse function.
    pub parse_fn: String,
}

/// A dispatch table for a single category's prefix parsing.
#[derive(Debug, Clone)]
pub struct DispatchTable {
    /// Category name.
    pub category: String,
    /// Map from first token variant name → action.
    pub entries: BTreeMap<String, DispatchAction>,
    /// Default action (usually variable fallback).
    pub default_action: Option<DispatchAction>,
}

/// Information about a grammar rule needed for FIRST set computation.
#[derive(Debug, Clone)]
pub struct RuleInfo {
    /// Constructor label.
    pub label: String,
    /// Category this rule belongs to.
    pub category: String,
    /// The first token(s) this rule can begin with.
    /// For terminals: the terminal variant name.
    /// For nonterminals: the FIRST set of the referenced category.
    pub first_items: Vec<FirstItem>,
    /// Whether this is an infix rule (handled by Pratt, not prefix dispatch).
    pub is_infix: bool,
    /// Whether this is a variable rule.
    pub is_var: bool,
    /// Whether this is a literal rule (Integer, Float, Boolean, StringLit).
    pub is_literal: bool,
    /// Whether this is a cross-category rule.
    pub is_cross_category: bool,
    /// Whether this is a cast rule.
    pub is_cast: bool,
}

/// What the first item of a rule can be.
#[derive(Debug, Clone)]
pub enum FirstItem {
    /// A fixed terminal token.
    Terminal(String),
    /// A nonterminal (needs FIRST set lookup).
    NonTerminal(String),
    /// An identifier (could be a variable).
    Ident,
}

/// Compute FIRST sets for all categories and build dispatch tables.
///
/// ## Optimizations
///
/// - **Dirty-flag convergence:** Replaces two `BTreeMap<String, usize>` snapshot
///   allocations per iteration with a single `changed` boolean, using
///   `BTreeSet::insert`'s return value to detect new tokens.
/// - **Reusable buffer:** `tokens_to_add` Vec is reused across iterations
///   (stack-local, not TLS — `clear()` drops Strings so only the Vec shell
///   is retained, making TLS marginal for the added complexity).
pub fn compute_first_sets(
    rules: &[RuleInfo],
    categories: &[String],
) -> BTreeMap<String, FirstSet> {
    let mut first_sets: BTreeMap<String, FirstSet> = BTreeMap::new();

    // Initialize empty FIRST sets for all categories
    for cat in categories {
        first_sets.insert(cat.clone(), FirstSet::new());
    }

    // Reusable buffer for tokens to add (retained across iterations)
    let mut tokens_to_add: Vec<String> = Vec::with_capacity(16);

    // Fixed-point iteration: keep adding to FIRST sets until stable.
    // Each iteration propagates nonterminal FIRST sets one level deeper.
    // Convergence is guaranteed in at most |categories| + 1 iterations
    // (each iteration can expand at least one category's FIRST set).
    loop {
        let mut changed = false;

        for rule in rules {
            if rule.is_infix {
                continue; // Infix rules don't contribute to prefix FIRST sets
            }

            for item in &rule.first_items {
                tokens_to_add.clear();
                match item {
                    FirstItem::Terminal(t) => {
                        tokens_to_add.push(terminal_to_variant_name(t));
                    }
                    FirstItem::NonTerminal(cat) => {
                        if let Some(cat_first) = first_sets.get(cat) {
                            tokens_to_add.extend(cat_first.tokens.iter().cloned());
                        }
                    }
                    FirstItem::Ident => {
                        tokens_to_add.push("Ident".to_string());
                    }
                };

                if let Some(cat_first) = first_sets.get_mut(&rule.category) {
                    for token in &tokens_to_add {
                        if cat_first.tokens.insert(token.clone()) {
                            changed = true;
                        }
                    }
                }
            }
        }

        if !changed {
            break;
        }
    }

    first_sets
}

/// Lightweight input for FOLLOW set computation. Send+Sync.
///
/// Captures only the two fields that `compute_follow_sets` needs from each
/// `RuleSpec`: the category and the syntax pattern. This allows FOLLOW set
/// computation to run on a rayon worker thread without touching the `!Send`
/// `rust_code: Option<TokenStream>` field on `RuleSpec`.
#[derive(Debug, Clone)]
pub struct FollowSetInput {
    /// Category this rule belongs to.
    pub category: String,
    /// Syntax items describing the concrete syntax.
    pub syntax: Vec<crate::SyntaxItemSpec>,
}

/// Compute FOLLOW sets for all categories from `FollowSetInput` slices.
///
/// Identical to `compute_follow_sets()` but takes `&[FollowSetInput]` instead
/// of `&[RuleSpec]`, enabling use from Send+Sync pipeline contexts.
pub fn compute_follow_sets_from_inputs(
    inputs: &[FollowSetInput],
    categories: &[String],
    first_sets: &BTreeMap<String, FirstSet>,
    primary_category: &str,
) -> BTreeMap<String, FirstSet> {
    let mut follow_sets: BTreeMap<String, FirstSet> = BTreeMap::new();

    for cat in categories {
        follow_sets.insert(cat.clone(), FirstSet::new());
    }

    if let Some(follow) = follow_sets.get_mut(primary_category) {
        follow.insert("Eof");
    }

    // Fixed-point iteration with dirty-flag convergence.
    // Replaces two BTreeMap snapshot allocations per iteration with a
    // single changed boolean, using BTreeSet::insert return values
    // propagated through the follow set helpers.
    loop {
        let mut changed = false;

        for input in inputs {
            changed |= propagate_follow_from_items(
                &input.syntax,
                &input.category,
                first_sets,
                &mut follow_sets,
            );
        }

        if !changed {
            break;
        }
    }

    follow_sets
}

/// Compute FOLLOW sets for all categories.
///
/// FOLLOW(C) is the set of tokens that can appear immediately after a
/// C-expression in any valid sentential form.
///
/// Algorithm (Aho & Ullman, 1972):
/// - FOLLOW(start) includes Eof
/// - For each rule with syntax `[item_0, ..., item_n]` in category A:
///   - For each NonTerminal(B) at position i:
///     - FOLLOW(B) += FIRST(item_{i+1}..item_n) \ {ε}
///     - If item_{i+1}..item_n is nullable: FOLLOW(B) += FOLLOW(A)
///
/// Also handles:
/// - Collections: FOLLOW(element_cat) += {separator, closing_delimiter}
/// - ZipMapSep: propagates through body items
/// - Optional groups: propagates through inner items
///
/// Convenience wrapper around `compute_follow_sets_from_inputs()`.
pub fn compute_follow_sets(
    rules: &[crate::RuleSpec],
    categories: &[String],
    first_sets: &BTreeMap<String, FirstSet>,
    primary_category: &str,
) -> BTreeMap<String, FirstSet> {
    let inputs: Vec<FollowSetInput> = rules
        .iter()
        .map(|r| FollowSetInput {
            category: r.category.clone(),
            syntax: r.syntax.clone(),
        })
        .collect();
    compute_follow_sets_from_inputs(&inputs, categories, first_sets, primary_category)
}

/// Propagate FOLLOW set information from a sequence of syntax items.
///
/// For each nonterminal-like item at position i, computes FIRST of the
/// suffix items[i+1..] and adds it to FOLLOW of that category. If the
/// suffix is nullable, also propagates FOLLOW(rule_category).
///
/// Returns `true` if any FOLLOW set was modified (for dirty-flag convergence).
fn propagate_follow_from_items(
    items: &[crate::SyntaxItemSpec],
    rule_category: &str,
    first_sets: &BTreeMap<String, FirstSet>,
    follow_sets: &mut BTreeMap<String, FirstSet>,
) -> bool {
    let mut changed = false;
    for i in 0..items.len() {
        let suffix = &items[i + 1..];

        match &items[i] {
            crate::SyntaxItemSpec::NonTerminal { category, .. } => {
                let (suffix_first, suffix_nullable) = first_of_suffix(suffix, first_sets);
                changed |= add_first_to_follow(follow_sets, category, &suffix_first);
                if suffix_nullable {
                    changed |= copy_follow(follow_sets, rule_category, category);
                }
            }
            crate::SyntaxItemSpec::Collection {
                element_category,
                separator,
                ..
            } => {
                // Inside a collection, the separator follows each element
                changed |= add_token_to_follow(
                    follow_sets,
                    element_category,
                    &terminal_to_variant_name(separator),
                );
                // After the last element, the closing delimiter (FIRST of suffix) follows
                let (suffix_first, suffix_nullable) = first_of_suffix(suffix, first_sets);
                changed |= add_first_to_follow(follow_sets, element_category, &suffix_first);
                if suffix_nullable {
                    changed |= copy_follow(follow_sets, rule_category, element_category);
                }
            }
            crate::SyntaxItemSpec::ZipMapSep {
                body_items,
                separator,
                ..
            } => {
                // Compute the "tail" tokens after a body iteration:
                // either the separator (another iteration) or the closing delimiter
                let (suffix_first, _) = first_of_suffix(suffix, first_sets);
                let mut body_tail = FirstSet::new();
                body_tail.insert(&terminal_to_variant_name(separator));
                body_tail.union(&suffix_first);

                // Walk body items and compute FOLLOW for nonterminals within
                for j in 0..body_items.len() {
                    if let crate::SyntaxItemSpec::NonTerminal { category, .. } = &body_items[j] {
                        let body_suffix = &body_items[j + 1..];
                        let (body_suffix_first, body_suffix_nullable) =
                            first_of_suffix(body_suffix, first_sets);
                        changed |= add_first_to_follow(follow_sets, category, &body_suffix_first);
                        if body_suffix_nullable {
                            changed |= add_first_to_follow(follow_sets, category, &body_tail);
                        }
                    }
                }
            }
            crate::SyntaxItemSpec::Optional { inner } => {
                // Walk inner items. At the end of the optional group,
                // the suffix after the Optional follows.
                let (suffix_first, suffix_nullable) = first_of_suffix(suffix, first_sets);

                for j in 0..inner.len() {
                    if let crate::SyntaxItemSpec::NonTerminal { category, .. } = &inner[j] {
                        let inner_suffix = &inner[j + 1..];
                        let (inner_suffix_first, inner_suffix_nullable) =
                            first_of_suffix(inner_suffix, first_sets);
                        changed |= add_first_to_follow(follow_sets, category, &inner_suffix_first);
                        if inner_suffix_nullable {
                            // After inner items, the suffix after Optional follows
                            changed |= add_first_to_follow(follow_sets, category, &suffix_first);
                            if suffix_nullable {
                                changed |= copy_follow(follow_sets, rule_category, category);
                            }
                        }
                    }
                }
            }
            // Terminal, IdentCapture, Binder — no category-level FOLLOW propagation
            _ => {}
        }
    }
    changed
}

/// Compute the FIRST set of a suffix of syntax items.
///
/// Returns (first_set, nullable) where:
/// - first_set: tokens that can begin the suffix
/// - nullable: whether the entire suffix can derive epsilon
fn first_of_suffix(
    items: &[crate::SyntaxItemSpec],
    first_sets: &BTreeMap<String, FirstSet>,
) -> (FirstSet, bool) {
    let mut result = FirstSet::new();
    let mut nullable = true; // empty suffix is nullable

    for item in items {
        match item {
            crate::SyntaxItemSpec::Terminal(t) => {
                result.insert(&terminal_to_variant_name(t));
                nullable = false;
                break; // Terminal is not nullable
            }
            crate::SyntaxItemSpec::NonTerminal { category, .. } => {
                if let Some(cat_first) = first_sets.get(category) {
                    for token in &cat_first.tokens {
                        result.insert(token);
                    }
                    if !cat_first.nullable {
                        nullable = false;
                        break;
                    }
                    // Category is nullable — continue to next item
                } else {
                    nullable = false;
                    break;
                }
            }
            crate::SyntaxItemSpec::IdentCapture { .. }
            | crate::SyntaxItemSpec::Binder { .. } => {
                result.insert("Ident");
                nullable = false;
                break; // Identifiers are not nullable
            }
            crate::SyntaxItemSpec::Collection { element_category, .. } => {
                // FIRST of a collection = FIRST of the element category
                if let Some(cat_first) = first_sets.get(element_category) {
                    for token in &cat_first.tokens {
                        result.insert(token);
                    }
                }
                // Collections can be empty (0 elements), so nullable — continue
            }
            crate::SyntaxItemSpec::ZipMapSep { body_items, .. } => {
                // FIRST = FIRST of first body item
                let (body_first, _) = first_of_suffix(body_items, first_sets);
                result.union(&body_first);
                // ZipMapSep can be empty (0 iterations), so nullable — continue
            }
            crate::SyntaxItemSpec::Optional { inner } => {
                // FIRST of Optional = FIRST of inner items
                let (inner_first, _) = first_of_suffix(inner, first_sets);
                result.union(&inner_first);
                // Optional is nullable by definition — continue
            }
        }
    }

    (result, nullable)
}

/// Add all tokens from a FIRST set to a category's FOLLOW set.
///
/// Returns `true` if any new token was inserted (for dirty-flag convergence).
fn add_first_to_follow(
    follow_sets: &mut BTreeMap<String, FirstSet>,
    category: &str,
    first: &FirstSet,
) -> bool {
    let mut changed = false;
    if let Some(follow) = follow_sets.get_mut(category) {
        for token in &first.tokens {
            if follow.tokens.insert(token.clone()) {
                changed = true;
            }
        }
    }
    changed
}

/// Add a single token to a category's FOLLOW set.
///
/// Returns `true` if the token was newly inserted (for dirty-flag convergence).
fn add_token_to_follow(
    follow_sets: &mut BTreeMap<String, FirstSet>,
    category: &str,
    token: &str,
) -> bool {
    if let Some(follow) = follow_sets.get_mut(category) {
        follow.tokens.insert(token.to_string())
    } else {
        false
    }
}

/// Copy FOLLOW(from_category) into FOLLOW(to_category).
///
/// No-op when from_category == to_category (would just add to itself).
/// Returns `true` if any new token was copied (for dirty-flag convergence).
fn copy_follow(
    follow_sets: &mut BTreeMap<String, FirstSet>,
    from_category: &str,
    to_category: &str,
) -> bool {
    if from_category == to_category {
        return false;
    }
    if let Some(from_follow) = follow_sets.get(from_category).cloned() {
        if let Some(to_follow) = follow_sets.get_mut(to_category) {
            let before = to_follow.tokens.len();
            to_follow.union(&from_follow);
            return to_follow.tokens.len() > before;
        }
    }
    false
}

// ══════════════════════════════════════════════════════════════════════════════
// Incremental FIRST/FOLLOW for grammar composition
// ══════════════════════════════════════════════════════════════════════════════

/// Incrementally extend FIRST sets after grammar composition.
///
/// Takes existing FIRST sets (from grammar A) and newly-added rules (from grammar B)
/// and computes the fixed-point extension. Categories that only appear in the new
/// rules are initialized with empty FIRST sets before the fixed-point iteration.
///
/// This avoids recomputing FIRST sets for grammar A's rules from scratch. The
/// result is equivalent to calling `compute_first_sets()` on the full merged
/// rule set, but skips already-converged rules from grammar A.
///
/// ## Correctness
///
/// The fixed-point iteration runs over *all* rules (both existing and new) because
/// new rules may reference existing categories, extending their FIRST sets.
/// However, existing rules that don't reference new categories are already stable
/// and converge in zero iterations, so the cost is proportional to the new rules'
/// dependency depth, not the total grammar size.
#[cfg(feature = "wfst")]
pub fn incremental_first_sets(
    existing: &BTreeMap<String, FirstSet>,
    new_rules: &[RuleInfo],
    new_categories: &[String],
) -> BTreeMap<String, FirstSet> {
    let mut first_sets = existing.clone();

    // Ensure all new categories have entries
    for cat in new_categories {
        first_sets.entry(cat.clone()).or_insert_with(FirstSet::new);
    }

    // Fixed-point iteration over new rules only
    let mut tokens_to_add: Vec<String> = Vec::with_capacity(16);
    loop {
        let mut changed = false;
        for rule in new_rules {
            if rule.is_infix {
                continue;
            }
            for item in &rule.first_items {
                tokens_to_add.clear();
                match item {
                    FirstItem::Terminal(t) => {
                        tokens_to_add.push(crate::automata::codegen::terminal_to_variant_name(t));
                    }
                    FirstItem::NonTerminal(cat) => {
                        if let Some(cat_first) = first_sets.get(cat) {
                            tokens_to_add.extend(cat_first.tokens.iter().cloned());
                        }
                    }
                    FirstItem::Ident => {
                        tokens_to_add.push("Ident".to_string());
                    }
                };
                if let Some(cat_first) = first_sets.get_mut(&rule.category) {
                    for token in &tokens_to_add {
                        if cat_first.tokens.insert(token.clone()) {
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    first_sets
}

/// Incrementally extend FOLLOW sets after grammar composition.
///
/// Takes existing FOLLOW sets (from grammar A), new rules (from grammar B),
/// and the merged FIRST sets, and computes the fixed-point extension.
///
/// Like `incremental_first_sets`, this runs the fixed-point over the new rules
/// only. Existing rules that don't reference new categories are already stable.
#[cfg(feature = "wfst")]
pub fn incremental_follow_sets(
    existing: &BTreeMap<String, FirstSet>,
    new_inputs: &[FollowSetInput],
    new_categories: &[String],
    first_sets: &BTreeMap<String, FirstSet>,
) -> BTreeMap<String, FirstSet> {
    let mut follow_sets = existing.clone();

    // Ensure all new categories have entries
    for cat in new_categories {
        follow_sets.entry(cat.clone()).or_insert_with(FirstSet::new);
    }

    // Fixed-point iteration over new inputs
    loop {
        let mut changed = false;
        for input in new_inputs {
            changed |= propagate_follow_from_items(
                &input.syntax,
                &input.category,
                first_sets,
                &mut follow_sets,
            );
        }
        if !changed {
            break;
        }
    }

    follow_sets
}

/// Merge two terminal sets, returning the union.
///
/// Used during grammar composition to incrementally build the terminal set
/// for the merged grammar without re-scanning all rules.
#[cfg(feature = "wfst")]
pub fn merge_terminal_sets(
    a: &BTreeSet<String>,
    b: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut merged = a.clone();
    merged.extend(b.iter().cloned());
    merged
}

/// Build dispatch tables for all categories.
///
/// For each category, determines which token triggers which parse alternative,
/// using FIRST set analysis to minimize backtracking.
pub fn build_dispatch_tables(
    rules: &[RuleInfo],
    categories: &[String],
    first_sets: &BTreeMap<String, FirstSet>,
) -> BTreeMap<String, DispatchTable> {
    let mut tables: BTreeMap<String, DispatchTable> = BTreeMap::new();

    for cat in categories {
        let cat_rules: Vec<&RuleInfo> = rules
            .iter()
            .filter(|r| r.category == *cat && !r.is_infix)
            .collect();

        let mut entries: BTreeMap<String, DispatchAction> = BTreeMap::new();
        let mut default_action = None;

        // Build a map from first token → list of rules that can start with it
        let mut token_to_rules: BTreeMap<String, Vec<&RuleInfo>> = BTreeMap::new();

        for rule in &cat_rules {
            if rule.is_var {
                default_action = Some(DispatchAction::Variable {
                    category: cat.clone(),
                });
                // Variables start with Ident
                token_to_rules
                    .entry("Ident".to_string())
                    .or_default()
                    .push(rule);
                continue;
            }

            for item in &rule.first_items {
                let tokens: Vec<String> = match item {
                    FirstItem::Terminal(t) => {
                        vec![terminal_to_variant_name(t)]
                    }
                    FirstItem::NonTerminal(ref_cat) => {
                        if let Some(ref_first) = first_sets.get(ref_cat) {
                            ref_first.tokens.iter().cloned().collect()
                        } else {
                            vec![]
                        }
                    }
                    FirstItem::Ident => {
                        vec!["Ident".to_string()]
                    }
                };

                for token in tokens {
                    token_to_rules
                        .entry(token)
                        .or_default()
                        .push(rule);
                }
            }
        }

        // For each first token, determine the dispatch action
        for (token, matching_rules) in &token_to_rules {
            if matching_rules.len() == 1 {
                // Unambiguous: direct dispatch
                let rule = matching_rules[0];
                if rule.is_var {
                    entries.insert(
                        token.clone(),
                        DispatchAction::Variable {
                            category: cat.clone(),
                        },
                    );
                } else if rule.is_cast {
                    // Cast rule: parse source category and wrap
                    if let Some(FirstItem::NonTerminal(src_cat)) = rule.first_items.first() {
                        entries.insert(
                            token.clone(),
                            DispatchAction::Cast {
                                source_category: src_cat.clone(),
                                wrapper_label: rule.label.clone(),
                            },
                        );
                    }
                } else {
                    entries.insert(
                        token.clone(),
                        DispatchAction::Direct {
                            rule_label: rule.label.clone(),
                            parse_fn: format!("parse_{}", rule.label.to_lowercase()),
                        },
                    );
                }
            } else {
                // Ambiguous: multiple rules start with the same token
                // Use lookahead to disambiguate
                let non_var_rules: Vec<&&RuleInfo> = matching_rules
                    .iter()
                    .filter(|r| !r.is_var)
                    .collect();

                if non_var_rules.is_empty() {
                    // Only variable rules — use variable dispatch
                    entries.insert(
                        token.clone(),
                        DispatchAction::Variable {
                            category: cat.clone(),
                        },
                    );
                } else if non_var_rules.len() == 1 && matching_rules.iter().any(|r| r.is_var) {
                    // One non-var rule + variable fallback: use lookahead
                    let rule = non_var_rules[0];
                    let mut alternatives = Vec::new();

                    // The non-var rule must have a distinguishing second token
                    // For now, generate a lookahead alternative based on the rule structure
                    alternatives.push(LookaheadAlternative {
                        lookahead_token: "specific".to_string(), // Will be refined
                        rule_label: rule.label.clone(),
                        parse_fn: format!("parse_{}", rule.label.to_lowercase()),
                    });

                    entries.insert(
                        token.clone(),
                        DispatchAction::Lookahead {
                            alternatives,
                            fallback: Some(cat.clone()),
                        },
                    );
                } else {
                    // Multiple non-var rules: need more sophisticated lookahead
                    let alternatives: Vec<LookaheadAlternative> = non_var_rules
                        .iter()
                        .map(|r| LookaheadAlternative {
                            lookahead_token: format!("rule_{}", r.label),
                            rule_label: r.label.clone(),
                            parse_fn: format!("parse_{}", r.label.to_lowercase()),
                        })
                        .collect();

                    let fallback = if matching_rules.iter().any(|r| r.is_var) {
                        Some(cat.clone())
                    } else {
                        None
                    };

                    entries.insert(
                        token.clone(),
                        DispatchAction::Lookahead {
                            alternatives,
                            fallback,
                        },
                    );
                }
            }
        }

        tables.insert(
            cat.clone(),
            DispatchTable {
                category: cat.clone(),
                entries,
                default_action,
            },
        );
    }

    tables
}

/// Analyze cross-category FIRST set overlaps.
///
/// For cross-category rules (e.g., `Int "==" Int → Bool`), determines which
/// tokens can unambiguously trigger the cross-category parse path vs which
/// require save/restore backtracking.
pub fn analyze_cross_category_overlaps(
    categories: &[String],
    first_sets: &BTreeMap<String, FirstSet>,
) -> BTreeMap<(String, String), CrossCategoryOverlap> {
    let mut overlaps = BTreeMap::new();

    for i in 0..categories.len() {
        for j in 0..categories.len() {
            if i == j {
                continue;
            }

            let cat_a = &categories[i];
            let cat_b = &categories[j];

            if let (Some(first_a), Some(first_b)) = (first_sets.get(cat_a), first_sets.get(cat_b)) {
                let intersection = first_a.intersection(first_b);
                let unique_a = first_a.difference(first_b);
                let unique_b = first_b.difference(first_a);

                if !intersection.is_empty() {
                    overlaps.insert(
                        (cat_a.clone(), cat_b.clone()),
                        CrossCategoryOverlap {
                            category_a: cat_a.clone(),
                            category_b: cat_b.clone(),
                            ambiguous_tokens: intersection,
                            unique_to_a: unique_a,
                            unique_to_b: unique_b,
                        },
                    );
                }
            }
        }
    }

    overlaps
}

/// Result of cross-category FIRST set overlap analysis.
#[derive(Debug, Clone)]
pub struct CrossCategoryOverlap {
    pub category_a: String,
    pub category_b: String,
    /// Tokens that can start expressions in both categories (need backtracking).
    pub ambiguous_tokens: FirstSet,
    /// Tokens unique to category A (deterministic dispatch).
    pub unique_to_a: FirstSet,
    /// Tokens unique to category B (deterministic dispatch).
    pub unique_to_b: FirstSet,
}

// ══════════════════════════════════════════════════════════════════════════════
// Grammar warning detection
// ══════════════════════════════════════════════════════════════════════════════

/// A compile-time grammar warning detected during analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GrammarWarning {
    /// Multiple non-infix, non-var, non-literal rules in the same category
    /// start with the same terminal token, causing ambiguous prefix dispatch.
    AmbiguousPrefix {
        token: String,
        category: String,
        rules: Vec<String>,
    },
    /// An RD rule's first syntax item is a NonTerminal of the same category,
    /// which causes infinite recursion in the generated recursive descent parser.
    LeftRecursion {
        rule_label: String,
        category: String,
    },
    /// A category is declared in `types` but never referenced in any rule's
    /// syntax as a NonTerminal or Collection element.
    UnusedCategory {
        category: String,
    },
}

impl std::fmt::Display for GrammarWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GrammarWarning::AmbiguousPrefix {
                token,
                category,
                rules,
            } => write!(
                f,
                "ambiguous prefix dispatch for token \"{}\" in category {}: rules [{}] both match",
                token,
                category,
                rules.join(", ")
            ),
            GrammarWarning::LeftRecursion {
                rule_label,
                category,
            } => write!(
                f,
                "left-recursive rule \"{}\" in category {} (first item is NonTerminal of same category)",
                rule_label, category
            ),
            GrammarWarning::UnusedCategory { category } => {
                write!(
                    f,
                    "category \"{}\" declared but never referenced in any rule syntax",
                    category
                )
            }
        }
    }
}

/// Detect grammar warnings from rule and category information.
///
/// Checks for:
/// 1. **Ambiguous prefix dispatch** — multiple non-infix/non-var/non-literal rules
///    in the same category start with the same terminal token.
/// 2. **Left-recursion in RD rules** — a rule's first syntax item is a NonTerminal
///    of the same category (infinite recursion in generated parser).
/// 3. **Unused categories** — categories declared in `types` but never referenced
///    in any rule's syntax.
pub fn detect_grammar_warnings(
    rules: &[RuleInfo],
    categories: &[String],
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)], // (label, category, syntax)
) -> Vec<GrammarWarning> {
    let mut warnings = Vec::new();

    // 1. Ambiguous prefix dispatch
    detect_ambiguous_prefix(rules, categories, &mut warnings);

    // 2. Left-recursion
    detect_left_recursion(all_syntax, &mut warnings);

    // 3. Unused categories
    detect_unused_categories(categories, all_syntax, &mut warnings);

    warnings
}

/// Detect ambiguous prefix dispatch: multiple non-infix, non-var, non-literal
/// rules in the same category starting with the same terminal.
fn detect_ambiguous_prefix(
    rules: &[RuleInfo],
    categories: &[String],
    warnings: &mut Vec<GrammarWarning>,
) {
    use std::collections::BTreeMap;

    for cat in categories {
        // Collect non-infix, non-var, non-literal rules for this category
        let prefix_rules: Vec<&RuleInfo> = rules
            .iter()
            .filter(|r| r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal)
            .collect();

        // Map terminal → list of rule labels
        let mut terminal_to_rules: BTreeMap<String, Vec<String>> = BTreeMap::new();

        for rule in &prefix_rules {
            for item in &rule.first_items {
                if let FirstItem::Terminal(t) = item {
                    terminal_to_rules
                        .entry(t.clone())
                        .or_default()
                        .push(rule.label.clone());
                }
            }
        }

        // Report ambiguities (2+ rules for the same terminal)
        for (token, rule_labels) in &terminal_to_rules {
            if rule_labels.len() > 1 {
                warnings.push(GrammarWarning::AmbiguousPrefix {
                    token: token.clone(),
                    category: cat.clone(),
                    rules: rule_labels.clone(),
                });
            }
        }
    }
}

/// Detect left-recursive rules: first syntax item is NonTerminal of the same category.
fn detect_left_recursion(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    warnings: &mut Vec<GrammarWarning>,
) {
    for (label, category, syntax) in all_syntax {
        if let Some(crate::SyntaxItemSpec::NonTerminal {
            category: ref first_cat,
            ..
        }) = syntax.first()
        {
            if first_cat == category {
                    // This is an infix rule if it's pattern is [NT, T, NT] — skip those.
                    // Left-recursion in infix rules is handled by Pratt parsing.
                    // Only warn for non-infix rules (RD handlers).
                    let terminal_count = syntax
                        .iter()
                        .filter(|i| matches!(i, crate::SyntaxItemSpec::Terminal(_)))
                        .count();
                    let nt_count = syntax
                        .iter()
                        .filter(|i| matches!(i, crate::SyntaxItemSpec::NonTerminal { .. }))
                        .count();

                    // Infix pattern: exactly 2 NTs of same category with terminal(s) between.
                    // Skip those — Pratt handles left-recursion for infix.
                    let is_infix_pattern = nt_count == 2
                        && terminal_count >= 1
                        && syntax.len() >= 3
                        && matches!(syntax.last(), Some(crate::SyntaxItemSpec::NonTerminal { category: ref last_cat, .. }) if last_cat == category);

                    // Postfix pattern: exactly 1 NT + 1 terminal
                    let is_postfix_pattern = nt_count == 1 && terminal_count == 1 && syntax.len() == 2;

                    // Mixfix: 3+ NTs with terminals — also handled by Pratt
                    let is_mixfix_pattern = nt_count >= 3 && terminal_count >= 2;

                    if !is_infix_pattern && !is_postfix_pattern && !is_mixfix_pattern {
                        warnings.push(GrammarWarning::LeftRecursion {
                            rule_label: label.clone(),
                            category: category.clone(),
                        });
                    }
                }
            }
        }
}

/// Detect unused categories: declared but never referenced in any rule's syntax.
fn detect_unused_categories(
    categories: &[String],
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    warnings: &mut Vec<GrammarWarning>,
) {
    use std::collections::BTreeSet;

    // Collect all categories referenced in syntax items
    let mut referenced: BTreeSet<String> = BTreeSet::new();

    for (_, _, syntax) in all_syntax {
        collect_referenced_categories(syntax, &mut referenced);
    }

    // Also count rule target categories as "used" (a category with rules is used)
    for (_, category, _) in all_syntax {
        referenced.insert(category.clone());
    }

    for cat in categories {
        if !referenced.contains(cat) {
            warnings.push(GrammarWarning::UnusedCategory {
                category: cat.clone(),
            });
        }
    }
}

/// Recursively collect all category names referenced in syntax items.
fn collect_referenced_categories(
    items: &[crate::SyntaxItemSpec],
    referenced: &mut std::collections::BTreeSet<String>,
) {
    for item in items {
        match item {
            crate::SyntaxItemSpec::NonTerminal { category, .. } => {
                referenced.insert(category.clone());
            }
            crate::SyntaxItemSpec::Collection {
                element_category, ..
            } => {
                referenced.insert(element_category.clone());
            }
            crate::SyntaxItemSpec::ZipMapSep {
                left_category,
                right_category,
                body_items,
                ..
            } => {
                referenced.insert(left_category.clone());
                referenced.insert(right_category.clone());
                collect_referenced_categories(body_items, referenced);
            }
            crate::SyntaxItemSpec::Optional { inner } => {
                collect_referenced_categories(inner, referenced);
            }
            crate::SyntaxItemSpec::Binder { category, .. } => {
                referenced.insert(category.clone());
            }
            _ => {}
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Dispatch action table extraction (for WFST weight assignment)
// ══════════════════════════════════════════════════════════════════════════════

/// Build per-category dispatch action tables from grammar analysis.
///
/// Produces `BTreeMap<category_name, BTreeMap<token_variant, DispatchAction>>` — the same
/// token-to-action mapping that `write_prefix_match_arms()` and `write_category_dispatch()`
/// encode as generated match arms, but as structured data suitable for WFST weight
/// assignment.
///
/// This function extracts the dispatch decisions without generating code, enabling the
/// WFST builder (`build_prediction_wfsts`) to assign weights to each action based on
/// ambiguity analysis.
///
/// The tables include:
/// - **Direct dispatch**: terminal-first RD rules → `Direct { rule_label, parse_fn }`
/// - **Variable fallback**: Ident token → `Variable { category }`
/// - **Native literals**: Integer/Float/Boolean/StringLit → `Direct` for native type rules
/// - **Grouping**: LParen → `Grouping { open: "(", close: ")" }`
/// - **Cast**: tokens unique to source category → `Cast { source, wrapper }`
/// - **Cross-category**: from cross-category rules and overlap analysis
#[cfg(feature = "wfst")]
pub fn build_dispatch_action_tables(
    categories: &[String],
    first_sets: &BTreeMap<String, FirstSet>,
    overlaps: &BTreeMap<(String, String), CrossCategoryOverlap>,
    rd_rules: &[crate::recursive::RDRuleInfo],
    cross_rules: &[crate::dispatch::CrossCategoryRule],
    cast_rules: &[crate::dispatch::CastRule],
    native_types: &BTreeMap<String, Option<String>>,
) -> BTreeMap<String, BTreeMap<String, DispatchAction>> {
    use crate::automata::codegen::terminal_to_variant_name;

    let mut tables: BTreeMap<String, BTreeMap<String, DispatchAction>> = BTreeMap::new();

    for cat in categories {
        let mut entries: BTreeMap<String, DispatchAction> = BTreeMap::new();

        // ── Terminal-first RD rules → Direct dispatch ──
        for rd_rule in rd_rules {
            if rd_rule.category != *cat {
                continue;
            }
            // Skip infix-like, collection-first, and nonterminal-first rules
            if rd_rule.prefix_bp.is_some() {
                // Unary prefix — still Direct, just with a different parse_fn
                if let Some(crate::recursive::RDSyntaxItem::Terminal(t)) = rd_rule.items.first() {
                    let variant = terminal_to_variant_name(t);
                    entries.entry(variant).or_insert_with(|| DispatchAction::Direct {
                        rule_label: rd_rule.label.clone(),
                        parse_fn: format!("parse_{}", rd_rule.label.to_lowercase()),
                    });
                }
                continue;
            }

            let starts_with_terminal = matches!(
                rd_rule.items.first(),
                Some(crate::recursive::RDSyntaxItem::Terminal(_))
            );
            if !starts_with_terminal {
                continue;
            }

            if let Some(crate::recursive::RDSyntaxItem::Terminal(t)) = rd_rule.items.first() {
                let variant = terminal_to_variant_name(t);
                entries.entry(variant).or_insert_with(|| DispatchAction::Direct {
                    rule_label: rd_rule.label.clone(),
                    parse_fn: format!("parse_{}", rd_rule.label.to_lowercase()),
                });
            }
        }

        // ── Native literal dispatch ──
        if let Some(Some(native_type)) = native_types.get(cat) {
            let literal_variants: Vec<&str> = match native_type.as_str() {
                "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => vec!["Integer"],
                "f32" | "f64" => vec!["Float"],
                "bool" => vec!["Boolean"],
                "str" | "String" => vec!["StringLit"],
                _ => vec![],
            };
            for variant in literal_variants {
                entries.entry(variant.to_string()).or_insert_with(|| DispatchAction::Direct {
                    rule_label: format!("{}Lit", cat),
                    parse_fn: format!("parse_{}_literal", cat.to_lowercase()),
                });
            }
        }

        // ── Grouping: parenthesized expression ──
        entries.entry("LParen".to_string()).or_insert_with(|| DispatchAction::Grouping {
            open: "(".to_string(),
            close: ")".to_string(),
        });

        // ── Cast rules targeting this category ──
        for cast_rule in cast_rules {
            if cast_rule.target_category != *cat {
                continue;
            }
            if let Some(source_first) = first_sets.get(&cast_rule.source_category) {
                let own_first = first_sets.get(cat);
                let unique_to_source = if let Some(own) = own_first {
                    source_first.difference(own)
                } else {
                    source_first.clone()
                };
                for token in &unique_to_source.tokens {
                    entries.entry(token.clone()).or_insert_with(|| DispatchAction::Cast {
                        source_category: cast_rule.source_category.clone(),
                        wrapper_label: cast_rule.label.clone(),
                    });
                }
            }
        }

        // ── Cross-category rules targeting this category ──
        for cross_rule in cross_rules {
            if cross_rule.result_category != *cat {
                continue;
            }
            if let Some(source_first) = first_sets.get(&cross_rule.source_category) {
                let own_first = first_sets.get(cat);
                let op_variant = terminal_to_variant_name(&cross_rule.operator);

                // Tokens unique to source → deterministic cross-category dispatch
                if let Some(own) = own_first {
                    let unique_to_source = source_first.difference(own);
                    for token in &unique_to_source.tokens {
                        entries.entry(token.clone()).or_insert_with(|| {
                            DispatchAction::CrossCategory {
                                source_category: cross_rule.source_category.clone(),
                                operator_token: op_variant.clone(),
                                rule_label: cross_rule.label.clone(),
                                needs_backtrack: false,
                            }
                        });
                    }

                    // Ambiguous tokens → needs backtracking
                    let overlap_key = (cross_rule.source_category.clone(), cat.clone());
                    if let Some(overlap) = overlaps.get(&overlap_key) {
                        for token in &overlap.ambiguous_tokens.tokens {
                            entries.entry(token.clone()).or_insert_with(|| {
                                DispatchAction::CrossCategory {
                                    source_category: cross_rule.source_category.clone(),
                                    operator_token: op_variant.clone(),
                                    rule_label: cross_rule.label.clone(),
                                    needs_backtrack: true,
                                }
                            });
                        }
                    }
                }
            }
        }

        // ── Variable fallback ──
        entries.entry("Ident".to_string()).or_insert_with(|| DispatchAction::Variable {
            category: cat.clone(),
        });

        tables.insert(cat.clone(), entries);
    }

    tables
}

// ══════════════════════════════════════════════════════════════════════════════
// Sync predicate generation (for panic-mode error recovery)
// ══════════════════════════════════════════════════════════════════════════════

/// Generate a sync predicate function for a category.
///
/// The sync predicate determines which tokens can serve as synchronization
/// points during panic-mode error recovery. It includes:
/// - All tokens in the category's FOLLOW set
/// - `Eof` (always a sync point)
/// - Structural delimiters (`)`, `}`, `]`) only if they appear in the FOLLOW set
///   or are known terminals in the grammar (guaranteed by the `)` always being in
///   the grammar from the grouping rule)
///
/// Generated function signature:
/// ```text
/// fn is_sync_<Cat><'a>(token: &Token<'a>) -> bool
/// ```
pub fn generate_sync_predicate(
    buf: &mut String,
    category: &str,
    follow_set: &FirstSet,
    grammar_terminals: &std::collections::BTreeSet<String>,
) {
    let mut patterns: Vec<String> = Vec::new();

    // Always include Eof
    patterns.push("Token::Eof".to_string());

    // Include structural delimiters only if they exist in the grammar
    let structural = [
        ("RParen", ")"),
        ("RBrace", "}"),
        ("RBracket", "]"),
        ("Semi", ";"),
        ("Comma", ","),
    ];
    for (variant, terminal) in &structural {
        if grammar_terminals.contains(*terminal) {
            let pattern = format!("Token::{}", variant);
            if !patterns.contains(&pattern) {
                patterns.push(pattern);
            }
        }
    }

    // Add FOLLOW set tokens
    for token in &follow_set.tokens {
        let pattern = token_to_match_pattern(token);
        if !patterns.contains(&pattern) {
            patterns.push(pattern);
        }
    }

    use std::fmt::Write;
    write!(
        buf,
        "fn is_sync_{cat}<'a>(token: &Token<'a>) -> bool {{ \
            matches!(token, {pats}) \
        }}",
        cat = category,
        pats = patterns.join(" | "),
    )
    .unwrap();
}

/// Convert a token name (from FIRST/FOLLOW sets) to a match pattern string.
fn token_to_match_pattern(token: &str) -> String {
    match token {
        "Ident" => "Token::Ident(_)".to_string(),
        "Integer" => "Token::Integer(_)".to_string(),
        "Float" => "Token::Float(_)".to_string(),
        "Boolean" => "Token::Boolean(_)".to_string(),
        "StringLit" => "Token::StringLit(_)".to_string(),
        "Dollar" => "Token::Dollar(_)".to_string(),
        "DoubleDollar" => "Token::DoubleDollar(_)".to_string(),
        "Eof" => "Token::Eof".to_string(),
        other => format!("Token::{}", other),
    }
}

/// Generate a FIRST set as a `contains` check in generated code.
pub fn generate_first_set_check(
    first_set: &FirstSet,
    token_var: &str,
) -> TokenStream {
    let token_ident = format_ident!("{}", token_var);
    let checks: Vec<TokenStream> = first_set
        .tokens
        .iter()
        .map(|t| {
            let variant = format_ident!("{}", t);
            match t.as_str() {
                "Ident" => quote! { Token::Ident(_) },
                "Integer" => quote! { Token::Integer(_) },
                "Float" => quote! { Token::Float(_) },
                "Boolean" => quote! { Token::Boolean(_) },
                "StringLit" => quote! { Token::StringLit(_) },
                "Dollar" => quote! { Token::Dollar(_) },
                "DoubleDollar" => quote! { Token::DoubleDollar(_) },
                _ => quote! { Token::#variant },
            }
        })
        .collect();

    if checks.is_empty() {
        quote! { false }
    } else {
        quote! { matches!(#token_ident, #(#checks)|*) }
    }
}
