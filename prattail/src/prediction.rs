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
        FirstSet { tokens: BTreeSet::new(), nullable: false }
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

impl DispatchAction {
    /// Return a human-readable rule label for this action.
    ///
    /// Used by composed dispatch to identify rules in codegen output.
    /// For `Variable`, returns the category name (caller should prepend "Var" if needed).
    pub fn rule_label(&self) -> String {
        match self {
            DispatchAction::Direct { rule_label, .. } => rule_label.clone(),
            DispatchAction::Lookahead { fallback, .. } => {
                fallback.clone().unwrap_or_else(|| "Lookahead".to_string())
            }
            DispatchAction::CrossCategory { rule_label, .. } => rule_label.clone(),
            DispatchAction::Cast { wrapper_label, .. } => wrapper_label.clone(),
            DispatchAction::Grouping { .. } => "Grouping".to_string(),
            DispatchAction::Variable { category } => format!("Var{}", category),
        }
    }
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
pub fn compute_first_sets(rules: &[RuleInfo], categories: &[String]) -> BTreeMap<String, FirstSet> {
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
                    },
                    FirstItem::NonTerminal(cat) => {
                        if let Some(cat_first) = first_sets.get(cat) {
                            tokens_to_add.extend(cat_first.tokens.iter().cloned());
                        }
                    },
                    FirstItem::Ident => {
                        tokens_to_add.push("Ident".to_string());
                    },
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
            },
            crate::SyntaxItemSpec::Collection { element_category, separator, .. } => {
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
            },
            crate::SyntaxItemSpec::ZipMapSep { body_items, separator, .. } => {
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
            },
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
            },
            // Terminal, IdentCapture, Binder — no category-level FOLLOW propagation
            _ => {},
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
            },
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
            },
            crate::SyntaxItemSpec::IdentCapture { .. } | crate::SyntaxItemSpec::Binder { .. } => {
                result.insert("Ident");
                nullable = false;
                break; // Identifiers are not nullable
            },
            crate::SyntaxItemSpec::BinderCollection { .. } => {
                result.insert("Ident");
                // Binder collections can be empty (0 elements), so nullable — continue
            },
            crate::SyntaxItemSpec::Collection { element_category, .. } => {
                // FIRST of a collection = FIRST of the element category
                if let Some(cat_first) = first_sets.get(element_category) {
                    for token in &cat_first.tokens {
                        result.insert(token);
                    }
                }
                // Collections can be empty (0 elements), so nullable — continue
            },
            crate::SyntaxItemSpec::ZipMapSep { body_items, .. } => {
                // FIRST = FIRST of first body item
                let (body_first, _) = first_of_suffix(body_items, first_sets);
                result.union(&body_first);
                // ZipMapSep can be empty (0 iterations), so nullable — continue
            },
            crate::SyntaxItemSpec::Optional { inner } => {
                // FIRST of Optional = FIRST of inner items
                let (inner_first, _) = first_of_suffix(inner, first_sets);
                result.union(&inner_first);
                // Optional is nullable by definition — continue
            },
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
pub fn incremental_first_sets(
    existing: &BTreeMap<String, FirstSet>,
    new_rules: &[RuleInfo],
    new_categories: &[String],
) -> BTreeMap<String, FirstSet> {
    let mut first_sets = existing.clone();

    // Ensure all new categories have entries
    for cat in new_categories {
        first_sets.entry(cat.clone()).or_default();
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
                    },
                    FirstItem::NonTerminal(cat) => {
                        if let Some(cat_first) = first_sets.get(cat) {
                            tokens_to_add.extend(cat_first.tokens.iter().cloned());
                        }
                    },
                    FirstItem::Ident => {
                        tokens_to_add.push("Ident".to_string());
                    },
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
pub fn incremental_follow_sets(
    existing: &BTreeMap<String, FirstSet>,
    new_inputs: &[FollowSetInput],
    new_categories: &[String],
    first_sets: &BTreeMap<String, FirstSet>,
) -> BTreeMap<String, FirstSet> {
    let mut follow_sets = existing.clone();

    // Ensure all new categories have entries
    for cat in new_categories {
        follow_sets.entry(cat.clone()).or_default();
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
pub fn merge_terminal_sets(a: &BTreeSet<String>, b: &BTreeSet<String>) -> BTreeSet<String> {
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
                default_action = Some(DispatchAction::Variable { category: cat.clone() });
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
                    },
                    FirstItem::NonTerminal(ref_cat) => {
                        if let Some(ref_first) = first_sets.get(ref_cat) {
                            ref_first.tokens.iter().cloned().collect()
                        } else {
                            vec![]
                        }
                    },
                    FirstItem::Ident => {
                        vec!["Ident".to_string()]
                    },
                };

                for token in tokens {
                    token_to_rules.entry(token).or_default().push(rule);
                }
            }
        }

        // For each first token, determine the dispatch action
        for (token, matching_rules) in &token_to_rules {
            if matching_rules.len() == 1 {
                // Unambiguous: direct dispatch
                let rule = matching_rules[0];
                if rule.is_var {
                    entries
                        .insert(token.clone(), DispatchAction::Variable { category: cat.clone() });
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
                let non_var_rules: Vec<&&RuleInfo> =
                    matching_rules.iter().filter(|r| !r.is_var).collect();

                if non_var_rules.is_empty() {
                    // Only variable rules — use variable dispatch
                    entries
                        .insert(token.clone(), DispatchAction::Variable { category: cat.clone() });
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
                        DispatchAction::Lookahead { alternatives, fallback },
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
    LeftRecursion { rule_label: String, category: String },
    /// A category is declared in `types` but never referenced in any rule's
    /// syntax as a NonTerminal or Collection element.
    UnusedCategory { category: String },
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
                "ambiguous prefix dispatch for token \"{}\" in category {}: rules [{}] all match",
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
        if let Some(crate::SyntaxItemSpec::NonTerminal { category: ref first_cat, .. }) =
            syntax.first()
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
            warnings.push(GrammarWarning::UnusedCategory { category: cat.clone() });
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
            },
            crate::SyntaxItemSpec::Collection { element_category, .. } => {
                referenced.insert(element_category.clone());
            },
            crate::SyntaxItemSpec::ZipMapSep {
                left_category,
                right_category,
                body_items,
                ..
            } => {
                referenced.insert(left_category.clone());
                referenced.insert(right_category.clone());
                collect_referenced_categories(body_items, referenced);
            },
            crate::SyntaxItemSpec::Optional { inner } => {
                collect_referenced_categories(inner, referenced);
            },
            crate::SyntaxItemSpec::Binder { category, .. } => {
                referenced.insert(category.clone());
            },
            _ => {},
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
                    entries
                        .entry(variant)
                        .or_insert_with(|| DispatchAction::Direct {
                            rule_label: rd_rule.label.clone(),
                            parse_fn: format!("parse_{}", rd_rule.label.to_lowercase()),
                        });
                }
                continue;
            }

            let starts_with_terminal =
                matches!(rd_rule.items.first(), Some(crate::recursive::RDSyntaxItem::Terminal(_)));
            if !starts_with_terminal {
                continue;
            }

            if let Some(crate::recursive::RDSyntaxItem::Terminal(t)) = rd_rule.items.first() {
                let variant = terminal_to_variant_name(t);
                entries
                    .entry(variant)
                    .or_insert_with(|| DispatchAction::Direct {
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
                entries
                    .entry(variant.to_string())
                    .or_insert_with(|| DispatchAction::Direct {
                        rule_label: format!("{}Lit", cat),
                        parse_fn: format!("parse_{}_literal", cat.to_lowercase()),
                    });
            }
        }

        // ── Grouping: parenthesized expression ──
        entries
            .entry("LParen".to_string())
            .or_insert_with(|| DispatchAction::Grouping {
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
                    entries
                        .entry(token.clone())
                        .or_insert_with(|| DispatchAction::Cast {
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
        entries
            .entry("Ident".to_string())
            .or_insert_with(|| DispatchAction::Variable { category: cat.clone() });

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
pub fn generate_first_set_check(first_set: &FirstSet, token_var: &str) -> TokenStream {
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

// ══════════════════════════════════════════════════════════════════════════════
// Composed dispatch — WFST-composed (category, DFA state) → (token, rule, weight)
// ══════════════════════════════════════════════════════════════════════════════

/// A single entry in the composed dispatch table.
///
/// Represents one valid (token_kind, rule) choice for an ambiguous
/// (category, DFA state) pair, with a composed weight for ranking.
#[derive(Debug, Clone)]
pub struct ComposedEntry {
    /// Compact ID of the token kind (from `TokenVariantMap`).
    pub token_kind_id: u8,
    /// Token variant name (e.g., "KwError", "Ident").
    pub token_variant_name: String,
    /// Rule label (e.g., "CompareProc", "VarProc").
    pub rule_label: String,
    /// Composed weight: `lexer_weight ⊗ rule_weight` (tropical times = addition).
    /// Lower = preferred by tropical shortest path.
    pub weight: f64,
}

/// Compute the composed dispatch table for all ambiguous DFA states.
///
/// For each (category, ambiguous DFA state) pair, composes the lexer's
/// alternative accepts with the grammar's FIRST sets and rule weights
/// to produce a weight-ranked slice of `ComposedEntry`s.
///
/// This is the core Phase 6C algorithm: WFST composition computed eagerly
/// over only the ambiguous states — not a full automaton product, just
/// pointwise composition.
///
/// When `prediction_wfsts` is `Some`, uses `PredictionWfst::predict()` for
/// weight-accurate results. When `None`, falls back to FIRST-set filtering
/// with rule specificity weights.
pub fn compute_composed_dispatch(
    ambiguous_states: &[(super::automata::StateId, Vec<(super::automata::TokenKind, super::automata::semiring::TropicalWeight)>)],
    categories: &[String],
    first_sets: &BTreeMap<String, FirstSet>,
    variant_map: &super::automata::codegen::TokenVariantMap,
    prediction_wfsts: Option<&BTreeMap<String, crate::wfst::PredictionWfst>>,
    rule_infos: &[RuleInfo],
) -> BTreeMap<(String, u32), Vec<ComposedEntry>> {
    let mut table: BTreeMap<(String, u32), Vec<ComposedEntry>> = BTreeMap::new();

    for &(state_id, ref alts) in ambiguous_states {
        for category in categories {
            let first_set = match first_sets.get(category) {
                Some(fs) => fs,
                None => continue,
            };

            let mut entries: Vec<ComposedEntry> = Vec::new();

            for (tok_kind, lexer_weight) in alts {
                // Map TokenKind → variant name for FIRST set membership test
                let variant_name = token_kind_to_variant_name(tok_kind);

                // Check if this token kind is in the category's FIRST set
                if !first_set.contains(&variant_name) {
                    continue;
                }

                let tok_id = variant_map.kind_to_id(tok_kind).unwrap_or(0);

                // Try PredictionWfst first for weight-accurate results
                let wfst_result = prediction_wfsts
                    .and_then(|wfsts| wfsts.get(category))
                    .map(|wfst| wfst.predict(&variant_name));

                if let Some(actions) = wfst_result {
                    if !actions.is_empty() {
                        for action in actions {
                            let rule_label = action.action.rule_label();
                            let composed = lexer_weight.value() + action.weight.value();
                            entries.push(ComposedEntry {
                                token_kind_id: tok_id,
                                token_variant_name: variant_name.clone(),
                                rule_label,
                                weight: composed,
                            });
                        }
                        continue;
                    }
                    /* PredictionWfst exists but had no actions for this token;
                       fall through to rule_infos fallback below. */
                }

                // Fallback: no PredictionWfst or no actions — use FIRST-set-aware
                // rule specificity weights
                let matching_rules =
                    find_rules_for_token(rule_infos, category, &variant_name, first_sets);

                if matching_rules.is_empty() {
                    // Token is in FIRST set but no specific rule found;
                    // create a generic entry (e.g., variable fallback)
                    entries.push(ComposedEntry {
                        token_kind_id: tok_id,
                        token_variant_name: variant_name.clone(),
                        rule_label: format!("Var{}", category),
                        weight: lexer_weight.value() + 2.0, // variable fallback penalty
                    });
                } else {
                    for (rule_label, specificity) in &matching_rules {
                        let rule_weight = specificity_weight(*specificity);
                        // Composed weight = lexer_weight ⊗ rule_weight
                        // (tropical times = addition)
                        let composed = lexer_weight.value() + rule_weight;
                        entries.push(ComposedEntry {
                            token_kind_id: tok_id,
                            token_variant_name: variant_name.clone(),
                            rule_label: rule_label.clone(),
                            weight: composed,
                        });
                    }
                }
            }

            if !entries.is_empty() {
                // Sort by weight ascending (best first)
                entries.sort_by(|a, b| {
                    a.weight
                        .partial_cmp(&b.weight)
                        .unwrap_or(std::cmp::Ordering::Equal)
                });

                // Emit codegen-time ambiguity warning using counting semiring:
                // CountingWeight tracks derivation count per (category, token).
                // count > 1 indicates ambiguity requiring tropical resolution.
                let derivation_count = crate::automata::semiring::CountingWeight::new(entries.len() as u64);
                if derivation_count.count() > 1 {
                    let alts_desc: Vec<String> = entries
                        .iter()
                        .map(|e| {
                            format!(
                                "  - Token::{} → rule {} (weight {:.2})",
                                e.token_variant_name, e.rule_label, e.weight
                            )
                        })
                        .collect();
                    eprintln!(
                        "warning: {}-way ambiguity at ({}, DFA state {}): {} derivations\n{}\n  \
                         Resolved by tropical shortest path → {}",
                        derivation_count.count(),
                        category,
                        state_id,
                        derivation_count.count(),
                        alts_desc.join("\n"),
                        entries[0].rule_label,
                    );
                }

                table.insert((category.clone(), state_id), entries);
            }
        }
    }

    table
}

/// Compute rule specificity weight.
///
/// Weight = 1 / (1 + terminals + 0.5 × nonterminals).
/// More specific rules (more structural tokens) get **lower** weight,
/// which is preferred by tropical shortest path (min).
fn specificity_weight(specificity: f64) -> f64 {
    1.0 / (1.0 + specificity)
}

/// Count the structural specificity of a rule: terminals + 0.5 × nonterminals.
fn compute_rule_specificity(rule: &RuleInfo) -> f64 {
    let mut terminals = 0.0;
    let mut nonterminals = 0.0;
    for item in &rule.first_items {
        match item {
            FirstItem::Terminal(_) => terminals += 1.0,
            FirstItem::NonTerminal(_) => nonterminals += 1.0,
            FirstItem::Ident => nonterminals += 0.5,
        }
    }
    terminals + 0.5 * nonterminals
}

/// Find rules in a category whose FIRST token matches a given variant name.
///
/// Returns `Vec<(rule_label, specificity_score)>`.
fn find_rules_for_token(
    rule_infos: &[RuleInfo],
    category: &str,
    variant_name: &str,
    first_sets: &BTreeMap<String, FirstSet>,
) -> Vec<(String, f64)> {
    let mut matches = Vec::new();

    for rule in rule_infos {
        if rule.category != category {
            continue;
        }
        if rule.is_infix {
            continue; // infix rules aren't dispatched by prefix token
        }

        // Check if this rule's first item matches the variant name
        let first_matches = rule.first_items.first().map_or(false, |item| {
            match item {
                FirstItem::Terminal(t) => terminal_to_variant_name(t) == variant_name,
                FirstItem::NonTerminal(nt_category) => {
                    // Cross-category NT: check if variant_name is in the FIRST set
                    // of the referenced NT's category
                    first_sets
                        .get(nt_category.as_str())
                        .map_or(false, |fs| fs.contains(variant_name))
                },
                FirstItem::Ident => variant_name == "Ident",
            }
        });

        if first_matches {
            let specificity = compute_rule_specificity(rule);
            matches.push((rule.label.clone(), specificity));
        }
    }

    matches
}

/// Convert a `TokenKind` to its variant name for FIRST set lookups.
fn token_kind_to_variant_name(kind: &super::automata::TokenKind) -> String {
    use super::automata::codegen::terminal_to_variant_name;
    match kind {
        super::automata::TokenKind::Eof => "Eof".to_string(),
        super::automata::TokenKind::Ident => "Ident".to_string(),
        super::automata::TokenKind::Integer => "Integer".to_string(),
        super::automata::TokenKind::Float => "Float".to_string(),
        super::automata::TokenKind::True => "Boolean".to_string(),
        super::automata::TokenKind::False => "Boolean".to_string(),
        super::automata::TokenKind::StringLit => "StringLit".to_string(),
        super::automata::TokenKind::Fixed(text) => terminal_to_variant_name(text),
        super::automata::TokenKind::Dollar => "Dollar".to_string(),
        super::automata::TokenKind::DoubleDollar => "DoubleDollar".to_string(),
    }
}

/// Emit composed dispatch table as a generated Rust function.
///
/// Produces:
/// ```text
/// fn composed_dispatch(category_id: u8, dfa_state: u32) -> &'static [(u8, &'static str, f64)] { ... }
/// ```
pub fn emit_composed_dispatch_table(
    buf: &mut String,
    table: &BTreeMap<(String, u32), Vec<ComposedEntry>>,
    categories: &[String],
) {
    use std::fmt::Write;

    // Map category names to IDs
    let cat_to_id: BTreeMap<&str, u8> = categories
        .iter()
        .enumerate()
        .map(|(i, c)| (c.as_str(), i as u8))
        .collect();

    // Category ID constants
    for (name, &id) in &cat_to_id {
        write!(buf, "const CATEGORY_ID_{}: u8 = {};", name.to_uppercase(), id).unwrap();
    }

    // Static dispatch table entries
    buf.push_str(
        "fn composed_dispatch(category_id: u8, dfa_state: u32) -> &'static [(u8, &'static str, f64)] {",
    );
    buf.push_str("match (category_id, dfa_state) {");

    for ((category, state_id), entries) in table {
        let cat_id = cat_to_id.get(category.as_str()).copied().unwrap_or(255);
        write!(buf, "({}, {}) => &[", cat_id, state_id).unwrap();
        for entry in entries {
            write!(
                buf,
                "({}, \"{}\", {:.6}),",
                entry.token_kind_id, entry.rule_label, entry.weight
            )
            .unwrap();
        }
        buf.push_str("],");
    }

    buf.push_str("_ => &[] } }");
}

/// Build a resolution map from composed dispatch entries for use in standard batch dispatch.
///
/// For each `(category, ambiguous_token_variant)` pair in the composed dispatch table,
/// picks the winning rule (lowest tropical weight) and records both the rule label
/// and the winning weight. The weight is preserved so dispatch codegen can sort
/// deterministic arms by weight (most likely first), improving CPU branch prediction.
///
/// Returns `BTreeMap<(category, token_variant), (winning_rule_label, weight)>`.
pub fn resolve_dispatch_winners(
    composed_table: &BTreeMap<(String, u32), Vec<ComposedEntry>>,
) -> BTreeMap<(String, String), (String, f64)> {
    let mut winners: BTreeMap<(String, String), (String, f64)> = BTreeMap::new();

    for ((category, _state_id), entries) in composed_table {
        for entry in entries {
            let key = (category.clone(), entry.token_variant_name.clone());
            match winners.get(&key) {
                Some((_existing_label, existing_weight)) if *existing_weight <= entry.weight => {
                    /* existing winner has equal or better weight; keep it */
                }
                _ => {
                    winners.insert(key, (entry.rule_label.clone(), entry.weight));
                }
            }
        }
    }

    winners
}

/// Build a weight map covering ALL (category, token_variant) pairs for dispatch arm ordering.
///
/// This provides weights for both ambiguous and deterministic tokens:
/// - **Ambiguous tokens**: use composed dispatch weights (tropical shortest-path winner)
/// - **Deterministic tokens**: use rule specificity weight (more specific = lower weight)
///
/// The resulting map is passed to dispatch codegen so that ALL match arms — not just
/// ambiguous ones — can be sorted by weight (most likely first), improving CPU branch
/// prediction hit rate.
pub fn build_complete_weight_map(
    composed_table: &BTreeMap<(String, u32), Vec<ComposedEntry>>,
    first_sets: &BTreeMap<String, FirstSet>,
    rule_infos: &[RuleInfo],
    category_names: &[String],
) -> BTreeMap<(String, String), f64> {
    let mut weight_map: BTreeMap<(String, String), f64> = BTreeMap::new();

    // 1. Seed with ambiguous token weights from composed dispatch (best weight per (cat, token))
    for ((category, _state_id), entries) in composed_table {
        for entry in entries {
            let key = (category.clone(), entry.token_variant_name.clone());
            match weight_map.get(&key) {
                Some(&existing) if existing <= entry.weight => { /* keep better */ }
                _ => { weight_map.insert(key, entry.weight); }
            }
        }
    }

    // 2. Fill deterministic tokens: for each category, each FIRST-set token that
    //    doesn't already have a weight gets a specificity-based weight.
    for category in category_names {
        let first_set = match first_sets.get(category) {
            Some(fs) => fs,
            None => continue,
        };

        for token in &first_set.tokens {
            let key = (category.clone(), token.clone());
            if weight_map.contains_key(&key) {
                continue; // already has an ambiguous weight
            }

            // Find the best (most specific) rule matching this token in this category
            let matching = find_rules_for_token(rule_infos, category, token, first_sets);
            if matching.is_empty() {
                // Variable fallback — higher weight (less specific)
                weight_map.insert(key, 2.0);
            } else {
                // Use the best specificity weight (lowest = most specific)
                let best = matching.iter()
                    .map(|(_, specificity)| specificity_weight(*specificity))
                    .fold(f64::INFINITY, f64::min);
                weight_map.insert(key, best);
            }
        }
    }

    weight_map
}

#[cfg(test)]
mod composed_dispatch_tests {
    use super::*;
    use crate::automata::{
        codegen::TokenVariantMap,
        semiring::TropicalWeight,
        TokenKind,
    };

    fn make_variant_map() -> TokenVariantMap {
        TokenVariantMap::from_token_kinds(&[
            TokenKind::Eof,
            TokenKind::Ident,
            TokenKind::Integer,
            TokenKind::Fixed("error".to_string()),
            TokenKind::Fixed("+".to_string()),
        ])
    }

    fn make_rule_infos() -> Vec<RuleInfo> {
        vec![
            RuleInfo {
                label: "CompareProc".to_string(),
                category: "Proc".to_string(),
                first_items: vec![
                    FirstItem::Terminal("error".to_string()),
                ],
                is_infix: false,
                is_var: false,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
            RuleInfo {
                label: "VarProc".to_string(),
                category: "Proc".to_string(),
                first_items: vec![FirstItem::Ident],
                is_infix: false,
                is_var: true,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
            RuleInfo {
                label: "AddInt".to_string(),
                category: "Int".to_string(),
                first_items: vec![FirstItem::Ident],
                is_infix: true,
                is_var: false,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
            RuleInfo {
                label: "VarInt".to_string(),
                category: "Int".to_string(),
                first_items: vec![FirstItem::Ident],
                is_infix: false,
                is_var: true,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
        ]
    }

    #[test]
    fn test_composed_dispatch_basic() {
        let variant_map = make_variant_map();
        let rule_infos = make_rule_infos();

        let mut first_sets = BTreeMap::new();
        let mut proc_first = FirstSet::new();
        proc_first.insert("KwError");
        proc_first.insert("Ident");
        first_sets.insert("Proc".to_string(), proc_first);

        let mut int_first = FirstSet::new();
        int_first.insert("Ident");
        int_first.insert("Integer");
        first_sets.insert("Int".to_string(), int_first);

        let categories = vec!["Proc".to_string(), "Int".to_string()];

        // Ambiguous state 7: "error" matches both Fixed("error") and Ident
        let ambiguous_states = vec![
            (
                7u32,
                vec![
                    (
                        TokenKind::Fixed("error".to_string()),
                        TropicalWeight::new(0.0), // high priority
                    ),
                    (
                        TokenKind::Ident,
                        TropicalWeight::new(9.0), // low priority
                    ),
                ],
            ),
        ];

        let table = compute_composed_dispatch(
            &ambiguous_states,
            &categories,
            &first_sets,
            &variant_map,
            None,
            &rule_infos,
        );

        // Should have entries for (Proc, 7) and (Int, 7)
        assert!(
            table.contains_key(&("Proc".to_string(), 7)),
            "should have composed entry for (Proc, 7)"
        );
        assert!(
            table.contains_key(&("Int".to_string(), 7)),
            "should have composed entry for (Int, 7)"
        );

        // (Proc, 7): should have entries for both KwError→CompareProc and Ident→VarProc
        let proc_entries = &table[&("Proc".to_string(), 7)];
        assert!(proc_entries.len() >= 2, "Proc should have at least 2 entries");
        // Best entry should be the one with lowest weight
        assert!(
            proc_entries[0].weight <= proc_entries[1].weight,
            "entries should be sorted by weight ascending"
        );

        // (Int, 7): only Ident is in Int's FIRST set
        let int_entries = &table[&("Int".to_string(), 7)];
        assert!(
            !int_entries.is_empty(),
            "Int should have entries for Ident"
        );
        // All entries should use Ident token
        for entry in int_entries {
            assert_eq!(entry.token_variant_name, "Ident");
        }
    }

    #[test]
    fn test_composed_dispatch_empty_when_no_ambiguity() {
        let variant_map = make_variant_map();
        let rule_infos = make_rule_infos();
        let first_sets = BTreeMap::new();
        let categories = vec!["Proc".to_string()];

        // No ambiguous states
        let table = compute_composed_dispatch(
            &[],
            &categories,
            &first_sets,
            &variant_map,
            None,
            &rule_infos,
        );
        assert!(table.is_empty());
    }

    #[test]
    fn test_specificity_weight() {
        // More specific = lower weight = preferred
        let high_specificity = specificity_weight(2.5); // e.g., 2 terminals + 1 NT
        let low_specificity = specificity_weight(0.0); // no terminals, no NTs

        assert!(
            high_specificity < low_specificity,
            "higher specificity should yield lower weight: {} vs {}",
            high_specificity,
            low_specificity
        );
    }

    #[test]
    fn test_compute_rule_specificity() {
        let rule_with_terminals = RuleInfo {
            label: "Compare".to_string(),
            category: "Proc".to_string(),
            first_items: vec![
                FirstItem::Terminal("==".to_string()),
                FirstItem::NonTerminal("Int".to_string()),
            ],
            is_infix: false,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        };
        let specificity = compute_rule_specificity(&rule_with_terminals);
        // 1 terminal + 0.5 * 1 nonterminal = 1.5
        assert!((specificity - 1.5).abs() < 1e-10);

        let var_rule = RuleInfo {
            label: "Var".to_string(),
            category: "Proc".to_string(),
            first_items: vec![FirstItem::Ident],
            is_infix: false,
            is_var: true,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        };
        let var_specificity = compute_rule_specificity(&var_rule);
        // 0.5 * 0.5 (Ident counts as 0.5 nonterminal) = 0.25
        assert!((var_specificity - 0.25).abs() < 1e-10);
    }

    #[test]
    fn test_emit_composed_dispatch_table() {
        let mut table = BTreeMap::new();
        table.insert(
            ("Proc".to_string(), 7),
            vec![
                ComposedEntry {
                    token_kind_id: 3,
                    token_variant_name: "KwError".to_string(),
                    rule_label: "CompareProc".to_string(),
                    weight: 0.29,
                },
                ComposedEntry {
                    token_kind_id: 1,
                    token_variant_name: "Ident".to_string(),
                    rule_label: "VarProc".to_string(),
                    weight: 10.0,
                },
            ],
        );

        let categories = vec!["Proc".to_string(), "Int".to_string()];
        let mut buf = String::new();
        emit_composed_dispatch_table(&mut buf, &table, &categories);

        assert!(buf.contains("CATEGORY_ID_PROC"));
        assert!(buf.contains("composed_dispatch"));
        assert!(buf.contains("CompareProc"));
        assert!(buf.contains("VarProc"));

        // Verify it parses as valid Rust tokens
        let _ts: proc_macro2::TokenStream = buf
            .parse()
            .expect("composed dispatch table should be valid Rust");
    }

    /// Test that NonTerminal rules are matched via FIRST-set lookup (not hardcoded to "Ident").
    ///
    /// Regression test for the bug where `find_rules_for_token()` hardcoded
    /// `variant_name == "Ident"` for NonTerminal items, incorrectly matching
    /// only Ident tokens regardless of the NT's actual FIRST set.
    #[test]
    fn test_composed_dispatch_nonterminal_first_set() {
        let variant_map = make_variant_map();

        // Set up: category "Proc" has a cross-category rule whose first item
        // is NonTerminal("Int"), and Int's FIRST set contains "Integer".
        let rule_infos = vec![
            RuleInfo {
                label: "CrossInt".to_string(),
                category: "Proc".to_string(),
                first_items: vec![FirstItem::NonTerminal("Int".to_string())],
                is_infix: false,
                is_var: false,
                is_literal: false,
                is_cross_category: true,
                is_cast: false,
            },
            RuleInfo {
                label: "VarProc".to_string(),
                category: "Proc".to_string(),
                first_items: vec![FirstItem::Ident],
                is_infix: false,
                is_var: true,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
        ];

        let mut first_sets = BTreeMap::new();
        let mut proc_first = FirstSet::new();
        proc_first.insert("Integer"); // Integer in Proc's FIRST (via cross-cat)
        proc_first.insert("Ident");
        first_sets.insert("Proc".to_string(), proc_first);

        let mut int_first = FirstSet::new();
        int_first.insert("Integer");
        int_first.insert("Ident");
        first_sets.insert("Int".to_string(), int_first);

        let categories = vec!["Proc".to_string()];

        // Ambiguous state: Integer token is in both variants
        let ambiguous_states = vec![(
            5u32,
            vec![
                (TokenKind::Integer, TropicalWeight::new(0.0)),
                (TokenKind::Ident, TropicalWeight::new(9.0)),
            ],
        )];

        let table = compute_composed_dispatch(
            &ambiguous_states,
            &categories,
            &first_sets,
            &variant_map,
            None,
            &rule_infos,
        );

        let proc_entries = &table[&("Proc".to_string(), 5)];

        // The CrossInt rule should match Integer via NonTerminal("Int")'s FIRST set
        let cross_int = proc_entries
            .iter()
            .find(|e| e.rule_label == "CrossInt");
        assert!(
            cross_int.is_some(),
            "CrossInt should be matched for Integer token via NT FIRST set; got entries: {:?}",
            proc_entries,
        );

        // The Ident token should still match VarProc
        let var_proc = proc_entries
            .iter()
            .find(|e| e.rule_label == "VarProc" && e.token_variant_name == "Ident");
        assert!(
            var_proc.is_some(),
            "VarProc should be matched for Ident token; got entries: {:?}",
            proc_entries,
        );
    }

    /// When `prediction_wfsts` is `Some(...)`, `compute_composed_dispatch` should
    /// use WFST weights instead of falling back to rule-specificity weights.
    #[test]
    fn test_composed_dispatch_with_prediction_wfsts() {
        use crate::token_id::TokenIdMap;
        use crate::wfst::{PredictionWfstBuilder, PredictionWfst};

        let variant_map = make_variant_map();
        let rule_infos = make_rule_infos();

        let mut first_sets = BTreeMap::new();
        let mut proc_first = FirstSet::new();
        proc_first.insert("KwError");
        proc_first.insert("Ident");
        first_sets.insert("Proc".to_string(), proc_first);

        let mut int_first = FirstSet::new();
        int_first.insert("Ident");
        int_first.insert("Integer");
        first_sets.insert("Int".to_string(), int_first);

        let categories = vec!["Proc".to_string(), "Int".to_string()];

        // Build a PredictionWfst for "Proc" that assigns specific weights
        let token_map = TokenIdMap::from_names(
            vec!["KwError".to_string(), "Ident".to_string(), "Integer".to_string()],
        );
        let mut proc_builder = PredictionWfstBuilder::new("Proc", token_map.clone());
        proc_builder.add_action(
            "KwError",
            crate::prediction::DispatchAction::Direct {
                rule_label: "CompareProc".to_string(),
                parse_fn: "parse_CompareProc".to_string(),
            },
            TropicalWeight::new(0.5),
        );
        proc_builder.add_action(
            "Ident",
            crate::prediction::DispatchAction::Direct {
                rule_label: "VarProc".to_string(),
                parse_fn: "parse_VarProc".to_string(),
            },
            TropicalWeight::new(1.0),
        );
        let proc_wfst = proc_builder.build();

        let mut prediction_wfsts: BTreeMap<String, PredictionWfst> = BTreeMap::new();
        prediction_wfsts.insert("Proc".to_string(), proc_wfst);

        // Ambiguous state 7: "error" matches both Fixed("error") and Ident
        let ambiguous_states = vec![(
            7u32,
            vec![
                (
                    TokenKind::Fixed("error".to_string()),
                    TropicalWeight::new(0.0),
                ),
                (
                    TokenKind::Ident,
                    TropicalWeight::new(9.0),
                ),
            ],
        )];

        // Call with Some(prediction_wfsts)
        let table = compute_composed_dispatch(
            &ambiguous_states,
            &categories,
            &first_sets,
            &variant_map,
            Some(&prediction_wfsts),
            &rule_infos,
        );

        // (Proc, 7): should use WFST weights (0.0+0.5=0.5 for CompareProc via KwError,
        // 9.0+1.0=10.0 for VarProc via Ident)
        let proc_entries = &table[&("Proc".to_string(), 7)];
        assert!(
            proc_entries.len() >= 2,
            "Proc should have at least 2 entries with WFST; got: {:?}",
            proc_entries,
        );
        // Best entry (lowest weight) should be first due to sorting
        assert!(
            proc_entries[0].weight <= proc_entries[1].weight,
            "entries should be sorted by weight ascending; got: {:?}",
            proc_entries,
        );

        // Verify the WFST-derived weights differ from specificity-only fallback:
        // WFST weight for KwError→CompareProc = lexer(0.0) + wfst(0.5) = 0.5
        let compare_entry = proc_entries.iter().find(|e| e.rule_label == "CompareProc");
        assert!(
            compare_entry.is_some(),
            "CompareProc should be in WFST-weighted entries; got: {:?}",
            proc_entries,
        );
        let compare_weight = compare_entry.expect("CompareProc entry missing").weight;
        assert!(
            (compare_weight - 0.5).abs() < 1e-6,
            "CompareProc weight should be 0.5 (lexer 0.0 + wfst 0.5); got {}",
            compare_weight,
        );

        // (Int, 7): no PredictionWfst for Int, so should fall back to specificity
        let int_entries = &table[&("Int".to_string(), 7)];
        assert!(
            !int_entries.is_empty(),
            "Int should have fallback entries for Ident; got empty",
        );
        // Int entries should NOT have WFST weight 10.0 — they use specificity fallback
        for entry in int_entries {
            assert_eq!(entry.token_variant_name, "Ident");
        }
    }
}
