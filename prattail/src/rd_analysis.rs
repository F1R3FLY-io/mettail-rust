//! Backend-neutral structural analyses over recursive-descent (RD) rules.
//!
//! These analyses examine `&[RDRuleInfo]` to compute facts about grammar
//! shape — dispatch grouping, NFA spillover detection, segment splits at
//! same-category nonterminal boundaries, capture-liveness analysis. The
//! results feed lint passes (W02, W10, CEK01) and pipeline diagnostics
//! (FCC, dispatch ambiguity).
//!
//! ## Why a separate module
//!
//! These functions originally lived in `prattail/src/trampoline.rs`
//! alongside the trampoline-based parser emitter. The trampoline backend
//! has been excised in favor of WPDS, but the analyses themselves are
//! **backend-neutral** — they describe rule structure, not runtime
//! behavior. Keeping them in `rd_analysis.rs` makes that independence
//! explicit and survives any future backend swap.
//!
//! ## Symbol inventory
//!
//! Rule classification: `should_use_standalone_fn`, `is_simple_collection`,
//! `has_complex_sep`, `has_guard_expression`, `has_foreign_leading_nt`.
//!
//! Dispatch grouping: `group_rd_by_dispatch_token` (private) +
//! `group_rd_by_dispatch_token_pub` (public wrapper),
//! `categories_needing_nfa_spillover`.
//!
//! Segment analysis: `HandlerSegment`, `SegmentNonTerminal`,
//! `SegmentCapture`, `split_rd_handler`, `compute_live_captures`,
//! `capture_name`, `constructor_capture_names`.

use crate::automata::codegen::terminal_to_variant_name;
use crate::grammar::ir::{CollectionKind, RDRuleInfo, RDSyntaxItem};

// ══════════════════════════════════════════════════════════════════════════════
// Rule classification
// ══════════════════════════════════════════════════════════════════════════════

/// Check if a rule is a "simple collection" — one whose elements can be
/// parsed element-by-element without standalone-fn delegation.
///
/// Complex collections (Sep rules with binders like PInputs) require their
/// standalone parse functions and are excluded.
pub(crate) fn is_simple_collection(rule: &RDRuleInfo) -> bool {
    rule.is_collection && !rule.has_binder && !rule.has_multi_binder && !has_complex_sep(rule)
}

/// Check if a rule has any Sep syntax items.
///
/// Sep rules are too complex for trampoline-style splitting and must use
/// their standalone parse functions.
pub(crate) fn has_complex_sep(rule: &RDRuleInfo) -> bool {
    rule.items
        .iter()
        .any(|item| matches!(item, RDSyntaxItem::Sep { .. }))
}

/// Check if a rule has any GuardExpression syntax items.
///
/// Guarded rules embed a sub-parser that consumes a `BehavioralPred`
/// expression. Split/frame/unwind machinery cannot meaningfully chunk a
/// guarded rule across continuation boundaries (a `BehavioralPred` is not
/// a `NonTerminal`, `Ident`, `Binder`, or `Collection`), so guarded rules
/// are routed through the standalone recursive-descent parse function
/// instead — see `recursive.rs:write_recursive_descent_body`'s
/// `RDSyntaxItem::GuardExpression` arm.
pub(crate) fn has_guard_expression(rule: &RDRuleInfo) -> bool {
    rule.items
        .iter()
        .any(|item| matches!(item, RDSyntaxItem::GuardExpression { .. }))
}

/// Check if a rule's first syntax item is a NonTerminal from a different
/// category than the rule's own category, AND the rule has more than 1
/// syntax item.
///
/// Phase 16F-0 (cross-category dispatch): rules like
/// `POutput . n:Name, p:Proc |- n "!" "(" p ")" : Proc` start by parsing
/// a foreign category (Name). These rules need standalone parse functions
/// so the speculative cross-category dispatch arm in
/// `dispatch.rs:compute_cross_cat_prefix_arms` can call them.
///
/// Single-item rules like `CastNum . a:Num |- a : Expr` are excluded
/// because they are handled by the existing cast-rule mechanism.
pub(crate) fn has_foreign_leading_nt(rule: &RDRuleInfo) -> bool {
    rule.items.len() > 1
        && matches!(
            rule.items.first(),
            Some(RDSyntaxItem::NonTerminal { category, .. })
            if category != &rule.category
        )
}

/// Check if a rule should be dispatched to its standalone parse function
/// rather than handled inline by trampoline-style splitting.
///
/// Returns true if the rule should use its standalone parse function. This
/// includes:
/// - Rules with Sep items (complex parsing logic)
/// - Rules with multi-binder items (complex binder handling)
/// - Rules with GuardExpression items (sub-parser for behavioral predicates)
/// - Rules with a foreign-category leading NonTerminal (cross-category dispatch)
pub fn should_use_standalone_fn(rule: &RDRuleInfo) -> bool {
    has_complex_sep(rule)
        || rule.has_multi_binder
        || has_guard_expression(rule)
        || has_foreign_leading_nt(rule)
}

// ══════════════════════════════════════════════════════════════════════════════
// Dispatch grouping
// ══════════════════════════════════════════════════════════════════════════════

/// Group RD rules by their dispatch token variant.
///
/// For each rule whose first non-IdentCapture item is a Terminal, this
/// returns a map from token variant → list of rules sharing that
/// dispatch token. Rules that start with a NonTerminal or IdentCapture
/// are excluded (they don't have a fixed dispatch token).
///
/// Used by lint W02/W10 (NFA ambiguous prefix detection), pipeline
/// dispatch ambiguity diagnostics, and `categories_needing_nfa_spillover`.
fn group_rd_by_dispatch_token<'a>(
    rd_rules: &'a [RDRuleInfo],
    cat: &str,
) -> std::collections::BTreeMap<String, Vec<&'a RDRuleInfo>> {
    let mut groups: std::collections::BTreeMap<String, Vec<&'a RDRuleInfo>> =
        std::collections::BTreeMap::new();

    for rd_rule in rd_rules {
        if rd_rule.category != *cat {
            continue;
        }
        if is_simple_collection(rd_rule) || rd_rule.prefix_bp.is_some() {
            continue;
        }

        // L9-3 Option A: a rule LEADING with a custom-kind capture has no fixed
        // dispatch byte (like IdentCapture / NonTerminal), so exclude it from the
        // terminal-prefix decision tree; the walker's kind gate resolves it by
        // trial (fanout-survival).
        let starts_with_nonterminal = matches!(
            rd_rule.items.first(),
            Some(RDSyntaxItem::NonTerminal { .. })
                | Some(RDSyntaxItem::IdentCapture { .. })
                | Some(RDSyntaxItem::TokenKindCapture { .. })
        );

        if starts_with_nonterminal {
            continue;
        }

        let first_terminal = rd_rule.items.iter().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item {
                Some(t.clone())
            } else {
                None
            }
        });

        if let Some(terminal) = first_terminal {
            let variant = terminal_to_variant_name(&terminal);
            groups.entry(variant).or_default().push(rd_rule);
        }
    }

    groups
}

/// Public wrapper for `group_rd_by_dispatch_token` — used by the pipeline
/// for ambiguity warning diagnostics.
pub fn group_rd_by_dispatch_token_pub<'a>(
    rd_rules: &'a [RDRuleInfo],
    cat: &str,
) -> std::collections::BTreeMap<String, Vec<&'a RDRuleInfo>> {
    group_rd_by_dispatch_token(rd_rules, cat)
}

/// Detect which categories have NFA-ambiguous prefix groups.
///
/// A category needs NFA spillover when `group_rd_by_dispatch_token()`
/// returns any group with more than one rule sharing the same dispatch
/// token. These are the categories where multiple parse alternatives
/// compete for the same prefix token (e.g., `float(x)` could be
/// `IntToFloat`, `BoolToFloat`, `StrToFloat`, or `FloatId`).
///
/// Returns a set of category names needing NFA spillover thread-locals.
pub fn categories_needing_nfa_spillover(
    rd_rules: &[RDRuleInfo],
    category_names: &[String],
) -> std::collections::HashSet<String> {
    let mut result = std::collections::HashSet::new();
    for cat in category_names {
        let rd_by_token = group_rd_by_dispatch_token(rd_rules, cat);
        for (_variant, rules) in &rd_by_token {
            if rules.len() > 1 {
                result.insert(cat.clone());
                break;
            }
        }
    }
    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Segment analysis (CEK-1 environment trimming + lint CEK01)
// ══════════════════════════════════════════════════════════════════════════════

/// One segment of an RD handler split at same-category nonterminal
/// boundaries.
///
/// Each segment contains:
/// - Inline items (terminals, ident captures, binders) to execute before
///   the nonterminal
/// - The nonterminal that triggers a "push frame + continue 'drive"
/// - Values captured from previous segments that must be saved in the frame
#[derive(Debug, Clone)]
pub struct HandlerSegment {
    /// Items to inline before the nonterminal parse (terminals, ident
    /// captures, binders).
    pub inline_items: Vec<RDSyntaxItem>,
    /// The nonterminal to parse (triggers frame push). None for the final
    /// segment.
    pub nonterminal: Option<SegmentNonTerminal>,
    /// Values captured from all prior segments that must be stored in the
    /// frame.
    pub accumulated_captures: Vec<SegmentCapture>,
    /// Frame variant name for this segment's continuation (e.g.,
    /// "RD_PInput_0").
    pub frame_variant: String,
}

/// A nonterminal parse target within an RD handler segment.
#[derive(Debug, Clone)]
pub struct SegmentNonTerminal {
    /// Category to parse (e.g., "Proc", "Name").
    pub category: String,
    /// Parameter name for the parsed result.
    pub param_name: String,
    /// Binding power for the parse call (0 for most, prefix_bp for unary
    /// prefix).
    pub bp: u8,
}

/// A captured value that must be stored in a frame variant.
#[derive(Debug, Clone)]
pub enum SegmentCapture {
    /// A parsed nonterminal result (stored as the category type).
    NonTerminal { name: String, category: String },
    /// A captured identifier string.
    Ident { name: String },
    /// A binder identifier string.
    Binder { name: String },
    /// A collection being built.
    Collection {
        name: String,
        kind: CollectionKind,
        element_category: String,
    },
    /// Phase 3A (predicated types): a behavioral predicate captured from
    /// a `?guard:Guard` slot. Stored as a `mettail_runtime::BehavioralPred`
    /// field on the frame variant.
    Guard { name: String },
}

/// Split an RD handler into segments at SAME-CATEGORY nonterminal
/// boundaries.
///
/// Only same-category nonterminals create split points (these are the
/// recursion points that need the trampoline). Cross-category nonterminals
/// are kept as inline items and handled with direct function calls
/// (bounded depth by grammar structure — no category cycles).
///
/// Algorithm:
/// 1. Walk items left to right
/// 2. Accumulate "inline" items (terminals, ident captures, binders,
///    cross-category NTs)
/// 3. When a SAME-CATEGORY NonTerminal is reached, emit a segment
/// 4. Each segment's frame variant captures all prior accumulated values
pub fn split_rd_handler(rule: &RDRuleInfo) -> Vec<HandlerSegment> {
    let mut segments: Vec<HandlerSegment> = Vec::new();
    let mut current_inline: Vec<RDSyntaxItem> = Vec::new();
    let mut accumulated_captures: Vec<SegmentCapture> = Vec::new();
    let mut segment_index = 0;

    let bp = rule.prefix_bp.unwrap_or(0);

    for item in &rule.items {
        match item {
            RDSyntaxItem::NonTerminal { category, param_name } => {
                if *category == rule.category {
                    // Same-category nonterminal: creates a split point (needs trampolining)
                    let variant_name = format!("RD_{}_{}", rule.label, segment_index);

                    segments.push(HandlerSegment {
                        inline_items: std::mem::take(&mut current_inline),
                        nonterminal: Some(SegmentNonTerminal {
                            category: category.clone(),
                            param_name: param_name.clone(),
                            bp,
                        }),
                        accumulated_captures: accumulated_captures.clone(),
                        frame_variant: variant_name,
                    });

                    // After this nonterminal is parsed, its result joins the captures
                    accumulated_captures.push(SegmentCapture::NonTerminal {
                        name: param_name.clone(),
                        category: category.clone(),
                    });
                    segment_index += 1;
                } else {
                    // Cross-category nonterminal: keep as inline item (bounded depth, direct call)
                    current_inline.push(item.clone());
                    accumulated_captures.push(SegmentCapture::NonTerminal {
                        name: param_name.clone(),
                        category: category.clone(),
                    });
                }
            },
            RDSyntaxItem::IdentCapture { param_name } => {
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Ident { name: param_name.clone() });
            },
            RDSyntaxItem::TokenKindCapture { param_name, .. } => {
                // L9-3 D-4: the captured value is just text, so reuse
                // SegmentCapture::Ident (the recovery layer only needs the name).
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Ident { name: param_name.clone() });
            },
            RDSyntaxItem::Binder { param_name, .. } => {
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Binder { name: param_name.clone() });
            },
            RDSyntaxItem::Terminal(_) => {
                current_inline.push(item.clone());
            },
            RDSyntaxItem::Collection { param_name, element_category, kind, .. } => {
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Collection {
                    name: param_name.clone(),
                    kind: *kind,
                    element_category: element_category.clone(),
                });
            },
            RDSyntaxItem::SepList {
                collection_name, element_category, kind, ..
            } => {
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Collection {
                    name: collection_name.clone(),
                    kind: *kind,
                    element_category: element_category.clone(),
                });
            },
            RDSyntaxItem::BinderCollection { param_name, .. } => {
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Binder { name: param_name.clone() });
            },
            RDSyntaxItem::GuardExpression { param_name } => {
                // Phase 3A: a `?guard:Guard` slot's parsed BehavioralPred
                // must be stored across the trampoline split so the frame
                // finalizer can construct the term.
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Guard { name: param_name.clone() });
            },
            RDSyntaxItem::Sep { .. }
            | RDSyntaxItem::Map { .. }
            | RDSyntaxItem::Zip { .. }
            | RDSyntaxItem::Optional { .. } => {
                // These complex items are kept as inline for now
                // The trampoline will handle them as-is (they have bounded depth)
                current_inline.push(item.clone());
            },
        }
    }

    // Final segment: remaining inline items + constructor (no nonterminal)
    if !current_inline.is_empty() || !accumulated_captures.is_empty() {
        segments.push(HandlerSegment {
            inline_items: current_inline,
            nonterminal: None,
            accumulated_captures,
            frame_variant: format!("RD_{}_final", rule.label),
        });
    }

    segments
}

/// CEK-1: Compute the set of live captures at each segment boundary.
///
/// Uses backward dataflow analysis: starting from the final constructor's
/// capture references, propagates liveness backward through segments.
/// A capture is live at segment i if it is referenced by any segment j > i
/// or by the final constructor.
///
/// Returns a Vec parallel to `segments` where each entry is the filtered
/// accumulated_captures for that segment.
pub fn compute_live_captures(
    segments: &[HandlerSegment],
    constructor_capture_names: &std::collections::HashSet<String>,
) -> Vec<Vec<SegmentCapture>> {
    if segments.is_empty() {
        return Vec::new();
    }

    let n = segments.len();
    let mut live_at: Vec<std::collections::HashSet<String>> =
        vec![std::collections::HashSet::new(); n];

    // Initialize: final segment's liveness = constructor capture names
    // (the final segment itself doesn't push a frame, but defines what the constructor needs)
    if n > 0 {
        live_at[n - 1] = constructor_capture_names.clone();
    }

    // Backward pass: live_at[i] = names used in segment[i+1].inline_items ∪ live_at[i+1]
    for i in (0..n.saturating_sub(1)).rev() {
        // Start with liveness from the next segment
        live_at[i] = live_at[i + 1].clone();

        // Add names referenced by the next segment's inline items
        if let Some(next_seg) = segments.get(i + 1) {
            for item in &next_seg.inline_items {
                collect_referenced_names(item, &mut live_at[i]);
            }
        }
    }

    // Filter accumulated_captures per segment
    segments
        .iter()
        .enumerate()
        .map(|(i, seg)| {
            seg.accumulated_captures
                .iter()
                .filter(|cap| live_at[i].contains(&capture_name(cap)))
                .cloned()
                .collect()
        })
        .collect()
}

/// Extract the variable name from a SegmentCapture.
pub fn capture_name(cap: &SegmentCapture) -> String {
    match cap {
        SegmentCapture::NonTerminal { name, .. } => name.clone(),
        SegmentCapture::Ident { name } => name.clone(),
        SegmentCapture::Binder { name } => name.clone(),
        SegmentCapture::Collection { name, .. } => name.clone(),
        // Guarded rules are routed through standalone fn via
        // should_use_standalone_fn, so this branch is unreachable in
        // practice. Returning the name keeps liveness analysis safe if
        // a future caller stages a Guard capture for analysis only.
        SegmentCapture::Guard { name } => name.clone(),
    }
}

/// Collect variable names referenced by an RDSyntaxItem.
fn collect_referenced_names(item: &RDSyntaxItem, names: &mut std::collections::HashSet<String>) {
    match item {
        RDSyntaxItem::NonTerminal { param_name, .. } => {
            names.insert(param_name.clone());
        },
        RDSyntaxItem::IdentCapture { param_name } => {
            names.insert(param_name.clone());
        },
        RDSyntaxItem::TokenKindCapture { param_name, .. } => {
            names.insert(param_name.clone());
        },
        RDSyntaxItem::Binder { param_name, .. } => {
            names.insert(param_name.clone());
        },
        RDSyntaxItem::Collection { param_name, .. } => {
            names.insert(param_name.clone());
        },
        RDSyntaxItem::SepList { collection_name, .. } => {
            names.insert(collection_name.clone());
        },
        RDSyntaxItem::BinderCollection { param_name, .. } => {
            names.insert(param_name.clone());
        },
        RDSyntaxItem::Terminal(_) => {},
        RDSyntaxItem::GuardExpression { param_name } => {
            names.insert(param_name.clone());
        },
        RDSyntaxItem::Sep { .. }
        | RDSyntaxItem::Map { .. }
        | RDSyntaxItem::Zip { .. }
        | RDSyntaxItem::Optional { .. } => {},
    }
}

/// CEK-1: Extract capture names referenced by the final constructor of an
/// RD rule.
///
/// The constructor uses all accumulated captures from the last segment.
/// This function returns the set of capture names that appear in the
/// rule's constructor pattern (i.e., the names that map to constructor
/// arguments).
pub fn constructor_capture_names(rule: &RDRuleInfo) -> std::collections::HashSet<String> {
    let mut names = std::collections::HashSet::new();
    for item in &rule.items {
        match item {
            RDSyntaxItem::NonTerminal { param_name, .. } => {
                names.insert(param_name.clone());
            },
            RDSyntaxItem::IdentCapture { param_name } => {
                names.insert(param_name.clone());
            },
            RDSyntaxItem::TokenKindCapture { param_name, .. } => {
                names.insert(param_name.clone());
            },
            RDSyntaxItem::Binder { param_name, .. } => {
                names.insert(param_name.clone());
            },
            RDSyntaxItem::Collection { param_name, .. } => {
                names.insert(param_name.clone());
            },
            RDSyntaxItem::SepList { collection_name, .. } => {
                names.insert(collection_name.clone());
            },
            RDSyntaxItem::BinderCollection { param_name, .. } => {
                names.insert(param_name.clone());
            },
            RDSyntaxItem::Terminal(_) => {},
            RDSyntaxItem::GuardExpression { param_name } => {
                names.insert(param_name.clone());
            },
            RDSyntaxItem::Sep { .. }
            | RDSyntaxItem::Map { .. }
            | RDSyntaxItem::Zip { .. }
            | RDSyntaxItem::Optional { .. } => {},
        }
    }
    names
}
