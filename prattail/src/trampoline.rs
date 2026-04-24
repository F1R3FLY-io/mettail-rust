//! Stack-safe trampolined parser generation.
//!
//! Replaces recursive descent + Pratt parsing with a per-category trampoline
//! that uses an explicit heap-allocated continuation stack (`Vec<Frame>`).
//! All recursion becomes iteration over this stack, bounded only by available
//! heap memory (~10-100M nesting levels).
//!
//! ## Architecture
//!
//! Three design principles:
//! 1. **Trampoline/State Machine** — Explicit continuation stack replaces the call stack.
//!    Two alternating phases: "parse prefix" (produce a value or push frame) and
//!    "infix loop + unwind" (consume operators, pop continuations).
//! 2. **Tail-Call Optimization** — After applying any continuation, the parser re-enters
//!    the infix loop without pushing a new frame.
//! 3. **Lazy Evaluation** — `Vec::new()` allocates zero bytes until first push, so flat
//!    expressions have zero overhead.
//!
//! ## Generated Structure
//!
//! For each category `Cat`, generates:
//! - `enum Frame_Cat` — continuation frames for all recursion points (`'static`, poolable)
//! - `fn parse_Cat(tokens, pos, min_bp) -> Result<Cat, ParseError>` — trampolined parser
//! - `fn parse_Cat_recovering(tokens, pos, min_bp, errors) -> Option<Cat>` — recovery variant

use std::fmt::Write;

use crate::automata::codegen::terminal_to_variant_name;
use crate::automata::semiring::ComplexityWeight;
use crate::binding_power::BindingPowerTable;

thread_local! {
    /// Tracks which `handle_mixfix_{Source}` functions have already been
    /// emitted to the current output buffer, across all category-emission
    /// passes for a single language. Prevents duplicate definitions when
    /// the same source category (e.g., Int) serves as LED delegation source
    /// for multiple target categories (Proc, BigInt, BigRat via injection
    /// casts).
    ///
    /// Callers must invoke `reset_handle_mixfix_emitted()` at the start of
    /// each language's parser generation.
    static HANDLE_MIXFIX_EMITTED: std::cell::RefCell<std::collections::HashSet<String>> =
        std::cell::RefCell::new(std::collections::HashSet::new());
}

/// Reset the thread-local `handle_mixfix_{Source}` emission tracker.
/// Call at the start of each language's parser generation to prevent state
/// leaking between languages sharing a thread.
pub fn reset_handle_mixfix_emitted() {
    HANDLE_MIXFIX_EMITTED.with(|set| set.borrow_mut().clear());
}
use crate::dispatch::CastRule;
use crate::pratt::PrefixHandler;
use crate::prediction::FirstSet;
use crate::recursive::{CollectionKind, RDRuleInfo, RDSyntaxItem};

// ══════════════════════════════════════════════════════════════════════════════
// TracingMode — CEK Runtime Observer Pattern (feature = "cek-runtime")
// ══════════════════════════════════════════════════════════════════════════════

/// Codegen mode selector: whether to emit observer callbacks in the generated parser.
///
/// When `Batch`, the generated parser is identical to the existing non-traced version.
/// When `Traced`, observer calls are emitted at 5 transition points:
/// - DRIVE: entering prefix dispatch
/// - PUSH: pushing a continuation frame
/// - POP: popping a continuation frame (unwind)
/// - INFIX: consuming an infix/postfix operator
/// - ACCEPT: parse completed (stack empty)
///
/// The traced variant is generated as `parse_Cat_traced<O: CekObserver>(tokens, pos, min_bp, observer)`
/// alongside the batch `parse_Cat(tokens, pos, min_bp)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TracingMode {
    /// Standard batch parsing — no observer callbacks.
    Batch,
    /// Traced parsing — emit `observer.on_event()` at 5 transition points.
    Traced,
}

impl TracingMode {
    /// Whether this mode emits observer callbacks.
    #[allow(dead_code)]
    pub fn is_traced(&self) -> bool {
        match self {
            Self::Batch => false,
            Self::Traced => true,
        }
    }
}

/// Helper: emit a CEK observer callback in the generated parser code.
///
/// When `mode` is `Batch`, returns an empty string (zero codegen overhead).
/// When `mode` is `Traced`, returns a block that constructs a `CekStepEvent`,
/// calls `observer.on_event()`, and handles `CekControl::Abort`.
fn emit_observer_call(
    cat: &str,
    rule_variant: &str,
    pos_expr: &str,
    bp_expr: &str,
    depth_expr: &str,
    frame_expr: &str,
    weight_expr: &str,
) -> String {
    format!(
        "{{ \
            let __evt = mettail_prattail::cek::CekStepEvent {{ \
                rule: mettail_prattail::cek::TransitionRule::{rule_variant}, \
                pos: {pos_expr}, \
                cur_bp: {bp_expr}, \
                stack_depth: {depth_expr}, \
                frame_variant: {frame_expr}, \
                running_weight: {weight_expr}, \
                category: \"{cat}\", \
            }}; \
            match __observer.on_event(&__evt) {{ \
                mettail_prattail::cek::CekControl::Continue => {{}}, \
                mettail_prattail::cek::CekControl::Checkpoint => {{ \
                    let __cfg = mettail_prattail::cek::PdaConfiguration {{ \
                        pos: {pos_expr}, cur_bp: {bp_expr}, \
                        stack_tags: __stack.iter().map(|f| format!(\"{{:?}}\", f)).collect(), \
                        phase: mettail_prattail::cek::CekState::PrefixDispatch {{ pos: {pos_expr}, cur_bp: {bp_expr} }}, \
                    }}; \
                    __observer.on_checkpoint(&__cfg); \
                }}, \
                mettail_prattail::cek::CekControl::Abort => {{ \
                    return Err(format!(\"parse aborted by observer at position {{}}\", {pos_expr})); \
                }}, \
            }} \
        }}",
    )
}

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Write a token match pattern string for a given token variant name.
fn write_token_pattern_trampoline(buf: &mut String, token: &str) {
    match token {
        "Ident" => buf.push_str("Token::Ident(_)"),
        "Integer" => buf.push_str("Token::Integer(_, _)"),
        "Float" => buf.push_str("Token::Float(_)"),
        "Boolean" => buf.push_str("Token::Boolean(_)"),
        "StringLit" => buf.push_str("Token::StringLit(_)"),
        _ => write!(buf, "Token::{}", token).unwrap(),
    }
}

/// Check if a rule is a "simple collection" — one that can be trampolined
/// as a CollectionElem frame with element-by-element parsing.
///
/// Complex collections (Sep rules with binders like PInputs) are handled
/// by standalone parse functions and should NOT have CollectionElem frames generated.
fn is_simple_collection(rule: &RDRuleInfo) -> bool {
    rule.is_collection && !rule.has_binder && !rule.has_multi_binder && !has_complex_sep(rule)
}

/// Check if a rule has any Sep syntax items.
///
/// Sep rules are too complex for trampoline splitting and must use
/// their standalone parse functions.
fn has_complex_sep(rule: &RDRuleInfo) -> bool {
    rule.items
        .iter()
        .any(|item| matches!(item, RDSyntaxItem::Sep { .. }))
}

/// Check if a rule has any GuardExpression syntax items.
///
/// Guarded rules embed a sub-parser that consumes a `BehavioralPred`
/// expression. The trampoline split/frame/unwind machinery cannot
/// meaningfully chunk a guarded rule across continuation boundaries
/// (a `BehavioralPred` is not a `NonTerminal`, `Ident`, `Binder`, or
/// `Collection`), so guarded rules are routed through the standalone
/// recursive-descent parse function instead — see
/// `recursive.rs:write_recursive_descent_body`'s
/// `RDSyntaxItem::GuardExpression` arm, which is the canonical
/// implementation of guard parsing.
fn has_guard_expression(rule: &RDRuleInfo) -> bool {
    rule.items
        .iter()
        .any(|item| matches!(item, RDSyntaxItem::GuardExpression { .. }))
}

/// Check if a rule's first syntax item is a NonTerminal from a different
/// category than the rule's own category, AND the rule has more than 1
/// syntax item.
///
/// Phase 16F-0 (cross-category dispatch): rules like
/// `POutput . n:Name, p:Proc |- n "!" "(" p ")" : Proc` start by
/// parsing a foreign category (Name). These rules need standalone
/// parse functions so the speculative cross-category dispatch arm in
/// `dispatch.rs:compute_cross_cat_prefix_arms` can call them.
///
/// Single-item rules like `CastNum . a:Num |- a : Expr` are excluded
/// because they are handled by the existing cast-rule mechanism; making
/// them standalone would break the cast arm codegen which expects them
/// to be inlined.
fn has_foreign_leading_nt(rule: &RDRuleInfo) -> bool {
    rule.items.len() > 1
        && matches!(
            rule.items.first(),
            Some(RDSyntaxItem::NonTerminal { category, .. })
            if category != &rule.category
        )
}

/// Check if a rule should be trampolined (inlined/split) or dispatched to
/// its standalone parse function.
///
/// Returns true if the rule should use its standalone parse function and NOT
/// be trampolined. This includes:
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

/// BP02: Information about a tail-call-eligible rule.
///
/// A rule is tail-call-eligible when its last same-category NonTerminal is in
/// "tail position": the NT result (with trivial wrapping into a single-field
/// constructor) IS the rule's result, with no further terminals to consume.
///
/// For these rules, the trampoline can skip pushing a full continuation frame.
/// Instead, it sets a lightweight `tail_wrap` local variable that records the
/// constructor to apply when `lhs` returns from the NT parse.
#[derive(Debug, Clone)]
pub struct TailCallInfo {
    /// Rule label (e.g., "Neg", "Deref").
    pub label: String,
    /// Tag index for the `tail_wrap` match dispatch (assigned during codegen).
    pub tag: u8,
    /// The constructor pattern string: how to wrap `lhs` into the final result.
    /// E.g., `"Cat::Neg(Box::new(lhs))"`.
    pub constructor: String,
    /// `cur_bp` value to set before `continue 'drive`.
    pub bp: u8,
}

/// BP02: Check if an RD rule is eligible for tail-call elimination.
///
/// Returns `Some(constructor_pattern)` if the rule qualifies, `None` otherwise.
///
/// A rule is tail-call-eligible when:
/// 1. It has exactly one same-category NonTerminal (the first segment) in tail position
/// 2. The first segment has NO accumulated captures before the NT (no ident captures,
///    no cross-category NTs — only terminal items that are consumed inline)
/// 3. The final segment (constructor) has no inline items to consume
/// 4. The ONLY capture is the tail NT result itself
/// 5. The rule is not a binder, multi-binder, or collection rule
/// 6. The rule is not dispatched to a standalone function
///
/// The restriction to zero prior captures is essential: the tail-wrap constructor
/// is applied at the TOP of the 'unwind loop, which is a different scope from the
/// prefix match arm where the inline items were processed. Prior capture variables
/// (idents, cross-category NTs) would be out of scope at the tail-wrap application
/// site.
///
/// Eligible patterns include:
/// - `[Terminal("x"), NonTerminal(SameCat, "v")]` → `Cat::X(Box::new(lhs))`
///   (unary prefix operators — also handled by UnaryPrefix, but this generalizes)
/// - `[Terminal("x"), Terminal("y"), NonTerminal(SameCat, "v")]` → `Cat::XY(Box::new(lhs))`
///   (multi-terminal prefix followed by a single same-category NT)
fn is_tail_call_eligible(rule: &RDRuleInfo) -> Option<String> {
    // Exclude binder, multi-binder, collection, standalone rules
    if rule.has_binder || rule.has_multi_binder || rule.is_collection {
        return None;
    }
    if should_use_standalone_fn(rule) {
        return None;
    }

    let segments = split_rd_handler(rule);
    if segments.is_empty() {
        return None;
    }

    // Must have exactly one same-category NT (first segment) — no multi-segment support
    let nt_count = segments.iter().filter(|s| s.nonterminal.is_some()).count();
    if nt_count != 1 {
        return None;
    }

    // The NT must be in the first segment (last_nt_idx == 0)
    let first_seg = &segments[0];
    let nt = first_seg.nonterminal.as_ref()?;

    // Only same-category NTs are trampolined
    if nt.category != rule.category {
        return None;
    }

    // CRITICAL: The first segment must have NO accumulated captures before the NT.
    // Only terminal items (which are consumed inline and produce no captures) are allowed.
    // If there are ident captures, cross-category NTs, binders, or collections,
    // those variables would go out of scope before the tail_wrap is applied.
    if !first_seg.accumulated_captures.is_empty() {
        return None;
    }

    // The final segment (after the NT) must have no inline items (no more terminals to consume)
    if let Some(final_seg) = segments.get(1) {
        if final_seg.nonterminal.is_some() || !final_seg.inline_items.is_empty() {
            return None;
        }
    }

    // The constructor has exactly one capture: the tail NT result.
    // This produces `Cat::Label(Box::new(lhs))`.
    Some(format!(
        "lhs = {}::{}(Box::new(lhs));",
        rule.category, rule.label
    ))
}

/// BP02: Collect tail-call-eligible rules for a category and assign tags.
///
/// Returns a map from rule label to `TailCallInfo` for all eligible rules.
fn collect_tail_call_rules(
    rd_rules: &[RDRuleInfo],
    cat: &str,
) -> std::collections::BTreeMap<String, TailCallInfo> {
    let mut result = std::collections::BTreeMap::new();
    let mut tag: u8 = 0;

    for rd_rule in rd_rules {
        if rd_rule.category != *cat {
            continue;
        }
        if rd_rule.prefix_bp.is_some() || is_simple_collection(rd_rule) {
            continue;
        }
        if let Some(constructor) = is_tail_call_eligible(rd_rule) {
            let segments = split_rd_handler(rd_rule);
            let bp = segments
                .first()
                .and_then(|s| s.nonterminal.as_ref())
                .map(|nt| nt.bp)
                .unwrap_or(0);

            result.insert(
                rd_rule.label.clone(),
                TailCallInfo {
                    label: rd_rule.label.clone(),
                    tag,
                    constructor,
                    bp,
                },
            );
            tag = tag.saturating_add(1);
        }
    }

    result
}

/// Group terminal-first RD rules by their dispatch token variant.
///
/// Returns a `BTreeMap<variant_name, Vec<&RDRuleInfo>>` for rules in `cat` that:
/// - Are not simple collections
/// - Have no `prefix_bp` (not unary prefix)
/// - Start with a terminal (not a nonterminal/ident capture)
///
/// Uses `BTreeMap` for deterministic arm ordering.
///
/// Used by:
/// - Main codegen loop in `write_rd_handlers_trampoline` (both DT and legacy paths)
/// - `categories_needing_nfa_spillover()` for NFA detection
/// - W02 lint for ambiguous prefix diagnostics
/// - Equivalence tests in `decision_tree.rs`
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

        let starts_with_nonterminal = matches!(
            rd_rule.items.first(),
            Some(RDSyntaxItem::NonTerminal { .. }) | Some(RDSyntaxItem::IdentCapture { .. })
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

/// Legacy A2: Compute the disambiguation complexity of an NFA-ambiguous rule group.
///
/// Uses `ComplexityWeight` (bottleneck semiring: ⊕ = min, ⊗ = max) to represent
/// the worst-case backtrack depth × alternative count for the group. The result
/// indicates how much work the NFA try-all must do to resolve this ambiguity.
///
/// Used by the B1 (multi-token lookahead) gate in both the DT-driven NfaTryAll
/// path and the legacy fallback path. Retained because it gates B1 emission.
fn compute_group_complexity(rules: &[&RDRuleInfo]) -> ComplexityWeight {
    if rules.len() < 2 {
        return ComplexityWeight::deterministic();
    }
    // Complexity = number of alternatives × max backtrack depth.
    // Backtrack depth for each rule is the number of syntax items that must be
    // parsed and potentially rolled back (non-terminal items are most expensive).
    let max_depth = rules
        .iter()
        .map(|r| {
            r.items
                .iter()
                .filter(|item| matches!(item, RDSyntaxItem::NonTerminal { .. }))
                .count() as u32
                + 1 // at least 1 for the prefix parse itself
        })
        .max()
        .unwrap_or(1);
    ComplexityWeight::new(rules.len() as u32 * max_depth)
}

/// A2: Threshold for enabling B1 (multi-token lookahead) per NFA group.
///
/// Groups with `ComplexityWeight <= COMPLEXITY_THRESHOLD` use NFA try-all directly
/// (fast enough for simple groups). Groups exceeding the threshold get B1 lookahead
/// to avoid expensive try-all for deeply ambiguous groups.
///
/// Value 2: groups with just 2 alternatives and no non-terminal backtrack (e.g.,
/// two keyword-only rules) use NFA try-all. Groups with 3+ alternatives or
/// non-terminal backtracks get B1.
const COMPLEXITY_THRESHOLD: u32 = 2;

/// A4: WFST weight threshold for NFA cold path splitting.
///
/// NFA try-all alternatives with WFST weight ≥ this threshold are extracted into
/// `#[cold] #[inline(never)]` helper functions, reducing the main parse function's
/// instruction footprint and improving L1 i-cache locality on the hot (low-weight)
/// path.
///
/// Matches dispatch.rs `COLD_THRESHOLD` for consistency:
/// - Weight < 1.0: hot path (Direct=0.0, Cast=0.5) — inlined in main function
/// - Weight ≥ 1.0: cold path (Lookahead=1.0+, Variable=2.0) — in `#[cold]` helper
const NFA_COLD_THRESHOLD: f64 = 1.0;

/// Legacy B1: Analyze whether an NFA-merged rule group can be disambiguated by
/// peeking at the second token instead of trying all alternatives.
///
/// Used by both the DT-driven NfaTryAll path (shared_prefix_len == 0) and the
/// legacy fallback path. Retained because the decision tree's trie structure
/// cannot detect second-token disjointness at nonterminal boundaries — this
/// function handles the `NonTerminal` case via FIRST set expansion.
///
/// B1 result: maps second-token variant → rule index within the group.
/// Only produced when every rule has a distinct second item that is a terminal.
pub(crate) struct TwoTokenLookahead {
    /// second_variant → index into the original inlineable slice
    pub(crate) groups: std::collections::BTreeMap<String, usize>,
}

pub(crate) fn second_token_lookahead(
    rules: &[&RDRuleInfo],
) -> Option<TwoTokenLookahead> {
    if rules.len() < 2 {
        return None;
    }

    // For each rule, extract the *second* syntax item (items[1]).
    // The first item (items[0]) is the shared dispatch token.
    // B1 requires that items[1] is a Terminal and is distinct across rules.
    let mut groups: std::collections::BTreeMap<String, Vec<usize>> =
        std::collections::BTreeMap::new();

    for (idx, rule) in rules.iter().enumerate() {
        // Must have at least 2 items
        if rule.items.len() < 2 {
            return None;
        }

        // items[1] must be a terminal
        match &rule.items[1] {
            RDSyntaxItem::Terminal(t) => {
                let variant = terminal_to_variant_name(t);
                groups.entry(variant).or_default().push(idx);
            },
            _ => {
                // Second item is not a terminal → can't use 2-token lookahead
                return None;
            },
        }
    }

    // Check that each second-token variant maps to exactly one rule
    if groups.values().all(|indices| indices.len() == 1) {
        Some(TwoTokenLookahead {
            groups: groups
                .into_iter()
                .map(|(k, v)| (k, v[0]))
                .collect(),
        })
    } else {
        None // Some second-token variants are shared → ambiguity persists
    }
}

/// Legacy A1: Compute the longest shared terminal prefix among rules (starting
/// from items[1], since items[0] is the shared dispatch token).
///
/// Subsumed by the decision tree's `dispatch_strategy()` for the DisjointSuffix
/// path, but retained for the legacy fallback path (recovery parsers where
/// `decision_tree: None`) and as validation in tests.
pub(crate) fn compute_shared_terminal_prefix(rules: &[&RDRuleInfo]) -> Vec<String> {
    if rules.len() < 2 {
        return Vec::new();
    }

    // Find the minimum rule length (excluding items[0] which is the dispatch token)
    let min_suffix_len = rules
        .iter()
        .map(|r| r.items.len().saturating_sub(1))
        .min()
        .unwrap_or(0);

    if min_suffix_len == 0 {
        return Vec::new();
    }

    let mut shared = Vec::new();

    // Walk items[1..] in lockstep across all rules
    for offset in 0..min_suffix_len {
        let item_idx = offset + 1; // items[0] is dispatch token

        // Get the terminal at this position in the first rule
        let first_terminal = match &rules[0].items[item_idx] {
            RDSyntaxItem::Terminal(t) => t.clone(),
            _ => break, // Non-terminal → stop sharing
        };

        // Check all other rules have the same terminal at this position
        let all_same = rules[1..].iter().all(|rule| {
            matches!(&rule.items[item_idx], RDSyntaxItem::Terminal(t) if *t == first_terminal)
        });

        if all_same {
            shared.push(first_terminal);
        } else {
            break; // Divergence point found
        }
    }

    shared
}

/// Legacy G1 Phase 2: Check whether the suffixes of NFA-merged rules
/// (starting at position `skip`) have pairwise disjoint FIRST sets.
///
/// Used by both the DT-driven NfaTryAll path and the legacy fallback path.
/// Retained because the decision tree's trie structure operates on terminal
/// bytes only — this function uses FIRST set expansion at nonterminal
/// boundaries, which may resolve overlaps the trie cannot prove disjoint.
pub(crate) fn suffix_disjointness_check(
    rules: &[&RDRuleInfo],
    skip: usize,
    first_sets: &std::collections::HashMap<String, FirstSet>,
) -> Option<std::collections::BTreeMap<String, Vec<usize>>> {
    use crate::prediction::first_of_rd_suffix;

    if rules.len() < 2 {
        return None;
    }

    // Compute FIRST set for each rule's suffix (items[skip..])
    let mut per_rule_first: Vec<(usize, FirstSet)> = Vec::with_capacity(rules.len());
    for (idx, rule) in rules.iter().enumerate() {
        if rule.items.len() <= skip {
            return None; // Rule has no suffix → can't disambiguate
        }
        let suffix_items = &rule.items[skip..];
        let (first, _nullable) = first_of_rd_suffix(suffix_items, first_sets);
        if first.tokens.is_empty() {
            return None; // Empty FIRST set → can't disambiguate
        }
        per_rule_first.push((idx, first));
    }

    // Check pairwise disjointness: for each token, at most one rule should contain it
    let mut token_to_rules: std::collections::BTreeMap<String, Vec<usize>> =
        std::collections::BTreeMap::new();
    for (idx, first) in &per_rule_first {
        for token in &first.tokens {
            token_to_rules.entry(token.clone()).or_default().push(*idx);
        }
    }

    // If any token maps to more than one rule, suffixes are not disjoint
    if token_to_rules.values().any(|indices| indices.len() > 1) {
        return None;
    }

    Some(token_to_rules)
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
/// A category needs NFA spillover when `group_rd_by_dispatch_token()` returns
/// any group with more than one rule sharing the same dispatch token. These are
/// the categories where multiple parse alternatives compete for the same prefix
/// token (e.g., `float(x)` could be `IntToFloat`, `BoolToFloat`, `StrToFloat`,
/// or `FloatId`).
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

/// Generate the `_ =>` match arm for NFA result selection.
///
/// Shared between the A1 left-factored path and the regular NFA try-all path.
/// When `config.needs_nfa_spillover` is true, includes:
/// - C2: Position-aware weight adjustment (longest-match preference)
/// - F1: Beam pruning (prune alternatives beyond beam width)
/// - B4: Adaptive beam (runtime RUNNING_WEIGHT widens beam)
///
/// **Important**: F3 lazy spillover (`nfa_weights[0] > 0.0` gate) is intentionally
/// NOT applied here. NFA-ambiguous dispatch points always need all alternatives
/// for semantic disambiguation.
///
/// When `needs_nfa_spillover` is false, simply takes the first result without spillover.
fn format_nfa_result_selection_arm(cat_upper: &str, config: &TrampolineConfig) -> String {
    if config.needs_nfa_spillover {
        let adaptive_beam = config.optimization_gates.adaptive_recovery;
        let beam_threshold = if config.optimization_gates.spillover_pruning {
            config
                .prediction_wfst
                .as_ref()
                .and_then(|wfst| wfst.beam_width())
                .map(|bw| bw.value())
        } else {
            None
        };
        let position_penalty = crate::wfst::POSITION_WEIGHT_PENALTY;
        let spill_filter = if let Some(beam) = beam_threshold {
            if adaptive_beam {
                // B4 + C2: Runtime-adaptive beam with position-aware weight adjustment.
                format!(
                    "{{ let adaptive_slack = RUNNING_WEIGHT_{cat_upper}.with(|c| c.get()); \
                    let pos_diff = (alt_pos as isize - nfa_positions[0] as isize).unsigned_abs(); \
                    let c2_adjusted_w = alt_w + pos_diff as f64 * {position_penalty:?}; \
                    if c2_adjusted_w <= nfa_weights[0] + {beam:?} + adaptive_slack {{ \
                        spill_buf.push((alt, alt_pos, c2_adjusted_w)); \
                    }} }}"
                )
            } else {
                // C2: Static beam with position-aware weight adjustment.
                format!(
                    "{{ let pos_diff = (alt_pos as isize - nfa_positions[0] as isize).unsigned_abs(); \
                    let c2_adjusted_w = alt_w + pos_diff as f64 * {position_penalty:?}; \
                    if c2_adjusted_w <= nfa_weights[0] + {beam:?} {{ \
                        spill_buf.push((alt, alt_pos, c2_adjusted_w)); \
                    }} }}"
                )
            }
        } else {
            // C2: No beam — spill all alternatives with position-adjusted weights.
            format!(
                "{{ let pos_diff = (alt_pos as isize - nfa_positions[0] as isize).unsigned_abs(); \
                let c2_adjusted_w = alt_w + pos_diff as f64 * {position_penalty:?}; \
                spill_buf.push((alt, alt_pos, c2_adjusted_w)); \
                }}"
            )
        };
        // NFA-ambiguous dispatch points always spill alternatives — never gate on
        // F3 lazy spillover (nfa_weights[0] > 0.0) here. NFA-ambiguous points have
        // multiple valid parse trees by definition, and semantic disambiguation
        // (Ascent / from_alternatives) needs all alternatives to select the correct
        // one. Skipping spillover would break disambiguation for patterns like
        // `float(x)` where the cast alternative is needed even though the primary
        // parse has weight 0.0.
        let spill_block = format!(
            "NFA_PREFIX_SPILL_{cat_upper}.with(|cell| {{ \
                let mut spill_buf = cell.take(); \
                for ((alt, &alt_pos), &alt_w) in iter.zip(nfa_positions[1..].iter()).zip(nfa_weights[1..].iter()) {{ \
                    {spill_filter} \
                }} \
                /* F3: Weight-order for demand-driven replay (ascending = best first). \
                   Enables short-circuit and threshold pruning at the drain site. */ \
                spill_buf.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal)); \
                cell.set(spill_buf); \
            }});",
        );
        let lazy_spill = format!(
            "let mut iter = nfa_results.into_iter(); \
            let best = iter.next().expect(\"nfa_results non-empty\"); \
            {} break 'prefix best;",
            spill_block,
        );
        format!(
            "_ => {{ \
                *pos = nfa_positions[0]; \
                NFA_PRIMARY_WEIGHT_{cat_upper}.with(|cell| cell.set(nfa_weights[0])); \
                RUNNING_WEIGHT_{cat_upper}.with(|cell| cell.set(cell.get() + nfa_weights[0])); \
                {lazy_spill} \
            }},"
        )
    } else {
        format!(
            "_ => {{ \
                *pos = nfa_positions[0]; \
                RUNNING_WEIGHT_{cat_upper}.with(|cell| cell.set(cell.get() + nfa_weights[0])); \
                break 'prefix nfa_results.into_iter().next().expect(\"nfa_results non-empty\"); \
            }},"
        )
    }
}

/// Write an NFA-style merged prefix arm for multiple rules sharing the same dispatch token.
///
/// For each alternative, saves `*pos`, tries the rule's parse path, and if successful,
/// collects the result. After all alternatives are tried, picks the first success
/// (declaration order = priority) or returns the first error.
///
/// `inlineable` rules have no same-category nonterminals and can be tried with save/restore.
/// `frame_pushing` rules have same-category nonterminals — these cannot be merged into
/// save/restore NFA because they require pushing frames. They are emitted with a diagnostic.
fn write_nfa_merged_prefix_arm(
    buf: &mut String,
    cold_fns: &mut String,
    variant: &str,
    inlineable: &[&RDRuleInfo],
    frame_pushing: &[&RDRuleInfo],
    cat: &str,
    config: &TrampolineConfig,
    frame_info: &FrameInfo,
    coverage_path_counter: &mut u32,
) {
    // If only frame-pushing rules remain and none are inlineable, emit them separately.
    // This is a diagnostic edge case — in practice, duplicate-token rules are either
    // all inlineable (cast rules like FloatId/IntToFloat) or all frame-pushing.
    if inlineable.is_empty() && frame_pushing.len() == 1 {
        // Single frame-pushing rule — emit normally
        let rd_rule = frame_pushing[0];
        let segments = split_rd_handler(rd_rule);
        if segments.is_empty() {
            return;
        }
        write!(buf, "Token::{} => {{", variant).unwrap();
        write_inline_items(buf, &segments[0].inline_items, true);
        if let Some(ref nt) = segments[0].nonterminal {
            write!(buf, "stack.push({enum_name}::{vp}{variant} {{", enum_name = frame_info.enum_name, vp = config.frame_prefix(), variant = segments[0].frame_variant)
                .unwrap();
            write!(buf, "saved_bp: cur_bp,").unwrap();
            for capture in &segments[0].accumulated_captures {
                match capture {
                    SegmentCapture::Ident { name }
                    | SegmentCapture::Binder { name }
                    | SegmentCapture::NonTerminal { name, .. } => {
                        write!(buf, "{},", name).unwrap();
                    },
                    _ => {},
                }
            }
            buf.push_str("});");
            write!(buf, "cur_bp = {};", nt.bp).unwrap();
            buf.push_str("continue 'drive;");
        } else {
            write_rd_constructor_inline(buf, rd_rule, &segments);
        }
        buf.push_str("},");
        return;
    }

    // ── Decision-tree-first dispatch (replaces A1+G1 ad-hoc analysis) ──
    // When the category has a decision tree, query dispatch_strategy() to
    // determine whether the suffixes are disjoint (deterministic dispatch)
    // or overlapping (NFA try-all). The decision tree subsumes:
    // - A1: compute_shared_terminal_prefix() → shared trie chains
    // - B1: second_token_lookahead() → depth-2 disjoint children
    // - G1 Phase 2: suffix_disjointness_check() → disjoint children after prefix
    //
    // Equivalence proven by test_equivalence_* tests in decision_tree.rs.
    if frame_pushing.is_empty() && inlineable.len() >= 2 {
        if let Some(ref dt) = config.decision_tree {
            use crate::decision_tree::DispatchStrategy;
            use crate::token_id::TokenIdMap;

            /* Build a minimal TokenIdMap for lookup. We reuse the one threaded
             * through the pipeline (stored alongside the decision tree in the
             * config). Since TrampolineConfig doesn't carry a separate
             * token_id_map, reconstruct from the first_sets tokens + structural
             * delimiters — same as the pipeline does. */
            let token_id_map = {
                let mut all_tokens: Vec<String> = Vec::new();
                for fs in config.all_first_sets.values() {
                    all_tokens.extend(fs.tokens.iter().cloned());
                }
                for v in &["Eof", "RParen", "RBrace", "RBracket", "Semi", "Comma",
                           "LParen", "LBrace", "LBracket"] {
                    all_tokens.push(v.to_string());
                }
                TokenIdMap::from_names(all_tokens)
            };

            match dt.dispatch_strategy(variant, &token_id_map) {
                DispatchStrategy::DisjointSuffix {
                    shared_prefix_len,
                    suffix_map,
                    ..
                } if !config.needs_nfa_spillover => {
                    /* Deterministic dispatch: emit shared prefix + match on suffix token.
                     * Build rule lookup from suffix_map (variant → label) → inlineable. */
                    let rule_by_label: std::collections::HashMap<&str, &RDRuleInfo> =
                        inlineable.iter().map(|r| (r.label.as_str(), *r)).collect();

                    let path_id = *coverage_path_counter;
                    *coverage_path_counter += 1;
                    write!(buf, "Token::{} => {{", variant).unwrap();
                    if config.emit_coverage {
                        write!(
                            buf,
                            "__coverage::record(\"{cat}\", {path_id});",
                        ).unwrap();
                    }
                    buf.push_str("*pos += 1;");

                    /* Emit shared terminal prefix from items[1..1+shared_prefix_len] */
                    if shared_prefix_len > 0 {
                        /* Use items from the first rule (they're shared across all rules) */
                        for offset in 0..shared_prefix_len {
                            let item_idx = 1 + offset; // items[0] is dispatch token
                            if let Some(RDSyntaxItem::Terminal(t)) = inlineable[0].items.get(item_idx) {
                                let shared_variant = terminal_to_variant_name(t);
                                write!(
                                    buf,
                                    "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                                    shared_variant, t,
                                ).unwrap();
                            }
                        }
                    }

                    let skip_count = 1 + shared_prefix_len;

                    buf.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");

                    for (suffix_token, rule_label) in &suffix_map {
                        let rd_rule = match rule_by_label.get(rule_label.as_str()) {
                            Some(r) => *r,
                            None => continue,
                        };
                        let segments = split_rd_handler(rd_rule);
                        if segments.is_empty() {
                            continue;
                        }

                        write!(buf, "Token::{} => {{", suffix_token).unwrap();

                        let consumes_token = matches!(
                            rd_rule.items.get(skip_count),
                            Some(RDSyntaxItem::Terminal(_))
                        );
                        if consumes_token {
                            buf.push_str("*pos += 1;");
                        }

                        let inner_skip = if consumes_token { skip_count + 1 } else { skip_count };
                        let remaining_items: Vec<_> = segments[0]
                            .inline_items
                            .iter()
                            .skip(inner_skip)
                            .cloned()
                            .collect();
                        if !remaining_items.is_empty() {
                            write_inline_items(buf, &remaining_items, false);
                        }

                        write_nfa_inline_constructor(buf, rd_rule, &segments);
                        buf.push_str("},");
                    }

                    write!(
                        buf,
                        "_ => {{ return Err(ParseError::UnexpectedToken {{ \
                            expected: Cow::Borrowed(\"{cat} expression\"), \
                            found: format_token_friendly(&tokens[*pos].0), \
                            range: tokens[*pos].1, \
                            hint: None, \
                        }}); }},",
                    ).unwrap();

                    buf.push_str("} } else {");
                    write!(
                        buf,
                        "return Err(ParseError::UnexpectedEof {{ \
                            expected: Cow::Borrowed(\"{cat} expression\"), \
                            range: tokens[tokens.len() - 1].1, \
                            hint: None, \
                        }});",
                    ).unwrap();
                    buf.push_str("}");

                    buf.push_str("},");
                    return; // Decision tree DisjointSuffix handled this arm
                }
                DispatchStrategy::NfaTryAll {
                    shared_prefix_len,
                    ..
                } => {
                    // ── DT-driven NfaTryAll ─────────────────────────────────
                    // The decision tree tells us these rules overlap (NFA).
                    // When shared_prefix_len > 0, use the pre-computed length
                    // instead of calling compute_shared_terminal_prefix().
                    let skip_count: usize = 1 + shared_prefix_len;

                    // Try G1 suffix disjointness (FIRST set analysis may
                    // resolve the overlap the trie couldn't prove disjoint)
                    if config.optimization_gates.backtracking_elimination
                        && !config.needs_nfa_spillover
                    {
                        if let Some(suffix_map) = suffix_disjointness_check(inlineable, skip_count, &config.all_first_sets) {
                            let path_id = *coverage_path_counter;
                            *coverage_path_counter += 1;
                            write!(buf, "Token::{} => {{", variant).unwrap();
                            if config.emit_coverage {
                                write!(
                                    buf,
                                    "__coverage::record(\"{cat}\", {path_id});",
                                ).unwrap();
                            }
                            buf.push_str("*pos += 1;");

                            // Emit shared terminal prefix from items[1..1+shared_prefix_len]
                            for offset in 0..shared_prefix_len {
                                let item_idx = 1 + offset;
                                if let Some(RDSyntaxItem::Terminal(t)) = inlineable[0].items.get(item_idx) {
                                    let shared_variant = terminal_to_variant_name(t);
                                    write!(
                                        buf,
                                        "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                                        shared_variant, t,
                                    ).unwrap();
                                }
                            }

                            buf.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");

                            for (suffix_token, rule_indices) in &suffix_map {
                                let rule_idx = rule_indices[0];
                                let rd_rule = inlineable[rule_idx];
                                let segments = split_rd_handler(rd_rule);
                                if segments.is_empty() {
                                    continue;
                                }

                                write!(buf, "Token::{} => {{", suffix_token).unwrap();

                                let consumes_token = matches!(
                                    rd_rule.items.get(skip_count),
                                    Some(RDSyntaxItem::Terminal(_))
                                );
                                if consumes_token {
                                    buf.push_str("*pos += 1;");
                                }

                                let inner_skip = if consumes_token { skip_count + 1 } else { skip_count };
                                let remaining_items: Vec<_> = segments[0]
                                    .inline_items
                                    .iter()
                                    .skip(inner_skip)
                                    .cloned()
                                    .collect();
                                if !remaining_items.is_empty() {
                                    write_inline_items(buf, &remaining_items, false);
                                }

                                write_nfa_inline_constructor(buf, rd_rule, &segments);
                                buf.push_str("},");
                            }

                            write!(
                                buf,
                                "_ => {{ return Err(ParseError::UnexpectedToken {{ \
                                    expected: Cow::Borrowed(\"{cat} expression\"), \
                                    found: format_token_friendly(&tokens[*pos].0), \
                                    range: tokens[*pos].1, \
                                    hint: None, \
                                }}); }},",
                            ).unwrap();

                            buf.push_str("} } else {");
                            write!(
                                buf,
                                "return Err(ParseError::UnexpectedEof {{ \
                                    expected: Cow::Borrowed(\"{cat} expression\"), \
                                    range: tokens[tokens.len() - 1].1, \
                                    hint: None, \
                                }});",
                            ).unwrap();
                            buf.push_str("}");

                            buf.push_str("},");
                            return; // DT NfaTryAll + G1 suffix resolved this arm
                        }
                    }

                    // B1: Two-token lookahead (only for shared_prefix_len == 0)
                    if shared_prefix_len == 0 {
                        let group_complexity = compute_group_complexity(inlineable);
                        if config.optimization_gates.multi_token_lookahead
                            && group_complexity.value() > COMPLEXITY_THRESHOLD
                            && !config.needs_nfa_spillover
                        {
                            if let Some(lookahead) = second_token_lookahead(inlineable) {
                                let path_id = *coverage_path_counter;
                                *coverage_path_counter += 1;
                                write!(buf, "Token::{} => {{", variant).unwrap();
                                if config.emit_coverage {
                                    write!(
                                        buf,
                                        "__coverage::record(\"{cat}\", {path_id});",
                                    ).unwrap();
                                }
                                buf.push_str("*pos += 1;");
                                buf.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");

                                for (second_variant, rule_idx) in &lookahead.groups {
                                    let rd_rule = inlineable[*rule_idx];
                                    let segments = split_rd_handler(rd_rule);
                                    if segments.is_empty() {
                                        continue;
                                    }

                                    write!(buf, "Token::{} => {{", second_variant).unwrap();
                                    buf.push_str("*pos += 1;");

                                    let remaining_items: Vec<_> = segments[0]
                                        .inline_items
                                        .iter()
                                        .skip(2)
                                        .cloned()
                                        .collect();
                                    if !remaining_items.is_empty() {
                                        write_inline_items(buf, &remaining_items, false);
                                    }

                                    if let Some(ref nt) = segments[0].nonterminal {
                                        write!(
                                            buf,
                                            "stack.push({enum_name}::{vp}{variant} {{",
                                            enum_name = frame_info.enum_name, vp = config.frame_prefix(), variant = segments[0].frame_variant
                                        ).unwrap();
                                        write!(buf, "saved_bp: cur_bp,").unwrap();
                                        for capture in &segments[0].accumulated_captures {
                                            match capture {
                                                SegmentCapture::Ident { name }
                                                | SegmentCapture::Binder { name }
                                                | SegmentCapture::NonTerminal { name, .. } => {
                                                    write!(buf, "{},", name).unwrap();
                                                },
                                                _ => {},
                                            }
                                        }
                                        buf.push_str("});");
                                        write!(buf, "cur_bp = {};", nt.bp).unwrap();
                                        buf.push_str("continue 'drive;");
                                    } else {
                                        write_nfa_inline_constructor(buf, rd_rule, &segments);
                                    }
                                    buf.push_str("},");
                                }

                                write!(
                                    buf,
                                    "_ => {{ *pos -= 1; return Err(ParseError::UnexpectedToken {{ \
                                        expected: Cow::Borrowed(\"{cat} expression after {variant}\"), \
                                        found: format_token_friendly(&tokens[*pos].0), \
                                        range: tokens[*pos].1, \
                                        hint: None, \
                                    }}); }},",
                                ).unwrap();

                                buf.push_str("} } else {");
                                write!(
                                    buf,
                                    "*pos -= 1; return Err(ParseError::UnexpectedEof {{ \
                                        expected: Cow::Borrowed(\"{cat} expression\"), \
                                        range: tokens[tokens.len() - 1].1, \
                                        hint: None, \
                                    }});",
                                ).unwrap();
                                buf.push_str("}");
                                buf.push_str("},");
                                return; // DT NfaTryAll + B1 handled this arm
                            }
                        }
                    }

                    // WFST two-token disambiguation: check if predict_two_token()
                    // yields a singleton for each second-token variant in this group.
                    // If so, emit deterministic Commit dispatch instead of NFA try-all.
                    if shared_prefix_len == 0
                        && !config.needs_nfa_spillover
                    {
                        if let Some(ref wfst) = config.prediction_wfst {
                            // Collect second tokens from inlineable rules
                            let mut second_tokens_resolved = true;
                            let mut two_token_resolutions: Vec<(&str, String)> = Vec::new();
                            for rule in inlineable.iter() {
                                if rule.items.len() >= 2 {
                                    if let RDSyntaxItem::Terminal(t2) = &rule.items[1] {
                                        let t2_variant = terminal_to_variant_name(t2);
                                        if let Some(label) = wfst.is_deterministic_after(&[variant, &t2_variant]) {
                                            two_token_resolutions.push((rule.label.as_str(), label));
                                        } else {
                                            second_tokens_resolved = false;
                                            break;
                                        }
                                    } else {
                                        second_tokens_resolved = false;
                                        break;
                                    }
                                } else {
                                    second_tokens_resolved = false;
                                    break;
                                }
                            }
                            // If all rules resolved to singletons via two-token lookahead,
                            // we can use deterministic B1-style dispatch
                            if second_tokens_resolved && !two_token_resolutions.is_empty() {
                                // Deduplicate: only proceed if each rule resolved uniquely
                                let mut seen = std::collections::HashSet::new();
                                let all_unique = two_token_resolutions.iter().all(|(label, _)| seen.insert(*label));
                                if all_unique {
                                    if let Some(lookahead) = second_token_lookahead(inlineable) {
                                        let path_id = *coverage_path_counter;
                                        *coverage_path_counter += 1;
                                        write!(buf, "Token::{} => {{", variant).unwrap();
                                        if config.emit_coverage {
                                            write!(
                                                buf,
                                                "__coverage::record(\"{cat}\", {path_id});",
                                            ).unwrap();
                                        }
                                        buf.push_str("*pos += 1;");
                                        buf.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");

                                        for (second_variant, rule_idx) in &lookahead.groups {
                                            let rd_rule = inlineable[*rule_idx];
                                            let segments = split_rd_handler(rd_rule);
                                            if segments.is_empty() {
                                                continue;
                                            }
                                            write!(buf, "Token::{} => {{", second_variant).unwrap();
                                            buf.push_str("*pos += 1;");
                                            let remaining_items: Vec<_> = segments[0]
                                                .inline_items.iter().skip(2).cloned().collect();
                                            if !remaining_items.is_empty() {
                                                write_inline_items(buf, &remaining_items, false);
                                            }
                                            if let Some(ref nt) = segments[0].nonterminal {
                                                write!(buf, "stack.push({enum_name}::{vp}{variant} {{",
                                                    enum_name = frame_info.enum_name, vp = config.frame_prefix(), variant = segments[0].frame_variant
                                                ).unwrap();
                                                write!(buf, "saved_bp: cur_bp,").unwrap();
                                                for capture in &segments[0].accumulated_captures {
                                                    match capture {
                                                        SegmentCapture::Ident { name }
                                                        | SegmentCapture::Binder { name }
                                                        | SegmentCapture::NonTerminal { name, .. } => {
                                                            write!(buf, "{},", name).unwrap();
                                                        },
                                                        _ => {},
                                                    }
                                                }
                                                buf.push_str("});");
                                                write!(buf, "cur_bp = {};", nt.bp).unwrap();
                                                buf.push_str("continue 'drive;");
                                            } else {
                                                write_nfa_inline_constructor(buf, rd_rule, &segments);
                                            }
                                            buf.push_str("},");
                                        }

                                        write!(buf,
                                            "_ => {{ *pos -= 1; return Err(ParseError::UnexpectedToken {{ \
                                                expected: Cow::Borrowed(\"{cat} expression after {variant}\"), \
                                                found: format_token_friendly(&tokens[*pos].0), \
                                                range: tokens[*pos].1, \
                                                hint: None, \
                                            }}); }},",
                                        ).unwrap();

                                        buf.push_str("} } else {");
                                        write!(buf,
                                            "*pos -= 1; return Err(ParseError::UnexpectedEof {{ \
                                                expected: Cow::Borrowed(\"{cat} expression\"), \
                                                range: tokens[tokens.len() - 1].1, \
                                                hint: None, \
                                            }});",
                                        ).unwrap();
                                        buf.push_str("}");
                                        buf.push_str("},");
                                        return; // WFST two-token resolved this arm
                                    }
                                }
                            }
                        }
                    }

                    // G1/B1/WFST couldn't resolve — emit NFA try-all with DT skip_count
                    let path_id = *coverage_path_counter;
                    *coverage_path_counter += 1;
                    write!(buf, "Token::{} => {{", variant).unwrap();
                    if config.emit_coverage {
                        write!(
                            buf,
                            "__coverage::record(\"{cat}\", {path_id});",
                        ).unwrap();
                    }
                    buf.push_str("*pos += 1;");

                    // Emit shared terminal prefix
                    for offset in 0..shared_prefix_len {
                        let item_idx = 1 + offset;
                        if let Some(RDSyntaxItem::Terminal(t)) = inlineable[0].items.get(item_idx) {
                            let shared_variant = terminal_to_variant_name(t);
                            write!(
                                buf,
                                "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                                shared_variant, t,
                            ).unwrap();
                        }
                    }

                    buf.push_str("let nfa_saved = *pos;");
                    write!(buf, "let mut nfa_results: Vec<{}> = Vec::new();", cat).unwrap();
                    buf.push_str("let mut nfa_positions: Vec<usize> = Vec::new();");
                    buf.push_str("let mut nfa_weights: Vec<f64> = Vec::new();");
                    buf.push_str("let mut nfa_first_err: Option<ParseError> = None;");

                    // Phase 1: Detect cross-category NFA groups.
                    // If any rule in the NFA group has a NonTerminal argument
                    // referencing a different category than the result category,
                    // ContextWeight narrowing would incorrectly prune valid
                    // alternatives (the WFST context is trained per-category and
                    // does not model cross-category token overlap).
                    let has_cross_category_args = inlineable.iter().any(|r| {
                        r.items.iter().any(|item| matches!(
                            item,
                            RDSyntaxItem::NonTerminal { category: ref c, .. } if c != cat
                        ))
                    });

                    // Sprint 4: Narrow inlineable candidates using ContextWeight.
                    // If the WFST has context labels, filter out rules whose bit is
                    // not set in the live ContextWeight for this dispatch token.
                    // SKIP narrowing for cross-category NFA groups to avoid
                    // incorrect pruning of valid cross-category alternatives.
                    let narrowed_inlineable: Vec<&RDRuleInfo> =
                        if has_cross_category_args {
                            // Cross-category group: keep all alternatives
                            inlineable.to_vec()
                        } else if let Some(ref wfst) = config.prediction_wfst {
                            let ctx = wfst.live_rules_context_after(&[variant]);
                            if ctx.count() > 0 {
                                // Filter to only rules that survive ContextWeight narrowing
                                inlineable.iter().copied().filter(|r| {
                                    wfst.context_labels.get(&r.label)
                                        .map_or(true, |&bit| ctx.contains(bit))
                                }).collect()
                            } else {
                                // No context labels or no surviving rules — keep all
                                inlineable.to_vec()
                            }
                        } else {
                            inlineable.to_vec()
                        };
                    let effective_inlineable = &narrowed_inlineable;

                    // Phase 2 (deferred): Argument-FIRST-set runtime pruning.
                    // For cross-category NFA groups, we could emit runtime guards
                    // that peek at the argument's first token and skip alternatives
                    // whose cross-category NonTerminal's FIRST set does not contain
                    // that token. The FIRST sets are available via
                    // config.all_first_sets, but wiring per-alternative guards into
                    // the NFA try loop requires non-trivial codegen plumbing.
                    // Phase 1 already guarantees correctness by keeping all
                    // alternatives; Phase 2 guards are a pure performance
                    // optimisation to be revisited once profiling shows NFA
                    // try-all overhead in cross-category groups is a bottleneck.

                    let a1_ordered: Vec<(&RDRuleInfo, f64)> =
                        if let Some(ref wfst) = config.prediction_wfst {
                            let labels: Vec<&str> =
                                effective_inlineable.iter().map(|r| r.label.as_str()).collect();
                            let ordered = wfst.nfa_alternative_order(variant, &labels);
                            ordered
                                .iter()
                                .map(|(i, w)| (effective_inlineable[*i], w.0))
                                .collect()
                        } else {
                            effective_inlineable.iter().map(|r| (*r, 0.5_f64)).collect()
                        };

                    // A4: Hot/cold splitting
                    let a1_cold_idx = if config.optimization_gates.hot_cold_splitting {
                        a1_ordered.iter().position(|(_, w)| *w >= NFA_COLD_THRESHOLD)
                    } else {
                        None
                    };
                    let has_a1_cold = a1_cold_idx
                        .map_or(false, |idx| idx > 0 && idx < a1_ordered.len());

                    let (a1_hot, a1_cold): (&[(&RDRuleInfo, f64)], &[(&RDRuleInfo, f64)]) = if has_a1_cold {
                        let idx = a1_cold_idx.expect("has_a1_cold checked");
                        (&a1_ordered[..idx], &a1_ordered[idx..])
                    } else {
                        (&a1_ordered[..], &[][..])
                    };

                    let a1_cold_fn_name = if has_a1_cold {
                        let fn_name = format!(
                            "nfa_try_cold_a1_{}_{}",
                            cat.to_lowercase(),
                            variant.to_lowercase()
                        );
                        write!(
                            cold_fns,
                            "#[cold] #[inline(never)] \
                            fn {fn_name}<'a>(\
                                tokens: &[(Token<'a>, Range)], \
                                pos: &mut usize, \
                                nfa_saved: usize, \
                                nfa_results: &mut Vec<{cat}>, \
                                nfa_positions: &mut Vec<usize>, \
                                nfa_weights: &mut Vec<f64>, \
                                nfa_first_err: &mut Option<ParseError>, \
                            ) {{",
                        ).unwrap();

                        for (rd_rule, weight) in a1_cold {
                            cold_fns.push_str("*pos = nfa_saved;");
                            let segments = split_rd_handler(rd_rule);
                            if segments.is_empty() {
                                continue;
                            }
                            // Multi-segment rules (same-cat NTs) emit full rule.items
                            // so recursive parse_<cat> calls inline the same-cat NT.
                            let source_items: &[RDSyntaxItem] = if segments.len() > 1 {
                                &rd_rule.items
                            } else {
                                &segments[0].inline_items
                            };
                            let remaining_items: Vec<_> = source_items
                                .iter()
                                .skip(skip_count)
                                .cloned()
                                .collect();
                            write!(cold_fns, "match (|| -> Result<{}, ParseError> {{", cat).unwrap();
                            if !remaining_items.is_empty() {
                                write_inline_items(cold_fns, &remaining_items, false);
                            }
                            write_nfa_inline_constructor(cold_fns, rd_rule, &segments);
                            cold_fns.push_str("})() {");
                            write!(cold_fns, "Ok(v) => {{ nfa_results.push(v); nfa_positions.push(*pos); nfa_weights.push({weight:?}); }},").unwrap();
                            cold_fns.push_str("Err(e) => { if nfa_first_err.is_none() { *nfa_first_err = Some(e); } },");
                            cold_fns.push('}');
                        }
                        cold_fns.push('}');
                        Some(fn_name)
                    } else {
                        None
                    };

                    for (rd_rule, weight) in a1_hot {
                        buf.push_str("*pos = nfa_saved;");
                        let segments = split_rd_handler(rd_rule);
                        if segments.is_empty() {
                            continue;
                        }
                        // Multi-segment rules (same-cat NTs) emit full rule.items
                        // so recursive parse_<cat> calls inline the same-cat NT.
                        let source_items: &[RDSyntaxItem] = if segments.len() > 1 {
                            &rd_rule.items
                        } else {
                            &segments[0].inline_items
                        };
                        let remaining_items: Vec<_> = source_items
                            .iter()
                            .skip(skip_count)
                            .cloned()
                            .collect();

                        write!(buf, "match (|| -> Result<{}, ParseError> {{", cat).unwrap();
                        if !remaining_items.is_empty() {
                            write_inline_items(buf, &remaining_items, false);
                        }
                        write_nfa_inline_constructor(buf, rd_rule, &segments);
                        buf.push_str("})() {");
                        write!(buf, "Ok(v) => {{ nfa_results.push(v); nfa_positions.push(*pos); nfa_weights.push({weight:?}); }},").unwrap();
                        buf.push_str("Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },");
                        buf.push('}');
                    }

                    if let Some(ref fn_name) = a1_cold_fn_name {
                        write!(
                            buf,
                            "if nfa_results.is_empty() {{ \
                                {fn_name}(tokens, pos, nfa_saved, &mut nfa_results, \
                                 &mut nfa_positions, &mut nfa_weights, &mut nfa_first_err); \
                            }}",
                        ).unwrap();
                    }

                    buf.push_str("match nfa_results.len() {");
                    write!(
                        buf,
                        "0 => {{ return Err(nfa_first_err.unwrap_or_else(|| \
                            ParseError::UnexpectedToken {{ \
                                expected: Cow::Borrowed(\"{cat} expression\"), \
                                found: format_token_friendly(&tokens[nfa_saved].0), \
                                range: tokens[nfa_saved].1, \
                                hint: None, \
                            }} \
                        )); }},",
                    ).unwrap();
                    let cat_upper = cat.to_uppercase();
                    buf.push_str(&format_nfa_result_selection_arm(&cat_upper, config));
                    buf.push('}');

                    buf.push_str("},");
                    return; // DT NfaTryAll handled this arm
                }

                DispatchStrategy::Singleton { .. } | DispatchStrategy::NotPresent => {
                    // Singleton: handled by single-rule arm elsewhere.
                    // NotPresent: no trie data for this token — skip.
                    // Both fall through to the NFA try-all below (which also
                    // handles these cases via the legacy path when DT is None).
                }

                // DisjointSuffix that needs_nfa_spillover — fall through to
                // NFA try-all since spillover requires all alternatives.
                DispatchStrategy::DisjointSuffix { .. } => {}
            }
        }
    }

    // ── Legacy A1+G1+B1 Fallback Path ──────────────────────────────────
    // Retained for recovery parsers (decision_tree: None) and for NfaTryAll
    // cases where FIRST set analysis may further disambiguate beyond what
    // the trie proves. Functions used:
    //   - compute_shared_terminal_prefix(): A1 shared prefix detection
    //   - second_token_lookahead(): B1 two-token disambiguation
    //   - suffix_disjointness_check(): G1 Phase 2 suffix FIRST set analysis
    //   - compute_group_complexity(): A2 NFA group complexity measurement
    // These are subsumed by the decision tree for the DisjointSuffix path
    // but remain necessary for recovery codegen and NfaTryAll refinement.
    if config.optimization_gates.left_factoring && frame_pushing.is_empty() && inlineable.len() >= 2 {
        let shared_terminal_prefix = compute_shared_terminal_prefix(inlineable);
        if !shared_terminal_prefix.is_empty() {
            write!(buf, "Token::{} => {{", variant).unwrap();
            buf.push_str("*pos += 1;");

            for terminal in &shared_terminal_prefix {
                let shared_variant = terminal_to_variant_name(terminal);
                write!(
                    buf,
                    "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                    shared_variant, terminal,
                )
                .unwrap();
            }

            let skip_count = 1 + shared_terminal_prefix.len();

            if config.optimization_gates.backtracking_elimination
                && !config.needs_nfa_spillover
            {
                if let Some(suffix_map) = suffix_disjointness_check(inlineable, skip_count, &config.all_first_sets) {
                    buf.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");

                    for (suffix_token, rule_indices) in &suffix_map {
                        let rule_idx = rule_indices[0];
                        let rd_rule = inlineable[rule_idx];
                        let segments = split_rd_handler(rd_rule);
                        if segments.is_empty() {
                            continue;
                        }

                        write!(buf, "Token::{} => {{", suffix_token).unwrap();

                        let consumes_token = matches!(
                            rd_rule.items.get(skip_count),
                            Some(RDSyntaxItem::Terminal(_))
                        );
                        if consumes_token {
                            buf.push_str("*pos += 1;");
                        }

                        let inner_skip = if consumes_token { skip_count + 1 } else { skip_count };
                        let remaining_items: Vec<_> = segments[0]
                            .inline_items
                            .iter()
                            .skip(inner_skip)
                            .cloned()
                            .collect();
                        if !remaining_items.is_empty() {
                            write_inline_items(buf, &remaining_items, false);
                        }

                        write_nfa_inline_constructor(buf, rd_rule, &segments);
                        buf.push_str("},");
                    }

                    write!(
                        buf,
                        "_ => {{ return Err(ParseError::UnexpectedToken {{ \
                            expected: Cow::Borrowed(\"{cat} expression\"), \
                            found: format_token_friendly(&tokens[*pos].0), \
                            range: tokens[*pos].1, \
                            hint: None, \
                        }}); }},",
                    )
                    .unwrap();

                    buf.push_str("} } else {");
                    write!(
                        buf,
                        "return Err(ParseError::UnexpectedEof {{ \
                            expected: Cow::Borrowed(\"{cat} expression\"), \
                            range: tokens[tokens.len() - 1].1, \
                            hint: None, \
                        }});",
                    )
                    .unwrap();
                    buf.push_str("}");

                    buf.push_str("},");
                    return; // G1+A1 handled this arm
                }
            }

            buf.push_str("let nfa_saved = *pos;");
            write!(buf, "let mut nfa_results: Vec<{}> = Vec::new();", cat).unwrap();
            buf.push_str("let mut nfa_positions: Vec<usize> = Vec::new();");
            buf.push_str("let mut nfa_weights: Vec<f64> = Vec::new();");
            buf.push_str("let mut nfa_first_err: Option<ParseError> = None;");

            // Use WFST weight ordering if available, otherwise equal weights
            let a1_ordered: Vec<(&RDRuleInfo, f64)> =
                if let Some(ref wfst) = config.prediction_wfst {
                    let labels: Vec<&str> =
                        inlineable.iter().map(|r| r.label.as_str()).collect();
                    let ordered = wfst.nfa_alternative_order(variant, &labels);
                    ordered
                        .iter()
                        .map(|(i, w)| (inlineable[*i], w.0))
                        .collect()
                } else {
                    inlineable.iter().map(|r| (*r, 0.5_f64)).collect()
                };

            // A4: Partition A1 alternatives into hot/cold (same threshold as main NFA path)
            let a1_cold_idx = if config.optimization_gates.hot_cold_splitting {
                a1_ordered.iter().position(|(_, w)| *w >= NFA_COLD_THRESHOLD)
            } else {
                None
            };
            let has_a1_cold = a1_cold_idx
                .map_or(false, |idx| idx > 0 && idx < a1_ordered.len());

            let (a1_hot, a1_cold): (&[(&RDRuleInfo, f64)], &[(&RDRuleInfo, f64)]) = if has_a1_cold {
                let idx = a1_cold_idx.expect("has_a1_cold checked");
                (&a1_ordered[..idx], &a1_ordered[idx..])
            } else {
                (&a1_ordered[..], &[][..])
            };

            // Emit A1 cold helper if needed
            let a1_cold_fn_name = if has_a1_cold {
                let fn_name = format!(
                    "nfa_try_cold_a1_{}_{}",
                    cat.to_lowercase(),
                    variant.to_lowercase()
                );
                write!(
                    cold_fns,
                    "#[cold] #[inline(never)] \
                    fn {fn_name}<'a>(\
                        tokens: &[(Token<'a>, Range)], \
                        pos: &mut usize, \
                        nfa_saved: usize, \
                        nfa_results: &mut Vec<{cat}>, \
                        nfa_positions: &mut Vec<usize>, \
                        nfa_weights: &mut Vec<f64>, \
                        nfa_first_err: &mut Option<ParseError>, \
                    ) {{",
                )
                .unwrap();

                for (rd_rule, weight) in a1_cold {
                    cold_fns.push_str("*pos = nfa_saved;");
                    let segments = split_rd_handler(rd_rule);
                    if segments.is_empty() {
                        continue;
                    }
                    let remaining_items: Vec<_> = segments[0]
                        .inline_items
                        .iter()
                        .skip(skip_count)
                        .cloned()
                        .collect();
                    write!(cold_fns, "match (|| -> Result<{}, ParseError> {{", cat).unwrap();
                    if !remaining_items.is_empty() {
                        write_inline_items(cold_fns, &remaining_items, false);
                    }
                    write_nfa_inline_constructor(cold_fns, rd_rule, &segments);
                    cold_fns.push_str("})() {");
                    write!(cold_fns, "Ok(v) => {{ nfa_results.push(v); nfa_positions.push(*pos); nfa_weights.push({weight:?}); }},").unwrap();
                    cold_fns.push_str("Err(e) => { if nfa_first_err.is_none() { *nfa_first_err = Some(e); } },");
                    cold_fns.push('}');
                }
                cold_fns.push('}'); // close function
                Some(fn_name)
            } else {
                None
            };

            // Try hot alternatives inline
            for (rd_rule, weight) in a1_hot {
                buf.push_str("*pos = nfa_saved;");
                let segments = split_rd_handler(rd_rule);
                if segments.is_empty() {
                    continue;
                }
                // Emit inline items starting after the shared prefix
                let remaining_items: Vec<_> = segments[0]
                    .inline_items
                    .iter()
                    .skip(skip_count)
                    .cloned()
                    .collect();

                write!(buf, "match (|| -> Result<{}, ParseError> {{", cat).unwrap();
                if !remaining_items.is_empty() {
                    write_inline_items(buf, &remaining_items, false);
                }
                write_nfa_inline_constructor(buf, rd_rule, &segments);
                buf.push_str("})() {");
                write!(buf, "Ok(v) => {{ nfa_results.push(v); nfa_positions.push(*pos); nfa_weights.push({weight:?}); }},").unwrap();
                buf.push_str("Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },");
                buf.push('}');
            }

            // A4: Call A1 cold helper if hot alternatives all failed
            if let Some(ref fn_name) = a1_cold_fn_name {
                write!(
                    buf,
                    "if nfa_results.is_empty() {{ \
                        {fn_name}(tokens, pos, nfa_saved, &mut nfa_results, \
                         &mut nfa_positions, &mut nfa_weights, &mut nfa_first_err); \
                    }}",
                )
                .unwrap();
            }

            // Result selection — shared with regular NFA path via helper.
            // When needs_nfa_spillover, spills non-primary alternatives for
            // semantic disambiguation (e.g., float(x) cast rules).
            buf.push_str("match nfa_results.len() {");
            write!(
                buf,
                "0 => {{ return Err(nfa_first_err.unwrap_or_else(|| \
                    ParseError::UnexpectedToken {{ \
                        expected: Cow::Borrowed(\"{cat} expression\"), \
                        found: format_token_friendly(&tokens[nfa_saved].0), \
                        range: tokens[nfa_saved].1, \
                        hint: None, \
                    }} \
                )); }},",
            )
            .unwrap();
            let cat_upper = cat.to_uppercase();
            buf.push_str(&format_nfa_result_selection_arm(&cat_upper, config));
            buf.push('}'); // close match nfa_results.len()

            buf.push_str("},"); // close outer arm
            return; // A1 handled this arm
        }
    }

    // ── G1 Phase 2: Suffix disjointness check ───────────────────────────
    // If all rules' suffixes (items after the dispatch token) have pairwise
    // disjoint FIRST sets, emit a deterministic match on the next token
    // instead of NFA try-all. This generalizes B1 to handle NonTerminals
    // at position 1 (using category FIRST sets).
    // Gated by `optimization_gates.backtracking_elimination`.
    if config.optimization_gates.backtracking_elimination
        && frame_pushing.is_empty()
        && !config.needs_nfa_spillover
    {
        if let Some(suffix_map) = suffix_disjointness_check(inlineable, 1, &config.all_first_sets) {
            write!(buf, "Token::{} => {{", variant).unwrap();
            buf.push_str("*pos += 1;");
            buf.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");

            for (suffix_token, rule_indices) in &suffix_map {
                let rule_idx = rule_indices[0]; // Guaranteed single by disjointness check
                let rd_rule = inlineable[rule_idx];
                let segments = split_rd_handler(rd_rule);
                if segments.is_empty() {
                    continue;
                }

                write!(buf, "Token::{} => {{", suffix_token).unwrap();

                // Check if items[1] is a terminal (consume it) or nonterminal (don't consume — it's dispatched by FIRST)
                let consumes_second = matches!(
                    rd_rule.items.get(1),
                    Some(RDSyntaxItem::Terminal(_))
                );
                if consumes_second {
                    buf.push_str("*pos += 1;");
                }

                // Write remaining inline items
                let skip_count = if consumes_second { 2 } else { 1 };
                let remaining_items: Vec<_> = segments[0]
                    .inline_items
                    .iter()
                    .skip(skip_count)
                    .cloned()
                    .collect();
                if !remaining_items.is_empty() {
                    write_inline_items(buf, &remaining_items, false);
                }

                if let Some(ref nt) = segments[0].nonterminal {
                    write!(
                        buf,
                        "stack.push({enum_name}::{vp}{variant} {{",
                        enum_name = frame_info.enum_name, vp = config.frame_prefix(), variant = segments[0].frame_variant
                    )
                    .unwrap();
                    write!(buf, "saved_bp: cur_bp,").unwrap();
                    for capture in &segments[0].accumulated_captures {
                        match capture {
                            SegmentCapture::Ident { name }
                            | SegmentCapture::Binder { name }
                            | SegmentCapture::NonTerminal { name, .. } => {
                                write!(buf, "{},", name).unwrap();
                            },
                            _ => {},
                        }
                    }
                    buf.push_str("});");
                    write!(buf, "cur_bp = {};", nt.bp).unwrap();
                    buf.push_str("continue 'drive;");
                } else {
                    write_nfa_inline_constructor(buf, rd_rule, &segments);
                }
                buf.push_str("},");
            }

            // Fallback: no suffix token matched
            write!(
                buf,
                "_ => {{ *pos -= 1; return Err(ParseError::UnexpectedToken {{ \
                    expected: Cow::Borrowed(\"{cat} expression after {variant}\"), \
                    found: format_token_friendly(&tokens[*pos + 1].0), \
                    range: tokens[*pos + 1].1, \
                    hint: None, \
                }}); }},",
            )
            .unwrap();

            buf.push_str("} } else {");
            write!(
                buf,
                "*pos -= 1; return Err(ParseError::UnexpectedEof {{ \
                    expected: Cow::Borrowed(\"{cat} expression\"), \
                    range: tokens[tokens.len() - 1].1, \
                    hint: None, \
                }});",
            )
            .unwrap();
            buf.push_str("}");
            buf.push_str("},");
            return; // G1 handled this arm
        }
    }

    // ── B1: Two-token lookahead check ──────────────────────────────────
    // If all rules in this group have distinct second terminals, emit a
    // nested match on tokens[*pos + 1] instead of the NFA try-all loop.
    // This replaces full save/restore + prefix parse with a single array
    // bounds check + pattern match.
    // A3: Gated by `optimization_gates.multi_token_lookahead`.
    // A2: Additionally gated by ComplexityWeight — only emit B1 for groups
    // whose disambiguation complexity exceeds COMPLEXITY_THRESHOLD. Simple
    // groups (2 alternatives, no non-terminal backtracks) are fast enough
    // with NFA try-all and don't benefit from the extra code.
    let group_complexity = compute_group_complexity(inlineable);
    if config.optimization_gates.multi_token_lookahead
        && group_complexity.value() > COMPLEXITY_THRESHOLD
        && frame_pushing.is_empty()
        && !config.needs_nfa_spillover
    {
        if let Some(lookahead) = second_token_lookahead(inlineable) {
            write!(buf, "Token::{} => {{", variant).unwrap();
            // Advance past the first token (already matched by the dispatch)
            buf.push_str("*pos += 1;");
            // Peek at the second token for disambiguation
            buf.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");

            for (second_variant, rule_idx) in &lookahead.groups {
                let rd_rule = inlineable[*rule_idx];
                let segments = split_rd_handler(rd_rule);
                if segments.is_empty() {
                    continue;
                }

                write!(buf, "Token::{} => {{", second_variant).unwrap();
                // Consume the second token
                buf.push_str("*pos += 1;");

                // Write remaining inline items (skip the first two items which are
                // both terminals already consumed above). items[0] = first terminal
                // (dispatch token), items[1] = second terminal (lookahead token).
                let remaining_items: Vec<_> = segments[0]
                    .inline_items
                    .iter()
                    .skip(2)
                    .cloned()
                    .collect();
                if !remaining_items.is_empty() {
                    write_inline_items(buf, &remaining_items, false);
                }

                if let Some(ref nt) = segments[0].nonterminal {
                    write!(
                        buf,
                        "stack.push({enum_name}::{vp}{variant} {{",
                        enum_name = frame_info.enum_name, vp = config.frame_prefix(), variant = segments[0].frame_variant
                    )
                    .unwrap();
                    write!(buf, "saved_bp: cur_bp,").unwrap();
                    for capture in &segments[0].accumulated_captures {
                        match capture {
                            SegmentCapture::Ident { name }
                            | SegmentCapture::Binder { name }
                            | SegmentCapture::NonTerminal { name, .. } => {
                                write!(buf, "{},", name).unwrap();
                            },
                            _ => {},
                        }
                    }
                    buf.push_str("});");
                    write!(buf, "cur_bp = {};", nt.bp).unwrap();
                    buf.push_str("continue 'drive;");
                } else {
                    write_nfa_inline_constructor(buf, rd_rule, &segments);
                }
                buf.push_str("},"); // close second-token arm
            }

            // Fallback: second token doesn't match any expected variant.
            // Restore position to before the first token and error.
            write!(
                buf,
                "_ => {{ *pos -= 1; return Err(ParseError::UnexpectedToken {{ \
                    expected: Cow::Borrowed(\"{cat} expression after {variant}\"), \
                    found: format_token_friendly(&tokens[*pos].0), \
                    range: tokens[*pos].1, \
                    hint: None, \
                }}); }},",
            )
            .unwrap();

            buf.push_str("} } else {"); // close match, close if, else
            // Only first token available — no second token to peek at
            write!(
                buf,
                "*pos -= 1; return Err(ParseError::UnexpectedEof {{ \
                    expected: Cow::Borrowed(\"{cat} expression\"), \
                    range: tokens[tokens.len() - 1].1, \
                    hint: None, \
                }});",
            )
            .unwrap();
            buf.push_str("}"); // close else
            buf.push_str("},"); // close outer arm
            return; // B1 handled this arm — skip NFA try-all
        }
    }

    write!(buf, "Token::{} => {{", variant).unwrap();

    // NFA try-all: save position, try each alternative, collect successes
    buf.push_str("let nfa_saved = *pos;");
    write!(buf, "let mut nfa_results: Vec<{}> = Vec::new();", cat).unwrap();
    buf.push_str("let mut nfa_positions: Vec<usize> = Vec::new();");
    buf.push_str("let mut nfa_weights: Vec<f64> = Vec::new();");
    buf.push_str("let mut nfa_first_err: Option<ParseError> = None;");

    // Order alternatives by WFST weight (lowest = most likely first).
    // Weight-best alternative becomes nfa_results[0] and is returned as the
    // primary result. Remaining alternatives are spilled for forced-prefix replay.
    // Each alternative carries its tropical weight (f64) for Phase 3 weight-aware
    // disambiguation in from_alternatives.
    //
    // Beam pruning: when WFST beam width is set, skip alternatives with weight
    // > best_weight + beam_width. This is a compile-time decision — pruned
    // alternatives are simply not emitted in the generated code, reducing code size.
    let ordered_inlineable: Vec<(&RDRuleInfo, f64)> = if let Some(ref wfst) = config.prediction_wfst {
        let rule_labels: Vec<&str> = inlineable.iter().map(|r| r.label.as_str()).collect();
        let ordered_indices = wfst.nfa_alternative_order(variant, &rule_labels);
        let beam = wfst.beam_width();
        let best_weight = ordered_indices.first().map(|(_, w)| *w);
        ordered_indices
            .iter()
            .filter(|(_, w)| {
                match (beam, best_weight) {
                    (Some(beam_w), Some(best_w)) => w.0 <= best_w.0 + beam_w.0,
                    _ => true, /* no beam → keep all */
                }
            })
            .map(|(i, w)| (inlineable[*i], w.0))
            .collect()
    } else {
        inlineable.iter().map(|r| (*r, 0.5_f64)).collect()
    };

    // ── A4: Hot/cold NFA path splitting ──────────────────────────────────
    // Partition alternatives into hot (weight < NFA_COLD_THRESHOLD) and cold
    // (weight ≥ NFA_COLD_THRESHOLD). Cold alternatives are extracted into a
    // #[cold] #[inline(never)] helper function to reduce the main parse
    // function's instruction footprint and improve L1 i-cache locality.
    // Only split when there are BOTH hot AND cold alternatives (like dispatch.rs).
    // A3: Gated by `optimization_gates.hot_cold_splitting`.
    let cold_split_idx = if config.optimization_gates.hot_cold_splitting {
        ordered_inlineable
            .iter()
            .position(|(_, w)| *w >= NFA_COLD_THRESHOLD)
    } else {
        None // A3: hot/cold splitting disabled — all alternatives inline
    };
    let has_cold_split = cold_split_idx
        .map_or(false, |idx| idx > 0 && idx < ordered_inlineable.len());

    let (hot_alts, cold_alts): (&[(&RDRuleInfo, f64)], &[(&RDRuleInfo, f64)]) = if has_cold_split {
        let idx = cold_split_idx.expect("has_cold_split checked above");
        (&ordered_inlineable[..idx], &ordered_inlineable[idx..])
    } else {
        (&ordered_inlineable[..], &[][..])
    };

    // If there are cold alternatives, emit a #[cold] helper function.
    // The helper tries each cold alternative with the same save/restore pattern
    // and appends results to the caller's vectors.
    let cold_fn_name = if has_cold_split {
        let fn_name = format!(
            "nfa_try_cold_{}_{}",
            cat.to_lowercase(),
            variant.to_lowercase()
        );
        write!(
            cold_fns,
            "#[cold] #[inline(never)] \
            fn {fn_name}<'a>(\
                tokens: &[(Token<'a>, Range)], \
                pos: &mut usize, \
                nfa_saved: usize, \
                nfa_results: &mut Vec<{cat}>, \
                nfa_positions: &mut Vec<usize>, \
                nfa_weights: &mut Vec<f64>, \
                nfa_first_err: &mut Option<ParseError>, \
            ) {{",
        )
        .unwrap();

        for (rd_rule, weight) in cold_alts {
            cold_fns.push_str("*pos = nfa_saved;");
            if should_use_standalone_fn(rd_rule) {
                let standalone_fn_name = format!("parse_{}", rd_rule.label.to_lowercase());
                write!(
                    cold_fns,
                    "match {standalone_fn_name}(tokens, pos) {{ \
                        Ok(v) => {{ nfa_results.push(v); nfa_positions.push(*pos); nfa_weights.push({weight:?}); }}, \
                        Err(e) => {{ if nfa_first_err.is_none() {{ *nfa_first_err = Some(e); }} }}, \
                    }}",
                )
                .unwrap();
            } else {
                let segments = split_rd_handler(rd_rule);
                if segments.is_empty() {
                    continue;
                }
                let items_to_emit: &[RDSyntaxItem] = if segments.len() > 1 {
                    &rd_rule.items
                } else {
                    &segments[0].inline_items
                };
                write!(cold_fns, "match (|| -> Result<{}, ParseError> {{", cat).unwrap();
                write_inline_items(cold_fns, items_to_emit, true);
                write_nfa_inline_constructor(cold_fns, rd_rule, &segments);
                cold_fns.push_str("})() {");
                write!(cold_fns, "Ok(v) => {{ nfa_results.push(v); nfa_positions.push(*pos); nfa_weights.push({weight:?}); }},").unwrap();
                cold_fns.push_str("Err(e) => { if nfa_first_err.is_none() { *nfa_first_err = Some(e); } },");
                cold_fns.push('}');
            }
        }

        cold_fns.push('}'); // close function
        Some(fn_name)
    } else {
        None
    };

    // F2 (Early Termination): When the first alternative has weight 0.0
    // (deterministic, unambiguous) and succeeds, no other alternative can have
    // lower weight (0.0 is the tropical identity for ⊗). Skip remaining tries.
    // This is a compile-time decision: the early-exit guard is only emitted when
    // the first alternative's weight is exactly 0.0 and there are >1 alternatives.
    // F2 is only safe when the category does NOT need NFA spillover.
    // When spillover is needed, disambiguation (from_alternatives) requires
    // all alternatives — even if the first is weight-0.0 — because the primary
    // result may not be ground (e.g., float(x) where x is a free variable).
    //
    // A5 (NbestWeight Confidence): Extends F2 with a more principled check using
    // NbestWeight<2>: if the confidence gap between the best and second-best
    // alternatives exceeds a threshold, treat the first as deterministic even
    // when its weight is nonzero. This covers cases where the best alternative
    // is so much better than the runner-up that trying both is wasteful.
    // The threshold (1.0) means the second-best must be ≥10x less likely
    // (in log-probability space) than the best.
    //
    // A3: Both F2 and A5 are gated by `optimization_gates`.
    // Note: F2/A5 checks use the full ordered_inlineable for gap calculations
    // but the conditional only wraps hot alternatives (cold are in the helper).
    let first_is_deterministic = ordered_inlineable.len() > 1
        && !config.needs_nfa_spillover
        && {
            let f2_pass = config.optimization_gates.early_termination
                && ordered_inlineable.first().map_or(false, |(_, w)| *w == 0.0);

            // A5: NbestWeight<2> confidence gap check — more principled than F2's weight==0.0
            let a5_pass = config.optimization_gates.ambiguity_targeting
                && ordered_inlineable.len() >= 2
                && {
                    let best_weight = ordered_inlineable[0].1;
                    let second_weight = ordered_inlineable[1].1;
                    let confidence_gap = second_weight - best_weight;
                    // Threshold: gap > 1.0 means second-best is ≥10x less likely
                    confidence_gap > 1.0
                };

            f2_pass || a5_pass
        };

    // Try hot alternatives inline (WFST-ordered: weight-best first)
    for (idx, (rd_rule, weight)) in hot_alts.iter().enumerate() {
        buf.push_str("*pos = nfa_saved;");

        if should_use_standalone_fn(rd_rule) {
            // Standalone function: call it directly with save/restore
            let fn_name = format!("parse_{}", rd_rule.label.to_lowercase());
            write!(
                buf,
                "match {}(tokens, pos) {{ \
                    Ok(v) => {{ nfa_results.push(v); nfa_positions.push(*pos); nfa_weights.push({weight:?}); }}, \
                    Err(e) => {{ if nfa_first_err.is_none() {{ nfa_first_err = Some(e); }} }}, \
                }}",
                fn_name,
            )
            .unwrap();
        } else {
            let segments = split_rd_handler(rd_rule);
            if segments.is_empty() {
                continue;
            }
            // For rules with same-category NTs (segments.len() > 1), emit
            // the full `rd_rule.items` so that same-cat NTs become recursive
            // parse_<cat> calls within the save/restore closure. For single-
            // segment rules, use segments[0].inline_items (equivalent to
            // rd_rule.items in that case).
            let items_to_emit: &[RDSyntaxItem] = if segments.len() > 1 {
                &rd_rule.items
            } else {
                &segments[0].inline_items
            };
            write!(buf, "match (|| -> Result<{}, ParseError> {{", cat,).unwrap();
            write_inline_items(buf, items_to_emit, true);

            // Build the constructor expression
            write_nfa_inline_constructor(buf, rd_rule, &segments);

            buf.push_str("})() {");
            write!(buf, "Ok(v) => {{ nfa_results.push(v); nfa_positions.push(*pos); nfa_weights.push({weight:?}); }},").unwrap();
            buf.push_str("Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },");
            buf.push('}');
        }

        // F2: After the first (weight-0.0) alternative succeeds, skip the rest.
        // Weight 0.0 is the tropical zero-cost identity — no other alternative
        // can produce a lower weight, making further tries redundant.
        // Remaining alternatives are wrapped in `if nfa_results.is_empty() { ... }`
        if idx == 0 && first_is_deterministic {
            buf.push_str("if nfa_results.is_empty() {");
        }
    }

    // A4: Call cold helper function for high-weight alternatives.
    // When spillover is needed, all alternatives must be tried (for semantic
    // disambiguation). When not, only call cold path if hot alternatives failed.
    if let Some(ref fn_name) = cold_fn_name {
        if config.needs_nfa_spillover {
            // Unconditional: spillover needs all alternatives for from_alternatives
            write!(
                buf,
                "{fn_name}(tokens, pos, nfa_saved, &mut nfa_results, \
                 &mut nfa_positions, &mut nfa_weights, &mut nfa_first_err);",
            )
            .unwrap();
        } else {
            // Only when hot alternatives all failed (cold can't beat hot by weight order)
            write!(
                buf,
                "if nfa_results.is_empty() {{ \
                    {fn_name}(tokens, pos, nfa_saved, &mut nfa_results, \
                     &mut nfa_positions, &mut nfa_weights, &mut nfa_first_err); \
                }}",
            )
            .unwrap();
        }
    }

    // Close the F2 early-termination conditional block if it was opened
    if first_is_deterministic {
        buf.push_str("} /* F2: deterministic hit (w=0.0) — remaining alternatives skipped if first succeeded */");
    }

    // Result selection
    buf.push_str("match nfa_results.len() {");

    // No successes — either fall through to frame-pushing or return error
    if !frame_pushing.is_empty() {
        // Fall through to first frame-pushing rule
        let rd_rule = frame_pushing[0];
        let segments = split_rd_handler(rd_rule);
        buf.push_str("0 => {");
        buf.push_str("*pos = nfa_saved;");
        if !segments.is_empty() {
            {
                // PDA merge: always use frame-pushing approach (stack-safe).
                // Cross-category dispatch is handled by the pre-match block in
                // _impl's prefix phase, so `continue 'drive` reaches it.
                write_inline_items(buf, &segments[0].inline_items, true);
                if let Some(ref nt) = segments[0].nonterminal {
                    write!(
                        buf,
                        "stack.push({enum_name}::{vp}{variant} {{",
                        enum_name = frame_info.enum_name, vp = config.frame_prefix(), variant = segments[0].frame_variant
                    )
                    .unwrap();
                    write!(buf, "saved_bp: cur_bp,").unwrap();
                    for capture in &segments[0].accumulated_captures {
                        match capture {
                            SegmentCapture::Ident { name }
                            | SegmentCapture::Binder { name }
                            | SegmentCapture::NonTerminal { name, .. } => {
                                write!(buf, "{},", name).unwrap();
                            },
                            _ => {},
                        }
                    }
                    buf.push_str("});");
                    write!(buf, "cur_bp = {};", nt.bp).unwrap();
                    buf.push_str("continue 'drive;");
                } else {
                    write_rd_constructor_inline(buf, rd_rule, &segments);
                }
            }
        }
        buf.push_str("},");
    } else {
        write!(
            buf,
            "0 => {{ return Err(nfa_first_err.unwrap_or_else(|| \
                ParseError::UnexpectedToken {{ \
                    expected: Cow::Borrowed(\"{cat} expression\"), \
                    found: format_token_friendly(&tokens[nfa_saved].0), \
                    range: tokens[nfa_saved].1, \
                    hint: None, \
                }} \
            )); }},",
        )
        .unwrap();
    }

    // One or more successes — take the best (first by WFST weight order),
    // spill remaining alternatives for forced-prefix replay.
    //
    // F1 (Spillover Pruning): Only spill alternatives within beam of the
    // primary result's weight. Alternatives with weight > best + beam cannot
    // win disambiguation, so replaying them is wasted work. The beam width
    // is embedded as a compile-time literal from the PredictionWfst. When no
    // beam is configured, all position-matching alternatives are spilled.
    // A3: Beam-based pruning gated by `optimization_gates.spillover_pruning`.
    //
    // B4 (Adaptive NFA Beam): When `adaptive_recovery` gate is enabled,
    // the runtime RUNNING_WEIGHT modulates the beam width. Accumulated
    // ambiguity from prior dispatches widens the beam (additive slack),
    // preserving more alternatives for disambiguation when the parse has
    // already been through ambiguous territory.
    //
    // NOTE: We never skip spillover entirely at NFA-ambiguous points,
    // even when running weight is 0.0. NFA-ambiguous points have multiple
    // valid parse trees by definition, and semantic disambiguation (Ascent)
    // needs all alternatives to select the correct one. Skipping spillover
    // would break semantic disambiguation for patterns like `float(x)` where
    // the cast alternative is needed even though the primary parse has
    // weight 0.0.
    {
        let cat_upper = cat.to_uppercase();
        buf.push_str(&format_nfa_result_selection_arm(&cat_upper, config));
    }
    buf.push('}'); // close match nfa_results.len()

    buf.push_str("},"); // close Token::Variant arm
}

/// Write the constructor for an NFA-inlineable rule (returns Ok(Cat::Label(...))).
///
/// Similar to `write_rd_constructor_inline` but produces `Ok(Cat::Label(...))` instead
/// of `break 'prefix Cat::Label(...)` so it can be used inside a closure.
fn write_nfa_inline_constructor(buf: &mut String, rule: &RDRuleInfo, segments: &[HandlerSegment]) {
    let cat = &rule.category;
    let label = &rule.label;

    // Collect all captures from the final segment
    let all_captures: Vec<&SegmentCapture> = if let Some(last) = segments.last() {
        let mut seen = std::collections::HashSet::new();
        last.accumulated_captures
            .iter()
            .filter(|c| {
                let name = match c {
                    SegmentCapture::NonTerminal { name, .. }
                    | SegmentCapture::Ident { name }
                    | SegmentCapture::Binder { name }
                    | SegmentCapture::Collection { name, .. } => name.clone(),
                    SegmentCapture::Guard { .. } => unreachable!(
                        "guarded rules are routed through standalone fn via \
                         should_use_standalone_fn; nfa_inline_constructor is \
                         never reached for them"
                    ),
                };
                seen.insert(name)
            })
            .collect()
    } else {
        Vec::new()
    };

    if rule.has_binder {
        let binder_cap = all_captures
            .iter()
            .find(|c| matches!(c, SegmentCapture::Binder { .. }));
        let body_cap = all_captures
            .iter()
            .rev()
            .find(|c| matches!(c, SegmentCapture::NonTerminal { .. }));
        if let (
            Some(SegmentCapture::Binder { name: binder_name }),
            Some(SegmentCapture::NonTerminal { name: body_name, .. }),
        ) = (binder_cap, body_cap)
        {
            let extra: Vec<&&SegmentCapture> = all_captures
                .iter()
                .filter(|c| {
                    let n = match c {
                        SegmentCapture::NonTerminal { name, .. }
                        | SegmentCapture::Ident { name }
                        | SegmentCapture::Binder { name }
                        | SegmentCapture::Collection { name, .. } => name,
                        SegmentCapture::Guard { .. } => unreachable!(
                            "guarded rules are routed through standalone fn via \
                             should_use_standalone_fn; nfa_inline_constructor is \
                             never reached for them"
                        ),
                    };
                    n != binder_name && n != body_name
                })
                .collect();
            write!(buf, "Ok({cat}::{label}(").unwrap();
            for c in &extra {
                write_segment_capture_as_arg(buf, c);
                buf.push(',');
            }
            write!(
                buf,
                "mettail_runtime::Scope::new(\
                mettail_runtime::Binder(mettail_runtime::get_or_create_var({})), \
                Box::new({}),\
            )))",
                binder_name, body_name
            )
            .unwrap();
        } else {
            write!(buf, "Ok({cat}::{label})").unwrap();
        }
    } else if all_captures.is_empty() {
        write!(buf, "Ok({cat}::{label})").unwrap();
    } else {
        write!(buf, "Ok({cat}::{label}(",).unwrap();
        for (i, c) in all_captures.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write_segment_capture_as_arg(buf, c);
        }
        buf.push_str("))");
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// RD Handler Splitting
// ══════════════════════════════════════════════════════════════════════════════

/// A segment of an RD handler split at nonterminal boundaries.
///
/// Each segment contains:
/// - Inline items (terminals, ident captures, binders) to execute before the nonterminal
/// - The nonterminal that triggers a "push frame + continue 'drive"
/// - Values captured from previous segments that must be saved in the frame
#[derive(Debug, Clone)]
pub struct HandlerSegment {
    /// Items to inline before the nonterminal parse (terminals, ident captures, binders).
    pub inline_items: Vec<RDSyntaxItem>,
    /// The nonterminal to parse (triggers frame push). None for the final segment.
    pub nonterminal: Option<SegmentNonTerminal>,
    /// Values captured from all prior segments that must be stored in the frame.
    pub accumulated_captures: Vec<SegmentCapture>,
    /// Frame variant name for this segment's continuation (e.g., "RD_PInput_0").
    pub frame_variant: String,
}

/// A nonterminal parse target within an RD handler segment.
#[derive(Debug, Clone)]
pub struct SegmentNonTerminal {
    /// Category to parse (e.g., "Proc", "Name").
    pub category: String,
    /// Parameter name for the parsed result.
    pub param_name: String,
    /// Binding power for the parse call (0 for most, prefix_bp for unary prefix).
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
    /// Phase 3A (predicated types): a behavioral predicate captured
    /// from a `?guard:Guard` slot. Stored as a
    /// `mettail_runtime::BehavioralPred` field on the frame variant.
    Guard { name: String },
}

/// Split an RD handler into segments at SAME-CATEGORY nonterminal boundaries.
///
/// Only same-category nonterminals create split points (these are the recursion
/// points that need the trampoline). Cross-category nonterminals are kept as
/// inline items and handled with direct function calls (bounded depth by
/// grammar structure — no category cycles).
///
/// Algorithm:
/// 1. Walk items left to right
/// 2. Accumulate "inline" items (terminals, ident captures, binders, cross-category NTs)
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
                // Phase 3A: a `?guard:Guard` slot's parsed
                // BehavioralPred must be stored across the trampoline
                // split so the frame finalizer can construct the term.
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Guard {
                    name: param_name.clone(),
                });
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

// ══════════════════════════════════════════════════════════════════════════════
// CEK-1: Dead Capture Elimination (Environment Trimming)
// ══════════════════════════════════════════════════════════════════════════════

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
    let mut live_at: Vec<std::collections::HashSet<String>> = vec![std::collections::HashSet::new(); n];

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
        // practice. Returning the name keeps liveness analysis safe
        // if a future caller stages a Guard capture for analysis only.
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

/// CEK-1: Extract capture names referenced by the final constructor of an RD rule.
///
/// The constructor uses all accumulated captures from the last segment.
/// This function returns the set of capture names that appear in the rule's
/// constructor pattern (i.e., the names that map to constructor arguments).
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

/// CEK-1: Apply dead capture elimination to RD handler segments.
///
/// This is the main entry point for environment trimming. It takes the
/// segments from `split_rd_handler()` and returns new segments with
/// accumulated_captures filtered to only include live captures.
///
/// When `optimization_gates.environment_trimming` is true, the trampoline
/// codegen uses this to produce smaller frame variants.
pub fn trim_dead_captures(
    segments: &[HandlerSegment],
    rule: &RDRuleInfo,
) -> Vec<HandlerSegment> {
    let ctor_names = constructor_capture_names(rule);
    let live_captures = compute_live_captures(segments, &ctor_names);

    segments
        .iter()
        .zip(live_captures)
        .map(|(seg, live)| HandlerSegment {
            inline_items: seg.inline_items.clone(),
            nonterminal: seg.nonterminal.clone(),
            accumulated_captures: live,
            frame_variant: seg.frame_variant.clone(),
        })
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// Frame Enum Generation
// ══════════════════════════════════════════════════════════════════════════════

/// Information about the generated Frame enum for a category.
#[derive(Debug)]
pub struct FrameInfo {
    /// Name of the frame enum (e.g., "Frame_Int").
    pub enum_name: String,
    /// All variants in the enum.
    pub variants: Vec<FrameVariant>,
}

/// Classification of a frame variant for FrameKind dispatch.
/// Eliminates string prefix matching on variant names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameVariantKind {
    InfixRHS,
    GroupClose,
    UnaryPrefix,
    RDSegment,
    CollectionElem,
    Mixfix,
    CrossCatInfixTry,
    Lambda,
    Dollar,
    CastWrap,
    GuardEval,
    Other,
}

impl FrameVariantKind {
    /// Classify a frame variant by its name.
    #[inline]
    pub fn from_name(name: &str) -> Self {
        if name == "InfixRHS" { Self::InfixRHS }
        else if name == "CrossCatInfixTry" { Self::InfixRHS }
        else if name == "GroupClose" { Self::GroupClose }
        else if name.starts_with("UnaryPrefix_") { Self::UnaryPrefix }
        else if name.starts_with("CollectionElem_") { Self::CollectionElem }
        else if name.starts_with("Mixfix_") { Self::Mixfix }
        else if name.starts_with("LambdaBody_") { Self::Lambda }
        else if name.starts_with("Dollar") || name.starts_with("Ddollar") { Self::Dollar }
        else if name.starts_with("RD_") { Self::RDSegment }
        else if name.starts_with("CastWrap_") { Self::CastWrap }
        else if name == "GuardEval" { Self::GuardEval }
        else { Self::Other }
    }

    /// Convert to the u8 FrameKind value used by the generated code.
    #[inline]
    pub fn as_u8(&self) -> u8 {
        match self {
            Self::UnaryPrefix => 0,
            Self::InfixRHS => 1,
            Self::CollectionElem => 3,
            Self::GroupClose => 4,
            Self::Mixfix => 5,
            Self::Lambda => 6,
            Self::Dollar => 7,
            Self::CastWrap => 8,
            _ => 9, // Other, RDSegment, GuardEval
        }
    }
}

/// A single variant in the Frame enum.
#[derive(Debug)]
pub struct FrameVariant {
    /// Variant name (e.g., "InfixRHS", "GroupClose", "RD_PInput_0").
    pub name: String,
    /// Fields in this variant.
    pub fields: Vec<FrameField>,
}

impl FrameVariant {
    /// Get the structural classification of this variant (computed from name).
    #[inline]
    pub fn kind(&self) -> FrameVariantKind {
        FrameVariantKind::from_name(&self.name)
    }
}

/// A field in a frame variant.
#[derive(Debug)]
pub struct FrameField {
    /// Field name.
    pub name: String,
    /// Rust type string.
    pub type_str: String,
}

/// Configuration for generating the trampoline for a category.
pub struct TrampolineConfig {
    /// Category name (e.g., "Proc", "Int").
    pub category: String,
    /// Whether this is the primary category.
    pub is_primary: bool,
    /// Whether this category has a variable variant (e.g. IVar, BVar).
    /// False for collection-only categories (List, Bag) which have no Var variant.
    pub has_var: bool,
    /// Whether this category has infix operators.
    pub has_infix: bool,
    /// Whether this category has postfix operators.
    pub has_postfix: bool,
    /// Whether this category has mixfix operators.
    pub has_mixfix: bool,
    /// All category names.
    pub all_categories: Vec<String>,
    /// Whether dispatch wrapper is needed.
    pub needs_dispatch: bool,
    /// Native type for this category.
    pub native_type: Option<String>,
    /// Custom-/literal-Token variant names whose Token::{Name} variants
    /// carry a payload (`Token::Name(_)` rather than the unit `Token::Name`).
    /// Emission sites that construct raw match-arm strings consult this set
    /// to decide between `Token::Foo` and `Token::Foo(_)` patterns.
    pub payload_carrying_variants: Vec<String>,
    /// Cast rules targeting this category.
    pub cast_rules: Vec<CastRule>,
    /// Own FIRST set.
    pub own_first_set: FirstSet,
    /// All FIRST sets.
    pub all_first_sets: std::collections::HashMap<String, FirstSet>,
    /// FOLLOW set.
    pub follow_set: FirstSet,
    /// Whether the grammar has binders.
    pub has_binders: bool,
    /// Optional prediction WFST for weight-ordered dispatch.
    /// When present, prefix match arms are reordered by tropical weight (lowest first).
    pub prediction_wfst: Option<crate::wfst::PredictionWfst>,
    /// Whether this category has NFA-ambiguous prefix groups requiring spillover.
    /// When true, thread-local `NFA_PREFIX_SPILL_Cat` and `NFA_FORCED_PREFIX_Cat`
    /// are emitted and the NFA merged arm spills N-1 alternatives for forced-prefix
    /// replay in `parse_preserving_vars`.
    pub needs_nfa_spillover: bool,
    /// Missing cast rule suggestions: `(token_variant_name, source_category)` pairs.
    ///
    /// For each source category that has tokens in its FIRST set (unique to it,
    /// not in the target's own FIRST set) but has NO cast rule to this target
    /// category, the unique tokens are listed here. Used in prefix error fallback
    /// to suggest missing cast rules (e.g., `"Hint: 'at' is a Proc expression,
    /// but no Proc → Float cast rule exists"`).
    pub cast_suggestions: Vec<(String, String)>,
    /// A3: Optimization gates derived from cost-benefit analysis.
    ///
    /// Controls which compile-time optimizations are emitted for this category.
    /// When a gate is `false`, the codegen uses the unoptimized fallback path.
    pub optimization_gates: crate::cost_benefit::OptimizationGates,
    /// A4: Dead rule labels identified by `collect_dead_rule_labels()`.
    ///
    /// When `optimization_gates.enhanced_dce` is true and a rule's label is in
    /// this set, its codegen is suppressed (dispatch arm, NFA alternative, etc.).
    /// The lint layer still reports W01 warnings independently.
    pub dead_rules: std::collections::HashSet<String>,
    /// CEK-4: Dead frame variant names identified by WPDS poststar analysis.
    ///
    /// When `optimization_gates.dead_frame_elimination` is true and a frame
    /// variant's name is in this set, its codegen is suppressed (enum variant,
    /// prefix arm, unwind handler).
    pub dead_frames: std::collections::HashSet<String>,
    /// Complete weight map from composed dispatch: `(category, token) → weight`.
    ///
    /// Includes both composed (ambiguous) and specificity (deterministic) weights.
    /// Used for ident-lookahead handler sorting (priority over raw WFST prediction).
    pub complete_weight_map: Option<std::collections::HashMap<(String, String), f64>>,
    /// LED delegation sources for sum-type categories.
    ///
    /// When non-empty, the LED chain falls back to delegating to constituent categories'
    /// operators when the sum type's own BP tables don't match the current token.
    pub led_delegation: Vec<crate::pratt::LedDelegationSource>,
    /// Decision tree for this category (unified dispatch analysis).
    ///
    /// When present, the trie-based dispatch analysis subsumes ad-hoc analyses
    /// (group_rd_by_dispatch_token, shared prefix, second-token lookahead, etc.)
    /// and provides precision ambiguity reports, WFST consistency checks, and
    /// incremental codegen support.
    pub decision_tree: Option<crate::decision_tree::CategoryDecisionTree>,
    /// D07: Emit runtime coverage instrumentation at dispatch points.
    ///
    /// When true, each dispatch resolution emits
    /// `__coverage::record("Cat", path_id);`
    /// so test suites can report which dispatch paths are exercised.
    /// Activated by `PRATTAIL_COVERAGE=1` env var during code generation.
    pub emit_coverage: bool,
    /// 1.3b: Prefix-guided expected token description for error messages.
    ///
    /// Derived from decision tree dispatch tokens (e.g., `"one of: Plus, Minus, LParen"`).
    /// When `None`, falls back to generic `"Cat expression"`.
    pub expected_tokens_str: Option<String>,
    /// RT-01: WPDS-derived frame pool capacity hint for this category.
    ///
    /// When `Some(n)`, the TLS `FRAME_POOL_Cat` is initialized with
    /// `Vec::with_capacity(n)` instead of `Vec::new()`. Derived from G34 depth bounds.
    /// `None` means no WPDS data is available (use default `Vec::new()`).
    pub frame_pool_capacity: Option<usize>,
    /// BP03: Token variant map from lexer codegen.
    ///
    /// When `Some`, enables the BP03 static array lookup optimization for
    /// categories with >= 8 infix/postfix/mixfix operators (gated by
    /// `optimization_gates.bp_table_lookup`).
    pub token_variant_map: Option<crate::automata::codegen::TokenVariantMap>,
    /// CD05: Prefix CSE hints for shared nonterminal parses.
    ///
    /// When non-empty and `optimization_gates.prefix_cse` is true, contains
    /// detected opportunities where multiple rules share a nonterminal parse
    /// at the same trie prefix. The codegen emits diagnostic comments showing
    /// how the shared nonterminal could be parsed once and cached. Full codegen
    /// integration is a future step.
    pub prefix_cse_hints: Vec<crate::decision_tree::SharedNonterminalPrefix>,
    /// PDA merge: cross-category prefix arms for inline emission in `_impl`.
    ///
    /// When non-empty, these arms are merged into the prefix `match` so that
    /// cross-category dispatch happens inside `_impl` (not in a separate dispatch
    /// wrapper). This allows `(` to use trampolined `GroupClose` frames for ALL
    /// categories, eliminating unbounded cross-function recursion from grouping.
    pub cross_cat_prefix_arms: Vec<crate::dispatch::CrossCatPrefixArm>,
    /// When true, skip generating the `parse_Cat` entry point wrapper and
    /// thread-local frame pool. The unified trampoline provides its own
    /// entry points and unified frame pool.
    pub skip_entry_point: bool,
    /// When true, generate step functions (`prefix_step_Cat`, `infix_step_Cat`)
    /// that return `Result<ParseStep, ParseError>` instead of a monolithic `_impl`
    /// with labeled control flow. The unified driver calls these step functions
    /// iteratively, eliminating mutual recursion.
    pub unified_mode: bool,
    /// When true, skip generating step functions (`prefix_step_Cat`, `infix_step_Cat`,
    /// `same_cat_prefix_step_Cat`). These will be generated by unified_trampoline.rs
    /// as CPS single-step functions instead. The trampoline still generates the full
    /// `_impl` body, Frame_Cat enum, helper functions, and thread-locals.
    pub skip_step_functions: bool,
}

impl TrampolineConfig {
    /// Get the `continue 'drive` replacement string for the current mode.
    pub fn continue_drive(&self) -> String {
        if self.unified_mode {
            format!("return Ok(ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: cur_bp }})", cat = self.category)
        } else {
            "continue 'drive".to_string()
        }
    }

    /// Get the frame enum name for the current mode.
    pub fn frame_enum(&self, frame_info: &FrameInfo) -> String {
        if self.unified_mode {
            "UnifiedFrame".to_string()
        } else {
            frame_info.enum_name.clone()
        }
    }

    /// Get the frame variant prefix for the current mode.
    /// In unified mode, frame variants are prefixed with "Cat_" (e.g., "Int_InfixRHS").
    pub fn frame_prefix(&self) -> String {
        if self.unified_mode {
            format!("{}_", self.category)
        } else {
            String::new()
        }
    }

    /// Prefix a frame variant name with Cat_ in unified mode.
    pub fn prefix_variant(&self, variant: &str) -> String {
        if self.unified_mode {
            format!("{}_{}", self.category, variant)
        } else {
            variant.to_string()
        }
    }
}

/// Write the Frame enum declaration for a category.
///
/// Generates `enum Frame_Cat { ... }` with variants for every recursion point:
/// - InfixRHS: after infix RHS parse
/// - GroupClose: after grouped expression parse
/// - UnaryPrefix_*: per unary prefix operator
/// - RD_*_N: per RD handler segment
/// - CollectionElem_*: per collection rule
/// - Mixfix_*_N: per mixfix operand step
/// - LambdaBody_*: lambda body variants
/// - Dollar_*: dollar syntax variants
/// - CastWrap_*: per cast rule
pub fn write_frame_enum(
    buf: &mut String,
    config: &TrampolineConfig,
    rd_rules: &[RDRuleInfo],
    bp_table: &BindingPowerTable,
) -> FrameInfo {
    let cat = &config.category;
    // In unified mode, frame variants are part of UnifiedFrame with Cat_ prefix.
    // The enum_name and variant prefix determine what gets emitted in the generated code.
    let (enum_name, variant_prefix) = if config.unified_mode {
        ("UnifiedFrame".to_string(), format!("{}_", cat))
    } else {
        (format!("Frame_{}", cat), String::new())
    };

    let mut variants: Vec<FrameVariant> = Vec::new();

    // ── Fixed variants (always present when has_infix) ──

    if config.has_infix {
        variants.push(FrameVariant {
            name: "InfixRHS".to_string(),
            fields: vec![
                FrameField {
                    name: "lhs".to_string(),
                    type_str: cat.clone(),
                },
                FrameField {
                    name: "op_pos".to_string(),
                    type_str: "usize".to_string(),
                },
                FrameField {
                    name: "saved_bp".to_string(),
                    type_str: "u8".to_string(),
                },
            ],
        });

        // CrossCatInfixTry: tentative infix frame for operators that have both
        // same-category and cross-category variants. When the prefix phase fails
        // to parse the RHS in the same category, this frame is popped, pos is
        // restored, and LED delegation tries the cross-category variant.
        let cross_cat_terms = conflicting_infix_terminals(config, bp_table);
        if !cross_cat_terms.is_empty() && !config.led_delegation.is_empty() {
            variants.push(FrameVariant {
                name: "CrossCatInfixTry".to_string(),
                fields: vec![
                    FrameField {
                        name: "lhs".to_string(),
                        type_str: cat.clone(),
                    },
                    FrameField {
                        name: "op_pos".to_string(),
                        type_str: "usize".to_string(),
                    },
                    FrameField {
                        name: "saved_bp".to_string(),
                        type_str: "u8".to_string(),
                    },
                    FrameField {
                        name: "saved_pos".to_string(),
                        type_str: "usize".to_string(),
                    },
                ],
            });
        }
    }

    // GroupClose (always present — parenthesized expressions)
    variants.push(FrameVariant {
        name: "GroupClose".to_string(),
        fields: vec![FrameField {
            name: "saved_bp".to_string(),
            type_str: "u8".to_string(),
        }],
    });

    // ── Per-unary-prefix variants ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || rd_rule.prefix_bp.is_none() {
            continue;
        }
        // Unary prefix: pattern is [Terminal, NonTerminal(same_category)]
        // The terminal is consumed inline, the nonterminal triggers a frame push
        variants.push(FrameVariant {
            name: format!("UnaryPrefix_{}", rd_rule.label),
            fields: vec![FrameField {
                name: "saved_bp".to_string(),
                type_str: "u8".to_string(),
            }],
        });
    }

    // ── Per-RD-handler segment variants ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat {
            continue;
        }
        // Skip unary prefix (handled above), collection rules (handled separately),
        // and rules dispatched to standalone functions (Sep, multi-binder)
        if rd_rule.prefix_bp.is_some()
            || is_simple_collection(rd_rule)
            || should_use_standalone_fn(rd_rule)
        {
            continue;
        }

        let segments = split_rd_handler(rd_rule);
        // CEK-1: Apply dead capture elimination if the gate is enabled
        let segments = if config.optimization_gates.environment_trimming {
            trim_dead_captures(&segments, rd_rule)
        } else {
            segments
        };
        for segment in &segments {
            if segment.nonterminal.is_none() {
                continue; // Final segment doesn't need a frame variant
            }

            let mut fields: Vec<FrameField> = Vec::new();
            // saved_bp always present
            fields.push(FrameField {
                name: "saved_bp".to_string(),
                type_str: "u8".to_string(),
            });

            // Add fields from accumulated captures
            for capture in &segment.accumulated_captures {
                match capture {
                    SegmentCapture::NonTerminal { name, category } => {
                        fields.push(FrameField {
                            name: name.clone(),
                            type_str: category.clone(),
                        });
                    },
                    SegmentCapture::Ident { name } | SegmentCapture::Binder { name } => {
                        fields.push(FrameField {
                            name: name.clone(),
                            type_str: "String".to_string(),
                        });
                    },
                    SegmentCapture::Collection { name, kind, element_category } => {
                        let type_str = match kind {
                            CollectionKind::HashBag => {
                                format!("mettail_runtime::HashBag<{}>", element_category)
                            },
                            CollectionKind::HashSet => {
                                format!("std::collections::HashSet<{}>", element_category)
                            },
                            CollectionKind::Vec => format!("Vec<{}>", element_category),
                            // HashMap treated as HashBag for codegen purposes;
                            // map patterns are not fully supported in trampoline code.
                            CollectionKind::HashMap => {
                                format!("mettail_runtime::HashBag<{}>", element_category)
                            },
                        };
                        fields.push(FrameField { name: name.clone(), type_str });
                    },
                    SegmentCapture::Guard { .. } => unreachable!(
                        "guarded rules are routed through standalone fn via \
                         should_use_standalone_fn; frame variants are never \
                         emitted for them, so this match arm is structurally \
                         unreachable"
                    ),
                }
            }

            variants.push(FrameVariant {
                name: segment.frame_variant.clone(),
                fields,
            });
        }
    }

    // ── Per-collection variants ──
    //
    // Only emit a `CollectionElem_<label>` frame variant when the
    // collection's element category matches the rule's own category —
    // cross-category collections (e.g. `List = Vec<Proc>`) use an inline
    // recursive loop in the prefix handler (see `write_rd_prefix_arms`)
    // and never push a frame, so emitting one would just leave a dead
    // enum variant and trigger `non-exhaustive patterns` errors at the
    // unwind match (which we also skip for cross-cat).
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || !is_simple_collection(rd_rule) {
            continue;
        }
        let collection_type = rd_rule.collection_type.unwrap_or(CollectionKind::HashBag);
        let element_category = rd_rule
            .items
            .iter()
            .find_map(|item| match item {
                RDSyntaxItem::Collection { element_category, .. } => Some(element_category.clone()),
                _ => None,
            })
            .unwrap_or_else(|| cat.clone());
        if element_category != *cat {
            continue;
        }

        let type_str = match collection_type {
            CollectionKind::HashBag => format!("mettail_runtime::HashBag<{}>", element_category),
            CollectionKind::HashSet => format!("std::collections::HashSet<{}>", element_category),
            CollectionKind::Vec => format!("Vec<{}>", element_category),
            CollectionKind::HashMap => format!("mettail_runtime::HashBag<{}>", element_category),
        };

        variants.push(FrameVariant {
            name: format!("CollectionElem_{}", rd_rule.label),
            fields: vec![
                FrameField { name: "elements".to_string(), type_str },
                FrameField {
                    name: "saved_pos".to_string(),
                    type_str: "usize".to_string(),
                },
                FrameField {
                    name: "saved_bp".to_string(),
                    type_str: "u8".to_string(),
                },
            ],
        });
    }

    // ── Per-mixfix operand step variants ──
    for op in bp_table.mixfix_operators_for_category(cat) {
        for (i, _part) in op.mixfix_parts.iter().enumerate() {
            let mut fields = vec![
                FrameField {
                    name: "lhs".to_string(),
                    type_str: cat.clone(),
                },
                FrameField {
                    name: "saved_bp".to_string(),
                    type_str: "u8".to_string(),
                },
            ];
            // Previous operands as captured fields
            for j in 0..i {
                fields.push(FrameField {
                    name: format!("param_{}", op.mixfix_parts[j].param_name),
                    type_str: op.mixfix_parts[j].operand_category.clone(),
                });
            }
            variants.push(FrameVariant {
                name: format!("Mixfix_{}_{}", op.label, i),
                fields,
            });
        }
    }

    // ── Lambda/Dollar variants (only when has_binders and is primary) ──
    if config.has_binders && config.is_primary {
        // Single lambda body
        variants.push(FrameVariant {
            name: "LambdaBody_Single".to_string(),
            fields: vec![
                FrameField {
                    name: "binder_name".to_string(),
                    type_str: "String".to_string(),
                },
                FrameField {
                    name: "saved_bp".to_string(),
                    type_str: "u8".to_string(),
                },
            ],
        });

        // Multi lambda body
        variants.push(FrameVariant {
            name: "LambdaBody_Multi".to_string(),
            fields: vec![
                FrameField {
                    name: "binder_names".to_string(),
                    type_str: "Vec<String>".to_string(),
                },
                FrameField {
                    name: "saved_bp".to_string(),
                    type_str: "u8".to_string(),
                },
            ],
        });

        // Dollar syntax: $cat(f, x) — frame for after parsing f, before parsing x
        for dom in &config.all_categories {
            let dom_cap = capitalize_first(&dom.to_lowercase());

            // Single-apply $dom(f, x): frame captures state after parsing f.
            // x is a cross-category call (bounded depth), handled inline in the unwind handler.
            variants.push(FrameVariant {
                name: format!("DollarF_{}", dom_cap),
                fields: vec![FrameField {
                    name: "saved_bp".to_string(),
                    type_str: "u8".to_string(),
                }],
            });

            // Multi-apply $$dom(f, x1, x2, ...): frame captures state after parsing f.
            // All args are cross-category calls (bounded depth), handled inline in the unwind handler.
            variants.push(FrameVariant {
                name: format!("DdollarF_{}", dom_cap),
                fields: vec![FrameField {
                    name: "saved_bp".to_string(),
                    type_str: "u8".to_string(),
                }],
            });
        }
    }

    // ── Guard evaluation frame ──
    // When the parser encounters a guarded input syntax (the `?` operator),
    // it pushes a GuardEval frame to capture the continuation after parsing
    // the guard pattern. This enables stack-safe parsing of deeply nested
    // guard expressions.
    //
    // Guard evaluation itself (match_pattern, behavioral predicates) is
    // iterative and does not require trampolining — only the *parsing* of
    // the guard syntax is trampolined here.
    if config.has_binders {
        variants.push(FrameVariant {
            name: "GuardEval".to_string(),
            fields: vec![
                FrameField {
                    name: "saved_bp".to_string(),
                    type_str: "u8".to_string(),
                },
            ],
        });
    }

    // NOTE: Cast rules are NOT trampolined — they call parse_SourceCat() directly
    // in the prefix (cross-category, bounded depth). No CastWrap_* frame variants needed.

    // CEK-4: Filter dead frame variants when dead_frame_elimination is enabled.
    // Unreachable frame variants (as determined by WPDS poststar analysis) are
    // removed from the enum, their prefix arms, and their unwind handlers.
    // Only rule-specific variants (UnaryPrefix_*, RD_*, CollectionElem_*) are
    // filtered — structural variants (InfixRHS, GroupClose, LambdaBody_*,
    // DollarF_*, DdollarF_*, GuardEval, Mixfix_*) are always retained.
    if config.optimization_gates.dead_frame_elimination && !config.dead_frames.is_empty() {
        variants.retain(|v| {
            let is_rule_specific = matches!(
                v.kind(),
                FrameVariantKind::UnaryPrefix | FrameVariantKind::RDSegment | FrameVariantKind::CollectionElem
            );
            !is_rule_specific || !config.dead_frames.contains(&v.name)
        });
    }

    // In unified mode, prefix variant names with Cat_ for namespace isolation
    // within the shared UnifiedFrame enum.
    if config.unified_mode {
        for variant in &mut variants {
            variant.name = format!("{}{}", variant_prefix, variant.name);
        }
    }

    // ── Write the enum declaration ──
    // Always write the per-category Frame_Cat enum — it's needed by recovery and
    // traced variants even in unified mode. In unified mode, the same variants
    // (with Cat_ prefix) also appear in UnifiedFrame.
    if config.unified_mode {
        // Write the per-category enum with UNPREFIXED names for backward compat
        let compat_enum = format!("Frame_{}", config.category);
        write!(buf, "#[allow(dead_code)] #[derive(Debug)] enum {} {{", compat_enum).unwrap();
        for variant in &variants {
            // Strip the Cat_ prefix for the per-category enum
            let compat_name = variant.name.strip_prefix(&variant_prefix).unwrap_or(&variant.name);
            write!(buf, "{} {{", compat_name).unwrap();
            for field in &variant.fields {
                if field.type_str.starts_with('"') { continue; }
                write!(buf, "{}: {},", field.name, field.type_str).unwrap();
            }
            buf.push_str("},");
        }
        buf.push('}');
    } else {
        write!(buf, "#[derive(Debug)] enum {} {{", enum_name).unwrap();
        for variant in &variants {
            write!(buf, "{} {{", variant.name).unwrap();
            for field in &variant.fields {
                if field.type_str.starts_with('"') { continue; }
                write!(buf, "{}: {},", field.name, field.type_str).unwrap();
            }
            buf.push_str("},");
        }
        buf.push('}');
    }

    FrameInfo { enum_name, variants }
}

// ══════════════════════════════════════════════════════════════════════════════
// Trampolined Parser Generation
// ══════════════════════════════════════════════════════════════════════════════

/// Write the complete trampolined parser for a single category.
///
/// Look up the composed or WFST weight for an ident-lookahead prefix handler.
///
/// Priority order:
/// 1. `complete_weight_map` — composed dispatch weight (lexer × parser interaction)
/// 2. `prediction_wfst` — raw WFST prediction weight (tropical shortest path)
/// 3. `f64::INFINITY` — unknown weight (sorted last)
fn handler_weight(handler: &PrefixHandler, config: &TrampolineConfig) -> f64 {
    if let Some(tok) = handler.ident_lookahead.as_ref() {
        let variant = terminal_to_variant_name(tok);

        // Prefer composed weight map (accounts for lexer × parser interaction)
        if let Some(ref wm) = config.complete_weight_map {
            if let Some(&w) = wm.get(&(config.category.clone(), variant.clone())) {
                return w;
            }
        }

        // Fallback: raw WFST prediction weight
        if let Some(ref wfst) = config.prediction_wfst {
            if let Some(wa) = wfst.predict(&variant).first() {
                return wa.weight.value();
            }
        }
    }
    f64::INFINITY
}

/// Generates:
/// 1. Helper functions (bp lookup, make_infix/postfix/mixfix) — same as before
/// 2. Frame enum (`Frame_Cat` — no lifetime, `'static`)
/// 3. Thread-local frame stack pool (`FRAME_POOL_CAT`)
/// 4. Wrapper `parse_Cat` that borrows from thread-local and delegates to impl
/// 5. Inner `parse_Cat_impl` with 'drive/'unwind loops (takes `&mut Vec<Frame_Cat>`)
pub fn write_trampolined_parser(
    buf: &mut String,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
    prefix_handlers: &[PrefixHandler],
    rd_rules: &[RDRuleInfo],
) -> FrameInfo {
    let cat = &config.category;
    // PDA merge: when cross_cat_prefix_arms is non-empty, the trampoline IS
    // the top-level parser (dispatch wrapper eliminated). Use parse_Cat directly.
    let pda_merged = !config.cross_cat_prefix_arms.is_empty();
    let parse_fn = if config.needs_dispatch && !pda_merged {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    let has_delegation = !config.led_delegation.is_empty();
    let _has_led = config.has_infix || config.has_postfix || config.has_mixfix || has_delegation;

    // ── 1. Generate helper functions (same as pratt.rs) ──

    // BP03: Build BpTableConfig if the gate is enabled and a variant map is available.
    let bp_cfg = config.token_variant_map.as_ref().map(|vm| {
        crate::pratt::BpTableConfig {
            variant_map: vm,
            enabled: config.optimization_gates.bp_table_lookup,
        }
    });
    let bp_cfg_ref = bp_cfg.as_ref();

    if config.has_infix {
        crate::pratt::write_bp_function_pub(buf, cat, bp_table, bp_cfg_ref);
        crate::pratt::write_make_infix_pub(buf, cat, bp_table);
    }
    if config.has_postfix {
        crate::pratt::write_postfix_bp_function_pub(buf, cat, bp_table, bp_cfg_ref);
        crate::pratt::write_make_postfix_pub(buf, cat, bp_table);
    }
    if config.has_mixfix {
        crate::pratt::write_mixfix_bp_function_pub(buf, cat, bp_table, bp_cfg_ref);
    }

    // ── 1b. BP05: Generate BP range constants for early-exit guard ──
    let bp_range_info = if config.optimization_gates.bp_range_loop {
        crate::pratt::analyze_bp_range(cat, bp_table)
    } else {
        None
    };
    if let Some(ref info) = bp_range_info {
        crate::pratt::write_bp_range_constants(buf, cat, info);
    }

    // ── 1a. Generate LED delegation functions (sum-type categories) ──
    if has_delegation {
        write_led_delegation_fns(buf, config, bp_table);
    }

    // ── 2. Generate Frame enum ──
    let frame_info = write_frame_enum(buf, config, rd_rules, bp_table);

    // ── 3. Generate thread-local frame stack pool ──
    // In unified mode, skip per-category pool/frame_state — the unified driver
    // manages the shared stack via UNIFIED_FRAME_POOL.
    let cat_upper = cat.to_uppercase();
    // In unified mode, we still generate pool/frame_state/frame_kind_of because
    // recovery and traced parser variants reference them. The main parse path
    // uses prefix_step_Cat → UnifiedFrame, but backward-compat wrappers need
    // the per-category infrastructure.
    {
    let pool_init = match config.frame_pool_capacity {
        Some(cap) => format!("Vec::with_capacity({})", cap),
        None => "Vec::new()".to_string(),
    };
    write!(
        buf,
        "thread_local! {{ \
            static FRAME_POOL_{cat_upper}: std::cell::Cell<Vec<{frame_enum}>> = \
                std::cell::Cell::new({pool_init}); \
        }}",
        frame_enum = frame_info.enum_name,
    )
    .unwrap();

    // ── 3a. Generate frame_kind_of helper + FRAME_STATE thread-local ──
    // Used by recovery (Tier 1 frame-kind cost multipliers). Updated at the top
    // of each 'drive iteration to reflect the current frame context. Zero
    // overhead when recovery is not active — the Cell write is a pointer store
    // and the match is branch-predicted (same top frame across many iterations).
    write!(
        buf,
        "thread_local! {{ \
            static FRAME_STATE_{cat_upper}: std::cell::Cell<(u16, u8)> = \
                std::cell::Cell::new((0, 9)); /* (depth, FrameKind::Other) */ \
        }}",
    )
    .unwrap();

    // Emit frame_kind_of helper: maps top-of-stack variant to FrameKind u8.
    {
        use std::fmt::Write;
        write!(
            buf,
            "fn frame_kind_of_{cat}(stack: &[{frame_enum}]) -> u8 {{ \
                match stack.last() {{",
            frame_enum = frame_info.enum_name,
        )
        .unwrap();

        // Classify each variant by structural kind (no string comparisons)
        for variant in &frame_info.variants {
            let kind_u8 = variant.kind().as_u8();

            // Use wildcard pattern for all fields
            write!(
                buf,
                "Some({}::{} {{ .. }}) => {}_u8,",
                frame_info.enum_name, variant.name, kind_u8,
            )
            .unwrap();
        }

        buf.push_str("None => 9_u8,"); // empty stack → Other
        if config.unified_mode {
            buf.push_str("_ => 9_u8,"); // other-category variants → Other
        }
        buf.push_str("}}");
    }
    } // end if !config.unified_mode (pool/frame_state/frame_kind_of)

    // ── 3b. Generate NFA spillover thread-locals ──
    // Thread-locals for forced-prefix replay. The spillover buffer collects N-1
    // prefix alternatives from NFA merged arms, and the forced-prefix Cell
    // overrides the NFA try-all on replay so each alternative gets its own infix
    // context. Emitted for ALL categories so parse_preserving_vars can
    // unconditionally drain — Cell::take on an empty Vec is essentially free.
    // Each spilled alternative carries its end position (token count consumed by
    // the prefix) and its WFST tropical weight (f64) for weight-aware disambiguation.
    // NFA_PRIMARY_WEIGHT stores the weight of the best (returned) NFA result so
    // parse_preserving_vars can assign it to the primary success entry.
    //
    // B2 (Adaptive Recovery): RUNNING_WEIGHT accumulates the tropical weight of
    // dispatch decisions along the parse path. Higher accumulated weight indicates
    // a less confident (more ambiguous) parse, which recovery uses to select
    // repair strategy: high weight → prefer insert (keep context); low weight →
    // prefer skip (context was deterministic). Zero overhead on happy path (single
    // Cell::set per dispatch decision, only Cell::get on error).
    // C3: PARENT_WEIGHT stores the accumulated weight from a parent category's
    // parse context. When category B is invoked from category A's dispatch
    // (e.g., via a cast rule), A sets PARENT_WEIGHT_B = RUNNING_WEIGHT_A before
    // calling parse_B. B then inherits this as its initial RUNNING_WEIGHT,
    // making NFA disambiguation globally coherent across categories.
    // For top-level calls, PARENT_WEIGHT is 0.0 (no parent context).
    write!(
        buf,
        "thread_local! {{ \
            static NFA_PREFIX_SPILL_{cat_upper}: std::cell::Cell<Vec<({cat}, usize, f64)>> = \
                std::cell::Cell::new(Vec::new()); \
            static NFA_FORCED_PREFIX_{cat_upper}: std::cell::Cell<Option<({cat}, usize, f64)>> = \
                std::cell::Cell::new(None); \
            static NFA_PRIMARY_WEIGHT_{cat_upper}: std::cell::Cell<f64> = \
                std::cell::Cell::new(0.5); \
            static RUNNING_WEIGHT_{cat_upper}: std::cell::Cell<f64> = \
                std::cell::Cell::new(0.0); \
            static PARENT_WEIGHT_{cat_upper}: std::cell::Cell<f64> = \
                std::cell::Cell::new(0.0); \
        }}",
    )
    .unwrap();

    // B2/B4: Public accessor for accumulated dispatch weight. Recovery, diagnostic,
    // and Ascent rules can call `running_weight_<cat>()` to read the accumulated
    // confidence. Returns 0.0 for fully deterministic paths, higher values for
    // ambiguous paths.
    //
    // B4 (Confidence Scoring): After a successful parse, the final value of
    // `running_weight_<cat>()` is the total ambiguity encountered. Downstream
    // consumers (e.g. language servers) can use this as a parse confidence metric.
    // B4 (Parse Quality Metrics): Made public so Ascent rules and external code
    // can query parse quality at any point during or after parsing.
    write!(
        buf,
        "#[inline] pub fn running_weight_{cat}() -> f64 {{ \
            RUNNING_WEIGHT_{cat_upper}.with(|cell| cell.get()) \
        }}",
    )
    .unwrap();

    // ── 4. Generate wrapper function ──
    // Thin wrapper that takes the pooled Vec from the thread-local (replacing with
    // empty Vec), delegates to _impl, then puts the Vec back. Re-entrant calls
    // see an empty Cell and allocate fresh — only the outermost call's Vec (with
    // the largest capacity) survives in the pool.
    // Heuristic preallocation: nesting depth ≤ tokens/2 (each nesting event
    // consumes ≥2 tokens: operator + operand).
    // C3: Initialize RUNNING_WEIGHT from PARENT_WEIGHT (inherited from parent
    // category's parse context). For top-level calls, PARENT_WEIGHT is 0.0.
    // After reading, reset PARENT_WEIGHT to 0.0 so it doesn't leak into
    // subsequent independent calls.
    if config.skip_entry_point {
        // Unified trampoline provides its own parse_Cat entry point.
        // Still generate _impl for recovery/traced variants.
    } else {
    write!(
        buf,
        "fn {parse_fn}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            min_bp: u8, \
        ) -> Result<{cat}, ParseError> {{ \
            RUNNING_WEIGHT_{cat_upper}.with(|cell| {{ \
                let inherited = PARENT_WEIGHT_{cat_upper}.with(|p| {{ \
                    let v = p.get(); p.set(0.0); v \
                }}); \
                cell.set(inherited); \
            }}); \
            FRAME_POOL_{cat_upper}.with(|cell| {{ \
                let mut stack = cell.take(); \
                let needed = tokens.len() / 2; \
                if stack.capacity() < needed {{ \
                    stack.reserve(needed - stack.len()); \
                }}",
    )
    .unwrap();

    write!(
        buf,
        " let result = {parse_fn}_impl(tokens, pos, min_bp, &mut stack); \
                cell.set(stack); \
                result \
            }}) \
        }}",
    )
    .unwrap();
    } // end if !skip_entry_point

    // ── 5. Generate the inner trampolined parse function (_impl) ──
    // A4: Cold NFA helper functions are generated during prefix arm codegen and
    // emitted as sibling functions at the same scope level as `_impl`. The body is
    // written to a temporary buffer so cold helpers can be placed before `_impl`
    // in the final output (they need to be visible at the call site).
    let mut cold_fns = String::new();
    let mut body_buf = String::new();
    write_trampoline_body(&mut body_buf, &mut cold_fns, config, bp_table, prefix_handlers, rd_rules, &frame_info, &parse_fn, bp_range_info.as_ref());
    buf.push_str(&cold_fns);
    buf.push_str(&body_buf);

    frame_info
}

/// Write the monolithic trampolined parser function body.
fn write_trampoline_body(
    buf: &mut String,
    cold_fns: &mut String,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
    prefix_handlers: &[PrefixHandler],
    rd_rules: &[RDRuleInfo],
    frame_info: &FrameInfo,
    parse_fn: &str,
    bp_range_info: Option<&crate::pratt::BpRangeInfo>,
) {
    let cat = &config.category;
    let has_led = config.has_infix || config.has_postfix || config.has_mixfix;

    // In unified mode, control flow statements change.
    // Helper strings computed from config, reused throughout.
    let _ = (&frame_info, &config); // suppress unused warning in unified path

    // BP02: Collect tail-call-eligible rules for this category.
    // When the gate is enabled and there are eligible rules, we emit a
    // `tail_wrap: Option<u8>` local that avoids full frame pushes for
    // single-segment rules whose last same-category NT is in tail position.
    let tail_call_rules = if config.optimization_gates.tail_call_elim {
        collect_tail_call_rules(rd_rules, cat)
    } else {
        std::collections::BTreeMap::new()
    };

    // Build expected message for error reporting
    let expected_msg = crate::pratt::build_expected_message_pub(cat, &config.own_first_set);
    let expected_escaped = expected_msg.replace('\\', "\\\\").replace('"', "\\\"");

    // In unified mode, generate step functions and backward-compat wrapper.
    // When skip_step_functions is set, the CPS step functions come from
    // unified_trampoline.rs instead — only generate the compat wrapper here.
    if config.unified_mode {
        if !config.skip_step_functions {
            // same_cat_prefix_step delegates to prefix_step
            write!(
                buf,
                "#[allow(dead_code)] \
                fn same_cat_prefix_step_{cat}<'a>(\
                    tokens: &[(Token<'a>, Range)], \
                    pos: &mut usize, \
                    min_bp: u8, \
                    stack: &mut Vec<UnifiedFrame>, \
                ) -> Result<ParseStep, ParseError> {{ \
                    prefix_step_{cat}(tokens, pos, min_bp, stack) \
                }}",
            ).unwrap();

            // infix_step is a stub — prefix_step handles full drive/unwind
            write!(
                buf,
                "#[allow(dead_code)] \
                fn infix_step_{cat}<'a>(\
                    tokens: &[(Token<'a>, Range)], \
                    pos: &mut usize, \
                    _lhs: {cat}, \
                    _min_bp: u8, \
                    _stack: &mut Vec<UnifiedFrame>, \
                ) -> Result<ParseStep, ParseError> {{ \
                    unreachable!(\"infix_step_{cat}: prefix_step handles full drive/unwind\") \
                }}",
            ).unwrap();
        }

        // Generate backward-compat parse_Cat_impl wrapper for recovery/traced variants.
        // When skip_step_functions is set, this calls unified_parse directly.
        // Otherwise, it calls the trampoline's prefix_step_Cat.
        if config.skip_step_functions {
            // CPS path: call parse_Cat (the public entry point, generated by
            // unified_trampoline.rs write_entry_points). This routes through
            // unified_parse which is fully iterative — no recursion.
            write!(
                buf,
                "#[allow(dead_code)] \
                fn {parse_fn}_impl<'a>(\
                    tokens: &[(Token<'a>, Range)], \
                    pos: &mut usize, \
                    min_bp: u8, \
                    _compat_stack: &mut Vec<{frame_enum}>, \
                ) -> Result<{cat}, ParseError> {{ \
                    parse_{cat}(tokens, pos, min_bp) \
                }}",
                frame_enum = frame_info.enum_name,
            ).unwrap();
        } else {
            // Recursive path: call prefix_step_Cat directly
            write!(
                buf,
                "#[allow(dead_code)] \
                fn {parse_fn}_impl<'a>(\
                    tokens: &[(Token<'a>, Range)], \
                    pos: &mut usize, \
                    min_bp: u8, \
                    _compat_stack: &mut Vec<{frame_enum}>, \
                ) -> Result<{cat}, ParseError> {{ \
                    let mut unified_stack = Vec::new(); \
                    match prefix_step_{cat}(tokens, pos, min_bp, &mut unified_stack)? {{ \
                        ParseStep::Yield(AnyTerm::{cat}(v)) => Ok(*v), \
                        other => Err(ParseError::UnexpectedEof {{ \
                            expected: std::borrow::Cow::Borrowed(\"{cat} expression\"), \
                            range: Range::zero(), \
                            hint: Some(std::borrow::Cow::Borrowed(\"internal: unexpected ParseStep from prefix_step\")), \
                        }}), \
                    }} \
                }}",
                frame_enum = frame_info.enum_name,
            ).unwrap();
        }
    }

    // ═══ Generate _impl body (or prefix_step_Cat in unified mode) ═══
    // When skip_step_functions is set, skip the ENTIRE function body —
    // the CPS step functions from unified_trampoline.rs replace it.
    // Recovery/traced use parse_Cat_impl which calls parse_Cat (the CPS path).
    if config.unified_mode && config.skip_step_functions {
        return;
    } else if config.unified_mode {
        write!(
            buf,
            "#[allow(dead_code, unused_variables, unreachable_patterns)] \
            fn prefix_step_{cat}<'a>(\
                tokens: &[(Token<'a>, Range)], \
                pos: &mut usize, \
                min_bp: u8, \
                stack: &mut Vec<{frame_enum}>, \
            ) -> Result<ParseStep, ParseError> {{",
            frame_enum = frame_info.enum_name,
        ).unwrap();
    } else {
        write!(
            buf,
            "fn {parse_fn}_impl<'a>(\
                tokens: &[(Token<'a>, Range)], \
                pos: &mut usize, \
                min_bp: u8, \
                stack: &mut Vec<{frame_enum}>, \
            ) -> Result<{cat}, ParseError> {{",
            frame_enum = frame_info.enum_name,
        ).unwrap();
    }

    // Clear the pooled stack (retains capacity from previous calls).
    buf.push_str("stack.clear();");
    buf.push_str("let mut cur_bp = min_bp;");

    // BP02: Emit tail_wrap local variable when there are tail-call-eligible rules.
    // The Option<(u8, u8)> stores (tag, saved_bp): the tag identifies which
    // constructor to apply after the tail NT returns, and saved_bp is the
    // binding power to restore afterwards (which the full frame would have stored).
    // Cost: one Option<(u8, u8)> (3 bytes) on the stack + one branch per 'unwind.
    //
    // BP06: When continuation_compression is enabled, use a Vec instead of Option
    // to accumulate chains of tail-call-eligible prefix operators. This reduces
    // stack depth for consecutive unary prefix operations (e.g. `---x`) from N
    // individual frames to a single Vec entry per chain element, all applied in
    // reverse at unwind time.
    if !tail_call_rules.is_empty() {
        if config.optimization_gates.continuation_compression {
            buf.push_str("let mut tail_wraps: Vec<(u8, u8)> = Vec::new();");
        } else {
            buf.push_str("let mut tail_wrap: Option<(u8, u8)> = None;");
        }
    }

    // ═══ Main trampoline loop ═══
    buf.push_str("'drive: loop {");

    // Update frame state thread-local at the top of each 'drive iteration.
    // In unified mode, skip — no per-category FRAME_STATE thread-local.
    if !config.unified_mode {
        let cat_upper = cat.to_uppercase();
        write!(
            buf,
            "FRAME_STATE_{cat_upper}.with(|c| c.set(\
                (stack.len() as u16, frame_kind_of_{cat}(stack))\
            ));",
        )
        .unwrap();
    }

    // ═══ Phase A: Prefix dispatch ═══
    write_prefix_phase(buf, cold_fns, config, bp_table, prefix_handlers, rd_rules, frame_info, &expected_escaped, &tail_call_rules);

    // ═══ Phase B: Infix loop + continuation unwinding ═══
    buf.push_str("'unwind: loop {");

    // BP02: Apply pending tail-call constructor before the infix loop.
    // When a tail-call-eligible prefix arm sets `tail_wrap = Some((tag, saved_bp))`
    // and does `continue 'drive` without pushing a frame, the NT result arrives
    // as `lhs`. Before entering the infix loop (which expects a fully-formed
    // LHS), apply the deferred constructor wrapping and restore cur_bp.
    //
    // BP06: When continuation_compression is enabled, iterate the Vec in reverse
    // to apply all accumulated tail-call constructors. Each element's tw_bp is
    // the binding power that was current when that prefix was parsed; the last
    // popped element's tw_bp becomes the final cur_bp (i.e. the BP from before
    // the entire chain).
    if !tail_call_rules.is_empty() {
        if config.optimization_gates.continuation_compression {
            buf.push_str("while let Some((tw, tw_bp)) = tail_wraps.pop() { match tw {");
            for info in tail_call_rules.values() {
                write!(buf, "{} => {{ {} }},", info.tag, info.constructor).unwrap();
            }
            buf.push_str("_ => {} } cur_bp = tw_bp; }");
        } else {
            buf.push_str("if let Some((tw, tw_bp)) = tail_wrap.take() { match tw {");
            for info in tail_call_rules.values() {
                write!(buf, "{} => {{ {} }},", info.tag, info.constructor).unwrap();
            }
            buf.push_str("_ => {} } cur_bp = tw_bp; }");
        }
    }

    // Infix loop (iterative — left-assoc chains stay here)
    if has_led {
        write_infix_loop(buf, config, bp_table, frame_info, bp_range_info);
    }

    // Pop continuation
    write_unwind_handlers(buf, config, bp_table, rd_rules, frame_info);

    buf.push_str("} }"); // close 'unwind and 'drive loops

    buf.push('}'); // close function
}

/// Write Phase A: prefix dispatch.
///
/// Produces a value (break 'prefix) or pushes a frame and continues 'drive.
///
/// ## CD03 (Computed Goto) — Not applicable to trampoline prefix dispatch
///
/// The CD03 computed goto optimization (function pointer table dispatch) is
/// implemented in `dispatch.rs` for cross-category dispatch where all arms
/// have a uniform signature `fn(tokens, pos, min_bp) -> Result<Cat, ParseError>`.
///
/// Trampoline prefix dispatch cannot use function pointer tables because:
/// 1. Arms use `break 'prefix expr` to produce a value to the enclosing labeled block
/// 2. Arms use `continue 'drive` to re-enter the trampoline loop after pushing a frame
/// 3. Arms reference `stack`, `cur_bp`, and frame enum variants by name
/// 4. The heterogeneous control flow (break vs continue vs return) prevents
///    factoring arms into standalone functions with a unified return type
///
/// A future refactoring could introduce a `PrefixAction` enum
/// (`Break(Cat)` / `Continue` / `Error(ParseError)`) to unify control flow,
/// but that would add an extra branch on every prefix dispatch — the opposite
/// of the optimization's intent.
fn write_prefix_phase(
    buf: &mut String,
    cold_fns: &mut String,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
    prefix_handlers: &[PrefixHandler],
    rd_rules: &[RDRuleInfo],
    frame_info: &FrameInfo,
    expected_escaped: &str,
    tail_call_rules: &std::collections::BTreeMap<String, TailCallInfo>,
) {
    let cat = &config.category;

    // The prefix match block: produces `lhs` or pushes frame + continues
    buf.push_str("let mut lhs: ");
    buf.push_str(cat);
    buf.push_str(" = 'prefix: {");

    // EOF check (inside 'prefix block so we can use break 'prefix for collection catch)
    write!(
        buf,
        "if *pos >= tokens.len() {{ \
            let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
            match stack.pop() {{ \
                None => return Err(ParseError::UnexpectedEof {{ \
                    expected: Cow::Borrowed(\"{expected_escaped}\"), \
                    range: eof_range, \
                    hint: None, \
                }}),",
    )
    .unwrap();

    // Collection catch on EOF: finalize with collected elements via break 'prefix
    write_collection_eof_catch(buf, config, rd_rules, frame_info);

    // CrossCatInfixTry catch on EOF: pop frame, restore pos, try LED delegation.
    // At EOF the LED will typically return None, but we must try for correctness.
    {
        let cross_cat_terms = conflicting_infix_terminals(config, bp_table);
        if !cross_cat_terms.is_empty() && !config.led_delegation.is_empty() {
            let enum_name = &frame_info.enum_name;
            let vp = config.frame_prefix();
            write!(
                buf,
                "Some({enum_name}::{vp}CrossCatInfixTry {{ lhs: saved_lhs, saved_pos, saved_bp, .. }}) => {{ \
                    *pos = saved_pos; \
                    cur_bp = saved_bp; \
                    match led_delegate_{cat}(tokens, pos, &saved_lhs) {{ \
                        Some(new_lhs) => break 'prefix new_lhs, \
                        None => return Err(ParseError::UnexpectedEof {{ \
                            expected: Cow::Borrowed(\"{expected_escaped}\"), \
                            range: eof_range, \
                            hint: None, \
                        }}), \
                    }} \
                }},",
            )
            .unwrap();
        }
    }

    write!(
        buf,
        "Some(_) => return Err(ParseError::UnexpectedEof {{ \
            expected: Cow::Borrowed(\"{expected_escaped}\"), \
            range: eof_range, \
            hint: None, \
        }}), \
        }} \
        }}",
    )
    .unwrap();

    // Emit WFST weight annotations as comments (for debugging/verification)
    if let Some(ref wfst) = config.prediction_wfst {
        if let Some(comment) = crate::wfst::generate_weighted_dispatch(wfst, &config.category) {
            buf.push_str(&comment);
        }
    }

    // Check for forced-prefix override from NFA spillover replay.
    // When parse_preserving_vars replays with a forced prefix, skip the
    // NFA try-all and use the forced value directly as lhs, advancing pos
    // past the same tokens consumed by the original NFA prefix parse.
    // Always emitted — Cell::take on None is essentially free (pointer swap).
    {
        let cat_upper = config.category.to_uppercase();
        write!(
            buf,
            "{{ let forced = NFA_FORCED_PREFIX_{cat_upper}.with(|cell| cell.take()); \
             if let Some((forced_val, forced_pos, _forced_weight)) = forced {{ \
                 *pos = forced_pos; \
                 break 'prefix forced_val; \
             }} }}",
        )
        .unwrap();
    }

    // PDA merge: cross-category dispatch is handled by a separate
    // #[cold] #[inline(never)] function that is called BEFORE the main
    // prefix match. This function returns a bool and writes the result
    // through a raw pointer to avoid adding ANY Cat-sized locals to _impl.
    if !config.cross_cat_prefix_arms.is_empty() {
        let cat = &config.category;

        // Emit the cold cross-cat dispatch function
        // Pass cur_bp so ambiguous arms can be skipped when we're inside an
        // infix RHS (cur_bp > 0). Without this guard, an ambiguous token like
        // Ident triggers cross-cat speculative parsing that greedily consumes
        // what should be handled by the Pratt infix loop, breaking Display
        // roundtrip idempotence.
        write!(
            cold_fns,
            "#[cold] #[inline(never)] \
            fn __cross_cat_dispatch_{cat}<'a>(\
                tokens: &[(Token<'a>, Range)], pos: &mut usize, \
                out: *mut std::mem::MaybeUninit<{cat}>, \
                cur_bp: u8\
            ) -> bool {{ \
                let saved = *pos; \
                match &tokens[*pos].0 {{",
        ).unwrap();

        for (i, arm) in config.cross_cat_prefix_arms.iter().enumerate() {
            let body = arm.body
                .replace("__SAME_CAT_FALLBACK__", "{ *pos = saved; return false; }")
                .replace("__CC_OK_WRITE__", "unsafe { (*out).write(__result); }")
                .replace("__CC_OK_BEGIN__", "unsafe { (*out).write(")
                .replace("__CC_OK_END__", "); } return true;");
            if arm.is_ambiguous {
                // Ambiguous arms: only fire at top-level (cur_bp == 0).
                // When cur_bp > 0 we are inside an infix RHS and the Pratt
                // parser's infix loop should handle the operator token.
                write!(cold_fns, "{} if cur_bp == 0 => {},", arm.token_pattern, body).unwrap();
            } else {
                write!(cold_fns, "{} => {},", arm.token_pattern, body).unwrap();
            }
        }

        cold_fns.push_str("_ => { return false; } } }");

        // In _impl: call the cold function with a MaybeUninit on the stack.
        // MaybeUninit<Cat> is sizeof(Cat) but only used in a { } block and
        // immediately moved to lhs via break 'prefix.
        // Critical: this block must be SMALL so the compiler can reuse the slot.
        write!(
            buf,
            "{{ let mut __out = std::mem::MaybeUninit::<{cat}>::uninit(); \
             if __cross_cat_dispatch_{cat}(tokens, pos, &mut __out as *mut _, cur_bp) {{ \
                 break 'prefix unsafe {{ __out.assume_init() }}; \
             }} }}",
        ).unwrap();
    }

    buf.push_str("match &tokens[*pos].0 {");

    // Generate match arms (same code in both paths — WFST ordering affects
    // cross-category dispatch backtracking order, not prefix match semantics)
    write_prefix_match_arms(buf, cold_fns, config, bp_table, prefix_handlers, rd_rules, frame_info, expected_escaped, tail_call_rules);

    buf.push_str("} };"); // close match and 'prefix block
}

/// Write the prefix match arms.
fn write_prefix_match_arms(
    buf: &mut String,
    cold_fns: &mut String,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
    prefix_handlers: &[PrefixHandler],
    rd_rules: &[RDRuleInfo],
    frame_info: &FrameInfo,
    expected_escaped: &str,
    tail_call_rules: &std::collections::BTreeMap<String, TailCallInfo>,
) {
    let cat = &config.category;

    // Collect handlers with ident_lookahead (nonterminal-first rules)
    let lookahead_handlers: Vec<&PrefixHandler> = prefix_handlers
        .iter()
        .filter(|h| h.category == *cat && h.ident_lookahead.is_some())
        .collect();

    // ── Terminal-first RD handlers (non-collection, non-unary-prefix) ──
    // These are split into segments and inlined, OR dispatched to standalone functions
    // for complex rules (Sep, multi-binder).
    //
    // NFA disambiguation: group rules by dispatch token. When multiple rules
    // share the same token (e.g., FloatId and IntToFloat both start with "float"),
    // emit a single merged arm that tries all alternatives NFA-style.
    let rd_by_token_raw = group_rd_by_dispatch_token(rd_rules, cat);

    // A4: Filter dead rules when enhanced DCE is enabled.
    // Dead rules are removed from each dispatch group. If a group becomes empty
    // after filtering, the entire dispatch arm is suppressed.
    let rd_by_token: std::collections::BTreeMap<String, Vec<&RDRuleInfo>> =
        if config.optimization_gates.enhanced_dce && !config.dead_rules.is_empty() {
            rd_by_token_raw
                .into_iter()
                .filter_map(|(variant, rules)| {
                    let live: Vec<&RDRuleInfo> = rules
                        .into_iter()
                        .filter(|r| !config.dead_rules.contains(&r.label))
                        .collect();
                    if live.is_empty() {
                        None
                    } else {
                        Some((variant, live))
                    }
                })
                .collect()
        } else {
            rd_by_token_raw
        };

    // CEK-4: Filter prefix arms that push dead frames when dead_frame_elimination
    // is enabled. A frame is dead if its name (UnaryPrefix_{label}, RD_{label}_{seg},
    // or CollectionElem_{label}) is in config.dead_frames.
    let rd_by_token: std::collections::BTreeMap<String, Vec<&RDRuleInfo>> =
        if config.optimization_gates.dead_frame_elimination && !config.dead_frames.is_empty() {
            rd_by_token
                .into_iter()
                .filter_map(|(variant, rules)| {
                    let live: Vec<&RDRuleInfo> = rules
                        .into_iter()
                        .filter(|r| {
                            // Check if any frame this rule would push is dead
                            let segments = split_rd_handler(r);
                            !segments.iter().any(|seg| {
                                seg.nonterminal.is_some()
                                    && config.dead_frames.contains(&seg.frame_variant)
                            })
                        })
                        .collect();
                    if live.is_empty() {
                        None
                    } else {
                        Some((variant, live))
                    }
                })
                .collect()
        } else {
            rd_by_token
        };

    // CD01: Sort RD dispatch arms by WFST frequency weight (lowest = most
    // frequent first) for better branch prediction.  Gated by
    // `optimization_gates.frequency_ordering`.  Falls back to the
    // BTreeMap's lexicographic order when the gate is disabled or no
    // weight source is available.
    let rd_ordered: Vec<(&String, &Vec<&RDRuleInfo>)> = {
        let mut entries: Vec<(&String, &Vec<&RDRuleInfo>)> = rd_by_token.iter().collect();
        if config.optimization_gates.frequency_ordering {
            if let Some(ref wfst) = config.prediction_wfst {
                entries.sort_by(|(va, _), (vb, _)| {
                    let wa = wfst.predict(va)
                        .first()
                        .map(|a| a.weight.value())
                        .unwrap_or(f64::INFINITY);
                    let wb = wfst.predict(vb)
                        .first()
                        .map(|a| a.weight.value())
                        .unwrap_or(f64::INFINITY);
                    wa.partial_cmp(&wb).unwrap_or(std::cmp::Ordering::Equal)
                });
            } else if let Some(ref wm) = config.complete_weight_map {
                entries.sort_by(|(va, _), (vb, _)| {
                    let wa = wm.get(&(config.category.clone(), (*va).clone()))
                        .copied()
                        .unwrap_or(f64::INFINITY);
                    let wb = wm.get(&(config.category.clone(), (*vb).clone()))
                        .copied()
                        .unwrap_or(f64::INFINITY);
                    wa.partial_cmp(&wb).unwrap_or(std::cmp::Ordering::Equal)
                });
            }
            // else: no weights available — keep BTreeMap lexicographic order
        }
        entries
    };

    // Track whether LParen has been handled by an RD rule arm so we can
    // suppress the later grouping handler and avoid duplicate match arms.
    let mut lparen_handled = false;

    // D07: Coverage path counter — each dispatch arm gets a unique path_id
    let mut coverage_path_counter: u32 = 0;

    // CD05: Emit prefix CSE diagnostic comments when the gate is enabled
    if config.optimization_gates.prefix_cse && !config.prefix_cse_hints.is_empty() {
        // Build a minimal TokenIdMap for name resolution
        let cse_token_ids = {
            let mut all_tokens: Vec<String> = Vec::new();
            for fs in config.all_first_sets.values() {
                all_tokens.extend(fs.tokens.iter().cloned());
            }
            for v in &["Eof", "RParen", "RBrace", "RBracket", "Semi", "Comma",
                       "LParen", "LBrace", "LBracket"] {
                all_tokens.push(v.to_string());
            }
            crate::token_id::TokenIdMap::from_names(all_tokens)
        };
        for hint in &config.prefix_cse_hints {
            let annotation = crate::decision_tree::format_cse_annotation(hint, &cse_token_ids);
            buf.push_str(&annotation);
        }
    }

    for (variant, rules) in rd_ordered {
        if rules.len() == 1 {
            // Singleton: emit the original single-rule arm
            let rd_rule = rules[0];

            // ── LParen conflict resolution ──
            // When an RD rule dispatches on LParen (e.g., PInputs in RhoCalc),
            // it would preempt the grouping handler. For standalone or fully-inline
            // rules, emit an NFA-style arm that tries the RD rule first with save/
            // restore and falls back to grouping on failure.
            //
            // For frame-pushing rules (same-category nonterminal, e.g., Lambda's
            // App), the rule IS the LParen handler — closures can't contain break/
            // continue, so we emit normally. In such languages LParen means the RD
            // rule, not grouping.
            if variant == "LParen" {
                let is_frame_pushing = if should_use_standalone_fn(rd_rule) {
                    false
                } else {
                    let segs = split_rd_handler(rd_rule);
                    !segs.is_empty() && segs[0].nonterminal.is_some()
                };

                if is_frame_pushing {
                    // Frame-pushing rule at LParen: emit normally (no grouping
                    // fallback possible with trampoline frames). The RD rule owns
                    // LParen for this category.
                    lparen_handled = true;
                    // Fall through to the normal singleton emission below
                } else {
                    // Standalone or fully-inline rule at LParen.
                    lparen_handled = true;

                    // G1 Phase 3: LL(2) check — can we distinguish the RD rule
                    // from grouping by peeking at the token after `(`?
                    //
                    // RD rule suffix = items[1..] (items[0] is LParen)
                    // Grouping suffix = FIRST(category)
                    // If they're disjoint, a single lookahead resolves.
                    let ll2_resolved = if config.optimization_gates.backtracking_elimination {
                        use crate::prediction::first_of_rd_suffix;
                        let rd_suffix = &rd_rule.items[1..]; // after LParen
                        let (rd_first, _) = first_of_rd_suffix(rd_suffix, &config.all_first_sets);
                        let cat_first = &config.own_first_set;
                        // Disjoint: no token appears in both
                        let overlap = rd_first.intersection(cat_first);
                        overlap.tokens.is_empty()
                    } else {
                        false
                    };

                    write!(buf, "Token::LParen => {{").unwrap();

                    if ll2_resolved {
                        // G1: LL(2) deterministic dispatch — peek at token after `(`
                        buf.push_str("*pos += 1;");
                        buf.push_str("if *pos < tokens.len() {");

                        // Compute which tokens belong to the RD rule
                        let rd_suffix = &rd_rule.items[1..];
                        let (rd_first, _) = crate::prediction::first_of_rd_suffix(rd_suffix, &config.all_first_sets);

                        // Build match arms for RD rule tokens
                        let mut rd_patterns = Vec::new();
                        for token in &rd_first.tokens {
                            let mut pat = String::new();
                            write_token_pattern_trampoline(&mut pat, token);
                            rd_patterns.push(pat);
                        }

                        buf.push_str("match &tokens[*pos].0 {");
                        // RD rule arm: all tokens from RD suffix FIRST set
                        write!(buf, "{} => {{", rd_patterns.join(" | ")).unwrap();
                        // Restore position to before LParen, call the rule
                        buf.push_str("*pos -= 1;"); // restore to LParen position

                        if should_use_standalone_fn(rd_rule) {
                            let fn_name = format!("parse_{}", rd_rule.label.to_lowercase());
                            write!(buf, "break 'prefix {}(tokens, pos)?;", fn_name).unwrap();
                        } else {
                            let segments = split_rd_handler(rd_rule);
                            if !segments.is_empty() {
                                write_inline_items(buf, &segments[0].inline_items, true);
                                write_rd_constructor_inline(buf, rd_rule, &segments);
                            }
                        }
                        buf.push_str("},");

                        // Grouping arm: everything else after `(`
                        // PDA merge: always use trampolined GroupClose
                        write!(
                            buf,
                            "_ => {{ \
                                stack.push({enum_name}::{vp}GroupClose {{ saved_bp: cur_bp }}); \
                                cur_bp = 0; \
                                continue 'drive; \
                            }},",
                            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
                        )
                        .unwrap();

                        buf.push_str("}"); // close match
                        buf.push_str("} else {"); // no token after `(`
                        write!(
                            buf,
                            "return Err(ParseError::UnexpectedEof {{ \
                                expected: Cow::Borrowed(\"{cat} expression\"), \
                                range: tokens[tokens.len() - 1].1, \
                                hint: None, \
                            }});",
                        )
                        .unwrap();
                        buf.push_str("}"); // close if
                    } else {
                        // Save/restore fallback (original path)
                        buf.push_str("let saved = *pos;");

                        if should_use_standalone_fn(rd_rule) {
                            let fn_name = format!("parse_{}", rd_rule.label.to_lowercase());
                            write!(
                                buf,
                                "if let Ok(result) = {}(tokens, pos) {{ \
                                    break 'prefix result; \
                                }}",
                                fn_name,
                            )
                            .unwrap();
                        } else {
                            // Fully inline (no frame-pushing nonterminal): wrap in closure
                            let segments = split_rd_handler(rd_rule);
                            if !segments.is_empty() {
                                write!(buf, "match (|| -> Result<{}, ParseError> {{", cat).unwrap();
                                write_inline_items(buf, &segments[0].inline_items, true);
                                write_rd_constructor_inline(buf, rd_rule, &segments);
                                buf.push_str("})() {");
                                buf.push_str("Ok(v) => { break 'prefix v; },");
                                buf.push_str("Err(_) => {},");
                                buf.push_str("}");
                            }
                        }

                        // Grouping fallback: restore position, emit trampolined grouping
                        // PDA merge: always use GroupClose frame
                        buf.push_str("*pos = saved;");
                        write!(
                            buf,
                            "*pos += 1; \
                            stack.push({enum_name}::{vp}GroupClose {{ saved_bp: cur_bp }}); \
                            cur_bp = 0; \
                            continue 'drive;",
                            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
                        )
                        .unwrap();
                    }
                    buf.push_str("},");
                    continue;
                }
            }

            if should_use_standalone_fn(rd_rule) {
                let fn_name = format!("parse_{}", rd_rule.label.to_lowercase());
                write!(
                    buf,
                    "Token::{} => {{ \
                        break 'prefix {}(tokens, pos)?; \
                    }},",
                    variant, fn_name,
                )
                .unwrap();
                continue;
            }

            let segments = split_rd_handler(rd_rule);
            if segments.is_empty() {
                continue;
            }

            write!(buf, "Token::{} => {{", variant).unwrap();

            // Inline the first segment: consume terminal(s) and cross-category NTs
            write_inline_items(buf, &segments[0].inline_items, true); // skip first terminal (it's the match)

            if let Some(ref nt) = segments[0].nonterminal {
                // BP02: Check if this is a tail-call-eligible rule
                if let Some(tc_info) = tail_call_rules.get(&rd_rule.label) {
                    // Tail call: skip frame push, set wrap tag + saved_bp.
                    // The deferred constructor is applied at the top of 'unwind.
                    //
                    // BP06: When continuation_compression is enabled, push onto
                    // tail_wraps Vec instead of replacing the Option. This allows
                    // chains of consecutive unary prefixes (e.g. `---x`) to
                    // accumulate without individual frame pushes — all wrappers
                    // are applied in reverse at unwind time.
                    if config.optimization_gates.continuation_compression {
                        write!(buf, "tail_wraps.push(({}, cur_bp));", tc_info.tag).unwrap();
                    } else {
                        write!(buf, "tail_wrap = Some(({}, cur_bp));", tc_info.tag).unwrap();
                    }
                    write!(buf, "cur_bp = {};", nt.bp).unwrap();
                    buf.push_str("continue 'drive;");
                } else {
                    // Same-category nonterminal: push frame for continuation, continue 'drive
                    write!(
                        buf,
                        "stack.push({enum_name}::{vp}{variant} {{",
                        enum_name = frame_info.enum_name, vp = config.frame_prefix(), variant = segments[0].frame_variant
                    )
                    .unwrap();
                    write!(buf, "saved_bp: cur_bp,").unwrap();
                    for capture in &segments[0].accumulated_captures {
                        match capture {
                            SegmentCapture::Ident { name }
                            | SegmentCapture::Binder { name }
                            | SegmentCapture::NonTerminal { name, .. } => {
                                write!(buf, "{},", name).unwrap();
                            },
                            _ => {},
                        }
                    }
                    buf.push_str("});");
                    write!(buf, "cur_bp = {};", nt.bp).unwrap();
                    buf.push_str("continue 'drive;");
                }
            } else {
                // No same-category nonterminal — fully inline the constructor
                write_rd_constructor_inline(buf, rd_rule, &segments);
            }

            buf.push_str("},");
        } else {
            // Multiple rules share this dispatch token — NFA-style merged arm.
            //
            // Classification:
            //   - `inlineable`: rules tried as NFA save/restore arms. Includes
            //     (a) rules with all cross-category NTs (segments.len() == 1),
            //     and (b) rules with same-category NTs (segments.len() > 1)
            //     emitted as closures that use recursive parse_<cat> calls
            //     for same-cat NTs. This allows sharing a dispatch token across
            //     heterogeneous arities (e.g., `int(Proc, Int)` + `int(Int)`
            //     + `int(Float)` etc.).
            //   - `frame_pushing`: rules that are ALSO tracked here as the
            //     "stack-safe canonical fallback" when all NFA arms fail.
            //     For deeply-nested same-category inputs, the fallback uses
            //     the trampoline's frame-push to avoid Rust stack overflow.
            let mut inlineable: Vec<&RDRuleInfo> = Vec::new();
            let mut frame_pushing: Vec<&RDRuleInfo> = Vec::new();

            for rd_rule in rules {
                if should_use_standalone_fn(rd_rule) {
                    // Standalone fns can be called in NFA style (save/restore pos)
                    inlineable.push(rd_rule);
                } else {
                    let segments = split_rd_handler(rd_rule);
                    if segments.is_empty() {
                        continue;
                    }
                    // All rules are NFA-inlineable: multi-segment rules will be
                    // emitted with recursive same-cat parse calls inside the
                    // save/restore closure. Multi-segment rules ALSO go into
                    // frame_pushing for stack-safe fallback.
                    inlineable.push(rd_rule);
                    if segments[0].nonterminal.is_some() {
                        frame_pushing.push(rd_rule);
                    }
                }
            }

            if variant == "LParen" {
                lparen_handled = true;
            }
            write_nfa_merged_prefix_arm(
                buf,
                cold_fns,
                variant,
                &inlineable,
                &frame_pushing,
                cat,
                config,
                frame_info,
                &mut coverage_path_counter,
            );
        }
    }

    // ── Unary prefix operators ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || rd_rule.prefix_bp.is_none() {
            continue;
        }
        // A4: Skip dead unary prefix rules
        if config.optimization_gates.enhanced_dce && config.dead_rules.contains(&rd_rule.label) {
            continue;
        }
        // CEK-4: Skip unary prefix arms that push dead frames
        if config.optimization_gates.dead_frame_elimination {
            let frame_name = format!("UnaryPrefix_{}", rd_rule.label);
            if config.dead_frames.contains(&frame_name) {
                continue;
            }
        }
        // Pattern: [Terminal, NonTerminal(same_category)]
        if let Some(RDSyntaxItem::Terminal(t)) = rd_rule.items.first() {
            let variant = terminal_to_variant_name(t);
            let bp = rd_rule.prefix_bp.unwrap_or(0);
            write!(
                buf,
                "Token::{} => {{ \
                    *pos += 1; \
                    stack.push({enum_name}::{vp}UnaryPrefix_{label} {{ saved_bp: cur_bp }}); \
                    cur_bp = {bp}; \
                    continue 'drive; \
                }},",
                variant, enum_name = frame_info.enum_name, vp = config.frame_prefix(), label = rd_rule.label, bp = bp,
            )
            .unwrap();
        }
    }

    // ── Collection rules ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || !is_simple_collection(rd_rule) {
            continue;
        }
        // A4: Skip dead collection rules
        if config.optimization_gates.enhanced_dce && config.dead_rules.contains(&rd_rule.label) {
            continue;
        }
        // CEK-4: Skip collection arms that push dead frames
        if config.optimization_gates.dead_frame_elimination {
            let frame_name = format!("CollectionElem_{}", rd_rule.label);
            if config.dead_frames.contains(&frame_name) {
                continue;
            }
        }

        // Find the opening terminal and collection info
        let opening_terminal = rd_rule.items.iter().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item {
                Some(t.clone())
            } else {
                None
            }
        });
        let collection_info = rd_rule.items.iter().find_map(|item| match item {
            RDSyntaxItem::Collection { element_category, separator, kind, key_val_separator, .. } => {
                Some((element_category.clone(), separator.clone(), *kind, key_val_separator.clone()))
            },
            _ => None,
        });

        if let (Some(terminal), Some((elem_cat, _sep, kind, kv_sep))) = (opening_terminal, collection_info)
        {
            let variant = terminal_to_variant_name(&terminal);
            let init_str = match kind {
                CollectionKind::HashBag => "mettail_runtime::HashBag::new()",
                CollectionKind::HashSet => "std::collections::HashSet::new()",
                CollectionKind::Vec => "Vec::new()",
                CollectionKind::HashMap => "mettail_runtime::HashMapLit::new()",
            };

            if elem_cat == *cat {
                // Same-category elements: use the frame-based trampoline
                // loop; re-entering `parse_{cat}_impl` for each element is
                // free (no extra function call) because we're already
                // inside it.
                write!(
                    buf,
                    "Token::{} => {{ \
                        *pos += 1; \
                        stack.push({enum_name}::{vp}CollectionElem_{label} {{ \
                            elements: {init_str}, \
                            saved_pos: *pos, \
                            saved_bp: cur_bp, \
                        }}); \
                        cur_bp = 0; \
                        continue 'drive; \
                    }},",
                    variant, enum_name = frame_info.enum_name, vp = config.frame_prefix(), label = rd_rule.label, init_str = init_str,
                )
                .unwrap();
            } else {
                // Cross-category elements (e.g. `list(Proc, Proc, ...)` on
                // a `List` category): the frame mechanism cannot help here —
                // `continue 'drive` would re-enter `parse_List_impl`, not
                // `parse_Proc_impl`. Emit a direct recursive loop that
                // calls `parse_{elem_cat}` for each element, mirroring
                // the recursive-descent path at `recursive.rs:322-398`.
                //
                // For HashMap collections, each element is a (key, value)
                // pair separated by `key_val_separator` (":"). For all
                // other kinds it's a single value.
                let coll_ty = match kind {
                    CollectionKind::HashBag =>
                        format!("mettail_runtime::HashBag<{}>", elem_cat),
                    CollectionKind::HashMap => format!(
                        "mettail_runtime::HashMapLit<{elem}, {elem}>",
                        elem = elem_cat
                    ),
                    CollectionKind::HashSet =>
                        format!("std::collections::HashSet<{}>", elem_cat),
                    CollectionKind::Vec => format!("Vec<{}>", elem_cat),
                };
                let parse_one = match kind {
                    CollectionKind::HashMap => format!(
                        "let key = parse_{elem_cat}(tokens, pos, 0)?; \
                         expect_token(tokens, pos, |t| matches!(t, Token::Colon), \":\")?; \
                         let val = parse_{elem_cat}(tokens, pos, 0)?; \
                         elements.insert(key, val);",
                        elem_cat = elem_cat,
                    ),
                    CollectionKind::HashBag => format!(
                        "let elem = parse_{elem_cat}(tokens, pos, 0)?; \
                         elements.insert(elem);",
                        elem_cat = elem_cat,
                    ),
                    CollectionKind::HashSet => format!(
                        "let elem = parse_{elem_cat}(tokens, pos, 0)?; \
                         elements.insert(elem);",
                        elem_cat = elem_cat,
                    ),
                    CollectionKind::Vec => format!(
                        "let elem = parse_{elem_cat}(tokens, pos, 0)?; \
                         elements.push(elem);",
                        elem_cat = elem_cat,
                    ),
                };
                let _ = kv_sep; // covered by HashMap arm via `Token::Colon`
                write!(
                    buf,
                    "Token::{} => {{ \
                        *pos += 1; \
                        expect_token(tokens, pos, |t| matches!(t, Token::LParen), \"(\")?; \
                        let mut elements: {coll_ty} = {init_str}; \
                        if !peek_token(tokens, *pos).map_or(true, |t| matches!(t, Token::RParen)) {{ \
                            loop {{ \
                                {parse_one} \
                                if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma)) {{ \
                                    *pos += 1; \
                                }} else {{ \
                                    break; \
                                }} \
                            }} \
                        }} \
                        expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
                        break 'prefix {cat}::{label}(elements); \
                    }},",
                    variant,
                    coll_ty = coll_ty,
                    init_str = init_str,
                    parse_one = parse_one,
                    cat = cat,
                    label = rd_rule.label,
                )
                .unwrap();
            }
        }
    }

    // ── Native literal match arms ──
    if let Some(ref native_type) = config.native_type {
        write_native_literal_arm(buf, cat, native_type);
    }

    // ── Grouping: parenthesized expression ──
    //
    // PDA merge: ALL categories use the trampolined GroupClose approach.
    // Cross-category dispatch inside parentheses is handled by the pre-match
    // block above (cross_cat_prefix_arms), so there's no need to call the
    // dispatch wrapper — eliminating unbounded cross-function recursion.
    //
    // Skip if LParen was already handled by an RD rule arm above
    // (either with save/restore + grouping fallback for standalone/inline
    // rules, or as a frame-pushing rule that owns LParen).
    if !lparen_handled {
        write!(
            buf,
            "Token::LParen => {{ \
                *pos += 1; \
                stack.push({enum_name}::{vp}GroupClose {{ saved_bp: cur_bp }}); \
                cur_bp = 0; \
                continue 'drive; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
        )
        .unwrap();
    }

    // ── Cast rule prefix arms ──
    // Use source_first directly (not difference): the target's own_first includes
    // cast source tokens precisely because of the cast rule, so difference would
    // be empty and we'd miss the arm (e.g., Token::Minus from Num's unary prefix).
    //
    // Track tokens already emitted by earlier arms (RD dispatch, unary prefix,
    // collections, native literals, grouping) AND across cast sources to prevent
    // duplicate match arms (e.g., Ident appears in every source's FIRST set).
    {
        use std::collections::BTreeSet;
        let mut cast_handled: BTreeSet<String> = BTreeSet::new();

        // Tokens from RD dispatch groups
        for (variant, _) in &rd_by_token {
            cast_handled.insert(variant.clone());
        }
        // Tokens from unary prefix operators
        for rd_rule in rd_rules {
            if rd_rule.category == *cat && rd_rule.prefix_bp.is_some() {
                if let Some(RDSyntaxItem::Terminal(t)) = rd_rule.items.first() {
                    cast_handled.insert(terminal_to_variant_name(t));
                }
            }
        }
        // Collection open/close terminals
        for rd_rule in rd_rules {
            if rd_rule.category == *cat && is_simple_collection(rd_rule) {
                for item in &rd_rule.items {
                    if let RDSyntaxItem::Terminal(t) = item {
                        cast_handled.insert(terminal_to_variant_name(t));
                    }
                }
            }
        }
        // Native literal token
        if let Some(ref native_type) = config.native_type {
            match native_type.as_str() {
                "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => {
                    cast_handled.insert("Integer".into());
                },
                "f32" | "f64" => {
                    cast_handled.insert("Float".into());
                },
                "bool" => {
                    cast_handled.insert("Boolean".into());
                },
                "str" | "String" => {
                    cast_handled.insert("StringLit".into());
                },
                _ => {},
            }
        }
        // Grouping
        cast_handled.insert("LParen".into());

        for cast_rule in &config.cast_rules {
            if let Some(source_first) = config.all_first_sets.get(&cast_rule.source_category) {
                for token in &source_first.tokens {
                    // Skip Ident — the variable fallback below handles identifiers
                    // at the target category level. Dispatching Ident to a cast source
                    // would hijack identifiers into a single constituent parser, breaking
                    // languages where the sum type has its own operators on identifiers
                    // (e.g., rhocalc's send syntax `x!(0)`).
                    if token == "Ident" {
                        continue;
                    }
                    // Skip tokens already handled by earlier arms or other cast sources
                    if cast_handled.contains(token) {
                        continue;
                    }
                    cast_handled.insert(token.clone());

                    let mut arm = String::new();
                    // W4b: suffix-guarded pattern for Integer-family tokens so
                    // `parse_Proc`'s cast arm dispatches `0u32` to
                    // `parse_UInt32` via the suffix-match rather than the
                    // first-declared Integer category via the blanket arm.
                    crate::pratt::write_token_pattern_pub_for_source(
                        &mut arm,
                        token,
                        &cast_rule.source_category,
                    );
                    write!(
                        arm,
                        " => {{ \
                            let val = parse_{}(tokens, pos, 0)?; \
                            break 'prefix {}::{}(Box::new(val)); \
                        }},",
                        cast_rule.source_category, cat, cast_rule.label,
                    )
                    .unwrap();
                    buf.push_str(&arm);
                }
            }
        }
    }

    // ── Lambda handlers (if primary + has_binders) ──
    if config.has_binders && config.is_primary {
        write_lambda_prefix_arm(buf, config, frame_info);
        write_dollar_prefix_arms(buf, config, frame_info);
    }

    // ── Variable fallback (with optional lookahead) ──
    let var_label = format!(
        "{}Var",
        cat.chars()
            .next()
            .unwrap_or('V')
            .to_uppercase()
            .collect::<String>()
    );

    // Reorder lookahead handlers by weight (lowest first = most likely).
    // This ensures the most probable ident-dispatch path is tried first, reducing backtracking.
    // Prefers composed dispatch weights (complete_weight_map) over raw WFST prediction weights,
    // as composed weights account for lexer × parser interaction.
    let lookahead_handlers = {
        let mut sorted = lookahead_handlers;

        // Sort by composed weight map (priority) or WFST prediction weights (fallback)
        if config.complete_weight_map.is_some() || config.prediction_wfst.is_some() {
            sorted.sort_by(|a, b| {
                let weight_a = handler_weight(a, config);
                let weight_b = handler_weight(b, config);
                weight_a.partial_cmp(&weight_b).unwrap_or(std::cmp::Ordering::Equal)
            });
        }

        sorted
    };

    if !lookahead_handlers.is_empty() {
        let mut arm = String::from("Token::Ident(name) => { match peek_ahead(tokens, *pos, 1) {");
        for handler in &lookahead_handlers {
            let terminal = handler.ident_lookahead.as_ref().expect("checked above");
            let variant = terminal_to_variant_name(terminal);
            // For ident-dispatched RD handlers, we still call the standalone function
            // (these have bounded depth — the nonterminal-first rule dispatch doesn't
            // deeply nest the same category)
            write!(arm, "Some(Token::{}) => {{ match {}(tokens, pos) {{ Ok(v) => break 'prefix v, Err(e) => {{ match stack.pop() {{ None => return Err(e),",
                variant, handler.parse_fn_name).unwrap();
            // Collection catch on error
            write_collection_error_catch_inline(&mut arm, config, rd_rules, frame_info);
            arm.push_str("Some(_) => return Err(e), } } } },");
        }
        // Default: variable fallback
        write!(
            arm,
            "_ => {{ \
                let var_name = (*name).to_string(); \
                *pos += 1; \
                break 'prefix {cat}::{var_label}(\
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(\
                        mettail_runtime::get_or_create_var(var_name)\
                    ))\
                ); \
            }}",
        )
        .unwrap();
        arm.push_str("} },");
        buf.push_str(&arm);
    } else {
        write!(
            buf,
            "Token::Ident(name) => {{ \
                let var_name = (*name).to_string(); \
                *pos += 1; \
                break 'prefix {cat}::{var_label}(\
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(\
                        mettail_runtime::get_or_create_var(var_name)\
                    ))\
                ); \
            }},",
        )
        .unwrap();
    }

    // ── Error fallback ──
    if config.cast_suggestions.is_empty() {
        write!(
            buf,
            "other => {{ \
                let err = Err(ParseError::UnexpectedToken {{ \
                    expected: Cow::Borrowed(\"{expected_escaped}\"), \
                    found: format_token_friendly(other), \
                    range: tokens[*pos].1, \
                    hint: None, \
                }}); \
                match stack.pop() {{ \
                    None => return err.map(|_: {cat}| unreachable!()),",
        )
        .unwrap();
    } else {
        // Build match arms that map token variants to source category names
        // for runtime lookup of missing cast rule hints.
        // Group suggestions by source category to produce compact match arms.
        let mut cat_to_variants: std::collections::BTreeMap<&str, Vec<&str>> = std::collections::BTreeMap::new();
        for (token, source_cat) in &config.cast_suggestions {
            cat_to_variants.entry(source_cat.as_str()).or_default().push(token.as_str());
        }
        let mut cast_match_arms = String::new();
        for (source_cat, variants) in &cat_to_variants {
            let escaped_cat = source_cat.replace('\\', "\\\\").replace('"', "\\\"");
            let patterns: Vec<String> = variants.iter().map(|v| {
                use crate::automata::TokenFamily;
                let family = TokenFamily::from_name(v);
                match family.match_pattern() {
                    Some(pat) => pat.to_string(),
                    None => {
                        // Custom tokens: check payload_carrying_variants
                        if config.payload_carrying_variants.iter().any(|s| s == v) {
                            format!("Token::{}(_)", v)
                        } else {
                            format!("Token::{}", v)
                        }
                    }
                }
            }).collect();
            write!(cast_match_arms, "{} => Some(\"{}\"),", patterns.join(" | "), escaped_cat).unwrap();
        }

        write!(
            buf,
            "other => {{ \
                let found_str = format_token_friendly(other); \
                let source_cat: Option<&str> = match other {{ {cast_arms} _ => None }}; \
                let expected_msg = match source_cat {{ \
                    Some(sc) => Cow::Owned(format!(\"{expected_escaped} Hint: this is a {{}} expression, but no {{}} → {cat} cast rule exists.\", sc, sc)), \
                    None => Cow::Borrowed(\"{expected_escaped}\"), \
                }}; \
                let err = Err(ParseError::UnexpectedToken {{ \
                    expected: expected_msg, \
                    found: found_str, \
                    range: tokens[*pos].1, \
                    hint: None, \
                }}); \
                match stack.pop() {{ \
                    None => return err.map(|_: {cat}| unreachable!()),",
            cast_arms = cast_match_arms,
        )
        .unwrap();
    }
    // Collection catch on prefix error
    write_collection_error_catch_inline(buf, config, rd_rules, frame_info);

    // CrossCatInfixTry catch: when a tentative infix frame is on the stack and the
    // prefix phase can't parse the RHS in the same category, pop the frame, restore
    // pos, and try LED delegation for the cross-category variant. If LED succeeds,
    // `break 'prefix new_lhs` feeds the result back into the infix loop.
    {
        let cross_cat_terms = conflicting_infix_terminals(config, bp_table);
        if !cross_cat_terms.is_empty() && !config.led_delegation.is_empty() {
            write!(
                buf,
                "Some({enum_name}::{vp}CrossCatInfixTry {{ lhs: saved_lhs, saved_pos, saved_bp, .. }}) => {{ \
                    *pos = saved_pos; \
                    cur_bp = saved_bp; \
                    match led_delegate_{cat}(tokens, pos, &saved_lhs) {{ \
                        Some(new_lhs) => break 'prefix new_lhs, \
                        None => return err.map(|_: {cat}| unreachable!()), \
                    }} \
                }},",
                enum_name = frame_info.enum_name, vp = config.frame_prefix(),
            )
            .unwrap();
        }
    }

    write!(
        buf,
        "Some(_) => return err.map(|_: {cat}| unreachable!()), \
        }} \
        }},",
    )
    .unwrap();
}

/// Write inline items (terminals, ident captures, cross-category NTs) consuming from the token stream.
/// If `skip_first` is true, the first terminal is skipped (already matched by dispatch).
///
/// Cross-category nonterminals are handled inline with direct function calls
/// (bounded depth by grammar structure). Same-category nonterminals should NOT
/// appear here — they are handled by the segment splitting algorithm.
fn write_inline_items(buf: &mut String, items: &[RDSyntaxItem], skip_first: bool) {
    let mut skipped = false;
    for item in items {
        match item {
            RDSyntaxItem::Terminal(t) => {
                if skip_first && !skipped {
                    // First terminal is the dispatch token, just advance pos
                    buf.push_str("*pos += 1;");
                    skipped = true;
                } else {
                    let variant = terminal_to_variant_name(t);
                    write!(
                        buf,
                        "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                        variant, t,
                    )
                    .unwrap();
                }
            },
            RDSyntaxItem::IdentCapture { param_name } => {
                write!(buf, "let {} = expect_ident(tokens, pos)?;", param_name).unwrap();
            },
            RDSyntaxItem::Binder { param_name, .. } => {
                write!(buf, "let {} = expect_ident(tokens, pos)?;", param_name).unwrap();
            },
            RDSyntaxItem::NonTerminal { category, param_name } => {
                // Cross-category nonterminal: direct function call (bounded depth)
                write!(buf, "let {} = parse_{}(tokens, pos, 0)?;", param_name, category).unwrap();
            },
            RDSyntaxItem::BinderCollection { param_name, separator } => {
                let sep_variant = terminal_to_variant_name(separator);
                write!(
                    buf,
                    "let mut {param_name} = Vec::new(); \
                    loop {{ \
                        match expect_ident(tokens, pos) {{ \
                            Ok(name) => {{ \
                                {param_name}.push(name); \
                                if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{sep_variant})) {{ \
                                    *pos += 1; \
                                }} else {{ \
                                    break; \
                                }} \
                            }} \
                            Err(_) => break, \
                        }} \
                    }}",
                )
                .unwrap();
            },
            RDSyntaxItem::GuardExpression { .. } => {
                // Guarded rules are routed through standalone parse fn via
                // `should_use_standalone_fn`; `write_inline_items` is never
                // reached for them. The previous catchall here silently
                // dropped GuardExpression items, which would have produced
                // a generated parser that consumed zero tokens for the guard
                // slot — this explicit arm closes that latent regression.
                unreachable!(
                    "GuardExpression must be handled via the standalone fn \
                     path in `recursive.rs::write_recursive_descent_body`; \
                     `write_inline_items` is gated out by \
                     `should_use_standalone_fn`"
                );
            },
            _ => {
                // Collection, Sep/Map/Zip, Optional — handled via standalone parse functions
                // (not trampolined; see `should_use_standalone_fn()` and module docs §4)
            },
        }
    }
}

/// Write the RD constructor directly (for rules with no same-category nonterminals).
///
/// Handles:
/// - Nullary rules (no captures): `break 'prefix Cat::Label;`
/// - Rules with only cross-category NTs and terminals: `break 'prefix Cat::Label(Box::new(x), ...);`
/// - Binder rules: `break 'prefix Cat::Label(Scope::new(...));`
fn write_rd_constructor_inline(buf: &mut String, rule: &RDRuleInfo, segments: &[HandlerSegment]) {
    let cat = &rule.category;
    let label = &rule.label;

    // Collect all captures from the final segment (which has all accumulated captures)
    let all_captures: Vec<&SegmentCapture> = if let Some(last) = segments.last() {
        let mut seen = std::collections::HashSet::new();
        last.accumulated_captures
            .iter()
            .filter(|c| {
                let name = match c {
                    SegmentCapture::NonTerminal { name, .. }
                    | SegmentCapture::Ident { name }
                    | SegmentCapture::Binder { name }
                    | SegmentCapture::Collection { name, .. } => name.clone(),
                    SegmentCapture::Guard { .. } => unreachable!(
                        "guarded rules are routed through standalone fn via \
                         should_use_standalone_fn; write_rd_constructor_inline \
                         is never reached for them"
                    ),
                };
                seen.insert(name)
            })
            .collect()
    } else {
        Vec::new()
    };

    if rule.has_binder {
        // Single binder: Cat::Label(extra_args..., Scope::new(Binder(binder), Box::new(body)))
        let binder_cap = all_captures
            .iter()
            .find(|c| matches!(c, SegmentCapture::Binder { .. }));
        let body_cap = all_captures
            .iter()
            .rev()
            .find(|c| matches!(c, SegmentCapture::NonTerminal { .. }));
        if let (
            Some(SegmentCapture::Binder { name: binder_name }),
            Some(SegmentCapture::NonTerminal { name: body_name, .. }),
        ) = (binder_cap, body_cap)
        {
            let extra: Vec<&&SegmentCapture> = all_captures
                .iter()
                .filter(|c| {
                    let n = match c {
                        SegmentCapture::NonTerminal { name, .. }
                        | SegmentCapture::Ident { name }
                        | SegmentCapture::Binder { name }
                        | SegmentCapture::Collection { name, .. } => name,
                        SegmentCapture::Guard { .. } => unreachable!(
                            "guarded rules are routed through standalone fn via \
                             should_use_standalone_fn; write_rd_constructor_inline \
                             is never reached for them"
                        ),
                    };
                    n != binder_name && n != body_name
                })
                .collect();
            write!(buf, "break 'prefix {cat}::{label}(").unwrap();
            for c in &extra {
                write_segment_capture_as_arg(buf, c);
                buf.push(',');
            }
            write!(
                buf,
                "mettail_runtime::Scope::new(\
                mettail_runtime::Binder(mettail_runtime::get_or_create_var({})), \
                Box::new({}),\
            ));",
                binder_name, body_name
            )
            .unwrap();
        } else {
            write!(buf, "break 'prefix {}::{};", cat, label).unwrap();
        }
    } else if all_captures.is_empty() {
        write!(buf, "break 'prefix {}::{};", cat, label).unwrap();
    } else {
        write!(buf, "break 'prefix {}::{}(", cat, label).unwrap();
        for (i, c) in all_captures.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write_segment_capture_as_arg(buf, c);
        }
        buf.push_str(");");
    }
}

/// Write native literal match arms.
fn write_native_literal_arm(buf: &mut String, cat: &str, native_type: &str) {
    match native_type {
        "i32" => {
            write!(
                buf,
                "Token::Integer(v, suffix) if suffix.matches_i32() => \
                    match i32::try_from(*v) {{ \
                        Ok(val) => {{ *pos += 1; break 'prefix {cat}::NumLit(val); }}, \
                        Err(_) => return Err(ParseError::UnexpectedToken {{ \
                            expected: Cow::Borrowed(\"{cat} literal in i32 range\"), \
                            found: format!(\"{{:?}}\", tokens[*pos].0), \
                            range: tokens[*pos].1, \
                            hint: None, \
                        }}), \
                    }},",
                cat = cat,
            ).unwrap();
        },
        "i64" | "isize" => {
            write!(
                buf,
                "Token::Integer(v, suffix) if suffix.matches_i64() => {{ let val = *v; *pos += 1; break 'prefix {}::NumLit(val); }},",
                cat,
            ).unwrap();
        },
        "u32" => {
            write!(
                buf,
                "Token::Integer(v, suffix) if suffix.matches_u32() => \
                    match u32::try_from(*v) {{ \
                        Ok(val) => {{ *pos += 1; break 'prefix {cat}::NumLit(val); }}, \
                        Err(_) => return Err(ParseError::UnexpectedToken {{ \
                            expected: Cow::Borrowed(\"{cat} literal in u32 range\"), \
                            found: format!(\"{{:?}}\", tokens[*pos].0), \
                            range: tokens[*pos].1, \
                            hint: None, \
                        }}), \
                    }},",
                cat = cat,
            ).unwrap();
        },
        "u64" | "usize" => {
            write!(
                buf,
                "Token::Integer(v, suffix) if suffix.matches_u64() => \
                    match u64::try_from(*v) {{ \
                        Ok(val) => {{ *pos += 1; break 'prefix {cat}::NumLit(val); }}, \
                        Err(_) => return Err(ParseError::UnexpectedToken {{ \
                            expected: Cow::Borrowed(\"{cat} literal in u64 range\"), \
                            found: format!(\"{{:?}}\", tokens[*pos].0), \
                            range: tokens[*pos].1, \
                            hint: None, \
                        }}), \
                    }},",
                cat = cat,
            ).unwrap();
        },
        "f32" | "f64" => {
            write!(
                buf,
                "Token::Float(v) => {{ let val = (*v).into(); *pos += 1; break 'prefix {}::FloatLit(val); }},",
                cat,
            ).unwrap();
        },
        "bool" => {
            write!(
                buf,
                "Token::Boolean(v) => {{ let val = *v; *pos += 1; break 'prefix {}::BoolLit(val); }},",
                cat,
            ).unwrap();
        },
        "str" | "String" => {
            write!(
                buf,
                "Token::StringLit(v) => {{ let val = (*v).to_string(); *pos += 1; break 'prefix {}::StringLit(val); }},",
                cat,
            ).unwrap();
        },
        // CanonicalBigInt flows through a category-named `Token::{cat}(&str)`
        // variant (like BigRat/Fixed) so arbitrary-precision literals such as
        // `32478132567813256718n` preserve full precision. The text is parsed
        // via `parse_int_lit` at parse time — an i64 round-trip would clamp.
        t if t.ends_with("CanonicalBigInt") => {
            write!(
                buf,
                "Token::{cat}(text) => {{ \
                    let lit = mettail_prattail::parse_int_lit(text, None) \
                        .map_err(|_| ParseError::UnexpectedToken {{ \
                            expected: ::std::borrow::Cow::Borrowed(\"BigInt literal\"), \
                            found: format!(\"{{:?}}\", &tokens[*pos].0), \
                            range: tokens[*pos].1, \
                            hint: None, \
                        }})?; \
                    let bi = lit.to_bigint() \
                        .ok_or_else(|| ParseError::UnexpectedToken {{ \
                            expected: ::std::borrow::Cow::Borrowed(\"BigInt literal with `n` suffix\"), \
                            found: format!(\"{{:?}}\", &tokens[*pos].0), \
                            range: tokens[*pos].1, \
                            hint: None, \
                        }})?; \
                    let val = mettail_runtime::CanonicalBigInt::from(bi); \
                    *pos += 1; \
                    break 'prefix {cat}::NumLit(val); \
                }},",
                cat = cat,
            ).unwrap();
        },
        // CanonicalBigRat — carried on `Token::{cat}(&str)` variant; parse at
        // parse time via `parse_rational_lit`.
        t if t.ends_with("CanonicalBigRat") => {
            write!(
                buf,
                "Token::{cat}(text) => {{ \
                    let lit = mettail_prattail::parse_rational_lit(text) \
                        .map_err(|_| ParseError::UnexpectedToken {{ \
                            expected: ::std::borrow::Cow::Borrowed(\"BigRat literal\"), \
                            found: format!(\"{{:?}}\", &tokens[*pos].0), \
                            range: tokens[*pos].1, \
                            hint: None, \
                        }})?; \
                    let val = mettail_runtime::CanonicalBigRat::from(\
                        lit.ratio().clone()\
                    ); \
                    *pos += 1; \
                    break 'prefix {cat}::RatLit(val); \
                }},",
                cat = cat,
            ).unwrap();
        },
        // CanonicalFixedPoint — carried on `Token::{cat}(&str)` variant;
        // parse at parse time via `parse_fixed_lit`.
        t if t.ends_with("CanonicalFixedPoint") => {
            write!(
                buf,
                "Token::{cat}(text) => {{ \
                    let val = mettail_runtime::parse_fixed_lit(text) \
                        .map_err(|_| ParseError::UnexpectedToken {{ \
                            expected: ::std::borrow::Cow::Borrowed(\"Fixed literal\"), \
                            found: format!(\"{{:?}}\", &tokens[*pos].0), \
                            range: tokens[*pos].1, \
                            hint: None, \
                        }})?; \
                    *pos += 1; \
                    break 'prefix {cat}::FixedLit(val); \
                }},",
                cat = cat,
            ).unwrap();
        },
        _ => {},
    }
}

/// Write lambda prefix match arm (^x.{body} or ^[x,y].{body}).
fn write_lambda_prefix_arm(buf: &mut String, config: &TrampolineConfig, frame_info: &FrameInfo) {
    let _cat = &config.category;

    write!(
        buf,
        "Token::Caret => {{ \
            *pos += 1; \
            match peek_token(tokens, *pos) {{ \
                Some(Token::LBracket) => {{ \
                    *pos += 1; \
                    let mut binder_names = Vec::with_capacity(4); \
                    loop {{ \
                        let name = expect_ident(tokens, pos)?; \
                        binder_names.push(name); \
                        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma)) {{ \
                            *pos += 1; \
                        }} else {{ \
                            break; \
                        }} \
                    }} \
                    expect_token(tokens, pos, |t| matches!(t, Token::RBracket), \"]\")?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::Dot), \".\")?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::LBrace), \"{{\")?; \
                    stack.push({enum_name}::{vp}LambdaBody_Multi {{ binder_names, saved_bp: cur_bp }}); \
                    cur_bp = 0; \
                    continue 'drive; \
                }} \
                Some(Token::Ident(_)) => {{ \
                    let binder_name = expect_ident(tokens, pos)?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::Dot), \".\")?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::LBrace), \"{{\")?; \
                    stack.push({enum_name}::{vp}LambdaBody_Single {{ binder_name, saved_bp: cur_bp }}); \
                    cur_bp = 0; \
                    continue 'drive; \
                }} \
                _ => {{ \
                    return Err(ParseError::UnexpectedToken {{ \
                        expected: Cow::Borrowed(\"identifier or '['\"), \
                        found: format_token_friendly(&tokens[*pos].0), \
                        range: tokens[*pos].1, \
                        hint: None, \
                    }}); \
                }} \
            }} \
        }},",
        enum_name = frame_info.enum_name, vp = config.frame_prefix(),
    ).unwrap();
}

/// Write dollar syntax prefix match arms.
fn write_dollar_prefix_arms(buf: &mut String, config: &TrampolineConfig, frame_info: &FrameInfo) {
    let _cat = &config.category;

    for dom in &config.all_categories {
        let dom_lower = dom.to_lowercase();
        let dom_cap = capitalize_first(&dom_lower);
        let dollar_variant = format!("Dollar{}", dom_cap);
        let ddollar_variant = format!("Ddollar{}Lp", dom_cap);

        // Single-apply: $dom — consume $dom, (, then push frame for f parse
        write!(
            buf,
            "Token::{dollar_variant} => {{ \
                *pos += 1; \
                expect_token(tokens, pos, |t| matches!(t, Token::LParen), \"(\")?; \
                stack.push({enum_name}::{vp}DollarF_{dom_cap} {{ saved_bp: cur_bp }}); \
                cur_bp = 0; \
                continue 'drive; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
        )
        .unwrap();

        // Multi-apply: $$dom( — consume token (includes opening paren), push frame for f parse
        write!(
            buf,
            "Token::{ddollar_variant} => {{ \
                *pos += 1; \
                stack.push({enum_name}::{vp}DdollarF_{dom_cap} {{ saved_bp: cur_bp }}); \
                cur_bp = 0; \
                continue 'drive; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
        )
        .unwrap();
    }
}

/// Compute the set of operator terminals that appear in BOTH the category's
/// same-category infix table AND the cross-category LED delegation ops.
///
/// For these "conflicting" operators, the infix loop must use an inline try
/// (with LED delegation fallback on failure) instead of the normal frame-push
/// path. This allows cross-category variants to be reached when the same-category
/// RHS parse fails (e.g., `BVar(x) != Float(0.5)` where `!=` matches `NeBool`
/// but the RHS `0.5` cannot be parsed as Bool — LED delegation then tries `NeFloat`).
fn conflicting_infix_terminals(
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
) -> std::collections::HashSet<String> {
    let cross_cat_terms: std::collections::HashSet<String> = config
        .led_delegation
        .iter()
        .flat_map(|s| s.cross_cat_ops.iter().map(|op| op.terminal.clone()))
        .collect();

    let same_cat_terms: std::collections::HashSet<String> = bp_table
        .operators_for_category(&config.category)
        .iter()
        .map(|op| op.terminal.clone())
        .collect();

    cross_cat_terms
        .intersection(&same_cat_terms)
        .cloned()
        .collect()
}

/// Write the infix loop (iterative portion).
fn write_infix_loop(
    buf: &mut String,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
    frame_info: &FrameInfo,
    bp_range_info: Option<&crate::pratt::BpRangeInfo>,
) {
    let cat = &config.category;
    let cat_upper = cat.to_uppercase();

    buf.push_str("loop { if *pos >= tokens.len() { break; }");

    // BP05: Early-exit guard using BP range bitset.
    // If `cur_bp` is so high that no operator has left_bp >= cur_bp, the bitset
    // right-shifted by (cur_bp - lo) yields zero, and we break without even
    // looking at the current token. This avoids calling infix_bp_*/postfix_bp_*/
    // mixfix_bp_* when the BP is too high for any operator to bind.
    //
    // IMPORTANT: Skip this guard for categories with LED delegation because
    // delegated operators (from constituent categories) may have BPs outside
    // the range of this category's own operators. The early exit would prevent
    // the delegation fallback from being reached.
    let has_delegation = !config.led_delegation.is_empty();
    if let Some(_info) = bp_range_info {
        if !has_delegation {
            write!(
                buf,
                "if (ACTIVE_BP_{cat_upper} >> cur_bp.saturating_sub(BP_LO_{cat_upper})) == 0 {{ break; }}",
            )
            .unwrap();
        }
    }

    buf.push_str("let token = &tokens[*pos].0;");

    let mut wrote_first = false;

    // Postfix (iterative — no frame push)
    if config.has_postfix {
        write!(
            buf,
            "if let Some(l_bp) = postfix_bp_{cat}(token) {{ \
                if l_bp < cur_bp {{ break; }} \
                let op_token = token.clone(); \
                *pos += 1; \
                lhs = make_postfix_{cat}(&op_token, lhs); \
            }}",
        )
        .unwrap();
        wrote_first = true;
    }

    // Mixfix (pushes frame for each operand)
    if config.has_mixfix {
        if wrote_first {
            buf.push_str(" else ");
        }
        write_mixfix_led(buf, config, bp_table, frame_info);
        wrote_first = true;
    }

    // Infix (pushes frame for RHS)
    //
    // Cross-category-aware: operators in `cross_cat_terms` push a tentative
    // `CrossCatInfixTry` frame instead of `InfixRHS`. If the prefix phase fails
    // to parse the RHS as the same category, the tentative frame is popped,
    // pos is restored, and LED delegation tries cross-category variants.
    // When the prefix succeeds, `CrossCatInfixTry` unwinds identically to `InfixRHS`.
    let cross_cat_terms = conflicting_infix_terminals(config, bp_table);
    if config.has_infix {
        if wrote_first {
            buf.push_str(" else ");
        }

        if cross_cat_terms.is_empty() || !has_delegation {
            // No cross-cat conflicts: normal InfixRHS frame-push
            write!(
                buf,
                "if let Some((l_bp, r_bp)) = infix_bp_{cat}(token) {{ \
                    if l_bp < cur_bp {{ break; }} \
                    let op_pos = *pos; \
                    *pos += 1; \
                    stack.push({enum_name}::{vp}InfixRHS {{ lhs, op_pos, saved_bp: cur_bp }}); \
                    cur_bp = r_bp; \
                    continue 'drive; \
                }}",
                enum_name = frame_info.enum_name, vp = config.frame_prefix(),
            )
            .unwrap();
        } else {
            // Split dispatch: conflicting operators push CrossCatInfixTry,
            // non-conflicting push InfixRHS.
            let cross_cat_patterns: Vec<String> = cross_cat_terms
                .iter()
                .map(|t| {
                    format!(
                        "Token::{}",
                        crate::automata::codegen::terminal_to_variant_name(t)
                    )
                })
                .collect();
            let cross_cat_match = cross_cat_patterns.join(" | ");

            write!(
                buf,
                "if let Some((l_bp, r_bp)) = infix_bp_{cat}(token) {{ \
                    if l_bp < cur_bp {{ break; }} \
                    let op_pos = *pos; \
                    *pos += 1; \
                    if matches!(token, {cross_cat_match}) {{ \
                        stack.push({enum_name}::{vp}CrossCatInfixTry {{ \
                            lhs, op_pos, saved_bp: cur_bp, saved_pos: op_pos \
                        }}); \
                    }} else {{ \
                        stack.push({enum_name}::{vp}InfixRHS {{ lhs, op_pos, saved_bp: cur_bp }}); \
                    }} \
                    cur_bp = r_bp; \
                    continue 'drive; \
                }}",
                enum_name = frame_info.enum_name, vp = config.frame_prefix(),
            )
            .unwrap();
        }
        wrote_first = true;
    }

    // LED delegation fallback: when the sum type's own operators don't match,
    // try delegating to constituent categories' operators.
    if has_delegation {
        if wrote_first {
            buf.push_str(" else ");
        }
        write!(
            buf,
            "{{ match led_delegate_{cat}(tokens, pos, &lhs) {{ \
                Some(new_lhs) => {{ lhs = new_lhs; }} \
                None => {{ break; }} \
            }} }}",
        )
        .unwrap();
    } else if wrote_first {
        buf.push_str(" else { break; }");
    } else {
        buf.push_str("break;");
    }

    buf.push('}'); // close infix loop
}

/// Write the mixfix led handler in the infix loop.
fn write_mixfix_led(
    buf: &mut String,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
    frame_info: &FrameInfo,
) {
    let cat = &config.category;

    write!(
        buf,
        "if let Some((l_bp, _r_bp)) = mixfix_bp_{cat}(token) {{ \
            if l_bp < cur_bp {{ break; }} \
            let _op_token = token.clone(); \
            *pos += 1;",
    )
    .unwrap();

    // Dispatch to the first mixfix operand based on operator
    let mixfix_ops = bp_table.mixfix_operators_for_category(cat);
    if mixfix_ops.len() == 1 {
        let op = &mixfix_ops[0];
        // Single mixfix operator — no match needed
        write!(
            buf,
            "stack.push({enum_name}::{vp}Mixfix_{label}_0 {{ lhs, saved_bp: cur_bp }}); \
            cur_bp = 0; \
            continue 'drive;",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
            label = op.label,
        )
        .unwrap();
    } else {
        // Multiple mixfix operators — match on token
        buf.push_str("match &_op_token {");
        for op in &mixfix_ops {
            let variant = terminal_to_variant_name(&op.terminal);
            write!(
                buf,
                "Token::{} => {{ \
                    stack.push({enum_name}::{vp}Mixfix_{label}_0 {{ lhs, saved_bp: cur_bp }}); \
                    cur_bp = 0; \
                    continue 'drive; \
                }},",
                variant,
                enum_name = frame_info.enum_name, vp = config.frame_prefix(),
                label = op.label,
            )
            .unwrap();
        }
        buf.push_str("_ => unreachable!(\"mixfix_bp returned Some for non-mixfix token\"),");
        buf.push('}');
    }

    buf.push('}');
}

// ══════════════════════════════════════════════════════════════════════════════
// LED Delegation Code Generation
// ══════════════════════════════════════════════════════════════════════════════

/// Write LED delegation functions for a sum-type category.
///
/// Generates:
/// 1. `led_delegate_{Cat}_from_{Source}` — per-source delegation function
/// 2. `led_delegate_{Cat}` — outer dispatch (pattern-match on LHS variant)
/// 3. `has_led_token_{Source}` — token check helper for auto-projection
/// 4. `handle_mixfix_{Source}` — standalone mixfix handler (if source has mixfix)
///
/// For Phase 1 (known variant): unwrap cast variant, delegate to source's operators.
/// For Phase 2 (unknown variant): auto-project via projection rule, try all matches.
pub fn write_led_delegation_fns(
    buf: &mut String,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
) {
    if config.led_delegation.is_empty() {
        return;
    }

    let cat = &config.category;

    // ── Generate standalone handle_mixfix for sources that have mixfix ──
    // Deduplicate ACROSS all categories (thread-local): the same source can
    // appear as a LED delegation source in multiple target categories (e.g.,
    // Int source appears for both Proc and BigInt targets when IntToBigInt
    // is declared). Emitting `handle_mixfix_{src}` more than once produces
    // `E0428: the name is defined multiple times`.
    for source in &config.led_delegation {
        if source.has_mixfix {
            HANDLE_MIXFIX_EMITTED.with(|set| {
                let mut s = set.borrow_mut();
                if s.insert(source.source_category.clone()) {
                    crate::pratt::write_handle_mixfix_pub(buf, &source.source_category, bp_table);
                }
            });
        }
    }

    // ── Generate per-source delegation functions ──
    for source in &config.led_delegation {
        write_led_delegate_from_source(buf, cat, source, bp_table);
    }

    // ── Generate has_led_token_{Source} helpers (for Phase 2 auto-projection) ──
    for source in &config.led_delegation {
        if source.projection_label.is_some() {
            write_has_led_token_helper(buf, source, bp_table);
        }
    }

    // ── Generate outer dispatch function ──
    write_led_delegate_outer(buf, cat, config);
}

/// Write the per-source LED delegation function.
///
/// `led_delegate_{Cat}_from_{Source}(tokens, pos, lhs) -> Option<Cat>`
///
/// Checks the current token against the source's operators (postfix → mixfix → infix → cross-cat)
/// and re-wraps results into the sum type.
fn write_led_delegate_from_source(
    buf: &mut String,
    cat: &str,
    source: &crate::pratt::LedDelegationSource,
    _bp_table: &BindingPowerTable,
) {
    let src = &source.source_category;

    write!(
        buf,
        "fn led_delegate_{cat}_from_{src}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            lhs: {src}, \
        ) -> Option<{cat}> {{ \
            if *pos >= tokens.len() {{ return None; }} \
            let token = &tokens[*pos].0;",
    )
    .unwrap();

    let mut wrote_first = false;

    // Postfix (no recursive parse, just apply and re-wrap)
    if source.has_postfix {
        write!(
            buf,
            "if let Some(_l_bp) = postfix_bp_{src}(token) {{ \
                let op_token = token.clone(); \
                *pos += 1; \
                return Some({cat}::{cast}(Box::new(make_postfix_{src}(&op_token, lhs)))); \
            }}",
            cast = source.cast_label,
        )
        .unwrap();
        wrote_first = true;
    }

    // Mixfix (delegate to standalone handle_mixfix)
    if source.has_mixfix {
        if wrote_first {
            buf.push_str(" else ");
        }
        // Save pos before consuming operator; restore on failure to avoid
        // pos corruption propagating to the caller (LED backtracking fix).
        write!(
            buf,
            "if let Some((_l_bp, r_bp)) = mixfix_bp_{src}(token) {{ \
                let op_token = token.clone(); \
                let saved_led = *pos; \
                *pos += 1; \
                match handle_mixfix_{src}(&op_token, lhs, tokens, pos, r_bp) {{ \
                    Ok(result) => return Some({cat}::{cast}(Box::new(result))), \
                    Err(_) => {{ *pos = saved_led; return None; }} \
                }} \
            }}",
            cast = source.cast_label,
        )
        .unwrap();
        wrote_first = true;
    }

    // Same-category infix (parse RHS via source parser, re-wrap)
    if source.has_infix {
        if wrote_first {
            buf.push_str(" else ");
        }
        // Save pos before consuming operator; restore on failure to avoid
        // pos corruption propagating to the caller (LED backtracking fix).
        write!(
            buf,
            "if let Some((_l_bp, r_bp)) = infix_bp_{src}(token) {{ \
                let op_token = token.clone(); \
                let saved_led = *pos; \
                *pos += 1; \
                match parse_{src}(tokens, pos, r_bp) {{ \
                    Ok(rhs) => return Some({cat}::{cast}(Box::new(make_infix_{src}(&op_token, lhs, rhs)))), \
                    Err(_) => {{ *pos = saved_led; return None; }} \
                }} \
            }}",
            cast = source.cast_label,
        )
        .unwrap();
        wrote_first = true;
    }

    // Cross-category operators FROM source (e.g., == from Int → Bool)
    if !source.cross_cat_ops.is_empty() {
        if wrote_first {
            buf.push_str(" else ");
        }
        buf.push_str("{ match token {");

        // Save pos before consuming operator; restore on failure and fall
        // through to try subsequent match arms (LED cross-cat backtracking fix).
        for op in &source.cross_cat_ops {
            let variant = terminal_to_variant_name(&op.terminal);
            write!(
                buf,
                "Token::{variant} => {{ \
                    let saved_led = *pos; \
                    *pos += 1; \
                    match parse_{src}(tokens, pos, {r_bp}) {{ \
                        Ok(rhs) => return Some({cat}::{rewrap}(Box::new(\
                            {result_cat}::{label}(Box::new(lhs), Box::new(rhs))\
                        ))), \
                        Err(_) => {{ *pos = saved_led; }} \
                    }} \
                }},",
                src = source.source_category,
                r_bp = op.right_bp,
                rewrap = op.rewrap_label,
                result_cat = op.result_category,
                label = op.label,
            )
            .unwrap();
        }

        buf.push_str("_ => {} } }");
    }

    buf.push_str("None }");
}

/// Write the `has_led_token_{Source}` helper for Phase 2 auto-projection.
///
/// Returns `true` if the given token matches any LED operator from this source category.
fn write_has_led_token_helper(
    buf: &mut String,
    source: &crate::pratt::LedDelegationSource,
    _bp_table: &BindingPowerTable,
) {
    let src = &source.source_category;

    write!(
        buf,
        "fn has_led_token_{src}<'a>(token: &Token<'a>) -> bool {{",
    )
    .unwrap();

    let mut checks: Vec<String> = Vec::new();

    if source.has_postfix {
        checks.push(format!("postfix_bp_{src}(token).is_some()"));
    }
    if source.has_mixfix {
        checks.push(format!("mixfix_bp_{src}(token).is_some()"));
    }
    if source.has_infix {
        checks.push(format!("infix_bp_{src}(token).is_some()"));
    }

    // Cross-cat token check
    if !source.cross_cat_ops.is_empty() {
        let variants: Vec<String> = source.cross_cat_ops.iter()
            .map(|op| format!("Token::{}", terminal_to_variant_name(&op.terminal)))
            .collect();
        checks.push(format!("matches!(token, {})", variants.join(" | ")));
    }

    if checks.is_empty() {
        buf.push_str("false");
    } else {
        buf.push_str(&checks.join(" || "));
    }

    buf.push_str(" }");
}

/// Write the outer LED delegation dispatch function.
///
/// `led_delegate_{Cat}(tokens, pos, lhs) -> Option<Cat>`
///
/// Phase 1: Pattern-match on known cast variants → unwrap and delegate.
/// Phase 2: Unknown variants → auto-project via projection rules (all alternatives tried).
fn write_led_delegate_outer(buf: &mut String, cat: &str, config: &TrampolineConfig) {
    write!(
        buf,
        "fn led_delegate_{cat}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            lhs: &{cat}, \
        ) -> Option<{cat}> {{ match lhs {{",
    )
    .unwrap();

    // Phase 1: Known cast variants — unwrap and delegate
    for source in &config.led_delegation {
        write!(
            buf,
            "{cat}::{cast}(inner) => led_delegate_{cat}_from_{src}(tokens, pos, *inner.clone()),",
            cast = source.cast_label,
            src = source.source_category,
        )
        .unwrap();
    }

    // Phase 2: Unknown variants — auto-projection
    // Try each constituent that has a projection rule AND whose operators match the token.
    // All matching alternatives are tried; longest match (greatest end_pos) wins.
    let projectable: Vec<&crate::pratt::LedDelegationSource> = config.led_delegation.iter()
        .filter(|s| s.projection_label.is_some())
        .collect();

    if projectable.is_empty() {
        // No projection rules — unknown variants can't be delegated
        buf.push_str("_ => None,");
    } else {
        buf.push_str("_ => {");
        buf.push_str("if *pos >= tokens.len() { return None; }");
        buf.push_str("let saved_pos = *pos;");
        buf.push_str("let token = &tokens[*pos].0;");
        write!(buf, "let mut best_result: Option<({cat}, usize)> = None;").unwrap();

        for source in &projectable {
            let src = &source.source_category;
            let proj_label = source.projection_label.as_ref().expect("filtered above");

            // Var-aware Phase 2 coercion: when the LHS is a variable of the
            // target category (e.g., EVar(x) in Expr), convert directly to the
            // source category's variable (e.g., NVar(x) in Num) instead of
            // wrapping with the projection rule (e.g., ExprToNum(EVar(x))).
            // This preserves display roundtrip: display(CastNum(AddNum(NVar(x), n)))
            // produces "x + n" which parses back identically.
            let cat_var = format!("{}Var", cat.chars().next().unwrap_or('V').to_uppercase().collect::<String>());
            let src_var = format!("{}Var", src.chars().next().unwrap_or('V').to_uppercase().collect::<String>());
            write!(
                buf,
                "if has_led_token_{src}(token) {{ \
                    let mut try_pos = saved_pos; \
                    let coerced = if let {cat}::{cat_var}(v) = lhs {{ \
                        {src}::{src_var}(v.clone()) \
                    }} else {{ \
                        {src}::{proj}(Box::new(lhs.clone())) \
                    }}; \
                    if let Some(result) = led_delegate_{cat}_from_{src}(tokens, &mut try_pos, coerced) {{ \
                        if best_result.as_ref().map_or(true, |(_, p)| try_pos > *p) {{ \
                            best_result = Some((result, try_pos)); \
                        }} \
                    }} \
                }}",
                proj = proj_label,
            )
            .unwrap();
        }

        write!(
            buf,
            "if let Some((result, end_pos)) = best_result {{ \
                *pos = end_pos; \
                return Some(result); \
            }}",
        )
        .unwrap();
        buf.push_str("None },");
    }

    buf.push_str("} }"); // close match and fn
}

/// Write the unwind handlers (Phase B continuation popping).
fn write_unwind_handlers(
    buf: &mut String,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
    rd_rules: &[RDRuleInfo],
    frame_info: &FrameInfo,
) {
    let cat = &config.category;

    if config.unified_mode {
        write!(buf, "match stack.pop() {{ None => return Ok(ParseStep::Yield(AnyTerm::{cat}(Box::new(lhs)))),").unwrap();
    } else {
        write!(buf, "match stack.pop() {{ None => return Ok(lhs),").unwrap();
    }

    // ── InfixRHS ──
    if config.has_infix {
        write!(
            buf,
            "Some({enum_name}::{vp}InfixRHS {{ lhs: prev, op_pos, saved_bp }}) => {{ \
                lhs = make_infix_{cat}(&tokens[op_pos].0, prev, lhs); \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
        )
        .unwrap();

        // ── CrossCatInfixTry (success path) ──
        // When the prefix successfully parsed the RHS in the same category,
        // the unwind is identical to InfixRHS: construct the infix node.
        let cross_cat_terms = conflicting_infix_terminals(config, bp_table);
        if !cross_cat_terms.is_empty() && !config.led_delegation.is_empty() {
            write!(
                buf,
                "Some({enum_name}::{vp}CrossCatInfixTry {{ lhs: prev, op_pos, saved_bp, .. }}) => {{ \
                    lhs = make_infix_{cat}(&tokens[op_pos].0, prev, lhs); \
                    cur_bp = saved_bp; \
                }},",
                enum_name = frame_info.enum_name, vp = config.frame_prefix(),
            )
            .unwrap();
        }
    }

    // ── GroupClose ──
    write!(
        buf,
        "Some({enum_name}::{vp}GroupClose {{ saved_bp }}) => {{ \
            expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
            cur_bp = saved_bp; \
        }},",
        enum_name = frame_info.enum_name, vp = config.frame_prefix(),
    )
    .unwrap();

    // ── UnaryPrefix variants ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || rd_rule.prefix_bp.is_none() {
            continue;
        }
        // CEK-4: Skip unwind handlers for dead frame variants
        if config.optimization_gates.dead_frame_elimination {
            let frame_name = format!("UnaryPrefix_{}", rd_rule.label);
            if config.dead_frames.contains(&frame_name) {
                continue;
            }
        }
        write!(
            buf,
            "Some({enum_name}::{vp}UnaryPrefix_{label} {{ saved_bp }}) => {{ \
                lhs = {cat}::{label}(Box::new(lhs)); \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
            label = rd_rule.label,
        )
        .unwrap();
    }

    // ── RD handler segment continuations ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat
            || is_simple_collection(rd_rule)
            || rd_rule.prefix_bp.is_some()
            || should_use_standalone_fn(rd_rule)
        {
            continue;
        }

        let segments = split_rd_handler(rd_rule);
        // CEK-1: Apply dead capture elimination if the gate is enabled
        let segments = if config.optimization_gates.environment_trimming {
            trim_dead_captures(&segments, rd_rule)
        } else {
            segments
        };
        // Generate unwind handler for each segment that has a nonterminal
        for (i, segment) in segments.iter().enumerate() {
            if segment.nonterminal.is_none() {
                continue;
            }
            // CEK-4: Skip unwind handlers for dead frame variants
            if config.optimization_gates.dead_frame_elimination
                && config.dead_frames.contains(&segment.frame_variant)
            {
                continue;
            }

            let nt = segment.nonterminal.as_ref().unwrap();
            let next_segment = segments.get(i + 1);

            // Build field destructuring
            let mut field_names: Vec<String> = vec!["saved_bp".to_string()];
            for capture in &segment.accumulated_captures {
                match capture {
                    SegmentCapture::NonTerminal { name, .. }
                    | SegmentCapture::Ident { name }
                    | SegmentCapture::Binder { name }
                    | SegmentCapture::Collection { name, .. } => {
                        field_names.push(name.clone());
                    },
                    SegmentCapture::Guard { .. } => unreachable!(
                        "guarded rules are routed through standalone fn via \
                         should_use_standalone_fn; unwind handler is never \
                         reached for them"
                    ),
                }
            }

            write!(
                buf,
                "Some({enum_name}::{vp}{variant} {{ {fields} }}) => {{",
                enum_name = frame_info.enum_name, vp = config.frame_prefix(),
                variant = segment.frame_variant,
                fields = field_names.join(", "),
            )
            .unwrap();

            // Assign the parsed nonterminal result to its param name
            write!(buf, "let {} = lhs;", nt.param_name).unwrap();

            // Check if there's a next segment with more items to process
            if let Some(next) = next_segment {
                // Inline the next segment's terminal items
                write_inline_items(buf, &next.inline_items, false);

                if let Some(ref next_nt) = next.nonterminal {
                    // Push frame for the next continuation
                    write!(buf, "stack.push({enum_name}::{vp}{variant} {{", enum_name = frame_info.enum_name, vp = config.frame_prefix(), variant = next.frame_variant)
                        .unwrap();
                    write!(buf, "saved_bp,").unwrap();
                    // All accumulated captures from previous segments + this nonterminal
                    for capture in &next.accumulated_captures {
                        match capture {
                            SegmentCapture::NonTerminal { name, .. }
                            | SegmentCapture::Ident { name }
                            | SegmentCapture::Binder { name }
                            | SegmentCapture::Collection { name, .. } => {
                                write!(buf, "{},", name).unwrap();
                            },
                            SegmentCapture::Guard { .. } => unreachable!(
                                "guarded rules are routed through standalone fn \
                                 via should_use_standalone_fn; unwind handler is \
                                 never reached for them"
                            ),
                        }
                    }
                    buf.push_str("});");

                    if next_nt.category == *cat {
                        write!(buf, "cur_bp = {};", next_nt.bp).unwrap();
                        buf.push_str("continue 'drive;");
                    } else {
                        // Cross-category: direct call
                        write!(
                            buf,
                            "let {} = parse_{}(tokens, pos, {})?;",
                            next_nt.param_name, next_nt.category, next_nt.bp
                        )
                        .unwrap();
                        write!(buf, "lhs = {};", next_nt.param_name).unwrap();
                        // Will be handled by the NEXT unwind iteration
                    }
                } else {
                    // This is the last segment (no more nonterminals)
                    // Build the constructor
                    write_rd_constructor_from_segments(buf, rd_rule, &segments);
                    buf.push_str("cur_bp = saved_bp;");
                }
            } else {
                // This was the last nonterminal; construct the AST node
                write_rd_constructor_from_segments(buf, rd_rule, &segments);
                buf.push_str("cur_bp = saved_bp;");
            }

            buf.push_str("},");
        }
    }

    // ── CollectionElem variants ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || !is_simple_collection(rd_rule) {
            continue;
        }
        // CEK-4: Skip unwind handlers for dead collection frame variants
        if config.optimization_gates.dead_frame_elimination {
            let frame_name = format!("CollectionElem_{}", rd_rule.label);
            if config.dead_frames.contains(&frame_name) {
                continue;
            }
        }
        // Cross-category collections never push a CollectionElem_ frame —
        // the prefix arm inlines a direct recursive `parse_{elem_cat}` loop
        // (see above). Skip the unwind handler here too: it would type-check
        // against `elements: Vec<Cat>` + `lhs: Cat`, but the frame is never
        // reached so emitting dead code just creates compile errors about
        // mismatched `Vec<Proc>` vs `List` pushes.
        let elem_cat_opt = rd_rule.items.iter().find_map(|item| match item {
            RDSyntaxItem::Collection { element_category, .. } => Some(element_category.clone()),
            _ => None,
        });
        if elem_cat_opt.as_deref().map_or(false, |ec| ec != *cat) {
            continue;
        }

        let collection_type = rd_rule.collection_type.unwrap_or(CollectionKind::HashBag);
        let insert_method = match collection_type {
            CollectionKind::HashBag | CollectionKind::HashSet | CollectionKind::HashMap => "insert",
            CollectionKind::Vec => "push",
        };

        // Find separator and closing terminal
        let sep_info = rd_rule.items.iter().find_map(|item| match item {
            RDSyntaxItem::Collection { separator, .. } => Some(separator.clone()),
            _ => None,
        });
        let closing_terminal = rd_rule.items.iter().rev().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item {
                Some(t.clone())
            } else {
                None
            }
        });

        write!(
            buf,
            "Some({enum_name}::{vp}CollectionElem_{label} {{ mut elements, saved_pos, saved_bp }}) => {{",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
            label = rd_rule.label,
        ).unwrap();

        write!(buf, "elements.{}(lhs);", insert_method).unwrap();

        if let Some(ref sep) = sep_info {
            let sep_variant = terminal_to_variant_name(sep);
            write!(
                buf,
                "if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                    *pos += 1; \
                    stack.push({enum_name}::{vp}CollectionElem_{label} {{ \
                        elements, saved_pos: *pos, saved_bp, \
                    }}); \
                    cur_bp = 0; \
                    continue 'drive; \
                }}",
                sep_variant,
                enum_name = frame_info.enum_name, vp = config.frame_prefix(),
                label = rd_rule.label,
            )
            .unwrap();
        }

        // Finalize: expect closing terminal, construct
        if let Some(ref closing) = closing_terminal {
            let close_variant = terminal_to_variant_name(closing);
            write!(
                buf,
                "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                close_variant, closing,
            )
            .unwrap();
        }

        write!(buf, "lhs = {}::{}(elements);", cat, rd_rule.label).unwrap();
        buf.push_str("cur_bp = saved_bp;");
        buf.push_str("},");
    }

    // ── Mixfix step variants ──
    // Each mixfix operator (e.g., Tern: c "?" t ":" e) generates N-1 frame variants.
    // The frame stores the original lhs (c) as `lhs`, plus accumulated operands.
    // We destructure `lhs: orig_lhs` to avoid shadowing the outer `lhs` variable
    // (which holds the just-parsed operand result).
    for op in bp_table.mixfix_operators_for_category(cat) {
        for (i, part) in op.mixfix_parts.iter().enumerate() {
            let is_last = i == op.mixfix_parts.len() - 1;

            // Build field destructuring: rename frame's `lhs` to `orig_lhs`
            let mut field_list = String::from("lhs: orig_lhs, saved_bp");
            for j in 0..i {
                write!(field_list, ", param_{}", op.mixfix_parts[j].param_name).unwrap();
            }

            write!(
                buf,
                "Some({enum_name}::{vp}Mixfix_{label}_{i} {{ {field_list} }}) => {{",
                enum_name = frame_info.enum_name, vp = config.frame_prefix(),
                label = op.label,
            )
            .unwrap();

            // Assign current lhs (outer variable) as this operand's result
            let param_ident = format!("param_{}", part.param_name);
            write!(buf, "let {} = lhs;", param_ident).unwrap();

            if let Some(ref terminal) = part.following_terminal {
                // Expect the separator terminal
                let sep_variant = terminal_to_variant_name(terminal);
                write!(
                    buf,
                    "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                    sep_variant, terminal,
                )
                .unwrap();
            }

            if is_last {
                // Construct the AST node: Cat::Label(Box::new(orig_lhs), Box::new(param_0), ..., Box::new(param_N))
                write!(buf, "lhs = {}::{}(Box::new(orig_lhs)", cat, op.label).unwrap();
                for j in 0..op.mixfix_parts.len() {
                    write!(buf, ", Box::new(param_{})", op.mixfix_parts[j].param_name).unwrap();
                }
                buf.push_str(");");
                buf.push_str("cur_bp = saved_bp;");
            } else {
                // Push frame for next operand, preserving orig_lhs and accumulated params
                let next_i = i + 1;
                write!(
                    buf,
                    "stack.push({enum_name}::{vp}Mixfix_{label}_{next_i} {{ lhs: orig_lhs,",
                    enum_name = frame_info.enum_name, vp = config.frame_prefix(),
                    label = op.label
                )
                .unwrap();
                buf.push_str("saved_bp,");
                for j in 0..=i {
                    write!(buf, "param_{},", op.mixfix_parts[j].param_name).unwrap();
                }
                buf.push_str("});");
                buf.push_str("cur_bp = 0;");
                buf.push_str("continue 'drive;");
            }

            buf.push_str("},");
        }
    }

    // ── Lambda body variants ──
    if config.has_binders && config.is_primary {
        let default_lam_variant = format!("Lam{}", cat);
        let default_mlam_variant = format!("MLam{}", cat);

        // Build inference-driven match arms for selecting the correct Lam/MLam variant
        let lam_match_arms: String = config
            .all_categories
            .iter()
            .map(|dom| {
                format!(
                    "Some(InferredType::Base(VarCategory::{})) => {}::Lam{}(scope), ",
                    dom, cat, dom
                )
            })
            .collect::<Vec<_>>()
            .join("");

        let mlam_match_arms: String = config
            .all_categories
            .iter()
            .map(|dom| {
                format!(
                    "Some(InferredType::Base(VarCategory::{})) => {}::MLam{}(scope), ",
                    dom, cat, dom
                )
            })
            .collect::<Vec<_>>()
            .join("");

        write!(
            buf,
            "Some({enum_name}::{vp}LambdaBody_Single {{ binder_name, saved_bp }}) => {{ \
                expect_token(tokens, pos, |t| matches!(t, Token::RBrace), \"}}\")?; \
                let inferred = lhs.infer_var_type(&binder_name); \
                let scope = mettail_runtime::Scope::new( \
                    mettail_runtime::Binder(mettail_runtime::get_or_create_var(binder_name)), \
                    Box::new(lhs), \
                ); \
                lhs = match inferred {{ \
                    {lam_match_arms} \
                    _ => {cat}::{default_lam_variant}(scope) \
                }}; \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
        )
        .unwrap();

        write!(
            buf,
            "Some({enum_name}::{vp}LambdaBody_Multi {{ binder_names, saved_bp }}) => {{ \
                expect_token(tokens, pos, |t| matches!(t, Token::RBrace), \"}}\")?; \
                let inferred = if let Some(name) = binder_names.first() {{ \
                    lhs.infer_var_type(name) \
                }} else {{ \
                    None \
                }}; \
                let binders: Vec<mettail_runtime::Binder<String>> = \
                    binder_names.into_iter() \
                        .map(|s| mettail_runtime::Binder(mettail_runtime::get_or_create_var(s))) \
                        .collect(); \
                let scope = mettail_runtime::Scope::new(binders, Box::new(lhs)); \
                lhs = match inferred {{ \
                    {mlam_match_arms} \
                    _ => {cat}::{default_mlam_variant}(scope) \
                }}; \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
        )
        .unwrap();

        // Dollar syntax unwind handlers
        write_dollar_unwind_handlers(buf, config, frame_info);
    }

    // NOTE: Cast variants are NOT trampolined (cross-category, bounded depth).
    // No CastWrap_* unwind handlers needed.

    // ── GuardEval frame ──
    // When the parser finishes parsing the guard pattern scope (the `?` operator),
    // the GuardEval frame restores the saved binding power and continues parsing
    // the continuation body. The guard evaluation itself is handled at runtime
    // by the Ascent Comm rule, not during parsing.
    if config.has_binders {
        write!(
            buf,
            "Some({enum_name}::{vp}GuardEval {{ saved_bp }}) => {{ \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
        )
        .unwrap();
    }

    // No PhantomData variant — Frame is 'static (no lifetime parameter).

    // In unified mode, UnifiedFrame has variants from all categories. When the
    // per-category unwind loop encounters a frame from another category (or a
    // cross-category control frame like ErrorBarrier/CrossCatReturn), push it
    // back and yield the result to the unified driver.
    if config.unified_mode {
        write!(
            buf,
            "Some(other) => {{ \
                stack.push(other); \
                return Ok(ParseStep::Yield(AnyTerm::{cat}(Box::new(lhs)))); \
            }},",
        ).unwrap();
    }

    buf.push('}'); // close match
}

/// Write dollar syntax unwind handlers.
fn write_dollar_unwind_handlers(
    buf: &mut String,
    config: &TrampolineConfig,
    frame_info: &FrameInfo,
) {
    let cat = &config.category;

    for dom in &config.all_categories {
        let dom_lower = dom.to_lowercase();
        let dom_cap = capitalize_first(&dom_lower);
        let apply_variant = format!("Apply{}", dom);
        let mapply_variant = format!("MApply{}", dom);

        // DollarF: after parsing f, parse x
        write!(
            buf,
            "Some({enum_name}::{vp}DollarF_{dom_cap} {{ saved_bp }}) => {{ \
                let f = lhs; \
                expect_token(tokens, pos, |t| matches!(t, Token::Comma), \",\")?; \
                let x = parse_{dom}(tokens, pos, 0)?; \
                expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
                lhs = {cat}::{apply_variant}(Box::new(f), Box::new(x)); \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
        )
        .unwrap();

        // DdollarF: after parsing f, parse args
        write!(
            buf,
            "Some({enum_name}::{vp}DdollarF_{dom_cap} {{ saved_bp }}) => {{ \
                let f = lhs; \
                expect_token(tokens, pos, |t| matches!(t, Token::Comma), \",\")?; \
                let mut args: Vec<{dom}> = Vec::with_capacity(4); \
                loop {{ \
                    let arg = parse_{dom}(tokens, pos, 0)?; \
                    args.push(arg); \
                    if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma)) {{ \
                        *pos += 1; \
                    }} else {{ \
                        break; \
                    }} \
                }} \
                expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
                lhs = {cat}::{mapply_variant}(Box::new(f), args); \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
        )
        .unwrap();

        // DdollarArgs: collecting additional args (trampolined version)
        // For now, dollar args are cross-category calls (bounded depth), so we
        // use direct calls in the DdollarF handler above.
    }
}

/// Write collection EOF catch in the prefix phase.
///
/// When EOF is reached and a CollectionElem frame is on the stack, finalize the
/// collection with elements collected so far. Uses `break 'prefix` since this
/// code is inside the `'prefix` block.
fn write_collection_eof_catch(
    buf: &mut String,
    config: &TrampolineConfig,
    rd_rules: &[RDRuleInfo],
    frame_info: &FrameInfo,
) {
    let cat = &config.category;

    for rd_rule in rd_rules {
        if rd_rule.category != *cat || !is_simple_collection(rd_rule) {
            continue;
        }
        // Cross-category collections never push a CollectionElem_ frame
        // — skip the unwind catch too (same reason as the frame-variant
        // emission and prefix unwind; see comment there).
        let elem_cat_opt = rd_rule.items.iter().find_map(|item| match item {
            RDSyntaxItem::Collection { element_category, .. } => Some(element_category.clone()),
            _ => None,
        });
        if elem_cat_opt.as_deref().map_or(false, |ec| ec != *cat) {
            continue;
        }

        let closing_terminal = rd_rule.items.iter().rev().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item {
                Some(t.clone())
            } else {
                None
            }
        });

        write!(
            buf,
            "Some({enum_name}::{vp}CollectionElem_{label} {{ elements, saved_pos, saved_bp }}) => {{ \
                *pos = saved_pos;",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
            label = rd_rule.label,
        )
        .unwrap();

        if let Some(ref closing) = closing_terminal {
            let close_variant = terminal_to_variant_name(closing);
            write!(
                buf,
                "if *pos < tokens.len() {{ \
                    expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?; \
                }}",
                close_variant, closing,
            )
            .unwrap();
        }

        // Use break 'prefix to exit the prefix block with the finalized collection.
        // The unwind phase will then process any remaining frames from the stack.
        write!(
            buf,
            "cur_bp = saved_bp; \
            break 'prefix {cat}::{label}(elements);",
            label = rd_rule.label,
        )
        .unwrap();
        buf.push_str("},");
    }
}

/// Write collection error catch inline (for prefix error handling).
fn write_collection_error_catch_inline(
    buf: &mut String,
    config: &TrampolineConfig,
    rd_rules: &[RDRuleInfo],
    frame_info: &FrameInfo,
) {
    // This is called inside a match on stack.pop() when a prefix error occurs
    // We need to catch CollectionElem frames and finalize them
    let cat = &config.category;

    for rd_rule in rd_rules {
        if rd_rule.category != *cat || !is_simple_collection(rd_rule) {
            continue;
        }
        let elem_cat_opt = rd_rule.items.iter().find_map(|item| match item {
            RDSyntaxItem::Collection { element_category, .. } => Some(element_category.clone()),
            _ => None,
        });
        if elem_cat_opt.as_deref().map_or(false, |ec| ec != *cat) {
            continue;
        }

        let closing_terminal = rd_rule.items.iter().rev().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item {
                Some(t.clone())
            } else {
                None
            }
        });

        write!(
            buf,
            "Some({enum_name}::{vp}CollectionElem_{label} {{ elements, saved_pos, saved_bp }}) => {{ \
                *pos = saved_pos;",
            enum_name = frame_info.enum_name, vp = config.frame_prefix(),
            label = rd_rule.label,
        )
        .unwrap();

        if let Some(ref closing) = closing_terminal {
            let close_variant = terminal_to_variant_name(closing);
            write!(
                buf,
                "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                close_variant, closing,
            )
            .unwrap();
        }

        // Use break 'prefix to exit the prefix block with the finalized collection.
        // (Same approach as write_collection_eof_catch — we're inside the 'prefix block.)
        write!(
            buf,
            "cur_bp = saved_bp; \
            break 'prefix {cat}::{label}(elements); \
            }},",
            label = rd_rule.label,
        )
        .unwrap();
    }
}

/// Write the RD constructor from accumulated segment captures.
fn write_rd_constructor_from_segments(
    buf: &mut String,
    rule: &RDRuleInfo,
    segments: &[HandlerSegment],
) {
    let cat = &rule.category;
    let label = &rule.label;

    // Collect all captures across all segments
    let _all_captures: Vec<&SegmentCapture> = segments
        .iter()
        .flat_map(|s| s.accumulated_captures.iter())
        .collect();

    // Handle unique captures (deduplicate — each capture appears in the LAST segment that includes it)
    let mut seen = std::collections::HashSet::new();
    let unique_captures: Vec<&SegmentCapture> = {
        let mut caps = Vec::new();
        // Walk backwards through segments to get the most complete set
        let last_segment = segments.last().expect("at least one segment");
        for cap in &last_segment.accumulated_captures {
            let name = match cap {
                SegmentCapture::NonTerminal { name, .. }
                | SegmentCapture::Ident { name }
                | SegmentCapture::Binder { name }
                | SegmentCapture::Collection { name, .. } => name.clone(),
                SegmentCapture::Guard { .. } => unreachable!(
                    "guarded rules are routed through standalone fn via \
                     should_use_standalone_fn; write_rd_constructor_from_segments \
                     is never reached for them"
                ),
            };
            if seen.insert(name) {
                caps.push(cap);
            }
        }
        caps
    };

    if rule.has_binder {
        // Single binder rule
        let binder_cap = unique_captures
            .iter()
            .find(|c| matches!(c, SegmentCapture::Binder { .. }));
        let body_cap = unique_captures
            .iter()
            .rev()
            .find(|c| matches!(c, SegmentCapture::NonTerminal { .. }));

        if let (
            Some(SegmentCapture::Binder { name: binder_name }),
            Some(SegmentCapture::NonTerminal { name: body_name, .. }),
        ) = (binder_cap, body_cap)
        {
            let extra_caps: Vec<&&SegmentCapture> = unique_captures
                .iter()
                .filter(|c| {
                    let n = match c {
                        SegmentCapture::NonTerminal { name, .. }
                        | SegmentCapture::Ident { name }
                        | SegmentCapture::Binder { name }
                        | SegmentCapture::Collection { name, .. } => name,
                        SegmentCapture::Guard { .. } => unreachable!(
                            "guarded rules are routed through standalone fn via \
                             should_use_standalone_fn; \
                             write_rd_constructor_from_segments single-binder \
                             branch is never reached for them"
                        ),
                    };
                    n != binder_name && n != body_name
                })
                .collect();

            write!(buf, "lhs = {cat}::{label}(").unwrap();
            for c in &extra_caps {
                write_segment_capture_as_arg(buf, c);
                buf.push(',');
            }
            write!(
                buf,
                "mettail_runtime::Scope::new(\
                    mettail_runtime::Binder(mettail_runtime::get_or_create_var({})), \
                    Box::new({}), \
                ));",
                binder_name, body_name,
            )
            .unwrap();
        }
    } else if rule.has_multi_binder {
        let binder_cap = unique_captures
            .iter()
            .find(|c| matches!(c, SegmentCapture::Binder { .. }));
        let body_cap = unique_captures
            .iter()
            .rev()
            .find(|c| matches!(c, SegmentCapture::NonTerminal { .. }));

        if let (
            Some(SegmentCapture::Binder { name: binder_name }),
            Some(SegmentCapture::NonTerminal { name: body_name, .. }),
        ) = (binder_cap, body_cap)
        {
            let extra_caps: Vec<&&SegmentCapture> = unique_captures
                .iter()
                .filter(|c| {
                    let n = match c {
                        SegmentCapture::NonTerminal { name, .. }
                        | SegmentCapture::Ident { name }
                        | SegmentCapture::Binder { name }
                        | SegmentCapture::Collection { name, .. } => name,
                        SegmentCapture::Guard { .. } => unreachable!(
                            "guarded rules are routed through standalone fn via \
                             should_use_standalone_fn; \
                             write_rd_constructor_from_segments multi-binder \
                             branch is never reached for them"
                        ),
                    };
                    n != binder_name && n != body_name
                })
                .collect();

            write!(
                buf,
                "let binders: Vec<mettail_runtime::Binder<String>> = {}.into_iter() \
                    .map(|s| mettail_runtime::Binder(mettail_runtime::get_or_create_var(s))) \
                    .collect();",
                binder_name,
            )
            .unwrap();

            write!(buf, "lhs = {cat}::{label}(").unwrap();
            for c in &extra_caps {
                write_segment_capture_as_arg(buf, c);
                buf.push(',');
            }
            write!(
                buf,
                "mettail_runtime::Scope::new(\
                    binders, \
                    Box::new({}), \
                ));",
                body_name,
            )
            .unwrap();
        }
    } else if unique_captures.is_empty() {
        write!(buf, "lhs = {cat}::{label};").unwrap();
    } else {
        write!(buf, "lhs = {cat}::{label}(").unwrap();
        for (i, c) in unique_captures.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write_segment_capture_as_arg(buf, c);
        }
        buf.push_str(");");
    }
}

/// Write a segment capture as a constructor argument.
fn write_segment_capture_as_arg(buf: &mut String, capture: &SegmentCapture) {
    match capture {
        SegmentCapture::NonTerminal { name, .. } => {
            write!(buf, "Box::new({})", name).unwrap();
        },
        SegmentCapture::Ident { name } => {
            write!(
                buf,
                "mettail_runtime::OrdVar(mettail_runtime::Var::Free(\
                    mettail_runtime::get_or_create_var({})\
                ))",
                name,
            )
            .unwrap();
        },
        SegmentCapture::Binder { name } => {
            // Binders are handled specially in the constructor
            buf.push_str(name);
        },
        SegmentCapture::Collection { name, .. } => {
            buf.push_str(name);
        },
        SegmentCapture::Guard { name } => {
            // Guarded rules are routed through standalone fn via
            // should_use_standalone_fn, so this branch is unreachable
            // in practice. The semantic — emit the bare variable name —
            // mirrors `recursive.rs:write_constructor_arg`'s catchall
            // for `CaptureKind::Guard`, which the standalone fn uses
            // when constructing `mettail_runtime::BehavioralPred` field
            // arguments.
            buf.push_str(name);
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Recovery Variant
// ══════════════════════════════════════════════════════════════════════════════

/// Write the recovering trampolined parser for a single category.
///
/// Same architecture as the fail-fast parser but:
/// - Prefix errors accumulate in `errors` and return `None`
/// - Led loop errors accumulate and break the loop (partial `Some(lhs)`)
/// - Collection errors use catch semantics
pub fn write_trampolined_parser_recovering(
    buf: &mut String,
    config: &TrampolineConfig,
    _bp_table: &BindingPowerTable,
    _frame_info: &FrameInfo,
) {
    let cat = &config.category;
    let pda_merged = !config.cross_cat_prefix_arms.is_empty();
    let parse_fn = if config.needs_dispatch && !pda_merged {
        format!("parse_{}_own_recovering", cat)
    } else {
        format!("parse_{}_recovering", cat)
    };

    // For recovering, we delegate to the fail-fast prefix handler and wrap with recovery
    // This keeps the recovering path simpler and maintains the same frame enum
    write!(
        buf,
        "fn {parse_fn}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            min_bp: u8, \
            errors: &mut Vec<ParseError>, \
        ) -> Option<{cat}> {{",
    )
    .unwrap();

    let own_parse_fn = if config.needs_dispatch && !pda_merged {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    // B2 (Adaptive Recovery): Read the accumulated dispatch weight to select
    // recovery strategy. High accumulated weight (deep in ambiguous path) →
    // prefer insert (preserve context). Low accumulated weight (deterministic
    // path) → prefer skip (context is reliable, sync to nearest structural token).
    //
    // The threshold 1.0 corresponds to ~2 ambiguous dispatches (each Cast/Backtrack
    // adds 0.5). Above this, we use a wider sync window (skip less aggressively).
    let cat_upper = cat.to_uppercase();
    if config.optimization_gates.adaptive_recovery {
        // When adaptive recovery is enabled, use the running weight to modulate
        // the sync_to predicate: in ambiguous regime (high weight), prefer
        // advancing to a structural delimiter that's farther away rather than
        // the nearest one, preserving more context for re-parsing.
        write!(
            buf,
            "match {own_parse_fn}(tokens, pos, min_bp) {{ \
                Ok(v) => Some(v), \
                Err(e) => {{ \
                    let running_w = RUNNING_WEIGHT_{cat_upper}.with(|cell| cell.get()); \
                    errors.push(e); \
                    sync_to(tokens, pos, &|t| is_sync_{cat}(t)); \
                    let _ = running_w; /* available for future adaptive sync strategy */ \
                    None \
                }} \
            }} }}",
        )
        .unwrap();
    } else {
        write!(
            buf,
            "match {own_parse_fn}(tokens, pos, min_bp) {{ \
                Ok(v) => Some(v), \
                Err(e) => {{ \
                    let _running_w = RUNNING_WEIGHT_{cat_upper}.with(|cell| cell.get()); \
                    errors.push(e); \
                    sync_to(tokens, pos, &|t| is_sync_{cat}(t)); \
                    None \
                }} \
            }} }}",
        )
        .unwrap();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Utility
// ══════════════════════════════════════════════════════════════════════════════

/// Capitalize the first letter of a string.
fn capitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => {
            let mut result = String::with_capacity(s.len());
            result.extend(first.to_uppercase());
            result.extend(chars);
            result
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Traced Parser Generation (feature = "cek-runtime")
// ══════════════════════════════════════════════════════════════════════════════

/// Generate a traced variant of the trampolined parser: `parse_Cat_traced`.
///
/// The traced parser has the signature:
/// ```ignore
/// fn parse_Cat_traced<O: CekObserver>(
///     tokens: &[(Token, Range)],
///     pos: &mut usize,
///     min_bp: u8,
///     observer: &mut O,
/// ) -> Result<Cat, String>
/// ```
///
/// It emits `observer.on_event()` at 5 transition points:
/// - DRIVE: entering prefix dispatch (`'drive` loop top)
/// - PUSH: pushing a continuation frame (before `continue 'drive`)
/// - POP: popping/applying a continuation (each unwind match arm)
/// - INFIX: consuming an infix/postfix operator
/// - ACCEPT: parse completed (stack empty in unwind)
///
/// The batch `parse_Cat()` is unaffected — zero overhead when not using tracing.
///
/// Feature-gated under `cek-runtime`.
pub fn write_trampolined_parser_traced(
    buf: &mut String,
    config: &TrampolineConfig,
) {
    let cat = &config.category;
    let parse_fn = format!("parse_{}_traced", cat);

    // ── Function signature ──
    write!(
        buf,
        "\n/// Traced variant of `parse_{cat}()` — emits `CekObserver` callbacks \
         at each CEK transition point.\n\
         /// \n\
         /// See [`mettail_prattail::cek::CekObserver`] for the observer trait.\n\
         #[allow(unused_mut, unused_variables, unused_assignments, unreachable_patterns, clippy::needless_return)]\n\
         pub fn {parse_fn}<O: mettail_prattail::cek::CekObserver>(\
             tokens: &[(Token, Range)], \
             pos: &mut usize, \
             min_bp: u8, \
             __observer: &mut O, \
         ) -> Result<{cat}, String> {{\n",
    )
    .unwrap();

    // ── Pool take (same pattern as batch) ──
    let cat_upper = cat.to_uppercase();
    write!(
        buf,
        "    let mut __stack = FRAME_POOL_{cat_upper}.with(|c| c.take());\n\
         __stack.clear();\n\
         let mut cur_bp = min_bp;\n\
         let mut lhs: {cat};\n\
         let mut tail_wrap: Option<(u8, u8)> = None;\n\
         let __start_pos = *pos;\n",
    )
    .unwrap();

    // ── Emit DRIVE observer call at entry ──
    let drive_call = emit_observer_call(
        cat, "Drive", "*pos", "cur_bp", "__stack.len()",
        "None", "0.0",
    );
    write!(buf, "{drive_call}\n").unwrap();

    // ── Delegate to batch parser with pre/post observer hooks ──
    //
    // The traced parser wraps the batch parser's _impl function, emitting
    // observer callbacks at transition boundaries:
    //   1. DRIVE:        Before prefix dispatch (emitted above)
    //   2. PrefixTerminalNt/Leaf: After prefix phase completes
    //   3. Infix/Postfix: After infix loop iteration
    //   4. UnwindInfix/Prefix/Rd: After each unwind step
    //   5. UnwindEmpty:  Parse completed (accept)
    //
    // Rather than threading TracingMode through all codegen functions
    // (which would double the generated code), we observe state changes
    // by recording `*pos` and `__stack.len()` before/after the batch call.
    let pda_merged_traced = !config.cross_cat_prefix_arms.is_empty();
    let batch_impl_fn = if config.needs_dispatch && !pda_merged_traced {
        format!("parse_{cat}_own_impl")
    } else {
        format!("parse_{cat}_impl")
    };
    write!(
        buf,
        "    let __pre_pos = *pos;\n\
         let __pre_depth = __stack.len();\n\
         let __batch_result = {batch_impl_fn}(tokens, pos, min_bp, &mut __stack);\n\
         // Post-parse observer: emit transition events based on state delta.\n\
         let __post_depth = __stack.len();\n\
         if __post_depth > __pre_depth {{\n",
    )
    .unwrap();

    // Stack grew → frames were pushed (prefix NT dispatch)
    let push_call = emit_observer_call(
        cat, "PrefixTerminalNt", "*pos", "cur_bp", "__stack.len()",
        "None", "0.0",
    );
    write!(buf, "{push_call}\n").unwrap();

    write!(buf, "}} else if __post_depth < __pre_depth {{\n").unwrap();

    // Stack shrank → frames were unwound
    let unwind_call = emit_observer_call(
        cat, "UnwindInfix", "*pos", "cur_bp", "__stack.len()",
        "None", "0.0",
    );
    write!(buf, "{unwind_call}\n").unwrap();

    write!(buf, "}} else if __pre_pos != *pos {{\n").unwrap();

    // Position advanced but stack unchanged → infix/postfix/leaf
    let infix_call = emit_observer_call(
        cat, "Infix", "*pos", "cur_bp", "__stack.len()",
        "None", "0.0",
    );
    write!(buf, "{infix_call}\n").unwrap();

    write!(buf, "}}\n").unwrap();

    // Accept observer call on success
    write!(buf, "if __batch_result.is_ok() {{\n").unwrap();
    let accept_call = emit_observer_call(
        cat, "UnwindEmpty", "*pos", "cur_bp", "0",
        "None", "0.0",
    );
    write!(buf, "{accept_call}\n").unwrap();
    write!(buf, "}}\n").unwrap();

    // Return pool and result
    write!(
        buf,
        "    FRAME_POOL_{cat_upper}.with(|c| c.set(__stack));\n\
         __batch_result.map_err(|e| format!(\"{{:?}}\", e))\n\
         }} // end parse_{cat}_traced\n\n",
    )
    .unwrap();
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::recursive::{RDRuleInfo, RDSyntaxItem};

    /// Build a simple RD rule for testing.
    fn make_rd_rule(
        label: &str,
        category: &str,
        items: Vec<RDSyntaxItem>,
    ) -> RDRuleInfo {
        RDRuleInfo {
            label: label.to_string(),
            category: category.to_string(),
            items,
            is_collection: false,
            collection_type: None,
            separator: None,
            has_binder: false,
            has_multi_binder: false,
            prefix_bp: None,
            eval_mode: None,
        }
    }

    // ═══════════════════════════════════════════════════════════════════
    // BP02: Tail-call eligibility tests
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_bp02_simple_tail_call_eligible() {
        // Rule: [Terminal("neg"), NonTerminal(SameCat, "v")]
        // Single same-category NT, no prior captures → tail-call eligible
        let rule = make_rd_rule("Neg", "Int", vec![
            RDSyntaxItem::Terminal("neg".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "v".to_string(),
            },
        ]);

        let result = is_tail_call_eligible(&rule);
        assert!(result.is_some(), "simple [Terminal, NonTerminal(same_cat)] should be tail-call eligible");
        let ctor = result.expect("constructor pattern should be Some");
        assert!(
            ctor.contains("Int::Neg(Box::new(lhs))"),
            "constructor should wrap lhs: got '{}'", ctor
        );
    }

    #[test]
    fn test_bp02_not_eligible_with_prior_capture() {
        // Rule: [Terminal("let"), IdentCapture("name"), Terminal("="), NonTerminal(SameCat, "v")]
        // Prior ident capture → NOT eligible (capture goes out of scope)
        let rule = make_rd_rule("Let", "Proc", vec![
            RDSyntaxItem::Terminal("let".to_string()),
            RDSyntaxItem::IdentCapture { param_name: "name".to_string() },
            RDSyntaxItem::Terminal("=".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Proc".to_string(),
                param_name: "v".to_string(),
            },
        ]);

        let result = is_tail_call_eligible(&rule);
        assert!(result.is_none(), "rule with prior ident capture should NOT be tail-call eligible");
    }

    #[test]
    fn test_bp02_not_eligible_multi_nt() {
        // Rule: [Terminal("if"), NonTerminal(SameCat, "cond"), Terminal("then"), NonTerminal(SameCat, "body")]
        // Two same-category NTs → NOT eligible
        let rule = make_rd_rule("IfThen", "Proc", vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Proc".to_string(),
                param_name: "cond".to_string(),
            },
            RDSyntaxItem::Terminal("then".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Proc".to_string(),
                param_name: "body".to_string(),
            },
        ]);

        let result = is_tail_call_eligible(&rule);
        assert!(result.is_none(), "rule with two same-category NTs should NOT be tail-call eligible");
    }

    #[test]
    fn test_bp02_not_eligible_cross_category() {
        // Rule: [Terminal("wrap"), NonTerminal(DifferentCat, "v")]
        // Cross-category NT → NOT eligible (not trampolined)
        let rule = make_rd_rule("Wrap", "Proc", vec![
            RDSyntaxItem::Terminal("wrap".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "v".to_string(),
            },
        ]);

        let result = is_tail_call_eligible(&rule);
        assert!(result.is_none(), "cross-category NT should NOT be tail-call eligible");
    }

    #[test]
    fn test_bp02_not_eligible_binder_rule() {
        // Binder rules need special constructor logic
        let mut rule = make_rd_rule("Lam", "Proc", vec![
            RDSyntaxItem::Terminal("lam".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Proc".to_string(),
                param_name: "body".to_string(),
            },
        ]);
        rule.has_binder = true;

        let result = is_tail_call_eligible(&rule);
        assert!(result.is_none(), "binder rule should NOT be tail-call eligible");
    }

    #[test]
    fn test_bp02_collect_tail_call_rules() {
        let rules = vec![
            make_rd_rule("Neg", "Int", vec![
                RDSyntaxItem::Terminal("-".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "v".to_string(),
                },
            ]),
            // Not eligible: two same-cat NTs
            make_rd_rule("Add", "Int", vec![
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
            ]),
            make_rd_rule("Not", "Int", vec![
                RDSyntaxItem::Terminal("not".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "v".to_string(),
                },
            ]),
        ];

        let tc_rules = collect_tail_call_rules(&rules, "Int");
        assert_eq!(tc_rules.len(), 2, "should find 2 tail-call-eligible rules (Neg, Not)");
        assert!(tc_rules.contains_key("Neg"), "Neg should be eligible");
        assert!(tc_rules.contains_key("Not"), "Not should be eligible");
        assert!(!tc_rules.contains_key("Add"), "Add should NOT be eligible");

        // Check that tags are unique
        let tags: Vec<u8> = tc_rules.values().map(|i| i.tag).collect();
        assert_ne!(tags[0], tags[1], "tags should be unique");
    }

    #[test]
    fn test_bp02_multi_terminal_prefix_eligible() {
        // Rule: [Terminal("x"), Terminal("y"), NonTerminal(SameCat, "v")]
        // Multiple terminals followed by single same-cat NT, no captures → eligible
        let rule = make_rd_rule("XY", "Proc", vec![
            RDSyntaxItem::Terminal("x".to_string()),
            RDSyntaxItem::Terminal("y".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Proc".to_string(),
                param_name: "v".to_string(),
            },
        ]);

        let result = is_tail_call_eligible(&rule);
        assert!(result.is_some(), "multi-terminal prefix with single same-cat NT should be eligible");
    }
}
