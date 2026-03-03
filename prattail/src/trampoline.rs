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
use crate::dispatch::CastRule;
use crate::pratt::PrefixHandler;
use crate::prediction::FirstSet;
use crate::recursive::{CollectionKind, RDRuleInfo, RDSyntaxItem};

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

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

/// Check if a rule should be trampolined (inlined/split) or dispatched to
/// its standalone parse function.
///
/// Returns true if the rule should use its standalone parse function and NOT
/// be trampolined. This includes:
/// - Rules with Sep items (complex parsing logic)
/// - Rules with multi-binder items (complex binder handling)
fn should_use_standalone_fn(rule: &RDRuleInfo) -> bool {
    has_complex_sep(rule) || rule.has_multi_binder
}

/// Group terminal-first RD rules by their dispatch token variant.
///
/// Returns a `BTreeMap<variant_name, Vec<&RDRuleInfo>>` for rules in `cat` that:
/// - Are not simple collections
/// - Have no `prefix_bp` (not unary prefix)
/// - Start with a terminal (not a nonterminal/ident capture)
///
/// Uses `BTreeMap` for deterministic arm ordering.
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

/// A2: Compute the disambiguation complexity of an NFA-ambiguous rule group.
///
/// Uses `ComplexityWeight` (bottleneck semiring: ⊕ = min, ⊗ = max) to represent
/// the worst-case backtrack depth × alternative count for the group. The result
/// indicates how much work the NFA try-all must do to resolve this ambiguity:
///
/// - `ComplexityWeight::deterministic()` (0) — no ambiguity (single rule)
/// - `ComplexityWeight::single_lookahead()` (1) — trivial: 2 alternatives, 1 item each
/// - Higher values — more complex disambiguation requiring deeper backtracks
///
/// The cost-benefit framework uses this to selectively enable B1 (multi-token
/// lookahead) only for groups whose complexity exceeds a threshold, avoiding
/// unnecessary lookahead codegen overhead for simple groups.
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

/// B1: Analyze whether an NFA-merged rule group can be disambiguated by
/// peeking at the second token instead of trying all alternatives.
///
/// Returns `Some(map)` where map is `second_token_variant → &RDRuleInfo` when
/// every rule in the group has a distinct second terminal. Returns `None` when:
/// - Fewer than 2 rules (no ambiguity to resolve)
/// - Any rule lacks a second terminal (e.g., single-token rule, or second item
///   is a NonTerminal/IdentCapture)
/// - Two rules share the same second terminal (ambiguity persists at depth 2)
/// B1 result: maps second-token variant → rule index within the group.
/// Only produced when every rule has a distinct second item that is a terminal.
struct TwoTokenLookahead {
    /// second_variant → index into the original inlineable slice
    groups: std::collections::BTreeMap<String, usize>,
}

fn second_token_lookahead(
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

/// A1: Compute the longest shared terminal prefix among rules (starting from
/// items[1], since items[0] is the shared dispatch token).
///
/// Returns the shared terminal strings. For example, if all rules start with
/// `"float" "(" ...`, items[0]="float" is the dispatch token, items[1]="(" is
/// the shared prefix. The returned vec would be `["("]`.
///
/// Returns empty vec when:
/// - Fewer than 2 rules
/// - Any rule's items[1..] starts with a non-terminal
/// - The items[1..] diverge immediately (no shared prefix)
fn compute_shared_terminal_prefix(rules: &[&RDRuleInfo]) -> Vec<String> {
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
            write!(buf, "stack.push({}::{} {{", frame_info.enum_name, segments[0].frame_variant)
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

    // ── A1: Left-factoring via shared prefix ────────────────────────────
    // Before trying NFA try-all, check if rules share a common prefix of
    // terminals (beyond the dispatch token). Walk shared terminals once without
    // save/restore, then NFA try-all only over the remaining (divergent) items.
    // This reduces code size and avoids redundant token matching.
    // A3: Gated by `optimization_gates.left_factoring`.
    if config.optimization_gates.left_factoring && frame_pushing.is_empty() && inlineable.len() >= 2 {
        let shared_terminal_prefix = compute_shared_terminal_prefix(inlineable);
        // shared_terminal_prefix starts from items[1] (items[0] is dispatch token).
        // If ≥ 1 shared terminal beyond the dispatch token, left-factor.
        if !shared_terminal_prefix.is_empty() {
            write!(buf, "Token::{} => {{", variant).unwrap();
            // Consume the dispatch token
            buf.push_str("*pos += 1;");

            // Walk the shared terminal prefix
            for terminal in &shared_terminal_prefix {
                let shared_variant = terminal_to_variant_name(terminal);
                write!(
                    buf,
                    "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                    shared_variant, terminal,
                )
                .unwrap();
            }

            // Now do NFA try-all over the divergent suffixes
            // The number of items to skip = 1 (dispatch token) + shared_prefix_len
            let skip_count = 1 + shared_terminal_prefix.len();

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
                        "stack.push({}::{} {{",
                        frame_info.enum_name, segments[0].frame_variant
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
                write!(cold_fns, "match (|| -> Result<{}, ParseError> {{", cat).unwrap();
                write_inline_items(cold_fns, &segments[0].inline_items, true);
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
            // Fully inlineable: wrap in a closure to use ? operator
            write!(buf, "match (|| -> Result<{}, ParseError> {{", cat,).unwrap();
            write_inline_items(buf, &segments[0].inline_items, true);

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
            if config.needs_dispatch && segments[0].nonterminal.is_some() {
                // ── Dispatch-aware fallback ──────────────────────────────────
                // When this category has a dispatch wrapper (parse_Cat), the
                // same-category nonterminal must route through it so that
                // cross-category rules are available. The trampoline's
                // continue 'drive only runs parse_Cat_own, missing dispatch.
                //
                // Solution: inline all segments with direct dispatch wrapper
                // calls for same-category nonterminals. Cast nesting depth is
                // bounded (1-2 levels) so stack overflow is not a concern.

                // Segment 0: consume prefix terminals
                write_inline_items(buf, &segments[0].inline_items, true);

                // Call dispatch wrapper for same-category nonterminal
                if let Some(ref nt) = segments[0].nonterminal {
                    write!(
                        buf,
                        "let {} = parse_{}(tokens, pos, {})?;",
                        nt.param_name, cat, nt.bp,
                    )
                    .unwrap();
                }

                // Remaining segments: consume inline items + nonterminals
                for seg in &segments[1..] {
                    write_inline_items(buf, &seg.inline_items, false);
                    if let Some(ref nt) = seg.nonterminal {
                        write!(
                            buf,
                            "let {} = parse_{}(tokens, pos, {})?;",
                            nt.param_name, cat, nt.bp,
                        )
                        .unwrap();
                    }
                }

                // Build constructor (uses captures bound above)
                write_rd_constructor_inline(buf, rd_rule, &segments);
            } else {
                // Original: push frame + continue 'drive (stack-safe)
                write_inline_items(buf, &segments[0].inline_items, true);
                if let Some(ref nt) = segments[0].nonterminal {
                    write!(
                        buf,
                        "stack.push({}::{} {{",
                        frame_info.enum_name, segments[0].frame_variant
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

/// A single variant in the Frame enum.
#[derive(Debug)]
pub struct FrameVariant {
    /// Variant name (e.g., "InfixRHS", "GroupClose", "RD_PInput_0").
    pub name: String,
    /// Fields in this variant.
    pub fields: Vec<FrameField>,
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
    let enum_name = format!("Frame_{}", cat);

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
                        };
                        fields.push(FrameField { name: name.clone(), type_str });
                    },
                }
            }

            variants.push(FrameVariant {
                name: segment.frame_variant.clone(),
                fields,
            });
        }
    }

    // ── Per-collection variants ──
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

        let type_str = match collection_type {
            CollectionKind::HashBag => format!("mettail_runtime::HashBag<{}>", element_category),
            CollectionKind::HashSet => format!("std::collections::HashSet<{}>", element_category),
            CollectionKind::Vec => format!("Vec<{}>", element_category),
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

    // NOTE: Cast rules are NOT trampolined — they call parse_SourceCat() directly
    // in the prefix (cross-category, bounded depth). No CastWrap_* frame variants needed.

    // ── Write the enum declaration ──
    // Frame_Cat is 'static (no lifetime parameter) — all fields are owned types.
    // This enables thread-local pooling of the continuation stack.
    write!(buf, "enum {} {{", enum_name).unwrap();
    for variant in &variants {
        write!(buf, "{} {{", variant.name).unwrap();
        for field in &variant.fields {
            // Skip phantom fields that encode type info as string literals
            if field.type_str.starts_with('"') {
                continue;
            }
            write!(buf, "{}: {},", field.name, field.type_str).unwrap();
        }
        buf.push_str("},");
    }
    buf.push('}');

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
) {
    let cat = &config.category;
    let parse_fn = if config.needs_dispatch {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    let has_delegation = !config.led_delegation.is_empty();
    let has_led = config.has_infix || config.has_postfix || config.has_mixfix || has_delegation;

    // ── 1. Generate helper functions (same as pratt.rs) ──

    if config.has_infix {
        crate::pratt::write_bp_function_pub(buf, cat, bp_table);
        crate::pratt::write_make_infix_pub(buf, cat, bp_table);
    }
    if config.has_postfix {
        crate::pratt::write_postfix_bp_function_pub(buf, cat, bp_table);
        crate::pratt::write_make_postfix_pub(buf, cat, bp_table);
    }
    if config.has_mixfix {
        crate::pratt::write_mixfix_bp_function_pub(buf, cat, bp_table);
    }

    // ── 1a. Generate LED delegation functions (sum-type categories) ──
    if has_delegation {
        write_led_delegation_fns(buf, config, bp_table);
    }

    // ── 2. Generate Frame enum ──
    let frame_info = write_frame_enum(buf, config, rd_rules, bp_table);

    // ── 3. Generate thread-local frame stack pool ──
    // Each category gets its own thread-local Vec<Frame_Cat> that retains capacity
    // across parse calls. Uses Cell (not RefCell) with take/set pattern to support
    // re-entrant calls from standalone parse functions (Sep, multi-binder,
    // ident-lookahead rules). Nested calls gracefully get a fresh Vec.
    let cat_upper = cat.to_uppercase();
    write!(
        buf,
        "thread_local! {{ \
            static FRAME_POOL_{cat_upper}: std::cell::Cell<Vec<{frame_enum}>> = \
                std::cell::Cell::new(Vec::new()); \
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

        // Classify each variant by prefix convention
        for variant in &frame_info.variants {
            let kind_u8 = if variant.name == "InfixRHS" {
                1_u8 // FrameKind::InfixRHS
            } else if variant.name == "GroupClose" {
                4 // FrameKind::Group
            } else if variant.name.starts_with("CollectionElem_") {
                3 // FrameKind::Collection
            } else if variant.name.starts_with("Mixfix_") {
                5 // FrameKind::Mixfix
            } else if variant.name.starts_with("UnaryPrefix_") {
                0 // FrameKind::Prefix
            } else if variant.name.starts_with("LambdaBody_") {
                6 // FrameKind::Lambda
            } else if variant.name.starts_with("Dollar") || variant.name.starts_with("Ddollar") {
                7 // FrameKind::Dollar
            } else if variant.name.starts_with("CastWrap_") {
                8 // FrameKind::CastWrap
            } else {
                9 // FrameKind::Other (RD segments, etc.)
            };

            // Use wildcard pattern for all fields
            write!(
                buf,
                "Some({}::{} {{ .. }}) => {}_u8,",
                frame_info.enum_name, variant.name, kind_u8,
            )
            .unwrap();
        }

        buf.push_str("None => 9_u8,"); // empty stack → Other
        buf.push_str("}}");
    }

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
                }} \
                let result = {parse_fn}_impl(tokens, pos, min_bp, &mut stack); \
                cell.set(stack); \
                result \
            }}) \
        }}",
    )
    .unwrap();

    // ── 5. Generate the inner trampolined parse function (_impl) ──
    // A4: Cold NFA helper functions are generated during prefix arm codegen and
    // emitted as sibling functions at the same scope level as `_impl`. The body is
    // written to a temporary buffer so cold helpers can be placed before `_impl`
    // in the final output (they need to be visible at the call site).
    let mut cold_fns = String::new();
    let mut body_buf = String::new();
    write_trampoline_body(&mut body_buf, &mut cold_fns, config, bp_table, prefix_handlers, rd_rules, &frame_info, &parse_fn);
    buf.push_str(&cold_fns);
    buf.push_str(&body_buf);
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
) {
    let cat = &config.category;
    let has_led = config.has_infix || config.has_postfix || config.has_mixfix;

    // Build expected message for error reporting
    let expected_msg = crate::pratt::build_expected_message_pub(cat, &config.own_first_set);
    let expected_escaped = expected_msg.replace('\\', "\\\\").replace('"', "\\\"");

    // Inner implementation function signature — takes the continuation stack by reference
    // so it can be pooled in a thread-local across parse calls.
    write!(
        buf,
        "fn {parse_fn}_impl<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            min_bp: u8, \
            stack: &mut Vec<{frame_enum}>, \
        ) -> Result<{cat}, ParseError> {{",
        frame_enum = frame_info.enum_name,
    )
    .unwrap();

    // Clear the pooled stack (retains capacity from previous calls).
    buf.push_str("stack.clear();");
    buf.push_str("let mut cur_bp = min_bp;");

    // ═══ Main trampoline loop ═══
    buf.push_str("'drive: loop {");

    // Update frame state thread-local at the top of each 'drive iteration.
    // This reflects the current depth and frame kind before prefix dispatch
    // (where parse errors are raised). Recovery reads this thread-local to
    // apply Tier 1 frame-kind cost multipliers.
    {
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
    write_prefix_phase(buf, cold_fns, config, prefix_handlers, rd_rules, frame_info, &expected_escaped);

    // ═══ Phase B: Infix loop + continuation unwinding ═══
    buf.push_str("'unwind: loop {");

    // Infix loop (iterative — left-assoc chains stay here)
    if has_led {
        write_infix_loop(buf, config, bp_table, frame_info);
    }

    // Pop continuation
    write_unwind_handlers(buf, config, bp_table, rd_rules, frame_info);

    buf.push_str("} }"); // close 'unwind and 'drive loops

    buf.push('}'); // close function
}

/// Write Phase A: prefix dispatch.
///
/// Produces a value (break 'prefix) or pushes a frame and continues 'drive.
fn write_prefix_phase(
    buf: &mut String,
    cold_fns: &mut String,
    config: &TrampolineConfig,
    prefix_handlers: &[PrefixHandler],
    rd_rules: &[RDRuleInfo],
    frame_info: &FrameInfo,
    expected_escaped: &str,
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

    buf.push_str("match &tokens[*pos].0 {");

    // Generate match arms (same code in both paths — WFST ordering affects
    // cross-category dispatch backtracking order, not prefix match semantics)
    write_prefix_match_arms(buf, cold_fns, config, prefix_handlers, rd_rules, frame_info, expected_escaped);

    buf.push_str("} };"); // close match and 'prefix block
}

/// Write the prefix match arms.
fn write_prefix_match_arms(
    buf: &mut String,
    cold_fns: &mut String,
    config: &TrampolineConfig,
    prefix_handlers: &[PrefixHandler],
    rd_rules: &[RDRuleInfo],
    frame_info: &FrameInfo,
    expected_escaped: &str,
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

    // Track whether LParen has been handled by an RD rule arm so we can
    // suppress the later grouping handler and avoid duplicate match arms.
    let mut lparen_handled = false;

    for (variant, rules) in &rd_by_token {
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
                    // Standalone or fully-inline rule at LParen: save/restore +
                    // grouping fallback.
                    lparen_handled = true;
                    write!(buf, "Token::LParen => {{").unwrap();
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

                    // Grouping fallback: restore position, emit grouping logic
                    buf.push_str("*pos = saved;");
                    if config.needs_dispatch {
                        write!(
                            buf,
                            "*pos += 1; \
                            let expr = parse_{}(tokens, pos, 0)?; \
                            expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
                            break 'prefix expr;",
                            cat,
                        )
                        .unwrap();
                    } else {
                        write!(
                            buf,
                            "*pos += 1; \
                            stack.push({}::GroupClose {{ saved_bp: cur_bp }}); \
                            cur_bp = 0; \
                            continue 'drive;",
                            frame_info.enum_name,
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
                // Same-category nonterminal: push frame for continuation, continue 'drive
                write!(
                    buf,
                    "stack.push({}::{} {{",
                    frame_info.enum_name, segments[0].frame_variant
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
                // No same-category nonterminal — fully inline the constructor
                write_rd_constructor_inline(buf, rd_rule, &segments);
            }

            buf.push_str("},");
        } else {
            // Multiple rules share this dispatch token — NFA-style merged arm.
            // Only rules that are fully inlined (all NTs cross-category) can be
            // merged. Rules requiring frame-pushing are emitted separately with
            // a diagnostic comment.
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
                    // Check if first segment has a same-category nonterminal (frame-pushing)
                    if segments[0].nonterminal.is_some() {
                        frame_pushing.push(rd_rule);
                    } else {
                        inlineable.push(rd_rule);
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
        // Pattern: [Terminal, NonTerminal(same_category)]
        if let Some(RDSyntaxItem::Terminal(t)) = rd_rule.items.first() {
            let variant = terminal_to_variant_name(t);
            let bp = rd_rule.prefix_bp.unwrap_or(0);
            write!(
                buf,
                "Token::{} => {{ \
                    *pos += 1; \
                    stack.push({}::UnaryPrefix_{} {{ saved_bp: cur_bp }}); \
                    cur_bp = {}; \
                    continue 'drive; \
                }},",
                variant, frame_info.enum_name, rd_rule.label, bp,
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

        // Find the opening terminal and collection info
        let opening_terminal = rd_rule.items.iter().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item {
                Some(t.clone())
            } else {
                None
            }
        });
        let collection_info = rd_rule.items.iter().find_map(|item| match item {
            RDSyntaxItem::Collection { element_category, separator, kind, .. } => {
                Some((element_category.clone(), separator.clone(), *kind))
            },
            _ => None,
        });

        if let (Some(terminal), Some((_elem_cat, _sep, kind))) = (opening_terminal, collection_info)
        {
            let variant = terminal_to_variant_name(&terminal);
            let init_str = match kind {
                CollectionKind::HashBag => "mettail_runtime::HashBag::new()",
                CollectionKind::HashSet => "std::collections::HashSet::new()",
                CollectionKind::Vec => "Vec::new()",
            };

            write!(
                buf,
                "Token::{} => {{ \
                    *pos += 1; \
                    stack.push({}::CollectionElem_{} {{ \
                        elements: {}, \
                        saved_pos: *pos, \
                        saved_bp: cur_bp, \
                    }}); \
                    cur_bp = 0; \
                    continue 'drive; \
                }},",
                variant, frame_info.enum_name, rd_rule.label, init_str,
            )
            .unwrap();
        }
    }

    // ── Native literal match arms ──
    if let Some(ref native_type) = config.native_type {
        write_native_literal_arm(buf, cat, native_type);
    }

    // ── Grouping: parenthesized expression ──
    //
    // When `needs_dispatch` is true, this category has a dispatch wrapper
    // (parse_Cat) that handles cross-category rules. Grouping must call
    // that wrapper so expressions like `(3 == 3)` can dispatch to a
    // different source category inside parentheses.
    //
    // When `needs_dispatch` is false, we use the continuation-stack
    // approach (GroupClose frame + continue 'drive) for full stack-safety.
    //
    // Skip if LParen was already handled by an RD rule arm above
    // (either with save/restore + grouping fallback for standalone/inline
    // rules, or as a frame-pushing rule that owns LParen).
    if !lparen_handled {
        if config.needs_dispatch {
            write!(
                buf,
                "Token::LParen => {{ \
                    *pos += 1; \
                    let expr = parse_{}(tokens, pos, 0)?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
                    break 'prefix expr; \
                }},",
                cat,
            )
            .unwrap();
        } else {
            write!(
                buf,
                "Token::LParen => {{ \
                    *pos += 1; \
                    stack.push({}::GroupClose {{ saved_bp: cur_bp }}); \
                    cur_bp = 0; \
                    continue 'drive; \
                }},",
                frame_info.enum_name,
            )
            .unwrap();
        }
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
                    crate::pratt::write_token_pattern_pub(&mut arm, token);
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
                // Variants with data use wildcard: Token::Integer(_), Token::Ident(_), etc.
                match *v {
                    "Integer" => "Token::Integer(_)".to_string(),
                    "Float" => "Token::Float(_)".to_string(),
                    "Boolean" => "Token::Boolean(_)".to_string(),
                    "StringLit" => "Token::StringLit(_)".to_string(),
                    "Ident" => "Token::Ident(_)".to_string(),
                    "Dollar" => "Token::Dollar(_)".to_string(),
                    "DoubleDollar" => "Token::DoubleDollar(_)".to_string(),
                    other => format!("Token::{}", other),
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
                "Token::Integer(v) => {{ let val = *v as i32; *pos += 1; break 'prefix {}::NumLit(val); }},",
                cat,
            ).unwrap();
        },
        "i64" | "isize" => {
            write!(
                buf,
                "Token::Integer(v) => {{ let val = *v; *pos += 1; break 'prefix {}::NumLit(val); }},",
                cat,
            ).unwrap();
        },
        "u32" => {
            write!(
                buf,
                "Token::Integer(v) => {{ let val = *v as u32; *pos += 1; break 'prefix {}::NumLit(val); }},",
                cat,
            ).unwrap();
        },
        "u64" | "usize" => {
            write!(
                buf,
                "Token::Integer(v) => {{ let val = *v as u64; *pos += 1; break 'prefix {}::NumLit(val); }},",
                cat,
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
                    stack.push({enum_name}::LambdaBody_Multi {{ binder_names, saved_bp: cur_bp }}); \
                    cur_bp = 0; \
                    continue 'drive; \
                }} \
                Some(Token::Ident(_)) => {{ \
                    let binder_name = expect_ident(tokens, pos)?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::Dot), \".\")?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::LBrace), \"{{\")?; \
                    stack.push({enum_name}::LambdaBody_Single {{ binder_name, saved_bp: cur_bp }}); \
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
        enum_name = frame_info.enum_name,
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
                stack.push({enum_name}::DollarF_{dom_cap} {{ saved_bp: cur_bp }}); \
                cur_bp = 0; \
                continue 'drive; \
            }},",
            enum_name = frame_info.enum_name,
        )
        .unwrap();

        // Multi-apply: $$dom( — consume token (includes opening paren), push frame for f parse
        write!(
            buf,
            "Token::{ddollar_variant} => {{ \
                *pos += 1; \
                stack.push({enum_name}::DdollarF_{dom_cap} {{ saved_bp: cur_bp }}); \
                cur_bp = 0; \
                continue 'drive; \
            }},",
            enum_name = frame_info.enum_name,
        )
        .unwrap();
    }
}

/// Write the infix loop (iterative portion).
fn write_infix_loop(
    buf: &mut String,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
    frame_info: &FrameInfo,
) {
    let cat = &config.category;

    buf.push_str("loop { if *pos >= tokens.len() { break; } let token = &tokens[*pos].0;");

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
    if config.has_infix {
        if wrote_first {
            buf.push_str(" else ");
        }
        write!(
            buf,
            "if let Some((l_bp, r_bp)) = infix_bp_{cat}(token) {{ \
                if l_bp < cur_bp {{ break; }} \
                let op_pos = *pos; \
                *pos += 1; \
                stack.push({enum_name}::InfixRHS {{ lhs, op_pos, saved_bp: cur_bp }}); \
                cur_bp = r_bp; \
                continue 'drive; \
            }}",
            enum_name = frame_info.enum_name,
        )
        .unwrap();
        wrote_first = true;
    }

    // LED delegation fallback: when the sum type's own operators don't match,
    // try delegating to constituent categories' operators.
    let has_delegation = !config.led_delegation.is_empty();
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
            "stack.push({enum_name}::Mixfix_{label}_0 {{ lhs, saved_bp: cur_bp }}); \
            cur_bp = 0; \
            continue 'drive;",
            enum_name = frame_info.enum_name,
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
                    stack.push({enum_name}::Mixfix_{label}_0 {{ lhs, saved_bp: cur_bp }}); \
                    cur_bp = 0; \
                    continue 'drive; \
                }},",
                variant,
                enum_name = frame_info.enum_name,
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
    for source in &config.led_delegation {
        if source.has_mixfix {
            crate::pratt::write_handle_mixfix_pub(buf, &source.source_category, bp_table);
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
    bp_table: &BindingPowerTable,
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
        write!(
            buf,
            "if let Some((_l_bp, r_bp)) = mixfix_bp_{src}(token) {{ \
                let op_token = token.clone(); \
                *pos += 1; \
                match handle_mixfix_{src}(&op_token, lhs, tokens, pos, r_bp) {{ \
                    Ok(result) => return Some({cat}::{cast}(Box::new(result))), \
                    Err(_) => return None, \
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
        write!(
            buf,
            "if let Some((_l_bp, r_bp)) = infix_bp_{src}(token) {{ \
                let op_token = token.clone(); \
                *pos += 1; \
                match parse_{src}(tokens, pos, r_bp) {{ \
                    Ok(rhs) => return Some({cat}::{cast}(Box::new(make_infix_{src}(&op_token, lhs, rhs)))), \
                    Err(_) => return None, \
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

        for op in &source.cross_cat_ops {
            let variant = terminal_to_variant_name(&op.terminal);
            write!(
                buf,
                "Token::{variant} => {{ \
                    *pos += 1; \
                    match parse_{src}(tokens, pos, {r_bp}) {{ \
                        Ok(rhs) => return Some({cat}::{rewrap}(Box::new(\
                            {result_cat}::{label}(Box::new(lhs), Box::new(rhs))\
                        ))), \
                        Err(_) => return None, \
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

            write!(
                buf,
                "if has_led_token_{src}(token) {{ \
                    let mut try_pos = saved_pos; \
                    let coerced = {src}::{proj}(Box::new(lhs.clone())); \
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

    write!(buf, "match stack.pop() {{ None => return Ok(lhs),").unwrap();

    // ── InfixRHS ──
    if config.has_infix {
        write!(
            buf,
            "Some({enum_name}::InfixRHS {{ lhs: prev, op_pos, saved_bp }}) => {{ \
                lhs = make_infix_{cat}(&tokens[op_pos].0, prev, lhs); \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name,
        )
        .unwrap();
    }

    // ── GroupClose ──
    write!(
        buf,
        "Some({enum_name}::GroupClose {{ saved_bp }}) => {{ \
            expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
            cur_bp = saved_bp; \
        }},",
        enum_name = frame_info.enum_name,
    )
    .unwrap();

    // ── UnaryPrefix variants ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || rd_rule.prefix_bp.is_none() {
            continue;
        }
        write!(
            buf,
            "Some({enum_name}::UnaryPrefix_{label} {{ saved_bp }}) => {{ \
                lhs = {cat}::{label}(Box::new(lhs)); \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name,
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
        // Generate unwind handler for each segment that has a nonterminal
        for (i, segment) in segments.iter().enumerate() {
            if segment.nonterminal.is_none() {
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
                }
            }

            write!(
                buf,
                "Some({enum_name}::{variant} {{ {fields} }}) => {{",
                enum_name = frame_info.enum_name,
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
                    write!(buf, "stack.push({}::{} {{", frame_info.enum_name, next.frame_variant)
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

        let collection_type = rd_rule.collection_type.unwrap_or(CollectionKind::HashBag);
        let insert_method = match collection_type {
            CollectionKind::HashBag | CollectionKind::HashSet => "insert",
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
            "Some({enum_name}::CollectionElem_{label} {{ mut elements, saved_pos, saved_bp }}) => {{",
            enum_name = frame_info.enum_name,
            label = rd_rule.label,
        ).unwrap();

        write!(buf, "elements.{}(lhs);", insert_method).unwrap();

        if let Some(ref sep) = sep_info {
            let sep_variant = terminal_to_variant_name(sep);
            write!(
                buf,
                "if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                    *pos += 1; \
                    stack.push({enum_name}::CollectionElem_{label} {{ \
                        elements, saved_pos: *pos, saved_bp, \
                    }}); \
                    cur_bp = 0; \
                    continue 'drive; \
                }}",
                sep_variant,
                enum_name = frame_info.enum_name,
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
                "Some({enum_name}::Mixfix_{label}_{i} {{ {field_list} }}) => {{",
                enum_name = frame_info.enum_name,
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
                    "stack.push({enum_name}::Mixfix_{label}_{next_i} {{ lhs: orig_lhs,",
                    enum_name = frame_info.enum_name,
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
            "Some({enum_name}::LambdaBody_Single {{ binder_name, saved_bp }}) => {{ \
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
            enum_name = frame_info.enum_name,
        )
        .unwrap();

        write!(
            buf,
            "Some({enum_name}::LambdaBody_Multi {{ binder_names, saved_bp }}) => {{ \
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
            enum_name = frame_info.enum_name,
        )
        .unwrap();

        // Dollar syntax unwind handlers
        write_dollar_unwind_handlers(buf, config, frame_info);
    }

    // NOTE: Cast variants are NOT trampolined (cross-category, bounded depth).
    // No CastWrap_* unwind handlers needed.

    // No PhantomData variant — Frame is 'static (no lifetime parameter).

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
            "Some({enum_name}::DollarF_{dom_cap} {{ saved_bp }}) => {{ \
                let f = lhs; \
                expect_token(tokens, pos, |t| matches!(t, Token::Comma), \",\")?; \
                let x = parse_{dom}(tokens, pos, 0)?; \
                expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
                lhs = {cat}::{apply_variant}(Box::new(f), Box::new(x)); \
                cur_bp = saved_bp; \
            }},",
            enum_name = frame_info.enum_name,
        )
        .unwrap();

        // DdollarF: after parsing f, parse args
        write!(
            buf,
            "Some({enum_name}::DdollarF_{dom_cap} {{ saved_bp }}) => {{ \
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
            enum_name = frame_info.enum_name,
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

        let closing_terminal = rd_rule.items.iter().rev().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item {
                Some(t.clone())
            } else {
                None
            }
        });

        write!(
            buf,
            "Some({enum_name}::CollectionElem_{label} {{ elements, saved_pos, saved_bp }}) => {{ \
                *pos = saved_pos;",
            enum_name = frame_info.enum_name,
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

        let closing_terminal = rd_rule.items.iter().rev().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item {
                Some(t.clone())
            } else {
                None
            }
        });

        write!(
            buf,
            "Some({enum_name}::CollectionElem_{label} {{ elements, saved_pos, saved_bp }}) => {{ \
                *pos = saved_pos;",
            enum_name = frame_info.enum_name,
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
    let parse_fn = if config.needs_dispatch {
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

    let own_parse_fn = if config.needs_dispatch {
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
