//! Unified Trampoline — Cross-Category CPS with Defunctionalized Continuations
//!
//! Generates a single iterative driver loop that replaces mutual recursion
//! between per-category parsers. Cross-category calls become frame pushes
//! on a shared heap-allocated stack, achieving O(1) OS call stack depth.
//!
//! ## Architecture
//!
//! ```text
//! unified_parse_inner(tokens, pos, CategoryId, bp, stack)
//!   loop:
//!     match step:
//!       EnterPrefix { cat, bp }    → cat.prefix_step(tokens, pos, bp, stack)
//!       ContinueInfix { cat, lhs } → cat.infix_step(tokens, pos, lhs, bp, stack)
//!       Yield(result)              → pop frame, apply_continuation(frame, result)
//!       Error(e)                   → unwind to ErrorBarrier or propagate
//! ```
//!
//! Cross-category calls: push `CrossCatReturn { resume }` frame, return `EnterPrefix`.
//! NFA try-all: push `ErrorBarrier` frame, return `EnterPrefix`. On error, unwind to
//! barrier and try next source.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::automata::codegen::terminal_to_variant_name;
use crate::binding_power::BindingPowerTable;
use crate::dispatch::{CastRule, CrossCategoryRule, CrossCatPrefixArm};
use crate::prediction::FirstSet;
use crate::pratt::LedDelegationSource;
use crate::trampoline::TrampolineConfig;

// ═══════════════════════════════════════════════════════════════════════════
// Code generator data structures (NOT generated code — used by the generator)
// ═══════════════════════════════════════════════════════════════════════════

/// Information about one variant in a per-category Frame enum.
#[derive(Debug, Clone)]
pub struct FrameVariantInfo {
    /// Category that owns this frame (e.g., "Int").
    pub category: String,
    /// Variant name within the per-category enum (e.g., "InfixRHS").
    pub variant_name: String,
    /// Fields as `(name, type_str)` pairs (e.g., `[("lhs", "Int"), ("op_pos", "usize")]`).
    pub fields: Vec<(String, String)>,
}

impl FrameVariantInfo {
    /// Get the structural classification of this frame variant.
    #[inline]
    pub fn kind(&self) -> crate::trampoline::FrameVariantKind {
        crate::trampoline::FrameVariantKind::from_name(&self.variant_name)
    }
}

/// Information about a cross-category call site that needs a ResumePoint variant.
#[derive(Debug, Clone)]
pub struct ResumePointInfo {
    /// Variant name for the ResumePoint enum (e.g., "Int_FloatToInt_AwaitSource").
    pub variant_name: String,
    /// Category making the cross-category call (the "caller").
    pub caller_cat: String,
    /// Category being called (the "target").
    pub target_cat: String,
    /// Binding power for the cross-category parse.
    pub target_bp: u8,
    /// Fields captured in the frame (beyond saved_bp).
    pub captured_fields: Vec<(String, String)>,
    /// What kind of cross-category call this is.
    pub context: CrossCatContext,
}

/// The calling context of a cross-category call site.
#[derive(Debug, Clone)]
pub enum CrossCatContext {
    /// NFA cast rule: `int(expr)` → parse source, expect RParen, wrap in cast constructor.
    NfaCast {
        /// Label of the cast rule (e.g., "FloatToInt").
        label: String,
        /// Source category being parsed inside the cast call.
        source_cat: String,
    },
    /// Cross-cat dispatch LHS: parse source, peek for comparison operator.
    DispatchLhs {
        /// Source category being parsed.
        source_cat: String,
        /// Operators to check after LHS parse (e.g., ["EqEq", "BangEq", ...]).
        operators: Vec<(String, String)>, // (token_variant, rule_label)
    },
    /// Cross-cat dispatch RHS: source LHS already parsed, now parsing RHS.
    DispatchRhs {
        /// Source category of both LHS and RHS.
        source_cat: String,
        /// Operator that was matched.
        rule_label: String,
    },
    /// LED delegation: cross-cat infix operator RHS parse.
    LedDelegation {
        source_cat: String,
        /// The result category where the cross-cat node lives.
        result_cat: String,
        /// Constructor label for the cross-cat node (e.g., "EqNum").
        op_label: String,
        /// Cast label wrapping result_cat INTO the sum type (e.g., "PredToExpr").
        rewrap_label: String,
    },
    /// RD rule with cross-category nonterminal.
    RdNonTerminal {
        rule_label: String,
        segment_idx: usize,
        nt_category: String,
    },
    /// Deterministic implicit cast: parse source value, unconditionally wrap in cast.
    /// Used when a token is unique to a source category and there's a cast rule to target.
    ImplicitCast {
        source_cat: String,
        cast_label: String,
    },
    /// LED delegation: same-category infix operator RHS parse.
    /// After parsing, wraps the infix result back into the sum type.
    LedDelegationInfix {
        source_cat: String,
        /// Cast label wrapping source INTO the sum type (e.g., "NumToExpr").
        cast_label: String,
    },
}

// ═══════════════════════════════════════════════════════════════════════════
// Type generators — emit Rust enum definitions into a string buffer
// ═══════════════════════════════════════════════════════════════════════════

/// Generate the `CategoryId` enum with one variant per grammar category.
pub fn write_category_id_enum(buf: &mut String, categories: &[String]) {
    buf.push_str(
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)] enum CategoryId { ",
    );
    for cat in categories {
        write!(buf, "{cat}, ").unwrap();
    }
    buf.push_str("}\n");
}

/// Generate the `AnyTerm` enum that wraps any category's parsed result.
/// AST types are boxed to reduce the enum's in-memory size and keep
/// rustc stack usage during compilation manageable.
pub fn write_any_term_enum(buf: &mut String, categories: &[String]) {
    buf.push_str("#[derive(Debug)] enum AnyTerm { ");
    for cat in categories {
        write!(buf, "{cat}(Box<{cat}>), ").unwrap();
    }
    buf.push_str("}\n");

    // Generate into_Cat() methods (unboxes)
    buf.push_str("impl AnyTerm {\n");
    for cat in categories {
        write!(
            buf,
            "  #[inline(always)] fn into_{cat_lower}(self) -> {cat} {{ \
               match self {{ AnyTerm::{cat}(v) => *v, other => panic!(\"AnyTerm::into_{cat_lower} called on {{:?}}\", \
               std::mem::discriminant(&other)) }} }}\n",
            cat_lower = cat.to_lowercase(),
            cat = cat,
        )
        .unwrap();
    }
    buf.push_str("}\n");
}

/// Generate the `ParseStep` enum.
pub fn write_parse_step_enum(buf: &mut String) {
    buf.push_str(
        "enum ParseStep { \
         EnterPrefix { cat: CategoryId, bp: u8 }, \
         EnterSameCatPrefix { cat: CategoryId, bp: u8 }, \
         ContinueInfix { cat: CategoryId, lhs: AnyTerm, bp: u8 }, \
         Yield(AnyTerm), \
         Error(ParseError), \
         }\n",
    );
}

/// Generate the `UnifiedFrame` enum combining all per-category frames plus
/// cross-category return and error barrier frames.
pub fn write_unified_frame_enum(
    buf: &mut String,
    categories: &[String],
    per_cat_frames: &HashMap<String, Vec<FrameVariantInfo>>,
) {
    buf.push_str("#[derive(Debug)] #[allow(non_camel_case_types)] enum UnifiedFrame { ");

    // Per-category frame variants (prefixed by category name).
    // Large AST-typed fields are boxed to reduce enum size and
    // rustc type-checking pressure.
    for cat in categories {
        if let Some(frames) = per_cat_frames.get(cat) {
            for frame in frames {
                // Variant names are already prefixed with Cat_ by write_frame_enum
                // when unified_mode is true. Don't add another prefix.
                write!(buf, "{}", frame.variant_name).unwrap();
                if frame.fields.is_empty() {
                    buf.push_str(", ");
                } else {
                    buf.push_str(" { ");
                    for (name, ty) in &frame.fields {
                        // Use same types as per-category Frame_Cat enum (no boxing)
                        // so the _impl body code works unchanged.
                        write!(buf, "{name}: {ty}, ").unwrap();
                    }
                    buf.push_str("}, ");
                }
            }
        }
    }

    // Cross-category return frame
    buf.push_str(
        "CrossCatReturn { resume: ResumePoint, saved_bp: u8 }, ",
    );

    // Error barrier for NFA try-all backtracking
    buf.push_str(
        "ErrorBarrier { saved_pos: usize, saved_bp: u8, on_error: NfaFallback }, ",
    );

    buf.push_str("}\n");
}

/// Generate the `ResumePoint` enum with one variant per cross-category call site.
pub fn write_resume_point_enum(
    buf: &mut String,
    resume_points: &[ResumePointInfo],
) {
    buf.push_str("#[derive(Debug)] #[allow(non_camel_case_types)] enum ResumePoint { ");
    for rp in resume_points {
        write!(buf, "{}", rp.variant_name).unwrap();
        if rp.captured_fields.is_empty() {
            buf.push_str(", ");
        } else {
            buf.push_str(" { ");
            for (name, ty) in &rp.captured_fields {
                write!(buf, "{name}: {ty}, ").unwrap();
            }
            buf.push_str("}, ");
        }
    }
    buf.push_str("}\n");
}

/// Generate the `NfaFallback` enum for NFA try-all error barrier handling.
pub fn write_nfa_fallback_enum(buf: &mut String) {
    buf.push_str(
        "#[derive(Debug)] enum NfaFallback { \
         TryCastSource { target_cat: CategoryId, next_attempt: u8, saved_pos: usize, min_bp: u8 }, \
         TryDispatchSource { target_cat: CategoryId, next_attempt: u8, saved_pos: usize, min_bp: u8 }, \
         TryDispatchSourceWithBest { target_cat: CategoryId, next_attempt: u8, saved_pos: usize, min_bp: u8, best: Box<AnyTerm>, best_pos: usize }, \
         SameCatFallback { category: CategoryId, min_bp: u8 }, \
         CommitDispatchBest { category: CategoryId, min_bp: u8, best: Box<AnyTerm>, best_pos: usize }, \
         NfaCastExhausted { saved_pos: usize }, \
         TryCastSourceCollectAll { target_cat: CategoryId, next_attempt: u8, saved_pos: usize, min_bp: u8 }, \
         TryCastSourceCollectAllWithResults { target_cat: CategoryId, next_attempt: u8, saved_pos: usize, min_bp: u8, results: Vec<(AnyTerm, usize, f64)> }, \
         CommitCastBest { category: CategoryId, min_bp: u8, results: Vec<(AnyTerm, usize, f64)> }, \
         }\n",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Analysis — identify all cross-category call sites in the grammar
// ═══════════════════════════════════════════════════════════════════════════

/// Analyze cross-category rules, cast rules, and LED delegations to enumerate
/// all cross-category call sites that need ResumePoint variants.
pub fn analyze_cross_cat_call_sites(
    categories: &[String],
    cross_rules: &[CrossCategoryRule],
    cast_rules: &[CastRule],
    led_delegations: &HashMap<String, Vec<LedDelegationSource>>,
    _bp_table: &BindingPowerTable,
    rd_rules: &[crate::recursive::RDRuleInfo],
) -> Vec<ResumePointInfo> {
    let mut resume_points = Vec::new();
    let mut seen_variants: std::collections::HashSet<String> = std::collections::HashSet::new();

    // 1a. NFA cast rules (single-NT casts): int(expr), float(expr), etc.
    for rule in cast_rules {
        let target = &rule.target_category;
        let source = &rule.source_category;
        let variant = format!("{target}_CastFrom_{source}_Await");
        if seen_variants.insert(variant.clone()) {
            resume_points.push(ResumePointInfo {
                variant_name: variant,
                caller_cat: target.clone(),
                target_cat: source.clone(),
                target_bp: 0,
                captured_fields: vec![
                    ("saved_pos".into(), "usize".into()),
                ],
                context: CrossCatContext::NfaCast {
                    label: rule.label.clone(),
                    source_cat: source.clone(),
                },
            });
        }
    }

    // 1b. NFA RD rules with cross-category nonterminals:
    //     e.g., FloatToInt . a:Float |- "int" "(" a ")" : Int
    //     These are functionally identical to cast rules for the CPS architecture.
    {
        use crate::recursive::RDSyntaxItem;
        for rd in rd_rules {
            // Find cross-category NTs
            for (item_idx, item) in rd.items.iter().enumerate() {
                if let RDSyntaxItem::NonTerminal { category: nt_cat, .. } = item {
                    if *nt_cat != rd.category {
                        let target = &rd.category;
                        let source = nt_cat;

                        // Check if this is a keyword-triggered NFA cast pattern:
                        // Terminal(kw) + Terminal("(") + NonTerminal(source) + Terminal(")")
                        let is_nfa_cast_pattern = rd.items.len() >= 4
                            && matches!(&rd.items[0], RDSyntaxItem::Terminal(_))
                            && matches!(&rd.items[1], RDSyntaxItem::Terminal(t) if t == "(")
                            && item_idx == 2
                            && matches!(rd.items.last(), Some(RDSyntaxItem::Terminal(t)) if t == ")");

                        if is_nfa_cast_pattern {
                            // Only keyword-triggered cast patterns share the CastFrom resume point.
                            // This prevents non-keyword patterns (like Len's "|s|") from
                            // poisoning the shared variant with the wrong constructor label.
                            let variant = format!("{target}_CastFrom_{source}_Await");
                            if seen_variants.insert(variant.clone()) {
                                resume_points.push(ResumePointInfo {
                                    variant_name: variant,
                                    caller_cat: target.clone(),
                                    target_cat: source.clone(),
                                    target_bp: 0,
                                    captured_fields: vec![
                                        ("saved_pos".into(), "usize".into()),
                                    ],
                                    context: CrossCatContext::NfaCast {
                                        label: rd.label.clone(),
                                        source_cat: source.clone(),
                                    },
                                });
                            }
                        }

                        // Always generate a rule-specific resume point for non-keyword patterns
                        // (e.g., Len's |s| uses Int_RD_Len_AwaitNt with RdNonTerminal context)
                        let rd_variant = format!("{target}_RD_{}_AwaitNt", rd.label);
                        if seen_variants.insert(rd_variant.clone()) {
                            resume_points.push(ResumePointInfo {
                                variant_name: rd_variant,
                                caller_cat: target.clone(),
                                target_cat: source.clone(),
                                target_bp: 0,
                                captured_fields: vec![
                                    ("saved_pos".into(), "usize".into()),
                                ],
                                context: CrossCatContext::RdNonTerminal {
                                    rule_label: rd.label.clone(),
                                    segment_idx: 0,
                                    nt_category: source.clone(),
                                },
                            });
                        }
                    }
                }
            }
        }
    }

    // 2. Cross-category dispatch (comparison operators): parse LHS, check op, parse RHS
    //    Group by (result_category, source_category) to avoid duplicate resume points.
    let mut dispatch_groups: HashMap<(String, String), Vec<(String, String)>> = HashMap::new();
    for rule in cross_rules {
        let key = (rule.result_category.clone(), rule.source_category.clone());
        let op_variant = terminal_to_variant_name(&rule.operator);
        dispatch_groups
            .entry(key)
            .or_default()
            .push((op_variant, rule.label.clone()));
    }

    // Sort by key to guarantee deterministic output across builds.
    // HashMap iteration order is random; sorting ensures the generated enum
    // variants and match arms are in the same order every time.
    let mut dispatch_groups_sorted: Vec<_> = dispatch_groups.into_iter().collect();
    dispatch_groups_sorted.sort_by(|(a, _), (b, _)| a.cmp(b));
    for ((result_cat, source_cat), operators) in &dispatch_groups_sorted {
        // LHS parse resume point
        resume_points.push(ResumePointInfo {
            variant_name: format!("{result_cat}_Dispatch_{source_cat}_AwaitLhs"),
            caller_cat: result_cat.clone(),
            target_cat: source_cat.clone(),
            target_bp: 0,
            captured_fields: vec![
                ("saved_pos".into(), "usize".into()),
                ("allow_implicit_cast".into(), "bool".into()),
            ],
            context: CrossCatContext::DispatchLhs {
                source_cat: source_cat.clone(),
                operators: operators.clone(),
            },
        });

        // RHS parse resume points (one per operator)
        for (op_variant, rule_label) in operators {
            resume_points.push(ResumePointInfo {
                variant_name: format!("{result_cat}_Dispatch_{source_cat}_{rule_label}_AwaitRhs"),
                caller_cat: result_cat.clone(),
                target_cat: source_cat.clone(),
                target_bp: 0,
                captured_fields: vec![
                    ("lhs".into(), source_cat.clone()),
                    ("saved_pos".into(), "usize".into()),
                ],
                context: CrossCatContext::DispatchRhs {
                    source_cat: source_cat.clone(),
                    rule_label: rule_label.clone(),
                },
            });
        }
    }

    // 3. LED delegation: cross-category infix RHS parse
    // Sort by key so generated resume point order is deterministic across builds.
    let mut led_delegations_sorted: Vec<_> = led_delegations.iter().collect();
    led_delegations_sorted.sort_by_key(|(cat, _)| *cat);
    for (cat, sources) in led_delegations_sorted {
        for source in sources {
            // Cross-category operator LED delegation (e.g., == producing Pred from Num)
            for op in &source.cross_cat_ops {
                resume_points.push(ResumePointInfo {
                    variant_name: format!(
                        "{cat}_Led_{src}_{label}_AwaitRhs",
                        src = source.source_category,
                        label = op.label,
                    ),
                    caller_cat: cat.clone(),
                    target_cat: source.source_category.clone(),
                    target_bp: op.right_bp,
                    captured_fields: vec![
                        ("lhs".into(), source.source_category.clone()),
                        ("op_pos".into(), "usize".into()),
                    ],
                    context: CrossCatContext::LedDelegation {
                        source_cat: source.source_category.clone(),
                        result_cat: op.result_category.clone(),
                        op_label: op.label.clone(),
                        rewrap_label: op.rewrap_label.clone(),
                    },
                });
            }

            // Same-category infix LED delegation (e.g., + on Num delegated from Expr)
            if source.has_infix {
                resume_points.push(ResumePointInfo {
                    variant_name: format!(
                        "{cat}_Led_{src}_Infix_AwaitRhs",
                        src = source.source_category,
                    ),
                    caller_cat: cat.clone(),
                    target_cat: source.source_category.clone(),
                    target_bp: 0, // determined at runtime from infix_bp
                    captured_fields: vec![
                        ("lhs".into(), source.source_category.clone()),
                        ("op_pos".into(), "usize".into()),
                    ],
                    context: CrossCatContext::LedDelegationInfix {
                        source_cat: source.source_category.clone(),
                        cast_label: source.cast_label.clone(),
                    },
                });
            }
        }
    }

    resume_points
}

// ═══════════════════════════════════════════════════════════════════════════
// Unified driver loop generation
// ═══════════════════════════════════════════════════════════════════════════

/// Generate the unified frame pool thread-local.
pub fn write_unified_frame_pool(buf: &mut String) {
    buf.push_str(
        "thread_local! { \
         static UNIFIED_FRAME_POOL: std::cell::Cell<Vec<UnifiedFrame>> = \
         std::cell::Cell::new(Vec::new()); \
         }\n",
    );
}

/// Generate per-category entry points that delegate to the unified driver.
///
/// Generate the primary `parse_Cat` entry points that delegate to `unified_parse`.
/// These replace the per-category entry points that use mutual recursion.
pub fn write_entry_points(buf: &mut String, categories: &[String]) {
    for cat in categories {
        let cat_lower = cat.to_lowercase();
        write!(
            buf,
            "#[allow(dead_code)] \
            fn parse_{cat}<'a>(\
                tokens: &[(Token<'a>, Range)], \
                pos: &mut usize, \
                min_bp: u8, \
            ) -> Result<{cat}, ParseError> {{ \
                match unified_parse(tokens, pos, CategoryId::{cat}, min_bp) {{ \
                    Ok(AnyTerm::{cat}(v)) => Ok(*v), \
                    Ok(_) => unreachable!(\"unified_parse({cat}) returned wrong category\"), \
                    Err(e) => Err(e), \
                }} \
            }}\n",
        )
        .unwrap();
    }
}

/// Generate the `unified_parse` function (pool management wrapper).
pub fn write_unified_parse_wrapper(buf: &mut String) {
    buf.push_str(
        "#[allow(dead_code)] fn unified_parse<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            cat: CategoryId, \
            min_bp: u8, \
        ) -> Result<AnyTerm, ParseError> { \
            UNIFIED_FRAME_POOL.with(|pool| { \
                let mut stack = pool.take(); \
                stack.clear(); \
                let result = unified_parse_inner(tokens, pos, cat, min_bp, &mut stack); \
                stack.clear(); \
                pool.set(stack); \
                result \
            }) \
        }\n",
    );
}

/// Generate the `unified_parse_inner` driver loop.
pub fn write_unified_driver(buf: &mut String, categories: &[String]) {
    buf.push_str(
        "#[allow(dead_code)] fn unified_parse_inner<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            initial_cat: CategoryId, \
            initial_bp: u8, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> Result<AnyTerm, ParseError> { \
            let mut step = ParseStep::EnterPrefix { cat: initial_cat, bp: initial_bp }; \
            let mut __iter_count: u64 = 0; \
            'driver: loop { \
                __iter_count += 1; \
                if __iter_count > 500_000 { panic!(\"unified_parse_inner: infinite loop at iter {}\", __iter_count); } \
                step = match step { \
                    ParseStep::EnterPrefix { cat, bp } => match cat { ",
    );

    // Dispatch to per-category prefix step
    for cat in categories {
        write!(
            buf,
            "CategoryId::{cat} => prefix_step_{cat}(tokens, pos, bp, stack), ",
        )
        .unwrap();
    }

    buf.push_str("}, ParseStep::EnterSameCatPrefix { cat, bp } => match cat { ");

    // Dispatch to per-category same-cat prefix (skips cross-cat dispatch)
    for cat in categories {
        write!(
            buf,
            "CategoryId::{cat} => same_cat_prefix_step_{cat}(tokens, pos, bp, stack), ",
        )
        .unwrap();
    }

    buf.push_str("}, ParseStep::ContinueInfix { cat, lhs, bp } => match cat { ");

    // Dispatch to per-category infix step
    for cat in categories {
        let cat_lower = cat.to_lowercase();
        write!(
            buf,
            "CategoryId::{cat} => infix_step_{cat}(tokens, pos, lhs.into_{cat_lower}(), bp, stack), ",
        )
        .unwrap();
    }

    buf.push_str(
        "}, \
         ParseStep::Yield(result) => { \
            match stack.pop() { \
                None => return Ok(result), \
                Some(frame) => apply_continuation(frame, result, tokens, pos, stack), \
            } \
         }, \
         ParseStep::Error(e) => { \
            while let Some(frame) = stack.pop() { \
                if let UnifiedFrame::ErrorBarrier { saved_pos, saved_bp: _, on_error } = frame { \
                    *pos = saved_pos; \
                    step = handle_nfa_fallback(on_error, tokens, pos, stack); \
                    continue 'driver; \
                } \
            } \
            return Err(e); \
         }, \
         }; \
         } \
         }\n",
    );
}

/// Generate the `handle_nfa_fallback` function that dispatches to the next
/// NFA try-all alternative after an error barrier catches a parse failure.
pub fn write_nfa_fallback_handler(buf: &mut String) {
    buf.push_str(
        "#[allow(dead_code)] fn handle_nfa_fallback<'a>(\
            fallback: NfaFallback, \
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep { \
            match fallback { \
                NfaFallback::TryCastSource { target_cat, next_attempt, saved_pos, min_bp } => { \
                    push_nfa_attempt(target_cat, next_attempt, saved_pos, min_bp, pos, stack) \
                } \
                NfaFallback::TryDispatchSource { target_cat, next_attempt, saved_pos, min_bp } => { \
                    push_dispatch_attempt(target_cat, next_attempt, saved_pos, min_bp, stack) \
                } \
                NfaFallback::TryDispatchSourceWithBest { target_cat, next_attempt, saved_pos, min_bp, best, best_pos } => { \
                    push_dispatch_attempt_with_best(target_cat, next_attempt, saved_pos, min_bp, best, best_pos, pos, stack) \
                } \
                NfaFallback::SameCatFallback { category, min_bp } => { \
                    ParseStep::EnterSameCatPrefix { cat: category, bp: min_bp } \
                } \
                NfaFallback::CommitDispatchBest { category, min_bp, best, best_pos } => { \
                    *pos = best_pos; \
                    ParseStep::ContinueInfix { cat: category, lhs: *best, bp: min_bp } \
                } \
                NfaFallback::NfaCastExhausted { saved_pos } => { \
                    let range = if saved_pos < tokens.len() { tokens[saved_pos].1 } \
                                else { tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()) }; \
                    ParseStep::Error(ParseError::UnexpectedToken { \
                        expected: std::borrow::Cow::Borrowed(\"valid expression inside cast\"), \
                        found: if saved_pos < tokens.len() { format_token_friendly(&tokens[saved_pos].0) } \
                               else { \"EOF\".to_string() }, \
                        range, hint: None }) \
                } \
                NfaFallback::TryCastSourceCollectAll { target_cat, next_attempt, saved_pos, min_bp } => { \
                    /* Error: this attempt failed, no results yet */ \
                    push_nfa_attempt_collect_all(target_cat, next_attempt, saved_pos, min_bp, Vec::new(), pos, stack) \
                } \
                NfaFallback::TryCastSourceCollectAllWithResults { target_cat, next_attempt, saved_pos, min_bp, results } => { \
                    /* Error: this attempt failed, but we have prior results */ \
                    push_nfa_attempt_collect_all(target_cat, next_attempt, saved_pos, min_bp, results, pos, stack) \
                } \
                NfaFallback::CommitCastBest { category, min_bp, results } => { \
                    /* Last attempt error: commit best from collected results */ \
                    if results.is_empty() { \
                        let range = if *pos < tokens.len() { tokens[*pos].1 } \
                                    else { tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()) }; \
                        ParseStep::Error(ParseError::UnexpectedToken { \
                            expected: std::borrow::Cow::Borrowed(\"valid expression inside cast\"), \
                            found: if *pos < tokens.len() { format_token_friendly(&tokens[*pos].0) } \
                                   else { \"EOF\".to_string() }, \
                            range, hint: None }) \
                    } else { \
                        commit_nfa_cast_results(category, min_bp, results, pos) \
                    } \
                } \
            } \
        }\n",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Top-level orchestration
// ═══════════════════════════════════════════════════════════════════════════

/// Configuration for generating the unified trampoline for one grammar.
pub struct UnifiedTrampolineConfig {
    pub categories: Vec<String>,
    pub cross_rules: Vec<CrossCategoryRule>,
    pub cast_rules: Vec<CastRule>,
    pub led_delegations: HashMap<String, Vec<LedDelegationSource>>,
    pub per_cat_frames: HashMap<String, Vec<FrameVariantInfo>>,
    pub per_cat_tramp_configs: HashMap<String, TrampolineConfig>,
    pub bp_table: BindingPowerTable,
    /// Unary prefix operators per category: (category, token_variant, label, right_bp)
    pub unary_prefix_ops: Vec<(String, String, String, u8)>,
    /// RD rules for all categories (needed for NFA-grouped keyword dispatch)
    pub rd_rules: Vec<crate::recursive::RDRuleInfo>,
}

/// Generate all unified trampoline types for a grammar.
/// Called from pipeline.rs after per-category code generation.
pub fn write_unified_types(
    buf: &mut String,
    config: &UnifiedTrampolineConfig,
) {
    let categories = &config.categories;

    // The unified trampoline is generated into a SEPARATE FILE to avoid
    // overwhelming rustc's stack. The per-category code is ~130KB; adding
    // 35KB more in the same compilation unit causes rustc to overflow its
    // default 8MB stack during type-checking. A separate file gives rustc
    // an independent compilation scope.
    //
    // The file is written to `src/generated/{grammar}-unified.rs` and
    // included via a `mod` declaration that the caller emits.
    let mut unified_buf = String::with_capacity(40_000);
    unified_buf.push_str(
        "// Auto-generated unified trampoline — included via include!() \n",
    );

    // Enums
    write_category_id_enum(&mut unified_buf, categories);
    write_any_term_enum(&mut unified_buf, categories);
    write_parse_step_enum(&mut unified_buf);
    write_nfa_fallback_enum(&mut unified_buf);

    // Analyze cross-cat call sites for ResumePoint
    let resume_points = analyze_cross_cat_call_sites(
        categories,
        &config.cross_rules,
        &config.cast_rules,
        &config.led_delegations,
        &config.bp_table,
        &config.rd_rules,
    );

    write_resume_point_enum(&mut unified_buf, &resume_points);
    write_unified_frame_enum(&mut unified_buf, categories, &config.per_cat_frames);

    // Driver infrastructure
    write_unified_frame_pool(&mut unified_buf);
    write_unified_parse_wrapper(&mut unified_buf);
    write_unified_driver(&mut unified_buf, categories);
    write_nfa_fallback_handler(&mut unified_buf);

    // Per-category CPS step functions: prefix_step_Cat, infix_step_Cat, same_cat_prefix_step_Cat.
    // These are single-step functions that return ParseStep. ALL cross-category calls use
    // frame pushes + EnterPrefix returns — NO recursion, NO stack overflow.
    {
        let cat_configs_available = !config.per_cat_tramp_configs.is_empty();
        if cat_configs_available {
            for cat in categories {
                let cat_cast: Vec<CastRule> = config.cast_rules.iter()
                    .filter(|r| r.target_category == *cat)
                    .cloned()
                    .collect();
                let cat_cross: Vec<CrossCategoryRule> = config.cross_rules.iter()
                    .filter(|r| r.result_category == *cat)
                    .cloned()
                    .collect();
                let cat_prefix_ops: Vec<(String, String, String, u8)> = config.unary_prefix_ops.iter()
                    .filter(|(c, _, _, _)| c == cat)
                    .cloned()
                    .collect();
                let cat_rd: Vec<crate::recursive::RDRuleInfo> = config.rd_rules.iter()
                    .filter(|r| r.category == *cat)
                    .cloned()
                    .collect();
                if let Some(tc) = config.per_cat_tramp_configs.get(cat) {
                    write_prefix_step(&mut unified_buf, cat, tc, &cat_cast, &cat_cross, &config.bp_table, &resume_points, &cat_prefix_ops, &cat_rd);
                    write_infix_step(&mut unified_buf, cat, tc, &config.bp_table, &config.led_delegations);
                }
            }
        }
    }

    // apply_continuation handles per-category frames (InfixRHS, GroupClose, etc.)
    // and cross-category frames (CrossCatReturn, ErrorBarrier).
    write_apply_continuation(&mut unified_buf, categories, &config.per_cat_frames, &config.cast_rules, &config.cross_rules, &config.led_delegations, &config.bp_table, &resume_points, &config.rd_rules);

    // Per-category entry points (replace parse_Cat wrapper)
    write_entry_points(&mut unified_buf, categories);

    // NFA cast attempt dispatcher
    write_nfa_attempt_dispatcher(&mut unified_buf, categories, &config.cast_rules, &config.rd_rules);

    // Cross-cat dispatch attempt dispatcher (comparison operators)
    write_dispatch_attempt_dispatcher(&mut unified_buf, categories, &config.cross_rules);

    // NFA spillover collect-all functions (for semantic disambiguation of variable-bearing terms)
    write_nfa_collect_all_functions(&mut unified_buf, categories, &config.rd_rules);

    // Write unified trampoline to a separate file — only if content changed.
    // Unconditional writes update the file mtime on every build, making cargo
    // believe the source is stale and triggering a full recompile of
    // `mettail-languages` even when nothing has changed.
    let grammar_name = categories.join("_");
    let file_name = format!("{}-unified.rs", grammar_name.to_lowercase());
    // Use the CARGO_MANIFEST_DIR of the languages crate to find the generated directory
    if let Ok(manifest_dir) = std::env::var("CARGO_MANIFEST_DIR") {
        let gen_dir = std::path::Path::new(&manifest_dir).join("src/generated");
        let file_path = gen_dir.join(&file_name);
        // Skip the write when the on-disk content already matches.
        let already_current = std::fs::read_to_string(&file_path)
            .map(|existing| existing == unified_buf)
            .unwrap_or(false);
        if !already_current {
            if let Ok(()) = std::fs::write(&file_path, &unified_buf) {
                eprintln!("  Generated unified trampoline: {}", file_path.display());
            }
        }
    }

    // Instead of putting all unified code in the main token stream (which
    // overwhelms rustc's 8MB stack), we write it to a separate file and
    // include it. The include! happens at a separate parse point, giving
    // rustc a fresh stack frame for type-checking.
    write!(
        buf,
        "\ninclude!(concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/src/generated/{file_name}\"));\n",
    ).unwrap();
}

// ═══════════════════════════════════════════════════════════════════════════
// Per-category step function generation
// ═══════════════════════════════════════════════════════════════════════════

/// Generate `prefix_step_Cat` for one category.
///
/// The prefix step handles token dispatch (literals, identifiers, unary operators,
/// grouping, cast rules, cross-category dispatch) and returns `ParseStep`.
fn write_prefix_step(
    buf: &mut String,
    cat: &str,
    config: &TrampolineConfig,
    cast_rules: &[CastRule],
    cross_rules: &[CrossCategoryRule],
    bp_table: &BindingPowerTable,
    resume_points: &[ResumePointInfo],
    unary_prefix_ops: &[(String, String, String, u8)],
    rd_rules: &[crate::recursive::RDRuleInfo],
) {
    let cat_lower = cat.to_lowercase();

    write!(
        buf,
        "#[allow(dead_code)] fn prefix_step_{cat}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            bp: u8, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep {{ ",
    ).unwrap();

    // Forced-prefix check: if NFA_FORCED_PREFIX is set (by parse_preserving_vars
    // during spillover replay), use it instead of parsing.
    if config.needs_nfa_spillover {
        let cat_upper = cat.to_uppercase();
        write!(
            buf,
            "{{ let forced = NFA_FORCED_PREFIX_{cat_upper}.with(|cell| cell.take()); \
               if let Some((forced_val, forced_pos, _forced_weight)) = forced {{ \
                   *pos = forced_pos; \
                   return ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                       lhs: AnyTerm::{cat}(Box::new(forced_val)), bp }}; \
               }} }} ",
        ).unwrap();
    }

    // EOF check
    write!(
        buf,
        "if *pos >= tokens.len() {{ \
            let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
            return ParseStep::Error(ParseError::UnexpectedEof {{ \
                expected: std::borrow::Cow::Borrowed(\"{cat} expression\"), \
                range: eof_range, hint: None }}); \
        }} ",
    ).unwrap();

    // Cross-category dispatch: for categories that are the RESULT of cross-cat
    // comparison rules (e.g., Bool from EqInt, GtFloat, etc.), try each source
    // category sequentially using error barriers.
    let has_cross_cat = cross_rules.iter().any(|r| r.result_category == cat);
    if has_cross_cat {
        write_cross_cat_prefix_dispatch_unified(buf, cat, config, cross_rules, resume_points);
    }

    // Token dispatch match
    buf.push_str("match &tokens[*pos].0 { ");

    // Generate match arms for each token (including NFA keyword dispatch)
    write_prefix_arms_unified(buf, cat, config, cast_rules, bp_table, resume_points, unary_prefix_ops, rd_rules, false);

    // Catch-all error arm
    write!(
        buf,
        "other => {{ \
            let found_str = format_token_friendly(other); \
            return ParseStep::Error(ParseError::UnexpectedToken {{ \
                expected: std::borrow::Cow::Borrowed(\"{cat} expression\"), \
                found: found_str, range: tokens[*pos].1, hint: None }}); \
        }} ",
    ).unwrap();

    buf.push_str("} }"); // close match and fn
    buf.push('\n');

    // Also generate same_cat_prefix_step (without cross-cat dispatch)
    // Called when SameCatFallback fires after cross-cat dispatch exhaustion.
    write!(
        buf,
        "#[allow(dead_code)] fn same_cat_prefix_step_{cat}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            bp: u8, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep {{ ",
    ).unwrap();

    // Forced-prefix check (same as prefix_step)
    if config.needs_nfa_spillover {
        let cat_upper = cat.to_uppercase();
        write!(
            buf,
            "{{ let forced = NFA_FORCED_PREFIX_{cat_upper}.with(|cell| cell.take()); \
               if let Some((forced_val, forced_pos, _forced_weight)) = forced {{ \
                   *pos = forced_pos; \
                   return ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                       lhs: AnyTerm::{cat}(Box::new(forced_val)), bp }}; \
               }} }} ",
        ).unwrap();
    }

    // EOF check (same as prefix_step)
    write!(
        buf,
        "if *pos >= tokens.len() {{ \
            let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
            return ParseStep::Error(ParseError::UnexpectedEof {{ \
                expected: std::borrow::Cow::Borrowed(\"{cat} expression\"), \
                range: eof_range, hint: None }}); \
        }} ",
    ).unwrap();

    // NO cross-cat dispatch AND NO NFA keyword arms — those are handled by prefix_step.
    // SameCatFallback enters here after all NFA alternatives failed.
    buf.push_str("match &tokens[*pos].0 { ");
    write_prefix_arms_unified(buf, cat, config, cast_rules, bp_table, resume_points, unary_prefix_ops, rd_rules, true);

    write!(
        buf,
        "other => {{ \
            let found_str = format_token_friendly(other); \
            return ParseStep::Error(ParseError::UnexpectedToken {{ \
                expected: std::borrow::Cow::Borrowed(\"{cat} expression\"), \
                found: found_str, range: tokens[*pos].1, hint: None }}); \
        }} ",
    ).unwrap();

    buf.push_str("} }"); // close match and fn
    buf.push('\n');
}

/// Generate prefix match arms for the unified trampoline.
///
/// Handles: literals, identifiers, unary prefix, grouping, NFA try-all cast rules.
fn write_prefix_arms_unified(
    buf: &mut String,
    cat: &str,
    config: &TrampolineConfig,
    cast_rules: &[CastRule],
    bp_table: &BindingPowerTable,
    resume_points: &[ResumePointInfo],
    unary_prefix_ops: &[(String, String, String, u8)],
    rd_rules: &[crate::recursive::RDRuleInfo],
    skip_nfa_keyword_arms: bool,
) {
    let cat_lower = cat.to_lowercase();

    // NFA-grouped RD rules dispatched by keyword token (e.g., Token::KwInt for
    // NFA-grouped RD rules dispatched by keyword token (e.g., Token::KwInt for
    // NFA-grouped RD rules dispatched by keyword token (e.g., Token::KwInt for
    // int(FloatToInt/BoolToInt/StrToInt/IntId)).
    // In same_cat_prefix_step (skip_nfa_keyword_arms=true), only emit the
    // same-category alternative (e.g., IntId) to avoid infinite SameCatFallback loop.
    {
        use crate::recursive::RDSyntaxItem;

        // Find RD rules with syntax: keyword "(" NT ")" pattern
        let mut nfa_groups: std::collections::HashMap<String, Vec<(String, String, bool)>> =
            std::collections::HashMap::new();

        for rd in rd_rules {
            if rd.category != cat { continue; }
            if rd.items.len() < 3 { continue; }
            // Match: Terminal(kw) + Terminal("(") + NonTerminal(nt) + Terminal(")")
            let kw = match &rd.items[0] {
                RDSyntaxItem::Terminal(t) => t.clone(),
                _ => continue,
            };
            if !matches!(&rd.items[1], RDSyntaxItem::Terminal(t) if t == "(") { continue; }
            let nt_cat = match &rd.items[2] {
                RDSyntaxItem::NonTerminal { category: c, .. } => c.clone(),
                _ => continue,
            };
            let is_same = nt_cat == cat;
            nfa_groups.entry(kw.clone())
                .or_default()
                .push((rd.label.clone(), nt_cat, is_same));
        }

        // Also include single-NT cast rules
        for cast in cast_rules {
            if cast.target_category != cat { continue; }
            let kw = cat.to_lowercase();
            let is_same = cast.source_category == cat;
            nfa_groups.entry(kw)
                .or_default()
                .push((cast.label.clone(), cast.source_category.clone(), is_same));
        }

        // Sort by keyword so generated match arms are in the same order every build.
        let mut nfa_groups_sorted: Vec<_> = nfa_groups.into_iter().collect();
        nfa_groups_sorted.sort_by(|(a, _), (b, _)| a.cmp(b));
        for (kw, mut alternatives) in nfa_groups_sorted {
            // Sort: cross-category first, same-category fallback last
            alternatives.sort_by_key(|(_, _, is_same)| if *is_same { 1u8 } else { 0u8 });

            let kw_token = crate::automata::codegen::terminal_to_variant_name(&kw);

            // Note: skip_nfa_keyword_arms is NOT used to skip the NFA arms.
            // The same_cat_prefix_step needs the full NFA dispatch (including
            // cross-category alternatives). The push_nfa_attempt function's
            // last-attempt fallback uses SameCatFallback which would infinite-loop,
            // BUT: same_cat_prefix_step is only entered from SameCatFallback
            // fired by the CROSS-CAT DISPATCH (comparison operators), not by
            // the NFA. The NFA's own SameCatFallback enters same_cat_prefix_step
            // which tries the NFA again — but this time IntToBool/FloatToBool/StrToInt
            // may succeed (they parse the inner expression, not a comparison).
            // If they all fail, SameCatFallback fires AGAIN — but this is bounded:
            // the NFA alternatives won't succeed on the second attempt either, so
            // the iteration limit (500K) would catch it. To prevent this, we could
            // add a "no-repeat" flag, but the practical impact is negligible since
            // the alternatives genuinely can't succeed for unparseable input.
            //
            // For now: emit the full NFA arm regardless of skip_nfa_keyword_arms.

            write!(buf, "Token::{kw_token} => {{ ").unwrap();

            write!(
                buf,
                "let nfa_saved = *pos; \
                 *pos += 1; \
                 if *pos >= tokens.len() || !matches!(&tokens[*pos].0, Token::LParen) {{ \
                     return ParseStep::Error(ParseError::UnexpectedToken {{ \
                         expected: std::borrow::Cow::Borrowed(\"(\"), \
                         found: if *pos < tokens.len() {{ format_token_friendly(&tokens[*pos].0) }} \
                                else {{ \"EOF\".to_string() }}, \
                         range: if *pos < tokens.len() {{ tokens[*pos].1 }} \
                                else {{ tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()) }}, \
                         hint: None }}); \
                 }} \
                 *pos += 1; /* consume LParen */ ",
            ).unwrap();

            // Push frames for first NFA attempt (attempt 0)
            if alternatives.len() > 1 {
                // Use collect-all pattern when NFA spillover is needed (semantic disambiguation)
                let fallback_variant = if config.needs_nfa_spillover {
                    "TryCastSourceCollectAll"
                } else {
                    "TryCastSource"
                };
                write!(
                    buf,
                    "stack.push(UnifiedFrame::ErrorBarrier {{ \
                        saved_pos: nfa_saved, saved_bp: bp, \
                        on_error: NfaFallback::{fallback_variant} {{ \
                            target_cat: CategoryId::{cat}, \
                            next_attempt: 1, \
                            saved_pos: nfa_saved, \
                            min_bp: bp, \
                        }}, \
                    }}); ",
                ).unwrap();
            }

            let (first_label, first_nt_cat, first_is_same) = &alternatives[0];
            if *first_is_same {
                // Same-category: use existing RD frame
                let vp = format!("{cat}_");
                write!(
                    buf,
                    "stack.push(UnifiedFrame::{vp}RD_{first_label}_0 {{ saved_bp: bp }}); \
                     return ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: 0 }}; ",
                ).unwrap();
            } else {
                // Cross-category: use CrossCatReturn
                let resume_variant = format!("{cat}_CastFrom_{first_nt_cat}_Await");
                write!(
                    buf,
                    "stack.push(UnifiedFrame::CrossCatReturn {{ \
                        resume: ResumePoint::{resume_variant} {{ saved_pos: nfa_saved }}, \
                        saved_bp: bp, \
                    }}); \
                    return ParseStep::EnterPrefix {{ cat: CategoryId::{first_nt_cat}, bp: 0 }}; ",
                ).unwrap();
            }

            buf.push_str("}, "); // close KwCat arm
        }
    } // end NFA keyword dispatch block

    // Unary prefix operators: push frame and enter prefix at right_bp
    for (op_cat, token_variant, label, right_bp) in unary_prefix_ops {
        if op_cat != cat { continue; }
        write!(
            buf,
            "Token::{token_variant} => {{ \
                *pos += 1; \
                stack.push(UnifiedFrame::{cat}_UnaryPrefix_{label} {{ saved_bp: bp }}); \
                return ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: {right_bp} }}; \
            }}, ",
        ).unwrap();
    }

    // Native literal — dispatch on the native type string to generate the
    // appropriate token match arm. The string is from the grammar definition;
    // it's matched once here at codegen time, not at parse time.
    if let Some(ref native) = config.native_type {
        match native.as_str() {
            "i32" => {
                write!(
                    buf,
                    "Token::Integer(v) => {{ let val = *v as i32; *pos += 1; \
                     return ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                     lhs: AnyTerm::{cat}(Box::new({cat}::NumLit(val))), bp }}; }}, ",
                ).unwrap();
            }
            "f64" => {
                write!(
                    buf,
                    "Token::Float(v) => {{ let val = (*v).into(); *pos += 1; \
                     return ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                     lhs: AnyTerm::{cat}(Box::new({cat}::FloatLit(val))), bp }}; }}, ",
                ).unwrap();
            }
            "bool" => {
                write!(
                    buf,
                    "Token::Boolean(v) => {{ let val = *v; *pos += 1; \
                     return ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                     lhs: AnyTerm::{cat}(Box::new({cat}::BoolLit(val))), bp }}; }}, ",
                ).unwrap();
            }
            "String" | "str" => {
                write!(
                    buf,
                    "Token::StringLit(v) => {{ let val = (*v).to_string(); *pos += 1; \
                     return ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                     lhs: AnyTerm::{cat}(Box::new({cat}::StringLit(val))), bp }}; }}, ",
                ).unwrap();
            }
            _ => {}
        }
    }

    // LParen grouping
    write!(
        buf,
        "Token::LParen => {{ \
            *pos += 1; \
            stack.push(UnifiedFrame::{cat}_GroupClose {{ saved_bp: bp }}); \
            return ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: 0 }}; \
        }}, ",
    ).unwrap();

    // Identifier
    write!(
        buf,
        "Token::Ident(name) => {{ \
            let var_name = (*name).to_string(); \
            *pos += 1; \
            return ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
            lhs: AnyTerm::{cat}(Box::new({cat}::{cat_var}(mettail_runtime::OrdVar(\
            mettail_runtime::Var::Free(mettail_runtime::get_or_create_var(var_name)))))), \
            bp }}; \
        }}, ",
        cat_var = get_var_constructor(cat),
    ).unwrap();

    // RD function rules (sin, cos, exp, ln, etc.) are handled by the NFA keyword
    // dispatch block above — no separate generation needed. The NFA block handles
    // ALL kw "(" NT ")" patterns for both same-category and cross-category NTs.

    // Pipe-delimited RD rules (e.g., Len: |str_expr| for Int)
    {
        use crate::recursive::RDSyntaxItem;
        for rd in rd_rules {
            if rd.category != cat { continue; }
            if rd.items.len() < 3 { continue; }
            // Match pattern: Terminal("|") + NonTerminal(nt) + Terminal("|")
            let is_pipe_delimited = matches!(
                (&rd.items[0], &rd.items[rd.items.len() - 1]),
                (RDSyntaxItem::Terminal(open), RDSyntaxItem::Terminal(close))
                    if open == "|" && close == "|"
            );
            if !is_pipe_delimited { continue; }
            if let Some(RDSyntaxItem::NonTerminal { category: nt_cat, .. }) = rd.items.get(1) {
                let label = &rd.label;
                let vp = config.frame_prefix();
                if nt_cat == cat {
                    // Same-category NT
                    write!(
                        buf,
                        "Token::Pipe => {{ \
                            *pos += 1; \
                            stack.push(UnifiedFrame::{vp}RD_{label}_0 {{ saved_bp: bp }}); \
                            return ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: 0 }}; \
                        }}, ",
                    ).unwrap();
                } else {
                    // Cross-category NT: use CrossCatReturn
                    let resume_variant = format!("{cat}_CastFrom_{nt_cat}_Await");
                    // For Len, the resume handler expects the closing |
                    // We reuse the NfaCast resume point pattern: after the NT yields,
                    // the resume checks for the closing terminal.
                    // Actually, the Len rule needs its OWN resume point because
                    // the closing terminal is | not ).
                    // For now, use a generic RD resume approach:
                    write!(
                        buf,
                        "Token::Pipe => {{ \
                            *pos += 1; \
                            stack.push(UnifiedFrame::CrossCatReturn {{ \
                                resume: ResumePoint::{cat}_RD_{label}_AwaitNt {{ saved_pos: *pos }}, \
                                saved_bp: bp, \
                            }}); \
                            return ParseStep::EnterPrefix {{ cat: CategoryId::{nt_cat}, bp: 0 }}; \
                        }}, ",
                    ).unwrap();
                }
            }
        }
    }

    // Deterministic cross-category dispatch arms for tokens unique to source categories.
    // When a token is in source_cat's FIRST set but NOT in this category's FIRST set,
    // enter the source category via CPS frame push. On yield, the resume handler
    // checks for comparison operators or falls back to implicit cast.
    {
        let cross_rules_for_cat: Vec<&CrossCategoryRule> = config.all_first_sets.keys()
            .filter(|_| true) // iterate all categories
            .flat_map(|_| std::iter::empty::<&CrossCategoryRule>()) // placeholder
            .collect();

        // Get the cross-cat rules where this category is the result
        let my_cross_rules: Vec<&crate::dispatch::CrossCategoryRule> = cast_rules.iter()
            .filter(|_| false) // cast_rules is usually empty; cross_rules passed separately
            .map(|_| unreachable!())
            .collect::<Vec<&crate::dispatch::CrossCategoryRule>>();

        // Get source categories from the cross-cat comparison rules
        // and from RD cast rules (for implicit cast)
        let own_first = &config.own_first_set;
        let mut handled_tokens: std::collections::HashSet<String> = std::collections::HashSet::new();

        // Collect tokens already handled by earlier arms
        // (native literals, ident, lparen, unary prefix, NFA keywords, pipe)
        if let Some(ref nt) = config.native_type {
            match nt.as_str() {
                "i32" | "i64" => { handled_tokens.insert("Integer".into()); },
                "f64" | "f32" => { handled_tokens.insert("Float".into()); },
                "bool" => { handled_tokens.insert("Boolean".into()); },
                "String" | "str" => { handled_tokens.insert("StringLit".into()); },
                _ => {},
            }
        }
        handled_tokens.insert("LParen".into());
        handled_tokens.insert("Ident".into());
        for (oc, tv, _, _) in unary_prefix_ops {
            if oc == cat { handled_tokens.insert(tv.clone()); }
        }
        // NFA keyword tokens
        for rd in rd_rules {
            if rd.category != cat { continue; }
            if let Some(crate::recursive::RDSyntaxItem::Terminal(t)) = rd.items.first() {
                let tv = crate::automata::codegen::terminal_to_variant_name(t);
                handled_tokens.insert(tv);
            }
        }
        // Pipe
        handled_tokens.insert("Pipe".into());

        // For each source category with comparison rules targeting this category.
        // Sort by source_cat name so generated match arms are in the same order every build.
        let mut all_first_sorted: Vec<_> = config.all_first_sets.iter().collect();
        all_first_sorted.sort_by_key(|(cat, _)| *cat);
        for (source_cat, source_first) in all_first_sorted {
            if source_cat == cat { continue; }

            // Check if this source has either comparison rules or cast rules to this category
            let has_dispatch = resume_points.iter().any(|rp| {
                rp.caller_cat == cat && rp.target_cat == *source_cat
                    && matches!(&rp.context, CrossCatContext::DispatchLhs { .. })
            });
            let has_implicit_cast = rd_rules.iter().any(|rd| {
                rd.category == cat
                    && rd.items.iter().any(|item| matches!(item,
                        crate::recursive::RDSyntaxItem::NonTerminal { category: c, .. } if c == source_cat))
            });

            if !has_dispatch && !has_implicit_cast { continue; }

            let unique_tokens = source_first.difference(own_first);
            // Sort token names so match arms are in the same order every build.
            // unique_tokens.tokens is a HashSet and iterates non-deterministically.
            let mut sorted_unique_tokens: Vec<&String> = unique_tokens.tokens.iter().collect();
            sorted_unique_tokens.sort();
            for token in sorted_unique_tokens {
                let tv = crate::automata::codegen::terminal_to_variant_name(token);
                if handled_tokens.contains(&tv) { continue; }
                handled_tokens.insert(tv.clone());

                let mut pattern = String::new();
                crate::dispatch::write_token_pattern(&mut pattern, token);

                if has_dispatch {
                    // Use DispatchLhs resume (handles both comparison and implicit cast)
                    let resume_variant = format!("{cat}_Dispatch_{source_cat}_AwaitLhs");
                    write!(
                        buf,
                        "{pattern} => {{ \
                            stack.push(UnifiedFrame::ErrorBarrier {{ \
                                saved_pos: *pos, saved_bp: bp, \
                                on_error: NfaFallback::NfaCastExhausted {{ saved_pos: *pos }}, \
                            }}); \
                            stack.push(UnifiedFrame::CrossCatReturn {{ \
                                resume: ResumePoint::{resume_variant} {{ saved_pos: *pos, allow_implicit_cast: true }}, \
                                saved_bp: bp, \
                            }}); \
                            return ParseStep::EnterPrefix {{ cat: CategoryId::{source_cat}, bp: 0 }}; \
                        }}, ",
                    ).unwrap();
                }
                // If only has_implicit_cast (no dispatch), we'd need ImplicitCast resume
                // For now, skip — the comparison dispatch handles the common case
            }
        }
    }
}

/// Generate cross-category prefix dispatch for unified mode (replaces cold function).
fn write_cross_cat_prefix_dispatch_unified(
    buf: &mut String,
    cat: &str,
    config: &TrampolineConfig,
    cross_rules: &[CrossCategoryRule],
    resume_points: &[ResumePointInfo],
) {
    // For categories with cross-cat comparison operators (like Bool),
    // try each source category sequentially using error barriers.
    // The cross_cat_prefix_arms from the PDA merge contain the analysis.

    // Group cross-cat rules by source category
    let my_rules: Vec<&CrossCategoryRule> = cross_rules.iter()
        .filter(|r| r.result_category == cat)
        .collect();

    if my_rules.is_empty() {
        return;
    }

    let mut source_cats: Vec<String> = Vec::new();
    for rule in &my_rules {
        if !source_cats.contains(&rule.source_category) {
            source_cats.push(rule.source_category.clone());
        }
    }

    // Guard: skip cross-cat dispatch when the current token is the category's
    // own keyword (e.g., KwBool for Bool). The keyword triggers the NFA cast
    // dispatch in the match arms below, not comparison operators.
    let cat_kw_token = crate::automata::codegen::terminal_to_variant_name(&cat.to_lowercase());
    write!(
        buf,
        "if !matches!(&tokens[*pos].0, Token::{cat_kw_token}) {{ ",
    ).unwrap();

    write!(
        buf,
        "/* cross-cat dispatch: try {n_sources} source categories */ \
         {{ let __cc_saved = *pos; ",
        n_sources = source_cats.len(),
    ).unwrap();

    // Push ErrorBarrier for backtracking to same-category parse
    write!(
        buf,
        "stack.push(UnifiedFrame::ErrorBarrier {{ \
            saved_pos: __cc_saved, saved_bp: bp, \
            on_error: NfaFallback::SameCatFallback {{ \
                category: CategoryId::{cat}, min_bp: bp }}, \
        }}); ",
    ).unwrap();

    // Push ErrorBarrier for trying next source (if multiple sources)
    if source_cats.len() > 1 {
        write!(
            buf,
            "stack.push(UnifiedFrame::ErrorBarrier {{ \
                saved_pos: __cc_saved, saved_bp: bp, \
                on_error: NfaFallback::TryDispatchSource {{ \
                    target_cat: CategoryId::{cat}, \
                    next_attempt: 1, \
                    saved_pos: __cc_saved, \
                    min_bp: bp, \
                }}, \
            }}); ",
        ).unwrap();
    }

    // Push CrossCatReturn for first source's LHS parse
    let first_source = &source_cats[0];
    let lhs_resume = format!("{cat}_Dispatch_{first_source}_AwaitLhs");
    write!(
        buf,
        "stack.push(UnifiedFrame::CrossCatReturn {{ \
            resume: ResumePoint::{lhs_resume} {{ saved_pos: __cc_saved, allow_implicit_cast: false }}, \
            saved_bp: bp, \
        }}); \
        return ParseStep::EnterPrefix {{ cat: CategoryId::{first_source}, bp: 0 }}; \
        }} \
        }} /* end keyword guard */ ",
    ).unwrap();
}

/// Generate `infix_step_Cat` for one category.
///
/// The infix step checks for operators (postfix, mixfix, infix) and LED delegation.
/// Returns `EnterPrefix` when pushing a frame, or `Yield` when no operators match.
fn write_infix_step(
    buf: &mut String,
    cat: &str,
    config: &TrampolineConfig,
    bp_table: &BindingPowerTable,
    led_delegations: &HashMap<String, Vec<LedDelegationSource>>,
) {
    let cat_lower = cat.to_lowercase();

    write!(
        buf,
        "#[allow(dead_code)] fn infix_step_{cat}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            lhs: {cat}, \
            bp: u8, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep {{ ",
    ).unwrap();

    // EOF check
    write!(
        buf,
        "if *pos >= tokens.len() {{ \
            return ParseStep::Yield(AnyTerm::{cat}(Box::new(lhs))); \
        }} \
        let token = &tokens[*pos].0; ",
    ).unwrap();

    // Postfix operators
    if config.has_postfix {
        write!(
            buf,
            "if let Some(l_bp) = postfix_bp_{cat}(token) {{ \
                if l_bp >= bp {{ \
                    let op_token = token.clone(); \
                    *pos += 1; \
                    let result = make_postfix_{cat}(&op_token, lhs); \
                    return ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                        lhs: AnyTerm::{cat}(Box::new(result)), bp }}; \
                }} \
            }} ",
        ).unwrap();
    }

    // Mixfix operators
    if config.has_mixfix {
        write!(
            buf,
            "if let Some((l_bp, _r_bp)) = mixfix_bp_{cat}(token) {{ \
                if l_bp >= bp {{ \
                    *pos += 1; \
                    stack.push(UnifiedFrame::{cat}_Mixfix_Tern_0 {{ lhs, saved_bp: bp }}); \
                    return ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: 0 }}; \
                }} \
            }} ",
        ).unwrap();
    }

    // Infix operators
    if config.has_infix {
        write!(
            buf,
            "if let Some((l_bp, r_bp)) = infix_bp_{cat}(token) {{ \
                if l_bp >= bp {{ \
                    let op_pos = *pos; \
                    *pos += 1; \
                    stack.push(UnifiedFrame::{cat}_InfixRHS {{ lhs, op_pos, saved_bp: bp }}); \
                    return ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: r_bp }}; \
                }} \
            }} ",
        ).unwrap();
    }

    // LED delegation: for sum-type categories, check if the LHS is a cast variant
    // and delegate to the constituent category's operators.
    if let Some(sources) = led_delegations.get(cat) {
        for source in sources {
            let src = &source.source_category;
            let src_lower = src.to_lowercase();
            let cast_label = &source.cast_label;

            // Match the cast variant and extract the inner value
            write!(
                buf,
                "if let {cat}::{cast_label}(inner) = &lhs {{ \
                    let inner_ref = inner.as_ref(); ",
            ).unwrap();

            // Same-category infix delegation
            if source.has_infix {
                let resume = format!("{cat}_Led_{src}_Infix_AwaitRhs");
                write!(
                    buf,
                    "if let Some((l_bp, r_bp)) = infix_bp_{src}(&tokens[*pos].0) {{ \
                        let op_pos = *pos; \
                        *pos += 1; \
                        stack.push(UnifiedFrame::CrossCatReturn {{ \
                            resume: ResumePoint::{resume} {{ lhs: inner_ref.clone(), op_pos }}, \
                            saved_bp: bp, \
                        }}); \
                        return ParseStep::EnterPrefix {{ cat: CategoryId::{src}, bp: r_bp }}; \
                    }} ",
                ).unwrap();
            }

            // Cross-category operator delegation
            for op in &source.cross_cat_ops {
                let op_variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
                let resume = format!("{cat}_Led_{src}_{}_AwaitRhs", op.label);
                write!(
                    buf,
                    "if matches!(&tokens[*pos].0, Token::{op_variant}) {{ \
                        let op_pos = *pos; \
                        *pos += 1; \
                        stack.push(UnifiedFrame::CrossCatReturn {{ \
                            resume: ResumePoint::{resume} {{ lhs: inner_ref.clone(), op_pos }}, \
                            saved_bp: bp, \
                        }}); \
                        return ParseStep::EnterPrefix {{ cat: CategoryId::{src}, bp: {} }}; \
                    }} ",
                    op.right_bp,
                ).unwrap();
            }

            // Postfix delegation (inline, no CPS needed)
            if source.has_postfix {
                write!(
                    buf,
                    "if let Some(l_bp) = postfix_bp_{src}(&tokens[*pos].0) {{ \
                        let op_token = tokens[*pos].0.clone(); \
                        *pos += 1; \
                        let result = make_postfix_{src}(&op_token, inner_ref.clone()); \
                        return ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                            lhs: AnyTerm::{cat}(Box::new({cat}::{cast_label}(Box::new(result)))), bp }}; \
                    }} ",
                ).unwrap();
            }

            buf.push_str("} "); // close if let cast variant
        }
    }

    // No operator matched
    write!(
        buf,
        "ParseStep::Yield(AnyTerm::{cat}(Box::new(lhs))) ",
    ).unwrap();

    buf.push_str("}\n");
}

/// Generate the `apply_continuation` function that handles ALL frame unwinding.
fn write_apply_continuation(
    buf: &mut String,
    categories: &[String],
    per_cat_frames: &HashMap<String, Vec<FrameVariantInfo>>,
    cast_rules: &[CastRule],
    cross_rules: &[CrossCategoryRule],
    led_delegations: &HashMap<String, Vec<LedDelegationSource>>,
    bp_table: &BindingPowerTable,
    resume_points: &[ResumePointInfo],
    rd_rules: &[crate::recursive::RDRuleInfo],
) {
    write!(
        buf,
        "#[allow(dead_code)] fn apply_continuation<'a>(\
            frame: UnifiedFrame, \
            result: AnyTerm, \
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep {{ \
            match frame {{ ",
    ).unwrap();

    // Per-category frame handlers
    for cat in categories {
        let cat_lower = cat.to_lowercase();

        if let Some(frames) = per_cat_frames.get(cat) {
            for frame in frames {
                write_frame_continuation_arm(buf, cat, frame, bp_table);
            }
        }
    }

    // CrossCatReturn handler
    buf.push_str(
        "UnifiedFrame::CrossCatReturn { resume, saved_bp } => { \
            apply_resume_point(resume, result, saved_bp, tokens, pos, stack) \
        }, ",
    );

    // ErrorBarrier handler: for dispatch barriers, implement longest-match by
    // saving the result and trying the next source. For non-dispatch barriers,
    // pass the result through (barrier is for errors only).
    buf.push_str(
        "UnifiedFrame::ErrorBarrier { saved_pos, saved_bp, on_error } => { \
            match on_error { \
                NfaFallback::TryDispatchSource { target_cat, next_attempt, saved_pos: sp, min_bp } => { \
                    /* First successful source — save result, try next for longest match */ \
                    let result_pos = *pos; \
                    *pos = sp; \
                    push_dispatch_attempt_with_best(target_cat, next_attempt, sp, min_bp, \
                        Box::new(result), result_pos, pos, stack) \
                } \
                NfaFallback::TryDispatchSourceWithBest { \
                    target_cat, next_attempt, saved_pos: sp, min_bp, best, best_pos \
                } => { \
                    /* Another successful source — keep the one with furthest pos */ \
                    let result_pos = *pos; \
                    let (final_best, final_pos) = if result_pos > best_pos { \
                        (Box::new(result), result_pos) \
                    } else { \
                        (best, best_pos) \
                    }; \
                    *pos = sp; \
                    push_dispatch_attempt_with_best(target_cat, next_attempt, sp, min_bp, \
                        final_best, final_pos, pos, stack) \
                } \
                NfaFallback::CommitDispatchBest { category, min_bp, best, best_pos } => { \
                    /* Last source succeeded — compare and commit best */ \
                    let result_pos = *pos; \
                    if result_pos > best_pos { \
                        ParseStep::ContinueInfix { cat: category, lhs: result, bp: min_bp } \
                    } else { \
                        *pos = best_pos; \
                        ParseStep::ContinueInfix { cat: category, lhs: *best, bp: min_bp } \
                    } \
                } \
                NfaFallback::TryCastSourceCollectAll { target_cat, next_attempt, saved_pos, min_bp } => { \
                    /* First successful NFA cast — save result, try next for spillover */ \
                    let result_pos = *pos; \
                    let results = vec![(result, result_pos, 0.5_f64)]; \
                    *pos = saved_pos; \
                    push_nfa_attempt_collect_all(target_cat, next_attempt, saved_pos, min_bp, results, pos, stack) \
                } \
                NfaFallback::TryCastSourceCollectAllWithResults { target_cat, next_attempt, saved_pos, min_bp, mut results } => { \
                    /* Another successful NFA cast — add to results, try next */ \
                    let result_pos = *pos; \
                    results.push((result, result_pos, 0.5_f64)); \
                    *pos = saved_pos; \
                    push_nfa_attempt_collect_all(target_cat, next_attempt, saved_pos, min_bp, results, pos, stack) \
                } \
                NfaFallback::CommitCastBest { category, min_bp, mut results } => { \
                    /* Last NFA cast succeeded — add to results, commit best, spill rest */ \
                    let result_pos = *pos; \
                    results.push((result, result_pos, 0.5_f64)); \
                    commit_nfa_cast_results(category, min_bp, results, pos) \
                } \
                _ => { \
                    /* Non-dispatch barriers: pass through */ \
                    ParseStep::Yield(result) \
                } \
            } \
        }, ",
    );

    buf.push_str("} }\n"); // close match and fn

    // Generate apply_resume_point
    write_apply_resume_point(buf, resume_points, cast_rules, cross_rules, categories, rd_rules);
}

/// Generate one frame continuation match arm.
fn write_frame_continuation_arm(
    buf: &mut String,
    cat: &str,
    frame: &FrameVariantInfo,
    bp_table: &BindingPowerTable,
) {
    let variant = &frame.variant_name;
    let cat_lower = cat.to_lowercase();
    // Classify the frame variant structurally instead of string matching.
    // The variant_name may be prefixed with "Cat_" from unified mode.
    let prefix = format!("{}_", cat);
    let base_variant = variant.strip_prefix(&prefix).unwrap_or(variant);
    let kind = crate::trampoline::FrameVariantKind::from_name(base_variant);

    use crate::trampoline::FrameVariantKind;
    match kind {
        FrameVariantKind::InfixRHS => {
            write!(
                buf,
                "UnifiedFrame::{cat}_InfixRHS {{ lhs: prev, op_pos, saved_bp }} => {{ \
                    let rhs = result.into_{cat_lower}(); \
                    let node = make_infix_{cat}(&tokens[op_pos].0, prev, rhs); \
                    ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                        lhs: AnyTerm::{cat}(Box::new(node)), bp: saved_bp }} \
                }}, ",
            ).unwrap();
        }
        FrameVariantKind::GroupClose => {
            write!(
                buf,
                "UnifiedFrame::{cat}_GroupClose {{ saved_bp }} => {{ \
                    if *pos < tokens.len() && matches!(&tokens[*pos].0, Token::RParen) {{ \
                        *pos += 1; \
                        ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, lhs: result, bp: saved_bp }} \
                    }} else {{ \
                        ParseStep::Error(ParseError::UnexpectedToken {{ \
                            expected: std::borrow::Cow::Borrowed(\")\"), \
                            found: if *pos < tokens.len() {{ format_token_friendly(&tokens[*pos].0) }} \
                                   else {{ \"EOF\".to_string() }}, \
                            range: if *pos < tokens.len() {{ tokens[*pos].1 }} \
                                   else {{ tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()) }}, \
                            hint: None }}) \
                    }} \
                }}, ",
            ).unwrap();
        }
        FrameVariantKind::UnaryPrefix => {
            let label = &base_variant["UnaryPrefix_".len()..];
            write!(
                buf,
                "UnifiedFrame::{cat}_{base_variant} {{ saved_bp }} => {{ \
                    let inner = result.into_{cat_lower}(); \
                    let node = {cat}::{label}(Box::new(inner)); \
                    ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                        lhs: AnyTerm::{cat}(Box::new(node)), bp: saved_bp }} \
                }}, ",
            ).unwrap();
        }
        FrameVariantKind::RDSegment => {
            // Single-segment RD rule: result is the NT value, expect RParen, construct
            let rule_label = &base_variant[3..base_variant.len()-2]; // e.g., "IntId" from "RD_IntId_0"
            write!(
                buf,
                "UnifiedFrame::{cat}_{base_variant} {{ saved_bp }} => {{ \
                    let a = result.into_{cat_lower}(); \
                    if *pos < tokens.len() && matches!(&tokens[*pos].0, Token::RParen) {{ \
                        *pos += 1; \
                        let node = {cat}::{rule_label}(Box::new(a)); \
                        ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                            lhs: AnyTerm::{cat}(Box::new(node)), bp: saved_bp }} \
                    }} else {{ \
                        ParseStep::Error(ParseError::UnexpectedToken {{ \
                            expected: std::borrow::Cow::Borrowed(\")\"), \
                            found: if *pos < tokens.len() {{ format_token_friendly(&tokens[*pos].0) }} \
                                   else {{ \"EOF\".to_string() }}, \
                            range: if *pos < tokens.len() {{ tokens[*pos].1 }} \
                                   else {{ tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()) }}, \
                            hint: None }}) \
                    }} \
                }}, ",
            ).unwrap();
        }
        FrameVariantKind::Mixfix if base_variant.ends_with("_0") => {
            // Mixfix first operand done, expect separator, push next frame
            let op_label = &base_variant[7..base_variant.len()-2]; // e.g., "Tern" from "Mixfix_Tern_0"
            write!(
                buf,
                "UnifiedFrame::{cat}_{base_variant} {{ lhs: orig_lhs, saved_bp }} => {{ \
                    let param_t = result.into_{cat_lower}(); \
                    if *pos < tokens.len() && matches!(&tokens[*pos].0, Token::Colon) {{ \
                        *pos += 1; \
                        stack.push(UnifiedFrame::{cat}_Mixfix_{op_label}_1 {{ \
                            lhs: orig_lhs, saved_bp, param_t }}); \
                        ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: 0 }} \
                    }} else {{ \
                        ParseStep::Error(ParseError::UnexpectedToken {{ \
                            expected: std::borrow::Cow::Borrowed(\":\"), \
                            found: if *pos < tokens.len() {{ format_token_friendly(&tokens[*pos].0) }} \
                                   else {{ \"EOF\".to_string() }}, \
                            range: if *pos < tokens.len() {{ tokens[*pos].1 }} \
                                   else {{ tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()) }}, \
                            hint: None }}) \
                    }} \
                }}, ",
            ).unwrap();
        }
        FrameVariantKind::Mixfix => { // _1 or other Mixfix parts
            // Mixfix second operand done, construct node
            let op_label = &base_variant[7..base_variant.len()-2]; // e.g., "Tern" from "Mixfix_Tern_1"
            write!(
                buf,
                "UnifiedFrame::{cat}_{base_variant} {{ lhs: orig_lhs, saved_bp, param_t }} => {{ \
                    let param_e = result.into_{cat_lower}(); \
                    let node = {cat}::{op_label}(Box::new(orig_lhs), Box::new(param_t), Box::new(param_e)); \
                    ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, \
                        lhs: AnyTerm::{cat}(Box::new(node)), bp: saved_bp }} \
                }}, ",
            ).unwrap();
        }
        _ => {
            // Fallback: unknown frame variant — panic at runtime with diagnostic
            write!(
                buf,
                "UnifiedFrame::{cat}_{base_variant} {{ .. }} => {{ \
                    panic!(\"apply_continuation: unhandled frame {cat}_{base_variant}\") \
                }}, ",
            ).unwrap();
        }
    }
}

/// Generate `apply_resume_point` for cross-category continuations.
fn write_apply_resume_point(
    buf: &mut String,
    resume_points: &[ResumePointInfo],
    cast_rules: &[CastRule],
    cross_rules: &[CrossCategoryRule],
    categories: &[String],
    rd_rules: &[crate::recursive::RDRuleInfo],
) {
    write!(
        buf,
        "#[allow(dead_code)] fn apply_resume_point<'a>(\
            resume: ResumePoint, \
            result: AnyTerm, \
            saved_bp: u8, \
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep {{ \
            match resume {{ ",
    ).unwrap();

    for rp in resume_points {
        match &rp.context {
            CrossCatContext::NfaCast { label, source_cat } => {
                let source_lower = source_cat.to_lowercase();
                let caller = &rp.caller_cat;
                write!(
                    buf,
                    "ResumePoint::{variant} {{ saved_pos }} => {{ \
                        let val = result.into_{source_lower}(); \
                        if *pos < tokens.len() && matches!(&tokens[*pos].0, Token::RParen) {{ \
                            *pos += 1; \
                            ParseStep::ContinueInfix {{ cat: CategoryId::{caller}, \
                                lhs: AnyTerm::{caller}(Box::new({caller}::{label}(Box::new(val)))), \
                                bp: saved_bp }} \
                        }} else {{ \
                            /* RParen missing — signal error (caught by ErrorBarrier for try-next) */ \
                            *pos = saved_pos; \
                            ParseStep::Error(ParseError::UnexpectedToken {{ \
                                expected: std::borrow::Cow::Borrowed(\")\"), \
                                found: if *pos < tokens.len() {{ format_token_friendly(&tokens[*pos].0) }} \
                                       else {{ \"EOF\".to_string() }}, \
                                range: if *pos < tokens.len() {{ tokens[*pos].1 }} \
                                       else {{ tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()) }}, \
                                hint: None }}) \
                        }} \
                    }}, ",
                    variant = rp.variant_name,
                ).unwrap();
            }
            CrossCatContext::DispatchLhs { source_cat, operators } => {
                let source_lower = source_cat.to_lowercase();
                let caller = &rp.caller_cat;
                write!(
                    buf,
                    "ResumePoint::{variant} {{ saved_pos, allow_implicit_cast }} => {{ \
                        let lhs_val = result.into_{source_lower}(); \
                        if *pos < tokens.len() {{ \
                            match &tokens[*pos].0 {{ ",
                    variant = rp.variant_name,
                ).unwrap();

                // For each operator, push CrossCatReturn for RHS and EnterPrefix
                for (op_variant, rule_label) in operators {
                    let rhs_resume = format!("{caller}_Dispatch_{source_cat}_{rule_label}_AwaitRhs");
                    write!(
                        buf,
                        "Token::{op_variant} => {{ \
                            *pos += 1; \
                            stack.push(UnifiedFrame::CrossCatReturn {{ \
                                resume: ResumePoint::{rhs_resume} {{ \
                                    lhs: lhs_val, saved_pos }}, \
                                saved_bp, \
                            }}); \
                            return ParseStep::EnterPrefix {{ \
                                cat: CategoryId::{source_cat}, bp: 0 }}; \
                        }}, ",
                    ).unwrap();
                }

                // No operator matched. For DETERMINISTIC arms (allow_implicit_cast=true),
                // synthesize an implicit cast. For AMBIGUOUS arms (allow_implicit_cast=false),
                // error to let the ErrorBarrier try the next source or fall back to same-cat.
                let cast_label = {
                    use crate::recursive::RDSyntaxItem;
                    rd_rules.iter()
                        .filter(|rd| rd.category == *caller)
                        .find_map(|rd| {
                            if rd.items.len() >= 4
                                && matches!(&rd.items[1], RDSyntaxItem::Terminal(t) if t == "(")
                                && matches!(&rd.items[2], RDSyntaxItem::NonTerminal { category: c, .. } if c == source_cat)
                                && matches!(rd.items.last(), Some(RDSyntaxItem::Terminal(t)) if t == ")")
                            {
                                Some(rd.label.clone())
                            } else { None }
                        })
                };

                if let Some(ref cast_lbl) = cast_label {
                    write!(
                        buf,
                        "_ => {{ \
                            if allow_implicit_cast && saved_bp > 0 {{ \
                                return ParseStep::ContinueInfix {{ cat: CategoryId::{caller}, \
                                    lhs: AnyTerm::{caller}(Box::new({caller}::{cast_lbl}(Box::new(lhs_val)))), \
                                    bp: saved_bp }}; \
                            }} \
                            *pos = saved_pos; \
                            return ParseStep::Error(ParseError::UnexpectedToken {{ \
                                expected: std::borrow::Cow::Borrowed(\"comparison operator\"), \
                                found: format_token_friendly(&tokens[*pos].0), \
                                range: tokens[*pos].1, hint: None }}); \
                        }} }} \
                        }} else {{ \
                            if allow_implicit_cast && saved_bp > 0 {{ \
                                return ParseStep::ContinueInfix {{ cat: CategoryId::{caller}, \
                                    lhs: AnyTerm::{caller}(Box::new({caller}::{cast_lbl}(Box::new(lhs_val)))), \
                                    bp: saved_bp }}; \
                            }} \
                            *pos = saved_pos; \
                            return ParseStep::Error(ParseError::UnexpectedEof {{ \
                                expected: std::borrow::Cow::Borrowed(\"comparison operator\"), \
                                range: tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()), \
                                hint: None }}); \
                        }} \
                        }}, ",
                    ).unwrap();
                } else {
                    // No cast available — always error
                    write!(
                        buf,
                        "_ => {{ *pos = saved_pos; \
                            return ParseStep::Error(ParseError::UnexpectedToken {{ \
                                expected: std::borrow::Cow::Borrowed(\"comparison operator\"), \
                                found: format_token_friendly(&tokens[*pos].0), \
                                range: tokens[*pos].1, hint: None }}); \
                        }} }} \
                        }} else {{ *pos = saved_pos; \
                            return ParseStep::Error(ParseError::UnexpectedEof {{ \
                                expected: std::borrow::Cow::Borrowed(\"comparison operator\"), \
                                range: tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()), \
                                hint: None }}); \
                        }} \
                        }}, ",
                    ).unwrap();
                }
            }
            CrossCatContext::DispatchRhs { source_cat, rule_label } => {
                let source_lower = source_cat.to_lowercase();
                let caller = &rp.caller_cat;
                write!(
                    buf,
                    "ResumePoint::{variant} {{ lhs, saved_pos }} => {{ \
                        let rhs = result.into_{source_lower}(); \
                        let node = {caller}::{rule_label}(Box::new(lhs), Box::new(rhs)); \
                        ParseStep::ContinueInfix {{ cat: CategoryId::{caller}, \
                            lhs: AnyTerm::{caller}(Box::new(node)), bp: saved_bp }} \
                    }}, ",
                    variant = rp.variant_name,
                ).unwrap();
            }
            CrossCatContext::LedDelegation { source_cat, result_cat, op_label, rewrap_label } => {
                let source_lower = source_cat.to_lowercase();
                let caller = &rp.caller_cat;
                // Cross-cat LED: construct the cross-cat node and re-wrap into sum type
                write!(
                    buf,
                    "ResumePoint::{variant} {{ lhs, op_pos }} => {{ \
                        let rhs = result.into_{source_lower}(); \
                        let node = {result_cat}::{op_label}(Box::new(lhs), Box::new(rhs)); \
                        let wrapped = {caller}::{rewrap_label}(Box::new(node)); \
                        ParseStep::ContinueInfix {{ cat: CategoryId::{caller}, \
                            lhs: AnyTerm::{caller}(Box::new(wrapped)), bp: saved_bp }} \
                    }}, ",
                    variant = rp.variant_name,
                ).unwrap();
            }
            CrossCatContext::LedDelegationInfix { source_cat, cast_label } => {
                let source_lower = source_cat.to_lowercase();
                let caller = &rp.caller_cat;
                // Same-cat infix LED: construct infix node and re-wrap into sum type
                write!(
                    buf,
                    "ResumePoint::{variant} {{ lhs, op_pos }} => {{ \
                        let rhs = result.into_{source_lower}(); \
                        let node = make_infix_{source_cat}(&tokens[op_pos].0, lhs, rhs); \
                        let wrapped = {caller}::{cast_label}(Box::new(node)); \
                        ParseStep::ContinueInfix {{ cat: CategoryId::{caller}, \
                            lhs: AnyTerm::{caller}(Box::new(wrapped)), bp: saved_bp }} \
                    }}, ",
                    variant = rp.variant_name,
                ).unwrap();
            }
            CrossCatContext::RdNonTerminal { rule_label, segment_idx, nt_category } => {
                let caller = &rp.caller_cat;
                let nt_lower = nt_category.to_lowercase();
                // Find the closing terminal from the RD rule (typically ")" or "|")
                // by looking at the items AFTER the nonterminal.
                let closing_terminal = {
                    let mut found = None;
                    for rd in rd_rules {
                        if rd.label == *rule_label && rd.category == *caller {
                            // Find the NT item, then get the terminal after it
                            let mut found_nt = false;
                            for item in &rd.items {
                                if found_nt {
                                    if let crate::recursive::RDSyntaxItem::Terminal(t) = item {
                                        found = Some(t.clone());
                                        break;
                                    }
                                }
                                if let crate::recursive::RDSyntaxItem::NonTerminal { category: c, .. } = item {
                                    if c == nt_category {
                                        found_nt = true;
                                    }
                                }
                            }
                            break;
                        }
                    }
                    found
                };

                let close_token_variant = closing_terminal.as_ref()
                    .map(|t| crate::automata::codegen::terminal_to_variant_name(t))
                    .unwrap_or_else(|| "RParen".into());
                let close_token_display = closing_terminal.as_deref().unwrap_or(")");

                write!(
                    buf,
                    "ResumePoint::{variant} {{ saved_pos }} => {{ \
                        let val = result.into_{nt_lower}(); \
                        if *pos < tokens.len() && matches!(&tokens[*pos].0, Token::{close_token_variant}) {{ \
                            *pos += 1; \
                            let node = {caller}::{rule_label}(Box::new(val)); \
                            ParseStep::ContinueInfix {{ cat: CategoryId::{caller}, \
                                lhs: AnyTerm::{caller}(Box::new(node)), bp: saved_bp }} \
                        }} else {{ \
                            ParseStep::Error(ParseError::UnexpectedToken {{ \
                                expected: std::borrow::Cow::Borrowed(\"{close_token_display}\"), \
                                found: if *pos < tokens.len() {{ format_token_friendly(&tokens[*pos].0) }} \
                                       else {{ \"EOF\".to_string() }}, \
                                range: if *pos < tokens.len() {{ tokens[*pos].1 }} \
                                       else {{ tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()) }}, \
                                hint: None }}) \
                        }} \
                    }}, ",
                    variant = rp.variant_name,
                ).unwrap();
            }
            CrossCatContext::ImplicitCast { source_cat, cast_label } => {
                let source_lower = source_cat.to_lowercase();
                let caller = &rp.caller_cat;
                write!(
                    buf,
                    "ResumePoint::{variant} {{ saved_pos }} => {{ \
                        let val = result.into_{source_lower}(); \
                        ParseStep::ContinueInfix {{ cat: CategoryId::{caller}, \
                            lhs: AnyTerm::{caller}(Box::new({caller}::{cast_label}(Box::new(val)))), \
                            bp: saved_bp }} \
                    }}, ",
                    variant = rp.variant_name,
                ).unwrap();
            }
        }
    }

    buf.push_str("} }\n"); // close match and fn
}

/// Generate the `push_nfa_attempt` dispatcher that pushes frames for the Nth NFA attempt.
fn write_nfa_attempt_dispatcher(
    buf: &mut String,
    categories: &[String],
    cast_rules: &[CastRule],
    rd_rules: &[crate::recursive::RDRuleInfo],
) {
    write!(
        buf,
        "#[allow(dead_code)] fn push_nfa_attempt<'a>(\
            target_cat: CategoryId, \
            attempt: u8, \
            saved_pos: usize, \
            min_bp: u8, \
            pos: &mut usize, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep {{ \
            match (target_cat, attempt) {{ ",
    ).unwrap();

    for cat in categories {
        // Collect NFA alternatives for this category's keyword token.
        // These are RD rules with syntax: KwCat "(" NT ")" where NT may
        // be same-category or cross-category. The last one (same-cat) is
        // the fallback (e.g., IntId for Int).
        use crate::recursive::RDSyntaxItem;
        let mut alternatives: Vec<(&str, &str, bool)> = Vec::new(); // (label, nt_category, is_same_cat)

        for rd in rd_rules {
            if rd.category != *cat { continue; }
            // Match pattern: Terminal(KwCat) + Terminal("(") + NonTerminal(nt) + Terminal(")")
            if rd.items.len() < 3 { continue; }
            let starts_with_kw = matches!(&rd.items[0], RDSyntaxItem::Terminal(t) if {
                let kw = format!("{}", cat.to_lowercase());
                t == &kw
            });
            if !starts_with_kw { continue; }
            let has_lparen = matches!(&rd.items[1], RDSyntaxItem::Terminal(t) if t == "(");
            if !has_lparen { continue; }
            // Find the NT
            if let Some(RDSyntaxItem::NonTerminal { category: nt_cat, .. }) = rd.items.get(2) {
                let is_same = nt_cat == cat;
                alternatives.push((&rd.label, nt_cat, is_same));
            }
        }

        // Also include single-NT cast rules (if any)
        for cast in cast_rules {
            if cast.target_category != *cat { continue; }
            alternatives.push((&cast.label, &cast.source_category, cast.source_category == *cat));
        }

        if alternatives.is_empty() { continue; }

        // Sort: cross-category first (try foreign sources before same-cat fallback)
        alternatives.sort_by_key(|(_, _, is_same)| if *is_same { 1u8 } else { 0u8 });

        for (i, (label, nt_cat, is_same)) in alternatives.iter().enumerate() {
            let attempt_idx = i as u8;
            let has_next = i + 1 < alternatives.len();

            write!(buf, "(CategoryId::{cat}, {attempt_idx}) => {{ ").unwrap();

            // Push error barrier for next attempt
            if has_next {
                let next_idx = attempt_idx + 1;
                write!(
                    buf,
                    "stack.push(UnifiedFrame::ErrorBarrier {{ \
                        saved_pos, saved_bp: min_bp, \
                        on_error: NfaFallback::TryCastSource {{ \
                            target_cat: CategoryId::{cat}, \
                            next_attempt: {next_idx}, \
                            saved_pos, min_bp, \
                        }}, \
                    }}); ",
                ).unwrap();
            } else {
                // Last attempt: terminal error if this also fails.
                // Uses NfaCastExhausted instead of SameCatFallback to prevent
                // infinite loop (SameCatFallback → same_cat_prefix → NFA → SameCatFallback).
                write!(
                    buf,
                    "stack.push(UnifiedFrame::ErrorBarrier {{ \
                        saved_pos, saved_bp: min_bp, \
                        on_error: NfaFallback::NfaCastExhausted {{ \
                            saved_pos, \
                        }}, \
                    }}); ",
                ).unwrap();
            }

            // After backtracking, pos is at saved_pos (keyword token).
            // Skip keyword + LParen to position at the inner expression.
            if *is_same {
                // Same-category NT: use the existing RD frame variant
                let vp = format!("{cat}_");
                write!(
                    buf,
                    "*pos = saved_pos + 2; /* skip keyword + LParen */ \
                     stack.push(UnifiedFrame::{vp}RD_{label}_0 {{ saved_bp: min_bp }}); \
                     ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: 0 }} \
                     }}, ",
                ).unwrap();
            } else {
                // Cross-category NT: use CrossCatReturn with resume point
                let resume_variant = format!("{cat}_CastFrom_{nt_cat}_Await");
                write!(
                    buf,
                    "*pos = saved_pos + 2; /* skip keyword + LParen */ \
                     stack.push(UnifiedFrame::CrossCatReturn {{ \
                        resume: ResumePoint::{resume_variant} {{ saved_pos }}, \
                        saved_bp: min_bp, \
                    }}); \
                    ParseStep::EnterPrefix {{ cat: CategoryId::{nt_cat}, bp: 0 }} \
                    }}, ",
                ).unwrap();
            }
        }
    }

    // Fallback: no more attempts
    buf.push_str(
        "_ => ParseStep::Error(ParseError::UnexpectedEof { \
            expected: std::borrow::Cow::Borrowed(\"NFA attempt\"), \
            range: Range::zero(), hint: None }), ",
    );

    buf.push_str("} }\n"); // close match and fn
}

/// Generate `push_nfa_attempt_collect_all` and `commit_nfa_cast_results` for NFA spillover.
/// These implement the collect-all pattern: try ALL NFA alternatives and record results,
/// then pick the best and spill the rest to NFA_PREFIX_SPILL for semantic disambiguation.
fn write_nfa_collect_all_functions(
    buf: &mut String,
    categories: &[String],
    rd_rules: &[crate::recursive::RDRuleInfo],
) {
    // push_nfa_attempt_collect_all: like push_nfa_attempt but carries collected results
    write!(
        buf,
        "#[allow(dead_code)] fn push_nfa_attempt_collect_all<'a>(\
            target_cat: CategoryId, \
            attempt: u8, \
            saved_pos: usize, \
            min_bp: u8, \
            results: Vec<(AnyTerm, usize, f64)>, \
            pos: &mut usize, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep {{ \
            match (target_cat, attempt) {{ ",
    ).unwrap();

    for cat in categories {
        use crate::recursive::RDSyntaxItem;
        let mut alternatives: Vec<(String, String, bool)> = Vec::new();
        for rd in rd_rules {
            if rd.category != *cat { continue; }
            if rd.items.len() < 3 { continue; }
            let kw = match &rd.items[0] {
                RDSyntaxItem::Terminal(t) => t.clone(),
                _ => continue,
            };
            if !matches!(&rd.items[1], RDSyntaxItem::Terminal(t) if t == "(") { continue; }
            let nt_cat = match &rd.items[2] {
                RDSyntaxItem::NonTerminal { category: c, .. } => c.clone(),
                _ => continue,
            };
            let cat_kw = cat.to_lowercase();
            if kw != cat_kw { continue; }
            let is_same = nt_cat == *cat;
            alternatives.push((rd.label.clone(), nt_cat, is_same));
        }
        alternatives.sort_by_key(|(_, _, is_same)| if *is_same { 1u8 } else { 0u8 });

        for (i, (label, nt_cat, is_same)) in alternatives.iter().enumerate() {
            let attempt_idx = i as u8;
            let has_next = i + 1 < alternatives.len();

            write!(buf, "(CategoryId::{cat}, {attempt_idx}) => {{ ").unwrap();

            if has_next {
                let next_idx = attempt_idx + 1;
                write!(
                    buf,
                    "stack.push(UnifiedFrame::ErrorBarrier {{ \
                        saved_pos, saved_bp: min_bp, \
                        on_error: NfaFallback::TryCastSourceCollectAllWithResults {{ \
                            target_cat: CategoryId::{cat}, \
                            next_attempt: {next_idx}, \
                            saved_pos, min_bp, \
                            results, \
                        }}, \
                    }}); ",
                ).unwrap();
            } else {
                write!(
                    buf,
                    "stack.push(UnifiedFrame::ErrorBarrier {{ \
                        saved_pos, saved_bp: min_bp, \
                        on_error: NfaFallback::CommitCastBest {{ \
                            category: CategoryId::{cat}, min_bp, \
                            results, \
                        }}, \
                    }}); ",
                ).unwrap();
            }

            if *is_same {
                let vp = format!("{cat}_");
                write!(
                    buf,
                    "*pos = saved_pos + 2; \
                     stack.push(UnifiedFrame::{vp}RD_{label}_0 {{ saved_bp: min_bp }}); \
                     ParseStep::EnterPrefix {{ cat: CategoryId::{cat}, bp: 0 }} \
                     }}, ",
                ).unwrap();
            } else {
                let resume_variant = format!("{cat}_CastFrom_{nt_cat}_Await");
                write!(
                    buf,
                    "*pos = saved_pos + 2; \
                     stack.push(UnifiedFrame::CrossCatReturn {{ \
                        resume: ResumePoint::{resume_variant} {{ saved_pos }}, \
                        saved_bp: min_bp, \
                    }}); \
                    ParseStep::EnterPrefix {{ cat: CategoryId::{nt_cat}, bp: 0 }} \
                    }}, ",
                ).unwrap();
            }
        }
    }

    buf.push_str(
        "_ => ParseStep::Error(ParseError::UnexpectedEof { \
            expected: std::borrow::Cow::Borrowed(\"NFA collect-all attempt\"), \
            range: Range::zero(), hint: None }), ",
    );
    buf.push_str("} }\n");

    // commit_nfa_cast_results: pick the best result, spill the rest to NFA_PREFIX_SPILL
    write!(
        buf,
        "#[allow(dead_code)] fn commit_nfa_cast_results<'a>(\
            category: CategoryId, \
            min_bp: u8, \
            mut results: Vec<(AnyTerm, usize, f64)>, \
            pos: &mut usize, \
        ) -> ParseStep {{ \
            /* Sort by weight ascending (best first) */ \
            results.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal)); \
            let (best, best_pos, _best_weight) = results.remove(0); \
            *pos = best_pos; \
            /* Spill remaining alternatives to NFA_PREFIX_SPILL */ \
            match category {{ ",
    ).unwrap();

    for cat in categories {
        let cat_upper = cat.to_uppercase();
        write!(
            buf,
            "CategoryId::{cat} => {{ \
                NFA_PREFIX_SPILL_{cat_upper}.with(|cell| {{ \
                    let mut spill = cell.take(); \
                    for (term, end_pos, weight) in results {{ \
                        if let AnyTerm::{cat}(v) = term {{ \
                            spill.push((*v, end_pos, weight)); \
                        }} \
                    }} \
                    spill.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal)); \
                    cell.set(spill); \
                }}); \
                ParseStep::ContinueInfix {{ cat: CategoryId::{cat}, lhs: best, bp: min_bp }} \
            }}, ",
        ).unwrap();
    }

    buf.push_str("} }\n");
}

/// Generate the `push_dispatch_attempt` function for cross-cat dispatch (comparison operators).
/// Each attempt tries a different source category for LHS of comparison ops.
fn write_dispatch_attempt_dispatcher(
    buf: &mut String,
    categories: &[String],
    cross_rules: &[CrossCategoryRule],
) {
    write!(
        buf,
        "#[allow(dead_code)] fn push_dispatch_attempt<'a>(\
            target_cat: CategoryId, \
            attempt: u8, \
            saved_pos: usize, \
            min_bp: u8, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep {{ \
            match (target_cat, attempt) {{ ",
    ).unwrap();

    // Group cross-cat rules by result category → source categories
    let mut by_result: HashMap<String, Vec<String>> = HashMap::new();
    for rule in cross_rules {
        let sources = by_result.entry(rule.result_category.clone()).or_default();
        if !sources.contains(&rule.source_category) {
            sources.push(rule.source_category.clone());
        }
    }

    // Sort by result category so generated match arms are in the same order every build.
    let mut by_result_sorted: Vec<_> = by_result.iter().collect();
    by_result_sorted.sort_by_key(|(cat, _)| *cat);

    for (result_cat, source_cats) in &by_result_sorted {
        for (i, source_cat) in source_cats.iter().enumerate() {
            let attempt_idx = i as u8;
            let has_next = i + 1 < source_cats.len();
            let lhs_resume = format!("{result_cat}_Dispatch_{source_cat}_AwaitLhs");

            write!(buf, "(CategoryId::{result_cat}, {attempt_idx}) => {{ ").unwrap();

            if has_next {
                let next_idx = attempt_idx + 1;
                write!(
                    buf,
                    "stack.push(UnifiedFrame::ErrorBarrier {{ \
                        saved_pos, saved_bp: min_bp, \
                        on_error: NfaFallback::TryDispatchSource {{ \
                            target_cat: CategoryId::{result_cat}, \
                            next_attempt: {next_idx}, \
                            saved_pos, min_bp, \
                        }}, \
                    }}); ",
                ).unwrap();
            } else {
                // Last source: fall back to same-category on failure
                write!(
                    buf,
                    "stack.push(UnifiedFrame::ErrorBarrier {{ \
                        saved_pos, saved_bp: min_bp, \
                        on_error: NfaFallback::SameCatFallback {{ \
                            category: CategoryId::{result_cat}, min_bp, \
                        }}, \
                    }}); ",
                ).unwrap();
            }

            write!(
                buf,
                "stack.push(UnifiedFrame::CrossCatReturn {{ \
                    resume: ResumePoint::{lhs_resume} {{ saved_pos, allow_implicit_cast: false }}, \
                    saved_bp: min_bp, \
                }}); \
                ParseStep::EnterPrefix {{ cat: CategoryId::{source_cat}, bp: 0 }} \
                }}, ",
            ).unwrap();
        }
    }

    // Fallback
    buf.push_str(
        "_ => ParseStep::Error(ParseError::UnexpectedEof { \
            expected: std::borrow::Cow::Borrowed(\"dispatch attempt\"), \
            range: Range::zero(), hint: None }), ",
    );

    buf.push_str("} }\n");

    // Generate push_dispatch_attempt_with_best: like push_dispatch_attempt but
    // carries the best result (AnyTerm) and position from a previous successful source.
    // Used by the longest-match dispatch: each source's success is compared by position,
    // and the one consuming the most tokens wins.
    write!(
        buf,
        "#[allow(dead_code)] fn push_dispatch_attempt_with_best<'a>(\
            target_cat: CategoryId, \
            attempt: u8, \
            saved_pos: usize, \
            min_bp: u8, \
            best: Box<AnyTerm>, \
            best_pos: usize, \
            pos: &mut usize, \
            stack: &mut Vec<UnifiedFrame>, \
        ) -> ParseStep {{ \
            match (target_cat, attempt) {{ ",
    ).unwrap();

    for (result_cat, source_cats) in &by_result_sorted {
        for (i, source_cat) in source_cats.iter().enumerate() {
            let attempt_idx = i as u8;
            let has_next = i + 1 < source_cats.len();
            let lhs_resume = format!("{result_cat}_Dispatch_{source_cat}_AwaitLhs");

            write!(buf, "(CategoryId::{result_cat}, {attempt_idx}) => {{ ").unwrap();

            if has_next {
                let next_idx = attempt_idx + 1;
                // Carry the best forward via TryDispatchSourceWithBest
                write!(
                    buf,
                    "stack.push(UnifiedFrame::ErrorBarrier {{ \
                        saved_pos, saved_bp: min_bp, \
                        on_error: NfaFallback::TryDispatchSourceWithBest {{ \
                            target_cat: CategoryId::{result_cat}, \
                            next_attempt: {next_idx}, \
                            saved_pos, min_bp, \
                            best, best_pos, \
                        }}, \
                    }}); ",
                ).unwrap();
            } else {
                // Last source: use CommitDispatchBest to commit the best on completion
                write!(
                    buf,
                    "stack.push(UnifiedFrame::ErrorBarrier {{ \
                        saved_pos, saved_bp: min_bp, \
                        on_error: NfaFallback::CommitDispatchBest {{ \
                            category: CategoryId::{result_cat}, min_bp, \
                            best, best_pos, \
                        }}, \
                    }}); ",
                ).unwrap();
            }

            write!(
                buf,
                "stack.push(UnifiedFrame::CrossCatReturn {{ \
                    resume: ResumePoint::{lhs_resume} {{ saved_pos, allow_implicit_cast: false }}, \
                    saved_bp: min_bp, \
                }}); \
                ParseStep::EnterPrefix {{ cat: CategoryId::{source_cat}, bp: 0 }} \
                }}, ",
            ).unwrap();
        }
    }

    // If attempt is past the last source, commit the best we have
    buf.push_str(
        "_ => { \
            *pos = best_pos; \
            ParseStep::ContinueInfix { cat: target_cat, lhs: *best, bp: min_bp } \
        }, ",
    );

    buf.push_str("} }\n");
}

// ═══════════════════════════════════════════════════════════════════════════
// Helpers for prefix arm generation
// ═══════════════════════════════════════════════════════════════════════════

/// Get the variable constructor name for a category (e.g., "IVar" for "Int").
fn get_var_constructor(cat: &str) -> &str {
    match cat {
        "Int" => "IVar",
        "Float" => "FVar",
        "Bool" => "BVar",
        "Str" => "SVar",
        "Proc" => "PVar",
        "Name" => "NVar",
        "Num" => "NumVar",
        "Pred" => "PredVar",
        "Expr" => "ExprVar",
        "Term" => "TermVar",
        _ => "Var",
    }
}

// get_rd_function_tokens removed — RD function rules are now handled by the
// NFA keyword dispatch block in write_prefix_arms_unified, which is data-driven
// from rd_rules. No hardcoding needed.
