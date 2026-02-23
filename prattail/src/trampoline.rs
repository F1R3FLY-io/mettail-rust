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
use crate::binding_power::BindingPowerTable;
use crate::dispatch::CastRule;
use crate::prediction::FirstSet;
use crate::pratt::PrefixHandler;
use crate::recursive::{CollectionKind, RDRuleInfo, RDSyntaxItem};

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Check if a rule is a "simple collection" — one that can be trampolined
/// as a CollectionElem frame with element-by-element parsing.
///
/// Complex collections (ZipMapSep rules with binders like PInputs) are handled
/// by standalone parse functions and should NOT have CollectionElem frames generated.
fn is_simple_collection(rule: &RDRuleInfo) -> bool {
    rule.is_collection && !rule.has_binder && !rule.has_multi_binder && !has_zipmapsep(rule)
}

/// Check if a rule has any ZipMapSep syntax items.
///
/// ZipMapSep rules are too complex for trampoline splitting and must use
/// their standalone parse functions.
fn has_zipmapsep(rule: &RDRuleInfo) -> bool {
    rule.items.iter().any(|item| matches!(item, RDSyntaxItem::ZipMapSep { .. }))
}

/// Check if a rule should be trampolined (inlined/split) or dispatched to
/// its standalone parse function.
///
/// Returns true if the rule should use its standalone parse function and NOT
/// be trampolined. This includes:
/// - Rules with ZipMapSep items (complex parsing logic)
/// - Rules with multi-binder items (complex binder handling)
fn should_use_standalone_fn(rule: &RDRuleInfo) -> bool {
    has_zipmapsep(rule) || rule.has_multi_binder
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
    Collection { name: String, kind: CollectionKind, element_category: String },
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
            }
            RDSyntaxItem::IdentCapture { param_name } => {
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Ident {
                    name: param_name.clone(),
                });
            }
            RDSyntaxItem::Binder { param_name, .. } => {
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Binder {
                    name: param_name.clone(),
                });
            }
            RDSyntaxItem::Terminal(_) => {
                current_inline.push(item.clone());
            }
            RDSyntaxItem::Collection { param_name, element_category, kind, .. } => {
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Collection {
                    name: param_name.clone(),
                    kind: *kind,
                    element_category: element_category.clone(),
                });
            }
            RDSyntaxItem::SepList { collection_name, element_category, kind, .. } => {
                current_inline.push(item.clone());
                accumulated_captures.push(SegmentCapture::Collection {
                    name: collection_name.clone(),
                    kind: *kind,
                    element_category: element_category.clone(),
                });
            }
            RDSyntaxItem::ZipMapSep { .. } | RDSyntaxItem::Optional { .. } => {
                // These complex items are kept as inline for now
                // The trampoline will handle them as-is (they have bounded depth)
                current_inline.push(item.clone());
            }
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
    pub all_first_sets: std::collections::BTreeMap<String, FirstSet>,
    /// FOLLOW set.
    pub follow_set: FirstSet,
    /// Whether the grammar has binders.
    pub has_binders: bool,
    /// Optional prediction WFST for weight-ordered dispatch (feature = "wfst").
    /// When present, prefix match arms are reordered by tropical weight (lowest first).
    #[cfg(feature = "wfst")]
    pub prediction_wfst: Option<crate::wfst::PredictionWfst>,
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
                FrameField { name: "lhs".to_string(), type_str: cat.clone() },
                FrameField { name: "op_pos".to_string(), type_str: "usize".to_string() },
                FrameField { name: "saved_bp".to_string(), type_str: "u8".to_string() },
            ],
        });
    }

    // GroupClose (always present — parenthesized expressions)
    variants.push(FrameVariant {
        name: "GroupClose".to_string(),
        fields: vec![
            FrameField { name: "saved_bp".to_string(), type_str: "u8".to_string() },
        ],
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
            fields: vec![
                FrameField { name: "saved_bp".to_string(), type_str: "u8".to_string() },
            ],
        });
    }

    // ── Per-RD-handler segment variants ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat {
            continue;
        }
        // Skip unary prefix (handled above), collection rules (handled separately),
        // and rules dispatched to standalone functions (ZipMapSep, multi-binder)
        if rd_rule.prefix_bp.is_some() || is_simple_collection(rd_rule) || should_use_standalone_fn(rd_rule) {
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
                    }
                    SegmentCapture::Ident { name } | SegmentCapture::Binder { name } => {
                        fields.push(FrameField {
                            name: name.clone(),
                            type_str: "String".to_string(),
                        });
                    }
                    SegmentCapture::Collection { name, kind, element_category } => {
                        let type_str = match kind {
                            CollectionKind::HashBag => format!("mettail_runtime::HashBag<{}>", element_category),
                            CollectionKind::HashSet => format!("std::collections::HashSet<{}>", element_category),
                            CollectionKind::Vec => format!("Vec<{}>", element_category),
                        };
                        fields.push(FrameField {
                            name: name.clone(),
                            type_str,
                        });
                    }
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
        let element_category = rd_rule.items.iter().find_map(|item| {
            match item {
                RDSyntaxItem::Collection { element_category, .. } => Some(element_category.clone()),
                _ => None,
            }
        }).unwrap_or_else(|| cat.clone());

        let type_str = match collection_type {
            CollectionKind::HashBag => format!("mettail_runtime::HashBag<{}>", element_category),
            CollectionKind::HashSet => format!("std::collections::HashSet<{}>", element_category),
            CollectionKind::Vec => format!("Vec<{}>", element_category),
        };

        variants.push(FrameVariant {
            name: format!("CollectionElem_{}", rd_rule.label),
            fields: vec![
                FrameField { name: "elements".to_string(), type_str },
                FrameField { name: "saved_pos".to_string(), type_str: "usize".to_string() },
                FrameField { name: "saved_bp".to_string(), type_str: "u8".to_string() },
            ],
        });
    }

    // ── Per-mixfix operand step variants ──
    for op in bp_table.mixfix_operators_for_category(cat) {
        for (i, _part) in op.mixfix_parts.iter().enumerate() {
            let mut fields = vec![
                FrameField { name: "lhs".to_string(), type_str: cat.clone() },
                FrameField { name: "saved_bp".to_string(), type_str: "u8".to_string() },
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
                FrameField { name: "binder_name".to_string(), type_str: "String".to_string() },
                FrameField { name: "saved_bp".to_string(), type_str: "u8".to_string() },
            ],
        });

        // Multi lambda body
        variants.push(FrameVariant {
            name: "LambdaBody_Multi".to_string(),
            fields: vec![
                FrameField { name: "binder_names".to_string(), type_str: "Vec<String>".to_string() },
                FrameField { name: "saved_bp".to_string(), type_str: "u8".to_string() },
            ],
        });

        // Dollar syntax: $cat(f, x) — frame for after parsing f, before parsing x
        for dom in &config.all_categories {
            let dom_cap = capitalize_first(&dom.to_lowercase());

            // Single-apply $dom(f, x): frame captures state after parsing f.
            // x is a cross-category call (bounded depth), handled inline in the unwind handler.
            variants.push(FrameVariant {
                name: format!("DollarF_{}", dom_cap),
                fields: vec![
                    FrameField { name: "saved_bp".to_string(), type_str: "u8".to_string() },
                ],
            });

            // Multi-apply $$dom(f, x1, x2, ...): frame captures state after parsing f.
            // All args are cross-category calls (bounded depth), handled inline in the unwind handler.
            variants.push(FrameVariant {
                name: format!("DdollarF_{}", dom_cap),
                fields: vec![
                    FrameField { name: "saved_bp".to_string(), type_str: "u8".to_string() },
                ],
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

    FrameInfo {
        enum_name,
        variants,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Trampolined Parser Generation
// ══════════════════════════════════════════════════════════════════════════════

/// Write the complete trampolined parser for a single category.
///
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

    let has_led = config.has_infix || config.has_postfix || config.has_mixfix;

    // ── 1. Generate helper functions (same as pratt.rs) ──

    if has_led {
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
    }

    // ── 2. Generate Frame enum ──
    let frame_info = write_frame_enum(buf, config, rd_rules, bp_table);

    // ── 3. Generate thread-local frame stack pool ──
    // Each category gets its own thread-local Vec<Frame_Cat> that retains capacity
    // across parse calls. Uses Cell (not RefCell) with take/set pattern to support
    // re-entrant calls from standalone parse functions (ZipMapSep, multi-binder,
    // ident-lookahead rules). Nested calls gracefully get a fresh Vec.
    let cat_upper = cat.to_uppercase();
    write!(
        buf,
        "thread_local! {{ \
            static FRAME_POOL_{cat_upper}: std::cell::Cell<Vec<{frame_enum}>> = \
                std::cell::Cell::new(Vec::new()); \
        }}",
        frame_enum = frame_info.enum_name,
    ).unwrap();

    // ── 4. Generate wrapper function ──
    // Thin wrapper that takes the pooled Vec from the thread-local (replacing with
    // empty Vec), delegates to _impl, then puts the Vec back. Re-entrant calls
    // see an empty Cell and allocate fresh — only the outermost call's Vec (with
    // the largest capacity) survives in the pool.
    // Heuristic preallocation: nesting depth ≤ tokens/2 (each nesting event
    // consumes ≥2 tokens: operator + operand).
    write!(
        buf,
        "fn {parse_fn}<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            min_bp: u8, \
        ) -> Result<{cat}, ParseError> {{ \
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
    ).unwrap();

    // ── 5. Generate the inner trampolined parse function (_impl) ──
    write_trampoline_body(buf, config, bp_table, prefix_handlers, rd_rules, &frame_info, &parse_fn);
}

/// Write the monolithic trampolined parser function body.
fn write_trampoline_body(
    buf: &mut String,
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
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            min_bp: u8, \
            stack: &mut Vec<{frame_enum}>, \
        ) -> Result<{cat}, ParseError> {{",
        frame_enum = frame_info.enum_name,
    ).unwrap();

    // Clear the pooled stack (retains capacity from previous calls).
    buf.push_str("stack.clear();");
    buf.push_str("let mut cur_bp = min_bp;");

    // ═══ Main trampoline loop ═══
    buf.push_str("'drive: loop {");

    // ═══ Phase A: Prefix dispatch ═══
    write_prefix_phase(buf, config, prefix_handlers, rd_rules, frame_info, &expected_escaped);

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
                    expected: \"{expected_escaped}\", \
                    range: eof_range, \
                }}),",
    ).unwrap();

    // Collection catch on EOF: finalize with collected elements via break 'prefix
    write_collection_eof_catch(buf, config, rd_rules, frame_info);

    write!(
        buf,
        "Some(_) => return Err(ParseError::UnexpectedEof {{ \
            expected: \"{expected_escaped}\", \
            range: eof_range, \
        }}), \
        }} \
        }}",
    ).unwrap();

    // Emit WFST weight annotations as comments (for debugging/verification)
    #[cfg(feature = "wfst")]
    if let Some(ref wfst) = config.prediction_wfst {
        if let Some(comment) = crate::wfst::generate_weighted_dispatch(wfst, &config.category) {
            buf.push_str(&comment);
        }
    }

    buf.push_str("match &tokens[*pos].0 {");

    // Generate match arms (same code in both paths — WFST ordering affects
    // cross-category dispatch backtracking order, not prefix match semantics)
    write_prefix_match_arms(buf, config, prefix_handlers, rd_rules, frame_info, expected_escaped);

    buf.push_str("} };"); // close match and 'prefix block
}

/// Write the prefix match arms.
fn write_prefix_match_arms(
    buf: &mut String,
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
    // for complex rules (ZipMapSep, multi-binder).
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
            // Handled by ident lookahead below
            continue;
        }

        // Determine the dispatch token
        let first_terminal = rd_rule.items.iter().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item {
                Some(t.clone())
            } else {
                None
            }
        });

        if let Some(ref terminal) = first_terminal {
            let variant = terminal_to_variant_name(terminal);

            // Complex rules (ZipMapSep, multi-binder) dispatch to their standalone parse function
            if should_use_standalone_fn(rd_rule) {
                let fn_name = format!("parse_{}", rd_rule.label.to_lowercase());
                write!(
                    buf,
                    "Token::{} => {{ \
                        break 'prefix {}(tokens, pos)?; \
                    }},",
                    variant, fn_name,
                ).unwrap();
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
                write!(buf, "stack.push({}::{} {{",
                    frame_info.enum_name, segments[0].frame_variant).unwrap();
                write!(buf, "saved_bp: cur_bp,").unwrap();
                for capture in &segments[0].accumulated_captures {
                    match capture {
                        SegmentCapture::Ident { name }
                        | SegmentCapture::Binder { name }
                        | SegmentCapture::NonTerminal { name, .. } => {
                            write!(buf, "{},", name).unwrap();
                        }
                        _ => {}
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
        }
    }

    // ── Unary prefix operators ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || rd_rule.prefix_bp.is_none() {
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
            ).unwrap();
        }
    }

    // ── Collection rules ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || !is_simple_collection(rd_rule) {
            continue;
        }

        // Find the opening terminal and collection info
        let opening_terminal = rd_rule.items.iter().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item { Some(t.clone()) } else { None }
        });
        let collection_info = rd_rule.items.iter().find_map(|item| {
            match item {
                RDSyntaxItem::Collection { element_category, separator, kind, .. } => {
                    Some((element_category.clone(), separator.clone(), *kind))
                }
                _ => None,
            }
        });

        if let (Some(terminal), Some((_elem_cat, _sep, kind))) = (opening_terminal, collection_info) {
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
            ).unwrap();
        }
    }

    // ── Native literal match arms ──
    if let Some(ref native_type) = config.native_type {
        write_native_literal_arm(buf, cat, native_type);
    }

    // ── Grouping: parenthesized expression ──
    write!(
        buf,
        "Token::LParen => {{ \
            *pos += 1; \
            stack.push({}::GroupClose {{ saved_bp: cur_bp }}); \
            cur_bp = 0; \
            continue 'drive; \
        }},",
        frame_info.enum_name,
    ).unwrap();

    // ── Cast rule prefix arms ──
    for cast_rule in &config.cast_rules {
        if let Some(source_first) = config.all_first_sets.get(&cast_rule.source_category) {
            let unique_tokens = source_first.difference(&config.own_first_set);
            for token in &unique_tokens.tokens {
                let mut arm = String::new();
                crate::pratt::write_token_pattern_pub(&mut arm, token);
                write!(
                    arm,
                    " => {{ \
                        let val = parse_{}(tokens, pos, 0)?; \
                        break 'prefix {}::{}(Box::new(val)); \
                    }},",
                    cast_rule.source_category, cat, cast_rule.label,
                ).unwrap();
                buf.push_str(&arm);
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
        cat.chars().next().unwrap_or('V').to_uppercase().collect::<String>()
    );

    // When WFST is enabled, reorder lookahead handlers by weight (lowest first = most likely).
    // This ensures the most probable ident-dispatch path is tried first, reducing backtracking.
    #[cfg(feature = "wfst")]
    let lookahead_handlers = {
        let mut sorted = lookahead_handlers;
        if let Some(ref wfst) = config.prediction_wfst {
            sorted.sort_by(|a, b| {
                let weight_a = a.ident_lookahead.as_ref()
                    .and_then(|tok| {
                        let variant = terminal_to_variant_name(tok);
                        wfst.predict(&variant).first().map(|wa| wa.weight)
                    })
                    .unwrap_or(crate::automata::semiring::TropicalWeight::new(f64::INFINITY));
                let weight_b = b.ident_lookahead.as_ref()
                    .and_then(|tok| {
                        let variant = terminal_to_variant_name(tok);
                        wfst.predict(&variant).first().map(|wa| wa.weight)
                    })
                    .unwrap_or(crate::automata::semiring::TropicalWeight::new(f64::INFINITY));
                weight_a.cmp(&weight_b)
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
        ).unwrap();
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
        ).unwrap();
    }

    // ── Error fallback ──
    write!(
        buf,
        "other => {{ \
            let err = Err(ParseError::UnexpectedToken {{ \
                expected: \"{expected_escaped}\", \
                found: format!(\"{{:?}}\", other), \
                range: tokens[*pos].1, \
            }}); \
            match stack.pop() {{ \
                None => return err.map(|_: {cat}| unreachable!()),",
    ).unwrap();
    // Collection catch on prefix error
    write_collection_error_catch_inline(buf, config, rd_rules, frame_info);
    write!(
        buf,
        "Some(_) => return err.map(|_: {cat}| unreachable!()), \
        }} \
        }},",
    ).unwrap();
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
                    ).unwrap();
                }
            }
            RDSyntaxItem::IdentCapture { param_name } => {
                write!(buf, "let {} = expect_ident(tokens, pos)?;", param_name).unwrap();
            }
            RDSyntaxItem::Binder { param_name, .. } => {
                write!(buf, "let {} = expect_ident(tokens, pos)?;", param_name).unwrap();
            }
            RDSyntaxItem::NonTerminal { category, param_name } => {
                // Cross-category nonterminal: direct function call (bounded depth)
                write!(buf, "let {} = parse_{}(tokens, pos, 0)?;", param_name, category).unwrap();
            }
            _ => {
                // Collection, ZipMapSep, Optional — kept as inline but not yet handled
                // (these are complex items that need special treatment)
            }
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
        last.accumulated_captures.iter().filter(|c| {
            let name = match c {
                SegmentCapture::NonTerminal { name, .. }
                | SegmentCapture::Ident { name }
                | SegmentCapture::Binder { name }
                | SegmentCapture::Collection { name, .. } => name.clone(),
            };
            seen.insert(name)
        }).collect()
    } else {
        Vec::new()
    };

    if rule.has_binder {
        // Single binder: Cat::Label(extra_args..., Scope::new(Binder(binder), Box::new(body)))
        let binder_cap = all_captures.iter().find(|c| matches!(c, SegmentCapture::Binder { .. }));
        let body_cap = all_captures.iter().rev().find(|c| matches!(c, SegmentCapture::NonTerminal { .. }));
        if let (Some(SegmentCapture::Binder { name: binder_name }), Some(SegmentCapture::NonTerminal { name: body_name, .. })) = (binder_cap, body_cap) {
            let extra: Vec<&&SegmentCapture> = all_captures.iter()
                .filter(|c| {
                    let n = match c {
                        SegmentCapture::NonTerminal { name, .. }
                        | SegmentCapture::Ident { name }
                        | SegmentCapture::Binder { name }
                        | SegmentCapture::Collection { name, .. } => name,
                    };
                    n != binder_name && n != body_name
                }).collect();
            write!(buf, "break 'prefix {cat}::{label}(").unwrap();
            for c in &extra {
                write_segment_capture_as_arg(buf, c);
                buf.push(',');
            }
            write!(buf, "mettail_runtime::Scope::new(\
                mettail_runtime::Binder(mettail_runtime::get_or_create_var({})), \
                Box::new({}),\
            ));", binder_name, body_name).unwrap();
        } else {
            write!(buf, "break 'prefix {}::{};", cat, label).unwrap();
        }
    } else if all_captures.is_empty() {
        write!(buf, "break 'prefix {}::{};", cat, label).unwrap();
    } else {
        write!(buf, "break 'prefix {}::{}(", cat, label).unwrap();
        for (i, c) in all_captures.iter().enumerate() {
            if i > 0 { buf.push(','); }
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
        }
        "i64" | "isize" => {
            write!(
                buf,
                "Token::Integer(v) => {{ let val = *v; *pos += 1; break 'prefix {}::NumLit(val); }},",
                cat,
            ).unwrap();
        }
        "u32" => {
            write!(
                buf,
                "Token::Integer(v) => {{ let val = *v as u32; *pos += 1; break 'prefix {}::NumLit(val); }},",
                cat,
            ).unwrap();
        }
        "u64" | "usize" => {
            write!(
                buf,
                "Token::Integer(v) => {{ let val = *v as u64; *pos += 1; break 'prefix {}::NumLit(val); }},",
                cat,
            ).unwrap();
        }
        "f32" | "f64" => {
            write!(
                buf,
                "Token::Float(v) => {{ let val = (*v).into(); *pos += 1; break 'prefix {}::FloatLit(val); }},",
                cat,
            ).unwrap();
        }
        "bool" => {
            write!(
                buf,
                "Token::Boolean(v) => {{ let val = *v; *pos += 1; break 'prefix {}::BoolLit(val); }},",
                cat,
            ).unwrap();
        }
        "str" | "String" => {
            write!(
                buf,
                "Token::StringLit(v) => {{ let val = (*v).to_string(); *pos += 1; break 'prefix {}::StringLit(val); }},",
                cat,
            ).unwrap();
        }
        _ => {}
    }
}

/// Write lambda prefix match arm (^x.{body} or ^[x,y].{body}).
fn write_lambda_prefix_arm(
    buf: &mut String,
    config: &TrampolineConfig,
    frame_info: &FrameInfo,
) {
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
                        expected: \"identifier or '['\", \
                        found: format!(\"{{:?}}\", tokens[*pos].0), \
                        range: tokens[*pos].1, \
                    }}); \
                }} \
            }} \
        }},",
        enum_name = frame_info.enum_name,
    ).unwrap();
}

/// Write dollar syntax prefix match arms.
fn write_dollar_prefix_arms(
    buf: &mut String,
    config: &TrampolineConfig,
    frame_info: &FrameInfo,
) {
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
        ).unwrap();

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
        ).unwrap();
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
        ).unwrap();
        wrote_first = true;
    }

    // Mixfix (pushes frame for each operand)
    if config.has_mixfix {
        if wrote_first { buf.push_str(" else "); }
        write_mixfix_led(buf, config, bp_table, frame_info);
        wrote_first = true;
    }

    // Infix (pushes frame for RHS)
    if config.has_infix {
        if wrote_first { buf.push_str(" else "); }
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
        ).unwrap();
        wrote_first = true;
    }

    if wrote_first {
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
    ).unwrap();

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
        ).unwrap();
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
            ).unwrap();
        }
        buf.push_str("_ => unreachable!(\"mixfix_bp returned Some for non-mixfix token\"),");
        buf.push('}');
    }

    buf.push('}');
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
        ).unwrap();
    }

    // ── GroupClose ──
    write!(
        buf,
        "Some({enum_name}::GroupClose {{ saved_bp }}) => {{ \
            expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
            cur_bp = saved_bp; \
        }},",
        enum_name = frame_info.enum_name,
    ).unwrap();

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
        ).unwrap();
    }

    // ── RD handler segment continuations ──
    for rd_rule in rd_rules {
        if rd_rule.category != *cat || is_simple_collection(rd_rule) || rd_rule.prefix_bp.is_some() || should_use_standalone_fn(rd_rule) {
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
                    }
                }
            }

            write!(
                buf,
                "Some({enum_name}::{variant} {{ {fields} }}) => {{",
                enum_name = frame_info.enum_name,
                variant = segment.frame_variant,
                fields = field_names.join(", "),
            ).unwrap();

            // Assign the parsed nonterminal result to its param name
            write!(buf, "let {} = lhs;", nt.param_name).unwrap();

            // Check if there's a next segment with more items to process
            if let Some(next) = next_segment {
                // Inline the next segment's terminal items
                write_inline_items(buf, &next.inline_items, false);

                if let Some(ref next_nt) = next.nonterminal {
                    // Push frame for the next continuation
                    write!(buf, "stack.push({}::{} {{",
                        frame_info.enum_name, next.frame_variant).unwrap();
                    write!(buf, "saved_bp,").unwrap();
                    // All accumulated captures from previous segments + this nonterminal
                    for capture in &next.accumulated_captures {
                        match capture {
                            SegmentCapture::NonTerminal { name, .. }
                            | SegmentCapture::Ident { name }
                            | SegmentCapture::Binder { name }
                            | SegmentCapture::Collection { name, .. } => {
                                write!(buf, "{},", name).unwrap();
                            }
                        }
                    }
                    buf.push_str("});");

                    if next_nt.category == *cat {
                        write!(buf, "cur_bp = {};", next_nt.bp).unwrap();
                        buf.push_str("continue 'drive;");
                    } else {
                        // Cross-category: direct call
                        write!(buf, "let {} = parse_{}(tokens, pos, {})?;",
                            next_nt.param_name, next_nt.category, next_nt.bp).unwrap();
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
        let sep_info = rd_rule.items.iter().find_map(|item| {
            match item {
                RDSyntaxItem::Collection { separator, .. } => Some(separator.clone()),
                _ => None,
            }
        });
        let closing_terminal = rd_rule.items.iter().rev().find_map(|item| {
            if let RDSyntaxItem::Terminal(t) = item { Some(t.clone()) } else { None }
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
            ).unwrap();
        }

        // Finalize: expect closing terminal, construct
        if let Some(ref closing) = closing_terminal {
            let close_variant = terminal_to_variant_name(closing);
            write!(
                buf,
                "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                close_variant, closing,
            ).unwrap();
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
            ).unwrap();

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
                ).unwrap();
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
                write!(buf, "stack.push({enum_name}::Mixfix_{label}_{next_i} {{ lhs: orig_lhs,",
                    enum_name = frame_info.enum_name, label = op.label).unwrap();
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
        let lam_match_arms: String = config.all_categories.iter().map(|dom| {
            format!(
                "Some(InferredType::Base(VarCategory::{})) => {}::Lam{}(scope), ",
                dom, cat, dom
            )
        }).collect::<Vec<_>>().join("");

        let mlam_match_arms: String = config.all_categories.iter().map(|dom| {
            format!(
                "Some(InferredType::Base(VarCategory::{})) => {}::MLam{}(scope), ",
                dom, cat, dom
            )
        }).collect::<Vec<_>>().join("");

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
        ).unwrap();

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
        ).unwrap();

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
        ).unwrap();

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
        ).unwrap();

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
            if let RDSyntaxItem::Terminal(t) = item { Some(t.clone()) } else { None }
        });

        write!(
            buf,
            "Some({enum_name}::CollectionElem_{label} {{ elements, saved_pos, saved_bp }}) => {{ \
                *pos = saved_pos;",
            enum_name = frame_info.enum_name,
            label = rd_rule.label,
        ).unwrap();

        if let Some(ref closing) = closing_terminal {
            let close_variant = terminal_to_variant_name(closing);
            write!(
                buf,
                "if *pos < tokens.len() {{ \
                    expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?; \
                }}",
                close_variant, closing,
            ).unwrap();
        }

        // Use break 'prefix to exit the prefix block with the finalized collection.
        // The unwind phase will then process any remaining frames from the stack.
        write!(
            buf,
            "cur_bp = saved_bp; \
            break 'prefix {cat}::{label}(elements);",
            label = rd_rule.label,
        ).unwrap();
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
            if let RDSyntaxItem::Terminal(t) = item { Some(t.clone()) } else { None }
        });

        write!(
            buf,
            "Some({enum_name}::CollectionElem_{label} {{ elements, saved_pos, saved_bp }}) => {{ \
                *pos = saved_pos;",
            enum_name = frame_info.enum_name,
            label = rd_rule.label,
        ).unwrap();

        if let Some(ref closing) = closing_terminal {
            let close_variant = terminal_to_variant_name(closing);
            write!(
                buf,
                "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                close_variant, closing,
            ).unwrap();
        }

        // Use break 'prefix to exit the prefix block with the finalized collection.
        // (Same approach as write_collection_eof_catch — we're inside the 'prefix block.)
        write!(
            buf,
            "cur_bp = saved_bp; \
            break 'prefix {cat}::{label}(elements); \
            }},",
            label = rd_rule.label,
        ).unwrap();
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
    let _all_captures: Vec<&SegmentCapture> = segments.iter()
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
        let binder_cap = unique_captures.iter().find(|c| matches!(c, SegmentCapture::Binder { .. }));
        let body_cap = unique_captures.iter().rev().find(|c| matches!(c, SegmentCapture::NonTerminal { .. }));

        if let (Some(SegmentCapture::Binder { name: binder_name }), Some(SegmentCapture::NonTerminal { name: body_name, .. })) = (binder_cap, body_cap) {
            let extra_caps: Vec<&&SegmentCapture> = unique_captures.iter()
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
            ).unwrap();
        }
    } else if rule.has_multi_binder {
        let binder_cap = unique_captures.iter().find(|c| matches!(c, SegmentCapture::Binder { .. }));
        let body_cap = unique_captures.iter().rev().find(|c| matches!(c, SegmentCapture::NonTerminal { .. }));

        if let (Some(SegmentCapture::Binder { name: binder_name }), Some(SegmentCapture::NonTerminal { name: body_name, .. })) = (binder_cap, body_cap) {
            let extra_caps: Vec<&&SegmentCapture> = unique_captures.iter()
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
            ).unwrap();

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
            ).unwrap();
        }
    } else if unique_captures.is_empty() {
        write!(buf, "lhs = {cat}::{label};").unwrap();
    } else {
        write!(buf, "lhs = {cat}::{label}(").unwrap();
        for (i, c) in unique_captures.iter().enumerate() {
            if i > 0 { buf.push(','); }
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
        }
        SegmentCapture::Ident { name } => {
            write!(
                buf,
                "mettail_runtime::OrdVar(mettail_runtime::Var::Free(\
                    mettail_runtime::get_or_create_var({})\
                ))",
                name,
            ).unwrap();
        }
        SegmentCapture::Binder { name } => {
            // Binders are handled specially in the constructor
            buf.push_str(name);
        }
        SegmentCapture::Collection { name, .. } => {
            buf.push_str(name);
        }
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
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            min_bp: u8, \
            errors: &mut Vec<ParseError>, \
        ) -> Option<{cat}> {{",
    ).unwrap();

    let own_parse_fn = if config.needs_dispatch {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    // Call the trampolined parser and catch errors
    write!(
        buf,
        "match {own_parse_fn}(tokens, pos, min_bp) {{ \
            Ok(v) => Some(v), \
            Err(e) => {{ \
                errors.push(e); \
                sync_to(tokens, pos, &|t| is_sync_{cat}(t)); \
                None \
            }} \
        }} }}",
    ).unwrap();
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
        }
    }
}
