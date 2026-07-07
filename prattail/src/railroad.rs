//! CEK-7: Railroad diagram generation from grammar specifications.
//!
//! Converts `LanguageSpec` / `RuleSpec` / `SyntaxItemSpec` structures into
//! SVG railroad diagrams. Each category gets one diagram.
//!
//! ## Grammar → Railroad Mapping
//!
//! | PraTTaIL | Railroad Node |
//! |----------|--------------|
//! | `Terminal(t)` | `Terminal::new(t)` |
//! | `NonTerminal { category }` | `NonTerminal::new(cat)` |
//! | `Optional { inner }` | `Optional::new(inner)` |
//! | Collection rule | `Repeat::new(elem, sep)` |
//! | Multiple rules for category | `Choice::new(alternatives)` |
//! | Rule items in sequence | `Sequence::new(items)` |
//! | Infix operator | `Sequence::new([lhs, Terminal(op), rhs])` |
//!
//! ## Runtime Annotation
//!
//! When a `CekMachine` is driven with trace collection, hit counts per rule
//! map onto the railroad diagram:
//! - Hot paths: red (high frequency)
//! - Cold paths: blue (low frequency)
//! - Dead paths: gray (never taken)
//!
//! ## Output Surfaces
//!
//! This module is an author-facing developer-experience (DX) tool: it is
//! compiled unconditionally but is NOT wired into the default parser pipeline,
//! so the default build is byte-identical whether or not it is used.
//!
//! - **Text/ASCII** — `render_grammar_railroad_text` is *always* available and
//!   needs no extra dependency. It folds [`generate_railroad_diagrams`] and
//!   [`diagram_to_text`] into a per-category `BTreeMap<String, String>`. See
//!   `prattail/examples/railroad.rs` for a runnable demo.
//! - **SVG** — `render_grammar_railroad_svg` is gated behind the
//!   `railroad-diagrams` Cargo feature (off by default). The SVG is emitted by
//!   hand from the format-independent [`RailroadNode`] tree, so enabling the
//!   feature pulls in NO new crate dependency.

use std::collections::HashMap;

use crate::{LanguageSpec, RuleSpec, SyntaxItemSpec};
// Phase 11 (F.1): railroad.rs decoupled from `TraceCollector`. Previously
// `annotate_diagrams` consumed a `&TraceCollector`; it now takes a
// `&HashMap<String, usize>` of rule_hits — the only field railroad ever
// consumed. This removes the dependency on parser-side CEK types so
// railroad survives Stage 6 Phase E.4 (atomic-swap commit 2).

// ══════════════════════════════════════════════════════════════════════════════
// Railroad Node Types (Abstract — independent of the `railroad` crate)
// ══════════════════════════════════════════════════════════════════════════════

/// Abstract railroad diagram node.
///
/// This representation is independent of the `railroad` crate — it can be
/// serialized, tested, and converted to SVG or other formats.
#[derive(Debug, Clone)]
pub enum RailroadNode {
    /// A terminal token (literal keyword or symbol).
    Terminal {
        /// Display text.
        text: String,
    },
    /// A nonterminal reference (category name).
    NonTerminal {
        /// Category name.
        text: String,
    },
    /// A sequence of nodes (left to right).
    Sequence {
        /// Ordered child nodes.
        children: Vec<RailroadNode>,
    },
    /// A choice between alternatives (vertical branches).
    Choice {
        /// Alternative paths.
        alternatives: Vec<RailroadNode>,
    },
    /// An optional element (bypass path).
    Optional {
        /// The optional inner node.
        inner: Box<RailroadNode>,
    },
    /// A repetition (loop back).
    Repeat {
        /// The repeated element.
        element: Box<RailroadNode>,
        /// The separator (if any).
        separator: Option<Box<RailroadNode>>,
    },
    /// An empty node (epsilon transition).
    Empty,
}

/// A railroad diagram for one category.
#[derive(Debug, Clone)]
pub struct CategoryDiagram {
    /// Category name.
    pub category: String,
    /// Root node of the diagram.
    pub root: RailroadNode,
    /// Per-node hit counts (from trace annotation).
    /// Key: node path (e.g., "Add/0", "Neg/1"), Value: count.
    pub hit_counts: HashMap<String, usize>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Diagram Generation
// ══════════════════════════════════════════════════════════════════════════════

/// Generate railroad diagram nodes for all categories in a grammar.
///
/// Returns a map from category name to its diagram.
pub fn generate_railroad_diagrams(spec: &LanguageSpec) -> HashMap<String, CategoryDiagram> {
    let mut diagrams = HashMap::new();

    for cat_spec in &spec.types {
        let cat_name = &cat_spec.name;

        // Collect all rules for this category
        let cat_rules: Vec<&RuleSpec> = spec
            .rules
            .iter()
            .filter(|r| r.category == *cat_name && !r.is_cross_category && !r.is_cast)
            .collect();

        if cat_rules.is_empty() {
            continue;
        }

        let root = if cat_rules.len() == 1 {
            rule_to_node(cat_rules[0])
        } else {
            // Multiple rules → Choice
            RailroadNode::Choice {
                alternatives: cat_rules.iter().map(|r| rule_to_node(r)).collect(),
            }
        };

        diagrams.insert(
            cat_name.clone(),
            CategoryDiagram {
                category: cat_name.clone(),
                root,
                hit_counts: HashMap::new(),
            },
        );
    }

    diagrams
}

/// Convert a single rule to a railroad node.
fn rule_to_node(rule: &RuleSpec) -> RailroadNode {
    if rule.is_infix {
        // Infix: lhs op rhs
        let op_terminals: Vec<&str> = rule
            .syntax
            .iter()
            .filter_map(|item| {
                if let SyntaxItemSpec::Terminal(t) = item {
                    Some(t.as_str())
                } else {
                    None
                }
            })
            .collect();

        let op_text = op_terminals.first().copied().unwrap_or("?");

        return RailroadNode::Sequence {
            children: vec![
                RailroadNode::NonTerminal { text: rule.category.clone() },
                RailroadNode::Terminal { text: op_text.to_string() },
                RailroadNode::NonTerminal { text: rule.category.clone() },
            ],
        };
    }

    if rule.is_collection {
        // Collection: repeat with separator
        let element_cat = rule
            .syntax
            .iter()
            .find_map(|item| match item {
                SyntaxItemSpec::Collection { element_category, .. } => {
                    Some(element_category.clone())
                },
                _ => None,
            })
            .unwrap_or_else(|| rule.category.clone());

        let separator = rule.separator.as_deref();

        return RailroadNode::Repeat {
            element: Box::new(RailroadNode::NonTerminal { text: element_cat }),
            separator: separator.map(|s| Box::new(RailroadNode::Terminal { text: s.to_string() })),
        };
    }

    // General rule: sequence of items
    let children: Vec<RailroadNode> = rule.syntax.iter().map(syntax_item_to_node).collect();

    if children.len() == 1 {
        children.into_iter().next().expect("single child")
    } else {
        RailroadNode::Sequence { children }
    }
}

/// Convert a syntax item to a railroad node.
fn syntax_item_to_node(item: &SyntaxItemSpec) -> RailroadNode {
    match item {
        SyntaxItemSpec::Terminal(t) => RailroadNode::Terminal { text: t.clone() },
        SyntaxItemSpec::NonTerminal { category, .. } => {
            RailroadNode::NonTerminal { text: category.clone() }
        },
        SyntaxItemSpec::IdentCapture { .. } => {
            RailroadNode::NonTerminal { text: "ident".to_string() }
        },
        SyntaxItemSpec::Binder { category, .. } => {
            RailroadNode::NonTerminal { text: format!("binder:{}", category) }
        },
        SyntaxItemSpec::Collection { element_category, separator, .. } => RailroadNode::Repeat {
            element: Box::new(RailroadNode::NonTerminal { text: element_category.clone() }),
            separator: Some(Box::new(RailroadNode::Terminal { text: separator.clone() })),
        },
        SyntaxItemSpec::Optional { inner } => {
            let inner_nodes: Vec<RailroadNode> = inner.iter().map(syntax_item_to_node).collect();
            let inner_node = if inner_nodes.len() == 1 {
                inner_nodes.into_iter().next().expect("single inner")
            } else {
                RailroadNode::Sequence { children: inner_nodes }
            };
            RailroadNode::Optional { inner: Box::new(inner_node) }
        },
        SyntaxItemSpec::Sep { body, separator, .. } => RailroadNode::Repeat {
            element: Box::new(syntax_item_to_node(body)),
            separator: Some(Box::new(RailroadNode::Terminal { text: separator.clone() })),
        },
        SyntaxItemSpec::Map { body_items } => {
            let children: Vec<RailroadNode> = body_items.iter().map(syntax_item_to_node).collect();
            RailroadNode::Sequence { children }
        },
        SyntaxItemSpec::Zip { left_category, right_category, body, .. } => RailroadNode::Sequence {
            children: vec![
                RailroadNode::NonTerminal { text: left_category.clone() },
                syntax_item_to_node(body),
                RailroadNode::NonTerminal { text: right_category.clone() },
            ],
        },
        SyntaxItemSpec::BinderCollection { separator, .. } => RailroadNode::Repeat {
            element: Box::new(RailroadNode::NonTerminal { text: "ident".to_string() }),
            separator: Some(Box::new(RailroadNode::Terminal { text: separator.clone() })),
        },
        SyntaxItemSpec::GuardExpression { param_name } => {
            RailroadNode::NonTerminal { text: format!("guard:{}", param_name) }
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Trace Annotation
// ══════════════════════════════════════════════════════════════════════════════

/// Annotate railroad diagrams with hit counts from a rule_hits map.
///
/// Maps each `(rule_label, count)` pair to all diagrams' hit_counts.
/// Callers pass `&trace.rule_hits` (or any compatible map) directly.
pub fn annotate_diagrams(
    diagrams: &mut HashMap<String, CategoryDiagram>,
    rule_hits: &HashMap<String, usize>,
) {
    for (rule_label, &count) in rule_hits {
        // Find which category this rule belongs to
        for diagram in diagrams.values_mut() {
            // Simple heuristic: if the rule label appears as a frame variant prefix,
            // it belongs to this category's diagram
            diagram.hit_counts.insert(rule_label.clone(), count);
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// SVG Generation (Textual)
// ══════════════════════════════════════════════════════════════════════════════

/// Generate a simple textual representation of a railroad diagram.
///
/// This is a basic ASCII-art visualization. For full SVG output,
/// use the `railroad` crate (feature-gated).
pub fn diagram_to_text(node: &RailroadNode) -> String {
    match node {
        RailroadNode::Terminal { text } => format!("──[ {} ]──", text),
        RailroadNode::NonTerminal { text } => format!("──⟨ {} ⟩──", text),
        RailroadNode::Sequence { children } => children
            .iter()
            .map(diagram_to_text)
            .collect::<Vec<_>>()
            .join(""),
        RailroadNode::Choice { alternatives } => {
            let mut out = String::new();
            out.push_str("──┬──");
            for (i, alt) in alternatives.iter().enumerate() {
                if i > 0 {
                    out.push_str("\n  ├──");
                }
                out.push_str(&diagram_to_text(alt));
                out.push_str("──");
            }
            out.push_str("\n  └──");
            out
        },
        RailroadNode::Optional { inner } => {
            format!("──┬──{}──┬──\n  └──────────────┘", diagram_to_text(inner))
        },
        RailroadNode::Repeat { element, separator } => {
            let sep_str = separator
                .as_ref()
                .map(|s| diagram_to_text(s))
                .unwrap_or_default();
            format!("──↻ {} {} ↻──", diagram_to_text(element), sep_str)
        },
        RailroadNode::Empty => "──ε──".to_string(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Author-DX Rendering Entrypoints
// ══════════════════════════════════════════════════════════════════════════════

/// Render every category's grammar railroad diagram as ASCII text.
///
/// This is the always-on author-DX entrypoint: it folds
/// [`generate_railroad_diagrams`] (one [`CategoryDiagram`] per category) and
/// [`diagram_to_text`] into a deterministically-ordered map from category name
/// to its rendered diagram. A `BTreeMap` is returned (rather than the internal
/// `HashMap`) so the output order is stable across runs — convenient for
/// golden-file snapshots and human review.
///
/// Needs no extra dependency and adds no caller to the parser pipeline, so the
/// default build is unaffected.
pub fn render_grammar_railroad_text(
    spec: &LanguageSpec,
) -> std::collections::BTreeMap<String, String> {
    let diagrams = generate_railroad_diagrams(spec);
    let mut rendered = std::collections::BTreeMap::new();
    for (category, diagram) in diagrams {
        rendered.insert(category, diagram_to_text(&diagram.root));
    }
    rendered
}

// ══════════════════════════════════════════════════════════════════════════════
// SVG Rendering (feature-gated, dependency-free)
// ══════════════════════════════════════════════════════════════════════════════

/// Render every category's grammar railroad diagram as a standalone SVG string.
///
/// Gated behind the `railroad-diagrams` Cargo feature. The SVG is emitted by
/// hand from the format-independent [`RailroadNode`] tree, so enabling the
/// feature pulls in NO new crate dependency. Like the text variant this returns
/// a deterministically-ordered `BTreeMap` from category name to SVG document.
///
/// The layout is intentionally simple: each node renders to a horizontal run of
/// labeled boxes (terminals as rounded rects, nonterminals as plain rects),
/// with choices stacked vertically and repeats/optionals annotated. It is a
/// review aid, not a typeset diagram.
#[cfg(feature = "railroad-diagrams")]
pub fn render_grammar_railroad_svg(
    spec: &LanguageSpec,
) -> std::collections::BTreeMap<String, String> {
    let diagrams = generate_railroad_diagrams(spec);
    let mut rendered = std::collections::BTreeMap::new();
    for (category, diagram) in diagrams {
        let svg = node_to_svg_document(&category, &diagram.root);
        rendered.insert(category, svg);
    }
    rendered
}

/// Wrap a node's emitted SVG fragment in a minimal standalone `<svg>` document.
#[cfg(feature = "railroad-diagrams")]
fn node_to_svg_document(category: &str, node: &RailroadNode) -> String {
    let mut cursor_x: u32 = 10;
    let mut max_y: u32 = 60;
    let body = node_to_svg_fragment(node, &mut cursor_x, 30, &mut max_y);
    let width = cursor_x + 10;
    let height = max_y + 20;
    format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\" \
         viewBox=\"0 0 {width} {height}\">\n  \
         <title>{category}</title>\n  \
         <rect x=\"0\" y=\"0\" width=\"{width}\" height=\"{height}\" fill=\"#ffffff\"/>\n\
         {body}</svg>\n",
        width = width,
        height = height,
        category = svg_escape(category),
        body = body,
    )
}

/// Emit an SVG fragment for one node, advancing `cursor_x` left-to-right and
/// tracking the maximum vertical extent in `max_y`.
#[cfg(feature = "railroad-diagrams")]
fn node_to_svg_fragment(
    node: &RailroadNode,
    cursor_x: &mut u32,
    y: u32,
    max_y: &mut u32,
) -> String {
    match node {
        RailroadNode::Terminal { text } => svg_box(text, cursor_x, y, max_y, true),
        RailroadNode::NonTerminal { text } => svg_box(text, cursor_x, y, max_y, false),
        RailroadNode::Empty => svg_box("ε", cursor_x, y, max_y, true),
        RailroadNode::Sequence { children } => children
            .iter()
            .map(|child| node_to_svg_fragment(child, cursor_x, y, max_y))
            .collect::<Vec<_>>()
            .join(""),
        RailroadNode::Choice { alternatives } => {
            // Stack alternatives vertically; each starts at the same x and
            // descends by a fixed row height. The cursor advances by the widest.
            let start_x = *cursor_x;
            let mut widest = start_x;
            let mut out = String::new();
            for (i, alt) in alternatives.iter().enumerate() {
                let mut branch_x = start_x;
                let branch_y = y + (i as u32) * 50;
                out.push_str(&node_to_svg_fragment(alt, &mut branch_x, branch_y, max_y));
                widest = widest.max(branch_x);
            }
            *cursor_x = widest;
            out
        },
        RailroadNode::Optional { inner } => {
            // Render the inner run, then annotate the bypass arc above it.
            let start_x = *cursor_x;
            let fragment = node_to_svg_fragment(inner, cursor_x, y, max_y);
            format!(
                "{fragment}  <path d=\"M{start} {arc_y} q {half} -18 {span} 0\" \
                 fill=\"none\" stroke=\"#888888\"/>\n",
                fragment = fragment,
                start = start_x,
                arc_y = y - 2,
                half = (*cursor_x - start_x) / 2,
                span = *cursor_x - start_x,
            )
        },
        RailroadNode::Repeat { element, separator } => {
            let start_x = *cursor_x;
            let mut fragment = node_to_svg_fragment(element, cursor_x, y, max_y);
            if let Some(sep) = separator {
                fragment.push_str(&node_to_svg_fragment(sep, cursor_x, y, max_y));
            }
            format!(
                "{fragment}  <path d=\"M{end} {arc_y} q -{half} 18 -{span} 0\" \
                 fill=\"none\" stroke=\"#3366cc\"/>\n",
                fragment = fragment,
                end = *cursor_x,
                arc_y = y + 22,
                half = (*cursor_x - start_x) / 2,
                span = *cursor_x - start_x,
            )
        },
    }
}

/// Emit one labeled box (rounded rect for terminals, plain rect for
/// nonterminals), advancing `cursor_x` by its width.
#[cfg(feature = "railroad-diagrams")]
fn svg_box(label: &str, cursor_x: &mut u32, y: u32, max_y: &mut u32, terminal: bool) -> String {
    // Width heuristic: ~8px per glyph plus padding, clamped to a sane minimum.
    let width = (label.chars().count() as u32 * 8 + 20).max(40);
    let x = *cursor_x;
    let (rx, fill) = if terminal {
        (10u32, "#e8f0fe")
    } else {
        (0u32, "#f4f4f4")
    };
    *max_y = (*max_y).max(y + 30);
    *cursor_x = x + width + 12;
    format!(
        "  <rect x=\"{x}\" y=\"{y}\" width=\"{width}\" height=\"24\" rx=\"{rx}\" \
         fill=\"{fill}\" stroke=\"#333333\"/>\n  \
         <text x=\"{tx}\" y=\"{ty}\" font-family=\"monospace\" font-size=\"12\" \
         text-anchor=\"middle\">{label}</text>\n",
        x = x,
        y = y,
        width = width,
        rx = rx,
        fill = fill,
        tx = x + width / 2,
        ty = y + 16,
        label = svg_escape(label),
    )
}

/// Escape the five XML metacharacters for safe inclusion in SVG text/titles.
#[cfg(feature = "railroad-diagrams")]
fn svg_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&apos;")
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_power::Associativity;
    use crate::CategorySpec;

    fn make_simple_spec() -> LanguageSpec {
        LanguageSpec {
            name: "Calc".to_string(),
            types: vec![CategorySpec {
                name: "Expr".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: true,
                has_var: true,
            }],
            rules: vec![
                RuleSpec {
                    label: "Lit".to_string(),
                    category: "Expr".to_string(),
                    syntax: vec![SyntaxItemSpec::Terminal("integer".to_string())],
                    is_infix: false,
                    associativity: Associativity::Left,
                    is_var: false,
                    is_literal: true,
                    has_binder: false,
                    has_multi_binder: false,
                    is_collection: false,
                    collection_type: None,
                    separator: None,
                    is_cross_category: false,
                    cross_source_category: None,
                    is_cast: false,
                    cast_source_category: None,
                    is_unary_prefix: false,
                    prefix_precedence: None,
                    is_postfix: false,
                    has_rust_code: false,
                    rust_code: None,
                    eval_mode: None,
                    source_location: None,
                    is_auto_injected: false,
                },
                RuleSpec {
                    label: "Add".to_string(),
                    category: "Expr".to_string(),
                    syntax: vec![
                        SyntaxItemSpec::NonTerminal {
                            category: "Expr".to_string(),
                            param_name: "a".to_string(),
                        },
                        SyntaxItemSpec::Terminal("+".to_string()),
                        SyntaxItemSpec::NonTerminal {
                            category: "Expr".to_string(),
                            param_name: "b".to_string(),
                        },
                    ],
                    is_infix: true,
                    associativity: Associativity::Left,
                    is_var: false,
                    is_literal: false,
                    has_binder: false,
                    has_multi_binder: false,
                    is_collection: false,
                    collection_type: None,
                    separator: None,
                    is_cross_category: false,
                    cross_source_category: None,
                    is_cast: false,
                    cast_source_category: None,
                    is_unary_prefix: false,
                    prefix_precedence: None,
                    is_postfix: false,
                    has_rust_code: false,
                    rust_code: None,
                    eval_mode: None,
                    source_location: None,
                    is_auto_injected: false,
                },
            ],
            beam_width: crate::BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            literal_patterns: crate::LiteralPatterns::default(),
            recovery_config: crate::recovery::RecoveryConfig::default(),
            semantic_dependency_groups: Vec::new(),
            custom_tokens: Vec::new(),
            modes: Vec::new(),
            sync: None,
            tree_invariants: Vec::new(),
            refinement_types: Vec::new(),
            guard_config: None,
            reservation_policy: crate::ReservationPolicy::default(),
        }
    }

    #[test]
    fn test_generate_diagrams() {
        let spec = make_simple_spec();
        let diagrams = generate_railroad_diagrams(&spec);

        assert!(diagrams.contains_key("Expr"));
        let expr = &diagrams["Expr"];
        assert_eq!(expr.category, "Expr");

        // Should be a Choice between Lit and Add
        match &expr.root {
            RailroadNode::Choice { alternatives } => {
                assert_eq!(alternatives.len(), 2);
            },
            _ => panic!("expected Choice node for multi-rule category"),
        }
    }

    #[test]
    fn test_terminal_node() {
        let node = RailroadNode::Terminal { text: "+".to_string() };
        let text = diagram_to_text(&node);
        assert!(text.contains("+"));
    }

    #[test]
    fn test_nonterminal_node() {
        let node = RailroadNode::NonTerminal { text: "Expr".to_string() };
        let text = diagram_to_text(&node);
        assert!(text.contains("Expr"));
    }

    #[test]
    fn test_sequence_node() {
        let node = RailroadNode::Sequence {
            children: vec![
                RailroadNode::NonTerminal { text: "Expr".to_string() },
                RailroadNode::Terminal { text: "+".to_string() },
                RailroadNode::NonTerminal { text: "Expr".to_string() },
            ],
        };
        let text = diagram_to_text(&node);
        assert!(text.contains("Expr"));
        assert!(text.contains("+"));
    }

    #[test]
    fn test_optional_node() {
        let node = RailroadNode::Optional {
            inner: Box::new(RailroadNode::Terminal { text: "else".to_string() }),
        };
        let text = diagram_to_text(&node);
        assert!(text.contains("else"));
    }

    #[test]
    fn test_repeat_node() {
        let node = RailroadNode::Repeat {
            element: Box::new(RailroadNode::NonTerminal { text: "Expr".to_string() }),
            separator: Some(Box::new(RailroadNode::Terminal { text: ",".to_string() })),
        };
        let text = diagram_to_text(&node);
        assert!(text.contains("Expr"));
        assert!(text.contains(","));
    }

    #[test]
    fn test_trace_annotation() {
        let spec = make_simple_spec();
        let mut diagrams = generate_railroad_diagrams(&spec);

        // annotate_diagrams takes &HashMap<String, usize> directly.
        let mut rule_hits: HashMap<String, usize> = HashMap::new();
        rule_hits.insert("InfixRHS".to_string(), 10);
        rule_hits.insert("RD_Lit_0".to_string(), 5);

        annotate_diagrams(&mut diagrams, &rule_hits);

        let expr = &diagrams["Expr"];
        assert_eq!(expr.hit_counts.get("InfixRHS"), Some(&10));
    }
}
