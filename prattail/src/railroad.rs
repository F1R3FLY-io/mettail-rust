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

#[path = "railroad/node_lifecycle.rs"]
mod node_lifecycle;

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
    enum Task<'item> {
        Visit(&'item SyntaxItemSpec),
        Optional { base: usize, len: usize },
        Sep(&'item str),
        Map { base: usize, len: usize },
        Zip(&'item str, &'item str),
    }

    let mut tasks = vec![Task::Visit(item)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(SyntaxItemSpec::Terminal(text)) => {
                values.push(RailroadNode::Terminal { text: text.clone() });
            },
            Task::Visit(SyntaxItemSpec::NonTerminal { category, .. }) => {
                values.push(RailroadNode::NonTerminal { text: category.clone() });
            },
            Task::Visit(SyntaxItemSpec::IdentCapture { .. }) => {
                values.push(RailroadNode::NonTerminal { text: "ident".to_string() });
            },
            Task::Visit(SyntaxItemSpec::TokenKindCapture { kind_name, .. }) => {
                values.push(RailroadNode::NonTerminal { text: kind_name.clone() });
            },
            Task::Visit(SyntaxItemSpec::Binder { category, .. }) => {
                values.push(RailroadNode::NonTerminal { text: format!("binder:{category}") });
            },
            Task::Visit(SyntaxItemSpec::Collection { element_category, separator, .. }) => {
                values.push(RailroadNode::Repeat {
                    element: Box::new(RailroadNode::NonTerminal { text: element_category.clone() }),
                    separator: Some(Box::new(RailroadNode::Terminal { text: separator.clone() })),
                });
            },
            Task::Visit(SyntaxItemSpec::Optional { inner }) => {
                tasks.push(Task::Optional { base: values.len(), len: inner.len() });
                tasks.extend(inner.iter().rev().map(Task::Visit));
            },
            Task::Visit(SyntaxItemSpec::Sep { body, separator, .. }) => {
                tasks.push(Task::Sep(separator));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(SyntaxItemSpec::Map { body_items }) => {
                tasks.push(Task::Map {
                    base: values.len(),
                    len: body_items.len(),
                });
                tasks.extend(body_items.iter().rev().map(Task::Visit));
            },
            Task::Visit(SyntaxItemSpec::Zip { left_category, right_category, body, .. }) => {
                tasks.push(Task::Zip(left_category, right_category));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(SyntaxItemSpec::BinderCollection { separator, .. }) => {
                values.push(RailroadNode::Repeat {
                    element: Box::new(RailroadNode::NonTerminal { text: "ident".to_string() }),
                    separator: Some(Box::new(RailroadNode::Terminal { text: separator.clone() })),
                });
            },
            Task::Visit(SyntaxItemSpec::GuardExpression { param_name }) => {
                values.push(RailroadNode::NonTerminal { text: format!("guard:{param_name}") });
            },
            Task::Optional { base, len } => {
                debug_assert_eq!(values.len(), base + len);
                let children: Vec<_> = values.drain(base..).collect();
                let inner = if len == 1 {
                    children
                        .into_iter()
                        .next()
                        .expect("single optional railroad child")
                } else {
                    RailroadNode::Sequence { children }
                };
                values.push(RailroadNode::Optional { inner: Box::new(inner) });
            },
            Task::Sep(separator) => {
                let element = values.pop().expect("railroad Sep lowering lost its body");
                values.push(RailroadNode::Repeat {
                    element: Box::new(element),
                    separator: Some(Box::new(RailroadNode::Terminal {
                        text: separator.to_string(),
                    })),
                });
            },
            Task::Map { base, len } => {
                debug_assert_eq!(values.len(), base + len);
                let children = values.drain(base..).collect();
                values.push(RailroadNode::Sequence { children });
            },
            Task::Zip(left_category, right_category) => {
                let body = values.pop().expect("railroad Zip lowering lost its body");
                values.push(RailroadNode::Sequence {
                    children: vec![
                        RailroadNode::NonTerminal { text: left_category.to_string() },
                        body,
                        RailroadNode::NonTerminal { text: right_category.to_string() },
                    ],
                });
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("syntax-item railroad lowering produced no node")
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
    use std::fmt::Write as _;

    enum Task<'node> {
        Visit(&'node RailroadNode),
        Text(&'static str),
    }

    let mut out = String::new();
    let mut tasks = vec![Task::Visit(node)];
    while let Some(task) = tasks.pop() {
        match task {
            Task::Text(text) => out.push_str(text),
            Task::Visit(RailroadNode::Terminal { text }) => {
                write!(&mut out, "──[ {text} ]──").expect("writing into String cannot fail");
            },
            Task::Visit(RailroadNode::NonTerminal { text }) => {
                write!(&mut out, "──⟨ {text} ⟩──").expect("writing into String cannot fail");
            },
            Task::Visit(RailroadNode::Sequence { children }) => {
                tasks.extend(children.iter().rev().map(Task::Visit));
            },
            Task::Visit(RailroadNode::Choice { alternatives }) => {
                out.push_str("──┬──");
                tasks.push(Task::Text("\n  └──"));
                for (index, alternative) in alternatives.iter().enumerate().rev() {
                    tasks.push(Task::Text("──"));
                    tasks.push(Task::Visit(alternative));
                    if index > 0 {
                        tasks.push(Task::Text("\n  ├──"));
                    }
                }
            },
            Task::Visit(RailroadNode::Optional { inner }) => {
                out.push_str("──┬──");
                tasks.push(Task::Text("──┬──\n  └──────────────┘"));
                tasks.push(Task::Visit(inner));
            },
            Task::Visit(RailroadNode::Repeat { element, separator }) => {
                out.push_str("──↻ ");
                tasks.push(Task::Text(" ↻──"));
                if let Some(separator) = separator {
                    tasks.push(Task::Visit(separator));
                }
                tasks.push(Task::Text(" "));
                tasks.push(Task::Visit(element));
            },
            Task::Visit(RailroadNode::Empty) => out.push_str("──ε──"),
        }
    }
    out
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
        let svg = diagram_to_svg(&category, &diagram.root);
        rendered.insert(category, svg);
    }
    rendered
}

/// Wrap a node's emitted SVG fragment in a minimal standalone `<svg>` document.
#[cfg(feature = "railroad-diagrams")]
pub fn diagram_to_svg(category: &str, node: &RailroadNode) -> String {
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
    struct Rendered {
        end_x: u32,
        max_y: u32,
    }

    enum Task<'node> {
        Visit {
            node: &'node RailroadNode,
            start_x: u32,
            y: u32,
            max_y: u32,
        },
        SequenceNext {
            children: &'node [RailroadNode],
            index: usize,
            cursor_x: u32,
            y: u32,
            max_y: u32,
        },
        SequenceAfter {
            children: &'node [RailroadNode],
            next_index: usize,
            y: u32,
        },
        ChoiceNext {
            alternatives: &'node [RailroadNode],
            index: usize,
            start_x: u32,
            widest: u32,
            y: u32,
            max_y: u32,
        },
        ChoiceAfter {
            alternatives: &'node [RailroadNode],
            next_index: usize,
            start_x: u32,
            widest: u32,
            y: u32,
        },
        OptionalFinish {
            start_x: u32,
            y: u32,
        },
        RepeatAfterElement {
            start_x: u32,
            y: u32,
            separator: Option<&'node RailroadNode>,
        },
        RepeatFinish {
            start_x: u32,
            y: u32,
            element: Rendered,
        },
    }

    fn finish_repeat(out: &mut String, rendered: Rendered, start_x: u32, y: u32) -> Rendered {
        out.push_str(&format!(
            "  <path d=\"M{end} {arc_y} q -{half} 18 -{span} 0\" \
             fill=\"none\" stroke=\"#3366cc\"/>\n",
            end = rendered.end_x,
            arc_y = y + 22,
            half = (rendered.end_x - start_x) / 2,
            span = rendered.end_x - start_x,
        ));
        rendered
    }

    let mut tasks = vec![Task::Visit {
        node,
        start_x: *cursor_x,
        y,
        max_y: *max_y,
    }];
    let mut values = Vec::new();
    let mut out = String::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit { node, start_x, y, max_y } => match node {
                RailroadNode::Terminal { text } | RailroadNode::NonTerminal { text } => {
                    let mut end_x = start_x;
                    let mut leaf_max_y = max_y;
                    let terminal = matches!(node, RailroadNode::Terminal { .. });
                    let fragment = svg_box(text, &mut end_x, y, &mut leaf_max_y, terminal);
                    out.push_str(&fragment);
                    values.push(Rendered { end_x, max_y: leaf_max_y });
                },
                RailroadNode::Empty => {
                    let mut end_x = start_x;
                    let mut leaf_max_y = max_y;
                    let fragment = svg_box("ε", &mut end_x, y, &mut leaf_max_y, true);
                    out.push_str(&fragment);
                    values.push(Rendered { end_x, max_y: leaf_max_y });
                },
                RailroadNode::Sequence { children } => tasks.push(Task::SequenceNext {
                    children,
                    index: 0,
                    cursor_x: start_x,
                    y,
                    max_y,
                }),
                RailroadNode::Choice { alternatives } => tasks.push(Task::ChoiceNext {
                    alternatives,
                    index: 0,
                    start_x,
                    widest: start_x,
                    y,
                    max_y,
                }),
                RailroadNode::Optional { inner } => {
                    tasks.push(Task::OptionalFinish { start_x, y });
                    tasks.push(Task::Visit { node: inner, start_x, y, max_y });
                },
                RailroadNode::Repeat { element, separator } => {
                    tasks.push(Task::RepeatAfterElement {
                        start_x,
                        y,
                        separator: separator.as_deref(),
                    });
                    tasks.push(Task::Visit { node: element, start_x, y, max_y });
                },
            },
            Task::SequenceNext { children, index, cursor_x, y, max_y } => {
                if let Some(child) = children.get(index) {
                    tasks.push(Task::SequenceAfter { children, next_index: index + 1, y });
                    tasks.push(Task::Visit { node: child, start_x: cursor_x, y, max_y });
                } else {
                    values.push(Rendered { end_x: cursor_x, max_y });
                }
            },
            Task::SequenceAfter { children, next_index, y } => {
                let child = values.pop().expect("railroad SVG sequence lost a child");
                tasks.push(Task::SequenceNext {
                    children,
                    index: next_index,
                    cursor_x: child.end_x,
                    y,
                    max_y: child.max_y,
                });
            },
            Task::ChoiceNext {
                alternatives,
                index,
                start_x,
                widest,
                y,
                max_y,
            } => {
                if let Some(alternative) = alternatives.get(index) {
                    tasks.push(Task::ChoiceAfter {
                        alternatives,
                        next_index: index + 1,
                        start_x,
                        widest,
                        y,
                    });
                    tasks.push(Task::Visit {
                        node: alternative,
                        start_x,
                        y: y + (index as u32) * 50,
                        max_y,
                    });
                } else {
                    values.push(Rendered { end_x: widest, max_y });
                }
            },
            Task::ChoiceAfter {
                alternatives,
                next_index,
                start_x,
                widest,
                y,
            } => {
                let alternative = values
                    .pop()
                    .expect("railroad SVG choice lost an alternative");
                tasks.push(Task::ChoiceNext {
                    alternatives,
                    index: next_index,
                    start_x,
                    widest: widest.max(alternative.end_x),
                    y,
                    max_y: alternative.max_y,
                });
            },
            Task::OptionalFinish { start_x, y } => {
                let inner = values.pop().expect("railroad SVG optional lost its child");
                out.push_str(&format!(
                    "  <path d=\"M{start_x} {arc_y} q {half} -18 {span} 0\" \
                     fill=\"none\" stroke=\"#888888\"/>\n",
                    arc_y = y - 2,
                    half = (inner.end_x - start_x) / 2,
                    span = inner.end_x - start_x,
                ));
                values.push(inner);
            },
            Task::RepeatAfterElement { start_x, y, separator } => {
                let element = values.pop().expect("railroad SVG repeat lost its element");
                if let Some(separator) = separator {
                    let separator_start = element.end_x;
                    let separator_max_y = element.max_y;
                    tasks.push(Task::RepeatFinish { start_x, y, element });
                    tasks.push(Task::Visit {
                        node: separator,
                        start_x: separator_start,
                        y,
                        max_y: separator_max_y,
                    });
                } else {
                    values.push(finish_repeat(&mut out, element, start_x, y));
                }
            },
            Task::RepeatFinish { start_x, y, mut element } => {
                let separator = values
                    .pop()
                    .expect("railroad SVG repeat lost its separator");
                element.end_x = separator.end_x;
                element.max_y = separator.max_y;
                values.push(finish_repeat(&mut out, element, start_x, y));
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    let rendered = values
        .pop()
        .expect("railroad SVG traversal produced no result");
    *cursor_x = rendered.end_x;
    *max_y = rendered.max_y;
    out
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
                    shares_level_with_previous: false,
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
                    shares_level_with_previous: false,
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
