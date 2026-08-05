//! Heap-backed lifecycle operations for recursive railroad-diagram trees.

use super::RailroadNode;
use std::fmt;

enum CloneTask<'node> {
    Visit(&'node RailroadNode),
    Sequence { base: usize, len: usize },
    Choice { base: usize, len: usize },
    Optional,
    Repeat { has_separator: bool },
}

impl Clone for RailroadNode {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(RailroadNode::Terminal { text }) => {
                    values.push(RailroadNode::Terminal { text: text.clone() });
                },
                CloneTask::Visit(RailroadNode::NonTerminal { text }) => {
                    values.push(RailroadNode::NonTerminal { text: text.clone() });
                },
                CloneTask::Visit(RailroadNode::Sequence { children }) => {
                    tasks.push(CloneTask::Sequence { base: values.len(), len: children.len() });
                    tasks.extend(children.iter().rev().map(CloneTask::Visit));
                },
                CloneTask::Visit(RailroadNode::Choice { alternatives }) => {
                    tasks.push(CloneTask::Choice {
                        base: values.len(),
                        len: alternatives.len(),
                    });
                    tasks.extend(alternatives.iter().rev().map(CloneTask::Visit));
                },
                CloneTask::Visit(RailroadNode::Optional { inner }) => {
                    tasks.push(CloneTask::Optional);
                    tasks.push(CloneTask::Visit(inner));
                },
                CloneTask::Visit(RailroadNode::Repeat { element, separator }) => {
                    tasks.push(CloneTask::Repeat { has_separator: separator.is_some() });
                    if let Some(separator) = separator {
                        tasks.push(CloneTask::Visit(separator));
                    }
                    tasks.push(CloneTask::Visit(element));
                },
                CloneTask::Visit(RailroadNode::Empty) => values.push(RailroadNode::Empty),
                CloneTask::Sequence { base, len } => {
                    debug_assert_eq!(values.len(), base + len);
                    let children = values.drain(base..).collect();
                    values.push(RailroadNode::Sequence { children });
                },
                CloneTask::Choice { base, len } => {
                    debug_assert_eq!(values.len(), base + len);
                    let alternatives = values.drain(base..).collect();
                    values.push(RailroadNode::Choice { alternatives });
                },
                CloneTask::Optional => {
                    let inner = values.pop().expect("railroad clone lost optional child");
                    values.push(RailroadNode::Optional { inner: Box::new(inner) });
                },
                CloneTask::Repeat { has_separator } => {
                    let separator = has_separator
                        .then(|| Box::new(values.pop().expect("railroad clone lost separator")));
                    let element =
                        Box::new(values.pop().expect("railroad clone lost repeat element"));
                    values.push(RailroadNode::Repeat { element, separator });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("railroad clone produced no node")
    }
}

fn take_children(node: &mut RailroadNode, work: &mut Vec<RailroadNode>) {
    match node {
        RailroadNode::Sequence { children } => work.extend(std::mem::take(children)),
        RailroadNode::Choice { alternatives } => work.extend(std::mem::take(alternatives)),
        RailroadNode::Optional { inner } => {
            work.push(*std::mem::replace(inner, Box::new(RailroadNode::Empty)));
        },
        RailroadNode::Repeat { element, separator } => {
            work.push(*std::mem::replace(element, Box::new(RailroadNode::Empty)));
            if let Some(separator) = separator.take() {
                work.push(*separator);
            }
        },
        RailroadNode::Terminal { .. } | RailroadNode::NonTerminal { .. } | RailroadNode::Empty => {
        },
    }
}

impl Drop for RailroadNode {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut node) = work.pop() {
            take_children(&mut node, &mut work);
        }
    }
}

enum DebugTask<'node> {
    Visit(&'node RailroadNode),
    Text(&'static str),
}

fn push_list<'node>(
    tasks: &mut Vec<DebugTask<'node>>,
    nodes: &'node [RailroadNode],
    prefix: &'static str,
) {
    tasks.push(DebugTask::Text("] }"));
    for (index, node) in nodes.iter().enumerate().rev() {
        tasks.push(DebugTask::Visit(node));
        if index > 0 {
            tasks.push(DebugTask::Text(", "));
        }
    }
    tasks.push(DebugTask::Text(prefix));
}

impl fmt::Debug for RailroadNode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(RailroadNode::Terminal { text }) => {
                    write!(formatter, "Terminal {{ text: {text:?} }}")?;
                },
                DebugTask::Visit(RailroadNode::NonTerminal { text }) => {
                    write!(formatter, "NonTerminal {{ text: {text:?} }}")?;
                },
                DebugTask::Visit(RailroadNode::Sequence { children }) => {
                    push_list(&mut tasks, children, "Sequence { children: [");
                },
                DebugTask::Visit(RailroadNode::Choice { alternatives }) => {
                    push_list(&mut tasks, alternatives, "Choice { alternatives: [");
                },
                DebugTask::Visit(RailroadNode::Optional { inner }) => {
                    tasks.push(DebugTask::Text(" }"));
                    tasks.push(DebugTask::Visit(inner));
                    tasks.push(DebugTask::Text("Optional { inner: "));
                },
                DebugTask::Visit(RailroadNode::Repeat { element, separator }) => {
                    tasks.push(DebugTask::Text(" }"));
                    match separator {
                        Some(separator) => {
                            tasks.push(DebugTask::Text(")"));
                            tasks.push(DebugTask::Visit(separator));
                            tasks.push(DebugTask::Text("Some("));
                        },
                        None => tasks.push(DebugTask::Text("None")),
                    }
                    tasks.push(DebugTask::Text(", separator: "));
                    tasks.push(DebugTask::Visit(element));
                    tasks.push(DebugTask::Text("Repeat { element: "));
                },
                DebugTask::Visit(RailroadNode::Empty) => formatter.write_str("Empty")?,
            }
        }
        Ok(())
    }
}
