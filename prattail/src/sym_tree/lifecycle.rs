//! Heap-backed lifecycle machines for symbolic terms and tree predicates.

use super::{SymTerm, TreePred};
use std::fmt;
use std::hash::{Hash, Hasher};

enum TermCloneTask<'term, D> {
    Visit(&'term SymTerm<D>),
    Build {
        constructor: &'term str,
        payload: &'term Option<D>,
        child_count: usize,
    },
}

impl<D: Clone> Clone for SymTerm<D> {
    fn clone(&self) -> Self {
        let mut tasks = vec![TermCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                TermCloneTask::Visit(term) => {
                    tasks.push(TermCloneTask::Build {
                        constructor: &term.constructor,
                        payload: &term.payload,
                        child_count: term.children.len(),
                    });
                    for child in term.children.iter().rev() {
                        tasks.push(TermCloneTask::Visit(child));
                    }
                },
                TermCloneTask::Build { constructor, payload, child_count } => {
                    let child_start = values
                        .len()
                        .checked_sub(child_count)
                        .expect("SymTerm clone lost children");
                    let children = values.split_off(child_start);
                    values.push(SymTerm {
                        constructor: constructor.to_string(),
                        payload: payload.clone(),
                        children,
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("SymTerm clone produced no value")
    }
}

impl<D: PartialEq> PartialEq for SymTerm<D> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            if left.constructor != right.constructor
                || left.payload != right.payload
                || left.children.len() != right.children.len()
            {
                return false;
            }
            work.extend(left.children.iter().zip(&right.children));
        }
        true
    }
}

impl<D: Eq> Eq for SymTerm<D> {}

impl<D: Hash> Hash for SymTerm<D> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(term) = work.pop() {
            term.constructor.hash(state);
            term.payload.hash(state);
            term.children.len().hash(state);
            work.extend(term.children.iter().rev());
        }
    }
}

impl<D> Drop for SymTerm<D> {
    fn drop(&mut self) {
        let mut work = std::mem::take(&mut self.children);
        while let Some(mut term) = work.pop() {
            work.append(&mut term.children);
        }
    }
}

enum TermDebugTask<'term, D> {
    Visit(&'term SymTerm<D>),
    Text(&'static str),
}

impl<D: fmt::Debug> fmt::Debug for SymTerm<D> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![TermDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                TermDebugTask::Text(text) => formatter.write_str(text)?,
                TermDebugTask::Visit(term) => {
                    write!(
                        formatter,
                        "SymTerm {{ constructor: {:?}, payload: {:?}, children: [",
                        term.constructor, term.payload
                    )?;
                    tasks.push(TermDebugTask::Text("] }"));
                    for (index, child) in term.children.iter().enumerate().rev() {
                        tasks.push(TermDebugTask::Visit(child));
                        if index > 0 {
                            tasks.push(TermDebugTask::Text(", "));
                        }
                    }
                },
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum TreeBinaryKind {
    And,
    Or,
}

enum TreeCloneTask<'pred, P> {
    Visit(&'pred TreePred<P>),
    Node {
        constructor: &'pred str,
        payload_guard: &'pred Option<P>,
        child_count: usize,
    },
    Binary(TreeBinaryKind),
    Not,
}

impl<P: Clone> Clone for TreePred<P> {
    fn clone(&self) -> Self {
        let mut tasks = vec![TreeCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                TreeCloneTask::Visit(TreePred::True) => values.push(TreePred::True),
                TreeCloneTask::Visit(TreePred::False) => values.push(TreePred::False),
                TreeCloneTask::Visit(TreePred::Wild) => values.push(TreePred::Wild),
                TreeCloneTask::Visit(TreePred::Node { constructor, payload_guard, children }) => {
                    tasks.push(TreeCloneTask::Node {
                        constructor,
                        payload_guard,
                        child_count: children.len(),
                    });
                    for child in children.iter().rev() {
                        tasks.push(TreeCloneTask::Visit(child));
                    }
                },
                TreeCloneTask::Visit(TreePred::Not(body)) => {
                    tasks.push(TreeCloneTask::Not);
                    tasks.push(TreeCloneTask::Visit(body));
                },
                TreeCloneTask::Visit(TreePred::And(left, right)) => {
                    push_tree_clone_binary(&mut tasks, TreeBinaryKind::And, left, right);
                },
                TreeCloneTask::Visit(TreePred::Or(left, right)) => {
                    push_tree_clone_binary(&mut tasks, TreeBinaryKind::Or, left, right);
                },
                TreeCloneTask::Node { constructor, payload_guard, child_count } => {
                    let child_start = values
                        .len()
                        .checked_sub(child_count)
                        .expect("TreePred clone lost node children");
                    let children = values.split_off(child_start);
                    values.push(TreePred::Node {
                        constructor: constructor.to_string(),
                        payload_guard: payload_guard.clone(),
                        children,
                    });
                },
                TreeCloneTask::Not => {
                    let body = values.pop().expect("TreePred clone lost negated body");
                    values.push(TreePred::Not(Box::new(body)));
                },
                TreeCloneTask::Binary(kind) => {
                    let right = values.pop().expect("TreePred clone lost right body");
                    let left = values.pop().expect("TreePred clone lost left body");
                    values.push(match kind {
                        TreeBinaryKind::And => TreePred::And(Box::new(left), Box::new(right)),
                        TreeBinaryKind::Or => TreePred::Or(Box::new(left), Box::new(right)),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("TreePred clone produced no value")
    }
}

fn push_tree_clone_binary<'pred, P>(
    tasks: &mut Vec<TreeCloneTask<'pred, P>>,
    kind: TreeBinaryKind,
    left: &'pred TreePred<P>,
    right: &'pred TreePred<P>,
) {
    tasks.push(TreeCloneTask::Binary(kind));
    tasks.push(TreeCloneTask::Visit(right));
    tasks.push(TreeCloneTask::Visit(left));
}

impl<P: PartialEq> PartialEq for TreePred<P> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (TreePred::True, TreePred::True)
                | (TreePred::False, TreePred::False)
                | (TreePred::Wild, TreePred::Wild) => {},
                (
                    TreePred::Node {
                        constructor: ac,
                        payload_guard: ap,
                        children: ach,
                    },
                    TreePred::Node {
                        constructor: bc,
                        payload_guard: bp,
                        children: bch,
                    },
                ) if ac == bc && ap == bp && ach.len() == bch.len() => {
                    work.extend(ach.iter().zip(bch));
                },
                (TreePred::Not(a), TreePred::Not(b)) => work.push((a, b)),
                (TreePred::And(al, ar), TreePred::And(bl, br))
                | (TreePred::Or(al, ar), TreePred::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl<P: Eq> Eq for TreePred<P> {}

impl<P: Hash> Hash for TreePred<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(predicate) = work.pop() {
            std::mem::discriminant(predicate).hash(state);
            match predicate {
                TreePred::True | TreePred::False | TreePred::Wild => {},
                TreePred::Node { constructor, payload_guard, children } => {
                    constructor.hash(state);
                    payload_guard.hash(state);
                    children.len().hash(state);
                    work.extend(children.iter().rev());
                },
                TreePred::Not(body) => work.push(body),
                TreePred::And(left, right) | TreePred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_tree_children<P>(predicate: &mut TreePred<P>, work: &mut Vec<TreePred<P>>) {
    let take = |child: &mut Box<TreePred<P>>| *std::mem::replace(child, Box::new(TreePred::True));
    match predicate {
        TreePred::Node { children, .. } => work.append(children),
        TreePred::Not(body) => work.push(take(body)),
        TreePred::And(left, right) | TreePred::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        TreePred::True | TreePred::False | TreePred::Wild => {},
    }
}

impl<P> Drop for TreePred<P> {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_tree_children(self, &mut work);
        while let Some(mut predicate) = work.pop() {
            take_tree_children(&mut predicate, &mut work);
        }
    }
}

enum TreeDebugTask<'pred, P> {
    Visit(&'pred TreePred<P>),
    Text(&'static str),
}

impl<P: fmt::Debug> fmt::Debug for TreePred<P> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![TreeDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                TreeDebugTask::Text(text) => formatter.write_str(text)?,
                TreeDebugTask::Visit(TreePred::True) => formatter.write_str("True")?,
                TreeDebugTask::Visit(TreePred::False) => formatter.write_str("False")?,
                TreeDebugTask::Visit(TreePred::Wild) => formatter.write_str("Wild")?,
                TreeDebugTask::Visit(TreePred::Node { constructor, payload_guard, children }) => {
                    write!(
                        formatter,
                        "Node {{ constructor: {constructor:?}, payload_guard: {payload_guard:?}, children: ["
                    )?;
                    tasks.push(TreeDebugTask::Text("] }"));
                    for (index, child) in children.iter().enumerate().rev() {
                        tasks.push(TreeDebugTask::Visit(child));
                        if index > 0 {
                            tasks.push(TreeDebugTask::Text(", "));
                        }
                    }
                },
                TreeDebugTask::Visit(TreePred::Not(body)) => {
                    push_tree_debug_unary(&mut tasks, "Not(", body);
                },
                TreeDebugTask::Visit(TreePred::And(left, right)) => {
                    push_tree_debug_binary(&mut tasks, "And(", left, right);
                },
                TreeDebugTask::Visit(TreePred::Or(left, right)) => {
                    push_tree_debug_binary(&mut tasks, "Or(", left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_tree_debug_unary<'pred, P>(
    tasks: &mut Vec<TreeDebugTask<'pred, P>>,
    prefix: &'static str,
    body: &'pred TreePred<P>,
) {
    tasks.push(TreeDebugTask::Text(")"));
    tasks.push(TreeDebugTask::Visit(body));
    tasks.push(TreeDebugTask::Text(prefix));
}

fn push_tree_debug_binary<'pred, P>(
    tasks: &mut Vec<TreeDebugTask<'pred, P>>,
    prefix: &'static str,
    left: &'pred TreePred<P>,
    right: &'pred TreePred<P>,
) {
    tasks.push(TreeDebugTask::Text(")"));
    tasks.push(TreeDebugTask::Visit(right));
    tasks.push(TreeDebugTask::Text(", "));
    tasks.push(TreeDebugTask::Visit(left));
    tasks.push(TreeDebugTask::Text(prefix));
}
