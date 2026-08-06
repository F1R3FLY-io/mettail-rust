//! Heap-backed lifecycle machines for bag and map predicates.

use super::{BagPred, MapPred};
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy)]
enum BinaryKind {
    And,
    Or,
}

enum BagCloneTask<'pred, P> {
    Visit(&'pred BagPred<P>),
    Binary(BinaryKind),
    Not,
}

impl<P: Clone> Clone for BagPred<P> {
    fn clone(&self) -> Self {
        let mut tasks = vec![BagCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                BagCloneTask::Visit(BagPred::True) => values.push(BagPred::True),
                BagCloneTask::Visit(BagPred::False) => values.push(BagPred::False),
                BagCloneTask::Visit(BagPred::Count { class, lo, hi }) => {
                    values.push(BagPred::Count { class: class.clone(), lo: *lo, hi: *hi });
                },
                BagCloneTask::Visit(BagPred::Not(body)) => {
                    tasks.push(BagCloneTask::Not);
                    tasks.push(BagCloneTask::Visit(body));
                },
                BagCloneTask::Visit(BagPred::And(left, right)) => {
                    push_bag_clone_binary(&mut tasks, BinaryKind::And, left, right);
                },
                BagCloneTask::Visit(BagPred::Or(left, right)) => {
                    push_bag_clone_binary(&mut tasks, BinaryKind::Or, left, right);
                },
                BagCloneTask::Not => {
                    let body = values.pop().expect("BagPred clone lost negated body");
                    values.push(BagPred::Not(Box::new(body)));
                },
                BagCloneTask::Binary(kind) => {
                    let right = values.pop().expect("BagPred clone lost right body");
                    let left = values.pop().expect("BagPred clone lost left body");
                    values.push(match kind {
                        BinaryKind::And => BagPred::And(Box::new(left), Box::new(right)),
                        BinaryKind::Or => BagPred::Or(Box::new(left), Box::new(right)),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("BagPred clone produced no value")
    }
}

fn push_bag_clone_binary<'pred, P>(
    tasks: &mut Vec<BagCloneTask<'pred, P>>,
    kind: BinaryKind,
    left: &'pred BagPred<P>,
    right: &'pred BagPred<P>,
) {
    tasks.push(BagCloneTask::Binary(kind));
    tasks.push(BagCloneTask::Visit(right));
    tasks.push(BagCloneTask::Visit(left));
}

impl<P: PartialEq> PartialEq for BagPred<P> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (BagPred::True, BagPred::True) | (BagPred::False, BagPred::False) => {},
                (
                    BagPred::Count { class: ac, lo: al, hi: ah },
                    BagPred::Count { class: bc, lo: bl, hi: bh },
                ) if ac == bc && al == bl && ah == bh => {},
                (BagPred::Not(a), BagPred::Not(b)) => work.push((a, b)),
                (BagPred::And(al, ar), BagPred::And(bl, br))
                | (BagPred::Or(al, ar), BagPred::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl<P: Eq> Eq for BagPred<P> {}

impl<P: Hash> Hash for BagPred<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(predicate) = work.pop() {
            std::mem::discriminant(predicate).hash(state);
            match predicate {
                BagPred::True | BagPred::False => {},
                BagPred::Count { class, lo, hi } => {
                    class.hash(state);
                    lo.hash(state);
                    hi.hash(state);
                },
                BagPred::Not(body) => work.push(body),
                BagPred::And(left, right) | BagPred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_bag_children<P>(predicate: &mut BagPred<P>, work: &mut Vec<BagPred<P>>) {
    let take = |child: &mut Box<BagPred<P>>| *std::mem::replace(child, Box::new(BagPred::True));
    match predicate {
        BagPred::Not(body) => work.push(take(body)),
        BagPred::And(left, right) | BagPred::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        BagPred::True | BagPred::False | BagPred::Count { .. } => {},
    }
}

impl<P> Drop for BagPred<P> {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_bag_children(self, &mut work);
        while let Some(mut predicate) = work.pop() {
            take_bag_children(&mut predicate, &mut work);
        }
    }
}

enum BagDebugTask<'pred, P> {
    Visit(&'pred BagPred<P>),
    Text(&'static str),
}

impl<P: fmt::Debug> fmt::Debug for BagPred<P> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![BagDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                BagDebugTask::Text(text) => formatter.write_str(text)?,
                BagDebugTask::Visit(BagPred::True) => formatter.write_str("True")?,
                BagDebugTask::Visit(BagPred::False) => formatter.write_str("False")?,
                BagDebugTask::Visit(BagPred::Count { class, lo, hi }) => {
                    write!(formatter, "Count {{ class: {class:?}, lo: {lo:?}, hi: {hi:?} }}")?;
                },
                BagDebugTask::Visit(BagPred::Not(body)) => {
                    push_bag_debug_unary(&mut tasks, "Not(", body);
                },
                BagDebugTask::Visit(BagPred::And(left, right)) => {
                    push_bag_debug_binary(&mut tasks, "And(", left, right);
                },
                BagDebugTask::Visit(BagPred::Or(left, right)) => {
                    push_bag_debug_binary(&mut tasks, "Or(", left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_bag_debug_unary<'pred, P>(
    tasks: &mut Vec<BagDebugTask<'pred, P>>,
    prefix: &'static str,
    body: &'pred BagPred<P>,
) {
    tasks.push(BagDebugTask::Text(")"));
    tasks.push(BagDebugTask::Visit(body));
    tasks.push(BagDebugTask::Text(prefix));
}

fn push_bag_debug_binary<'pred, P>(
    tasks: &mut Vec<BagDebugTask<'pred, P>>,
    prefix: &'static str,
    left: &'pred BagPred<P>,
    right: &'pred BagPred<P>,
) {
    tasks.push(BagDebugTask::Text(")"));
    tasks.push(BagDebugTask::Visit(right));
    tasks.push(BagDebugTask::Text(", "));
    tasks.push(BagDebugTask::Visit(left));
    tasks.push(BagDebugTask::Text(prefix));
}

enum MapCloneTask<'pred, KP, VP> {
    Visit(&'pred MapPred<KP, VP>),
    Binary(BinaryKind),
    Not,
}

impl<KP: Clone, VP: Clone> Clone for MapPred<KP, VP> {
    fn clone(&self) -> Self {
        let mut tasks = vec![MapCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                MapCloneTask::Visit(MapPred::True) => values.push(MapPred::True),
                MapCloneTask::Visit(MapPred::False) => values.push(MapPred::False),
                MapCloneTask::Visit(MapPred::CountEntries { key_class, val_class, lo, hi }) => {
                    values.push(MapPred::CountEntries {
                        key_class: key_class.clone(),
                        val_class: val_class.clone(),
                        lo: *lo,
                        hi: *hi,
                    });
                },
                MapCloneTask::Visit(MapPred::Not(body)) => {
                    tasks.push(MapCloneTask::Not);
                    tasks.push(MapCloneTask::Visit(body));
                },
                MapCloneTask::Visit(MapPred::And(left, right)) => {
                    push_map_clone_binary(&mut tasks, BinaryKind::And, left, right);
                },
                MapCloneTask::Visit(MapPred::Or(left, right)) => {
                    push_map_clone_binary(&mut tasks, BinaryKind::Or, left, right);
                },
                MapCloneTask::Not => {
                    let body = values.pop().expect("MapPred clone lost negated body");
                    values.push(MapPred::Not(Box::new(body)));
                },
                MapCloneTask::Binary(kind) => {
                    let right = values.pop().expect("MapPred clone lost right body");
                    let left = values.pop().expect("MapPred clone lost left body");
                    values.push(match kind {
                        BinaryKind::And => MapPred::And(Box::new(left), Box::new(right)),
                        BinaryKind::Or => MapPred::Or(Box::new(left), Box::new(right)),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("MapPred clone produced no value")
    }
}

fn push_map_clone_binary<'pred, KP, VP>(
    tasks: &mut Vec<MapCloneTask<'pred, KP, VP>>,
    kind: BinaryKind,
    left: &'pred MapPred<KP, VP>,
    right: &'pred MapPred<KP, VP>,
) {
    tasks.push(MapCloneTask::Binary(kind));
    tasks.push(MapCloneTask::Visit(right));
    tasks.push(MapCloneTask::Visit(left));
}

impl<KP: PartialEq, VP: PartialEq> PartialEq for MapPred<KP, VP> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (MapPred::True, MapPred::True) | (MapPred::False, MapPred::False) => {},
                (
                    MapPred::CountEntries {
                        key_class: ak,
                        val_class: av,
                        lo: al,
                        hi: ah,
                    },
                    MapPred::CountEntries {
                        key_class: bk,
                        val_class: bv,
                        lo: bl,
                        hi: bh,
                    },
                ) if ak == bk && av == bv && al == bl && ah == bh => {},
                (MapPred::Not(a), MapPred::Not(b)) => work.push((a, b)),
                (MapPred::And(al, ar), MapPred::And(bl, br))
                | (MapPred::Or(al, ar), MapPred::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl<KP: Eq, VP: Eq> Eq for MapPred<KP, VP> {}

impl<KP: Hash, VP: Hash> Hash for MapPred<KP, VP> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(predicate) = work.pop() {
            std::mem::discriminant(predicate).hash(state);
            match predicate {
                MapPred::True | MapPred::False => {},
                MapPred::CountEntries { key_class, val_class, lo, hi } => {
                    key_class.hash(state);
                    val_class.hash(state);
                    lo.hash(state);
                    hi.hash(state);
                },
                MapPred::Not(body) => work.push(body),
                MapPred::And(left, right) | MapPred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_map_children<KP, VP>(predicate: &mut MapPred<KP, VP>, work: &mut Vec<MapPred<KP, VP>>) {
    let take =
        |child: &mut Box<MapPred<KP, VP>>| *std::mem::replace(child, Box::new(MapPred::True));
    match predicate {
        MapPred::Not(body) => work.push(take(body)),
        MapPred::And(left, right) | MapPred::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        MapPred::True | MapPred::False | MapPred::CountEntries { .. } => {},
    }
}

impl<KP, VP> Drop for MapPred<KP, VP> {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_map_children(self, &mut work);
        while let Some(mut predicate) = work.pop() {
            take_map_children(&mut predicate, &mut work);
        }
    }
}

enum MapDebugTask<'pred, KP, VP> {
    Visit(&'pred MapPred<KP, VP>),
    Text(&'static str),
}

impl<KP: fmt::Debug, VP: fmt::Debug> fmt::Debug for MapPred<KP, VP> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![MapDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                MapDebugTask::Text(text) => formatter.write_str(text)?,
                MapDebugTask::Visit(MapPred::True) => formatter.write_str("True")?,
                MapDebugTask::Visit(MapPred::False) => formatter.write_str("False")?,
                MapDebugTask::Visit(MapPred::CountEntries { key_class, val_class, lo, hi }) => {
                    write!(
                        formatter,
                        "CountEntries {{ key_class: {key_class:?}, val_class: {val_class:?}, lo: {lo:?}, hi: {hi:?} }}"
                    )?;
                },
                MapDebugTask::Visit(MapPred::Not(body)) => {
                    push_map_debug_unary(&mut tasks, "Not(", body);
                },
                MapDebugTask::Visit(MapPred::And(left, right)) => {
                    push_map_debug_binary(&mut tasks, "And(", left, right);
                },
                MapDebugTask::Visit(MapPred::Or(left, right)) => {
                    push_map_debug_binary(&mut tasks, "Or(", left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_map_debug_unary<'pred, KP, VP>(
    tasks: &mut Vec<MapDebugTask<'pred, KP, VP>>,
    prefix: &'static str,
    body: &'pred MapPred<KP, VP>,
) {
    tasks.push(MapDebugTask::Text(")"));
    tasks.push(MapDebugTask::Visit(body));
    tasks.push(MapDebugTask::Text(prefix));
}

fn push_map_debug_binary<'pred, KP, VP>(
    tasks: &mut Vec<MapDebugTask<'pred, KP, VP>>,
    prefix: &'static str,
    left: &'pred MapPred<KP, VP>,
    right: &'pred MapPred<KP, VP>,
) {
    tasks.push(MapDebugTask::Text(")"));
    tasks.push(MapDebugTask::Visit(right));
    tasks.push(MapDebugTask::Text(", "));
    tasks.push(MapDebugTask::Visit(left));
    tasks.push(MapDebugTask::Text(prefix));
}
