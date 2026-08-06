//! Heap-backed lifecycle and debug-formatting machines for KAT models.

use super::{BooleanTest, KatExpr};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

#[derive(Clone, Copy)]
enum BoolUnary {
    Not,
}

#[derive(Clone, Copy)]
enum BoolBinary {
    And,
    Or,
}

enum BoolCloneTask<'test> {
    Visit(&'test BooleanTest),
    Unary(BoolUnary),
    Binary(BoolBinary),
}

impl Clone for BooleanTest {
    fn clone(&self) -> Self {
        let mut tasks = vec![BoolCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                BoolCloneTask::Visit(BooleanTest::True) => values.push(BooleanTest::True),
                BoolCloneTask::Visit(BooleanTest::False) => values.push(BooleanTest::False),
                BoolCloneTask::Visit(BooleanTest::Atom(name)) => {
                    values.push(BooleanTest::Atom(name.clone()));
                },
                BoolCloneTask::Visit(BooleanTest::Not(body)) => {
                    tasks.push(BoolCloneTask::Unary(BoolUnary::Not));
                    tasks.push(BoolCloneTask::Visit(body));
                },
                BoolCloneTask::Visit(BooleanTest::And(left, right)) => {
                    push_bool_clone_binary(&mut tasks, BoolBinary::And, left, right);
                },
                BoolCloneTask::Visit(BooleanTest::Or(left, right)) => {
                    push_bool_clone_binary(&mut tasks, BoolBinary::Or, left, right);
                },
                BoolCloneTask::Unary(BoolUnary::Not) => {
                    let body = values.pop().expect("BooleanTest clone lost unary body");
                    values.push(BooleanTest::Not(Box::new(body)));
                },
                BoolCloneTask::Binary(kind) => {
                    let right = Box::new(values.pop().expect("BooleanTest clone lost right body"));
                    let left = Box::new(values.pop().expect("BooleanTest clone lost left body"));
                    values.push(match kind {
                        BoolBinary::And => BooleanTest::And(left, right),
                        BoolBinary::Or => BooleanTest::Or(left, right),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("BooleanTest clone produced no value")
    }
}

fn push_bool_clone_binary<'test>(
    tasks: &mut Vec<BoolCloneTask<'test>>,
    kind: BoolBinary,
    left: &'test BooleanTest,
    right: &'test BooleanTest,
) {
    tasks.push(BoolCloneTask::Binary(kind));
    tasks.push(BoolCloneTask::Visit(right));
    tasks.push(BoolCloneTask::Visit(left));
}

impl PartialEq for BooleanTest {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (BooleanTest::True, BooleanTest::True)
                | (BooleanTest::False, BooleanTest::False) => {},
                (BooleanTest::Atom(a), BooleanTest::Atom(b)) if a == b => {},
                (BooleanTest::Not(a), BooleanTest::Not(b)) => work.push((a, b)),
                (BooleanTest::And(al, ar), BooleanTest::And(bl, br))
                | (BooleanTest::Or(al, ar), BooleanTest::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for BooleanTest {}

impl Hash for BooleanTest {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(test) = work.pop() {
            std::mem::discriminant(test).hash(state);
            match test {
                BooleanTest::True | BooleanTest::False => {},
                BooleanTest::Atom(name) => name.hash(state),
                BooleanTest::Not(body) => work.push(body),
                BooleanTest::And(left, right) | BooleanTest::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

fn take_bool_children(test: &mut BooleanTest, work: &mut Vec<BooleanTest>) {
    let take =
        |child: &mut Box<BooleanTest>| *std::mem::replace(child, Box::new(BooleanTest::True));
    match test {
        BooleanTest::Not(body) => work.push(take(body)),
        BooleanTest::And(left, right) | BooleanTest::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        BooleanTest::True | BooleanTest::False | BooleanTest::Atom(_) => {},
    }
}

impl Drop for BooleanTest {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_bool_children(self, &mut work);
        while let Some(mut test) = work.pop() {
            take_bool_children(&mut test, &mut work);
        }
    }
}

enum BoolDebugTask<'test> {
    Visit(&'test BooleanTest),
    Text(&'static str),
}

impl fmt::Debug for BooleanTest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![BoolDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                BoolDebugTask::Text(text) => formatter.write_str(text)?,
                BoolDebugTask::Visit(BooleanTest::True) => formatter.write_str("True")?,
                BoolDebugTask::Visit(BooleanTest::False) => formatter.write_str("False")?,
                BoolDebugTask::Visit(BooleanTest::Atom(name)) => {
                    write!(formatter, "Atom({name:?})")?;
                },
                BoolDebugTask::Visit(BooleanTest::Not(body)) => {
                    push_bool_debug_unary(&mut tasks, "Not(", body);
                },
                BoolDebugTask::Visit(BooleanTest::And(left, right)) => {
                    push_bool_debug_binary(&mut tasks, "And(", left, right);
                },
                BoolDebugTask::Visit(BooleanTest::Or(left, right)) => {
                    push_bool_debug_binary(&mut tasks, "Or(", left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_bool_debug_unary<'test>(
    tasks: &mut Vec<BoolDebugTask<'test>>,
    prefix: &'static str,
    body: &'test BooleanTest,
) {
    tasks.push(BoolDebugTask::Text(")"));
    tasks.push(BoolDebugTask::Visit(body));
    tasks.push(BoolDebugTask::Text(prefix));
}

fn push_bool_debug_binary<'test>(
    tasks: &mut Vec<BoolDebugTask<'test>>,
    prefix: &'static str,
    left: &'test BooleanTest,
    right: &'test BooleanTest,
) {
    tasks.push(BoolDebugTask::Text(")"));
    tasks.push(BoolDebugTask::Visit(right));
    tasks.push(BoolDebugTask::Text(", "));
    tasks.push(BoolDebugTask::Visit(left));
    tasks.push(BoolDebugTask::Text(prefix));
}

impl PartialEq for KatExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (KatExpr::Zero, KatExpr::Zero) | (KatExpr::One, KatExpr::One) => {},
                (KatExpr::Test(a), KatExpr::Test(b)) if a == b => {},
                (KatExpr::Action(a), KatExpr::Action(b)) if a == b => {},
                (KatExpr::Seq(al, ar), KatExpr::Seq(bl, br))
                | (KatExpr::Alt(al, ar), KatExpr::Alt(bl, br)) => {
                    if !Arc::ptr_eq(ar, br) {
                        work.push((ar, br));
                    }
                    if !Arc::ptr_eq(al, bl) {
                        work.push((al, bl));
                    }
                },
                (KatExpr::Star(a), KatExpr::Star(b)) => {
                    if !Arc::ptr_eq(a, b) {
                        work.push((a, b));
                    }
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for KatExpr {}

impl Hash for KatExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(expr) = work.pop() {
            std::mem::discriminant(expr).hash(state);
            match expr {
                KatExpr::Zero | KatExpr::One => {},
                KatExpr::Test(test) => test.hash(state),
                KatExpr::Action(name) => name.hash(state),
                KatExpr::Seq(left, right) | KatExpr::Alt(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                KatExpr::Star(body) => work.push(body),
            }
        }
    }
}

fn take_kat_children(expr: &mut KatExpr, work: &mut Vec<Arc<KatExpr>>) {
    let take = |child: &mut Arc<KatExpr>| std::mem::replace(child, Arc::new(KatExpr::Zero));
    match expr {
        KatExpr::Seq(left, right) | KatExpr::Alt(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        KatExpr::Star(body) => work.push(take(body)),
        KatExpr::Zero | KatExpr::One | KatExpr::Test(_) | KatExpr::Action(_) => {},
    }
}

impl Drop for KatExpr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_kat_children(self, &mut work);
        while let Some(child) = work.pop() {
            if let Ok(mut child) = Arc::try_unwrap(child) {
                take_kat_children(&mut child, &mut work);
            }
        }
    }
}

enum KatDebugTask<'expr> {
    Visit(&'expr KatExpr),
    Text(&'static str),
}

impl fmt::Debug for KatExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![KatDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                KatDebugTask::Text(text) => formatter.write_str(text)?,
                KatDebugTask::Visit(KatExpr::Zero) => formatter.write_str("Zero")?,
                KatDebugTask::Visit(KatExpr::One) => formatter.write_str("One")?,
                KatDebugTask::Visit(KatExpr::Test(test)) => {
                    write!(formatter, "Test({test:?})")?;
                },
                KatDebugTask::Visit(KatExpr::Action(name)) => {
                    write!(formatter, "Action({name:?})")?;
                },
                KatDebugTask::Visit(KatExpr::Seq(left, right)) => {
                    push_kat_debug_binary(&mut tasks, "Seq(", left, right);
                },
                KatDebugTask::Visit(KatExpr::Alt(left, right)) => {
                    push_kat_debug_binary(&mut tasks, "Alt(", left, right);
                },
                KatDebugTask::Visit(KatExpr::Star(body)) => {
                    tasks.push(KatDebugTask::Text(")"));
                    tasks.push(KatDebugTask::Visit(body));
                    tasks.push(KatDebugTask::Text("Star("));
                },
            }
        }
        Ok(())
    }
}

fn push_kat_debug_binary<'expr>(
    tasks: &mut Vec<KatDebugTask<'expr>>,
    prefix: &'static str,
    left: &'expr KatExpr,
    right: &'expr KatExpr,
) {
    tasks.push(KatDebugTask::Text(")"));
    tasks.push(KatDebugTask::Visit(right));
    tasks.push(KatDebugTask::Text(", "));
    tasks.push(KatDebugTask::Visit(left));
    tasks.push(KatDebugTask::Text(prefix));
}
