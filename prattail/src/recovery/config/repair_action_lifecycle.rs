//! Heap-backed lifecycle and formatting for nested recovery actions.

use super::RepairAction;
use std::fmt;

enum CloneTask<'action> {
    Visit(&'action RepairAction),
    Composite { base: usize, len: usize },
}

impl Clone for RepairAction {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(RepairAction::SkipToSync { skip_count, sync_token }) => values
                    .push(RepairAction::SkipToSync {
                        skip_count: *skip_count,
                        sync_token: *sync_token,
                    }),
                CloneTask::Visit(RepairAction::InsertToken { token }) => {
                    values.push(RepairAction::InsertToken { token: *token })
                },
                CloneTask::Visit(RepairAction::DeleteToken) => {
                    values.push(RepairAction::DeleteToken)
                },
                CloneTask::Visit(RepairAction::SubstituteToken { replacement }) => {
                    values.push(RepairAction::SubstituteToken { replacement: *replacement })
                },
                CloneTask::Visit(RepairAction::SwapTokens { pos_a, pos_b }) => {
                    values.push(RepairAction::SwapTokens { pos_a: *pos_a, pos_b: *pos_b })
                },
                CloneTask::Visit(RepairAction::Composite { steps }) => {
                    tasks.push(CloneTask::Composite { base: values.len(), len: steps.len() });
                    tasks.extend(steps.iter().rev().map(CloneTask::Visit));
                },
                CloneTask::Visit(RepairAction::CategorySwitch { from_category, to_category }) => {
                    values.push(RepairAction::CategorySwitch {
                        from_category: from_category.clone(),
                        to_category: to_category.clone(),
                    })
                },
                CloneTask::Composite { base, len } => {
                    debug_assert_eq!(values.len(), base + len);
                    let steps = values.drain(base..).collect();
                    values.push(RepairAction::Composite { steps });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("repair-action clone produced no action")
    }
}

impl PartialEq for RepairAction {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (
                    RepairAction::SkipToSync { skip_count: ac, sync_token: at },
                    RepairAction::SkipToSync { skip_count: bc, sync_token: bt },
                ) if ac == bc && at == bt => {},
                (
                    RepairAction::InsertToken { token: a },
                    RepairAction::InsertToken { token: b },
                ) if a == b => {},
                (RepairAction::DeleteToken, RepairAction::DeleteToken) => {},
                (
                    RepairAction::SubstituteToken { replacement: a },
                    RepairAction::SubstituteToken { replacement: b },
                ) if a == b => {},
                (
                    RepairAction::SwapTokens { pos_a: aa, pos_b: ab },
                    RepairAction::SwapTokens { pos_a: ba, pos_b: bb },
                ) if aa == ba && ab == bb => {},
                (RepairAction::Composite { steps: a }, RepairAction::Composite { steps: b })
                    if a.len() == b.len() =>
                {
                    work.extend(a.iter().zip(b).rev());
                },
                (
                    RepairAction::CategorySwitch { from_category: af, to_category: at },
                    RepairAction::CategorySwitch { from_category: bf, to_category: bt },
                ) if af == bf && at == bt => {},
                _ => return false,
            }
        }
        true
    }
}

impl Eq for RepairAction {}

fn take_children(action: &mut RepairAction, work: &mut Vec<RepairAction>) {
    if let RepairAction::Composite { steps } = action {
        work.extend(std::mem::take(steps));
    }
}

impl Drop for RepairAction {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut action) = work.pop() {
            take_children(&mut action, &mut work);
        }
    }
}

impl fmt::Display for RepairAction {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'action> {
            Visit(&'action RepairAction),
            Separator,
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Separator => formatter.write_str(", ")?,
                Task::Visit(RepairAction::Composite { steps }) => {
                    for (index, step) in steps.iter().enumerate().rev() {
                        tasks.push(Task::Visit(step));
                        if index > 0 {
                            tasks.push(Task::Separator);
                        }
                    }
                },
                Task::Visit(RepairAction::SkipToSync { skip_count, sync_token }) => {
                    write!(formatter, "skip {skip_count} tokens to sync token {sync_token}")?;
                },
                Task::Visit(RepairAction::InsertToken { token }) => {
                    write!(formatter, "insert token {token}")?;
                },
                Task::Visit(RepairAction::DeleteToken) => formatter.write_str("delete token")?,
                Task::Visit(RepairAction::SubstituteToken { replacement }) => {
                    write!(formatter, "substitute with token {replacement}")?;
                },
                Task::Visit(RepairAction::SwapTokens { pos_a, pos_b }) => {
                    write!(formatter, "swap tokens at positions {pos_a} and {pos_b}")?;
                },
                Task::Visit(RepairAction::CategorySwitch { from_category, to_category }) => {
                    write!(formatter, "switch {from_category} → {to_category}")?;
                },
            }
        }
        Ok(())
    }
}

enum DebugTask<'action> {
    Visit(&'action RepairAction),
    Text(&'static str),
}

impl fmt::Debug for RepairAction {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(RepairAction::SkipToSync { skip_count, sync_token }) => write!(
                    formatter,
                    "SkipToSync {{ skip_count: {skip_count:?}, sync_token: {sync_token:?} }}"
                )?,
                DebugTask::Visit(RepairAction::InsertToken { token }) => {
                    write!(formatter, "InsertToken {{ token: {token:?} }}")?
                },
                DebugTask::Visit(RepairAction::DeleteToken) => {
                    formatter.write_str("DeleteToken")?
                },
                DebugTask::Visit(RepairAction::SubstituteToken { replacement }) => write!(
                    formatter,
                    "SubstituteToken {{ replacement: {replacement:?} }}"
                )?,
                DebugTask::Visit(RepairAction::SwapTokens { pos_a, pos_b }) => write!(
                    formatter,
                    "SwapTokens {{ pos_a: {pos_a:?}, pos_b: {pos_b:?} }}"
                )?,
                DebugTask::Visit(RepairAction::Composite { steps }) => {
                    tasks.push(DebugTask::Text("] }"));
                    for (index, step) in steps.iter().enumerate().rev() {
                        tasks.push(DebugTask::Visit(step));
                        if index > 0 {
                            tasks.push(DebugTask::Text(", "));
                        }
                    }
                    tasks.push(DebugTask::Text("Composite { steps: ["));
                },
                DebugTask::Visit(RepairAction::CategorySwitch {
                    from_category,
                    to_category,
                }) => write!(
                    formatter,
                    "CategorySwitch {{ from_category: {from_category:?}, to_category: {to_category:?} }}"
                )?,
            }
        }
        Ok(())
    }
}
