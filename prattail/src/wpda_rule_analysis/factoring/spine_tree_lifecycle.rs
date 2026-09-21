//! Stack-safe lifecycle operations for shared-prefix spine tries.

use super::SpineTree;
use std::fmt;

fn take_children(tree: &mut SpineTree, work: &mut Vec<SpineTree>) {
    if let SpineTree::Interior { children, .. } = tree {
        work.extend(std::mem::take(children));
    }
}

impl Drop for SpineTree {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut tree) = work.pop() {
            take_children(&mut tree, &mut work);
        }
    }
}

enum DebugTask<'tree> {
    Visit(&'tree SpineTree),
    Text(&'static str),
}

impl fmt::Debug for SpineTree {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(SpineTree::Leaf { item, member }) => {
                    write!(formatter, "Leaf {{ item: {item:?}, member: {member:?} }}")?;
                },
                DebugTask::Visit(SpineTree::Interior { item, children }) => {
                    tasks.push(DebugTask::Text("] }"));
                    for (index, child) in children.iter().enumerate().rev() {
                        tasks.push(DebugTask::Visit(child));
                        if index > 0 {
                            tasks.push(DebugTask::Text(", "));
                        }
                    }
                    write!(formatter, "Interior {{ item: {item:?}, children: [")?;
                },
            }
        }
        Ok(())
    }
}
