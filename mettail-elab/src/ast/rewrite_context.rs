use super::Ident;
use crate::canonical::{RhoValue, ValueDecodeError};
use crate::schema::rule_context::decode_rule_context_type;

#[derive(Clone, Debug)]
pub struct RewriteContextBinding {
    pub name: Ident,
    sort: RhoValue,
}

impl RewriteContextBinding {
    pub fn try_new(name: Ident, sort: RhoValue) -> Result<Self, ValueDecodeError> {
        Self::try_new_at(name, sort, "$.context.type")
    }

    pub(crate) fn try_new_at(
        name: Ident,
        sort: RhoValue,
        path: &str,
    ) -> Result<Self, ValueDecodeError> {
        decode_rule_context_type(&sort, path, true)?;
        Ok(Self { name, sort })
    }

    pub fn sort(&self) -> &RhoValue {
        &self.sort
    }

    pub fn render_sort(&self) -> String {
        enum Task<'a> {
            Visit(&'a RhoValue),
            Text(&'static str),
        }
        let mut tasks = vec![Task::Visit(&self.sort)];
        let mut output = String::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => output.push_str(text),
                Task::Visit(RhoValue::String(name)) => output.push_str(name),
                Task::Visit(RhoValue::List(values)) => {
                    let RhoValue::String(tag) = &values[0] else {
                        unreachable!("context types are validated on construction");
                    };
                    match tag.as_str() {
                        "arrow" => {
                            tasks.push(Task::Text("]"));
                            tasks.push(Task::Visit(&values[2]));
                            tasks.push(Task::Text(" -> "));
                            tasks.push(Task::Visit(&values[1]));
                            tasks.push(Task::Text("["));
                        },
                        "multi" => {
                            tasks.push(Task::Text("*"));
                            tasks.push(Task::Visit(&values[1]));
                        },
                        "bag" | "set" | "vec" | "map" | "pathmap" | "rewrite" => {
                            let name = match tag.as_str() {
                                "bag" => "HashBag(",
                                "set" => "Set(",
                                "vec" => "List(",
                                "map" => "Map(",
                                "pathmap" => "PathMap(",
                                _ => "Rewrite(",
                            };
                            tasks.push(Task::Text(")"));
                            if values.len() == 3 {
                                tasks.push(Task::Visit(&values[2]));
                                tasks.push(Task::Text(", "));
                            }
                            tasks.push(Task::Visit(&values[1]));
                            tasks.push(Task::Text(name));
                        },
                        _ => unreachable!("context types are validated on construction"),
                    }
                },
                Task::Visit(_) => unreachable!("context types are validated on construction"),
            }
        }
        output
    }
}
