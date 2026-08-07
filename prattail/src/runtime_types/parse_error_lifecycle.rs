//! Stack-safe lifecycle and formatting for recovery-wrapped parse errors.

use super::{ParseError, Position, Range};
use std::borrow::Cow;
use std::fmt;

enum CloneTask<'error> {
    Visit(&'error ParseError),
    Recovery(&'error str, Range, usize),
}

impl Clone for ParseError {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(ParseError::UnexpectedToken { expected, found, range, hint }) => {
                    values.push(ParseError::UnexpectedToken {
                        expected: expected.clone(),
                        found: found.clone(),
                        range: *range,
                        hint: hint.clone(),
                    })
                },
                CloneTask::Visit(ParseError::UnexpectedEof { expected, range, hint }) => values
                    .push(ParseError::UnexpectedEof {
                        expected: expected.clone(),
                        range: *range,
                        hint: hint.clone(),
                    }),
                CloneTask::Visit(ParseError::LexError { message, position }) => {
                    values.push(ParseError::LexError {
                        message: message.clone(),
                        position: *position,
                    })
                },
                CloneTask::Visit(ParseError::TrailingTokens { found, range, hint }) => {
                    values.push(ParseError::TrailingTokens {
                        found: found.clone(),
                        range: *range,
                        hint: hint.clone(),
                    })
                },
                CloneTask::Visit(ParseError::RecoveryApplied {
                    original_error,
                    repair_description,
                    range,
                }) => {
                    tasks.push(CloneTask::Recovery(repair_description, *range, values.len()));
                    tasks.push(CloneTask::Visit(original_error));
                },
                CloneTask::Visit(ParseError::AmbiguityBudget { budget, actual, range, hint }) => {
                    values.push(ParseError::AmbiguityBudget {
                        budget: *budget,
                        actual: *actual,
                        range: *range,
                        hint: hint.clone(),
                    })
                },
                CloneTask::Recovery(repair_description, range, base) => {
                    let original_error = values.pop().expect("parse-error clone lost its source");
                    values.truncate(base);
                    values.push(ParseError::RecoveryApplied {
                        original_error: Box::new(original_error),
                        repair_description: repair_description.to_owned(),
                        range,
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("parse-error clone produced no error")
    }
}

fn take_original(error: &mut ParseError) -> Option<ParseError> {
    match error {
        ParseError::RecoveryApplied { original_error, .. } => Some(*std::mem::replace(
            original_error,
            Box::new(ParseError::LexError {
                message: String::new(),
                position: Position::zero(),
            }),
        )),
        _ => None,
    }
}

impl Drop for ParseError {
    fn drop(&mut self) {
        let mut next = take_original(self);
        while let Some(mut error) = next {
            next = take_original(&mut error);
        }
    }
}

enum DebugTask<'error> {
    Visit(&'error ParseError),
    RecoverySuffix(&'error str, &'error Range),
}

impl fmt::Debug for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::RecoverySuffix(repair_description, range) => write!(
                    formatter,
                    ", repair_description: {repair_description:?}, range: {range:?} }}"
                )?,
                DebugTask::Visit(ParseError::UnexpectedToken {
                    expected,
                    found,
                    range,
                    hint,
                }) => write!(
                    formatter,
                    "UnexpectedToken {{ expected: {expected:?}, found: {found:?}, range: {range:?}, hint: {hint:?} }}"
                )?,
                DebugTask::Visit(ParseError::UnexpectedEof { expected, range, hint }) => write!(
                    formatter,
                    "UnexpectedEof {{ expected: {expected:?}, range: {range:?}, hint: {hint:?} }}"
                )?,
                DebugTask::Visit(ParseError::LexError { message, position }) => write!(
                    formatter,
                    "LexError {{ message: {message:?}, position: {position:?} }}"
                )?,
                DebugTask::Visit(ParseError::TrailingTokens { found, range, hint }) => write!(
                    formatter,
                    "TrailingTokens {{ found: {found:?}, range: {range:?}, hint: {hint:?} }}"
                )?,
                DebugTask::Visit(ParseError::RecoveryApplied {
                    original_error,
                    repair_description,
                    range,
                }) => {
                    write!(formatter, "RecoveryApplied {{ original_error: ")?;
                    tasks.push(DebugTask::RecoverySuffix(repair_description, range));
                    tasks.push(DebugTask::Visit(original_error));
                },
                DebugTask::Visit(ParseError::AmbiguityBudget {
                    budget,
                    actual,
                    range,
                    hint,
                }) => write!(
                    formatter,
                    "AmbiguityBudget {{ budget: {budget:?}, actual: {actual:?}, range: {range:?}, hint: {hint:?} }}"
                )?,
            }
        }
        Ok(())
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut recoveries = Vec::new();
        let mut leaf = self;
        loop {
            match leaf {
                ParseError::RecoveryApplied { original_error, repair_description, .. } => {
                    recoveries.push(repair_description.as_str());
                    leaf = original_error;
                },
                ParseError::UnexpectedToken { expected, found, range, hint } => {
                    write!(
                        formatter,
                        "{}:{}: expected {}, found {}",
                        range.start.line + 1,
                        range.start.column + 1,
                        expected,
                        found
                    )?;
                    display_hint(hint, formatter)?;
                    break;
                },
                ParseError::UnexpectedEof { expected, range, hint } => {
                    write!(
                        formatter,
                        "{}:{}: unexpected end of input, expected {}",
                        range.start.line + 1,
                        range.start.column + 1,
                        expected
                    )?;
                    display_hint(hint, formatter)?;
                    break;
                },
                ParseError::LexError { message, position } => {
                    write!(
                        formatter,
                        "{}:{}: {}",
                        position.line + 1,
                        position.column + 1,
                        message
                    )?;
                    break;
                },
                ParseError::TrailingTokens { found, range, hint } => {
                    write!(
                        formatter,
                        "{}:{}: unexpected {} after parsing",
                        range.start.line + 1,
                        range.start.column + 1,
                        found
                    )?;
                    display_hint(hint, formatter)?;
                    break;
                },
                ParseError::AmbiguityBudget { budget, actual, range, hint } => {
                    write!(
                        formatter,
                        "{}:{}: ambiguity budget {} exceeded (actual {})",
                        range.start.line + 1,
                        range.start.column + 1,
                        budget,
                        actual
                    )?;
                    display_hint(hint, formatter)?;
                    break;
                },
            }
        }
        for description in recoveries.into_iter().rev() {
            write!(formatter, " (recovered: {description})")?;
        }
        Ok(())
    }
}

fn display_hint(
    hint: &Option<Cow<'static, str>>,
    formatter: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    if let Some(hint) = hint {
        write!(formatter, "\n  = hint: {hint}")?;
    }
    Ok(())
}
