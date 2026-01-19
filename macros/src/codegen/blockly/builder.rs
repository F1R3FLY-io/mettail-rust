//! Block definition builder
//!
//! Converts MeTTaIL grammar rules into Blockly block definitions

use super::{ArgType, BlockArg, BlockDefinition, ConnectionType};
use crate::ast::grammar::{GrammarItem, GrammarRule};

/// Generate a Blockly block definition from a grammar rule
pub fn generate_block_definition(rule: &GrammarRule, theory_name: &str) -> BlockDefinition {
    let label = rule.label.to_string();
    let category = rule.category.to_string();

    // Generate block type: theory_category_label
    let block_type = format_block_type(&label, &category, theory_name);

    // Generate tooltip
    let tooltip = generate_tooltip(rule);

    // Generate message0 format string and arguments
    let (message, args) = generate_message_and_args(&rule.items);

    // Determine connection type (value vs statement)
    let connection_type = determine_connection_type(&label, &category);

    // Get color for this category
    let colour = super::colors::category_color(&category);

    // Most blocks use inline inputs
    let inputs_inline = !has_statement_input(&args);

    BlockDefinition {
        block_type,
        tooltip,
        message,
        args,
        connection_type,
        colour,
        inputs_inline,
    }
}

/// Format block type identifier: lowercase with underscores
fn format_block_type(label: &str, category: &str, _theory_name: &str) -> String {
    let category_prefix = extract_category_prefix(category);

    // Convert label to snake_case: POutput -> output, NQuote -> quote
    let label_part = to_snake_case(label);

    format!("{}_{}", category_prefix, label_part)
}

/// Extract category prefix (Proc -> proc, Name -> name)
fn extract_category_prefix(category: &str) -> String {
    category.to_lowercase()
}

/// Convert PascalCase to snake_case
fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    let mut chars = s.chars().peekable();

    // Skip only single uppercase category prefix (P, N, E, etc.)
    let first = chars.next();
    if let Some(first_char) = first {
        // Check if this is a single-letter prefix followed by uppercase
        if first_char.is_uppercase() {
            if let Some(&next_char) = chars.peek() {
                if next_char.is_uppercase() {
                    // Single letter prefix (P, N) - skip it and continue
                    // The next uppercase will be lowercased below
                } else {
                    // Not a prefix pattern, keep the first char
                    result.push(first_char.to_ascii_lowercase());
                }
            } else {
                // Single char only
                result.push(first_char.to_ascii_lowercase());
                return result;
            }
        } else {
            result.push(first_char);
        }
    }

    let mut prev_was_lower = false;
    for ch in chars {
        if ch.is_uppercase() {
            if prev_was_lower {
                result.push('_');
            }
            result.push(ch.to_ascii_lowercase());
            prev_was_lower = false;
        } else {
            result.push(ch);
            prev_was_lower = true;
        }
    }

    result
}

/// Generate tooltip from grammar rule
fn generate_tooltip(rule: &GrammarRule) -> String {
    let label = rule.label.to_string();
    let human_label = humanize_label(&label);

    // Extract shape from terminals
    let shape = extract_shape(&rule.items);

    if shape.is_empty() {
        human_label
    } else {
        format!("{}: {}", human_label, shape)
    }
}

/// Convert label to human-readable text
fn humanize_label(label: &str) -> String {
    // Remove single-letter category prefix (P, N, etc.)
    let mut chars = label.chars();
    let first = chars.next();

    let without_prefix = if let Some(first_char) = first {
        if first_char.is_uppercase() {
            let rest: String = chars.collect();
            if !rest.is_empty() && rest.chars().next().unwrap().is_uppercase() {
                // Has uppercase after first char, so first is a prefix
                rest
            } else {
                label.to_string()
            }
        } else {
            label.to_string()
        }
    } else {
        return label.to_string();
    };

    if without_prefix.is_empty() {
        return label.to_string();
    }

    // Insert spaces before capitals
    let mut result = String::new();
    for (i, ch) in without_prefix.chars().enumerate() {
        if i > 0 && ch.is_uppercase() {
            result.push(' ');
        }
        result.push(ch);
    }

    result
}

/// Extract visual shape from terminals
fn extract_shape(items: &[GrammarItem]) -> String {
    let mut shape = String::new();

    for item in items {
        match item {
            GrammarItem::Terminal(s) => {
                if !shape.is_empty() && !s.trim().is_empty() {
                    shape.push(' ');
                }
                shape.push_str(s);
            },
            GrammarItem::NonTerminal(_) | GrammarItem::Binder { .. } => {
                if !shape.is_empty() {
                    shape.push(' ');
                }
                shape.push_str("...");
            },
            GrammarItem::Collection { delimiters, .. } => {
                if let Some((open, close)) = delimiters {
                    if !shape.is_empty() {
                        shape.push(' ');
                    }
                    shape.push_str(&format!("{} ... {}", open, close));
                }
            },
        }
    }

    shape
}

/// Generate message0 format string and args0 array
fn generate_message_and_args(items: &[GrammarItem]) -> (String, Vec<BlockArg>) {
    let mut message = String::new();
    let mut args = Vec::new();
    let mut arg_index = 1;

    for item in items {
        match item {
            GrammarItem::Terminal(s) => {
                // Add terminal text directly to message
                if !message.is_empty() && !s.is_empty() {
                    message.push(' ');
                }
                message.push_str(s);
            },

            GrammarItem::NonTerminal(category) => {
                let cat_str = category.to_string();

                // Special handling for Var pseudo-terminal
                if cat_str == "Var" {
                    if !message.is_empty() {
                        message.push(' ');
                    }
                    message.push_str(&format!("%{}", arg_index));

                    args.push(BlockArg {
                        arg_type: ArgType::FieldInput,
                        name: "VAR".to_string(),
                        check: None,
                        text: Some(default_var_name(category)),
                    });

                    arg_index += 1;
                    continue;
                }

                // Add placeholder and create argument
                if !message.is_empty() {
                    message.push(' ');
                }
                message.push_str(&format!("%{}", arg_index));

                let arg_name = generate_arg_name(arg_index, &cat_str, items);
                let arg_type = determine_arg_type(arg_index, items);

                args.push(BlockArg {
                    arg_type,
                    name: arg_name,
                    check: Some(cat_str),
                    text: None,
                });

                arg_index += 1;
            },

            GrammarItem::Binder { category: _ } => {
                // Binders become text input fields
                if !message.is_empty() {
                    message.push(' ');
                }
                message.push_str(&format!("%{}", arg_index));

                args.push(BlockArg {
                    arg_type: ArgType::FieldInput,
                    name: "VAR".to_string(),
                    check: None,
                    text: Some("x".to_string()),
                });

                arg_index += 1;
            },

            GrammarItem::Collection {
                coll_type: _, element_type, delimiters, ..
            } => {
                // Collections become statement inputs
                if let Some((open, close)) = delimiters {
                    if !message.is_empty() {
                        message.push(' ');
                    }
                    message.push_str(&format!("{} %{} {}", open, arg_index, close));
                } else {
                    if !message.is_empty() {
                        message.push(' ');
                    }
                    message.push_str(&format!("%{}", arg_index));
                }

                let arg_name = pluralize(&element_type.to_string());
                args.push(BlockArg {
                    arg_type: ArgType::InputStatement,
                    name: arg_name,
                    check: Some(element_type.to_string()),
                    text: None,
                });

                arg_index += 1;
            },
        }
    }

    (message, args)
}

/// Generate argument name based on position and category
fn generate_arg_name(index: usize, category: &str, items: &[GrammarItem]) -> String {
    // Heuristics for common patterns
    match (index, category) {
        (1, "Name") => "CHANNEL".to_string(),
        (1, "Proc") => "BODY".to_string(),
        (2, "Proc") => {
            // Check if this looks like the body of a binding construct
            if has_binder_before_index(items, index) {
                "BODY".to_string()
            } else {
                "MESSAGE".to_string()
            }
        },
        _ => format!("ARG{}", index),
    }
}

/// Check if there's a binder before a given argument index
fn has_binder_before_index(items: &[GrammarItem], target_index: usize) -> bool {
    let mut arg_count = 0;
    for item in items {
        match item {
            GrammarItem::Binder { .. } => {
                arg_count += 1;
                // Any arg after a binder should return true
                if arg_count < target_index {
                    return true;
                }
            },
            GrammarItem::NonTerminal(cat) if *cat != "Var" => {
                arg_count += 1;
            },
            GrammarItem::Collection { .. } => {
                arg_count += 1;
            },
            _ => {},
        }
    }
    false
}

/// Determine argument type (value vs statement) based on context
fn determine_arg_type(index: usize, items: &[GrammarItem]) -> ArgType {
    // Check if this is after a binder (likely a body)
    if has_binder_before_index(items, index) {
        ArgType::InputStatement
    } else {
        ArgType::InputValue
    }
}

/// Default variable name for Var fields
fn default_var_name(category: &syn::Ident) -> String {
    let cat = category.to_string();
    if cat.starts_with('P') {
        "P".to_string()
    } else if cat.starts_with('N') {
        "x".to_string()
    } else {
        "v".to_string()
    }
}

/// Pluralize category name for collection fields
fn pluralize(s: &str) -> String {
    format!("{}S", s.to_uppercase())
}

/// Check if args contain statement input
fn has_statement_input(args: &[BlockArg]) -> bool {
    args.iter()
        .any(|arg| arg.arg_type == ArgType::InputStatement)
}

/// Determine connection type (value vs statement)
fn determine_connection_type(label: &str, category: &str) -> ConnectionType {
    // Heuristic: Variables and certain constructors are value blocks
    if label.ends_with("Var") || label.ends_with("Zero") || label == "NQuote" {
        return ConnectionType::Value { output: category.to_string() };
    }

    // Proc blocks that look like statements
    if category == "Proc" {
        return ConnectionType::Statement {
            previous: category.to_string(),
            next: category.to_string(),
        };
    }

    // Default: value output for other categories
    ConnectionType::Value { output: category.to_string() }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_snake_case() {
        assert_eq!(to_snake_case("POutput"), "output");
        assert_eq!(to_snake_case("NQuote"), "quote");
        assert_eq!(to_snake_case("PZero"), "zero");
        assert_eq!(to_snake_case("PDrop"), "drop");
    }

    #[test]
    fn test_humanize_label() {
        assert_eq!(humanize_label("POutput"), "Output");
        assert_eq!(humanize_label("NQuote"), "Quote");
        assert_eq!(humanize_label("PInput"), "Input");
    }
}
