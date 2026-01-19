use crate::ast::theory::TheoryDef;
use syn::Ident;

/// Check if a category has a native type and return it
pub fn has_native_type<'a>(category: &Ident, theory: &'a TheoryDef) -> Option<&'a syn::Type> {
    theory
        .exports
        .iter()
        .find(|e| e.name == *category)
        .and_then(|e| e.native_type.as_ref())
}

/// Get native type as string for comparison
pub fn native_type_to_string(native_type: &syn::Type) -> String {
    match native_type {
        syn::Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                segment.ident.to_string()
            } else {
                "unknown".to_string()
            }
        },
        _ => "unknown".to_string(),
    }
}

pub fn split_commas_outside_parens(s: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut depth = 0;
    let mut start = 0;

    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                result.push(&s[start..i]);
                start = i + 1;
            },
            _ => {},
        }
    }

    // Add the last segment
    if start <= s.len() {
        result.push(&s[start..]);
    }

    result
}

/// Normalize whitespace in a string by replacing all consecutive whitespace
/// (including newlines) with a single space. This fixes formatting issues
/// from TokenStream::to_string() which can insert unwanted line breaks.
fn normalize_whitespace(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

pub fn print_rule(line: &str) -> String {
    if line.trim().is_empty() {
        return String::new();
    }

    // Normalize whitespace to fix TokenStream formatting issues
    let normalized = normalize_whitespace(line);

    let (head, body) = normalized
        .split_once("<- -")
        .unwrap_or((normalized.trim(), ""));
    let head_clauses = split_commas_outside_parens(head);
    let (head_last, head_rest) = head_clauses.split_last().unwrap_or((&"", &[]));
    let clauses = split_commas_outside_parens(body);
    let (last, rest) = clauses.split_last().unwrap_or((&"", &[]));
    if !body.trim().is_empty() {
        let mut result = String::new();
        for clause in head_rest {
            result.push_str(&format!("{},\n", clause.trim()));
        }
        result.push_str(&format!("{} <--\n", head_last.trim()));
        for clause in rest {
            result.push_str(&format!("    {},\n", clause.trim()));
        }
        result.push_str(&format!("    {};\n\n", last.trim()));
        result.to_string()
    } else {
        format!("{};\n\n", normalized.trim())
    }
}
