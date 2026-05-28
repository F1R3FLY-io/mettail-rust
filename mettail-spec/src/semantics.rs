use crate::error::{Result, SpecError};
use crate::ntir::Ntir;
use crate::surface::ContextTemplate;

const INSERT_MARKER: &str = "INSERT_HERE";

/// Splice `body` at the first `marker` in `template.raw`.
pub fn insert_at_marker(template: &ContextTemplate, body: &str, marker: &str) -> Result<String> {
    let Some(offset) = template.insert_offset else {
        return Ok(template.raw.clone());
    };

    let count = template.raw.match_indices(marker).count();
    if count > 1 {
        return Err(SpecError::Assemble {
            message: format!(
                "context template contains {count} '{marker}' markers; expected at most one"
            ),
        });
    }
    if count == 0 {
        return Err(SpecError::Assemble {
            message: format!("context template insert_offset set but '{marker}' not found"),
        });
    }

    let mut out = String::new();
    out.push_str(&template.raw[..offset]);
    out.push_str(body);
    out.push_str(&template.raw[offset + marker.len()..]);
    Ok(out)
}

/// Replace `INSERT_HERE` in a Rust context template with the assembled theory body.
pub fn lower_rust_context(template: &ContextTemplate, theory_body: &str) -> Result<String> {
    insert_at_marker(template, theory_body, INSERT_MARKER)
}

/// Build the Rust backend payload: `use`, island snippets, and `language! { … }`.
pub fn assemble_rust_theory_body(ntir: &Ntir) -> Result<String> {
    if ntir.semantics != crate::ntir::SemanticsTarget::Rust {
        return Err(SpecError::Assemble {
            message: format!("Rust projection requires semantics Rust, got {:?}", ntir.semantics),
        });
    }

    let mut out = String::new();
    out.push_str("use mettail_macros::language;\n\n");

    for snippet in &ntir.rust_island_snippets {
        out.push_str(snippet.trim());
        if !snippet.trim_end().ends_with('\n') {
            out.push('\n');
        }
        out.push('\n');
    }

    out.push_str("language! {\n");
    out.push_str(&format!("    name: {},\n", ntir.name));
    push_section(&mut out, "types", &ntir.sources.types);
    push_section(&mut out, "literals", &ntir.sources.literals);
    push_section(&mut out, "terms", &ntir.sources.terms);
    push_section(&mut out, "equations", &ntir.sources.equations);
    push_section(&mut out, "rewrites", &ntir.sources.rewrites);
    push_logic_section(&mut out, &ntir.sources.logic);
    out.push_str("}\n");
    Ok(out)
}

fn push_section(out: &mut String, keyword: &str, body: &Option<String>) {
    if let Some(src) = body {
        if src.trim().is_empty() {
            return;
        }
        out.push_str("    ");
        out.push_str(keyword);
        out.push_str(" { ");
        out.push_str(src.trim());
        if !src.trim_end().ends_with(';') {
            out.push(';');
        }
        out.push_str(" }\n");
    }
}

fn push_logic_section(out: &mut String, body: &Option<String>) {
    if let Some(src) = body {
        if src.trim().is_empty() {
            return;
        }
        out.push_str("    logic { ");
        out.push_str(src.trim());
        if !src.trim_end().ends_with(';') {
            out.push(';');
        }
        out.push_str(" }\n");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_at_marker_replaces_single_marker() {
        let template = ContextTemplate {
            raw: "use std::collections::HashMap;\nINSERT_HERE\n".to_string(),
            insert_offset: Some("use std::collections::HashMap;\n".len()),
        };
        let out =
            insert_at_marker(&template, "language! { name: L }", INSERT_MARKER).expect("splice");
        assert!(out.contains("use std::collections::HashMap;"));
        assert!(out.contains("language! { name: L }"));
        assert!(!out.contains("INSERT_HERE"));
    }

    #[test]
    fn insert_at_marker_errors_on_duplicate_marker() {
        let template = ContextTemplate {
            raw: "INSERT_HERE\nINSERT_HERE\n".to_string(),
            insert_offset: Some(0),
        };
        let err = insert_at_marker(&template, "body", INSERT_MARKER).unwrap_err();
        assert!(err.to_string().contains("2"));
    }
}
