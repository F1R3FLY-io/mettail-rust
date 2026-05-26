//! Structural parity between composed `.rho` specs and monolithic `language!` references.

use mettail_ast::language::LanguageDef;

use crate::error::{Result, SpecError};
use crate::ntir::Ntir;

/// Deterministic view of a language spec for modular vs monolithic comparison.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LanguageSnapshot {
    pub name: String,
    pub type_names: Vec<String>,
    pub term_labels: Vec<String>,
    pub equation_names: Vec<String>,
    pub rewrite_names: Vec<String>,
    pub has_literals: bool,
    pub logic_relation_count: usize,
}

impl LanguageSnapshot {
    pub fn from_language_def(def: &LanguageDef) -> Self {
        let mut type_names: Vec<String> = def.types.iter().map(|t| t.name.to_string()).collect();
        type_names.sort();

        let mut term_labels: Vec<String> = def.terms.iter().map(|r| r.label.to_string()).collect();
        term_labels.sort();

        let mut equation_names: Vec<String> =
            def.equations.iter().map(|e| e.name.to_string()).collect();
        equation_names.sort();

        let mut rewrite_names: Vec<String> =
            def.rewrites.iter().map(|r| r.name.to_string()).collect();
        rewrite_names.sort();

        let logic_relation_count = def.logic.as_ref().map(|l| l.relations.len()).unwrap_or(0);

        Self {
            name: def.name.to_string(),
            type_names,
            term_labels,
            equation_names,
            rewrite_names,
            has_literals: def.literals.is_some(),
            logic_relation_count,
        }
    }

    pub fn from_ntir(ntir: &Ntir) -> Self {
        Self::from_language_def(&ntir.to_language_def())
    }
}

/// Parse a monolithic `language! { … }` block from Rust source text.
pub fn language_def_from_monolithic(source: &str) -> Result<LanguageDef> {
    syn::parse_str(source)
        .map_err(|e| SpecError::Other(format!("monolithic LanguageDef parse failed: {e}")))
}

/// Human-readable differences between two snapshots (empty if equal).
pub fn diff_snapshots(expected: &LanguageSnapshot, actual: &LanguageSnapshot) -> Vec<String> {
    let mut diffs = Vec::new();
    if expected.name != actual.name {
        diffs.push(format!("name: expected {:?}, got {:?}", expected.name, actual.name));
    }
    diff_vec("type_names", &expected.type_names, &actual.type_names, &mut diffs);
    diff_vec("term_labels", &expected.term_labels, &actual.term_labels, &mut diffs);
    diff_vec("equation_names", &expected.equation_names, &actual.equation_names, &mut diffs);
    diff_vec("rewrite_names", &expected.rewrite_names, &actual.rewrite_names, &mut diffs);
    if expected.has_literals != actual.has_literals {
        diffs.push(format!(
            "has_literals: expected {}, got {}",
            expected.has_literals, actual.has_literals
        ));
    }
    if expected.logic_relation_count != actual.logic_relation_count {
        diffs.push(format!(
            "logic_relation_count: expected {}, got {}",
            expected.logic_relation_count, actual.logic_relation_count
        ));
    }
    diffs
}

fn diff_vec(field: &str, expected: &[String], actual: &[String], diffs: &mut Vec<String>) {
    if expected != actual {
        diffs.push(format!("{field}: expected {expected:?}, got {actual:?}"));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diff_empty_when_equal() {
        let s = LanguageSnapshot {
            name: "X".into(),
            type_names: vec!["A".into()],
            term_labels: vec![],
            equation_names: vec![],
            rewrite_names: vec![],
            has_literals: false,
            logic_relation_count: 0,
        };
        assert!(diff_snapshots(&s, &s).is_empty());
    }
}
