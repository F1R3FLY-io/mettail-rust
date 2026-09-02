//! Mechanical source inventory for the in-Rholang DDL migration corpus.
//!
//! This module answers a narrower question than the formal-requirement audits:
//! which concrete `language!` and `language_fragment!` occurrences must have
//! canonical DDL artifacts?
//! It reuses the workspace's single recursive file walk, but keeps its own
//! structural declaration decision. Rust source is parsed with `syn`; comments,
//! strings, quoted macro output, and non-inline module declarations therefore do
//! not become false grammar declarations.
//!
//! An occurrence key is the repository-relative source path, the zero-based
//! declaration ordinal within that file, and the declared language name. The
//! ordinal distinguishes multiple declarations in one file without pretending
//! that a mutable source line is semantic identity. The line and column are
//! retained only for diagnostics.

use crate::fragment::FragmentDef;
use crate::language::{AttributeValue, LanguageDef};
use quote::ToTokens;
use std::collections::BTreeSet;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use syn::spanned::Spanned;
use syn::{Item, ItemMacro};

/// Directory containing the mechanically associated in-Rholang DDL artifacts.
pub const DDL_MIGRATION_ROOT: &str = "languages/specs/migrations";

/// Which compile-time declaration produced an inventory entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum DeclarationKind {
    Language,
    Fragment,
}

impl DeclarationKind {
    pub const fn macro_name(self) -> &'static str {
        match self {
            Self::Language => "language!",
            Self::Fragment => "language_fragment!",
        }
    }
}

/// One structurally parsed complete-language or reusable-fragment occurrence.
#[derive(Clone, Debug)]
pub struct LanguageDeclaration {
    /// The source macro's closed declaration kind.
    pub kind: DeclarationKind,
    /// Stable, checkout-independent occurrence identity.
    pub source_key: String,
    /// Repository-relative Rust source path with `/` separators.
    pub source_path: String,
    /// Zero-based declaration ordinal within `source_path`.
    pub ordinal: usize,
    /// One-based source line for diagnostics only.
    pub line: usize,
    /// Zero-based source column for diagnostics only.
    pub column: usize,
    /// Declared language name, preserving source spelling.
    pub name: String,
    /// Whether this is an explicit syntax-only profile.
    pub parse_only: bool,
    /// Exact macro-body tokens used to replay composition and auto-injection.
    ///
    /// These tokens are migration-tool input only. Production installation
    /// consumes the resulting canonical DDL value and never reconstructs or
    /// reparses Rust source.
    pub source_tokens: proc_macro2::TokenStream,
    /// The parsed compile-time language definition.
    pub definition: LanguageDef,
}

impl LanguageDeclaration {
    /// Whether this occurrence is the authoritative compile-time Rholang seed.
    pub fn is_rholang_seed(&self) -> bool {
        self.kind == DeclarationKind::Language
            && self.source_path == "languages/src/rholang.rs"
            && self.name == "Rholang"
    }

    /// Deterministic artifact path derived from the occurrence rather than a
    /// hand-maintained manifest.
    pub fn ddl_artifact_path(&self) -> PathBuf {
        let source = Path::new(&self.source_path)
            .strip_prefix("languages")
            .unwrap_or_else(|_| Path::new(&self.source_path));
        let parent = source.parent().unwrap_or_else(|| Path::new(""));
        let stem = source
            .file_stem()
            .and_then(|value| value.to_str())
            .unwrap_or("language");
        Path::new(DDL_MIGRATION_ROOT)
            .join(parent)
            .join(stem)
            .join(format!("{:03}-{}.rho", self.ordinal, artifact_component(&self.name)))
    }
}

/// Inventory discovery failure. Every variant is fatal because an incomplete
/// inventory must never be accepted as an empty or smaller corpus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventoryError {
    pub message: String,
}

impl InventoryError {
    fn new(message: impl Into<String>) -> Self {
        Self { message: message.into() }
    }
}

impl fmt::Display for InventoryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for InventoryError {}

#[derive(Debug)]
struct ParsedOccurrence {
    kind: DeclarationKind,
    source_tokens: proc_macro2::TokenStream,
    definition: LanguageDef,
    line: usize,
    column: usize,
}

/// Discover every `language!` and `language_fragment!` occurrence under the
/// manifest-declared roots and prove those roots cover every structural grammar
/// declaration in the repository.
pub fn discover_language_declarations(
    workspace_root: &Path,
) -> Result<Vec<LanguageDeclaration>, InventoryError> {
    let files =
        crate::language_scan::language_files(workspace_root).map_err(InventoryError::new)?;
    let audited = files.iter().cloned().collect::<BTreeSet<_>>();
    let mut declarations = Vec::new();

    for path in files {
        declarations.extend(parse_file(workspace_root, &path)?);
    }

    let mut escaped = Vec::new();
    for path in crate::language_scan::repository_rust_files(workspace_root) {
        if audited.contains(&path) {
            continue;
        }
        let source = fs::read_to_string(&path).map_err(|error| {
            InventoryError::new(format!("failed to read {}: {error}", path.display()))
        })?;
        if !crate::language_scan::mentions_grammar_invocation(&source) {
            continue;
        }
        let parsed = syn::parse_file(&source).map_err(|error| {
            InventoryError::new(format!(
                "{} may contain a language declaration but is not valid Rust: {error}",
                crate::language_scan::repo_relative(workspace_root, &path),
            ))
        })?;
        let mut found = Vec::new();
        collect_occurrences(&parsed.items, &mut found)?;
        if !found.is_empty() {
            escaped.push(crate::language_scan::repo_relative(workspace_root, &path));
        }
    }
    if !escaped.is_empty() {
        return Err(InventoryError::new(format!(
            "{} language declaration file(s) escape the manifest-declared roots: {}",
            escaped.len(),
            escaped.join(", "),
        )));
    }
    if declarations.is_empty() {
        return Err(InventoryError::new(
            "the manifest-declared roots contain no structural grammar declarations",
        ));
    }

    declarations.sort_by(|left, right| {
        (&left.source_path, left.ordinal).cmp(&(&right.source_path, right.ordinal))
    });
    let mut keys = BTreeSet::new();
    for declaration in &declarations {
        if !keys.insert(declaration.source_key.clone()) {
            return Err(InventoryError::new(format!(
                "duplicate language declaration key `{}`",
                declaration.source_key,
            )));
        }
    }
    Ok(declarations)
}

fn parse_file(
    workspace_root: &Path,
    path: &Path,
) -> Result<Vec<LanguageDeclaration>, InventoryError> {
    let source = fs::read_to_string(path).map_err(|error| {
        InventoryError::new(format!("failed to read {}: {error}", path.display()))
    })?;
    if !crate::language_scan::mentions_grammar_invocation(&source) {
        return Ok(Vec::new());
    }
    let parsed = syn::parse_file(&source).map_err(|error| {
        InventoryError::new(format!(
            "failed to parse {} while discovering language declarations: {error}",
            path.display(),
        ))
    })?;
    let mut occurrences = Vec::new();
    collect_occurrences(&parsed.items, &mut occurrences)?;
    let source_path = crate::language_scan::repo_relative(workspace_root, path);
    Ok(occurrences
        .into_iter()
        .enumerate()
        .map(|(ordinal, occurrence)| {
            let name = occurrence.definition.name.to_string();
            let source_key = format!("{source_path}#{ordinal}:{name}");
            let parse_only = occurrence.kind == DeclarationKind::Language
                && matches!(
                    occurrence.definition.options.get("parse_only"),
                    Some(AttributeValue::Bool(true))
                );
            LanguageDeclaration {
                kind: occurrence.kind,
                source_key,
                source_path: source_path.clone(),
                ordinal,
                line: occurrence.line,
                column: occurrence.column,
                name,
                parse_only,
                source_tokens: occurrence.source_tokens,
                definition: occurrence.definition,
            }
        })
        .collect())
}

fn collect_occurrences(
    items: &[Item],
    output: &mut Vec<ParsedOccurrence>,
) -> Result<(), InventoryError> {
    for item in items {
        match item {
            Item::Macro(item_macro) => collect_macro(item_macro, output)?,
            Item::Mod(item_module) => {
                if let Some((_, nested)) = &item_module.content {
                    collect_occurrences(nested, output)?;
                }
            },
            _ => {},
        }
    }
    Ok(())
}

fn collect_macro(
    item_macro: &ItemMacro,
    output: &mut Vec<ParsedOccurrence>,
) -> Result<(), InventoryError> {
    let kind = if item_macro.mac.path.is_ident("language") {
        DeclarationKind::Language
    } else if item_macro.mac.path.is_ident("language_fragment") {
        DeclarationKind::Fragment
    } else {
        return Ok(());
    };
    let start = item_macro.mac.path.span().start();
    let source_tokens = item_macro.mac.tokens.clone();
    let definition = match kind {
        DeclarationKind::Language => syn::parse2::<LanguageDef>(source_tokens.clone()),
        DeclarationKind::Fragment => syn::parse2::<FragmentDef>(source_tokens.clone())
            .map(|fragment| fragment.to_language_def()),
    }
    .map_err(|error| {
        InventoryError::new(format!(
            "failed to parse {} body at {}:{}: {error}; tokens: {}",
            kind.macro_name(),
            start.line,
            start.column,
            source_tokens.to_token_stream(),
        ))
    })?;
    output.push(ParsedOccurrence {
        kind,
        source_tokens,
        definition,
        line: start.line,
        column: start.column,
    });
    Ok(())
}

fn artifact_component(name: &str) -> String {
    let mut output = String::new();
    for character in name.chars() {
        if character.is_ascii_alphanumeric() {
            output.push(character.to_ascii_lowercase());
        } else if !output.ends_with('-') {
            output.push('-');
        }
    }
    output.trim_matches('-').to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inline_modules_preserve_source_order_and_locations() {
        let file = syn::parse_file(
            "language! { name: First, types { data A } terms {} }\n\
             mod nested {
               language_fragment! { name: Reusable, types { data R } terms {} }
               language! { name: Second, types { data B } terms {} }
             }",
        )
        .expect("fixture is Rust");
        let mut declarations = Vec::new();
        collect_occurrences(&file.items, &mut declarations).expect("definitions parse");
        assert_eq!(
            declarations
                .iter()
                .map(|entry| entry.definition.name.to_string())
                .collect::<Vec<_>>(),
            ["First", "Reusable", "Second"],
        );
        assert_eq!(declarations[0].line, 1);
        assert_eq!(declarations[1].line, 3);
        assert_eq!(declarations[2].line, 4);
        assert_eq!(declarations[1].kind, DeclarationKind::Fragment);
        assert_eq!(declarations[2].kind, DeclarationKind::Language);
    }

    #[test]
    fn artifact_paths_are_occurrence_derived() {
        let declaration = LanguageDeclaration {
            kind: DeclarationKind::Language,
            source_key: "languages/tests/example.rs#2:Guest_Lang".into(),
            source_path: "languages/tests/example.rs".into(),
            ordinal: 2,
            line: 10,
            column: 0,
            name: "Guest_Lang".into(),
            parse_only: false,
            source_tokens: syn::parse_str("name: Guest_Lang, types { data Expr } terms {}")
                .expect("language tokens"),
            definition: syn::parse_str("name: Guest_Lang, types { data Expr } terms {}")
                .expect("language fixture"),
        };
        assert_eq!(
            declaration.ddl_artifact_path(),
            Path::new("languages/specs/migrations/tests/example/002-guest-lang.rho"),
        );
    }
}
