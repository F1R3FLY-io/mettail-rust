//! ascent_syntax_export - Export Ascent's parser types for external use
//!
//! This crate vendors and patches Ascent's internal parser to make it
//! accessible for tools that need to parse Ascent programs at runtime.
//!
//! # Why This Crate Exists
//!
//! Ascent's parser is in `ascent_macro/src/ascent_syntax.rs` - a private module.
//! The types (`AscentProgram`, `RelationNode`, `RuleNode`, etc.) are `pub(crate)`.
//! Since `ascent_macro` is a proc-macro crate, it can only export proc-macro functions.
//!
//! This crate provides a non-proc-macro wrapper that:
//! 1. Vendors source files from `ascent_macro` at build time
//! 2. Patches visibility modifiers to make types public
//! 3. Re-exports the types as a regular Rust library
//!
//! # Example
//!
//! ```ignore
//! use ascent_syntax_export::{parse_ascent_program_text, AscentProgram};
//!
//! let program = parse_ascent_program_text(r#"
//!     relation edge(Uuid, Uuid);
//!     relation path(Uuid, Uuid);
//!     
//!     path(x, y) <-- edge(x, y);
//!     path(x, z) <-- path(x, y), edge(y, z);
//! "#)?;
//!
//! println!("Found {} relations", program.relations.len());
//! println!("Found {} rules", program.rules.len());
//! ```

#![allow(
    clippy::useless_format,
    clippy::redundant_static_lifetimes,
    clippy::get_first
)]
#![allow(dead_code, unused_imports)]

// Vendored modules (created by build.rs)
mod vendored;

// Re-export the full ascent_syntax module for advanced usage
pub mod ascent_syntax {
    pub use super::vendored::ascent_syntax::*;
}

// Re-export the key types at crate root for convenience
pub use vendored::ascent_syntax::{
    desugar_ascent_program,
    // Functions
    parse_ascent_program,
    rule_node_summary,
    AggClauseNode,
    AggregatorNode,
    // Main program type
    AscentProgram,
    BodyClauseArg,
    BodyClauseNode,
    // Body clause types
    BodyItemNode,
    ClauseArgPattern,
    // Condition types
    CondClause,
    DisjunctionNode,
    // Attribute types
    DsAttributeContents,
    GeneratorNode,
    HeadClauseNode,
    // Head clause types
    HeadItemNode,
    IfClause,
    IfLetClause,
    ImplSignature,
    IncludeSourceMacroCall,
    IncludeSourceNode,
    LetClause,
    // Macro types
    MacroDefNode,
    // Other clause types
    NegationClauseNode,
    RelationIdentity,
    // Relation types
    RelationNode,
    // Rule types
    RuleNode,
    // Signature types
    Signatures,
    TypeSignature,
};

// Re-export AscentMacroKind from vendored module
pub use vendored::AscentMacroKind;

use itertools::Either;
use proc_macro2::Span;
use syn::parse::Parser;

/// Parse Ascent program text into an AST.
///
/// This is the main entry point for parsing Ascent programs at runtime.
///
/// # Arguments
/// * `text` - The Ascent program source code (without the `ascent!` wrapper)
///
/// # Returns
/// * `Ok(AscentProgram)` - The parsed program AST
/// * `Err(syn::Error)` - Parse error with location info
///
/// # Syntax Notes
/// - Ascent uses `<--` for rule arrows (not `:-` like traditional Datalog)
/// - Relations are declared with `relation name(Type1, Type2, ...);`
/// - Lattices are declared with `lattice name(Type1, Type2, ...);`
///
/// # Example
/// ```ignore
/// use ascent_syntax_export::parse_ascent_program_text;
///
/// let program = parse_ascent_program_text(r#"
///     relation edge(Uuid, Uuid);
///     relation path(Uuid, Uuid);
///     
///     path(x, y) <-- edge(x, y);
///     path(x, z) <-- path(x, y), edge(y, z);
/// "#)?;
///
/// assert_eq!(program.relations.len(), 2);
/// assert_eq!(program.rules.len(), 2);
/// ```
pub fn parse_ascent_program_text(text: &str) -> syn::Result<AscentProgram> {
    let tokens: proc_macro2::TokenStream = text.parse()?;

    let dummy_path: syn::Path = syn::parse_quote!(::ascent::ascent);

    syn::parse::Parser::parse2(
        |input: syn::parse::ParseStream| match vendored::ascent_syntax::parse_ascent_program(
            input,
            dummy_path.clone(),
        )? {
            Either::Left(program) => Ok(program),
            Either::Right(_) => Err(syn::Error::new(
                input.span(),
                "include_source! is not supported in runtime parsing",
            )),
        },
        tokens,
    )
}

/// Extract relation information from a parsed program.
///
/// Returns a vector of (relation_name, field_types, is_lattice) tuples.
pub fn extract_relations(program: &AscentProgram) -> Vec<(String, Vec<String>, bool)> {
    program
        .relations
        .iter()
        .map(|rel| {
            let name = rel.name.to_string();
            let types: Vec<String> = rel
                .field_types
                .iter()
                .map(|ty| quote::quote!(#ty).to_string())
                .collect();
            (name, types, rel.is_lattice)
        })
        .collect()
}

/// Extract rule head relation names from a parsed program.
///
/// Returns a vector of head relation names for each rule.
pub fn extract_rule_heads(program: &AscentProgram) -> Vec<String> {
    program
        .rules
        .iter()
        .filter_map(|rule| {
            rule.head_clauses.first().and_then(|head| match head {
                HeadItemNode::HeadClause(clause) => Some(clause.rel.to_string()),
                HeadItemNode::MacroInvocation(_) => None,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_program() {
        let text = r#"
            relation path(i32, i32);
            path(x, y) <-- edge(x, y);
        "#;

        let program = parse_ascent_program_text(text).unwrap();
        assert_eq!(program.relations.len(), 1);
        assert_eq!(program.rules.len(), 1);
    }

    #[test]
    fn test_parse_transitive_closure() {
        let text = r#"
            relation edge(i32, i32);
            relation path(i32, i32);
            
            path(x, y) <-- edge(x, y);
            path(x, z) <-- path(x, y), edge(y, z);
        "#;

        let program = parse_ascent_program_text(text).unwrap();
        assert_eq!(program.relations.len(), 2);
        assert_eq!(program.rules.len(), 2);

        let relations = extract_relations(&program);
        assert!(relations.iter().any(|(name, _, _)| name == "edge"));
        assert!(relations.iter().any(|(name, _, _)| name == "path"));

        let heads = extract_rule_heads(&program);
        assert_eq!(heads.len(), 2);
        assert!(heads.iter().all(|h| h == "path"));
    }

    #[test]
    fn test_extract_relation_types() {
        let text = r#"
            relation person(String, i64, bool);
        "#;

        let program = parse_ascent_program_text(text).unwrap();
        let relations = extract_relations(&program);

        assert_eq!(relations.len(), 1);
        let (name, types, is_lattice) = &relations[0];
        assert_eq!(name, "person");
        assert_eq!(types.len(), 3);
        assert!(!is_lattice);
    }

    #[test]
    fn test_parse_with_conditions() {
        let text = r#"
            relation person(String, i64);
            relation senior(String);
            
            senior(name) <-- person(name, age), if age >= 65;
        "#;

        let program = parse_ascent_program_text(text).unwrap();
        assert_eq!(program.relations.len(), 2);
        assert_eq!(program.rules.len(), 1);
    }

    #[test]
    fn test_parse_error() {
        let text = r#"
            relation bad syntax here;
        "#;

        let result = parse_ascent_program_text(text);
        assert!(result.is_err());
    }

    #[test]
    fn test_lattice_declaration() {
        let text = r#"
            lattice dist(i32, i32, i64);
        "#;

        let program = parse_ascent_program_text(text).unwrap();
        let relations = extract_relations(&program);

        assert_eq!(relations.len(), 1);
        let (name, _, is_lattice) = &relations[0];
        assert_eq!(name, "dist");
        assert!(is_lattice);
    }
}
