//! Blockly block definition generation
//!
//! This module generates TypeScript block definitions for Blockly visual editor
//! from MeTTaIL theory definitions. Each theory constructor becomes a block.
//!
//! ## Architecture
//!
//! - `builder.rs` - Constructs individual block definitions
//! - `colors.rs` - Generates deterministic colors for categories
//! - `writer.rs` - Writes TypeScript files to disk
//!
//! ## Generated Files
//!
//! For each theory, we generate:
//! - `<theory>-blocks.ts` - Block definitions
//! - `<theory>-categories.ts` - Category metadata

mod builder;
mod colors;
mod writer;

use mettail_ast::language::LanguageDef;
use std::collections::HashMap;

pub use writer::{write_blockly_blocks, write_blockly_categories};

/// Main entry point: Generate Blockly definitions for a theory
pub fn generate_blockly_definitions(language: &LanguageDef) -> BlocklyOutput {
    let language_name = language.name.to_string();

    // Seed every declared category so constructor-free categories still appear
    // in generated metadata and remain visible to downstream inventory checks.
    let mut categories: HashMap<String, Vec<String>> = HashMap::new();
    for ty in &language.types {
        categories.entry(ty.name.to_string()).or_default();
    }

    // Group constructors by category.
    for rule in &language.terms {
        let category = rule.category.to_string();
        categories
            .entry(category)
            .or_default()
            .push(rule.label.to_string());
    }

    // Generate block definitions
    let blocks = language
        .terms
        .iter()
        .map(|rule| builder::generate_block_definition(rule, &language_name))
        .collect();

    // Generate category information
    let category_info = colors::generate_category_info(&categories);

    BlocklyOutput {
        language_name,
        blocks,
        categories: category_info,
    }
}

/// Complete Blockly output for a theory
pub struct BlocklyOutput {
    pub language_name: String,
    pub blocks: Vec<BlockDefinition>,
    pub categories: HashMap<String, CategoryInfo>,
}

/// A single block definition
#[derive(Debug, Clone)]
pub struct BlockDefinition {
    pub block_type: String,
    pub tooltip: String,
    pub message: String,
    pub args: Vec<BlockArg>,
    pub connection_type: ConnectionType,
    pub colour: String,
    pub inputs_inline: bool,
}

/// Block argument (input field)
#[derive(Debug, Clone)]
pub struct BlockArg {
    pub arg_type: ArgType,
    pub name: String,
    pub check: Option<String>,
    pub text: Option<String>,
}

/// Type of block argument
#[derive(Debug, Clone, PartialEq)]
pub enum ArgType {
    InputValue,     // input_value (for expressions)
    InputStatement, // input_statement (for statement blocks)
    FieldInput,     // field_input (for text entry)
}

/// How the block connects to others
#[derive(Debug, Clone, PartialEq)]
pub enum ConnectionType {
    Value { output: String },                     // Has output connection
    Statement { previous: String, next: String }, // Has statement connections
}

/// Category metadata
#[derive(Debug, Clone)]
pub struct CategoryInfo {
    pub name: String,
    pub constructors: Vec<String>,
    pub colour: String,
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::LanguageDef;

    #[test]
    fn declared_constructor_free_categories_are_emitted() {
        let language: LanguageDef = syn::parse_quote! {
            name: BlocklySmoke,

            types {
                Proc;
                Name;
            }

            terms {
                PZero . Proc ::= "0";
            }
        };

        let output = generate_blockly_definitions(&language);

        let proc_category = output.categories.get("Proc").expect("Proc metadata");
        assert_eq!(proc_category.constructors, vec!["PZero"]);

        let name_category = output.categories.get("Name").expect("Name metadata");
        assert!(name_category.constructors.is_empty());
    }
}
