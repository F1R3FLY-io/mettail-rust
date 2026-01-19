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

use crate::ast::theory::TheoryDef;
use std::collections::HashMap;

pub use writer::{write_blockly_blocks, write_blockly_categories};

/// Main entry point: Generate Blockly definitions for a theory
pub fn generate_blockly_definitions(theory: &TheoryDef) -> BlocklyOutput {
    let theory_name = theory.name.to_string();

    // Group constructors by category
    let mut categories: HashMap<String, Vec<String>> = HashMap::new();
    for rule in &theory.terms {
        let category = rule.category.to_string();
        categories
            .entry(category)
            .or_default()
            .push(rule.label.to_string());
    }

    // Generate block definitions
    let blocks = theory
        .terms
        .iter()
        .map(|rule| builder::generate_block_definition(rule, &theory_name))
        .collect();

    // Generate category information
    let category_info = colors::generate_category_info(&categories);

    BlocklyOutput {
        theory_name,
        blocks,
        categories: category_info,
    }
}

/// Complete Blockly output for a theory
pub struct BlocklyOutput {
    pub theory_name: String,
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
