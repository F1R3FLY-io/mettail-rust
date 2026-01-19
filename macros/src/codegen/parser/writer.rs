// Helper module for writing generated LALRPOP grammars to files
// This is used during macro expansion or build process

use crate::ast::theory::TheoryDef;
use std::fs;
use std::path::Path;

/// Write a LALRPOP grammar file for a theory
///
/// This writes the generated grammar to src/generated/ directory.
pub fn write_grammar_file(theory_name: &str, grammar_content: &str) -> std::io::Result<()> {
    // Get the manifest directory of the crate that's using the macro
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());

    let base_dir = Path::new(&manifest_dir);

    // Try src/generated/ first (for library crates), fall back to generated/ (for binary crates)
    let src_generated_dir = base_dir.join("src").join("generated");
    let root_generated_dir = base_dir.join("generated");

    let output_dir = if base_dir.join("src").exists() {
        // Library crate: use src/generated/
        fs::create_dir_all(&src_generated_dir).ok();
        src_generated_dir
    } else {
        // Binary crate: use generated/ in root
        fs::create_dir_all(&root_generated_dir).ok();
        root_generated_dir
    };

    let theory_name_lower = theory_name.to_lowercase();
    let file_path = output_dir.join(format!("{}.lalrpop", theory_name_lower));

    fs::write(&file_path, grammar_content)?;

    eprintln!("Generated LALRPOP grammar: {}", file_path.display());
    Ok(())
}

/// Generate grammar file path for a theory
pub fn grammar_file_name(theory: &TheoryDef) -> String {
    format!("{}.lalrpop", theory.name.to_string().to_lowercase())
}
