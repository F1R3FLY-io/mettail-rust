// Helper module for writing generated LALRPOP grammars to files
// This is used during macro expansion or build process

use std::fs;
use std::path::Path;

/// Name of the grammar-generator build-dependency crate (writes into parent languages crate).
const LANG_GEN_CRATE: &str = "mettail-lang-gen";

/// Write a LALRPOP grammar file for a theory
///
/// This writes the generated grammar to src/generated/ directory.
/// When invoked from the grammar-generator crate (`mettail-lang-gen`), writes to
/// `../src/generated` so files land in the parent `languages` crate.
pub fn write_grammar_file(language_name: &str, grammar_content: &str) -> std::io::Result<()> {
    // Get the manifest directory of the crate that's using the macro
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let pkg_name = std::env::var("CARGO_PKG_NAME").unwrap_or_default();

    let base_dir = Path::new(&manifest_dir);

    let output_dir = if pkg_name == LANG_GEN_CRATE {
        // Grammar generator build-dependency: write into parent languages crate
        let out = base_dir.join("..").join("src").join("generated");
        fs::create_dir_all(&out).ok();
        out
    } else {
        // Try src/generated/ first (for library crates), fall back to generated/ (for binary crates)
        let src_generated_dir = base_dir.join("src").join("generated");
        let root_generated_dir = base_dir.join("generated");
        if base_dir.join("src").exists() {
            fs::create_dir_all(&src_generated_dir).ok();
            src_generated_dir
        } else {
            fs::create_dir_all(&root_generated_dir).ok();
            root_generated_dir
        }
    };

    let language_name_lower = language_name.to_lowercase();
    let file_path = output_dir.join(format!("{}.lalrpop", language_name_lower));

    fs::write(&file_path, grammar_content)?;

    eprintln!("Generated LALRPOP grammar: {}", file_path.display());
    Ok(())
}
