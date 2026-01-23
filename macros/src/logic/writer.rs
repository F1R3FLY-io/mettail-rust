// Helper module for writing generated Ascent Datalog to files
// This writes the generated Datalog source alongside LALRPOP grammars for debugging/inspection

use std::fs;
use std::path::Path;

/// Write an Ascent Datalog source file for a theory
///
/// This writes the generated Datalog to src/generated/ directory for inspection.
/// The file is not compiled - it's just for documentation/debugging.
pub fn write_ascent_file(theory_name: &str, ascent_content: &str) -> std::io::Result<()> {
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
    let file_path = output_dir.join(format!("{}-datalog.rs", theory_name_lower));

    fs::write(&file_path, ascent_content)?;

    eprintln!("Generated Ascent Datalog: {}", file_path.display());
    Ok(())
}
