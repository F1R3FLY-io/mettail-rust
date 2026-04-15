// Helper module for writing generated Ascent Datalog to files
// This writes the generated Datalog source for debugging/inspection

use std::fs;
use std::path::Path;

/// Write content to a file only if it differs from what is already on disk.
///
/// Skipping the write when content is unchanged prevents cargo from seeing a
/// newer mtime on generated files and triggering spurious recompilation of the
/// entire `mettail-languages` crate on every build.
///
/// Returns `true` if the file was written, `false` if it was unchanged.
fn write_if_changed(path: &Path, content: &str) -> std::io::Result<bool> {
    if let Ok(existing) = fs::read_to_string(path) {
        if existing == content {
            return Ok(false);
        }
    }
    fs::write(path, content)?;
    Ok(true)
}

/// Write an Ascent Datalog source file for a theory
///
/// This writes the generated Datalog to src/generated/ directory for inspection.
/// The file is not compiled - it's just for documentation/debugging.
pub fn write_ascent_file(grammar_name: &str, theory_name: &str, ascent_content: &str) -> std::io::Result<()> {
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

    if write_if_changed(&file_path, ascent_content)? {
        eprintln!("  ({}) Generated Ascent Datalog: {}", grammar_name, file_path.display());
    }
    Ok(())
}
