//! Helpers for writing generated Rust source to disk and emitting `include!`
//! stubs back into the `language!` macro expansion.
//!
//! The emitters in `macros/src/gen/` used to inline every generated module
//! directly into the returned `TokenStream`. For a 12-category language like
//! Calculator that produces a single multi-MB TokenStream, which the proc-macro
//! bridge copies to `rustc` and which `rustc` then parses and holds in memory
//! through type-check and codegen. Peak proc-macro-expansion RSS exceeded
//! 64 GB post-merge.
//!
//! This module lets each emitter *write its output to disk* (as formatted
//! Rust source) and emit a tiny `include!("...")` back into the TokenStream.
//! `rustc` then reads the files during expansion via its normal file-loading
//! path — one copy instead of two — and humans can inspect/diff the
//! generated sources in `target/generated/<lang>/`.
//!
//! Files are written with `write_if_changed` semantics so cargo's incremental
//! build doesn't treat unchanged modules as dirty.

use proc_macro2::{Span, TokenStream};
use quote::quote;
use std::fs;
use std::path::{Path, PathBuf};

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

/// Return the per-language generated-source directory.
///
/// Layout: `<workspace-root>/target/generated/<lang_lower>/` (workspace builds)
/// or `<CARGO_MANIFEST_DIR>/target/generated/<lang_lower>/` (standalone builds).
///
/// Detects the workspace root by walking up from the caller's
/// `CARGO_MANIFEST_DIR` looking for a `Cargo.toml` that contains `[workspace]`.
/// Falls back to the caller's manifest dir if no workspace is found.
///
/// Rationale: when the crate invoking `language!` is a workspace member, its
/// crate-level `target/` is not what cargo actually uses — cargo uses
/// `<workspace>/target/`. Writing to the real workspace target keeps generated
/// files in one discoverable location and matches where `cargo clean` cleans.
///
/// This is the ONLY destination any `language!` writer may compute. It is public so the
/// non-Rust emitters (Blockly TypeScript) can reach it too: `write_lang_module` appends
/// `.rs`, which is wrong for them, but the DIRECTORY rule must still be the same one.
pub fn lang_generated_dir(lang_name: &str) -> PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let base = Path::new(&manifest_dir);
    let target_root = find_workspace_root(base).unwrap_or_else(|| base.to_path_buf());
    target_root
        .join("target")
        .join("generated")
        .join(lang_name.to_lowercase())
}

/// Walk parent dirs from `start` looking for a `Cargo.toml` whose content
/// contains a top-level `[workspace]` table. Returns the containing dir if
/// found; `None` otherwise.
fn find_workspace_root(start: &Path) -> Option<PathBuf> {
    let mut cur: Option<&Path> = Some(start);
    while let Some(dir) = cur {
        let manifest = dir.join("Cargo.toml");
        if let Ok(contents) = fs::read_to_string(&manifest) {
            if contents
                .lines()
                .any(|l| l.trim_start().starts_with("[workspace]"))
            {
                return Some(dir.to_path_buf());
            }
        }
        cur = dir.parent();
    }
    None
}

/// Write a generated Rust source file for one module of one language.
///
/// `lang_name` is the language name (e.g., `"Calculator"`); it is lowercased
/// for the directory name. `module_name` is the file stem (e.g., `"ast_enums"`).
/// The `.rs` extension is appended automatically.
///
/// Returns the absolute path the content was written to (whether or not it
/// was actually written — the path is always valid, and `include!` needs it
/// regardless of write-if-changed skipping).
pub fn write_lang_module(
    lang_name: &str,
    module_name: &str,
    content: &str,
) -> std::io::Result<PathBuf> {
    let dir = lang_generated_dir(lang_name);
    fs::create_dir_all(&dir)?;
    let path = dir.join(format!("{}.rs", module_name));
    let _wrote = write_if_changed(&path, content)?;
    Ok(path)
}

/// Remove one generated Rust module retired by the generator.
///
/// Generated sources are write-if-changed and therefore survive when an
/// emitter is deleted. Calling this migration helper from the current
/// expansion keeps `target/generated/<lang>/` an inventory of live output
/// without deleting the language directory or any unrelated artifact.
/// Returns `true` when a file was removed and `false` when it was already
/// absent.
pub fn retire_lang_module(lang_name: &str, module_name: &str) -> std::io::Result<bool> {
    let path = lang_generated_dir(lang_name).join(format!("{}.rs", module_name));
    match fs::remove_file(path) {
        Ok(()) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

/// Emit an `include!("<absolute-path>")` TokenStream for a language module.
///
/// The path is baked as a string literal into the macro expansion. `include!`
/// is resolved by `rustc` at parse time and pulls the file contents into the
/// enclosing scope as if they had been written inline — without the
/// proc-macro bridge overhead of shipping the code as a TokenStream.
pub fn include_stmt(path: &Path) -> TokenStream {
    let path_str = path.to_string_lossy().into_owned();
    let path_lit = syn::LitStr::new(&path_str, Span::call_site());
    quote! { include!(#path_lit); }
}

/// Format a `TokenStream` as pretty-printed Rust source using `prettyplease`
/// if available, falling back to `TokenStream::to_string()`.
///
/// Pretty-printing makes the on-disk files reviewable by humans and keeps
/// diffs stable across equivalent token streams. Fallback path works during
/// bootstrapping when `prettyplease` may not yet be wired as a dep.
pub fn format_rust_source(tokens: &TokenStream) -> String {
    match syn::parse2::<syn::File>(tokens.clone()) {
        Ok(file) => prettyplease::unparse(&file),
        Err(_) => tokens.to_string(),
    }
}

/// One-shot helper: emit a TokenStream to disk and return an `include!` stub
/// pointing at the file.
///
/// This is the primary entry point for generator modules that want to
/// spill their output to disk. The returned `TokenStream` is what goes
/// into `generate_all`'s combined output.
pub fn spill_and_include(lang_name: &str, module_name: &str, tokens: TokenStream) -> TokenStream {
    let source = format_rust_source(&tokens);
    match write_lang_module(lang_name, module_name, &source) {
        Ok(path) => include_stmt(&path),
        Err(e) => {
            eprintln!(
                "  ({}) WARNING: could not write {}.rs ({}) — falling back to inline emission",
                lang_name, module_name, e
            );
            tokens
        },
    }
}
