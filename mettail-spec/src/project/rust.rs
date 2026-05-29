use std::fs;
use std::path::Path;

use mettail_ast::language::LanguageDef;
use syn::parse::{ParseStream, Parser};

use crate::assemble::{compile_entry_with_spaces, validate_ntir};
use crate::error::{Result, SpecError};
use crate::ntir::Ntir;
use crate::semantics::{assemble_rust_theory_body, lower_rust_context};

/// Emit a complete Rust module source containing `language! { … }`.
pub fn project_rust_source(ntir: &Ntir) -> Result<String> {
    project_rust_source_with_spaces(ntir, &[])
}

pub fn project_rust_source_with_spaces(
    ntir: &Ntir,
    spaces: &[crate::ntir::SpaceSummary],
) -> Result<String> {
    let theory = assemble_rust_theory_body(ntir)?;
    let spaces_src = project_spaces_const(spaces);
    match &ntir.context_template {
        Some(tmpl) if tmpl.insert_offset.is_some() => {
            let lowered = lower_rust_context(tmpl, &theory)?;
            Ok(format!("{lowered}\n{spaces_src}"))
        },
        Some(tmpl) => Ok(format!("{}\n\n{}\n{}", tmpl.raw.trim_end(), theory, spaces_src)),
        None => Ok(format!("{theory}\n{spaces_src}")),
    }
}

/// Compile `.rho` entry and write projected Rust to `out_path`.
pub fn project_rust_file(
    entry_path: impl AsRef<Path>,
    language_name: Option<&str>,
    out_path: impl AsRef<Path>,
) -> Result<Ntir> {
    let (ntir, spaces) =
        compile_entry_with_spaces(entry_path.as_ref().to_path_buf(), language_name)?;
    validate_ntir(&ntir)?;
    write_projected_rs_with_spaces(&ntir, &spaces, out_path.as_ref())?;
    Ok(ntir)
}

/// Write projected Rust for an existing NTIR.
pub fn write_projected_rs(ntir: &Ntir, out_path: &Path) -> Result<()> {
    write_projected_rs_with_spaces(ntir, &[], out_path)
}

pub fn write_projected_rs_with_spaces(
    ntir: &Ntir,
    spaces: &[crate::ntir::SpaceSummary],
    out_path: &Path,
) -> Result<()> {
    let source = project_rust_source_with_spaces(ntir, spaces)?;
    if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent)
            .map_err(|e| SpecError::Io { path: parent.to_path_buf(), source: e })?;
    }
    fs::write(out_path, &source)
        .map_err(|e| SpecError::Io { path: out_path.to_path_buf(), source: e })?;
    Ok(())
}

fn project_spaces_const(spaces: &[crate::ntir::SpaceSummary]) -> String {
    let mut out = String::new();
    out.push('\n');
    out.push_str("pub const EXPORTED_SPACES: &[mettail_runtime::SpaceSpec] = &[\n");
    for s in spaces {
        // String escaping: this is a `.rho` identifier and language name; keep it simple.
        out.push_str(&format!(
            "    mettail_runtime::SpaceSpec {{ name: {:?}, language: {:?}, language_hash: {:?} }},\n",
            s.name, s.language, s.language_hash
        ));
    }
    out.push_str("];\n");
    out
}

/// Parse projected source back into [`LanguageDef`] (round-trip check).
pub fn parse_projected_language_def(ntir: &Ntir) -> Result<LanguageDef> {
    let body = project_language_def_input(ntir)?;
    parse_language_def
        .parse2(body)
        .map_err(|e| SpecError::Other(format!("projected LanguageDef parse failed: {e}")))
}

fn parse_language_def(input: ParseStream) -> syn::Result<LanguageDef> {
    input.parse::<LanguageDef>()
}

fn project_language_def_input(ntir: &Ntir) -> Result<proc_macro2::TokenStream> {
    let mut parts = vec![format!("name: {}", ntir.name)];
    if let Some(s) = &ntir.sources.types {
        parts.push(format!("types {{ {} }}", s.trim()));
    }
    if let Some(s) = &ntir.sources.literals {
        parts.push(format!("literals {{ {} }}", s.trim()));
    }
    if let Some(s) = &ntir.sources.terms {
        parts.push(format!("terms {{ {} }}", s.trim()));
    }
    if let Some(s) = &ntir.sources.equations {
        parts.push(format!("equations {{ {} }}", s.trim()));
    }
    if let Some(s) = &ntir.sources.rewrites {
        parts.push(format!("rewrites {{ {} }}", s.trim()));
    }
    if let Some(s) = &ntir.sources.logic {
        parts.push(format!("logic {{ {} }}", s.trim()));
    }
    let joined = parts.join(", ");
    syn::parse_str(&joined).map_err(|e| SpecError::Other(format!("tokenize projected def: {e}")))
}

/// Verify projected sources reproduce the same theory fields as NTIR.
pub fn verify_projection_sources(ntir: &Ntir) -> Result<()> {
    let def = parse_projected_language_def(ntir)?;
    if def.name != ntir.name {
        return Err(SpecError::Other(format!(
            "projected name mismatch: {} vs {}",
            def.name, ntir.name
        )));
    }
    if def.types.len() != ntir.types.len() {
        return Err(SpecError::Other(format!(
            "projected types count {} vs {}",
            def.types.len(),
            ntir.types.len()
        )));
    }
    if def.terms.len() != ntir.terms.len() {
        return Err(SpecError::Other(format!(
            "projected terms count {} vs {}",
            def.terms.len(),
            ntir.terms.len()
        )));
    }
    mettail_ast::validation::validate_language(&def)
        .map_err(|e| SpecError::Validation(e.message()))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::ntir::TheorySources;

    #[test]
    fn theory_sources_default_empty() {
        let s = TheorySources::default();
        assert!(s.types.is_none());
    }
}
