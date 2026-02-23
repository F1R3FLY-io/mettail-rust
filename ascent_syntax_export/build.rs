//! Build script that optionally vendors and patches Ascent's internal parser files.
//!
//! If ascent_macro source is available (env ASCENT_MACRO_SRC or `../../ascent/ascent_macro/src`),
//! regenerates `src/vendored/`. Otherwise the committed vendored source is used so the crate
//! builds without cloning ascent.
//!
//! Patches applied when regenerating:
//! 1. Make types public (pub(crate) → pub)
//! 2. Add a proc_macro stub for non-proc-macro context
//! 3. Fix module imports (crate:: → super::)
//! 4. Replace closure-based derive with manual Parse impl

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

fn main() {
    let src_dir: Option<PathBuf> = env::var("ASCENT_MACRO_SRC")
        .ok()
        .filter(|s| Path::new(s).join("ascent_syntax.rs").exists())
        .map(PathBuf::from)
        .or_else(|| {
            let p = Path::new("../../ascent/ascent_macro/src");
            if p.join("ascent_syntax.rs").exists() {
                Some(p.to_path_buf())
            } else {
                None
            }
        });

    let out_dir = Path::new("src/vendored");

    if let Some(src_dir) = src_dir {
        fs::create_dir_all(out_dir).expect("Failed to create vendored directory");
        patch_ascent_syntax(&src_dir, out_dir);
        patch_syn_utils(&src_dir, out_dir);
        patch_utils(&src_dir, out_dir);
        create_mod_file(out_dir);
        println!("cargo:rerun-if-changed={}/ascent_syntax.rs", src_dir.display());
        println!("cargo:rerun-if-changed={}/syn_utils.rs", src_dir.display());
        println!("cargo:rerun-if-changed={}/utils.rs", src_dir.display());
    }
    println!("cargo:rerun-if-changed=build.rs");
}

fn patch_ascent_syntax(src_dir: &Path, out_dir: &Path) {
    let content = fs::read_to_string(src_dir.join("ascent_syntax.rs"))
        .expect("Failed to read ascent_syntax.rs");

    let mut patched = content;

    // Remove #![deny(warnings)] since we're modifying the code
    patched = patched.replace("#![deny(warnings)]", "#![allow(warnings)]");

    // Remove the extern crate proc_macro line (we'll provide our own stub)
    patched = patched.replace("extern crate proc_macro;", "// extern crate proc_macro; // Removed - using stub");

    // Add quote macro imports at the top of the file (after allow warnings)
    // The original lib.rs has #[macro_use] extern crate quote; which makes macros globally available
    // We need explicit imports since we're not in lib.rs
    let imports_to_add = "\nuse quote::{quote, quote_spanned};\n";
    if let Some(pos) = patched.find("use std::collections") {
        patched.insert_str(pos, imports_to_add);
    }

    // Make types public
    patched = patched.replace("pub(crate) struct Signatures", "pub struct Signatures");
    patched = patched.replace("pub(crate) struct AscentProgram", "pub struct AscentProgram");
    patched = patched.replace("pub(crate) struct RelationIdentity", "pub struct RelationIdentity");
    patched = patched.replace("pub(crate) struct DsAttributeContents", "pub struct DsAttributeContents");
    patched = patched.replace("pub(crate) struct IncludeSourceMacroCall", "pub struct IncludeSourceMacroCall");
    patched = patched.replace("pub(crate) fn parse_ascent_program", "pub fn parse_ascent_program");
    patched = patched.replace("pub(crate) fn desugar_ascent_program", "pub fn desugar_ascent_program");
    patched = patched.replace("pub(crate) fn rule_node_summary", "pub fn rule_node_summary");

    // Fix imports - replace crate:: with super:: for our vendored modules
    patched = patched.replace("use crate::AscentMacroKind;", "use super::AscentMacroKind;");
    patched = patched.replace("use crate::syn_utils::", "use super::syn_utils::");
    // Fix utils import inside the nested kw module FIRST (needs super::super:: since it's nested)
    // The kw module is inside ascent_syntax.rs, so it needs to go up two levels
    // This must come BEFORE the general utils replacement
    patched = patched.replace(
        "   use crate::utils::join_spans;",
        "   use super::super::utils::join_spans;"
    );
    // Fix utils import at module level (general replacement)
    patched = patched.replace("use crate::utils::", "use super::utils::");

    // Replace the BodyClauseArg enum definition with one that has a manual Parse impl
    // The original uses #[peek_with({ |_| true }, ...)] which doesn't work outside proc-macro
    let old_body_clause_arg = r#"#[derive(Parse, Clone, PartialEq, Eq, Debug)]
pub enum BodyClauseArg {
   #[peek(Token![?], name = "Pattern arg")]
   Pat(ClauseArgPattern),
   #[peek_with({ |_| true }, name = "Expression arg")]
   Expr(Expr),
}"#;

    let new_body_clause_arg = r#"#[derive(Clone, PartialEq, Eq, Debug)]
pub enum BodyClauseArg {
   Pat(ClauseArgPattern),
   Expr(Expr),
}

impl syn::parse::Parse for BodyClauseArg {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        if input.peek(syn::Token![?]) {
            Ok(BodyClauseArg::Pat(input.parse()?))
        } else {
            Ok(BodyClauseArg::Expr(input.parse()?))
        }
    }
}"#;

    patched = patched.replace(old_body_clause_arg, new_body_clause_arg);

    fs::write(out_dir.join("ascent_syntax.rs"), patched)
        .expect("Failed to write patched ascent_syntax.rs");
}

fn patch_syn_utils(src_dir: &Path, out_dir: &Path) {
    let content = fs::read_to_string(src_dir.join("syn_utils.rs"))
        .expect("Failed to read syn_utils.rs");

    let mut patched = content;

    // Remove #![deny(warnings)]
    patched = patched.replace("#![deny(warnings)]", "#![allow(warnings)]");

    // Fix imports
    patched = patched.replace("use crate::utils::", "use super::utils::");

    // Add proc_macro stub and quote imports at the beginning (after the warning suppression)
    let proc_macro_stub = r#"
// Stub module for non-proc-macro context
// The real proc_macro crate is only available in proc-macro crates
mod proc_macro {
    pub struct TokenStream;
    impl From<proc_macro2::TokenStream> for TokenStream {
        fn from(_: proc_macro2::TokenStream) -> Self { TokenStream }
    }
}

// Import quote macros for tests
#[cfg(test)]
use quote::quote;
"#;

    // Insert after the first line (after #![allow(warnings)])
    if let Some(pos) = patched.find('\n') {
        patched.insert_str(pos + 1, proc_macro_stub);
    } else {
        patched = format!("{}\n{}", proc_macro_stub, patched);
    }

    fs::write(out_dir.join("syn_utils.rs"), patched)
        .expect("Failed to write patched syn_utils.rs");
}

fn patch_utils(src_dir: &Path, out_dir: &Path) {
    let content = fs::read_to_string(src_dir.join("utils.rs"))
        .expect("Failed to read utils.rs");

    let mut patched = content;

    // Remove #![deny(warnings)]
    patched = patched.replace("#![deny(warnings)]", "#![allow(warnings)]");

    // Add quote macro imports at the top
    let imports_to_add = "use quote::{quote, quote_spanned};\n";
    if let Some(pos) = patched.find("use std::collections") {
        patched.insert_str(pos, imports_to_add);
    }

    // Fix imports
    patched = patched.replace("use crate::syn_utils::", "use super::syn_utils::");

    fs::write(out_dir.join("utils.rs"), patched)
        .expect("Failed to write patched utils.rs");
}

fn create_mod_file(out_dir: &Path) {
    let mod_content = r#"//! Vendored and patched Ascent parser modules
//! 
//! This module is auto-generated by build.rs

pub mod utils;
pub mod syn_utils;
pub mod ascent_syntax;

// Re-export AscentMacroKind which is needed by ascent_syntax
// This is a simplified version that provides the minimal interface needed
#[derive(Clone, Copy, Default)]
pub struct AscentMacroKind {
    pub is_ascent_run: bool,
    pub is_parallel: bool,
}

impl AscentMacroKind {
    pub fn name(&self) -> &'static str {
        match (self.is_ascent_run, self.is_parallel) {
            (false, false) => "ascent",
            (false, true) => "ascent_par",
            (true, false) => "ascent_run",
            (true, true) => "ascent_run_par",
        }
    }

    pub fn macro_path(&self, span: proc_macro2::Span) -> syn::Path {
        let name_ident = syn::Ident::new(self.name(), span);
        syn::parse_quote!(::ascent::#name_ident)
    }
}
"#;

    fs::write(out_dir.join("mod.rs"), mod_content)
        .expect("Failed to write mod.rs");
}

