use crate::island::plugin::ProcGst;
use crate::surface::ContextTemplate;
use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::{
    Equation, LangType, LanguageDef, LiteralBlock, LogicBlock, RewriteRule,
};
use std::collections::BTreeSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Serialize)]
pub enum SemanticsTarget {
    Rust,
    #[default]
    Unknown,
}

/// Rholang (or other) process island lowered to GST (Phase 3).
#[derive(Debug, Clone, serde::Serialize)]
pub struct ProcArtifact {
    pub lang: String,
    pub gst: ProcGst,
}

pub struct Ntir {
    pub name: String,
    pub types: Vec<LangType>,
    pub literals: Option<LiteralBlock>,
    pub terms: Vec<GrammarRule>,
    pub equations: Vec<Equation>,
    pub rewrites: Vec<RewriteRule>,
    pub logic: Option<LogicBlock>,
    pub semantics: SemanticsTarget,
    pub context_template: Option<ContextTemplate>,
    pub lowered_context: Option<String>,
    pub rust_island_snippets: Vec<String>,
    pub proc_artifacts: Vec<ProcArtifact>,
    pub sources: TheorySources,
    pub hash: String,
}

/// Raw source text for each `language!` section (preserved for Rust projection).
#[derive(Clone, Default)]
pub struct TheorySources {
    pub types: Option<String>,
    pub literals: Option<String>,
    pub terms: Option<String>,
    pub equations: Option<String>,
    pub rewrites: Option<String>,
    pub logic: Option<String>,
}

/// Intermediate assembled presentation before naming/hashing.
#[derive(Clone, Default)]
pub struct Presentation {
    pub types: Vec<LangType>,
    pub literals: Option<LiteralBlock>,
    pub terms: Vec<GrammarRule>,
    pub equations: Vec<Equation>,
    pub rewrites: Vec<RewriteRule>,
    pub logic: Option<LogicBlock>,
    pub semantics: SemanticsTarget,
    pub context_template: Option<ContextTemplate>,
    pub rust_island_snippets: Vec<String>,
    pub proc_artifacts: Vec<ProcArtifact>,
    pub sources: TheorySources,
    pub term_label_conflicts: BTreeSet<String>,
}

impl Presentation {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn into_ntir(self, name: String, lowered_context: Option<String>) -> Ntir {
        let hash = content_hash(&self);
        Ntir {
            name,
            types: self.types,
            literals: self.literals,
            terms: self.terms,
            equations: self.equations,
            rewrites: self.rewrites,
            logic: self.logic,
            semantics: self.semantics,
            context_template: self.context_template,
            lowered_context,
            rust_island_snippets: self.rust_island_snippets,
            proc_artifacts: self.proc_artifacts,
            sources: self.sources,
            hash,
        }
    }
}

impl Ntir {
    pub fn to_language_def(&self) -> LanguageDef {
        mettail_ast::fragments::language_def_from_parts(
            syn::Ident::new(&self.name, proc_macro2::Span::call_site()),
            self.types.clone(),
            self.literals.clone(),
            self.terms.clone(),
            self.equations.clone(),
            self.rewrites.clone(),
            self.logic.clone(),
        )
    }
}

pub fn content_hash(p: &Presentation) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&serde_json::to_vec(&PresentationHashView::from(p)).unwrap_or_default());
    hasher.finalize().to_hex().to_string()
}

#[derive(serde::Serialize)]
pub struct NtirSummary {
    pub name: String,
    pub hash: String,
    pub semantics: SemanticsTarget,
    pub types: Vec<String>,
    pub term_labels: Vec<String>,
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct SpaceSummary {
    pub name: String,
    pub language: String,
    pub language_hash: String,
}

impl Ntir {
    pub fn summary(&self) -> NtirSummary {
        NtirSummary {
            name: self.name.clone(),
            hash: self.hash.clone(),
            semantics: self.semantics,
            types: self.types.iter().map(|t| t.name.to_string()).collect(),
            term_labels: self.terms.iter().map(|r| r.label.to_string()).collect(),
        }
    }
}

#[derive(serde::Serialize)]
struct PresentationHashView {
    types: usize,
    terms: usize,
    equations: usize,
    rewrites: usize,
    semantics: SemanticsTarget,
    type_names: Vec<String>,
    term_labels: Vec<String>,
    equation_names: Vec<String>,
    rewrite_names: Vec<String>,
}

impl From<&Presentation> for PresentationHashView {
    fn from(p: &Presentation) -> Self {
        Self {
            types: p.types.len(),
            terms: p.terms.len(),
            equations: p.equations.len(),
            rewrites: p.rewrites.len(),
            semantics: p.semantics,
            type_names: p.types.iter().map(|t| t.name.to_string()).collect(),
            term_labels: p.terms.iter().map(|r| r.label.to_string()).collect(),
            equation_names: p.equations.iter().map(|e| e.name.to_string()).collect(),
            rewrite_names: p.rewrites.iter().map(|r| r.name.to_string()).collect(),
        }
    }
}
