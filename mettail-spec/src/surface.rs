use std::path::PathBuf;

use proc_macro2::TokenStream;

/// A parsed `.rho` file: imports then one module.
#[derive(Debug, Clone)]
pub struct SurfaceFile {
    pub path: PathBuf,
    pub imports: Vec<Import>,
    pub module: Module,
}

#[derive(Debug, Clone)]
pub struct Import {
    pub path: String,
    pub alias: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub items: Vec<ContentItem>,
}

#[derive(Debug, Clone)]
pub enum ContentItem {
    Extender(ExtenderDecl),
    Language(LanguageDecl),
    Space(SpaceDecl),
    Nested(Module),
    Proc(ProcContent),
}

#[derive(Debug, Clone)]
pub struct ExtenderDecl {
    pub exported: bool,
    pub name: String,
    pub params: Vec<String>,
    pub body: ExtenderExpr,
}

#[derive(Debug, Clone)]
pub struct LanguageDecl {
    pub exported: bool,
    pub name: String,
    pub expr: LanguageExpr,
}

#[derive(Debug, Clone)]
pub struct SpaceDecl {
    pub exported: bool,
    pub name: String,
    pub lang: LanguageExpr,
}

#[derive(Debug, Clone)]
pub struct ProcContent {
    pub lang: String,
    pub raw: String,
}

#[derive(Debug, Clone)]
pub enum ExtenderExpr {
    Empty,
    Union(Box<ExtenderExpr>, Box<ExtenderExpr>),
    Group(Box<ExtenderExpr>),
    Suffix {
        inner: Box<ExtenderExpr>,
        kind: SuffixKind,
        tokens: TokenStream,
        raw: String,
    },
    Semantics {
        inner: Box<ExtenderExpr>,
        target: LanguageExpr,
    },
    Context {
        inner: Box<ExtenderExpr>,
        template: ContextTemplate,
    },
    Call {
        name: String,
        args: Vec<ExtenderExpr>,
    },
    Island(IslandToken),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SuffixKind {
    Types,
    Terms,
    Literals,
    Equations,
    Relations,
    Rewrites,
    Exports,
    Replacements,
}

#[derive(Debug, Clone)]
pub struct ContextTemplate {
    pub raw: String,
    pub insert_offset: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct IslandToken {
    pub lang: String,
    pub body: String,
    pub triple: bool,
}

#[derive(Debug, Clone)]
pub struct LanguageExpr {
    pub segments: Vec<String>,
    pub args: Option<Vec<LanguageExpr>>,
}

impl LanguageExpr {
    pub fn path_only(segments: Vec<String>) -> Self {
        Self { segments, args: None }
    }

    pub fn call(segments: Vec<String>, args: Vec<LanguageExpr>) -> Self {
        Self { segments, args: Some(args) }
    }

    pub fn is_simple_ident(&self) -> Option<&str> {
        if self.args.is_none() && self.segments.len() == 1 {
            Some(&self.segments[0])
        } else {
            None
        }
    }
}
