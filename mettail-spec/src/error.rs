use std::path::PathBuf;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum SpecError {
    #[error("IO error reading {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },

    #[error("parse error in {path}:{line}:{col}: {message}")]
    Parse {
        path: PathBuf,
        line: usize,
        col: usize,
        message: String,
    },

    #[error("import cycle: {}", trace.join(" -> "))]
    ImportCycle { trace: Vec<String> },

    #[error("import not found: {path} (from {from})")]
    ImportNotFound { path: PathBuf, from: PathBuf },

    #[error("resolve error in {module}: {message}")]
    Resolve { module: String, message: String },

    #[error("eval error in {module}: {message}")]
    Eval { module: String, message: String },

    #[error("assemble error: {message}")]
    Assemble { message: String },

    #[error("fragment parse error in {module} ({kind}): {source}")]
    Fragment {
        module: String,
        kind: String,
        #[source]
        source: syn::Error,
    },

    #[error("validation error: {0}")]
    Validation(String),

    #[error("{0}")]
    Other(String),
}

pub type Result<T> = std::result::Result<T, SpecError>;
