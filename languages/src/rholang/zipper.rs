//! Rholang aliases for the language-neutral read/write zipper carriers.
//!
//! Executable zipper semantics live in f1r3node's native `EPathMap` method table. These compact
//! carriers remain because the generated AST and structural receive matcher can represent zipper
//! literals without duplicating PathMap operations in the language crate.

pub use mettail_runtime::{ReadZipperLit, WriteZipperLit};
