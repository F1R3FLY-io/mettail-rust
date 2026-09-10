//! Node-independent Rholang construction contracts.
//!
//! This crate factors the target of the existing generated-Rholang lowerer.
//! It does not define another language, parser or evaluator. Construction of
//! the initial primitive family is implemented here; source admission and the
//! complete owned frontend envelope remain separate integration boundaries.
#![forbid(unsafe_code)]

pub mod arena;
pub mod construction;
