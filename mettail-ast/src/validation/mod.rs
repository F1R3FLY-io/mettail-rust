//! Validation and type checking for theory definitions
//!
//! This module provides semantic validation, type checking, and error reporting
//! for theory definitions parsed by the theory! macro.

mod error;
mod typechecker;
mod validator;

pub use error::*;
pub use typechecker::*;
pub use validator::*;
