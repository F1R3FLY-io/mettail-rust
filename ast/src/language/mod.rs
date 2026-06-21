use proc_macro2::TokenStream;
use syn::{
    ext::IdentExt,
    parse::{Parse, ParseStream},
    GenericArgument, Ident, Result as SynResult, Token, Type,
};

use super::grammar::{parse_terms, GrammarRule};
use super::pattern::{Pattern, PatternTerm};
use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;

mod model;
pub use model::*;
mod parse;
pub use parse::*;

#[cfg(test)]
mod tests;
