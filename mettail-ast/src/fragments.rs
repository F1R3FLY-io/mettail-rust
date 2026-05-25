//! Parse theory fragment bodies (brace contents) for `.rho` and other hosts.

use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::Parser;
use syn::Result as SynResult;

use crate::grammar::parse_terms;
use crate::grammar::GrammarRule;
use crate::language::{
    parse_equations, parse_literals, parse_logic, parse_rewrites, parse_types, Equation, LangType,
    LanguageDef, LiteralBlock, LogicBlock, RewriteRule,
};

fn wrap_keyword_body(keyword: &str, inner: TokenStream) -> TokenStream {
    let kw = syn::Ident::new(keyword, proc_macro2::Span::call_site());
    quote! { #kw { #inner } }
}

/// Parse the inside of a `types { … }` block (no outer keyword/braces).
pub fn parse_types_fragment(inner: TokenStream) -> SynResult<Vec<LangType>> {
    parse_types.parse2(wrap_keyword_body("types", inner))
}

/// Parse the inside of a `terms { … }` block.
pub fn parse_terms_fragment(inner: TokenStream) -> SynResult<Vec<GrammarRule>> {
    parse_terms.parse2(wrap_keyword_body("terms", inner))
}

/// Parse the inside of a `literals { … }` block.
pub fn parse_literals_fragment(inner: TokenStream) -> SynResult<LiteralBlock> {
    parse_literals.parse2(wrap_keyword_body("literals", inner))
}

/// Parse the inside of an `equations { … }` block.
pub fn parse_equations_fragment(inner: TokenStream) -> SynResult<Vec<Equation>> {
    parse_equations.parse2(wrap_keyword_body("equations", inner))
}

/// Parse the inside of a `rewrites { … }` block.
pub fn parse_rewrites_fragment(inner: TokenStream) -> SynResult<Vec<RewriteRule>> {
    parse_rewrites.parse2(wrap_keyword_body("rewrites", inner))
}

/// Parse the inside of a `logic { … }` block.
pub fn parse_logic_fragment(inner: TokenStream) -> SynResult<LogicBlock> {
    parse_logic.parse2(wrap_keyword_body("logic", inner))
}

/// Parse a `relations { … }` block (stored as logic content for Phase 1).
pub fn parse_relations_fragment(inner: TokenStream) -> SynResult<LogicBlock> {
    parse_logic.parse2(wrap_keyword_body("logic", inner))
}

/// Build a [`LanguageDef`] from assembled fragments (for validation).
pub fn language_def_from_parts(
    name: syn::Ident,
    types: Vec<LangType>,
    literals: Option<LiteralBlock>,
    terms: Vec<GrammarRule>,
    equations: Vec<Equation>,
    rewrites: Vec<RewriteRule>,
    logic: Option<LogicBlock>,
) -> LanguageDef {
    LanguageDef {
        name,
        options: std::collections::HashMap::new(),
        types,
        literals,
        terms,
        equations,
        rewrites,
        logic,
    }
}
