use mettail_ast::grammar::TermParam;
use mettail_ast::types::TypeExpr;
use mettail_prattail::wpda_rule_analysis::binder::term_param as shared;
use syn::Ident;

pub(crate) type TermParamLeafKind<'a> =
    shared::TermParamLeafKind<&'a TermParam, &'a Ident, &'a TypeExpr>;
pub(crate) type TermParamLeaf<'a> = shared::TermParamLeaf<&'a TermParam, &'a Ident, &'a TypeExpr>;

pub(crate) use mettail_ast::grammar::AstTermParamReader as MacroTermParamReader;

/// Keep the macro-facing iterator API while executing the shared worklist.
pub(crate) struct TermParamLeaves<'a> {
    inner: shared::TermParamLeaves<'a, MacroTermParamReader>,
}

impl<'a> TermParamLeaves<'a> {
    pub(crate) fn new(params: &'a [TermParam], is_optional: bool) -> Self {
        Self {
            inner: shared::TermParamLeaves::new(&MacroTermParamReader, params, is_optional),
        }
    }
}

impl<'a> Iterator for TermParamLeaves<'a> {
    type Item = TermParamLeaf<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

#[cfg(test)]
#[path = "../../tests/support/term_param_walk_recursive_oracle.rs"]
mod recursive_oracle;
