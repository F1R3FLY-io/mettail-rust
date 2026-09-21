use mettail_ast::grammar::TermParam;
use mettail_ast::types::TypeExpr;
use mettail_prattail::wpda_rule_analysis::binder::term_param as shared;
use syn::Ident;

pub(crate) type TermParamLeafKind<'a> =
    shared::TermParamLeafKind<&'a TermParam, &'a Ident, &'a TypeExpr>;
pub(crate) type TermParamLeaf<'a> = shared::TermParamLeaf<&'a TermParam, &'a Ident, &'a TypeExpr>;

/// Shallow macro-AST access for the shared original declaration worklist.
pub(crate) struct MacroTermParamReader;

impl<'syntax> shared::TermParamReader<'syntax> for MacroTermParamReader {
    type Parameters = &'syntax [TermParam];
    type Param = &'syntax TermParam;
    type Name = &'syntax Ident;
    type Type = &'syntax TypeExpr;

    fn params_len(&self, params: Self::Parameters) -> usize {
        params.len()
    }

    fn param_at(&self, params: Self::Parameters, index: usize) -> Option<Self::Param> {
        params.get(index)
    }

    fn param(
        &self,
        param: Self::Param,
    ) -> shared::TermParamObservation<Self::Name, Self::Parameters, Self::Type> {
        match param {
            TermParam::Simple { name, ty } => shared::TermParamObservation::Simple { name, ty },
            TermParam::GuardBody { name } => shared::TermParamObservation::GuardBody { name },
            TermParam::Abstraction { binder, body, ty } => {
                shared::TermParamObservation::Abstraction { binder, body, ty }
            },
            TermParam::MultiAbstraction { binder, body, ty } => {
                shared::TermParamObservation::MultiAbstraction { binder, body, ty }
            },
            TermParam::Optional { params } => shared::TermParamObservation::Optional { params },
        }
    }
}

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
