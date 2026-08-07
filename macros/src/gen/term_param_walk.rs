use mettail_ast::grammar::TermParam;
use mettail_ast::types::TypeExpr;
use syn::Ident;

/// A non-grouping term parameter, with the variant-specific fields exposed by type.
#[derive(Clone, Copy)]
pub(crate) enum TermParamLeafKind<'a> {
    Simple {
        param: &'a TermParam,
        name: &'a Ident,
        ty: &'a TypeExpr,
    },
    GuardBody {
        param: &'a TermParam,
        name: &'a Ident,
    },
    Abstraction {
        param: &'a TermParam,
        binder: &'a Ident,
        body: &'a Ident,
        ty: &'a TypeExpr,
    },
    MultiAbstraction {
        param: &'a TermParam,
        binder: &'a Ident,
        body: &'a Ident,
        ty: &'a TypeExpr,
    },
}

impl<'a> TermParamLeafKind<'a> {
    #[cfg(test)]
    pub(crate) fn param(self) -> &'a TermParam {
        match self {
            Self::Simple { param, .. }
            | Self::GuardBody { param, .. }
            | Self::Abstraction { param, .. }
            | Self::MultiAbstraction { param, .. } => param,
        }
    }
}

/// One non-grouping term parameter encountered in declaration preorder.
#[derive(Clone, Copy)]
pub(crate) struct TermParamLeaf<'a> {
    pub(crate) kind: TermParamLeafKind<'a>,
    /// True once the path to this leaf has entered an `Optional` group.
    pub(crate) is_optional: bool,
}

/// Stack-safe declaration-order traversal over the leaves of nested term
/// parameters. `Optional` is structural and therefore does not itself yield an
/// item; each enclosed leaf is yielded with `is_optional = true`.
pub(crate) struct TermParamLeaves<'a> {
    work: Vec<(&'a TermParam, bool)>,
}

impl<'a> TermParamLeaves<'a> {
    pub(crate) fn new(params: &'a [TermParam], is_optional: bool) -> Self {
        Self {
            work: params
                .iter()
                .rev()
                .map(|param| (param, is_optional))
                .collect(),
        }
    }
}

impl<'a> Iterator for TermParamLeaves<'a> {
    type Item = TermParamLeaf<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((param, is_optional)) = self.work.pop() {
            if let TermParam::Optional { params } = param {
                self.work
                    .extend(params.iter().rev().map(|param| (param, true)));
                continue;
            }
            let kind = match param {
                TermParam::Simple { name, ty } => TermParamLeafKind::Simple { param, name, ty },
                TermParam::GuardBody { name } => TermParamLeafKind::GuardBody { param, name },
                TermParam::Abstraction { binder, body, ty } => {
                    TermParamLeafKind::Abstraction { param, binder, body, ty }
                },
                TermParam::MultiAbstraction { binder, body, ty } => {
                    TermParamLeafKind::MultiAbstraction { param, binder, body, ty }
                },
                TermParam::Optional { .. } => continue,
            };
            return Some(TermParamLeaf { kind, is_optional });
        }
        None
    }
}

#[cfg(test)]
#[path = "../../tests/support/term_param_walk_recursive_oracle.rs"]
mod recursive_oracle;
