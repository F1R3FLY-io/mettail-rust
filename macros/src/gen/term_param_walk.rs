use mettail_ast::grammar::TermParam;

/// One non-grouping term parameter encountered in declaration preorder.
#[derive(Clone, Copy)]
pub(crate) struct TermParamLeaf<'a> {
    pub(crate) param: &'a TermParam,
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
            return Some(TermParamLeaf { param, is_optional });
        }
        None
    }
}

#[cfg(test)]
#[path = "../../tests/support/term_param_walk_recursive_oracle.rs"]
mod recursive_oracle;
