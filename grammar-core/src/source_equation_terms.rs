//! Shared constant-depth source reads for sufficient equation-schema checks.
//! These borrow the existing arena; they do not match substituted terms.

use crate::{
    TheoryRuleArenaV1, TheoryTermFormV1, TheoryTermId, TheoryVariableId, TheoryVariableRoleV1,
};

pub(crate) struct SourceEquationTerms<'a> {
    pub(crate) sort: &'a str,
}

impl SourceEquationTerms<'_> {
    pub(crate) fn variable(
        &self,
        arena: &TheoryRuleArenaV1,
        root: TheoryTermId,
    ) -> Option<TheoryVariableId> {
        let node = arena.terms.get(root.0 as usize)?;
        let TheoryTermFormV1::Variable(id) = &node.form else {
            return None;
        };
        let variable = arena.variables.get(id.0 as usize)?;
        (node.sort == self.sort
            && variable.id == *id
            && variable.sort == self.sort
            && variable.role == TheoryVariableRoleV1::Input)
            .then_some(*id)
    }

    pub(crate) fn constructor<const N: usize>(
        &self,
        arena: &TheoryRuleArenaV1,
        root: TheoryTermId,
        expected: &str,
    ) -> Option<[TheoryTermId; N]> {
        let node = arena.terms.get(root.0 as usize)?;
        let TheoryTermFormV1::Constructor { constructor, arguments } = &node.form else {
            return None;
        };
        if node.sort != self.sort || constructor != expected {
            return None;
        }
        arguments.as_slice().try_into().ok()
    }
}
