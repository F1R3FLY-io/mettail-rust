//! Source construction adapters for the existing sugar and pattern operations.
//!
//! Checked preparation reserves before each action and passes the same meter to
//! generated copying. Original preparation retains the internal oracle behavior.
//! The common constructor match stays in the lowerer: these adapters introduce
//! no grammar, evaluation, binding, or arity convention. Records are logical
//! retention units, not allocator bytes or a claim about physical memory.

use super::*;
use mettail_runtime::{BindingOperation, CheckedBindingLeaf, CheckedIterativeBinding};

pub(super) struct SourceBuilder<'a, 'r> {
    policy: SourcePreparation,
    reservation: &'a mut StorageReservation<'r>,
}

impl<'a, 'r> SourceBuilder<'a, 'r> {
    pub(super) fn new(
        policy: SourcePreparation,
        reservation: &'a mut StorageReservation<'r>,
    ) -> Self {
        Self { policy, reservation }
    }

    pub(super) fn reserve(
        &mut self,
        work: usize,
        records: usize,
    ) -> Result<(), RholangAstLowerError> {
        match self.policy {
            SourcePreparation::Original => Ok(()),
            SourcePreparation::Checked => {
                preparation_scope::reserve_parts(work, records, 0, self.reservation)
            },
        }
    }

    pub(super) fn share<T>(&mut self, source: &Arc<T>) -> Result<Arc<T>, RholangAstLowerError> {
        self.reserve(3, 1)?;
        Ok(Arc::clone(source))
    }

    fn allocate<T>(&mut self, build: impl FnOnce() -> T) -> Result<Arc<T>, RholangAstLowerError> {
        self.reserve(3, 1)?;
        Ok(Arc::new(build()))
    }

    pub(super) fn copy_proc(&mut self, source: &Proc) -> Result<Proc, RholangAstLowerError> {
        match self.policy {
            SourcePreparation::Original => Ok(source.clone()),
            SourcePreparation::Checked => source
                .try_copy_iterative(BindingOperation::Clone, &mut |w, u| (self.reservation)(w, u))
                .map_err(preparation_scope::binding_failure),
        }
    }

    pub(super) fn name_pattern(&mut self, source: &Name) -> Result<Proc, RholangAstLowerError> {
        self.reserve(2, 1)?;
        Ok(match source {
            Name::NVar(var) => Proc::PVar(match self.policy {
                SourcePreparation::Original => var.clone(),
                SourcePreparation::Checked => var
                    .try_copy_binding(BindingOperation::Clone, &mut |w, u| (self.reservation)(w, u))
                    .map_err(preparation_scope::binding_failure)?,
            }),
            Name::NQuote(proc) | Name::NQuoteShort(proc) => return self.copy_proc(proc),
            Name::NQuoteNil => Proc::PZero,
            _ => Proc::Err,
        })
    }

    pub(super) fn quote(&mut self, source: &Arc<Proc>) -> Result<Arc<Name>, RholangAstLowerError> {
        let child = self.share(source)?;
        self.allocate(|| Name::NQuote(child))
    }

    pub(super) fn quote_nil(&mut self) -> Result<Arc<Name>, RholangAstLowerError> {
        let child = self.allocate(|| Proc::PZero)?;
        self.allocate(|| Name::NQuote(child))
    }

    pub(super) fn quote_name(&mut self, source: &Name) -> Result<Arc<Name>, RholangAstLowerError> {
        let child = self.name_pattern(source)?;
        let child = self.allocate(|| child)?;
        self.allocate(|| Name::NQuote(child))
    }

    pub(super) fn list1(
        &mut self,
        first: &Proc,
        rest: &[Proc],
    ) -> Result<Arc<Proc>, RholangAstLowerError> {
        let count = polyadic_count(rest.len())?;
        // Header and all owned element slots are admitted before allocation.
        self.reserve(
            2,
            count
                .checked_add(1)
                .ok_or(RholangAstLowerError::PreparationSizeOverflow)?,
        )?;
        let mut items = Vec::with_capacity(count);
        items.push(self.copy_proc(first)?);
        self.reserve(1, 1)?;
        let mut rest = rest.iter();
        loop {
            // Includes the terminal next; no uncharged scan of the remaining list.
            self.reserve(2, 0)?;
            let Some(item) = rest.next() else { break };
            items.push(self.copy_proc(item)?);
        }
        self.list(items)
    }

    fn list(&mut self, items: Vec<Proc>) -> Result<Arc<Proc>, RholangAstLowerError> {
        let list = self.allocate(|| List::ListLit(items))?;
        self.allocate(|| Proc::CastList(list))
    }

    pub(super) fn empty(&mut self) -> Result<Arc<Proc>, RholangAstLowerError> {
        self.reserve(1, 1)?;
        self.list(Vec::new())
    }
}

fn polyadic_count(rest: usize) -> Result<usize, RholangAstLowerError> {
    rest.checked_add(1)
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)
}

#[cfg(test)]
#[path = "preparation_source_tests.rs"]
mod tests;
