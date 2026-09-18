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
    pub(super) fn push_proc_copy(
        &mut self,
        values: &mut Vec<Proc>,
        source: &Proc,
    ) -> Result<(), RholangAstLowerError> {
        self.reserve(3, 1)?;
        values
            .len()
            .checked_add(1)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
        let copied = self.copy_proc(source)?;
        values.push(copied);
        Ok(())
    }

    pub(super) fn push_name_copy(
        &mut self,
        values: &mut Vec<Name>,
        source: &Name,
    ) -> Result<(), RholangAstLowerError> {
        self.reserve(3, 1)?;
        values
            .len()
            .checked_add(1)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
        let copied = match self.policy {
            SourcePreparation::Original => source.clone(),
            SourcePreparation::Checked => source
                .try_copy_iterative(BindingOperation::Clone, &mut |w, u| (self.reservation)(w, u))
                .map_err(preparation_scope::binding_failure)?,
        };
        values.push(copied);
        Ok(())
    }

    pub(super) fn copy_string(&mut self, source: &String) -> Result<String, RholangAstLowerError> {
        match self.policy {
            SourcePreparation::Original => Ok(source.clone()),
            SourcePreparation::Checked => source
                .try_copy_binding(BindingOperation::Clone, &mut |w, u| (self.reservation)(w, u))
                .map_err(preparation_scope::binding_failure),
        }
    }

    pub(super) fn take_children<T>(
        &mut self,
        values: &mut Vec<T>,
        base: usize,
        expected: usize,
    ) -> Result<Vec<T>, RholangAstLowerError> {
        self.reserve(3, 0)?;
        if values.len().checked_sub(base) != Some(expected) {
            return Err(RholangAstLowerError::UnsupportedProc(
                "invalid body replacement child roster",
            ));
        }
        let slots = expected
            .checked_add(1)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
        let work = expected
            .checked_add(3)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
        self.reserve(work, slots)?;
        Ok(values.split_off(base))
    }

    pub(super) fn rebuild_parallel(
        &mut self,
        source: &mettail_runtime::HashBag<Proc>,
        children: Vec<Proc>,
    ) -> Result<mettail_runtime::HashBag<Proc>, RholangAstLowerError> {
        preparation_rebuild::parallel(source, children, self.policy, self.reservation)
    }

    pub(super) fn rebuild_map(
        &mut self,
        source: &mettail_runtime::HashMapLit<Proc, Proc>,
        pairs: Vec<(Proc, Proc)>,
    ) -> Result<mettail_runtime::HashMapLit<Proc, Proc>, RholangAstLowerError> {
        preparation_rebuild::map(source, pairs, self.policy, self.reservation)
    }

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

    pub(super) fn worklist<T>(&mut self) -> Result<Vec<T>, RholangAstLowerError> {
        self.reserve(1, 1)?;
        Ok(Vec::new())
    }

    pub(super) fn push<T>(
        &mut self,
        work: &mut Vec<T>,
        task: impl FnOnce() -> T,
    ) -> Result<(), RholangAstLowerError> {
        self.reserve(3, 1)?;
        work.len()
            .checked_add(1)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
        work.push(task());
        Ok(())
    }

    pub(super) fn pop<T>(&mut self, work: &mut Vec<T>) -> Result<Option<T>, RholangAstLowerError> {
        // The terminal pop is a paid cancellation point too.
        self.reserve(2, 0)?;
        Ok(work.pop())
    }

    pub(super) fn reverse_batch<T>(
        &mut self,
        work: &mut [T],
        start: usize,
    ) -> Result<(), RholangAstLowerError> {
        match self.policy {
            SourcePreparation::Original => {
                work[start..].reverse();
                Ok(())
            },
            SourcePreparation::Checked => {
                mettail_runtime::try_reverse_task_batch(work, start, &mut |w, u| {
                    (self.reservation)(w, u)
                })
                .map_err(preparation_scope::binding_failure)
            },
        }
    }

    pub(super) fn push_slice_reversed<'s, T>(
        &mut self,
        work: &mut Vec<T>,
        items: &'s [Proc],
        mut task: impl FnMut(&'s Proc) -> T,
    ) -> Result<(), RholangAstLowerError> {
        self.reserve(2, 1)?;
        let mut items = items.iter().rev();
        loop {
            self.reserve(2, 0)?;
            let Some(item) = items.next() else { break };
            self.push(work, || task(item))?;
        }
        Ok(())
    }

    pub(super) fn push_bag_reversed<'s, T>(
        &mut self,
        work: &mut Vec<T>,
        items: &'s mettail_runtime::HashBag<Proc>,
        mut task: impl FnMut(&'s Proc) -> T,
    ) -> Result<(), RholangAstLowerError> {
        self.reserve(1, 1)?;
        let start = work.len();
        match self.policy {
            SourcePreparation::Original => work.extend(items.iter_elements().map(task)),
            SourcePreparation::Checked => items
                .try_for_each_entry(&mut |w, u| (self.reservation)(w, u), |item, count, reserve| {
                    let mut build = SourceBuilder::new(SourcePreparation::Checked, reserve);
                    // Expand occurrences, not distinct keys. A stored zero count
                    // schedules nothing, just as the original iter_elements does.
                    build
                        .reserve(1, 1)
                        .map_err(mettail_runtime::BindingFailure::Reservation)?;
                    let mut occurrences = 0..count;
                    loop {
                        build
                            .reserve(2, 0)
                            .map_err(mettail_runtime::BindingFailure::Reservation)?;
                        let Some(_) = occurrences.next() else { break };
                        build
                            .push(work, || task(item))
                            .map_err(mettail_runtime::BindingFailure::Reservation)?;
                    }
                    Ok(())
                })
                .map_err(preparation_scope::binding_failure)?,
        }
        self.reverse_batch(work, start)
    }

    pub(super) fn push_map_reversed<'s, T>(
        &mut self,
        work: &mut Vec<T>,
        entries: &'s mettail_runtime::HashMapLit<Proc, Proc>,
        mut task: impl FnMut(&'s Proc) -> T,
    ) -> Result<(), RholangAstLowerError> {
        self.reserve(1, 1)?;
        let start = work.len();
        match self.policy {
            SourcePreparation::Original => {
                for (key, value) in entries.iter() {
                    work.push(task(key));
                    work.push(task(value));
                }
            },
            SourcePreparation::Checked => entries
                .try_for_each_entry(&mut |w, u| (self.reservation)(w, u), |key, value, reserve| {
                    let mut build = SourceBuilder::new(SourcePreparation::Checked, reserve);
                    build.push(work, || task(key)).map_err(|error| {
                        mettail_runtime::NativeComparisonFailure::Admission(
                            mettail_runtime::BindingFailure::Reservation(error),
                        )
                    })?;
                    build.push(work, || task(value)).map_err(|error| {
                        mettail_runtime::NativeComparisonFailure::Admission(
                            mettail_runtime::BindingFailure::Reservation(error),
                        )
                    })?;
                    Ok(())
                })
                .map_err(|error| preparation_scope::binding_failure(error.into()))?,
        }
        self.reverse_batch(work, start)
    }

    pub(super) fn desugar(&mut self, proc: &Proc) -> Result<Option<Proc>, RholangAstLowerError> {
        desugar_surface_sugar_node_preparing(proc, self.policy, self.reservation)
    }

    pub(super) fn keep<'s>(
        &mut self,
        arena: &'s Arena<Proc>,
        node: Proc,
    ) -> Result<&'s Proc, RholangAstLowerError> {
        self.reserve(3, 1)?;
        Ok(arena.alloc(node))
    }

    pub(super) fn original_only(
        &mut self,
        constructor: &'static str,
    ) -> Result<(), RholangAstLowerError> {
        match self.policy {
            SourcePreparation::Original => Ok(()),
            SourcePreparation::Checked => Err(preparation_scope::binding_failure(
                mettail_runtime::BindingFailure::UnsupportedConstructor {
                    category: "Proc",
                    constructor,
                },
            )),
        }
    }

    pub(super) fn selector_level(
        &mut self,
        node: &FltNode,
        env: &BoundEnv,
    ) -> Result<Option<usize>, RholangAstLowerError> {
        if self.policy == SourcePreparation::Original {
            return Ok(flt_selector_level(node, env));
        }
        self.reserve(1, 0)?;
        let Var::Free(selector) = &node.selector.0 else {
            return Ok(None);
        };
        if !mettail_runtime::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
            return Err(preparation_scope::binding_failure(
                mettail_runtime::BindingFailure::UnsupportedProfile,
            ));
        }
        self.reserve(1, 0)?;
        let work = identity_lookup_work(env.binders.len(), env.binders.capacity())?;
        self.reserve(work, 0)?;
        // Only moniker identity resolves a selector. Neither pretty names nor
        // the separate FLT-hole environment may substitute for this lookup.
        Ok(env.binders.get(selector).copied())
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

    pub(super) fn bind_pattern(
        &mut self,
        bind: &InputBind,
    ) -> Result<Option<Proc>, RholangAstLowerError> {
        self.reserve(2, 0)?;
        Ok(match bind {
            InputBind::InputBind(lhs, _)
            | InputBind::InputBindPersistent(lhs, _)
            | InputBind::InputBindQuery(lhs, _, _) => Some(self.name_pattern(lhs)?),
            InputBind::InputBindQuoted(pattern, _)
            | InputBind::InputBindQuotedPersistent(pattern, _)
            | InputBind::InputBindQuotedQuery(pattern, _, _) => Some(self.copy_proc(pattern)?),
            InputBind::InputBindPolyadic(first, rest, _)
            | InputBind::InputBindPersistentPolyadic(first, rest, _) => {
                let count = polyadic_count(rest.len())?;
                let records = polyadic_count(count)?;
                self.reserve(3, records)?;
                let mut items = Vec::with_capacity(count);
                items.push(self.name_pattern(first)?);
                self.reserve(1, 1)?;
                let mut rest = rest.iter();
                loop {
                    self.reserve(2, 0)?;
                    let Some(item) = rest.next() else { break };
                    let pattern = self.name_pattern(item)?;
                    self.reserve(1, 0)?;
                    items.push(pattern);
                }
                let list = self.allocate(|| List::ListLit(items))?;
                self.reserve(1, 1)?;
                Some(Proc::CastList(list))
            },
            InputBind::InputBindEmpty(_)
            | InputBind::InputBindEmptyPersistent(_)
            | InputBind::InputBindEmptyQuery(_, _) => {
                self.reserve(1, 1)?;
                let list = self.allocate(|| List::ListLit(Vec::new()))?;
                self.reserve(1, 1)?;
                Some(Proc::CastList(list))
            },
            _ => None,
        })
    }

    pub(super) fn bind_pattern_variable(
        &mut self,
        state: &mut PatternState,
        variable: &FreeVar<String>,
    ) -> Result<i32, RholangAstLowerError> {
        self.reserve(3, 0)?;
        let index = state.counter;
        let next = index
            .checked_add(1)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
        state
            .binders
            .len()
            .checked_add(1)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
        let variable = match self.policy {
            SourcePreparation::Original => variable.clone(),
            SourcePreparation::Checked => variable
                .try_copy_binding(BindingOperation::Clone, &mut |w, u| (self.reservation)(w, u))
                .map_err(preparation_scope::binding_failure)?,
        };
        // No state mutation happens until both the owned identity and its slot
        // are admitted. The existing left-to-right free-variable numbering stays.
        self.reserve(3, 1)?;
        state.binders.push(Binder(variable));
        state.counter = next;
        Ok(index)
    }

    pub(super) fn for_row<'s>(
        &mut self,
        row: &'s ForRow,
    ) -> Result<(Vec<&'s InputBind>, bool, Option<&'s Proc>), RholangAstLowerError> {
        self.reserve(2, 0)?;
        let (first, rest, condition) = match row {
            ForRow::ForRowSingleNoWhere(first) => (first.as_ref(), &[][..], None),
            ForRow::ForRowSingleWhere(first, condition) => {
                (first.as_ref(), &[][..], Some(condition.as_ref()))
            },
            ForRow::ForRowNoWhere(first, rest) => (first.as_ref(), rest.as_slice(), None),
            ForRow::ForRowWhere(first, rest, condition) => {
                (first.as_ref(), rest.as_slice(), Some(condition.as_ref()))
            },
            _ => return Err(RholangAstLowerError::UnsupportedProc("non-ground for-row")),
        };
        let count = polyadic_count(rest.len())?;
        self.reserve(3, polyadic_count(count)?)?;
        let mut binds = Vec::with_capacity(count);
        binds.push(first);
        let mut persistent = is_persistent_bind(first);
        self.reserve(1, 1)?;
        let mut rest = rest.iter();
        loop {
            self.reserve(2, 0)?;
            let Some(bind) = rest.next() else { break };
            self.reserve(3, 0)?;
            binds.push(bind);
            persistent = persistent || is_persistent_bind(bind);
        }
        Ok((binds, persistent, condition))
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

/// Native get on the clean, immutable identity map built by BoundEnv.
///
/// No deletion/tombstones enter that map. NativeHashBagExtent therefore bounds
/// buckets by twice its capacity; ProbeControl/CandidateCover bound original
/// probe groups and distinct candidate callbacks. StageCharge supplies
/// 22*groups + 2*entries + 17 control groups. AdmittedIdentityComparison's
/// fresh SipHasher13(u32) path supplies 31+3 hashing groups; the native get
/// shell supplies 13, and FreeVar Eq plus callback forwarding supplies 12 per
/// candidate. This is logical work, not instructions, elapsed time or RSS.
/// Empty get never hashes/probes, even when its map retained an allocation.
fn identity_lookup_work(entries: usize, capacity: usize) -> Result<usize, RholangAstLowerError> {
    if entries == 0 {
        return Ok(5);
    }
    let overflow = || RholangAstLowerError::PreparationSizeOverflow;
    let buckets = capacity.checked_mul(2).ok_or_else(overflow)?.max(1);
    let groups = (buckets / 16).max(1);
    let probes = groups.checked_mul(22).ok_or_else(overflow)?;
    let candidates = entries.checked_mul(14).ok_or_else(overflow)?;
    64usize
        .checked_add(probes)
        .and_then(|work| work.checked_add(candidates))
        .ok_or_else(overflow)
}

#[cfg(test)]
#[path = "preparation_source_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "preparation_body_tests.rs"]
mod body_tests;
