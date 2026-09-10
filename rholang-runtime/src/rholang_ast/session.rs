//! Synchronous ownership of the existing whole-body lowerer's side outputs.
//!
//! This internal boundary is not public source admission: caller-import
//! validation, preparation budgets and provider binding are separate checks.
//! No parser, evaluator or alternate lowering traversal is introduced here.

use std::cell::Cell;
use std::marker::PhantomData;
use std::rc::Rc;

use super::*;

/// One successful driver's owned output, not a prepared-program certificate.
pub(crate) struct DirectLoweringOutput {
    pub(crate) par: Par,
    pub(crate) folds: Vec<FoldSpec>,
    pub(crate) guard_report: GuardDischargeReport,
}

thread_local! {
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
}

/// Private and non-Send: the bracket cannot migrate between threads.
pub(super) struct SessionGuard(PhantomData<Rc<()>>);

impl SessionGuard {
    fn enter() -> Result<Self, RholangAstLowerError> {
        let already_active = ACTIVE.with(|active| active.replace(true));
        if already_active {
            return Err(RholangAstLowerError::ReentrantLoweringSession);
        }
        // Establish the unwind guard before clearing any stale inactive output.
        let guard = Self(PhantomData);
        clear_held_fold_sites_inner();
        clear_guard_discharge_report_inner();
        Ok(guard)
    }

    /// Only the live owner can enter the machine without the legacy gate.
    pub(super) fn drive(
        &self,
        seed: Seed<'_>,
        context: &BoundEnv,
    ) -> Result<Par, RholangAstLowerError> {
        drive_machine(seed, context)
    }

    fn drive_with_budget<C: FnMut() -> bool>(
        &self,
        seed: Seed<'_>,
        context: &BoundEnv,
        budget: &mut mettail_rholang_codegen::ReflectedCodecBudget<'_, C>,
    ) -> Result<Par, RholangAstLowerError> {
        let mut reserve = |work, bytes| {
            budget
                .charge(work, bytes)
                .map_err(RholangAstLowerError::Preparation)
        };
        drive_machine_with_reservation(seed, context, &mut reserve)
    }
}

impl Drop for SessionGuard {
    fn drop(&mut self) {
        clear_held_fold_sites_inner();
        clear_guard_discharge_report_inner();
        ACTIVE.with(|active| active.set(false));
    }
}

pub(super) fn ensure_inactive() -> Result<(), RholangAstLowerError> {
    match ACTIVE.with(Cell::get) {
        true => Err(RholangAstLowerError::ReentrantLoweringSession),
        false => Ok(()),
    }
}

pub(super) fn assert_legacy_output_access() {
    assert!(
        ensure_inactive().is_ok(),
        "legacy output access is forbidden during an owned lowering session"
    );
}

pub(super) fn with_owned_outputs(
    lower: impl FnOnce(&SessionGuard) -> Result<Par, RholangAstLowerError>,
) -> Result<DirectLoweringOutput, RholangAstLowerError> {
    let guard = SessionGuard::enter()?;
    let result = lower(&guard);
    let folds = take_held_fold_sites_inner();
    let guard_report = take_guard_discharge_report_inner();
    result.map(|par| DirectLoweringOutput { par, folds, guard_report })
}

/// Preserve every supplied context field while explicitly selecting Public
/// resolution. In particular, production guard options do not imply this mode.
pub(crate) fn lower_public_body(
    proc: &Proc,
    mut context: BoundEnv,
) -> Result<DirectLoweringOutput, RholangAstLowerError> {
    with_owned_outputs(|owner| {
        context.admission = SourceAdmissionMode::Public;
        owner.drive(Seed::Body(proc), &context)
    })
}

/// Internal bounded-storage composition of the same owned driver. This is
/// not public admission: source, constructor and side-output precharges must
/// also be composed before the node frontend can publish a prepared artifact.
pub(crate) fn lower_public_body_with_budget<C: FnMut() -> bool>(
    proc: &Proc,
    mut context: BoundEnv,
    budget: &mut mettail_rholang_codegen::ReflectedCodecBudget<'_, C>,
) -> Result<DirectLoweringOutput, RholangAstLowerError> {
    with_owned_outputs(|owner| {
        context.admission = SourceAdmissionMode::Public;
        owner.drive_with_budget(Seed::Body(proc), &context, budget)
    })
}

pub(super) fn checked_fold_site_index(index: usize) -> Result<u8, RholangAstLowerError> {
    u8::try_from(index).map_err(|_| RholangAstLowerError::FoldSiteIndexOverflow { index })
}

#[cfg(test)]
#[path = "session_tests.rs"]
mod tests;
