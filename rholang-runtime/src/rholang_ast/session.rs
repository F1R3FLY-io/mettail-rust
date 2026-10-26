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
    static ALTERNATIVE_FOLDS: std::cell::RefCell<Option<AlternativeFolds>> = const {
        std::cell::RefCell::new(None)
    };
}

#[derive(Default)]
struct AlternativeFolds {
    next: usize,
    candidates: Vec<Vec<u8>>,
}

pub(super) struct AlternativeFoldScope(PhantomData<Rc<()>>);

impl AlternativeFoldScope {
    pub(super) fn enter() -> Result<Self, RholangAstLowerError> {
        ALTERNATIVE_FOLDS.with(|state| {
            let mut state = state.borrow_mut();
            if state.is_some() {
                return Err(RholangAstLowerError::ReentrantLoweringSession);
            }
            *state = Some(AlternativeFolds::default());
            Ok(Self(PhantomData))
        })
    }

    pub(super) fn begin_alternative(&self) {
        ALTERNATIVE_FOLDS.with(|state| {
            state
                .borrow_mut()
                .as_mut()
                .expect("live alternative scope")
                .next = 0;
        });
    }
}

impl Drop for AlternativeFoldScope {
    fn drop(&mut self) {
        ALTERNATIVE_FOLDS.with(|state| *state.borrow_mut() = None);
    }
}

pub(super) fn register_fold_site(
    kind: FoldKind,
    width: i64,
    fingerprint: &str,
) -> Result<u8, RholangAstLowerError> {
    HELD_FOLD_SITES.with(|sites| {
        ALTERNATIVE_FOLDS.with(|state| {
            let mut sites = sites.borrow_mut();
            let mut state = state.borrow_mut();
            let candidates = state.as_mut().map(|state| {
                let ordinal = state.next;
                state.next += 1;
                if ordinal == state.candidates.len() {
                    state.candidates.push(Vec::new());
                }
                &mut state.candidates[ordinal]
            });
            if let Some(index) = candidates.as_ref().and_then(|candidates| {
                candidates.iter().copied().find(|&index| {
                    let spec = &sites[usize::from(index)];
                    spec.kind == kind && spec.width == width && spec.fingerprint == fingerprint
                })
            }) {
                return Ok(index);
            }
            let site_index = checked_fold_site_index(sites.len())?;
            sites.push(FoldSpec {
                kind,
                width,
                site_index,
                fingerprint: fingerprint.to_owned(),
            });
            if let Some(candidates) = candidates {
                candidates.push(site_index);
            }
            Ok(site_index)
        })
    })
}

/// Private and non-Send: the bracket cannot migrate between threads.
pub(super) struct SessionGuard(PhantomData<Rc<()>>);

impl SessionGuard {
    fn enter() -> Result<Self, RholangAstLowerError> {
        if ALTERNATIVE_FOLDS.with(|state| state.borrow().is_some()) {
            return Err(RholangAstLowerError::ReentrantLoweringSession);
        }
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
        drive_machine_preparing(seed, context, &mut reserve, SourcePreparation::Checked, None)
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
        ensure_inactive().is_ok() && ALTERNATIVE_FOLDS.with(|state| state.borrow().is_none()),
        "legacy output access is forbidden during an owned lowering or alternative session"
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

/// Check the closed source profile before entering the same bounded-storage
/// owned driver. Constructor and side-output precharges must still be composed
/// before the node frontend can publish a prepared artifact.
pub(crate) fn lower_public_body_with_budget<C: FnMut() -> bool>(
    proc: &Proc,
    mut context: BoundEnv,
    budget: &mut mettail_rholang_codegen::ReflectedCodecBudget<'_, C>,
) -> Result<DirectLoweringOutput, RholangAstLowerError> {
    with_owned_outputs(|owner| {
        context.admission = SourceAdmissionMode::Public;
        proc.try_check_source_profile(
            mettail_languages::rholang::source_profile::SourceRole::Term,
            &mettail_languages::rholang::source_profile::RholangSourceProfile,
            &mut |work, bytes| budget.charge(work, bytes),
        )
        .map_err(RholangAstLowerError::SourceProfile)?;
        owner.drive_with_budget(Seed::Body(proc), &context, budget)
    })
}

/// Changed by the DR-131 extension to F1R3Lang (user decision 1): public
/// source preparation has no work or storage-unit ceiling. `reserve` sees
/// each existing reservation point and may refuse only on cancellation.
pub(super) type PreparationReservation<'a> =
    dyn FnMut(usize, usize) -> Result<(), mettail_rholang_codegen::DynamicReflectionError> + 'a;

/// Check the closed source profile, then enter the checked owned driver, for
/// public source preparation. `parsed_source` binds the receipt to the exact
/// source text; the test-only tree path passes `None`.
pub(super) fn lower_public_checked(
    proc: &Proc,
    parsed_source: Option<&prepared_frontend::ParsedSource<'_>>,
    mut context: BoundEnv,
    reserve: &mut PreparationReservation<'_>,
) -> Result<DirectLoweringOutput, RholangAstLowerError> {
    with_owned_outputs(|_owner| {
        context.admission = SourceAdmissionMode::Public;
        proc.try_check_source_profile(
            mettail_languages::rholang::source_profile::SourceRole::Term,
            &mettail_languages::rholang::source_profile::RholangSourceProfile,
            &mut |work, bytes| reserve(work, bytes),
        )
        .map_err(RholangAstLowerError::SourceProfile)?;
        drive_machine_preparing(
            Seed::Body(proc),
            &context,
            &mut |work, bytes| reserve(work, bytes).map_err(RholangAstLowerError::Preparation),
            SourcePreparation::Checked,
            parsed_source,
        )
    })
}

pub(super) fn checked_fold_site_index(index: usize) -> Result<u8, RholangAstLowerError> {
    u8::try_from(index).map_err(|_| RholangAstLowerError::FoldSiteIndexOverflow { index })
}

#[cfg(test)]
#[path = "session_tests.rs"]
mod tests;
