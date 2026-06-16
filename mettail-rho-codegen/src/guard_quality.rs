//! Guard-quality classification — the predicate substrate's *quality tag* for a
//! guard disposition.
//!
//! The Dovetail/Rho backend (`backend.rs`) classifies each guard obligation with
//! a *mechanism* ([`RhoGuardDispositionKind`]) — how it is covered. This module
//! adds the orthogonal *quality* axis: the documented 7-value vocabulary from
//! `docs/architecture/dovetail/04-rules-and-saturation.md` describing *how
//! strong* the evidence is. The predicate-substrate generalization (EBA / SFT /
//! tree-automata / behavioral-algebra family) produces this tag; Dovetail's
//! fail-closed gate refuses production-default lowering on [`RhoGuardQuality::Unknown`].
//!
//! This is the *left half* of the boundary (classify, don't lower). It aligns to
//! the existing [`RhoGuardDisposition`] type rather than inventing a parallel
//! disposition: a [`RhoGuardDispositionQuality`] simply pairs the existing
//! disposition with its quality tag. Proof attribution stays external (commit
//! `6d20b82d`): [`RhoGuardQuality::MachineCheckedModel`] is a quality *class*,
//! never a `RocqLemmaRef` carried in `LanguageDef` identity or runtime data.
//!
//! Wiring status: **live**. [`crate::backend::plan_rho_default_backend`] derives
//! these qualities for a language's covered guard obligations
//! ([`derive_guard_qualities`]), carries them on the
//! [`RhoDefaultBackendPlan`](crate::backend::RhoDefaultBackendPlan) as
//! observability, and folds a fail-closed
//! [`RhoFlipBlocker::GuardQuality`](crate::flip::RhoFlipBlocker::GuardQuality)
//! into the flip gate for any obligation whose quality
//! [`refuses_production_default`](RhoGuardQuality::refuses_production_default)
//! (i.e. `Unknown`) — enforcing doc-08's "`Unknown` quality ⇒ production-default
//! refused". The Rocq gate model
//! `formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v` proves the necessity
//! of the `Unknown` blocker and composes with the M7 mixed-guard soundness
//! theorem (`RhoGuardedCommSoundness.v`).

use mettail_ast::language::LanguageDef;

use crate::backend::{
    collect_guard_obligations, guard_disposition_covers, RhoGuardDispositionKind,
    RhoGuardObligationKind,
};

/// The documented 7-value guard-quality vocabulary (docs §04). Ordered weakest
/// last so `Unknown` sorts highest (most-restrictive for the fail-closed gate).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RhoGuardQuality {
    /// Complete static / runtime-decidable evidence (structural matcher, EBA/SFT
    /// proof, exact model-checker result). Maps to tiers T1/T2 (regular core).
    ExactDecidable,
    /// Sound and complete only under a recorded bound (tier T3 boundary).
    BoundedDecidable,
    /// May conservatively reject; usable only where false negatives cannot
    /// fabricate successful rewrites (the Heyting reject-safe behavioral leg).
    RejectSafeApprox,
    /// A native assertion site owns the contract (tier T4 / native handler).
    TrustedNativeGuard,
    /// A machine-checked formal model discharges the obligation; the proof is
    /// attributed in docs/comments, never carried as runtime data.
    MachineCheckedModel,
    /// The Rho runtime supplies the behavioral evidence via a named observation
    /// or join contract.
    RuntimeObservation,
    /// No disposition could be derived — production-default lowering is refused.
    Unknown,
}

/// The decidability tier of a guard's decision procedure — the predicate-substrate
/// classification (prattail `DecidabilityTier` / macros `GuardTier` / Coq
/// `GuardTierCertificate.Tier`). T1/T2 are exact, T3 is bounded, T4 is asserted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RhoGuardTier {
    /// Static-constant decision (compile-time).
    T1Exact,
    /// Decidable at runtime (exact).
    T2Decidable,
    /// Sound+complete only under a bound.
    T3Bounded,
    /// Trusted assertion site (no static guarantee).
    T4Asserted,
}

/// The substrate's findings for one guard obligation: the covering mechanism, the
/// decidability tier, and the orthogonal evidence flags that can override the
/// tier-driven quality. This is what this plan's algebra family computes per
/// obligation; [`classify_quality`] folds it to a [`RhoGuardQuality`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RhoGuardClassification {
    /// The covering mechanism (existing backend vocabulary).
    pub disposition_kind: RhoGuardDispositionKind,
    /// The decidability tier of the decision procedure.
    pub tier: RhoGuardTier,
    /// A semi-decidable behavioral (reject-safe) leg is present — the complement
    /// may conservatively reject (no excluded middle).
    pub reject_safe: bool,
    /// Discharged by a zero-admission machine-checked model (proof attribution
    /// external, per `6d20b82d`).
    pub machine_checked: bool,
    /// Backed by a Rho runtime observation / join contract.
    pub runtime_observed: bool,
}

impl RhoGuardClassification {
    /// A plain decidable classification at a given tier (no override flags).
    pub fn decidable(kind: RhoGuardDispositionKind, tier: RhoGuardTier) -> Self {
        Self {
            disposition_kind: kind,
            tier,
            reject_safe: false,
            machine_checked: false,
            runtime_observed: false,
        }
    }
}

/// Fold a substrate classification to its quality tag. Override precedence
/// (runtime ▷ machine-checked ▷ reject-safe) reflects the strongest *named*
/// evidence; otherwise the mechanism + tier drive the tag.
pub fn classify_quality(c: RhoGuardClassification) -> RhoGuardQuality {
    use RhoGuardDispositionKind::*;
    use RhoGuardQuality as Q;
    use RhoGuardTier::*;

    if c.runtime_observed {
        return Q::RuntimeObservation;
    }
    if c.machine_checked {
        return Q::MachineCheckedModel;
    }
    if c.reject_safe {
        return Q::RejectSafeApprox;
    }
    match c.disposition_kind {
        NativeHandler | ExternalContract => Q::TrustedNativeGuard,
        RhoNativeJoin => Q::RuntimeObservation,
        DovetailCoreStructural | EffectiveBooleanAlgebra | SymbolicFiniteTransducer => {
            match c.tier {
                T1Exact | T2Decidable => Q::ExactDecidable,
                T3Bounded => Q::BoundedDecidable,
                T4Asserted => Q::TrustedNativeGuard,
            }
        },
    }
}

impl RhoGuardQuality {
    /// Whether Dovetail must refuse production-default lowering for this quality.
    /// Only `Unknown` is fail-closed; every other tag carries usable (if bounded
    /// or reject-safe) evidence.
    pub fn refuses_production_default(self) -> bool {
        matches!(self, RhoGuardQuality::Unknown)
    }

    /// Whether the evidence is exact (complete classical decidability). False for
    /// bounded, reject-safe, trusted, runtime, machine-checked-only, and unknown.
    pub fn is_exact(self) -> bool {
        matches!(self, RhoGuardQuality::ExactDecidable)
    }
}

/// An existing [`RhoGuardDisposition`](crate::backend::RhoGuardDisposition)
/// paired with its substrate quality tag — the substrate's per-obligation
/// output. Held alongside (not merged into) `RhoGuardDisposition` so the
/// coverage gate keeps checking the disposition MECHANISM while the planner
/// folds the orthogonal QUALITY axis into the flip gate
/// ([`crate::backend::guard_quality_blockers_for`]) and carries it on the plan
/// as diagnostic observability.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoGuardDispositionQuality {
    /// The obligation id this classifies (mirrors `RhoGuardDisposition::obligation`).
    pub obligation: String,
    /// The covering mechanism.
    pub kind: RhoGuardDispositionKind,
    /// The substrate quality tag.
    pub quality: RhoGuardQuality,
}

impl RhoGuardDispositionQuality {
    /// Build a disposition+quality from a substrate classification for one
    /// obligation id.
    pub fn from_classification(
        obligation: impl Into<String>,
        c: RhoGuardClassification,
    ) -> Self {
        Self { obligation: obligation.into(), kind: c.disposition_kind, quality: classify_quality(c) }
    }
}

/// The substrate's *default* classification for an obligation kind: which
/// mechanism covers it, at what tier, and whether it is reject-safe. This is the
/// conservative, sound default the algebra family assigns before any deeper
/// analysis upgrades it (e.g. promoting an exact relational behavioral predicate
/// off the reject-safe leg). Every result is gate-compatible with its obligation
/// kind by construction (asserted in [`derive_guard_qualities`]).
pub fn default_classification(kind: RhoGuardObligationKind) -> RhoGuardClassification {
    use RhoGuardDispositionKind as D;
    use RhoGuardObligationKind as O;
    use RhoGuardTier::*;
    match kind {
        // Structural shape predicates are decided exactly by Dovetail's core.
        O::StructuralPattern => RhoGuardClassification::decidable(D::DovetailCoreStructural, T1Exact),
        // A registered theory supplies an exact effective Boolean algebra.
        O::TheoryRegistration => RhoGuardClassification::decidable(D::EffectiveBooleanAlgebra, T2Decidable),
        // Behavioral predicates are semi-decidable ⇒ the reject-safe leg by
        // default (conservative: may reject, never wrongly admits a Comm).
        O::BehavioralPredicate => RhoGuardClassification {
            disposition_kind: D::EffectiveBooleanAlgebra,
            tier: T2Decidable,
            reject_safe: true,
            machine_checked: false,
            runtime_observed: false,
        },
        // Rho-native joins are discharged by a runtime join/observation contract.
        O::RhoNativeJoin => RhoGuardClassification {
            disposition_kind: D::RhoNativeJoin,
            tier: T2Decidable,
            reject_safe: false,
            machine_checked: false,
            runtime_observed: true,
        },
    }
}

/// Derive quality-tagged dispositions for every guard obligation a `LanguageDef`
/// induces — the predicate substrate's per-language output that the Dovetail/Rho
/// evidence gate consumes. Each emitted disposition mechanism is gate-compatible
/// with its obligation kind ([`guard_disposition_covers`]); the quality tag lets
/// Dovetail refuse production-default lowering on `Unknown` and record the
/// evidence strength in the run report.
pub fn derive_guard_qualities(def: &LanguageDef) -> Vec<RhoGuardDispositionQuality> {
    collect_guard_obligations(def)
        .into_iter()
        .map(|obligation| {
            let classification = default_classification(obligation.kind);
            debug_assert!(
                guard_disposition_covers(obligation.kind, classification.disposition_kind),
                "substrate emitted a gate-incompatible disposition {:?} for obligation kind {:?}",
                classification.disposition_kind,
                obligation.kind,
            );
            RhoGuardDispositionQuality::from_classification(obligation.id, classification)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use RhoGuardDispositionKind::*;
    use RhoGuardQuality as Q;
    use RhoGuardTier::*;

    #[test]
    fn tier_drives_decidable_quality() {
        // structural / EBA / SFT decidable legs: tier → quality.
        for kind in [DovetailCoreStructural, EffectiveBooleanAlgebra, SymbolicFiniteTransducer] {
            assert_eq!(classify_quality(RhoGuardClassification::decidable(kind, T1Exact)), Q::ExactDecidable);
            assert_eq!(classify_quality(RhoGuardClassification::decidable(kind, T2Decidable)), Q::ExactDecidable);
            assert_eq!(classify_quality(RhoGuardClassification::decidable(kind, T3Bounded)), Q::BoundedDecidable);
            assert_eq!(classify_quality(RhoGuardClassification::decidable(kind, T4Asserted)), Q::TrustedNativeGuard);
        }
    }

    #[test]
    fn native_and_join_kinds() {
        assert_eq!(classify_quality(RhoGuardClassification::decidable(NativeHandler, T1Exact)), Q::TrustedNativeGuard);
        assert_eq!(classify_quality(RhoGuardClassification::decidable(ExternalContract, T2Decidable)), Q::TrustedNativeGuard);
        assert_eq!(classify_quality(RhoGuardClassification::decidable(RhoNativeJoin, T1Exact)), Q::RuntimeObservation);
    }

    #[test]
    fn override_flags_take_precedence() {
        let base = RhoGuardClassification::decidable(EffectiveBooleanAlgebra, T1Exact);
        // reject-safe behavioral leg ⇒ RejectSafeApprox even though tier is exact.
        assert_eq!(classify_quality(RhoGuardClassification { reject_safe: true, ..base }), Q::RejectSafeApprox);
        // machine-checked beats reject-safe and tier.
        assert_eq!(
            classify_quality(RhoGuardClassification { reject_safe: true, machine_checked: true, ..base }),
            Q::MachineCheckedModel
        );
        // runtime observation beats everything.
        assert_eq!(
            classify_quality(RhoGuardClassification {
                reject_safe: true,
                machine_checked: true,
                runtime_observed: true,
                ..base
            }),
            Q::RuntimeObservation
        );
    }

    #[test]
    fn every_disposition_kind_classifiable() {
        // Snapshot: every existing RhoGuardDispositionKind yields a usable
        // (non-Unknown) quality from a plain decidable classification.
        for kind in [
            DovetailCoreStructural,
            EffectiveBooleanAlgebra,
            SymbolicFiniteTransducer,
            RhoNativeJoin,
            NativeHandler,
            ExternalContract,
        ] {
            let q = classify_quality(RhoGuardClassification::decidable(kind, T2Decidable));
            assert_ne!(q, Q::Unknown, "kind {kind:?} should classify to a usable quality");
            assert!(!q.refuses_production_default());
        }
    }

    #[test]
    fn unknown_is_fail_closed_and_observable() {
        assert!(Q::Unknown.refuses_production_default());
        assert!(!Q::ExactDecidable.refuses_production_default());
        assert!(!Q::RejectSafeApprox.refuses_production_default());
        assert!(Q::ExactDecidable.is_exact());
        assert!(!Q::BoundedDecidable.is_exact());
        assert!(!Q::RejectSafeApprox.is_exact());
    }

    #[test]
    fn disposition_quality_pairing() {
        let dq = RhoGuardDispositionQuality::from_classification(
            "rule:Comm:guard:0",
            RhoGuardClassification {
                disposition_kind: EffectiveBooleanAlgebra,
                tier: T3Bounded,
                reject_safe: false,
                machine_checked: false,
                runtime_observed: false,
            },
        );
        assert_eq!(dq.obligation, "rule:Comm:guard:0");
        assert_eq!(dq.kind, EffectiveBooleanAlgebra);
        assert_eq!(dq.quality, Q::BoundedDecidable);
    }

    // ── Live wiring: default classification + coverage-matrix consistency ────
    // (consumed by `backend::plan_rho_default_backend` via the flip gate).

    use crate::backend::{guard_disposition_covers, RhoGuardObligationKind};

    /// COVERAGE-MATRIX TEST: the disposition the substrate emits for every
    /// obligation kind is gate-compatible (`guard_disposition_covers`) — the
    /// substrate never emits evidence the fail-closed gate would reject as
    /// incompatible.
    #[test]
    fn default_classifications_are_gate_compatible() {
        for okind in [
            RhoGuardObligationKind::BehavioralPredicate,
            RhoGuardObligationKind::StructuralPattern,
            RhoGuardObligationKind::TheoryRegistration,
            RhoGuardObligationKind::RhoNativeJoin,
        ] {
            let c = default_classification(okind);
            assert!(
                guard_disposition_covers(okind, c.disposition_kind),
                "obligation {okind:?} → disposition {:?} is NOT gate-compatible",
                c.disposition_kind
            );
        }
    }

    /// The default quality per obligation kind: structural/theory exact,
    /// behavioral reject-safe (sound — never wrongly admits a Comm), native join
    /// runtime-observed. None is Unknown.
    #[test]
    fn default_quality_per_obligation_kind() {
        let q = |o| classify_quality(default_classification(o));
        assert_eq!(q(RhoGuardObligationKind::StructuralPattern), Q::ExactDecidable);
        assert_eq!(q(RhoGuardObligationKind::TheoryRegistration), Q::ExactDecidable);
        assert_eq!(q(RhoGuardObligationKind::BehavioralPredicate), Q::RejectSafeApprox);
        assert_eq!(q(RhoGuardObligationKind::RhoNativeJoin), Q::RuntimeObservation);
        for o in [
            RhoGuardObligationKind::BehavioralPredicate,
            RhoGuardObligationKind::StructuralPattern,
            RhoGuardObligationKind::TheoryRegistration,
            RhoGuardObligationKind::RhoNativeJoin,
        ] {
            assert_ne!(q(o), Q::Unknown);
        }
    }
}
