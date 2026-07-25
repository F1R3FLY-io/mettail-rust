//! **Compile-time guard discharge** — deciding a `where`-guard once, at lowering, when the
//! answer cannot depend on anything the run time will supply.
//!
//! # The whole mechanism in one sentence
//!
//! The runtime half already ships: f1r3node's matcher short-circuits on a missing guard —
//! `rholang/src/rust/interpreter/matcher/match.rs`'s `check_commit` opens with
//! `let Some(guard) = k.guard.as_ref() else { return true; };` — and `reduce.rs`'s
//! `eval_receive` collapses a `Some(Par::default())` condition to `None` before the
//! continuation is registered. **Discharging a guard is therefore simply DECLINING TO POPULATE
//! `Receive.condition`.** Zero new runtime code, zero f1r3node change, and it holds identically
//! on play (`rspace.rs`) and on replay (`replay_rspace.rs`, which reaches `check_commit`
//! through `extract_first_match`).
//!
//! # The sound class: D0, the binder-closed guard
//!
//! A guard is **binder-closed** when its lowered `Par` mentions no variable
//! ([`is_binder_closed`]). `rho-pure-eval` reads its `Env` at exactly one place — `resolve_var`,
//! reached only from the `ExprInstance::EVarBody` arm — so a binder-closed condition evaluates
//! identically under every environment. The compile-time call is then *the same function on the
//! same input* as the runtime call: same evaluator (`rho_pure_eval::eval_with`), same oracle
//! (the reducer's own [`SpatialMatcherOracle`]), same `Par`. There is no model and no
//! abstraction gap to argue about.
//!
//! Mechanized in `formal/rocq/rho_bridge/theories/GuardDischargeSoundness.v`:
//! `T-GD-5 env_independence_of_closed_conditions` is the workhorse induction;
//! `T-GD-1 discharged_guard_would_have_held` is the hypothesis that keeps
//! `RhoGuardedCommSoundness.v`'s `comm_fires_implies_true_guard` true after the elision.
//!
//! ## What is deliberately NOT discharged
//!
//! * **D0′ — operational tautologies** (`x == x`, `p or not p`). Excluded. The guard-fail
//!   collapse in `guard_passes` (false, non-boolean and evaluation-error all become "do not
//!   commit") makes classical validity worthless here: `Par` binders are untyped, so `x == x`
//!   is not a theorem of the *operational* guard language.
//! * **D1 — payload subsumption** (a guard implied by the bind pattern). NOT BUILT — a
//!   decision, not a deferral. The measured yield with sound side conditions is 0 sites.
//! * **Refutation** (`Discharge`'s mirror: a guard that is statically FALSE) is **diagnostic
//!   only** — see [`GuardDischarge::Refuted`]. The artifact is byte-identical.
//!
//! # The anti-divergence fence
//!
//! [`classify`] requires **both** guard evaluators in the tree to agree before it will act:
//!
//! ```text
//!   Discharged ⟸ host_verdict == Some(true)  ∧ machine_verdict(⟦φ⟧) == Some(true)
//!   Refuted    ⟸ host_verdict == Some(false) ∧ machine_verdict(⟦φ⟧) == Some(false)
//!   otherwise  ⟹ Residual                    (and a DISAGREEMENT emits a hard diagnostic)
//! ```
//!
//! The MACHINE leg is the authority — it is what actually runs. The HOST leg
//! (`mettail_languages::rhocalc::receive::eval_guard_bool`, the Dovetail/oracle receive path)
//! is a free redundancy check: it costs nothing at a site where the guard was already lowered,
//! and it converts any divergence-A-shaped hazard (two evaluators of the same surface language
//! disagreeing) into a loud warning instead of an unsound elision. A disagreement is
//! [`GuardDischarge::Residual`] *and* a `WARN`-level event — never a silent Residual.
//!
//! # ★ THE ROUTE-SITE INVARIANT
//!
//! *One routing decision per guard, computed once at lowering, consulted by every decider; no
//! site derives its own routing.* This is the invariant whose violation produced the divergence
//! this module's fence exists to catch, and it will be mechanized as
//! `T-R5 route_is_site_invariant` once the Dovetail/SFT wiring plan lands its `GuardPlan`.
//!
//! [`classify`] complies **structurally**, not by convention:
//!
//! * its verdict is a pure function of the condition — it embeds no judgement about *where* any
//!   construct is evaluated;
//! * it takes the route as an INPUT ([`GuardRouting`]) rather than deriving one. Today the
//!   lowering passes [`GuardRouting::MachineEvaluated`], which is not a derivation but a
//!   structural fact about the artifact being emitted: a populated `Receive.condition` is
//!   evaluated by `check_commit`, by construction. When `GuardPlan` exists, the caller passes
//!   the plan's recorded route and `classify` still decides nothing about routing.
//!
//! # The substrate-routing boundary, checked not assumed
//!
//! The wiring plan also constrains discharge to fold a substrate-routed (`S`) node **only if
//! its operands are ground at lowering time**. For a binder-closed D0 guard that is entailed —
//! there are no operands left to route — but [`classify`] conjoins
//! [`all_operands_ground`] as an *independent* requirement so the boundary is checked rather
//! than inherited from D0's definition. See `guard_closure`'s
//! `binder_closed_implies_operands_ground_on_operand_shaped_conditions`.
//!
//! # Consensus consequence (recorded, accepted)
//!
//! Discharging skips one `substitute_and_charge` per receive-eval, so a program's PHLO price
//! now depends on the compiler version that produced its artifact. This is sound for consensus
//! because the artifact is fixed: every validator replays the same bytes and therefore charges
//! the same amount. It is recorded here because it is a real, observable delta, not because it
//! is a hazard.

use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{Par, TaggedContinuation};
use rho_pure_eval::Env as PureEnv;
use rholang::rust::interpreter::matcher::r#match::SpatialMatcherOracle;

pub use mettail_rholang_codegen::guard_closure::{all_operands_ground, is_binder_closed};
pub use mettail_rholang_codegen::guard_quality::RhoGuardSiteTier;

/// The verdict for one guard site.
///
/// Exactly one of these three outcomes is recorded per lowered `where`-clause. Only
/// [`Discharged`](GuardDischarge::Discharged) changes the emitted artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GuardDischarge {
    /// The guard is binder-closed and BOTH evaluators decide it `true`. The lowering omits
    /// `Receive.condition` entirely; `check_commit` then returns `true` without work, which is
    /// exactly what the guard would have returned. **This is the only outcome that changes the
    /// emitted `Par`.**
    Discharged,
    /// The guard is binder-closed and BOTH evaluators decide it `false`. **Diagnostic only —
    /// the artifact is byte-identical and the exit code is 0.**
    ///
    /// A `for` that can never fire is not dead code: it is a *resting, observable*
    /// continuation. It appears in the normal form, in the state hash, and in storage, and the
    /// corpus asserts exactly that (`assert_host_guard_on` checks the normal form still
    /// contains the `where` clause AND the unconsumed send; the `assert_never_reaches` family
    /// checks the datum stays put). Deleting such a receive, or folding it away, would be an
    /// UNSOUND transformation, so this variant only ever raises
    /// `W1 GuardStaticallyFalse`.
    Refuted,
    /// Everything else: the guard mentions a binder, is not a settled operand, does not
    /// evaluate to a boolean, or the two evaluators disagreed. The condition is emitted
    /// verbatim and the machine decides it at COMM time, exactly as before.
    Residual,
}

impl GuardDischarge {
    /// `true` iff this outcome licenses OMITTING `Receive.condition`.
    ///
    /// The single place the artifact-affecting question is asked, so the (deliberate)
    /// asymmetry with [`GuardDischarge::Refuted`] cannot be reintroduced by accident at a
    /// call site.
    pub fn omits_condition(self) -> bool {
        matches!(self, GuardDischarge::Discharged)
    }

    /// A short stable tag for diagnostics and golden files.
    pub fn tag(self) -> &'static str {
        match self {
            GuardDischarge::Discharged => "Discharged",
            GuardDischarge::Refuted => "Refuted",
            GuardDischarge::Residual => "Residual",
        }
    }

    /// This outcome as the PER-SITE decision tier the route table records (S-Q).
    ///
    /// ★ ROUTE-SITE INVARIANT: the tier is *produced* here, as a by-product of the decision
    /// this module already made, so a later consumer READS the site's route instead of
    /// re-deriving one. `Discharged` and `Refuted` are both
    /// [`RhoGuardSiteTier::StaticConstant`] — the verdict is fixed in the artifact either way;
    /// they differ only in how that verdict is RECORDED (an omitted condition vs a `W1`
    /// diagnostic). `Residual` is [`RhoGuardSiteTier::MachineEvaluated`]: the condition rides
    /// in the artifact and `check_commit` reads it.
    ///
    /// Note the tier this never produces: [`RhoGuardSiteTier::SubstrateDecided`]. A guard
    /// routed to another substrate is refused at the top of [`classify`] and never reaches an
    /// outcome, precisely because deciding it here would be this module deciding a routing
    /// question it has no standing to decide.
    pub fn site_tier(self) -> RhoGuardSiteTier {
        match self {
            GuardDischarge::Discharged | GuardDischarge::Refuted => {
                RhoGuardSiteTier::StaticConstant
            },
            GuardDischarge::Residual => RhoGuardSiteTier::MachineEvaluated,
        }
    }
}

/// The already-decided evaluation route for a guard — an INPUT to [`classify`], never a
/// derivation inside it. See the ROUTE-SITE INVARIANT in the module docs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GuardRouting {
    /// The guard rides as a `Receive.condition` / `MatchCase.guard`, so the Rho machine's own
    /// guard evaluator decides it (`check_commit` → `guard_passes` → `rho_pure_eval::eval_with`).
    ///
    /// This is a structural fact about the artifact being emitted, not a routing derivation:
    /// a populated condition *is* what `check_commit` reads. Discharge is licensed here
    /// because the compile-time evaluator is literally the same function.
    MachineEvaluated,
    /// The guard is decided by some other substrate (a Dovetail native fold, an SFT/EBA
    /// decision procedure, a native handler). Discharge is REFUSED: the compile-time evaluator
    /// is not that substrate, so folding here would be `classify` deciding a routing question
    /// it has no standing to decide.
    OtherSubstrate,
}

impl GuardRouting {
    /// `true` iff a guard on this route may be decided by *this* module's evaluator.
    fn permits_compile_time_decision(self) -> bool {
        matches!(self, GuardRouting::MachineEvaluated)
    }
}

/// Whether the lowering may omit a statically-decided guard.
///
/// A **compilation input**, deliberately not an environment variable: the emitted artifact must
/// be a function of the declared inputs alone, so that two builds of the same source with the
/// same options are byte-identical and a validator can reproduce them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoweringOptions {
    /// `true` (the production default) enables D0 discharge. Guard test harnesses set this
    /// `false` so the ~100 existing guard tests keep exercising the runtime guard evaluator
    /// they exist to test; a parallel discharge-ON differential suite covers the other arm.
    pub guard_discharge: bool,
}

impl LoweringOptions {
    /// The production lowering options: discharge ON.
    pub const PRODUCTION: Self = Self { guard_discharge: true };
    /// Discharge OFF — every guard is emitted verbatim. Byte-identical to the pre-discharge
    /// compiler on the whole corpus (pinned by the S-D0 byte-identity gate).
    pub const NO_DISCHARGE: Self = Self { guard_discharge: false };
}

impl Default for LoweringOptions {
    fn default() -> Self {
        Self::PRODUCTION
    }
}

/// The tracing target every guard-discharge diagnostic is emitted on.
pub const GUARD_DISCHARGE_TARGET: &str = "mettail.lowering.guard";

/// Decide a lowered guard.
///
/// * `host_verdict` — the FRONT-END evaluator's answer for the same guard, or `None` if it
///   declined. For RhoCalc this is `mettail_languages::rhocalc::receive::eval_guard_bool(φ)`,
///   applied at the call site so that this module carries no front-end dependency (and so any
///   other front end can supply its own leg). It is a redundancy check, never the authority.
/// * `cond_par` — the lowered condition, exactly the `Par` that would be stored in
///   `Receive.condition`.
/// * `routing` — the guard's already-decided route (see [`GuardRouting`] and the ROUTE-SITE
///   INVARIANT). `classify` consults it; it never derives it.
///
/// Pure and total: no I/O beyond `tracing` diagnostics, no panics, no environment reads.
pub fn classify(
    host_verdict: Option<bool>,
    cond_par: &Par,
    routing: GuardRouting,
) -> GuardDischarge {
    // Routing is CONSULTED, never derived. A guard the machine does not evaluate is not this
    // module's to decide.
    if !routing.permits_compile_time_decision() {
        return GuardDischarge::Residual;
    }

    // D0. No variable mentioned anywhere ⇒ `eval_with` never reads its `Env`.
    if !is_binder_closed(cond_par) {
        return GuardDischarge::Residual;
    }

    // The substrate-routing boundary, as an INDEPENDENT conjunct (checked, not inherited).
    if !all_operands_ground(cond_par) {
        return GuardDischarge::Residual;
    }

    // The authority: the machine's own evaluator, on the machine's own oracle, under the empty
    // environment (sound precisely because the condition is binder-closed).
    let machine = machine_verdict(cond_par);

    match (machine, host_verdict) {
        (Some(true), Some(true)) => {
            debug_assert!(
                all_operands_ground(cond_par),
                "discharge requires ground operands (wiring-plan substrate boundary)"
            );
            GuardDischarge::Discharged
        },
        (Some(false), Some(false)) => GuardDischarge::Refuted,

        // ★ DISAGREEMENT. Two evaluators of the same surface guard language reached different
        // conclusions on a condition with no free variables — a divergence-A-shaped finding.
        // The safe action is Residual (the machine decides at COMM time, as it does today), but
        // it must NEVER be silent: this is precisely the class of defect the fence exists for.
        (Some(m), Some(h)) => {
            tracing::warn!(
                target: GUARD_DISCHARGE_TARGET,
                machine_verdict = m,
                host_verdict = h,
                condition = ?cond_par,
                "GUARD EVALUATOR DISAGREEMENT on a binder-closed condition: the machine \
                 (rho_pure_eval + SpatialMatcherOracle) and the host front-end evaluator \
                 reached different verdicts. Falling back to Residual (the machine decides at \
                 COMM time). This is a divergence-A-shaped defect; the two evaluators must be \
                 reconciled."
            );
            GuardDischarge::Residual
        },

        // One leg declined. Not a disagreement — one evaluator simply does not cover this
        // fragment (e.g. the host declines `FormulaShape::Separation`, or the machine answers
        // `UnsupportedExpression`). Residual, at DEBUG.
        (machine, host) => {
            tracing::debug!(
                target: GUARD_DISCHARGE_TARGET,
                machine_verdict = ?machine,
                host_verdict = ?host,
                "binder-closed guard not decided by both evaluators; left residual"
            );
            GuardDischarge::Residual
        },
    }
}

/// The MACHINE's verdict for a guard, computed with the machine's own evaluator, the machine's
/// own spatial-match oracle, and the empty environment.
///
/// `Some(b)` iff the condition reduces to the ground boolean `b`; `None` if it does not reduce
/// to a boolean at all (an evaluation error, a non-boolean value, or a residual process). The
/// three-valued answer is the only place this differs from f1r3node's `guard_passes`, which
/// collapses all three "not true" cases into one `false` verdict — a collapse that is correct
/// for deciding a COMM but would conflate [`GuardDischarge::Refuted`] with
/// [`GuardDischarge::Residual`] here.
///
/// Calling it with the empty `Env` is sound **only** for a binder-closed condition; [`classify`]
/// establishes that precondition before calling.
///
/// Agreement with the real runtime entry point (`Matcher::check_commit`) is pinned across the
/// whole corpus by `guard_discharge_corpus.rs`'s
/// `machine_verdict_agrees_with_the_runtime_check_commit`.
pub fn machine_verdict(cond_par: &Par) -> Option<bool> {
    let env: PureEnv<Par> = PureEnv::new();
    let result = rho_pure_eval::eval_with(cond_par, &env, &SpatialMatcherOracle).ok()?;
    extract_bool(&result)
}

/// `Some(b)` iff `par` represents the ground boolean `b` — exactly one `Expr` (a `GBool`) and
/// nothing else of substance.
///
/// Mirrors, field for field, the private `extract_bool` in f1r3node's
/// `rholang/src/rust/interpreter/matcher/match.rs` (and its twin in `reduce.rs`). It is
/// reproduced rather than imported because both are private; the reproduction is not trusted on
/// faith — `machine_verdict_agrees_with_the_runtime_check_commit` drives the real
/// `Matcher::check_commit` over the whole guard corpus and requires
/// `machine_verdict(φ) == Some(true) ⟺ check_commit(φ) == true`, which is the property
/// discharge actually rests on.
fn extract_bool(par: &Par) -> Option<bool> {
    if !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.unforgeables.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
        || par.exprs.len() != 1
    {
        return None;
    }
    match par.exprs[0].expr_instance.as_ref()? {
        ExprInstance::GBool(b) => Some(*b),
        _ => None,
    }
}

/// Wrap a guard as the `TaggedContinuation` the RSpace matcher would see, so a caller can drive
/// the REAL runtime guard path (`Matcher::check_commit`) against the same condition this module
/// decided statically.
///
/// Exposed for the agreement tests; the lowering never builds one.
pub fn guard_as_tagged_continuation(cond_par: &Par) -> TaggedContinuation {
    TaggedContinuation { guard: Some(cond_par.clone()), tagged_cont: None }
}

/// The `W1 GuardStaticallyFalse` refutation diagnostic (S-D0R).
///
/// Emitted at DEBUG on [`GUARD_DISCHARGE_TARGET`] and recorded on the lowering report. **The
/// artifact is byte-identical and the exit code is 0** — see [`GuardDischarge::Refuted`] for
/// why a never-firing `for` is a resting observable rather than dead code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardStaticallyFalse {
    /// A stable identifier for the guard site within the compilation unit: the 0-based index of
    /// the guard in lowering order.
    pub site: usize,
    /// The guard as it was written, when the front end can supply it; otherwise a rendering of
    /// the lowered condition.
    pub guard: String,
}

impl GuardStaticallyFalse {
    /// Emit the `W1` diagnostic for this site. Non-fatal by construction: there is no error
    /// path and no exit-code effect.
    pub fn emit(&self) {
        tracing::debug!(
            target: GUARD_DISCHARGE_TARGET,
            code = "W1",
            site = self.site,
            guard = %self.guard,
            "W1 GuardStaticallyFalse: this `where` guard is statically FALSE, so the receive can \
             never fire. The artifact is UNCHANGED: a never-firing `for` is a resting, \
             observable continuation (it appears in the normal form, the state hash and \
             storage), so removing or folding it would be an unsound transformation."
        );
    }
}

/// What a lowering did with the guards it saw — the observability half of S-D0/S-D0R.
///
/// Carried alongside the emitted `Par` rather than inside it: the artifact must not depend on
/// the report.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GuardDischargeReport {
    /// Guard sites whose `Receive.condition` was omitted.
    pub discharged: usize,
    /// Guard sites decided statically FALSE. Diagnostic only.
    pub refuted: Vec<GuardStaticallyFalse>,
    /// Guard sites emitted verbatim for the machine to decide.
    pub residual: usize,
    /// Guard sites where the two evaluators DISAGREED. Always `0` in a healthy tree; any
    /// non-zero value is a divergence-A-shaped defect that has already been logged at WARN.
    pub disagreements: usize,
}

impl GuardDischargeReport {
    /// Total guard sites seen.
    pub fn total(&self) -> usize {
        self.discharged + self.refuted.len() + self.residual
    }

    /// Record one site's outcome. `guard` is the source rendering used by the `W1` diagnostic.
    pub fn record(&mut self, outcome: GuardDischarge, guard: impl FnOnce() -> String) {
        match outcome {
            GuardDischarge::Discharged => self.discharged += 1,
            GuardDischarge::Refuted => {
                let event = GuardStaticallyFalse { site: self.total(), guard: guard() };
                event.emit();
                self.refuted.push(event);
            },
            GuardDischarge::Residual => self.residual += 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::create_bit_vector;
    use models::rhoapi::{EAnd, EEq, EGt, ENot, EOr, Expr};
    use models::rust::utils::{new_boundvar_par, new_gbool_par, new_gint_par, new_gstring_par};
    use rspace_plus_plus::rspace::r#match::Match;

    fn expr_par(instance: ExprInstance) -> Par {
        Par { exprs: vec![Expr { expr_instance: Some(instance) }], ..Par::default() }
    }

    fn gbool(b: bool) -> Par {
        new_gbool_par(b, Vec::new(), false)
    }

    fn gint(i: i64) -> Par {
        new_gint_par(i, Vec::new(), false)
    }

    fn machine(cond: &Par) -> GuardDischarge {
        // The host leg agrees with the machine by construction in these unit tests; the
        // corpus test drives the REAL host evaluator.
        classify(machine_verdict(cond), cond, GuardRouting::MachineEvaluated)
    }

    #[test]
    fn a_true_constant_guard_discharges() {
        assert_eq!(machine(&gbool(true)), GuardDischarge::Discharged);
    }

    #[test]
    fn a_false_constant_guard_is_refuted_not_discharged() {
        let outcome = machine(&gbool(false));
        assert_eq!(outcome, GuardDischarge::Refuted);
        assert!(!outcome.omits_condition(), "refutation must NOT change the artifact");
    }

    #[test]
    fn a_closed_comparison_is_decided() {
        // 3 > 2
        let gt = expr_par(ExprInstance::EGtBody(EGt { p1: Some(gint(3)), p2: Some(gint(2)) }));
        assert_eq!(machine(&gt), GuardDischarge::Discharged);
        // 2 > 3
        let lt = expr_par(ExprInstance::EGtBody(EGt { p1: Some(gint(2)), p2: Some(gint(3)) }));
        assert_eq!(machine(&lt), GuardDischarge::Refuted);
    }

    #[test]
    fn the_implies_shape_or_not_a_b_is_decided_closed() {
        // `a implies b` lowers to EOr(ENot a, b). All four ground rows.
        for (a, b, expected) in [
            (false, false, GuardDischarge::Discharged),
            (false, true, GuardDischarge::Discharged),
            (true, false, GuardDischarge::Refuted),
            (true, true, GuardDischarge::Discharged),
        ] {
            let implies = expr_par(ExprInstance::EOrBody(EOr {
                p1: Some(expr_par(ExprInstance::ENotBody(ENot { p: Some(gbool(a)) }))),
                p2: Some(gbool(b)),
            }));
            assert_eq!(machine(&implies), expected, "{a} implies {b}");
        }
    }

    #[test]
    fn a_guard_mentioning_a_binder_is_residual() {
        // x > 0, with x a bound var — the overwhelmingly common shape.
        let guard = expr_par(ExprInstance::EGtBody(EGt {
            p1: Some(new_boundvar_par(0, create_bit_vector(&[0]), false)),
            p2: Some(gint(0)),
        }));
        assert_eq!(machine(&guard), GuardDischarge::Residual);
    }

    /// The `EEq(BoundVar_i, BoundVar_j)` shape the three codegen guard sites build.
    #[test]
    fn a_nonlinear_consistency_conjunction_is_residual() {
        let eq0 = expr_par(ExprInstance::EEqBody(EEq {
            p1: Some(new_boundvar_par(2, create_bit_vector(&[2]), false)),
            p2: Some(new_boundvar_par(0, create_bit_vector(&[0]), false)),
        }));
        let eq1 = expr_par(ExprInstance::EEqBody(EEq {
            p1: Some(new_boundvar_par(3, create_bit_vector(&[3]), false)),
            p2: Some(new_boundvar_par(1, create_bit_vector(&[1]), false)),
        }));
        let conj =
            expr_par(ExprInstance::EAndBody(EAnd { p1: Some(eq0), p2: Some(eq1) }));
        assert_eq!(machine(&conj), GuardDischarge::Residual);
    }

    #[test]
    fn a_non_boolean_closed_guard_is_residual_not_refuted() {
        // `1` is closed and decides to a value, but not to a bool: the machine cannot say
        // "false", it can only decline. Refuting it would claim knowledge we do not have.
        assert_eq!(machine(&gint(1)), GuardDischarge::Residual);
        assert_eq!(machine_verdict(&gint(1)), None);
    }

    #[test]
    fn a_guard_the_evaluator_rejects_is_residual() {
        // `"a" > 1` — a heterogeneous comparison `cmp_binop` refuses.
        let bad = expr_par(ExprInstance::EGtBody(EGt {
            p1: Some(new_gstring_par("a".to_string(), Vec::new(), false)),
            p2: Some(gint(1)),
        }));
        assert_eq!(machine_verdict(&bad), None);
        assert_eq!(machine(&bad), GuardDischarge::Residual);
    }

    /// ★ ROUTE-SITE INVARIANT. A guard routed to another substrate is never decided here, even
    /// when it is a closed constant this module could trivially fold.
    #[test]
    fn a_guard_routed_elsewhere_is_never_discharged_here() {
        assert_eq!(
            classify(Some(true), &gbool(true), GuardRouting::OtherSubstrate),
            GuardDischarge::Residual
        );
        assert_eq!(
            classify(Some(true), &gbool(true), GuardRouting::MachineEvaluated),
            GuardDischarge::Discharged
        );
    }

    /// ★ THE FENCE. A fabricated disagreement must fall to Residual, never to Discharged.
    #[test]
    fn evaluator_disagreement_falls_to_residual() {
        // machine says true; a (hypothetical) host leg says false.
        assert_eq!(
            classify(Some(false), &gbool(true), GuardRouting::MachineEvaluated),
            GuardDischarge::Residual
        );
        // machine says false; host says true.
        assert_eq!(
            classify(Some(true), &gbool(false), GuardRouting::MachineEvaluated),
            GuardDischarge::Residual
        );
    }

    /// A host leg that DECLINED (`None`) can never license discharge, however confident the
    /// machine is. This is what keeps the eager-site `None`-handling defect in
    /// `languages/src/rhocalc/receive.rs` (an unevaluable guard treated as false) from ever
    /// reaching the artifact through this path.
    #[test]
    fn a_declining_host_leg_never_licenses_discharge() {
        assert_eq!(
            classify(None, &gbool(true), GuardRouting::MachineEvaluated),
            GuardDischarge::Residual
        );
        assert_eq!(
            classify(None, &gbool(false), GuardRouting::MachineEvaluated),
            GuardDischarge::Residual
        );
    }

    /// ★ THE CORE INSIGHT, exercised against the REAL runtime entry point: for a binder-closed
    /// guard, `machine_verdict(φ) == Some(true)` iff f1r3node's own `Matcher::check_commit`
    /// admits the COMM. Discharge is sound exactly because these two coincide.
    #[test]
    fn machine_verdict_matches_check_commit_on_closed_guards() {
        let matcher = rholang::rust::interpreter::matcher::r#match::Matcher;
        let cases = [
            gbool(true),
            gbool(false),
            gint(1),
            expr_par(ExprInstance::EGtBody(EGt { p1: Some(gint(3)), p2: Some(gint(2)) })),
            expr_par(ExprInstance::EGtBody(EGt { p1: Some(gint(2)), p2: Some(gint(3)) })),
            expr_par(ExprInstance::EAndBody(EAnd { p1: Some(gbool(true)), p2: Some(gbool(true)) })),
            expr_par(ExprInstance::EAndBody(EAnd {
                p1: Some(gbool(true)),
                p2: Some(gbool(false)),
            })),
        ];
        for cond in cases {
            let tc = guard_as_tagged_continuation(&cond);
            let commits = matcher.check_commit(&tc, &[]);
            assert_eq!(
                machine_verdict(&cond) == Some(true),
                commits,
                "compile-time verdict must agree with the runtime `check_commit` for {cond:?}"
            );
        }
    }

    /// An OMITTED guard is what `check_commit` short-circuits on — the runtime half that makes
    /// discharge a no-op rather than a semantic change.
    #[test]
    fn an_absent_guard_commits_unconditionally() {
        let matcher = rholang::rust::interpreter::matcher::r#match::Matcher;
        let absent = TaggedContinuation { guard: None, tagged_cont: None };
        assert!(matcher.check_commit(&absent, &[]));
        // …and so does the empty-`Par` form `reduce.rs` collapses to `None`.
        let empty = TaggedContinuation { guard: Some(Par::default()), tagged_cont: None };
        assert!(matcher.check_commit(&empty, &[]));
    }

    #[test]
    fn the_report_counts_and_only_refutation_carries_events() {
        let mut report = GuardDischargeReport::default();
        report.record(GuardDischarge::Discharged, || "true".to_string());
        report.record(GuardDischarge::Refuted, || "false".to_string());
        report.record(GuardDischarge::Residual, || "x > 0".to_string());
        assert_eq!(report.discharged, 1);
        assert_eq!(report.residual, 1);
        assert_eq!(report.refuted.len(), 1);
        assert_eq!(report.refuted[0].guard, "false");
        assert_eq!(report.total(), 3);
    }

    /// S-Q: every outcome maps to a per-SITE tier, and `SubstrateDecided` is unreachable from
    /// here by construction (a substrate-routed guard is refused before it can get an outcome).
    #[test]
    fn every_outcome_carries_its_per_site_tier() {
        assert_eq!(GuardDischarge::Discharged.site_tier(), RhoGuardSiteTier::StaticConstant);
        assert_eq!(GuardDischarge::Refuted.site_tier(), RhoGuardSiteTier::StaticConstant);
        assert_eq!(GuardDischarge::Residual.site_tier(), RhoGuardSiteTier::MachineEvaluated);
        // A guard on another substrate never reaches an outcome, so this path can never
        // report `SubstrateDecided` — it reports the safe `Residual`/`MachineEvaluated` pair.
        assert_eq!(
            classify(Some(true), &gbool(true), GuardRouting::OtherSubstrate).site_tier(),
            RhoGuardSiteTier::MachineEvaluated
        );
    }

    #[test]
    fn production_options_discharge_and_the_harness_switch_does_not() {
        assert!(LoweringOptions::PRODUCTION.guard_discharge);
        assert!(!LoweringOptions::NO_DISCHARGE.guard_discharge);
        assert_eq!(LoweringOptions::default(), LoweringOptions::PRODUCTION);
    }
}
