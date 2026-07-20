//! The generated in-Rho self-re-spreading QUIESCENCE DRIVER (A-S5.2, plan v2 §4 — leg v)
//! — the persistent `^drive` receiver family that normalizes a seeded reflected subject to
//! quiescence FULLY ON the live f1r3node reducer: matching, firing (through the EXISTING
//! σ ABI), contractum re-entry, congruence descent with join reassembly, and the
//! quiescence observation are all COMMs; the host seeds once and reads channels.
//!
//! # Architecture (plan v2 §4; v1 §4.2 F1/F2)
//!
//! No host trampoline ⟹ the per-iteration re-match machinery is **persistent and
//! site-generic**: one reserved receiver `^drive(t, fuel, ret)` carrying the driven value
//! as DATA on a fixed `GPrivate` channel (the R3-walker technique). Contexts are implicit
//! in continuations: descent spawns concurrent child drives with fresh returns, and an
//! atomic JOIN reassembles the parent node only after EVERY child delivered its normal
//! form — the subst-TRS join-reassembly recursion ([`crate::rho_net_subst_trs::join`])
//! generalized from "substitute" to "reduce". Quiescence is structural: the root call
//! returns exactly when its subtree is normal, so the single OUT datum is the resting
//! term.
//!
//! # The `^drive` receiver, per driven node (`match t`, arm order is load-bearing)
//!
//! ```text
//! for(@t, @fuel, @ret <= ⌜^drive⌝) {
//!   match t {
//!     ⟦LHSᵢ⟧-pattern =>                                     -- 1. redex arms (declaration order)
//!         match fuel {
//!           0 => @"^drive-fuel:{fp}"!(⟦redex-node⟧)          --    exhaustion: typed, 0-case FIRST (AM-7)
//!           _ => new r in { acceptᵢ!(σ…, r)                  --    fire through the EXISTING σ ABI
//!                         | @"^fired:{fp}"!("RuleLabelᵢ")    --    the firing ledger
//!                         | for(@c <- r){ ⌜^drive⌝!(c, fuel - 1, ret) } }   -- contractum re-drive
//!         }
//!     [⌜C⌝, c₀, …, c_{m-1}] =>                              -- 2. congruence-descent arms (one per object ctor)
//!         new r₀…r_{m-1} in {
//!           ⌜^drive⌝!(c₀, fuel, r₀) | … |                    --    concurrent child drives (NO decrement)
//!           for(@s₀ <- r₀ & …){                              --    atomic join
//!             match [⌜C⌝, s₀, …] {                           --    inline post-join re-check
//!               ⟦LHSᵢ⟧-pattern => <the same fuel-gated firing>  --    (redex arms ONLY)
//!               _ => ret!([⌜C⌝, s₀, …])                      --    default: publish the reassembled NF
//!             } } }
//!     [⌜C⌝] => ret!([⌜C⌝])                                   --    (m = 0: a nullary leaf)
//!     [⌜^lambda⌝, b] =>                                      -- 3. binder arm: drive the body, rewrap
//!         new r in { ⌜^drive⌝!(b, fuel, r) | for(@rb <- r){ ret!([⌜^lambda⌝, rb]) } }
//!     [⌜^free⌝, x]  => ret!([⌜^free⌝, x])                    -- 4. reserved passthroughs
//!     [⌜^bound⌝, n] => ret!([⌜^bound⌝, n])
//!     _ => @"^drive-err:{fp}"!(t)                            -- 5. typed fail-close wildcard
//!   }
//! }
//! ```
//!
//! * **Strategy**: redex arms precede descent ⟹ per-node outermost-first
//!   (normal-order-flavored); a fired contractum is fully re-driven.
//! * **Post-join re-check**: catches redexes *enabled by* child normalization (e.g.
//!   `App(x, a)` whose function position normalized to a `^lambda`) without re-descending
//!   normal children. Termination: every `^drive` call either strictly descends or
//!   consumes one fuel-bounded firing; the inline re-check fires or returns — no descent
//!   loop.
//! * **Binder-arm re-check emission rule (plan v2 §4.3.2 / F14)**: the post-REWRAP
//!   re-check is emitted iff some compiled redex arm's root is the binder's reflected tag
//!   (compile-time known). No bundled driver language has a binder-rooted entry (Lambda's
//!   only entry root is `App`), so the arm stays byte-lean; the emission rule keeps the
//!   totality argument honest for a future binder-rooted language.
//! * **Fuel (plan v2 §4.2 / F10, decision (2))**: a `GInt`, default
//!   [`DRIVE_DEFAULT_FUEL`], threaded from the seed. Firing arms ONLY consult it — the
//!   ground `GInt(0)` case FIRST, then the wildcard firing case (AM-7: `wrapping_sub`
//!   makes a mis-ordered wildcard-first list an infinite negative cascade; probe P2 in
//!   `rholang-runtime/tests/drive_fuel_probe.rs` pins the reducer facts). Fuel is
//!   **per-path**: each descent copies the current value into child frames, so the bound
//!   is on firings along any causal chain from the seed, and global firings are
//!   O(branching^depth × fuel) worst case — the host exhaustion report names BOTH the
//!   per-path bound and the ledger's global fired count.
//! * **Channel discipline (plan v2 §4.5 / F7)**: `^drive` itself and every in-Rho
//!   rendezvous (fresh returns, σ-ABI accepts) are `GPrivate` unforgeables; ONLY the three
//!   observation channels — [`drive_fired_channel`], [`drive_err_channel`],
//!   [`drive_fuel_channel`] — are GString names, because host readback rides the proven
//!   GString `get_data` path and the `^`-prefix + fingerprint suffix keep them
//!   collision-free with user constructors (Rust `Ident`s never contain `^` or `:`).
//!
//! # Carrier seam (plan v2 §5 — Branch PS ACTIVE, PM parked)
//!
//! The candidate-carrier surface is the [`DriveCarrier`] trait (v1 §5.3):
//! [`PsValueCarrier`] — the driven value itself threading through `^drive`, redex checks
//! as `Match` arms, "re-spread" = contractum re-entry — is the ONLY implementation
//! compiled (the 2026-07-19 E-6a measurement kept the PathMap carrier parked; its unblock
//! routes are documented in plan v2 §5.3). The acceptance surface binding ANY future
//! carrier: same fired-label multiset per subject, same resting term, no
//! `NestedEntryMultiSite` for driver languages, same typed fail-close channels, same cap
//! behavior.
//!
//! # Scion seam (plan v2 §4.6 — the E-1 drop-in)
//!
//! The firing arm's contractum re-entry is factored through [`FiringEmission`] /
//! [`firing_emission_node`]: `ContractumRedrive` (today's re-drive `for`) is implemented;
//! `ScionBundle` is the E-1 forward-compatibility variant — PRESENT, CONSTRUCTED NOWHERE
//! (deliberately: it is the seam, not dead code). Seam invariant a bundle must preserve:
//! the value ultimately reaching `ret` is `norm(contractum)` under the SAME `^drive`
//! semantics.
//!
//! # Admission (plan v2 §4.4 / F9, amendment AM-4)
//!
//! `drive_admissible(def, ruleset)` = static-gate-Ok ∧ every admitted matching family is
//! driver-supported (THIS stage: positional/subst σ-ABI entries only — AC / nested-AC /
//! contextual / native / comm families land with A-S5.5) ∧ the language is opted in via
//! the codegen-visible [`DRIVE_OPT_IN`] const (consulted by the macro emitter, so a
//! non-opted-in language's generated module is byte-identical — the AM-4 pin). The
//! disposition is RECORDED on [`crate::rho_net_lower::RhoNetLowered`] as
//! [`DriveAdmission`], never silent. Ambient is opted in but `Unsupported` until A-S5.5
//! (its AC families have no driver arms yet) — exactly the recorded state the sub-stage
//! sequence expects.
//!
//! FV: `formal/rocq/rho_bridge/theories/InRhoQuiescenceDriver.v` (A-S5.2) — the driver as
//! a big-step LTS over the reflected object fragment: `drive_steps_sound`,
//! `quiescence_sound` (per-trace, join re-check case included),
//! `fuel_exhaustion_never_wrong`, and the iterated β weak bisimulation
//! (`drive_weak_bisim`) discharged through `DeBruijnSubstTRS.v`'s SN + confluence.

use std::collections::HashMap;

use mettail_ast::grammar::TermParam;
use mettail_ast::language::{LanguageDef, RewriteRule};
use mettail_ast::pattern::{Pattern, PatternTerm};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EMinus, Expr, Par};
use models::rust::utils::{new_gint_par, new_gstring_par};

use crate::rho_net::RhoNetProgram;
use crate::rho_net_lower::{
    lower_lhs_vars, RhoNetLoweredRule, RhoNetLoweringError, DRIVE_ERR_RESERVED_LABEL,
    DRIVE_FUEL_RESERVED_LABEL, DRIVE_RESERVED_LABEL, FIRED_RESERVED_LABEL,
    BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
};
use crate::rho_net_ruleset::{compile_in_rho_matching_ruleset, in_rho_static_gate, InRhoMatchingRuleset};
use crate::rho_net_subst_trs::{
    for1, free_bits, ground, is_binder_term, join, match_, new_scope, object_congruence_constructors,
    par2, pat_free, pat_tagged, pat_wildcard, persistent_contract, send, tag_par, tagged, union_free,
    Case, Env, Node,
};

// ─────────────────────────────────────────────────────────────────────────────────────────────
// Admission (plan v2 §4.4 / F9, AM-4).
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The codegen-visible driver OPT-IN list (amendment AM-4): the A-S5 scope, by language
/// name. Consulted BOTH by [`drive_admissible`] (the recorded lowering disposition) and by
/// the macro emitter (`macros/src/gen/runtime/rho_invocation.rs`), so a non-opted-in
/// language never receives a generated `rho_net_drive_invocation_to` — the SwapDemo
/// byte-identity pin depends on exactly this.
///
/// Ambient is opted in but stays [`DriveAdmission::Unsupported`] until A-S5.5 lands its AC
/// driver arms — opt-in expresses INTENT; admission is the conjunction in
/// [`drive_admissible`].
pub const DRIVE_OPT_IN: &[&str] = &["Lambda", "Ambient"];

/// The per-path fuel value the generated drive seed threads (plan v2 §4.2, user decision
/// (2): fixed 64, Dovetail-saturation parity). Changeable without ABI impact — the seed
/// carries the value; the receivers only decrement and compare to ground `0`.
pub const DRIVE_DEFAULT_FUEL: i64 = 64;

/// The RECORDED in-Rho quiescence-driver admission disposition of one lowered language
/// (plan v2 §4.4 / F9) — carried by
/// [`RhoNetLowered::drive_admission`](crate::rho_net_lower::RhoNetLowered::drive_admission),
/// recorded-never-silent (the `congruence_exempt_rules` discipline).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DriveAdmission {
    /// Every conjunct of [`drive_admissible`] holds — the `^drive` receiver family is
    /// built and installed.
    Admitted,
    /// The language is not in [`DRIVE_OPT_IN`] — the zero-cost default for every
    /// non-A-S5 language; its lowering artifact and installed program are byte-identical
    /// to pre-A-S5.2.
    NotRequested,
    /// Opted in, but a conjunct fails; `reason` names EVERY failed conjunct (static-gate
    /// rejects, driver-unsupported matching families, lowering diagnostics, or a seed
    /// that does not transcribe).
    Unsupported {
        /// Every failed admission conjunct, `; `-joined.
        reason: String,
    },
}

/// The A-S5.2 driver-admission predicate (plan v2 §4.4): **opted in** (AM-4, by name in
/// [`DRIVE_OPT_IN`]) ∧ **static gate Ok** ([`in_rho_static_gate`] — every fireable rewrite
/// matchable in Rho, congruence-only rewrites exempt) ∧ **every admitted matching family
/// driver-supported** (this stage: positional/subst σ-ABI entries only — a non-empty
/// native / AC / contextual / structural-AC / nested-structural-AC dispatch family or a
/// multi-binder term is not yet drivable; Ambient therefore records `Unsupported` until
/// A-S5.5) ∧ **every fireable seed transcribes** to a driver redex arm (linear,
/// constructor-rooted LHS whose σ variables avoid the driver frame names).
///
/// A PURE function of `(def, ruleset)` — both live in the memoized
/// [`crate::rho_net_cache::CompiledInRhoArtifacts`], so the generated
/// `rho_net_drive_invocation_to` body re-checks admission per exec at cache-hit cost (the
/// fail-closed guard for the A-S5.4b→A-S5.5 window where Ambient's static gate passes but
/// its driver arms do not yet exist: without this check the seed would rest unanswered).
pub fn drive_admissible(def: &LanguageDef, ruleset: &InRhoMatchingRuleset) -> DriveAdmission {
    let name = def.name.to_string();
    if !DRIVE_OPT_IN.contains(&name.as_str()) {
        return DriveAdmission::NotRequested;
    }

    let mut reasons: Vec<String> = Vec::new();

    // Conjunct 1: the A-S2 static capability gate.
    if let Err(deferred) = in_rho_static_gate(ruleset, def) {
        let labels: Vec<String> = deferred
            .iter()
            .map(|entry| format!("{} ({:?})", entry.rule_label, entry.reason))
            .collect();
        reasons.push(format!(
            "static gate rejects: fireable rule(s) not matchable in Rho: {}",
            labels.join(", ")
        ));
    }

    // Conjunct 2: every admitted matching family must be driver-supported. This stage
    // supports the positional/subst σ-ABI entries only (plan v2 §8 row A-S5.2); the AC
    // family arms land with A-S5.5.
    let mut unsupported_families: Vec<String> = Vec::new();
    if !ruleset.native_dispatch.is_empty() {
        unsupported_families.push(format!("native({})", ruleset.native_dispatch.len()));
    }
    if !ruleset.ac_dispatch.is_empty() {
        unsupported_families.push(format!("ac({})", ruleset.ac_dispatch.len()));
    }
    if !ruleset.contextual_dispatch.is_empty() {
        unsupported_families.push(format!("contextual({})", ruleset.contextual_dispatch.len()));
    }
    if !ruleset.structural_ac_dispatch.is_empty() {
        unsupported_families.push(format!(
            "structural-ac({})",
            ruleset.structural_ac_dispatch.len()
        ));
    }
    if !ruleset.nested_structural_ac_dispatch.is_empty() {
        unsupported_families.push(format!(
            "nested-structural-ac({})",
            ruleset.nested_structural_ac_dispatch.len()
        ));
    }
    if !unsupported_families.is_empty() {
        reasons.push(format!(
            "matching families not yet driver-supported (A-S5.5): {}",
            unsupported_families.join(", ")
        ));
    }
    if def
        .terms
        .iter()
        .any(|term| is_binder_term(term) && is_multi_binder_term(term))
    {
        reasons.push(
            "multi-binder (^multilambda) terms have no driver binder arm this stage".to_string(),
        );
    }

    // Conjunct 3: every fireable (non-congruence-only) rewrite's LHS must transcribe to a
    // driver redex arm — the same first-occurrence σ order the σ-receiver binds.
    for rewrite in &def.rewrites {
        if crate::rho_net_lower::congruence_only_premises(&rewrite.premises) {
            continue;
        }
        if let Err(error) = validate_seed_transcription(rewrite, def, &ruleset.language_fingerprint)
        {
            reasons.push(format!(
                "rewrite {} does not transcribe to a driver redex arm: {error}",
                rewrite.name
            ));
        }
    }

    if reasons.is_empty() {
        DriveAdmission::Admitted
    } else {
        DriveAdmission::Unsupported { reason: reasons.join("; ") }
    }
}

/// Whether a binder term is a MULTI-binder (`MultiAbstraction` — reflected `^multilambda`).
/// The driver's binder arm covers single binders (`^lambda`) only this stage.
fn is_multi_binder_term(term: &mettail_ast::grammar::GrammarRule) -> bool {
    term.term_context.as_ref().is_some_and(|params| {
        params
            .iter()
            .any(|param| matches!(param, TermParam::MultiAbstraction { .. }))
    })
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// Observation-channel names (plan v2 §4.5 / F7) + the seed / invocation surface.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The GString firing-ledger channel name `"^fired:{fp}"` — one GString rule label rests
/// here per driver firing.
pub fn drive_fired_channel(language_fingerprint: &str) -> String {
    format!("{FIRED_RESERVED_LABEL}:{language_fingerprint}")
}

/// The GString typed fail-close channel name `"^drive-err:{fp}"` — an unrecognized driven
/// head rests here (never silently normal).
pub fn drive_err_channel(language_fingerprint: &str) -> String {
    format!("{DRIVE_ERR_RESERVED_LABEL}:{language_fingerprint}")
}

/// The GString fuel-exhaustion channel name `"^drive-fuel:{fp}"` — the stuck redex node
/// rests here when a firing arm sees fuel `0`.
pub fn drive_fuel_channel(language_fingerprint: &str) -> String {
    format!("{DRIVE_FUEL_RESERVED_LABEL}:{language_fingerprint}")
}

/// A codegen-owned drive-seed invocation, ready for the runtime to run against a
/// language's INSTALLED program (which carries the `^drive` receiver family for admitted
/// languages): the seed `call` plus the four observation-channel names the readback API
/// (`DriveObservationChannels`) consumes. The drive analogue of
/// [`crate::rho_net_lower::RhoNetInjectionInvocation`].
#[derive(Debug, Clone, PartialEq)]
pub struct RhoNetDriveInvocation {
    /// The closed seed `Par`: `⌜^drive⌝!(⟦term⟧, fuel, @out_channel)`.
    pub call: Par,
    /// The quoted channel the quiescent resting term lands on.
    pub out_channel: String,
    /// [`drive_fired_channel`] of the language fingerprint.
    pub fired_channel: String,
    /// [`drive_err_channel`] of the language fingerprint.
    pub err_channel: String,
    /// [`drive_fuel_channel`] of the language fingerprint.
    pub fuel_channel: String,
}

/// The drive SEED send `⌜^drive⌝!(⟦subject⟧, fuel, @out_channel)` with an EXPLICIT
/// per-path fuel — the test surface for fuel-exhaustion subjects (Ω with a small bound).
/// Production seeding uses [`rho_net_drive_call_par`] (fuel = [`DRIVE_DEFAULT_FUEL`]).
pub fn rho_net_drive_call_par_with_fuel(
    language_fingerprint: &str,
    subject: Par,
    fuel: i64,
    out_channel: &str,
) -> Par {
    send(
        ground(tag_par(language_fingerprint, DRIVE_RESERVED_LABEL)),
        vec![
            ground(subject),
            ground(new_gint_par(fuel, Vec::new(), false)),
            ground(new_gstring_par(out_channel.to_string(), Vec::new(), false)),
        ],
    )
    .par
}

/// The drive SEED send with the production per-path fuel ([`DRIVE_DEFAULT_FUEL`]).
pub fn rho_net_drive_call_par(language_fingerprint: &str, subject: Par, out_channel: &str) -> Par {
    rho_net_drive_call_par_with_fuel(language_fingerprint, subject, DRIVE_DEFAULT_FUEL, out_channel)
}

/// Assemble the full [`RhoNetDriveInvocation`] for a reflected subject: the default-fuel
/// seed plus the fingerprint-derived observation-channel names. The generated
/// `rho_net_drive_invocation_to` body calls this after its admission checks.
pub fn rho_net_drive_invocation(
    language_fingerprint: &str,
    subject: Par,
    out_channel: &str,
) -> RhoNetDriveInvocation {
    RhoNetDriveInvocation {
        call: rho_net_drive_call_par(language_fingerprint, subject, out_channel),
        out_channel: out_channel.to_string(),
        fired_channel: drive_fired_channel(language_fingerprint),
        err_channel: drive_err_channel(language_fingerprint),
        fuel_channel: drive_fuel_channel(language_fingerprint),
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// The carrier seam (plan v2 §5 / v1 §5.3) — Branch PS active; PM parked.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The reserved-channel payload layout of one drive frame (arity + roles).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DriveFrame {
    /// The receive formals, outermost-first (the [`Env::root`] order).
    pub formals: Vec<&'static str>,
}

/// One compiled redex arm: the rule's identity, its σ-ABI accept surface, and its
/// transcribed `Match` pattern. Built once per admitted fireable rewrite by
/// [`drive_lowering`]; consumed by the carrier's [`DriveCarrier::redex_check`] and by the
/// firing emission (accept send + ledger label + fuel-datum rebuild).
#[derive(Debug, Clone)]
pub struct DriveRedexArm {
    /// The bare source rewrite label (the ledger datum).
    pub rule_label: String,
    /// The installed σ-receiver's SOURCE channel (`RhoNetRule::input_channels[0]`) — the
    /// arm fires `accept!(σ…, r)` on exactly this GString name, so the EXISTING receiver
    /// (β SEED or base σ-receiver) computes/delivers the contractum to the fresh `r`.
    pub accept_channel: String,
    /// The σ capture order = the LHS first-occurrence variable order
    /// ([`lower_lhs_vars`]) = the σ-receiver's formal order — the coherence that makes
    /// the accept send line up with the installed receiver's frame.
    pub sigma_vars: Vec<String>,
    /// The source LHS pattern (retained for the fuel-exhaustion datum rebuild).
    pub(crate) lhs: Pattern,
    /// The transcribed tagged-`EList` `Match` pattern (σ variables as `FreeVar`s in
    /// first-occurrence order; binder constructors remapped to their reflected tags).
    pub(crate) pattern: Par,
    /// Whether the transcribed pattern's ROOT is a binder tag — drives the binder-arm
    /// post-rewrap re-check emission rule (plan v2 §4.3.2; `false` for every bundled
    /// driver language).
    pub(crate) root_is_binder: bool,
}

/// The redex-check a carrier realizes for one arm: for PS a `Match` pattern (+ optional
/// per-case guard — the machine's `MatchCase.guard`, F12-confirmed; `None` for every
/// linear arm, populated by the A-S5.5 non-linear Ambient arms); for a future PM carrier,
/// a guard-expression + σ-extraction plan over the index.
#[derive(Debug, Clone)]
pub struct DriveCheck {
    /// The `Match` case pattern.
    pub pattern: Par,
    /// The pattern's `FreeVar` count (= σ slot count for a redex arm).
    pub free_count: usize,
    /// An optional per-case guard `Par` (`MatchCase.guard`).
    pub guard: Option<Par>,
}

/// The candidate-carrier seam (plan v2 §5.2 / v1 §5.3) — Branch PS (value) active; Branch
/// PM (index) parked with documented unblock routes (plan v2 §5.3).
///
/// The driver generator ([`drive_program_par`]) is written against this trait, so a
/// future carrier is a swap of the implementation under the FIXED acceptance surface
/// (fired-set multiset equality, same resting term, no `NestedEntryMultiSite`, same typed
/// fail-close channels, same cap behavior).
///
/// Deviation from the v1 §5.3 sketch, documented: the sketch wrote `pub trait`; the
/// method types ([`Node`]/[`Env`]) are the crate-internal De Bruijn combinators
/// (`rho_net_subst_trs.rs` — deliberately `pub(crate)`, the naive-kt sharing precedent),
/// so the trait is crate-visible. Same swap surface; no public leak of frame internals.
pub(crate) trait DriveCarrier {
    /// The reserved-channel payload layout of one drive frame.
    fn frame_formals(&self) -> DriveFrame;
    /// The redex-check for one compiled arm.
    fn redex_check(&self, arm: &DriveRedexArm, env: &Env) -> DriveCheck;
    /// The descent payload for child `i` of an m-ary node (the frame binds the captured
    /// children as `c0…c_{m-1}`, innermost-last).
    fn child_payload(&self, env: &Env, child_index: usize) -> Node;
    /// Reassembly of the parent payload from child results (the join body).
    fn reassemble(&self, env: &Env, label: &str, children: &[Node]) -> Node;
    /// The contractum's re-entry payload (`ContractumRedrive` builds it; a `ScionBundle`
    /// bypasses it — the [`FiringEmission`] seam sits above this).
    fn contractum_payload(&self, env: &Env, contractum: Node) -> Node;
}

/// Branch PS — the ACTIVE value carrier (plan v2 §5.1): the driven value `t` itself
/// threads through `^drive`; redex checks are `Match` arms over `t`; "re-spread" =
/// contractum re-entry. Per-candidate private datum ≙ private spread nonce
/// (contention-free by construction — each datum is consumed by exactly one checker, so
/// `NestedEntryMultiSite` cannot arise).
pub(crate) struct PsValueCarrier {
    /// The language fingerprint every reflected tag / reassembly shares.
    pub(crate) fingerprint: String,
}

impl DriveCarrier for PsValueCarrier {
    fn frame_formals(&self) -> DriveFrame {
        DriveFrame { formals: vec!["t", "fuel", "ret"] }
    }

    fn redex_check(&self, arm: &DriveRedexArm, _env: &Env) -> DriveCheck {
        // PS: the transcribed pattern IS the check (env-independent — pattern `Par`s are
        // ground-relative); linear arms carry no guard this stage.
        DriveCheck {
            pattern: arm.pattern.clone(),
            free_count: arm.sigma_vars.len(),
            guard: None,
        }
    }

    fn child_payload(&self, env: &Env, child_index: usize) -> Node {
        env.var(&format!("c{child_index}"))
    }

    fn reassemble(&self, env: &Env, label: &str, children: &[Node]) -> Node {
        let _ = env;
        tagged(&self.fingerprint, label, children.to_vec())
    }

    fn contractum_payload(&self, env: &Env, contractum: Node) -> Node {
        let _ = env;
        contractum
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// The scion seam (plan v2 §4.6 / v1 §4.4 — the E-1 drop-in).
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// A-S5 firing-emission seam (E-1 forward-compatibility): how a fired redex arm's
/// contractum re-enters the drive.
#[derive(Debug, Clone, PartialEq)]
pub enum FiringEmission {
    /// Today: read the contractum off the firing's fresh return channel and re-drive it
    /// whole — `for(@c <- r){ ⌜^drive⌝!(c, fuel - 1, ret) }`.
    ContractumRedrive,
    /// E-1: a per-(entry, rule) precompiled scion bundle `Par`, emitted INSTEAD of the
    /// redrive `for` — it publishes the contractum's pre-analyzed drive decomposition
    /// (known-RHS structure never re-scanned; only RHS variable positions re-enter
    /// `^drive`). THE SEAM, deliberately constructed nowhere in A-S5.2. Contract a bundle
    /// must satisfy: (a) compiled against the firing frame this emitter builds (`r` =
    /// `BoundVar(0)` inside the `new r` scope, `fuel`/`ret` at the enclosing arm frame);
    /// (b) the value ultimately reaching `ret` is `norm(contractum)` under the SAME
    /// `^drive` semantics — the acceptance surface of §5.2 binds it.
    ScionBundle {
        /// The precompiled emission `Par`.
        bundle: Par,
    },
}

/// Emit ONE fired redex arm's firing body (plan v2 §4.6): the fresh return scope, the
/// σ-ABI accept send, the firing-ledger send, and the contractum re-entry per `emission`.
///
/// ```text
/// new r in { accept!(σ…, r) | @"^fired:{fp}"!("RuleLabel") | <emission> }
/// ```
///
/// `env` is the De Bruijn frame with the arm's σ captures pushed (innermost-last, the
/// `pat_tagged` free-count frame); `fuel_var`/`ret_var` NAME the frame variables and are
/// resolved lazily inside each nested scope — a deliberate deviation from the v1 §4.4
/// sketch's `fuel: Node, ret: Node` (a [`Node`] is frame-relative and cannot be hoisted
/// across the `new r` / `for(@c <- r)` binders; the module's [`Env`] discipline requires
/// name-late resolution). The `carrier` supplies the contractum payload (the seam sits
/// above the carrier).
pub(crate) fn firing_emission_node(
    arm: &DriveRedexArm,
    emission: &FiringEmission,
    fingerprint: &str,
    env: &Env,
    fuel_var: &str,
    ret_var: &str,
    carrier: &dyn DriveCarrier,
) -> Node {
    new_scope(1, {
        let env = env.push(&["r"]);
        // Fire through the EXISTING σ ABI: `accept!(σ₀, …, σ_{k-1}, r)` — the installed
        // σ-receiver (β SEED / base receiver) binds `(σ…, out=r)` and delivers the
        // contractum (for β: the subst-TRS cascade NF) to the fresh `r`.
        let mut accept_data: Vec<Node> = Vec::with_capacity(arm.sigma_vars.len() + 1);
        for sigma in &arm.sigma_vars {
            accept_data.push(env.var(sigma));
        }
        accept_data.push(env.var("r"));
        let accept = send(
            ground(new_gstring_par(arm.accept_channel.clone(), Vec::new(), false)),
            accept_data,
        );
        // The firing ledger: `@"^fired:{fp}"!("RuleLabel")`.
        let ledger = send(
            ground(new_gstring_par(drive_fired_channel(fingerprint), Vec::new(), false)),
            vec![ground(new_gstring_par(arm.rule_label.clone(), Vec::new(), false))],
        );
        let emission_node = match emission {
            FiringEmission::ContractumRedrive => for1(env.var("r"), {
                let env = env.push(&["c"]);
                send(
                    ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
                    vec![
                        carrier.contractum_payload(&env, env.var("c")),
                        eminus(env.var(fuel_var), gint(1)),
                        env.var(ret_var),
                    ],
                )
            }),
            // The E-1 seam: the precompiled bundle replaces the redrive `for` (see the
            // [`FiringEmission::ScionBundle`] contract). Constructed nowhere this stage.
            FiringEmission::ScionBundle { bundle } => ground(bundle.clone()),
        };
        par2(par2(accept, ledger), emission_node)
    })
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// Node helpers: GInt / EMinus (the F10 fuel arithmetic).
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// A ground `GInt` value node.
fn gint(value: i64) -> Node {
    ground(new_gint_par(value, Vec::new(), false))
}

/// `a - b` as an `EMinus` expression node — machine-evaluable in send DATA
/// (`eval_send` evaluates every datum; probe P2 pins the fact), free in
/// `a.free ∪ b.free`.
fn eminus(a: Node, b: Node) -> Node {
    let free = union_free(&[a.free.as_slice(), b.free.as_slice()]);
    let bits = free_bits(&free);
    let par = Par {
        exprs: vec![Expr {
            expr_instance: Some(ExprInstance::EMinusBody(EMinus {
                p1: Some(a.par),
                p2: Some(b.par),
            })),
        }],
        locally_free: bits,
        ..Default::default()
    };
    Node { par, free }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// LHS-pattern transcription (v1 §4.3.1): `DvPattern` → tagged-`EList` `Match` pattern.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The driver frame names a σ variable must not shadow — [`Env::get`] resolves
/// innermost-first, so a σ capture named `fuel` would corrupt the firing arm's fuel
/// resolution. Checked (fail-closed) by the seed transcription.
const DRIVE_FRAME_NAMES: [&str; 6] = ["t", "fuel", "ret", "r", "c", "rb"];

/// Whether a σ variable name collides with the driver's frame discipline (the fixed
/// frame/scope names, or the generated `c{i}`/`r{i}`/`s{i}` descent names).
fn collides_with_drive_frame(name: &str) -> bool {
    if DRIVE_FRAME_NAMES.contains(&name) {
        return true;
    }
    let mut chars = name.chars();
    matches!(chars.next(), Some('c' | 'r' | 's')) && chars.as_str().chars().all(|c| c.is_ascii_digit())
        && name.len() > 1
}

/// Transcribe one fireable rewrite's LHS to its driver redex-arm `Match` pattern
/// (plan v1 §4.3.1): constructor applications become tagged-`EList` patterns
/// ([`pat_tagged`]) with BINDER constructors remapped to their reflected tag
/// ([`LAMBDA_REFLECT_LABEL`] — the same `is_binder_term` predicate the TRS reflection
/// uses, so the remap cannot drift), and σ variables become [`pat_free`] binders in
/// pattern-DFS FIRST-OCCURRENCE order — the σ-receiver's `lower_lhs_vars` order, so the
/// arm's accept send lines up with the installed receiver's frame by construction
/// (asserted below).
///
/// Fail-closed (`Err`, surfaced as [`DriveAdmission::Unsupported`]) on every
/// out-of-this-stage shape: a repeated σ variable (non-linear — needs the A-S5.5
/// `MatchCase.guard` arms), a literal binder pattern, a substitution node, a collection
/// (AC — A-S5.5), a multi-binder constructor, or an unknown constructor.
fn transcribe_lhs_pattern(
    pattern: &Pattern,
    def: &LanguageDef,
    fingerprint: &str,
    order: &mut Vec<String>,
) -> Result<Par, String> {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => {
            let name = name.to_string();
            if order.contains(&name) {
                return Err(format!(
                    "repeated LHS variable {name:?} (a non-linear redex arm needs the A-S5.5 \
                     MatchCase.guard equality)"
                ));
            }
            if collides_with_drive_frame(&name) {
                return Err(format!(
                    "LHS variable {name:?} collides with a driver frame name \
                     ({DRIVE_FRAME_NAMES:?} / c#, r#, s#)"
                ));
            }
            let level = order.len();
            order.push(name);
            Ok(pat_free(level))
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let label = constructor.to_string();
            let term = def
                .terms
                .iter()
                .find(|term| term.label == label)
                .ok_or_else(|| format!("unknown constructor {label:?} in a redex-arm LHS"))?;
            let tag = if is_binder_term(term) {
                if is_multi_binder_term(term) {
                    return Err(format!(
                        "multi-binder constructor {label:?} has no driver arm this stage"
                    ));
                }
                if args.len() != 1 {
                    return Err(format!(
                        "binder constructor {label:?} applied to {} argument(s) in a redex-arm \
                         LHS (the reflected binder node has exactly one child, its body)",
                        args.len()
                    ));
                }
                LAMBDA_REFLECT_LABEL
            } else {
                label.as_str()
            };
            let mut children = Vec::with_capacity(args.len());
            for arg in args {
                children.push(transcribe_lhs_pattern(arg, def, fingerprint, order)?);
            }
            Ok(pat_tagged(fingerprint, tag, children))
        },
        Pattern::Term(PatternTerm::Lambda { .. }) | Pattern::Term(PatternTerm::MultiLambda { .. }) => {
            Err("a literal binder pattern in a redex-arm LHS is not driver-supported this \
                 stage"
                .to_string())
        },
        Pattern::Term(PatternTerm::Subst { .. }) | Pattern::Term(PatternTerm::MultiSubst { .. }) => {
            Err("a substitution node in a redex-arm LHS has no matching image".to_string())
        },
        Pattern::Collection { .. } => {
            Err("a collection (AC) LHS is not driver-supported this stage (A-S5.5)".to_string())
        },
        Pattern::Map { .. } => Err("a map (AC) LHS is not driver-supported this stage".to_string()),
        Pattern::Zip { .. } => Err("a zip (AC) LHS is not driver-supported this stage".to_string()),
    }
}

/// REBUILD the redex node from the arm's own σ pattern (every child bound), used as the
/// fuel-exhaustion datum: at the top-level arm the `^drive` formal `t` names the same
/// value, but inside the post-join re-check the pre-descent `t` would be a STALE datum —
/// rebuilding from the pattern is the uniform, always-current form.
fn rebuild_from_pattern(
    pattern: &Pattern,
    def: &LanguageDef,
    fingerprint: &str,
    env: &Env,
) -> Result<Node, String> {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => Ok(env.var(&name.to_string())),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let label = constructor.to_string();
            let term = def
                .terms
                .iter()
                .find(|term| term.label == label)
                .ok_or_else(|| format!("unknown constructor {label:?} in a redex-arm rebuild"))?;
            let tag = if is_binder_term(term) { LAMBDA_REFLECT_LABEL } else { label.as_str() };
            let mut children = Vec::with_capacity(args.len());
            for arg in args {
                children.push(rebuild_from_pattern(arg, def, fingerprint, env)?);
            }
            Ok(tagged(fingerprint, tag, children))
        },
        _ => Err("redex-arm rebuild reached a shape the transcription admitted incorrectly"
            .to_string()),
    }
}

/// Validate (admission-time) that a fireable rewrite's LHS transcribes AND that its σ
/// order agrees with [`lower_lhs_vars`] — the σ-receiver coherence check.
fn validate_seed_transcription(
    rewrite: &RewriteRule,
    def: &LanguageDef,
    fingerprint: &str,
) -> Result<(), String> {
    let mut order = Vec::new();
    transcribe_lhs_pattern(&rewrite.left, def, fingerprint, &mut order)?;
    let receiver_order = lower_lhs_vars(&rewrite.left)
        .map_err(|family| format!("σ-receiver LHS order unavailable ({family:?})"))?;
    let receiver_order: Vec<String> = receiver_order.iter().map(|v| v.to_string()).collect();
    if order != receiver_order {
        return Err(format!(
            "transcription σ order {order:?} diverges from the σ-receiver order \
             {receiver_order:?}"
        ));
    }
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// The lowering entry point + the `^drive` receiver generator.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The A-S5.2 driver lowering (called by [`crate::rho_net_lower::lower`]): decide (and
/// RECORD) admission, and for admitted languages build the `^drive` receiver family from
/// the SAME lowered rules / program channels the installed σ-receivers were compiled
/// with.
///
/// The opt-in short-circuit is a name comparison ([`DRIVE_OPT_IN`], AM-4), so every
/// non-opted-in language pays nothing and lowers byte-identically to pre-A-S5.2.
thread_local! {
    /// Re-entrancy guard for [`drive_lowering`]'s admission ruleset compile.
    ///
    /// `compile_in_rho_matching_ruleset` derives its site channels through
    /// `rho_net_injection_sites`, which runs the FULL lowering (`lower_to_par`) —
    /// including `drive_lowering` — so an unguarded admission compile for an opted-in
    /// language would recurse without bound (lower → drive_lowering → compile ruleset →
    /// injection sites → lower → …). While the guard is set, nested `drive_lowering`
    /// calls short-circuit to `NotRequested`: a nested lowering exists ONLY as a
    /// sub-computation of the admission check itself (the site/family enumerators read
    /// its channels and rule sites, never its drive fields, and drop it), so the
    /// short-circuit is unobservable outside this module — the OUTER call still computes
    /// the full predicate against the completed ruleset. Panic-safe via [`AdmissionGuard`].
    static DRIVE_ADMISSION_IN_PROGRESS: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// The drop-guard that clears [`DRIVE_ADMISSION_IN_PROGRESS`] even if the ruleset
/// compile panics (fail-closed: a poisoned flag would silently disable every later
/// admission on the thread).
struct AdmissionGuard;

impl AdmissionGuard {
    fn enter() -> Option<AdmissionGuard> {
        DRIVE_ADMISSION_IN_PROGRESS.with(|flag| {
            if flag.get() {
                None
            } else {
                flag.set(true);
                Some(AdmissionGuard)
            }
        })
    }
}

impl Drop for AdmissionGuard {
    fn drop(&mut self) {
        DRIVE_ADMISSION_IN_PROGRESS.with(|flag| flag.set(false));
    }
}

pub(crate) fn drive_lowering(
    def: &LanguageDef,
    program: &RhoNetProgram,
    rules: &[RhoNetLoweredRule],
    errors: &[RhoNetLoweringError],
    rewrite_by_id: &HashMap<String, &RewriteRule>,
) -> (Option<Par>, DriveAdmission) {
    let name = def.name.to_string();
    if !DRIVE_OPT_IN.contains(&name.as_str()) {
        return (None, DriveAdmission::NotRequested);
    }
    if !errors.is_empty() {
        return (
            None,
            DriveAdmission::Unsupported {
                reason: format!(
                    "lowering recorded {} fail-closed diagnostic(s): {errors:?}",
                    errors.len()
                ),
            },
        );
    }
    // The full admission predicate over the SAME pure derivation the memoized artifacts
    // carry (`compile_in_rho_matching_ruleset` is a pure function of `def`, so this
    // agrees with the generated body's per-exec re-check by construction). The guard
    // breaks the lower ↔ ruleset derivation cycle — see `DRIVE_ADMISSION_IN_PROGRESS`.
    let Some(_guard) = AdmissionGuard::enter() else {
        // A nested lowering inside the admission compile of THIS thread's outer call:
        // its artifact is an enumeration sub-computation, never installed.
        return (None, DriveAdmission::NotRequested);
    };
    let ruleset = compile_in_rho_matching_ruleset(def);
    debug_assert_eq!(
        ruleset.language_fingerprint, program.language_fingerprint,
        "the matching ruleset and the RhoNet program derive the same fingerprint from one def"
    );
    match drive_admissible(def, &ruleset) {
        DriveAdmission::Admitted => {},
        other => return (None, other),
    }

    // Extract one redex-arm seed per fired-through-σ-ABI lowered rule (SubstRewrite — the
    // β SEED — and positional BaseRewrite; the admission conjuncts above guarantee no
    // other fireable family is present).
    let fingerprint = program.language_fingerprint.as_str();
    let mut arms: Vec<DriveRedexArm> = Vec::with_capacity(rules.len());
    for rule in rules {
        let rule_id = match rule {
            RhoNetLoweredRule::SubstRewrite { rule_id, .. }
            | RhoNetLoweredRule::BaseRewrite { rule_id, .. } => rule_id,
            _ => continue,
        };
        let Some(rewrite) = rewrite_by_id.get(rule_id) else {
            return (
                None,
                DriveAdmission::Unsupported {
                    reason: format!("lowered rule {rule_id} has no source rewrite (drift)"),
                },
            );
        };
        let Some(program_rule) = program.rules.iter().find(|r| r.id == *rule_id) else {
            return (
                None,
                DriveAdmission::Unsupported {
                    reason: format!("lowered rule {rule_id} has no program rule (drift)"),
                },
            );
        };
        let Some(accept_channel) = program_rule.input_channels.first() else {
            return (
                None,
                DriveAdmission::Unsupported {
                    reason: format!("lowered rule {rule_id} has no accept channel (drift)"),
                },
            );
        };
        let mut order = Vec::new();
        let pattern = match transcribe_lhs_pattern(&rewrite.left, def, fingerprint, &mut order) {
            Ok(pattern) => pattern,
            Err(error) => {
                // Unreachable when `drive_admissible` validated the same rewrites;
                // recorded defensively (never a partial driver).
                return (
                    None,
                    DriveAdmission::Unsupported {
                        reason: format!("rewrite {} does not transcribe: {error}", rewrite.name),
                    },
                );
            },
        };
        let root_is_binder = matches!(
            &rewrite.left,
            Pattern::Term(PatternTerm::Apply { constructor, .. })
                if def
                    .terms
                    .iter()
                    .any(|term| term.label == constructor.to_string() && is_binder_term(term))
        );
        arms.push(DriveRedexArm {
            rule_label: rewrite.name.to_string(),
            accept_channel: accept_channel.clone(),
            sigma_vars: order,
            lhs: rewrite.left.clone(),
            pattern,
            root_is_binder,
        });
    }

    let carrier = PsValueCarrier { fingerprint: fingerprint.to_string() };
    match drive_program_par(def, fingerprint, &arms, &carrier) {
        Ok(par) => (Some(par), DriveAdmission::Admitted),
        Err(reason) => (None, DriveAdmission::Unsupported { reason }),
    }
}

/// The fuel-gated firing body of one redex arm (plan v2 §4.2): the ground `GInt(0)`
/// exhaustion case FIRST (AM-7 — arm order is load-bearing under `wrapping_sub`), then
/// the wildcard firing case through the [`firing_emission_node`] seam. `env` carries the
/// arm's σ captures.
fn fuel_gated_firing(
    arm: &DriveRedexArm,
    def: &LanguageDef,
    fingerprint: &str,
    env: &Env,
    carrier: &dyn DriveCarrier,
) -> Result<Node, String> {
    let exhaustion_datum = rebuild_from_pattern(&arm.lhs, def, fingerprint, env)?;
    Ok(match_(
        env.var("fuel"),
        vec![
            Case {
                pattern: new_gint_par(0, Vec::new(), false),
                free_count: 0,
                body: send(
                    ground(new_gstring_par(drive_fuel_channel(fingerprint), Vec::new(), false)),
                    vec![exhaustion_datum],
                ),
            },
            Case {
                pattern: pat_wildcard(),
                free_count: 0,
                body: firing_emission_node(
                    arm,
                    &FiringEmission::ContractumRedrive,
                    fingerprint,
                    env,
                    "fuel",
                    "ret",
                    carrier,
                ),
            },
        ],
    ))
}

/// The redex `Case`s (pattern + σ frame + fuel-gated firing body) — shared between the
/// top-level `match t` and every post-join / post-rewrap re-check (the re-check re-tests
/// the reassembled node against the redex arms ONLY: its children are already normal
/// forms, so descent would be redundant).
fn redex_cases(
    arms: &[DriveRedexArm],
    def: &LanguageDef,
    fingerprint: &str,
    env: &Env,
    carrier: &dyn DriveCarrier,
) -> Result<Vec<Case>, String> {
    let mut cases = Vec::with_capacity(arms.len());
    for arm in arms {
        let check = carrier.redex_check(arm, env);
        debug_assert!(check.guard.is_none(), "linear arms carry no guard this stage");
        let sigma_refs: Vec<&str> = arm.sigma_vars.iter().map(String::as_str).collect();
        let body = {
            let env = env.push(&sigma_refs);
            fuel_gated_firing(arm, def, fingerprint, &env, carrier)?
        };
        cases.push(Case { pattern: check.pattern, free_count: check.free_count, body });
    }
    Ok(cases)
}

/// The post-join re-check node (v1 §4.3.2): match the reassembled `[⌜label⌝, s₀, …]`
/// against the redex arms only; the wildcard default publishes it as this subtree's
/// normal form.
fn recheck_node(
    arms: &[DriveRedexArm],
    def: &LanguageDef,
    fingerprint: &str,
    env: &Env,
    label: &str,
    child_names: &[String],
    carrier: &dyn DriveCarrier,
) -> Result<Node, String> {
    let children: Vec<Node> = child_names.iter().map(|name| env.var(name)).collect();
    let assembled = carrier.reassemble(env, label, &children);
    let mut cases = redex_cases(arms, def, fingerprint, env, carrier)?;
    let default_children: Vec<Node> = child_names.iter().map(|name| env.var(name)).collect();
    cases.push(Case {
        pattern: pat_wildcard(),
        free_count: 0,
        body: send(env.var("ret"), vec![carrier.reassemble(env, label, &default_children)]),
    });
    Ok(match_(assembled, cases))
}

/// Build the persistent `^drive` receiver family for one admitted language (see the
/// module docs for the emitted shape). Deterministic arm order: redex arms (declaration
/// order), congruence-descent arms (constructor declaration order), the binder arm, the
/// `^free`/`^bound` passthroughs, the `^drive-err` wildcard.
pub(crate) fn drive_program_par(
    def: &LanguageDef,
    fingerprint: &str,
    arms: &[DriveRedexArm],
    carrier: &dyn DriveCarrier,
) -> Result<Par, String> {
    let frame = carrier.frame_formals();
    let env = Env::root(&frame.formals);
    let mut cases: Vec<Case> = Vec::new();

    // 1. Redex arms — outermost-first strategy: a redex at this node fires before any
    //    descent.
    cases.extend(redex_cases(arms, def, fingerprint, &env, carrier)?);

    // 2. Congruence-descent arms — one per non-reserved object constructor (the C2
    //    enumeration the subst TRS uses, minus nothing: binders are excluded there and
    //    carried by the dedicated arm below).
    for (label, arity) in object_congruence_constructors(def) {
        let child_pats: Vec<Par> = (0..arity).map(pat_free).collect();
        let body = {
            let child_names: Vec<String> = (0..arity).map(|i| format!("c{i}")).collect();
            let child_refs: Vec<&str> = child_names.iter().map(String::as_str).collect();
            let env = env.push(&child_refs);
            if arity == 0 {
                // A nullary object leaf is its own normal form.
                send(env.var("ret"), vec![tagged(fingerprint, &label, Vec::new())])
            } else {
                new_scope(arity, {
                    let ret_names: Vec<String> = (0..arity).map(|i| format!("r{i}")).collect();
                    let ret_refs: Vec<&str> = ret_names.iter().map(String::as_str).collect();
                    let env = env.push(&ret_refs);
                    // Concurrent child drives — descent copies fuel, NEVER decrements
                    // (per-path semantics, plan v2 §4.2).
                    let mut composed: Option<Node> = None;
                    for i in 0..arity {
                        let call = send(
                            ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
                            vec![
                                carrier.child_payload(&env, i),
                                env.var("fuel"),
                                env.var(&ret_names[i]),
                            ],
                        );
                        composed = Some(match composed {
                            None => call,
                            Some(acc) => par2(acc, call),
                        });
                    }
                    // The atomic join, then the inline post-join re-check.
                    let join_sources: Vec<Node> = ret_names.iter().map(|r| env.var(r)).collect();
                    let join_node = join(join_sources, {
                        let s_names: Vec<String> = (0..arity).map(|i| format!("s{i}")).collect();
                        let s_refs: Vec<&str> = s_names.iter().map(String::as_str).collect();
                        let env = env.push(&s_refs);
                        recheck_node(arms, def, fingerprint, &env, &label, &s_names, carrier)?
                    });
                    par2(composed.expect("arity ≥ 1"), join_node)
                })
            }
        };
        cases.push(Case {
            pattern: pat_tagged(fingerprint, &label, child_pats),
            free_count: arity,
            body,
        });
    }

    // 3. The binder arm (`[⌜^lambda⌝, b]` ⟹ drive the body, rewrap) — emitted when the
    //    language declares a single-binder term. The post-REWRAP re-check follows the
    //    plan v2 §4.3.2 emission rule: emitted iff some compiled redex arm is
    //    binder-rooted (compile-time known; skipped for Lambda/Ambient — no bundled entry
    //    root is a binder).
    let has_single_binder = def
        .terms
        .iter()
        .any(|term| is_binder_term(term) && !is_multi_binder_term(term));
    if has_single_binder {
        let binder_rooted_entry = arms.iter().any(|arm| arm.root_is_binder);
        let body = {
            let env = env.push(&["b"]);
            new_scope(1, {
                let env = env.push(&["r"]);
                let drive_body = send(
                    ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
                    vec![env.var("b"), env.var("fuel"), env.var("r")],
                );
                let rewrap = for1(env.var("r"), {
                    let env = env.push(&["rb"]);
                    if binder_rooted_entry {
                        // A binder-rooted entry exists: the rewrapped node may itself be
                        // a redex — re-check it against the redex arms only.
                        recheck_node(
                            arms,
                            def,
                            fingerprint,
                            &env,
                            LAMBDA_REFLECT_LABEL,
                            &["rb".to_string()],
                            carrier,
                        )?
                    } else {
                        send(
                            env.var("ret"),
                            vec![tagged(fingerprint, LAMBDA_REFLECT_LABEL, vec![env.var("rb")])],
                        )
                    }
                });
                par2(drive_body, rewrap)
            })
        };
        cases.push(Case {
            pattern: pat_tagged(fingerprint, LAMBDA_REFLECT_LABEL, vec![pat_free(0)]),
            free_count: 1,
            body,
        });
    }

    // 4. Reserved passthroughs: a free-variable leaf and a bound-variable leaf are inert
    //    under the drive (the `^subst`/`^shift` `:787-796` / `:831-833` shape).
    cases.push(Case {
        pattern: pat_tagged(fingerprint, FREE_VAR_REFLECT_LABEL, vec![pat_free(0)]),
        free_count: 1,
        body: {
            let env = env.push(&["x"]);
            send(env.var("ret"), vec![tagged(fingerprint, FREE_VAR_REFLECT_LABEL, vec![env.var("x")])])
        },
    });
    cases.push(Case {
        pattern: pat_tagged(fingerprint, BOUND_VAR_REFLECT_LABEL, vec![pat_free(0)]),
        free_count: 1,
        body: {
            let env = env.push(&["n"]);
            send(env.var("ret"), vec![tagged(fingerprint, BOUND_VAR_REFLECT_LABEL, vec![env.var("n")])])
        },
    });

    // 5. The typed fail-close wildcard: an unrecognized head is NEVER silently normal
    //    (the R3 `^respread-err` discipline) — it rests on the GString err channel where
    //    the host cross-check sees it.
    cases.push(Case {
        pattern: pat_wildcard(),
        free_count: 0,
        body: send(
            ground(new_gstring_par(drive_err_channel(fingerprint), Vec::new(), false)),
            vec![env.var("t")],
        ),
    });

    let body = match_(env.var("t"), cases);
    Ok(persistent_contract(tag_par(fingerprint, DRIVE_RESERVED_LABEL), frame.formals.len(), body).par)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::lower_language_def;
    use mettail_ast::language::LanguageDef;

    /// The PRODUCTION-Lambda-shaped def (same name, terms, rewrites as
    /// `languages/src/lambda.rs`) — name `Lambda` IS in [`DRIVE_OPT_IN`].
    fn production_lambda_shaped_def() -> LanguageDef {
        let fragment = r#"
            name: Lambda,
            types { Term },
            terms {
                Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
                App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
            },
            equations {},
            rewrites {
                Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ;
                AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N) ;
                AppCongR . | N0 ~> N1 |- (App M N0) ~> (App M N1) ;
                LamCong . | S ~> T |- (Lam ^x.S) ~> (Lam ^x.T) ;
            },
        "#;
        syn::parse_str::<LanguageDef>(fragment).expect("the Lambda-shaped def parses")
    }

    /// The same grammar under a NON-opted-in name.
    fn renamed_lambda_shaped_def() -> LanguageDef {
        let fragment = r#"
            name: NotOptedLambda,
            types { Term },
            terms {
                Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
                App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
            },
            equations {},
            rewrites {
                Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ;
            },
        "#;
        syn::parse_str::<LanguageDef>(fragment).expect("the renamed def parses")
    }

    fn lowered_for(def: &LanguageDef) -> crate::rho_net_lower::RhoNetLowered {
        let lowering = lower_language_def(def);
        RhoNetProgram::from_language_def(def, &lowering).lower_to_par(def, &lowering)
    }

    #[test]
    fn lambda_shaped_def_is_drive_admitted_with_one_persistent_drive_receiver() {
        let def = production_lambda_shaped_def();
        let lowered = lowered_for(&def);
        assert_eq!(
            lowered.drive_admission(),
            &DriveAdmission::Admitted,
            "the Lambda-shaped opted-in def admits the driver"
        );
        let drive = lowered.drive().expect("an admitted language carries the drive program");
        assert_eq!(drive.receives.len(), 1, "the driver is ONE persistent ^drive receiver");
        let receive = &drive.receives[0];
        assert!(receive.persistent, "the ^drive receiver is persistent");
        assert_eq!(
            receive.binds[0].patterns.len(),
            3,
            "the PS frame is (t, fuel, ret)"
        );
        let expected_chan = tag_par(&lowered.language_fingerprint, DRIVE_RESERVED_LABEL);
        assert_eq!(
            receive.binds[0].source.as_ref(),
            Some(&expected_chan),
            "the driver listens on the reserved GPrivate ^drive channel"
        );

        // The installed program gains the driver ONCE, alongside the β seed + the 5 TRS
        // receivers: 1 (SubstRewrite σ-receiver) + 5 (TRS) + 1 (^drive) = 7.
        let installed = lowered
            .installed_program_par()
            .expect("the Lambda-shaped def installs (A-S5.1 exemptions + drive)");
        assert_eq!(
            installed.receives.len(),
            7,
            "installed = β seed + five TRS receivers + the ^drive receiver"
        );
    }

    #[test]
    fn non_opted_in_language_records_not_requested_and_installs_byte_identically() {
        let def = renamed_lambda_shaped_def();
        let lowered = lowered_for(&def);
        assert_eq!(
            lowered.drive_admission(),
            &DriveAdmission::NotRequested,
            "a non-DRIVE_OPT_IN language never requests the driver"
        );
        assert!(lowered.drive().is_none(), "no drive program is built");
        let installed = lowered.installed_program_par().expect("the renamed def installs");
        assert_eq!(
            installed.receives.len(),
            6,
            "installed = β seed + five TRS receivers ONLY (byte-lean, no driver)"
        );
    }

    #[test]
    fn non_linear_lhs_records_unsupported_with_the_transcription_reason() {
        // Opted-in name, but the fireable rewrite's LHS repeats a variable — the driver
        // has no MatchCase.guard equality arms this stage (A-S5.5), so admission records
        // Unsupported (either via the transcription conjunct or the static gate,
        // whichever family the ruleset assigns — both are fail-closed).
        let fragment = r#"
            name: Lambda,
            types { Term },
            terms {
                A . |- "A" : Term ;
                Pair . x:Term, y:Term |- "pair" "(" x "," y ")" : Term ;
            },
            equations {},
            rewrites {
                Collapse . |- (Pair x x) ~> x ;
            },
        "#;
        let def = syn::parse_str::<LanguageDef>(fragment).expect("the non-linear def parses");
        let lowered = lowered_for(&def);
        match lowered.drive_admission() {
            DriveAdmission::Unsupported { reason } => {
                assert!(
                    reason.contains("Collapse") || reason.contains("static gate"),
                    "the reason names the failing rewrite or gate: {reason}"
                );
            },
            other => panic!("a non-linear fireable LHS must record Unsupported, got {other:?}"),
        }
        assert!(lowered.drive().is_none(), "no partial driver is ever built");
    }

    #[test]
    fn sigma_variable_colliding_with_the_drive_frame_records_unsupported() {
        // `fuel` as an LHS σ variable would shadow the driver's fuel formal
        // (innermost-first Env resolution) — fail-closed at admission.
        let fragment = r#"
            name: Lambda,
            types { Term },
            terms {
                A . |- "A" : Term ;
                Wrap . x:Term |- "wrap" "(" x ")" : Term ;
                Pair . x:Term, y:Term |- "pair" "(" x "," y ")" : Term ;
            },
            equations {},
            rewrites {
                Unwrap . |- (Pair (Wrap fuel) other) ~> (Pair fuel other) ;
            },
        "#;
        let def = syn::parse_str::<LanguageDef>(fragment).expect("the colliding def parses");
        let lowered = lowered_for(&def);
        match lowered.drive_admission() {
            DriveAdmission::Unsupported { reason } => {
                assert!(
                    reason.contains("fuel"),
                    "the reason names the colliding variable: {reason}"
                );
            },
            other => panic!("a frame-name collision must record Unsupported, got {other:?}"),
        }
    }

    #[test]
    fn drive_invocation_carries_the_seed_and_the_fingerprint_derived_channels() {
        let invocation = rho_net_drive_invocation("fp-x", Par::default(), "OUT");
        assert_eq!(invocation.out_channel, "OUT");
        assert_eq!(invocation.fired_channel, "^fired:fp-x");
        assert_eq!(invocation.err_channel, "^drive-err:fp-x");
        assert_eq!(invocation.fuel_channel, "^drive-fuel:fp-x");
        assert_eq!(invocation.call.sends.len(), 1, "the seed is one send");
        let send = &invocation.call.sends[0];
        assert_eq!(
            send.chan.as_ref(),
            Some(&tag_par("fp-x", DRIVE_RESERVED_LABEL)),
            "the seed targets the reserved ^drive channel"
        );
        assert_eq!(send.data.len(), 3, "^drive!(subject, fuel, out) — three data");
        assert_eq!(
            send.data[1],
            new_gint_par(DRIVE_DEFAULT_FUEL, Vec::new(), false),
            "the default seed fuel is the fixed per-path bound (decision 2)"
        );
    }

    #[test]
    fn reserved_registry_carries_the_four_drive_labels() {
        let reserved = crate::rho_net_subst_trs::reserved_subst_trs_labels();
        for label in [
            DRIVE_RESERVED_LABEL,
            DRIVE_ERR_RESERVED_LABEL,
            DRIVE_FUEL_RESERVED_LABEL,
            FIRED_RESERVED_LABEL,
        ] {
            assert!(
                reserved.contains(&label),
                "the C2 reserved registry must guard {label:?}"
            );
        }
    }
}
