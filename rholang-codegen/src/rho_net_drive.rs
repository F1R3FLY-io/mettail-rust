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
//!     ⟦LHSᵢ⟧-pattern =>                                     -- 1. redex arms — POSITIONAL first (Lambda Beta),
//!         match fuel {                                       --    then NESTED-AC (In, Out — declaration order),
//!           0 => @"^drive-fuel:{fp}"!(⟦redex-node⟧)          --    then STRUCTURAL-AC (Open) — the documented
//!           _ => new r in { acceptᵢ!(σ…, r)                  --    deterministic order. Exhaustion: 0-case FIRST
//!                         | @"^fired:{fp}"!("RuleLabelᵢ")    --    (AM-7). Positional arms fire through the
//!                         | for(@c <- r){ ⌜^drive⌝!(c, fuel - 1, ret) } }   -- EXISTING σ ABI + re-drive.
//!         }
//!     ⟦AC-LHSⱼ⟧-check-pattern  guard (Mₐ == M_b) =>         --    A-S5.5 AC arms: the operand CHECK pattern
//!         match fuel {                                       --    (nested_match_pattern_for — guard slots +
//!           0 => @"^drive-fuel:{fp}"!(t)                     --    the bound outer rest, all else wildcarded)
//!           _ => new r in { ⌜^drive-ac:Rⱼ⌝!(t, r)            --    + the cross-level EEq as MatchCase.guard
//!                         | @"^fired:{fp}"!("RuleLabelⱼ")    --    (F12); fire through the CARRIER ABI
//!                         | for(@c <- r){ ⌜^drive⌝!(c, fuel - 1, ret) } }   -- (plan v2 §4.3.1), then re-drive.
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
//!     {@"ac:op"!(e) | rem} =>                                -- 4. BAG arm (A-S5.5, one per HashBag op):
//!         new re, rr in {                                    --    peel ONE element (send-pattern + free
//!           ⌜^drive⌝!(e, fuel, re)                           --    remainder), drive the element AND the
//!         | ⌜^drive⌝!(rem, fuel, rr)                         --    remainder concurrently (NO decrement),
//!         | for(@ve <- re & @vr <- rr){                      --    atomic join, then
//!             new f in {
//!               match ve {                                   --    the AM-3 THREE-CASE reassembly splice:
//!                 Nil => f!(Nil)                             --      Nil ⇒ splice-as-nothing
//!                 {@"ac:op"!(_) | _} => f!(ve)               --      same-op soup ⇒ compose its sends (splice)
//!                 _ => f!(@"ac:op"!(ve))                     --      else ⇒ wrap one element send
//!               }
//!             | for(@w <- f){                                --    then the POST-JOIN RE-CHECK of the
//!                 match {w | vr} {                           --    re-composed soup (redex arms ONLY —
//!                   <redex arms, fuel-gated>                 --    catches redexes formed ACROSS the
//!                   _ => ret!({w | vr})                      --    reassembled siblings)
//!                 } } } } }
//!     Nil => ret!(Nil)                                       -- 5. the EMPTY BAG is its own NF (AM-3 Nil leaf)
//!     [⌜^free⌝, x]  => ret!([⌜^free⌝, x])                    -- 6. reserved passthroughs
//!     [⌜^bound⌝, n] => ret!([⌜^bound⌝, n])
//!     _ => @"^drive-err:{fp}"!(t)                            -- 7. typed fail-close wildcard
//!   }
//! }
//! ```
//!
//! * **Strategy**: redex arms precede descent ⟹ per-node outermost-first
//!   (normal-order-flavored); a fired contractum is fully re-driven. A guard-vetoed AC
//!   arm (the reducer evaluates `MatchCase.guard` in the case env and FALLS THROUGH on
//!   `false` — F12, `f1r3node reduce.rs:1290-1303`) reaches the bag arm, so a
//!   name-mismatched soup still descends and rests.
//! * **Bag-arm termination**: each peel strictly shrinks the soup (the remainder has one
//!   element fewer, the empty remainder is the Nil leaf), the element/remainder drives are
//!   strict sub-value descents, and the post-join re-check fires (fuel-bounded) or
//!   returns — no descent loop.
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
//! # The AC carrier ABI (A-S5.5, plan v2 §4.3.1 / F4 / AM-3)
//!
//! Every admitted structural-AC / nested-structural-AC rule `R` gets ONE reserved
//! per-rule `GPrivate` carrier channel `⌜^drive-ac:R⌝`
//! ([`crate::rho_net_lower::DRIVE_AC_RESERVED_LABEL`], joined to the reserved registry +
//! C2 collision assertion) and a FIXED-CHANNEL persistent AC-CARRIER receiver
//! ([`ac_carrier_receiver_par`]) installed beside `^drive`: the SAME operand bind pattern
//! + cross-level non-linear `Receive.condition` as the site-keyed `ac:` MATCH receivers
//! landed through A-S5.4b ([`crate::rho_net_lower::nested_match_bind_pattern_for`] —
//! every σ slot re-bound from the DELIVERED operand, no host σ), the source channel the
//! reserved per-rule carrier instead of the site-keyed `ac:` name. The site-keyed
//! receivers on the non-driver locate-all path are UNTOUCHED (byte-identity pinned).
//!
//! ONE deliberate body difference from the site-keyed receivers (plan v2 §4.3.3
//! "contractum entry" + AM-3): every reduct element that is a bound σ SLOT (an
//! [`AcReconstructTemplate::Var`] at a bag-element position) is emitted through the
//! THREE-CASE bag-fragment dispatch —
//!
//! ```text
//! match σ[v] { Nil => f!(Nil)                 -- an empty bag splices as NOTHING
//!            ; {@"ac:op"!(_) | _} => f!(σ[v]) -- a same-op soup composes its sends DIRECTLY (one-level splice)
//!            ; _ => f!(@"ac:op"!(σ[v])) }     -- anything else wraps as ONE element send
//! ```
//!
//! — so a bag-valued σ slot SPLICES instead of nesting, matching the host's value-level
//! `add_flattened_bag` (`dovetail/src/rules.rs:707`; multiplicity-preserving). One level
//! of splice per reassembly suffices BY THE DRIVE INDUCTION (AM-3(b)): a never-driven
//! value (a capability continuation) can arrive arbitrarily deeply nested in ONE firing,
//! but the contractum's own re-drive descends every element (the bag arm) and each
//! reassembly seam — the carrier's contractum emission AND the bag arm's element
//! re-composition — splices one layer, so the resting term is flat. FV:
//! `driver_flatten_agrees_with_add_flattened_bag` (`InRhoQuiescenceDriver.v`).
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
//! [`firing_emission_node`] (positional σ-ABI arms) and its A-S5.5 carrier-ABI twin
//! [`ac_firing_emission_node`] (AC arms): `ContractumRedrive` (today's re-drive `for`) is
//! implemented; `ScionBundle` is the E-1 forward-compatibility variant — PRESENT,
//! CONSTRUCTED NOWHERE (deliberately: it is the seam, not dead code). Seam invariant a
//! bundle must preserve (the SM-7 wording, issued here because A-S5.5 landed first): for
//! every schedule, the value ultimately reaching `ret` is a member of
//! `NF_drive(contractum)` — the set of values some `^drive` trace rests at from the
//! contractum at the arm's post-firing fuel. On confluent (or root-stable orthogonal)
//! fragments this set is a singleton and the clause degenerates to `norm(contractum)`.
//! Fired-multiset and exhaustion observations are per-trace, compared under the
//! decision-(3)/AM-5 regime: strict equality on confluent cells; valid-NF-set membership
//! + ledger consistency on non-confluent cells.
//!
//! # Admission (plan v2 §4.4 / F9, amendment AM-4)
//!
//! `drive_admissible(def, ruleset)` = static-gate-Ok ∧ every admitted matching family is
//! driver-supported (positional/subst σ-ABI entries since A-S5.2; structural-AC +
//! nested-structural-AC carrier-ABI entries since A-S5.5 — native / linear-AC /
//! contextual / comm families remain unsupported) ∧ the language is opted in via the
//! codegen-visible [`DRIVE_OPT_IN`] const (consulted by the macro emitter, so a
//! non-opted-in language's generated module is byte-identical — the AM-4 pin) ∧ every
//! fireable rewrite transcribes to a driver redex arm (positional transcription, or the
//! AC shape recognition + match-representability for a collection LHS). The disposition
//! is RECORDED on [`crate::rho_net_lower::RhoNetLowered`] as [`DriveAdmission`], never
//! silent. Both A-S5 languages now admit: Lambda (positional Beta, A-S5.2) and Ambient
//! (nested In/Out + structural Open through the carrier ABI, A-S5.5).
//!
//! FV: `formal/rocq/rho_bridge/theories/InRhoQuiescenceDriver.v` — the driver as a
//! big-step LTS over the reflected object fragment: `drive_steps_sound`,
//! `quiescence_sound` (per-trace, join re-check case included),
//! `fuel_exhaustion_never_wrong`, the iterated β weak bisimulation (`drive_weak_bisim`)
//! discharged through `DeBruijnSubstTRS.v`'s SN + confluence, and — A-S5.5 — the BAG
//! driver model (`bdrives`: the peel/join/three-case-splice arm over an abstract redex
//! relation; `bag_quiescence_sound`, `bag_flatness_sound`, `bag_fuel_exhaustion_is_redex`)
//! plus the flattening agreement lemma `driver_flatten_agrees_with_add_flattened_bag`
//! (plan v2 §7.2).

use std::collections::{HashMap, HashSet};

use mettail_ast::grammar::TermParam;
use mettail_ast::language::{LanguageDef, RewriteRule};
use mettail_ast::pattern::{Pattern, PatternTerm};
use mettail_ast::types::CollectionType;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EMinus, Expr, Par, Receive, ReceiveBind};
use models::rust::utils::{new_freevar_par, new_gint_par, new_gstring_par, new_send_par};
use syn::Ident;

use crate::rho_net::RhoNetProgram;
use crate::rho_net_lower::{
    ac_soup_channel, count_var_occurrences, lower_lhs_vars, nested_match_bind_pattern_for,
    nested_match_pattern_for, nested_structural_ac_rule_shape,
    nested_structural_ac_shape_is_match_representable, nonlinear_consistency_condition,
    resolve_ac_collection_type, resolve_constructor_collection_type, structural_ac_rule_shape,
    structural_ac_shape_is_match_representable, AcReconstructTemplate, NestedBindState,
    RhoNetLoweredRule, RhoNetLoweringError, UnsupportedFamily, BOUND_VAR_REFLECT_LABEL,
    DRIVE_AC_RESERVED_LABEL, DRIVE_ERR_RESERVED_LABEL, DRIVE_FUEL_RESERVED_LABEL,
    DRIVE_RESERVED_LABEL, FIRED_RESERVED_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
};
use crate::rho_net_ruleset::{
    compile_in_rho_matching_ruleset, in_rho_static_gate, InRhoMatchingRuleset,
};
use crate::rho_net_subst_trs::{
    for1, free_bits, ground, is_binder_term, join, match_, match_guarded, new_scope, node_from_par,
    nullary_term, object_congruence_constructors, par2, pat_free, pat_tagged, pat_wildcard,
    persistent_contract, send, tag_par, tagged, union_free, Case, Env, Node,
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
/// Opt-in expresses INTENT; admission is the conjunction in [`drive_admissible`]. Both
/// opted-in languages ADMIT since A-S5.5: Lambda through its positional σ-ABI Beta arm
/// (A-S5.2), Ambient through the AC carrier-ABI arms (A-S5.5).
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

/// The driver-admission predicate (plan v2 §4.4; A-S5.2, AC families A-S5.5): **opted
/// in** (AM-4, by name in [`DRIVE_OPT_IN`]) ∧ **static gate Ok** ([`in_rho_static_gate`]
/// — every fireable rewrite matchable in Rho, congruence-only rewrites exempt) ∧ **every
/// admitted matching family driver-supported** (positional/subst σ-ABI entries +
/// structural-AC / nested-structural-AC carrier-ABI entries; a non-empty native /
/// linear-AC / contextual dispatch family or a multi-binder term is not drivable) ∧
/// **every fireable seed transcribes** to a driver redex arm (a linear,
/// constructor-rooted positional LHS whose σ variables avoid the driver frame names, OR
/// a match-representable structural/nested-structural AC shape whose carrier builds).
///
/// A PURE function of `(def, ruleset)` — both live in the memoized
/// [`crate::rho_net_cache::CompiledInRhoArtifacts`], so the generated
/// `rho_net_drive_invocation_to` body re-checks admission per exec at cache-hit cost
/// (the fail-closed guard that kept the A-S5.4b→A-S5.5 window typed: Ambient's static
/// gate passed while its driver arms did not yet exist, and the seed would otherwise
/// have rested unanswered).
pub fn drive_admissible(def: &LanguageDef, ruleset: &InRhoMatchingRuleset) -> DriveAdmission {
    let name = def.name.to_string();
    if !DRIVE_OPT_IN.contains(&name.as_str()) {
        return DriveAdmission::NotRequested;
    }

    let mut reasons: Vec<String> = Vec::new();

    // Conjunct 1: the A-S2 static capability gate. A-S5.8 refinement (F8-AM-1b — the
    // constructive-discharge witness's admission): a static-gate DEFER is DISCHARGED when
    // its fireable rewrite is a collection-LHS rule that TRANSCRIBES to a driver AC-carrier
    // arm ([`build_drive_ac_arm`] — the carrier is SELF-CONTAINED: the drive's own `Match`
    // arm decides the redex and the carrier receiver rebuilds the contractum, needing no
    // locate-all match entry). This is exactly the binder-templated nested-AC shape
    // ([`crate::rho_net_lower::RhoNetLoweredRule::NestedStructuralAcBinderTemplated`]):
    // recorded NO-MATCH-ENTRY on the locate-all paths (which stay fail-closed — the
    // report-free MATCH body still rejects such a def, correctly, because the locate-all
    // network genuinely cannot fire the rule), while the DRIVE path — whose matching is its
    // own arms — admits it. Every bundled production language passes the gate outright, so
    // this discharge changes NO bundled admission; a defer that does NOT transcribe still
    // rejects, fail-closed.
    if let Err(deferred) = in_rho_static_gate(ruleset, def) {
        let undischarged: Vec<String> = deferred
            .iter()
            .filter(|entry| {
                let carrier_transcribes = def.rewrites.iter().any(|rewrite| {
                    rewrite.name == entry.rule_label
                        && !crate::rho_net_lower::congruence_only_premises(&rewrite.premises)
                        && matches!(
                            lower_lhs_vars(&rewrite.left),
                            Err(UnsupportedFamily::CollectionAc)
                        )
                        && build_drive_ac_arm(rewrite, def, &ruleset.language_fingerprint).is_ok()
                });
                !carrier_transcribes
            })
            .map(|entry| format!("{} ({:?})", entry.rule_label, entry.reason))
            .collect();
        if !undischarged.is_empty() {
            reasons.push(format!(
                "static gate rejects: fireable rule(s) not matchable in Rho: {}",
                undischarged.join(", ")
            ));
        }
    }

    // Conjunct 2: every admitted matching family must be driver-supported. Since A-S5.5
    // the structural-AC + nested-structural-AC families ARE driver-supported (carrier-ABI
    // arms; each entry's transcription is validated per-rewrite in conjunct 3); the
    // native / linear-AC / contextual families remain unsupported.
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
    if !unsupported_families.is_empty() {
        reasons.push(format!(
            "matching families not driver-supported: {}",
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
    // driver redex arm. The routing mirrors `lower_base_rewrite` exactly: a flat-σ LHS
    // (`lower_lhs_vars` Ok, or any non-collection failure) takes the POSITIONAL
    // transcription (A-S5.2 — the σ-receiver first-occurrence order); a collection LHS
    // (`Err(CollectionAc)`) takes the A-S5.5 AC-CARRIER transcription (the nested /
    // structural shape recognition + match-representability + the carrier build).
    for rewrite in &def.rewrites {
        if crate::rho_net_lower::congruence_only_premises(&rewrite.premises) {
            continue;
        }
        let validation = match lower_lhs_vars(&rewrite.left) {
            Err(UnsupportedFamily::CollectionAc) => {
                build_drive_ac_arm(rewrite, def, &ruleset.language_fingerprint).map(|_| ())
            },
            _ => validate_seed_transcription(rewrite, def, &ruleset.language_fingerprint),
        };
        if let Err(error) = validation {
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
    /// The closed seed `Par`: `⌜^drive⌝!(⟦term⟧, fuel, @out_channel)` — or, for a
    /// float-bearing language (A-S5.8 decision Q-SEED = S2), the float-routed sibling
    /// `new rf { ⌜^float⌝!(⟦term⟧, rf) | for(@cf <- rf){ ⌜^drive⌝!(cf, fuel, @out) } }`.
    pub call: Par,
    /// A-S5.8 (F8-AM-5a): the RAW reflected subject `⟦term⟧` the seed carries — surfaced
    /// directly so harness/ledger readers survive BOTH seed shapes without navigating the
    /// call structure (under S2 the subject is no longer `call.sends[0].data[0]`).
    pub subject: Par,
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
        call: rho_net_drive_call_par(language_fingerprint, subject.clone(), out_channel),
        subject,
        out_channel: out_channel.to_string(),
        fired_channel: drive_fired_channel(language_fingerprint),
        err_channel: drive_err_channel(language_fingerprint),
        fuel_channel: drive_fuel_channel(language_fingerprint),
    }
}

/// A-S5.8 (decision Q-SEED = S2): the FLOAT-ROUTED drive seed with an EXPLICIT per-path
/// fuel — the sibling of [`rho_net_drive_call_par_with_fuel`] for float-bearing languages:
///
/// ```text
/// new rf in { ⌜^float⌝!(⟦subject⟧, rf) | for(@cf <- rf){ ⌜^drive⌝!(cf, fuel, @out) } }
/// ```
///
/// The installed `^float` dispatcher canonicalizes the RAW subject (every extrudable
/// binder to the top run, every bag flat) BEFORE the first `^drive` frame sees it, so a
/// raw direct injection is correct WITHOUT the host boundary float. Under S2 the
/// production seed's subject is ALREADY host-float-canonical (the retained boundary float,
/// INV — load-bearing for the run-order-sensitive α goldens, F8-AM-5b), so this float is
/// an identity pass (≈ 2 COMMs per node, once per exec).
pub fn rho_net_drive_float_call_par_with_fuel(
    language_fingerprint: &str,
    subject: Par,
    fuel: i64,
    out_channel: &str,
) -> Par {
    new_scope(1, {
        let env = Env::root(&["rf"]);
        let float_call = send(
            ground(tag_par(language_fingerprint, crate::rho_net_lower::FLOAT_RESERVED_LABEL)),
            vec![ground(subject), env.var("rf")],
        );
        let redrive = for1(env.var("rf"), {
            let env = env.push(&["cf"]);
            send(
                ground(tag_par(language_fingerprint, DRIVE_RESERVED_LABEL)),
                vec![
                    env.var("cf"),
                    ground(new_gint_par(fuel, Vec::new(), false)),
                    ground(new_gstring_par(out_channel.to_string(), Vec::new(), false)),
                ],
            )
        });
        par2(float_call, redrive)
    })
    .par
}

/// The FLOAT-ROUTED drive seed with the production per-path fuel ([`DRIVE_DEFAULT_FUEL`]).
pub fn rho_net_drive_float_call_par(
    language_fingerprint: &str,
    subject: Par,
    out_channel: &str,
) -> Par {
    rho_net_drive_float_call_par_with_fuel(
        language_fingerprint,
        subject,
        DRIVE_DEFAULT_FUEL,
        out_channel,
    )
}

/// Assemble the full [`RhoNetDriveInvocation`] whose seed routes through the installed
/// `^float` dispatcher (A-S5.8, decision Q-SEED = S2) — the float-bearing sibling of
/// [`rho_net_drive_invocation`], emitted by the generated `rho_net_drive_invocation_to`
/// for exactly the languages passing the float gate. Same observation channels; the
/// [`RhoNetDriveInvocation::subject`] field carries the raw reflected subject (F8-AM-5a).
pub fn rho_net_drive_float_invocation(
    language_fingerprint: &str,
    subject: Par,
    out_channel: &str,
) -> RhoNetDriveInvocation {
    RhoNetDriveInvocation {
        call: rho_net_drive_float_call_par(language_fingerprint, subject.clone(), out_channel),
        subject,
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
    /// The source RHS pattern (E-1: retained for the scion-bundle construction —
    /// [`scion_bundle_for_rule`]; unused when the arm re-drives).
    pub(crate) rhs: Pattern,
    /// The transcribed tagged-`EList` `Match` pattern (σ variables as `FreeVar`s in
    /// first-occurrence order; binder constructors remapped to their reflected tags).
    pub(crate) pattern: Par,
    /// Whether the transcribed pattern's ROOT is a binder tag — drives the binder-arm
    /// post-rewrap re-check emission rule (plan v2 §4.3.2; `false` for every bundled
    /// driver language).
    pub(crate) root_is_binder: bool,
    /// E-1: emit a scion bundle for this arm instead of `ContractumRedrive`. Set only under
    /// [`ScionPolicy::StructuralScion`] for a positional `BaseRewrite` arm (never β
    /// `SubstRewrite`); ALWAYS `false` on the production path ([`ScionPolicy::AllRedrive`]),
    /// keeping every emitted driver byte-identical.
    pub(crate) scion: bool,
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// A-S5.5: the AC carrier-ABI redex arms (structural-AC + nested-structural-AC families).
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// One compiled AC-family redex arm (A-S5.5, plan v2 §4.3.1): an admitted structural-AC
/// (`OpenRule`) or nested-structural-AC (`InRule`/`OutRule`) rewrite transcribed to a
/// driver `Match` arm — the operand CHECK pattern
/// ([`crate::rho_net_lower::nested_match_pattern_for`]: one guard slot per cross-level /
/// non-linear channel occurrence + the bound outer rest, all else wildcarded), the
/// non-linear `EEq` conjunction as the per-case `MatchCase.guard` (F12), and the firing
/// through the CARRIER ABI: `new r { ⌜^drive-ac:R⌝!(t, r) | ledger |
/// for(@c <- r){ ^drive!(c, fuel-1, ret) } }`, where the fixed-channel persistent
/// AC-carrier receiver ([`Self::receiver`]) re-binds every σ slot from the delivered
/// operand and emits the contractum (three-case-spliced, F4/AM-3) to the fresh `r`.
///
/// The POSITIONAL twin is [`DriveRedexArm`]; the two are joined by [`DriveArm`] in the
/// documented deterministic arm order (positional, then nested-AC, then structural-AC).
#[derive(Debug, Clone)]
pub(crate) struct DriveAcArm {
    /// The bare source rewrite label (the ledger datum).
    pub(crate) rule_label: String,
    /// The reserved per-rule carrier tag label `"^drive-ac:{rule_label}"` — the arm fires
    /// `⌜carrier⌝!(t, r)` on `tag_par(fp, carrier_label)`, the SAME `GPrivate` channel
    /// [`Self::receiver`] rests on.
    pub(crate) carrier_label: String,
    /// The transcribed operand CHECK `Match` pattern (guard slots + the bound outer rest;
    /// every reduct position wildcarded — the carrier re-binds those itself).
    pub(crate) pattern: Par,
    /// The pattern's bound-slot count (`guard occurrences + 1` for the outer rest).
    pub(crate) free_count: usize,
    /// The cross-level / non-linear consistency conjunction
    /// ([`crate::rho_net_lower::nonlinear_consistency_condition`] over the case frame) —
    /// carried as `MatchCase.guard`, evaluated by the reducer in the case env; a `false`
    /// falls through to the next arm (guard-veto ⟹ descent).
    pub(crate) guard: Par,
    /// Synthetic case-frame binder names for the pattern's slots (`__ac0…`, innermost
    /// last) — pushed on the [`Env`] so the case body's `t`/`fuel`/`ret` references
    /// resolve at the right depth; the slots themselves are never read by the arm body
    /// (the carrier re-binds from the delivered operand).
    pub(crate) case_names: Vec<String>,
    /// The fixed-channel persistent AC-CARRIER receiver ([`ac_carrier_receiver_par`]) —
    /// appended to the drive program once per AC arm.
    pub(crate) receiver: Par,
}

/// A compiled driver redex arm of either family, in the documented deterministic order
/// (positional first, then nested-AC, then structural-AC; declaration order within each).
///
/// BOTH payloads are boxed, symmetrically, and the symmetry is the point. `DriveRedexArm`
/// is 456 bytes and `DriveAcArm` is 824, so an unboxed sum is 832 bytes per element — and
/// the three vectors it is assembled from (`positional_arms` / `nested_ac_arms` /
/// `structural_ac_arms`, each `Vec::with_capacity(rules.len())`, then concatenated) are
/// HOMOGENEOUS, so every positional rule paid 376 bytes for a variant its vector never
/// holds. Boxing only the larger payload just moves the complaint to the other variant
/// (measured: `large_enum_variant` re-fired on `Positional` at 456 vs 8) and makes the
/// total WORSE whenever AC rules outnumber positional ones. Boxing both makes the element
/// 16 bytes, pays exactly one allocation per rule at lowering time, and leaves no variant
/// subsidising the other.
#[derive(Debug, Clone)]
pub(crate) enum DriveArm {
    /// A positional/subst σ-ABI arm (A-S5.2) — fires `accept!(σ…, r)` through the
    /// EXISTING installed σ-receiver.
    Positional(Box<DriveRedexArm>),
    /// An AC carrier-ABI arm (A-S5.5) — fires `⌜^drive-ac:R⌝!(t, r)` through the
    /// fixed-channel persistent AC-carrier receiver.
    AcCarrier(Box<DriveAcArm>),
}

/// The unified RHS/operand description one AC carrier receiver is built from — the
/// structural (`OpenRule`) and nested (`InRule`/`OutRule`) shapes projected onto ONE
/// surface so [`ac_carrier_receiver_par`] has a single builder:
///
/// * a [`crate::rho_net_lower::NestedStructuralAcShape`] maps verbatim (its
///   `reduct_templates` are already [`AcReconstructTemplate`]s);
/// * a [`crate::rho_net_lower::StructuralAcShape`] (flat, `OpenRule`) maps with
///   `root_pattern = LHS`, `reduct_templates = reduct_vars.map(Var)`, and
///   `rest_splices_at_top = true` (its RHS is always `op{ r₀, …, ...rest }`).
pub(crate) struct AcCarrierSpec {
    /// The HashBag operand/reduct bag constructor (e.g. `PPar`).
    op: String,
    /// The LHS root pattern (bag-rooted or wrapper-rooted) — both the carrier's bind
    /// pattern and the arm's check pattern walk it.
    root_pattern: Pattern,
    /// The cross-level / shared non-linear channel variable.
    nonlinear_var: Ident,
    /// The outer bag's `...rest` remainder variable.
    spliced_rest: Ident,
    /// The RHS reduct element templates, in RHS order.
    reduct_templates: Vec<AcReconstructTemplate>,
    /// Where the outer rest is consumed (A-S5.4b AM-1 exactly-once): `true` ⟹ spliced at
    /// the top of the RHS bag; `false` ⟹ referenced exactly once inside a template (the
    /// redeclared `OutRule`).
    rest_splices_at_top: bool,
}

/// The reserved per-rule AC carrier tag label `"^drive-ac:{rule_label}"` (module docs:
/// the `^` prefix keeps the whole suffixed family collision-free with user constructors).
pub(crate) fn drive_ac_carrier_label(rule_label: &str) -> String {
    format!("{DRIVE_AC_RESERVED_LABEL}:{rule_label}")
}

/// Recognize one fireable collection-LHS rewrite as an AC carrier spec (A-S5.5): the
/// NESTED shape first (the depth-2 `InRule`/`OutRule` recognizer — it rejects flat
/// shapes), then the FLAT structural shape (`OpenRule`), each REQUIRING
/// match-representability (a shape the carrier cannot faithfully bind stays
/// driver-unsupported — never a wrong in-Rho arm). `Err` carries the fail-closed reason
/// surfaced by [`DriveAdmission::Unsupported`].
fn ac_carrier_spec(rewrite: &RewriteRule, def: &LanguageDef) -> Result<AcCarrierSpec, String> {
    if let Some(shape) = nested_structural_ac_rule_shape(&rewrite.left, &rewrite.right, def) {
        if !nested_structural_ac_shape_is_match_representable(&shape) {
            return Err(format!(
                "nested structural-AC rewrite {} is not match-representable (a reduct \
                 variable has no single unambiguous bind position)",
                rewrite.name
            ));
        }
        return Ok(AcCarrierSpec {
            op: shape.op,
            root_pattern: shape.root_pattern,
            nonlinear_var: shape.nonlinear_var,
            spliced_rest: shape.spliced_rest,
            reduct_templates: shape.reduct_templates,
            rest_splices_at_top: shape.rest_splices_at_top,
        });
    }
    let resolved_kind = resolve_ac_collection_type(def, &rewrite.left);
    if let Some(shape) =
        structural_ac_rule_shape(&rewrite.left, &rewrite.right, resolved_kind.as_ref())
    {
        if !structural_ac_shape_is_match_representable(&shape) {
            return Err(format!(
                "structural-AC rewrite {} is not match-representable (a reduct variable \
                 occurs at multiple element-argument positions)",
                rewrite.name
            ));
        }
        return Ok(AcCarrierSpec {
            op: shape.op.clone(),
            root_pattern: rewrite.left.clone(),
            nonlinear_var: shape.nonlinear_var.clone(),
            spliced_rest: shape.rest.clone(),
            reduct_templates: shape
                .reduct_vars
                .iter()
                .map(|var| AcReconstructTemplate::Var(var.to_string()))
                .collect(),
            rest_splices_at_top: true,
        });
    }
    Err("a collection (AC) LHS that is neither a nested structural-AC nor a flat \
         structural-AC shape has no driver carrier arm (linear-AC / Comm families are \
         not driver-supported)"
        .to_string())
}

/// Build one AC carrier-ABI redex arm (check pattern + guard + carrier receiver) from a
/// fireable collection-LHS rewrite — the single derivation shared by
/// [`drive_admissible`]'s conjunct-3 validation and [`drive_lowering`]'s arm
/// materialization (a PURE function of `(rewrite, def, fingerprint)`, so the two can
/// never drift).
fn build_drive_ac_arm(
    rewrite: &RewriteRule,
    def: &LanguageDef,
    fingerprint: &str,
) -> Result<DriveAcArm, String> {
    let spec = ac_carrier_spec(rewrite, def)?;

    // The arm's CHECK pattern: the report-path operand walk (guard slot per non-linear
    // occurrence, the bound outer rest, wildcards elsewhere) transcribed into Match-case
    // position over the driven value.
    let guard_occurrences = count_var_occurrences(&spec.root_pattern, &spec.nonlinear_var);
    if guard_occurrences < 2 {
        return Err(format!(
            "rewrite {}: the non-linear channel variable {} occurs {guard_occurrences} \
             time(s) — an AC arm needs the cross-level pair for its guard",
            rewrite.name, spec.nonlinear_var
        ));
    }
    let spliced_rest_slot = guard_occurrences;
    let mut next_guard_slot = 0usize;
    let mut occurrence_levels = Vec::with_capacity(guard_occurrences);
    let pattern = nested_match_pattern_for(
        &spec.root_pattern,
        &spec.nonlinear_var,
        &spec.spliced_rest,
        spliced_rest_slot,
        &mut next_guard_slot,
        &mut occurrence_levels,
        fingerprint,
    );
    debug_assert_eq!(
        next_guard_slot, guard_occurrences,
        "the check-pattern walk binds exactly one guard slot per non-linear occurrence"
    );
    let free_count = guard_occurrences + 1;
    let guard = nonlinear_consistency_condition(&occurrence_levels, free_count);
    let case_names: Vec<String> = (0..free_count).map(|i| format!("__ac{i}")).collect();

    let receiver = ac_carrier_receiver_par(&spec, rewrite, fingerprint)?;

    Ok(DriveAcArm {
        rule_label: rewrite.name.to_string(),
        carrier_label: drive_ac_carrier_label(&rewrite.name.to_string()),
        pattern,
        free_count,
        guard,
        case_names,
        receiver,
    })
}

/// The `Match`-case pattern claiming a SAME-`op` process soup — one send-pattern on the
/// `"ac:{op}"` GString carrier plus a WILDCARD remainder (`{@"ac:op"!(_) | _}`): matches
/// any Par with ≥ 1 element send on the op's carrier (an empty bag — Nil — does NOT
/// match, which is exactly why the AM-3 dispatch is THREE-case).
///
/// `pub(crate)`: shared with the A-S5.8 `^float` family (`crate::rho_net_float`), whose
/// merge base case rides the SAME three-case dispatch.
pub(crate) fn soup_case_pattern(language_fingerprint: &str, op: &str) -> Par {
    let send_pattern = new_send_par(
        new_gstring_par(ac_soup_channel(language_fingerprint, op), Vec::new(), false),
        vec![pat_wildcard()],
        false,
        Vec::new(),
        true,
        Vec::new(),
        true,
    );
    send_pattern.append(pat_wildcard())
}

/// The `Match`-case pattern claiming a soup while PEELING one element: one send-pattern
/// binding the element datum (`FreeVar(0)`) plus the free-Par remainder (`FreeVar(1)`) —
/// the bag arm's `{@"ac:op"!(e) | rem}` (the delta-verified spatial-matcher Par-Par
/// send-pattern + free-remainder shape).
///
/// `pub(crate)`: shared with the A-S5.8 `^float` dispatcher's soup-peel arm
/// (`crate::rho_net_float`) and the A-S5.8 `^shift` soup arm
/// (`crate::rho_net_subst_trs::shift_receiver_par` — F8-AM-5d/5e).
pub(crate) fn soup_peel_pattern(language_fingerprint: &str, op: &str) -> Par {
    let send_pattern = new_send_par(
        new_gstring_par(ac_soup_channel(language_fingerprint, op), Vec::new(), false),
        vec![pat_free(0)],
        false,
        Vec::new(),
        true,
        Vec::new(),
        true,
    );
    send_pattern.append(pat_free(1))
}

/// The VALUE `@"ac:{op}"!(element)` — one wrapped bag-element send, used as (part of) a
/// send DATUM (the WRAP leg of the three-case dispatch and the rebuild of a
/// statically-non-bag template element).
///
/// `pub(crate)`: shared with the A-S5.8 `^float` family and the `^shift` soup arm's
/// rewrap (`crate::rho_net_float` / `crate::rho_net_subst_trs` — F8-AM-5d/5e).
pub(crate) fn wrap_element_send(language_fingerprint: &str, op: &str, element: Node) -> Node {
    send(
        ground(new_gstring_par(ac_soup_channel(language_fingerprint, op), Vec::new(), false)),
        vec![element],
    )
}

/// Emit the AM-3 THREE-CASE bag-fragment dispatch for one σ-slot / driven value `value`
/// (plan v2 §4.3.3 as amended by AM-3(a)): deliver `value`'s contribution to a same-`op`
/// soup as a Par FRAGMENT on the fresh channel `dest` —
///
/// ```text
/// match value { Nil                => dest!(Nil)              -- splice-as-nothing
///             ; {@"ac:op"!(_) | _} => dest!(value)            -- same-op soup: compose its sends (splice)
///             ; _                  => dest!(@"ac:op"!(value)) -- wrap one element send
/// }
/// ```
///
/// Composing the delivered fragment in parallel with the other fragments/remainder IS the
/// splice (Par-valued substitution splices sends); the Nil case exists so an empty bag
/// contributes NOTHING (the wrap leg would otherwise manufacture a spurious
/// `@"ac:op"!(Nil)` element — AM-3's exact defect). The dispatch is ONE level deep by
/// design: deeper never-driven nesting flattens through the contractum's own re-drive
/// (the AM-3(b) drive induction, module docs).
///
/// `pub(crate)`: shared with the A-S5.8 `^float-merge:{op}` satellite's base case
/// (`crate::rho_net_float` — the AM-2/AM-3 splice INSIDE the float).
pub(crate) fn bag_fragment_dispatch(
    language_fingerprint: &str,
    op: &str,
    value: Node,
    dest: Node,
) -> Node {
    match_(
        value.clone(),
        vec![
            // Nil ⟹ the empty-bag fragment (contributes nothing when composed).
            Case {
                pattern: Par::default(),
                free_count: 0,
                body: send(dest.clone(), vec![ground(Par::default())]),
            },
            // A same-op soup ⟹ the value ITSELF is the fragment (its sends splice).
            Case {
                pattern: soup_case_pattern(language_fingerprint, op),
                free_count: 0,
                body: send(dest.clone(), vec![value.clone()]),
            },
            // Anything else ⟹ one wrapped element send.
            Case {
                pattern: pat_wildcard(),
                free_count: 0,
                body: send(dest, vec![wrap_element_send(language_fingerprint, op, value)]),
            },
        ],
    )
}

/// Collect (first-appearance order, deduplicated) every template VARIABLE sitting at a
/// bag-ELEMENT position, WITH its enclosing template-binder depth (A-S5.8) — the σ slots
/// whose (depth-shifted) values need the [`bag_fragment_dispatch`] (they may be bags/Nil
/// at runtime). A `Var` at a NODE-child position (a name argument) and a `Bag`'s `...rest`
/// remainder need no dispatch (the rest slot is always a soup/Nil, composed directly); a
/// `Node` element is statically non-bag (wrapped unconditionally); a `Binder` element is
/// the statically-non-bag `^lambda` node (wrapped), its BODY recursing one binder deeper
/// (F8-AM-1c).
fn collect_bag_element_vars(
    template: &AcReconstructTemplate,
    at_bag_element: bool,
    depth: usize,
    out: &mut Vec<(String, usize)>,
) {
    match template {
        AcReconstructTemplate::Var(name) => {
            if at_bag_element && !out.iter().any(|(n, d)| n == name && *d == depth) {
                out.push((name.clone(), depth));
            }
        },
        AcReconstructTemplate::Node { children, .. } => {
            for child in children {
                collect_bag_element_vars(child, false, depth, out);
            }
        },
        AcReconstructTemplate::Bag { elements, .. } => {
            for element in elements {
                collect_bag_element_vars(element, true, depth, out);
            }
        },
        AcReconstructTemplate::Binder { body } => {
            collect_bag_element_vars(body, false, depth + 1, out);
        },
    }
}

/// Collect (first-appearance order, deduplicated) every `(σ-slot name, binder depth ≥ 1)`
/// pair a template references UNDER a [`AcReconstructTemplate::Binder`] — the F8-AM-1c
/// σ-slot shift requirements: each pair's matched value is pre-shifted by `depth` composed
/// `^shift(Z, ·)` applications on a fresh channel BEFORE the carrier's rebuild composes it
/// (never by shifting a composed body — that would corrupt template-introduced de Bruijn
/// coordinates — and never depth-plus-per-level, a double shift). Bag `...rest` slots
/// count too (shifting a bag = shifting its elements at an unchanged cutoff — the A-S5.8
/// `^shift` soup arm, F8-AM-5e).
fn collect_shift_requirements(
    template: &AcReconstructTemplate,
    depth: usize,
    out: &mut Vec<(String, usize)>,
) {
    fn push(name: &str, depth: usize, out: &mut Vec<(String, usize)>) {
        if depth >= 1 && !out.iter().any(|(n, d)| n == name && *d == depth) {
            out.push((name.to_string(), depth));
        }
    }
    match template {
        AcReconstructTemplate::Var(name) => push(name, depth, out),
        AcReconstructTemplate::Node { children, .. } => {
            for child in children {
                collect_shift_requirements(child, depth, out);
            }
        },
        AcReconstructTemplate::Bag { elements, rest, .. } => {
            for element in elements {
                collect_shift_requirements(element, depth, out);
            }
            if let Some(rest) = rest {
                push(rest, depth, out);
            }
        },
        AcReconstructTemplate::Binder { body } => {
            collect_shift_requirements(body, depth + 1, out);
        },
    }
}

/// The carrier frame name holding a σ slot's DEPTH-SHIFTED value (A-S5.8, F8-AM-1c):
/// depth 0 is the raw receive-frame slot itself; depth `k ≥ 1` is the `k`-fold-shifted
/// value bound by the shift pre-stage's join.
fn slot_value_name(slot: &str, depth: usize) -> String {
    if depth == 0 {
        slot.to_string()
    } else {
        format!("__sh{depth}_{slot}")
    }
}

/// Emit the `k`-fold `^shift(Z, ·)` chain for one σ slot (A-S5.8, F8-AM-1c): shift the
/// value named `value_name` `k ≥ 1` times at cutoff `Z`, resting the result on the channel
/// named `dest_name`. `k` composed applications — the exact F8-AM-1c form (each
/// application increments every `^bound(n)` with `n ≥ 0` by one).
fn chained_shift_node(
    fingerprint: &str,
    env: &Env,
    value_name: &str,
    dest_name: &str,
    k: usize,
) -> Node {
    debug_assert!(k >= 1, "a shift chain has at least one application");
    let zero = || ground(nullary_term(fingerprint, crate::rho_net_lower::PEANO_ZERO_REFLECT_LABEL));
    if k == 1 {
        return send(
            ground(tag_par(fingerprint, crate::rho_net_lower::SHIFT_RESERVED_LABEL)),
            vec![zero(), env.var(value_name), env.var(dest_name)],
        );
    }
    new_scope(1, {
        let env = env.push(&["__t"]);
        let first = send(
            ground(tag_par(fingerprint, crate::rho_net_lower::SHIFT_RESERVED_LABEL)),
            vec![zero(), env.var(value_name), env.var("__t")],
        );
        let rest = for1(env.var("__t"), {
            let env = env.push(&["__w"]);
            chained_shift_node(fingerprint, &env, "__w", dest_name, k - 1)
        });
        par2(first, rest)
    })
}

/// Rebuild one reduct template as a receiver-body [`Node`] over the carrier's bound σ
/// slots (the [`Env`]-combinator twin of
/// `rho_net_lower::reflect_ac_template_bound_par`, with the F4/AM-3 difference at
/// bag-element positions):
///
/// * `Var(v)` at a NODE-child position ⟹ the slot's DEPTH-shifted value
///   (`env.var(slot_value_name(v, depth))` — the raw slot at depth 0, the pre-shifted
///   `__sh{k}_{v}` under `k` template binders, F8-AM-1c);
/// * `Node { C, children }` ⟹ the tagged `EList[⌜C⌝, …]` (byte-compatible with
///   `reflect_ground_term_par`'s constructor image);
/// * `Binder { body }` (A-S5.8) ⟹ the ctor-erased `EList[⌜^lambda⌝, ⟦body⟧]` with the body
///   rebuilt one binder DEEPER (its σ slots resolve to their `depth + 1` shifted values);
/// * `Bag { op, elements, rest }` ⟹ the process soup: each element emitted per its
///   STATIC kind — a `Var` composes its PRE-COMPUTED three-case FRAGMENT
///   (`env.var(__frag…)` — the splice), a `Node`/`Binder` wraps unconditionally
///   (statically non-bag), a same-`op` inner `Bag` composes its rebuilt soup directly (a
///   static splice — the AM-2 `insert_into` mirror), a different-op inner `Bag` wraps its
///   soup as one element — plus the `...rest` slot composed directly (always a soup/Nil;
///   depth-shifted like every σ slot).
fn rebuild_template_node(
    template: &AcReconstructTemplate,
    env: &Env,
    fingerprint: &str,
    depth: usize,
) -> Node {
    match template {
        AcReconstructTemplate::Var(name) => env.var(&slot_value_name(name, depth)),
        AcReconstructTemplate::Node { constructor, children } => tagged(
            fingerprint,
            constructor,
            children
                .iter()
                .map(|child| rebuild_template_node(child, env, fingerprint, depth))
                .collect(),
        ),
        AcReconstructTemplate::Binder { body } => tagged(
            fingerprint,
            LAMBDA_REFLECT_LABEL,
            vec![rebuild_template_node(body, env, fingerprint, depth + 1)],
        ),
        AcReconstructTemplate::Bag { op, elements, rest } => {
            let mut soup: Option<Node> = None;
            let push = |node: Node, soup: &mut Option<Node>| {
                *soup = Some(match soup.take() {
                    None => node,
                    Some(acc) => par2(acc, node),
                });
            };
            for element in elements {
                let node = match element {
                    // A σ-slot element: its THREE-CASE fragment was pre-computed onto
                    // `__frag…` (see [`ac_carrier_receiver_par`]) — composing it IS
                    // the one-level splice.
                    AcReconstructTemplate::Var(name) => env.var(&fragment_value_name(name, depth)),
                    // A constructor / binder element is statically non-bag ⟹ wrap.
                    AcReconstructTemplate::Node { .. } | AcReconstructTemplate::Binder { .. } => {
                        wrap_element_send(
                            fingerprint,
                            op,
                            rebuild_template_node(element, env, fingerprint, depth),
                        )
                    },
                    // An inner literal bag: same-op ⟹ static splice; different-op ⟹ its
                    // soup wrapped as one element.
                    AcReconstructTemplate::Bag { op: inner_op, .. } => {
                        let rebuilt = rebuild_template_node(element, env, fingerprint, depth);
                        if inner_op == op {
                            rebuilt
                        } else {
                            wrap_element_send(fingerprint, op, rebuilt)
                        }
                    },
                };
                push(node, &mut soup);
            }
            if let Some(rest_name) = rest {
                push(env.var(&slot_value_name(rest_name, depth)), &mut soup);
            }
            soup.unwrap_or_else(|| ground(Par::default()))
        },
    }
}

/// The synthetic frame name carrying a σ slot's pre-computed three-case FRAGMENT value at
/// one template-binder depth: `__frag_{slot}` at depth 0 (BYTE-STABLE with the A-S5.5
/// emission — the production Ambient carriers are binder-free) and `__frag{k}_{slot}`
/// under `k` template binders (A-S5.8, reachable only with a `Binder` template).
fn fragment_value_name(slot: &str, depth: usize) -> String {
    if depth == 0 {
        format!("__frag_{slot}")
    } else {
        format!("__frag{depth}_{slot}")
    }
}

/// Build the FIXED-CHANNEL persistent AC-CARRIER receiver for one admitted AC rule
/// (A-S5.5, plan v2 §4.3.1 — module docs "The AC carrier ABI"):
///
/// ```text
/// for( <operand bind pattern>, out <- ⌜^drive-ac:R⌝ )
///   where ( Mₐ == M_b )
///   { new f₀…f_{q-1} in {
///       <three-case dispatch: σ[v₀] → f₀> | … |
///       for(@__frag_v₀ <- f₀ & …){ out!( ⟦RHS bag⟧ ) } } }
/// ```
///
/// The operand bind pattern + non-linear `Receive.condition` are the SAME derivation as
/// the site-keyed `ac:` match receivers
/// ([`crate::rho_net_lower::nested_match_bind_pattern_for`] over the reduct-referenced
/// slot set — the carrier re-binds EVERYTHING from the delivered operand, no host σ);
/// the source channel is the reserved per-rule carrier; and the body emits each
/// σ-slot reduct element through the AM-3 three-case fragment dispatch before composing
/// the RHS bag (the F4 "contractum entry" splice). Fail-closed (`Err`) on a slot-name
/// collision with the carrier's own frame names (`out` / `__frag_*` / `__g*` / `__f*`).
fn ac_carrier_receiver_par(
    spec: &AcCarrierSpec,
    rewrite: &RewriteRule,
    fingerprint: &str,
) -> Result<Par, String> {
    // The reduct-referenced slot set (+ the outer spliced rest), mirroring the site-keyed
    // receiver's derivation.
    let mut referenced: HashSet<String> = HashSet::new();
    for template in &spec.reduct_templates {
        template.collect_vars(&mut referenced);
    }
    referenced.insert(spec.spliced_rest.to_string());

    // Fail-closed frame-name hygiene: a user σ variable named like the carrier's own
    // frame names would shadow-resolve inside the body.
    for name in &referenced {
        if name == "out" || name.starts_with("__") {
            return Err(format!(
                "rewrite {}: σ variable {name:?} collides with the AC carrier frame \
                 (`out` / `__*` are reserved)",
                rewrite.name
            ));
        }
    }

    let mut state = NestedBindState {
        next_level: 0,
        slot_of: HashMap::new(),
        occurrence_levels: Vec::new(),
    };
    let bind_pattern = nested_match_bind_pattern_for(
        &spec.root_pattern,
        &spec.nonlinear_var,
        &referenced,
        &mut state,
        fingerprint,
    );
    let out_level = state.next_level;
    let free_count = out_level + 1;
    let condition = nonlinear_consistency_condition(&state.occurrence_levels, free_count);

    // The receive frame names, by slot level: named σ slots from the bind walk, synthetic
    // `__g{level}` for the unnamed extra guard occurrences (the non-linear var's
    // occurrences beyond its first), `out` last.
    let mut names: Vec<String> = (0..out_level).map(|level| format!("__g{level}")).collect();
    for (name, level) in &state.slot_of {
        names[*level] = name.clone();
    }
    names.push("out".to_string());
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let env = Env::root(&name_refs);

    // The σ slots needing the three-case fragment dispatch: every template Var at a
    // bag-element position, WITH its template-binder depth (first-appearance order — the
    // emission order of the dispatches and join binds).
    let mut fragment_slots: Vec<(String, usize)> = Vec::new();
    for template in &spec.reduct_templates {
        collect_bag_element_vars(template, true, 0, &mut fragment_slots);
    }
    // A-S5.8 (F8-AM-1c): the σ slots referenced UNDER template binders — each `(name, k)`
    // pair's value is pre-shifted by `k` composed `^shift(Z, ·)` applications on a fresh
    // channel (stage A) before the fragment dispatches / rebuild compose it. Empty for
    // every binder-free rule (the whole production Ambient corpus), so the A-S5.5 carrier
    // emission is BYTE-IDENTICAL there.
    let mut shift_requirements: Vec<(String, usize)> = Vec::new();
    for template in &spec.reduct_templates {
        collect_shift_requirements(template, 0, &mut shift_requirements);
    }

    // The RHS top-level bag emission, built in a frame where every fragment value is
    // bound as `__frag…` (or the root frame when no dispatch is needed).
    let top_soup = |env: &Env| -> Node {
        let mut soup: Option<Node> = None;
        let push = |node: Node, soup: &mut Option<Node>| {
            *soup = Some(match soup.take() {
                None => node,
                Some(acc) => par2(acc, node),
            });
        };
        for template in &spec.reduct_templates {
            let node = match template {
                AcReconstructTemplate::Var(name) => env.var(&fragment_value_name(name, 0)),
                AcReconstructTemplate::Node { .. } | AcReconstructTemplate::Binder { .. } => {
                    wrap_element_send(
                        fingerprint,
                        &spec.op,
                        rebuild_template_node(template, env, fingerprint, 0),
                    )
                },
                AcReconstructTemplate::Bag { op: inner_op, .. } => {
                    let rebuilt = rebuild_template_node(template, env, fingerprint, 0);
                    if *inner_op == spec.op {
                        rebuilt
                    } else {
                        wrap_element_send(fingerprint, &spec.op, rebuilt)
                    }
                },
            };
            push(node, &mut soup);
        }
        if spec.rest_splices_at_top {
            push(env.var(&spec.spliced_rest.to_string()), &mut soup);
        }
        soup.unwrap_or_else(|| ground(Par::default()))
    };

    // Stage B: the fragment dispatches + the atomic fragment join + the single
    // out-emission of the RHS bag — built in a frame where every SHIFTED slot value
    // (stage A) is already bound.
    let stage_b = |env: &Env| -> Node {
        if fragment_slots.is_empty() {
            // No σ-slot bag-element positions (impossible for the bundled Ambient rules,
            // kept total): emit the RHS bag directly.
            return send(env.var("out"), vec![top_soup(env)]);
        }
        let q = fragment_slots.len();
        new_scope(q, {
            let dispatch_names: Vec<String> = (0..q).map(|i| format!("__f{i}")).collect();
            let dispatch_refs: Vec<&str> = dispatch_names.iter().map(String::as_str).collect();
            let env = env.push(&dispatch_refs);
            // One three-case dispatch per fragment slot, concurrent — the dispatched
            // value is the slot's DEPTH-shifted value (raw at depth 0).
            let mut composed: Option<Node> = None;
            for (i, (slot, depth)) in fragment_slots.iter().enumerate() {
                let dispatch = bag_fragment_dispatch(
                    fingerprint,
                    &spec.op,
                    env.var(&slot_value_name(slot, *depth)),
                    env.var(&dispatch_names[i]),
                );
                composed = Some(match composed {
                    None => dispatch,
                    Some(acc) => par2(acc, dispatch),
                });
            }
            // The atomic fragment join, then the single out-emission of the RHS bag.
            let join_sources: Vec<Node> = dispatch_names.iter().map(|f| env.var(f)).collect();
            let join_node = join(join_sources, {
                let frag_names: Vec<String> = fragment_slots
                    .iter()
                    .map(|(slot, depth)| fragment_value_name(slot, *depth))
                    .collect();
                let frag_refs: Vec<&str> = frag_names.iter().map(String::as_str).collect();
                let env = env.push(&frag_refs);
                send(env.var("out"), vec![top_soup(&env)])
            });
            par2(composed.expect("q ≥ 1"), join_node)
        })
    };

    let body = if shift_requirements.is_empty() {
        stage_b(&env)
    } else {
        // Stage A (A-S5.8, F8-AM-1c): one fresh channel + one `k`-fold `^shift(Z, ·)`
        // chain per `(slot, depth)` requirement, concurrent; the atomic join binds each
        // shifted value as `__sh{k}_{slot}`, and stage B runs in that frame.
        let p = shift_requirements.len();
        new_scope(p, {
            let shift_chan_names: Vec<String> = (0..p).map(|i| format!("__fs{i}")).collect();
            let shift_chan_refs: Vec<&str> = shift_chan_names.iter().map(String::as_str).collect();
            let env = env.push(&shift_chan_refs);
            let mut composed: Option<Node> = None;
            for (i, (slot, depth)) in shift_requirements.iter().enumerate() {
                let chain =
                    chained_shift_node(fingerprint, &env, slot, &shift_chan_names[i], *depth);
                composed = Some(match composed {
                    None => chain,
                    Some(acc) => par2(acc, chain),
                });
            }
            let join_sources: Vec<Node> = shift_chan_names.iter().map(|c| env.var(c)).collect();
            let join_node = join(join_sources, {
                let shifted_names: Vec<String> = shift_requirements
                    .iter()
                    .map(|(slot, depth)| slot_value_name(slot, *depth))
                    .collect();
                let shifted_refs: Vec<&str> = shifted_names.iter().map(String::as_str).collect();
                let env = env.push(&shifted_refs);
                stage_b(&env)
            });
            par2(composed.expect("p ≥ 1"), join_node)
        })
    };

    // The receiver: [operand bind pattern, FreeVar(out)] over the reserved per-rule
    // carrier channel, the non-linear condition, persistent — the 2-value message
    // `⌜^drive-ac:R⌝!(⟦operand⟧, r)` the driver's AC arm sends.
    let carrier_channel = tag_par(fingerprint, &drive_ac_carrier_label(&rewrite.name.to_string()));
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: vec![bind_pattern, new_freevar_par(out_level as i32, Vec::new())],
            source: Some(carrier_channel),
            remainder: None,
            free_count: free_count as i32,
        }],
        body: Some(body.par),
        persistent: true,
        peek: false,
        bind_count: free_count as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition: Some(condition),
    };
    Ok(Par::default().with_receives(vec![receive]))
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
    /// The redex-check for one compiled AC carrier-ABI arm (A-S5.5): for PS the
    /// transcribed operand check pattern + the non-linear conjunction as the per-case
    /// `MatchCase.guard` (F12). Provided (PS-shaped) because the check data live on the
    /// arm; a future PM carrier overrides with its guard-expression + σ-extraction plan.
    fn ac_redex_check(&self, arm: &DriveAcArm) -> DriveCheck {
        DriveCheck {
            pattern: arm.pattern.clone(),
            free_count: arm.free_count,
            guard: Some(arm.guard.clone()),
        }
    }
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
    /// `^drive`). THE SEAM: constructed ONLY by a scion-selected arm
    /// ([`fuel_gated_firing`], gated on `arm.scion`); production lowers under `AllRedrive`
    /// (`arm.scion == false`), so `ContractumRedrive` is the path every emitted byte takes
    /// today. Contract a bundle must
    /// satisfy: (a) compiled against the firing frame the emitter builds (`r` =
    /// `BoundVar(0)` inside the `new r` scope, `fuel`/`ret` at the enclosing arm frame);
    /// (b) the SM-7 seam invariant — for every schedule, the value ultimately reaching
    /// `ret` is a member of `NF_drive(contractum)`, the set of values some `^drive` trace
    /// rests at from the contractum at the arm's post-firing fuel. On confluent (or
    /// root-stable orthogonal) fragments this set is a singleton and the clause
    /// degenerates to `norm(contractum)`. Fired-multiset and exhaustion observations are
    /// per-trace, compared under the decision-(3)/AM-5 regime: strict equality on
    /// confluent cells; valid-NF-set membership + ledger consistency on non-confluent
    /// cells. The acceptance surface of §5.2 binds it.
    ScionBundle {
        /// The precompiled emission `Par`, BOXED: a `Par` is 248 bytes and the variant that
        /// production actually takes (`ContractumRedrive`) carries none of it, so the
        /// unboxed field widened every `FiringEmission` local to 248 bytes to serve the
        /// arm-gated E-1 path. Both consumers ([`firing_emission_node`] and its carrier-ABI
        /// twin) already clone the `Par` out, so the indirection costs them nothing.
        bundle: Box<Par>,
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
///
/// A-S5.8 (decision Q-AB = A, always-float): for a FLOAT-BEARING language
/// (`route_through_float`, [`crate::rho_net_float::language_is_float_bearing`]) the
/// `ContractumRedrive` emission routes the contractum through the installed `^float`
/// dispatcher BEFORE the re-drive — `for(@c <- r){ new rf { ⌜^float⌝!(c, rf) |
/// for(@cf <- rf){ ⌜^drive⌝!(cf, fuel - 1, ret) } } }` — establishing the uniform
/// invariant "every `^drive` subject is float-canonical" per firing. Float COMMs consume
/// NO drive fuel (a `≡` canonicalization, not a `→` step) and the family carries no fuel
/// of its own (termination is structural). A non-float language's emission is
/// BYTE-IDENTICAL to pre-A-S5.8 (the Lambda no-regression pin).
#[allow(clippy::too_many_arguments)]
pub(crate) fn firing_emission_node(
    arm: &DriveRedexArm,
    emission: &FiringEmission,
    fingerprint: &str,
    env: &Env,
    fuel_var: &str,
    ret_var: &str,
    carrier: &dyn DriveCarrier,
    route_through_float: bool,
) -> Node {
    // The firing ledger `@"^fired:{fp}"!("RuleLabel")` — all-ground (no frame references),
    // so it is byte-identical whether assembled inside the `new r` scope (ContractumRedrive)
    // or in the arm frame (ScionBundle).
    let ledger = || {
        send(
            ground(new_gstring_par(drive_fired_channel(fingerprint), Vec::new(), false)),
            vec![ground(new_gstring_par(arm.rule_label.clone(), Vec::new(), false))],
        )
    };
    match emission {
        // Byte-identical to pre-E-1: `new r { accept!(σ…, r) | @^fired!(label) | redrive-for }`.
        FiringEmission::ContractumRedrive => new_scope(1, {
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
            let emission_node = for1(env.var("r"), {
                let env = env.push(&["c"]);
                contractum_redrive_node(
                    fingerprint,
                    &env,
                    fuel_var,
                    ret_var,
                    carrier,
                    route_through_float,
                )
            });
            par2(par2(accept, ledger()), emission_node)
        }),
        // E-1 §3.3 (accept-bypass): the precompiled scion bundle owns its own fresh scopes and
        // reassembles the contractum directly from the frame σ captures — NO `new r`, NO accept
        // round-trip (a retained accept would leak 1 COMM + 1 resting produce per firing, SM-11).
        // The bundle references σ / `fuel` / `ret` at the arm-frame depth; [`node_from_par`]
        // recovers its free-set from `locally_free` (a plain `ground` would zero it, corrupting
        // the enclosing `Match`-case COMM). The `^fired:` ledger is RETAINED — it is the
        // treatment arm's ONLY firing observable (`fired_labels()`, SM-3).
        FiringEmission::ScionBundle { bundle } => {
            par2(ledger(), node_from_par(bundle.as_ref().clone()))
        },
    }
}

/// The shared contractum RE-ENTRY node of both firing emitters, built in the frame where
/// `c` names the delivered contractum: the direct re-drive `⌜^drive⌝!(c, fuel - 1, ret)`
/// (non-float languages, byte-identical to pre-A-S5.8), or the A-S5.8 float-routed form
/// `new rf { ⌜^float⌝!(c, rf) | for(@cf <- rf){ ⌜^drive⌝!(cf, fuel - 1, ret) } }`
/// (name-late [`Env`] discipline — `fuel_var`/`ret_var` resolve inside the nested scopes).
fn contractum_redrive_node(
    fingerprint: &str,
    env: &Env,
    fuel_var: &str,
    ret_var: &str,
    carrier: &dyn DriveCarrier,
    route_through_float: bool,
) -> Node {
    if !route_through_float {
        return send(
            ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
            vec![
                carrier.contractum_payload(env, env.var("c")),
                eminus(env.var(fuel_var), gint(1)),
                env.var(ret_var),
            ],
        );
    }
    new_scope(1, {
        let env = env.push(&["rf"]);
        let float_call = send(
            ground(tag_par(fingerprint, crate::rho_net_lower::FLOAT_RESERVED_LABEL)),
            vec![carrier.contractum_payload(&env, env.var("c")), env.var("rf")],
        );
        let redrive = for1(env.var("rf"), {
            let env = env.push(&["cf"]);
            send(
                ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
                vec![env.var("cf"), eminus(env.var(fuel_var), gint(1)), env.var(ret_var)],
            )
        });
        par2(float_call, redrive)
    })
}

/// Emit ONE fired AC CARRIER-ABI arm's firing body (A-S5.5, plan v2 §4.3.1) — the
/// carrier-ABI twin of [`firing_emission_node`], covered by the SAME [`FiringEmission`]
/// seam (an E-1 `ScionBundle` swaps in per (entry, rule) here too, under the SM-7
/// invariant on the enum):
///
/// ```text
/// new r in { ⌜^drive-ac:R⌝!(subject, r) | @"^fired:{fp}"!("RuleLabel") | <emission> }
/// ```
///
/// The delivered operand is the WHOLE matched subject ([`drive_subject_node`] — the
/// driver's own `Match` + guard already decided the redex, so the carrier's re-match is
/// redundancy, not risk); the fixed-channel persistent AC-carrier receiver re-binds every
/// σ slot from it and emits the three-case-spliced contractum to the fresh `r`, which the
/// `ContractumRedrive` emission re-drives with `fuel - 1`.
#[allow(clippy::too_many_arguments)]
fn ac_firing_emission_node(
    arm: &DriveAcArm,
    emission: &FiringEmission,
    fingerprint: &str,
    env: &Env,
    fuel_var: &str,
    ret_var: &str,
    carrier: &dyn DriveCarrier,
    subject: &DriveSubject<'_>,
    route_through_float: bool,
) -> Node {
    // Byte-identical whether inside the `new r` scope or the arm frame (all-ground).
    let ledger = || {
        send(
            ground(new_gstring_par(drive_fired_channel(fingerprint), Vec::new(), false)),
            vec![ground(new_gstring_par(arm.rule_label.clone(), Vec::new(), false))],
        )
    };
    match emission {
        // Byte-identical to pre-E-1: `new r { ⌜^drive-ac:R⌝!(subject, r) | @^fired!(label) |
        // redrive-for }`.
        FiringEmission::ContractumRedrive => new_scope(1, {
            let env = env.push(&["r"]);
            // Deliver the whole subject operand + the fresh return through the carrier ABI.
            let operand = drive_subject_node(subject, &env, carrier);
            let carrier_send =
                send(ground(tag_par(fingerprint, &arm.carrier_label)), vec![operand, env.var("r")]);
            let emission_node = for1(env.var("r"), {
                let env = env.push(&["c"]);
                contractum_redrive_node(
                    fingerprint,
                    &env,
                    fuel_var,
                    ret_var,
                    carrier,
                    route_through_float,
                )
            });
            par2(par2(carrier_send, ledger()), emission_node)
        }),
        // E-1 §3.3 (accept-bypass): the scion bundle owns its own scopes and reassembles the
        // contractum from the frame slots directly — NO `new r`, NO carrier round-trip; the
        // `^fired:` ledger is retained (`fired_labels()`, SM-3). (AC-carrier scion bundles are
        // the L4 / W-D stage; the seam accepts them here under the SM-7 invariant.)
        FiringEmission::ScionBundle { bundle } => {
            par2(ledger(), node_from_par(bundle.as_ref().clone()))
        },
    }
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
    let mut par = Par::default();
    par.exprs = vec![Expr {
        expr_instance: Some(ExprInstance::EMinusBody(EMinus { p1: Some(a.par), p2: Some(b.par) })),
    }];
    par.locally_free = bits;
    Node { par, free }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// LHS-pattern transcription (v1 §4.3.1): `DvPattern` → tagged-`EList` `Match` pattern.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The driver frame names a σ variable must not shadow — [`Env::get`] resolves
/// innermost-first, so a σ capture named `fuel` would corrupt the firing arm's fuel
/// resolution. Checked (fail-closed) by the seed transcription. A-S5.8 adds `rf`/`cf`
/// (the float-routed contractum re-entry's fresh return + floated-contractum formals) —
/// pure admission-time hygiene (no emitted byte depends on the const), and no bundled
/// language declares a σ variable named either.
const DRIVE_FRAME_NAMES: [&str; 8] = ["t", "fuel", "ret", "r", "c", "rb", "rf", "cf"];

/// Whether a σ variable name collides with the driver's frame discipline (the fixed
/// frame/scope names, or the generated `c{i}`/`r{i}`/`s{i}` descent names).
fn collides_with_drive_frame(name: &str) -> bool {
    if DRIVE_FRAME_NAMES.contains(&name) {
        return true;
    }
    let mut chars = name.chars();
    matches!(chars.next(), Some('c' | 'r' | 's'))
        && chars.as_str().chars().all(|c| c.is_ascii_digit())
        && name.len() > 1
}

/// Fold the positional Var/Apply subset of a pattern with an explicit post-order PDA.
///
/// Callers supply the leaf action, constructor validation/tag selection, result assembly, and the
/// diagnostic for unsupported metasyntax. Constructor validation runs before its children, matching
/// recursive fail-fast order; assembled child results remain in left-to-right source order.
fn fold_positional_pattern<T>(
    pattern: &Pattern,
    mut variable: impl FnMut(&Ident) -> Result<T, String>,
    mut constructor: impl FnMut(&Ident, usize) -> Result<String, String>,
    mut assemble: impl FnMut(String, Vec<T>) -> T,
    mut unsupported: impl FnMut(&Pattern) -> String,
) -> Result<T, String> {
    enum Task<'a> {
        Visit(&'a Pattern),
        Assemble { tag: String, child_count: usize },
    }

    let mut tasks = vec![Task::Visit(pattern)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Pattern::Term(PatternTerm::Var(name))) => {
                values.push(variable(name)?);
            },
            Task::Visit(Pattern::Term(PatternTerm::Apply { constructor: op, args })) => {
                let tag = constructor(op, args.len())?;
                tasks.push(Task::Assemble { tag, child_count: args.len() });
                tasks.extend(args.iter().rev().map(Task::Visit));
            },
            Task::Visit(other) => return Err(unsupported(other)),
            Task::Assemble { tag, child_count } => {
                let first_child = values
                    .len()
                    .checked_sub(child_count)
                    .expect("positional-pattern PDA lost a child result");
                let children = values.split_off(first_child);
                values.push(assemble(tag, children));
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    Ok(values
        .pop()
        .expect("positional-pattern PDA produced no result"))
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
/// out-of-scope shape: a repeated σ variable (POSITIONAL non-linearity stays
/// unsupported — `MatchCase.guard` equalities ride the AC carrier arms only, where the
/// shape recognizers bound them), a literal binder pattern, a substitution node, a
/// collection (rides the A-S5.5 AC carrier path, never this transcription), a
/// multi-binder constructor, or an unknown constructor.
fn transcribe_lhs_pattern(
    pattern: &Pattern,
    def: &LanguageDef,
    fingerprint: &str,
    order: &mut Vec<String>,
) -> Result<Par, String> {
    let term_by_label: HashMap<String, _> = def
        .terms
        .iter()
        .map(|term| (term.label.to_string(), term))
        .collect();
    let mut seen: HashSet<String> = order.iter().cloned().collect();
    fold_positional_pattern(
        pattern,
        |name| {
            let name = name.to_string();
            if !seen.insert(name.clone()) {
                return Err(format!(
                    "repeated LHS variable {name:?} (a non-linear POSITIONAL redex arm is \
                     not driver-supported; MatchCase.guard equalities ride the AC carrier \
                     arms only)"
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
        |constructor, arity| {
            let label = constructor.to_string();
            let term = term_by_label
                .get(&label)
                .copied()
                .ok_or_else(|| format!("unknown constructor {label:?} in a redex-arm LHS"))?;
            if is_binder_term(term) {
                if is_multi_binder_term(term) {
                    return Err(format!(
                        "multi-binder constructor {label:?} has no driver arm this stage"
                    ));
                }
                if arity != 1 {
                    return Err(format!(
                        "binder constructor {label:?} applied to {arity} argument(s) in a redex-arm \
                         LHS (the reflected binder node has exactly one child, its body)"
                    ));
                }
                Ok(LAMBDA_REFLECT_LABEL.to_string())
            } else {
                Ok(label)
            }
        },
        |tag, children| pat_tagged(fingerprint, &tag, children),
        |unsupported| match unsupported {
            Pattern::Term(PatternTerm::Lambda { .. } | PatternTerm::MultiLambda { .. }) => {
                "a literal binder pattern in a redex-arm LHS is not driver-supported this stage"
                    .to_string()
            },
            Pattern::Term(PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. }) => {
                "a substitution node in a redex-arm LHS has no matching image".to_string()
            },
            Pattern::Collection { .. } => {
                "a collection inside a POSITIONAL redex-arm LHS has no σ-ABI image (a \
                 collection-rooted LHS rides the A-S5.5 AC carrier arms instead)"
                    .to_string()
            },
            Pattern::Map { .. } => "a map (AC) LHS is not driver-supported this stage".to_string(),
            Pattern::Zip { .. } => "a zip (AC) LHS is not driver-supported this stage".to_string(),
            Pattern::IndexedVec { .. } => {
                "an indexed-vec (ORDERED) LHS is not driver-supported this stage — and it must \
                 not be routed to the AC carrier, which may permute the payload"
                    .to_string()
            },
            Pattern::Term(PatternTerm::Var(_) | PatternTerm::Apply { .. }) => {
                unreachable!("the positional fold handles Var and Apply")
            },
        },
    )
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
    let term_by_label: HashMap<String, _> = def
        .terms
        .iter()
        .map(|term| (term.label.to_string(), term))
        .collect();
    fold_positional_pattern(
        pattern,
        |name| Ok(env.var(&name.to_string())),
        |constructor, _| {
            let label = constructor.to_string();
            let term = term_by_label
                .get(&label)
                .copied()
                .ok_or_else(|| format!("unknown constructor {label:?} in a redex-arm rebuild"))?;
            Ok(if is_binder_term(term) {
                LAMBDA_REFLECT_LABEL.to_string()
            } else {
                label
            })
        },
        |tag, children| tagged(fingerprint, &tag, children),
        |_| "redex-arm rebuild reached a shape the transcription admitted incorrectly".to_string(),
    )
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

/// The driver lowering (called by [`crate::rho_net_lower::lower`]; A-S5.2, AC arms
/// A-S5.5): decide (and RECORD) admission, and for admitted languages build the `^drive`
/// receiver family (+ the per-rule AC-carrier receivers) from the SAME lowered rules /
/// program channels the installed σ-receivers were compiled with.
///
/// The opt-in short-circuit is a name comparison ([`DRIVE_OPT_IN`], AM-4), so every
/// non-opted-in language pays nothing and lowers byte-identically to pre-A-S5.2.
pub(crate) fn drive_lowering(
    def: &LanguageDef,
    program: &RhoNetProgram,
    rules: &[RhoNetLoweredRule],
    errors: &[RhoNetLoweringError],
    rewrite_by_id: &HashMap<String, &RewriteRule>,
    policy: ScionPolicy,
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

    // Extract one redex arm per fireable lowered rule: positional/subst arms fire through
    // the σ ABI (SubstRewrite — the β SEED — and positional BaseRewrite); AC arms
    // (A-S5.5: StructuralAcRewrite / NestedStructuralAcRewrite) fire through the
    // per-rule CARRIER ABI. The admission conjuncts above guarantee no other fireable
    // family is present. Arms are assembled in the DOCUMENTED deterministic order:
    // positional first, then nested-AC, then structural-AC — declaration order within
    // each (the `rules` slice is already declaration-ordered).
    let fingerprint = program.language_fingerprint.as_str();
    let mut positional_arms: Vec<DriveArm> = Vec::with_capacity(rules.len());
    let mut nested_ac_arms: Vec<DriveArm> = Vec::with_capacity(rules.len());
    let mut structural_ac_arms: Vec<DriveArm> = Vec::with_capacity(rules.len());
    for rule in rules {
        // `is_subst_beta`: the β SEED (`SubstRewrite`) — its contractum is the subst-TRS
        // cascade result, unknowable at codegen, so it is NEVER scion'd (v1 §2.2: the β
        // bundle is definitionally `ContractumRedrive`); a positional `BaseRewrite` is the
        // structural scion target.
        let (rule_id, is_ac, is_nested, is_subst_beta) = match rule {
            RhoNetLoweredRule::SubstRewrite { rule_id, .. } => (rule_id, false, false, true),
            RhoNetLoweredRule::BaseRewrite { rule_id, .. } => (rule_id, false, false, false),
            RhoNetLoweredRule::NestedStructuralAcRewrite { rule_id, .. } => {
                (rule_id, true, true, false)
            },
            // A-S5.8 (F8-AM-1b): a binder-templated nested-AC rule has NO site-keyed match
            // receiver (the NO-MATCH-ENTRY disposition) but its DRIVE carrier — which
            // pre-shifts σ slots asynchronously before the join — carries it: same nested
            // AC-arm family, declaration order preserved.
            RhoNetLoweredRule::NestedStructuralAcBinderTemplated { rule_id } => {
                (rule_id, true, true, false)
            },
            RhoNetLoweredRule::StructuralAcRewrite { rule_id, .. } => (rule_id, true, false, false),
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
        if is_ac {
            // A-S5.5: an AC-family rule fires through its reserved per-rule carrier.
            match build_drive_ac_arm(rewrite, def, fingerprint) {
                Ok(arm) => {
                    if is_nested {
                        nested_ac_arms.push(DriveArm::AcCarrier(Box::new(arm)));
                    } else {
                        structural_ac_arms.push(DriveArm::AcCarrier(Box::new(arm)));
                    }
                },
                Err(error) => {
                    // Unreachable when `drive_admissible` validated the same rewrites;
                    // recorded defensively (never a partial driver).
                    return (
                        None,
                        DriveAdmission::Unsupported {
                            reason: format!(
                                "rewrite {} does not transcribe: {error}",
                                rewrite.name
                            ),
                        },
                    );
                },
            }
            continue;
        }
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
                    .any(|term| term.label == *constructor && is_binder_term(term))
        );
        // E-1: scion-select a positional `BaseRewrite` arm iff the policy asks for it (β
        // `SubstRewrite` never scions). The actual bundle build (and its fail-closed
        // fallback to `ContractumRedrive`) happens in-frame at `fuel_gated_firing`.
        let scion = matches!(policy, ScionPolicy::StructuralScion) && !is_subst_beta;
        positional_arms.push(DriveArm::Positional(Box::new(DriveRedexArm {
            rule_label: rewrite.name.to_string(),
            accept_channel: accept_channel.clone(),
            sigma_vars: order,
            lhs: rewrite.left.clone(),
            rhs: rewrite.right.clone(),
            pattern,
            root_is_binder,
            scion,
        })));
    }
    let mut arms = positional_arms;
    arms.extend(nested_ac_arms);
    arms.extend(structural_ac_arms);

    let carrier = PsValueCarrier { fingerprint: fingerprint.to_string() };
    match drive_program_par(def, fingerprint, &arms, &carrier) {
        Ok(par) => {
            // Append the fixed-channel persistent AC-carrier receivers (one per AC arm,
            // arm order — deterministic). Empty for Lambda, so its drive `Par` is
            // byte-identical to A-S5.2 (the no-regression pin).
            let mut par = par;
            for arm in &arms {
                if let DriveArm::AcCarrier(ac) = arm {
                    par = par.append(ac.receiver.clone());
                }
            }
            (Some(par), DriveAdmission::Admitted)
        },
        Err(reason) => (None, DriveAdmission::Unsupported { reason }),
    }
}

/// WHERE a redex-arm `Match` sits — the expression naming the matched SUBJECT value in
/// the current frame (A-S5.5). A positional arm never needs it (its exhaustion datum is
/// [`rebuild_from_pattern`] over its own σ, byte-identical to A-S5.2); an AC arm fires
/// the WHOLE subject through the carrier and rests it as the exhaustion datum, and the
/// subject expression differs per position: the `^drive` formal `t` at the top level, the
/// reassembled node in a post-join re-check, the re-composed soup in a bag-arm re-check.
/// Carried as NAMES (not [`Node`]s) because a `Node` is frame-relative and each case body
/// pushes its own binders — the expression is rebuilt name-late inside the case env.
#[derive(Debug, Clone)]
pub(crate) enum DriveSubject<'a> {
    /// The `^drive` receive formal `t` (top-level arm position).
    FrameT,
    /// The reassembled congruence/binder node `[⌜label⌝, s₀, …]` (post-join / post-rewrap
    /// re-check position).
    ReassembledNode {
        /// The reflected constructor label.
        label: &'a str,
        /// The join-formal names holding the driven children.
        child_names: &'a [String],
    },
    /// The re-composed soup `{fragment | remainder}` (bag-arm reassembly re-check
    /// position — the fragment is the three-case-dispatched element contribution).
    ReassembledSoup {
        /// The frame name holding the element's bag-fragment value.
        fragment: &'a str,
        /// The frame name holding the driven remainder soup.
        remainder: &'a str,
    },
}

/// Build the subject expression for the current frame (see [`DriveSubject`]). The
/// carrier supplies the node reassembly (its reflected-tag discipline), so no
/// fingerprint threads through here.
fn drive_subject_node(subject: &DriveSubject<'_>, env: &Env, carrier: &dyn DriveCarrier) -> Node {
    match subject {
        DriveSubject::FrameT => env.var("t"),
        DriveSubject::ReassembledNode { label, child_names } => {
            let children: Vec<Node> = child_names.iter().map(|name| env.var(name)).collect();
            carrier.reassemble(env, label, &children)
        },
        DriveSubject::ReassembledSoup { fragment, remainder } => {
            par2(env.var(fragment), env.var(remainder))
        },
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// E-1 scion grafting (design v1 §3; delta amendments SM-1..11): the per-rule precompiled
// drive decomposition of a positional structural (`BaseRewrite`) rule's RHS. Known
// constructor positions are GRAFTED (Skip — no re-drive); σ-slot occurrences are DRIVEN
// (buds, at `fuel-1`); positions whose slot-as-unknown sub-instance could match a redex arm
// are RE-CHECKED (P-resubmit at `fuel-1`). Built with the `rho_net_subst_trs` De Bruijn
// combinators in the arm frame, so the emitted Par's `locally_free` tracks the σ/fuel/ret
// slots (recovered by `node_from_par` at the seam). Thesis Ch. 6: `scion(s, ℓ→r)` / `graft`.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// Per-rule firing-emission policy (design v1 §3.6): the codegen selector the E-1 A/B
/// measurement swaps. Production ALWAYS lowers under [`ScionPolicy::AllRedrive`] — every
/// emitted driver Par is then byte-identical to pre-E-1 (the a_s5_6 / a_s5_8 pins guard
/// this). The `bench-scion` surface lowers a second copy under
/// [`ScionPolicy::StructuralScion`], selecting a scion bundle for each admitted POSITIONAL
/// `BaseRewrite` arm; β `SubstRewrite` and every AC arm stay `ContractumRedrive` (L1 scope).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScionPolicy {
    /// Every arm re-drives its whole contractum — the production default, byte-identical
    /// to pre-E-1.
    AllRedrive,
    /// Positional `BaseRewrite` arms emit a scion bundle; β and AC arms re-drive.
    StructuralScion,
}

/// Conservative slot-as-unknown unification of a rule LHS against an RHS subterm (design
/// v1 §2.1 / §3.2.1 `harvest`): `true` (⟹ Re-check the position) UNLESS the two roots are
/// DEFINITELY distinct constructors. A variable on either side (an LHS pattern var, or an
/// RHS σ-slot whose normal form is unknown) could unify. Re-check-when-uncertain is always
/// SOUND (a spurious re-check is a redundant `Match`, never a wrong step); only a definite
/// constructor / arity mismatch licenses the Skip (the graft — the savings).
fn scion_could_unify(lhs: &Pattern, sub: &Pattern) -> bool {
    match (lhs, sub) {
        (Pattern::Term(PatternTerm::Var(_)), _) | (_, Pattern::Term(PatternTerm::Var(_))) => true,
        (
            Pattern::Term(PatternTerm::Apply { constructor: c1, args: a1 }),
            Pattern::Term(PatternTerm::Apply { constructor: c2, args: a2 }),
        ) => {
            c1 == c2
                && a1.len() == a2.len()
                && a1.iter().zip(a2).all(|(x, y)| scion_could_unify(x, y))
        },
        // Any other shape pairing (binder / subst / collection LHS vs a constructor RHS) —
        // conservatively re-check (sound); the L1 positional cells never reach this arm.
        _ => true,
    }
}

/// Whether the constructor at RHS position `sub` could be a redex root for SOME fireable
/// rule (design v1 §3.2.1 `mark = Recheck`). Only called on `Apply` positions (a σ-slot is
/// a bud, driven — never a re-check).
fn scion_position_is_recheck(sub: &Pattern, fireable_lhs: &[&Pattern]) -> bool {
    fireable_lhs.iter().any(|lhs| scion_could_unify(lhs, sub))
}

/// Whether `pat` or any constructor descendant is a re-check position (a σ-slot leaf is
/// never one). Drives the Skip-vs-recheck partition in [`scion_emit_point`].
fn scion_contains_recheck(pat: &Pattern, fireable_lhs: &[&Pattern]) -> bool {
    match pat {
        Pattern::Term(PatternTerm::Apply { args, .. }) => {
            scion_position_is_recheck(pat, fireable_lhs)
                || args
                    .iter()
                    .any(|arg| scion_contains_recheck(arg, fireable_lhs))
        },
        _ => false,
    }
}

/// Collect the σ-slot occurrences of `rhs` in left-to-right DFS order, each paired with its
/// position PATH (child-index list). Fail-closed (`Err`) on a dangling RHS variable (not a
/// σ capture) or any non-positional shape (binder / substitution / collection RHS) — such a
/// rule stays `ContractumRedrive` (SM-8 fail-closed).
fn scion_collect_slots(
    rhs: &Pattern,
    path: &mut Vec<usize>,
    sigma_set: &HashSet<String>,
    out: &mut Vec<(Vec<usize>, String)>,
) -> Result<(), String> {
    match rhs {
        Pattern::Term(PatternTerm::Var(name)) => {
            let name = name.to_string();
            if sigma_set.contains(&name) {
                out.push((path.clone(), name));
                Ok(())
            } else {
                Err(format!("scion: RHS variable {name:?} is not a σ capture (dangling)"))
            }
        },
        Pattern::Term(PatternTerm::Apply { args, .. }) => {
            for (index, arg) in args.iter().enumerate() {
                path.push(index);
                scion_collect_slots(arg, path, sigma_set, out)?;
                path.pop();
            }
            Ok(())
        },
        _ => Err("scion: non-positional RHS shape (binder / substitution / collection) is not \
             driver-scion-supported this stage"
            .to_string()),
    }
}

/// Rebuild the reflected value of a PURE (no re-check) RHS subtree at `env`: a σ-slot leaf
/// resolves to its joined normal form `s{i}` (the `i`-th slot in DFS order), a constructor
/// to `tagged(fp, label, children)`. Env-parametric (name-late `env.var`) so it is safe to
/// re-invoke at any De Bruijn depth (inside a re-check `Match` case, the join body, …).
fn scion_build_pure(
    pat: &Pattern,
    path: &[usize],
    slot_index: &HashMap<Vec<usize>, usize>,
    env: &Env,
    fingerprint: &str,
) -> Node {
    match pat {
        Pattern::Term(PatternTerm::Var(_)) => {
            let idx = slot_index.get(path).copied().unwrap_or(0);
            env.var(&format!("s{idx}"))
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let label = constructor.to_string();
            let children: Vec<Node> = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    let mut child_path = path.to_vec();
                    child_path.push(index);
                    scion_build_pure(arg, &child_path, slot_index, env, fingerprint)
                })
                .collect();
            tagged(fingerprint, &label, children)
        },
        // Unreachable: `scion_collect_slots` fail-closed on every other shape before build.
        _ => tagged(fingerprint, "^scion-bug", Vec::new()),
    }
}

/// Rebuild the reflected value of a RECHECK subtree in RAW form (design v2 §1.2 `build_raw`):
/// identical to [`scion_build_pure`] EXCEPT a σ-slot leaf resolves to its RAW arm-frame capture
/// `env.var(σ)` (the UN-driven slot) rather than a joined normal form `s{i}`. The reassembled raw
/// node is resubmitted to the generic `^drive` AT THE PARENT (recheck) node, where the redex-arm-
/// before-descent discipline ([`drive_program_par`] step 1: "a redex at this node fires before any
/// descent") fires the head redex per firing WITHOUT ever descending the slot spine — recovering
/// the linear, ΔDriveTau/firing = s behavior the v1 eager-slot drive lost to a ½m² spine re-drive.
/// `env` MUST be the drive-point frame where σ is in scope (R-9 frame discipline — NOT a detached
/// ground context; the σ names live in the arm frame the reassembly threads through).
fn scion_build_raw(pat: &Pattern, env: &Env, fingerprint: &str) -> Node {
    match pat {
        Pattern::Term(PatternTerm::Var(name)) => env.var(&name.to_string()),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let label = constructor.to_string();
            let children: Vec<Node> = args
                .iter()
                .map(|arg| scion_build_raw(arg, env, fingerprint))
                .collect();
            tagged(fingerprint, &label, children)
        },
        // Unreachable: `scion_collect_slots` fail-closed on every other shape before build.
        _ => tagged(fingerprint, "^scion-bug", Vec::new()),
    }
}

/// Emit the demand-driven DRIVE-POINT of a recheck subtree (design v2 §1.2 — the head-inspection
/// recovery): `new r' { ⌜^drive⌝!(build_raw(subtree), fuel-1, r') | for(@c <- r'){ <tail c> } }`.
/// The whole recheck subtree is resubmitted RAW (its σ-slots un-driven, [`scion_build_raw`]) to the
/// generic `^drive`, which — because a redex at the resubmitted (parent) node fires BEFORE any
/// congruence descent — peels the head redex per firing WITHOUT re-descending the un-fired slot
/// spine (the v1 eager-slot ½m² is eliminated). A hit re-fires through `^drive` (chained,
/// outermost-first, +1 `^drive` COMM/firing); a quiesced subtree is published as this position's
/// normal form on `r'`. `r'`/`c` use the `r#`/`c#` fresh-name namespace (SM-8c). The subtree is
/// PURE below its recheck root (no nested recheck) — the Fold 3 guard, checked by the caller.
/// `next_index` is SHARED with the bare-slot returns so no channel aliases (R-5).
fn scion_emit_recheck_point(
    subtree: &Pattern,
    fingerprint: &str,
    env: &Env,
    fuel_var: &str,
    next_index: &std::cell::Cell<usize>,
    tail: &dyn Fn(Node, &Env) -> Result<Node, String>,
) -> Result<Node, String> {
    let idx = next_index.get();
    next_index.set(idx + 1);
    let r_name = format!("r{idx}");
    let c_name = format!("c{idx}");
    let renv = env.push(&[r_name.as_str()]);
    let drive_call = send(
        ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
        vec![
            scion_build_raw(subtree, &renv, fingerprint),
            eminus(renv.var(fuel_var), gint(1)),
            renv.var(&r_name),
        ],
    );
    let cenv = renv.push(&[c_name.as_str()]);
    let for_body = tail(cenv.var(&c_name), &cenv)?;
    let for_node = for1(renv.var(&r_name), for_body);
    Ok(new_scope(1, par2(drive_call, for_node)))
}

/// Whether a σ-slot at `slot_path` is a BARE slot (design v2 §1.2): NO proper ancestor position on
/// its root-to-leaf path is a [`scion_position_is_recheck`] root. A bare slot is driven ONCE and
/// joined (the v1 eager path — no resubmit covers it, so no quadratic); a slot BELOW a recheck
/// instead rides RAW into that recheck's drive-point ([`scion_build_raw`]) and is never separately
/// driven. Fail-safe `false` on a malformed path (treats it as recheck-internal — conservative).
fn scion_slot_is_bare(rhs: &Pattern, slot_path: &[usize], fireable_lhs: &[&Pattern]) -> bool {
    let mut node = rhs;
    for &child in slot_path {
        // `node` is a proper ANCESTOR of the slot leaf; a recheck ancestor ⟹ the slot is internal.
        if scion_position_is_recheck(node, fireable_lhs) {
            return false;
        }
        let Pattern::Term(PatternTerm::Apply { args, .. }) = node else {
            return false;
        };
        node = &args[child];
    }
    true
}

/// Reassemble `pat`'s value in the demand-driven scion bundle (design v2 §1.2), threading a
/// continuation `tail` (given this position's value node + the env it is live in, produce the
/// rest). Partitions each position into the three v2 roles:
///  * PURE (no recheck below): grafted directly ([`scion_build_pure`]; bare σ-slots resolve to
///    their joined NF `s{i}`) — the thesis-Ch6 inert graft, ZERO `^drive`.
///  * RECHECK subtree (a [`scion_position_is_recheck`] root): ONE demand-driven drive-point
///    ([`scion_emit_recheck_point`]) — the whole subtree resubmitted raw and driven head-first.
///  * SKIP constructor above a recheck: grafted, recursing into its (single) recheck-bearing
///    child — the D1..Ds ladder wrap.
///
/// FOLD 1 (R-3, the inert-graft ROOTEDNESS guard, MANDATORY): a Skip constructor that is EVER a
/// rule redex root (`redex_root_ctors`) above a reducible subtree can BECOME a redex once its
/// children reduce — which [`scion_could_unify`]'s static-shape check misses — so control would
/// fire it and grafting it inert would UNDER-REDUCE. Such a position fails CLOSED (`Err` → the arm
/// stays `ContractumRedrive`), closing the gap the shape check leaves open. FOLD 3 (kept for L1):
/// branching recheck (>1 recheck child) and nested recheck (recheck above recheck) also fail
/// closed this stage.
#[allow(clippy::too_many_arguments)]
fn scion_emit_point(
    pat: &Pattern,
    path: &[usize],
    slot_index: &HashMap<Vec<usize>, usize>,
    fireable_lhs: &[&Pattern],
    redex_root_ctors: &HashSet<String>,
    fingerprint: &str,
    env: &Env,
    fuel_var: &str,
    next_index: &std::cell::Cell<usize>,
    tail: &dyn Fn(Node, &Env) -> Result<Node, String>,
) -> Result<Node, String> {
    // PURE (no recheck anywhere below) → graft directly (bare σ-slots → joined NF `s{i}`).
    if !scion_contains_recheck(pat, fireable_lhs) {
        return tail(scion_build_pure(pat, path, slot_index, env, fingerprint), env);
    }
    // Contains a recheck ⟹ `pat` is an `Apply` (a σ-slot leaf never contains one).
    let Pattern::Term(PatternTerm::Apply { constructor, args }) = pat else {
        return Err("scion: re-check at a non-constructor RHS position".to_string());
    };
    let label = constructor.to_string();
    // RECHECK subtree root — the whole subtree is ONE demand-driven drive-point.
    if scion_position_is_recheck(pat, fireable_lhs) {
        // FOLD 3 (kept): a nested recheck (recheck strictly below this recheck root) is
        // unsupported this stage — `build_raw` reassembles the subtree raw and cannot host a
        // second drive-point below it. Fail closed.
        if args
            .iter()
            .any(|arg| scion_contains_recheck(arg, fireable_lhs))
        {
            return Err(
                "scion: nested re-check (re-check above a re-check) unsupported this stage"
                    .to_string(),
            );
        }
        return scion_emit_recheck_point(pat, fingerprint, env, fuel_var, next_index, tail);
    }
    // A SKIP constructor above a recheck. FOLD 1 (R-3): reject the inert graft when the ctor is
    // ever a rule redex root — after its reducible child normalizes it could BECOME a redex that
    // control fires, so grafting it inert would under-reduce (fail closed → `ContractumRedrive`).
    if redex_root_ctors.contains(&label) {
        return Err(format!(
            "scion: inert-graft rootedness (Fold 1) — Skip ctor {label:?} is a rule redex root \
             above a reducible subtree; grafting it inert could under-reduce vs control"
        ));
    }
    // FOLD 3 (kept): branching recheck (>1 recheck-bearing child) unsupported this stage.
    let non_pure: Vec<usize> = (0..args.len())
        .filter(|&i| scion_contains_recheck(&args[i], fireable_lhs))
        .collect();
    if non_pure.len() > 1 {
        return Err(
            "scion: branching re-check (>1 re-check child) unsupported this stage".to_string()
        );
    }
    // Recurse into the single recheck-bearing child, grafting THIS constructor around the result
    // (pure siblings built with bare-slot NFs at the tail env).
    let j = non_pure[0];
    let mut child_path = path.to_vec();
    child_path.push(j);
    let child_tail = |child_value: Node, tail_env: &Env| -> Result<Node, String> {
        let children: Vec<Node> = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                if index == j {
                    child_value.clone()
                } else {
                    let mut cp = path.to_vec();
                    cp.push(index);
                    scion_build_pure(arg, &cp, slot_index, tail_env, fingerprint)
                }
            })
            .collect();
        tail(tagged(fingerprint, &label, children), tail_env)
    };
    scion_emit_point(
        &args[j],
        &child_path,
        slot_index,
        fireable_lhs,
        redex_root_ctors,
        fingerprint,
        env,
        fuel_var,
        next_index,
        &child_tail,
    )
}

/// Build the E-1 scion bundle Node for one positional structural (`BaseRewrite`) arm (design v2
/// §1.2 — the DEMAND-DRIVEN slot-scion): the RHS is reassembled with each recheck subtree emitted
/// as ONE drive-point that resubmits the subtree RAW to the generic `^drive` (head-first firing,
/// [`scion_emit_recheck_point`]) and each inert Skip constructor grafted; only BARE σ-slots (none
/// under a recheck) are driven concurrently at `fuel-1` and joined
/// (`new r0..r_{kb-1} { drive(σ_i, fuel-1, r_i) | join(r_i){ reassemble → ret } }`). This
/// REPLACES the v1 eager scion (which drove EVERY slot to NF and re-descended the un-fired slot
/// spine per firing → the measured ½m² pessimization); driving the recheck NODE rather than the
/// slot recovers ΔDriveTau/firing = s (linear). Built in the arm frame `env` (σ innermost).
/// Fail-closed `Err` on any RHS outside the positional-scion scope (dangling var, non-positional
/// shape, Fold 1 rootedness, or a Fold 3 branching/nested recheck) → the arm stays
/// `ContractumRedrive`.
fn scion_bundle_for_rule(
    rhs: &Pattern,
    sigma_vars: &[String],
    arms: &[DriveArm],
    fingerprint: &str,
    env: &Env,
    fuel_var: &str,
    ret_var: &str,
) -> Result<Node, String> {
    let sigma_set: HashSet<String> = sigma_vars.iter().cloned().collect();
    let mut slots: Vec<(Vec<usize>, String)> = Vec::new();
    scion_collect_slots(rhs, &mut Vec::new(), &sigma_set, &mut slots)?;
    let fireable_lhs: Vec<&Pattern> = arms
        .iter()
        .filter_map(|arm| match arm {
            DriveArm::Positional(positional) => Some(&positional.lhs),
            DriveArm::AcCarrier(_) => None,
        })
        .collect();
    // FOLD 1 (R-3): the constructors that are EVER a positional rule's LHS redex root. A Skip ctor
    // in this set above a reducible subtree cannot be grafted inert (it could BECOME a redex once
    // its children reduce). AC-family roots are out of L1 scope — the scion is positional-only
    // (`fireable_lhs` already drops AC arms, matching the recheck marks) and dormant in production.
    let redex_root_ctors: HashSet<String> = fireable_lhs
        .iter()
        .filter_map(|lhs| match lhs {
            Pattern::Term(PatternTerm::Apply { constructor, .. }) => Some(constructor.to_string()),
            _ => None,
        })
        .collect();
    // Partition the σ-slots: BARE (driven + joined, v1-style — no resubmit covers them) vs
    // RECHECK-INTERNAL (ride RAW into a recheck drive-point via `scion_build_raw`). Only bare slots
    // get a join return channel + `s{i}` NF value; `slot_index` is over the bare slots alone.
    let bare_slots: Vec<&(Vec<usize>, String)> = slots
        .iter()
        .filter(|(path, _)| scion_slot_is_bare(rhs, path, &fireable_lhs))
        .collect();
    let slot_index: HashMap<Vec<usize>, usize> = bare_slots
        .iter()
        .enumerate()
        .map(|(i, (p, _))| (p.clone(), i))
        .collect();
    let k_bare = bare_slots.len();
    // Fresh `r#`/`c#` recheck indices start after the k_bare slot returns (SM-8c / R-5 namespace).
    let next_index = std::cell::Cell::new(k_bare);
    let tail = |value: Node, tail_env: &Env| -> Result<Node, String> {
        Ok(send(tail_env.var(ret_var), vec![value]))
    };
    if k_bare == 0 {
        // No bare slots (every slot rides raw into a recheck drive-point, or the RHS is ground) —
        // no join; the reassembly (with its drive-points) is emitted straight in the arm frame.
        return scion_emit_point(
            rhs,
            &[],
            &slot_index,
            &fireable_lhs,
            &redex_root_ctors,
            fingerprint,
            env,
            fuel_var,
            &next_index,
            &tail,
        );
    }
    let slot_r_names: Vec<String> = (0..k_bare).map(|i| format!("r{i}")).collect();
    let slot_r_refs: Vec<&str> = slot_r_names.iter().map(String::as_str).collect();
    let inner_env = env.push(&slot_r_refs);
    // Concurrent BARE-slot drives at `fuel-1` (the single per-firing decrement, v2 §1.2).
    let mut composed: Option<Node> = None;
    for (i, (_, sigma)) in bare_slots.iter().enumerate() {
        let call = send(
            ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
            vec![
                inner_env.var(sigma),
                eminus(inner_env.var(fuel_var), gint(1)),
                inner_env.var(&slot_r_names[i]),
            ],
        );
        composed = Some(match composed {
            None => call,
            Some(acc) => par2(acc, call),
        });
    }
    let join_sources: Vec<Node> = slot_r_names.iter().map(|r| inner_env.var(r)).collect();
    let slot_val_names: Vec<String> = (0..k_bare).map(|i| format!("s{i}")).collect();
    let slot_val_refs: Vec<&str> = slot_val_names.iter().map(String::as_str).collect();
    let join_body_env = inner_env.push(&slot_val_refs);
    let reassembly = scion_emit_point(
        rhs,
        &[],
        &slot_index,
        &fireable_lhs,
        &redex_root_ctors,
        fingerprint,
        &join_body_env,
        fuel_var,
        &next_index,
        &tail,
    )?;
    let join_node = join(join_sources, reassembly);
    Ok(new_scope(k_bare, par2(composed.expect("k_bare ≥ 1"), join_node)))
}

/// The fuel-gated firing body of one POSITIONAL redex arm (plan v2 §4.2): the ground
/// `GInt(0)` exhaustion case FIRST (AM-7 — arm order is load-bearing under
/// `wrapping_sub`), then the wildcard firing case through the [`firing_emission_node`]
/// seam. `env` carries the arm's σ captures. Byte-identical to the A-S5.2 emission (the
/// Lambda no-regression pin) UNLESS this arm is scion-selected (E-1 `StructuralScion`).
fn fuel_gated_firing(
    arm: &DriveRedexArm,
    all_arms: &[DriveArm],
    def: &LanguageDef,
    fingerprint: &str,
    env: &Env,
    carrier: &dyn DriveCarrier,
    route_through_float: bool,
) -> Result<Node, String> {
    let exhaustion_datum = rebuild_from_pattern(&arm.lhs, def, fingerprint, env)?;
    // E-1: a scion-selected arm emits its precompiled bundle (built in THIS arm frame) in
    // place of the redrive `for`; any RHS outside the positional-scion scope fails closed to
    // `ContractumRedrive` (SM-8). Production lowers under `AllRedrive` (`arm.scion == false`),
    // so this is inert and the emission is byte-identical.
    let emission = if arm.scion {
        match scion_bundle_for_rule(
            &arm.rhs,
            &arm.sigma_vars,
            all_arms,
            fingerprint,
            env,
            "fuel",
            "ret",
        ) {
            Ok(bundle) => FiringEmission::ScionBundle { bundle: Box::new(bundle.par) },
            Err(_) => FiringEmission::ContractumRedrive,
        }
    } else {
        FiringEmission::ContractumRedrive
    };
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
                    &emission,
                    fingerprint,
                    env,
                    "fuel",
                    "ret",
                    carrier,
                    route_through_float,
                ),
            },
        ],
    ))
}

/// The fuel-gated firing body of one AC CARRIER-ABI redex arm (A-S5.5): the ground
/// `GInt(0)` exhaustion case FIRST (AM-7), the exhaustion datum the SUBJECT expression
/// itself (an AC arm's check pattern binds only guard slots — the redex node is the
/// whole matched value, current-by-construction in every position via
/// [`drive_subject_node`]), then the wildcard firing case through the
/// [`ac_firing_emission_node`] seam.
fn ac_fuel_gated_firing(
    arm: &DriveAcArm,
    fingerprint: &str,
    env: &Env,
    carrier: &dyn DriveCarrier,
    subject: &DriveSubject<'_>,
    route_through_float: bool,
) -> Node {
    match_(
        env.var("fuel"),
        vec![
            Case {
                pattern: new_gint_par(0, Vec::new(), false),
                free_count: 0,
                body: send(
                    ground(new_gstring_par(drive_fuel_channel(fingerprint), Vec::new(), false)),
                    vec![drive_subject_node(subject, env, carrier)],
                ),
            },
            Case {
                pattern: pat_wildcard(),
                free_count: 0,
                body: ac_firing_emission_node(
                    arm,
                    &FiringEmission::ContractumRedrive,
                    fingerprint,
                    env,
                    "fuel",
                    "ret",
                    carrier,
                    subject,
                    route_through_float,
                ),
            },
        ],
    )
}

/// The redex cases (pattern + guard + frame + fuel-gated firing body), one per compiled
/// [`DriveArm`] in the documented deterministic order — shared between the top-level
/// `match t` and every post-join / post-rewrap / bag-arm re-check (a re-check re-tests
/// the reassembled subject against the redex arms ONLY: its children are already normal
/// forms, so descent would be redundant). Positional arms are byte-identical to the
/// A-S5.2 emission (guard `None`, [`rebuild_from_pattern`] datum); AC arms carry the
/// non-linear `MatchCase.guard` and fire the SUBJECT through the carrier ABI.
fn redex_cases(
    arms: &[DriveArm],
    def: &LanguageDef,
    fingerprint: &str,
    env: &Env,
    carrier: &dyn DriveCarrier,
    subject: &DriveSubject<'_>,
) -> Result<Vec<(Case, Option<Par>)>, String> {
    // A-S5.8 (decision Q-AB = A): a float-bearing language's firing emissions route EVERY
    // contractum through the installed `^float` dispatcher before the re-drive; every other
    // language's emissions are byte-identical to pre-A-S5.8.
    let route_through_float = crate::rho_net_float::language_is_float_bearing(def);
    let mut cases = Vec::with_capacity(arms.len());
    for arm in arms {
        match arm {
            DriveArm::Positional(arm) => {
                let check = carrier.redex_check(arm, env);
                debug_assert!(check.guard.is_none(), "positional arms carry no guard");
                let sigma_refs: Vec<&str> = arm.sigma_vars.iter().map(String::as_str).collect();
                let body = {
                    let env = env.push(&sigma_refs);
                    fuel_gated_firing(
                        arm,
                        arms,
                        def,
                        fingerprint,
                        &env,
                        carrier,
                        route_through_float,
                    )?
                };
                cases.push((
                    Case {
                        pattern: check.pattern,
                        free_count: check.free_count,
                        body,
                    },
                    None,
                ));
            },
            DriveArm::AcCarrier(arm) => {
                let check = carrier.ac_redex_check(arm);
                let case_refs: Vec<&str> = arm.case_names.iter().map(String::as_str).collect();
                let body = {
                    let env = env.push(&case_refs);
                    ac_fuel_gated_firing(
                        arm,
                        fingerprint,
                        &env,
                        carrier,
                        subject,
                        route_through_float,
                    )
                };
                cases.push((
                    Case {
                        pattern: check.pattern,
                        free_count: check.free_count,
                        body,
                    },
                    check.guard,
                ));
            },
        }
    }
    Ok(cases)
}

/// The re-check node (v1 §4.3.2, A-S5.5-generalized): match the reassembled SUBJECT
/// (node or soup — [`DriveSubject`]) against the redex arms only; the wildcard default
/// publishes it as this subtree's normal form.
fn recheck_node(
    arms: &[DriveArm],
    def: &LanguageDef,
    fingerprint: &str,
    env: &Env,
    subject: &DriveSubject<'_>,
    carrier: &dyn DriveCarrier,
) -> Result<Node, String> {
    let assembled = drive_subject_node(subject, env, carrier);
    let mut cases = redex_cases(arms, def, fingerprint, env, carrier, subject)?;
    cases.push((
        Case {
            pattern: pat_wildcard(),
            free_count: 0,
            body: send(env.var("ret"), vec![drive_subject_node(subject, env, carrier)]),
        },
        None,
    ));
    Ok(match_guarded(assembled, cases))
}

/// Build the persistent `^drive` receiver family for one admitted language (see the
/// module docs for the emitted shape). Deterministic arm order: redex arms (positional,
/// then nested-AC, then structural-AC — declaration order within each, pre-ordered by
/// [`drive_lowering`]), congruence-descent arms (constructor declaration order), the
/// binder arm, the bag arms (one per HashBag collection constructor, A-S5.5) + the Nil
/// empty-bag leaf, the `^free`/`^bound` passthroughs, the `^drive-err` wildcard.
pub(crate) fn drive_program_par(
    def: &LanguageDef,
    fingerprint: &str,
    arms: &[DriveArm],
    carrier: &dyn DriveCarrier,
) -> Result<Par, String> {
    let frame = carrier.frame_formals();
    let env = Env::root(&frame.formals);
    let mut cases: Vec<(Case, Option<Par>)> = Vec::new();

    // 1. Redex arms — outermost-first strategy: a redex at this node fires before any
    //    descent. The subject at the top level is the `^drive` formal `t`.
    cases.extend(redex_cases(arms, def, fingerprint, &env, carrier, &DriveSubject::FrameT)?);

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
                    for (i, ret_name) in ret_names.iter().enumerate() {
                        let call = send(
                            ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
                            vec![
                                carrier.child_payload(&env, i),
                                env.var("fuel"),
                                env.var(ret_name),
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
                        recheck_node(
                            arms,
                            def,
                            fingerprint,
                            &env,
                            &DriveSubject::ReassembledNode { label: &label, child_names: &s_names },
                            carrier,
                        )?
                    });
                    par2(composed.expect("arity ≥ 1"), join_node)
                })
            }
        };
        cases.push((
            Case {
                pattern: pat_tagged(fingerprint, &label, child_pats),
                free_count: arity,
                body,
            },
            None,
        ));
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
        let binder_rooted_entry = arms.iter().any(
            |arm| matches!(arm, DriveArm::Positional(positional) if positional.root_is_binder),
        );
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
                        let rb_names = ["rb".to_string()];
                        recheck_node(
                            arms,
                            def,
                            fingerprint,
                            &env,
                            &DriveSubject::ReassembledNode {
                                label: LAMBDA_REFLECT_LABEL,
                                child_names: &rb_names,
                            },
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
        cases.push((
            Case {
                pattern: pat_tagged(fingerprint, LAMBDA_REFLECT_LABEL, vec![pat_free(0)]),
                free_count: 1,
                body,
            },
            None,
        ));
    }

    // 4. BAG arms (A-S5.5, plan v2 §4.3.3 — the R3 `SelfDrivingCollectionSubject` gap
    //    closed) — one per HashBag collection constructor: peel ONE element off the soup
    //    (send-pattern + free-Par remainder), drive the element and the remainder
    //    CONCURRENTLY (fuel copied, never decremented — descent), atomically join, splice
    //    the element's THREE-CASE fragment back into the remainder (AM-3), and re-check
    //    the re-composed soup against the redex arms only (a redex formed ACROSS the
    //    reassembled siblings — e.g. In/Open needing ≥ 2 normalized elements — fires
    //    here). Followed by the Nil leaf: the EMPTY bag (`Par::default()`, the AM-3
    //    reflection of `op{}`) is its own normal form — without it a Nil element value
    //    would fall to the `^drive-err` wildcard (AM-3's exact defect).
    let bag_ops = hashbag_collection_ops(def);
    for op in &bag_ops {
        let body = {
            let env = env.push(&["e", "rem"]);
            new_scope(2, {
                let env = env.push(&["re", "rr"]);
                let drive_element = send(
                    ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
                    vec![env.var("e"), env.var("fuel"), env.var("re")],
                );
                let drive_remainder = send(
                    ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
                    vec![env.var("rem"), env.var("fuel"), env.var("rr")],
                );
                let join_node = join(vec![env.var("re"), env.var("rr")], {
                    let env = env.push(&["ve", "vr"]);
                    new_scope(1, {
                        let env = env.push(&["f"]);
                        let dispatch =
                            bag_fragment_dispatch(fingerprint, op, env.var("ve"), env.var("f"));
                        let observe = for1(env.var("f"), {
                            let env = env.push(&["w"]);
                            recheck_node(
                                arms,
                                def,
                                fingerprint,
                                &env,
                                &DriveSubject::ReassembledSoup { fragment: "w", remainder: "vr" },
                                carrier,
                            )?
                        });
                        par2(dispatch, observe)
                    })
                });
                par2(par2(drive_element, drive_remainder), join_node)
            })
        };
        cases.push((
            Case {
                pattern: soup_peel_pattern(fingerprint, op),
                free_count: 2,
                body,
            },
            None,
        ));
    }
    if !bag_ops.is_empty() {
        // The Nil empty-bag leaf (AM-3 case (a)): `op{}` reflects as `Par::default()`
        // and is its own normal form.
        cases.push((
            Case {
                pattern: Par::default(),
                free_count: 0,
                body: send(env.var("ret"), vec![ground(Par::default())]),
            },
            None,
        ));
    }

    // 5. Reserved passthroughs: a free-variable leaf and a bound-variable leaf are inert
    //    under the drive (the `^subst`/`^shift` `:787-796` / `:831-833` shape).
    cases.push((
        Case {
            pattern: pat_tagged(fingerprint, FREE_VAR_REFLECT_LABEL, vec![pat_free(0)]),
            free_count: 1,
            body: {
                let env = env.push(&["x"]);
                send(
                    env.var("ret"),
                    vec![tagged(fingerprint, FREE_VAR_REFLECT_LABEL, vec![env.var("x")])],
                )
            },
        },
        None,
    ));
    cases.push((
        Case {
            pattern: pat_tagged(fingerprint, BOUND_VAR_REFLECT_LABEL, vec![pat_free(0)]),
            free_count: 1,
            body: {
                let env = env.push(&["n"]);
                send(
                    env.var("ret"),
                    vec![tagged(fingerprint, BOUND_VAR_REFLECT_LABEL, vec![env.var("n")])],
                )
            },
        },
        None,
    ));

    // 6. The typed fail-close wildcard: an unrecognized head is NEVER silently normal
    //    (the R3 `^respread-err` discipline) — it rests on the GString err channel where
    //    the host cross-check sees it.
    cases.push((
        Case {
            pattern: pat_wildcard(),
            free_count: 0,
            body: send(
                ground(new_gstring_par(drive_err_channel(fingerprint), Vec::new(), false)),
                vec![env.var("t")],
            ),
        },
        None,
    ));

    let body = match_guarded(env.var("t"), cases);
    Ok(
        persistent_contract(tag_par(fingerprint, DRIVE_RESERVED_LABEL), frame.formals.len(), body)
            .par,
    )
}

/// The HashBag collection constructors of a language (`op` labels), in term-declaration
/// order — the bag arms' enumeration. Resolves each term's collection kind through the
/// A-S5.3 [`resolve_constructor_collection_type`] (term-context first, `::=`-declared
/// grammar-item fallback), so the driver's bag arms can never disagree with the AC
/// lowering about which constructors are bags.
///
/// `pub(crate)` (A-S5.8, F8-AM-5d): shared with the `^shift` soup-arm gate
/// (`crate::rho_net_subst_trs::shift_receiver_par` — the arms are emitted iff this is
/// non-empty, keeping bag-free languages byte-identical) and the `^float` family's
/// soup-peel enumeration (`crate::rho_net_float`).
pub(crate) fn hashbag_collection_ops(def: &LanguageDef) -> Vec<String> {
    def.terms
        .iter()
        .filter_map(|term| {
            let label = term.label.to_string();
            matches!(
                resolve_constructor_collection_type(def, &label),
                Some(CollectionType::HashBag)
            )
            .then_some(label)
        })
        .collect()
}

#[cfg(test)]
#[path = "../tests/support/rho_net_drive_pattern_recursive_oracle.rs"]
mod pattern_recursive_oracle;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::lower_language_def;
    use mettail_ast::language::LanguageDef;

    /// The INV-S6 scope these unit tests derive their channel names under. Any
    /// slash-free string serves: these tests assert Par SHAPE (case structure, send
    /// targets, receiver arity), not the scope's value — a production emission takes
    /// its scope from `language_definition_fingerprint`.
    const FP: &str = "mettail-langdef-v1:0000000000000000";

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
        let drive = lowered
            .drive()
            .expect("an admitted language carries the drive program");
        assert_eq!(drive.receives.len(), 1, "the driver is ONE persistent ^drive receiver");
        let receive = &drive.receives[0];
        assert!(receive.persistent, "the ^drive receiver is persistent");
        assert_eq!(receive.binds[0].patterns.len(), 3, "the PS frame is (t, fuel, ret)");
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

    /// The (prost length, `DefaultHasher`) fingerprint of an encoded `Par` — the
    /// `a_s5_6_byte_identity_pins` convention (SipHash-1-3, fixed keys ⇒ cross-process
    /// deterministic), paired with the exact byte length so any codegen perturbation flips
    /// at least one component.
    fn par_fingerprint(par: &Par) -> (usize, u64) {
        use prost::Message;
        let bytes = par.encode_to_vec();
        let mut hasher = std::hash::DefaultHasher::new();
        std::hash::Hash::hash(&bytes, &mut hasher);
        (bytes.len(), std::hash::Hasher::finish(&hasher))
    }

    /// SM-6 (E-1 precondition, delta amendment 2026-07-20): the byte-golden of the admitted
    /// **synthetic Lambda-shaped** driver — its `^drive` receiver family `Par` and its full
    /// installed program (β seed + 5 TRS receivers + driver, 7 receives) — captured BEFORE
    /// the E-1 `firing_emission_node` restructure (design v1 §3.3). Every firing arm here is
    /// the β `SubstRewrite`, which emits through `firing_emission_node` with
    /// [`FiringEmission::ContractumRedrive`]; the restructure widens the seam so the
    /// `ScionBundle` variant bypasses the accept, but `ContractumRedrive` MUST stay
    /// byte-for-byte identical. This pin — synthetic-def-stable, unlike the
    /// production-fingerprint-sensitive `a_s5_6` pins — makes that verifiable at the exact
    /// code path E-1 restructures.
    #[test]
    fn sm6_contractum_redrive_synthetic_driver_par_byte_golden() {
        let def = production_lambda_shaped_def();
        let lowered = lowered_for(&def);
        let drive = lowered
            .drive()
            .expect("the Lambda-shaped def is drive-admitted");
        assert_eq!(
            par_fingerprint(drive),
            // ★ #36 S6 RE-CAPTURE (4357, 0xcd74c7d13495d5d5) → (4429, 0x0cfebce014446d5d).
            // EXPLAINED DIFF: INV-S6 scopes every driver-network channel name by the
            // language fingerprint, growing this emission by exactly 2 × 36 bytes (two
            // scope insertions; no name crossed prost's 127-byte varint boundary).
            // PROVEN to be EXACTLY that: inverting `rho_net::scoped_channel_name`'s one
            // scope-insertion line restores (4357, 0xcd74c7d13495d5d5) byte-for-byte.
            // The ContractumRedrive SHAPE this pin guards is unchanged.
            (4429, 936393443138366813),
            "SM-6: the synthetic-Lambda ^drive receiver family (ContractumRedrive) — pin \
             pre-restructure; the E-1 firing_emission_node restructure must keep this exact \
             (E-2-D re-pin: reflected-ABI v2 adds the hereditary-ground marker at index 1)"
        );
        let installed = lowered
            .installed_program_par()
            .expect("the Lambda-shaped def installs");
        assert_eq!(installed.receives.len(), 7, "β seed + 5 TRS + ^drive");
        assert_eq!(
            par_fingerprint(&installed),
            // ★ #36 S3 RE-CAPTURE (12807, 12027684232042018179) → (12824, …). EXPLAINED
            // DIFF: the Peano reflect labels moved into the `^` namespace (`Z`/`S` →
            // `^Z`/`^S`), so every `GPrivate(reflect_tag(fp, Z|S))` tag string in the
            // subst-TRS receivers grew by one byte. The `^drive` family above is
            // UNCHANGED (4357) — it emits no Peano node — which localizes the delta to
            // the TRS half of the installed program. Proof that nothing else moved:
            // inverting S3 at its source (the two constants + the
            // `is_marked_object_label` Peano arm they made redundant) restores this pin
            // and every other byte-identity pin EXACTLY; see the `#36 S3` note on
            // `rho_net_subst_trs::reserved_subst_trs_labels`.
            // ★ #36 S6 RE-CAPTURE (12824, 0x89ea12b54e7c61a0) → (12932, 0x87c0768a017c399d).
            // EXPLAINED DIFF: INV-S6 fingerprint-scoping, exactly 3 × 36 bytes (three scope
            // insertions; no name crossed prost's 127-byte varint boundary). PROVEN by the
            // same inversion as the `^drive` pin above: reverting `scoped_channel_name`'s
            // one scope-insertion line restores (12824, 0x89ea12b54e7c61a0) byte-for-byte.
            // Receive count UNCHANGED at 7 — only names grew.
            (12932, 9781948725751200157),
            "SM-6: the full synthetic-Lambda installed program (ContractumRedrive) — pin \
             pre-restructure; ContractumRedrive byte-identity across the E-1 restructure \
             (E-2-D re-pin: reflected-ABI v2 adds the hereditary-ground marker at index 1)"
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
        let installed = lowered
            .installed_program_par()
            .expect("the renamed def installs");
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
    fn reserved_registry_carries_the_five_drive_labels() {
        // A-S5.5 extends the A-S5.2 four with the per-rule AC-carrier tag PREFIX
        // (`^drive-ac`): reserving the base label keeps the whole `:`-suffixed per-rule
        // family (`"^drive-ac:{RuleLabel}"`) collision-free with user constructors (a
        // Rust `Ident` contains neither `^` nor `:`), and the C2 object-congruence
        // assertion guards the base like every other reserved tag. A-S5.8 extends the
        // registry again (16 → 19) with the `^float` family — the dispatcher rendezvous
        // plus the two satellite tag prefixes (`^float-hoist:{C}` / `^float-merge:{op}`),
        // guarded identically.
        let reserved = crate::rho_net_subst_trs::reserved_subst_trs_labels();
        for label in [
            DRIVE_RESERVED_LABEL,
            DRIVE_ERR_RESERVED_LABEL,
            DRIVE_FUEL_RESERVED_LABEL,
            FIRED_RESERVED_LABEL,
            DRIVE_AC_RESERVED_LABEL,
            crate::rho_net_lower::FLOAT_RESERVED_LABEL,
            crate::rho_net_lower::FLOAT_HOIST_RESERVED_LABEL,
            crate::rho_net_lower::FLOAT_MERGE_RESERVED_LABEL,
        ] {
            assert!(reserved.contains(&label), "the C2 reserved registry must guard {label:?}");
        }
    }

    // ─── A-S5.5: the Ambient AC carrier-ABI arms ─────────────────────────────────────────

    /// The REAL production Ambient definition, reconstructed the production way (the
    /// a_s5c path) — the AC-arm tests run against the exact shipped declarations.
    fn production_ambient_def() -> LanguageDef {
        let source = include_str!("../../languages/src/ambient.rs");
        let start = source.find("language! {").expect("language! block") + "language! {".len();
        let end = source.rfind('}').expect("closing brace");
        crate::reconstruct_language_def(&source[start..end])
            .expect("the production Ambient body must reconstruct")
    }

    /// ★ A-S5.5: production Ambient ADMITS the driver — the exact inversion of the
    /// A-S5.2..A-S5.4b `Unsupported` pin — and its drive program is the `^drive`
    /// receiver plus THREE fixed-channel persistent AC-carrier receivers (one per
    /// admitted AC rule), installed once.
    #[test]
    fn ambient_def_is_drive_admitted_with_the_three_carrier_receivers() {
        let def = production_ambient_def();
        let lowered = lowered_for(&def);
        assert_eq!(
            lowered.drive_admission(),
            &DriveAdmission::Admitted,
            "A-S5.5: production Ambient admits the in-Rho quiescence driver"
        );
        let drive = lowered
            .drive()
            .expect("an admitted language carries the drive program");
        assert_eq!(
            drive.receives.len(),
            4,
            "the Ambient drive program = the ^drive receiver + 3 AC-carrier receivers"
        );
        assert!(
            drive.receives.iter().all(|receive| receive.persistent),
            "every drive-program receiver is persistent"
        );
        // The ^drive receiver listens on the reserved channel; the three carriers on
        // their per-rule reserved channels (deterministic arm order: the nested arms
        // InRule, OutRule — declaration order — then the structural OpenRule).
        let fp = lowered.language_fingerprint.as_str();
        let mut sources: Vec<Par> = drive
            .receives
            .iter()
            .map(|receive| {
                receive.binds[0]
                    .source
                    .clone()
                    .expect("every drive receiver has a ground source")
            })
            .collect();
        let expected = vec![
            tag_par(fp, DRIVE_RESERVED_LABEL),
            tag_par(fp, &drive_ac_carrier_label("InRule")),
            tag_par(fp, &drive_ac_carrier_label("OutRule")),
            tag_par(fp, &drive_ac_carrier_label("OpenRule")),
        ];
        sources.sort_by_key(|par| format!("{par:?}"));
        let mut expected_sorted = expected.clone();
        expected_sorted.sort_by_key(|par| format!("{par:?}"));
        assert_eq!(
            sources, expected_sorted,
            "the drive program's receivers rest on ^drive + the three per-rule carriers"
        );
        // Each carrier receiver binds the 2-value message `carrier!(⟦operand⟧, r)` and
        // carries the non-linear cross-level condition.
        for receive in drive.receives.iter().filter(|receive| {
            receive.binds[0].source.as_ref() != Some(&tag_par(fp, DRIVE_RESERVED_LABEL))
        }) {
            assert_eq!(
                receive.binds[0].patterns.len(),
                2,
                "a carrier receiver binds [operand pattern, out]"
            );
            assert!(
                receive.condition.is_some(),
                "a carrier receiver carries the non-linear Receive.condition"
            );
        }
        // Installed once: 3 legacy AC σ-receivers + the 4 drive-program receivers + the
        // A-S5.8 `^float` family (dispatcher + merge:PPar + 4 hoists + first-time
        // `^shift`/`^cmp` — Ambient carries no subst TRS) = 15.
        let installed = lowered
            .installed_program_par()
            .expect("A-S5.5: production Ambient installs with the driver");
        assert_eq!(
            installed.receives.len(),
            15,
            "installed = InRule + OutRule + OpenRule σ-receivers + ^drive + 3 carriers + \
             the 8 A-S5.8 ^float-family receivers"
        );
    }

    /// ★ A-S5.5 arm transcription (the three production rules): the check pattern binds
    /// exactly the guard-slot pair + the outer rest (free_count 3), the cross-level /
    /// non-linear `EEq` rides `MatchCase.guard`, the carrier label is the reserved
    /// per-rule tag, and the ^drive receiver's Match opens with the three AC redex arms
    /// in the documented order (nested InRule, OutRule; then structural OpenRule) —
    /// GUARDED — before the congruence-descent arms.
    #[test]
    fn ambient_arm_transcription_patterns_guards_and_carrier_wiring() {
        let def = production_ambient_def();
        let fingerprint = "fp-test";
        for (rule_name, expected_label) in [
            ("InRule", "^drive-ac:InRule"),
            ("OutRule", "^drive-ac:OutRule"),
            ("OpenRule", "^drive-ac:OpenRule"),
        ] {
            let rewrite = def
                .rewrites
                .iter()
                .find(|rewrite| rewrite.name == rule_name)
                .expect("the production rule exists");
            let arm = build_drive_ac_arm(rewrite, &def, fingerprint)
                .unwrap_or_else(|error| panic!("{rule_name} must transcribe: {error}"));
            assert_eq!(arm.carrier_label, expected_label, "{rule_name} carrier label");
            assert_eq!(
                arm.free_count, 3,
                "{rule_name}: 2 guard slots (the cross-level / non-linear pair) + the \
                 bound outer rest"
            );
            assert_eq!(
                arm.case_names,
                vec!["__ac0", "__ac1", "__ac2"],
                "{rule_name}: synthetic case-frame names"
            );
            // The guard is the EEq over the two guard slots — case-closed (BoundVar < 3).
            assert!(
                !arm.guard.exprs.is_empty(),
                "{rule_name}: the non-linear guard is a real expression"
            );
            assert_eq!(arm.receiver.receives.len(), 1, "{rule_name}: one carrier receiver");
            let receive = &arm.receiver.receives[0];
            assert!(receive.persistent, "{rule_name}: the carrier receiver is persistent");
            assert_eq!(
                receive.binds[0].source,
                Some(tag_par(fingerprint, expected_label)),
                "{rule_name}: the carrier receiver rests on the reserved per-rule channel"
            );
        }

        // The ^drive receiver's Match arm ORDER over the real lowering: 3 AC redex arms
        // first (each guarded), then the congruence/binder/bag/Nil/passthrough/wildcard
        // arms (unguarded).
        let lowered = lowered_for(&def);
        let drive = lowered.drive().expect("Ambient admits");
        let fp = lowered.language_fingerprint.as_str();
        let drive_receive = drive
            .receives
            .iter()
            .find(|receive| {
                receive.binds[0].source.as_ref() == Some(&tag_par(fp, DRIVE_RESERVED_LABEL))
            })
            .expect("the ^drive receiver is present");
        let body = drive_receive
            .body
            .as_ref()
            .expect("the ^drive receiver has a body");
        let top_match = &body.matches[0];
        // Arms: 3 AC redex + 5 congruence (PZero, PIn, POut, POpen, PAmb) + 1 binder
        // (PNew) + 1 bag (PPar) + 1 Nil + 2 passthroughs + 1 wildcard = 14.
        assert_eq!(top_match.cases.len(), 14, "the Ambient ^drive Match arm count");
        for (index, expect_guard) in [(0, true), (1, true), (2, true), (3, false)] {
            assert_eq!(
                top_match.cases[index].guard.is_some(),
                expect_guard,
                "case {index}: exactly the three leading AC redex arms are guarded"
            );
        }
    }

    /// ★ A-S5.5 AM-3: the three-case bag-fragment dispatch emits EXACTLY the
    /// Nil / same-op-soup / wildcard-wrap cases, in that order (Nil first — the wrap leg
    /// must never see an empty bag).
    #[test]
    fn three_case_bag_fragment_dispatch_shape() {
        let env = Env::root(&["v", "dest"]);
        let node = bag_fragment_dispatch(FP, "PPar", env.var("v"), env.var("dest"));
        assert_eq!(node.par.matches.len(), 1, "the dispatch is one Match");
        let cases = &node.par.matches[0].cases;
        assert_eq!(cases.len(), 3, "Nil / soup / wrap — exactly three cases");
        assert_eq!(
            cases[0].pattern,
            Some(Par::default()),
            "case 0 claims Nil (the empty bag) — splice-as-nothing"
        );
        assert_eq!(
            cases[1].pattern.as_ref(),
            Some(&soup_case_pattern(FP, "PPar")),
            "case 1 claims a same-op soup — compose its sends directly"
        );
        assert_eq!(
            cases[2].pattern.as_ref(),
            Some(&pat_wildcard()),
            "case 2 is the wildcard — wrap one element send"
        );
        // The wrap leg sends `@\"ac:{fingerprint}/PPar\"!(v)` as its datum.
        let wrap_body = cases[2].source.as_ref().expect("wrap body");
        let datum = &wrap_body.sends[0].data[0];
        assert_eq!(datum.sends.len(), 1, "the wrapped fragment is one element send");
        assert_eq!(
            datum.sends[0].chan,
            Some(new_gstring_par(ac_soup_channel(FP, "PPar"), Vec::new(), false)),
            "the wrap rides the op's INV-S6-scoped ac: carrier"
        );
    }

    /// The A-S5.8 constructive-discharge WITNESS def (F8-AM-1a, decision Q-W): a
    /// name-keyed test `LanguageDef` named `Ambient` (DRIVE_OPT_IN unchanged) whose
    /// `Seal` rewrite's RHS introduces a `PNew` over a ν-split `POpen` redex. The LHS is
    /// DEPTH-2 NESTED (the `PAmb N (PPar {Q, ...rest1})` element — the F8-AM-1a step-2
    /// requirement, so the RHS flows through the TEMPLATE path where
    /// `AcReconstructTemplate::Binder` applies); the binder sits at an ELEMENT template
    /// position.
    fn witness_seal_def() -> LanguageDef {
        let fragment = r#"
            name: Ambient,
            types { Proc Name },
            terms {
                PZero . Proc ::= "0" ;
                PSeal . Proc ::= "seal(" Name "," Proc ")" ;
                POpen . Proc ::= "open(" Name "," Proc ")" ;
                PAmb . Proc ::= Name "[" Proc "]" ;
                PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;
                PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
            },
            equations {
                NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));
                ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
                OpenNew . | x # N |- (POpen N (PNew ^x.P)) = (PNew ^x.(POpen N P));
                SealNew . | x # N |- (PSeal N (PNew ^x.P)) = (PNew ^x.(PSeal N P));
                AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
            },
            rewrites {
                Seal . |- (PPar {(PSeal N P), (PAmb N (PPar {Q, ...rest1})), ...rest})
                    ~> (PPar {(PNew ^x.(PPar {(POpen N P)})), (PAmb N (PPar {Q, ...rest1})), ...rest});
                OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
                    ~> (PPar {P, Q, ...rest});
            },
        "#;
        syn::parse_str::<LanguageDef>(fragment).expect("the witness Seal def parses")
    }

    /// ★ A-S5.8 (F8-AM-1b): the witness `Seal` rule takes the fail-closed NO-MATCH-ENTRY
    /// disposition (`NestedStructuralAcBinderTemplated` — recorded, no `Par`, no install
    /// error), the def still INSTALLS, the drive ADMITS it (the conjunct-1 discharge for
    /// driver-transcribable carrier defers), the drive program carries the Seal + OpenRule
    /// carriers, and the `^float` family is installed (the witness is float-bearing).
    #[test]
    fn witness_seal_rule_takes_the_binder_templated_disposition_and_the_drive_admits() {
        let def = witness_seal_def();
        assert!(
            crate::rho_net_float::language_is_float_bearing(&def),
            "the witness def is float-bearing (its equations are all recognized floats)"
        );
        let lowered = lowered_for(&def);
        assert!(
            lowered.errors().is_empty(),
            "the binder-templated disposition pushes NO install error: {:?}",
            lowered.errors()
        );
        let seal = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id().ends_with(":Seal"))
            .expect("the Seal rule lowers");
        assert!(
            matches!(seal, RhoNetLoweredRule::NestedStructuralAcBinderTemplated { .. }),
            "Seal takes the NO-MATCH-ENTRY disposition, got {seal:?}"
        );
        assert!(seal.par().is_none(), "no site-keyed match receiver is built for Seal");
        assert_eq!(
            lowered.drive_admission(),
            &DriveAdmission::Admitted,
            "the drive ADMITS the witness def (the A-S5.8 conjunct-1 discharge)"
        );
        let drive = lowered
            .drive()
            .expect("the witness def carries the drive program");
        assert_eq!(
            drive.receives.len(),
            3,
            "the witness drive program = ^drive + the Seal carrier + the OpenRule carrier"
        );
        let fp = lowered.language_fingerprint.as_str();
        assert!(
            drive.receives.iter().any(|receive| {
                receive.binds[0].source.as_ref()
                    == Some(&tag_par(fp, &drive_ac_carrier_label("Seal")))
            }),
            "the Seal AC carrier rests on its reserved per-rule channel"
        );
        assert!(
            lowered.float().is_some(),
            "the witness def installs the ^float family (float-bearing ∧ admitted)"
        );
        lowered
            .installed_program_par()
            .expect("the witness def INSTALLS (the disposition never blocks the boundary)");
    }

    /// ★ A-S5.8 (F8-AM-1): the Seal carrier's Binder-template rebuild — the carrier
    /// receiver pre-shifts the under-binder σ slots (`N`/`P` at depth 1 — ONE
    /// `^shift(Z, ·)` application each, the F8-AM-1c rule) on fresh channels and emits
    /// the ctor-erased `⌜^lambda⌝` node; the whole-arm transcription carries the
    /// cross-level guard exactly like a binder-free nested rule.
    #[test]
    fn witness_seal_carrier_pre_shifts_the_under_binder_slots() {
        let def = witness_seal_def();
        let rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == "Seal")
            .expect("the Seal rewrite exists");
        let arm = build_drive_ac_arm(rewrite, &def, "fp-witness")
            .expect("the Seal rewrite transcribes to a driver AC-carrier arm");
        assert_eq!(arm.carrier_label, "^drive-ac:Seal");
        assert_eq!(arm.free_count, 3, "2 cross-level guard slots (N × 2) + the bound outer rest");
        assert!(!arm.guard.exprs.is_empty(), "the non-linear guard is real");
        // The carrier receiver: persistent, on the reserved channel, with the shift
        // pre-stage (a `^shift` send appears in its body — the F8-AM-1c σ-slot shifts)
        // and the ctor-erased `^lambda` tag in its rebuild.
        assert_eq!(arm.receiver.receives.len(), 1);
        let receive = &arm.receiver.receives[0];
        assert!(receive.persistent);
        let body_debug = format!("{:?}", receive.body.as_ref().expect("carrier body"));
        let shift_tag =
            format!("{:?}", tag_par("fp-witness", crate::rho_net_lower::SHIFT_RESERVED_LABEL));
        assert!(
            body_debug.contains(&shift_tag),
            "the carrier body pre-shifts under-binder σ slots through ⌜^shift⌝"
        );
        let lambda_tag = format!("{:?}", tag_par("fp-witness", LAMBDA_REFLECT_LABEL));
        assert!(
            body_debug.contains(&lambda_tag),
            "the carrier rebuild emits the ctor-erased ⌜^lambda⌝ node"
        );
    }

    /// A-S5.8 fail-closed (every non-witness shape): a binder at the RHS-bag ROOT is
    /// rejected by `resolve_bag_apply` (the RHS must be bag-rooted), so the rule stays
    /// `Unsupported{CollectionAc}` — recorded loud, never a wrong carrier.
    #[test]
    fn binder_at_the_rhs_root_stays_fail_closed() {
        let fragment = r#"
            name: Ambient,
            types { Proc Name },
            terms {
                PZero . Proc ::= "0" ;
                PSeal . Proc ::= "seal(" Name "," Proc ")" ;
                PAmb . Proc ::= Name "[" Proc "]" ;
                PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;
                PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
            },
            equations {
                ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
                SealNew . | x # N |- (PSeal N (PNew ^x.P)) = (PNew ^x.(PSeal N P));
                AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
            },
            rewrites {
                BadSeal . |- (PPar {(PSeal N P), (PAmb N (PPar {Q, ...rest1})), ...rest})
                    ~> (PNew ^x.(PPar {(PSeal N P), ...rest}));
            },
        "#;
        let def = syn::parse_str::<LanguageDef>(fragment).expect("the bad-shape def parses");
        let lowered = lowered_for(&def);
        let bad = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id().ends_with(":BadSeal"))
            .expect("the BadSeal rule lowers");
        assert!(
            matches!(bad, RhoNetLoweredRule::Unsupported { .. }),
            "a binder at the RHS root is fail-closed Unsupported, got {bad:?}"
        );
        assert!(
            matches!(lowered.drive_admission(), DriveAdmission::Unsupported { .. }),
            "the drive records Unsupported for the untranscribable shape"
        );
    }

    /// A-S5.5: a language with an AC rewrite whose shape is NOT a recognized
    /// structural/nested structural AC form still records `Unsupported` (fail-closed) —
    /// the linear-AC family has no carrier arm.
    #[test]
    fn linear_ac_rewrite_records_unsupported() {
        let fragment = r#"
            name: Ambient,
            types { Elem },
            terms {
                EA . |- "a" : Elem ;
                Bag . Elem ::= HashBag(Elem) sep "|" delim "{" "}" ;
            },
            equations {},
            rewrites {
                Drop . |- (Bag {x, ...rest}) ~> (Bag {...rest}) ;
            },
        "#;
        let def = syn::parse_str::<LanguageDef>(fragment).expect("the linear-AC def parses");
        let lowered = lowered_for(&def);
        match lowered.drive_admission() {
            DriveAdmission::Unsupported { reason } => {
                assert!(
                    reason.contains("Drop") || reason.contains("ac("),
                    "the reason names the linear-AC rewrite or family: {reason}"
                );
            },
            other => panic!("a linear-AC rewrite must stay Unsupported, got {other:?}"),
        }
        assert!(lowered.drive().is_none(), "no partial driver is ever built");
    }
}
