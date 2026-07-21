//! Track B — B3 (fair-comparison hoisting) + B4 (benchmark instrumentation):
//! BENCHMARK-ONLY support for driving the naive Knotted-Topoi Appendix-A
//! baseline against the optimized set-automaton matcher on a live, in-memory,
//! COUNTING f1r3node `RhoRuntime`.
//!
//! # Quarantine (read this first)
//!
//! Everything in this module is compiled ONLY under the `bench-naive-baseline`
//! feature and is referenced ONLY by Track-B benchmarks/tests. There is NO
//! production metering, budget, or cost surface here: budgets remain entirely
//! F1r3node's concern (wallet.txt). The single cost touch in this module is a
//! bench-internal SECONDARY read of `runtime.cost().total_cost()` on the
//! harness's OWN in-memory runtime AFTER `inj` reaches quiescence
//! ([`bench_inj_and_read`]) — a bench-local diagnostic (the consensus unit is
//! one source-token per committed COMM, so the value doubles as an independent
//! COMM count), never a knob, never installed on a production path.
//! `run::inj_on_runtime` and every production entry point are untouched.
//!
//! # B4 — what is instrumented
//!
//! 1. [`CountingSpace`]: an `ISpace` wrapper mirroring `step::SteppingSpace`'s
//!    delegation exactly (every trait method forwarded to the wrapped
//!    `RSpace`), but instead of the stepper's gate/observer it CLASSIFIES the
//!    continuation's channel set of every COMMITTED COMM (the `Some(..)` arms
//!    of `consume` and `produce` — the same extraction as the stepper's
//!    `emit_if_comm`) and bumps `AtomicU64` counters in a shared
//!    [`Arc<CommCounters>`].
//! 2. A delegating COUNTING matcher around the production spatial
//!    [`Matcher`]: the trait-object seam at `RSpace::create(store,
//!    Arc<Box<dyn Match<BindPattern, ListParWithRandom, TaggedContinuation>>>)`
//!    IS wrappable (`rspace_plus_plus::rspace::r#match::Match` is a public
//!    trait with `&self` methods `get` / `check_commit`), so
//!    [`MatchAttemptCounters`] records every spatial match ATTEMPT (`get`
//!    call) and every SUCCESS (`get` returning `Some`); `check_commit`
//!    delegates verbatim so cross-channel guards behave byte-identically. No
//!    fallback path was needed.
//! 3. [`bench_runtime_with_counters`]: the bring-up mirror of `run::
//!    build_runtime` / `step::run_stepped_inj` (`InMemoryStoreManager` →
//!    `RSpace::create` → `create_rho_runtime`) with the counting space +
//!    counting matcher installed.
//! 4. [`bench_inj_and_read`]: the per-run injection helper — phase timers
//!    (`Instant` around build/inj/readback), the emitted program's
//!    `prost::Message::encoded_len`, a recursive `Receive`-node count
//!    ([`count_receive_nodes`]), counter snapshots, and the bench-internal
//!    secondary consumed-cost read described above.
//!
//! # Channel classification (the τ-vs-visible taxonomy)
//!
//! The COMM counters bucket by the continuation's channel set, using the exact
//! channel constructors the emitters share (all provenance in
//! `rholang-codegen`):
//!
//! | channel shape | class | constructor |
//! |---|---|---|
//! | `@"loc:…"` (spread head-tag / location) | `matching_tau` | `spread_root_location` / `spread_child_location` (`rho_net_lower.rs`), `RhoNetChannel::location` (`rho_net.rs`) |
//! | `@"col:…"` (chain collapse) | `matching_tau` | `collapse_chain_location` (`rho_net_lower.rs`) |
//! | `@"cap:…"` (capture collapse) | `matching_tau` | `collapse_capture_location` (`rho_net_lower.rs`) |
//! | `@"sa:…"` (accept / σ-receiver source / native trigger-dispatch, incl. `sa:pattern/…`, `sa:scalar/…`) | `firing_visible` | `RhoNetChannel::set_automaton_trace` (`rho_net.rs`) |
//! | `GPrivate(mettail.term.{fp}.{^subst,^shift,^shiftk,^cmp,^pred})` | `subst_tau` | `tag_par(fp, label)` over the reserved TRS labels (`rho_net_subst_trs.rs`, `rho_net_lower.rs`) |
//! | `GPrivate(mettail.term.{fp}.{^respread,^respread-root,^respread-err})` | `respread_tau` | `respread_reserved_labels()` — the R3 self-driving walker family (`rho_net_naive_kt.rs`; EXPLORATORY, pre-registered) |
//! | `GPrivate(mettail.term.{fp}.^drive)` | `drive_tau` | `tag_par(fp, DRIVE_RESERVED_LABEL)` — the in-Rho quiescence driver's per-node `^drive!(t, fuel, ret)` rendezvous (`rho_net_drive.rs`; E-1 leg 0, the scion-grafting PRIMARY metric). The GString firing-ledger (`^fired:{fp}`) and the typed fail-close channels (`^drive-err:{fp}` / `^drive-fuel:{fp}`) are RESTING PRODUCES — nothing in-Rho consumes them, so they contribute ZERO COMMs and are read back by peek (`run::DriveObservationSet`), never classified here |
//! | `@"ac:…"` (AC bag carrier, bare `ac:{op}` and site-keyed `ac:{loc}/…`) | `ac_carrier` | `ac_carrier_channel` + the `ac:{op}` soup channel (`rho_net_lower.rs`) |
//! | `@"e6a:…"` (E-6a PathMap subject-index / site-enumeration) | `pathmap_index` | `e6a_index_channel` / `e6a_sites_channel` (`e6a_support.rs`; treatment arm only) |
//! | `@"ph:…"` (premise-hole bridge) and `@"loc:…/contextual-premise/…"` (join premise) | `contextual_plumbing` | `contextual_premise_hole_channel` (`rho_net_lower.rs`), the `Premise::Congruence` location channel (`rho_net.rs`) |
//! | `@"{out_channel}"` (the CONFIGURED observation channel) | `observation` | `run::quoted_channel` |
//! | anything else | `other` | counted AND the first [`MAX_UNKNOWN_CHANNEL_SAMPLES`] renderings retained — never silently bucketed |
//!
//! A multi-channel JOIN is classified by the FIRST matching class under the
//! FIXED precedence `SubstTau > RespreadTau > DriveTau > FiringVisible > AcCarrier >
//! PathMapIndex > ContextualPlumbing > MatchingTau > Observation > Other` (the [`Ord`] on
//! [`CommChannelClass`], most specific first; reserved prefixes outrank an
//! `out_channel` that pathologically collides with one), and additionally
//! bumps `join_arity_gt1`. (The three reserved-`GPrivate` classes — `SubstTau`,
//! `RespreadTau`, `DriveTau` — never join with each other OR with any other
//! class: every reserved contract is single-channel — the `^drive` receiver
//! binds `(t, fuel, ret)` from the ONE `^drive` channel, and the scion bundle's
//! k-ary slot join reads only fresh unforgeable returns (class `Other`) — so
//! their relative order is documentation, not behavior.)
//!
//! # Determinism
//!
//! The injection seed is a FIXED byte string ([`BENCH_FIXED_SEED`], the same
//! fixed-bytes pattern as `step::FIXED_SEED`), so a bench trace reproduces
//! bit-identically. (The B2 equivalence suite's `inj_on_runtime` uses the
//! entropy `Blake2b512Random::create_from_length(128)`; its assertions are
//! multiset-sorted so it does not need seed determinism — a benchmark does.)
//!
//! # B3 — fair-comparison hoisting (harness level)
//!
//! [`compile_bench_language`] performs the per-language
//! reconstruct → lower → plan → `compile_in_rho_matching_ruleset` →
//! installed-program chain ONCE and hands back a [`CompiledBenchLanguage`] the
//! harness reuses (`&InRhoMatchingRuleset` + the installed program `Par`)
//! across all iterations — the WARM mode. COLD mode is simply calling
//! [`compile_bench_language`] inside the measured region. The macro-generated
//! production rebuild paths are untouched.

use std::collections::{BTreeSet, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use async_trait::async_trait;

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{
    compile_in_rho_matching_ruleset, lower_language_def, plan_rho_default_backend,
    reconstruct_language_def, respread_reserved_labels, suggest_rejected_rule_dispositions,
    InRhoMatchingRuleset, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence, RhoLowering, CMP_RESERVED_LABEL, DRIVE_RESERVED_LABEL,
    PRED_RESERVED_LABEL, SHIFTK_RESERVED_LABEL, SHIFT_RESERVED_LABEL, SUBST_RESERVED_LABEL,
};
use models::rhoapi::connective::ConnectiveInstance;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::{BindPattern, Expr, ListParWithRandom, Par, TaggedContinuation};
use prost::Message;
use rho_pure_eval::Env;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime, RhoRuntimeImpl};
use rholang::rust::interpreter::system_processes::Definition;
use rspace_plus_plus::rspace::checkpoint::{Checkpoint, SoftCheckpoint};
use rspace_plus_plus::rspace::errors::RSpaceError;
use rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash;
use rspace_plus_plus::rspace::internal::{Datum, Row, WaitingContinuation};
use rspace_plus_plus::rspace::r#match::Match;
use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::rspace_interface::{ISpace, MaybeConsumeResult, MaybeProduceResult};
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;
use rspace_plus_plus::rspace::trace::event::Produce;
use rspace_plus_plus::rspace::trace::Log;

use crate::run::quoted_channel;

/// Deterministic seed for every bench `inj` — the same fixed-bytes pattern as the
/// reactive stepper's `FIXED_SEED` (NOT the entropy `create_from_length`), so a
/// bench COMM trace reproduces bit-identically across runs and machines.
const BENCH_FIXED_SEED: &[u8] =
    b"mettail Track-B naive-vs-optimized matcher bench :: deterministic seed v1 (do not change)";

/// How many UNKNOWN (class `Other`) channel renderings [`CommCounters`] retains
/// for diagnosis. Beyond this bound only the `other` counter grows, so a
/// misclassifying run stays cheap while its first offenders remain readable.
pub const MAX_UNKNOWN_CHANNEL_SAMPLES: usize = 16;

/// The classification of ONE COMM continuation channel (or, by precedence, of a
/// whole continuation channel SET). Declaration order IS the fixed precedence —
/// the derived [`Ord`] makes the most specific class the smallest, so a
/// multi-channel join classifies as `min` over its members (see the module-level
/// classification table).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CommChannelClass {
    /// A reserved de-Bruijn subst-TRS rendezvous channel:
    /// `GPrivate(mettail.term.{fp}.{label})` for `label` ∈
    /// {`^subst`, `^shift`, `^shiftk`, `^cmp`, `^pred`}.
    SubstTau,
    /// A reserved R3 `^respread`-family rendezvous channel (the self-driving
    /// walker; EXPLORATORY, pre-registered): `GPrivate(mettail.term.{fp}.
    /// {label})` for `label` ∈ {`^respread`, `^respread-root`,
    /// `^respread-err`} — one COMM per delivered reduct (the dispatcher) plus
    /// one per re-spread WALKED NODE, so this counter IS the in-session
    /// re-spread volume metric.
    RespreadTau,
    /// A reserved in-Rho quiescence-DRIVER rendezvous channel
    /// `GPrivate(mettail.term.{fp}.^drive)` (E-1 leg 0, the scion-grafting
    /// PRIMARY metric): the persistent `^drive` receiver reads
    /// `^drive!(t, fuel, ret)` here on every node visit — the top-level seed,
    /// each concurrent child descent, each firing arm's contractum re-drive
    /// (control `ContractumRedrive`) or per-slot bud drive + re-check resubmit
    /// (treatment `ScionBundle`). Single-channel by contract, so it never joins.
    /// The GString firing-ledger / typed fail-close channels are resting
    /// produces (zero COMMs) and are peeked from `run::DriveObservationSet`, not
    /// classified here.
    DriveTau,
    /// A `sa:`-prefixed set-automaton trace channel — the accept / σ-receiver
    /// source (`sa:pattern/…`), the native scalar dispatch (`sa:scalar/…`), and
    /// the native locate trigger (`sa:scalar/…/sa-locate`).
    FiringVisible,
    /// An `ac:`-prefixed AC bag-carrier channel (bare `ac:{op}` soup or the
    /// site-keyed `ac:{loc}/{op}` carrier).
    AcCarrier,
    /// An `e6a:`-prefixed PathMap subject-index channel (experiment E-6a,
    /// `e6a_support`): the persistent index (`e6a:idx:…`) and the machine-side
    /// site-enumeration results (`e6a:sites:…`) — the treatment arm's QUERY
    /// COMMs. Never emitted by any production or control-arm path.
    PathMapIndex,
    /// Contextual (congruence) plumbing: the `ph:`-prefixed premise-hole bridge
    /// channel, or a `loc:…/contextual-premise/…` join premise channel.
    ContextualPlumbing,
    /// A `loc:`/`col:`/`cap:` spread-location / collapse channel — the matching
    /// network's internal τ traffic.
    MatchingTau,
    /// The CONFIGURED observation (OUT) channel.
    Observation,
    /// None of the above — counted, and the first
    /// [`MAX_UNKNOWN_CHANNEL_SAMPLES`] renderings are retained for diagnosis.
    Other,
}

/// Shared, lock-free COMM classification counters (one [`Arc`] per counting
/// runtime). Every counter is an `AtomicU64` bumped with `Relaxed` ordering on
/// the reducer's COMM path; the only lock is the bounded unknown-channel
/// diagnostic list, touched only when a COMM classifies [`CommChannelClass::Other`].
#[derive(Debug)]
pub struct CommCounters {
    /// The configured observation channel name this instance classifies as
    /// [`CommChannelClass::Observation`].
    out_channel: String,
    /// COMMs whose continuation reads `loc:`/`col:`/`cap:` spread channels.
    pub matching_tau: AtomicU64,
    /// COMMs whose continuation reads `sa:` accept/σ/trigger channels.
    pub firing_visible: AtomicU64,
    /// COMMs whose continuation reads a reserved subst-TRS tag channel.
    pub subst_tau: AtomicU64,
    /// COMMs whose continuation reads a reserved R3 `^respread`-family channel.
    pub respread_tau: AtomicU64,
    /// COMMs whose continuation reads the reserved `^drive` quiescence-driver
    /// channel (E-1 leg 0, the scion-grafting PRIMARY metric).
    pub drive_tau: AtomicU64,
    /// COMMs whose continuation reads an `ac:` carrier channel.
    pub ac_carrier: AtomicU64,
    /// COMMs whose continuation reads an `e6a:` PathMap subject-index channel
    /// (the E-6a treatment arm's query COMMs).
    pub pathmap_index: AtomicU64,
    /// COMMs whose continuation reads `ph:`/premise contextual channels.
    pub contextual_plumbing: AtomicU64,
    /// COMMs whose continuation reads the configured OUT channel.
    pub observation: AtomicU64,
    /// COMMs whose continuation reads none of the known channel families.
    pub other: AtomicU64,
    /// COMMs whose continuation joined MORE THAN ONE channel (any class).
    pub join_arity_gt1: AtomicU64,
    /// The first [`MAX_UNKNOWN_CHANNEL_SAMPLES`] renderings of channels that
    /// classified [`CommChannelClass::Other`] — retained so an unexpected
    /// channel family is diagnosable, never silently bucketed.
    unknown_channels: Mutex<Vec<String>>,
}

/// A plain-data copy of [`CommCounters`] at one instant (`Debug + Clone`),
/// embedded in [`BenchRunResult`]. Counters are CUMULATIVE over the owning
/// runtime's lifetime; under the intended fresh-runtime-per-rep discipline a
/// post-run snapshot IS the per-run count.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommCounterSnapshot {
    pub matching_tau: u64,
    pub firing_visible: u64,
    pub subst_tau: u64,
    pub respread_tau: u64,
    pub drive_tau: u64,
    pub ac_carrier: u64,
    pub pathmap_index: u64,
    pub contextual_plumbing: u64,
    pub observation: u64,
    pub other: u64,
    pub join_arity_gt1: u64,
    pub unknown_channel_samples: Vec<String>,
}

impl CommCounters {
    /// Fresh zeroed counters classifying `out_channel` as the observation
    /// channel.
    pub fn new(out_channel: &str) -> CommCounters {
        CommCounters {
            out_channel: out_channel.to_string(),
            matching_tau: AtomicU64::new(0),
            firing_visible: AtomicU64::new(0),
            subst_tau: AtomicU64::new(0),
            respread_tau: AtomicU64::new(0),
            drive_tau: AtomicU64::new(0),
            ac_carrier: AtomicU64::new(0),
            pathmap_index: AtomicU64::new(0),
            contextual_plumbing: AtomicU64::new(0),
            observation: AtomicU64::new(0),
            other: AtomicU64::new(0),
            join_arity_gt1: AtomicU64::new(0),
            unknown_channels: Mutex::new(Vec::with_capacity(MAX_UNKNOWN_CHANNEL_SAMPLES)),
        }
    }

    /// Classify ONE channel `Par` against the module-level table. Public so the
    /// in-module tests (and a future harness's ad-hoc probes) can exercise the
    /// taxonomy directly.
    pub fn classify_channel(&self, channel: &Par) -> CommChannelClass {
        if let Some(name) = quoted_string_channel_name(channel) {
            // Reserved prefixes take precedence over the configured OUT name, so
            // an out_channel that pathologically collides with a reserved prefix
            // never absorbs matching traffic (fixed, documented precedence).
            if name.starts_with("sa:") {
                CommChannelClass::FiringVisible
            } else if name.starts_with("ac:") {
                CommChannelClass::AcCarrier
            } else if name.starts_with("e6a:") {
                CommChannelClass::PathMapIndex
            } else if name.starts_with("ph:") {
                CommChannelClass::ContextualPlumbing
            } else if name.starts_with("loc:") {
                // A contextual JOIN's premise channels are `loc:`-prefixed
                // location channels whose path carries the `contextual-premise`
                // segment (`rho_net.rs`, `Premise::Congruence`): classify them
                // as contextual plumbing BEFORE the generic `loc:` bucket.
                if name.contains("/contextual-premise/") {
                    CommChannelClass::ContextualPlumbing
                } else {
                    CommChannelClass::MatchingTau
                }
            } else if name.starts_with("cap:") || name.starts_with("col:") {
                CommChannelClass::MatchingTau
            } else if name == self.out_channel {
                CommChannelClass::Observation
            } else {
                CommChannelClass::Other
            }
        } else if let Some(tag) = private_channel_tag(channel) {
            if is_subst_trs_channel_tag(&tag) {
                CommChannelClass::SubstTau
            } else if is_respread_channel_tag(&tag) {
                CommChannelClass::RespreadTau
            } else if is_drive_channel_tag(&tag) {
                CommChannelClass::DriveTau
            } else {
                CommChannelClass::Other
            }
        } else {
            CommChannelClass::Other
        }
    }

    /// Record ONE committed COMM given its continuation's channel set: bump the
    /// class counter selected by the fixed precedence (`min` over the members'
    /// classes — see [`CommChannelClass`]), bump `join_arity_gt1` when the
    /// continuation joined more than one channel, and retain a rendering for
    /// every member that classified [`CommChannelClass::Other`] (bounded by
    /// [`MAX_UNKNOWN_CHANNEL_SAMPLES`]).
    pub fn record_comm(&self, channels: &[Par]) {
        if channels.len() > 1 {
            self.join_arity_gt1.fetch_add(1, Ordering::Relaxed);
        }
        let mut comm_class = CommChannelClass::Other;
        for channel in channels {
            let class = self.classify_channel(channel);
            if class == CommChannelClass::Other {
                self.retain_unknown_channel(channel);
            }
            comm_class = comm_class.min(class);
        }
        let counter = match comm_class {
            CommChannelClass::SubstTau => &self.subst_tau,
            CommChannelClass::RespreadTau => &self.respread_tau,
            CommChannelClass::DriveTau => &self.drive_tau,
            CommChannelClass::FiringVisible => &self.firing_visible,
            CommChannelClass::AcCarrier => &self.ac_carrier,
            CommChannelClass::PathMapIndex => &self.pathmap_index,
            CommChannelClass::ContextualPlumbing => &self.contextual_plumbing,
            CommChannelClass::MatchingTau => &self.matching_tau,
            CommChannelClass::Observation => &self.observation,
            CommChannelClass::Other => &self.other,
        };
        counter.fetch_add(1, Ordering::Relaxed);
    }

    fn retain_unknown_channel(&self, channel: &Par) {
        let mut samples = self
            .unknown_channels
            .lock()
            .expect("unknown-channel diagnostic list lock");
        if samples.len() < MAX_UNKNOWN_CHANNEL_SAMPLES {
            samples.push(render_channel_for_diagnosis(channel));
        }
    }

    /// A plain-data copy of the current counter values (Relaxed loads) plus the
    /// retained unknown-channel renderings.
    pub fn snapshot(&self) -> CommCounterSnapshot {
        CommCounterSnapshot {
            matching_tau: self.matching_tau.load(Ordering::Relaxed),
            firing_visible: self.firing_visible.load(Ordering::Relaxed),
            subst_tau: self.subst_tau.load(Ordering::Relaxed),
            respread_tau: self.respread_tau.load(Ordering::Relaxed),
            drive_tau: self.drive_tau.load(Ordering::Relaxed),
            ac_carrier: self.ac_carrier.load(Ordering::Relaxed),
            pathmap_index: self.pathmap_index.load(Ordering::Relaxed),
            contextual_plumbing: self.contextual_plumbing.load(Ordering::Relaxed),
            observation: self.observation.load(Ordering::Relaxed),
            other: self.other.load(Ordering::Relaxed),
            join_arity_gt1: self.join_arity_gt1.load(Ordering::Relaxed),
            unknown_channel_samples: self
                .unknown_channels
                .lock()
                .expect("unknown-channel diagnostic list lock")
                .clone(),
        }
    }
}

/// The quoted-`GString` name of a channel `Par` (`@"name"` — the shape
/// `run::quoted_channel` and every string-channel emitter produce), if it is
/// exactly a single-`GString` expression. Lenient on the remaining `Par`
/// fields: the emitters only ever produce pure quoted string channels, and a
/// hybrid channel would be a codegen bug this module reports through the
/// unknown-channel diagnostics rather than a hard failure.
fn quoted_string_channel_name(channel: &Par) -> Option<&str> {
    match channel.exprs.as_slice() {
        [expr] => match &expr.expr_instance {
            Some(ExprInstance::GString(name)) => Some(name.as_str()),
            _ => None,
        },
        _ => None,
    }
}

/// The decoded UTF-8 tag of a single-`GPrivate` unforgeable channel built by
/// `GPrivateBuilder::new_par_from_string(tag)` (which sets `id ==
/// <String as prost::Message>::encode_to_vec()`, so `String::decode` is its
/// exact inverse — the same recovery as `run::private_name_tag`). `None` for
/// any other shape or an undecodable id (e.g. a runtime `new`-allocated fresh
/// name).
fn private_channel_tag(channel: &Par) -> Option<String> {
    if !channel.exprs.is_empty() {
        return None;
    }
    let [unforgeable] = channel.unforgeables.as_slice() else {
        return None;
    };
    match unforgeable.unf_instance.as_ref()? {
        UnfInstance::GPrivateBody(value) => String::decode(value.id.as_slice()).ok(),
        _ => None,
    }
}

/// Whether a decoded `GPrivate` tag names one of the FIVE reserved subst-TRS
/// rendezvous channels: `mettail.term.{fp}.{label}` with `label` ∈
/// {`^subst`, `^shift`, `^shiftk`, `^cmp`, `^pred`} (`^sb`/`^shb` are reserved
/// labels but have NO standalone channel — their dispatch arms are inlined in
/// the `^subst`/`^shift` receivers — so they are deliberately not listed).
fn is_subst_trs_channel_tag(tag: &str) -> bool {
    let Some(suffix) = tag.strip_prefix(crate::REFLECTED_TERM_ABI_PREFIX) else {
        return false;
    };
    let Some((_fingerprint, label)) = suffix.rsplit_once('.') else {
        return false;
    };
    matches!(
        label,
        _ if label == SUBST_RESERVED_LABEL
            || label == SHIFT_RESERVED_LABEL
            || label == SHIFTK_RESERVED_LABEL
            || label == CMP_RESERVED_LABEL
            || label == PRED_RESERVED_LABEL
    )
}

/// Whether a decoded `GPrivate` tag names one of the THREE reserved R3
/// `^respread`-family rendezvous channels: `mettail.term.{fp}.{label}` with
/// `label` ∈ {`^respread`, `^respread-root`, `^respread-err`}
/// (`respread_reserved_labels()` in `rho_net_naive_kt.rs` — the self-driving
/// walker family; `^respread-err` has no receiver on any sound run, so a COMM
/// classifying through it would itself be diagnostic).
fn is_respread_channel_tag(tag: &str) -> bool {
    let Some(suffix) = tag.strip_prefix(crate::REFLECTED_TERM_ABI_PREFIX) else {
        return false;
    };
    let Some((_fingerprint, label)) = suffix.rsplit_once('.') else {
        return false;
    };
    respread_reserved_labels().contains(&label)
}

/// Whether a decoded `GPrivate` tag names the reserved in-Rho quiescence-driver
/// rendezvous channel `mettail.term.{fp}.^drive` (E-1 leg 0). Matches the base
/// [`DRIVE_RESERVED_LABEL`] EXACTLY — the per-rule AC-carrier family
/// (`^drive-ac:{RuleLabel}`, whose full label survives the last-`.` split intact
/// because it carries no `.`) is DELIBERATELY not matched here: it is AC firing
/// traffic re-pinned with the W-D Ambient cells (A-S5.5), not the structural
/// `^drive` descent the L2 cells measure, so it stays `Other` until that leg
/// classifies it. The GString observation channels (`^drive-err:`/`^drive-fuel:`/
/// `^fired:`) are NOT `GPrivate` and never reach this helper — they are resting
/// produces read back by peek, never COMM channels.
fn is_drive_channel_tag(tag: &str) -> bool {
    let Some(suffix) = tag.strip_prefix(crate::REFLECTED_TERM_ABI_PREFIX) else {
        return false;
    };
    let Some((_fingerprint, label)) = suffix.rsplit_once('.') else {
        return false;
    };
    label == DRIVE_RESERVED_LABEL
}

/// A compact, printer-free rendering of a channel for the unknown-channel
/// diagnostics (f1r3node's `PrettyPrinter` is recursive and not stack-safe, so
/// it is deliberately not used on the reducer path).
fn render_channel_for_diagnosis(channel: &Par) -> String {
    if let Some(name) = quoted_string_channel_name(channel) {
        return format!("@\"{name}\"");
    }
    if let Some(tag) = private_channel_tag(channel) {
        return format!("gprivate:{tag}");
    }
    if let [unforgeable] = channel.unforgeables.as_slice() {
        if let Some(UnfInstance::GPrivateBody(value)) = unforgeable.unf_instance.as_ref() {
            let prefix: String = value
                .id
                .iter()
                .take(8)
                .map(|byte| format!("{byte:02x}"))
                .collect();
            return format!("gprivate:0x{prefix}…");
        }
    }
    let rendered = format!("{channel:?}");
    rendered.chars().take(160).collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// CountingSpace — the ISpace wrapper (SteppingSpace's delegation, counting
// instead of gating)
// ─────────────────────────────────────────────────────────────────────────────

/// An `ISpace` wrapper around the live `RSpace` that mirrors
/// `step::SteppingSpace`'s delegation EXACTLY (every trait method forwarded)
/// but, instead of the stepper's gate/observer, classifies the continuation's
/// channel set of every COMMITTED COMM (the `Some(..)` consume-result and
/// produce-result arms — the same extraction as the stepper's `emit_if_comm`)
/// into the shared [`CommCounters`]. `install` results are NOT counted,
/// mirroring the stepper: bootstrap system-process installs are not reduction
/// COMMs.
#[derive(Clone)]
pub struct CountingSpace {
    inner: RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
    counters: Arc<CommCounters>,
}

#[async_trait]
impl ISpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> for CountingSpace {
    async fn create_checkpoint(&self) -> Result<Checkpoint, RSpaceError> {
        self.inner.create_checkpoint().await
    }

    async fn get_data(&self, channel: &Par) -> Vec<Datum<ListParWithRandom>> {
        self.inner.get_data(channel).await
    }

    async fn get_waiting_continuations(
        &self,
        channels: Vec<Par>,
    ) -> Vec<WaitingContinuation<BindPattern, TaggedContinuation>> {
        self.inner.get_waiting_continuations(channels).await
    }

    async fn get_joins(&self, channel: Par) -> Vec<Vec<Par>> {
        self.inner.get_joins(channel).await
    }

    async fn remove_all_data(&self, channel: &Par) -> Result<(), RSpaceError> {
        self.inner.remove_all_data(channel).await
    }

    async fn remove_all_continuations(&self, channels: Vec<Par>) -> Result<(), RSpaceError> {
        self.inner.remove_all_continuations(channels).await
    }

    async fn clear(&self) -> Result<(), RSpaceError> {
        self.inner.clear().await
    }

    async fn get_root(&self) -> Blake2b256Hash {
        self.inner.get_root().await
    }

    async fn reset(&self, root: &Blake2b256Hash) -> Result<(), RSpaceError> {
        self.inner.reset(root).await
    }

    async fn consume_result(
        &self,
        channel: Vec<Par>,
        pattern: Vec<BindPattern>,
    ) -> Result<Option<(TaggedContinuation, Vec<ListParWithRandom>)>, RSpaceError> {
        self.inner.consume_result(channel, pattern).await
    }

    async fn to_map(
        &self,
    ) -> HashMap<Vec<Par>, Row<BindPattern, ListParWithRandom, TaggedContinuation>> {
        self.inner.to_map().await
    }

    async fn create_soft_checkpoint(
        &self,
    ) -> SoftCheckpoint<Par, BindPattern, ListParWithRandom, TaggedContinuation> {
        self.inner.create_soft_checkpoint().await
    }

    async fn take_event_log(&self) -> Log {
        self.inner.take_event_log().await
    }

    async fn revert_to_soft_checkpoint(
        &self,
        checkpoint: SoftCheckpoint<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
    ) -> Result<(), RSpaceError> {
        self.inner.revert_to_soft_checkpoint(checkpoint).await
    }

    async fn consume(
        &self,
        channels: Vec<Par>,
        patterns: Vec<BindPattern>,
        continuation: TaggedContinuation,
        persist: bool,
        peeks: BTreeSet<i32>,
    ) -> Result<
        MaybeConsumeResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
        RSpaceError,
    > {
        let result = self
            .inner
            .consume(channels, patterns, continuation, persist, peeks)
            .await?;
        if let Some((continuation, _matched)) = &result {
            self.counters.record_comm(&continuation.channels);
        }
        Ok(result)
    }

    async fn produce(
        &self,
        channel: Par,
        data: ListParWithRandom,
        persist: bool,
    ) -> Result<
        MaybeProduceResult<Par, BindPattern, ListParWithRandom, TaggedContinuation>,
        RSpaceError,
    > {
        let result = self.inner.produce(channel, data, persist).await?;
        if let Some((continuation, _matched, _produce)) = &result {
            self.counters.record_comm(&continuation.channels);
        }
        Ok(result)
    }

    async fn install(
        &self,
        channels: Vec<Par>,
        patterns: Vec<BindPattern>,
        continuation: TaggedContinuation,
    ) -> Result<Option<(TaggedContinuation, Vec<ListParWithRandom>)>, RSpaceError> {
        self.inner.install(channels, patterns, continuation).await
    }

    async fn rig_and_reset(&self, start_root: Blake2b256Hash, log: Log) -> Result<(), RSpaceError> {
        self.inner.rig_and_reset(start_root, log).await
    }

    async fn rig(&self, log: Log) -> Result<(), RSpaceError> {
        self.inner.rig(log).await
    }

    async fn check_replay_data(&self) -> Result<(), RSpaceError> {
        self.inner.check_replay_data().await
    }

    async fn is_replay(&self) -> bool {
        self.inner.is_replay().await
    }

    async fn update_produce(&self, produce: Produce) {
        self.inner.update_produce(produce).await
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Match-attempt counting (the RSpace matcher seam)
// ─────────────────────────────────────────────────────────────────────────────

/// Shared spatial-match attempt counters. The seam WORKS: `RSpace::create`
/// accepts `Arc<Box<dyn Match<BindPattern, ListParWithRandom,
/// TaggedContinuation>>>` and `rspace_plus_plus::rspace::r#match::Match` is a
/// public trait with `&self` methods, so the production [`Matcher`] is wrapped
/// by a delegating counter (no fallback needed). `attempts` counts every
/// `Match::get` call (one per (pattern, datum) spatial trial); `successes`
/// counts the `Some` returns.
#[derive(Debug, Clone, Default)]
pub struct MatchAttemptCounters {
    attempts: Arc<AtomicU64>,
    successes: Arc<AtomicU64>,
}

/// A plain-data copy of [`MatchAttemptCounters`] at one instant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MatchAttemptSnapshot {
    pub attempts: u64,
    pub successes: u64,
}

impl MatchAttemptCounters {
    /// A plain-data copy of the current attempt/success counts (Relaxed loads).
    pub fn snapshot(&self) -> MatchAttemptSnapshot {
        MatchAttemptSnapshot {
            attempts: self.attempts.load(Ordering::Relaxed),
            successes: self.successes.load(Ordering::Relaxed),
        }
    }
}

/// The delegating counting matcher installed at `RSpace::create`: forwards
/// `get` to the production spatial [`Matcher`] (counting attempts/successes)
/// and `check_commit` verbatim (cross-channel `where`-clause guards behave
/// byte-identically — a guard veto is NOT a spatial-match failure and is
/// deliberately not counted).
struct CountingMatcher {
    inner: Matcher,
    counters: MatchAttemptCounters,
}

impl Match<BindPattern, ListParWithRandom, TaggedContinuation> for CountingMatcher {
    // EPathMap fix P4.2 coupling (f1r3node-rust-mettail fix/epathmap-value-handling):
    // the `Match` trait is borrowed — `get(&P, &A)`, `check_commit(&K, &[&A])`.
    // Pure signature adaptation; the delegation and the counting semantics are
    // unchanged (a guard veto is still not counted as a spatial-match failure).
    fn get(&self, pattern: &BindPattern, data: &ListParWithRandom) -> Option<ListParWithRandom> {
        self.counters.attempts.fetch_add(1, Ordering::Relaxed);
        let result = self.inner.get(pattern, data);
        if result.is_some() {
            self.counters.successes.fetch_add(1, Ordering::Relaxed);
        }
        result
    }

    fn check_commit(&self, k: &TaggedContinuation, matched: &[&ListParWithRandom]) -> bool {
        self.inner.check_commit(k, matched)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Bench runtime bring-up + per-run injection
// ─────────────────────────────────────────────────────────────────────────────

/// Build a COUNTING in-memory `RhoRuntime`: the exact
/// `InMemoryStoreManager` → `RSpace::create` → `create_rho_runtime` sequence of
/// `run::build_runtime` / `step::run_stepped_inj`, with [`CountingSpace`]
/// wrapped around the live `RSpace` and the counting matcher installed at the
/// `RSpace::create` seam. `out_channel` is the observation channel the COMM
/// classifier buckets as [`CommChannelClass::Observation`];
/// `extra_system_processes` mirrors the Tier-3 fold-contract parameter of the
/// production bring-up (empty for the Track-B workloads).
///
/// Returns the runtime plus the two shared counter handles. The intended
/// discipline is ONE runtime per benchmark rep (the equivalence tests likewise
/// run each drive on a fresh runtime), so post-run snapshots are per-run counts.
pub async fn bench_runtime_with_counters(
    mut extra_system_processes: Vec<Definition>,
    out_channel: &str,
) -> Result<(RhoRuntimeImpl, Arc<CommCounters>, MatchAttemptCounters), String> {
    let comm_counters = Arc::new(CommCounters::new(out_channel));
    let match_counters = MatchAttemptCounters::default();

    let mut kvm = InMemoryStoreManager::new();
    let store = kvm
        .r_space_stores()
        .await
        .map_err(|e| format!("in-mem store: {e:?}"))?;
    let inner: RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> = RSpace::create(
        store,
        Arc::new(Box::new(CountingMatcher {
            inner: Matcher,
            counters: match_counters.clone(),
        })),
    )
    .map_err(|e| format!("rspace: {e:?}"))?;
    let space = CountingSpace { inner, counters: comm_counters.clone() };

    let runtime = create_rho_runtime(
        space,
        Arc::new(HashMap::new()), // mergeable tags: none (single-node eval)
        false,                    // init_registry: not needed for bench workloads
        &mut extra_system_processes,
        ExternalServices::noop(), // inert — no ChromaDB/SBERT/OpenAI
    )
    .await;
    Ok((runtime, comm_counters, match_counters))
}

/// Workload identity carried on every [`BenchRunResult`] so a JSON-lines log is
/// self-describing: workload `name`, which `matcher` ran
/// (`"optimized"`/`"naive"`), the naive guard `encoding`
/// (`"pattern-guard"`/`"consume-test"`, or `"-"` for the optimized side), the
/// size parameter `n`, and the repetition index `rep`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BenchWorkloadParams {
    pub name: String,
    pub matcher: String,
    pub encoding: String,
    pub n: u64,
    pub rep: u64,
}

/// One benchmark run's plain-data record (`Debug + Clone`; serde is NOT a
/// dependency of this crate, so [`BenchRunResult::to_json_line`] is the
/// hand-rolled serializer).
#[derive(Debug, Clone)]
pub struct BenchRunResult {
    /// The workload identity this run executed.
    pub workload: BenchWorkloadParams,
    /// Pre-`inj` preparation on the live runtime: soft-checkpoint creation +
    /// budget reset + seed derivation (the runtime BRING-UP is timed by the
    /// harness around [`bench_runtime_with_counters`], outside this record).
    pub build: Duration,
    /// The `inj` reduction to quiescence — the measured region proper.
    pub inj: Duration,
    /// The post-quiescence observation-channel `get_data` read.
    pub readback: Duration,
    /// `prost::Message::encoded_len` of the injected program `Par`.
    pub program_encoded_len: usize,
    /// Recursive `Receive`-node count of the injected program
    /// ([`count_receive_nodes`]) — the installed-network volume metric.
    pub program_receiver_count: usize,
    /// The raw `Par` values resting on the readback channel at quiescence (the
    /// same channel-scoped read as `run::read_ground_from_runtime`, undecoded so
    /// this module needs no observation-report feature). Excluded from
    /// [`Self::to_json_line`], which carries `observed_count` instead.
    pub observed: Vec<Par>,
    /// Bench-internal SECONDARY consumed-cost read:
    /// `runtime.cost().total_cost().value` after `inj` on the harness's OWN
    /// in-memory runtime — consumed source-token units, i.e. one per committed
    /// COMM (f1r3node DR-9), read at quiescence. Bench-local diagnostic ONLY;
    /// budgets are F1r3node's (wallet.txt), and no production path is touched.
    pub consumed_cost_units: i64,
    /// COMM classification counters at readback time (cumulative for the
    /// runtime; per-run under the fresh-runtime-per-rep discipline).
    pub comm: CommCounterSnapshot,
    /// Spatial-match attempt counters at readback time.
    pub matches: MatchAttemptSnapshot,
}

impl BenchRunResult {
    /// Serialize this record as one JSON object line (hand-rolled — serde is
    /// not a dependency of `rholang-runtime`). `observed` is summarized as
    /// `observed_count`; durations are integer nanoseconds.
    pub fn to_json_line(&self) -> String {
        let samples = &self.comm.unknown_channel_samples;
        let mut line = String::with_capacity(512 + 64 * samples.len());
        line.push_str("{\"workload\":{\"name\":\"");
        escape_json_into(&self.workload.name, &mut line);
        line.push_str("\",\"matcher\":\"");
        escape_json_into(&self.workload.matcher, &mut line);
        line.push_str("\",\"encoding\":\"");
        escape_json_into(&self.workload.encoding, &mut line);
        line.push_str("\",\"n\":");
        line.push_str(&self.workload.n.to_string());
        line.push_str(",\"rep\":");
        line.push_str(&self.workload.rep.to_string());
        line.push_str("},\"build_ns\":");
        line.push_str(&self.build.as_nanos().to_string());
        line.push_str(",\"inj_ns\":");
        line.push_str(&self.inj.as_nanos().to_string());
        line.push_str(",\"readback_ns\":");
        line.push_str(&self.readback.as_nanos().to_string());
        line.push_str(",\"program_encoded_len\":");
        line.push_str(&self.program_encoded_len.to_string());
        line.push_str(",\"program_receiver_count\":");
        line.push_str(&self.program_receiver_count.to_string());
        line.push_str(",\"observed_count\":");
        line.push_str(&self.observed.len().to_string());
        line.push_str(",\"consumed_cost_units\":");
        line.push_str(&self.consumed_cost_units.to_string());
        line.push_str(",\"comm\":{\"matching_tau\":");
        line.push_str(&self.comm.matching_tau.to_string());
        line.push_str(",\"firing_visible\":");
        line.push_str(&self.comm.firing_visible.to_string());
        line.push_str(",\"subst_tau\":");
        line.push_str(&self.comm.subst_tau.to_string());
        line.push_str(",\"respread_tau\":");
        line.push_str(&self.comm.respread_tau.to_string());
        line.push_str(",\"drive_tau\":");
        line.push_str(&self.comm.drive_tau.to_string());
        line.push_str(",\"ac_carrier\":");
        line.push_str(&self.comm.ac_carrier.to_string());
        line.push_str(",\"pathmap_index\":");
        line.push_str(&self.comm.pathmap_index.to_string());
        line.push_str(",\"contextual_plumbing\":");
        line.push_str(&self.comm.contextual_plumbing.to_string());
        line.push_str(",\"observation\":");
        line.push_str(&self.comm.observation.to_string());
        line.push_str(",\"other\":");
        line.push_str(&self.comm.other.to_string());
        line.push_str(",\"join_arity_gt1\":");
        line.push_str(&self.comm.join_arity_gt1.to_string());
        line.push_str(",\"unknown_channel_samples\":[");
        for (index, sample) in samples.iter().enumerate() {
            if index > 0 {
                line.push(',');
            }
            line.push('"');
            escape_json_into(sample, &mut line);
            line.push('"');
        }
        line.push_str("]},\"matches\":{\"attempts\":");
        line.push_str(&self.matches.attempts.to_string());
        line.push_str(",\"successes\":");
        line.push_str(&self.matches.successes.to_string());
        line.push_str("}}");
        line
    }
}

/// Append `value` to `out` with JSON string escaping (quote, backslash, and
/// control characters).
fn escape_json_into(value: &str, out: &mut String) {
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            },
            c => out.push(c),
        }
    }
}

/// Inject `program` on a counting runtime and read the resting values back —
/// one benchmark REP, mirroring `run::inj_on_runtime` +
/// `run::read_ground_from_runtime` with instrumentation:
///
/// * phase timers (`Instant`): `build` = pre-`inj` preparation (soft
///   checkpoint + budget reset + seed), `inj` = the reduction to quiescence,
///   `readback` = the observation-channel `get_data`;
/// * `program_encoded_len` (`prost::Message::encoded_len`) and
///   `program_receiver_count` ([`count_receive_nodes`]) of the injected `Par`;
/// * the [`CommCounters`]/[`MatchAttemptCounters`] snapshots at readback time
///   (pass the handles returned by [`bench_runtime_with_counters`]);
/// * the bench-internal SECONDARY consumed-cost read
///   (`runtime.cost().total_cost().value` after `inj`) — bench-local
///   diagnostic only; budgets are F1r3node's.
///
/// `out_channel` is the READBACK channel (normally the same OUT name the
/// counters classify as observation; the in-module counting test deliberately
/// reads a forwarder's channel instead, to exercise an observation COMM). The
/// budget reset mirrors `inj_on_runtime`'s `Cost::unsafe_max()` (that function
/// is deliberately untouched); the seed is the FIXED [`BENCH_FIXED_SEED`]. On
/// an `inj` error the soft checkpoint is reverted and the error surfaced.
pub async fn bench_inj_and_read<R: RhoRuntime>(
    runtime: &mut R,
    program: &Par,
    out_channel: &str,
    workload: BenchWorkloadParams,
    comm_counters: &CommCounters,
    match_counters: &MatchAttemptCounters,
) -> Result<BenchRunResult, String> {
    let program_encoded_len = program.encoded_len();
    let program_receiver_count = count_receive_nodes(program);

    let build_started = Instant::now();
    let checkpoint = runtime.create_soft_checkpoint().await;
    runtime.cost().set(Cost::unsafe_max());
    let rand = Blake2b512Random::create_from_bytes(BENCH_FIXED_SEED);
    let build = build_started.elapsed();

    let inj_started = Instant::now();
    if let Err(err) = runtime.inj(program.clone(), Env::new(), rand).await {
        runtime.revert_to_soft_checkpoint(checkpoint).await;
        return Err(format!("inj: {err:?}"));
    }
    let inj = inj_started.elapsed();

    // Bench-internal SECONDARY consumed-cost read (see the struct field's
    // rustdoc): total_cost() reconciles at quiescence, strictly after inj.
    let consumed_cost_units = runtime.cost().total_cost().value;

    let readback_started = Instant::now();
    let channel = quoted_channel(out_channel);
    let data = runtime.get_data(&channel).await;
    let mut observed: Vec<Par> =
        Vec::with_capacity(data.iter().map(|datum| datum.a.pars.len()).sum());
    for datum in data {
        // EPathMap fix P4.1 coupling: Datum.a is Arc-shared — materialize
        // the readback (cold path, once per run).
        for par in std::sync::Arc::unwrap_or_clone(datum.a).pars {
            observed.push(par);
        }
    }
    let readback = readback_started.elapsed();

    Ok(BenchRunResult {
        workload,
        build,
        inj,
        readback,
        program_encoded_len,
        program_receiver_count,
        observed,
        consumed_cost_units,
        comm: comm_counters.snapshot(),
        matches: match_counters.snapshot(),
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Receive-node visitor
// ─────────────────────────────────────────────────────────────────────────────

/// Count every `Receive` node in `par`, recursively — the installed-network
/// volume metric (the naive Appendix-A scheme's per-rule/per-site duplication
/// shows up directly here). The walk is STRUCTURAL and total over every
/// `Par`-carrying field: sends (channel + data), receives (self + bind
/// patterns/sources + condition + body), news, matches (target + case
/// pattern/source/guard), bundles, conditionals, `ConnAnd`/`ConnOr`/`ConnNot`
/// connective bodies, and every expression that carries `Par` operands
/// (collections, method calls, unary/binary operators).
pub fn count_receive_nodes(par: &Par) -> usize {
    let mut count = 0usize;
    visit_par(par, &mut count);
    count
}

fn visit_opt_par(par: &Option<Par>, count: &mut usize) {
    if let Some(par) = par {
        visit_par(par, count);
    }
}

fn visit_par(par: &Par, count: &mut usize) {
    for send in &par.sends {
        visit_opt_par(&send.chan, count);
        for datum in &send.data {
            visit_par(datum, count);
        }
    }
    for receive in &par.receives {
        *count += 1;
        for bind in &receive.binds {
            for pattern in &bind.patterns {
                visit_par(pattern, count);
            }
            visit_opt_par(&bind.source, count);
        }
        visit_opt_par(&receive.body, count);
        visit_opt_par(&receive.condition, count);
    }
    for new in &par.news {
        visit_opt_par(&new.p, count);
    }
    for expr in &par.exprs {
        visit_expr(expr, count);
    }
    for match_node in &par.matches {
        visit_opt_par(&match_node.target, count);
        for case in &match_node.cases {
            visit_opt_par(&case.pattern, count);
            visit_opt_par(&case.source, count);
            visit_opt_par(&case.guard, count);
        }
    }
    for bundle in &par.bundles {
        visit_opt_par(&bundle.body, count);
    }
    for connective in &par.connectives {
        match connective.connective_instance.as_ref() {
            Some(ConnectiveInstance::ConnAndBody(body))
            | Some(ConnectiveInstance::ConnOrBody(body)) => {
                for p in &body.ps {
                    visit_par(p, count);
                }
            },
            Some(ConnectiveInstance::ConnNotBody(p)) => visit_par(p, count),
            _ => {},
        }
    }
    for conditional in &par.conditionals {
        visit_opt_par(&conditional.condition, count);
        visit_opt_par(&conditional.if_true, count);
        visit_opt_par(&conditional.if_false, count);
    }
}

fn visit_expr(expr: &Expr, count: &mut usize) {
    let Some(instance) = expr.expr_instance.as_ref() else {
        return;
    };
    match instance {
        ExprInstance::EListBody(list) => {
            for p in &list.ps {
                visit_par(p, count);
            }
        },
        ExprInstance::ETupleBody(tuple) => {
            for p in &tuple.ps {
                visit_par(p, count);
            }
        },
        ExprInstance::ESetBody(set) => {
            for p in &set.ps {
                visit_par(p, count);
            }
        },
        ExprInstance::EPathmapBody(pathmap) => {
            for p in &pathmap.ps {
                visit_par(p, count);
            }
        },
        ExprInstance::EZipperBody(zipper) => {
            if let Some(pathmap) = &zipper.pathmap {
                for p in &pathmap.ps {
                    visit_par(p, count);
                }
            }
        },
        ExprInstance::EMapBody(map) => {
            for pair in &map.kvs {
                visit_opt_par(&pair.key, count);
                visit_opt_par(&pair.value, count);
            }
        },
        ExprInstance::EMethodBody(method) => {
            visit_opt_par(&method.target, count);
            for argument in &method.arguments {
                visit_par(argument, count);
            }
        },
        ExprInstance::ENotBody(inner) => visit_opt_par(&inner.p, count),
        ExprInstance::ENegBody(inner) => visit_opt_par(&inner.p, count),
        ExprInstance::EMultBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EDivBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EModBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EPlusBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EMinusBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::ELtBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::ELteBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EGtBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EGteBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EEqBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::ENeqBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EAndBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EOrBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EPercentPercentBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EPlusPlusBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EMinusMinusBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EMatchesBody(inner) => {
            visit_opt_par(&inner.target, count);
            visit_opt_par(&inner.pattern, count);
        },
        // Scalar grounds and bare variables carry no Par operands.
        ExprInstance::GBool(_)
        | ExprInstance::GInt(_)
        | ExprInstance::GString(_)
        | ExprInstance::GUri(_)
        | ExprInstance::GByteArray(_)
        | ExprInstance::GDouble(_)
        | ExprInstance::GBigInt(_)
        | ExprInstance::GBigRat(_)
        | ExprInstance::GFixedPoint(_)
        | ExprInstance::EVarBody(_) => {},
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// B3 — fair-comparison hoisting (harness level)
// ─────────────────────────────────────────────────────────────────────────────

/// One language's benchmark compilation artifacts, produced ONCE by
/// [`compile_bench_language`] and reused (`&self.ruleset`,
/// `&self.installed_program`) across every iteration — the WARM-mode hoist of
/// the per-invocation reconstruct → lower → compile chain the equivalence
/// tests perform per drive. COLD mode = calling [`compile_bench_language`]
/// inside the measured region. Purely harness-level: no macro-generated
/// production rebuild path is touched.
pub struct CompiledBenchLanguage {
    /// The reconstructed macro-time `LanguageDef`.
    pub def: LanguageDef,
    /// The general Rholang lowering (`lower_language_def`) — carries the
    /// definition fingerprint the coherence check pins.
    pub lowered: RhoLowering,
    /// The compiled in-Rho matching ruleset both matchers consume (same
    /// entries, same accept channels, same fingerprint).
    pub ruleset: InRhoMatchingRuleset,
    /// The installed σ-receiver program (`RhoDefaultBackendPlan::
    /// installed_rho_net_program_par`) each drive composes its call against.
    pub installed_program: Par,
}

/// Compile a language's benchmark artifacts ONCE from its
/// `definition_source()`: reconstruct the `LanguageDef`, lower it, plan the
/// Rho-default backend (the same requirements construction as the B2
/// equivalence suite: `CoveredRejectedRules(suggest_rejected_rule_dispositions)`
/// + `NoGuardObligations` — a language WITH guard obligations fails closed
/// here, which the v1 bench corpus never hits), compile the in-Rho matching
/// ruleset, verify the ruleset and the plan share ONE fingerprint (the
/// interface-coherence anchor), and extract the installed σ-receiver program.
///
/// This is the WARM-mode hoist (see [`CompiledBenchLanguage`]); every error is
/// surfaced as a `String` so the harness fails loudly rather than measuring a
/// half-compiled language.
pub fn compile_bench_language(definition_source: &str) -> Result<CompiledBenchLanguage, String> {
    let def = reconstruct_language_def(definition_source)
        .map_err(|error| format!("reconstruct LanguageDef from definition_source: {error}"))?;
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .map_err(|error| format!("Rho-default backend plan rejected: {error:?}"))?;
    let ruleset = compile_in_rho_matching_ruleset(&def);
    if ruleset.language_fingerprint != plan.definition_fingerprint() {
        return Err(format!(
            "fingerprint drift: compiled ruleset carries `{}` but the planned backend carries \
             `{}` — the two drives would not share one interface-coherence anchor",
            ruleset.language_fingerprint,
            plan.definition_fingerprint(),
        ));
    }
    let installed_program = plan
        .installed_rho_net_program_par()
        .map_err(|error| format!("installed Rho-net program: {error:?}"))?;
    Ok(CompiledBenchLanguage { def, lowered: plan.lowering, ruleset, installed_program })
}

// ─────────────────────────────────────────────────────────────────────────────
// E-1 scion grafting (pgmcp experiment 147, design v1 §3.6 / delta SM-8b/SM-9):
// the L2 A/B measurement surface — build BOTH arms' installed programs from ONE
// `LanguageDef` and drive each on a counting runtime. Quarantined behind
// `bench-scion`; `DRIVE_OPT_IN` is untouched (the caller NAMES its ladder def
// `Lambda` to ride the existing name-gate). No production path reaches any of it.
// ─────────────────────────────────────────────────────────────────────────────

/// The two seam-swapped arms' installed programs for one `LanguageDef` (E-1
/// design v1 §3.6, decision D3): CONTROL = the production `AllRedrive` lowering
/// (byte-identical to [`RhoLowering::lower_to_par`] — every firing arm re-drives
/// its whole contractum); TREATMENT = the SAME `RhoNetProgram` + lowering
/// re-lowered under [`ScionPolicy::StructuralScion`](mettail_rholang_codegen::ScionPolicy)
/// (positional `BaseRewrite` arms emit per-rule scion bundles; β `SubstRewrite`
/// and every AC arm stay `ContractumRedrive`). Same def, same lowered rules, same
/// fingerprint, same reserved observation channels — the seam-swapped A/B the
/// seam was built for.
#[cfg(feature = "bench-scion")]
#[derive(Debug, Clone)]
pub struct ScionArmPrograms {
    /// The shared language fingerprint (both arms derive it from the one def).
    pub fingerprint: String,
    /// The CONTROL installed program (`AllRedrive`).
    pub control_installed: Par,
    /// The TREATMENT installed program (`StructuralScion`).
    pub treatment_installed: Par,
}

/// Build both E-1 arms' installed programs from `def` (see [`ScionArmPrograms`]).
/// Fail-loud (`String`) at every planning/install boundary — the harness never
/// measures a half-compiled language. Both arms flow from ONE
/// [`plan_rho_default_backend`] so they share the def fingerprint, the lowered
/// rules, and the reserved `^drive`/`^fired`/`^drive-err`/`^drive-fuel` channel
/// names; only the per-arm [`FiringEmission`](mettail_rholang_codegen::FiringEmission)
/// selection differs.
#[cfg(feature = "bench-scion")]
pub fn scion_arm_programs(def: &LanguageDef) -> Result<ScionArmPrograms, String> {
    let lowering = lower_language_def(def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(def, requirements)
        .map_err(|error| format!("Rho-default backend plan rejected: {error:?}"))?;
    // CONTROL: the production `AllRedrive` installed program (byte-identical to
    // `lower_to_par` — the a_s5_6 / a_s5_8 pins guard this).
    let control_installed = plan
        .installed_rho_net_program_par()
        .map_err(|error| format!("control (AllRedrive) installed program: {error:?}"))?;
    // TREATMENT: the SAME RhoNetProgram + lowering, re-lowered under StructuralScion.
    let treatment_installed = plan
        .rho_net_program()
        .lower_to_par_with_scion_policy(
            def,
            &plan.lowering,
            mettail_rholang_codegen::ScionPolicy::StructuralScion,
        )
        .installed_program_par()
        .map_err(|error| format!("treatment (StructuralScion) installed program: {error:?}"))?;
    let fingerprint = plan.definition_fingerprint().to_string();
    Ok(ScionArmPrograms { fingerprint, control_installed, treatment_installed })
}

/// Drive one arm's `installed` program composed with the `^drive` seed `call` on
/// a FRESH counting runtime and read back BOTH the COMM-classification snapshot
/// AND the full drive observation set (design v1 §6 leg-0). The four reserved
/// observation channels are PEEKED via `get_data` — a non-consuming read that
/// records no COMM — so the returned [`CommCounterSnapshot`] is the
/// reduction-only total (`DriveTau` is the scion-grafting primary metric).
///
/// The counting runtime is the exact [`bench_runtime_with_counters`] bring-up;
/// the seed is the fixed [`BENCH_FIXED_SEED`] (deterministic COMM trace), the
/// budget [`Cost::unsafe_max()`] (mirroring [`bench_inj_and_read`] — budgets
/// remain F1r3node's). ONE arm per fresh runtime, so the post-`inj` snapshot IS
/// the per-drive count. Fail-loud on `inj` error and on an OUT datum that does
/// not decode as a closed runtime observation value.
#[cfg(feature = "bench-scion")]
pub async fn drive_arm_with_counters(
    installed: &Par,
    call: &Par,
    channels: &crate::run::DriveObservationChannels,
) -> Result<(crate::run::DriveObservationSet, CommCounterSnapshot), String> {
    // The concrete `RhoRuntimeImpl` has a `cost` FIELD that shadows the trait
    // method; bring `HasCost` into scope so `runtime.cost()` resolves to it (the
    // generic `bench_inj_and_read` gets this for free via its `R: RhoRuntime`
    // bound).
    use rholang::rust::interpreter::accounting::has_cost::HasCost;
    let (runtime, comm_counters, _match_counters) =
        bench_runtime_with_counters(Vec::new(), &channels.out).await?;
    runtime.cost().set(Cost::unsafe_max());
    let rand = Blake2b512Random::create_from_bytes(BENCH_FIXED_SEED);
    let composed = installed.append(call.clone());
    runtime
        .inj(composed, Env::new(), rand)
        .await
        .map_err(|error| format!("scion drive inj: {error:?}"))?;
    // Snapshot BEFORE any readback: `get_data` below is non-consuming, but taking
    // the snapshot at quiescence makes the reduction-only invariant explicit.
    let snapshot = comm_counters.snapshot();

    let out_raw = drive_peek_channel(&runtime, &channels.out).await;
    let mut out_values = Vec::with_capacity(out_raw.len());
    for par in &out_raw {
        match crate::run::par_as_runtime_observation_value(par) {
            Some(value) => out_values.push(value),
            None => {
                return Err(format!(
                    "scion drive OUT channel {:?} datum did not decode as a closed runtime \
                     observation value: {par:?}",
                    channels.out
                ));
            },
        }
    }
    let fired_data = drive_peek_channel(&runtime, &channels.fired).await;
    let err_data = drive_peek_channel(&runtime, &channels.err).await;
    let fuel_data = drive_peek_channel(&runtime, &channels.fuel).await;
    Ok((
        crate::run::DriveObservationSet { out_values, fired_data, err_data, fuel_data },
        snapshot,
    ))
}

/// Peek every resting `Par` on a quoted channel (`get_data` — NON-consuming, so
/// no COMM is recorded on the counting space), the counting-runtime twin of
/// `run::read_ground_from_runtime` with the verbatim reader.
#[cfg(feature = "bench-scion")]
async fn drive_peek_channel<R: RhoRuntime>(runtime: &R, channel: &str) -> Vec<Par> {
    let channel = quoted_channel(channel);
    let data = runtime.get_data(&channel).await;
    let mut out = Vec::with_capacity(data.iter().map(|datum| datum.a.pars.len()).sum());
    for datum in data {
        for par in &datum.a.pars {
            out.push(par.clone());
        }
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// In-module tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dovetail::rules::Pattern;
    use dovetail::set_automaton::{PatternId, SetAutomaton};
    use mettail_rholang_codegen::{naive_kt_match_call_par, GroundTerm, NaiveGuardEncoding};
    use models::create_bit_vector;
    use models::rhoapi::{GPrivate, GUnforgeable, ReceiveBind};
    use models::rust::rholang::implicits::GPrivateBuilder;
    use models::rust::utils::{
        new_boundvar_par, new_freevar_par, new_gstring_par, new_receive_par, new_send_par,
    };

    const FP: &str = "fp";
    const SITE: &str = "site0";
    /// The forwarder's terminal channel the counting test reads back from (the
    /// OUT COMM itself is what the observation counter must see).
    const FINAL_CHANNEL: &str = "bench:final";

    fn quoted(name: &str) -> Par {
        new_gstring_par(name.to_string(), Vec::new(), false)
    }

    /// The reserved subst-TRS rendezvous channel `GPrivate(reflect_tag(fp,
    /// label))` — byte-identical to `rho_net_subst_trs::tag_par` (the tag
    /// string is `REFLECTED_TERM_ABI_PREFIX + fp + "." + label`).
    fn subst_tag_channel(label: &str) -> Par {
        GPrivateBuilder::new_par_from_string(format!(
            "{}{FP}.{label}",
            crate::REFLECTED_TERM_ABI_PREFIX
        ))
    }

    fn workload(name: &str) -> BenchWorkloadParams {
        BenchWorkloadParams {
            name: name.to_string(),
            matcher: "naive".to_string(),
            encoding: "pattern-guard".to_string(),
            n: 1,
            rep: 0,
        }
    }

    /// (B4.5 classification) Every channel family classifies into its own
    /// bucket, with the contextual-premise `loc:` refinement, the five reserved
    /// subst-TRS tag channels, the configured OUT name, and the unknown
    /// fallback all covered.
    #[test]
    fn classification_covers_every_channel_family() {
        let counters = CommCounters::new("OUT");
        let cases: Vec<(Par, CommChannelClass, &str)> = vec![
            (quoted("loc:site0"), CommChannelClass::MatchingTau, "spread root location"),
            (quoted("loc:site0/Swap.1"), CommChannelClass::MatchingTau, "spread child location"),
            (quoted("col:site0"), CommChannelClass::MatchingTau, "chain collapse"),
            (quoted("cap:site0/Swap.0"), CommChannelClass::MatchingTau, "capture collapse"),
            (quoted("sa:pattern/abc123"), CommChannelClass::FiringVisible, "σ-receiver source"),
            (quoted("sa:scalar/AddInt"), CommChannelClass::FiringVisible, "native dispatch"),
            (
                quoted("sa:scalar/AddInt/sa-locate"),
                CommChannelClass::FiringVisible,
                "native locate trigger",
            ),
            (quoted("ac:PPar"), CommChannelClass::AcCarrier, "bare AC soup carrier"),
            (
                quoted("ac:loc:site0/PPar.0/PPar"),
                CommChannelClass::AcCarrier,
                "site-keyed AC carrier",
            ),
            (
                quoted("e6a:idx:site0"),
                CommChannelClass::PathMapIndex,
                "the E-6a persistent subject-index channel",
            ),
            (
                quoted("e6a:sites:site0/Swap"),
                CommChannelClass::PathMapIndex,
                "an E-6a machine-side site-enumeration result channel",
            ),
            (
                quoted("ph:loc:rewrite/WrapCong/contextual-premise/0/S-to-T"),
                CommChannelClass::ContextualPlumbing,
                "premise-hole bridge",
            ),
            (
                quoted("loc:rewrite/WrapCong/contextual-premise/0/S-to-T"),
                CommChannelClass::ContextualPlumbing,
                "contextual join premise",
            ),
            (quoted("OUT"), CommChannelClass::Observation, "the configured OUT channel"),
            (quoted("mystery"), CommChannelClass::Other, "an unknown quoted channel"),
            (subst_tag_channel(SUBST_RESERVED_LABEL), CommChannelClass::SubstTau, "^subst"),
            (subst_tag_channel(SHIFT_RESERVED_LABEL), CommChannelClass::SubstTau, "^shift"),
            (subst_tag_channel(SHIFTK_RESERVED_LABEL), CommChannelClass::SubstTau, "^shiftk"),
            (subst_tag_channel(CMP_RESERVED_LABEL), CommChannelClass::SubstTau, "^cmp"),
            (subst_tag_channel(PRED_RESERVED_LABEL), CommChannelClass::SubstTau, "^pred"),
            (
                subst_tag_channel(mettail_rholang_codegen::RESPREAD_RESERVED_LABEL),
                CommChannelClass::RespreadTau,
                "^respread (the R3 walker)",
            ),
            (
                subst_tag_channel(mettail_rholang_codegen::RESPREAD_ROOT_RESERVED_LABEL),
                CommChannelClass::RespreadTau,
                "^respread-root (the R3 dispatcher)",
            ),
            (
                subst_tag_channel(mettail_rholang_codegen::RESPREAD_ERR_RESERVED_LABEL),
                CommChannelClass::RespreadTau,
                "^respread-err (the R3 fail-closed channel)",
            ),
            (
                subst_tag_channel(mettail_rholang_codegen::DRIVE_RESERVED_LABEL),
                CommChannelClass::DriveTau,
                "^drive (the E-1 quiescence-driver rendezvous)",
            ),
            (
                // The per-rule AC-carrier tag is DELIBERATELY not DriveTau — it is
                // AC firing traffic re-pinned with the W-D Ambient cells, not the
                // structural `^drive` descent, so it stays Other until that leg.
                subst_tag_channel("^drive-ac:OpenRule"),
                CommChannelClass::Other,
                "^drive-ac:{rule} (AC carrier, not the structural ^drive metric)",
            ),
            (
                // A reflected TERM tag (an ordinary constructor) is data, never
                // a reserved rendezvous channel — it must NOT classify SubstTau.
                subst_tag_channel("Pair"),
                CommChannelClass::Other,
                "a non-reserved GPrivate tag",
            ),
        ];
        for (channel, expected, what) in &cases {
            assert_eq!(
                counters.classify_channel(channel),
                *expected,
                "{what} must classify as {expected:?}"
            );
        }

        // An undecodable GPrivate id (a runtime-fresh name shape) is Other.
        let fresh = Par {
            unforgeables: vec![GUnforgeable {
                unf_instance: Some(UnfInstance::GPrivateBody(GPrivate {
                    id: vec![0xff, 0x00, 0x99],
                })),
            }],
            ..Default::default()
        };
        assert_eq!(
            counters.classify_channel(&fresh),
            CommChannelClass::Other,
            "an undecodable GPrivate id has no reserved tag"
        );
    }

    /// (B4.5 classification, joins) A multi-channel join classifies by the
    /// FIXED precedence (min over the members) and bumps `join_arity_gt1`;
    /// an unknown member is retained in the diagnostics even when the join
    /// itself classifies into a known bucket.
    #[test]
    fn join_classification_uses_fixed_precedence_and_records_arity() {
        let counters = CommCounters::new("OUT");

        // Two matching channels (the root collapse join shape) → matching_tau.
        counters.record_comm(&[quoted("col:site0/Swap.0"), quoted("col:site0/Swap.1")]);
        // A capture + an accept → firing_visible outranks matching_tau.
        counters.record_comm(&[quoted("cap:site0/Swap.0"), quoted("sa:swap")]);
        // A single unknown channel → other, with its rendering retained.
        counters.record_comm(&[quoted("mystery:chan")]);
        // A known + unknown join → the known class wins, the unknown member is
        // still retained for diagnosis (never silently dropped).
        counters.record_comm(&[quoted("loc:site0"), quoted("mystery:other")]);

        let snapshot = counters.snapshot();
        assert_eq!(snapshot.matching_tau, 2, "col-join + loc-with-unknown-join");
        assert_eq!(snapshot.firing_visible, 1, "the cap+sa join classifies by precedence");
        assert_eq!(snapshot.other, 1, "only the all-unknown COMM counts as other");
        assert_eq!(snapshot.join_arity_gt1, 3, "three of the four COMMs joined > 1 channel");
        assert_eq!(
            snapshot.unknown_channel_samples,
            vec!["@\"mystery:chan\"".to_string(), "@\"mystery:other\"".to_string()],
            "every unknown member is retained, in arrival order"
        );
    }

    /// The unknown-channel diagnostic list is bounded by
    /// [`MAX_UNKNOWN_CHANNEL_SAMPLES`] while the `other` counter keeps growing.
    #[test]
    fn unknown_channel_samples_are_bounded() {
        let counters = CommCounters::new("OUT");
        for index in 0..(MAX_UNKNOWN_CHANNEL_SAMPLES + 5) {
            counters.record_comm(&[quoted(&format!("mystery:{index}"))]);
        }
        let snapshot = counters.snapshot();
        assert_eq!(snapshot.other, (MAX_UNKNOWN_CHANNEL_SAMPLES + 5) as u64);
        assert_eq!(snapshot.unknown_channel_samples.len(), MAX_UNKNOWN_CHANNEL_SAMPLES);
    }

    /// A σ-echo observer for a direct-construction accept (the same shape as
    /// `tests/rho_net_naive_equivalence.rs`):
    /// `for(y_0,…,y_{k-1}, o <- accept){ o!(y_0) | … | o!(y_{k-1}) }` forwards
    /// each σ slot to the accept's dynamic out channel. ONE-SHOT.
    fn sigma_echo_receiver(accept_channel: &str, arity: usize) -> Par {
        let mut body = Par::default();
        for i in 0..arity {
            let yi = arity - i; // y_i = BoundVar(arity - i); o = BoundVar(0).
            let send = new_send_par(
                new_boundvar_par(0, create_bit_vector(&[0]), false),
                vec![new_boundvar_par(yi as i32, create_bit_vector(&[yi]), false)],
                false,
                create_bit_vector(&[0, yi]),
                false,
                create_bit_vector(&[0, yi]),
                false,
            );
            body = body.append(send);
        }
        if arity > 0 {
            body.locally_free = create_bit_vector(&(0..=arity).collect::<Vec<_>>());
        }
        new_receive_par(
            vec![ReceiveBind {
                patterns: (0..arity + 1)
                    .map(|i| new_freevar_par(i as i32, Vec::new()))
                    .collect(),
                source: Some(quoted(accept_channel)),
                remainder: None,
                free_count: (arity + 1) as i32,
            }],
            body,
            false,
            false,
            (arity + 1) as i32,
            Vec::new(),
            false,
            Vec::new(),
            false,
        )
    }

    /// A PERSISTENT forwarder `for(@v <= @"from"){ @"to"!(v) }` — the OUT
    /// consumer that turns the σ-echo's resting sends into observation COMMs
    /// (production drives leave OUT as pure resting data, so a bench run
    /// normally counts 0 observation COMMs; this test wants ≥ 1).
    fn out_forward_receiver(from_channel: &str, to_channel: &str) -> Par {
        let body = new_send_par(
            quoted(to_channel),
            vec![new_boundvar_par(0, create_bit_vector(&[0]), false)],
            false,
            create_bit_vector(&[0]),
            false,
            create_bit_vector(&[0]),
            false,
        );
        new_receive_par(
            vec![ReceiveBind {
                patterns: vec![new_freevar_par(0, Vec::new())],
                source: Some(quoted(from_channel)),
                remainder: None,
                free_count: 1,
            }],
            body,
            true, // persistent: forward EVERY OUT value
            false,
            1,
            Vec::new(),
            false,
            Vec::new(),
            false,
        )
    }

    /// The SwapDemo-shaped direct-construction ruleset: ONE flat entry
    /// `Swap(x, y)` routed to `sa:swap` (admission-matrix style — no demo
    /// language needed).
    fn swap_shaped_ruleset() -> InRhoMatchingRuleset {
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "Swap".to_string(),
                vec![Pattern::var("x"), Pattern::var("y")],
            ),
        )])
        .expect("Swap(x, y) compiles to a positional automaton");
        InRhoMatchingRuleset {
            automaton,
            accept_channels: vec![(PatternId(0), "sa:swap".to_string())],
            language_fingerprint: FP.to_string(),
            deferred: Vec::new(),
            native_dispatch: Vec::new(),
            ac_dispatch: Vec::new(),
            contextual_dispatch: Vec::new(),
            structural_ac_dispatch: Vec::new(),
            nested_structural_ac_dispatch: Vec::new(),
        }
    }

    /// (B4.5 counting) A minimal spread + naive receiver + accept run on the
    /// counting runtime: the SwapDemo-shaped direct construction `Swap(A, B)`
    /// driven through `naive_kt_match_call_par`, with a σ-echo on the accept
    /// and a persistent OUT forwarder. Asserts the classification profile
    /// (`matching_tau > 0`, `firing_visible ≥ 1`, `observation ≥ 1`,
    /// `other == 0` with actionable diagnostics), the match-attempt counters,
    /// the phase timers, `encoded_len`, and the receiver count.
    #[tokio::test]
    async fn swap_shaped_counting_run_classifies_and_instruments() {
        let ruleset = swap_shaped_ruleset();
        let subject =
            GroundTerm::new("Swap", vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")]);
        let (call, installed) = naive_kt_match_call_par(
            &ruleset,
            &subject,
            SITE,
            "OUT",
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the naive Appendix-A call admits the flat Swap entry");
        assert_eq!(installed, 1, "one head-Swap position ⇒ one installed naive receiver");

        // σ-echo (2 slots) + persistent OUT→FINAL forwarder + the naive call.
        let program = sigma_echo_receiver("sa:swap", 2)
            .append(out_forward_receiver("OUT", FINAL_CHANNEL))
            .append(call);

        let (mut runtime, comm_counters, match_counters) =
            bench_runtime_with_counters(Vec::new(), "OUT")
                .await
                .expect("the counting runtime builds");
        let wall_started = Instant::now();
        let result = bench_inj_and_read(
            &mut runtime,
            &program,
            FINAL_CHANNEL,
            workload("swap-shaped-direct"),
            &comm_counters,
            &match_counters,
        )
        .await
        .expect("the counting drive executes on the Rho runtime");
        let wall = wall_started.elapsed();

        // Classification profile. `other == 0` failure must be actionable:
        // print the retained unknown-channel renderings.
        let snapshot = &result.comm;
        assert_eq!(
            snapshot.other, 0,
            "no COMM may fall outside the channel taxonomy; unknown channels seen: {:?}",
            snapshot.unknown_channel_samples
        );
        assert!(
            snapshot.matching_tau > 0,
            "the spread/receiver τ traffic (loc:/cap:/col:) must be counted; got {snapshot:?}"
        );
        assert!(
            snapshot.firing_visible >= 1,
            "the accept COMM on sa:swap must be counted; got {snapshot:?}"
        );
        assert!(
            snapshot.observation >= 1,
            "the forwarder's OUT COMM must be counted; got {snapshot:?}"
        );
        assert!(
            snapshot.join_arity_gt1 >= 1,
            "the root collapse joins two col: channels; got {snapshot:?}"
        );
        assert_eq!(snapshot.subst_tau, 0, "no subst TRS in this workload; got {snapshot:?}");
        assert_eq!(snapshot.respread_tau, 0, "no R3 walker in this workload; got {snapshot:?}");
        assert_eq!(snapshot.ac_carrier, 0, "no AC carrier in this workload; got {snapshot:?}");
        assert_eq!(snapshot.pathmap_index, 0, "no E-6a index in this workload; got {snapshot:?}");
        assert_eq!(
            snapshot.contextual_plumbing, 0,
            "no contextual join in this workload; got {snapshot:?}"
        );

        // Both σ slots (⟦A⟧, ⟦B⟧) were forwarded to the FINAL channel.
        assert_eq!(
            result.observed.len(),
            2,
            "the persistent forwarder relays both σ-echo sends; got {:?}",
            result.observed
        );

        // Match-attempt seam: the spatial matcher ran and succeeded.
        assert!(
            result.matches.attempts >= result.matches.successes,
            "attempts bound successes: {:?}",
            result.matches
        );
        assert!(
            result.matches.successes >= 1,
            "at least one spatial match succeeded (the COMMs above fired): {:?}",
            result.matches
        );

        // Bench-internal secondary cost read: ≥ 1 committed COMM ⇒ ≥ 1
        // consumed source-token unit (DR-9, one token per COMM).
        assert!(
            result.consumed_cost_units >= 1,
            "the secondary cost read must see the committed COMMs; got {}",
            result.consumed_cost_units
        );

        // Phase timers: the phases are disjoint sub-intervals of the wall time,
        // and the reduction phase did real work.
        assert!(result.inj > Duration::ZERO, "the inj phase timed a real reduction");
        assert!(
            result.build + result.inj + result.readback <= wall,
            "the three phases are disjoint sub-intervals of the wall time \
             (build {:?} + inj {:?} + readback {:?} vs wall {:?})",
            result.build,
            result.inj,
            result.readback,
            wall
        );

        // Program-shape metrics.
        assert!(result.program_encoded_len > 0, "the emitted Par has a positive encoding");
        assert!(
            result.program_receiver_count >= 5,
            "σ-echo (1) + forwarder (1) + the naive receiver's nested tag/capture receives \
             (≥ 3) are all counted; got {}",
            result.program_receiver_count
        );

        // The JSON line is well-formed enough to carry every scalar field.
        let line = result.to_json_line();
        for key in [
            "\"name\":\"swap-shaped-direct\"",
            "\"matcher\":\"naive\"",
            "\"encoding\":\"pattern-guard\"",
            "\"inj_ns\":",
            "\"program_encoded_len\":",
            "\"observed_count\":2",
            "\"consumed_cost_units\":",
            "\"matching_tau\":",
            "\"attempts\":",
        ] {
            assert!(line.contains(key), "the JSON line must carry {key}; got {line}");
        }
    }

    /// The receive visitor counts nested, data-carried, and pattern-carried
    /// `Receive` nodes (a hand-built Par with a KNOWN count).
    #[test]
    fn count_receive_nodes_walks_nested_and_carried_receives() {
        // for(@v <- @"a"){ for(@w <- @"b"){ Nil } } | @"c"!( for(@u <- @"d"){ Nil } )
        let inner = out_forward_receiver("b", "unused");
        let outer = new_receive_par(
            vec![ReceiveBind {
                patterns: vec![new_freevar_par(0, Vec::new())],
                source: Some(quoted("a")),
                remainder: None,
                free_count: 1,
            }],
            inner,
            false,
            false,
            1,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let carried = new_send_par(
            quoted("c"),
            vec![out_forward_receiver("d", "unused")],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let par = outer.append(carried);
        assert_eq!(
            count_receive_nodes(&par),
            3,
            "outer + nested-in-body + carried-in-send-data receives are all counted"
        );
        assert_eq!(count_receive_nodes(&Par::default()), 0, "an empty Par has no receives");
    }

    /// JSON escaping covers quotes, backslashes, and control characters.
    #[test]
    fn json_escaping_is_safe_for_diagnostic_strings() {
        let mut out = String::new();
        escape_json_into("a\"b\\c\nd\te\u{01}f", &mut out);
        assert_eq!(out, "a\\\"b\\\\c\\nd\\te\\u0001f");
    }

    /// (B3) The warm-mode hoist compiles SwapDemo ONCE: the ruleset and the
    /// plan share one fingerprint, the installed σ-receiver program is a real
    /// receiver network, and the compiled artifacts are reusable by reference.
    #[cfg(feature = "swap-demo-runtime")]
    #[test]
    fn compile_bench_language_hoists_swapdemo_once() {
        use mettail_languages::swapdemo::SwapDemoLanguage;
        use mettail_runtime::Language;

        let source = SwapDemoLanguage
            .metadata()
            .definition_source()
            .expect("the generated SwapDemo exposes its definition_source");
        let compiled = compile_bench_language(source)
            .expect("SwapDemo compiles through the warm-mode hoist");
        assert_eq!(
            compiled.ruleset.language_fingerprint,
            compiled.lowered.definition_fingerprint(),
            "the hoisted ruleset and lowering share ONE fingerprint"
        );
        assert!(
            compiled.ruleset.automaton.view().entry_count() >= 1,
            "SwapDemo compiles at least the SwapStep entry"
        );
        assert!(
            count_receive_nodes(&compiled.installed_program) >= 1,
            "the installed program is a real σ-receiver network"
        );
        assert!(!compiled.def.rewrites.is_empty(), "the reconstructed def carries its rewrites");
    }
}
