//! Track B — B5: DETERMINISTIC workload generators + per-rep drive functions for
//! the naive-vs-optimized matcher benchmark, shared (by `#[path]` inclusion)
//! between the criterion bench (`benches/bench_sa_vs_naive.rs`) and the
//! JSON-lines driver bin (`src/bin/bench_sa_vs_naive_driver.rs`).
//!
//! Every subject is DETERMINISTIC BY CONSTRUCTION (no randomness anywhere): a
//! workload is a pure function of its size parameter, and every workload carries
//! a directly-computed ground-truth `expected_firings` count plus the exact
//! expected observation multiset the drive verifies against on every rep.
//!
//! # The workload families (mirroring the B2 equivalence suite's drive discipline)
//!
//! | workload | subject | drive (per matcher column) | ground truth |
//! |---|---|---|---|
//! | (i) `lambda_chain(n)` | the B2 `App(^lambda(^bound Z), ·)` spine, terminal atom `A` | PER-STEP root redex on BOTH matchers (`in_rho_match_call_par` vs the root-restricted naive receiver ∥ spread), n steps to NF, each step on a FRESH counting runtime fed by the PREVIOUS step's OBSERVED reduct | n firings; step k observes the remaining chain of length n−k−1 |
//! | (ii) `swap_comb(m)` | m PAIRWISE-DISTINCT `Swap(L₂ᵢ, L₂ᵢ₊₁)` under a right `Pair` comb (distinctness via distinct nullary leaf constructors — opaque data to the matcher) | ONE locate-all call (`in_rho_match_all_sites_call_par`) vs ONE naive comprehension call (`naive_kt_match_call_par`) | m firings; multiset { Pair(L₂ᵢ₊₁, L₂ᵢ) } |
//! | (iv) `swap_small(k)` | a single `Swap(A, B)` under k−1 inert `Pair` wrappers (k = 1 is the bare root redex) | both drivers (locate-all vs comprehension) — the crossover floor | 1 firing; { Pair(B, A) } |
//! | (v) `wrap_swap_ctx(depth)` | CtxDemo `Wrap(Swap(A, B))` (depth 1) | both CONTEXTUAL drivers (`contextual_match_call_par` vs `naive_kt_contextual_match_call_par`) | 1 firing; { Wrap(Pair(B, A)) } |
//! | (vi) `nested_spine(k)` | direct-construction `f(g(x))` entry over a right `Pair` comb of k head-`f` candidate sites, ONE true redex per site (the B2 divergent-admission test's shape) | naive in-Rho comprehension vs the production host-σ REPLAY fallback (host-computed σ fired as ground accept-send COMMs against the SAME σ-echo receivers) | k firings; multiset { L₀ … L₍ₖ₋₁₎ } |
//! | (vii) `multi_rule_shared(n = 100·r + s)` | direct-construction r-rule PATTERN SET `Rᵢ(Sˢ(x))`, i ∈ 0..r (pairwise-DISTINCT roots `Rᵢ`, ONE SHARED non-root sub-pattern chain `Sˢ(x)`), over a right `Pair` comb of r redexes `Rᵢ(Sˢ(Kᵢ))` | per-rule drive at admitted sites (the production per-site `multi_pattern_receiver_network_par` — ALL r entries' interned automaton — at each of the r sites over ONE spread) vs ONE naive comprehension call | r firings; multiset { K₀ … K₍ᵣ₋₁₎ } (rule i's σ[x], routed through its OWN accept channel's σ-echo) |
//!
//! # (vii) `multi_rule_shared` — the multi-rule pattern-set sharing regime (amended W1)
//!
//! The regime the set automaton was DESIGNED for: ONE subject matched against
//! r rules SIMULTANEOUSLY. The optimized side compiles all r rules into ONE
//! interned automaton — the `Sˢ(x)` sub-pattern chain interns to a SINGLE
//! shared state set across every entry (`state_count = r + s + 1` vs the
//! per-rule sum `r·(s + 2)`; asserted by the
//! `multi_rule_shared_state_sharing_is_real` unit test) — and matches the
//! subject once per site through the shared root dispatch. The naive side
//! installs r independent per-rule receivers (the Appendix-A per-rule
//! comprehension), each independently descending its own copy of the shared
//! sub-structure.
//!
//! **PRE-REGISTERED prediction (the amended-W1 exponent leg, pgmcp experiment
//! 144 amendment):** per-cell `matching_tau` and `attempts` scale ~O(subject)
//! on the sa column but ~O(r · subject-overlap) on the naive column, so the
//! naive/sa ratio grows with r (and with s at fixed r). The smoke HARD-asserts
//! the signal exists at r = 4, s = 2 (naive `matching_tau` > sa
//! `matching_tau`); if it does not hold, that is a REFUTATION to surface —
//! never weaken the assertion. (Context: the B6 smoke FINDING in
//! `docs/benchmarks/data/sa-vs-naive/README.md` already established
//! sa-vs-naive counter EQUALITY on every SINGLE-rule drive, and noted the
//! naive blow-up "needs multi-RULE root sharing" — which the naive
//! `OverlappingTagDemand` gate fails closed on. This family is the closest
//! BOTH-columns-admitted approach to that regime: maximal cross-rule
//! sub-pattern sharing under pairwise-distinct roots.)
//!
//! **Admission (why this exact shape passes BOTH gates):**
//!
//! * Naive (`NaiveKtUnsupported::OverlappingTagDemand`): the roots `Rᵢ` are
//!   pairwise distinct (no duplicate-root demand) and the shared op `S` is not
//!   any rule's root op (no nested-vs-root demand) — pinned by
//!   `multi_rule_shared_generator_pins_shape_ground_truth_and_gates`.
//! * Optimized: the ONE-call locate-all
//!   ([`in_rho_match_all_sites_call_par`](mettail_rholang_codegen::in_rho_match_all_sites_call_par))
//!   FAILS CLOSED for r ≥ 2 — its `NestedEntryMultiSite` gate counts candidate
//!   sites ACROSS entries (`sites.len() > 1 && !ruleset_all_entries_flat`),
//!   not per entry, so r distinct-rooted nested redexes trip it (pinned by the
//!   same unit test). The sa column therefore drives PER-RULE AT ADMITTED
//!   SITES: each of the r sites is exactly the admitted nested-ruleset
//!   ≤ 1-site install, emitted by the SAME production per-site emitter
//!   (`multi_pattern_receiver_network_par`, all r entries' shared automaton),
//!   composed over ONE spread. That composition is contention-free FOR THIS
//!   FAMILY because (a) the r sites are pairwise non-ancestral comb-leaf
//!   positions (disjoint `loc:`/`cap:` channel prefixes; pinned by
//!   `multi_rule_shared_sites_are_pairwise_non_ancestral`) and (b) no rule
//!   root op occurs at any non-root pattern position (the naive gate's own
//!   static condition), so no installed network's descent read can alias
//!   another installed network's root read — exactly the hazard
//!   `NestedEntryMultiSite` conservatively guards against.
//!
//! Size encoding: `n = 100·r + s` (r = `n / 100` rules, s = `n % 100` shared
//! `S`-chain depth; both ≥ 1). The full ladder is the cross product
//! r ∈ {2, 4, 8} × s ∈ {1, 2, 3}; the smoke cell is n = 402 (r = 4, s = 2).
//!
//! `wrap_swap_ctx` depth 2 (`Wrap(Wrap(Swap(A, B)))`) FAILS CLOSED on BOTH
//! contextual emitters (the single-congruence hole bijection admits only the
//! depth-1 hole site — pinned by
//! [`tests::wrap_swap_ctx_depth_two_fails_closed_on_both_emitters`]), so the
//! admitted `wrap_swap_ctx` size set is exactly `{1}`.
//!
//! # (iii) AC characterization — SCOPED OUT of the head-to-head
//!
//! The AC (HashBag / structural-AC / nested-structural-AC) rewrite families are
//! deliberately NOT generated here: the naive Knotted-Topoi Appendix-A emitter
//! is a POSITIONAL comprehension scheme (`rho_net_naive_kt` drives only
//! automaton entries — its rustdoc excludes `ac_dispatch` /
//! `structural_ac_dispatch` / `nested_structural_ac_dispatch` outright), so an
//! AC workload has no naive column to compare against and would characterize
//! only the optimized AC carrier in isolation. AC-carrier COMM traffic is still
//! CLASSIFIED (the `ac_carrier` counter in every [`CommCounterSnapshot`]) so an
//! accidental AC excursion in any workload would be visible, but no AC subject
//! is generated and no AC head-to-head cell exists in the protocol.
//!
//! # Fail-closed admission facts the generators pin (unit-tested)
//!
//! * `lambda_chain` n ≥ 2 and `nested_spine` k ≥ 2 fail closed on the optimized
//!   locate-all (`AutomatonUnsupported::NestedEntryMultiSite`, the B0 admission
//!   matrix) — hence the per-step root drive for (i) and the REPLAY column for
//!   (vi): the honest production comparison in the fail-closed regime.
//! * `multi_rule_shared` r ≥ 2 likewise fails closed on the ONE-CALL locate-all
//!   (the same across-entry gate), but its sa column keeps the AUTOMATON via
//!   the per-rule drive at admitted sites (module rustdoc §(vii)) — the
//!   amendment's explicit alternative to a replay column.
//! * `swap_comb` / `swap_small` admit on BOTH columns at every size (flat-entry
//!   co-installation is contention-free).
//! * `ConsumeTest` is admitted ONLY where the subject is single-candidate
//!   (the B2 partial-fire hazard exclusion): `swap_small` (all k),
//!   `lambda_chain` (each per-step root drive installs exactly one receiver),
//!   `wrap_swap_ctx` (one hole premise), `swap_comb` m = 1, and
//!   `multi_rule_shared` r = 1.
//!
//! # What a rep is (and what is timed)
//!
//! One rep = one [`run_compiled_workload`] call: a FRESH counting runtime per
//! injection ([`bench_runtime_with_counters`] — counters are per-runtime, so
//! reps are independent), the per-call emission, one `inj` to quiescence, the
//! readback, and the observed-vs-expected multiset verification. The
//! multi-step `lambda_chain` rep runs its n steps each on its own fresh
//! runtime (exactly the B2 per-step discipline) and SUMS the per-step phase
//! timers / counters into one aggregate [`BenchRunResult`]. The
//! [`WorkloadRepOutcome`] separates `emission` (per-call emitter + program
//! composition) and `bringup` (counting-runtime construction) from the
//! [`BenchRunResult`] phase timers (`build`/`inj`/`readback`) so the harness
//! can time warm (emission + build + inj + readback) and cold (+ compile +
//! bringup) regions exactly. Verification/decode time is in NO measured span.

use std::collections::BTreeSet;
use std::time::{Duration, Instant};

use dovetail::rules::Pattern;
use dovetail::set_automaton::{AutomatonNode, PatternId, SetAutomaton};
// Task #11 (extended 2026-07-26): `CtxDemo` is a DEMONSTRATION grammar whose definition lives
// in `languages/tests/definitions/ctxdemo.rs`, not in the `languages` library, so it is
// `#[path]`-included. This module is a CONSUMER: it does not invoke the
// `ctxdemo_generated_tests!` wrapper (a bench has no business materializing a test suite).
#[path = "../../../languages/tests/definitions/ctxdemo.rs"]
mod ctxdemo;

// Task #11 (extended 2026-07-26): `LambdaDemo` is a DEMONSTRATION grammar whose definition lives
// in `languages/tests/definitions/lambdademo.rs`, not in the `languages` library, so it is
// `#[path]`-included. This module is a CONSUMER: it does not invoke the
// `lambdademo_generated_tests!` wrapper (a bench has no business materializing a test suite).
#[path = "../../../languages/tests/definitions/lambdademo.rs"]
mod lambdademo;

// Task #11 (extended 2026-07-26): `SwapDemo` is a DEMONSTRATION grammar whose definition lives
// in `languages/tests/definitions/swapdemo.rs`, not in the `languages` library, so it is
// `#[path]`-included. This module is a CONSUMER: it does not invoke the
// `swapdemo_generated_tests!` wrapper (a bench has no business materializing a test suite).
#[path = "../../../languages/tests/definitions/swapdemo.rs"]
mod swapdemo;

use ctxdemo::CtxDemoLanguage;
use lambdademo::LambdaDemoLanguage;
use mettail_rholang_codegen::{
    contextual_match_call_par, in_rho_match_all_sites_call_par, in_rho_match_call_par,
    multi_pattern_receiver_networks_at_rule_roots_par, naive_kt_contextual_match_call_par,
    naive_kt_entry_receiver_par, naive_kt_match_call_par, naive_kt_selfdriving_call_par,
    reflect_ground_term_par, spread_child_location, spread_term_par, AutomatonAcceptTarget,
    GroundTerm, InRhoMatchingRuleset, NaiveGuardEncoding, BOUND_VAR_REFLECT_LABEL,
    LAMBDA_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    bench_inj_and_read, bench_runtime_with_counters, compile_bench_language,
    par_as_runtime_observation_value, BenchRunResult, BenchWorkloadParams, CommCounterSnapshot,
    CompiledBenchLanguage, MatchAttemptSnapshot, MAX_UNKNOWN_CHANNEL_SAMPLES,
};
use mettail_runtime::{Language, RuntimeObservationValue};
use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{Par, ReceiveBind};
use models::rust::utils::{
    new_boundvar_par, new_freevar_par, new_gstring_par, new_receive_par, new_send_par,
};
use prost::Message;
use swapdemo::SwapDemoLanguage;

/// The shared root-site nonce for every drive (each injection executes on its
/// own isolated fresh counting runtime, so a fixed nonce cannot collide — the
/// same convention as the B2 equivalence suite).
pub const ROOT_SITE: &str = "site0";

/// The observation channel every drive reads back from (and the channel the
/// per-runtime [`CommCounters`](mettail_rholang_runtime::CommCounters) classify
/// as `Observation`).
pub const OUT_CHANNEL: &str = "OUT";

/// The direct-construction `f(g(x))` accept channel of the `nested_spine`
/// workload (the B2 divergent-admission test's channel).
pub const NESTED_SPINE_ACCEPT: &str = "sa:fg";

/// The direct-construction language fingerprint of the `nested_spine` workload
/// (admission-matrix style — no demo language exists for `f(g(x))`).
pub const NESTED_SPINE_FINGERPRINT: &str = "fp";

/// The direct-construction language fingerprint of the `multi_rule_shared`
/// workload (admission-matrix style — no demo language carries a multi-rule
/// shared-sub-pattern set; the B6 FINDING pinned that no bundled demo language
/// exercises multi-rule sharing at all).
pub const MULTI_RULE_SHARED_FINGERPRINT: &str = "fp";

/// The direct-construction accept channel of `multi_rule_shared` rule `i` —
/// one channel PER RULE, so each firing is routed to its own one-shot σ-echo
/// and the observed value is attributable to exactly one rule (only entry i's
/// network/receiver can fire `sa:mrs:i`, and subject site i is the only
/// head-`Rᵢ` position).
pub fn multi_rule_shared_accept(rule: usize) -> String {
    format!("sa:mrs:{rule}")
}

/// Per-rep emitted-program size guard: an emission whose COMPOSED program
/// exceeds this `prost` encoding length is recorded as a DNF (reason
/// `encoded-len-guard`) instead of being injected.
pub const MAX_PROGRAM_ENCODED_LEN: usize = 8 * 1024 * 1024;

/// The FORMERLY-PANICKING f1r3node interpreter split zone, kept as a
/// REGRESSION zone: `DebruijnInterpreter::eval` splits its per-term
/// `Blake2b512Random` by the 0-based term index; the old branch sent every
/// parallel width `2 ..= 256` to `split_byte(i8)`
/// (`rholang/src/rust/interpreter/reduce.rs`), so a term index ≥ 128
/// overflowed the `i8` conversion (`crypto/src/rust/hash/
/// blake2b512_random.rs:97`) and panicked with `TryFromIntError(PosOverflow)`
/// — every width in `INTERPRETER_SPLIT_REGRESSION_MIN ..=
/// INTERPRETER_SPLIT_REGRESSION_MAX` crashed, per eval level. FIXED in the
/// f1r3node-rust-mettail working tree this repo path-depends on (branch
/// `fix/split-byte-width-range`, commit 31b354e6): widths in [129, 256] now
/// join the `split_short(i16)` path used by every larger width, and widths
/// ≤ 128 keep byte-identical `split_byte` randomness. The harness no longer
/// gates in-zone injections; instead [`cell_width_probe`] records the zone as
/// PROVENANCE (which cells exercise the fixed range) and the driver-bin unit
/// tests assert the zone WORKS: the 9-cell in-zone pin plus a width-129
/// actual-eval spot check (`interpreter_split_regression_*` tests). The
/// upstream fix is consensus-relevant (the split id feeds unforgeable-name
/// derivation) — review before upstreaming beyond that branch.
pub const INTERPRETER_SPLIT_REGRESSION_MIN: usize = 129;

/// Upper bound (inclusive) of the formerly-panicking f1r3node split
/// regression zone — see [`INTERPRETER_SPLIT_REGRESSION_MIN`].
pub const INTERPRETER_SPLIT_REGRESSION_MAX: usize = 256;

// ─────────────────────────────────────────────────────────────────────────────
// The registry: workloads × matchers × naive guard encodings
// ─────────────────────────────────────────────────────────────────────────────

/// The six generated Track-B workload families (see the module rustdoc table;
/// (iii) AC characterization is scoped out and has NO generator).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkloadKind {
    /// (i) The per-step β chain `App(^lambda(^bound Z), ·)ⁿ · A`.
    LambdaChain,
    /// (ii) The m-redex pairwise-distinct `Swap` comb.
    SwapComb,
    /// (iv) The single-`Swap` shallow-nesting crossover floor.
    SwapSmall,
    /// (v) The CtxDemo `Wrap(Swap)` contextual hole.
    WrapSwapCtx,
    /// (vi) The nested `f(g(x))` k-candidate spine (naive vs REPLAY).
    NestedSpine,
    /// (vii) The r-rule shared-sub-pattern set `Rᵢ(Sˢ(x))` over an r-redex
    /// comb (`n = 100·r + s`) — the amended-W1 pattern-set sharing regime.
    MultiRuleShared,
}

/// Every generated workload, in protocol order.
pub const ALL_WORKLOADS: [WorkloadKind; 6] = [
    WorkloadKind::LambdaChain,
    WorkloadKind::SwapComb,
    WorkloadKind::SwapSmall,
    WorkloadKind::WrapSwapCtx,
    WorkloadKind::NestedSpine,
    WorkloadKind::MultiRuleShared,
];

/// A matcher column of the head-to-head.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatcherKind {
    /// The optimized set-automaton drivers (`in_rho_match_call_par` /
    /// `in_rho_match_all_sites_call_par` / `contextual_match_call_par`).
    Sa,
    /// The naive Knotted-Topoi Appendix-A comprehension
    /// (`naive_kt_match_call_par` / the root-restricted per-entry receiver /
    /// `naive_kt_contextual_match_call_par`).
    Naive,
    /// The production host-σ REPLAY fallback: the host computes each firing's σ
    /// and fires it as one ground accept-send COMM against the same σ-echo
    /// receivers — the honest production comparison where the optimized
    /// locate-all fails closed (`nested_spine` only).
    Replay,
    /// R3 — the SELF-DRIVING naive variant (EXPLORATORY, pre-registered,
    /// USER-approved 2026-07-19; `lambda_chain` only, PatternGuard only). ONE
    /// session installs the persistent R3 receivers + one fixed-route seed; each firing's
    /// reduct is delivered to the in-session `^respread` walker family
    /// (`naive_kt_selfdriving_call_par`), so the chain normalizes in ONE
    /// injection — the first probe of the PERSISTENT-fire regime, DEVIATING
    /// from the same-firing-contract constraint BY DESIGN (the reduct's
    /// destination is the walker, not OUT). Ground truth: `firing_visible = n`
    /// (one accept COMM per β step) and the observed OUT multiset is the
    /// TERMINAL ATOM once.
    NaiveR3,
}

/// Every matcher column, in protocol order (R3 exploratory last).
pub const ALL_MATCHERS: [MatcherKind; 4] =
    [MatcherKind::Sa, MatcherKind::Naive, MatcherKind::Replay, MatcherKind::NaiveR3];

/// The naive Appendix-A guard encoding selector (forwarded to
/// [`NaiveGuardEncoding`] on the naive column; the optimized and replay columns
/// have no guard encoding and record `"-"`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardEncodingKind {
    /// The reject-never-consumes `Match`-pattern guard (the default; safe at
    /// every admitted subject).
    PatternGuard,
    /// The paper-literal consume-then-test encoding — SINGLE-CANDIDATE subjects
    /// only (the B2 partial-fire hazard exclusion, [`consume_test_admitted`]).
    ConsumeTest,
}

/// Every guard encoding, in protocol order.
pub const ALL_ENCODINGS: [GuardEncodingKind; 2] =
    [GuardEncodingKind::PatternGuard, GuardEncodingKind::ConsumeTest];

impl WorkloadKind {
    /// The stable CLI / group name of this workload.
    pub fn name(self) -> &'static str {
        match self {
            WorkloadKind::LambdaChain => "lambda_chain",
            WorkloadKind::SwapComb => "swap_comb",
            WorkloadKind::SwapSmall => "swap_small",
            WorkloadKind::WrapSwapCtx => "wrap_swap_ctx",
            WorkloadKind::NestedSpine => "nested_spine",
            WorkloadKind::MultiRuleShared => "multi_rule_shared",
        }
    }

    /// The FULL-protocol size ladder (the smoke ladder is the small prefix
    /// documented in `docs/benchmarks/data/sa-vs-naive/README.md` and driven by
    /// `smoke.sh`: lambda_chain {2, 4}, swap_comb {2, 4}, swap_small {2},
    /// wrap_swap_ctx {1}, nested_spine {2}, multi_rule_shared {402}).
    pub fn full_sizes(self) -> &'static [u64] {
        match self {
            WorkloadKind::LambdaChain => &[4, 8, 16, 32, 64],
            WorkloadKind::SwapComb => &[1, 2, 4, 8, 16, 32, 64],
            WorkloadKind::SwapSmall => &[1, 2, 3, 4, 5, 6, 7, 8],
            // Depth 2 fails closed on BOTH contextual emitters (pinned by
            // `tests::wrap_swap_ctx_depth_two_fails_closed_on_both_emitters`),
            // so the admitted ladder is exactly {1}.
            WorkloadKind::WrapSwapCtx => &[1],
            WorkloadKind::NestedSpine => &[2, 4, 8, 16],
            // The r × s cross product (n = 100·r + s): the r-scaling leg at
            // every shared depth AND the s-scaling leg at every rule count —
            // r ∈ {2, 4, 8} × s ∈ {1, 2, 3}.
            WorkloadKind::MultiRuleShared => &[201, 202, 203, 401, 402, 403, 801, 802, 803],
        }
    }

    /// The matcher columns of this workload's head-to-head cell.
    pub fn matchers(self) -> &'static [MatcherKind] {
        match self {
            // λ-chain additionally carries the R3 exploratory self-driving
            // column (single-session persistent-fire; see `MatcherKind::NaiveR3`).
            WorkloadKind::LambdaChain => {
                &[MatcherKind::Sa, MatcherKind::Naive, MatcherKind::NaiveR3]
            },
            WorkloadKind::SwapComb | WorkloadKind::SwapSmall | WorkloadKind::WrapSwapCtx => {
                &[MatcherKind::Sa, MatcherKind::Naive]
            },
            // The optimized locate-all fails closed on k ≥ 2 nested candidate
            // sites (B0), so the honest optimized-side column is the
            // production host-σ REPLAY fallback.
            WorkloadKind::NestedSpine => &[MatcherKind::Naive, MatcherKind::Replay],
            // The ONE-CALL locate-all likewise fails closed for r ≥ 2 (its
            // gate counts candidate sites ACROSS entries), but the per-rule
            // drive at admitted sites keeps the AUTOMATON on the optimized
            // column (see the module rustdoc §(vii)) — so this cell is a
            // genuine sa-vs-naive head-to-head, not a replay comparison.
            WorkloadKind::MultiRuleShared => &[MatcherKind::Sa, MatcherKind::Naive],
        }
    }

    /// Ground truth: how many rule firings size `n` of this workload produces
    /// (each firing lands exactly one observed value, so this is also the
    /// expected `observed_count`).
    pub fn expected_firings(self, n: u64) -> u64 {
        match self {
            WorkloadKind::LambdaChain => n,
            WorkloadKind::SwapComb => n,
            WorkloadKind::SwapSmall => 1,
            WorkloadKind::WrapSwapCtx => 1,
            WorkloadKind::NestedSpine => n,
            // One firing per rule: r = n / 100 (the `100·r + s` encoding).
            WorkloadKind::MultiRuleShared => n / 100,
        }
    }

    /// Whether size `n` is admitted for this workload (the single source of
    /// truth [`compile_workload`] and the driver's argument validation share).
    /// Sizes are open-ended except where an emitter admission fact closes them.
    pub fn admitted_size(self, n: u64) -> Result<(), String> {
        if n == 0 {
            return Err(format!("workload {} requires n >= 1", self.name()));
        }
        if self == WorkloadKind::WrapSwapCtx && n != 1 {
            return Err(format!(
                "wrap_swap_ctx admits ONLY depth 1: depth {n} fails closed on BOTH contextual \
                 emitters (the single-congruence hole bijection — pinned by the \
                 wrap_swap_ctx_depth_two_fails_closed_on_both_emitters unit test)"
            ));
        }
        if self == WorkloadKind::MultiRuleShared && (n < 100 || n.is_multiple_of(100)) {
            return Err(format!(
                "multi_rule_shared sizes encode n = 100·r + s (r = n/100 rules ≥ 1, \
                 s = n%100 shared-chain depth in 1..=99): {n} decodes to r = {} s = {}",
                n / 100,
                n % 100,
            ));
        }
        Ok(())
    }
}

/// Decode a `multi_rule_shared` size parameter `n = 100·r + s` into
/// `(r, s)` — the rule count and the shared `S`-chain depth. Callers must have
/// validated `n` through [`WorkloadKind::admitted_size`] first (r ≥ 1, s ≥ 1).
pub fn multi_rule_shared_params(n: u64) -> (usize, usize) {
    (
        usize::try_from(n / 100).expect("rule count fits usize"),
        usize::try_from(n % 100).expect("shared depth fits usize"),
    )
}

impl MatcherKind {
    /// The stable CLI / group / JSON name of this matcher column.
    pub fn name(self) -> &'static str {
        match self {
            MatcherKind::Sa => "sa",
            MatcherKind::Naive => "naive",
            MatcherKind::Replay => "replay",
            MatcherKind::NaiveR3 => "naive-r3",
        }
    }
}

impl GuardEncodingKind {
    /// The stable CLI / JSON name of this encoding.
    pub fn name(self) -> &'static str {
        match self {
            GuardEncodingKind::PatternGuard => "pattern-guard",
            GuardEncodingKind::ConsumeTest => "consume-test",
        }
    }

    /// The codegen-side encoding selector this kind forwards to.
    fn to_naive(self) -> NaiveGuardEncoding {
        match self {
            GuardEncodingKind::PatternGuard => NaiveGuardEncoding::PatternGuard,
            GuardEncodingKind::ConsumeTest => NaiveGuardEncoding::ConsumeTest,
        }
    }
}

/// Whether `matcher` is a column of `workload`'s head-to-head cell.
pub fn matcher_admitted(workload: WorkloadKind, matcher: MatcherKind) -> bool {
    workload.matchers().contains(&matcher)
}

/// Whether the `ConsumeTest` naive guard encoding is admitted for size `n` of
/// `workload`: single-candidate subjects ONLY (the B2 partial-fire hazard
/// exclusion — several candidate consumers racing one site's held tags). The
/// encoding only applies to the naive column; the optimized/replay columns
/// ignore it (and record `"-"`).
pub fn consume_test_admitted(workload: WorkloadKind, n: u64) -> bool {
    match workload {
        // Each per-step root drive installs exactly ONE receiver.
        WorkloadKind::LambdaChain => true,
        // m candidate receivers race the shared spread's tags for m > 1.
        WorkloadKind::SwapComb => n == 1,
        WorkloadKind::SwapSmall => true,
        // One hole premise ⇒ one per-hole receiver.
        WorkloadKind::WrapSwapCtx => true,
        // k ≥ 2 candidate receivers by construction.
        WorkloadKind::NestedSpine => false,
        // r candidate receivers (one per rule); single-candidate only at
        // r = 1 (n = 100 + s) — the same discipline as `swap_comb` m = 1.
        WorkloadKind::MultiRuleShared => n / 100 == 1,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Subject generators (pure, deterministic by construction)
// ─────────────────────────────────────────────────────────────────────────────

/// The identity function `λ.x` in reflected de-Bruijn form:
/// `^lambda(^bound(Z))` (the B2 suite's shape, verbatim).
fn identity_lambda() -> GroundTerm {
    GroundTerm::new(
        LAMBDA_REFLECT_LABEL,
        vec![GroundTerm::new(
            BOUND_VAR_REFLECT_LABEL,
            vec![GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL)],
        )],
    )
}

/// (i) The `App(Lam(^x. x), ·)` chain spine of depth `n` (reflected):
/// each root β step substitutes the argument for the identity's bound variable,
/// so the reduct IS the remaining chain — the spine reduces in exactly `n`
/// sequential root steps to the terminal `A`. Node count: `4n + 1`.
pub fn lambda_chain_subject(n: usize) -> GroundTerm {
    let mut term = GroundTerm::nullary("A");
    for _ in 0..n {
        term = GroundTerm::new("App", vec![identity_lambda(), term]);
    }
    term
}

/// The distinct nullary comb leaf `L{index}` of `swap_comb` (`pub` for the
/// driver-side generator unit tests, which live in the driver bin because a
/// `harness = false` criterion bench has no libtest harness to anchor a
/// `#[cfg(test)]` module). A leaf constructor tag is OPAQUE DATA to the
/// matcher (only `Swap` is a rule LHS root; σ slots carry the M-collapsed
/// `⟦subtree⟧` whatever its tag — the same free-form-leaf discipline as the B2
/// divergent-admission direct construction), so distinctness costs ONE node
/// per leaf instead of a log-width encoding tree. That also keeps the comb's
/// parallel eval width low — see [`INTERPRETER_SPLIT_REGRESSION_MIN`].
pub fn swap_comb_leaf(index: usize) -> GroundTerm {
    GroundTerm::nullary(format!("L{index}"))
}

/// (ii) The m-redex comb: a right-leaning INERT `Pair` spine carrying `m`
/// PAIRWISE-DISTINCT `Swap(L₂ᵢ, L₂ᵢ₊₁)` redexes (distinct nullary leaf
/// constructors, [`swap_comb_leaf`]), plus the directly-computed expected
/// contracta multiset `{ Pair(L₂ᵢ₊₁, L₂ᵢ) }`. `Pair` and the leaves are not
/// rule LHS roots, so exactly the `m` Swaps are candidate sites. Node count:
/// `4m − 1`.
pub fn swap_comb_subject(m: usize) -> (GroundTerm, Vec<RuntimeObservationValue>) {
    assert!(m >= 1, "the comb carries at least one redex");
    let swap_at =
        |i: usize| GroundTerm::new("Swap", vec![swap_comb_leaf(2 * i), swap_comb_leaf(2 * i + 1)]);
    let mut expected: Vec<RuntimeObservationValue> = Vec::with_capacity(m);
    for i in 0..m {
        expected.push(ground_to_observation(&GroundTerm::new(
            "Pair",
            vec![swap_comb_leaf(2 * i + 1), swap_comb_leaf(2 * i)],
        )));
    }
    let mut subject = swap_at(m - 1);
    for i in (0..m - 1).rev() {
        subject = GroundTerm::new("Pair", vec![swap_at(i), subject]);
    }
    (subject, expected)
}

/// (iv) The crossover floor: a single `Swap(A, B)` under `k − 1` inert `Pair`
/// wrappers (`k = 1` is the bare root redex). ONE candidate site at every k;
/// the fired σ-receiver lands `Pair(B, A)` regardless of the nesting depth
/// (the contractum, not a context reassembly). Node count: `2k + 1`.
pub fn swap_small_subject(k: usize) -> (GroundTerm, Vec<RuntimeObservationValue>) {
    assert!(k >= 1, "the crossover floor starts at the bare redex");
    let mut subject =
        GroundTerm::new("Swap", vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")]);
    for _ in 1..k {
        subject = GroundTerm::new("Pair", vec![subject, GroundTerm::nullary("B")]);
    }
    let expected = vec![ground_to_observation(&GroundTerm::new(
        "Pair",
        vec![GroundTerm::nullary("B"), GroundTerm::nullary("A")],
    ))];
    (subject, expected)
}

/// (v) The CtxDemo contextual subject: `depth` `Wrap` wrappers around
/// `Swap(A, B)`. Depth 1 (`Wrap(Swap(A, B))`) is the admitted hole shape,
/// reassembling to `Wrap(Pair(B, A))`; depth 2 fails closed on BOTH contextual
/// emitters (pinned by the unit test — see [`WorkloadKind::admitted_size`]).
pub fn wrap_swap_ctx_subject(depth: usize) -> (GroundTerm, Vec<RuntimeObservationValue>) {
    assert!(depth >= 1, "the contextual subject wraps at least once");
    let mut subject =
        GroundTerm::new("Swap", vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")]);
    for _ in 0..depth {
        subject = GroundTerm::new("Wrap", vec![subject]);
    }
    let mut reduced =
        GroundTerm::new("Pair", vec![GroundTerm::nullary("B"), GroundTerm::nullary("A")]);
    for _ in 0..depth {
        reduced = GroundTerm::new("Wrap", vec![reduced]);
    }
    (subject, vec![ground_to_observation(&reduced)])
}

/// The distinct nullary leaf of `nested_spine` candidate site `i`.
fn nested_spine_leaf(i: usize) -> GroundTerm {
    GroundTerm::nullary(format!("L{i}"))
}

/// (vi) The nested k-candidate spine: a right-leaning inert `Pair` comb whose
/// k leaves are `f(g(Lᵢ))` — k head-`f` candidate sites with ONE true redex
/// each (the B2 divergent-admission test's shape, widened from k = 2). The
/// expected multiset is the pairwise-distinct `{ L₀ … L₍ₖ₋₁₎ }` (each firing's
/// σ[x], forwarded by its one-shot σ-echo).
pub fn nested_spine_subject(k: usize) -> (GroundTerm, Vec<RuntimeObservationValue>) {
    assert!(k >= 1, "the spine carries at least one candidate site");
    let fg =
        |i: usize| GroundTerm::new("f", vec![GroundTerm::new("g", vec![nested_spine_leaf(i)])]);
    let mut expected: Vec<RuntimeObservationValue> = Vec::with_capacity(k);
    for i in 0..k {
        expected.push(ground_to_observation(&nested_spine_leaf(i)));
    }
    let mut subject = fg(k - 1);
    for i in (0..k - 1).rev() {
        subject = GroundTerm::new("Pair", vec![fg(i), subject]);
    }
    (subject, expected)
}

/// The direct-construction `f(g(x))` ruleset of `nested_spine` (admission-matrix
/// style — no demo language): ONE nested entry routed to
/// [`NESTED_SPINE_ACCEPT`].
pub fn nested_spine_ruleset() -> InRhoMatchingRuleset {
    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app("f".to_string(), vec![Pattern::app("g".to_string(), vec![Pattern::var("x")])]),
    )])
    .expect("f(g(x)) compiles to a positional automaton");
    InRhoMatchingRuleset {
        automaton,
        accept_channels: vec![(PatternId(0), NESTED_SPINE_ACCEPT.to_string())],
        language_fingerprint: NESTED_SPINE_FINGERPRINT.to_string(),
        deferred: Vec::new(),
        native_dispatch: Vec::new(),
        ac_dispatch: Vec::new(),
        contextual_dispatch: Vec::new(),
        structural_ac_dispatch: Vec::new(),
        nested_structural_ac_dispatch: Vec::new(),
    }
}

/// The distinct nullary contractum leaf of `multi_rule_shared` rule `i`
/// (`Kᵢ`; a leaf constructor tag is OPAQUE DATA to the matcher — the same
/// free-form-leaf discipline as [`swap_comb_leaf`]).
pub fn multi_rule_shared_leaf(rule: usize) -> GroundTerm {
    GroundTerm::nullary(format!("K{rule}"))
}

/// The root op of `multi_rule_shared` rule `i` (`Rᵢ` — pairwise distinct
/// across the r rules, which is exactly what the naive duplicate-root gate
/// requires).
fn multi_rule_shared_root_op(rule: usize) -> String {
    format!("R{rule}")
}

/// Rule i's LHS pattern `Rᵢ(Sˢ(x))`: the DISTINCT root over the ONE SHARED
/// non-root sub-pattern chain `Sˢ(x)`. Every rule uses the SAME var name `x`
/// and the SAME `S` chain, so the interner shares the whole sub-pattern state
/// set across all r entries (`state_count = r + s + 1`). (`pub` for the
/// driver-bin state-sharing unit test, which compares the combined interned
/// count against the per-rule sum.)
pub fn multi_rule_shared_pattern(rule: usize, shared_depth: usize) -> Pattern<String> {
    let mut inner = Pattern::var("x");
    for _ in 0..shared_depth {
        inner = Pattern::app("S".to_string(), vec![inner]);
    }
    Pattern::app(multi_rule_shared_root_op(rule), vec![inner])
}

/// (vii) The r-rule shared-sub-pattern subject: a right-leaning inert `Pair`
/// comb whose r leaves are `Rᵢ(Sˢ(Kᵢ))` — one redex PER RULE, each rule's
/// DISTINCT root over its own subject copy of the shared `Sˢ` sub-structure.
/// The expected multiset is the pairwise-distinct { K₀ … K₍ᵣ₋₁₎ } (rule i's
/// σ[x] = its contractum, forwarded by rule i's OWN accept channel's σ-echo —
/// so the observation pins each rule fired exactly once). Node count:
/// `(r − 1) + r·(s + 2)`.
pub fn multi_rule_shared_subject(r: usize, s: usize) -> (GroundTerm, Vec<RuntimeObservationValue>) {
    assert!(r >= 1, "the pattern set carries at least one rule");
    assert!(s >= 1, "the shared sub-pattern chain has at least one level");
    let redex_at = |i: usize| {
        let mut term = multi_rule_shared_leaf(i);
        for _ in 0..s {
            term = GroundTerm::new("S", vec![term]);
        }
        GroundTerm::new(multi_rule_shared_root_op(i), vec![term])
    };
    let mut expected: Vec<RuntimeObservationValue> = Vec::with_capacity(r);
    for i in 0..r {
        expected.push(ground_to_observation(&multi_rule_shared_leaf(i)));
    }
    let mut subject = redex_at(r - 1);
    for i in (0..r - 1).rev() {
        subject = GroundTerm::new("Pair", vec![redex_at(i), subject]);
    }
    (subject, expected)
}

/// The direct-construction r-rule ruleset of `multi_rule_shared`
/// (admission-matrix style — no demo language): ALL r nested entries compiled
/// into ONE interned automaton (the pattern-set sharing under test: the
/// `Sˢ(x)` chain interns to a single shared state set across every entry),
/// each entry routed to its OWN accept channel [`multi_rule_shared_accept`].
pub fn multi_rule_shared_ruleset(r: usize, s: usize) -> InRhoMatchingRuleset {
    let patterns: Vec<(PatternId, Pattern<String>)> = (0..r)
        .map(|i| (PatternId(i), multi_rule_shared_pattern(i, s)))
        .collect();
    let automaton = SetAutomaton::compile_structural(patterns)
        .expect("the r-rule shared-sub-pattern set compiles to a positional automaton");
    InRhoMatchingRuleset {
        automaton,
        accept_channels: (0..r)
            .map(|i| (PatternId(i), multi_rule_shared_accept(i)))
            .collect(),
        language_fingerprint: MULTI_RULE_SHARED_FINGERPRINT.to_string(),
        deferred: Vec::new(),
        native_dispatch: Vec::new(),
        ac_dispatch: Vec::new(),
        contextual_dispatch: Vec::new(),
        structural_ac_dispatch: Vec::new(),
        nested_structural_ac_dispatch: Vec::new(),
    }
}

/// The structural E-6a PathMap keys of every `subject` node whose head is one of
/// `ruleset`'s compiled entry root ops. This quarantined comparison treatment
/// deliberately keeps its component-wise trie keys; the optimized positional
/// spread uses a private fixed-width subject index instead. This is the site
/// enumeration of the `multi_rule_shared` E-6a treatment's per-rule drive;
/// for that family it returns exactly r pairwise NON-ANCESTRAL comb-leaf
/// positions, one per rule (pinned by the driver-bin unit tests).
pub fn multi_rule_shared_sites(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    root_site: &str,
) -> Vec<String> {
    let view = ruleset.automaton.view();
    let roots: BTreeSet<String> = (0..view.entry_count())
        .filter_map(|entry| match view.node(view.entry_root_state(entry)) {
            AutomatonNode::App { op, .. } => Some(op.to_string()),
            AutomatonNode::Var => None,
        })
        .collect();
    fn walk(node: &GroundTerm, location: &str, roots: &BTreeSet<String>, sites: &mut Vec<String>) {
        if roots.contains(&node.constructor) {
            sites.push(location.to_string());
        }
        for (index, child) in node.children.iter().enumerate() {
            let child_location = spread_child_location(location, &node.constructor, index);
            walk(child, &child_location, roots, sites);
        }
    }
    let mut sites: Vec<String> = Vec::new();
    walk(subject, root_site, &roots, &mut sites);
    sites
}

/// Count the nodes of a `GroundTerm` subject (the generator-size metric the
/// unit tests pin and the driver's run-header records).
pub fn node_count(term: &GroundTerm) -> usize {
    1 + term.children.iter().map(node_count).sum::<usize>()
}

// ─────────────────────────────────────────────────────────────────────────────
// Observation plumbing (decode + multiset comparison, mirroring B2)
// ─────────────────────────────────────────────────────────────────────────────

/// The observation a `GroundTerm` subject decodes back to on OUT (the decoder
/// counterpart of `reflect_ground_term_par` over a positional tree).
pub fn ground_to_observation(term: &GroundTerm) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: term.constructor.clone(),
        children: term.children.iter().map(ground_to_observation).collect(),
    }
}

/// Rebuild an observed OUT value into the `GroundTerm` subject of the NEXT
/// β-chain step (the per-step drive is fed by what the reducer actually
/// landed, never a host-side prediction). The β-chain reducts are pure
/// positional constructor terms, so any other observation variant is an error.
fn observation_to_ground(value: &RuntimeObservationValue) -> Result<GroundTerm, String> {
    match value {
        RuntimeObservationValue::Term { constructor, children } => {
            let mut ground_children: Vec<GroundTerm> = Vec::with_capacity(children.len());
            for child in children {
                ground_children.push(observation_to_ground(child)?);
            }
            Ok(GroundTerm::new(constructor.clone(), ground_children))
        },
        other => Err(format!("a β-chain reduct must be a pure constructor term, got {other:?}")),
    }
}

/// Sort an observation multiset into its canonical (debug-render) order. The
/// matchers' τ-COMM schedules differ, so OUT arrival order differs — the
/// MULTISET is the visible-firing content the same-CLTS claim constrains.
pub fn sorted_multiset(mut values: Vec<RuntimeObservationValue>) -> Vec<RuntimeObservationValue> {
    values.sort_by_key(|value| format!("{value:?}"));
    values
}

/// Decode every raw observed `Par` into a [`RuntimeObservationValue`], failing
/// loudly on any undecodable resting value.
fn decode_observed(observed: &[Par]) -> Result<Vec<RuntimeObservationValue>, String> {
    let mut values: Vec<RuntimeObservationValue> = Vec::with_capacity(observed.len());
    for par in observed {
        values.push(
            par_as_runtime_observation_value(par)
                .ok_or_else(|| format!("undecodable observation value on OUT: {par:?}"))?,
        );
    }
    Ok(values)
}

/// The accept channel of the compiled entry at view index `entry` (the
/// `InRhoMatchingRuleset` lockstep-invariant lookup, mirrored from B2).
fn entry_accept_channel(ruleset: &InRhoMatchingRuleset, entry: usize) -> Result<String, String> {
    let pid = ruleset.automaton.view().entry_id(entry);
    ruleset
        .accept_channels
        .iter()
        .find(|(entry_pid, _)| *entry_pid == pid)
        .map(|(_, channel)| channel.clone())
        .ok_or_else(|| "every compiled automaton entry has an accept channel".to_string())
}

fn quoted(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

/// A σ-echo observer for a direct-construction accept (the B2 shape, verbatim):
/// `for(y_0,…,y_{k-1}, o <- accept){ o!(y_0) | … | o!(y_{k-1}) }` forwards each
/// σ slot to the accept's dynamic out channel. ONE-SHOT — the k-firing
/// `nested_spine` drive appends k copies on its one accept channel, and the
/// r-rule `multi_rule_shared` drive appends one per PER-RULE accept channel
/// ([`workload_echo_channels`]).
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

/// One host-σ REPLAY firing of `nested_spine` site `i`: the GROUND accept send
/// `@"sa:fg"!(⟦Lᵢ⟧, @"OUT")` — the host computed σ[x] = Lᵢ (matching on the
/// host, exactly what the production σ-replay fallback does where locate-all
/// fails closed) and fires it as one COMM against the σ-echo receivers. The
/// send is byte-shaped like `build_accept_send`'s accept (σ slots then `@out`),
/// with the σ slot already reflected ground data instead of a capture-bound
/// variable.
fn nested_spine_replay_send(i: usize) -> Par {
    let reflected = reflect_ground_term_par(&nested_spine_leaf(i), NESTED_SPINE_FINGERPRINT);
    new_send_par(
        quoted(NESTED_SPINE_ACCEPT),
        vec![reflected, quoted(OUT_CHANNEL)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Compiled workloads (the B3 hoist boundary) + the per-rep drive
// ─────────────────────────────────────────────────────────────────────────────

/// The compiled matching source a workload drives against.
enum CompiledSource {
    /// A demo language compiled through the B3 warm-mode hoist
    /// ([`compile_bench_language`]): ruleset + installed σ-receiver program.
    Language(CompiledBenchLanguage),
    /// The direct-construction `nested_spine` ruleset (no installed program —
    /// the per-rep drive composes its own σ-echo receivers).
    Direct(InRhoMatchingRuleset),
}

/// One workload cell's compiled artifacts: produced ONCE per (workload, n) by
/// [`compile_workload`] — OUTSIDE the measured region for the warm groups,
/// INSIDE it for the cold groups — and reused by reference across reps.
pub struct CompiledWorkload {
    /// Which workload family this is.
    pub kind: WorkloadKind,
    /// The size parameter.
    pub n: u64,
    /// The initial ground subject (for `lambda_chain` the step-0 spine; later
    /// steps are rebuilt from the OBSERVED reducts).
    pub subject: GroundTerm,
    /// The expected observation values: for `lambda_chain` in STEP order (step
    /// k's single reduct at index k), for every other workload the expected
    /// firing multiset (compared sorted).
    pub expected: Vec<RuntimeObservationValue>,
    source: CompiledSource,
}

impl CompiledWorkload {
    /// The compiled in-Rho matching ruleset both matcher columns consume.
    /// (`pub` for the driver-side admission unit tests.)
    pub fn ruleset(&self) -> &InRhoMatchingRuleset {
        match &self.source {
            CompiledSource::Language(compiled) => &compiled.ruleset,
            CompiledSource::Direct(ruleset) => ruleset,
        }
    }

    /// The installed σ-receiver program each drive composes its call against
    /// (`None` for the direct-construction `nested_spine`, whose per-rep drive
    /// installs its own σ-echo receivers).
    fn installed_program(&self) -> Option<&Par> {
        match &self.source {
            CompiledSource::Language(compiled) => Some(&compiled.installed_program),
            CompiledSource::Direct(_) => None,
        }
    }
}

/// Compile ONE workload cell: validate the size (fail-closed on the pinned
/// non-admitted sizes), build the deterministic subject + expected values, and
/// perform the per-language B3 hoist (reconstruct → lower → plan → compile →
/// installed program) or the direct `f(g(x))` construction. This is the ONLY
/// compilation site — the warm benchmark groups hoist it out of the measured
/// region, the cold groups deliberately re-run it inside.
pub fn compile_workload(kind: WorkloadKind, n: u64) -> Result<CompiledWorkload, String> {
    kind.admitted_size(n)?;
    let size = usize::try_from(n).map_err(|_| format!("size {n} does not fit usize"))?;
    match kind {
        WorkloadKind::LambdaChain => {
            let source = LambdaDemoLanguage
                .metadata()
                .definition_source()
                .ok_or("LambdaDemo must expose its definition_source")?;
            let compiled = compile_bench_language(source)?;
            if compiled.ruleset.automaton.view().entry_count() != 1 {
                return Err("LambdaDemo compiles exactly the Beta entry (workload precondition)"
                    .to_string());
            }
            let subject = lambda_chain_subject(size);
            // Step k's single expected reduct is the remaining chain n − k − 1.
            let mut expected: Vec<RuntimeObservationValue> = Vec::with_capacity(size);
            for step in 0..size {
                expected.push(ground_to_observation(&lambda_chain_subject(size - step - 1)));
            }
            Ok(CompiledWorkload {
                kind,
                n,
                subject,
                expected,
                source: CompiledSource::Language(compiled),
            })
        },
        WorkloadKind::SwapComb | WorkloadKind::SwapSmall => {
            let source = SwapDemoLanguage
                .metadata()
                .definition_source()
                .ok_or("SwapDemo must expose its definition_source")?;
            let compiled = compile_bench_language(source)?;
            let (subject, expected) = match kind {
                WorkloadKind::SwapComb => swap_comb_subject(size),
                _ => swap_small_subject(size),
            };
            Ok(CompiledWorkload {
                kind,
                n,
                subject,
                expected,
                source: CompiledSource::Language(compiled),
            })
        },
        WorkloadKind::WrapSwapCtx => {
            let source = CtxDemoLanguage
                .metadata()
                .definition_source()
                .ok_or("CtxDemo must expose its definition_source")?;
            let compiled = compile_bench_language(source)?;
            let (subject, expected) = wrap_swap_ctx_subject(size);
            Ok(CompiledWorkload {
                kind,
                n,
                subject,
                expected,
                source: CompiledSource::Language(compiled),
            })
        },
        WorkloadKind::NestedSpine => {
            let (subject, expected) = nested_spine_subject(size);
            Ok(CompiledWorkload {
                kind,
                n,
                subject,
                expected,
                source: CompiledSource::Direct(nested_spine_ruleset()),
            })
        },
        WorkloadKind::MultiRuleShared => {
            let (r, s) = multi_rule_shared_params(n);
            let (subject, expected) = multi_rule_shared_subject(r, s);
            Ok(CompiledWorkload {
                kind,
                n,
                subject,
                expected,
                source: CompiledSource::Direct(multi_rule_shared_ruleset(r, s)),
            })
        },
    }
}

/// The direct-construction σ-echo channels one rep of `compiled` installs
/// (each gets ONE one-shot arity-1 [`sigma_echo_receiver`]): `nested_spine`
/// appends k copies of its ONE accept channel (k firings on one channel);
/// `multi_rule_shared` appends each rule's OWN accept channel once (r firings,
/// one per channel — the per-rule routing that pins rule attribution). Every
/// language-compiled workload installs its hoisted σ-receiver program instead
/// (empty here).
fn workload_echo_channels(compiled: &CompiledWorkload) -> Vec<String> {
    match compiled.kind {
        WorkloadKind::NestedSpine => {
            let k = usize::try_from(compiled.n).expect("k fits usize");
            vec![NESTED_SPINE_ACCEPT.to_string(); k]
        },
        WorkloadKind::MultiRuleShared => compiled
            .ruleset()
            .accept_channels
            .iter()
            .map(|(_, channel)| channel.clone())
            .collect(),
        _ => Vec::new(),
    }
}

/// One rep's outcome: the (possibly step-aggregated) [`BenchRunResult`] plus
/// the two harness-level phases the result's own timers do not cover —
/// `emission` (per-call emitter + program composition + size accounting) and
/// `bringup` (counting-runtime construction). Warm measured time =
/// `emission + result.build + result.inj + result.readback`; cold adds the
/// compile span and `bringup`. Verification/decode time is in NO phase.
pub struct WorkloadRepOutcome {
    /// The instrumented run record (step-aggregated for `lambda_chain`).
    pub result: BenchRunResult,
    /// Total per-call emission + composition time across the rep's injections.
    pub emission: Duration,
    /// Total counting-runtime construction time across the rep's injections.
    pub bringup: Duration,
}

/// A rep that did not finish (or failed verification): the driver records it as
/// a `"dnf":true` JSON line with this reason and continues.
#[derive(Debug)]
pub struct WorkloadFailure {
    /// Human-readable cause (guard breach, emitter fail-closed, runtime error,
    /// or observed-vs-expected mismatch).
    pub reason: String,
}

impl WorkloadFailure {
    fn new(reason: impl Into<String>) -> WorkloadFailure {
        WorkloadFailure { reason: reason.into() }
    }
}

/// The self-describing identity carried on every emitted record.
fn bench_params(
    kind: WorkloadKind,
    matcher: MatcherKind,
    encoding: GuardEncodingKind,
    n: u64,
    rep: u64,
) -> BenchWorkloadParams {
    BenchWorkloadParams {
        name: kind.name().to_string(),
        matcher: matcher.name().to_string(),
        // Only the naive column HAS a guard encoding (bench_support convention:
        // "-" for the non-naive columns).
        encoding: match matcher {
            // R3 is PatternGuard-only BY CONSTRUCTION (ConsumeTest is rejected
            // up front), so its recorded encoding is the genuine demand
            // encoding, mirroring the naive column.
            MatcherKind::Naive | MatcherKind::NaiveR3 => encoding.name().to_string(),
            MatcherKind::Sa | MatcherKind::Replay => "-".to_string(),
        },
        n,
        rep,
    }
}

/// Zeroed COMM-classification totals for step aggregation.
fn zero_comm_snapshot() -> CommCounterSnapshot {
    CommCounterSnapshot {
        matching_tau: 0,
        firing_visible: 0,
        subst_tau: 0,
        respread_tau: 0,
        drive_tau: 0,
        ac_carrier: 0,
        pathmap_index: 0,
        contextual_plumbing: 0,
        observation: 0,
        other: 0,
        join_arity_gt1: 0,
        unknown_channel_samples: Vec::new(),
    }
}

/// Accumulate one per-step snapshot into the rep totals (samples stay bounded
/// by [`MAX_UNKNOWN_CHANNEL_SAMPLES`], mirroring the source counters).
fn accumulate_comm(total: &mut CommCounterSnapshot, step: &CommCounterSnapshot) {
    total.matching_tau += step.matching_tau;
    total.firing_visible += step.firing_visible;
    total.subst_tau += step.subst_tau;
    total.respread_tau += step.respread_tau;
    total.drive_tau += step.drive_tau;
    total.ac_carrier += step.ac_carrier;
    total.pathmap_index += step.pathmap_index;
    total.contextual_plumbing += step.contextual_plumbing;
    total.observation += step.observation;
    total.other += step.other;
    total.join_arity_gt1 += step.join_arity_gt1;
    for sample in &step.unknown_channel_samples {
        if total.unknown_channel_samples.len() < MAX_UNKNOWN_CHANNEL_SAMPLES {
            total.unknown_channel_samples.push(sample.clone());
        }
    }
}

/// Emit the per-call `call` `Par` for one injection of `(kind, matcher)` over
/// `subject`, plus the emitter's site/receiver count for the installed-count
/// consistency checks (`None` where the emitter reports no count).
/// (`pub` for the driver-side admission unit tests.)
pub fn emit_call(
    kind: WorkloadKind,
    matcher: MatcherKind,
    encoding: GuardEncodingKind,
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
) -> Result<(Par, Option<usize>), WorkloadFailure> {
    match (kind, matcher) {
        (WorkloadKind::LambdaChain, MatcherKind::Sa) => {
            let call = in_rho_match_call_par(ruleset, subject, ROOT_SITE, OUT_CHANNEL)
                .map_err(|e| WorkloadFailure::new(format!("optimized root emitter: {e:?}")))?;
            Ok((call, None))
        },
        (WorkloadKind::LambdaChain, MatcherKind::NaiveR3) => {
            // R3 (EXPLORATORY, pre-registered): the SELF-DRIVING single-session
            // call — persistent R3 root receiver + finite `^respread` route
            // PDA + one reflected-chain seed; the session normalizes
            // in-runtime (see `naive_kt_selfdriving_call_par`'s rustdoc).
            // PatternGuard-only by construction (the encoding parameter is
            // rejected as ConsumeTest before any drive reaches this arm).
            let (call, installed) =
                naive_kt_selfdriving_call_par(ruleset, subject, ROOT_SITE, OUT_CHANNEL)
                    .map_err(|e| WorkloadFailure::new(format!("R3 self-driving emitter: {e:?}")))?;
            Ok((call, Some(installed)))
        },
        (WorkloadKind::LambdaChain, MatcherKind::Naive) => {
            // The root-restricted Appendix-A drive (B2's `naive_root_beta_call`):
            // the entry's per-site receiver at exactly the root site ∥ the ONE
            // spread of the whole subject.
            let view = ruleset.automaton.view();
            let accept_channel = entry_accept_channel(ruleset, 0).map_err(WorkloadFailure::new)?;
            let receiver = naive_kt_entry_receiver_par(
                &view,
                0,
                subject,
                ROOT_SITE,
                &accept_channel,
                OUT_CHANNEL,
                &ruleset.language_fingerprint,
                encoding.to_naive(),
            )
            .map_err(|e| WorkloadFailure::new(format!("naive root receiver emitter: {e:?}")))?;
            let call =
                receiver.append(spread_term_par(subject, &ruleset.language_fingerprint, ROOT_SITE));
            Ok((call, Some(1)))
        },
        (WorkloadKind::SwapComb | WorkloadKind::SwapSmall, MatcherKind::Sa) => {
            let (call, sites) =
                in_rho_match_all_sites_call_par(ruleset, subject, ROOT_SITE, OUT_CHANNEL).map_err(
                    |e| WorkloadFailure::new(format!("optimized locate-all emitter: {e:?}")),
                )?;
            Ok((call, Some(sites)))
        },
        (
            WorkloadKind::SwapComb
            | WorkloadKind::SwapSmall
            | WorkloadKind::NestedSpine
            | WorkloadKind::MultiRuleShared,
            MatcherKind::Naive,
        ) => {
            let (call, installed) = naive_kt_match_call_par(
                ruleset,
                subject,
                ROOT_SITE,
                OUT_CHANNEL,
                encoding.to_naive(),
            )
            .map_err(|e| WorkloadFailure::new(format!("naive comprehension emitter: {e:?}")))?;
            Ok((call, Some(installed)))
        },
        (WorkloadKind::MultiRuleShared, MatcherKind::Sa) => {
            // The PER-RULE drive at admitted sites (module rustdoc §(vii)):
            // the ONE-call locate-all fails closed for r ≥ 2 (its
            // `NestedEntryMultiSite` gate counts candidate sites ACROSS
            // entries — pinned by the driver-bin unit tests), so the sa column
            // composes the SAME production per-site emitter — ALL r entries'
            // shared interned automaton at each site — once per admitted site
            // (each site in isolation is exactly the admitted nested-ruleset
            // ≤ 1-site install), then ONE spread of the whole subject.
            // Contention-free FOR THIS FAMILY: the sites are pairwise
            // non-ancestral comb-leaf positions and no rule root op occurs at
            // any non-root pattern position (both pinned), so no installed
            // network's descent read aliases another's root read.
            let view = ruleset.automaton.view();
            let targets: Vec<AutomatonAcceptTarget> = ruleset
                .accept_channels
                .iter()
                .map(|(pattern, accept_channel)| AutomatonAcceptTarget {
                    pattern: *pattern,
                    accept_channel: accept_channel.clone(),
                    out_channel: OUT_CHANNEL.to_string(),
                })
                .collect();
            let (call, site_count) = multi_pattern_receiver_networks_at_rule_roots_par(
                &view,
                subject,
                ROOT_SITE,
                &targets,
                &ruleset.language_fingerprint,
            )
            .map_err(|e| {
                WorkloadFailure::new(format!("optimized per-site network emitter: {e:?}"))
            })?;
            let call =
                call.append(spread_term_par(subject, &ruleset.language_fingerprint, ROOT_SITE));
            Ok((call, Some(site_count)))
        },
        (WorkloadKind::WrapSwapCtx, MatcherKind::Sa) => {
            let call = contextual_match_call_par(ruleset, subject, ROOT_SITE, OUT_CHANNEL)
                .map_err(|e| {
                    WorkloadFailure::new(format!("optimized contextual emitter: {e:?}"))
                })?;
            Ok((call, None))
        },
        (WorkloadKind::WrapSwapCtx, MatcherKind::Naive) => {
            let call = naive_kt_contextual_match_call_par(
                ruleset,
                subject,
                ROOT_SITE,
                OUT_CHANNEL,
                encoding.to_naive(),
            )
            .map_err(|e| WorkloadFailure::new(format!("naive contextual emitter: {e:?}")))?;
            Ok((call, None))
        },
        (WorkloadKind::NestedSpine, MatcherKind::Replay) => {
            // Host-computed σ replayed as COMMs: one ground accept send per
            // candidate site (NO spread, NO in-Rho matching network).
            let k = usize::try_from(nested_spine_expected(kind, subject))
                .expect("nested_spine k fits usize");
            let mut call = Par::default();
            for i in 0..k {
                call = call.append(nested_spine_replay_send(i));
            }
            Ok((call, Some(k)))
        },
        (kind, matcher) => Err(WorkloadFailure::new(format!(
            "matcher `{}` is not a column of workload `{}` (admitted: {:?})",
            matcher.name(),
            kind.name(),
            kind.matchers().iter().map(|m| m.name()).collect::<Vec<_>>(),
        ))),
    }
}

/// The k of a `nested_spine` subject (its head-`f` candidate count) — read off
/// the right `Pair` comb structurally so the emitters and the expected counts
/// can never drift. (`pub` for the driver-side generator unit tests.)
pub fn nested_spine_expected(kind: WorkloadKind, subject: &GroundTerm) -> u64 {
    debug_assert_eq!(kind, WorkloadKind::NestedSpine);
    let mut node = subject;
    let mut count: u64 = 0;
    loop {
        match node.constructor.as_str() {
            "Pair" => {
                count += 1; // the left leaf is one f(g(Lᵢ)) site
                node = &node.children[1];
            },
            "f" => return count + 1,
            other => panic!("a nested_spine subject is a Pair/f comb, found `{other}`"),
        }
    }
}

/// The interpreter's PER-EVAL-LEVEL parallel term count of one `Par` — exactly
/// the `terms` list `DebruijnInterpreter::eval_inner` splits its random over:
/// sends + receives + news + matches + conditionals + bundles + the
/// `EVar`/`EMethod` expressions (every other expression is inert data at
/// process position).
fn top_level_width(par: &Par) -> usize {
    par.sends.len()
        + par.receives.len()
        + par.news.len()
        + par.matches.len()
        + par.conditionals.len()
        + par.bundles.len()
        + par
            .exprs
            .iter()
            .filter(|expr| {
                matches!(
                    expr.expr_instance,
                    Some(ExprInstance::EVarBody(_)) | Some(ExprInstance::EMethodBody(_))
                )
            })
            .count()
}

/// The STRUCTURAL maximum of [`top_level_width`] over a program's eval levels:
/// the top level plus every process position the reducer later evaluates as
/// its own `Par` (`new`/bundle bodies, receive bodies and conditions, match
/// case bodies, conditional branches). Send DATA is deliberately not walked —
/// it is produced as data, not evaluated (the Track-B workloads never
/// re-evaluate received values as processes). Used by the offline width probe
/// ([`cell_width_probe`]) for the [`INTERPRETER_SPLIT_REGRESSION_MIN`]
/// provenance zone.
pub fn max_eval_width(par: &Par) -> usize {
    let mut width = top_level_width(par);
    let mut visit = |child: &Option<Par>| {
        if let Some(child) = child {
            width = width.max(max_eval_width(child));
        }
    };
    for new in &par.news {
        visit(&new.p);
    }
    for bundle in &par.bundles {
        visit(&bundle.body);
    }
    for receive in &par.receives {
        visit(&receive.body);
        visit(&receive.condition);
    }
    for match_node in &par.matches {
        for case in &match_node.cases {
            visit(&case.source);
        }
    }
    for conditional in &par.conditionals {
        visit(&conditional.if_true);
        visit(&conditional.if_false);
    }
    width
}

/// Compose the FULL injected program for one `(workload, matcher)` injection
/// over `subject`: the emitted call, the hoisted installed σ-receiver program
/// (when the workload has one), and the direct-construction σ-echo observers
/// (when it does not; one one-shot arity-1 [`sigma_echo_receiver`] per
/// `echo_channels` entry — [`workload_echo_channels`]) — the SINGLE
/// composition site shared by the live drive ([`drive_single_injection`]) and
/// the offline width probe ([`cell_width_probe`]), so the guard can never
/// drift from the drive. Also enforces the emitter site-count consistency
/// check.
fn composed_program_for(
    kind: WorkloadKind,
    matcher: MatcherKind,
    encoding: GuardEncodingKind,
    ruleset: &InRhoMatchingRuleset,
    installed_program: Option<&Par>,
    echo_channels: &[String],
    subject: &GroundTerm,
    n: u64,
) -> Result<Par, WorkloadFailure> {
    let (call, emitted_count) = emit_call(kind, matcher, encoding, ruleset, subject)?;
    if let Some(count) = emitted_count {
        let expected_sites = match kind {
            WorkloadKind::LambdaChain => 1, // the root-restricted per-step drive
            _ => {
                usize::try_from(kind.expected_firings(n)).expect("expected firing count fits usize")
            },
        };
        if count != expected_sites {
            return Err(WorkloadFailure::new(format!(
                "emitter located/installed {count} sites, expected {expected_sites} \
                 (workload {}, matcher {})",
                kind.name(),
                matcher.name(),
            )));
        }
    }
    let mut program = match installed_program {
        Some(installed) => installed.clone(),
        None => Par::default(),
    };
    for channel in echo_channels {
        program = program.append(sigma_echo_receiver(channel, 1));
    }
    Ok(program.append(call))
}

/// The pre-injection guard shared by every drive: the
/// [`MAX_PROGRAM_ENCODED_LEN`] size bound. Fails CLOSED with a structured
/// reason.
///
/// RETIRED (interpreter fix): this guard previously ALSO failed closed on the
/// f1r3node `split_byte(i8)` panic zone (`interpreter-split-hazard` DNF for
/// any parallel eval width in [129, 256]). The interpreter is fixed — see
/// [`INTERPRETER_SPLIT_REGRESSION_MIN`] (f1r3node branch
/// `fix/split-byte-width-range`, commit 31b354e6) — so the width gate is
/// gone: in-zone cells now RUN, and the driver-bin unit tests assert the zone
/// works (9-cell in-zone pin + a width-129 actual-eval spot check). The
/// driver's per-rep `catch_unwind` panic guard remains as belt-and-suspenders
/// against any future interpreter panic.
fn guard_composed_program(program: &Par) -> Result<(), WorkloadFailure> {
    let encoded_len = program.encoded_len();
    if encoded_len >= MAX_PROGRAM_ENCODED_LEN {
        return Err(WorkloadFailure::new(format!(
            "encoded-len-guard: composed program is {encoded_len} bytes \
             (limit {MAX_PROGRAM_ENCODED_LEN})"
        )));
    }
    Ok(())
}

/// The OFFLINE width probe of one cell `(compiled workload, matcher,
/// encoding)`: composes every injection the cell's rep would perform — for
/// `lambda_chain` one composed program per GROUND-TRUTH step subject (the
/// observed reducts are verified equal to those, so the probe is exact) — and
/// reports both the maximum width and whether ANY single injection's width
/// falls in the formerly-panicking split regression zone. A multi-step rep
/// passes through EVERY intermediate width, so the zone predicate is
/// per-INJECTION, not max-based: e.g. an n = 32 λ-chain's first steps are
/// wide (> 256, the always-safe `split_short` branch) but its
/// 14-to-27-links-remaining steps land inside [129, 256] — safe only on the
/// FIXED interpreter (see [`INTERPRETER_SPLIT_REGRESSION_MIN`]); the probe
/// records them as provenance.
pub struct CellWidthProbe {
    /// The maximum [`max_eval_width`] across the cell's injections (recorded
    /// in the driver's run header as a size metric).
    pub max_eval_width: usize,
    /// The FIRST per-injection width inside the formerly-panicking split
    /// regression zone, if any — PROVENANCE, not a gate: `Some` means this
    /// cell's results exercise (and depend on) the fixed interpreter's
    /// [129, 256] `split_short` routing.
    pub regression_zone_width: Option<usize>,
}

/// Probe one cell's injection widths — see [`CellWidthProbe`]. The driver
/// records the probe in its run header (`max_eval_width` +
/// `in_split_regression_zone`); the driver-bin unit tests pin which cells
/// exercise the regression zone. Nothing gates on it anymore (the interpreter
/// is fixed — [`INTERPRETER_SPLIT_REGRESSION_MIN`]).
pub fn cell_width_probe(
    compiled: &CompiledWorkload,
    matcher: MatcherKind,
    encoding: GuardEncodingKind,
) -> Result<CellWidthProbe, WorkloadFailure> {
    let ruleset = compiled.ruleset();
    let echo_channels = workload_echo_channels(compiled);
    let mut probe = CellWidthProbe {
        max_eval_width: 0,
        regression_zone_width: None,
    };
    let mut record = |width: usize| {
        probe.max_eval_width = probe.max_eval_width.max(width);
        if probe.regression_zone_width.is_none() && width_in_split_regression_zone(width) {
            probe.regression_zone_width = Some(width);
        }
    };
    match compiled.kind {
        // The R3 self-driving column is ONE injection of the FULL chain (no
        // per-step programs exist), so it probes like a single-injection cell.
        WorkloadKind::LambdaChain if matcher != MatcherKind::NaiveR3 => {
            let steps = usize::try_from(compiled.n).expect("n fits usize");
            for remaining in (1..=steps).rev() {
                let subject = lambda_chain_subject(remaining);
                let program = composed_program_for(
                    compiled.kind,
                    matcher,
                    encoding,
                    ruleset,
                    compiled.installed_program(),
                    &echo_channels,
                    &subject,
                    compiled.n,
                )?;
                record(max_eval_width(&program));
            }
        },
        _ => {
            let program = composed_program_for(
                compiled.kind,
                matcher,
                encoding,
                ruleset,
                compiled.installed_program(),
                &echo_channels,
                &compiled.subject,
                compiled.n,
            )?;
            record(max_eval_width(&program));
        },
    }
    Ok(probe)
}

/// Whether `width` (a [`cell_max_eval_width`] result) falls in the
/// formerly-panicking f1r3node split regression zone — the PROVENANCE
/// predicate the probe and the driver-bin regression pins share (nothing
/// fails closed on it anymore; see [`INTERPRETER_SPLIT_REGRESSION_MIN`]).
pub fn width_in_split_regression_zone(width: usize) -> bool {
    (INTERPRETER_SPLIT_REGRESSION_MIN..=INTERPRETER_SPLIT_REGRESSION_MAX).contains(&width)
}

/// Drive ONE injection on a FRESH counting runtime and return its
/// [`BenchRunResult`] plus the emission/bringup spans. `program` composition
/// happens inside the measured `emission` span; runtime construction is the
/// separate `bringup` span; `bench_inj_and_read` provides `build`/`inj`/
/// `readback`. The [`guard_composed_program`] fail-closed guard
/// ([`MAX_PROGRAM_ENCODED_LEN`]) runs BEFORE any injection.
async fn drive_single_injection(
    kind: WorkloadKind,
    matcher: MatcherKind,
    encoding: GuardEncodingKind,
    ruleset: &InRhoMatchingRuleset,
    installed_program: Option<&Par>,
    echo_channels: &[String],
    subject: &GroundTerm,
    params: BenchWorkloadParams,
) -> Result<(BenchRunResult, Duration, Duration), WorkloadFailure> {
    // ── bringup (unmeasured in warm groups) ─────────────────────────────────
    let bringup_started = Instant::now();
    let (mut runtime, comm_counters, match_counters) =
        bench_runtime_with_counters(Vec::new(), OUT_CHANNEL)
            .await
            .map_err(|e| WorkloadFailure::new(format!("counting runtime bring-up: {e}")))?;
    let bringup = bringup_started.elapsed();

    // ── emission (measured) ─────────────────────────────────────────────────
    let emission_started = Instant::now();
    let program = composed_program_for(
        kind,
        matcher,
        encoding,
        ruleset,
        installed_program,
        echo_channels,
        subject,
        params.n,
    )?;
    let emission = emission_started.elapsed();

    // ── fail-closed guards, BEFORE any injection (outside the spans) ────────
    guard_composed_program(&program)?;

    // ── the instrumented injection (build/inj/readback measured inside) ─────
    let result = bench_inj_and_read(
        &mut runtime,
        &program,
        OUT_CHANNEL,
        params,
        &comm_counters,
        &match_counters,
    )
    .await
    .map_err(|e| WorkloadFailure::new(format!("inj: {e}")))?;
    Ok((result, emission, bringup))
}

/// Run ONE rep of a compiled workload cell on the given matcher column and
/// return the instrumented outcome. Every failure (emitter fail-closed, guard
/// breach, runtime error, observed-vs-expected mismatch) surfaces as a
/// [`WorkloadFailure`] the driver records as a DNF line. See the module
/// rustdoc for what a rep is per workload; the observed multiset is VERIFIED
/// against the compiled ground truth on every rep (per step for
/// `lambda_chain`, sorted-multiset for the rest).
pub async fn run_compiled_workload(
    compiled: &CompiledWorkload,
    matcher: MatcherKind,
    encoding: GuardEncodingKind,
    rep: u64,
) -> Result<WorkloadRepOutcome, WorkloadFailure> {
    if !matcher_admitted(compiled.kind, matcher) {
        return Err(WorkloadFailure::new(format!(
            "matcher `{}` is not a column of workload `{}`",
            matcher.name(),
            compiled.kind.name(),
        )));
    }
    if matcher == MatcherKind::Naive
        && encoding == GuardEncodingKind::ConsumeTest
        && !consume_test_admitted(compiled.kind, compiled.n)
    {
        return Err(WorkloadFailure::new(format!(
            "consume-test is single-candidate only: not admitted for workload `{}` n={}",
            compiled.kind.name(),
            compiled.n,
        )));
    }
    // R3 is PatternGuard-ONLY (the emitter has no ConsumeTest form): a
    // consume-test request on the R3 column is a typed rejection, never a
    // silent encoding downgrade.
    if matcher == MatcherKind::NaiveR3 && encoding == GuardEncodingKind::ConsumeTest {
        return Err(WorkloadFailure::new(
            "the R3 self-driving column is PatternGuard-only: consume-test is not admitted"
                .to_string(),
        ));
    }
    // Registry consistency: the compiled expected values ARE the ground truth
    // firing count (each firing lands exactly one observed value).
    let expected_firings = usize::try_from(compiled.kind.expected_firings(compiled.n))
        .expect("expected firing count fits usize");
    if compiled.expected.len() != expected_firings {
        return Err(WorkloadFailure::new(format!(
            "registry drift: {} expected values vs expected_firings {expected_firings}",
            compiled.expected.len(),
        )));
    }

    let params = bench_params(compiled.kind, matcher, encoding, compiled.n, rep);
    let ruleset = compiled.ruleset();

    match compiled.kind {
        // R3 (EXPLORATORY, pre-registered): ONE session — one counting
        // runtime, one injection of installed-program ∥ R3 call; the chain
        // self-normalizes in-runtime. Verification: the observed OUT multiset
        // is the TERMINAL atom exactly once (`compiled.expected.last()` — the
        // per-step ladder's final reduct, so R3's observed value equals the
        // per-step column's terminal NF by construction), and the per-session
        // FIRING count is pinned through the `firing_visible` COMM counter
        // (= expected_firings: one accept COMM per β step — the counter-based
        // firing ground truth the pre-registration names).
        WorkloadKind::LambdaChain if matcher == MatcherKind::NaiveR3 => {
            let (result, emission, bringup) = drive_single_injection(
                compiled.kind,
                matcher,
                encoding,
                ruleset,
                compiled.installed_program(),
                &[],
                &compiled.subject,
                params,
            )
            .await?;

            let observed_values =
                decode_observed(&result.observed).map_err(WorkloadFailure::new)?;
            let terminal = compiled
                .expected
                .last()
                .expect("expected_firings >= 1 was checked above")
                .clone();
            if observed_values != vec![terminal.clone()] {
                return Err(WorkloadFailure::new(format!(
                    "R3 observed-mismatch: {observed_values:?} vs the terminal NF {terminal:?} \
                     exactly once",
                )));
            }
            let expected = u64::try_from(expected_firings).expect("firing count fits u64");
            if result.comm.firing_visible != expected {
                return Err(WorkloadFailure::new(format!(
                    "R3 firing-count-mismatch: firing_visible = {} but the ground truth is {} \
                     (one accept COMM per β step)",
                    result.comm.firing_visible, expected,
                )));
            }
            Ok(WorkloadRepOutcome { result, emission, bringup })
        },
        WorkloadKind::LambdaChain => {
            // Per-step root drive (B2 discipline): each step on a FRESH
            // counting runtime, the next subject rebuilt from the OBSERVED
            // reduct, per-step results SUMMED into one rep record.
            let steps = expected_firings;
            let mut subject = compiled.subject.clone();
            let mut emission_total = Duration::ZERO;
            let mut bringup_total = Duration::ZERO;
            let mut build_total = Duration::ZERO;
            let mut inj_total = Duration::ZERO;
            let mut readback_total = Duration::ZERO;
            let mut encoded_len_total = 0usize;
            let mut receiver_count_total = 0usize;
            let mut consumed_total: i64 = 0;
            let mut observed_total: Vec<Par> = Vec::with_capacity(steps);
            let mut comm_total = zero_comm_snapshot();
            let mut matches_total = MatchAttemptSnapshot { attempts: 0, successes: 0 };

            for step in 0..steps {
                let (step_result, emission, bringup) = drive_single_injection(
                    compiled.kind,
                    matcher,
                    encoding,
                    ruleset,
                    compiled.installed_program(),
                    &[],
                    &subject,
                    params.clone(),
                )
                .await
                .map_err(|failure| {
                    WorkloadFailure::new(format!("step {step}: {}", failure.reason))
                })?;

                // Verify: exactly one reduct, equal to the ground-truth
                // remaining chain, then feed the NEXT step from what the
                // reducer actually landed.
                let step_values = decode_observed(&step_result.observed)
                    .map_err(|e| WorkloadFailure::new(format!("step {step}: {e}")))?;
                let [reduct] = step_values.as_slice() else {
                    return Err(WorkloadFailure::new(format!(
                        "step {step}: the root drive fires exactly once, observed {} values",
                        step_values.len(),
                    )));
                };
                if *reduct != compiled.expected[step] {
                    return Err(WorkloadFailure::new(format!(
                        "step {step}: observed-mismatch — reduct {reduct:?} vs expected {:?}",
                        compiled.expected[step],
                    )));
                }
                subject = observation_to_ground(reduct)
                    .map_err(|e| WorkloadFailure::new(format!("step {step}: {e}")))?;

                emission_total += emission;
                bringup_total += bringup;
                build_total += step_result.build;
                inj_total += step_result.inj;
                readback_total += step_result.readback;
                encoded_len_total += step_result.program_encoded_len;
                receiver_count_total += step_result.program_receiver_count;
                consumed_total += step_result.consumed_cost_units;
                accumulate_comm(&mut comm_total, &step_result.comm);
                matches_total.attempts += step_result.matches.attempts;
                matches_total.successes += step_result.matches.successes;
                observed_total.extend(step_result.observed);
            }

            Ok(WorkloadRepOutcome {
                result: BenchRunResult {
                    workload: params,
                    build: build_total,
                    inj: inj_total,
                    readback: readback_total,
                    program_encoded_len: encoded_len_total,
                    program_receiver_count: receiver_count_total,
                    observed: observed_total,
                    consumed_cost_units: consumed_total,
                    comm: comm_total,
                    matches: matches_total,
                },
                emission: emission_total,
                bringup: bringup_total,
            })
        },
        WorkloadKind::SwapComb
        | WorkloadKind::SwapSmall
        | WorkloadKind::WrapSwapCtx
        | WorkloadKind::NestedSpine
        | WorkloadKind::MultiRuleShared => {
            // Direct construction: one one-shot σ-echo per expected firing
            // ([`workload_echo_channels`] — identical across the cell's
            // matcher columns, so the installed observer program never
            // differs between them).
            let echo_channels = workload_echo_channels(compiled);
            let (result, emission, bringup) = drive_single_injection(
                compiled.kind,
                matcher,
                encoding,
                ruleset,
                compiled.installed_program(),
                &echo_channels,
                &compiled.subject,
                params,
            )
            .await?;

            let observed_values =
                decode_observed(&result.observed).map_err(WorkloadFailure::new)?;
            let observed_sorted = sorted_multiset(observed_values);
            let expected_sorted = sorted_multiset(compiled.expected.clone());
            if observed_sorted != expected_sorted {
                return Err(WorkloadFailure::new(format!(
                    "observed-mismatch: {observed_sorted:?} vs expected {expected_sorted:?}",
                )));
            }
            Ok(WorkloadRepOutcome { result, emission, bringup })
        },
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// E-6a (pgmcp experiment 145): the TREATMENT-arm workload drive — the
// PathMap-index counterpart of [`run_compiled_workload`], shared by the
// equivalence gate (`tests/rho_net_e6a_equivalence.rs`) and the E-6a driver
// bin (`src/bin/bench_e6a_pathmap_driver.rs`).
// ─────────────────────────────────────────────────────────────────────────────

/// One E-6a treatment rep's outcome: the (possibly step-aggregated)
/// [`BenchRunResult`] plus the treatment-specific accounting.
pub struct E6aWorkloadOutcome {
    /// The instrumented run record (step-aggregated for `lambda_chain`).
    pub result: BenchRunResult,
    /// The MACHINE-enumerated candidate sites per rule-root op (for
    /// `lambda_chain`, the FIRST step's enumeration — later steps re-enumerate
    /// on their own fresh runtimes).
    pub machine_sites: std::collections::BTreeMap<String, Vec<String>>,
    /// The treatment's static spread-send count (Σ over injections of
    /// `1 index publish + #ops discovery-result sends`).
    pub treatment_spread_sends: usize,
    /// Total per-call emission span (index build + discovery + query codegen).
    pub emission: Duration,
    /// Total counting-runtime construction span.
    pub bringup: Duration,
    /// Total phase-1 injection span (index publication plus discovery).
    pub phase1_inj: Duration,
    /// Total phase-2 injection span (guard and sigma-value queries).
    pub phase2_inj: Duration,
    /// Total encoded phase-1 program size.
    pub phase1_encoded_len: usize,
    /// Total encoded phase-2 program size.
    pub phase2_encoded_len: usize,
}

/// The CONTROL matcher column of each E-6a corpus cell — the CURRENT
/// spread+drive path: the `sa` column where the automaton drives (swap_comb
/// locate-all, multi_rule_shared per-rule, lambda_chain per-step root), and
/// the `naive` comprehension for `nested_spine` (whose sa locate-all fails
/// closed — `NestedEntryMultiSite` — leaving naive as the current IN-RHO
/// column; `replay` is host-side matching and has no spread at all).
pub fn e6a_control_matcher(kind: WorkloadKind) -> Option<MatcherKind> {
    match kind {
        WorkloadKind::LambdaChain
        | WorkloadKind::SwapComb
        | WorkloadKind::SwapSmall
        | WorkloadKind::MultiRuleShared => Some(MatcherKind::Sa),
        WorkloadKind::NestedSpine => Some(MatcherKind::Naive),
        // Contextual JOIN reassembly is out of E-6a scope (the treatment fires
        // entry redexes, not congruence-context reassembly).
        WorkloadKind::WrapSwapCtx => None,
    }
}

/// The control arm's STATIC spread-send count for one cell: the sends of the
/// per-node [`spread_term_par`] the control call embeds (summed over the
/// per-step subjects for `lambda_chain` — the ground-truth step ladder, which
/// the per-step drive verifies the observed reducts against).
pub fn e6a_control_spread_sends(compiled: &CompiledWorkload) -> usize {
    let fingerprint = &compiled.ruleset().language_fingerprint;
    match compiled.kind {
        WorkloadKind::LambdaChain => {
            let steps = usize::try_from(compiled.n).expect("n fits usize");
            (1..=steps)
                .map(|remaining| {
                    mettail_rholang_runtime::count_send_nodes(&spread_term_par(
                        &lambda_chain_subject(remaining),
                        fingerprint,
                        ROOT_SITE,
                    ))
                })
                .sum()
        },
        _ => mettail_rholang_runtime::count_send_nodes(&spread_term_par(
            &compiled.subject,
            fingerprint,
            ROOT_SITE,
        )),
    }
}

/// Run ONE E-6a TREATMENT rep of a compiled workload cell: the two-phase
/// PathMap-index drive ([`drive_e6a_treatment`]) with the SAME installed
/// σ-receiver program / σ-echo observers and the SAME observed-vs-expected
/// verification as the control's [`run_compiled_workload`]. `lambda_chain`
/// runs per-step on fresh runtimes with the ROOT-site β-strategy filter
/// (mirroring the control column's root-restricted per-step discipline),
/// feeding each next step from the OBSERVED reduct.
pub async fn run_e6a_treatment_workload(
    compiled: &CompiledWorkload,
    rep: u64,
) -> Result<E6aWorkloadOutcome, WorkloadFailure> {
    use mettail_rholang_runtime::drive_e6a_treatment;

    if e6a_control_matcher(compiled.kind).is_none() {
        return Err(WorkloadFailure::new(format!(
            "workload `{}` is out of E-6a scope (no treatment drive)",
            compiled.kind.name(),
        )));
    }
    let expected_firings = usize::try_from(compiled.kind.expected_firings(compiled.n))
        .expect("expected firing count fits usize");
    if compiled.expected.len() != expected_firings {
        return Err(WorkloadFailure::new(format!(
            "registry drift: {} expected values vs expected_firings {expected_firings}",
            compiled.expected.len(),
        )));
    }
    let params = BenchWorkloadParams {
        name: compiled.kind.name().to_string(),
        matcher: "e6a-pathmap".to_string(),
        encoding: "-".to_string(),
        n: compiled.n,
        rep,
    };
    let ruleset = compiled.ruleset();
    let echo = |channel: &str| sigma_echo_receiver(channel, 1);

    match compiled.kind {
        WorkloadKind::LambdaChain => {
            // Per-step ROOT drive (the control column's discipline): each step
            // on a FRESH counting runtime, the treatment restricted to the
            // machine-enumerated ROOT site, the next subject rebuilt from the
            // OBSERVED reduct, per-step records SUMMED into one rep record.
            let steps = expected_firings;
            let mut subject = compiled.subject.clone();
            let root_filter: std::collections::BTreeSet<String> =
                std::iter::once(ROOT_SITE.to_string()).collect();
            let mut machine_sites_first: Option<std::collections::BTreeMap<String, Vec<String>>> =
                None;
            let mut spread_sends_total = 0usize;
            let mut emission_total = Duration::ZERO;
            let mut bringup_total = Duration::ZERO;
            let mut build_total = Duration::ZERO;
            let mut inj_total = Duration::ZERO;
            let mut phase1_inj_total = Duration::ZERO;
            let mut phase2_inj_total = Duration::ZERO;
            let mut readback_total = Duration::ZERO;
            let mut encoded_len_total = 0usize;
            let mut phase1_encoded_len_total = 0usize;
            let mut phase2_encoded_len_total = 0usize;
            let mut receiver_count_total = 0usize;
            let mut consumed_total: i64 = 0;
            let mut observed_total: Vec<Par> = Vec::with_capacity(steps);
            let mut comm_total = zero_comm_snapshot();
            let mut matches_total = MatchAttemptSnapshot { attempts: 0, successes: 0 };

            for step in 0..steps {
                let outcome = drive_e6a_treatment(
                    ruleset,
                    compiled.installed_program(),
                    &[],
                    &subject,
                    ROOT_SITE,
                    OUT_CHANNEL,
                    params.clone(),
                    echo,
                    Some(&root_filter),
                )
                .await
                .map_err(|failure| {
                    WorkloadFailure::new(format!("step {step}: {}", failure.reason))
                })?;

                let step_values = decode_observed(&outcome.result.observed)
                    .map_err(|e| WorkloadFailure::new(format!("step {step}: {e}")))?;
                let [reduct] = step_values.as_slice() else {
                    return Err(WorkloadFailure::new(format!(
                        "step {step}: the root-restricted treatment fires exactly once, \
                         observed {} values",
                        step_values.len(),
                    )));
                };
                if *reduct != compiled.expected[step] {
                    return Err(WorkloadFailure::new(format!(
                        "step {step}: observed-mismatch — reduct {reduct:?} vs expected {:?}",
                        compiled.expected[step],
                    )));
                }
                subject = observation_to_ground(reduct)
                    .map_err(|e| WorkloadFailure::new(format!("step {step}: {e}")))?;

                if machine_sites_first.is_none() {
                    machine_sites_first = Some(outcome.machine_sites.clone());
                }
                spread_sends_total += outcome.treatment_spread_sends;
                emission_total += outcome.emission;
                bringup_total += outcome.bringup;
                build_total += outcome.result.build;
                inj_total += outcome.result.inj;
                phase1_inj_total += outcome.phase1_inj;
                phase2_inj_total += outcome.phase2_inj;
                readback_total += outcome.result.readback;
                encoded_len_total += outcome.result.program_encoded_len;
                phase1_encoded_len_total += outcome.phase1_encoded_len;
                phase2_encoded_len_total += outcome.phase2_encoded_len;
                receiver_count_total += outcome.result.program_receiver_count;
                consumed_total += outcome.result.consumed_cost_units;
                accumulate_comm(&mut comm_total, &outcome.result.comm);
                matches_total.attempts += outcome.result.matches.attempts;
                matches_total.successes += outcome.result.matches.successes;
                observed_total.extend(outcome.result.observed);
            }

            Ok(E6aWorkloadOutcome {
                result: BenchRunResult {
                    workload: params,
                    build: build_total,
                    inj: inj_total,
                    readback: readback_total,
                    program_encoded_len: encoded_len_total,
                    program_receiver_count: receiver_count_total,
                    observed: observed_total,
                    consumed_cost_units: consumed_total,
                    comm: comm_total,
                    matches: matches_total,
                },
                machine_sites: machine_sites_first.expect("steps >= 1"),
                treatment_spread_sends: spread_sends_total,
                emission: emission_total,
                bringup: bringup_total,
                phase1_inj: phase1_inj_total,
                phase2_inj: phase2_inj_total,
                phase1_encoded_len: phase1_encoded_len_total,
                phase2_encoded_len: phase2_encoded_len_total,
            })
        },
        _ => {
            let echo_channels = workload_echo_channels(compiled);
            let outcome = drive_e6a_treatment(
                ruleset,
                compiled.installed_program(),
                &echo_channels,
                &compiled.subject,
                ROOT_SITE,
                OUT_CHANNEL,
                params,
                echo,
                None,
            )
            .await
            .map_err(|failure| WorkloadFailure::new(failure.reason))?;

            let observed_values =
                decode_observed(&outcome.result.observed).map_err(WorkloadFailure::new)?;
            let observed_sorted = sorted_multiset(observed_values);
            let expected_sorted = sorted_multiset(compiled.expected.clone());
            if observed_sorted != expected_sorted {
                return Err(WorkloadFailure::new(format!(
                    "e6a observed-mismatch: {observed_sorted:?} vs expected {expected_sorted:?}",
                )));
            }
            Ok(E6aWorkloadOutcome {
                result: outcome.result,
                machine_sites: outcome.machine_sites,
                treatment_spread_sends: outcome.treatment_spread_sends,
                emission: outcome.emission,
                bringup: outcome.bringup,
                phase1_inj: outcome.phase1_inj,
                phase2_inj: outcome.phase2_inj,
                phase1_encoded_len: outcome.phase1_encoded_len,
                phase2_encoded_len: outcome.phase2_encoded_len,
            })
        },
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Generator unit tests: `src/bin/bench_sa_vs_naive_driver.rs`, module
// `workloads_tests` (subject sizes, expected firing counts, admission pins).
// They live in the DRIVER BIN — which has a libtest harness — because this
// file is also compiled into the `harness = false` criterion bench, where a
// `#[cfg(test)]` module would have no harness to anchor it (dead code).
// ─────────────────────────────────────────────────────────────────────────────
