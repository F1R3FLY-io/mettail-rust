//! Phase F.13 (2026-05-20): walker statistics counters for algorithmic-
//! bottleneck attribution.
//!
//! Empirical context: AMD uProf call-graph analysis of
//! `test_right_assoc_chain_100` at tip `9108cfb` showed
//! `apply_action_to_cursor` consumed 71.7% of parse time across an
//! estimated ~10,000 invocations. The bottleneck is invocation COUNT,
//! not per-call cost. Chain scaling exponent ~2.62 — super-quadratic.
//!
//! These counters establish the exact numbers behind the estimate:
//! - How many `apply_action_to_cursor` calls actually fire per parse?
//! - How many cursors proliferate at peak?
//! - How effective is `merge_equivalent_cursors` (collapse ratio)?
//! - Where do cursors come from (seed/fork) and where do they die
//!   (resolution check / explicit drop / outcome drop / merge)?
//! - Which Fork dispatch kinds dominate the Fork count?
//!
//! With these numbers we can design the next algorithmic hypothesis
//! from empirical data instead of inference.
//!
//! ## Zero-cost when disabled
//!
//! Both this module's struct field on `WpdaWalker` AND the increment
//! macros are gated by `#[cfg(feature = "walker-stats")]`. When the
//! feature is off, macros expand to empty blocks and the field doesn't
//! exist. Verified with `cargo expand --release -p mettail-prattail`.
//!
//! ## Per-walker scoping
//!
//! Counters live on the `WpdaWalker` struct (not in a global / thread-
//! local). This eliminates parallel-test interference automatically:
//! each parse session owns its counters. No atomics, no mutexes — the
//! walker is single-threaded per session and `apply_action_to_cursor`
//! always borrows `&mut self`.
//!
//! ## Output
//!
//! Set environment variable `PRATTAIL_WALKER_STATS=1` before running.
//! At each `resolve_at_end_of_input` the walker prints a human-readable
//! summary to stderr via `Display` impl. Pattern matches the
//! `PRATTAIL_HANG_DUMP` env-var precedent in `hang_dump.rs`.

use std::fmt;

/// Walker statistics — 19 u64 counters tracking invocation count,
/// cursor proliferation, merge effectiveness, lifecycle, and Fork
/// composition.
///
/// All counters monotonically increment except `branch_cursors_peak_*`
/// which use max-update. `Default` produces all zeros.
#[derive(Default, Debug, Clone)]
pub struct WalkerStats {
    // ── Invocation / cost ─────────────────────────────────────────────
    /// Per-cursor `apply_action_to_cursor` calls. Confirms the ~10,000
    /// estimate for chain_100 and gives the exact scaling slope for
    /// chain_50/100/200.
    pub apply_action_calls: u64,
    /// `step_fanout` outer-loop iterations (one per parse step).
    /// Ratio `apply_action_calls / step_fanout_calls` = average
    /// cursors-per-step.
    pub step_fanout_calls: u64,
    /// Peak `branch_cursors.len()` BEFORE `merge_equivalent_cursors`
    /// runs. Captures the pre-merge cursor frontier size.
    pub branch_cursors_peak_pre_merge: u64,
    /// Peak `branch_cursors.len()` AFTER `merge_equivalent_cursors`
    /// runs. Difference vs pre-merge = number of cursors collapsed at
    /// peak.
    pub branch_cursors_peak_post_merge: u64,
    /// Running sum of `branch_cursors.len()` at each step entry.
    /// Average = `branch_cursors_sum / step_fanout_calls`.
    pub branch_cursors_sum: u64,

    // ── Merge effectiveness ───────────────────────────────────────────
    /// Total cursors considered for merge (running sum of input cursor
    /// count to each `merge_equivalent_cursors` invocation).
    pub merge_attempts_total: u64,
    /// Total cursors COLLAPSED by merge (one increment per Entry::Occupied
    /// hit). Ratio `merge_collapses_total / merge_attempts_total` =
    /// collapse rate. Low = ConfigKey too narrow.
    pub merge_collapses_total: u64,

    // ── Cursor lifecycle: sources ─────────────────────────────────────
    /// Cursors created by walker constructors + reset (always 1 per parse).
    pub cursors_created_via_seed: u64,
    /// Cursors created as Fork-arm children. Dominant source under
    /// chain-parsing.
    pub cursors_created_via_fork: u64,

    // ── Cursor lifecycle: sinks ───────────────────────────────────────
    /// Cursors dropped in `cursor_resolution_check` when transitioning
    /// to `WpdaState::Error`. NOT WIRED in first iteration —
    /// cursor_resolution_check has `&self` signature, would require
    /// breaking change to count here. The Drop is still captured in
    /// `cursors_dropped_via_outcome_drop` below (which counts ALL Drops
    /// reaching step_fanout's outcome handler).
    pub cursors_dropped_via_resolution_check: u64,
    /// Cursors dropped via `return CursorOutcome::Drop` inside
    /// `apply_action_to_cursor` (B12 / B14 / recovery cycle defenses).
    /// NOT WIRED in first iteration — 5 sites would require individual
    /// increments. Still captured in `cursors_dropped_via_outcome_drop`.
    pub cursors_dropped_via_explicit_drop: u64,
    /// Cursors dropped via the `CursorOutcome::Drop` arm at
    /// `step_fanout` (catches ALL Drops — from resolution_check + from
    /// explicit return in apply_action_to_cursor). This is the
    /// authoritative cursor-death counter in the first iteration.
    pub cursors_dropped_via_outcome_drop: u64,
    /// Cursors absorbed by `merge_equivalent_cursors`. Same source as
    /// `merge_collapses_total`; tracked separately for lifecycle
    /// conservation check (sum of sinks ≈ sum of sources).
    pub cursors_dropped_via_merge: u64,

    // ── Fork composition ──────────────────────────────────────────────
    /// Total `WpdaStepAction::Fork` firings.
    pub fork_total: u64,
    /// Branches with `ForkActionKind::Push` (cross-cat-projection
    /// dispatch family).
    pub fork_kind_push: u64,
    /// Branches with `ForkActionKind::OptGroupAbsent` (Optional Group
    /// SKIP arm).
    pub fork_kind_opt_group_absent: u64,
    /// Branches with any `LexAlt*` family (LexAlt, LexAltPrefixOp,
    /// LexAltPostfixOp, LexAltInfixOp, LexAltMixfixOp).
    pub fork_kind_lex_alt_family: u64,
    /// Branches with any `Consume*` / `ConsumeAndReplace*` family
    /// (terminal-consuming).
    pub fork_kind_consume_family: u64,
    /// Branches with other ForkActionKind variants (Pop /
    /// ReplaceAndPush / GuardedConsume* / etc.).
    pub fork_kind_other: u64,
    /// Recovery-typed Fork dispatches (where `is_recovery == true`).
    /// Distinguishes recovery Forks from grammar Forks in the total.
    pub fork_recovery_dispatches: u64,
    /// Branches whose `new_state` is `WpdaState::CrossCatDelegate { .. }`.
    /// Confirms cross-cat projection as the dominant Fork-branch source.
    pub fork_cross_cat_projection_branches: u64,
}

impl WalkerStats {
    /// Effective number of average cursors per step.
    pub fn avg_cursors_per_step(&self) -> f64 {
        if self.step_fanout_calls == 0 {
            0.0
        } else {
            self.branch_cursors_sum as f64 / self.step_fanout_calls as f64
        }
    }

    /// Merge collapse ratio (0.0–1.0). 1.0 = every considered cursor
    /// gets merged (rare). 0.0 = merge collapses nothing (ConfigKey
    /// too narrow).
    pub fn merge_collapse_ratio(&self) -> f64 {
        if self.merge_attempts_total == 0 {
            0.0
        } else {
            self.merge_collapses_total as f64 / self.merge_attempts_total as f64
        }
    }
}

impl fmt::Display for WalkerStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "═══ PRATTAIL WALKER STATS ═══")?;
        writeln!(
            f,
            "  apply_action_calls={}  step_fanout_calls={}  avg_cursors_per_step={:.2}",
            self.apply_action_calls,
            self.step_fanout_calls,
            self.avg_cursors_per_step(),
        )?;
        writeln!(
            f,
            "  branch_cursors_peak_pre_merge={}  post_merge={}  sum={}",
            self.branch_cursors_peak_pre_merge,
            self.branch_cursors_peak_post_merge,
            self.branch_cursors_sum,
        )?;
        writeln!(
            f,
            "  merge_attempts={}  merge_collapses={}  collapse_ratio={:.3}",
            self.merge_attempts_total,
            self.merge_collapses_total,
            self.merge_collapse_ratio(),
        )?;
        writeln!(
            f,
            "  cursors_created: seed={} fork={} → total={}",
            self.cursors_created_via_seed,
            self.cursors_created_via_fork,
            self.cursors_created_via_seed + self.cursors_created_via_fork,
        )?;
        writeln!(
            f,
            "  cursors_dropped: resolution={} explicit={} outcome={} merge={}",
            self.cursors_dropped_via_resolution_check,
            self.cursors_dropped_via_explicit_drop,
            self.cursors_dropped_via_outcome_drop,
            self.cursors_dropped_via_merge,
        )?;
        writeln!(
            f,
            "  fork_total={}  recovery_dispatches={}  cross_cat_branches={}",
            self.fork_total,
            self.fork_recovery_dispatches,
            self.fork_cross_cat_projection_branches,
        )?;
        writeln!(
            f,
            "  fork_kinds: push={} opt_group_absent={} lex_alt={} consume={} other={}",
            self.fork_kind_push,
            self.fork_kind_opt_group_absent,
            self.fork_kind_lex_alt_family,
            self.fork_kind_consume_family,
            self.fork_kind_other,
        )?;
        Ok(())
    }
}

/// Increment a `u64` counter on `self.stats` (zero-cost when feature off).
///
/// Usage: `stats_inc!(self, apply_action_calls);`
#[macro_export]
macro_rules! stats_inc {
    ($walker:expr, $field:ident) => {
        #[cfg(feature = "walker-stats")]
        {
            $walker.stats.$field = $walker.stats.$field.saturating_add(1);
        }
    };
}

/// Add an arbitrary value to a `u64` counter on `self.stats` (zero-cost
/// when feature off).
///
/// Usage: `stats_add!(self, branch_cursors_sum, self.branch_cursors.len() as u64);`
#[macro_export]
macro_rules! stats_add {
    ($walker:expr, $field:ident, $value:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            let v: u64 = ($value) as u64;
            $walker.stats.$field = $walker.stats.$field.saturating_add(v);
        }
    };
}

/// Max-update a `u64` counter on `self.stats` (zero-cost when feature
/// off). Used for peak counters.
///
/// Usage: `stats_max!(self, branch_cursors_peak_pre_merge,
///                    self.branch_cursors.len() as u64);`
#[macro_export]
macro_rules! stats_max {
    ($walker:expr, $field:ident, $value:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            let v: u64 = ($value) as u64;
            if v > $walker.stats.$field {
                $walker.stats.$field = v;
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_all_zeros() {
        let s = WalkerStats::default();
        assert_eq!(s.apply_action_calls, 0);
        assert_eq!(s.step_fanout_calls, 0);
        assert_eq!(s.avg_cursors_per_step(), 0.0);
        assert_eq!(s.merge_collapse_ratio(), 0.0);
    }

    #[test]
    fn display_renders_without_panic() {
        let s = WalkerStats {
            apply_action_calls: 9_847,
            step_fanout_calls: 412,
            branch_cursors_peak_pre_merge: 47,
            branch_cursors_peak_post_merge: 23,
            branch_cursors_sum: 9_847,
            merge_attempts_total: 2_184,
            merge_collapses_total: 1_772,
            cursors_created_via_seed: 1,
            cursors_created_via_fork: 9_846,
            cursors_dropped_via_resolution_check: 12,
            cursors_dropped_via_explicit_drop: 4,
            cursors_dropped_via_outcome_drop: 58,
            cursors_dropped_via_merge: 1_772,
            fork_total: 1_968,
            fork_kind_push: 5_904,
            fork_kind_opt_group_absent: 0,
            fork_kind_lex_alt_family: 0,
            fork_kind_consume_family: 3_936,
            fork_kind_other: 12,
            fork_recovery_dispatches: 0,
            fork_cross_cat_projection_branches: 5_904,
        };
        let rendered = format!("{}", s);
        assert!(rendered.contains("apply_action_calls=9847"));
        assert!(rendered.contains("collapse_ratio=0.811"));
    }

    #[test]
    fn merge_collapse_ratio_zero_attempts() {
        let s = WalkerStats {
            merge_attempts_total: 0,
            merge_collapses_total: 0,
            ..Default::default()
        };
        assert_eq!(s.merge_collapse_ratio(), 0.0);
    }

    #[test]
    fn avg_cursors_zero_steps() {
        let s = WalkerStats::default();
        assert_eq!(s.avg_cursors_per_step(), 0.0);
    }
}
