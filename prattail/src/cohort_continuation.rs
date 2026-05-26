//! Phase F.13 chain_10000 Exp 9 / Approach P Substage 1.a (2026-05-26):
//! realize-time cohort fanout via continuations.
//!
//! # Mandate
//!
//! Exp 11 S0 measured `cohort_cursors_emitted = 335,808` on
//! `test_right_assoc_chain_1000` against `branch_cursors_sum = 193,102`
//! — a 174 % cohort-revive share. Projected ~3.4 M revived cursors at
//! chain_10000, the largest single factor in cursor population. Per
//! Plan agent (`/home/dylon/.claude/plans/...` for Exp 9): defer cohort
//! revives into `CohortContinuation` records that are interned as
//! Packings at EOI rather than materialized as concrete cursors during
//! parse-time stepping.
//!
//! # Design
//!
//! A `CohortContinuation<W>` captures the *outer-rule wrapping intent*
//! at the moment a cohort member pauses: which outer rule the member
//! belongs to, the pre-dispatched children of that outer rule, which
//! child slot the worker's resolved Symbol substitutes into, and the
//! per-packing weight contribution. At end-of-input,
//! `install_cohort_continuations` (Substage 1.c) enumerates the
//! continuations into outer-rule packings via `sppf.intern_packing` +
//! `sppf.link_packing_to_symbol`.
//!
//! # Why this works
//!
//! - `intern_packing` is dedup'd — cycle-defense is automatic by
//!   construction, no `visited_dispatch` state needed on continuations.
//! - Per-cohort placement (Vec on `DispatchCacheEntry::Resolved`)
//!   matches the natural index: when worker resolves at key K, the
//!   continuations attached to K all wrap against the same `symbol_id`.
//! - ~32 B per continuation (this struct) vs ~64 B per
//!   `CohortMemberState` vs ~3.2 KB per materialized `BranchCursor`.
//!
//! # Eligibility (Substage 1.b)
//!
//! Not every cohort site is P-eligible. The continuation only
//! correctly substitutes when the worker's `CrossCatDelegate` dispatch
//! is positioned at the *last child slot* of the outer rule (so the
//! other_children Vec captures the prefix and substitution_slot is
//! `arity - 1`). For mixfix with post-dispatch children, fall back to
//! today's per-cursor revive path.
//!
//! Chain workloads are universally eligible (InfixOp `lhs op rhs`
//! dispatches the RHS as the last child).

use crate::automata::semiring::SemiringRef;
use crate::sppf::SppfId;

/// Captures the outer-rule wrapping intent for a paused cohort member.
///
/// At EOI, `install_cohort_continuations` (Substage 1.c) substitutes
/// the worker's resolved `symbol_id` into `other_children` at
/// `substitution_slot` and interns the resulting outer packing.
#[derive(Clone)]
pub struct CohortContinuation<W: SemiringRef> {
    /// Rule index within `outer_cat_src_idx`'s category. Used by
    /// `intern_packing` to identify which outer rule's packing to
    /// produce.
    pub outer_rule_idx: u16,
    /// Category source index of the outer rule. The pair
    /// `(outer_cat_src_idx, outer_rule_idx)` uniquely identifies the
    /// outer rule's action definition.
    pub outer_cat_src_idx: u16,
    /// Input position at the moment of pause. Becomes the `lo_pos`
    /// component of the outer Symbol interned at EOI.
    pub outer_lo_pos: u32,
    /// Pre-dispatched children of the outer rule, captured from the
    /// pausing member's `sppf_stack` at pause time. For an InfixOp
    /// `lhs op rhs` whose dispatch is the RHS, this is `[lhs_id,
    /// op_id]` and `substitution_slot = 2` (the RHS).
    pub other_children: Vec<SppfId>,
    /// Which child slot the worker's resolved `symbol_id` substitutes
    /// into. For chain workloads this is always `arity - 1`.
    pub substitution_slot: u8,
    /// Per-packing weight contribution = `weight_at_dispatch` at the
    /// moment of pause. Matches today's
    /// `member.weight_at_dispatch × snap.worker_pending_packing_weight`
    /// for revived cursors. EOI install combines with `intern_packing`'s
    /// weight aggregation (Schwartz-Zippel ⊕ summing).
    pub weight_at_dispatch: W,
}

impl<W: SemiringRef> std::fmt::Debug for CohortContinuation<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CohortContinuation")
            .field("outer_rule_idx", &self.outer_rule_idx)
            .field("outer_cat_src_idx", &self.outer_cat_src_idx)
            .field("outer_lo_pos", &self.outer_lo_pos)
            .field("other_children_len", &self.other_children.len())
            .field("substitution_slot", &self.substitution_slot)
            .finish()
    }
}

/// Hard cap per Plan agent: bound continuation buffer growth in
/// pathological grammars (>64 eligible cohort members at one key fall
/// back to per-cursor revive for the overflow). Strictly safe degrade.
/// Cap raised to 256 in Substage 1.e once S1.d ships lazy.
pub const MAX_DEFERRED_PER_KEY: usize = 64;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;

    fn dummy_weight() -> LexicographicWeight {
        use crate::automata::semiring::{Semiring, TropicalWeight};
        LexicographicWeight::new(TropicalWeight::one(), 0, 0)
    }

    #[test]
    fn continuation_constructs() {
        let c: CohortContinuation<LexicographicWeight> = CohortContinuation {
            outer_rule_idx: 7,
            outer_cat_src_idx: 3,
            outer_lo_pos: 42,
            other_children: vec![100u32, 101u32],
            substitution_slot: 2,
            weight_at_dispatch: dummy_weight(),
        };
        assert_eq!(c.outer_rule_idx, 7);
        assert_eq!(c.outer_cat_src_idx, 3);
        assert_eq!(c.outer_lo_pos, 42);
        assert_eq!(c.other_children.len(), 2);
        assert_eq!(c.substitution_slot, 2);
    }

    #[test]
    fn continuation_clone_preserves_fields() {
        let c: CohortContinuation<LexicographicWeight> = CohortContinuation {
            outer_rule_idx: 1,
            outer_cat_src_idx: 2,
            outer_lo_pos: 3,
            other_children: vec![4u32],
            substitution_slot: 1,
            weight_at_dispatch: dummy_weight(),
        };
        let c2 = c.clone();
        assert_eq!(c2.outer_rule_idx, c.outer_rule_idx);
        assert_eq!(c2.outer_cat_src_idx, c.outer_cat_src_idx);
        assert_eq!(c2.outer_lo_pos, c.outer_lo_pos);
        assert_eq!(c2.other_children, c.other_children);
        assert_eq!(c2.substitution_slot, c.substitution_slot);
    }

    #[test]
    fn debug_redacts_weight_for_readability() {
        let c: CohortContinuation<LexicographicWeight> = CohortContinuation {
            outer_rule_idx: 1,
            outer_cat_src_idx: 2,
            outer_lo_pos: 3,
            other_children: vec![4u32, 5u32, 6u32],
            substitution_slot: 0,
            weight_at_dispatch: dummy_weight(),
        };
        let s = format!("{:?}", c);
        // Debug shows the discriminating bookkeeping (rule idx, cat,
        // position, children-len, slot) but not the weight (which is
        // workload-dependent and noisy).
        assert!(s.contains("outer_rule_idx: 1"));
        assert!(s.contains("other_children_len: 3"));
        assert!(s.contains("substitution_slot: 0"));
        assert!(!s.contains("weight_at_dispatch"));
    }

    #[test]
    fn max_deferred_per_key_is_64() {
        assert_eq!(MAX_DEFERRED_PER_KEY, 64);
    }
}
