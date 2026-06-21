use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// State equivalence signature (for B3 minimization)
// ══════════════════════════════════════════════════════════════════════════════

/// Signature capturing the observable behavior of a WFST state.
///
/// Two states with identical signatures are equivalent: they accept the same
/// inputs, produce the same outputs, and transition to the same targets with
/// the same weights. Used by `PredictionWfst::minimize()` to identify
/// mergeable states.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct StateSignature {
    is_final: bool,
    final_weight_bits: u64,
    /// Sorted transitions: (token_id, action_idx, target_state_id, weight_bits)
    transitions: Vec<(TokenId, u32, WfstStateId, u64)>,
}

impl StateSignature {
    pub(crate) fn from_state(state: &WfstState) -> Self {
        let mut transitions: Vec<(TokenId, u32, WfstStateId, u64)> = state
            .transitions
            .iter()
            .map(|t| (t.input, t.action_idx, t.to, t.weight.value().to_bits()))
            .collect();
        transitions.sort();

        StateSignature {
            is_final: state.is_final,
            final_weight_bits: state.final_weight.value().to_bits(),
            transitions,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sprint 8: Canonical WFST structure for alpha-equivalence / isomorphism detection
// ══════════════════════════════════════════════════════════════════════════════

/// The shape of a dispatch action, erasing category-specific names.
///
/// Two actions with the same shape but different names (e.g., `Direct { rule_label: "AddInt" }`
/// vs `Direct { rule_label: "AddFloat" }`) are considered alpha-equivalent. The shape
/// preserves structural properties that affect codegen (e.g., `needs_backtrack`, alternative
/// count) while erasing concrete identifiers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CanonicalActionShape {
    Direct,
    Lookahead {
        alternative_count: usize,
        has_fallback: bool,
    },
    CrossCategory {
        needs_backtrack: bool,
    },
    Cast,
    Grouping,
    Variable,
}

impl CanonicalActionShape {
    /// Extract the shape from a concrete `DispatchAction`.
    pub fn from_action(action: &crate::prediction::DispatchAction) -> Self {
        match action {
            crate::prediction::DispatchAction::Direct { .. } => CanonicalActionShape::Direct,
            crate::prediction::DispatchAction::Lookahead { alternatives, fallback } => {
                CanonicalActionShape::Lookahead {
                    alternative_count: alternatives.len(),
                    has_fallback: fallback.is_some(),
                }
            },
            crate::prediction::DispatchAction::CrossCategory { needs_backtrack, .. } => {
                CanonicalActionShape::CrossCategory { needs_backtrack: *needs_backtrack }
            },
            crate::prediction::DispatchAction::Cast { .. } => CanonicalActionShape::Cast,
            crate::prediction::DispatchAction::Grouping { .. } => CanonicalActionShape::Grouping,
            crate::prediction::DispatchAction::Variable { .. } => CanonicalActionShape::Variable,
        }
    }
}

/// A canonicalized state in a WFST, with De Bruijn action indices.
///
/// Action indices are replaced with encounter-order De Bruijn indices so that
/// two WFSTs with the same topology but different action tables produce identical
/// canonical states. This enables hash-based grouping of isomorphic WFSTs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CanonicalState {
    pub is_final: bool,
    pub final_weight_bits: u64,
    /// Sorted transitions: `(token_id, de_bruijn_action_index, target_state, weight_bits)`
    pub transitions: Vec<(TokenId, u32, WfstStateId, u64)>,
}

/// De Bruijn-canonicalized WFST structure for alpha-equivalence detection.
///
/// Two `PredictionWfst` instances are **alpha-equivalent** (isomorphic) if they
/// have identical `CanonicalWfstStructure` values. This means:
/// - Same state count, same state accepting status/weights
/// - Same transition topology (same tokens lead to same states with same weights)
/// - Same action *shapes* at each De Bruijn position (Direct vs Lookahead vs Cast etc.)
/// - Only the concrete names (rule labels, category names) differ
///
/// The De Bruijn canonicalization walks transitions in deterministic order
/// (state 0 first, sorted by token_id within each state) and replaces each
/// unique `action_idx` with a sequential index (0, 1, 2, ...).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CanonicalWfstStructure {
    pub states: Vec<CanonicalState>,
    pub start: WfstStateId,
    /// Action shapes in De Bruijn order. `action_shapes[i]` is the shape of
    /// the action at De Bruijn index `i`.
    pub action_shapes: Vec<CanonicalActionShape>,
}
