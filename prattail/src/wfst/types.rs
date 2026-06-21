use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// WFST types (minimal, from lling-llang)
// ══════════════════════════════════════════════════════════════════════════════

/// State identifier in a WFST.
pub type WfstStateId = u32;

/// Sentinel for "no state".
pub const NO_STATE: WfstStateId = WfstStateId::MAX;

/// A weighted transition in the prediction WFST.
///
/// Maps an input token to a dispatch action with an associated weight.
#[derive(Debug, Clone)]
pub struct WeightedTransition {
    /// Source state.
    pub from: WfstStateId,
    /// Input label (token ID). `EPSILON_TOKEN` for epsilon transitions.
    pub input: TokenId,
    /// Output: index into the action table.
    pub action_idx: u32,
    /// Target state.
    pub to: WfstStateId,
    /// Transition weight (tropical: lower = more likely).
    pub weight: TropicalWeight,
}

/// A state in the prediction WFST.
#[derive(Debug, Clone)]
pub struct WfstState {
    /// State identifier.
    pub id: WfstStateId,
    /// Whether this is a final (accepting) state.
    pub is_final: bool,
    /// Final weight (if accepting).
    pub final_weight: TropicalWeight,
    /// Outgoing transitions.
    pub transitions: Vec<WeightedTransition>,
}

impl WfstState {
    /// Create a new non-final state.
    pub fn new(id: WfstStateId) -> Self {
        WfstState {
            id,
            is_final: false,
            final_weight: TropicalWeight::zero(),
            transitions: Vec::new(),
        }
    }

    /// Create a new final state with the given weight.
    pub fn final_state(id: WfstStateId, weight: TropicalWeight) -> Self {
        WfstState {
            id,
            is_final: true,
            final_weight: weight,
            transitions: Vec::new(),
        }
    }
}

/// A weighted prediction entry: dispatch action + tropical weight.
#[derive(Debug, Clone)]
pub struct WeightedAction {
    /// The dispatch action to take.
    pub action: DispatchAction,
    /// Weight for this action (tropical: lower = better).
    pub weight: TropicalWeight,
}
