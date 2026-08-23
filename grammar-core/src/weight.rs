use serde::{Deserialize, Serialize};

/// Deterministic weight used by consensus parser images.
///
/// Components are compared lexicographically and added component-wise. They
/// are integers so ordering is independent of the host floating-point unit.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ExactWeight {
    pub recovery: u32,
    pub ambiguity: u32,
    pub preference: u32,
    pub declaration: u32,
}

impl ExactWeight {
    pub const ZERO: Self = Self {
        recovery: 0,
        ambiguity: 0,
        preference: 0,
        declaration: 0,
    };

    pub fn checked_extend(self, rhs: Self) -> Option<Self> {
        Some(Self {
            recovery: self.recovery.checked_add(rhs.recovery)?,
            ambiguity: self.ambiguity.checked_add(rhs.ambiguity)?,
            preference: self.preference.checked_add(rhs.preference)?,
            declaration: self.declaration.checked_add(rhs.declaration)?,
        })
    }

    pub fn rank_key(self) -> (u32, u32, u32, u32) {
        (self.recovery, self.ambiguity, self.preference, self.declaration)
    }
}

impl Ord for ExactWeight {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.rank_key().cmp(&other.rank_key())
    }
}

impl PartialOrd for ExactWeight {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// The execution profile is part of the image contract.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum WeightProfile {
    /// Consensus-safe. All alternatives are retained; weights rank only.
    Exact {
        default: ExactWeight,
        retain_all_alternatives: bool,
    },
    /// Tooling-only probabilistic profile. It cannot be accepted by the exact VM.
    LocalLog {
        beam_width: Option<f64>,
        model_fingerprint: Option<[u8; 32]>,
    },
}

impl WeightProfile {
    pub fn exact() -> Self {
        Self::Exact {
            default: ExactWeight::ZERO,
            retain_all_alternatives: true,
        }
    }

    pub fn is_consensus_safe(&self) -> bool {
        matches!(self, Self::Exact { retain_all_alternatives: true, .. })
    }
}
