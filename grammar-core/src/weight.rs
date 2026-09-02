use serde::{Deserialize, Serialize};
use std::cmp::Ordering;

pub use rigail::{ExactParseCost, ParseCostError, TICKS_PER_UNIT};

/// One lexer decision at a logical input position.
///
/// Longer extents precede shorter extents (maximal munch); equal extents use
/// the canonical lexer-alternative ordinal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LexicalDecision {
    pub extent: u32,
    pub alternative: u32,
}

impl Ord for LexicalDecision {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .extent
            .cmp(&self.extent)
            .then_with(|| self.alternative.cmp(&other.alternative))
    }
}

impl PartialOrd for LexicalDecision {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Declaration-order identity of a completed source production.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SourceRuleRank {
    pub source_category: u32,
    pub declaration: u32,
}

/// Canonical two-phase provenance at one logical input position.
///
/// Lexical decisions are compared before completed productions. Encounter
/// order remains stable inside each phase.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PositionRank {
    pub position: u32,
    pub lexical: Vec<LexicalDecision>,
    pub productions: Vec<SourceRuleRank>,
}

/// Deterministic derivation provenance, deliberately separate from cost.
///
/// The sparse position vector is canonical: positions are strictly ascending,
/// and composition appends the lexical and production phases independently at
/// equal positions. This is the executable representation of the
/// position-indexed monoid proved in `DerivationRank.v`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct DerivationRank {
    positions: Vec<PositionRank>,
}

impl DerivationRank {
    pub fn lexical(position: u32, extent: u32, alternative: u32) -> Self {
        Self {
            positions: vec![PositionRank {
                position,
                lexical: vec![LexicalDecision { extent, alternative }],
                productions: Vec::new(),
            }],
        }
    }

    pub fn positions(&self) -> &[PositionRank] {
        &self.positions
    }

    pub fn event_count(&self) -> usize {
        self.positions
            .iter()
            .map(|position| position.lexical.len() + position.productions.len())
            .sum()
    }

    pub(crate) fn retained_heap_weight(&self) -> usize {
        let mut weight = self
            .positions
            .capacity()
            .saturating_mul(std::mem::size_of::<PositionRank>());
        for position in &self.positions {
            weight = weight
                .saturating_add(
                    position
                        .lexical
                        .capacity()
                        .saturating_mul(std::mem::size_of::<LexicalDecision>()),
                )
                .saturating_add(
                    position
                        .productions
                        .capacity()
                        .saturating_mul(std::mem::size_of::<SourceRuleRank>()),
                );
        }
        weight
    }

    /// Compose provenance in grammatical order using an iterative merge.
    pub fn combine(&self, right: &Self) -> Self {
        if self.positions.is_empty() {
            return right.clone();
        }
        if right.positions.is_empty() {
            return self.clone();
        }

        let mut positions = Vec::with_capacity(self.positions.len() + right.positions.len());
        let mut left_index = 0;
        let mut right_index = 0;
        while left_index < self.positions.len() && right_index < right.positions.len() {
            let left = &self.positions[left_index];
            let right = &right.positions[right_index];
            match left.position.cmp(&right.position) {
                Ordering::Less => {
                    positions.push(left.clone());
                    left_index += 1;
                },
                Ordering::Greater => {
                    positions.push(right.clone());
                    right_index += 1;
                },
                Ordering::Equal => {
                    let mut combined = left.clone();
                    combined.lexical.extend(right.lexical.iter().copied());
                    combined
                        .productions
                        .extend(right.productions.iter().copied());
                    positions.push(combined);
                    left_index += 1;
                    right_index += 1;
                },
            }
        }
        positions.extend(self.positions[left_index..].iter().cloned());
        positions.extend(right.positions[right_index..].iter().cloned());
        Self { positions }
    }

    /// Attach one source production exactly once at constituent completion.
    ///
    /// Inserting at the start of the production phase puts an outer production
    /// before children that share its origin while retaining the lexical-first
    /// phase invariant.
    pub fn complete_production(mut self, position: u32, rule: SourceRuleRank) -> Self {
        match self
            .positions
            .binary_search_by_key(&position, |entry| entry.position)
        {
            Ok(index) => self.positions[index].productions.insert(0, rule),
            Err(index) => self.positions.insert(
                index,
                PositionRank {
                    position,
                    lexical: Vec::new(),
                    productions: vec![rule],
                },
            ),
        }
        self
    }
}

/// The execution profile is part of the image contract.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum WeightProfile {
    /// Consensus-safe exact min-plus cost. All alternatives are retained;
    /// derivation provenance provides the separate deterministic tie-break.
    Exact {
        default: ExactParseCost,
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
            default: ExactParseCost::default(),
            retain_all_alternatives: true,
        }
    }

    pub fn exact_default(&self) -> Option<ExactParseCost> {
        match self {
            Self::Exact { default, .. } => Some(*default),
            Self::LocalLog { .. } => None,
        }
    }

    pub fn is_consensus_safe(&self) -> bool {
        matches!(self, Self::Exact { retain_all_alternatives: true, .. })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lexical(position: u32, extent: u32, alternative: u32) -> DerivationRank {
        DerivationRank::lexical(position, extent, alternative)
    }

    fn rule(category: u32, declaration: u32) -> SourceRuleRank {
        SourceRuleRank { source_category: category, declaration }
    }

    #[test]
    fn iterative_composition_is_associative_and_has_identity() {
        let first = lexical(7, 1, 0).complete_production(7, rule(0, 4));
        let second = lexical(2, 3, 1).complete_production(2, rule(1, 0));
        let third = lexical(7, 2, 0).complete_production(7, rule(0, 8));
        let empty = DerivationRank::default();

        assert_eq!(empty.combine(&first), first);
        assert_eq!(first.combine(&empty), first);
        assert_eq!(first.combine(&second).combine(&third), first.combine(&second.combine(&third)));
    }

    #[test]
    fn lexical_phase_precedes_outer_then_inner_productions() {
        let child = lexical(0, 1, 0).complete_production(0, rule(0, 2));
        let completed = child.complete_production(0, rule(0, 9));
        let position = &completed.positions()[0];

        assert_eq!(position.lexical, vec![LexicalDecision { extent: 1, alternative: 0 }]);
        assert_eq!(position.productions, vec![rule(0, 9), rule(0, 2)]);
    }

    #[test]
    fn maximal_munch_and_alternative_order_are_local() {
        assert!(lexical(3, 2, 0) < lexical(3, 1, 0));
        assert!(lexical(3, 2, 0) < lexical(3, 2, 1));
    }

    #[test]
    fn grammatical_slot_fold_is_scheduler_independent() {
        let parent = DerivationRank::default().complete_production(0, rule(0, 9));
        let left = lexical(0, 1, 0).complete_production(0, rule(0, 4));
        let right = lexical(3, 1, 0).complete_production(3, rule(0, 5));

        let left_finished_first = [parent.clone(), left.clone(), right.clone()]
            .iter()
            .fold(DerivationRank::default(), |rank, child| rank.combine(child));
        let right_finished_first = [parent, left, right]
            .iter()
            .fold(DerivationRank::default(), |rank, child| rank.combine(child));
        assert_eq!(left_finished_first, right_finished_first);
    }
}
