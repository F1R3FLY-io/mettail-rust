//! Deterministic derivation ordering, separate from semiring path cost.
//!
//! Weighted parsing has two distinct concerns:
//!
//! - [`ExactParseCost`](crate::automata::semiring::ExactParseCost) is the
//!   lawful min-plus carrier used by weighted pushdown reachability.
//! - This module records *why* a derivation was chosen: lexical extent,
//!   lexer-alternative priority, and grammar declaration priority.
//!
//! A [`RankFragment`] annotates lexical decisions made by a parser transition.
//! Completed grammar productions are attached exactly once to their completed
//! SPPF packing; transition timing never supplies production authority.
//!
//! A complete rank is canonicalized as a sparse sequence of logical input
//! positions. Each position has two phases: lexical decisions in surface order,
//! followed by completed productions in parse-tree preorder. Composition
//! concatenates the two phases independently at each position. This is the
//! position-indexed monoid proved in `formal/rocq/runtime_grammar/theories/
//! DerivationRank.v`: it is associative, has the empty rank as identity, and is
//! independent of parse-forest association, GSS sharing, worker scheduling,
//! delayed commits, and synthetic factoring.
//!
//! Maximal munch is local to an input position: a longer opener wins only at
//! the position where the competing lexical decisions occur. It cannot mask
//! an earlier decision merely because it appears later in the derivation.

use std::{cmp::Ordering, collections::BTreeMap};

use crate::path_tree_arena::{PathTreeArena, StackId, STACK_ID_ROOT};

/// Declaration-order identity of a grammar decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SourceRuleRank {
    pub source_category: u16,
    pub rule: u16,
}

/// Rank evidence contributed by one parser transition.
///
/// Every field is optional because a pure scalar charge, such as the
/// cross-category grouping penalty, must carry no derivation authority and no
/// fabricated source/rule identity.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RankFragment {
    pub open_len: Option<u32>,
    pub lex_alt: Option<u16>,
    pub source_rule: Option<SourceRuleRank>,
}

impl RankFragment {
    pub const EMPTY: Self = Self {
        open_len: None,
        lex_alt: None,
        source_rule: None,
    };

    pub const fn rule(source_category: u16, rule: u16) -> Self {
        Self {
            open_len: None,
            lex_alt: None,
            source_rule: Some(SourceRuleRank { source_category, rule }),
        }
    }

    /// Record a lexer decision without claiming that a grammar rule has
    /// completed. Grammar declaration evidence is derived exactly once from
    /// the completed Symbol/Packing during final forest election.
    pub const fn lexical_only(open_len: Option<u32>, lex_alt: u16) -> Self {
        Self {
            open_len,
            lex_alt: Some(lex_alt),
            source_rule: None,
        }
    }

    pub const fn lexical(
        open_len: Option<u32>,
        lex_alt: u16,
        source_category: u16,
        rule: u16,
    ) -> Self {
        Self {
            open_len,
            lex_alt: Some(lex_alt),
            source_rule: Some(SourceRuleRank { source_category, rule }),
        }
    }

    pub const fn is_empty(self) -> bool {
        self.open_len.is_none() && self.lex_alt.is_none() && self.source_rule.is_none()
    }

    /// Whether this fragment records only a completed grammar-rule choice.
    /// Such a choice is positioned at the constituent origin, even when the
    /// transition that commits it scans the closing delimiter.
    pub const fn is_rule_only(self) -> bool {
        self.open_len.is_none() && self.lex_alt.is_none() && self.source_rule.is_some()
    }

    /// Remove completed-production authority from a transition annotation.
    /// Production evidence is reconstructed exactly once from a completed
    /// Symbol/Packing pair during final forest election.
    pub const fn lexical_evidence(self) -> Self {
        Self {
            open_len: self.open_len,
            lex_alt: self.lex_alt,
            source_rule: None,
        }
    }

    /// Expand this allocation-free transition annotation into its canonical
    /// event components at `input_position`.
    pub fn events_at(self, input_position: u32) -> impl Iterator<Item = RankEvent> {
        let open = self.open_len.map(|open_len| RankEvent {
            input_position,
            decision: RankDecision::OpenLength(open_len),
        });
        let alternative = self.lex_alt.map(|lex_alt| RankEvent {
            input_position,
            decision: RankDecision::LexAlternative(lex_alt),
        });
        let rule = self.source_rule.map(|source_rule| RankEvent {
            input_position,
            decision: RankDecision::SourceRule(source_rule),
        });
        open.into_iter().chain(alternative).chain(rule)
    }
}

/// One input-positioned, consensus-visible derivation decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RankEvent {
    pub input_position: u32,
    pub decision: RankDecision,
}

/// Kind and value of a derivation-ranking decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RankDecision {
    /// Matched opener width. Larger is preferred at the same input position.
    OpenLength(u32),
    /// Lexer alternative ordinal. Smaller is preferred.
    LexAlternative(u16),
    /// Grammar declaration priority. Smaller category/rule ordinals win.
    SourceRule(SourceRuleRank),
}

impl RankEvent {
    fn decision_kind(self) -> u8 {
        match self.decision {
            RankDecision::OpenLength(_) => 0,
            RankDecision::LexAlternative(_) => 1,
            RankDecision::SourceRule(_) => 2,
        }
    }
}

impl Ord for RankEvent {
    fn cmp(&self, other: &Self) -> Ordering {
        self.input_position
            .cmp(&other.input_position)
            .then_with(|| self.decision_kind().cmp(&other.decision_kind()))
            .then_with(|| match (self.decision, other.decision) {
                // Reverse only the width value: larger openers rank first.
                (RankDecision::OpenLength(left), RankDecision::OpenLength(right)) => {
                    right.cmp(&left)
                },
                (RankDecision::LexAlternative(left), RankDecision::LexAlternative(right)) => {
                    left.cmp(&right)
                },
                (RankDecision::SourceRule(left), RankDecision::SourceRule(right)) => {
                    left.cmp(&right)
                },
                // The decision-kind comparison above made unlike kinds unequal.
                _ => Ordering::Equal,
            })
    }
}

impl PartialOrd for RankEvent {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Canonical rank of one complete derivation.
///
/// Events are stored by ascending logical input position. Within one position,
/// all lexical events precede all production events; encounter order is stable
/// inside each phase. Lexicographic comparison of this canonical persistent
/// vector is therefore total and deterministic. If one vector is a prefix of
/// the other, the shorter derivation wins.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CompleteDerivationRank {
    events: im::Vector<RankEvent>,
}

/// Opaque handle to a persistent rank-event trace.
///
/// The wrapper prevents accidental interchange with SPPF- or GSS-stack arena
/// handles, which use the same underlying path-tree implementation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RankTraceId(StackId);

impl RankTraceId {
    pub const EMPTY: Self = Self(STACK_ID_ROOT);
}

/// Hash-consed persistent traces for fork-heavy parser execution.
///
/// A cursor carries only two `RankTraceId` values (whole derivation and the
/// current packing suffix). Forking therefore copies eight bytes rather than
/// cloning a growing event vector. Equal event histories share arena nodes.
#[derive(Default)]
pub struct DerivationRankArena {
    traces: PathTreeArena<RankEvent>,
}

impl DerivationRankArena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&mut self) {
        self.traces.clear();
    }

    pub fn append_event(&mut self, trace: RankTraceId, event: RankEvent) -> RankTraceId {
        RankTraceId(self.traces.intern_push(trace.0, event))
    }

    /// Append all non-empty decisions from one parser transition.
    pub fn append_fragment(
        &mut self,
        mut trace: RankTraceId,
        input_position: u32,
        fragment: RankFragment,
    ) -> RankTraceId {
        for event in fragment.lexical_evidence().events_at(input_position) {
            trace = self.append_event(trace, event);
        }
        trace
    }

    /// Canonicalize one persistent trace for final comparison or packing.
    pub fn complete(&self, trace: RankTraceId) -> CompleteDerivationRank {
        CompleteDerivationRank::from_events(self.traces.to_vec(trace.0))
    }

    pub fn len(&self, trace: RankTraceId) -> usize {
        self.traces.len(trace.0)
    }

    pub fn node_count(&self) -> usize {
        self.traces.node_count()
    }
}

/// One generated parser transition: lawful scalar cost plus non-algebraic
/// deterministic rank evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RankedStep<W> {
    pub cost: W,
    pub rank: RankFragment,
}

impl<W> RankedStep<W> {
    pub const fn new(cost: W, rank: RankFragment) -> Self {
        Self { cost, rank }
    }

    pub const fn scalar(cost: W) -> Self {
        Self { cost, rank: RankFragment::EMPTY }
    }
}

impl CompleteDerivationRank {
    pub fn from_events(events: impl IntoIterator<Item = RankEvent>) -> Self {
        Self { events: canonicalize_events(events) }
    }

    pub fn from_positioned_fragments(
        fragments: impl IntoIterator<Item = (u32, RankFragment)>,
    ) -> Self {
        Self::from_events(
            fragments
                .into_iter()
                .flat_map(|(position, fragment)| fragment.events_at(position)),
        )
    }

    pub fn events(&self) -> &im::Vector<RankEvent> {
        &self.events
    }

    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Retain only lexical evidence. Parser-transition rank is projected
    /// through this method before a completed packing contributes its unique
    /// production decision.
    pub fn lexical_evidence(&self) -> Self {
        Self::from_events(
            self.events
                .iter()
                .copied()
                .filter(|event| !matches!(event.decision, RankDecision::SourceRule(_))),
        )
    }

    /// Retain only completed-production evidence.
    pub fn production_evidence(&self) -> Self {
        Self::from_events(
            self.events
                .iter()
                .copied()
                .filter(|event| matches!(event.decision, RankDecision::SourceRule(_))),
        )
    }

    pub fn combine<'a>(parts: impl IntoIterator<Item = &'a Self>) -> Self {
        Self::from_events(
            parts
                .into_iter()
                .flat_map(|part| part.events.iter().copied()),
        )
    }
}

#[derive(Default)]
struct PositionPhases {
    lexical: Vec<RankEvent>,
    productions: Vec<RankEvent>,
}

/// Iteratively normalize an arbitrary event stream into the position-indexed
/// two-phase representation. The stable per-phase pushes are the executable
/// counterpart of the Rocq `combine_bucket` append laws.
fn canonicalize_events(events: impl IntoIterator<Item = RankEvent>) -> im::Vector<RankEvent> {
    let mut by_position: BTreeMap<u32, PositionPhases> = BTreeMap::new();
    for event in events {
        let phases = by_position.entry(event.input_position).or_default();
        match event.decision {
            RankDecision::OpenLength(_) | RankDecision::LexAlternative(_) => {
                phases.lexical.push(event);
            },
            RankDecision::SourceRule(_) => phases.productions.push(event),
        }
    }

    let event_count = by_position
        .values()
        .map(|phases| phases.lexical.len() + phases.productions.len())
        .sum();
    let mut canonical = Vec::with_capacity(event_count);
    for phases in by_position.into_values() {
        canonical.extend(phases.lexical);
        canonical.extend(phases.productions);
    }
    canonical.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_fragment_has_no_events() {
        assert!(RankFragment::EMPTY.is_empty());
        assert_eq!(RankFragment::EMPTY.events_at(7).count(), 0);
        assert!(!RankFragment::EMPTY.is_rule_only());
        assert!(RankFragment::rule(2, 3).is_rule_only());
        assert!(!RankFragment::lexical_only(Some(2), 0).is_rule_only());
    }

    #[test]
    fn complete_rank_is_independent_of_fragment_association() {
        let a = CompleteDerivationRank::from_positioned_fragments([
            (9, RankFragment::rule(2, 4)),
            (1, RankFragment::lexical(Some(2), 0, 0, 3)),
        ]);
        let left = CompleteDerivationRank::combine([
            &CompleteDerivationRank::combine([
                &CompleteDerivationRank::from_positioned_fragments([(9, RankFragment::rule(2, 4))]),
                &CompleteDerivationRank::default(),
            ]),
            &CompleteDerivationRank::from_positioned_fragments([(
                1,
                RankFragment::lexical(Some(2), 0, 0, 3),
            )]),
        ]);
        assert_eq!(left, a);
    }

    #[test]
    fn complete_rank_preserves_causal_order_at_one_position() {
        let outer_then_inner = CompleteDerivationRank::from_positioned_fragments([
            (0, RankFragment::rule(0, 9)),
            (0, RankFragment::rule(0, 0)),
        ]);
        let different_outer = CompleteDerivationRank::from_positioned_fragments([
            (0, RankFragment::rule(0, 1)),
            (0, RankFragment::rule(0, 9)),
        ]);

        assert!(different_outer < outer_then_inner);
    }

    #[test]
    fn canonical_rank_is_position_indexed_and_phase_ordered() {
        let rank = CompleteDerivationRank::from_positioned_fragments([
            (9, RankFragment::rule(2, 4)),
            (1, RankFragment::rule(0, 3)),
            (1, RankFragment::lexical_only(Some(2), 0)),
            (9, RankFragment::lexical_only(Some(1), 1)),
        ]);
        let observed: Vec<_> = rank.events().iter().copied().collect();

        assert_eq!(
            observed
                .iter()
                .map(|event| event.input_position)
                .collect::<Vec<_>>(),
            [1, 1, 1, 9, 9, 9]
        );
        assert!(matches!(observed[0].decision, RankDecision::OpenLength(2)));
        assert!(matches!(observed[1].decision, RankDecision::LexAlternative(0)));
        assert!(matches!(observed[2].decision, RankDecision::SourceRule(_)));
        assert!(matches!(observed[3].decision, RankDecision::OpenLength(1)));
        assert!(matches!(observed[4].decision, RankDecision::LexAlternative(1)));
        assert!(matches!(observed[5].decision, RankDecision::SourceRule(_)));
    }

    #[test]
    fn pointwise_composition_keeps_parent_before_child_at_shared_origin() {
        let parent =
            CompleteDerivationRank::from_positioned_fragments([(0, RankFragment::rule(0, 7))]);
        let child = CompleteDerivationRank::from_positioned_fragments([
            (0, RankFragment::lexical_only(Some(1), 0)),
            (0, RankFragment::rule(0, 2)),
        ]);
        let completed = CompleteDerivationRank::combine([&parent, &child]);
        let productions: Vec<_> = completed
            .events()
            .iter()
            .filter_map(|event| match event.decision {
                RankDecision::SourceRule(rule) => Some(rule.rule),
                _ => None,
            })
            .collect();

        assert_eq!(productions, [7, 2]);
        assert!(matches!(completed.events()[0].decision, RankDecision::OpenLength(1)));
    }

    #[test]
    fn grammatical_slot_assembly_is_independent_of_completion_schedule() {
        let parent =
            CompleteDerivationRank::from_positioned_fragments([(0, RankFragment::rule(0, 9))]);
        let left =
            CompleteDerivationRank::from_positioned_fragments([(0, RankFragment::rule(0, 4))]);
        let right =
            CompleteDerivationRank::from_positioned_fragments([(3, RankFragment::rule(0, 5))]);

        let left_finished_first = CompleteDerivationRank::combine([&parent, &left, &right]);
        let right_finished_first = CompleteDerivationRank::combine([&parent, &left, &right]);
        assert_eq!(left_finished_first, right_finished_first);
    }

    #[test]
    fn transition_projection_removes_production_authority_only() {
        let mixed = CompleteDerivationRank::from_positioned_fragments([(
            2,
            RankFragment::lexical(Some(3), 1, 4, 8),
        )]);

        assert_eq!(mixed.lexical_evidence().events().len(), 2);
        assert_eq!(mixed.production_evidence().events().len(), 1);
        assert!(mixed
            .lexical_evidence()
            .events()
            .iter()
            .all(|event| !matches!(event.decision, RankDecision::SourceRule(_))));
    }

    #[test]
    fn lexical_only_never_claims_a_completed_grammar_rule() {
        let fragment = RankFragment::lexical_only(Some(3), 2);
        assert!(fragment.source_rule.is_none());
        assert_eq!(fragment.events_at(4).count(), 2);
    }

    #[test]
    fn maximal_munch_is_local_to_the_competing_input_position() {
        let earlier_short = CompleteDerivationRank::from_positioned_fragments([
            (1, RankFragment::lexical(Some(1), 0, 0, 0)),
            (8, RankFragment::lexical(Some(9), 0, 0, 0)),
        ]);
        let earlier_long = CompleteDerivationRank::from_positioned_fragments([
            (1, RankFragment::lexical(Some(2), 0, 0, 0)),
            (8, RankFragment::lexical(Some(1), 0, 0, 0)),
        ]);
        assert!(earlier_long < earlier_short);
    }

    #[test]
    fn lexical_then_declaration_priority_is_total() {
        let primary = CompleteDerivationRank::from_positioned_fragments([(
            3,
            RankFragment::lexical(Some(1), 0, 2, 7),
        )]);
        let lexical_alternative = CompleteDerivationRank::from_positioned_fragments([(
            3,
            RankFragment::lexical(Some(1), 1, 0, 0),
        )]);
        let later_rule = CompleteDerivationRank::from_positioned_fragments([(
            3,
            RankFragment::lexical(Some(1), 0, 2, 8),
        )]);
        assert!(primary < lexical_alternative);
        assert!(primary < later_rule);
    }

    #[test]
    fn persistent_trace_forks_share_prefix_and_canonicalize_independently() {
        let mut arena = DerivationRankArena::new();
        let prefix =
            arena.append_fragment(RankTraceId::EMPTY, 1, RankFragment::lexical(Some(2), 0, 0, 0));
        let first = arena.append_fragment(prefix, 5, RankFragment::lexical_only(None, 1));
        let second = arena.append_fragment(prefix, 5, RankFragment::lexical_only(None, 2));

        assert_eq!(arena.len(prefix), 2);
        assert_eq!(arena.len(first), 3);
        assert_eq!(arena.len(second), 3);
        assert_ne!(arena.complete(first), arena.complete(second));
        // Two shared prefix nodes plus one suffix node per fork.
        assert_eq!(arena.node_count(), 4);
    }

    #[test]
    fn transition_arena_cannot_record_completed_productions() {
        let mut arena = DerivationRankArena::new();
        let trace = arena.append_fragment(RankTraceId::EMPTY, 4, RankFragment::rule(2, 7));

        assert_eq!(trace, RankTraceId::EMPTY);
        assert!(arena.complete(trace).is_empty());
    }

    #[test]
    fn empty_fragment_does_not_allocate_or_change_trace_identity() {
        let mut arena = DerivationRankArena::new();
        let trace = arena.append_fragment(RankTraceId::EMPTY, 17, RankFragment::EMPTY);
        assert_eq!(trace, RankTraceId::EMPTY);
        assert_eq!(arena.node_count(), 0);
    }
}
