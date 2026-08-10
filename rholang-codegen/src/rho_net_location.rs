//! Compact subject-position identities for the in-Rho matching network.
//!
//! The original location ABI copied the complete `/constructor.index` prefix
//! into every descendant channel.  A unary term of depth `d` consequently
//! retained `1 + 2 + ... + d` path bytes even though its topology has only
//! `d` edges.  [`SubjectLocationIndex`] assigns one fixed-width identity to
//! every position and records each parent-to-child edge once.  The spread and
//! every matcher receive the same index, so rendezvous remains by construction
//! rather than by a hash or a second independently implemented numbering pass.

use crate::rho_net::scoped_channel_name;
use crate::rho_net_lower::GroundTerm;

/// Encode one exact compact position into the shared matching-channel ABI.
///
/// `root_site` is byte-length-prefixed and `position` is fixed-width, so the
/// encoding is injective without a digest or delimiter-escaping convention.
/// Subject indexes and the benchmark-only persistent matcher both use this
/// function; neither may grow a channel by copying its ancestors' path.
pub(crate) fn compact_position_channel(
    family: &str,
    language_fingerprint: &str,
    root_site: &str,
    position: u64,
) -> String {
    let path = format!("@i2:{:016x}:{}:{position:016x}", root_site.len(), root_site);
    scoped_channel_name(family, language_fingerprint, path)
}

/// One real subject position.  The value is an index into a
/// [`SubjectLocationIndex`], hence equality is exact and collision-free.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct SubjectPosition(usize);

impl SubjectPosition {
    pub(crate) const ROOT: Self = Self(0);

    #[cfg(test)]
    pub(crate) fn index(self) -> usize {
        self.0
    }
}

/// A matcher position can be absent when a pattern descends beyond the actual
/// subject.  Every absent continuation reads one reserved dead channel; the
/// spread never publishes there, so sharing that name cannot create a COMM.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MatcherPosition {
    Live(SubjectPosition),
    Dead,
}

impl From<SubjectPosition> for MatcherPosition {
    fn from(position: SubjectPosition) -> Self {
        Self::Live(position)
    }
}

#[derive(Debug)]
struct IndexedNode<'a> {
    term: &'a GroundTerm,
    first_child: usize,
    child_count: usize,
}

/// A stack-safe, prefix-compressed index of the positional portion of one
/// ground subject.  AC collections are leaves in this index because their
/// elements travel through the native collection carrier rather than through
/// positional `loc:` descent.
#[derive(Debug)]
pub(crate) struct SubjectLocationIndex<'a> {
    nodes: Vec<IndexedNode<'a>>,
}

impl<'a> SubjectLocationIndex<'a> {
    /// Build the index iteratively.  Each subject node and edge is retained
    /// exactly once, so construction and resident topology are both linear.
    pub(crate) fn new(root: &'a GroundTerm) -> Self {
        let mut nodes = vec![IndexedNode {
            term: root,
            first_child: 0,
            child_count: 0,
        }];
        let mut pending = vec![SubjectPosition::ROOT];

        while let Some(position) = pending.pop() {
            let term = nodes[position.0].term;
            if term.coll_type.is_some() || term.children.is_empty() {
                continue;
            }

            let first_child = nodes.len();
            for (offset, child) in term.children.iter().enumerate() {
                debug_assert_eq!(nodes.len(), first_child + offset);
                nodes.push(IndexedNode {
                    term: child,
                    first_child: 0,
                    child_count: 0,
                });
            }
            for offset in (0..term.children.len()).rev() {
                pending.push(SubjectPosition(first_child + offset));
            }
            nodes[position.0].first_child = first_child;
            nodes[position.0].child_count = term.children.len();
        }

        assert!(
            nodes.len() < u64::MAX as usize,
            "a subject-location index must leave u64::MAX reserved for the dead channel"
        );
        Self { nodes }
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    pub(crate) fn term(&self, position: SubjectPosition) -> &'a GroundTerm {
        self.nodes[position.0].term
    }

    pub(crate) fn child(
        &self,
        position: SubjectPosition,
        child_index: usize,
    ) -> Option<SubjectPosition> {
        let node = &self.nodes[position.0];
        (child_index < node.child_count).then(|| SubjectPosition(node.first_child + child_index))
    }

    pub(crate) fn matcher_child(
        &self,
        position: MatcherPosition,
        child_index: usize,
    ) -> MatcherPosition {
        match position {
            MatcherPosition::Live(position) => self
                .child(position, child_index)
                .map_or(MatcherPosition::Dead, MatcherPosition::Live),
            MatcherPosition::Dead => MatcherPosition::Dead,
        }
    }

    pub(crate) fn children(
        &self,
        position: SubjectPosition,
    ) -> impl ExactSizeIterator<Item = SubjectPosition> + DoubleEndedIterator<Item = SubjectPosition> + '_
    {
        let node = &self.nodes[position.0];
        (node.first_child..node.first_child + node.child_count).map(SubjectPosition)
    }

    /// Resolve a compiler-owned `(parent constructor, child index)` path.
    /// Constructor checks keep contextual-hole paths fail-closed if a subject
    /// has the same arity but a different spine.
    pub(crate) fn resolve_path(
        &self,
        start: SubjectPosition,
        path: &[(String, usize)],
    ) -> Option<SubjectPosition> {
        let mut position = start;
        for (parent_op, child_index) in path {
            if self.term(position).constructor != *parent_op {
                return None;
            }
            position = self.child(position, *child_index)?;
        }
        Some(position)
    }

    /// Iterative pre-order walk from `start`.  `visit` controls whether the
    /// current node's positional children are scheduled.
    pub(crate) fn walk(
        &self,
        start: SubjectPosition,
        mut visit: impl FnMut(SubjectPosition, &'a GroundTerm) -> bool,
    ) {
        let mut pending = vec![start];
        while let Some(position) = pending.pop() {
            if !visit(position, self.term(position)) {
                continue;
            }
            pending.extend(self.children(position).rev());
        }
    }

    /// Collision-free v2 channel name for one real or deliberately absent
    /// position.  `root_site` is byte-length-prefixed and the position is a
    /// fixed-width hexadecimal `u64`; therefore two triples
    /// `(root_site, position, family)` encode equally iff all components are
    /// equal.  No probabilistic digest participates in rendezvous identity.
    pub(crate) fn channel(
        &self,
        family: &str,
        language_fingerprint: &str,
        root_site: &str,
        position: impl Into<MatcherPosition>,
    ) -> String {
        let position = match position.into() {
            MatcherPosition::Live(position) => position.0 as u64,
            MatcherPosition::Dead => u64::MAX,
        };
        compact_position_channel(family, language_fingerprint, root_site, position)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_width_positions_are_injective_even_for_adversarial_root_text() {
        let subject =
            GroundTerm::new("f", vec![GroundTerm::nullary("a"), GroundTerm::nullary("b")]);
        let index = SubjectLocationIndex::new(&subject);
        let left = index.child(SubjectPosition::ROOT, 0).expect("left child");
        let right = index.child(SubjectPosition::ROOT, 1).expect("right child");
        let adversarial = "@i2:0000000000000001:x:0000000000000000";

        let names = [
            index.channel("loc", "fp", adversarial, SubjectPosition::ROOT),
            index.channel("loc", "fp", adversarial, left),
            index.channel("loc", "fp", adversarial, right),
            index.channel("loc", "fp", adversarial, MatcherPosition::Dead),
            index.channel("cap", "fp", adversarial, left),
            index.channel("loc", "other-fp", adversarial, left),
        ];
        for (i, name) in names.iter().enumerate() {
            assert!(
                names[..i].iter().all(|previous| previous != name),
                "channel components must be jointly injective"
            );
        }
    }

    #[test]
    fn collection_elements_are_not_positional_children() {
        let subject = GroundTerm::collection(
            mettail_ast::types::CollectionType::HashBag,
            "Bag",
            vec![GroundTerm::nullary("a")],
        );
        let index = SubjectLocationIndex::new(&subject);
        assert_eq!(index.len(), 1);
        assert_eq!(index.child(SubjectPosition::ROOT, 0), None);
    }

    #[test]
    fn unary_depth_twenty_thousand_has_fixed_width_channels_on_a_small_stack() {
        std::thread::Builder::new()
            .name("subject-position-index-small-stack".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 20_000;
                let mut subject = GroundTerm::nullary("leaf");
                for _ in 0..DEPTH {
                    subject = GroundTerm::new("n", vec![subject]);
                }

                let index = SubjectLocationIndex::new(&subject);
                assert_eq!(index.len(), DEPTH + 1);
                let root_width = index
                    .channel("loc", "fp", "site0", SubjectPosition::ROOT)
                    .len();
                let total_width: usize = (0..index.len())
                    .map(|position| {
                        index
                            .channel("loc", "fp", "site0", SubjectPosition(position))
                            .len()
                    })
                    .sum();
                assert_eq!(total_width, root_width * index.len());

                drop(index);
                drop(subject);
            })
            .expect("spawn compact subject-position gate")
            .join()
            .expect("compact subject-position indexing overflowed or panicked");
    }
}
