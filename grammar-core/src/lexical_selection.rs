//! Shared selection from an already ordered stream of lexer acceptances.
//!
//! This is the longest-per-kind operation extracted from PraTTaIL's generated
//! lexer adapter. DFA traversal, primary trivia handling, mode transitions,
//! token decoding and worklist scheduling remain the caller's responsibility.
//! Acceptances must arrive in descending endpoint order; alternatives at one
//! endpoint must already have their canonical order. The first occurrence of
//! each kind survives with its payload unchanged. Successors are reported once
//! per surviving endpoint, in encounter order.

use std::collections::HashSet;
use std::hash::Hash;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexicalSelectionError<E> {
    Visitor(E),
    OrdinalOverflow,
}

/// Visit the existing longest-per-kind edge sequence without materializing a
/// second edge buffer. An emitter can enforce its allocation limit before
/// retaining an edge. Any error aborts the operation; callers must discard
/// their partial local output, not report it as a complete selection.
///
/// `kind` is token-definition identity, not result-category identity. `payload`
/// is backend-owned and is neither inspected nor decoded here. The ordinal is
/// global to this node, not reset at each endpoint. A successor is locally
/// primary only when it is the first supplied endpoint; the worklist must also
/// require its parent to be on the primary chain before propagating that flag.
///
/// Formal contract: `LexicalSurvivorAdapter::loop_refines_ordered_selection`,
/// `every_survivor_is_maximal_for_its_kind`, and
/// `successor_iff_surviving_endpoint`. These are relative to the existing
/// lexical policy, not unrestricted token-segmentation completeness.
pub fn visit_lexical_survivors<K, P, A, I, Alternatives, E>(
    accepts: I,
    mut alternatives: impl FnMut(A, usize) -> Alternatives,
    mut emit: impl FnMut(K, P, usize, usize) -> Result<(), E>,
    mut successor: impl FnMut(usize, bool) -> Result<(), E>,
) -> Result<(), LexicalSelectionError<E>>
where
    K: Clone + Eq + Hash,
    I: IntoIterator<Item = (A, usize)>,
    Alternatives: IntoIterator<Item = (K, P)>,
{
    let mut accepts = accepts.into_iter().peekable();
    let primary_end = accepts.peek().map(|(_, end)| *end);
    let mut seen_kinds = HashSet::new();
    let mut enqueued_endpoints = HashSet::new();
    let mut ordinal = 0usize;
    for (accept, end) in accepts {
        let mut emitted_any = false;
        for (kind, payload) in alternatives(accept, end) {
            if seen_kinds.contains(&kind) {
                continue;
            }
            let next_ordinal = ordinal
                .checked_add(1)
                .ok_or(LexicalSelectionError::OrdinalOverflow)?;
            // The caller checks its retained-output budget before the shared
            // selector allocates bookkeeping for this additional survivor.
            emit(kind.clone(), payload, end, ordinal).map_err(LexicalSelectionError::Visitor)?;
            seen_kinds.insert(kind);
            ordinal = next_ordinal;
            emitted_any = true;
        }
        if emitted_any && enqueued_endpoints.insert(end) {
            successor(end, Some(end) == primary_end).map_err(LexicalSelectionError::Visitor)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinct_kinds_retain_their_own_endpoints_and_exact_payloads() {
        let mut edges = Vec::new();
        let mut next = Vec::new();
        visit_lexical_survivors(
            [(vec![(0, "Identifier ab")], 2), (vec![(0, "Identifier a"), (1, "Scalar a")], 1)],
            |tokens, _| tokens,
            |kind, payload, end, ordinal| {
                edges.push((kind, payload, end, ordinal));
                Ok::<_, ()>(())
            },
            |end, primary| {
                next.push((end, primary));
                Ok(())
            },
        )
        .expect("ordered selection");
        assert_eq!(edges, [(0, "Identifier ab", 2, 0), (1, "Scalar a", 1, 1)]);
        assert_eq!(next, [(2, true), (1, false)]);
    }

    #[test]
    fn same_endpoint_keeps_order_and_only_surviving_endpoints_are_queued() {
        let mut edges = Vec::new();
        let mut next = Vec::new();
        visit_lexical_survivors(
            [(vec![(7, 10), (8, 11)], 4), (vec![(7, 12)], 3), (vec![(8, 13), (9, 14)], 2)],
            |tokens, _| tokens,
            |kind, payload, end, ordinal| {
                edges.push((kind, payload, end, ordinal));
                Ok::<_, ()>(())
            },
            |end, primary| {
                next.push((end, primary));
                Ok(())
            },
        )
        .expect("ordered selection");
        assert_eq!(edges, [(7, 10, 4, 0), (8, 11, 4, 1), (9, 14, 2, 2)]);
        assert_eq!(next, [(4, true), (2, false)]);
    }

    #[test]
    fn empty_primary_acceptance_does_not_promote_a_secondary_endpoint() {
        let mut next = Vec::new();
        visit_lexical_survivors(
            [(Vec::<(u8, ())>::new(), 3), (vec![(1, ())], 2)],
            |tokens, _| tokens,
            |_, _, _, _| Ok::<_, ()>(()),
            |end, primary| {
                next.push((end, primary));
                Ok(())
            },
        )
        .expect("selection");
        assert_eq!(next, [(2, false)]);
    }

    #[test]
    fn visitor_failure_aborts_before_reporting_a_successor() {
        let result = visit_lexical_survivors(
            [(vec![(1, ())], 1)],
            |tokens, _| tokens,
            |_, _, _, _| Err("edge limit"),
            |_, _| panic!("a failed edge must not yield a successor"),
        );
        assert_eq!(result, Err(LexicalSelectionError::Visitor("edge limit")));
    }

    #[test]
    fn shared_selection_matches_the_pre_extraction_loop_on_the_finite_corpus() {
        // Each of three descending endpoints has any subset of three kinds.
        // Run both canonical within-end orders. The oracle below is the old
        // generated adapter's loop, retained only as a regression reference.
        for masks in 0..512usize {
            for reverse in [false, true] {
                let accepts = (0..3)
                    .map(|group| {
                        let mask = (masks >> (group * 3)) & 7;
                        let mut tokens = (0..3)
                            .filter(|kind| mask & (1 << kind) != 0)
                            .map(|kind| (kind, group * 10 + kind))
                            .collect::<Vec<_>>();
                        if reverse {
                            tokens.reverse();
                        }
                        (tokens, 3 - group)
                    })
                    .collect::<Vec<_>>();
                let mut expected_edges = Vec::new();
                let mut expected_successors = Vec::new();
                let mut seen = HashSet::new();
                let mut enqueued = HashSet::new();
                let primary = accepts.first().map(|(_, end)| *end);
                for (tokens, end) in &accepts {
                    let mut emitted = false;
                    for (kind, payload) in tokens {
                        if !seen.insert(*kind) {
                            continue;
                        }
                        expected_edges.push((*kind, *payload, *end, expected_edges.len()));
                        emitted = true;
                    }
                    if emitted && enqueued.insert(*end) {
                        expected_successors.push((*end, Some(*end) == primary));
                    }
                }
                let mut actual_edges = Vec::new();
                let mut actual_successors = Vec::new();
                visit_lexical_survivors(
                    accepts,
                    |tokens, _| tokens,
                    |kind, payload, end, ordinal| {
                        actual_edges.push((kind, payload, end, ordinal));
                        Ok::<_, ()>(())
                    },
                    |end, primary| {
                        actual_successors.push((end, primary));
                        Ok(())
                    },
                )
                .expect("finite corpus selection");
                assert_eq!(actual_edges, expected_edges, "masks={masks}, reverse={reverse}");
                assert_eq!(actual_successors, expected_successors);
            }
        }
    }
}
