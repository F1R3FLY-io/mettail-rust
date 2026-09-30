//! Project the existing runtime lexer into the existing lattice token source.
//!
//! The session owns lexical evidence, including refutations and structural
//! holes. The dense view owns only the token observations required by the
//! original walker. Full mode-context positions, never bare byte offsets,
//! identify nodes. No text is lexed, joined, or rewritten here.

use crate::automata::{semiring::TropicalWeight, TokenKind};
use crate::lexer_types::{LexAlternative, LexDag, LexDagEdge, LexDagNode};
use crate::wpda_runtime::{LatticeTokenSource, WpdaTokenSource};
use mettail_grammar_core::TokenId;
use mettail_grammar_core::{
    LexPosition, LexicalEdge, LexicalNode, RuntimeLexicalSession, TemplateHoleOccurrence,
};
use std::collections::BTreeMap;

/// Storage admission for the additional view, independent of lexer work limits.
#[derive(Clone, Copy, Debug)]
pub struct SourceAdapterLimits {
    pub nodes: usize,
    pub edges: usize,
    /// Retained source and token-kind bytes, including lazy secondary copies.
    pub text_bytes: usize,
}

#[cfg(test)]
mod tests;

#[derive(Debug, PartialEq, Eq)]
pub enum SourceAdapterError<E> {
    NodeLimit,
    NodeIndexOverflow,
    EdgeLimit,
    TextLimit,
    AlternativeIndexOverflow(u32),
    MissingPosition(LexPosition),
    MissingEnd,
    InvalidSlice { start: usize, end: usize },
    TokenBinding(E),
}

/// Identity of an accepted source edge, separate from its dense view index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TokenOccurrence {
    pub token: TokenId,
    pub end: LexPosition,
    pub alternative: u32,
}

pub struct OwnedTokenSource<'session, 'parser, 'input, 'grammar> {
    session: &'session RuntimeLexicalSession<'parser, 'input, 'grammar>,
    inner: LatticeTokenSource,
    positions: Vec<LexPosition>,
    node_ids: BTreeMap<LexPosition, usize>,
    occurrences: Vec<Vec<TokenOccurrence>>,
}

impl<'session, 'parser, 'input, 'grammar> OwnedTokenSource<'session, 'parser, 'input, 'grammar> {
    /// Admit copied source text first; then project each original accepted
    /// edge once, in order. `token_kind` must use admitted lexer observations,
    /// not names, regex guessing, native evaluation, or a replacement lexer.
    /// Internal callers separately prepay any allocating token observer.
    pub(crate) fn new<E>(
        session: &'session RuntimeLexicalSession<'parser, 'input, 'grammar>,
        limits: SourceAdapterLimits,
        mut token_kind: impl FnMut(TokenId, &str) -> Result<TokenKind, E>,
    ) -> Result<Self, SourceAdapterError<E>> {
        use SourceAdapterError as Error;
        let start = session.canonical_position(LexPosition::START);
        session.node(start).ok_or(Error::MissingPosition(start))?;
        let (mut node_count, mut edge_count, mut text_bytes) = (0usize, 0usize, 0usize);
        // This finite census precedes all adapter-owned allocation and all
        // token-observer calls. Refuted edges also count toward edge admission.
        for (position, node) in session.nodes() {
            node_count = node_count.checked_add(1).ok_or(Error::NodeLimit)?;
            if node_count > limits.nodes {
                return Err(Error::NodeLimit);
            }
            u32::try_from(node_count).map_err(|_| Error::NodeIndexOverflow)?;
            edge_count = edge_count
                .checked_add(node.edges.len())
                .ok_or(Error::EdgeLimit)?;
            if edge_count > limits.edges {
                return Err(Error::EdgeLimit);
            }
            let mut primary = true;
            for edge in &node.edges {
                if let LexicalEdge::Accepted { target, alternative, .. } = edge {
                    u16::try_from(*alternative)
                        .map_err(|_| Error::AlternativeIndexOverflow(*alternative))?;
                    let text = session.input_slice(position.offset, target.offset).ok_or(
                        Error::InvalidSlice {
                            start: position.offset,
                            end: target.offset,
                        },
                    )?;
                    let copies = if primary { 1 } else { 2 };
                    primary = false;
                    let retained = text.len().checked_mul(copies).ok_or(Error::TextLimit)?;
                    text_bytes = text_bytes.checked_add(retained).ok_or(Error::TextLimit)?;
                    if text_bytes > limits.text_bytes {
                        return Err(Error::TextLimit);
                    }
                }
            }
        }
        let mut positions = Vec::with_capacity(node_count);
        // The original walker starts at node zero. Only an existing trivia
        // alias is followed; no token edge or mode context is collapsed.
        positions.push(start);
        positions.extend(session.nodes().map(|(p, _)| p).filter(|p| *p != start));
        let node_ids: BTreeMap<_, _> = positions.iter().copied().zip(0..).collect();
        let eof_node = positions
            .iter()
            .position(|p| session.is_logical_eoi(*p))
            .ok_or(Error::MissingEnd)?;
        let mut nodes = Vec::with_capacity(node_count);
        let mut occurrences = Vec::with_capacity(node_count);
        for &position in &positions {
            if let Some(hole) = session.hole_at(position.offset) {
                let end = session.canonical_position(position.at(hole.end));
                if !node_ids.contains_key(&end) {
                    return Err(Error::MissingPosition(end));
                }
            }
            let node = session
                .node(position)
                .ok_or(Error::MissingPosition(position))?;
            let accepted = node
                .edges
                .iter()
                .filter(|e| matches!(e, LexicalEdge::Accepted { .. }))
                .count();
            let mut edges = Vec::with_capacity(accepted);
            let mut origins = Vec::with_capacity(accepted);
            for edge in &node.edges {
                let LexicalEdge::Accepted { token, target, alternative } = edge else {
                    // The entire original node remains available through
                    // evidence_at; refutation is not converted into EOF.
                    continue;
                };
                let canonical = session.canonical_position(*target);
                let target_node = *node_ids
                    .get(&canonical)
                    .ok_or(Error::MissingPosition(canonical))?;
                let text = session.input_slice(position.offset, target.offset).ok_or(
                    Error::InvalidSlice {
                        start: position.offset,
                        end: target.offset,
                    },
                )?;
                let kind = token_kind(*token, text).map_err(Error::TokenBinding)?;
                edges.push(LexDagEdge {
                    kind,
                    text: text.to_owned(),
                    end_byte: target.offset,
                    target_node,
                    // Runtime lexical candidates have no scalar cost. Their
                    // original ordinals/extents remain separate rank evidence.
                    weight: TropicalWeight::new(0.0),
                    alt_idx: u16::try_from(*alternative)
                        .map_err(|_| Error::AlternativeIndexOverflow(*alternative))?,
                });
                origins.push(TokenOccurrence {
                    token: *token,
                    end: *target,
                    alternative: *alternative,
                });
            }
            nodes.push(LexDagNode { byte_start: position.offset, edges });
            occurrences.push(origins);
        }
        let inner = LatticeTokenSource::new(LexDag {
            nodes,
            // That legacy builder index is not read by LatticeTokenSource.
            // Providing a byte-only index here would erase mode distinctions.
            byte_to_node: BTreeMap::new(),
            eof_node,
        });
        Ok(Self {
            session,
            inner,
            positions,
            node_ids,
            occurrences,
        })
    }

    /// Resolve token kinds from the observations retained by this exact grammar.
    /// Missing observations remain explicit errors, never guessed token kinds.
    pub fn from_admitted_session(
        session: &'session RuntimeLexicalSession<'parser, 'input, 'grammar>,
        mut limits: SourceAdapterLimits,
    ) -> Result<Self, SourceAdapterError<super::token_bindings::TokenBindingError>> {
        let bindings = super::token_bindings::OwnedTokenBindings::new(session.grammar())
            .map_err(SourceAdapterError::TokenBinding)?;
        // Include the existing source's lazy secondary kind clones before any
        // observer allocates. The text census below pays the same copy count.
        for (_, node) in session.nodes() {
            let mut primary = true;
            for edge in &node.edges {
                if let LexicalEdge::Accepted { token, .. } = edge {
                    let bytes = bindings
                        .payload_bytes(*token)
                        .map_err(SourceAdapterError::TokenBinding)?;
                    let copies = if primary { 1 } else { 2 };
                    primary = false;
                    let retained = bytes
                        .checked_mul(copies)
                        .ok_or(SourceAdapterError::TextLimit)?;
                    limits.text_bytes = limits
                        .text_bytes
                        .checked_sub(retained)
                        .ok_or(SourceAdapterError::TextLimit)?;
                }
            }
        }
        Self::new(session, limits, |token, text| bindings.resolve(token, text))
    }

    pub fn session(&self) -> &'session RuntimeLexicalSession<'parser, 'input, 'grammar> {
        self.session
    }

    pub fn position(&self, node: usize) -> Option<LexPosition> {
        self.positions.get(node).copied()
    }

    pub fn node_id(&self, position: LexPosition) -> Option<usize> {
        self.node_ids.get(&position).copied()
    }

    pub fn token_occurrence(&self, node: usize, alternative: usize) -> Option<TokenOccurrence> {
        self.occurrences.get(node)?.get(alternative).copied()
    }

    pub fn evidence_at(&self, node: usize) -> Option<&'session LexicalNode> {
        self.session.node(self.position(node)?)
    }

    pub fn hole_at(&self, node: usize) -> Option<&'session TemplateHoleOccurrence> {
        self.session.hole_at(self.position(node)?.offset)
    }

    pub fn hole_target(&self, node: usize) -> Option<usize> {
        let position = self.position(node)?;
        let hole = self.hole_at(node)?;
        self.node_id(self.session.canonical_position(position.at(hole.end)))
    }

    pub fn structural_hole_edge(
        &self,
        category: mettail_grammar_core::CategoryId,
        node: usize,
    ) -> Option<mettail_grammar_core::StructuralHoleEdge> {
        self.session
            .structural_hole_edge(category.0, self.position(node)?)
    }
}

impl WpdaTokenSource for OwnedTokenSource<'_, '_, '_, '_> {
    fn token_occurrence(&self, pos: usize, alternative: usize) -> Option<u32> {
        self.occurrences.get(pos)?.get(alternative)?;
        u32::try_from(alternative).ok()
    }
    fn peek_kind(&self, pos: usize) -> Option<TokenKind> {
        // Empty dead ends and structural holes are not fabricated EOF tokens.
        match self.occurrences.get(pos) {
            Some(edges) if !edges.is_empty() || self.is_logical_eoi(pos) => {
                self.inner.peek_kind(pos)
            },
            _ => None,
        }
    }
    fn peek_text(&self, pos: usize) -> Option<&str> {
        match self.occurrences.get(pos) {
            Some(edges) if !edges.is_empty() || self.is_logical_eoi(pos) => {
                self.inner.peek_text(pos)
            },
            _ => None,
        }
    }
    fn len(&self) -> usize {
        self.inner.len()
    }
    fn peek_alternatives(&self, pos: usize) -> &[LexAlternative] {
        self.inner.peek_alternatives(pos)
    }
    fn is_ambiguous_at(&self, pos: usize) -> bool {
        self.inner.is_ambiguous_at(pos)
    }
    fn end_byte(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        self.inner.end_byte(pos, alt_idx)
    }
    fn next_pos(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        self.inner.next_pos(pos, alt_idx)
    }
    fn positions_are_linear_tokens(&self) -> bool {
        false
    }
    fn position_order_key(&self, pos: usize) -> Option<usize> {
        self.inner.position_order_key(pos)
    }
    fn eof_node(&self) -> usize {
        self.inner.eof_node()
    }
    fn is_logical_eoi(&self, pos: usize) -> bool {
        self.position(pos)
            .is_some_and(|p| self.session.is_logical_eoi(p))
    }
}
