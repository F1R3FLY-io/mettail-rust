//! Runtime-image adapter for the shared longest-per-kind selector.
//!
//! Positions retain the complete persistent mode context. Source offsets are
//! separate from context identity and remain the only input to slicing/ranking.
//! The queue visits context-indexed positions; it never enumerates whole paths.

use super::{
    lexer_transition, DelimitedSpanError, EffectiveRuntimeLimits, InputText, ModeId, RuntimeError,
    RuntimeParser, TemplateHoleOccurrence, TokenId, TokenPattern,
};
use crate::{visit_lexical_survivors, BuiltinToken, LexicalSelectionError, ModeTransition};
use std::collections::{BTreeMap, VecDeque};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct LexPosition {
    pub offset: usize,
    context: usize,
}

impl LexPosition {
    pub const START: Self = Self { offset: 0, context: 0 };

    pub fn at(self, offset: usize) -> Self {
        Self { offset, ..self }
    }

    pub fn is_balanced(self) -> bool {
        self.context == 0
    }
}

#[derive(Clone, Debug)]
pub(super) enum LexicalEdge {
    Accepted {
        token: TokenId,
        target: LexPosition,
        alternative: u32,
    },
    /// A retained lexical candidate whose exact mode transition is invalid.
    /// It remains explicit evidence, never an exhaustion-to-empty conversion.
    Refuted {
        token: TokenId,
        end: usize,
        reason: RuntimeError,
    },
}

#[derive(Clone, Default)]
pub(super) struct LexicalNode {
    pub edges: Vec<LexicalEdge>,
    pub trivia: Option<LexPosition>,
    primary_successor: Option<LexPosition>,
    primary_failure: Option<RuntimeError>,
}

#[derive(Default)]
struct NodeState {
    primary: bool,
    expanded: Option<LexicalNode>,
}

#[derive(Default)]
pub(super) struct LexicalLattice {
    nodes: BTreeMap<LexPosition, NodeState>,
}

impl LexicalLattice {
    pub fn node(&self, position: LexPosition) -> Option<&LexicalNode> {
        self.nodes.get(&position)?.expanded.as_ref()
    }

    pub fn build(
        parser: &RuntimeParser<'_>,
        input: &InputText<'_>,
        holes: &BTreeMap<usize, TemplateHoleOccurrence>,
    ) -> Result<Self, RuntimeError> {
        let mut budget = Budget::new(parser.limits);
        budget.state()?;
        let mut builder = Builder {
            parser,
            input,
            holes,
            foreign_delimiters: parser.foreign_delimiters(),
            contexts: ModeContexts::new(),
            budget,
            lattice: Self::default(),
            queue: VecDeque::new(),
        };
        builder.enqueue(LexPosition::START, true)?;
        while let Some(position) = builder.queue.pop_front() {
            builder.budget.work(1)?;
            let state = &builder.lattice.nodes[&position];
            let primary = state.primary;
            if let Some(node) = &state.expanded {
                // A position first reached through a secondary edge may later
                // join the primary chain. Reuse its result and propagate only
                // primary reachability, without re-lexing or merging contexts.
                if primary {
                    if let Some(error) = &node.primary_failure {
                        return Err(error.clone());
                    }
                    if let Some(next) = node.primary_successor {
                        builder.enqueue(next, true)?;
                    }
                }
                continue;
            }
            let (node, successors) = match builder.expand(position) {
                Ok(result) => result,
                Err(error) if !primary && structural_failure(&error) => (
                    LexicalNode {
                        primary_failure: Some(error),
                        ..Default::default()
                    },
                    Vec::new(),
                ),
                Err(error) => return Err(error),
            };
            if primary {
                if let Some(error) = &node.primary_failure {
                    return Err(error.clone());
                }
            }
            builder
                .lattice
                .nodes
                .get_mut(&position)
                .expect("queued position exists")
                .expanded = Some(node);
            for (next, locally_primary) in successors {
                builder.enqueue(next, primary && locally_primary)?;
            }
        }
        Ok(builder.lattice)
    }
}

fn structural_failure(error: &RuntimeError) -> bool {
    matches!(
        error,
        RuntimeError::Lex { .. }
            | RuntimeError::LexerModeUnderflow { .. }
            | RuntimeError::LexerModeUnclosed { .. }
            | RuntimeError::ForeignLanguage { .. }
    )
}

struct Budget {
    states: usize,
    edges: usize,
    work: u64,
    scratch: usize,
}

impl Budget {
    fn new(limits: EffectiveRuntimeLimits) -> Self {
        Self {
            states: limits.lexer_states,
            edges: limits.lexer_edges,
            work: limits.lexer_work,
            scratch: limits.lexer_edges,
        }
    }

    fn state(&mut self) -> Result<(), RuntimeError> {
        self.states = self
            .states
            .checked_sub(1)
            .ok_or(RuntimeError::LexerStateLimit)?;
        Ok(())
    }

    fn edge(&mut self) -> Result<(), RuntimeError> {
        self.edges = self
            .edges
            .checked_sub(1)
            .ok_or(RuntimeError::LexerEdgeLimit)?;
        Ok(())
    }

    fn work(&mut self, amount: usize) -> Result<(), RuntimeError> {
        let amount = u64::try_from(amount).map_err(|_| RuntimeError::LexerWorkLimit)?;
        self.work = self
            .work
            .checked_sub(amount)
            .ok_or(RuntimeError::LexerWorkLimit)?;
        Ok(())
    }
}

struct ModeFrame {
    parent: Option<usize>,
    top: ModeId,
    depth: usize,
}

struct ModeContexts {
    frames: Vec<ModeFrame>,
    pushed: BTreeMap<(usize, ModeId), usize>,
}

impl ModeContexts {
    fn new() -> Self {
        Self {
            frames: vec![ModeFrame { parent: None, top: ModeId(0), depth: 1 }],
            pushed: BTreeMap::new(),
        }
    }

    fn transition(
        &mut self,
        mut context: usize,
        transition: ModeTransition,
        byte: usize,
        depth_limit: usize,
        budget: &mut Budget,
    ) -> Result<usize, RuntimeError> {
        if transition.pop {
            context = self.frames[context]
                .parent
                .ok_or(RuntimeError::LexerModeUnderflow { byte })?;
        }
        if let Some(mode) = transition.push {
            let depth = self.frames[context].depth;
            if depth >= depth_limit {
                return Err(RuntimeError::LexerModeDepthLimit { byte });
            }
            let key = (context, mode);
            if let Some(existing) = self.pushed.get(&key) {
                return Ok(*existing);
            }
            budget.state()?;
            let id = self.frames.len();
            self.frames.push(ModeFrame {
                parent: Some(context),
                top: mode,
                depth: depth + 1,
            });
            self.pushed.insert(key, id);
            context = id;
        }
        Ok(context)
    }
}

struct Builder<'a, 'input, 'grammar> {
    parser: &'a RuntimeParser<'grammar>,
    input: &'a InputText<'input>,
    holes: &'a BTreeMap<usize, TemplateHoleOccurrence>,
    foreign_delimiters: Vec<(&'a str, &'a str)>,
    contexts: ModeContexts,
    budget: Budget,
    lattice: LexicalLattice,
    queue: VecDeque<LexPosition>,
}

impl Builder<'_, '_, '_> {
    fn enqueue(&mut self, position: LexPosition, primary: bool) -> Result<(), RuntimeError> {
        if let Some(existing) = self.lattice.nodes.get_mut(&position) {
            if primary && !existing.primary {
                existing.primary = true;
                self.queue.push_back(position);
            }
            return Ok(());
        }
        self.budget.state()?;
        self.lattice
            .nodes
            .insert(position, NodeState { primary, expanded: None });
        self.queue.push_back(position);
        Ok(())
    }

    fn jump(
        &mut self,
        target: LexPosition,
        trivia: bool,
    ) -> Result<(LexicalNode, Vec<(LexPosition, bool)>), RuntimeError> {
        self.budget.edge()?;
        Ok((
            LexicalNode {
                trivia: trivia.then_some(target),
                primary_successor: Some(target),
                ..Default::default()
            },
            vec![(target, true)],
        ))
    }

    fn expand(
        &mut self,
        position: LexPosition,
    ) -> Result<(LexicalNode, Vec<(LexPosition, bool)>), RuntimeError> {
        let parser = self.parser;
        let mode = self.contexts.frames[position.context].top;
        if position.offset >= self.input.end {
            if !position.is_balanced() {
                return Err(RuntimeError::LexerModeUnclosed {
                    byte: self.input.end,
                    depth: self.contexts.frames[position.context].depth,
                });
            }
            if position.offset > self.input.end {
                return Ok((LexicalNode::default(), Vec::new()));
            }
            let mut eof = Vec::new();
            for id in &parser.grammar.modes[mode.0 as usize].token_ids {
                self.budget.work(1)?;
                if matches!(
                    parser.grammar.tokens[id.0 as usize].pattern,
                    TokenPattern::Builtin(BuiltinToken::EndOfInput)
                ) {
                    self.budget.edge()?;
                    eof.push(*id);
                }
            }
            eof.sort_by_key(|id| {
                (std::cmp::Reverse(parser.grammar.tokens[id.0 as usize].priority), *id)
            });
            if eof.is_empty() {
                return Ok((LexicalNode::default(), Vec::new()));
            }
            // Preserve the logical-EOF contract: no mode transition is run.
            let target = position.at(position
                .offset
                .checked_add(1)
                .ok_or(RuntimeError::InputTooLarge)?);
            let edges = eof
                .into_iter()
                .enumerate()
                .map(|(alternative, token)| {
                    Ok(LexicalEdge::Accepted {
                        token,
                        target,
                        alternative: u32::try_from(alternative)
                            .map_err(|_| RuntimeError::LexerEdgeLimit)?,
                    })
                })
                .collect::<Result<Vec<_>, RuntimeError>>()?;
            return Ok((
                LexicalNode {
                    edges,
                    primary_successor: Some(target),
                    ..Default::default()
                },
                vec![(target, true)],
            ));
        }
        if let Some(hole) = self.holes.get(&position.offset) {
            return self.jump(position.at(hole.end), false);
        }
        let (base, fragment) = self
            .input
            .fragments
            .range(..=position.offset)
            .next_back()
            .ok_or(RuntimeError::Lex { byte: position.offset })?;
        let local = position.offset - *base;
        let suffix = fragment
            .get(local..)
            .ok_or(RuntimeError::Lex { byte: position.offset })?;
        for &(open, close) in &self.foreign_delimiters {
            self.budget.work(1)?;
            if !suffix.starts_with(open) {
                continue;
            }
            let end = match self.input.delimited_span(
                position.offset,
                open,
                close,
                parser.limits.foreign_nesting,
            ) {
                Ok(Some((_, _, end))) => end,
                Err(DelimitedSpanError::NestingLimit) => {
                    return Err(RuntimeError::ForeignNestingLimit { byte: position.offset })
                },
                _ => {
                    return Err(RuntimeError::ForeignLanguage {
                        byte: position.offset,
                        message: format!(
                            "unterminated foreign-language region `{open}` ... `{close}`"
                        ),
                    })
                },
            };
            // This is not a trivia alias: only scan_foreign crosses the span.
            return self.jump(position.at(end), false);
        }
        let mut state = parser.image.lexer.mode_starts[mode.0 as usize];
        let mut accepts = Vec::new();
        for (index, byte) in suffix.bytes().enumerate() {
            self.budget.work(1)?;
            let Some(next) = lexer_transition(&parser.image.lexer, state, byte) else {
                break;
            };
            state = next;
            let candidates = &parser.image.lexer.states[state as usize].accept;
            self.budget.work(candidates.len())?;
            if !candidates.is_empty() {
                if accepts.len() >= self.budget.scratch {
                    return Err(RuntimeError::LexerEdgeLimit);
                }
                accepts.push((state, position.offset + index + 1));
            }
        }
        let Some(&(primary_state, primary_end)) = accepts.last() else {
            return Err(RuntimeError::Lex { byte: position.offset });
        };
        let primary_token = parser.image.lexer.states[primary_state as usize].accept[0];
        let primary = &parser.grammar.tokens[primary_token.0 as usize];
        if primary.channel != "main" {
            let context = self.contexts.transition(
                position.context,
                primary.transition,
                position.offset,
                parser.limits.lexer_mode_depth,
                &mut self.budget,
            )?;
            return self.jump(LexPosition { offset: primary_end, context }, true);
        }
        let accepts = accepts.into_iter().rev().filter(|(state, _)| {
            let id = parser.image.lexer.states[*state as usize].accept[0];
            parser.grammar.tokens[id.0 as usize].channel == "main"
        });
        let mut node = LexicalNode::default();
        let mut targets = BTreeMap::new();
        let mut surviving_ends = Vec::new();
        visit_lexical_survivors(
            accepts,
            |state, _| {
                parser.image.lexer.states[state as usize]
                    .accept
                    .iter()
                    .copied()
                    .map(|id| (id, ()))
            },
            |token, (), end, ordinal| {
                self.budget.edge()?;
                let definition = &parser.grammar.tokens[token.0 as usize];
                match self.contexts.transition(
                    position.context,
                    definition.transition,
                    position.offset,
                    parser.limits.lexer_mode_depth,
                    &mut self.budget,
                ) {
                    Ok(context) => {
                        let target = LexPosition { offset: end, context };
                        if let Some(previous) = targets.insert(end, target) {
                            if previous != target {
                                return Err(RuntimeError::Image(
                                    "coaccepting tokens disagree on mode context".into(),
                                ));
                            }
                        }
                        node.edges.push(LexicalEdge::Accepted {
                            token,
                            target,
                            alternative: u32::try_from(ordinal)
                                .map_err(|_| RuntimeError::LexerEdgeLimit)?,
                        });
                    },
                    Err(reason) if structural_failure(&reason) => {
                        if end == primary_end {
                            node.primary_failure = Some(reason.clone());
                        }
                        node.edges.push(LexicalEdge::Refuted { token, end, reason });
                    },
                    Err(error) => return Err(error),
                }
                Ok(())
            },
            |end, primary| {
                surviving_ends.push((end, primary));
                Ok(())
            },
        )
        .map_err(|error| match error {
            LexicalSelectionError::Visitor(error) => error,
            LexicalSelectionError::OrdinalOverflow => RuntimeError::LexerEdgeLimit,
        })?;
        let mut successors = Vec::with_capacity(surviving_ends.len());
        for (end, primary) in surviving_ends {
            if let Some(target) = targets.get(&end).copied() {
                if primary {
                    node.primary_successor = Some(target);
                }
                successors.push((target, primary));
            }
        }
        Ok((node, successors))
    }
}
