//! Original generated token-kind observations, keyed by admitted Core IDs.
//! No regex inspection, token-name fallback, lexer construction or host call.
//! `TokenKindBindingObservation.v` covers the finite observation boundary;
//! lexer/image admission and actual lexical parity remain separate obligations.

use crate::automata::{token_kind_matches_capture_name, TokenKind};
use crate::wpda_rule_analysis::prefix_pattern::NeutralPattern;
use mettail_grammar_core::{GrammarCoreV1, TokenId, WpdaTokenObservation as O};
use std::collections::BTreeMap;

#[cfg(test)]
mod tests;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenBindingError {
    MissingTable,
    WrongTableLength,
    MissingToken(TokenId),
}

/// Borrow only an already admitted grammar. This view does not grant admission.
pub struct OwnedTokenBindings<'grammar> {
    rows: &'grammar [Option<O>],
}

impl<'grammar> OwnedTokenBindings<'grammar> {
    pub fn new(grammar: &'grammar GrammarCoreV1) -> Result<Self, TokenBindingError> {
        let rows = grammar
            .wpda_token_observations
            .as_deref()
            .ok_or(TokenBindingError::MissingTable)?;
        if rows.len() != grammar.tokens.len() {
            return Err(TokenBindingError::WrongTableLength);
        }
        Ok(Self { rows })
    }

    /// Resolve one actual lattice alternative. BooleanText is the original
    /// generated lexer payload operation, NOT RuntimeParser::decode_token.
    pub fn resolve(&self, token: TokenId, text: &str) -> Result<TokenKind, TokenBindingError> {
        let row = self
            .rows
            .get(token.0 as usize)
            .and_then(Option::as_ref)
            .ok_or(TokenBindingError::MissingToken(token))?;
        Ok(observe(row, text))
    }

    /// Bytes cloned into the TokenKind payload, available before allocation.
    /// Charge these in addition to matched source text in the source adapter.
    pub fn payload_bytes(&self, token: TokenId) -> Result<usize, TokenBindingError> {
        let row = self
            .rows
            .get(token.0 as usize)
            .and_then(Option::as_ref)
            .ok_or(TokenBindingError::MissingToken(token))?;
        Ok(match row {
            O::IntegerLit(text)
            | O::RationalLit(text)
            | O::FixedPointLit(text)
            | O::Fixed(text)
            | O::Custom(text) => text.len(),
            _ => 0,
        })
    }
}

fn observe(row: &O, text: &str) -> TokenKind {
    match row {
        O::Eof => TokenKind::Eof,
        O::Ident => TokenKind::Ident,
        O::Integer => TokenKind::Integer,
        O::IntegerLit(name) => TokenKind::IntegerLit(name.clone()),
        O::RationalLit(name) => TokenKind::RationalLit(name.clone()),
        O::FixedPointLit(name) => TokenKind::FixedPointLit(name.clone()),
        O::Float => TokenKind::Float,
        O::True => TokenKind::True,
        O::False => TokenKind::False,
        O::BooleanLit => TokenKind::BooleanLit,
        O::StringLit => TokenKind::StringLit,
        O::Fixed(text) => TokenKind::Fixed(text.clone()),
        O::Dollar => TokenKind::Dollar,
        O::DoubleDollar => TokenKind::DoubleDollar,
        O::Custom(name) => TokenKind::Custom(name.clone()),
        O::BooleanText => {
            if text == "true" {
                TokenKind::True
            } else {
                TokenKind::False
            }
        },
    }
}

/// Mirror the actual quotation sites, preserving their distinct descriptors.
/// Guards are evaluated only after the original TokenKind pattern matches.
pub fn matches_prefix(
    pattern: &NeutralPattern,
    guard: Option<&NeutralPattern>,
    kind: &TokenKind,
) -> bool {
    use NeutralPattern as P;
    let matched = match pattern {
        P::FixedKeyword => matches!(kind, TokenKind::Fixed(_)),
        P::Ident => matches!(kind, TokenKind::Ident),
        P::Integer => matches!(kind, TokenKind::Integer),
        P::BooleanAlternative => {
            matches!(kind, TokenKind::True | TokenKind::False | TokenKind::BooleanLit)
        },
        P::StringLiteral => matches!(kind, TokenKind::StringLit),
        P::Float => matches!(kind, TokenKind::Float),
        P::Capture => true,
        P::GuestCustomRef | P::CustomTyped => matches!(kind, TokenKind::Custom(_)),
        P::IntegerTyped => matches!(kind, TokenKind::IntegerLit(_)),
        P::RationalTyped => matches!(kind, TokenKind::RationalLit(_)),
        P::FixedPointTyped => matches!(kind, TokenKind::FixedPointLit(_)),
        _ => false,
    };
    if !matched {
        return false;
    }
    match guard {
        None | Some(P::Empty) => true,
        Some(P::FixedText(expected)) => {
            matches!(kind, TokenKind::Fixed(actual) if actual == expected)
        },
        Some(P::CaptureName(name)) => token_kind_matches_capture_name(name, kind),
        Some(P::GuestName(expected)) => {
            matches!(kind, TokenKind::Custom(actual) if actual == expected)
        },
        Some(P::CategoryName(expected)) => matches!(kind,
            TokenKind::IntegerLit(actual) | TokenKind::RationalLit(actual)
            | TokenKind::FixedPointLit(actual) | TokenKind::Custom(actual) if actual == expected),
        _ => false,
    }
}

/// Compile-time retained projection of the SAME active lexer input and writer
/// roster. Calling this builds no automaton and renders no generated source.
pub struct TokenObservationProducer {
    by_variant: BTreeMap<String, O>,
    selected_terminals: BTreeMap<String, TokenKind>,
}

impl TokenObservationProducer {
    pub(crate) fn for_spec(spec: &crate::LanguageSpec) -> Self {
        let bundle = crate::pipeline::extract_lexer_bundle(spec);
        let input = crate::pipeline::lexer_input_for_bundle(&bundle);
        Self::for_input(&input)
    }

    pub fn for_input(input: &crate::lexer::LexerInput) -> Self {
        Self::for_metadata(
            input,
            &input.custom_tokens,
            input.modes.iter().map(|mode| mode.custom_tokens.as_slice()),
        )
    }

    /// Source-only view of the same roster. Execution fields not observed by
    /// the original writer need not be fabricated by another frontend.
    pub fn for_metadata<'a, T: crate::token_declarations::TokenMetadata + Clone + 'a>(
        input: &crate::lexer::LexerInput,
        global: &[T],
        modes: impl IntoIterator<Item = &'a [T]>,
    ) -> Self {
        let mut kinds = crate::lexer::hybrid_token_kinds_from_metadata(input, global);
        let mut custom = global.to_vec();
        // Original modal concatenation: default roster, then each named mode.
        for mode in modes {
            kinds.extend(crate::lexer::mode_token_kinds(mode));
            custom.extend(mode.iter().cloned());
        }
        let mut by_variant = BTreeMap::new();
        crate::automata::codegen::visit_token_kind_projection(&kinds, &custom, |row| {
            by_variant.insert(row.variant, retain(row.kind));
        });
        // TerminalPattern is selected by source text in the original lexer.
        // A native Boolean terminal can therefore win over a later grammar
        // Fixed("true")/Fixed("false") declaration with the same text.
        let selected_terminals = input
            .terminals
            .iter()
            .map(|terminal| (terminal.text.clone(), terminal.kind.clone()))
            .collect();
        Self { by_variant, selected_terminals }
    }

    /// Retain the kind selected by the original lexer's terminal roster.
    /// The Core append site supplies the exact terminal text, not a guessed
    /// token family; the original token-kind writer supplies its observation.
    pub fn record_terminal(
        &self,
        core: &mut GrammarCoreV1,
        token: TokenId,
        terminal: &str,
    ) -> Result<(), String> {
        let kind = self
            .selected_terminals
            .get(terminal)
            .ok_or_else(|| format!("original lexer has no selected terminal {terminal:?}"))?;
        let variant = crate::automata::codegen::token_projection_variant(kind);
        let observation = self.by_variant.get(&variant).cloned().ok_or_else(|| {
            format!("original token-kind writer has no observation for selected {variant:?}")
        })?;
        self.record_observation(core, token, || Some(observation))
    }

    /// Called beside each existing TokenDefinition append, with its actual
    /// source kind. Core display names never participate in this association.
    pub fn record(
        &self,
        core: &mut GrammarCoreV1,
        token: TokenId,
        kind: &TokenKind,
    ) -> Result<(), String> {
        self.record_observation(core, token, || {
            self.by_variant
                .get(&crate::automata::codegen::token_projection_variant(kind))
                .cloned()
        })
    }

    /// The original declaration worker's selected builtin family, or its
    /// original Custom variant name. Never an execution TokenDefinition name.
    pub fn record_source_variant(
        &self,
        core: &mut GrammarCoreV1,
        token: TokenId,
        variant: &str,
    ) -> Result<(), String> {
        self.record_observation(core, token, || self.by_variant.get(variant).cloned())
    }

    fn record_observation(
        &self,
        core: &mut GrammarCoreV1,
        token: TokenId,
        observation: impl FnOnce() -> Option<O>,
    ) -> Result<(), String> {
        let rows = core.wpda_token_observations.get_or_insert_with(Vec::new);
        if rows.len() != token.0 as usize {
            return Err("token observations do not follow original append order".into());
        }
        rows.push(observation());
        Ok(())
    }
}

fn retain(kind: &TokenKind) -> O {
    match kind {
        TokenKind::Eof => O::Eof,
        TokenKind::Ident => O::Ident,
        TokenKind::Integer => O::Integer,
        TokenKind::IntegerLit(name) => O::IntegerLit(name.clone()),
        TokenKind::RationalLit(name) => O::RationalLit(name.clone()),
        TokenKind::FixedPointLit(name) => O::FixedPointLit(name.clone()),
        TokenKind::Float => O::Float,
        TokenKind::True | TokenKind::False => O::BooleanText,
        TokenKind::BooleanLit => O::BooleanLit,
        TokenKind::StringLit => O::StringLit,
        TokenKind::Fixed(text) => O::Fixed(text.clone()),
        TokenKind::Dollar => O::Dollar,
        TokenKind::DoubleDollar => O::DoubleDollar,
        TokenKind::Custom(name) => O::Custom(name.clone()),
        TokenKind::LexError(_) => unreachable!("projection rejects runtime lexical errors"),
    }
}
