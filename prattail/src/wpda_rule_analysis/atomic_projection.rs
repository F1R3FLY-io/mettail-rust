//! Original legacy-item projection shared by macro and owned atomic inputs.
//!
//! Every position is retained, including unsupported items. The stored kind is
//! copied as a discriminator; it is never inferred again from a name. The
//! caller admits the complete observation/copy domain before invoking this
//! helper. `AtomicClassifierProjection.v` proves this exact list projection.

use super::atomic::{LegacyAtomicItem, LegacyAtomicKind};
use mettail_grammar_core::NonTerminalKind;

pub enum LegacyAtomicObservation<'source, N> {
    NonTerminal { kind: NonTerminalKind, ident: N },
    Terminal(&'source str),
    Other,
}

/// The original ordered map; shallow observers borrow source-specific payloads.
pub fn project_legacy_atomic_items<'source, I, N: ToString>(
    items: &'source [I],
    mut observe: impl FnMut(&'source I) -> LegacyAtomicObservation<'source, N>,
) -> Vec<LegacyAtomicItem> {
    items
        .iter()
        .map(|item| match observe(item) {
            LegacyAtomicObservation::NonTerminal { kind, ident } => LegacyAtomicItem::NonTerminal {
                kind: match kind {
                    NonTerminalKind::Integer => LegacyAtomicKind::Integer,
                    NonTerminalKind::Boolean => LegacyAtomicKind::Boolean,
                    NonTerminalKind::StringLiteral => LegacyAtomicKind::StringLiteral,
                    NonTerminalKind::FloatLiteral => LegacyAtomicKind::FloatLiteral,
                    NonTerminalKind::Var => LegacyAtomicKind::Var,
                    NonTerminalKind::Ident => LegacyAtomicKind::Ident,
                    NonTerminalKind::Category => LegacyAtomicKind::Category,
                },
                ident: ident.to_string(),
            },
            LegacyAtomicObservation::Terminal(text) => LegacyAtomicItem::Terminal(text.to_owned()),
            LegacyAtomicObservation::Other => LegacyAtomicItem::Other,
        })
        .collect()
}
