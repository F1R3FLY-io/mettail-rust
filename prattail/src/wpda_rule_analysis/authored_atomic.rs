//! Owned atomic descriptors through the original shared classifier and helpers.
//!
//! No grammar normalization, source reconstruction, or literal evaluation takes
//! place here. Literal payloads remain the caller's existing opaque objects.
//! `AtomicClassifierProjection.v` and `UnaryPrefixReaderProjection.v` supply
//! observation/callback correspondence, not installed-parser admission.

use super::atomic::{classify_atomic, AtomicDescriptor, AtomicUnaryPrefix};
use super::atomic_projection::{project_legacy_atomic_items, LegacyAtomicObservation};
use super::authored::AuthoredRuleReader;
use super::infix_projection::{try_project_infix_rule_in, InfixProjectionError};
use mettail_ast::grammar_shapes::classify_unary_prefix_shape_in;
use mettail_grammar_core::{
    Associativity, AuthoredLegacyItem, AuthoredNameId, AuthoredRuleId, NonTerminalKind,
};

/// Admit the complete helper domain once, then use the original lazy callbacks.
///
/// The rule handle must belong to this validated reader. Admission prepays the
/// projection, original workers, callbacks, string copies and temporary storage;
/// a no-accounting callback is not a finite runtime resource policy. The existing
/// projection's explicit nonassociativity refusal is propagated: no flags are
/// invented or silently mapped. That profile restriction is not an assertion
/// that atomic classification itself depends on associativity.
///
/// The literal resolver receives the exact retained singleton Category name
/// handle, not a reconstructed identifier or authority inferred from spelling.
/// It runs only at the original classifier's literal site. Header access and
/// native eligibility, when needed, belong to that injected existing resolver.
pub fn derive_authored_atomic<'store, E, L>(
    reader: &AuthoredRuleReader<'store>,
    rule: AuthoredRuleId,
    associativity: Associativity,
    shares_level_with_previous: bool,
    admit: impl FnOnce(&AuthoredRuleReader<'store>, AuthoredRuleId) -> Result<(), E>,
    literal: impl FnOnce(AuthoredNameId) -> Option<L>,
) -> Result<AtomicDescriptor<L>, InfixProjectionError<E>> {
    let view =
        try_project_infix_rule_in(reader, rule, associativity, shares_level_with_previous, admit)?;
    let items = project_legacy_atomic_items(&reader.rule(rule).items, |item| match item {
        AuthoredLegacyItem::NonTerminal { kind, ident } => {
            LegacyAtomicObservation::NonTerminal { kind: *kind, ident: reader.name(*ident) }
        },
        AuthoredLegacyItem::Terminal(text) => LegacyAtomicObservation::Terminal(text),
        _ => LegacyAtomicObservation::Other,
    });
    Ok(classify_atomic(
        &view,
        &items,
        || {
            classify_unary_prefix_shape_in(reader, rule).map(|shape| AtomicUnaryPrefix {
                trigger: shape.trigger,
                operand_category: shape.operand_category,
            })
        },
        |_| {
            let [AuthoredLegacyItem::NonTerminal { ident, kind: NonTerminalKind::Category }] =
                reader.rule(rule).items.as_slice()
            else {
                unreachable!("shared atomic classifier only resolves singleton Category items");
            };
            literal(*ident)
        },
    ))
}
