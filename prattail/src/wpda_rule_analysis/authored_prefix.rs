//! Complete owned prefix buckets through the original shared FIRST/Ident driver.
//!
//! Raw source occurrences, normalized global occurrences and indexed synthetic
//! buckets retain their distinct roles. The synthesis argument is the unchanged
//! output of `derive_authored_rules` for this Core and explicit source roster;
//! representation checks below do not re-prove arbitrary supplied normalization.
//! No source text, syntax AST, normalizer, FIRST algorithm or evaluator is built.
//!
//! Admission prepays this complete finite helper domain before validation,
//! source staging, callbacks and owned copies. The caller supplies the production
//! finite policy; an infallible test policy is not a runtime resource bound.
//! Errors publish no partial bucket artifact. Physical allocator failure and
//! panic recovery remain outside this logical admission contract.

mod literal;
pub(super) mod reader;

use super::atomic::AtomicDescriptor;
use super::atomic_prefix::{atomic_arm_descriptors, PrefixArmDescriptor};
use super::authored::{AuthoredNameRef, AuthoredReaderError, AuthoredRuleReader};
use super::authored_atomic::{try_derive_authored_atomic, AuthoredAtomicError};
use super::authored_binder::{derive_authored_binder, AuthoredBinderError};
use super::authored_declarations::{AuthoredDeclarationReader, AuthoredDeclarationReaderError};
use super::authored_synthesis::{AuthoredRuleOrigin, AuthoredRulePayload, AuthoredSynthesisOutput};
use super::binder::BinderShape;
use super::infix_projection::{try_project_infix_rule_in, InfixProjectionError};
use super::native_first::{literal_patterned_pattern_and_guard_for_kind, EmissionContext};
use super::prefix::{FirstLegacyItem, FirstPredicate, TryFirstSetContext, TryIdentSummaryContext};
use super::prefix_bucket::{try_derive_prefix_buckets, PrefixBuckets, TryPrefixBucketContext};
use super::prefix_pattern::{
    neutral_predicate_parts, NeutralNativeFirstConstructors, NeutralPattern, NeutralPatternKey,
};
use crate::binding_power::{
    try_analyze_binding_powers, BindingPowerError, BindingPowerTable, InfixRuleInfo,
};
pub use literal::LiteralError;
use literal::OwnedLiteral;
use mettail_grammar_core::{
    Associativity, AuthoredLegacyItem, AuthoredNode, GrammarCoreV1, Precedence,
};
use reader::OccurrenceReader;
use std::convert::Infallible;
use std::marker::PhantomData;

#[derive(Debug)]
pub enum AuthoredPrefixError<E> {
    Admission(E),
    Declaration(AuthoredDeclarationReaderError),
    Reader(AuthoredReaderError),
    MissingSourceStore,
    SourceStoreMismatch,
    InvalidOccurrence(usize),
    MissingAuthoredRule(usize),
    InvalidRule,
    SourceRosterMismatch(usize),
    CategoryRosterMismatch,
    InvalidCategory(usize),
    CategoryIndexOverflow,
    RuleIndexOverflow(usize),
    MissingCategoryBinding(usize),
    MissingCollectionOpen(usize),
    PrefixBindingPowerOverflow(u16),
    Allocation,
    Projection(InfixProjectionError<Infallible>),
    Atomic(AuthoredAtomicError<Infallible, LiteralError>),
    Binder(AuthoredBinderError<Infallible>),
    Collection(super::authored_collection::AuthoredCollectionError<Infallible>),
    BindingPower(BindingPowerError<Infallible>),
}

/// Produce the actual ordered neutral bucket artifact consumed by WPDA planning.
///
/// The original source roster is explicit; absent authored handles are errors,
/// never a heuristic for filtering generated bridge productions. Repeated source
/// occurrences keep distinct roster ordinals, even when their handles are equal.
pub fn derive_authored_prefix_buckets<P, E>(
    core: &GrammarCoreV1,
    original_occurrences: &[usize],
    synthesis: &AuthoredSynthesisOutput<P>,
    category_src_idx: u16,
    crosscat_lex_compat_gate: bool,
    admit: impl FnOnce(&GrammarCoreV1, &[usize], &AuthoredSynthesisOutput<P>, u16) -> Result<(), E>,
) -> Result<PrefixBuckets<NeutralPattern, NeutralPatternKey>, AuthoredPrefixError<E>> {
    admit(core, original_occurrences, synthesis, category_src_idx)
        .map_err(AuthoredPrefixError::Admission)?;
    with_authored_context(core, original_occurrences, synthesis, |reader, context| {
        derive_category_prefix(
            reader,
            context,
            synthesis,
            category_src_idx,
            crosscat_lex_compat_gate,
        )
    })?
}

/// Borrow one validated occurrence context for complete descriptor assembly.
/// The caller admits the complete helper domain before entering this function;
/// its result cannot borrow the local original-occurrence roster.
pub(super) fn with_authored_context<'store, P, E, T>(
    core: &'store GrammarCoreV1,
    original_occurrences: &[usize],
    synthesis: &'store AuthoredSynthesisOutput<P>,
    consume: impl for<'reader> FnOnce(
        &OccurrenceReader<'reader, 'store>,
        &mut Context<'reader, 'store, E>,
    ) -> T,
) -> Result<T, AuthoredPrefixError<E>> {
    use AuthoredPrefixError as Error;
    let declarations = AuthoredDeclarationReader::new(core).map_err(Error::Declaration)?;
    let rules = AuthoredRuleReader::new(&synthesis.store).map_err(Error::Reader)?;
    let source_store = core.authored.as_ref().ok_or(Error::MissingSourceStore)?;
    if synthesis.store.len() < source_store.len()
        || synthesis.store.declarations() != source_store.declarations()
        || (0..source_store.len()).any(|index| {
            let index = u32::try_from(index).expect("validated source arena index");
            source_store.get(index) != synthesis.store.get(index)
        })
    {
        return Err(Error::SourceStoreMismatch);
    }
    if synthesis.categories.len() > usize::from(u16::MAX) + 1 {
        return Err(Error::CategoryIndexOverflow);
    }
    if synthesis.categories.len() != synthesis.per_category.len() {
        return Err(Error::CategoryRosterMismatch);
    }
    if synthesis.source_order.len() != original_occurrences.len() {
        return Err(Error::SourceRosterMismatch(original_occurrences.len()));
    }
    let mut originals = Vec::new();
    originals
        .try_reserve_exact(original_occurrences.len())
        .map_err(|_| Error::Allocation)?;
    for (roster_index, &production_index) in original_occurrences.iter().enumerate() {
        let production = core
            .productions
            .get(production_index)
            .ok_or(Error::InvalidOccurrence(production_index))?;
        let rule = production
            .authored
            .ok_or(Error::MissingAuthoredRule(production_index))?;
        let origin = AuthoredRuleOrigin::User { roster_index, production_index };
        if synthesis.source_order[roster_index].origin != origin {
            return Err(Error::SourceRosterMismatch(roster_index));
        }
        for rule in [rule, synthesis.source_order[roster_index].rule] {
            if !matches!(synthesis.store.get(rule.0), Some(AuthoredNode::Rule(_))) {
                return Err(Error::InvalidRule);
            }
        }
        originals.push(AuthoredRulePayload { rule, origin });
    }
    for (category_index, rows) in synthesis.per_category.iter().enumerate() {
        if rows.len() > usize::from(u16::MAX) + 1 {
            return Err(Error::RuleIndexOverflow(category_index));
        }
        for payload in rows {
            if !matches!(synthesis.store.get(payload.rule.0), Some(AuthoredNode::Rule(_))) {
                return Err(Error::InvalidRule);
            }
            if let AuthoredRuleOrigin::User { roster_index, .. } = payload.origin {
                if synthesis.source_order.get(roster_index) != Some(payload) {
                    return Err(Error::SourceRosterMismatch(roster_index));
                }
            }
            if rules.name(rules.rule(payload.rule).category).to_string()
                != synthesis.categories[category_index]
            {
                return Err(Error::CategoryRosterMismatch);
            }
        }
    }
    let reader = OccurrenceReader::new(&rules);
    let mut context = Context {
        core,
        declarations,
        rules: &rules,
        originals: &originals,
        normalized: &synthesis.source_order,
        expected_categories: &synthesis.categories,
        error: PhantomData,
    };
    Ok(consume(&reader, &mut context))
}

pub(super) fn derive_category_prefix<'reader, 'store, P, E>(
    reader: &OccurrenceReader<'reader, 'store>,
    context: &mut Context<'reader, 'store, E>,
    synthesis: &AuthoredSynthesisOutput<P>,
    category_src_idx: u16,
    crosscat_lex_compat_gate: bool,
) -> Result<PrefixBuckets<NeutralPattern, NeutralPatternKey>, AuthoredPrefixError<E>> {
    use AuthoredPrefixError as Error;
    let category_index = usize::from(category_src_idx);
    let category_name = synthesis
        .categories
        .get(category_index)
        .ok_or(Error::InvalidCategory(category_index))?;
    let rows = &synthesis.per_category[category_index];
    let mut indexed = Vec::new();
    indexed
        .try_reserve_exact(rows.len())
        .map_err(|_| Error::Allocation)?;
    for (index, &rule) in rows.iter().enumerate() {
        let index = u16::try_from(index).map_err(|_| Error::RuleIndexOverflow(category_index))?;
        indexed.push((index, rule));
    }
    try_derive_prefix_buckets(
        reader,
        context,
        category_src_idx,
        category_name,
        &indexed,
        crosscat_lex_compat_gate,
    )
}

pub(super) struct Context<'reader, 'store, E> {
    core: &'store GrammarCoreV1,
    declarations: AuthoredDeclarationReader<'store>,
    pub(super) rules: &'reader AuthoredRuleReader<'store>,
    pub(super) originals: &'reader [AuthoredRulePayload],
    pub(super) normalized: &'store [AuthoredRulePayload],
    expected_categories: &'store [String],
    error: PhantomData<E>,
}

impl<'store, E> Context<'_, 'store, E> {
    pub(super) fn infix_original(
        &self,
        rule: AuthoredRulePayload,
    ) -> Result<Option<InfixRuleInfo>, AuthoredPrefixError<E>> {
        let AuthoredRuleOrigin::User { roster_index, .. } = rule.origin else {
            return Err(AuthoredPrefixError::InvalidRule);
        };
        let normalized = *self
            .normalized
            .get(roster_index)
            .ok_or(AuthoredPrefixError::SourceRosterMismatch(roster_index))?;
        if normalized.origin != rule.origin {
            return Err(AuthoredPrefixError::SourceRosterMismatch(roster_index));
        }
        self.infix_normalized(normalized)
    }
    pub(super) fn atomic(
        &self,
        rule: AuthoredRulePayload,
    ) -> Result<AtomicDescriptor<OwnedLiteral<'store>>, AuthoredPrefixError<E>> {
        let precedence = self.precedence(rule)?;
        try_derive_authored_atomic(
            self.rules,
            rule.rule,
            precedence.associativity,
            precedence.shares_previous_level,
            |_, _| Ok::<_, Infallible>(()),
            |name| literal::resolve(self.rules, &self.declarations, name),
        )
        .map_err(AuthoredPrefixError::Atomic)
    }

    pub(super) fn binder_shape(
        &self,
        rule: AuthoredRulePayload,
    ) -> Result<Option<BinderShape>, AuthoredPrefixError<E>> {
        derive_authored_binder(self.rules, rule.rule, |_, _, _| Ok::<_, Infallible>(()))
            .map_err(AuthoredPrefixError::Binder)
    }

    pub(super) fn explicit_prefix_bp(
        &self,
        rule: AuthoredRulePayload,
    ) -> Result<Option<u8>, AuthoredPrefixError<E>> {
        self.precedence(rule)?
            .binding_power
            .map(|power| {
                u8::try_from(power)
                    .map_err(|_| AuthoredPrefixError::PrefixBindingPowerOverflow(power))
            })
            .transpose()
    }

    pub(super) fn precedence(
        &self,
        rule: AuthoredRulePayload,
    ) -> Result<Precedence, AuthoredPrefixError<E>> {
        match rule.origin {
            AuthoredRuleOrigin::User { production_index, .. } => self
                .core
                .productions
                .get(production_index)
                .map(|production| production.precedence)
                .ok_or(AuthoredPrefixError::InvalidOccurrence(production_index)),
            AuthoredRuleOrigin::Synthetic => Ok(Precedence {
                associativity: Associativity::Left,
                binding_power: None,
                shares_previous_level: false,
            }),
        }
    }
    pub(super) fn infix_normalized(
        &self,
        payload: AuthoredRulePayload,
    ) -> Result<Option<InfixRuleInfo>, AuthoredPrefixError<E>> {
        let precedence = self.precedence(payload)?;
        let shape = try_project_infix_rule_in(
            self.rules,
            payload.rule,
            precedence.associativity,
            precedence.shares_previous_level,
            |_, _| Ok::<_, Infallible>(()),
        )
        .map_err(AuthoredPrefixError::Projection)?;
        Ok(super::classify_rule(&shape))
    }
    fn legacy(
        &self,
        rule: AuthoredRulePayload,
        index: usize,
    ) -> Option<FirstLegacyItem<'store, AuthoredNameRef<'store>>> {
        self.rules
            .rule(rule.rule)
            .items
            .get(index)
            .map(|item| match item {
                AuthoredLegacyItem::Terminal(text) => FirstLegacyItem::Terminal(text),
                AuthoredLegacyItem::NonTerminal { kind, ident } => FirstLegacyItem::NonTerminal {
                    kind: *kind,
                    name: self.rules.name(*ident),
                },
                _ => FirstLegacyItem::Other,
            })
    }
}

impl<'reader, 'store, E> TryFirstSetContext<'store, OccurrenceReader<'reader, 'store>>
    for Context<'reader, 'store, E>
{
    type Error = AuthoredPrefixError<E>;
    type Category = usize;
    type Literal = OwnedLiteral<'store>;
    type Pattern = NeutralPattern;
    fn try_rules_len(&self) -> Result<usize, Self::Error> {
        Ok(self.originals.len())
    }
    fn try_rule_at(&self, index: usize) -> Result<AuthoredRulePayload, Self::Error> {
        self.originals
            .get(index)
            .copied()
            .ok_or(AuthoredPrefixError::InvalidOccurrence(index))
    }
    fn try_find_category(&mut self, name: &str) -> Result<Option<usize>, Self::Error> {
        Ok(self
            .declarations
            .header()
            .categories
            .iter()
            .position(|category| self.rules.name(category.name).to_string() == name))
    }
    fn try_is_data(&self, category: usize) -> Result<bool, Self::Error> {
        self.declarations
            .is_data(category)
            .ok_or(AuthoredPrefixError::MissingCategoryBinding(category))
    }
    fn try_collection_open(&self, category: usize) -> Result<Option<&'store str>, Self::Error> {
        self.declarations
            .header()
            .categories
            .get(category)
            .ok_or(AuthoredPrefixError::InvalidCategory(category))?
            .collection
            .as_ref()
            .map(|collection| {
                collection
                    .open
                    .as_deref()
                    .ok_or(AuthoredPrefixError::MissingCollectionOpen(category))
            })
            .transpose()
    }
    fn try_legacy_first(
        &self,
        rule: AuthoredRulePayload,
    ) -> Result<Option<FirstLegacyItem<'store, AuthoredNameRef<'store>>>, Self::Error> {
        Ok(self.legacy(rule, 0))
    }
    fn try_native_first(
        &mut self,
        category: usize,
        name: &str,
    ) -> Result<Vec<(NeutralPattern, Option<NeutralPattern>)>, Self::Error> {
        let declaration = self
            .declarations
            .header()
            .categories
            .get(category)
            .ok_or(AuthoredPrefixError::InvalidCategory(category))?;
        if let Some(kind) = declaration.native {
            if let Some(family) = self.declarations.literal_family(name) {
                return Ok(literal_patterned_pattern_and_guard_for_kind(
                    name,
                    family,
                    Some(&kind),
                    EmissionContext::FirstSet,
                    &mut NeutralNativeFirstConstructors,
                ));
            }
        }
        Ok(Vec::new())
    }
    fn try_atomic(
        &mut self,
        rule: AuthoredRulePayload,
    ) -> Result<AtomicDescriptor<Self::Literal>, Self::Error> {
        self.atomic(rule)
    }
    fn try_patterned_first(
        &mut self,
        literal: Self::Literal,
    ) -> Result<Vec<(NeutralPattern, Option<NeutralPattern>)>, Self::Error> {
        Ok(literal.rows(EmissionContext::FirstSet))
    }
    fn try_binder_leading(
        &mut self,
        rule: AuthoredRulePayload,
    ) -> Result<Option<String>, Self::Error> {
        Ok(derive_authored_binder(self.rules, rule.rule, |_, _, _| Ok::<_, Infallible>(()))
            .map_err(AuthoredPrefixError::Binder)?
            .and_then(|shape| shape.leading_category))
    }
    fn try_predicate_parts(
        &mut self,
        predicate: FirstPredicate<'_>,
    ) -> Result<(NeutralPattern, Option<NeutralPattern>), Self::Error> {
        Ok(neutral_predicate_parts(predicate))
    }
}
impl<'reader, 'store, E> TryIdentSummaryContext<'store, OccurrenceReader<'reader, 'store>>
    for Context<'reader, 'store, E>
{
    fn try_categories_len(&self) -> Result<usize, Self::Error> {
        Ok(self.declarations.header().categories.len())
    }
    fn try_category_at(&self, index: usize) -> Result<usize, Self::Error> {
        self.declarations
            .header()
            .categories
            .get(index)
            .map(|_| index)
            .ok_or(AuthoredPrefixError::InvalidCategory(index))
    }
    fn try_category_spelling(&self, category: usize) -> Result<String, Self::Error> {
        Ok(self
            .rules
            .name(
                self.declarations
                    .header()
                    .categories
                    .get(category)
                    .ok_or(AuthoredPrefixError::InvalidCategory(category))?
                    .name,
            )
            .to_string())
    }
    fn try_legacy_len(&self, rule: AuthoredRulePayload) -> Result<usize, Self::Error> {
        Ok(self.rules.rule(rule.rule).items.len())
    }
    fn try_legacy_at(
        &self,
        rule: AuthoredRulePayload,
        index: usize,
    ) -> Result<Option<FirstLegacyItem<'store, AuthoredNameRef<'store>>>, Self::Error> {
        Ok(self.legacy(rule, index))
    }
}
impl<'reader, 'store, E> TryPrefixBucketContext<'store, OccurrenceReader<'reader, 'store>>
    for Context<'reader, 'store, E>
{
    fn try_infix(
        &mut self,
        rule: AuthoredRulePayload,
    ) -> Result<Option<InfixRuleInfo>, Self::Error> {
        self.infix_original(rule)
    }
    fn try_category_names(&mut self) -> Result<Vec<String>, Self::Error> {
        let rules: Vec<_> = self.originals.iter().map(|payload| payload.rule).collect();
        let categories = self
            .declarations
            .collect_category_names(&rules)
            .map_err(AuthoredPrefixError::Declaration)?;
        // This is the driver's original census callback, not a second preflight.
        // Empty category buckets also contribute positional identity.
        if categories.as_slice() != self.expected_categories {
            return Err(AuthoredPrefixError::CategoryRosterMismatch);
        }
        Ok(categories)
    }
    fn try_binding_power_table(&mut self) -> Result<BindingPowerTable, Self::Error> {
        let mut infix = Vec::new();
        for &payload in self.normalized {
            if let Some(info) = self.infix_normalized(payload)? {
                infix.push(info);
            }
        }
        try_analyze_binding_powers(&infix, |_| Ok::<_, Infallible>(()))
            .map_err(AuthoredPrefixError::BindingPower)
    }
    fn try_explicit_prefix_bp(&self, rule: AuthoredRulePayload) -> Result<Option<u8>, Self::Error> {
        self.explicit_prefix_bp(rule)
    }
    fn try_binder_shape(
        &mut self,
        rule: AuthoredRulePayload,
    ) -> Result<Option<BinderShape>, Self::Error> {
        self.binder_shape(rule)
    }
    fn try_atomic_rows(
        &mut self,
        category_src_idx: u16,
        rule_idx: u16,
        shape: &AtomicDescriptor<Self::Literal>,
    ) -> Result<Vec<PrefixArmDescriptor<NeutralPattern>>, Self::Error> {
        Ok(atomic_arm_descriptors(
            category_src_idx,
            rule_idx,
            shape,
            neutral_predicate_parts,
            |literal, mode| literal.rows(mode),
        ))
    }
    fn try_nested_guest_openers(&mut self, open: &str) -> Result<Vec<String>, Self::Error> {
        Ok(self.declarations.guest_nested_open_kinds(open))
    }
}
