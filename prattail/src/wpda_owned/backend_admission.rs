//! Capacity admission for the existing owned derivation workers.
//!
//! Slots and flat encoded payload bytes are logical policy quantities, not
//! CPU instructions or physical RSS. The same balances span all preparation
//! stages. Counting flat authored data never constructs a source string,
//! serialized buffer, execution trace, or replacement grammar.

use crate::wpda_rule_analysis::{
    authored_descriptors::OwnedWpdaDescriptors,
    authored_normalization::AuthoredNormalizationEvent,
    authored_synthesis::{
        AuthoredRulePayload, AuthoredSourceOccurrence, AuthoredSynthesisEvent,
        AuthoredSynthesisOutput,
    },
    synthetic::SynthesisEvent,
};
use mettail_ast::legacy_rule_normalization::LegacyNormalizationEvent;
use mettail_grammar_core::{
    term_param_walk::{BinderPresenceEvent, TermParamWalkEvent},
    AuthoredLegacyItem, AuthoredNode, AuthoredOperation, AuthoredRuleStore, AuthoredSyntax,
    CollectionKind, GrammarCoreV1, ParserImageAdmissionLimits, RuntimeError,
};
use serde::Serialize;

fn exhausted() -> RuntimeError {
    RuntimeError::Image("shared WPDA preparation capacity exhausted".into())
}

pub(super) struct PreparationBudget {
    slots: usize,
    bytes: usize,
}

/// Checked, bounded adaptation of postcard's existing counting flavor.
struct CheckedSize {
    remaining: usize,
    used: usize,
}

impl postcard::ser_flavors::Flavor for CheckedSize {
    type Output = usize;

    fn try_push(&mut self, _byte: u8) -> postcard::Result<()> {
        self.try_extend(&[0])
    }

    fn try_extend(&mut self, bytes: &[u8]) -> postcard::Result<()> {
        self.remaining = self
            .remaining
            .checked_sub(bytes.len())
            .ok_or(postcard::Error::SerializeBufferFull)?;
        self.used = self
            .used
            .checked_add(bytes.len())
            .ok_or(postcard::Error::SerializeBufferFull)?;
        Ok(())
    }

    fn finalize(self) -> postcard::Result<usize> {
        Ok(self.used)
    }
}

impl PreparationBudget {
    pub(super) fn new(limits: ParserImageAdmissionLimits) -> Self {
        Self {
            slots: limits.max_runtime_symbols,
            bytes: limits.max_encoded_bytes,
        }
    }

    fn slots(&mut self, count: usize) -> Result<(), RuntimeError> {
        self.slots = self.slots.checked_sub(count).ok_or_else(exhausted)?;
        Ok(())
    }

    fn bytes(&mut self, count: usize) -> Result<(), RuntimeError> {
        self.bytes = self.bytes.checked_sub(count).ok_or_else(exhausted)?;
        Ok(())
    }

    /// Called only with flat arena/header/shallow-node values, never recursive
    /// Core SyntaxItem or DynamicValue. It preserves the original serializer.
    fn flat<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<usize, RuntimeError> {
        let used = postcard::serialize_with_flavor::<T, CheckedSize, usize>(
            value,
            CheckedSize { remaining: self.bytes, used: 0 },
        )
        .map_err(|_| exhausted())?;
        self.bytes(used)?;
        Ok(used)
    }

    fn store(&mut self, store: &AuthoredRuleStore) -> Result<usize, RuntimeError> {
        self.slots(flat_slots(store)?)?;
        self.flat(store)
    }

    pub(super) fn occurrences(&mut self, count: usize) -> Result<(), RuntimeError> {
        self.slots(count)
    }

    pub(super) fn contextual_keywords(
        &mut self,
        keywords: &std::collections::BTreeSet<String>,
    ) -> Result<(), RuntimeError> {
        self.slots(keywords.len())?;
        for keyword in keywords {
            self.bytes(keyword.len())?;
        }
        Ok(())
    }

    fn source(&mut self, core: &GrammarCoreV1) -> Result<usize, RuntimeError> {
        self.slots(core.categories.len())?;
        self.slots(core.tokens.len())?;
        self.slots(core.modes.len())?;
        self.slots(core.productions.len())?;
        self.store(
            core.authored.as_ref().ok_or_else(|| {
                RuntimeError::Image("original authored store is unavailable".into())
            })?,
        )
    }

    pub(super) fn event(&mut self, event: AuthoredSynthesisEvent<'_>) -> Result<(), RuntimeError> {
        use AuthoredSynthesisEvent as E;
        self.slots(1)?;
        match event {
            E::ValidateSource(core) => {
                self.source(core)?;
            },
            E::StoreCopy(store) => {
                self.store(store)?;
            },
            E::OriginalRosterSlots(n)
            | E::SourceReceiptSlots(n)
            | E::SourceOrderSlots(n)
            | E::UserInputSlots(n)
            | E::TypeIndexSlots(n)
            | E::TypeInputSlots(n)
            | E::SourceOrderOutputSlots(n) => self.slots(n)?,
            E::StringCopy(text) | E::VarLabel(text) => self.bytes(text.len())?,
            E::CategoryCensus { source, rules } => {
                // Original five passes plus the category/global-token scan.
                // Rule occurrences are charged separately: duplicate receipts
                // still clone the rule category and its set-insertion copy.
                let bytes = self.source(source)?;
                let tokens = source
                    .authored
                    .as_ref()
                    .and_then(|s| s.declarations())
                    .ok_or_else(exhausted)?
                    .global_tokens
                    .len();
                let passes = tokens.checked_add(4).ok_or_else(exhausted)?;
                self.bytes(bytes.checked_mul(passes).ok_or_else(exhausted)?)?;
                let store = source.authored.as_ref().ok_or_else(exhausted)?;
                for rule in rules {
                    let Some(AuthoredNode::Rule(rule)) = store.get(rule.0) else {
                        return Err(exhausted());
                    };
                    let Some(AuthoredNode::Name(category)) = store.get(rule.category.0) else {
                        return Err(exhausted());
                    };
                    self.bytes(
                        category
                            .spelling
                            .len()
                            .checked_mul(2)
                            .ok_or_else(exhausted)?,
                    )?;
                }
                self.slots(rules.len())?;
                self.slots(
                    source
                        .categories
                        .len()
                        .checked_mul(tokens)
                        .ok_or_else(exhausted)?,
                )?;
            },
            E::CollectionLookup { source, rules } => {
                let bytes = self.source(source)?;
                self.bytes(bytes.checked_mul(rules.len()).ok_or_else(exhausted)?)?;
                self.slots(rules.len())?;
            },
            E::NativeObservation(observation) => {
                self.flat(observation)?;
            },
            E::Normalization(event) => self.normalization(event)?,
            E::Binder(BinderPresenceEvent::Parameter(TermParamWalkEvent::ReserveFrames(n))) => {
                self.slots(n)?
            },
            E::Synthesis(event) => self.synthesis(event)?,
            E::CollectionDefaults(_) => {
                // Prepay the original helper's temporary strings, separately
                // from later copies into a recipe. Four strings and eleven
                // bytes cover every current collection kind (PathMap is the
                // largest); the original helper still chooses the delimiters.
                self.slots(4)?;
                self.bytes(11)?;
            },
            E::OriginalOccurrence(_)
            | E::TypeObservation(_)
            | E::NativeProbe { .. }
            | E::LiteralToken(_)
            | E::CheckCategoryIndex(_)
            | E::CheckRuleIndex { .. }
            | E::SourceOrderCheck(_)
            | E::SourceOrderWrite(_)
            | E::SourceOrderRead(_)
            | E::Binder(_) => {},
        }
        Ok(())
    }

    fn normalization(&mut self, event: AuthoredNormalizationEvent<'_>) -> Result<(), RuntimeError> {
        use AuthoredNormalizationEvent as E;
        match event {
            E::NameLookup(text) | E::NameIndexEntry(text) => self.bytes(text.len())?,
            E::Append(node) => {
                self.slots(1)?;
                self.flat(node)?;
            },
            E::LegacyItem(item) => {
                self.flat(item)?;
            },
            E::ParamSlots(n) | E::SyntaxSlots(n) | E::LegacyItems(n) => self.slots(n)?,
            E::Legacy(event) => match event {
                LegacyNormalizationEvent::Literal(text) => self.bytes(text.len())?,
                LegacyNormalizationEvent::Param(text) => self.bytes(text.len())?,
                LegacyNormalizationEvent::Sep { name, separator } => {
                    self.bytes(name.len())?;
                    self.bytes(separator.len())?;
                },
                LegacyNormalizationEvent::Simple { name, .. }
                | LegacyNormalizationEvent::Collection { name, .. } => self.bytes(name.len())?,
                LegacyNormalizationEvent::Abstraction { binder, body, .. } => {
                    self.bytes(binder.len())?;
                    self.bytes(body.len())?;
                },
                // Original indexed fresh names are bounded by usize's decimal
                // digits and fixed spelling; no name is constructed here.
                LegacyNormalizationEvent::FreshName(_) | LegacyNormalizationEvent::ElemsName => {
                    self.bytes(32)?
                },
                LegacyNormalizationEvent::PreflightItem(_)
                | LegacyNormalizationEvent::BuildItem(_)
                | LegacyNormalizationEvent::PendingBinder(_) => {},
            },
            E::OriginalRule(_) | E::NameNode(_) => {},
        }
        Ok(())
    }

    fn synthesis(
        &mut self,
        event: SynthesisEvent<
            '_,
            AuthoredSourceOccurrence,
            usize,
            AuthoredRulePayload,
            CollectionKind,
        >,
    ) -> Result<(), RuntimeError> {
        use SynthesisEvent as E;
        match event {
            E::CategoryIndexSlots(n) | E::BucketSlots(n) | E::BinderNameSlots(n) => {
                self.slots(n)?
            },
            E::CategoryIndexEntry { name, .. }
            | E::CategoryLookup(name)
            | E::StringCopy(name)
            | E::TrimOpen(name) => self.bytes(name.len())?,
            E::Lowercase(text) => {
                self.bytes(text.len())?;
                // Observe the original Unicode worker without allocating an
                // output string or replacing its transformation.
                let bytes = text
                    .chars()
                    .flat_map(char::to_lowercase)
                    .try_fold(0usize, |sum, ch| {
                        sum.checked_add(ch.len_utf8()).ok_or_else(exhausted)
                    })?;
                self.bytes(bytes)?;
            },
            E::Format { prefix, body, suffix } => {
                self.bytes(prefix.len())?;
                self.bytes(body.len())?;
                self.bytes(suffix.len())?;
            },
            E::RecipeSlots { items, params, syntax } => {
                self.slots(items)?;
                self.slots(params)?;
                self.slots(syntax)?;
            },
            E::Visit(_) | E::RowSlot(_) | E::VectorKindClone(_) | E::Callback(_) => {},
        }
        Ok(())
    }

    /// Admit finite output relation/copy domains before the original helpers.
    /// This is a capacity tariff, not a claim about their instruction count.
    /// Categories x categories bounds reachability/grouping; category x arena
    /// bounds FIRST/prefix observations; rule x arena bounds per-rule metadata.
    pub(super) fn descriptors<P>(
        &mut self,
        synthesis: &AuthoredSynthesisOutput<P>,
    ) -> Result<(), RuntimeError> {
        let categories = synthesis.categories.len();
        let rules = synthesis
            .per_category
            .iter()
            .try_fold(0usize, |n, rows| n.checked_add(rows.len()).ok_or_else(exhausted))?;
        let arena = synthesis.store.len();
        let domain = flat_slots(&synthesis.store)?;
        let mut rows = categories.checked_mul(categories).ok_or_else(exhausted)?;
        rows = rows
            .checked_add(categories.checked_mul(domain).ok_or_else(exhausted)?)
            .ok_or_else(exhausted)?;
        rows = rows
            .checked_add(rules.checked_mul(domain).ok_or_else(exhausted)?)
            .ok_or_else(exhausted)?;
        self.slots(rows)?;
        self.store(&synthesis.store)?;
        // Each charged string slot copies a member of the original spelling
        // vocabulary, not the complete arena. Count the largest such payload
        // without allocating a second string or following arena references.
        let mut longest = 0usize;
        let mut observe = |text: &str| longest = longest.max(text.len());
        for index in 0..arena {
            match synthesis
                .store
                .get(u32::try_from(index).map_err(|_| exhausted())?)
            {
                Some(AuthoredNode::Name(name)) => observe(&name.spelling),
                Some(AuthoredNode::Syntax(items)) => {
                    for item in items {
                        if let AuthoredSyntax::Literal(text) = item {
                            observe(text);
                        }
                    }
                },
                Some(AuthoredNode::Operation(AuthoredOperation::Sep { separator, .. })) => {
                    observe(separator)
                },
                Some(AuthoredNode::Rule(rule)) => {
                    for item in &rule.items {
                        match item {
                            AuthoredLegacyItem::Terminal(text) => observe(text),
                            AuthoredLegacyItem::Collection { separator, open, close, .. } => {
                                observe(separator);
                                if let Some(text) = open {
                                    observe(text);
                                }
                                if let Some(text) = close {
                                    observe(text);
                                }
                            },
                            _ => {},
                        }
                    }
                },
                _ => {},
            }
        }
        self.bytes(longest.checked_mul(rows).ok_or_else(exhausted)?)?;
        Ok(())
    }

    pub(super) fn actions_and_routing<P>(
        &mut self,
        descriptors: &OwnedWpdaDescriptors<P>,
    ) -> Result<(), RuntimeError> {
        self.descriptors(&descriptors.synthesis)
    }
}

/// Count actual shallow vector entries and immediate arena references. A Rule
/// or Syntax node may contain arbitrarily many entries; arena length alone is
/// not their allocation domain. No reference is recursively followed here.
fn flat_slots(store: &AuthoredRuleStore) -> Result<usize, RuntimeError> {
    let mut total = store.len();
    for index in 0..store.len() {
        let node = store
            .get(u32::try_from(index).map_err(|_| exhausted())?)
            .ok_or_else(exhausted)?;
        let entries = match node {
            AuthoredNode::Names(items) => items.len(),
            AuthoredNode::Params(items) => items.len(),
            AuthoredNode::Syntax(items) => items.len(),
            AuthoredNode::Rule(rule) => rule.items.len(),
            _ => 0,
        };
        total = total.checked_add(entries).ok_or_else(exhausted)?;
        node.try_for_each_reference(|_, _| {
            total = total.checked_add(1).ok_or_else(exhausted)?;
            Ok::<_, RuntimeError>(())
        })?;
    }
    if let Some(header) = store.declarations() {
        for count in [
            header.categories.len(),
            header.tokens.len(),
            header.global_tokens.len(),
            header.modes.len(),
        ] {
            total = total.checked_add(count).ok_or_else(exhausted)?;
        }
        for mode in &header.modes {
            total = total.checked_add(mode.tokens.len()).ok_or_else(exhausted)?;
        }
        header.try_for_each_name(|_| {
            total = total.checked_add(1).ok_or_else(exhausted)?;
            Ok::<_, RuntimeError>(())
        })?;
    }
    Ok(total)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_grammar_core::{
        AuthoredDeclarations, AuthoredName, AuthoredNameId, AuthoredRule, AuthoredRuleId,
        SourceObservation,
    };

    #[test]
    fn collection_defaults_are_paid_before_later_recipe_copies() {
        for kind in [
            CollectionKind::List,
            CollectionKind::Bag,
            CollectionKind::Map,
            CollectionKind::Set,
            CollectionKind::PathMap,
        ] {
            let mut budget = PreparationBudget { slots: 5, bytes: 11 };
            budget
                .event(AuthoredSynthesisEvent::CollectionDefaults(kind))
                .expect("complete default allocation tariff");
            assert_eq!((budget.slots, budget.bytes), (0, 0));
            assert!(budget
                .event(AuthoredSynthesisEvent::StringCopy("later"))
                .is_err());
            let mut short = PreparationBudget { slots: 5, bytes: 10 };
            assert!(short
                .event(AuthoredSynthesisEvent::CollectionDefaults(kind))
                .is_err());
        }
    }

    #[test]
    fn contextual_keywords_pay_exact_utf8_payload_and_vector_slots() {
        let words = ["a".to_owned(), "λ".to_owned()].into_iter().collect();
        let mut exact = PreparationBudget { slots: 2, bytes: 3 };
        exact
            .contextual_keywords(&words)
            .expect("exact keyword tariff");
        assert_eq!((exact.slots, exact.bytes), (0, 0));
        for (slots, bytes) in [(1, 3), (2, 2)] {
            assert!(PreparationBudget { slots, bytes }
                .contextual_keywords(&words)
                .is_err());
        }
    }

    #[test]
    fn inner_syntax_slots_are_not_replaced_by_outer_arena_length() {
        let mut store = AuthoredRuleStore::new();
        store
            .try_push(AuthoredNode::Syntax(vec![AuthoredSyntax::Literal("x".into()); 5]))
            .expect("flat syntax fixture");
        assert_eq!(store.len(), 1);
        assert_eq!(flat_slots(&store).expect("shallow slots"), 6);
        assert!(PreparationBudget { slots: 5, bytes: 4096 }
            .store(&store)
            .is_err());
        let mut exact = PreparationBudget { slots: 6, bytes: 4096 };
        exact.store(&store).expect("all six shallow slots paid");
        assert_eq!(exact.slots, 0);
    }

    #[test]
    fn census_charges_repeated_rule_category_copies_independently() {
        let mut store = AuthoredRuleStore::new();
        let name = AuthoredNameId(
            store
                .try_push(AuthoredNode::Name(AuthoredName {
                    spelling: "Expr".into(),
                    equality_class: 0,
                }))
                .expect("name"),
        );
        let rule = AuthoredRuleId(
            store
                .try_push(AuthoredNode::Rule(AuthoredRule {
                    label: name,
                    category: name,
                    source_body_present: SourceObservation::Known(false),
                    explicit_fold: SourceObservation::Known(false),
                    term_context: None,
                    syntax_pattern: None,
                    items: vec![],
                }))
                .expect("rule"),
        );
        let store = store
            .with_declarations(AuthoredDeclarations {
                categories: vec![],
                tokens: vec![],
                global_tokens: vec![],
                modes: vec![],
            })
            .expect("empty declaration header");
        let mut core = GrammarCoreV1::new("census-admission");
        core.authored = Some(store);
        let mut once = PreparationBudget { slots: 4096, bytes: 4096 };
        let mut twice = PreparationBudget { slots: 4096, bytes: 4096 };
        once.event(AuthoredSynthesisEvent::CategoryCensus { source: &core, rules: &[rule] })
            .expect("one receipt occurrence");
        twice
            .event(AuthoredSynthesisEvent::CategoryCensus { source: &core, rules: &[rule, rule] })
            .expect("two receipt occurrences");
        assert_eq!(once.bytes - twice.bytes, 2 * "Expr".len());
        assert_eq!(once.slots - twice.slots, 1);
    }
}
