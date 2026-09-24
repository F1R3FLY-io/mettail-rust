//! Owned inputs to the original synthetic-rule derivation, not another grammar
//! normalizer or parser. The caller supplies the exact original production
//! occurrence roster; auxiliary bridge productions are not inferred from flags
//! or missing authored handles. One source store copy feeds one consuming
//! normalization/materialization session and one caller-owned admission policy.
//!
//! `AuthoredSynthesisComposition.v` composes original occurrence provenance,
//! immutable source metadata, append-only materialization, and success-only
//! publication with the existing synthesis worker. Helper-specific models cover
//! the original label, collection, binder, and category-census observations.
//! This adapter does not establish native decoder parity or parser cutover.

use super::authored::AuthoredRuleReader;
use super::authored_declarations::{AuthoredDeclarationReader, AuthoredDeclarationReaderError};
use super::authored_normalization::{
    AuthoredNormalizationError, AuthoredNormalizationEvent, AuthoredNormalizationSession,
};
use super::synthetic::{
    try_build_per_category_rules, CollectionRecipe, SynthesisError, SynthesisEvent,
    SynthesisEventFor, SyntheticRule, TrySynthesisAdapter, TypeInput, UserInput,
};
use mettail_grammar_core::collection_declaration::{self, CollectionElementReader};
use mettail_grammar_core::constructor_labels::{
    generate_var_label, try_generate_literal_label_observed,
};
use mettail_grammar_core::term_param_walk::{
    try_declares_binder, BinderPresenceError, BinderPresenceEvent, BinderPresenceReader,
};
use mettail_grammar_core::{
    AuthoredCategoryDeclaration, AuthoredLegacyItem, AuthoredNameId, AuthoredNode, AuthoredParamId,
    AuthoredParamsId, AuthoredRuleId, AuthoredRuleStore, CollectionKind, GrammarCoreV1,
    NonTerminalKind, SourceObservation,
};
use std::cell::RefCell;

/// Source occurrence identity is independent of both the current arena handle
/// and the eventual category-local WPDA rule index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AuthoredRuleOrigin {
    User { production_index: usize },
    Synthetic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthoredRulePayload {
    pub rule: AuthoredRuleId,
    pub origin: AuthoredRuleOrigin,
}

pub struct AuthoredSynthesisOutput<P> {
    pub store: AuthoredRuleStore,
    pub categories: Vec<String>,
    pub per_category: Vec<Vec<AuthoredRulePayload>>,
    pub policy: P,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeProbe {
    ByteVector,
    Literal,
    CollectionElement,
}

/// Admission descriptions are borrowed at actual call sites. Whole-helper
/// events explicitly require prepayment of the supplied source domain, including
/// its string copies and temporary storage. They are not constant-cost tokens.
/// A production caller must provide a finite policy; GrammarLimits is not a
/// compilation-work budget. Static/test callers may use an infallible policy.
/// These events describe logical work/storage, not physical RSS or every Rust
/// allocation failure. No allocated execution trace is constructed here.
pub enum AuthoredSynthesisEvent<'a> {
    ValidateSource(&'a GrammarCoreV1),
    OriginalRosterSlots(usize),
    OriginalOccurrence(usize),
    CategoryCensus {
        source: &'a GrammarCoreV1,
        rules: &'a [AuthoredRuleId],
    },
    UserInputSlots(usize),
    TypeIndexSlots(usize),
    TypeInputSlots(usize),
    TypeObservation(usize),
    StringCopy(&'a str),
    StoreCopy(&'a AuthoredRuleStore),
    NativeProbe {
        category: usize,
        probe: NativeProbe,
    },
    NativeObservation(&'a mettail_grammar_core::LiteralNativeObservation),
    LiteralToken(u32),
    CollectionDefaults(CollectionKind),
    CollectionLookup {
        source: &'a GrammarCoreV1,
        rules: &'a [AuthoredRuleId],
    },
    VarLabel(&'a str),
    CheckCategoryIndex(usize),
    CheckRuleIndex {
        category: usize,
        count: usize,
    },
    Synthesis(SynthesisEvent<'a, usize, usize, AuthoredRulePayload, CollectionKind>),
    Normalization(AuthoredNormalizationEvent<'a>),
    Binder(BinderPresenceEvent<AuthoredRuleId, AuthoredParamId, AuthoredParamsId>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthoredSynthesisError<E> {
    Admission(E),
    Declaration(AuthoredDeclarationReaderError),
    InvalidOccurrence(usize),
    MissingAuthoredRule(usize),
    InvalidAuthoredRule { occurrence: usize, rule: AuthoredRuleId },
    MissingCategoryBinding(usize),
    UnavailableObservation { category: usize, probe: NativeProbe },
    AbsentNativeObservation(usize),
    Normalization(AuthoredNormalizationError<E>),
    Binder(BinderPresenceError<E>),
    CategoryIndexOverflow,
    RuleIndexOverflow(usize),
    Allocation,
}

type Outcome<T, E> = Result<T, AuthoredSynthesisError<E>>;

fn admit<P, E>(policy: &mut P, event: AuthoredSynthesisEvent<'_>) -> Outcome<(), E>
where
    P: FnMut(AuthoredSynthesisEvent<'_>) -> Result<(), E>,
{
    policy(event).map_err(AuthoredSynthesisError::Admission)
}

fn copy<P, E>(policy: &mut P, text: &str) -> Outcome<String, E>
where
    P: FnMut(AuthoredSynthesisEvent<'_>) -> Result<(), E>,
{
    admit(policy, AuthoredSynthesisEvent::StringCopy(text))?;
    let mut result = String::new();
    result
        .try_reserve_exact(text.len())
        .map_err(|_| AuthoredSynthesisError::Allocation)?;
    result.push_str(text);
    Ok(result)
}

fn reserve<T, E>(count: usize) -> Outcome<Vec<T>, E> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| AuthoredSynthesisError::Allocation)?;
    Ok(values)
}

/// Derive category buckets through the same worker used by macro generation.
///
/// `original_occurrences` is an ordered source receipt supplied by the caller,
/// not a selection heuristic. Duplicates and an empty roster are valid. Every
/// selected occurrence must exist and name an original authored Rule. Failure
/// returns neither a partially appended store nor partial buckets or the owner.
pub fn derive_authored_rules<P, E>(
    core: &GrammarCoreV1,
    original_occurrences: &[usize],
    mut policy: P,
) -> Outcome<AuthoredSynthesisOutput<P>, E>
where
    P: for<'event> FnMut(AuthoredSynthesisEvent<'event>) -> Result<(), E>,
{
    use AuthoredSynthesisError as Error;
    use AuthoredSynthesisEvent as Event;
    admit(&mut policy, Event::ValidateSource(core))?;
    let mut reader = AuthoredDeclarationReader::new(core).map_err(Error::Declaration)?;
    let store = core
        .authored
        .as_ref()
        .expect("declaration reader checked source store");
    admit(&mut policy, Event::OriginalRosterSlots(original_occurrences.len()))?;
    let mut original_rules = reserve(original_occurrences.len())?;
    for &occurrence in original_occurrences {
        admit(&mut policy, Event::OriginalOccurrence(occurrence))?;
        let production = core
            .productions
            .get(occurrence)
            .ok_or(Error::InvalidOccurrence(occurrence))?;
        let rule = production
            .authored
            .ok_or(Error::MissingAuthoredRule(occurrence))?;
        if !matches!(store.get(rule.0), Some(AuthoredNode::Rule(_))) {
            return Err(Error::InvalidAuthoredRule { occurrence, rule });
        }
        original_rules.push(rule);
    }
    admit(&mut policy, Event::CategoryCensus { source: core, rules: &original_rules })?;
    let categories = reader
        .collect_category_names(&original_rules)
        .map_err(Error::Declaration)?;
    admit(&mut policy, Event::CheckCategoryIndex(categories.len()))?;
    if categories.len() > usize::from(u16::MAX) + 1 {
        return Err(Error::CategoryIndexOverflow);
    }
    admit(&mut policy, Event::UserInputSlots(original_occurrences.len()))?;
    let mut users = reserve(original_occurrences.len())?;
    for (occurrence, rule) in original_occurrences.iter().zip(&original_rules) {
        let category = reader.rule_reader().rule(*rule).category;
        users.push(UserInput {
            category: copy(&mut policy, &reader.rule_reader().name(category).payload().spelling)?,
            source: occurrence,
        });
    }
    let header = reader.header();
    admit(&mut policy, Event::TypeIndexSlots(header.categories.len()))?;
    let mut type_indices = reserve(header.categories.len())?;
    type_indices.extend(0..header.categories.len());
    admit(&mut policy, Event::TypeInputSlots(header.categories.len()))?;
    let mut types = reserve(header.categories.len())?;
    for index in &type_indices {
        admit(&mut policy, Event::TypeObservation(*index))?;
        let category = &header.categories[*index];
        types.push(TypeInput {
            name: copy(&mut policy, &reader.rule_reader().name(category.name).payload().spelling)?,
            is_data: reader
                .is_data(*index)
                .ok_or(Error::MissingCategoryBinding(*index))?,
            has_native: category.native.is_some(),
            has_collection: category.collection.is_some(),
            source: index,
        });
    }
    admit(&mut policy, Event::StoreCopy(store))?;
    let adapter = OwnedSynthesisAdapter {
        source: core,
        reader,
        original_rules: &original_rules,
        session: AuthoredNormalizationSession::new(store.clone()),
        policy,
    };
    let (mut adapter, per_category) =
        try_build_per_category_rules(&categories, &users, &types, CollectionKind::List, adapter)
            .map_err(|error| match error {
                SynthesisError::Admission(error) | SynthesisError::Callback(error) => error,
                SynthesisError::Allocation => Error::Allocation,
            })?;
    for (category, row) in per_category.iter().enumerate() {
        admit(&mut adapter.policy, Event::CheckRuleIndex { category, count: row.len() })?;
        if row.len() > usize::from(u16::MAX) + 1 {
            return Err(Error::RuleIndexOverflow(category));
        }
    }
    Ok(AuthoredSynthesisOutput {
        store: adapter.session.into_store(),
        categories,
        per_category,
        policy: adapter.policy,
    })
}

struct OwnedSynthesisAdapter<'core, 'rules, P> {
    source: &'core GrammarCoreV1,
    reader: AuthoredDeclarationReader<'core>,
    original_rules: &'rules [AuthoredRuleId],
    session: AuthoredNormalizationSession,
    policy: P,
}

impl<P, E> TrySynthesisAdapter for OwnedSynthesisAdapter<'_, '_, P>
where
    P: for<'event> FnMut(AuthoredSynthesisEvent<'event>) -> Result<(), E>,
{
    type SourceUser = usize;
    type SourceType = usize;
    type RulePayload = AuthoredRulePayload;
    type CollectionKind = CollectionKind;
    type Error = AuthoredSynthesisError<E>;

    fn admit(&mut self, event: SynthesisEventFor<'_, Self>) -> Outcome<(), E> {
        admit(&mut self.policy, AuthoredSynthesisEvent::Synthesis(event))
    }

    fn clone_user(&mut self, occurrence: &usize) -> Outcome<AuthoredRulePayload, E> {
        Ok(AuthoredRulePayload {
            rule: self.source.productions[*occurrence]
                .authored
                .expect("selected source occurrence was checked"),
            origin: AuthoredRuleOrigin::User { production_index: *occurrence },
        })
    }

    fn normalize_user(self, rule: &mut AuthoredRulePayload) -> Outcome<Self, E> {
        let Self {
            source,
            reader,
            original_rules,
            session,
            mut policy,
        } = self;
        let (session, current) = session
            .normalize(rule.rule, |event| policy(AuthoredSynthesisEvent::Normalization(event)))
            .map_err(AuthoredSynthesisError::Normalization)?;
        rule.rule = current;
        Ok(Self {
            source,
            reader,
            original_rules,
            session,
            policy,
        })
    }

    fn first_item_is_var(&mut self, payload: &AuthoredRulePayload) -> Outcome<bool, E> {
        let Some(AuthoredNode::Rule(rule)) = self.session.store().get(payload.rule.0) else {
            unreachable!("only checked original or materialized rule handles enter buckets")
        };
        Ok(matches!(
            rule.items.first(),
            Some(AuthoredLegacyItem::NonTerminal { kind: NonTerminalKind::Var, .. })
        ))
    }

    fn materialize_synthetic(
        self,
        recipe: SyntheticRule<CollectionKind>,
    ) -> Outcome<(Self, AuthoredRulePayload), E> {
        let Self {
            source,
            reader,
            original_rules,
            session,
            mut policy,
        } = self;
        let (session, rule) = session
            .materialize_synthetic(recipe, |event| {
                policy(AuthoredSynthesisEvent::Normalization(event))
            })
            .map_err(AuthoredSynthesisError::Normalization)?;
        Ok((
            Self {
                source,
                reader,
                original_rules,
                session,
                policy,
            },
            AuthoredRulePayload {
                rule,
                origin: AuthoredRuleOrigin::Synthetic,
            },
        ))
    }

    fn has_literal_block(&mut self, index: &usize) -> Outcome<bool, E> {
        let header = self.reader.header();
        let name = self
            .reader
            .rule_reader()
            .name(header.categories[*index].name)
            .payload();
        for position in &header.global_tokens {
            admit(&mut self.policy, AuthoredSynthesisEvent::LiteralToken(*position))?;
            let token = &header.tokens[*position as usize];
            if token.from_literals
                && token.category.is_some_and(|category| {
                    self.reader.rule_reader().name(category).payload().spelling == name.spelling
                })
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn literal_label(&mut self, index: &usize) -> Outcome<String, E> {
        let category = &self.reader.header().categories[*index];
        // The callbacks are invoked sequentially by the original selector. The
        // local cell only permits that one policy borrow across FnOnce inputs.
        let policy = RefCell::new(&mut self.policy);
        try_generate_literal_label_observed(
            || {
                admit(
                    &mut **policy.borrow_mut(),
                    AuthoredSynthesisEvent::NativeProbe {
                        category: *index,
                        probe: NativeProbe::ByteVector,
                    },
                )?;
                match category.byte_observation {
                    SourceObservation::Known(value) => Ok(value),
                    SourceObservation::Unavailable => {
                        Err(AuthoredSynthesisError::UnavailableObservation {
                            category: *index,
                            probe: NativeProbe::ByteVector,
                        })
                    },
                }
            },
            || {
                admit(
                    &mut **policy.borrow_mut(),
                    AuthoredSynthesisEvent::NativeProbe {
                        category: *index,
                        probe: NativeProbe::Literal,
                    },
                )?;
                match &category.literal_observation {
                    SourceObservation::Known(Some(observation)) => {
                        admit(
                            &mut **policy.borrow_mut(),
                            AuthoredSynthesisEvent::NativeObservation(observation),
                        )?;
                        Ok(observation.clone())
                    },
                    SourceObservation::Known(None) => {
                        Err(AuthoredSynthesisError::AbsentNativeObservation(*index))
                    },
                    SourceObservation::Unavailable => {
                        Err(AuthoredSynthesisError::UnavailableObservation {
                            category: *index,
                            probe: NativeProbe::Literal,
                        })
                    },
                }
            },
            |label| copy(&mut **policy.borrow_mut(), label),
        )
    }

    fn collection(&mut self, index: &usize) -> Outcome<CollectionRecipe<CollectionKind>, E> {
        let category = &self.reader.header().categories[*index];
        let collection = category
            .collection
            .as_ref()
            .expect("original synthesis checked collection presence");
        let defaults = if collection.open.is_none()
            || collection.close.is_none()
            || collection.separator.is_none()
        {
            admit(&mut self.policy, AuthoredSynthesisEvent::CollectionDefaults(collection.kind))?;
            Some(match collection.kind {
                CollectionKind::List => collection_declaration::list_defaults(),
                CollectionKind::Bag => collection_declaration::bag_defaults(),
                CollectionKind::Set => collection_declaration::set_defaults(),
                CollectionKind::Map => collection_declaration::map_defaults(),
                CollectionKind::PathMap => collection_declaration::pathmap_defaults(),
            })
        } else {
            None
        };
        let open = copy(
            &mut self.policy,
            collection.open.as_deref().unwrap_or_else(|| {
                &defaults
                    .as_ref()
                    .expect("missing opener selected defaults")
                    .open
            }),
        )?;
        let close = copy(
            &mut self.policy,
            collection.close.as_deref().unwrap_or_else(|| {
                &defaults
                    .as_ref()
                    .expect("missing closer selected defaults")
                    .close
            }),
        )?;
        let separator = copy(
            &mut self.policy,
            collection.separator.as_deref().unwrap_or_else(|| {
                &defaults
                    .as_ref()
                    .expect("missing separator selected defaults")
                    .sep
            }),
        )?;
        admit(
            &mut self.policy,
            AuthoredSynthesisEvent::CollectionLookup {
                source: self.source,
                rules: self.original_rules,
            },
        )?;
        let element_reader = ElementReader {
            reader: self.reader.rule_reader(),
            target: category.name,
        };
        let element = collection_declaration::collection_element_for_category(
            &element_reader,
            &self.reader.header().categories,
            self.original_rules,
        )
        .transpose()
        .map_err(|()| AuthoredSynthesisError::UnavailableObservation {
            category: *index,
            probe: NativeProbe::CollectionElement,
        })?;
        let element_category = copy(
            &mut self.policy,
            &self
                .reader
                .rule_reader()
                .name(element.unwrap_or(category.name))
                .payload()
                .spelling,
        )?;
        let label = copy(
            &mut self.policy,
            collection_declaration::declared_collection_literal_label(collection.kind),
        )?;
        Ok(CollectionRecipe {
            kind: collection.kind,
            label,
            element_category,
            open,
            close,
            separator,
        })
    }

    fn var_label(&mut self, index: &usize) -> Outcome<String, E> {
        let category = &self
            .reader
            .rule_reader()
            .name(self.reader.header().categories[*index].name)
            .payload()
            .spelling;
        admit(&mut self.policy, AuthoredSynthesisEvent::VarLabel(category))?;
        generate_var_label(category, |prefix| {
            let length = prefix
                .len()
                .checked_add(3)
                .ok_or(AuthoredSynthesisError::Allocation)?;
            let mut label = String::new();
            label
                .try_reserve_exact(length)
                .map_err(|_| AuthoredSynthesisError::Allocation)?;
            label.push_str(&prefix);
            label.push_str("Var");
            Ok(label)
        })
    }

    fn declares_binder(&mut self) -> Outcome<bool, E> {
        let policy = &mut self.policy;
        try_declares_binder(
            self.reader.rule_reader(),
            self.original_rules.iter().copied(),
            |event| policy(AuthoredSynthesisEvent::Binder(event)),
        )
        .map_err(AuthoredSynthesisError::Binder)
    }
}

struct ElementReader<'reader, 'core> {
    reader: &'reader AuthoredRuleReader<'core>,
    target: AuthoredNameId,
}

impl<'core> BinderPresenceReader<'core> for AuthoredRuleReader<'core> {
    type Rule = AuthoredRuleId;
    type Item = AuthoredLegacyItem;

    fn context(&self, rule: Self::Rule) -> Option<AuthoredParamsId> {
        self.rule(rule).term_context
    }
    fn items(&self, rule: Self::Rule) -> &'core [Self::Item] {
        &self.rule(rule).items
    }
    fn item_is_binder(&self, item: &Self::Item) -> bool {
        matches!(item, AuthoredLegacyItem::Binder { .. })
    }
}

impl<'core> CollectionElementReader<'core> for ElementReader<'_, 'core> {
    type Declaration = AuthoredCategoryDeclaration;
    type Rule = AuthoredRuleId;
    type Item = AuthoredLegacyItem;
    type Element = Result<AuthoredNameId, ()>;

    fn type_matches(&self, declaration: &'core Self::Declaration) -> bool {
        self.reader.name(declaration.name).payload().equality_class
            == self.reader.name(self.target).payload().equality_class
    }
    fn has_collection(&self, declaration: &'core Self::Declaration) -> bool {
        declaration.collection.is_some()
    }
    fn native_element(&self, declaration: &'core Self::Declaration) -> Option<Self::Element> {
        match declaration.element_observation {
            SourceObservation::Known(value) => value.map(Ok),
            SourceObservation::Unavailable => Some(Err(())),
        }
    }
    fn rule_matches(&self, rule: &'core Self::Rule) -> bool {
        self.reader
            .name(self.reader.rule(*rule).category)
            .payload()
            .equality_class
            == self.reader.name(self.target).payload().equality_class
    }
    fn items(&self, rule: &'core Self::Rule) -> &'core [Self::Item] {
        &self.reader.rule(*rule).items
    }
    fn item_element(&self, item: &'core Self::Item) -> Option<Self::Element> {
        match item {
            AuthoredLegacyItem::Collection { element, .. } => Some(Ok(*element)),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests;
