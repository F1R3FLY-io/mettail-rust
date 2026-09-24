//! Owned construction adapter for the original legacy normalization worker.
//!
//! One consuming session retains the original flat arena and appends only the
//! original constructors' fixed shallow results. It neither reparses grammar
//! source nor derives normalization rules. Generated names use the original
//! spellings and a lazily checked spelling/equality-class source profile.
//! `AuthoredNormalizationMaterialization.v` covers this materialization boundary;
//! the original worker's separate model covers its two scans and event order.
//! `AuthoredSyntheticMaterialization.v` covers the additional shallow recipe
//! bridge, using this same session and preserving optional field presence.

use super::atomic::{LegacyAtomicItem, LegacyAtomicKind};
use super::synthetic::{SyntheticParam, SyntheticRule, SyntheticType};
use super::InfixSyntaxShape;

use mettail_ast::legacy_rule_normalization::{
    try_normalize_legacy_rule_with, LegacyItemView, LegacyNormalizationError,
    LegacyNormalizationEvent, LegacyRuleNormalizationAdapter,
};
use mettail_grammar_core::{
    AuthoredLegacyItem, AuthoredName, AuthoredNameId, AuthoredNode, AuthoredOperation,
    AuthoredOperationId, AuthoredParam, AuthoredParamId, AuthoredParamsId, AuthoredRule,
    AuthoredRuleId, AuthoredRuleStore, AuthoredStoreError, AuthoredSyntax, AuthoredSyntaxId,
    AuthoredType, AuthoredTypeId, CollectionKind, NonTerminalKind,
};
use std::collections::HashMap;

/// Borrowed work descriptions, emitted before their associated work/allocation.
/// A caller supplies a finite policy covering payload sizes and slot counts.
/// These events are not an allocated execution trace or a physical RSS bound.
#[derive(Debug)]
pub enum AuthoredNormalizationEvent<'a> {
    OriginalRule(AuthoredRuleId),
    Legacy(LegacyNormalizationEvent<'a, AuthoredNameId, String, CollectionKind>),
    NameNode(u32),
    NameLookup(&'a str),
    NameIndexEntry(&'a str),
    Append(&'a AuthoredNode),
    ParamSlots(usize),
    SyntaxSlots(usize),
    LegacyItems(usize),
    LegacyItem(&'a AuthoredLegacyItem),
}

/// Semantic refusal is a successful unchanged rule, distinct from these errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthoredNormalizationError<E> {
    Admission(E),
    InvalidOriginalRule(AuthoredRuleId),
    HalfDelimiter { rule: AuthoredRuleId, index: usize },
    NameProfileConflict(AuthoredNameId),
    NameClassOverflow,
    Store(AuthoredStoreError),
    Allocation,
    CounterOverflow,
    UnsupportedSyntheticLegacyItem,
    UnsupportedSyntheticSyntax,
}

type Outcome<T, E> = Result<T, AuthoredNormalizationError<E>>;

/// Private flat ownership for one derivation. No mutable arena reference escapes.
/// Errors consume the session: no partially materialized result can be reused.
#[derive(Debug)]
pub struct AuthoredNormalizationSession {
    store: AuthoredRuleStore,
    original_len: usize,
    names: Option<NameIndex>,
}

impl AuthoredNormalizationSession {
    /// Consume the already validated store in constant time, without copying it.
    /// Generated-name profile checking is deferred until normalization succeeds.
    pub fn new(store: AuthoredRuleStore) -> Self {
        let original_len = store.len();
        Self { store, original_len, names: None }
    }

    pub fn store(&self) -> &AuthoredRuleStore {
        &self.store
    }

    pub fn into_store(self) -> AuthoredRuleStore {
        self.store
    }

    fn original_rule<E>(&self, id: AuthoredRuleId) -> Outcome<&AuthoredRule, E> {
        if (id.0 as usize) < self.original_len {
            if let Some(AuthoredNode::Rule(rule)) = self.store.get(id.0) {
                return Ok(rule);
            }
        }
        Err(AuthoredNormalizationError::InvalidOriginalRule(id))
    }

    /// Invoke the existing normalizer once, then materialize its successful pair.
    /// `Ok((session, original))` preserves original semantic refusal. A successful
    /// new handle has both context and syntax and cannot be resubmitted as an
    /// original input in this session. The declaration header is never changed.
    pub fn normalize<E>(
        mut self,
        id: AuthoredRuleId,
        mut admit: impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<(Self, AuthoredRuleId), E> {
        use AuthoredNormalizationError as Error;
        use AuthoredNormalizationEvent as Event;
        admit(Event::OriginalRule(id)).map_err(Error::Admission)?;
        let rule = self.original_rule(id)?;
        let mut adapter = RecipeAdapter { rule };
        let output = try_normalize_legacy_rule_with(&mut adapter, |event| {
            let preflight = match &event {
                LegacyNormalizationEvent::PreflightItem(index) => Some(*index),
                _ => None,
            };
            admit(Event::Legacy(event)).map_err(Error::Admission)?;
            if let Some(index) = preflight {
                if let AuthoredLegacyItem::Collection { open, close, .. } = &rule.items[index] {
                    if open.is_some() != close.is_some() {
                        return Err(Error::HalfDelimiter { rule: id, index });
                    }
                }
            }
            Ok(())
        })
        .map_err(|error| match error {
            LegacyNormalizationError::Admission(error) => error,
            LegacyNormalizationError::Allocation => Error::Allocation,
            LegacyNormalizationError::CounterOverflow => Error::CounterOverflow,
        })?;
        let Some((params, syntax)) = output else {
            return Ok((self, id));
        };

        self.ensure_name_index(&mut admit)?;
        admit(Event::ParamSlots(params.len())).map_err(Error::Admission)?;
        let mut param_ids = Vec::new();
        param_ids
            .try_reserve_exact(params.len())
            .map_err(|_| Error::Allocation)?;
        for param in params {
            param_ids.push(self.materialize_param(param, &mut admit)?);
        }
        admit(Event::SyntaxSlots(syntax.len())).map_err(Error::Admission)?;
        let mut syntax_items = Vec::new();
        syntax_items
            .try_reserve_exact(syntax.len())
            .map_err(|_| Error::Allocation)?;
        for item in syntax {
            syntax_items.push(self.materialize_syntax(item, &mut admit)?);
        }

        // Copy only the retained original fields; no per-rule arena clone and
        // no public rule with just one of the two normalized fields installed.
        let original = self.original_rule(id)?;
        let (label, category) = (original.label, original.category);
        let source_body_present = original.source_body_present;
        let explicit_fold = original.explicit_fold;
        admit(Event::LegacyItems(original.items.len())).map_err(Error::Admission)?;
        let mut items = Vec::new();
        items
            .try_reserve_exact(original.items.len())
            .map_err(|_| Error::Allocation)?;
        for item in &original.items {
            admit(Event::LegacyItem(item)).map_err(Error::Admission)?;
            items.push(item.clone());
        }
        let result = self.commit_rule(
            label,
            category,
            source_body_present,
            explicit_fold,
            items,
            Some(param_ids),
            Some(syntax_items),
            &mut admit,
        )?;
        Ok((self, result))
    }

    /// Consume an original synthetic recipe through the existing materializers.
    /// The caller supplies admitted source names and the original worker's
    /// recipe; this method neither synthesizes rules nor validates Rust syntax.
    /// An error returns no session or rule handle. External descriptor metadata
    /// retains the original synthetic defaults independently of this source arena.
    pub fn materialize_synthetic<E>(
        mut self,
        rule: SyntheticRule<CollectionKind>,
        mut admit: impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<(Self, AuthoredRuleId), E> {
        use AuthoredNormalizationError as Error;
        use AuthoredNormalizationEvent as Event;
        self.ensure_name_index(&mut admit)?;
        let category = self.intern(rule.category, &mut admit)?;
        let params = if let Some(params) = rule.term_context {
            admit(Event::ParamSlots(params.len())).map_err(Error::Admission)?;
            let mut ids = Vec::new();
            ids.try_reserve_exact(params.len())
                .map_err(|_| Error::Allocation)?;
            for param in params {
                let recipe = match param {
                    SyntheticParam::Simple { name, ty: SyntheticType::Base(category) } => {
                        ParamRecipe::Simple {
                            name,
                            category: CategoryName::Spelling(category),
                        }
                    },
                    SyntheticParam::Simple {
                        name,
                        ty: SyntheticType::Collection { kind, element },
                    } => ParamRecipe::Collection {
                        name,
                        kind,
                        element: CategoryName::Spelling(element),
                    },
                    SyntheticParam::Abstraction { binder, body, domain, codomain } => {
                        ParamRecipe::Abstraction {
                            binder,
                            body,
                            domain: CategoryName::Spelling(domain),
                            codomain: CategoryName::Spelling(codomain),
                        }
                    },
                };
                ids.push(self.materialize_param(recipe, &mut admit)?);
            }
            Some(ids)
        } else {
            None
        };
        let label = self.intern(rule.label, &mut admit)?;
        admit(Event::LegacyItems(rule.items.len())).map_err(Error::Admission)?;
        let mut items = Vec::new();
        items
            .try_reserve_exact(rule.items.len())
            .map_err(|_| Error::Allocation)?;
        for item in rule.items {
            let item = match item {
                LegacyAtomicItem::Terminal(text) => AuthoredLegacyItem::Terminal(text),
                LegacyAtomicItem::NonTerminal { kind, ident } => AuthoredLegacyItem::NonTerminal {
                    ident: self.intern(ident, &mut admit)?,
                    kind: match kind {
                        LegacyAtomicKind::Integer => NonTerminalKind::Integer,
                        LegacyAtomicKind::Boolean => NonTerminalKind::Boolean,
                        LegacyAtomicKind::StringLiteral => NonTerminalKind::StringLiteral,
                        LegacyAtomicKind::FloatLiteral => NonTerminalKind::FloatLiteral,
                        LegacyAtomicKind::Var => NonTerminalKind::Var,
                        LegacyAtomicKind::Ident => NonTerminalKind::Ident,
                        LegacyAtomicKind::Category => NonTerminalKind::Category,
                    },
                },
                LegacyAtomicItem::Other => return Err(Error::UnsupportedSyntheticLegacyItem),
            };
            admit(Event::LegacyItem(&item)).map_err(Error::Admission)?;
            items.push(item);
        }
        let syntax = if let Some(syntax) = rule.syntax_pattern {
            admit(Event::SyntaxSlots(syntax.len())).map_err(Error::Admission)?;
            let mut output = Vec::new();
            output
                .try_reserve_exact(syntax.len())
                .map_err(|_| Error::Allocation)?;
            for item in syntax {
                let recipe = match item {
                    InfixSyntaxShape::Literal(text) => SyntaxRecipe::Literal(text),
                    InfixSyntaxShape::Param(name) => SyntaxRecipe::Param(name),
                    InfixSyntaxShape::Sep { collection, separator } => {
                        SyntaxRecipe::Sep { name: collection, separator }
                    },
                    InfixSyntaxShape::Other => return Err(Error::UnsupportedSyntheticSyntax),
                };
                output.push(self.materialize_syntax(recipe, &mut admit)?);
            }
            Some(output)
        } else {
            None
        };
        let result = self.commit_rule(
            label,
            category,
            mettail_grammar_core::SourceObservation::Known(false),
            mettail_grammar_core::SourceObservation::Known(false),
            items,
            params,
            syntax,
            &mut admit,
        )?;
        Ok((self, result))
    }

    fn ensure_name_index<E>(
        &mut self,
        admit: &mut impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<(), E> {
        if self.names.is_none() {
            self.names = Some(NameIndex::from_store(&self.store, admit)?);
        }
        Ok(())
    }

    fn commit_rule<E>(
        &mut self,
        label: AuthoredNameId,
        category: AuthoredNameId,
        source_body_present: mettail_grammar_core::SourceObservation<bool>,
        explicit_fold: mettail_grammar_core::SourceObservation<bool>,
        items: Vec<AuthoredLegacyItem>,
        params: Option<Vec<AuthoredParamId>>,
        syntax: Option<Vec<AuthoredSyntax>>,
        admit: &mut impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<AuthoredRuleId, E> {
        let term_context = params
            .map(|ids| {
                self.append(AuthoredNode::Params(ids), admit)
                    .map(AuthoredParamsId)
            })
            .transpose()?;
        let syntax_pattern = syntax
            .map(|items| {
                self.append(AuthoredNode::Syntax(items), admit)
                    .map(AuthoredSyntaxId)
            })
            .transpose()?;
        self.append(
            AuthoredNode::Rule(AuthoredRule {
                label,
                category,
                source_body_present,
                explicit_fold,
                term_context,
                syntax_pattern,
                items,
            }),
            admit,
        )
        .map(AuthoredRuleId)
    }

    fn append<E>(
        &mut self,
        node: AuthoredNode,
        admit: &mut impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<u32, E> {
        use AuthoredNormalizationError as Error;
        admit(AuthoredNormalizationEvent::Append(&node)).map_err(Error::Admission)?;
        self.store.try_reserve(1).map_err(|_| Error::Allocation)?;
        self.store.try_push(node).map_err(Error::Store)
    }

    fn intern<E>(
        &mut self,
        spelling: String,
        admit: &mut impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<AuthoredNameId, E> {
        use AuthoredNormalizationError as Error;
        use AuthoredNormalizationEvent as Event;
        let names = self
            .names
            .as_mut()
            .expect("successful recipes initialized the name index");
        admit(Event::NameLookup(&spelling)).map_err(Error::Admission)?;
        if let Some(class) = names.by_spelling.get(&spelling) {
            return Ok(names.by_class[class]);
        }
        // Lookup precedes extension: an existing MAX-class name remains valid.
        let class = names.next_class.ok_or(Error::NameClassOverflow)?;
        admit(Event::NameIndexEntry(&spelling)).map_err(Error::Admission)?;
        names.reserve()?;
        let key = spelling.clone();
        let id =
            AuthoredNameId(self.append(
                AuthoredNode::Name(AuthoredName { spelling, equality_class: class }),
                admit,
            )?);
        let names = self
            .names
            .as_mut()
            .expect("append preserves the private name index");
        names.by_spelling.insert(key, class);
        names.by_class.insert(class, id);
        names.next_class = class.checked_add(1);
        Ok(id)
    }

    fn base<E>(
        &mut self,
        category: AuthoredNameId,
        admit: &mut impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<AuthoredTypeId, E> {
        self.append(AuthoredNode::Type(AuthoredType::Base(category)), admit)
            .map(AuthoredTypeId)
    }

    fn materialize_param<E>(
        &mut self,
        recipe: ParamRecipe,
        admit: &mut impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<AuthoredParamId, E> {
        let param = match recipe {
            ParamRecipe::Simple { name, category } => {
                let name = self.intern(name, admit)?;
                let category = self.resolve_category(category, admit)?;
                let ty = self.base(category, admit)?;
                AuthoredParam::Simple { name, ty }
            },
            ParamRecipe::Abstraction { binder, body, domain, codomain } => {
                let binder = self.intern(binder, admit)?;
                let body = self.intern(body, admit)?;
                let domain = self.resolve_category(domain, admit)?;
                let codomain = self.resolve_category(codomain, admit)?;
                let domain = self.base(domain, admit)?;
                let codomain = self.base(codomain, admit)?;
                let ty =
                    AuthoredTypeId(self.append(
                        AuthoredNode::Type(AuthoredType::Arrow { domain, codomain }),
                        admit,
                    )?);
                AuthoredParam::Abstraction { binder, body, ty }
            },
            ParamRecipe::Collection { name, kind, element } => {
                let name = self.intern(name, admit)?;
                let element = self.resolve_category(element, admit)?;
                let element = self.base(element, admit)?;
                let ty = AuthoredTypeId(self.append(
                    AuthoredNode::Type(AuthoredType::Collection { kind, element }),
                    admit,
                )?);
                AuthoredParam::Simple { name, ty }
            },
        };
        self.append(AuthoredNode::Param(param), admit)
            .map(AuthoredParamId)
    }

    fn materialize_syntax<E>(
        &mut self,
        recipe: SyntaxRecipe,
        admit: &mut impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<AuthoredSyntax, E> {
        Ok(match recipe {
            SyntaxRecipe::Literal(text) => AuthoredSyntax::Literal(text),
            SyntaxRecipe::Param(name) => AuthoredSyntax::Param(self.intern(name, admit)?),
            SyntaxRecipe::Sep { name, separator } => {
                let collection = self.intern(name, admit)?;
                let id = self.append(
                    AuthoredNode::Operation(AuthoredOperation::Sep {
                        collection,
                        separator,
                        source: None,
                    }),
                    admit,
                )?;
                AuthoredSyntax::Op(AuthoredOperationId(id))
            },
        })
    }

    fn resolve_category<E>(
        &mut self,
        category: CategoryName,
        admit: &mut impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<AuthoredNameId, E> {
        match category {
            CategoryName::Existing(id) => Ok(id),
            CategoryName::Spelling(text) => self.intern(text, admit),
        }
    }
}

/// Lookup tables are never iterated to choose an ID or equality class.
/// The source arena order chooses the first representative; sparse class
/// numbers are retained. This profile is narrower than generic store validity.
#[derive(Debug)]
struct NameIndex {
    by_spelling: HashMap<String, u32>,
    by_class: HashMap<u32, AuthoredNameId>,
    next_class: Option<u32>,
}

impl NameIndex {
    fn reserve<E>(&mut self) -> Outcome<(), E> {
        self.by_spelling
            .try_reserve(1)
            .map_err(|_| AuthoredNormalizationError::Allocation)?;
        self.by_class
            .try_reserve(1)
            .map_err(|_| AuthoredNormalizationError::Allocation)
    }

    fn from_store<E>(
        store: &AuthoredRuleStore,
        admit: &mut impl FnMut(AuthoredNormalizationEvent<'_>) -> Result<(), E>,
    ) -> Outcome<Self, E> {
        use AuthoredNormalizationError as Error;
        use AuthoredNormalizationEvent as Event;
        let mut result = Self {
            by_spelling: HashMap::new(),
            by_class: HashMap::new(),
            next_class: Some(0),
        };
        let mut maximum = None;
        for index in 0..store.len() {
            let index = u32::try_from(index)
                .map_err(|_| Error::Store(AuthoredStoreError::IndexOverflow))?;
            admit(Event::NameNode(index)).map_err(Error::Admission)?;
            let Some(AuthoredNode::Name(name)) = store.get(index) else {
                continue;
            };
            admit(Event::NameLookup(&name.spelling)).map_err(Error::Admission)?;
            match result.by_spelling.get(&name.spelling) {
                Some(class) if *class == name.equality_class => continue,
                Some(_) => return Err(Error::NameProfileConflict(AuthoredNameId(index))),
                None if result.by_class.contains_key(&name.equality_class) => {
                    return Err(Error::NameProfileConflict(AuthoredNameId(index)));
                },
                None => {},
            }
            admit(Event::NameIndexEntry(&name.spelling)).map_err(Error::Admission)?;
            result.reserve()?;
            result
                .by_spelling
                .insert(name.spelling.clone(), name.equality_class);
            result
                .by_class
                .insert(name.equality_class, AuthoredNameId(index));
            maximum =
                Some(maximum.map_or(name.equality_class, |old: u32| old.max(name.equality_class)));
        }
        result.next_class = match maximum {
            None => Some(0),
            Some(value) => value.checked_add(1),
        };
        Ok(result)
    }
}

// Fixed-depth constructor recipes allow the original worker to borrow the
// immutable source while keeping all fallible arena effects outside its total
// callbacks. They are not a recursive AST or a second normalization pass.
enum CategoryName {
    Existing(AuthoredNameId),
    Spelling(String),
}

enum ParamRecipe {
    Simple {
        name: String,
        category: CategoryName,
    },
    Abstraction {
        binder: String,
        body: String,
        domain: CategoryName,
        codomain: CategoryName,
    },
    Collection {
        name: String,
        kind: CollectionKind,
        element: CategoryName,
    },
}

enum SyntaxRecipe {
    Literal(String),
    Param(String),
    Sep { name: String, separator: String },
}

struct RecipeAdapter<'input> {
    rule: &'input AuthoredRule,
}

impl<'input> LegacyRuleNormalizationAdapter<'input> for RecipeAdapter<'input> {
    type OriginalName = AuthoredNameId;
    type GeneratedName = String;
    type CollectionKind = CollectionKind;
    type Param = ParamRecipe;
    type Syntax = SyntaxRecipe;

    fn has_term_context(&self) -> bool {
        self.rule.term_context.is_some()
    }
    fn has_syntax_pattern(&self) -> bool {
        self.rule.syntax_pattern.is_some()
    }
    fn items_len(&self) -> usize {
        self.rule.items.len()
    }

    fn item(&self, index: usize) -> LegacyItemView<'input, AuthoredNameId, CollectionKind> {
        match &self.rule.items[index] {
            AuthoredLegacyItem::Terminal(text) => LegacyItemView::Terminal(text),
            AuthoredLegacyItem::NonTerminal { ident, kind } => {
                LegacyItemView::NonTerminal { ident, kind: *kind }
            },
            AuthoredLegacyItem::Binder { category } => LegacyItemView::Binder { category },
            AuthoredLegacyItem::Collection { kind, element, separator, open, close } => {
                // The admission callback already rejected every reached half
                // pair during the original full preflight before this view.
                LegacyItemView::Collection {
                    kind,
                    element,
                    separator,
                    delimiters: open.as_ref().zip(close.as_ref()),
                }
            },
        }
    }

    fn fresh_name(&mut self, index: usize) -> String {
        format!("p{}", index)
    }
    fn elems_name(&mut self) -> String {
        "elems".to_owned()
    }
    fn make_simple(&mut self, name: String, category: AuthoredNameId) -> ParamRecipe {
        ParamRecipe::Simple {
            name,
            category: CategoryName::Existing(category),
        }
    }
    fn make_abstraction(
        &mut self,
        binder: String,
        body: String,
        domain: AuthoredNameId,
        codomain: AuthoredNameId,
    ) -> ParamRecipe {
        ParamRecipe::Abstraction {
            binder,
            body,
            domain: CategoryName::Existing(domain),
            codomain: CategoryName::Existing(codomain),
        }
    }
    fn make_collection(
        &mut self,
        name: String,
        kind: CollectionKind,
        element: AuthoredNameId,
    ) -> ParamRecipe {
        ParamRecipe::Collection {
            name,
            kind,
            element: CategoryName::Existing(element),
        }
    }
    fn make_literal(&mut self, text: String) -> SyntaxRecipe {
        SyntaxRecipe::Literal(text)
    }
    fn make_param(&mut self, name: String) -> SyntaxRecipe {
        SyntaxRecipe::Param(name)
    }
    fn make_sep(&mut self, name: String, separator: String) -> SyntaxRecipe {
        SyntaxRecipe::Sep { name, separator }
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod synthetic_tests;
