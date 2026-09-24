//! Retained authored observations for the shared original WPDA classifiers.
//!
//! This is flat ownership, not another grammar or a parser. Every child is a
//! typed index into the same arena and must precede its owner, following the
//! existing theory-rule arena discipline. Clone, serialization, validation and
//! destruction therefore have no grammar-dependent native-stack depth.
//!
//! `AuthoredRuleStoreProjection.v` proves checked append, typed backward edges,
//! exact ordered payload retention and shallow reader correspondence. Source
//! capture must separately preserve source equality classes and observations.
//! Admission budgets and the original classifiers' narrower arithmetic domains
//! are separate checks; this store does not certify a grammar for execution.

use crate::{CollectionKind, LiteralNativeObservation, NativeKind};
use serde::{Deserialize, Deserializer, Serialize};

/// Original parser's unobserved collection field for a sourced separator.
/// This is a parser convention, not an inferred collection name.
pub const AUTHORED_CHAIN_COLLECTION_NAME: &str = "__chain__";

macro_rules! authored_ids {
    ($($name:ident),+ $(,)?) => {$(
        /// A typed arena reference. The default is the checked owned index;
        /// capture recipes may instead carry a borrowed source handle.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
        pub struct $name<I = u32>(pub I);
    )+};
}

authored_ids!(
    AuthoredNameId,
    AuthoredNamesId,
    AuthoredTypeId,
    AuthoredParamId,
    AuthoredParamsId,
    AuthoredSyntaxId,
    AuthoredOperationId,
    AuthoredRuleId,
);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AuthoredNodeTag {
    Name,
    Names,
    Type,
    Param,
    Params,
    Syntax,
    Operation,
    Rule,
}

/// Spelling and source equality are independent of the occurrence's arena ID.
/// Capture assigns classes using the source's actual equality, not Display.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoredName<K = u32> {
    pub spelling: String,
    pub equality_class: K,
}

/// Type observations read by the original classifiers and context converter.
/// Binder classification still ignores arrow domains and multi-binder interiors;
/// the context converter observes them through its separate shallow probes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthoredType<I = u32> {
    Base(AuthoredNameId<I>),
    Collection {
        kind: CollectionKind,
        element: AuthoredTypeId<I>,
    },
    Map {
        key: AuthoredTypeId<I>,
        value: AuthoredTypeId<I>,
    },
    Arrow {
        domain: AuthoredTypeId<I>,
        codomain: AuthoredTypeId<I>,
    },
    MultiBinder {
        inner: AuthoredTypeId<I>,
    },
    Unsupported {
        tag: u32,
    },
    /// The value frontend can express this shape; the original macro reader
    /// cannot. Keep both children and refuse an unsupported reader projection,
    /// never silently convert it to HashMap or a single-element PathMap.
    KeyedPathMap {
        key: AuthoredTypeId<I>,
        value: AuthoredTypeId<I>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthoredParam<I = u32> {
    Simple {
        name: AuthoredNameId<I>,
        ty: AuthoredTypeId<I>,
    },
    GuardBody {
        name: AuthoredNameId<I>,
    },
    Abstraction {
        binder: AuthoredNameId<I>,
        body: AuthoredNameId<I>,
        ty: AuthoredTypeId<I>,
    },
    MultiAbstraction {
        binder: AuthoredNameId<I>,
        body: AuthoredNameId<I>,
        ty: AuthoredTypeId<I>,
    },
    Optional {
        params: AuthoredParamsId<I>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthoredDelimitedRegionKind {
    Flt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthoredSyntax<I = u32> {
    Literal(String),
    Param(AuthoredNameId<I>),
    TokenKind {
        name: AuthoredNameId<I>,
        bind: Option<AuthoredNameId<I>>,
    },
    GuestBody {
        open: AuthoredNameId<I>,
        close: AuthoredNameId<I>,
        bind: AuthoredNameId<I>,
        kind: AuthoredDelimitedRegionKind,
    },
    Op(AuthoredOperationId<I>),
}

/// All original operation readers share this one handle space.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthoredOperation<I = u32> {
    Opt {
        inner: AuthoredSyntaxId<I>,
    },
    Sep {
        collection: AuthoredNameId<I>,
        separator: String,
        source: Option<AuthoredOperationId<I>>,
    },
    Map {
        source: AuthoredOperationId<I>,
        params: AuthoredNamesId<I>,
        body: AuthoredSyntaxId<I>,
    },
    Zip {
        left: AuthoredNameId<I>,
        right: AuthoredNameId<I>,
    },
    Unsupported {
        tag: u32,
    },
}

/// Retain the authored API name for the single original classifier vocabulary.
pub use crate::NonTerminalKind as AuthoredNonTerminalKind;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthoredLegacyItem<I = u32> {
    Terminal(String),
    NonTerminal {
        ident: AuthoredNameId<I>,
        kind: AuthoredNonTerminalKind,
    },
    Binder {
        category: AuthoredNameId<I>,
    },
    Collection {
        kind: CollectionKind,
        element: AuthoredNameId<I>,
        separator: String,
        /// Independent presence preserves the value frontend's raw data.
        /// The macro's optional pair maps to both present or both absent.
        open: Option<String>,
        close: Option<String>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoredRule<I = u32> {
    pub label: AuthoredNameId<I>,
    pub category: AuthoredNameId<I>,
    /// Authored body presence, not a later reduction/evaluation inference.
    pub source_body_present: SourceObservation<bool>,
    /// Whether Fold was explicitly present in this source declaration.
    pub explicit_fold: SourceObservation<bool>,
    pub term_context: Option<AuthoredParamsId<I>>,
    pub syntax_pattern: Option<AuthoredSyntaxId<I>>,
    pub items: Vec<AuthoredLegacyItem<I>>,
}

/// Source collection declarations retain independent optional delimiters.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoredCollectionDeclaration {
    pub kind: CollectionKind,
    pub open: Option<String>,
    pub close: Option<String>,
    pub separator: Option<String>,
    pub key_value_separator: Option<String>,
}

/// Retained source knowledge. Unavailable is not known absence: consumers
/// inspect availability only when the original helper reaches that probe.
/// There is deliberately no default for omitted wire fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SourceObservation<T> {
    Unavailable,
    Known(T),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoredCategoryDeclaration<I = u32> {
    pub name: AuthoredNameId<I>,
    pub native: Option<NativeKind>,
    pub collection: Option<AuthoredCollectionDeclaration>,
    pub byte_observation: SourceObservation<bool>,
    pub literal_observation: SourceObservation<Option<LiteralNativeObservation>>,
    pub element_observation: SourceObservation<Option<AuthoredNameId<I>>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoredTokenDeclaration<I = u32> {
    pub name: AuthoredNameId<I>,
    pub category: Option<AuthoredNameId<I>>,
    pub from_literals: bool,
    pub has_evaluation: bool,
    pub push: Option<AuthoredNameId<I>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoredModeDeclaration<I = u32> {
    pub name: AuthoredNameId<I>,
    /// Indices into the source token roster, not final lexer token IDs.
    pub tokens: Vec<u32>,
}

/// Immutable source observations. Final lexer/category/mode bindings are
/// stored separately: lowering can coalesce rows or give a row two routes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoredDeclarations<I = u32> {
    pub categories: Vec<AuthoredCategoryDeclaration<I>>,
    pub tokens: Vec<AuthoredTokenDeclaration<I>>,
    pub global_tokens: Vec<u32>,
    pub modes: Vec<AuthoredModeDeclaration<I>>,
}

impl<I: Copy> AuthoredDeclarations<I> {
    /// Extra capture roots, after rules, in original declaration field order.
    pub fn try_for_each_name<E>(
        &self,
        mut visit: impl FnMut(AuthoredNameId<I>) -> Result<(), E>,
    ) -> Result<(), E> {
        for category in &self.categories {
            visit(category.name)?;
            if let SourceObservation::Known(Some(element)) = category.element_observation {
                visit(element)?;
            }
        }
        for token in &self.tokens {
            visit(token.name)?;
            if let Some(category) = token.category {
                visit(category)?;
            }
            if let Some(push) = token.push {
                visit(push)?;
            }
        }
        for mode in &self.modes {
            visit(mode.name)?;
        }
        Ok(())
    }
}

impl<I> AuthoredDeclarations<I> {
    /// Resolve the same ordered name occurrences without touching payloads,
    /// source token positions, duplicates, or optional presence.
    pub fn try_map_names<J, E>(
        self,
        mut resolve: impl FnMut(AuthoredNameId<I>) -> Result<AuthoredNameId<J>, E>,
    ) -> Result<AuthoredDeclarations<J>, E> {
        let categories = self
            .categories
            .into_iter()
            .map(|row| {
                Ok(AuthoredCategoryDeclaration {
                    name: resolve(row.name)?,
                    native: row.native,
                    collection: row.collection,
                    byte_observation: row.byte_observation,
                    literal_observation: row.literal_observation,
                    element_observation: match row.element_observation {
                        SourceObservation::Unavailable => SourceObservation::Unavailable,
                        SourceObservation::Known(element) => {
                            SourceObservation::Known(element.map(&mut resolve).transpose()?)
                        },
                    },
                })
            })
            .collect::<Result<_, E>>()?;
        let tokens = self
            .tokens
            .into_iter()
            .map(|row| {
                Ok(AuthoredTokenDeclaration {
                    name: resolve(row.name)?,
                    category: row.category.map(&mut resolve).transpose()?,
                    from_literals: row.from_literals,
                    has_evaluation: row.has_evaluation,
                    push: row.push.map(&mut resolve).transpose()?,
                })
            })
            .collect::<Result<_, E>>()?;
        let modes = self
            .modes
            .into_iter()
            .map(|row| {
                Ok(AuthoredModeDeclaration {
                    name: resolve(row.name)?,
                    tokens: row.tokens,
                })
            })
            .collect::<Result<_, E>>()?;
        Ok(AuthoredDeclarations {
            categories,
            tokens,
            global_tokens: self.global_tokens,
            modes,
        })
    }

    /// Capture order is global tokens followed by each ordered mode roster.
    /// Check that exact partition without allocating a visited-token set.
    fn validate_source_rosters(&self) -> Result<(), AuthoredStoreError> {
        let mut expected = 0usize;
        for &actual in self
            .global_tokens
            .iter()
            .chain(self.modes.iter().flat_map(|mode| &mode.tokens))
        {
            if expected >= self.tokens.len() || usize::try_from(actual).ok() != Some(expected) {
                return Err(AuthoredStoreError::InvalidSourceTokenRoster {
                    position: expected,
                    actual: Some(actual),
                });
            }
            expected = expected
                .checked_add(1)
                .ok_or(AuthoredStoreError::IndexOverflow)?;
        }
        if expected != self.tokens.len() {
            return Err(AuthoredStoreError::InvalidSourceTokenRoster {
                position: expected,
                actual: None,
            });
        }
        Ok(())
    }
}

/// One vocabulary for owned nodes and shallow capture recipes. Neither generic
/// parameter introduces recursive ownership; children are always references.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthoredNode<I = u32, K = u32> {
    Name(AuthoredName<K>),
    Names(Vec<AuthoredNameId<I>>),
    Type(AuthoredType<I>),
    Param(AuthoredParam<I>),
    Params(Vec<AuthoredParamId<I>>),
    Syntax(Vec<AuthoredSyntax<I>>),
    Operation(AuthoredOperation<I>),
    Rule(AuthoredRule<I>),
}

impl<I, K> AuthoredNode<I, K> {
    pub fn tag(&self) -> AuthoredNodeTag {
        match self {
            Self::Name(_) => AuthoredNodeTag::Name,
            Self::Names(_) => AuthoredNodeTag::Names,
            Self::Type(_) => AuthoredNodeTag::Type,
            Self::Param(_) => AuthoredNodeTag::Param,
            Self::Params(_) => AuthoredNodeTag::Params,
            Self::Syntax(_) => AuthoredNodeTag::Syntax,
            Self::Operation(_) => AuthoredNodeTag::Operation,
            Self::Rule(_) => AuthoredNodeTag::Rule,
        }
    }
}

impl<I: Copy, K> AuthoredNode<I, K> {
    /// Visit only immediate references, in field/declaration order. This is the
    /// same edge roster used by checked append and deserialization validation.
    /// No referenced node is followed and no temporary edge vector is allocated.
    pub fn try_for_each_reference<E>(
        &self,
        mut visit: impl FnMut(AuthoredNodeTag, I) -> Result<(), E>,
    ) -> Result<(), E> {
        use AuthoredNodeTag as Tag;
        match self {
            Self::Name(_) => {},
            Self::Names(names) => {
                for name in names {
                    visit(Tag::Name, name.0)?;
                }
            },
            Self::Type(ty) => match ty {
                AuthoredType::Base(name) => visit(Tag::Name, name.0)?,
                AuthoredType::Collection { element, .. } => visit(Tag::Type, element.0)?,
                AuthoredType::Map { key, value } | AuthoredType::KeyedPathMap { key, value } => {
                    visit(Tag::Type, key.0)?;
                    visit(Tag::Type, value.0)?;
                },
                AuthoredType::Arrow { domain, codomain } => {
                    visit(Tag::Type, domain.0)?;
                    visit(Tag::Type, codomain.0)?;
                },
                AuthoredType::MultiBinder { inner } => visit(Tag::Type, inner.0)?,
                AuthoredType::Unsupported { .. } => {},
            },
            Self::Param(param) => match param {
                AuthoredParam::Simple { name, ty } => {
                    visit(Tag::Name, name.0)?;
                    visit(Tag::Type, ty.0)?;
                },
                AuthoredParam::GuardBody { name } => visit(Tag::Name, name.0)?,
                AuthoredParam::Abstraction { binder, body, ty }
                | AuthoredParam::MultiAbstraction { binder, body, ty } => {
                    visit(Tag::Name, binder.0)?;
                    visit(Tag::Name, body.0)?;
                    visit(Tag::Type, ty.0)?;
                },
                AuthoredParam::Optional { params } => visit(Tag::Params, params.0)?,
            },
            Self::Params(params) => {
                for param in params {
                    visit(Tag::Param, param.0)?;
                }
            },
            Self::Syntax(items) => {
                for item in items {
                    match item {
                        AuthoredSyntax::Literal(_) => {},
                        AuthoredSyntax::Param(name) => visit(Tag::Name, name.0)?,
                        AuthoredSyntax::TokenKind { name, bind } => {
                            visit(Tag::Name, name.0)?;
                            if let Some(bind) = bind {
                                visit(Tag::Name, bind.0)?;
                            }
                        },
                        AuthoredSyntax::GuestBody { open, close, bind, .. } => {
                            visit(Tag::Name, open.0)?;
                            visit(Tag::Name, close.0)?;
                            visit(Tag::Name, bind.0)?;
                        },
                        AuthoredSyntax::Op(operation) => visit(Tag::Operation, operation.0)?,
                    }
                }
            },
            Self::Operation(operation) => match operation {
                AuthoredOperation::Opt { inner } => visit(Tag::Syntax, inner.0)?,
                AuthoredOperation::Sep { collection, source, .. } => {
                    visit(Tag::Name, collection.0)?;
                    if let Some(source) = source {
                        visit(Tag::Operation, source.0)?;
                    }
                },
                AuthoredOperation::Map { source, params, body } => {
                    visit(Tag::Operation, source.0)?;
                    visit(Tag::Names, params.0)?;
                    visit(Tag::Syntax, body.0)?;
                },
                AuthoredOperation::Zip { left, right } => {
                    visit(Tag::Name, left.0)?;
                    visit(Tag::Name, right.0)?;
                },
                AuthoredOperation::Unsupported { .. } => {},
            },
            Self::Rule(rule) => {
                visit(Tag::Name, rule.label.0)?;
                visit(Tag::Name, rule.category.0)?;
                if let Some(params) = rule.term_context {
                    visit(Tag::Params, params.0)?;
                }
                if let Some(syntax) = rule.syntax_pattern {
                    visit(Tag::Syntax, syntax.0)?;
                }
                for item in &rule.items {
                    match item {
                        AuthoredLegacyItem::Terminal(_) => {},
                        AuthoredLegacyItem::NonTerminal { ident, .. } => visit(Tag::Name, ident.0)?,
                        AuthoredLegacyItem::Binder { category } => visit(Tag::Name, category.0)?,
                        AuthoredLegacyItem::Collection { element, .. } => {
                            visit(Tag::Name, element.0)?
                        },
                    }
                }
            },
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthoredStoreError {
    DeclarationsAlreadyPresent,
    InvalidDeclarationName {
        target: u32,
        actual: Option<AuthoredNodeTag>,
    },
    InvalidSourceTokenRoster {
        position: usize,
        actual: Option<u32>,
    },
    IndexOverflow,
    InvalidReference {
        owner: u32,
        target: u32,
        expected: AuthoredNodeTag,
        actual: Option<AuthoredNodeTag>,
    },
}

impl std::fmt::Display for AuthoredStoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DeclarationsAlreadyPresent => {
                write!(f, "authored declarations are already installed")
            },
            Self::InvalidDeclarationName { target, actual } => {
                write!(f, "authored declaration requires Name node {target}, found {actual:?}")
            },
            Self::InvalidSourceTokenRoster { position, actual } => write!(
                f,
                "authored source token roster requires position {position}, found {actual:?}"
            ),
            Self::IndexOverflow => write!(f, "authored-rule arena index exceeds u32"),
            Self::InvalidReference { owner, target, expected, actual } => write!(
                f,
                "authored node {owner} requires prior {expected:?} node {target}, found {actual:?}"
            ),
        }
    }
}

impl std::error::Error for AuthoredStoreError {}

/// Validated flat ownership. The private roster cannot be mutated except by
/// checked append. Deserialization also checks every node against its prefix.
/// Source/byte/allocation budgets must be enforced by the caller before decoding.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct AuthoredRuleStore {
    nodes: Vec<AuthoredNode>,
    declarations: Option<AuthoredDeclarations>,
}

impl AuthoredRuleStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn get(&self, index: u32) -> Option<&AuthoredNode> {
        self.nodes.get(index as usize)
    }

    pub fn declarations(&self) -> Option<&AuthoredDeclarations> {
        self.declarations.as_ref()
    }

    /// Publish a header only after all its captured names and source rosters
    /// validate. Existing immutable source declarations cannot be replaced.
    pub fn with_declarations(
        mut self,
        declarations: AuthoredDeclarations,
    ) -> Result<Self, AuthoredStoreError> {
        if self.declarations.is_some() {
            return Err(AuthoredStoreError::DeclarationsAlreadyPresent);
        }
        self.validate_declarations(&declarations)?;
        self.declarations = Some(declarations);
        Ok(self)
    }

    fn validate_declarations(
        &self,
        declarations: &AuthoredDeclarations,
    ) -> Result<(), AuthoredStoreError> {
        declarations.try_for_each_name(|name| {
            let actual = self.get(name.0).map(AuthoredNode::tag);
            if actual == Some(AuthoredNodeTag::Name) {
                Ok(())
            } else {
                Err(AuthoredStoreError::InvalidDeclarationName { target: name.0, actual })
            }
        })?;
        declarations.validate_source_rosters()
    }

    /// Append once only after the complete shallow reference check succeeds.
    /// Rejection leaves all previously retained nodes and handles unchanged.
    pub fn try_push(&mut self, node: AuthoredNode) -> Result<u32, AuthoredStoreError> {
        let index = checked_index(self.nodes.len())?;
        validate_node(&self.nodes, index, &node)?;
        self.nodes.push(node);
        Ok(index)
    }

    /// Reserve append capacity without changing any node, handle or declaration.
    /// Callers admit the requested allocation before invoking this operation;
    /// checked append remains responsible for index and reference validation.
    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.nodes.try_reserve(additional)
    }

    /// Admit an already owned roster without cloning, reordering or repairing it.
    pub fn from_nodes(nodes: Vec<AuthoredNode>) -> Result<Self, AuthoredStoreError> {
        let store = Self { nodes, declarations: None };
        store.validate()?;
        Ok(store)
    }

    pub fn validate(&self) -> Result<(), AuthoredStoreError> {
        for (index, node) in self.nodes.iter().enumerate() {
            validate_node(&self.nodes[..index], checked_index(index)?, node)?;
        }
        if let Some(declarations) = &self.declarations {
            self.validate_declarations(declarations)?;
        }
        Ok(())
    }
}

fn checked_index(index: usize) -> Result<u32, AuthoredStoreError> {
    u32::try_from(index).map_err(|_| AuthoredStoreError::IndexOverflow)
}

fn validate_node(
    prefix: &[AuthoredNode],
    owner: u32,
    node: &AuthoredNode,
) -> Result<(), AuthoredStoreError> {
    node.try_for_each_reference(|expected, target| {
        let actual = prefix.get(target as usize).map(AuthoredNode::tag);
        if actual == Some(expected) {
            Ok(())
        } else {
            Err(AuthoredStoreError::InvalidReference { owner, target, expected, actual })
        }
    })
}

impl<'de> Deserialize<'de> for AuthoredRuleStore {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        struct Wire {
            nodes: Vec<AuthoredNode>,
            #[serde(deserialize_with = "crate::core::required_option")]
            declarations: Option<AuthoredDeclarations>,
        }
        let wire = Wire::deserialize(deserializer)?;
        let store = Self {
            nodes: wire.nodes,
            declarations: wire.declarations,
        };
        store.validate().map_err(serde::de::Error::custom)?;
        Ok(store)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(spelling: &str, equality_class: u32) -> AuthoredNode {
        AuthoredNode::Name(AuthoredName {
            spelling: spelling.into(),
            equality_class,
        })
    }

    fn seed() -> AuthoredRuleStore {
        AuthoredRuleStore::from_nodes(vec![
            name("x", 7),                                              // 0 Name
            name("Expr", 8),                                           // 1 Name
            AuthoredNode::Type(AuthoredType::Base(AuthoredNameId(1))), // 2 Type
            AuthoredNode::Param(AuthoredParam::Simple {
                name: AuthoredNameId(0),
                ty: AuthoredTypeId(2),
            }), // 3 Param
            AuthoredNode::Names(vec![AuthoredNameId(0), AuthoredNameId(0)]), // 4 Names
            AuthoredNode::Params(vec![AuthoredParamId(3)]),            // 5 Params
            AuthoredNode::Syntax(vec![AuthoredSyntax::Param(AuthoredNameId(0))]), // 6 Syntax
            AuthoredNode::Operation(AuthoredOperation::Opt { inner: AuthoredSyntaxId(6) }), // 7 Operation
        ])
        .expect("valid ordered seed")
    }

    #[test]
    fn append_checks_each_tag_and_is_atomic_on_refusal() {
        use AuthoredNode as Node;
        use AuthoredNodeTag as Tag;
        let cases = vec![
            (Node::Names(vec![AuthoredNameId(2)]), Tag::Name, 2),
            (Node::Type(AuthoredType::Base(AuthoredNameId(2))), Tag::Name, 2),
            (
                Node::Type(AuthoredType::Collection {
                    kind: CollectionKind::List,
                    element: AuthoredTypeId(0),
                }),
                Tag::Type,
                0,
            ),
            (
                Node::Type(AuthoredType::Map {
                    key: AuthoredTypeId(0),
                    value: AuthoredTypeId(2),
                }),
                Tag::Type,
                0,
            ),
            (
                Node::Type(AuthoredType::Map {
                    key: AuthoredTypeId(2),
                    value: AuthoredTypeId(1),
                }),
                Tag::Type,
                1,
            ),
            (
                Node::Type(AuthoredType::KeyedPathMap {
                    key: AuthoredTypeId(2),
                    value: AuthoredTypeId(1),
                }),
                Tag::Type,
                1,
            ),
            (
                Node::Type(AuthoredType::Arrow {
                    domain: AuthoredTypeId(0),
                    codomain: AuthoredTypeId(2),
                }),
                Tag::Type,
                0,
            ),
            (
                Node::Type(AuthoredType::Arrow {
                    domain: AuthoredTypeId(2),
                    codomain: AuthoredTypeId(1),
                }),
                Tag::Type,
                1,
            ),
            (Node::Type(AuthoredType::MultiBinder { inner: AuthoredTypeId(0) }), Tag::Type, 0),
            (
                Node::Param(AuthoredParam::Simple {
                    name: AuthoredNameId(2),
                    ty: AuthoredTypeId(2),
                }),
                Tag::Name,
                2,
            ),
            (
                Node::Param(AuthoredParam::Simple {
                    name: AuthoredNameId(0),
                    ty: AuthoredTypeId(0),
                }),
                Tag::Type,
                0,
            ),
            (Node::Param(AuthoredParam::GuardBody { name: AuthoredNameId(2) }), Tag::Name, 2),
            (
                Node::Param(AuthoredParam::Abstraction {
                    binder: AuthoredNameId(0),
                    body: AuthoredNameId(2),
                    ty: AuthoredTypeId(2),
                }),
                Tag::Name,
                2,
            ),
            (
                Node::Param(AuthoredParam::MultiAbstraction {
                    binder: AuthoredNameId(0),
                    body: AuthoredNameId(1),
                    ty: AuthoredTypeId(0),
                }),
                Tag::Type,
                0,
            ),
            (
                Node::Param(AuthoredParam::Optional { params: AuthoredParamsId(4) }),
                Tag::Params,
                4,
            ),
            (Node::Params(vec![AuthoredParamId(0)]), Tag::Param, 0),
            (Node::Syntax(vec![AuthoredSyntax::Param(AuthoredNameId(2))]), Tag::Name, 2),
            (
                Node::Syntax(vec![AuthoredSyntax::TokenKind {
                    name: AuthoredNameId(0),
                    bind: Some(AuthoredNameId(2)),
                }]),
                Tag::Name,
                2,
            ),
            (
                Node::Syntax(vec![AuthoredSyntax::GuestBody {
                    open: AuthoredNameId(0),
                    close: AuthoredNameId(2),
                    bind: AuthoredNameId(1),
                    kind: AuthoredDelimitedRegionKind::Flt,
                }]),
                Tag::Name,
                2,
            ),
            (
                Node::Syntax(vec![AuthoredSyntax::Op(AuthoredOperationId(6))]),
                Tag::Operation,
                6,
            ),
            (
                Node::Operation(AuthoredOperation::Opt { inner: AuthoredSyntaxId(5) }),
                Tag::Syntax,
                5,
            ),
            (
                Node::Operation(AuthoredOperation::Sep {
                    collection: AuthoredNameId(0),
                    separator: ",".into(),
                    source: Some(AuthoredOperationId(6)),
                }),
                Tag::Operation,
                6,
            ),
            (
                Node::Operation(AuthoredOperation::Map {
                    source: AuthoredOperationId(7),
                    params: AuthoredNamesId(5),
                    body: AuthoredSyntaxId(6),
                }),
                Tag::Names,
                5,
            ),
            (
                Node::Operation(AuthoredOperation::Zip {
                    left: AuthoredNameId(0),
                    right: AuthoredNameId(2),
                }),
                Tag::Name,
                2,
            ),
            (
                Node::Rule(AuthoredRule {
                    source_body_present: crate::SourceObservation::Unavailable,
                    explicit_fold: crate::SourceObservation::Unavailable,
                    label: AuthoredNameId(0),
                    category: AuthoredNameId(1),
                    term_context: Some(AuthoredParamsId(4)),
                    syntax_pattern: Some(AuthoredSyntaxId(6)),
                    items: vec![],
                }),
                Tag::Params,
                4,
            ),
            (
                Node::Rule(AuthoredRule {
                    source_body_present: crate::SourceObservation::Unavailable,
                    explicit_fold: crate::SourceObservation::Unavailable,
                    label: AuthoredNameId(0),
                    category: AuthoredNameId(1),
                    term_context: Some(AuthoredParamsId(5)),
                    syntax_pattern: Some(AuthoredSyntaxId(5)),
                    items: vec![],
                }),
                Tag::Syntax,
                5,
            ),
            (
                Node::Rule(AuthoredRule {
                    source_body_present: crate::SourceObservation::Unavailable,
                    explicit_fold: crate::SourceObservation::Unavailable,
                    label: AuthoredNameId(0),
                    category: AuthoredNameId(1),
                    term_context: None,
                    syntax_pattern: None,
                    items: vec![AuthoredLegacyItem::Binder { category: AuthoredNameId(2) }],
                }),
                Tag::Name,
                2,
            ),
        ];
        for (node, expected, target) in cases {
            let mut store = seed();
            let before = store.clone();
            let actual = store.get(target).map(AuthoredNode::tag);
            assert_eq!(
                store.try_push(node),
                Err(AuthoredStoreError::InvalidReference { owner: 8, target, expected, actual })
            );
            assert_eq!(store, before);
        }
    }

    #[test]
    fn forward_self_and_cyclic_references_are_not_admitted_or_deserialized() {
        for nodes in [
            vec![AuthoredNode::Param(AuthoredParam::Optional { params: AuthoredParamsId(0) })],
            vec![
                AuthoredNode::Param(AuthoredParam::Optional { params: AuthoredParamsId(1) }),
                AuthoredNode::Params(vec![AuthoredParamId(0)]),
            ],
            vec![name("n", 0), AuthoredNode::Params(vec![AuthoredParamId(0)])],
        ] {
            let wire = postcard::to_allocvec(&AuthoredRuleStore {
                nodes: nodes.clone(),
                declarations: None,
            })
            .expect("encode invalid store in current wire format");
            assert!(AuthoredRuleStore::from_nodes(nodes).is_err());
            assert!(postcard::from_bytes::<AuthoredRuleStore>(&wire).is_err());
        }
        let mut store = seed();
        let before = store.clone();
        assert!(store
            .try_push(AuthoredNode::Syntax(
                vec![AuthoredSyntax::Op(AuthoredOperationId(u32::MAX)),]
            ))
            .is_err());
        assert_eq!(store, before);
    }

    #[test]
    fn declarations_preserve_payloads_and_validate_every_name_and_source_position() {
        let header = AuthoredDeclarations {
            categories: vec![AuthoredCategoryDeclaration {
                name: AuthoredNameId(1),
                native: Some(NativeKind::Bool),
                byte_observation: SourceObservation::Known(false),
                literal_observation: SourceObservation::Known(Some(
                    LiteralNativeObservation::ExactNativeType(crate::NativeType::Bool),
                )),
                element_observation: SourceObservation::Known(Some(AuthoredNameId(0))),
                collection: Some(AuthoredCollectionDeclaration {
                    kind: CollectionKind::PathMap,
                    open: Some(String::new()),
                    close: None,
                    separator: Some("|".into()),
                    key_value_separator: Some(":".into()),
                }),
            }],
            tokens: vec![
                AuthoredTokenDeclaration {
                    name: AuthoredNameId(0),
                    category: Some(AuthoredNameId(1)),
                    from_literals: true,
                    has_evaluation: false,
                    push: Some(AuthoredNameId(0)),
                };
                2
            ],
            global_tokens: vec![0],
            modes: vec![AuthoredModeDeclaration { name: AuthoredNameId(0), tokens: vec![1] }],
        };
        let store = seed()
            .with_declarations(header.clone())
            .expect("complete source header");
        assert_eq!(store.declarations(), Some(&header));
        let encoded = postcard::to_allocvec(&store).expect("header encode");
        assert_eq!(
            postcard::from_bytes::<AuthoredRuleStore>(&encoded).expect("header decode"),
            store
        );
        assert_eq!(
            store.clone().with_declarations(header.clone()),
            Err(AuthoredStoreError::DeclarationsAlreadyPresent)
        );
        for which in 0..6 {
            let mut bad = header.clone();
            let target = AuthoredNameId(2); // existing Type, not Name
            match which {
                0 => bad.categories[0].name = target,
                1 => bad.tokens[0].name = target,
                2 => bad.tokens[0].category = Some(target),
                3 => bad.tokens[0].push = Some(target),
                4 => bad.modes[0].name = target,
                _ => bad.categories[0].element_observation = SourceObservation::Known(Some(target)),
            }
            assert!(matches!(
                seed().with_declarations(bad),
                Err(AuthoredStoreError::InvalidDeclarationName { target: 2, .. })
            ));
        }
        for roster in [vec![], vec![0], vec![2], vec![1, 1]] {
            let mut bad = header.clone();
            bad.modes[0].tokens = roster;
            assert!(matches!(
                seed().with_declarations(bad),
                Err(AuthoredStoreError::InvalidSourceTokenRoster { .. })
            ));
        }
        let mut bad = header;
        bad.global_tokens = vec![1];
        assert!(seed().with_declarations(bad).is_err());
        let old_wire = postcard::to_allocvec(&seed().nodes).expect("legacy node-only format");
        assert!(
            postcard::from_bytes::<AuthoredRuleStore>(&old_wire).is_err(),
            "missing declarations option must not default"
        );
    }

    #[test]
    fn native_observation_roots_remap_in_order_and_stop_on_first_failure() {
        let row = |category, element| AuthoredCategoryDeclaration {
            name: AuthoredNameId(category),
            native: None,
            collection: None,
            byte_observation: SourceObservation::Known(false),
            literal_observation: SourceObservation::Known(None),
            element_observation: element,
        };
        let header = AuthoredDeclarations {
            categories: vec![
                row(1, SourceObservation::Known(Some(AuthoredNameId(0)))),
                row(1, SourceObservation::Unavailable),
                row(0, SourceObservation::Known(None)),
            ],
            tokens: vec![],
            global_tokens: vec![],
            modes: vec![],
        };
        let mut roots = vec![];
        header
            .try_for_each_name(|name| {
                roots.push(name.0);
                Ok::<_, ()>(())
            })
            .expect("ordered roots");
        assert_eq!(roots, [1, 0, 1, 0]);
        let mut mapped = vec![];
        let actual = header
            .clone()
            .try_map_names(|name| {
                mapped.push(name.0);
                Ok::<_, ()>(AuthoredNameId(name.0 + 10))
            })
            .expect("same ordered resolver");
        assert_eq!(mapped, roots);
        assert_eq!(actual.categories[0].name, AuthoredNameId(11));
        assert_eq!(
            actual.categories[0].element_observation,
            SourceObservation::Known(Some(AuthoredNameId(10)))
        );
        assert_eq!(actual.categories[1].element_observation, SourceObservation::Unavailable);
        assert_eq!(actual.categories[2].element_observation, SourceObservation::Known(None));
        for deny in 0..roots.len() {
            let mut visited = vec![];
            let result = header.clone().try_map_names(|name| {
                visited.push(name.0);
                if visited.len() - 1 == deny {
                    Err("denied")
                } else {
                    Ok(name)
                }
            });
            assert_eq!(result, Err("denied"));
            assert_eq!(visited, roots[..=deny]);
        }
    }

    #[test]
    fn every_native_observation_round_trips_and_changes_the_commitment() {
        use crate::{GrammarCoreV1, NativeType::*};
        let mut observations = vec![
            SourceObservation::Unavailable,
            SourceObservation::Known(None),
            SourceObservation::Known(Some(LiteralNativeObservation::CanonicalOpaque)),
        ];
        observations.extend(
            [
                Int8,
                Int16,
                Int32,
                Int64,
                Int128,
                Isize,
                UInt8,
                UInt16,
                UInt32,
                UInt64,
                UInt128,
                Usize,
                Float32,
                Float64,
                Bool,
                Str,
                CanonicalBigInt,
                CanonicalBigRat,
                CanonicalFixedPoint,
                VecCollection,
                HashBagCollection,
                HashSetCollection,
                HashMapLitCollection,
                HashMapCollection,
                Other("HashSetLit".into()),
                Other("PathMapLit".into()),
                Other("Opaque".into()),
            ]
            .into_iter()
            .map(|native| {
                SourceObservation::Known(Some(LiteralNativeObservation::ExactNativeType(native)))
            }),
        );
        let mut fingerprints = std::collections::HashSet::new();
        for observation in observations {
            let header = AuthoredDeclarations {
                categories: vec![AuthoredCategoryDeclaration {
                    name: AuthoredNameId(1),
                    native: None,
                    collection: None,
                    byte_observation: SourceObservation::Known(false),
                    literal_observation: observation,
                    element_observation: SourceObservation::Known(None),
                }],
                tokens: vec![],
                global_tokens: vec![],
                modes: vec![],
            };
            let store = seed().with_declarations(header).expect("typed header");
            let encoded = postcard::to_allocvec(&store).expect("all variants encode");
            assert_eq!(
                postcard::from_bytes::<AuthoredRuleStore>(&encoded).expect("all variants decode"),
                store
            );
            let mut grammar = GrammarCoreV1::new("observations");
            grammar.authored = Some(store);
            assert!(
                fingerprints.insert(grammar.fingerprint().expect("commitment includes metadata")),
                "distinct retained observations must not be erased from commitment input"
            );
        }
    }

    #[test]
    fn presence_legacy_payloads_and_duplicate_declarations_round_trip_exactly() {
        let mut store = seed();
        let empty_params = AuthoredParamsId(
            store
                .try_push(AuthoredNode::Params(vec![]))
                .expect("empty params"),
        );
        let empty_syntax = AuthoredSyntaxId(
            store
                .try_push(AuthoredNode::Syntax(vec![]))
                .expect("empty syntax"),
        );
        let items = vec![
            AuthoredLegacyItem::Terminal("literal".into()),
            AuthoredLegacyItem::NonTerminal {
                ident: AuthoredNameId(0),
                kind: AuthoredNonTerminalKind::Ident,
            },
            AuthoredLegacyItem::Binder { category: AuthoredNameId(1) },
            AuthoredLegacyItem::Collection {
                kind: CollectionKind::PathMap,
                element: AuthoredNameId(1),
                separator: ":".into(),
                open: Some("[".into()),
                close: None,
            },
        ];
        for context in [None, Some(empty_params)] {
            for syntax in [None, Some(empty_syntax)] {
                let rule = AuthoredRule {
                    source_body_present: crate::SourceObservation::Unavailable,
                    explicit_fold: crate::SourceObservation::Unavailable,
                    label: AuthoredNameId(0),
                    category: AuthoredNameId(1),
                    term_context: context,
                    syntax_pattern: syntax,
                    items: items.clone(),
                };
                let id = store
                    .try_push(AuthoredNode::Rule(rule.clone()))
                    .expect("independent presence");
                assert_eq!(store.get(id), Some(&AuthoredNode::Rule(rule)));
            }
        }
        store
            .try_push(name("x", 99))
            .expect("same spelling distinct identity");
        store
            .try_push(name("x", 7))
            .expect("different occurrence same identity");
        store
            .try_push(AuthoredNode::Params(vec![AuthoredParamId(3), AuthoredParamId(3)]))
            .expect("ordered duplicate params");
        store
            .try_push(AuthoredNode::Type(AuthoredType::KeyedPathMap {
                key: AuthoredTypeId(2),
                value: AuthoredTypeId(2),
            }))
            .expect("retained, not silently projected");
        let wire = postcard::to_allocvec(&store).expect("encode store");
        let decoded: AuthoredRuleStore = postcard::from_bytes(&wire).expect("validate store");
        assert_eq!(decoded, store);
    }

    #[test]
    fn reference_roster_preserves_order_duplicates_and_early_error() {
        let node: AuthoredNode = AuthoredNode::Rule(AuthoredRule {
            source_body_present: crate::SourceObservation::Unavailable,
            explicit_fold: crate::SourceObservation::Unavailable,
            label: AuthoredNameId(1),
            category: AuthoredNameId(1),
            term_context: Some(AuthoredParamsId(5)),
            syntax_pattern: Some(AuthoredSyntaxId(6)),
            items: vec![AuthoredLegacyItem::Binder { category: AuthoredNameId(0) }],
        });
        let mut visited = Vec::new();
        node.try_for_each_reference(|tag, index| {
            visited.push((tag, index));
            Ok::<_, ()>(())
        })
        .expect("collect shallow references");
        assert_eq!(
            visited,
            vec![
                (AuthoredNodeTag::Name, 1),
                (AuthoredNodeTag::Name, 1),
                (AuthoredNodeTag::Params, 5),
                (AuthoredNodeTag::Syntax, 6),
                (AuthoredNodeTag::Name, 0),
            ]
        );
        let mut calls = 0;
        assert_eq!(
            node.try_for_each_reference(|_, _| {
                calls += 1;
                Err::<(), _>("stop")
            }),
            Err("stop")
        );
        assert_eq!(calls, 1);
    }

    #[test]
    fn index_boundary_does_not_wrap() {
        assert_eq!(checked_index(u32::MAX as usize), Ok(u32::MAX));
        if let Some(over) = (u32::MAX as usize).checked_add(1) {
            assert_eq!(checked_index(over), Err(AuthoredStoreError::IndexOverflow));
        }
    }

    #[test]
    fn deeply_nested_owned_graph_lifecycle_is_stack_safe() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut store = seed();
                let mut params = AuthoredParamsId(5);
                for _ in 0..20_000 {
                    let param = AuthoredParamId(
                        store
                            .try_push(AuthoredNode::Param(AuthoredParam::Optional { params }))
                            .expect("backward optional child"),
                    );
                    params = AuthoredParamsId(
                        store
                            .try_push(AuthoredNode::Params(vec![param]))
                            .expect("backward sequence child"),
                    );
                }
                store.validate().expect("linear shallow validation");
                let cloned = store.clone();
                let bytes = postcard::to_allocvec(&cloned).expect("flat encoding");
                let decoded: AuthoredRuleStore =
                    postcard::from_bytes(&bytes).expect("flat decoding");
                assert_eq!(decoded, store);
                drop((decoded, cloned, store));
            })
            .expect("small-stack thread")
            .join()
            .expect("stack-safe lifecycle");
    }
}
