//! Shallow existing-reader adapters over the retained authored-rule arena.
//!
//! Construction validates the immutable store and rejects keyed PathMap types,
//! which the original borrowed type observation cannot represent. No syntax is
//! parsed, normalized, reconstructed, or recursively projected. The original
//! declaration/syntax algorithms remain in their existing shared modules.
//!
//! `AuthoredRuleStoreProjection.v` proves the storage/read boundary, not source
//! capture, classifier arithmetic admission, callback lawfulness, or runtime
//! image admission. Callers must satisfy those additional boundaries separately.
//! Every handle passed to a reader method must belong to this reader's store and
//! have its declared tag, as required by the existing reader traits.

use super::binder::optional::{
    BinderSyntaxObservation, BinderSyntaxReader, OptionalOperationObservation,
};
use super::binder::rule::{BinderRuleReader, BinderTypeObservation, MapZipObservation};
use super::binder::term_param::{TermParamObservation, TermParamReader};
use mettail_ast::grammar::DelimitedRegionKind;
use mettail_ast::types::CollectionType;
use mettail_grammar_core::{
    AuthoredDelimitedRegionKind, AuthoredName, AuthoredNameId, AuthoredNamesId, AuthoredNode,
    AuthoredOperation, AuthoredOperationId, AuthoredParam, AuthoredParamId, AuthoredParamsId,
    AuthoredRule, AuthoredRuleId, AuthoredRuleStore, AuthoredStoreError, AuthoredSyntax,
    AuthoredSyntaxId, AuthoredType, AuthoredTypeId, CollectionKind,
};
use std::fmt;

/// Borrowed spelling and source equality class, not arena-occurrence equality.
#[derive(Clone, Copy, Debug)]
pub struct AuthoredNameRef<'store>(&'store AuthoredName);

impl fmt::Display for AuthoredNameRef<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0.spelling)
    }
}

/// Failure to expose an owned store through the original shallow observations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthoredReaderError {
    InvalidStore(AuthoredStoreError),
    KeyedPathMap { type_id: AuthoredTypeId },
}

impl fmt::Display for AuthoredReaderError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidStore(error) => write!(formatter, "invalid authored-rule store: {error}"),
            Self::KeyedPathMap { type_id } => write!(
                formatter,
                "authored keyed PathMap type at index {} has no original type-reader observation",
                type_id.0,
            ),
        }
    }
}

impl std::error::Error for AuthoredReaderError {}

/// Immutable validated borrowing of one owned arena. This is not parser admission.
pub struct AuthoredRuleReader<'store> {
    store: &'store AuthoredRuleStore,
}

impl<'store> AuthoredRuleReader<'store> {
    pub fn new(store: &'store AuthoredRuleStore) -> Result<Self, AuthoredReaderError> {
        store
            .validate()
            .map_err(AuthoredReaderError::InvalidStore)?;
        for index in 0..store.len() {
            let index = u32::try_from(index).expect("validated authored node indices fit u32");
            if matches!(
                store.get(index),
                Some(AuthoredNode::Type(AuthoredType::KeyedPathMap { .. }))
            ) {
                return Err(AuthoredReaderError::KeyedPathMap { type_id: AuthoredTypeId(index) });
            }
        }
        Ok(Self { store })
    }

    fn name(&self, id: AuthoredNameId) -> AuthoredNameRef<'store> {
        match self.store.get(id.0) {
            Some(AuthoredNode::Name(name)) => AuthoredNameRef(name),
            _ => panic!("authored name handle must belong to this validated reader"),
        }
    }

    fn params(&self, id: AuthoredParamsId) -> &'store [AuthoredParamId] {
        match self.store.get(id.0) {
            Some(AuthoredNode::Params(params)) => params,
            _ => panic!("authored parameter-sequence handle must belong to this validated reader"),
        }
    }

    fn syntax(&self, id: AuthoredSyntaxId) -> &'store [AuthoredSyntax] {
        match self.store.get(id.0) {
            Some(AuthoredNode::Syntax(syntax)) => syntax,
            _ => panic!("authored syntax-sequence handle must belong to this validated reader"),
        }
    }

    fn op(&self, id: AuthoredOperationId) -> &'store AuthoredOperation {
        match self.store.get(id.0) {
            Some(AuthoredNode::Operation(operation)) => operation,
            _ => panic!("authored operation handle must belong to this validated reader"),
        }
    }

    fn rule(&self, id: AuthoredRuleId) -> &'store AuthoredRule {
        match self.store.get(id.0) {
            Some(AuthoredNode::Rule(rule)) => rule,
            _ => panic!("authored rule handle must belong to this validated reader"),
        }
    }

    fn names(&self, id: AuthoredNamesId) -> &'store [AuthoredNameId] {
        match self.store.get(id.0) {
            Some(AuthoredNode::Names(names)) => names,
            _ => panic!("authored name-sequence handle must belong to this validated reader"),
        }
    }
}

/// Only a finite discriminator mapping; no type AST is constructed.
fn collection_kind(kind: CollectionKind) -> &'static CollectionType {
    match kind {
        CollectionKind::Bag => &CollectionType::HashBag,
        CollectionKind::Set => &CollectionType::HashSet,
        CollectionKind::List => &CollectionType::Vec,
        CollectionKind::Map => &CollectionType::HashMap,
        CollectionKind::PathMap => &CollectionType::PathMap,
    }
}

impl<'store> TermParamReader<'store> for AuthoredRuleReader<'store> {
    type Parameters = AuthoredParamsId;
    type Param = AuthoredParamId;
    type Name = AuthoredNameRef<'store>;
    type Type = AuthoredTypeId;

    fn params_len(&self, params: Self::Parameters) -> usize {
        self.params(params).len()
    }

    fn param_at(&self, params: Self::Parameters, index: usize) -> Option<Self::Param> {
        self.params(params).get(index).copied()
    }

    fn param(
        &self,
        param: Self::Param,
    ) -> TermParamObservation<Self::Name, Self::Parameters, Self::Type> {
        let param = match self.store.get(param.0) {
            Some(AuthoredNode::Param(param)) => param,
            _ => panic!("authored parameter handle must belong to this validated reader"),
        };
        match *param {
            AuthoredParam::Simple { name, ty } => {
                TermParamObservation::Simple { name: self.name(name), ty }
            },
            AuthoredParam::GuardBody { name } => {
                TermParamObservation::GuardBody { name: self.name(name) }
            },
            AuthoredParam::Abstraction { binder, body, ty } => TermParamObservation::Abstraction {
                binder: self.name(binder),
                body: self.name(body),
                ty,
            },
            AuthoredParam::MultiAbstraction { binder, body, ty } => {
                TermParamObservation::MultiAbstraction {
                    binder: self.name(binder),
                    body: self.name(body),
                    ty,
                }
            },
            AuthoredParam::Optional { params } => TermParamObservation::Optional { params },
        }
    }
}

impl<'store> BinderSyntaxReader<'store> for AuthoredRuleReader<'store> {
    type Sequence = AuthoredSyntaxId;
    type Name = AuthoredNameRef<'store>;
    type Operation = AuthoredOperationId;

    fn sequence_len(&self, sequence: Self::Sequence) -> usize {
        self.syntax(sequence).len()
    }

    fn at(
        &self,
        sequence: Self::Sequence,
        index: usize,
    ) -> Option<BinderSyntaxObservation<'store, Self::Name, Self::Operation>> {
        Some(match self.syntax(sequence).get(index)? {
            AuthoredSyntax::Literal(text) => BinderSyntaxObservation::Literal(text),
            AuthoredSyntax::Param(name) => BinderSyntaxObservation::Param(self.name(*name)),
            AuthoredSyntax::TokenKind { name, bind } => BinderSyntaxObservation::TokenKind {
                name: self.name(*name),
                bind: bind.map(|name| self.name(name)),
            },
            AuthoredSyntax::GuestBody { open, close, bind, kind } => {
                BinderSyntaxObservation::GuestBody {
                    open: self.name(*open),
                    close: self.name(*close),
                    bind: self.name(*bind),
                    kind: match kind {
                        AuthoredDelimitedRegionKind::Flt => DelimitedRegionKind::Flt,
                    },
                }
            },
            AuthoredSyntax::Op(operation) => BinderSyntaxObservation::Op(*operation),
        })
    }

    fn operation(
        &self,
        operation: Self::Operation,
    ) -> OptionalOperationObservation<'store, Self::Name, Self::Sequence, Self::Operation> {
        match self.op(operation) {
            AuthoredOperation::Opt { inner } => OptionalOperationObservation::Opt { inner: *inner },
            AuthoredOperation::Sep { collection, separator, source } => {
                OptionalOperationObservation::Sep {
                    collection: self.name(*collection),
                    separator,
                    source: *source,
                }
            },
            _ => OptionalOperationObservation::Other(operation),
        }
    }
}

impl<'store> BinderRuleReader<'store> for AuthoredRuleReader<'store> {
    type Rule = AuthoredRuleId;
    type Names = AuthoredNamesId;

    fn term_context(&self, rule: Self::Rule) -> Option<Self::Parameters> {
        self.rule(rule).term_context
    }

    fn syntax_pattern(&self, rule: Self::Rule) -> Option<Self::Sequence> {
        self.rule(rule).syntax_pattern
    }

    fn label(&self, rule: Self::Rule) -> AuthoredNameRef<'store> {
        self.name(self.rule(rule).label)
    }

    fn category(&self, rule: Self::Rule) -> AuthoredNameRef<'store> {
        self.name(self.rule(rule).category)
    }

    fn ty(
        &self,
        ty: Self::Type,
    ) -> BinderTypeObservation<'store, AuthoredNameRef<'store>, Self::Type> {
        match self.store.get(ty.0) {
            Some(AuthoredNode::Type(AuthoredType::Base(name))) => {
                BinderTypeObservation::Base(self.name(*name))
            },
            Some(AuthoredNode::Type(AuthoredType::Collection { kind, element })) => {
                BinderTypeObservation::Collection {
                    coll_type: collection_kind(*kind),
                    element: *element,
                }
            },
            Some(AuthoredNode::Type(AuthoredType::Map { key, value })) => {
                BinderTypeObservation::Map { key: *key, value: *value }
            },
            Some(AuthoredNode::Type(AuthoredType::Arrow { codomain, .. })) => {
                BinderTypeObservation::Arrow { codomain: *codomain }
            },
            Some(AuthoredNode::Type(
                AuthoredType::Unsupported { .. } | AuthoredType::MultiBinder { .. },
            )) => BinderTypeObservation::Other(ty),
            Some(AuthoredNode::Type(AuthoredType::KeyedPathMap { .. })) => {
                unreachable!("keyed PathMap is rejected before reader construction")
            },
            _ => panic!("authored type handle must belong to this validated reader"),
        }
    }

    fn names_len(&self, names: Self::Names) -> usize {
        self.names(names).len()
    }

    fn name_at(&self, names: Self::Names, index: usize) -> Option<AuthoredNameRef<'store>> {
        self.names(names).get(index).map(|name| self.name(*name))
    }

    fn names_equal(&self, left: AuthoredNameRef<'store>, right: AuthoredNameRef<'store>) -> bool {
        left.0.equality_class == right.0.equality_class
    }

    fn map_zip_operation(
        &self,
        operation: Self::Operation,
    ) -> MapZipObservation<AuthoredNameRef<'store>, Self::Names, Self::Sequence, Self::Operation>
    {
        match *self.op(operation) {
            AuthoredOperation::Map { source, params, body } => {
                MapZipObservation::Map { source, params, body }
            },
            AuthoredOperation::Zip { left, right } => MapZipObservation::Zip {
                left: self.name(left),
                right: self.name(right),
            },
            _ => MapZipObservation::Other(operation),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wpda_rule_analysis::binder::term_param::TermParamLeaves;

    fn push(store: &mut AuthoredRuleStore, node: AuthoredNode) -> u32 {
        store
            .try_push(node)
            .expect("backward typed fixture reference")
    }

    fn name(store: &mut AuthoredRuleStore, spelling: &str, equality_class: u32) -> AuthoredNameId {
        AuthoredNameId(push(
            store,
            AuthoredNode::Name(AuthoredName {
                spelling: spelling.into(),
                equality_class,
            }),
        ))
    }

    #[test]
    fn independent_context_and_syntax_presence_survive_empty_sequences() {
        let mut store = AuthoredRuleStore::new();
        let label = name(&mut store, "Rule", 0);
        let category = name(&mut store, "Expr", 1);
        let params = AuthoredParamsId(push(&mut store, AuthoredNode::Params(Vec::new())));
        let syntax = AuthoredSyntaxId(push(&mut store, AuthoredNode::Syntax(Vec::new())));
        let mut rules = Vec::new();
        for tc in [None, Some(params)] {
            for sp in [None, Some(syntax)] {
                let rule = AuthoredRuleId(push(
                    &mut store,
                    AuthoredNode::Rule(AuthoredRule {
                        label,
                        category,
                        term_context: tc,
                        syntax_pattern: sp,
                        items: Vec::new(),
                    }),
                ));
                rules.push((rule, tc, sp));
            }
        }
        let reader = AuthoredRuleReader::new(&store).expect("representable store");
        for (rule, tc, sp) in rules {
            assert_eq!(reader.term_context(rule), tc);
            assert_eq!(reader.syntax_pattern(rule), sp);
            assert_eq!(reader.label(rule).to_string(), "Rule");
            assert_eq!(reader.category(rule).to_string(), "Expr");
        }
        assert_eq!(reader.params_len(params), 0);
        assert_eq!(reader.param_at(params, 0), None);
        assert_eq!(reader.sequence_len(syntax), 0);
        assert!(reader.at(syntax, 0).is_none());
    }

    #[test]
    fn name_equality_uses_source_class_not_occurrence_or_spelling() {
        let mut store = AuthoredRuleStore::new();
        let first = name(&mut store, "x", 7);
        let unequal = name(&mut store, "x", 8);
        let equal_occurrence = name(&mut store, "x", 7);
        let names = AuthoredNamesId(push(
            &mut store,
            AuthoredNode::Names(vec![first, unequal, equal_occurrence, first]),
        ));
        let reader = AuthoredRuleReader::new(&store).expect("representable names");
        let first_read = reader.name_at(names, 0).expect("first name");
        let unequal_read = reader.name_at(names, 1).expect("second name");
        let equal_read = reader.name_at(names, 2).expect("third name");
        assert_eq!(reader.names_len(names), 4);
        assert!(reader.name_at(names, 4).is_none());
        assert_eq!(first_read.to_string(), unequal_read.to_string());
        assert!(!reader.names_equal(first_read, unequal_read));
        assert!(reader.names_equal(first_read, equal_read));
        assert!(!std::ptr::eq(first_read.0, equal_read.0));
        assert!(std::ptr::eq(
            first_read.0,
            reader.name_at(names, 3).expect("duplicate occurrence").0
        ));
    }

    #[test]
    fn parameter_variants_and_existing_leaf_worklist_preserve_order_and_duplicates() {
        let mut store = AuthoredRuleStore::new();
        let x = name(&mut store, "x", 0);
        let body = name(&mut store, "body", 1);
        let cat = name(&mut store, "Expr", 2);
        let ty = AuthoredTypeId(push(&mut store, AuthoredNode::Type(AuthoredType::Base(cat))));
        let simple = AuthoredParamId(push(
            &mut store,
            AuthoredNode::Param(AuthoredParam::Simple { name: x, ty }),
        ));
        let guard = AuthoredParamId(push(
            &mut store,
            AuthoredNode::Param(AuthoredParam::GuardBody { name: body }),
        ));
        let abstraction = AuthoredParamId(push(
            &mut store,
            AuthoredNode::Param(AuthoredParam::Abstraction { binder: x, body, ty }),
        ));
        let multi = AuthoredParamId(push(
            &mut store,
            AuthoredNode::Param(AuthoredParam::MultiAbstraction { binder: x, body, ty }),
        ));
        let children =
            AuthoredParamsId(push(&mut store, AuthoredNode::Params(vec![simple, simple])));
        let optional = AuthoredParamId(push(
            &mut store,
            AuthoredNode::Param(AuthoredParam::Optional { params: children }),
        ));
        let params = AuthoredParamsId(push(
            &mut store,
            AuthoredNode::Params(vec![guard, optional, abstraction, multi, simple]),
        ));
        let reader = AuthoredRuleReader::new(&store).expect("representable parameters");
        assert_eq!(reader.params_len(params), 5);
        assert_eq!(reader.param_at(params, 1), Some(optional));
        assert_eq!(reader.param_at(params, 5), None);
        assert!(
            matches!(reader.param(simple), TermParamObservation::Simple { name, ty: actual } if name.to_string() == "x" && actual == ty)
        );
        assert!(
            matches!(reader.param(guard), TermParamObservation::GuardBody { name } if name.to_string() == "body")
        );
        assert!(
            matches!(reader.param(abstraction), TermParamObservation::Abstraction { binder, body, ty: actual } if binder.to_string() == "x" && body.to_string() == "body" && actual == ty)
        );
        assert!(
            matches!(reader.param(multi), TermParamObservation::MultiAbstraction { binder, body, ty: actual } if binder.to_string() == "x" && body.to_string() == "body" && actual == ty)
        );
        assert!(
            matches!(reader.param(optional), TermParamObservation::Optional { params: actual } if actual == children)
        );
        let leaves: Vec<_> = TermParamLeaves::new(&reader, params, false)
            .map(|leaf| (leaf.kind.param(), leaf.is_optional))
            .collect();
        assert_eq!(
            leaves,
            vec![
                (guard, false),
                (simple, true),
                (simple, true),
                (abstraction, false),
                (multi, false),
                (simple, false)
            ]
        );
    }

    #[test]
    fn syntax_fields_are_borrowed_with_guest_closer_and_operation_identity() {
        let mut store = AuthoredRuleStore::new();
        let open = name(&mut store, "Open", 0);
        let close = name(&mut store, "Close", 1);
        let bind = name(&mut store, "payload", 2);
        let op = AuthoredOperationId(push(
            &mut store,
            AuthoredNode::Operation(AuthoredOperation::Unsupported { tag: 73 }),
        ));
        let syntax = AuthoredSyntaxId(push(
            &mut store,
            AuthoredNode::Syntax(vec![
                AuthoredSyntax::Literal("literal".into()),
                AuthoredSyntax::Param(bind),
                AuthoredSyntax::TokenKind { name: open, bind: None },
                AuthoredSyntax::TokenKind { name: open, bind: Some(bind) },
                AuthoredSyntax::GuestBody {
                    open,
                    close,
                    bind,
                    kind: AuthoredDelimitedRegionKind::Flt,
                },
                AuthoredSyntax::Op(op),
            ]),
        ));
        let reader = AuthoredRuleReader::new(&store).expect("representable syntax");
        assert_eq!(reader.sequence_len(syntax), 6);
        assert!(reader.at(syntax, 6).is_none());
        let BinderSyntaxObservation::Literal(text) = reader.at(syntax, 0).expect("literal") else {
            panic!("literal shape")
        };
        let AuthoredSyntax::Literal(stored) = &reader.syntax(syntax)[0] else {
            panic!("stored literal")
        };
        assert_eq!(text.as_ptr(), stored.as_ptr());
        assert!(
            matches!(reader.at(syntax, 1), Some(BinderSyntaxObservation::Param(name)) if name.to_string() == "payload")
        );
        assert!(
            matches!(reader.at(syntax, 2), Some(BinderSyntaxObservation::TokenKind { name, bind: None }) if name.to_string() == "Open")
        );
        assert!(
            matches!(reader.at(syntax, 3), Some(BinderSyntaxObservation::TokenKind { name, bind: Some(bind) }) if name.to_string() == "Open" && bind.to_string() == "payload")
        );
        assert!(
            matches!(reader.at(syntax, 4), Some(BinderSyntaxObservation::GuestBody { open, close, bind, kind: DelimitedRegionKind::Flt }) if open.to_string() == "Open" && close.to_string() == "Close" && bind.to_string() == "payload")
        );
        assert!(
            matches!(reader.at(syntax, 5), Some(BinderSyntaxObservation::Op(actual)) if actual == op)
        );
    }

    #[test]
    fn operation_views_preserve_source_aliases_and_opaque_handles() {
        let mut store = AuthoredRuleStore::new();
        let left = name(&mut store, "left", 0);
        let right = name(&mut store, "right", 1);
        let aliases =
            AuthoredNamesId(push(&mut store, AuthoredNode::Names(vec![right, left, right])));
        let body = AuthoredSyntaxId(push(&mut store, AuthoredNode::Syntax(Vec::new())));
        let zip = AuthoredOperationId(push(
            &mut store,
            AuthoredNode::Operation(AuthoredOperation::Zip { left, right }),
        ));
        let map = AuthoredOperationId(push(
            &mut store,
            AuthoredNode::Operation(AuthoredOperation::Map { source: zip, params: aliases, body }),
        ));
        let sep = AuthoredOperationId(push(
            &mut store,
            AuthoredNode::Operation(AuthoredOperation::Sep {
                collection: left,
                separator: ",".into(),
                source: Some(map),
            }),
        ));
        let plain = AuthoredOperationId(push(
            &mut store,
            AuthoredNode::Operation(AuthoredOperation::Sep {
                collection: right,
                separator: ";".into(),
                source: None,
            }),
        ));
        let opt = AuthoredOperationId(push(
            &mut store,
            AuthoredNode::Operation(AuthoredOperation::Opt { inner: body }),
        ));
        let unsupported = AuthoredOperationId(push(
            &mut store,
            AuthoredNode::Operation(AuthoredOperation::Unsupported { tag: 42 }),
        ));
        let reader = AuthoredRuleReader::new(&store).expect("representable operations");
        assert!(
            matches!(reader.operation(opt), OptionalOperationObservation::Opt { inner } if inner == body)
        );
        assert!(
            matches!(reader.operation(sep), OptionalOperationObservation::Sep { collection, separator: ",", source: Some(source) } if collection.to_string() == "left" && source == map)
        );
        assert!(
            matches!(reader.operation(plain), OptionalOperationObservation::Sep { collection, separator: ";", source: None } if collection.to_string() == "right")
        );
        for original in [map, zip, unsupported] {
            assert!(
                matches!(reader.operation(original), OptionalOperationObservation::Other(actual) if actual == original)
            );
        }
        assert!(
            matches!(reader.map_zip_operation(map), MapZipObservation::Map { source, params, body: actual } if source == zip && params == aliases && actual == body)
        );
        assert!(
            matches!(reader.map_zip_operation(zip), MapZipObservation::Zip { left, right } if left.to_string() == "left" && right.to_string() == "right")
        );
        for original in [opt, sep, plain, unsupported] {
            assert!(
                matches!(reader.map_zip_operation(original), MapZipObservation::Other(actual) if actual == original)
            );
        }
        assert_eq!(
            (0..reader.names_len(aliases))
                .map(|i| reader.name_at(aliases, i).expect("alias").to_string())
                .collect::<Vec<_>>(),
            vec!["right", "left", "right"]
        );
    }

    #[test]
    fn type_constructors_remain_distinct_and_keyed_pathmap_is_refused() {
        let mut store = AuthoredRuleStore::new();
        let cat = name(&mut store, "Expr", 0);
        let base = AuthoredTypeId(push(&mut store, AuthoredNode::Type(AuthoredType::Base(cat))));
        let arrow = AuthoredTypeId(push(
            &mut store,
            AuthoredNode::Type(AuthoredType::Arrow { domain: base, codomain: base }),
        ));
        let map = AuthoredTypeId(push(
            &mut store,
            AuthoredNode::Type(AuthoredType::Map { key: base, value: arrow }),
        ));
        let unsupported = AuthoredTypeId(push(
            &mut store,
            AuthoredNode::Type(AuthoredType::Unsupported { tag: 67 }),
        ));
        let multi = AuthoredTypeId(push(
            &mut store,
            AuthoredNode::Type(AuthoredType::MultiBinder { inner: arrow }),
        ));
        let mut collections = Vec::new();
        for kind in [
            CollectionKind::Bag,
            CollectionKind::Set,
            CollectionKind::List,
            CollectionKind::Map,
            CollectionKind::PathMap,
        ] {
            let id = AuthoredTypeId(push(
                &mut store,
                AuthoredNode::Type(AuthoredType::Collection { kind, element: base }),
            ));
            collections.push((id, kind));
        }
        {
            let reader = AuthoredRuleReader::new(&store).expect("original type observations");
            assert!(
                matches!(reader.ty(base), BinderTypeObservation::Base(name) if name.to_string() == "Expr")
            );
            assert!(
                matches!(reader.ty(arrow), BinderTypeObservation::Arrow { codomain } if codomain == base)
            );
            assert!(
                matches!(reader.ty(map), BinderTypeObservation::Map { key, value } if key == base && value == arrow)
            );
            assert!(
                matches!(reader.ty(unsupported), BinderTypeObservation::Other(original) if original == unsupported)
            );
            assert!(
                matches!(reader.ty(multi), BinderTypeObservation::Other(original) if original == multi)
            );
            for (id, kind) in collections {
                assert!(
                    matches!(reader.ty(id), BinderTypeObservation::Collection { coll_type, element } if coll_type == collection_kind(kind) && element == base)
                );
            }
        }
        let keyed = AuthoredTypeId(push(
            &mut store,
            AuthoredNode::Type(AuthoredType::KeyedPathMap { key: base, value: arrow }),
        ));
        assert!(
            matches!(AuthoredRuleReader::new(&store), Err(AuthoredReaderError::KeyedPathMap { type_id }) if type_id == keyed)
        );
    }
}
