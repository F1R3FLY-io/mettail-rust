//! Borrowed original AST observations and constructors for shared consumers.

use super::{GrammarItem, GrammarRule, TermParam};
use crate::types::{CollectionType, TypeExpr};
use mettail_grammar_core::{
    context_items::ContextItemsReader, term_param_walk::BinderPresenceReader, TermParamObservation,
    TermParamReader,
};
use syn::Ident;

/// Shallow macro-AST access for the shared original declaration worklist.
pub struct AstTermParamReader;

impl<'syntax> TermParamReader<'syntax> for AstTermParamReader {
    type Parameters = &'syntax [TermParam];
    type Param = &'syntax TermParam;
    type Name = &'syntax Ident;
    type Type = &'syntax TypeExpr;

    fn params_len(&self, params: Self::Parameters) -> usize {
        params.len()
    }

    fn param_at(&self, params: Self::Parameters, index: usize) -> Option<Self::Param> {
        params.get(index)
    }

    fn param(
        &self,
        param: Self::Param,
    ) -> TermParamObservation<Self::Name, Self::Parameters, Self::Type> {
        match param {
            TermParam::Simple { name, ty } => TermParamObservation::Simple { name, ty },
            TermParam::GuardBody { name } => TermParamObservation::GuardBody { name },
            TermParam::Abstraction { binder, body, ty } => {
                TermParamObservation::Abstraction { binder, body, ty }
            },
            TermParam::MultiAbstraction { binder, body, ty } => {
                TermParamObservation::MultiAbstraction { binder, body, ty }
            },
            TermParam::Optional { params } => TermParamObservation::Optional { params },
        }
    }
}

impl<'syntax> BinderPresenceReader<'syntax> for AstTermParamReader {
    type Rule = &'syntax GrammarRule;
    type Item = GrammarItem;

    fn context(&self, rule: Self::Rule) -> Option<Self::Parameters> {
        rule.term_context.as_deref()
    }

    fn items(&self, rule: Self::Rule) -> &'syntax [Self::Item] {
        &rule.items
    }

    fn item_is_binder(&self, item: &Self::Item) -> bool {
        matches!(item, GrammarItem::Binder { .. })
    }
}

impl<'syntax> ContextItemsReader<'syntax> for AstTermParamReader {
    type CollectionKind = &'syntax CollectionType;
    type Item = GrammarItem;

    fn base_name(&self, ty: Self::Type) -> Option<Self::Name> {
        match ty {
            TypeExpr::Base(name) => Some(name),
            _ => None,
        }
    }

    fn collection(&self, ty: Self::Type) -> Option<(Self::CollectionKind, Self::Type)> {
        match ty {
            TypeExpr::Collection { coll_type, element } => Some((coll_type, element)),
            _ => None,
        }
    }

    fn map(&self, ty: Self::Type) -> Option<(Self::Type, Self::Type)> {
        match ty {
            TypeExpr::Map { key, value } => Some((key, value)),
            _ => None,
        }
    }

    fn arrow(&self, ty: Self::Type) -> Option<(Self::Type, Self::Type)> {
        match ty {
            TypeExpr::Arrow { domain, codomain } => Some((domain, codomain)),
            _ => None,
        }
    }

    fn multi_binder(&self, ty: Self::Type) -> Option<Self::Type> {
        match ty {
            TypeExpr::MultiBinder(inner) => Some(inner),
            _ => None,
        }
    }

    fn names_equal(&self, left: Self::Name, right: Self::Name) -> bool {
        left == right
    }

    fn hash_map_kind(&self) -> Self::CollectionKind {
        &CollectionType::HashMap
    }

    fn make_nonterminal(&self, name: Self::Name) -> Self::Item {
        GrammarItem::non_terminal(name.clone())
    }

    fn make_binder(&self, name: Self::Name) -> Self::Item {
        GrammarItem::Binder { category: name.clone() }
    }

    fn make_collection(
        &self,
        kind: Self::CollectionKind,
        element: Self::Name,
        separator: &'static str,
    ) -> Self::Item {
        GrammarItem::Collection {
            coll_type: kind.clone(),
            element_type: element.clone(),
            separator: separator.to_string(),
            delimiters: None,
        }
    }
}
