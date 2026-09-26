//! Owned observations at the original semantic-action selection sites.
//! The classifier sequence is `collect_action_arms_by_category`'s original
//! binder, collection, atomic, infix priority. No rule syntax is reclassified.

use super::atomic::AtomicDescriptor;
use super::authored_collection::derive_authored_collection;
use super::authored_descriptors::OwnedWpdaDescriptors;
use super::authored_prefix::{with_authored_context, AuthoredPrefixError};
use super::binder::ActionArgKind;
use mettail_grammar_core::{CategoryId, CollectionKind, GrammarCoreV1};
use std::convert::Infallible;

#[derive(Debug)]
pub enum AuthoredActionShape {
    /// One selected token, through the existing literal decoder binding.
    Literal,
    /// The original synthetic VarRule, with its native identity worker.
    Variable,
    /// Category names in the original action's operand order.
    Inputs(Vec<AuthoredActionInput>),
    /// The original keyword constructor takes one ANY_CAT argument and
    /// ignores it; its reduction has no semantic inputs.
    Keyword,
    Unsupported(&'static str),
}

#[derive(Debug)]
pub enum AuthoredActionInput {
    Term(String),
    Collection { category: String, kind: CollectionKind },
}

/// Retain the declaration producer's explicit category binding. Final Core
/// category names are not used as a substitute for this source relation.
pub fn authored_action_categories<P>(
    core: &GrammarCoreV1,
    descriptors: &OwnedWpdaDescriptors<P>,
) -> Result<Vec<CategoryId>, AuthoredPrefixError<Infallible>> {
    let declarations = super::authored_declarations::AuthoredDeclarationReader::new(core)
        .map_err(AuthoredPrefixError::Declaration)?;
    descriptors
        .synthesis
        .categories
        .iter()
        .enumerate()
        .map(|(index, name)| {
            declarations
                .header()
                .categories
                .iter()
                .enumerate()
                .find(|(_, declaration)| {
                    declarations
                        .rule_reader()
                        .name(declaration.name)
                        .to_string()
                        == *name
                })
                .and_then(|(index, _)| declarations.category_binding(index).copied())
                .ok_or(AuthoredPrefixError::MissingCategoryBinding(index))
        })
        .collect()
}

fn collection_kind(kind: &mettail_ast::types::CollectionType) -> CollectionKind {
    use mettail_ast::types::CollectionType;
    match kind {
        CollectionType::Vec => CollectionKind::List,
        CollectionType::HashBag => CollectionKind::Bag,
        CollectionType::HashSet => CollectionKind::Set,
        CollectionType::HashMap => CollectionKind::Map,
        CollectionType::PathMap => CollectionKind::PathMap,
    }
}

/// The caller prepays the complete descriptor domain, including copies, before
/// calling this projection. Unsupported rows stay in place, never disappear.
pub fn derive_authored_action_shapes<P>(
    core: &GrammarCoreV1,
    descriptors: &OwnedWpdaDescriptors<P>,
) -> Result<Vec<Vec<AuthoredActionShape>>, AuthoredPrefixError<Infallible>> {
    with_authored_context(
        core,
        &descriptors.original_occurrences,
        &descriptors.synthesis,
        |reader, context| {
            descriptors
                .synthesis
                .per_category
                .iter()
                .map(|rules| {
                    rules
                        .iter()
                        .map(|&rule| {
                            if let Some(shape) = context.binder_shape(rule)? {
                                let mut terms = Vec::with_capacity(shape.action_args.len());
                                for arg in &shape.action_args {
                                    match arg {
                                        ActionArgKind::Term(category) => {
                                            terms.push(AuthoredActionInput::Term(category.clone()))
                                        },
                                        ActionArgKind::CollectionDrain { elem_cat, coll_kind } => {
                                            terms.push(AuthoredActionInput::Collection {
                                                category: elem_cat.clone(),
                                                kind: collection_kind(coll_kind),
                                            })
                                        },
                                        _ => {
                                            return Ok(AuthoredActionShape::Unsupported(
                                                "non-Term binder action",
                                            ))
                                        },
                                    }
                                }
                                return Ok(AuthoredActionShape::Inputs(terms));
                            }
                            if derive_authored_collection(reader.inner, rule.rule, |_, _, _| {
                                Ok::<_, Infallible>(())
                            })
                            .map_err(AuthoredPrefixError::Collection)?
                            .is_some()
                            {
                                return Ok(AuthoredActionShape::Unsupported("collection action"));
                            }
                            match context.atomic(rule)? {
                                AtomicDescriptor::LiteralInteger
                                | AtomicDescriptor::LiteralBoolean
                                | AtomicDescriptor::LiteralString
                                | AtomicDescriptor::LiteralFloat
                                | AtomicDescriptor::LiteralPatterned(_) => {
                                    return Ok(AuthoredActionShape::Literal)
                                },
                                AtomicDescriptor::VarRule { .. } => {
                                    return Ok(AuthoredActionShape::Variable)
                                },
                                AtomicDescriptor::TerminalKeyword { .. } => {
                                    return Ok(AuthoredActionShape::Keyword)
                                },
                                AtomicDescriptor::NullaryLiteralRun { .. } => {
                                    return Ok(AuthoredActionShape::Inputs(Vec::new()))
                                },
                                AtomicDescriptor::CrossCatProjection {
                                    source_cat_name, ..
                                }
                                | AtomicDescriptor::CrossCatPrefixUnary {
                                    source_cat_name, ..
                                } => {
                                    return Ok(AuthoredActionShape::Inputs(vec![
                                        AuthoredActionInput::Term(source_cat_name),
                                    ]));
                                },
                                AtomicDescriptor::NonAtomic => {},
                                _ => {
                                    return Ok(AuthoredActionShape::Unsupported(
                                        "literal/variable semantic binding",
                                    ))
                                },
                            }
                            let Some(info) = context.infix_normalized(rule)? else {
                                return Ok(AuthoredActionShape::Unsupported("no original action"));
                            };
                            let mut terms = vec![AuthoredActionInput::Term(info.category.clone())];
                            if !info.is_postfix {
                                if info.is_mixfix {
                                    for part in &info.mixfix_parts {
                                        if part.repetition.is_some() || part.capture_kind.is_some()
                                        {
                                            return Ok(AuthoredActionShape::Unsupported(
                                                "capture/repetition infix action",
                                            ));
                                        }
                                        terms.push(AuthoredActionInput::Term(
                                            part.operand_category.clone(),
                                        ));
                                    }
                                } else {
                                    terms.push(AuthoredActionInput::Term(info.category.clone()));
                                }
                            }
                            Ok(AuthoredActionShape::Inputs(terms))
                        })
                        .collect()
                })
                .collect()
        },
    )?
}
