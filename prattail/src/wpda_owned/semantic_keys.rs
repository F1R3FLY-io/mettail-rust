//! Borrowed owned-value observations for the original semantic visitor.
//!
//! The roster admits the non-evaluating, non-folded source profile and original
//! constructor/field order. Syntax is therefore the same parse-time carrier
//! observed by the generated visitor. Span and production bookkeeping are not
//! encoded. Transparent rows are unranked, preserving the admitted precedence
//! observations when the original variable/projection quotient merges them.
//!
//! A session with structural holes retains the original no-key/push-all hook:
//! no generated AST encoder for a hole is invented. Missing profile support is
//! decided before key construction. Construction errors always remain Err.
//! The portable DynamicValue key/serialization APIs are never called.

use super::actions::OwnedTerm;
use super::semantic_roster::{self, OwnedSemanticRoster, SemanticFieldKind};
use super::source::OwnedTokenSource;
use crate::wpda_rule_analysis::authored_descriptors::OwnedWpdaDescriptors;
use mettail_grammar_core::{CategoryId, CollectionKind, DynamicValue, NativeKind};
use mettail_semantic_key::visitor::{self, ComposingSemanticSink, SemanticSink};
use mettail_semantic_key::{
    ContentKey, ContentKeyCache, ContentKeyCacheError, ContentKeyNodeIdentity, SemanticKeyBuilder,
};
use std::any::Any;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

pub(super) struct OwnedSemanticKeys {
    roster: OwnedSemanticRoster,
}

enum Task<'value> {
    Node {
        value: &'value DynamicValue,
        category: CategoryId,
    },
    Length(usize),
    Finish {
        identity: ContentKeyNodeIdentity,
        cacheable: bool,
    },
}

impl OwnedSemanticKeys {
    pub(super) fn new<P>(
        source: &OwnedTokenSource<'_, '_, '_, '_>,
        descriptors: &OwnedWpdaDescriptors<P>,
    ) -> Option<Self> {
        // Availability, not a failed-key fallback. The source already owns this
        // finite node roster; no text assembly or extra lexing is performed.
        if source
            .session()
            .nodes()
            .any(|(position, _)| source.session().hole_at(position.offset).is_some())
        {
            return None;
        }
        semantic_roster::derive(source.session().grammar(), descriptors)
            .map(|roster| Self { roster })
    }

    pub(super) fn content_key(
        &self,
        term: &Arc<dyn Any + Send + Sync>,
        cache: &mut ContentKeyCache,
    ) -> Result<Option<ContentKey>, ContentKeyCacheError> {
        let Ok(owner) = term.clone().downcast::<OwnedTerm>() else {
            return Ok(None);
        };
        let category = self
            .roster
            .categories
            .get(usize::from(owner.category))
            .ok_or(ContentKeyCacheError::ConstructionInvariant)?
            .category;
        let mut transaction = cache.transaction_for_root(owner.clone());
        // SAFETY: tasks borrow only immutable syntax descendants of owner.
        // Each physical value has one source-checked category/field observation;
        // the transaction retains owner through every cached identity's life.
        let mut sink = unsafe { ComposingSemanticSink::new(&mut transaction) };
        self.walk(&owner.syntax, category, &mut sink)?;
        let term_key = sink.into_result()?;
        transaction.commit()?;
        // Original generated WpdaEngine root framing, after category key commit.
        let mut builder = SemanticKeyBuilder::with_max_bytes(cache.max_key_bytes());
        builder.write_u16(owner.category);
        builder.push_key(term_key);
        Ok(Some(builder.into_key()?))
    }

    fn walk<H: SemanticSink>(
        &self,
        value: &DynamicValue,
        category: CategoryId,
        state: &mut H,
    ) -> Result<(), ContentKeyCacheError> {
        let mut stack = vec![Task::Node { value, category }];
        let mut result = Ok(());
        visitor::drain(&mut stack, state, |task, stack, state| {
            if result.is_err() {
                return;
            }
            match task {
                Task::Node { value, category } => {
                    visitor::visit_node(
                        stack,
                        state,
                        true,
                        || ContentKeyNodeIdentity::of_ref(value),
                        |identity, cacheable| Task::Finish { identity, cacheable },
                        |stack, state| result = self.visit(value, category, stack, state),
                    );
                },
                Task::Length(length) => Hash::hash(&length, state),
                Task::Finish { identity, cacheable } => state.finish_node(identity, cacheable),
            }
        });
        result
    }

    #[inline(never)]
    fn visit<'value, H: SemanticSink>(
        &self,
        value: &'value DynamicValue,
        category: CategoryId,
        stack: &mut Vec<Task<'value>>,
        state: &mut H,
    ) -> Result<(), ContentKeyCacheError> {
        let invalid = ContentKeyCacheError::ConstructionInvariant;
        let declaration = self
            .roster
            .categories
            .iter()
            .find(|declaration| declaration.category == category)
            .ok_or_else(|| invalid.clone())?;
        match value {
            DynamicValue::Term(term) => {
                if term.category != category {
                    return Err(invalid);
                }
                let constructor = self
                    .roster
                    .constructors
                    .get(&(category, term.constructor))
                    .ok_or_else(|| invalid.clone())?;
                if constructor.fields.len() != term.fields.len() {
                    return Err(invalid);
                }
                if constructor.transparent {
                    let ([field], [value]) =
                        (constructor.fields.as_slice(), term.fields.as_slice())
                    else {
                        return Err(invalid);
                    };
                    if !matches!(field.kind, SemanticFieldKind::Term) {
                        return Err(invalid);
                    }
                    visitor::transparent(stack, || Task::Node { value, category: field.category });
                } else {
                    visitor::tagged(stack, state, constructor.local_tag, |stack, _| {
                        for (field, value) in constructor.fields.iter().zip(&term.fields).rev() {
                            match field.kind {
                                SemanticFieldKind::Term => {
                                    stack.push(Task::Node { value, category: field.category });
                                },
                                SemanticFieldKind::OrderedList => {
                                    let DynamicValue::Collection {
                                        kind: CollectionKind::List,
                                        entries,
                                    } = value
                                    else {
                                        return Err(invalid.clone());
                                    };
                                    visitor::ordered(
                                        stack,
                                        entries.iter(),
                                        |value| Task::Node { value, category: field.category },
                                        || entries.len(),
                                        Task::Length,
                                    );
                                },
                            }
                        }
                        Ok(())
                    })?;
                }
            },
            DynamicValue::NativeVariable { category: actual, variable }
                if *actual == category && declaration.variable =>
            {
                visitor::variable(state, |state| {
                    visitor::free_variable(state, || variable.pretty_name.as_deref())
                });
            },
            DynamicValue::Text(value) if declaration.native == Some(NativeKind::Str) => {
                visitor::literal(state, declaration.literal_tag.ok_or(invalid)?, value);
            },
            DynamicValue::Boolean(value) if declaration.native == Some(NativeKind::Bool) => {
                visitor::literal(state, declaration.literal_tag.ok_or(invalid)?, value);
            },
            DynamicValue::Integer(value)
                if declaration.native.is_some_and(NativeKind::is_integer)
                    && declaration.literal_tag.is_some() =>
            {
                visitor::numeric(state, 0xFE, || {
                    num_bigint::BigInt::from(*value).to_signed_bytes_le()
                });
            },
            _ => return Err(invalid),
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::semantic_roster::{SemanticCategory, SemanticConstructor, SemanticField};
    use super::*;
    use mettail_grammar_core::{ConstructorId, DynamicTerm, SourceSpan};
    use mettail_semantic_key::FramedSemanticKeyHasher;

    #[test]
    fn borrowed_variable_projection_uses_original_bytes_and_keeps_category_frame() {
        let keys = OwnedSemanticKeys {
            roster: OwnedSemanticRoster {
                categories: vec![
                    SemanticCategory {
                        category: CategoryId(0),
                        native: None,
                        literal_tag: None,
                        variable: true,
                    },
                    SemanticCategory {
                        category: CategoryId(1),
                        native: Some(NativeKind::Str),
                        literal_tag: Some(1),
                        variable: true,
                    },
                ],
                constructors: [(
                    (CategoryId(0), ConstructorId(0)),
                    SemanticConstructor {
                        local_tag: 0,
                        transparent: true,
                        fields: vec![SemanticField {
                            category: CategoryId(1),
                            kind: SemanticFieldKind::Term,
                        }],
                    },
                )]
                .into_iter()
                .collect(),
            },
        };
        let variable = mettail_grammar_core::native_variable::get_or_create_var("a");
        let leaf = |category| DynamicValue::NativeVariable { category, variable: variable.clone() };
        let carrier = |category, syntax: DynamicValue| -> Arc<dyn Any + Send + Sync> {
            Arc::new(OwnedTerm {
                category,
                production: None,
                value: syntax.clone(),
                syntax,
                span: SourceSpan { start: 0, end: 1 },
            })
        };
        let direct = carrier(0, leaf(CategoryId(0)));
        let projected = carrier(
            0,
            DynamicValue::Term(Box::new(DynamicTerm {
                category: CategoryId(0),
                constructor: ConstructorId(0),
                fields: vec![leaf(CategoryId(1))],
                span: SourceSpan { start: 0, end: 1 },
            })),
        );
        let scalar = carrier(1, leaf(CategoryId(1)));
        let mut cache = ContentKeyCache::default();
        let direct_key = keys
            .content_key(&direct, &mut cache)
            .expect("bounded direct key")
            .expect("admitted direct variable");
        assert_eq!(
            direct_key,
            keys.content_key(&projected, &mut cache)
                .expect("bounded projected key")
                .expect("admitted transparent projection")
        );
        assert_ne!(
            direct_key,
            keys.content_key(&scalar, &mut cache)
                .expect("bounded scalar key")
                .expect("admitted scalar variable")
        );

        // The original generated free-variable write body, with its root frame.
        let mut flat = FramedSemanticKeyHasher::default();
        flat.write_u16(0);
        flat.write_u8(0xFB);
        flat.write_u8(0);
        flat.write_u8(1);
        Hash::hash("a", &mut flat);
        assert_eq!(direct_key.as_bytes(), flat.into_key());

        let mut no_entries = ContentKeyCache::with_max_entries(0);
        assert!(matches!(
            keys.content_key(&direct, &mut no_entries),
            Err(ContentKeyCacheError::ResourceExhausted { limit: 0, .. })
        ));
        let mut no_bytes = ContentKeyCache::with_limits(64, 0);
        assert!(matches!(
            keys.content_key(&direct, &mut no_bytes),
            Err(ContentKeyCacheError::KeyBytesExhausted { limit: 0, .. })
        ));
    }
}
