//! Owned authored rules feed the original collection classifier directly.
//!
//! The validated reader and declaration header share one immutable arena.
//! Neither a source AST nor a second classifier is constructed. Missing source
//! declarations are an error, not evidence that no declaration matched.
//! `CollectionReaderProjection.v` models the reader, first-match lookup and
//! admission boundary; it does not supply a finite installed-compiler budget.

use super::authored::{collection_kind, AuthoredRuleReader};
use super::binder::rule::BinderRuleReader;
use super::collection::{classify_collection, kv_sep_for, CollectionShape};
use super::collection_projection::{try_project_collection_rule_in, CollectionProjectionError};
use mettail_ast::types::CollectionType;
use mettail_grammar_core::{AuthoredDeclarations, AuthoredRuleId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthoredCollectionError<E> {
    MissingDeclarations,
    Admission(E),
    Projection(CollectionProjectionError<E>),
}

/// Derive the original descriptor, preserving structural nonmatches as None.
///
/// The rule handle must belong to this validated reader, as required by its
/// existing shallow-reader contract. The caller prepays the complete projection,
/// classifier and possible declaration scan, including string copies and
/// temporary storage, in one callback before any of those operations. A callback
/// that does no accounting is suitable only for trusted/static test domains.
/// No partial descriptor is returned on error. This interface does not promise
/// recovery from physical allocator failure in the original classifier.
pub fn derive_authored_collection<'store, E>(
    reader: &AuthoredRuleReader<'store>,
    rule: AuthoredRuleId,
    admit: impl FnOnce(
        &AuthoredRuleReader<'store>,
        AuthoredRuleId,
        &'store AuthoredDeclarations,
    ) -> Result<(), E>,
) -> Result<Option<CollectionShape<CollectionType>>, AuthoredCollectionError<E>> {
    let header = reader
        .declarations()
        .ok_or(AuthoredCollectionError::MissingDeclarations)?;
    admit(reader, rule, header).map_err(AuthoredCollectionError::Admission)?;
    let view = try_project_collection_rule_in(reader, rule, |_, _| Ok::<(), E>(()))
        .map_err(AuthoredCollectionError::Projection)?;
    Ok(classify_collection(&view, || {
        // Preserve the original first matching RESULT declaration. In
        // particular a matching noncollection row hides later duplicate rows.
        // Parameter/Sep equality inside the classifier is spelling-based;
        // declaration equality here is the original captured name identity.
        header
            .categories
            .iter()
            .find(|declaration| {
                reader.names_equal(reader.name(declaration.name), reader.category(rule))
            })
            .and_then(|declaration| declaration.collection.as_ref())
            .and_then(|declaration| {
                kv_sep_for(collection_kind(declaration.kind), || {
                    declaration.key_value_separator.as_deref()
                })
            })
    }))
}

#[cfg(test)]
mod tests;
