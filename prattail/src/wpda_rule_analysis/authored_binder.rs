//! Owned binder derivation through the original shared classifier.
//!
//! The validated rule reader supplies its own retained declaration header;
//! no Core, source AST, or declaration reader is reconstructed. The original
//! classifier determines when declaration, guest-mode, and separator callbacks
//! run. `BinderRuleProjection.v` and `BinderNumericAdmission.v` cover that
//! worker; `AuthoredDeclarationReaderProjection.v` covers the reused guest
//! observations, and `CollectionReaderProjection.v` supplies the header and
//! first-declaration lookup correspondence.

use super::authored::AuthoredRuleReader;
use super::authored_declarations::guest_nested_open_kinds_in;
use super::binder::rule::{try_classify_binder_in, BinderRuleReader};
use super::binder::{BinderNumericError, BinderShape};
use super::collection::kv_sep_for;
use mettail_grammar_core::{AuthoredDeclarations, AuthoredRuleId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthoredBinderError<E> {
    MissingDeclarations,
    Admission(E),
    Numeric(BinderNumericError),
}

/// Derive a binder descriptor without changing structural nonmatch semantics.
///
/// The rule handle must belong to this validated reader. Admission prepays the
/// complete existing worker, its callbacks, string copies, and temporary storage
/// before any classification work. A no-accounting callback is only suitable for
/// trusted/static domains; it is not a runtime resource policy. Numeric refusal
/// is an error rather than a structural nonmatch, and never publishes a partial
/// descriptor. Physical allocation failure and panic recovery are not promised.
pub fn derive_authored_binder<'store, E>(
    reader: &AuthoredRuleReader<'store>,
    rule: AuthoredRuleId,
    admit: impl FnOnce(
        &AuthoredRuleReader<'store>,
        AuthoredRuleId,
        &'store AuthoredDeclarations,
    ) -> Result<(), E>,
) -> Result<Option<BinderShape>, AuthoredBinderError<E>> {
    let header = reader
        .declarations()
        .ok_or(AuthoredBinderError::MissingDeclarations)?;
    admit(reader, rule, header).map_err(AuthoredBinderError::Admission)?;
    try_classify_binder_in(
        reader,
        rule,
        || {
            header
                .categories
                .iter()
                .find(|declaration| {
                    reader.names_equal(reader.name(declaration.name), reader.category(rule))
                })
                .and_then(|declaration| declaration.collection.as_ref())
        },
        |open| guest_nested_open_kinds_in(reader, header, open),
        |slot_kind, declaration| {
            // Unlike a collection-literal descriptor, the binder's actual slot
            // kind decides whether a key/value separator exists. A matching
            // result declaration supplies only its optional spelling.
            kv_sep_for(slot_kind, || {
                declaration.and_then(|declaration| declaration.key_value_separator.as_deref())
            })
        },
    )
    .map_err(AuthoredBinderError::Numeric)
}
