//! Retained observations of the original generated token-to-kind arms.
//!
//! These are populated at frontend token append sites, never inferred from a
//! token's display name or regex. Missing rows remain unavailable. They are
//! grammar data, not proof that an arbitrary serialized table came from the
//! original frontend. Admission and source correspondence are separate duties.

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WpdaTokenObservation {
    Eof,
    Ident,
    Integer,
    IntegerLit(String),
    RationalLit(String),
    FixedPointLit(String),
    Float,
    True,
    False,
    BooleanLit,
    StringLit,
    Fixed(String),
    Dollar,
    DoubleDollar,
    Custom(String),
    /// Original generated Boolean accept payload: `text == "true"`, followed
    /// by the selected token_to_kind Boolean(true)/Boolean(false) arms.
    BooleanText,
}
