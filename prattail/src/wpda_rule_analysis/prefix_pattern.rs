//! Source-neutral observations of the original prefix quotation sites.
//!
//! These are descriptor payloads, not another lexer or recognizer. Key equality
//! preserves original quotation equality, including the empty guard default;
//! key ordering is not a claim about Rust token formatting order. Consumers use
//! the original separate insertion-order roster. `PrefixKeyObservation.v`
//! proves the key-interface law; macro differentials check the constructors.

use super::native_first::{NativeFirstConstructors, NativePatternSite};
use super::prefix::FirstPredicate;

/// Exactly the two observations made by the original FIRST/identifier workers.
/// Implementations must preserve quotation-key equality and the original Ident
/// substring observation, not merely semantic token matching equivalence.
pub trait PrefixPatternObservation {
    type Key: Ord + Clone + Default;
    fn key(&self) -> Self::Key;
    fn mentions_ident(&self) -> bool;
}

impl<P: ToString> PrefixPatternObservation for P {
    type Key = String;
    fn key(&self) -> String {
        self.to_string()
    }
    fn mentions_ident(&self) -> bool {
        self.to_string().contains("Ident")
    }
}

/// Closed vocabulary of the existing pattern and guard constructors.
/// GuestCustomRef and CustomTyped intentionally remain distinct: the original
/// quotations bind different variables and therefore occupy distinct buckets.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum NeutralPattern {
    #[default]
    Empty,
    FixedKeyword,
    Ident,
    Integer,
    BooleanAlternative,
    StringLiteral,
    Float,
    Capture,
    GuestCustomRef,
    IntegerTyped,
    CustomTyped,
    RationalTyped,
    FixedPointTyped,
    FixedText(String),
    CaptureName(String),
    GuestName(String),
    CategoryName(String),
}

pub type NeutralPatternKey = NeutralPattern;

impl PrefixPatternObservation for NeutralPattern {
    type Key = NeutralPatternKey;
    fn key(&self) -> Self::Key {
        self.clone()
    }
    fn mentions_ident(&self) -> bool {
        match self {
            Self::Ident => true,
            // Preserve the observation even on guard payloads. Actual Ident
            // analysis checks guard absence before inspecting the pattern.
            Self::FixedText(text)
            | Self::CaptureName(text)
            | Self::GuestName(text)
            | Self::CategoryName(text) => text.contains("Ident"),
            _ => false,
        }
    }
}

/// Retain the existing first_predicate_parts construction, without Rust tokens.
pub fn neutral_predicate_parts(
    predicate: FirstPredicate<'_>,
) -> (NeutralPattern, Option<NeutralPattern>) {
    use NeutralPattern as P;
    match predicate {
        FirstPredicate::Fixed(text) => (P::FixedKeyword, Some(P::FixedText(text.into()))),
        FirstPredicate::Ident => (P::Ident, None),
        FirstPredicate::Integer => (P::Integer, None),
        FirstPredicate::Boolean => (P::BooleanAlternative, None),
        FirstPredicate::String => (P::StringLiteral, None),
        FirstPredicate::Float => (P::Float, None),
        FirstPredicate::CaptureName(text) => (P::Capture, Some(P::CaptureName(text.into()))),
        FirstPredicate::GuestOpen(text) => (P::GuestCustomRef, Some(P::GuestName(text.into()))),
    }
}

pub struct NeutralNativeFirstConstructors;

impl NativeFirstConstructors for NeutralNativeFirstConstructors {
    type Pattern = NeutralPattern;
    fn pattern(&mut self, site: NativePatternSite) -> NeutralPattern {
        use NeutralPattern as P;
        match site {
            NativePatternSite::IntegerTyped => P::IntegerTyped,
            NativePatternSite::CustomTyped => P::CustomTyped,
            NativePatternSite::RationalTyped => P::RationalTyped,
            NativePatternSite::FixedPointTyped => P::FixedPointTyped,
            NativePatternSite::FloatBare => P::Float,
            NativePatternSite::BooleanAlternative => P::BooleanAlternative,
            NativePatternSite::StringBare => P::StringLiteral,
            NativePatternSite::IntegerBare => P::Integer,
        }
    }
    fn category_guard(&mut self, category: &str) -> NeutralPattern {
        NeutralPattern::CategoryName(category.into())
    }
}
