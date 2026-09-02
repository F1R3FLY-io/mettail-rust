//! Exact scalar cost for consensus-sensitive parser search.
//!
//! [`ExactParseCost`] is the min-plus semiring used by runtime parser search:
//! alternatives select the smaller cost and sequential steps add costs.  The
//! carrier deliberately contains no lexical, source-category, rule, or span
//! provenance.  Those facts describe a derivation and belong on parse-forest
//! packings; folding them through semiring addition would discard ambiguity.
//!
//! Finite costs are non-negative integer ticks.  One cost unit is exactly
//! [`TICKS_PER_UNIT`] ticks, so every existing parser bias is integral:
//! `0.025`, `0.05`, `0.1`, `0.15`, `0.2`, `0.5`, `1.25`, and `1.5` map to
//! `1`, `2`, `4`, `6`, `8`, `20`, `50`, and `60` ticks respectively.
//! [`ExactParseCost::from_decimal_str`] parses source decimals without first
//! converting them through binary floating point and rejects values outside
//! this exact grid.

use std::fmt;

use serde::{Deserialize, Serialize};

use crate::{
    CompleteSemiring, DetectableZero, IdempotentSemiring, LexProvenance, Semiring, StarSemiring,
    TropicalDeltaWeight,
};

/// Number of exact parser ticks in one externally displayed cost unit.
pub const TICKS_PER_UNIT: u64 = 40;

/// An exact non-negative min-plus parser cost.
///
/// `u64::MAX` is the unique additive zero (unreachable/infinity). All other
/// values are finite costs. Finite overflow saturates to infinity, which keeps
/// addition total, associative, monotone, and distributive over minimum.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ExactParseCost(u64);

/// Failure to convert an external cost into the exact parser-cost domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseCostError {
    Empty,
    Negative,
    InvalidDecimal,
    NotRepresentable,
    Overflow,
    NonFinite,
}

impl ExactParseCost {
    /// Unique representation of an unreachable path.
    pub const INFINITY_TICKS: u64 = u64::MAX;

    /// Construct a finite cost from its exact tick count.
    pub const fn from_ticks(ticks: u64) -> Result<Self, ParseCostError> {
        if ticks == Self::INFINITY_TICKS {
            Err(ParseCostError::Overflow)
        } else {
            Ok(Self(ticks))
        }
    }

    /// Return the exact tick count, or `None` for infinity.
    pub const fn ticks(self) -> Option<u64> {
        if self.0 == Self::INFINITY_TICKS {
            None
        } else {
            Some(self.0)
        }
    }

    /// Convert a finite cost to its display-unit value.
    pub fn to_f64(self) -> f64 {
        match self.ticks() {
            Some(ticks) => ticks as f64 / TICKS_PER_UNIT as f64,
            None => f64::INFINITY,
        }
    }

    /// Convert a binary floating-point boundary value after proving that it is
    /// finite, non-negative, and exactly on the parser tick grid.
    ///
    /// Grammar/source values should use [`Self::from_decimal_str`]. This
    /// method exists for generated Rust constants and compatibility adapters.
    pub fn try_from_f64(value: f64) -> Result<Self, ParseCostError> {
        if !value.is_finite() {
            return Err(ParseCostError::NonFinite);
        }
        if value.is_sign_negative() {
            return Err(ParseCostError::Negative);
        }
        let scaled = value * TICKS_PER_UNIT as f64;
        if scaled.fract() != 0.0 {
            return Err(ParseCostError::NotRepresentable);
        }
        if scaled >= Self::INFINITY_TICKS as f64 {
            return Err(ParseCostError::Overflow);
        }
        Self::from_ticks(scaled as u64)
    }

    /// Parse a non-negative decimal source value exactly.
    ///
    /// Accepted syntax is one or more decimal digits, optionally followed by
    /// a decimal point and one or more digits. Scientific notation and signs
    /// are intentionally rejected so canonical source spelling has one simple,
    /// auditable interpretation.
    pub fn from_decimal_str(source: &str) -> Result<Self, ParseCostError> {
        if source.is_empty() {
            return Err(ParseCostError::Empty);
        }
        if source.starts_with('-') {
            return Err(ParseCostError::Negative);
        }
        if source.starts_with('+') {
            return Err(ParseCostError::InvalidDecimal);
        }

        let mut parts = source.split('.');
        let whole_text = parts.next().expect("split always yields one component");
        let fractional_text = parts.next();
        if parts.next().is_some()
            || whole_text.is_empty()
            || !whole_text.bytes().all(|byte| byte.is_ascii_digit())
            || fractional_text.is_some_and(|text| {
                text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit())
            })
        {
            return Err(ParseCostError::InvalidDecimal);
        }

        let whole = parse_decimal_u64(whole_text)?;
        let mut ticks = whole
            .checked_mul(TICKS_PER_UNIT)
            .ok_or(ParseCostError::Overflow)?;
        if let Some(fractional_text) = fractional_text {
            let fractional = parse_decimal_u64(fractional_text)?;
            let scale = checked_pow10(fractional_text.len())?;
            let numerator = fractional
                .checked_mul(TICKS_PER_UNIT)
                .ok_or(ParseCostError::Overflow)?;
            if numerator % scale != 0 {
                return Err(ParseCostError::NotRepresentable);
            }
            ticks = ticks
                .checked_add(numerator / scale)
                .ok_or(ParseCostError::Overflow)?;
        }
        Self::from_ticks(ticks)
    }
}

fn parse_decimal_u64(text: &str) -> Result<u64, ParseCostError> {
    text.bytes().try_fold(0u64, |value, byte| {
        value
            .checked_mul(10)
            .and_then(|value| value.checked_add(u64::from(byte - b'0')))
            .ok_or(ParseCostError::Overflow)
    })
}

fn checked_pow10(exponent: usize) -> Result<u64, ParseCostError> {
    (0..exponent).try_fold(1u64, |value, _| value.checked_mul(10).ok_or(ParseCostError::Overflow))
}

impl Semiring for ExactParseCost {
    fn zero() -> Self {
        Self(Self::INFINITY_TICKS)
    }

    fn one() -> Self {
        Self(0)
    }

    fn plus(&self, other: &Self) -> Self {
        (*self).min(*other)
    }

    fn times(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        Self(self.0.saturating_add(other.0))
    }

    fn is_zero(&self) -> bool {
        self.0 == Self::INFINITY_TICKS
    }

    fn is_one(&self) -> bool {
        self.0 == 0
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self == other
    }

    fn ess_primary_cost(&self) -> Option<f64> {
        Some(self.to_f64())
    }
}

impl TropicalDeltaWeight for ExactParseCost {
    fn tropical_primary_delta(pre: &Self, post: &Self) -> Self {
        match (pre.ticks(), post.ticks()) {
            (_, None) => Self::zero(),
            (None, Some(post)) => Self(post),
            (Some(pre), Some(post)) => Self(post.saturating_sub(pre)),
        }
    }
}

// Parse provenance is deliberately external to the scalar cost carrier.
impl LexProvenance for ExactParseCost {}
impl DetectableZero for ExactParseCost {}
impl IdempotentSemiring for ExactParseCost {}
impl CompleteSemiring for ExactParseCost {}

impl StarSemiring for ExactParseCost {
    fn star(&self) -> Self {
        Self::one()
    }
}

impl Default for ExactParseCost {
    fn default() -> Self {
        Self::one()
    }
}

impl fmt::Debug for ExactParseCost {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ticks() {
            Some(ticks) => write!(formatter, "ExactParseCost({ticks} ticks)"),
            None => formatter.write_str("ExactParseCost(infinity)"),
        }
    }
}

impl fmt::Display for ExactParseCost {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ticks() {
            Some(ticks) => {
                let whole = ticks / TICKS_PER_UNIT;
                let remainder = ticks % TICKS_PER_UNIT;
                if remainder == 0 {
                    write!(formatter, "{whole}")
                } else {
                    let thousandths = remainder * (1000 / TICKS_PER_UNIT);
                    write!(formatter, "{whole}.{thousandths:03}")
                }
            },
            None => formatter.write_str("inf"),
        }
    }
}

impl fmt::Display for ParseCostError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            ParseCostError::Empty => "parser cost is empty",
            ParseCostError::Negative => "parser cost is negative",
            ParseCostError::InvalidDecimal => "parser cost is not a canonical decimal",
            ParseCostError::NotRepresentable => "parser cost is not exactly representable in ticks",
            ParseCostError::Overflow => "parser cost exceeds the finite tick domain",
            ParseCostError::NonFinite => "parser cost is not finite",
        })
    }
}

impl std::error::Error for ParseCostError {}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn cost(ticks: u64) -> ExactParseCost {
        ExactParseCost::from_ticks(ticks).expect("test ticks are finite")
    }

    #[test]
    fn existing_parser_biases_have_exact_tick_encodings() {
        for (source, ticks) in [
            ("0", 0),
            ("0.025", 1),
            ("0.05", 2),
            ("0.1", 4),
            ("0.15", 6),
            ("0.2", 8),
            ("0.5", 20),
            ("1.25", 50),
            ("1.5", 60),
        ] {
            assert_eq!(ExactParseCost::from_decimal_str(source), Ok(cost(ticks)));
        }
    }

    #[test]
    fn decimal_boundary_rejects_ambiguous_or_inexact_values() {
        for source in ["", ".5", "1.", "+1", "-1", "1e2", "nan", "0.01"] {
            assert!(ExactParseCost::from_decimal_str(source).is_err(), "{source}");
        }
    }

    proptest! {
        #[test]
        fn exact_min_plus_semiring_laws(
            a in any::<u64>().prop_map(|value| cost(value % u64::MAX)),
            b in any::<u64>().prop_map(|value| cost(value % u64::MAX)),
            c in any::<u64>().prop_map(|value| cost(value % u64::MAX)),
        ) {
            let zero = ExactParseCost::zero();
            let one = ExactParseCost::one();

            prop_assert_eq!(a.plus(&zero), a);
            prop_assert_eq!(zero.plus(&a), a);
            prop_assert_eq!(a.times(&one), a);
            prop_assert_eq!(one.times(&a), a);
            prop_assert_eq!(a.times(&zero), zero);
            prop_assert_eq!(zero.times(&a), zero);
            prop_assert_eq!(a.plus(&a), a);
            prop_assert_eq!(a.plus(&b), b.plus(&a));
            prop_assert_eq!(a.plus(&b).plus(&c), a.plus(&b.plus(&c)));
            prop_assert_eq!(a.times(&b).times(&c), a.times(&b.times(&c)));
            prop_assert_eq!(a.times(&b.plus(&c)), a.times(&b).plus(&a.times(&c)));
            prop_assert_eq!(a.plus(&b).times(&c), a.times(&c).plus(&b.times(&c)));
        }
    }
}
