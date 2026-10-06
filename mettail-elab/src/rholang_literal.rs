//! Canonical source spelling for the ordinary Rholang value subset.
//!
//! This module is migration/bootstrap tooling, not a production decode seam.
//! Inline DDL is parsed once by the generated Rholang parser and lowered
//! structurally.  The emitter exists so an already-typed canonical value can
//! be checked into a `.rho` artifact and fed to that entrypoint.

use crate::canonical::{admit_canonical_value, RhoValue};
use std::fmt;

/// The complete emitted literal, including punctuation, must remain bounded
/// independently of the semantic value limits.
pub const MAX_RHOLANG_LITERAL_BYTES: usize = 128 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RholangLiteralLimits {
    pub max_output_bytes: usize,
}

impl Default for RholangLiteralLimits {
    fn default() -> Self {
        Self {
            max_output_bytes: MAX_RHOLANG_LITERAL_BYTES,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RholangLiteralError {
    InvalidCanonicalValue(String),
    NonFiniteFloat(u64),
    NonCanonicalFloat(u64),
    IntegerOutsideNativeCarrier(i128),
    OutputLimit { limit: usize },
    Allocation(String),
}

impl fmt::Display for RholangLiteralError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCanonicalValue(message) => formatter.write_str(message),
            Self::NonFiniteFloat(bits) => {
                write!(formatter, "non-finite float bits 0x{bits:016x} have no Rholang literal")
            },
            Self::NonCanonicalFloat(bits) => {
                write!(formatter, "float bits 0x{bits:016x} are not a canonical Rholang Float")
            },
            Self::IntegerOutsideNativeCarrier(value) => {
                write!(formatter, "integer {value} is outside Rholang Int; use a BigInt value")
            },
            Self::OutputLimit { limit } => {
                write!(formatter, "Rholang value literal exceeds {limit} output bytes")
            },
            Self::Allocation(message) => {
                write!(formatter, "cannot allocate Rholang value literal: {message}")
            },
        }
    }
}

impl std::error::Error for RholangLiteralError {}

enum Task<'a> {
    Value(&'a RhoValue),
    Quoted(&'a str),
    Text(&'static str),
}

/// Render one typed value with deterministic map ordering and no recursion by
/// value depth.  Strings use Rholang's single literal transducer: quote and
/// backslash are escaped; every other Unicode scalar is copied unchanged.
pub fn render_rholang_value_literal(value: &RhoValue) -> Result<String, RholangLiteralError> {
    render_rholang_value_literal_with(value, RholangLiteralLimits::default())
}

pub fn render_rholang_value_literal_with(
    value: &RhoValue,
    limits: RholangLiteralLimits,
) -> Result<String, RholangLiteralError> {
    admit_canonical_value(value)
        .map_err(|error| RholangLiteralError::InvalidCanonicalValue(error.to_string()))?;
    let mut output = String::new();
    let mut tasks = vec![Task::Value(value)];
    while let Some(task) = tasks.pop() {
        match task {
            Task::Text(text) => append(&mut output, text, limits)?,
            Task::Quoted(value) => append_quoted(&mut output, value, limits)?,
            Task::Value(RhoValue::Map(values)) => {
                if values.is_empty() {
                    // Bare `{}` deliberately has both the empty-map and empty-
                    // parallel readings in Rholang.  `Map()` is the language's
                    // unambiguous empty-map constructor, so using it is required
                    // for a canonical value -> source -> value round trip.
                    append(&mut output, "Map()", limits)?;
                    continue;
                }
                append(&mut output, "{", limits)?;
                tasks.push(Task::Text("}"));
                for (index, (key, value)) in values.iter().enumerate().rev() {
                    tasks.push(Task::Value(value));
                    tasks.push(Task::Text(":"));
                    tasks.push(Task::Quoted(key));
                    if index > 0 {
                        tasks.push(Task::Text(","));
                    }
                }
            },
            Task::Value(RhoValue::List(values)) => {
                append(&mut output, "[", limits)?;
                tasks.push(Task::Text("]"));
                for (index, value) in values.iter().enumerate().rev() {
                    tasks.push(Task::Value(value));
                    if index > 0 {
                        tasks.push(Task::Text(","));
                    }
                }
            },
            Task::Value(RhoValue::String(value)) => {
                append_quoted(&mut output, value, limits)?;
            },
            Task::Value(RhoValue::Bytes(value)) => {
                append_bytes(&mut output, value, limits)?;
            },
            Task::Value(RhoValue::Integer(value)) => {
                i64::try_from(*value)
                    .map_err(|_| RholangLiteralError::IntegerOutsideNativeCarrier(*value))?;
                let literal = value.to_string();
                append(&mut output, &literal, limits)?;
            },
            Task::Value(RhoValue::BigInt(bytes)) => {
                let literal = num_bigint::BigInt::from_signed_bytes_be(bytes).to_string();
                append(&mut output, &literal, limits)?;
                append(&mut output, "n", limits)?;
            },
            Task::Value(RhoValue::BigRat { numerator, denominator }) => {
                let n = num_bigint::BigInt::from_signed_bytes_be(numerator).to_string();
                let d = num_bigint::BigInt::from_signed_bytes_be(denominator).to_string();
                append(&mut output, &n, limits)?;
                append(&mut output, "r/", limits)?;
                append(&mut output, &d, limits)?;
                append(&mut output, "r", limits)?;
            },
            Task::Value(RhoValue::FixedPoint { unscaled, scale }) => {
                append_fixed_point(&mut output, unscaled, *scale, limits)?;
            },
            Task::Value(RhoValue::FloatBits(bits)) => {
                let value = f64::from_bits(*bits);
                if !value.is_finite() {
                    return Err(RholangLiteralError::NonFiniteFloat(*bits));
                }
                if mettail_runtime::CanonicalFloat64::from(value)
                    .get()
                    .to_bits()
                    != *bits
                {
                    return Err(RholangLiteralError::NonCanonicalFloat(*bits));
                }
                let mut literal = value.to_string();
                if !literal.contains(['.', 'e', 'E']) {
                    literal.push_str(".0");
                }
                append(&mut output, &literal, limits)?;
            },
            Task::Value(RhoValue::Boolean(value)) => {
                append(&mut output, if *value { "true" } else { "false" }, limits)?;
            },
            Task::Value(RhoValue::Nil) => append(&mut output, "Nil", limits)?,
        }
    }
    Ok(output)
}

fn append(
    output: &mut String,
    value: &str,
    limits: RholangLiteralLimits,
) -> Result<(), RholangLiteralError> {
    let length = output
        .len()
        .checked_add(value.len())
        .ok_or(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes })?;
    if length > limits.max_output_bytes {
        return Err(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes });
    }
    output
        .try_reserve(value.len())
        .map_err(|error| RholangLiteralError::Allocation(error.to_string()))?;
    output.push_str(value);
    Ok(())
}

fn append_fixed_point(
    output: &mut String,
    unscaled: &[u8],
    scale: u32,
    limits: RholangLiteralLimits,
) -> Result<(), RholangLiteralError> {
    let number = num_bigint::BigInt::from_signed_bytes_be(unscaled).to_string();
    let negative = number.starts_with('-');
    let digits = if negative { &number[1..] } else { &number };
    let places = scale as usize;
    let suffix = format!("p{scale}");
    let width = if places == 0 {
        number.len().checked_add(suffix.len())
    } else {
        places
            .max(digits.len())
            .checked_add(2 + usize::from(negative))
            .and_then(|n| n.checked_add(suffix.len()))
    }
    .ok_or(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes })?;
    if output
        .len()
        .checked_add(width)
        .is_none_or(|n| n > limits.max_output_bytes)
    {
        return Err(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes });
    }
    if places == 0 {
        append(output, &number, limits)?;
    } else {
        if negative {
            append(output, "-", limits)?;
        }
        if digits.len() <= places {
            append(output, "0.", limits)?;
            let padding = places - digits.len();
            output
                .try_reserve(padding)
                .map_err(|error| RholangLiteralError::Allocation(error.to_string()))?;
            output.extend(std::iter::repeat_n('0', padding));
            append(output, digits, limits)?;
        } else {
            let split = digits.len() - places;
            append(output, &digits[..split], limits)?;
            append(output, ".", limits)?;
            append(output, &digits[split..], limits)?;
        }
    }
    append(output, &suffix, limits)
}

fn append_quoted(
    output: &mut String,
    value: &str,
    limits: RholangLiteralLimits,
) -> Result<(), RholangLiteralError> {
    let escaped = value
        .bytes()
        .filter(|byte| matches!(byte, b'"' | b'\\'))
        .count();
    let width = value
        .len()
        .checked_add(escaped)
        .and_then(|length| length.checked_add(2))
        .ok_or(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes })?;
    let length = output
        .len()
        .checked_add(width)
        .ok_or(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes })?;
    if length > limits.max_output_bytes {
        return Err(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes });
    }
    output
        .try_reserve(width)
        .map_err(|error| RholangLiteralError::Allocation(error.to_string()))?;
    output.push('"');
    for character in value.chars() {
        if matches!(character, '"' | '\\') {
            output.push('\\');
        }
        output.push(character);
    }
    output.push('"');
    Ok(())
}

fn append_bytes(
    output: &mut String,
    value: &[u8],
    limits: RholangLiteralLimits,
) -> Result<(), RholangLiteralError> {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let width = value
        .len()
        .checked_mul(2)
        .and_then(|length| length.checked_add(3))
        .ok_or(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes })?;
    let length = output
        .len()
        .checked_add(width)
        .ok_or(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes })?;
    if length > limits.max_output_bytes {
        return Err(RholangLiteralError::OutputLimit { limit: limits.max_output_bytes });
    }
    output
        .try_reserve(width)
        .map_err(|error| RholangLiteralError::Allocation(error.to_string()))?;
    output.push_str("b\"");
    for byte in value {
        output.push(HEX[(byte >> 4) as usize] as char);
        output.push(HEX[(byte & 0x0f) as usize] as char);
    }
    output.push('"');
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn canonical_scalar_spellings_are_unambiguous() {
        let value = RhoValue::List(vec![
            RhoValue::BigInt(num_bigint::BigInt::from(i64::MAX as i128 + 1).to_signed_bytes_be()),
            RhoValue::FloatBits(0.0f64.to_bits()),
            RhoValue::String("quote \" slash \\".into()),
            RhoValue::Bytes(vec![0, 0xab, 0xff]),
            RhoValue::Boolean(true),
            RhoValue::Nil,
        ]);
        assert_eq!(
            render_rholang_value_literal(&value).unwrap(),
            r#"[9223372036854775808n,0.0,"quote \" slash \\",b"00abff",true,Nil]"#,
        );
    }

    #[test]
    fn renderer_refuses_values_that_native_rholang_would_retype_or_normalize() {
        let outside = i64::MAX as i128 + 1;
        assert_eq!(
            render_rholang_value_literal(&RhoValue::Integer(outside)),
            Err(RholangLiteralError::IntegerOutsideNativeCarrier(outside)),
        );
        let negative_zero = (-0.0f64).to_bits();
        assert_eq!(
            render_rholang_value_literal(&RhoValue::FloatBits(negative_zero)),
            Err(RholangLiteralError::NonCanonicalFloat(negative_zero)),
        );
    }

    #[test]
    fn map_order_and_output_limit_are_deterministic() {
        let value = RhoValue::Map(BTreeMap::from([
            ("z".into(), RhoValue::Integer(2)),
            ("a".into(), RhoValue::Integer(1)),
        ]));
        let rendered = render_rholang_value_literal(&value).unwrap();
        assert_eq!(rendered, r#"{"a":1,"z":2}"#);
        assert_eq!(
            render_rholang_value_literal_with(
                &value,
                RholangLiteralLimits { max_output_bytes: rendered.len() - 1 },
            ),
            Err(RholangLiteralError::OutputLimit { limit: rendered.len() - 1 })
        );
    }

    #[test]
    fn empty_map_uses_the_unambiguous_rholang_constructor() {
        let empty = RhoValue::Map(BTreeMap::new());
        assert_eq!(render_rholang_value_literal(&empty).unwrap(), "Map()");

        let nested = RhoValue::Map(BTreeMap::from([("empty".into(), empty)]));
        assert_eq!(render_rholang_value_literal(&nested).unwrap(), r#"{"empty":Map()}"#,);
    }

    #[test]
    fn deepest_admitted_value_renders_on_a_small_stack_and_extra_depth_is_rejected() {
        fn nested_list(depth: usize) -> RhoValue {
            let mut value = RhoValue::Nil;
            for _ in 0..depth {
                value = RhoValue::List(vec![value]);
            }
            value
        }

        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let admitted_wrappers = crate::parse::MAX_DDL_STRUCTURAL_DEPTH - 1;
                let admitted = nested_list(admitted_wrappers);
                let rendered = render_rholang_value_literal(&admitted)
                    .expect("the deepest admitted canonical value must render iteratively");
                assert_eq!(rendered.len(), admitted_wrappers * 2 + 3);

                let rejected = nested_list(crate::parse::MAX_DDL_STRUCTURAL_DEPTH);
                assert!(matches!(
                    render_rholang_value_literal(&rejected),
                    Err(RholangLiteralError::InvalidCanonicalValue(_))
                ));
            })
            .expect("small-stack renderer test thread must start")
            .join()
            .expect("small-stack renderer test must not overflow");
    }
}
