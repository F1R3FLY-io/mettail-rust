use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum CanonicalValue {
    Map(BTreeMap<String, CanonicalValue>),
    List(Vec<CanonicalValue>),
    String(String),
    Bytes(Vec<u8>),
    Integer(i128),
    FloatBits(u64),
    Boolean(bool),
    Nil,
    /// Minimal signed big-endian two's-complement bytes.
    BigInt(Vec<u8>),
    /// Reduced numerator and strictly positive denominator.
    BigRat {
        numerator: Vec<u8>,
        denominator: Vec<u8>,
    },
    /// Signed unscaled integer with an explicit decimal scale.
    FixedPoint {
        unscaled: Vec<u8>,
        scale: u32,
    },
}

impl CanonicalValue {
    pub fn from_f64(value: f64) -> Self {
        Self::FloatBits(value.to_bits())
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Self::FloatBits(bits) => Some(f64::from_bits(*bits)),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticProgram {
    pub target: Vec<String>,
    pub equations: Vec<CanonicalValue>,
    pub rewrites: Vec<CanonicalValue>,
    pub relations: Vec<CanonicalValue>,
    pub guards: Option<CanonicalValue>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NativeEvaluation {
    Operator(String),
    Carrier {
        kind: String,
        parameters: BTreeMap<String, CanonicalValue>,
    },
    Handler(String),
    Source {
        semantics: Vec<String>,
        text: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EvaluationMode {
    Fold,
    Step,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EvaluationTier {
    T1,
    T2,
    T3,
    T4,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TierDirective {
    pub tier: EvaluationTier,
    pub bound: Option<u32>,
    pub force: bool,
}

#[cfg(test)]
mod exact_value_tests {
    use super::*;

    #[test]
    fn exact_values_round_trip_and_existing_serde_tags_stay_stable() {
        assert_eq!(postcard::to_allocvec(&CanonicalValue::Nil).unwrap(), vec![7]);
        for value in [
            CanonicalValue::BigInt(vec![0, 0x80]),
            CanonicalValue::BigRat {
                numerator: vec![0xff],
                denominator: vec![3],
            },
            CanonicalValue::FixedPoint { unscaled: vec![0], scale: 7 },
        ] {
            let encoded = postcard::to_allocvec(&value).unwrap();
            let decoded: CanonicalValue = postcard::from_bytes(&encoded).unwrap();
            assert_eq!(decoded, value);
        }
    }
}
