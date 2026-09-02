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
