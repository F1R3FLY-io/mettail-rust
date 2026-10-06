//! Canonical, typed rule contracts for runtime-defined GSLTs.
//!
//! Rule syntax is represented as bounded flat arenas.  Every term and premise
//! edge points backward, so validation, image compilation, and execution can
//! use explicit worklists without consuming the native call stack.  Names are
//! diagnostic and stable; dense numeric identifiers are the executable links.

use crate::{CanonicalValue, CollectionKind, PathMapModeV1};
use num_bigint::BigInt;
use num_integer::Integer;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TheoryVariableId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryVariableRoleV1 {
    Input,
    Derived,
    Binder,
    Remainder,
    Quantified,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryVariableV1 {
    pub id: TheoryVariableId,
    pub name: String,
    pub sort: String,
    pub role: TheoryVariableRoleV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TheoryTermId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryTermNodeV1 {
    pub sort: String,
    pub form: TheoryTermFormV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryTermFormV1 {
    Variable(TheoryVariableId),
    Constructor {
        constructor: String,
        arguments: Vec<TheoryTermId>,
    },
    Abstraction {
        binder: TheoryVariableId,
        body: TheoryTermId,
    },
    Substitution {
        abstraction: TheoryTermId,
        argument: TheoryTermId,
    },
    Collection {
        elements: Vec<TheoryTermId>,
        remainder: Option<TheoryVariableId>,
        /// Exact structural mode for a PathMap pattern or construction.
        /// `None` is mode-polymorphic and is valid only when a canonical
        /// remainder supplies the mode; mode is never inferred from entries.
        #[serde(default)]
        pathmap_mode: Option<PathMapModeV1>,
    },
    /// A collection comprehension. One source is ordinary map; two or more
    /// sources are exact zip. The construct is rule metasyntax and is
    /// eliminated by matching/construction, never published as an object term.
    Map {
        sources: Vec<TheoryTermId>,
        parameters: Vec<TheoryVariableId>,
        body: TheoryTermId,
    },
    /// A structural product value. This is deliberately distinct from the
    /// `pzip` source syntax consumed by `Map`.
    Product {
        factors: Vec<TheoryTermId>,
    },
    Literal(TheoryLiteralV1),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TheoryLiteralV1 {
    String(String),
    Bytes(Vec<u8>),
    Integer(i128),
    FloatBits(u64),
    Boolean(bool),
    Unit,
    /// Minimal signed big-endian two's-complement representation.
    BigInt(Vec<u8>),
    /// Reduced numerator and strictly positive denominator, both minimal signed BE.
    BigRat {
        numerator: Vec<u8>,
        denominator: Vec<u8>,
    },
    /// Signed unscaled integer and an explicit decimal scale (including trailing zeros).
    FixedPoint {
        unscaled: Vec<u8>,
        scale: u32,
    },
}

/// A unique signed two's-complement representation, including zero as `[0]`.
pub fn is_canonical_signed_big_endian(bytes: &[u8]) -> bool {
    match bytes {
        [] => false,
        [first, second, ..] => {
            !((*first == 0 && *second & 0x80 == 0) || (*first == 0xff && *second & 0x80 != 0))
        },
        [_] => true,
    }
}

/// Check the exact representation before it can enter an image or runtime key.
pub fn is_canonical_theory_literal(literal: &TheoryLiteralV1) -> bool {
    match literal {
        TheoryLiteralV1::BigInt(bytes) => is_canonical_signed_big_endian(bytes),
        TheoryLiteralV1::BigRat { numerator, denominator } => {
            is_canonical_big_rational(numerator, denominator)
        },
        TheoryLiteralV1::FixedPoint { unscaled, .. } => is_canonical_signed_big_endian(unscaled),
        _ => true,
    }
}

/// Exact reduced rational validation; a denominator of zero or negative is invalid.
pub fn is_canonical_big_rational(numerator: &[u8], denominator: &[u8]) -> bool {
    if !is_canonical_signed_big_endian(numerator)
        || !is_canonical_signed_big_endian(denominator)
        || denominator[0] & 0x80 != 0
        || denominator == [0]
    {
        return false;
    }
    BigInt::from_signed_bytes_be(numerator).gcd(&BigInt::from_signed_bytes_be(denominator))
        == BigInt::from(1)
}

#[cfg(test)]
mod exact_literal_tests {
    use super::*;

    #[test]
    fn signed_big_endian_bytes_have_one_representation_per_integer() {
        for bytes in [&[0][..], &[0x7f], &[0, 0x80], &[0x80], &[0xff], &[0xff, 0x7f]] {
            assert!(is_canonical_signed_big_endian(bytes), "{bytes:?}");
        }
        for bytes in [&[][..], &[0, 0], &[0, 0x7f], &[0xff, 0xff], &[0xff, 0x80]] {
            assert!(!is_canonical_signed_big_endian(bytes), "{bytes:?}");
        }
    }

    #[test]
    fn rational_requires_positive_reduced_denominator_and_fixed_preserves_scale() {
        assert!(is_canonical_big_rational(&[0xff], &[2]));
        assert!(is_canonical_big_rational(&[0], &[1]));
        for (numerator, denominator) in [
            (&[2][..], &[4][..]),
            (&[0], &[2]),
            (&[1], &[0]),
            (&[1], &[0xff]),
            (&[0, 1], &[2]),
        ] {
            assert!(!is_canonical_big_rational(numerator, denominator));
        }
        assert!(is_canonical_theory_literal(&TheoryLiteralV1::FixedPoint {
            unscaled: vec![0],
            scale: 7
        }));
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TheoryPremiseId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryPremiseNodeV1 {
    pub form: TheoryPremiseFormV1,
}

/// Closed, pure operations over canonical literal payloads.
///
/// Inputs must already be bound when the premise runs. Outputs are fresh
/// [`TheoryVariableRoleV1::Derived`] slots and become visible only after the
/// premise succeeds. The finite enum is the complete runtime dispatch table:
/// no value can name a callback, parser, URI, or ambient capability.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryIntrinsicV1 {
    ExactTermEq {
        left: TheoryVariableId,
        right: TheoryVariableId,
        output: TheoryVariableId,
    },
    Utf8AtEnd {
        text: TheoryVariableId,
        cursor: TheoryVariableId,
        output: TheoryVariableId,
    },
    Utf8ScalarAt {
        text: TheoryVariableId,
        cursor: TheoryVariableId,
        scalar: TheoryVariableId,
        next_cursor: TheoryVariableId,
    },
    Utf8Slice {
        text: TheoryVariableId,
        start: TheoryVariableId,
        end: TheoryVariableId,
        output: TheoryVariableId,
    },
    CheckedNatAdd {
        left: TheoryVariableId,
        right: TheoryVariableId,
        output: TheoryVariableId,
    },
    Utf8ConcatMany {
        pieces: TheoryVariableId,
        output: TheoryVariableId,
    },
}

impl TheoryIntrinsicV1 {
    pub fn for_each_input(&self, mut visit: impl FnMut(TheoryVariableId)) {
        match self {
            Self::ExactTermEq { left, right, .. } | Self::CheckedNatAdd { left, right, .. } => {
                visit(*left);
                visit(*right);
            },
            Self::Utf8AtEnd { text, cursor, .. } | Self::Utf8ScalarAt { text, cursor, .. } => {
                visit(*text);
                visit(*cursor);
            },
            Self::Utf8Slice { text, start, end, .. } => {
                visit(*text);
                visit(*start);
                visit(*end);
            },
            Self::Utf8ConcatMany { pieces, .. } => visit(*pieces),
        }
    }

    pub fn for_each_output(&self, mut visit: impl FnMut(TheoryVariableId)) {
        match self {
            Self::ExactTermEq { output, .. }
            | Self::Utf8AtEnd { output, .. }
            | Self::Utf8Slice { output, .. }
            | Self::CheckedNatAdd { output, .. }
            | Self::Utf8ConcatMany { output, .. } => visit(*output),
            Self::Utf8ScalarAt { scalar, next_cursor, .. } => {
                visit(*scalar);
                visit(*next_cursor);
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryPremiseFormV1 {
    Freshness {
        variable: TheoryVariableId,
        target: TheoryVariableId,
        remainder: bool,
    },
    Transition {
        source: TheoryVariableId,
        target: TheoryVariableId,
    },
    Judgment(JudgmentAtomV1),
    ForAll {
        collection: TheoryVariableId,
        parameter: TheoryVariableId,
        body: TheoryPremiseId,
    },
    Intrinsic(TheoryIntrinsicV1),
    Guard(CanonicalValue),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryRuleArenaV1 {
    pub variables: Vec<TheoryVariableV1>,
    pub terms: Vec<TheoryTermNodeV1>,
    pub premises: Vec<TheoryPremiseNodeV1>,
    pub premise_roots: Vec<TheoryPremiseId>,
}

impl TheoryRuleArenaV1 {
    pub fn empty() -> Self {
        Self {
            variables: Vec::new(),
            terms: Vec::new(),
            premises: Vec::new(),
            premise_roots: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryEquationV1 {
    pub name: String,
    pub arena: TheoryRuleArenaV1,
    pub left: TheoryTermId,
    pub right: TheoryTermId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryRewriteV1 {
    pub name: String,
    pub arena: TheoryRuleArenaV1,
    pub left: TheoryTermId,
    pub right: TheoryTermId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JudgmentAtomV1 {
    pub judgment: String,
    pub terms: Vec<TheoryTermId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JudgmentRuleV1 {
    pub name: String,
    pub variables: Vec<TheoryVariableV1>,
    pub terms: Vec<TheoryTermNodeV1>,
    pub premises: Vec<JudgmentAtomV1>,
    pub conclusion: JudgmentAtomV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheorySortKindV1 {
    Syntax {
        literal: Option<TheoryLiteralCarrierV1>,
    },
    Collection {
        kind: CollectionKind,
        key: Option<String>,
        element: String,
    },
    Function {
        domain: String,
        codomain: String,
        multiple: bool,
    },
    Product {
        factors: Vec<String>,
    },
    Opaque {
        abi: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryLiteralCarrierV1 {
    Boolean,
    Integer,
    Rational,
    FixedPoint,
    Float,
    String,
    Bytes,
    Unit,
    External(String),
    HostOpaque(String),
}
