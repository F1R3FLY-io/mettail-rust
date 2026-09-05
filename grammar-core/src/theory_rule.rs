//! Canonical, typed rule contracts for runtime-defined GSLTs.
//!
//! Rule syntax is represented as bounded flat arenas.  Every term and premise
//! edge points backward, so validation, image compilation, and execution can
//! use explicit worklists without consuming the native call stack.  Names are
//! diagnostic and stable; dense numeric identifiers are the executable links.

use crate::{CanonicalValue, CollectionKind, PathMapModeV1};
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
