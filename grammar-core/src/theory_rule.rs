//! Canonical, typed rule contracts for runtime-defined GSLTs.
//!
//! Rule syntax is represented as bounded flat arenas.  Every term and premise
//! edge points backward, so validation, image compilation, and execution can
//! use explicit worklists without consuming the native call stack.  Names are
//! diagnostic and stable; dense numeric identifiers are the executable links.

use crate::{CanonicalValue, CollectionKind};
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
    },
    Map {
        collection: TheoryTermId,
        parameters: Vec<TheoryVariableId>,
        body: TheoryTermId,
    },
    Zip {
        left: TheoryTermId,
        right: TheoryTermId,
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
