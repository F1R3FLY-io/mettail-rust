//! Explicit migrations for historical counterexample corpora.
//!
//! A proptest corpus records the constructor tree that existed when a failure
//! was minimized. Refactoring a grammar must not erase that evidence, but a
//! promoted regression must construct the current type. This module contains
//! the mechanically checkable bridge for Rholang's 2026-08-04 method collapse:
//! each former receiver-first constructor becomes the single
//! `MethodCall(receiver, method_name, arguments)` constructor.

use crate::ctor::DebugNode;

/// One retired Rholang method constructor and its exact generic successor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LegacyRholangMethod {
    /// Retired constructor label in historical `Debug` text.
    pub constructor: &'static str,
    /// Reducer method identifier retained by `MethodCall`.
    pub method: &'static str,
    /// Total constructor arity, including the receiver in slot zero.
    pub arity: usize,
}

/// Complete manifest removed by commit `438e3a3d`, plus `KeysMap`, the
/// pre-`MKeys` spelling still present in the merged historical corpus.
pub const LEGACY_RHOLANG_METHODS: &[LegacyRholangMethod] = &[
    legacy("MGet", "get", 2),
    legacy("MSet", "set", 3),
    legacy("MContains", "contains", 2),
    legacy("MDelete", "delete", 2),
    legacy("MUnion", "union", 2),
    legacy("MSize", "size", 1),
    legacy("MToByteArray", "toByteArray", 1),
    legacy("MHexToBytes", "hexToBytes", 1),
    legacy("MBytesToHex", "bytesToHex", 1),
    legacy("MToUtf8Bytes", "toUtf8Bytes", 1),
    legacy("MKeys", "keys", 1),
    legacy("KeysMap", "keys", 1),
    legacy("MValues", "values", 1),
    legacy("LLength", "length", 1),
    legacy("LNth", "nth", 2),
    legacy("LLast", "last", 1),
    legacy("LConcat", "concat", 2),
    legacy("BCount", "count", 2),
    legacy("BDiff", "diff", 2),
    legacy("BRemove", "remove", 2),
    legacy("PRestrict", "restrict", 2),
    legacy("PSubtract", "subtract", 2),
    legacy("PMeet", "meet", 2),
    legacy("PGetSubtrie", "getSubtrie", 1),
    legacy("PGetSubtrieAt", "getSubtrieAt", 2),
    legacy("PReadZipper", "readZipper", 1),
    legacy("PReadZipperAt", "readZipperAt", 2),
    legacy("PWriteZipper", "writeZipper", 1),
    legacy("PWriteZipperAt", "writeZipperAt", 2),
    legacy("RZGetLeaf", "getLeaf", 1),
    legacy("RZDescendTo", "descendTo", 2),
    legacy("RZChildCount", "childCount", 1),
    legacy("RZDescendFirst", "descendFirst", 1),
    legacy("RZToNextSibling", "toNextSibling", 1),
    legacy("RZToPrevSibling", "toPrevSibling", 1),
    legacy("RZDescendIndexedBranch", "descendIndexedBranch", 2),
    legacy("RZAscendOne", "ascendOne", 1),
    legacy("RZAscend", "ascend", 2),
    legacy("RZGetPath", "getPath", 1),
    legacy("RZToNextLeaf", "toNextLeaf", 1),
    legacy("RZLeafCount", "leafCount", 1),
    legacy("WZSetLeaf", "setLeaf", 3),
    legacy("WZSetSubtrie", "setSubtrie", 2),
    legacy("WZRemoveLeaf", "removeLeaf", 1),
    legacy("WZRemoveBranches", "removeBranches", 1),
    legacy("WZGraft", "graft", 2),
    legacy("WZJoinInto", "joinInto", 2),
    legacy("SAdd", "add", 2),
];

const fn legacy(
    constructor: &'static str,
    method: &'static str,
    arity: usize,
) -> LegacyRholangMethod {
    LegacyRholangMethod { constructor, method, arity }
}

/// Why a historical constructor tree cannot be migrated exactly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CorpusMigrationError {
    /// Retired constructor whose recorded arity drifted.
    pub constructor: String,
    /// Arity in the source grammar's historical manifest.
    pub expected_arity: usize,
    /// Arity found in the corpus tree.
    pub actual_arity: usize,
}

impl std::fmt::Display for CorpusMigrationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "legacy Rholang method `{}` has arity {}, expected {}",
            self.constructor, self.actual_arity, self.expected_arity
        )
    }
}

/// Counts for every representation-changing corpus migration currently needed
/// by Rholang's historical corpus.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RholangCorpusMigration {
    /// Receiver-specific constructors collapsed into `MethodCall`.
    pub method_calls: usize,
    /// Old empty `ListLit` byte carriers migrated to `BytesLit`.
    pub byte_carriers: usize,
    /// Old untagged empty `PathMapLit(HashMapLit({}))` values migrated to the
    /// current mode-neutral `Empty` representation.
    pub pathmap_empty_carriers: usize,
}

/// Failure to translate a historical Rholang constructor without guessing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RholangCorpusMigrationError {
    /// A retired method constructor no longer matches its historical arity.
    Method(CorpusMigrationError),
    /// A pre-byte-literal `CastBytes(ListLit(..))` contains nonempty process
    /// elements, for which no semantics-preserving byte conversion exists.
    NonemptyLegacyByteList { element_count: usize },
    /// An old untagged nonempty path map cannot reveal whether unit-like
    /// values represented set membership or map values.
    NonemptyLegacyPathMap { entry_count: usize },
}

impl std::fmt::Display for RholangCorpusMigrationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Method(error) => error.fmt(formatter),
            Self::NonemptyLegacyByteList { element_count } => write!(
                formatter,
                "legacy CastBytes(ListLit(..)) contains {element_count} process element(s); \
                 only the empty list has a unique Vec<u8> successor"
            ),
            Self::NonemptyLegacyPathMap { entry_count } => write!(
                formatter,
                "legacy PathMapLit(HashMapLit(..)) contains {entry_count} entr{}; only the \
                 empty untagged container has a unique mode-neutral successor",
                if *entry_count == 1 { "y" } else { "ies" }
            ),
        }
    }
}

impl From<CorpusMigrationError> for RholangCorpusMigrationError {
    fn from(error: CorpusMigrationError) -> Self {
        Self::Method(error)
    }
}

/// Apply every exact migration required by the historical Rholang corpus.
///
/// Besides the method collapse, historical seeds retain two pre-specialization
/// carriers. `CastBytes(ListLit([]))` has the unique byte value `BytesLit([])`.
/// `PathMapLit(HashMapLit({}))` has the unique mode-neutral value `Empty`.
/// Nonempty forms are rejected where inferring bytes or set/map mode would
/// fabricate semantics.
pub fn migrate_rholang_corpus(
    root: &mut DebugNode,
) -> Result<RholangCorpusMigration, RholangCorpusMigrationError> {
    let method_calls = migrate_rholang_method_calls(root)?;
    let mut work = vec![root];
    let mut byte_carriers = 0usize;
    let mut pathmap_empty_carriers = 0usize;

    while let Some(node) = work.pop() {
        if let DebugNode::Call { head, args } = node {
            if head == "CastBytes" {
                if let [DebugNode::Call { head: inner_head, args: inner_args }] =
                    args.as_mut_slice()
                {
                    if inner_head == "ListLit" {
                        if let [DebugNode::List(elements)] = inner_args.as_slice() {
                            if !elements.is_empty() {
                                return Err(RholangCorpusMigrationError::NonemptyLegacyByteList {
                                    element_count: elements.len(),
                                });
                            }
                            *inner_head = "BytesLit".to_string();
                            byte_carriers += 1;
                        }
                    }
                }
            }
            if head == "PathMapLit" {
                if let [DebugNode::Call { head: inner_head, args: inner_args }] =
                    args.as_mut_slice()
                {
                    if inner_head == "HashMapLit" {
                        if let [DebugNode::Map(entries)] = inner_args.as_slice() {
                            if !entries.is_empty() {
                                return Err(RholangCorpusMigrationError::NonemptyLegacyPathMap {
                                    entry_count: entries.len(),
                                });
                            }
                            *node = DebugNode::Ident("Empty".to_string());
                            pathmap_empty_carriers += 1;
                        }
                    }
                }
            }
        }

        match node {
            DebugNode::Call { args, .. }
            | DebugNode::List(args)
            | DebugNode::Set(args)
            | DebugNode::Tuple(args) => work.extend(args.iter_mut().rev()),
            DebugNode::Struct { fields, .. } => {
                work.extend(fields.iter_mut().rev().map(|(_, value)| value));
            },
            DebugNode::Map(entries) => {
                for (key, value) in entries.iter_mut().rev() {
                    work.push(value);
                    work.push(key);
                }
            },
            DebugNode::Named { value, .. } => work.push(value),
            DebugNode::Ident(_)
            | DebugNode::Str(_)
            | DebugNode::Int(_)
            | DebugNode::Float(_)
            | DebugNode::Ratio(_, _)
            | DebugNode::Range(_, _) => {},
        }
    }

    Ok(RholangCorpusMigration {
        method_calls,
        byte_carriers,
        pathmap_empty_carriers,
    })
}

/// Rewrite every retired Rholang method constructor in `root` to `MethodCall`.
///
/// The walk is an explicit pushdown automaton, so a deeply nested historical
/// counterexample cannot overflow while being promoted. Children are visited
/// after their parent is rewritten, which also migrates nested receiver and
/// argument calls. The returned count is an anti-vacuity witness used by the
/// promotion gates.
pub fn migrate_rholang_method_calls(root: &mut DebugNode) -> Result<usize, CorpusMigrationError> {
    let mut work = vec![root];
    let mut migrated = 0usize;

    while let Some(node) = work.pop() {
        if let DebugNode::Call { head, args } = node {
            if let Some(spec) = LEGACY_RHOLANG_METHODS
                .iter()
                .find(|spec| spec.constructor == head)
            {
                if args.len() != spec.arity || args.is_empty() {
                    return Err(CorpusMigrationError {
                        constructor: head.clone(),
                        expected_arity: spec.arity.max(1),
                        actual_arity: args.len(),
                    });
                }
                let mut old_args = std::mem::take(args).into_iter();
                let Some(receiver) = old_args.next() else {
                    return Err(CorpusMigrationError {
                        constructor: head.clone(),
                        expected_arity: 1,
                        actual_arity: 0,
                    });
                };
                *node = DebugNode::Call {
                    head: "MethodCall".to_string(),
                    args: vec![
                        receiver,
                        DebugNode::Str(spec.method.to_string()),
                        DebugNode::List(old_args.collect()),
                    ],
                };
                migrated += 1;
            }
        }

        match node {
            DebugNode::Call { args, .. }
            | DebugNode::List(args)
            | DebugNode::Set(args)
            | DebugNode::Tuple(args) => work.extend(args.iter_mut().rev()),
            DebugNode::Struct { fields, .. } => {
                work.extend(fields.iter_mut().rev().map(|(_, value)| value));
            },
            DebugNode::Map(entries) => {
                for (key, value) in entries.iter_mut().rev() {
                    work.push(value);
                    work.push(key);
                }
            },
            DebugNode::Named { value, .. } => work.push(value),
            DebugNode::Ident(_)
            | DebugNode::Str(_)
            | DebugNode::Int(_)
            | DebugNode::Float(_)
            | DebugNode::Ratio(_, _)
            | DebugNode::Range(_, _) => {},
        }
    }

    Ok(migrated)
}
